module

public import Green64.Library.Sieve.Foundations.Part015
public import Green64.Library.Sieve.Foundations.Part014
public import Green64.Library.Sieve.Foundations.Part013
public import Green64.Library.Sieve.Foundations.Part009
public import Green64.Library.Sieve.Foundations.Part012
public import Green64.Library.Weights.Part112
public import Green64.Library.Sieve.Foundations.Part010

@[expose] public section

/-!
# Sieve / Foundations / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalSignedOddBoxJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- At every genuine B590 Fourier coordinate ξ, the original odd
projected full-Q 20! factorial f0/f1 integrand is precisely half
the signed ε=1 minus signed ε=E complete Q-source integrands.
Signed forms are preserved independently and no parity sign has
been absorbed into alpha/beta. -/
theorem parity_original_B590_odd_integrand_eq_signed_difference434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _=>0) z *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) z.1
        (fun i => (parityActualSourceRemainingFullQTuple434
          d L band slot z.2 i).val) ξ) =
    (parityOriginalSignedFullSourceFourierAtU434 d L E u false band slot ξ -
     parityOriginalSignedFullSourceFourierAtU434 d L E u true band slot ξ)/2 := by
  rw [Fintype.sum_prod_type]
  unfold parityOriginalSignedFullSourceFourierAtU434
  rw [←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro δ hδ
  rw [←parity_original_fullQ_odd_fourier_eq_signed_half_difference434]
  unfold parityOriginalActualFullQAllGateFourierAtU434
  apply Finset.sum_congr rfl
  intro f hf
  rw [parity_original_B590_arithmetic_at_zero_eq_actual_tuple_weight434]

/-- The TRUE original odd-projected B590 Fourier BOX arithmetic
coefficient is EXACTLY half the difference of the independently
integrated signed ε=1 and ε=E source Fourier coefficients. This
proves the split before any Cauchy or correlation, under genuine
product Lebesgue measure with original Q/P weights and factorials.
Signed ε=E need not be nonnegative, but its integrability is proved. -/
theorem parity_original_B590_odd_A_box_eq_signed_half_difference434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
      (parityOriginalSignedPhysicalABoxAtU434 d L E u false band slot T -
       parityOriginalSignedPhysicalABoxAtU434 d L E u true band slot T)/2 := by
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  have h0 := parity_original_signed_full_source_fourier_integrable_on_box434
    d L E u false band slot T
  have h1 := parity_original_signed_full_source_fourier_integrable_on_box434
    d L E u true band slot T
  have hOld := parity_original_B590_actual_A_box_eq_full_arithmetic_integral434
    d L E u band slot T
  rw [hOld]
  unfold parityOriginalSignedPhysicalABoxAtU434
  rw [←integral_sub h0 h1]
  rw [←integral_div]
  apply integral_congr_ae
  filter_upwards [] with ξ
  exact parity_original_B590_odd_integrand_eq_signed_difference434
    d L E u band slot ξ

/-- SOURCE h=-2 complete original odd B590 Fourier BOX bilinear
is half the difference of TWO signed ε=1,E original B590 Fourier
BOX bilinears, with the same original Ψ and literal shifted
mn=u+2 alpha_m beta_n. This is the correct signed-to-projector
identity **after** Fourier integration and **before** squaring. -/
theorem parity_original_hminus2_odd_fourier_box_eq_signed_half_difference434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearFourierBox434
      d L E band slot Psi K J α β Y T =
      (parityOriginalShiftTwoSignedBilinearFourierBox434
        d L E band slot Psi K J α β false Y T -
       parityOriginalShiftTwoSignedBilinearFourierBox434
        d L E band slot Psi K J α β true Y T)/2 := by
  unfold parityOriginalShiftTwoBilinearFourierBox434
    parityOriginalShiftTwoSignedBilinearFourierBox434
  rw [←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_B590_odd_A_box_eq_signed_half_difference434]
  push_cast
  ring

/-- The two independent signed physical Parity ε=1,E H Fourier-box
h=-2 bilinears recombine to EXACTLY the original odd-projected
source B590 Fourier-box. The signed H representations were proved
separately before their half-difference; this is the source-facing
endpoint identity needed before Parity(4.17) square/correlation. -/
theorem parity_original_hminus2_odd_fourier_box_eq_signed_H_half_difference434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearFourierBox434
      d L E band slot Psi K J α β Y T =
      (parityOriginalShiftTwoSignedBilinearHBox434
        d L E band slot Psi K J α β false Y T -
       parityOriginalShiftTwoSignedBilinearHBox434
        d L E band slot Psi K J α β true Y T)/2 := by
  rw [parity_original_hminus2_odd_fourier_box_eq_signed_half_difference434]
  rw [parity_original_hminus2_signed_fourier_box_eq_H434
    d L E hL hd band slot Psi K J α β false Y T]
  rw [parity_original_hminus2_signed_fourier_box_eq_H434
    d L E hL hd band slot Psi K J α β true Y T]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedHBoxAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- ORIGINAL Parity §4.1 sourceOriginalA odd-projected h=-2
α_mβ_n source is within `2AB exp(L)L^-A` of the HALF DIFFERENCE of
two genuinely independent physical B590 Fourier-BOX signed source
integrals: ε=1 and ε=E(v)=(-1)^Ω_P(v). Each integral was obtained
from its own complete source Q/P factorial-labelled signed Fourier
sum and physically factors into selected Q e-only coefficients times
`v^0 W1(P,v) ε(v) H_0(vStar)` with the ACTUAL reserved-Q prime and
native B509 skipped-Q c_r. The signs are separated BEFORE squaring.

This is a direct norm inequality from the genuine original unsmoothed
sourceOriginalA to the correct pair of signed Parity(4.7) physical
Fourier BOX bilinears; it is NOT merely a parity projector statement.
The original signed SOURCE-to-physical Rankin error for each ε
independently, nonzero reserved σ and historical Parity(4.17) signed
correlation are separate open mathematical obligations. -/
theorem parity_eventually_original_hminus2_source_to_signed_H_boxes_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β
          ⌊2*Real.exp L⌋₊ -
        (parityOriginalShiftTwoSignedBilinearHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β false ⌊2*Real.exp L⌋₊ L -
         parityOriginalShiftTwoSignedBilinearHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β true ⌊2*Real.exp L⌋₊ L)/2‖ ≤
        2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_source_to_fourier_box_all_log434
    betaP A hbetaP jQ hBand,
    eventually_gt_atTop (0:ℝ)] with L hSource hLp
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  rw [←parity_original_hminus2_odd_fourier_box_eq_signed_H_half_difference434
    (sourceOriginalLiteralDepth 20 L) L E hLp rfl band slot
    Psi K J α β ⌊2*Real.exp L⌋₊ L]
  exact hSource.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedPhysicalBounds -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The native Parity(4.9) signed physical coefficient for BOTH
ε=1 and ε=E, including nonzero source v^(i rho), complete W1(P,v)
and genuine reserved-prime H_sigma(vStar), obeys the honest source
size `W1(P,v)*tau(vStar)` for every positive vStar.
The signed epsilon has unit modulus and native B509 residual c_r has
factorial-cancelled |c_r|≤1, so NO additional factorial or number-of-
reserved-primes factor is introduced. -/
theorem parity_original_signed_physical_aV_norm_le_W1_tau434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ σ rho : ℝ) (signed : Bool)
    (vStar v : ℕ) (hvStar : 0 < vStar) :
    ‖parityOriginalReservedSignedPhysicalAV434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ σ rho signed vStar v‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
        (vStar.divisors.card:ℝ) := by
  let P := sourceOriginalPAllActualBands 20 L
  let W : ℝ := sourceOriginalW1 P v
  have hW : 0 ≤ W := source_original_W1_nonneg P v
  have hH := parity_original_reserved_H_norm_le_divisor_count434
    d L hL band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar hvStar
  have hSign := parity_original_P_signed_epsilon_abs_one434
    (Finset.univ.biUnion P) signed v
  unfold parityOriginalReservedSignedPhysicalAV434
  rw [norm_mul,norm_mul,source_original_pure_mellin_phase_norm_one434,one_mul]
  rw [Complex.norm_real,Real.norm_eq_abs]
  rw [abs_mul,abs_of_nonneg hW,hSign,mul_one]
  exact mul_le_mul_of_nonneg_left hH hW

/-- Complete genuine Parity (4.9) signed ε=1/E physical a_v SOURCE
uniform fixed logarithmic bound `L^C_W1 tau(vStar)`. The exponent
is entirely independent of later K0 and Fourier/moment accuracy,
real σ/rho and signed branch; this is NOT by itself Parity(4.17)
correlation or the signed discrepancy required to invoke it. -/
theorem parity_eventually_original_signed_physical_aV_polylog_tau434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (K : Finset ℕ) (alpha : ℕ → ℂ)
        (q : ℕ) (χ : DirichletCharacter ℂ q)
        (σ₀ σ₁ σ rho : ℝ) (signed : Bool)
        (vStar v : ℕ), 0 < vStar →
      ‖parityOriginalReservedSignedPhysicalAV434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ K alpha
          q χ σ₀ σ₁ σ rho signed vStar v‖ ≤
        L^parityOriginalW1PolylogExponent434 *
          (vStar.divisors.card:ℝ) := by
  filter_upwards [parity_eventually_original_actual_W1_pointwise_polylog434,
    eventually_gt_atTop (0:ℝ)] with L hW hLp
  intro band slot δ ξ K alpha q χ σ₀ σ₁ σ rho signed vStar v hv
  have hBound := parity_original_signed_physical_aV_norm_le_W1_tau434
    (sourceOriginalLiteralDepth 20 L) L hLp
    band slot δ ξ K alpha q χ σ₀ σ₁ σ rho signed vStar v hv
  exact hBound.trans (mul_le_mul_of_nonneg_right (hW v) (Nat.cast_nonneg _))
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedMellinEFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Genuine signed Parity ε=1/E ORIGINAL full 20!-labelled source
B590 Fourier coefficient at any real Mellin rho factors exactly into
selected e^(i rho) Fourier e-only term times physical
v^(i rho) W1(P,v) ε(v) H_0(vStar) on true e*v=u Q-product gate,
with no quotient by the odd projector and no split into alpha/beta.
Reserved prime σ remains 0 until sourced from further transforms. -/
theorem parity_original_signed_fullQ_mellin_fourier_eq_e_aV434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ) :
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedFullQAllGateFourierAtU434
        d L E u signed band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2 = sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateMellinCoefficient434
          d L E band slot δ ξ rho z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  rw [parity_original_signed_fullQ_all_gate_fourier_eq_e_H434
    d L E hL hd u hu signed band slot δ ξ K alpha q χ σ₀ σ₁]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  let P := sourceOriginalPAllActualBands 20 L
  let v := z.2*sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  by_cases hgate : z.1*z.2=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion P) u
  · dsimp only [P] at hgate ⊢
    simp only [if_pos hgate]
    have hEv : z.1*v=u := by
      dsimp [v]
      calc
        _ = (z.1*z.2)*sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by ac_rfl
        _ = sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u *
          sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by rw [hgate]
        _ = u := source_original_ordinary_times_P_part _ u hu
    have hprod : 0 < z.1*v := by
      rw [hEv]
      exact Nat.pos_of_ne_zero hu
    have he : 0 < z.1 := Nat.pos_of_mul_pos_right hprod
    have hv : 0 < v := Nat.pos_of_mul_pos_left hprod
    have hPhase : sourceOriginalPureMellinPhase434 rho u =
        sourceOriginalPureMellinPhase434 rho z.1 *
          sourceOriginalPureMellinPhase434 rho v := by
      rw [←hEv]
      exact parity_original_source_mellin_phase_mul_pos434 rho z.1 v he hv
    have hAV : parityOriginalReservedSignedPhysicalAV434 d L band slot δ ξ K alpha q χ
        σ₀ σ₁ 0 rho signed z.2 v =
        sourceOriginalPureMellinPhase434 rho v *
          parityOriginalReservedSignedPhysicalAV434 d L band slot δ ξ K alpha q χ
            σ₀ σ₁ 0 0 signed z.2 v := by
      unfold parityOriginalReservedSignedPhysicalAV434
      have hZero : sourceOriginalPureMellinPhase434 (0:ℝ) v=1 := by
        simp [sourceOriginalPureMellinPhase434]
      rw [hZero]
      ring
    rw [hPhase]
    unfold parityOriginalSelectedEGateMellinCoefficient434
    rw [hAV]
    ring
  · dsimp only [P] at hgate ⊢
    simp only [if_neg hgate]
    ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedMellinHBoxIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- ORIGINAL signed Parity ε=1/E complete selected-e and physical
reserved H(vStar) source integrand with a nonzero arbitrary Mellin
rho separated e^(i rho) and v^(i rho), true 20! Q product gate and
P-sign. Each branch remains independently signed before a norm. -/
def parityOriginalSignedSourceMellinHAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2=sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateMellinCoefficient434
          d L E band slot δ ξ rho z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0

/-- Genuine original signed ε=1/E source at u>0, multiplied by
arbitrary original Mellin rho phase u^(i rho), is exactly the full
physical e^(i rho) × v^(i rho) signed W1(v)ε(v)H_0(vStar) Fourier
integrand after summing ALL actual B590 δ assignments. -/
theorem parity_original_signed_source_mellin_H_integrand_exact434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedFullSourceFourierAtU434
        d L E u signed band slot ξ =
      parityOriginalSignedSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ := by
  unfold parityOriginalSignedFullSourceFourierAtU434
    parityOriginalSignedSourceMellinHAtU434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_signed_fullQ_mellin_fourier_eq_e_aV434
    d L E hL hd u hu signed band slot δ ξ K alpha q χ σ₀ σ₁ rho

/-- Full true independent SIGNED original ε=1/E B590 Fourier BOX
at physical u>0, weighted by the actual Mellin phase u^(i rho),
equals an integrable physical e^(i rho)×v^(i rho) W1ε H_0(vStar)
integral over the REAL N-dimensional source f0/f1 Fourier box.
All source Q labels, factorials and P multiplicity signs retained. -/
theorem parity_original_signed_A_box_mellin_H_integral434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (T : ℝ) :
    let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
      Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    Integrable (parityOriginalSignedSourceMellinHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁ rho) μ ∧
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T =
      ∫ ξ, parityOriginalSignedSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ ∂μ := by
  dsimp only
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  have hBase := parity_original_signed_A_box_eq_H_integral434
    d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ T
  have hEq (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
      sourceOriginalPureMellinPhase434 rho u *
        parityOriginalSignedSourceFourierHAtU434
          d L E u signed band slot K alpha q χ σ₀ σ₁ ξ =
      parityOriginalSignedSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ := by
    rw [←parity_original_signed_full_source_integrand_eq_H434
      d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ ξ]
    exact parity_original_signed_source_mellin_H_integrand_exact434
      d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ rho ξ
  have hInt : Integrable
      (parityOriginalSignedSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ rho) μ :=
    (hBase.1.const_mul _).congr (Filter.Eventually.of_forall hEq)
  refine ⟨hInt,?_⟩
  rw [hBase.2]
  rw [←integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall hEq)
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedBilinearMellinHBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The genuine original signed ε=1/E physical h=-2 B590 Fourier-box bilinear
with nonzero Mellin phase u^(i rho), where u=mn-2 on its actual
positive source carrier. This is the source B590 sum, not a fabricated
separable alpha/beta twist. -/
def parityOriginalShiftTwoSignedBilinearMellinFourierBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- The exact **physical** e-only × H(vStar) nonzero-Mellin rho
representation after integrating genuine B590 f0/f1 source Fourier
gates over the real N-dimensional box and summing all original
shift-two factorizations mn=u+2. Source W1/P odd parity and
reserved prime are carried in actual native H(vStar). -/
def parityOriginalShiftTwoSignedBilinearMellinHBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalSignedSourceMellinHAtU434 d L E u signed band slot K α 1
          (1 : DirichletCharacter ℂ 1) 0 0 rho ξ *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2))
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- True ORIGINAL full-source h=-2 alpha beta B590 Fourier BOX
bilinear equality to selected e^(i rho) × physical v^(i rho) H_0(vStar)
for ANY real Mellin frequency rho. Every original Q/P W1/parity
factor and all alpha_m beta_n remain literal, with 20! factorial
normalization once and real product Lebesgue Fubini. The source
B590 frequency box is not evaluated at ξ=0. The separate Mellin
inversion of Psi, historical epsilon, and nonzero reserved p^(iσ)
are still distinct mathematical obligations. -/
theorem parity_original_hminus2_signed_bilinear_mellin_fourier_box_eq_source_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinFourierBox434 d L E band slot
      Psi K J α β signed rho Y T =
    parityOriginalShiftTwoSignedBilinearMellinHBox434 d L E band slot
      Psi K J α β signed rho Y T := by
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let H := fun (u : ℕ) (ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
    parityOriginalSignedSourceMellinHAtU434 d L E u signed band slot K α 1
      (1 : DirichletCharacter ℂ 1) 0 0 rho ξ
  let C : ℕ → ℂ := fun u =>
    (Psi ((u:ℝ)/Real.exp L):ℂ) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)
  have hPos (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) : u ≠ 0 := by
    exact (Finset.mem_Ioc.mp hu).1.ne'
  have hA (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (H u) μ ∧
      sourceOriginalPureMellinPhase434 rho u *
        parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T =
        ∫ ξ, H u ξ ∂μ :=
    parity_original_signed_A_box_mellin_H_integral434
      d L E hL hd u (hPos u hu) signed band slot K α 1
        (1 : DirichletCharacter ℂ 1) 0 0 rho T
  have hInt (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (fun ξ => H u ξ * C u) μ :=
    (hA u hu).1.mul_const _
  unfold parityOriginalShiftTwoSignedBilinearMellinFourierBox434
    parityOriginalShiftTwoSignedBilinearMellinHBox434
  calc
    (∑ u ∈ Finset.Ioc 0 Y,
      (sourceOriginalPureMellinPhase434 rho u *
        parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2)) =
      ∑ u ∈ Finset.Ioc 0 Y, ∫ ξ, H u ξ * C u ∂μ := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [integral_mul_const, ←(hA u hu).2]
        ring
    _ = ∫ ξ, ∑ u ∈ Finset.Ioc 0 Y, H u ξ * C u ∂μ :=
      (integral_finsetSum (Finset.Ioc 0 Y) hInt).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [H,C]
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedMellinOddJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- True ORIGINAL odd-projector h=-2 source B590 Fourier BOX with
arbitrary nonseparable Mellin rho on u=mn-2 is exactly HALF the
difference of the two INDEPENDENT signed ε=1,E original B590
Fourier BOX h=-2 bilinears. The splitting occurs before Cauchy
and works for every rho because the same u^(i rho) is applied to
both signed branches. No artificial alpha_m beta_n separation. -/
theorem parity_original_hminus2_odd_mellin_box_eq_signed_half_difference434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearMellinFourierBox434
      d L E band slot Psi K J α β rho Y T =
      (parityOriginalShiftTwoSignedBilinearMellinFourierBox434
         d L E band slot Psi K J α β false rho Y T -
       parityOriginalShiftTwoSignedBilinearMellinFourierBox434
         d L E band slot Psi K J α β true rho Y T)/2 := by
  unfold parityOriginalShiftTwoBilinearMellinFourierBox434
    parityOriginalShiftTwoSignedBilinearMellinFourierBox434
  rw [←Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_B590_odd_A_box_eq_signed_half_difference434]
  push_cast
  ring

/-- The true signed Parity ε=1/E physical H(vStar) bilinear Fourier
BOX representations combine into the original odd-projected B590
Fourier BOX after the nonzero Mellin frequency u^(i rho) has been
split into the selected e^(i rho) and physical v^(i rho) factors.
This is the exact SOURCE signed input bridge required to reason
about each Parity(4.17) correlation separately BEFORE squaring. -/
theorem parity_original_hminus2_odd_mellin_box_eq_signed_H_half_difference434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearMellinFourierBox434
      d L E band slot Psi K J α β rho Y T =
      (parityOriginalShiftTwoSignedBilinearMellinHBox434
         d L E band slot Psi K J α β false rho Y T -
       parityOriginalShiftTwoSignedBilinearMellinHBox434
         d L E band slot Psi K J α β true rho Y T)/2 := by
  rw [parity_original_hminus2_odd_mellin_box_eq_signed_half_difference434]
  rw [parity_original_hminus2_signed_bilinear_mellin_fourier_box_eq_source_H434
    d L E hL hd band slot Psi K J α β false rho Y T]
  rw [parity_original_hminus2_signed_bilinear_mellin_fourier_box_eq_source_H434
    d L E hL hd band slot Psi K J α β true rho Y T]

/-- **True original h=-2 odd source to TWO separate signed Parity
physical H(vStar) Fourier BOX branches with arbitrary real Mellin
rho, uniform direct all-log complex-norm error**:

`‖sourceOriginalA_rho - (B_H^(ε=1,rho)-B_H^(ε=E,rho))/2‖
  ≤ 2 Acoef Bcoef exp(L) L^-A`.

Both B_H branches are genuine SOURCE original full factorial Q/P
B590 f0/f1 Fourier BOX integrals, each with its own exactly
factored selected e^(i rho) coefficient times physical
v^(i rho) W1(P,v) ε(v) H_0(vStar); no parity projector is inserted
after squaring. The true original sourceOriginalA rho Rankin and
Schwartz Fourier errors are proved uniformly in rho and applied only
AFTER the signed source decomposition has been established exactly.

This is the strongest signed source-form original Parity(4.7) bridge so
far. It does NOT provide the separate signed original SOURCE-to-B590
Rankin all-log comparison (only the odd combination is bounded),
nonzero reserved prime σ from the real source transform, historical
postintegrated a_e, genuine all-character correlation Parity(4.17),
TypeII(4.2), sieve or terminal Green64.green_64. -/
theorem parity_eventually_original_hminus2_source_mellin_to_signed_H_boxes_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (rho : ℝ),
      ‖parityOriginalShiftTwoBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β rho
          ⌊2*Real.exp L⌋₊ -
        (parityOriginalShiftTwoSignedBilinearMellinHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β false rho ⌊2*Real.exp L⌋₊ L -
         parityOriginalShiftTwoSignedBilinearMellinHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β true rho ⌊2*Real.exp L⌋₊ L)/2‖ ≤
        2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_source_mellin_to_H_box_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  rw [←parity_original_hminus2_odd_mellin_box_eq_signed_H_half_difference434
    (sourceOriginalLiteralDepth 20 L) L E (by nlinarith [h.1]) rfl
      band slot Psi K J α β rho ⌊2*Real.exp L⌋₊ L]
  rw [parity_original_hminus2_bilinear_mellin_fourier_box_eq_source_H434
    (sourceOriginalLiteralDepth 20 L) L E (by nlinarith [h.1]) rfl
      band slot Psi K J α β rho ⌊2*Real.exp L⌋₊ L]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedMassBound -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The full ORIGINAL signed ε=1 source is exactly the unsigned
sourceOriginalA0 with its true W1(P,u) and original Q-band factorial
20! normalization. No odd projector or arbitrary Q count. -/
theorem parity_original_signed_false_source_eq_A0434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (u : ℕ) :
    parityOriginalSignedSourceA434 d L false u =
    sourceOriginalA0 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u := by
  have hp : ∀ b p, p ∈ sourceOriginalQActualBands 20 d L b → p.Prime :=
    source_original_Q_actual_prime 20 d L
  have hd : ∀ b c p,
      p ∈ sourceOriginalQActualBands 20 d L b →
      p ∈ sourceOriginalQActualBands 20 d L c → b=c :=
    source_original_Q_actual_all_disjoint 20 d L (by norm_num) hL
  have hCoeff := parity_source_original_ordinary_coefficient_full_labelled434
    20 (sourceOriginalQActualBands 20 d L)
    (sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    hp hd
  unfold parityOriginalSignedSourceA434
  unfold sourceOriginalA0
  rw [hCoeff,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  unfold parityActualOriginalSignedFullTupleWeight434
  by_cases hGate : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hGate]
    rw [show parityOriginalPSignedEpsilon434
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) false u = 1 by rfl]
    ring
  · simp only [if_neg hGate, mul_zero]

/-- The UNSIGNED source Q-factorial mass is nonnegative and ≤ the
literal original W1(P,u), by existing source original ordinary
coefficient ≤1. This is stronger than the odd projected A(u) bound
and needed for signed ε=E absolute Rankin. -/
theorem parity_original_signed_false_A_le_W1434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (u : ℕ) :
    0 ≤ parityOriginalSignedSourceA434 d L false u ∧
    parityOriginalSignedSourceA434 d L false u ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
  rw [parity_original_signed_false_source_eq_A0434 d L hL u]
  constructor
  · exact source_original_A0_nonneg 20
      (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u
  · unfold sourceOriginalA0
    exact mul_le_of_le_one_right
      (source_original_W1_nonneg (sourceOriginalPAllActualBands 20 L) u)
      (source_original_ordinary_le_one 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u))

/-- The independent signed Q labelled source weight is exactly its
nonnegative ε=1 weight times the true common sign ε(P,u). The
factorial normalized Q gate is identical in both. -/
theorem parity_original_signed_full_tuple_weight_eq_false_mul_sign434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    parityActualOriginalSignedFullTupleWeight434 d L u signed f =
      parityActualOriginalSignedFullTupleWeight434 d L u false f *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed u := by
  unfold parityActualOriginalSignedFullTupleWeight434
  by_cases hg : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hg]
    rw [show parityOriginalPSignedEpsilon434
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) false u = 1 by rfl]
    ring
  · simp only [if_neg hg, zero_mul]


/-- TRUE ε=1 original full-Q factorial labelled branch weight is
nonnegative even for repeated Q primes and any original P parity.
No odd projector is present. -/
theorem parity_original_signed_false_full_tuple_nonneg434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    0 ≤ parityActualOriginalSignedFullTupleWeight434 d L u false f := by
  unfold parityActualOriginalSignedFullTupleWeight434
  by_cases hg : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hg]
    rw [show parityOriginalPSignedEpsilon434
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) false u = 1 by
        rfl]
    rw [mul_one]
    exact mul_nonneg
      (Finset.prod_nonneg (by intro j hj; positivity))
      (source_original_W1_nonneg (sourceOriginalPAllActualBands 20 L) u)
  · simp only [if_neg hg]; exact le_refl (0:ℝ)

/-- Exact ABSOLUTE value of ANY SOURCE signed ε=1 or ε=E
full-Q tuple weight equals its unsigned normalized original
Q factorial weight. This is necessary because ε=E is NOT a
nonnegative source. -/
theorem parity_original_signed_tuple_weight_abs_eq_false434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    |parityActualOriginalSignedFullTupleWeight434 d L u signed f| =
      parityActualOriginalSignedFullTupleWeight434 d L u false f := by
  rw [parity_original_signed_full_tuple_weight_eq_false_mul_sign434]
  rw [abs_mul,abs_of_nonneg (parity_original_signed_false_full_tuple_nonneg434
    d L u f),parity_original_P_signed_epsilon_abs_one434,mul_one]

/-- Each independent signed Parity branch's FULL factorial-labelled
original Q SOURCE TOTAL VARIATION is ≤ the actual original W1(P,u)
WITHOUT an extra 2^N or (20!)^(d+1). This follows from original A0,
not the odd projector. -/
theorem parity_original_signed_full_Q_total_variation_le_W1434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (u : ℕ) (signed : Bool) :
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        |parityActualOriginalSignedFullTupleWeight434 d L u signed f|) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
  simp_rw [parity_original_signed_tuple_weight_abs_eq_false434]
  exact (parity_original_signed_false_A_le_W1434 d L hL u).2
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedBufferDefect -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The ORIGINAL independent signed Parity ε=1 or ε=E B590 full-Q
allocation mass defect, with every original factorial Q tuple,
actual history-dependent B590 gate and source sign. This may be
negative for ε=E, unlike the odd-projected defect. -/
def parityOriginalSignedFullQBufferDefectAtU434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (signed : Bool) (u : ℕ) : ℝ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
    {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    parityActualOriginalSignedFullTupleWeight434 d L u signed f *
      (1-parityActualOriginalAFullTupleAllocationMass434 d L E band slot f)

/-- The genuine original signed ε=1/E B590 buffer defect is
absolutely bounded by original W1(P,u), without the NONNEGATIVITY
of the signed ε=E contribution. The argument uses original A0
factorial Q mass <= W1, |ε|=1, and the true B590 branch mass
0<=M<=1. This is the source counterpart of the odd projector
Rankin domination, proved for each signed branch INDIVIDUALLY. -/
theorem parity_original_signed_buffer_defect_abs_le_W1434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20) (signed : Bool) (u : ℕ) :
    |parityOriginalSignedFullQBufferDefectAtU434
      d L E band slot signed u| ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
  let W := fun f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) =>
    parityActualOriginalSignedFullTupleWeight434 d L u signed f
  let M := fun f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) =>
    parityActualOriginalAFullTupleAllocationMass434 d L E band slot f
  have hMass (f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})) :
      0 ≤ 1-M f ∧ 1-M f ≤ 1 := by
    have ha := parity_actual_original_A_full_tuple_allocation_mass_le_one434
      d L E band slot f
    exact ⟨by linarith [ha.2], by linarith [ha.1]⟩
  unfold parityOriginalSignedFullQBufferDefectAtU434
  change |∑ f, W f*(1-M f)| ≤ _
  rw [←Real.norm_eq_abs]
  calc
    ‖∑ f, W f*(1-M f)‖ ≤ ∑ f, ‖W f*(1-M f)‖ := norm_sum_le _ _
    _ ≤ ∑ f, |W f| := by
      apply Finset.sum_le_sum
      intro f hf
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hMass f).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hMass f).2
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
      parity_original_signed_full_Q_total_variation_le_W1434 d L hL u signed

/-- On the original SOURCE β/4-retained Ppart and actual original
Q-prime product gate, EVERY separate signed ε=1 or ε=E B590
allocation defect vanishes at u. There is no cancellation among
signed Q tuples: each normalized original Q tuple has either zero
weight or total B590 branch mass exactly one. -/
theorem parity_original_signed_buffer_defect_retained_zero434
    (beta : ℝ) (hbeta : 0 < beta)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-beta)*L))
    (u : ℕ) (hu : u ≠ 0) (hLarge : Real.exp L ≤ (u:ℝ))
    (hPcap : parityOriginalPhysicalPcapBeta434 beta L u)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4)
    (slot : Fin 20) (signed : Bool) :
    parityOriginalSignedFullQBufferDefectAtU434
      d L E band slot signed u = 0 := by
  have hMem : sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
      sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ :=
    (parity_actual_original_beta_Pcap_mem434 beta L u).2 hPcap
  unfold parityOriginalSignedFullQBufferDefectAtU434
  apply Finset.sum_eq_zero
  intro f hf
  by_cases hQ : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · rw [parity_original_beta_retained_full_Q_tuple_B590_mass_one434
      beta hbeta d L E hL hElo hEhi u hu hLarge hMem f hQ band hBand slot]
    ring
  · unfold parityActualOriginalSignedFullTupleWeight434
    simp only [if_neg hQ,zero_mul]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedBufferBilinear -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- Genuine independent signed Parity ε=1/E original full-Q B590
allocation error after summing all actual h=-2 pairs mn=u+2,
real Psi and nonzero Mellin rho source u=mn-2. No sign is absorbed
into alpha_m or beta_n and every original 20! Q label is retained. -/
def parityOriginalSignedShiftTwoBilinearMellinBufferError434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    (sourceOriginalPureMellinPhase434 rho u *
      (((parityOriginalSignedFullQBufferDefectAtU434
         d L E band slot signed u * Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))) *
    (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      α z.1*β z.2)

/-- True SOURCE Parity signed ε=1/E pre-Cauchy B590 smooth allocation
error is controlled by the SAME original discarded-Ppart W1τ mass
as the old odd-projected buffer, for ANY Mellin rho. The signed E
branch is NOT nonnegative, hence the proof explicitly uses its
independent original Q factorial TOTAL VARIATION≤W1(P,u) and the
retained β/4 Ppart signed defect ZERO at each u with Ψ≠0.

No false pointwise τ(u+2)≤polylog and no sqrt(correlation) estimate. -/
theorem parity_original_signed_mellin_buffer_pre_cauchy_tau434
    (betaP : ℝ) (hbetaP : 0 < betaP)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-betaP)*L))
    (Psi : ℝ → ℝ)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsi0 : ∀ t, 0 ≤ Psi t) (hPsi1 : ∀ t, Psi t ≤ 1)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ betaP/4)
    (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ m ∈ K, ‖α m‖ ≤ A)
    (hβ : ∀ n ∈ J, ‖β n‖ ≤ B)
    (signed : Bool) (rho : ℝ) :
    ‖parityOriginalSignedShiftTwoBilinearMellinBufferError434
      d L E band slot Psi K J α β signed rho (⌊2*Real.exp L⌋₊)‖ ≤
      A*B*(∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := by
  let Y := ⌊2*Real.exp L⌋₊
  let D := parityOriginalSignedFullQBufferDefectAtU434 d L E band slot signed
  let C := fun u => ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
    α z.1 * β z.2
  have hD (u : ℕ) : |D u| ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
    parity_original_signed_buffer_defect_abs_le_W1434 d L E hL band slot signed u
  have hRetained (u : ℕ) (hLarge : Real.exp L ≤ (u:ℝ))
      (hCap : parityOriginalPhysicalPcapBeta434 betaP L u) : D u = 0 := by
    have hu : u ≠ 0 := by
      intro hz
      subst u
      have hp := Real.exp_pos L
      norm_num at hLarge
      linarith
    exact parity_original_signed_buffer_defect_retained_zero434
      betaP hbetaP d L E hL hElo hEhi u hu hLarge hCap
      band hBand slot signed
  have hTerm (u : ℕ) (hu : u ∈ Finset.range (Y+1)) :
      ‖sourceOriginalPureMellinPhase434 rho u *
         (((D u * Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)) * C u‖ ≤
      A*B*(if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := by
    rw [norm_mul,norm_mul,source_original_pure_mellin_phase_norm_one434,one_mul]
    have hC := parity_original_shift_two_bilinear_fibre_norm_le_tau434
      K J u α β A B hA hB hα hβ
    have hPsiPos := hPsi0 ((u:ℝ)/Real.exp L)
    have hPsiHi := hPsi1 ((u:ℝ)/Real.exp L)
    by_cases hCap : parityOriginalPhysicalPcapBeta434 betaP L u
    · by_cases hPsiZero : Psi ((u:ℝ)/Real.exp L)=0
      · simp [hCap,hPsiZero]
      · have hS : ((u:ℝ)/Real.exp L) ∈ Set.Icc (1:ℝ) 2 :=
          hSupport (by simpa [Function.mem_support] using hPsiZero)
        have huLarge : Real.exp L ≤ (u:ℝ) := by
          have hExp : 0 < Real.exp L := Real.exp_pos _
          have h := (le_div_iff₀ hExp).mp hS.1
          simpa only [one_mul] using h
        have hZero := hRetained u huLarge hCap
        simp [hCap,hZero]
    · simp only [if_neg hCap]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,
        abs_of_nonneg hPsiPos]
      have hProd : |D u| * Psi ((u:ℝ)/Real.exp L) ≤
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
        calc
          _ ≤ |D u| := mul_le_of_le_one_right (abs_nonneg _) hPsiHi
          _ ≤ _ := hD u
      calc
        _ ≤ (|D u| * Psi ((u:ℝ)/Real.exp L)) *
            (((u+2).divisors.card:ℝ)*A*B) :=
              mul_le_mul_of_nonneg_left hC
                (mul_nonneg (abs_nonneg _) hPsiPos)
        _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            (((u+2).divisors.card:ℝ)*A*B) :=
              mul_le_mul_of_nonneg_right hProd (by positivity)
        _ = A*B*(sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            ((u+2).divisors.card:ℝ)) := by ring
  unfold parityOriginalSignedShiftTwoBilinearMellinBufferError434
  let W : ℕ → ℂ := fun u =>
    (sourceOriginalPureMellinPhase434 rho u *
      (((D u*Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)))*C u
  have hTriangle := norm_sum_le (Finset.range (Y+1)) W
  calc
    _ ≤ ∑ u ∈ Finset.range (Y+1), ‖W u‖ := hTriangle
    _ ≤ ∑ u ∈ Finset.range (Y+1),
        A*B*(if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
          else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := Finset.sum_le_sum hTerm
    _ = _ := by rw [←Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedBufferAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Individually signed Parity(4.7) ε=1 or ε=E ORIGINAL full
20!-labelled source B590 allocation buffer error before Cauchy:
for arbitrary fixed beta>0 and requested inverse-log A, every
physical reserved band, every bounded original alpha_m beta_n
with true mn=u+2 and EVERY Mellin rho, the signed buffer error is
≤Acoef Bcoef exp(L)L^-A. This uses native original signed total
variation ≤W1(P,u), retained beta/4 Ppart defect ZERO, and genuine
shifted fourth-divisor Rankin; no nonnegativity or odd-projector
replacement for ε=E, and no false alpha_m beta_n separability.
This closes the SOURCE allocation error for each signed branch,
not by itself the entire source-to-signed-H Fourier inverse.
-/
theorem parity_eventually_original_hminus2_signed_mellin_buffer_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool) (rho : ℝ),
      ‖parityOriginalSignedShiftTwoBilinearMellinBufferError434
        (sourceOriginalLiteralDepth 20 L) L E band slot
        Psi K J α β signed rho (⌊2*Real.exp L⌋₊)‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_beta_Pcap_discard_W1_shifted_tau_all_log434
      betaP A hbetaP,
    parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ] with
    L hRankin hDepth
  refine ⟨hRankin.1,hDepth,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  have hLp : 0 < L := by nlinarith [hRankin.1]
  have hActual : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ betaP/4 := by
    rw [hb]; exact hBand
  have hPre := parity_original_signed_mellin_buffer_pre_cauchy_tau434
    betaP hbetaP (sourceOriginalLiteralDepth 20 L) L E hLp
    hElo hEhi Psi hSupport hPsi0 hPsi1 band hActual slot
    K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  have hRange := parity_original_beta_shifted_tau_Pcap_range_eq_Ioc434
    betaP L hbetaP (le_of_lt hLp) ⌊2*Real.exp L⌋₊
  have hIte :
      (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) =
      (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        (if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
         else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
          ((u+2).divisors.card:ℝ)) := by
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hc : parityOriginalPhysicalPcapBeta434 betaP L u <;> simp [hc]
  rw [hIte,hRange] at hPre
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hAcoef hBcoef
  calc
    _ ≤ (Acoef*Bcoef)*
      (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        (if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
          else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u)*
          ((u+2).divisors.card:ℝ)) := hPre
    _ ≤ (Acoef*Bcoef)*(Real.exp L*L^(-A)) :=
      mul_le_mul_of_nonneg_left hRankin.2 hAB
    _ = Acoef*Bcoef*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEWindowAbsolute -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal independently signed Parity epsilon=1 or epsilon=E original
full-factorial source outside the HISTORICAL selected e window.
The weight is the actual signed Q/P original tuple, not the odd projector.
The Fourier box is real [-T,T]^N, not a fictitious pointwise cutoff. -/
def parityOriginalSignedB590OutsideEAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ) *
      (∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434
        d L E band slot f,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot f i).val) T)

/-- The TRUE full-Q factorial mass gives the same absolute outside
Fourier variation for BOTH signs, with no factor counting Q tuples.
This is a direct bound for the signed source before Cauchy, and does
not use any cancellation of the two branches of the odd projector. -/
theorem parity_original_signed_outside_e_box_norm_le_W1_variation434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    ‖parityOriginalSignedB590OutsideEAtU434 d L E u signed band slot T‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalB590FourierBranchVariation434 δ) := by
  let F := ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let V : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool,
    parityOriginalB590FourierBranchVariation434 δ
  let w : F → ℝ := fun f => parityActualOriginalSignedFullTupleWeight434 d L u signed f
  let B : F → ℂ := fun f =>
    ∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434 d L E band slot f,
      parityOriginalB590AllGateFourierBox434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) δ
        (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) T
  have hV : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg
      (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hTerm (f : F) : ‖((w f:ℝ):ℂ)*B f‖ ≤ |w f| * V := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (parity_original_B590_fullQ_outside_e_fourier_box_norm_le_variation434
        d L E band slot f T) (abs_nonneg (w f))
  have hSum : (∑ f : F, |w f|) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
    parity_original_signed_full_Q_total_variation_le_W1434 d L hL u signed
  unfold parityOriginalSignedB590OutsideEAtU434
  change ‖∑ f : F, ((w f:ℝ):ℂ)*B f‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * V
  calc
    _ ≤ ∑ f : F, ‖((w f:ℝ):ℂ)*B f‖ := norm_sum_le _ _
    _ ≤ ∑ f : F, |w f| * V := by
      apply Finset.sum_le_sum
      intro f hf
      exact hTerm f
    _ = (∑ f : F, |w f|)*V := by rw [Finset.sum_mul]
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u*V :=
      mul_le_mul_of_nonneg_right hSum hV
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEWindowRetained -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- REAL historical Parity (4.5) retained beta/4 physical P-primepart
support controls the original e-window Fourier leakage for each of
the two signed epsilon=1/E Q/P sources individually, not merely
for the odd projector. The true original f0/f1 truncated Fourier
gate may be nonzero outside the source e window; its norm is paid
by actual Schwartz Fourier tails and actual Q-product capacity.
The source factorial total variation is <=W1 without a Q-count. -/
theorem parity_eventually_original_signed_retained_e_window_le_W1_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (u : ℕ), Real.exp L ≤ (u:ℝ) →
        sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
          sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20) (signed : Bool),
      ‖parityOriginalSignedB590OutsideEAtU434
         (sourceOriginalLiteralDepth 20 L) L E u signed band slot L‖ ≤
         sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * L^(-A) := by
  filter_upwards [parity_eventually_original_B590_fullQ_outside_e_fourier_box_all_log434 A,
    parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ]
    with L hWin hDepth
  refine ⟨hWin.1,hDepth,?_⟩
  intro E hE hEcap u hLarge hPcap band hb slot signed
  let d := sourceOriginalLiteralDepth 20 L
  let F := ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let w : F → ℝ := fun f => parityActualOriginalSignedFullTupleWeight434 d L u signed f
  let S : F → ℂ := fun f =>
      ∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434 d L E band slot f,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) L
  have hLp : 0 < L := by linarith [hWin.1]
  have hu : u ≠ 0 := by
    intro he
    subst u
    norm_num at hLarge
    linarith [Real.exp_pos L]
  have hBandSmall : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ beta/4 := by
    rw [hb]
    exact hBand
  have hTerm (f : F) : ‖((w f:ℝ):ℂ)*S f‖ ≤ |w f| * L^(-A) := by
    by_cases hFull : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
        sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    · have hMass := parity_actual_original_full_Q_tuple_beta_E_source_mass434
        beta hbeta d L hLp.le E hEcap u hu hLarge hPcap
        f hFull band hBandSmall slot
      have hC := hWin.2 E hE band slot f hMass
      dsimp only [S]
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hC (abs_nonneg (w f))
    · have hz : w f=0 := by
        unfold w parityActualOriginalSignedFullTupleWeight434
        simp only [if_neg hFull]
      rw [hz]
      simp
  have hBound : (∑ f : F, |w f|) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
    parity_original_signed_full_Q_total_variation_le_W1434 d L hLp u signed
  have hPow : 0 ≤ L^(-A) := Real.rpow_nonneg hLp.le _
  unfold parityOriginalSignedB590OutsideEAtU434
  change ‖∑ f : F, ((w f:ℝ):ℂ)*S f‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * L^(-A)
  calc
    _ ≤ ∑ f : F, ‖((w f:ℝ):ℂ)*S f‖ := norm_sum_le _ _
    _ ≤ ∑ f : F, |w f| * L^(-A) := by
      apply Finset.sum_le_sum
      intro f hf
      exact hTerm f
    _ = (∑ f : F, |w f|)*L^(-A) := by rw [Finset.sum_mul]
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u * L^(-A) :=
      mul_le_mul_of_nonneg_right hBound hPow
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEWindowPsiPointwise -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- TRUE, INDIVIDUALLY SIGNED original Parity(4.5) Fourier-box e-window truncation loss at a
single SOURCE integer u, with real Ψ supported [1,2], 0<=Ψ<=1. The sign is fixed BEFORE the box/square and bounded via exact factorial absolute mass.
The retained beta/4 Ppart receives arbitrary L^-A saving; the
DISCARDED Ppart receives only its honest total Fourier variation.
One must not assume e-support at each fixed Fourier ξ or impose
Q-product capacity on discarded Pparts. This is the literal pointwise
bridge required before summing the complete alpha_m beta_n bilinear
source over mn=u+2. -/
theorem parity_eventually_original_signed_outside_e_Psi_pointwise_bound434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (u : ℕ)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20) (signed : Bool),
      ‖parityOriginalSignedB590OutsideEAtU434
          (sourceOriginalLiteralDepth 20 L) L E u signed band slot L *
          (Psi ((u:ℝ)/Real.exp L) : ℂ)‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        (L^(-A) +
          if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ) else
            ∑ δ : Fin (sourceOrderedLabels 20
              (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length → Bool,
              parityOriginalB590FourierBranchVariation434 δ) := by
  filter_upwards [parity_eventually_original_signed_retained_e_window_le_W1_all_log434
      beta A hbeta jQ hBand] with L hRetained
  refine ⟨hRetained.1,hRetained.2.1,?_⟩
  intro E hE hEcap Psi hSupport hPsi0 hPsi1 u band hb slot signed
  let d := sourceOriginalLiteralDepth 20 L
  let W := sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u
  let D := parityOriginalSignedB590OutsideEAtU434 d L E u signed band slot L
  let V : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      parityOriginalB590FourierBranchVariation434 δ
  let psi := Psi ((u:ℝ)/Real.exp L)
  have hLp : 0 < L := by linarith [hRetained.1]
  have hW : 0 ≤ W := source_original_W1_nonneg _ _
  have hA : 0 ≤ L^(-A) := Real.rpow_nonneg hLp.le _
  have hV : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hPsiPos : 0 ≤ psi := hPsi0 _
  have hPsiUp : psi ≤ 1 := hPsi1 _
  have hScalar : ‖(psi:ℂ)‖ = psi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hPsiPos]
  have hPos : 0 ≤ W*(L^(-A)+(if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ) else V)) := by
    apply mul_nonneg hW
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · simpa [hc] using hA
    · simpa [hc] using add_nonneg hA hV
  by_cases hZero : psi=0
  · rw [norm_mul,hScalar,hZero,mul_zero]
    exact hPos
  · have hMem : ((u:ℝ)/Real.exp L) ∈ Set.Icc (1:ℝ) 2 :=
      hSupport (by simpa [Function.mem_support,psi] using hZero)
    have hLarge : Real.exp L ≤ (u:ℝ) := by
      have hp := Real.exp_pos L
      have h := (le_div_iff₀ hp).mp hMem.1
      simpa only [one_mul] using h
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · have hPcap : sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u ∈
          sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ :=
        (parity_actual_original_beta_Pcap_mem434 beta L u).2 hc
      have hD := hRetained.2.2 E hE hEcap u hLarge hPcap band hb slot signed
      rw [norm_mul,hScalar]
      have hBound : ‖D‖*psi ≤ W*L^(-A) :=
        (mul_le_mul_of_nonneg_right hD hPsiPos).trans
          (mul_le_of_le_one_right (mul_nonneg hW hA) hPsiUp)
      simpa only [if_pos hc, add_zero] using hBound
    · have hD := parity_original_signed_outside_e_box_norm_le_W1_variation434
        d L E hLp u signed band slot L
      rw [norm_mul,hScalar]
      have hBound : ‖D‖*psi ≤ W*V :=
        (mul_le_mul_of_nonneg_right hD hPsiPos).trans
          (mul_le_of_le_one_right (mul_nonneg hW hV) hPsiUp)
      have hMon : W*V ≤ W*(L^(-A)+V) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) hW
      simpa only [if_neg hc] using hBound.trans hMon
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEWindowPreCauchy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Individually signed TRUE historical Parity(4.5) OUTSIDE selected-e window on the
ORIGINAL h=-2 B590 Fourier box: all 20! Q prime labelled tuples,
W1, independent epsilon=1/E multiplicity parity, Psi and the true mn=u+2 alpha/beta.
No proxy e-support assumption: outside branches are kept as the actual
truncated Fourier integrals (which need not be zero individually). -/
def parityOriginalShiftTwoSignedBilinearMellinOutsideEBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (sourceOriginalPureMellinPhase434 rho u *
    (parityOriginalSignedB590OutsideEAtU434 d L E u signed band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ))) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- TRUE individually signed outside-e-box pre-Cauchy bound after summing all h=-2
alpha_m beta_n factorisations. The retained beta/4 source Ppart has
arbitrary small L^-A leakage; the discarded part has only its honest
source Fourier-variation times the exact W1(u)tau(u+2) mass.
This is a bound on a literal COMPLEX source bilinear difference, not
an unconnected variation budget or artificial zero of Fourier gates. -/
theorem parity_eventually_original_signed_hminus2_mellin_outside_e_box_pre_cauchy434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool) (rho : ℝ),
      ‖parityOriginalShiftTwoSignedBilinearMellinOutsideEBox434
        (sourceOriginalLiteralDepth 20 L) L E band slot Psi K J α β signed rho
        ⌊2*Real.exp L⌋₊ L‖ ≤
      Acoef*Bcoef *
        ((L^(-A)) *
          (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
            sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            ((u+2).divisors.card:ℝ)) +
        (∑ δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool,
          parityOriginalB590FourierBranchVariation434 δ) *
        (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
          (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
            else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
            ((u+2).divisors.card:ℝ))) := by
  filter_upwards [parity_eventually_original_signed_outside_e_Psi_pointwise_bound434
    beta A hbeta jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro E hE hEcap Psi hSupport hPsi0 hPsi1 band hb slot
    K J α β Acoef Bcoef hA hB hα hβ signed rho
  let Y := ⌊2*Real.exp L⌋₊
  let w : ℕ → ℝ := fun u => sourceOriginalW1
    (sourceOriginalPAllActualBands 20 L) u
  let t : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length → Bool,
    parityOriginalB590FourierBranchVariation434 δ
  let c : ℕ → ℝ := fun u => if parityOriginalPhysicalPcapBeta434 beta L u then 0 else t
  let Q : ℕ → ℂ := fun u => parityOriginalSignedB590OutsideEAtU434
    (sourceOriginalLiteralDepth 20 L) L E u signed band slot L *
    (Psi ((u:ℝ)/Real.exp L):ℂ)
  let F : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      α z.1*β z.2
  have hU (u : ℕ) : ‖Q u‖ ≤ w u*(L^(-A)+c u) :=
    h.2.2 E hE hEcap Psi hSupport hPsi0 hPsi1 u band hb slot signed
  have hF (u : ℕ) : ‖F u‖ ≤
      ((u+2).divisors.card:ℝ)*Acoef*Bcoef :=
    parity_original_shift_two_bilinear_fibre_norm_le_tau434 K J u
      α β Acoef Bcoef hA hB hα hβ
  have hw (u : ℕ) : 0 ≤ w u := source_original_W1_nonneg _ _
  have ht : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hPow : 0 ≤ L^(-A) := Real.rpow_nonneg (by linarith [h.1]) _
  have hc (u : ℕ) : 0 ≤ c u := by
    dsimp [c]
    split <;> positivity
  have hterm (u : ℕ) :
      ‖(sourceOriginalPureMellinPhase434 rho u*Q u)*F u‖ ≤ Acoef*Bcoef *
        (w u * ((u+2).divisors.card:ℝ) * (L^(-A)+c u)) := by
    rw [norm_mul,norm_mul,source_original_pure_mellin_phase_norm_one434,one_mul]
    have hn : 0 ≤ (w u*(L^(-A)+c u)) :=
      mul_nonneg (hw u) (add_nonneg hPow (hc u))
    have hn2 : 0 ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef := by positivity
    calc
      _ ≤ (w u*(L^(-A)+c u))*
          (((u+2).divisors.card:ℝ)*Acoef*Bcoef) :=
        mul_le_mul (hU u) (hF u) (norm_nonneg _) hn
      _ = _ := by ring
  unfold parityOriginalShiftTwoSignedBilinearMellinOutsideEBox434
  calc
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        ‖(sourceOriginalPureMellinPhase434 rho u*Q u)*F u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        Acoef*Bcoef*(w u*((u+2).divisors.card:ℝ)*(L^(-A)+c u)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hterm u
    _ = Acoef*Bcoef *
        (∑ u ∈ Finset.Ioc 0 Y, w u*((u+2).divisors.card:ℝ)*(L^(-A)+c u)) := by
      rw [Finset.mul_sum]
    _ = Acoef*Bcoef *
        (L^(-A)*(∑ u ∈ Finset.Ioc 0 Y,
          w u*((u+2).divisors.card:ℝ)) +
         t*(∑ u ∈ Finset.Ioc 0 Y,
          (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
            else w u)*((u+2).divisors.card:ℝ))) := by
      congr 1
      have hSplit (u : ℕ) :
          w u * ((u+2).divisors.card:ℝ) * (L^(-A)+c u) =
          L^(-A)*(w u*((u+2).divisors.card:ℝ)) +
          t*((if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
              else w u)*((u+2).divisors.card:ℝ)) := by
        by_cases hp : parityOriginalPhysicalPcapBeta434 beta L u
        · simp [c,hp]
          ring
        · simp [c,hp]
          ring
      conv_lhs =>
        arg 2
        ext u
        rw [hSplit u]
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEWindowAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- FULL unconditional separate SIGNED original Parity §4.2 (4.5) source e-window
truncation: the ACTUAL h=-2 complex α_m β_n Fourier-BOX contribution
from selected e OUTSIDE `[E*L^-88,E]` is negligible with arbitrary
inverse-log precision, uniformly in all original reserved Q slots and
all originally allowed `1≤E≤exp((1-beta)L)`.
The retained beta/4 original Ppart uses true real f0/f1 gate support,
and outside window the truncated integral is bounded by Fourier tails,
not assumed zero. The discarded Ppart gets the original weighted
shifted-divisor Rankin estimate times genuine Fourier variation. All
original factorial W1/P parity and source `mn=u+2` factors are kept.
The constant 2 is explicit; accuracy A and beta are arbitrary fixed
parameters. This establishes support truncation for the integrated
source object, NOT pointwise ξ support or finished Parity(4.7) a_e. -/
theorem parity_eventually_original_signed_hminus2_mellin_outside_e_fourier_box_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool) (rho : ℝ),
      ‖parityOriginalShiftTwoSignedBilinearMellinOutsideEBox434
        (sourceOriginalLiteralDepth 20 L) L E band slot Psi K J α β signed rho
        ⌊2*Real.exp L⌋₊ L‖ ≤
        2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  let D := parityOriginalOutsideEBoxRetainedAccuracy434 A
  let R := parityOriginalOutsideEBoxDiscardAccuracy434 A
  filter_upwards [parity_eventually_original_signed_hminus2_mellin_outside_e_box_pre_cauchy434
      beta D hbeta jQ hBand,
    parity_eventually_original_W1_shifted_tau_total_mass_polylog434,
    parity_eventually_original_beta_Pcap_discard_W1_shifted_tau_all_log434
      beta R hbeta,
    parity_eventually_original_B590_actual_full_fourier_variation_polylog434]
    with L hPre hTotal hDiscard hVariation
  refine ⟨hPre.1,hPre.2.1,?_⟩
  intro E hE hEcap Psi hSupport hPsi0 hPsi1 band hb slot
    K J α β Acoef Bcoef hA hB hα hβ signed rho
  let Y := ⌊2*Real.exp L⌋₊
  let M : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
    ((u+2).divisors.card:ℝ)
  let V : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length → Bool, parityOriginalB590FourierBranchVariation434 δ
  let B : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
     else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
     ((u+2).divisors.card:ℝ)
  have hLp : 0 < L := by linarith [hPre.1]
  have hMass : M ≤ Real.exp L*L^parityOriginalW1PolylogExponent434*L^16 := hTotal
  have hV : V ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 :=
    hVariation band slot
  have hDiscardBound : B ≤ Real.exp L*L^(-R) := hDiscard.2
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hVnonneg : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro u hu
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · simp [hc]
    · simp only [if_neg hc]
      exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hD0 : 0 ≤ L^(-D) := Real.rpow_nonneg hLp.le _
  have hR0 : 0 ≤ L^(-R) := Real.rpow_nonneg hLp.le _
  have hCF0 : 0 ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 :=
    Real.rpow_nonneg hLp.le _
  have hFirst : L^(-D)*M ≤ Real.exp L*L^(-A) := by
    calc
      _ ≤ L^(-D)*(Real.exp L*L^parityOriginalW1PolylogExponent434*L^16) :=
        mul_le_mul_of_nonneg_left hMass hD0
      _ = Real.exp L*(L^parityOriginalW1PolylogExponent434*L^16*L^(-D)) := by ring
      _ = Real.exp L*L^(-A) := by
        have h := parity_original_B590_arithmetic_fourier_power_cancel434 L A hLp
        change L^parityOriginalW1PolylogExponent434*L^16*L^(-D) = L^(-A) at h
        rw [h]
  have hSecond : V*B ≤ Real.exp L*L^(-A) := by
    calc
      _ ≤ V*(Real.exp L*L^(-R)) := mul_le_mul_of_nonneg_left hDiscardBound hVnonneg
      _ ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 *
          (Real.exp L*L^(-R)) :=
        mul_le_mul_of_nonneg_right hV
          (mul_nonneg (Real.exp_nonneg _) hR0)
      _ = Real.exp L*(L^parityOriginalB590FixedFourierPolynomialExponent434*
          L^(-R)) := by ring
      _ = Real.exp L*L^(-A) := by
        rw [parity_original_outside_e_discarded_power_cancel434 L A hLp]
  have hPreBound := hPre.2.2 E hE hEcap Psi hSupport hPsi0 hPsi1
    band hb slot K J α β Acoef Bcoef hA hB hα hβ signed rho
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hA hB
  calc
    _ ≤ (Acoef*Bcoef)*(L^(-D)*M+V*B) := hPreBound
    _ ≤ (Acoef*Bcoef)*((Real.exp L*L^(-A))+(Real.exp L*L^(-A))) :=
      mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hAB
    _ = 2*Acoef*Bcoef*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedSourcePhysicalRankin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The actual independent ε=1/E original signed unsmoothed SOURCE
with nonzero Mellin rho, full 20! factorial Q/P W1, real Ψ and
true h=-2 alpha_m beta_n mn=u+2. This includes u=0 literally. -/
def parityOriginalShiftTwoSignedBilinearMellinSource434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    (sourceOriginalPureMellinPhase434 rho u *
      (((parityOriginalSignedSourceA434 d L signed u *
        Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- Literal signed ε=1/E B590 full Q factorial allocation mass at u,
with true history-dependent sum over f0/f1 δ. This real signed mass
need not be nonnegative for ε=E. -/
def parityOriginalSignedBufferedAAtU434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (signed : Bool) (u : ℕ) : ℝ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
    {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    parityActualOriginalSignedFullTupleWeight434 d L u signed f *
    parityActualOriginalAFullTupleAllocationMass434 d L E band slot f

/-- True original signed physical B590 buffered source with
nonzero Mellin rho and original h=-2 alpha beta arithmetic. -/
def parityOriginalShiftTwoSignedBilinearMellinB590Allocated434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    (sourceOriginalPureMellinPhase434 rho u *
      (((parityOriginalSignedBufferedAAtU434 d L E band slot signed u *
        Psi ((u:ℝ)/Real.exp L)):ℝ):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- Exact original ε=1/E signed SOURCE minus its actual B590
f0/f1 total-allocation descendant equals the true signed factorial
Q buffer defect, at arbitrary rho on u=mn-2. The equality does NOT
assume that the signed ε=E source is nonnegative, nor that the
f0/f1 allocation forms a pointwise partition outside compact support.
-/
theorem parity_original_signed_mellin_source_minus_B590_exact434
    (d : ℕ) (L E : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J α β signed rho Y -
    parityOriginalShiftTwoSignedBilinearMellinB590Allocated434
      d L E band slot Psi K J α β signed rho Y =
    parityOriginalSignedShiftTwoBilinearMellinBufferError434
      d L E band slot Psi K J α β signed rho Y := by
  unfold parityOriginalShiftTwoSignedBilinearMellinSource434
    parityOriginalShiftTwoSignedBilinearMellinB590Allocated434
    parityOriginalSignedShiftTwoBilinearMellinBufferError434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hA : parityOriginalSignedSourceA434 d L signed u -
      parityOriginalSignedBufferedAAtU434 d L E band slot signed u =
      parityOriginalSignedFullQBufferDefectAtU434 d L E band slot signed u := by
    unfold parityOriginalSignedSourceA434
      parityOriginalSignedBufferedAAtU434
      parityOriginalSignedFullQBufferDefectAtU434
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f hf
    ring
  calc
    _ = (sourceOriginalPureMellinPhase434 rho u *
      (((parityOriginalSignedSourceA434 d L signed u -
         parityOriginalSignedBufferedAAtU434 d L E band slot signed u) *
         Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)) *
       (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
         α z.1*β z.2) := by push_cast; ring
    _ = _ := by rw [hA]

/-- Independently for ε=1 and ε=E, TRUE original unsmoothed h=-2
SOURCE with arbitrary Mellin rho and original full Q/P factorial
arithmetic differs from its legitimate B590 buffered real-source
descendant by at most `Acoef Bcoef expL L^-A` for every requested
A, under the original beta/4 retained Pcap, true reserved-Q cap,
Psi support and complete shifted-divisor Rankin; this is not merely
a bound on their odd half-difference. -/
theorem parity_eventually_original_signed_mellin_source_to_B590_allocated_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool) (rho : ℝ),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
        (sourceOriginalLiteralDepth 20 L) L Psi K J α β signed rho
          ⌊2*Real.exp L⌋₊ -
       parityOriginalShiftTwoSignedBilinearMellinB590Allocated434
        (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_signed_mellin_buffer_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  rw [parity_original_signed_mellin_source_minus_B590_exact434]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedFourierCutoff -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The genuine signed ε=1/E B590 physical A(u) Fourier BOX is EXACTLY
the sum over original full 20! factorial Q-labelled tuples of the
actual signed weight times the all-δ Fourier BOX assignment mass.
Its derivation uses genuine N-dimensional product Lebesgue Fubini,
not a value of Fourier integrand at ξ=0. -/
theorem parity_original_signed_B590_box_eq_weighted_fullQ_sum434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T =
      ∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        ((parityActualOriginalSignedFullTupleWeight434 d L u signed f:ℝ):ℂ) *
        (∑ δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          parityOriginalB590AllGateFourierBox434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) δ
            (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot f i).val) T) := by
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let μ : Measure (Fin N → ℝ) := Measure.pi (fun _ : Fin N =>
    (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let F := ((j : Fin (d+1)) → Fin 20 →
    {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let w : F → ℂ := fun f =>
    ((parityActualOriginalSignedFullTupleWeight434 d L u signed f:ℝ):ℂ)
  let I : (Fin N → Bool) → F → (Fin N → ℝ) → ℂ := fun δ f ξ =>
    parityOriginalB590AllGateFourierIntegrand434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ
      (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) ξ
  have hI (δ : Fin N → Bool) (f : F) : Integrable (I δ f) μ :=
    parity_original_B590_all_gate_integrable_on_fourier_box434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ
      (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) T
  have hW (δ : Fin N → Bool) (f : F) :
      Integrable (fun ξ => w f * I δ f ξ) μ := (hI δ f).const_mul _
  unfold parityOriginalSignedPhysicalABoxAtU434
    parityOriginalSignedFullSourceFourierAtU434
    parityOriginalSignedFullQAllGateFourierAtU434
  rw [integral_finsetSum Finset.univ (by
    intro δ hδ
    exact integrable_finsetSum Finset.univ (by intro f hf; exact hW δ f))]
  conv_lhs =>
    arg 2
    ext δ
    rw [integral_finsetSum Finset.univ (by intro f hf; exact hW δ f)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  rfl

/-- ORIGINAL independent signed ε=1/E B590 full-real f0/f1
allocated source minus true N-dimensional Fourier BOX at each u
has complex norm ≤W1(P,u) * SUM OF ALL REAL FOURIER TAILS.
The proof explicitly uses the ABSOLUTE signed factorial total mass
≤W1(P,u), not the old positive odd projector bound. No extra 2^N
or extra Q-band cardinality, uniform in signed choice. -/
theorem parity_original_signed_B590_allocated_minus_box_le_W1_tail434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (signed : Bool) (T : ℝ) :
    ‖((parityOriginalSignedBufferedAAtU434 d L E band slot signed u:ℝ):ℂ) -
      parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        (∑ δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∑ i : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length,
            parityOriginalB590OneCoordinateFourierTail434 δ i T) := by
  let F := ((j : Fin (d+1)) → Fin 20 →
    {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let t : ℝ := ∑ δ : Fin N → Bool,
    ∑ i : Fin N, parityOriginalB590OneCoordinateFourierTail434 δ i T
  let w : F → ℝ := fun f => parityActualOriginalSignedFullTupleWeight434 d L u signed f
  let M : F → ℝ := fun f => parityActualOriginalAFullTupleAllocationMass434 d L E band slot f
  let B : F → ℂ := fun f => ∑ δ : Fin N → Bool,
    parityOriginalB590AllGateFourierBox434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ
      (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) T
  have hTail0 : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro δ hδ
    apply Finset.sum_nonneg
    intro i hi
    unfold parityOriginalB590OneCoordinateFourierTail434
    exact mul_nonneg
      (setIntegral_nonneg measurableSet_Icc.compl (by intro ξ hξ; exact norm_nonneg _))
      (Finset.prod_nonneg (by intro j hj; exact integral_nonneg (fun ξ => norm_nonneg _)))
  have hTerm (f : F) : ‖((w f:ℝ):ℂ)*(((M f:ℝ):ℂ)-B f)‖ ≤ |w f| * t := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (parity_original_actual_fullQ_B590_mass_minus_fourier_box_le_union434
        d L E band slot f T) (abs_nonneg _)
  have hSum : (∑ f : F, |w f|) ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
    parity_original_signed_full_Q_total_variation_le_W1434 d L hL u signed
  have hDiff : ((parityOriginalSignedBufferedAAtU434 d L E band slot signed u:ℝ):ℂ)-
      parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T =
      ∑ f : F, ((w f:ℝ):ℂ)*(((M f:ℝ):ℂ)-B f) := by
    rw [parity_original_signed_B590_box_eq_weighted_fullQ_sum434]
    unfold parityOriginalSignedBufferedAAtU434
    push_cast
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f hf
    push_cast
    ring
  rw [hDiff]
  calc
    _ ≤ ∑ f : F, ‖((w f:ℝ):ℂ)*(((M f:ℝ):ℂ)-B f)‖ := norm_sum_le _ _
    _ ≤ ∑ f : F, |w f| * t := Finset.sum_le_sum (by intro f hf; exact hTerm f)
    _ = (∑ f : F, |w f|)*t := by rw [Finset.sum_mul]
    _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u*t :=
      mul_le_mul_of_nonneg_right hSum hTail0
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEWindowSplit -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine individual signed original factorial Q/P B590 Fourier-box
with precisely Parity (4.5) selected-e window E*L^-88<=e<=E.
The sign epsilon=1/E is applied BEFORE restricting e, integration
or taking absolute values. Full original Q tuples and δ histories. -/
def parityOriginalSignedB590InsideEAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ) *
      (∑ δ ∈ parityOriginalB590InsideEWindowAssignments434
        d L E band slot f,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot f i).val) T)

/-- EXACT signed arithmetic/source Fourier equality:
original B590 physical A(u) = historical in-window + true
out-of-window Fourier BOX leakage, for EACH epsilon=1 and E.
No pointwise support assertion for truncated Fourier integrands. -/
theorem parity_original_signed_B590_box_eq_inside_plus_outside434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T =
      parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T +
      parityOriginalSignedB590OutsideEAtU434 d L E u signed band slot T := by
  rw [parity_original_signed_B590_box_eq_weighted_fullQ_sum434]
  unfold parityOriginalSignedB590InsideEAtU434
    parityOriginalSignedB590OutsideEAtU434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←mul_add]
  congr 1
  exact (parity_original_B590_e_window_sum_partition434
    d L E band slot f
    (fun δ => parityOriginalB590AllGateFourierBox434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ
      (fun i => (parityActualSourceRemainingFullQTuple434
        d L band slot f i).val) T)).symm

/-- The TRUE signed original h=-2 B590 arithmetic Fourier source
for the selected-e Parity (4.5) window, including Ψ(u/x), real Mellin
rho, independent signed original Q/P W1/E, and actual mn=u+2
complex alpha_m beta_n. -/
def parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- Both real signed B590 Fourier sources split EXACTLY into
selected-e and outside-e, independent of the odd projector.
This identity still includes the original signed multiplicity parity
and an arbitrary Mellin rho before Cauchy. -/
theorem parity_original_signed_hminus2_mellin_box_eq_inside_plus_outside434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinFourierBox434
      d L E band slot Psi K J α β signed rho Y T =
    parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
      d L E band slot Psi K J α β signed rho Y T +
    parityOriginalShiftTwoSignedBilinearMellinOutsideEBox434
      d L E band slot Psi K J α β signed rho Y T := by
  unfold parityOriginalShiftTwoSignedBilinearMellinFourierBox434
    parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
    parityOriginalShiftTwoSignedBilinearMellinOutsideEBox434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_signed_B590_box_eq_inside_plus_outside434]
  ring

/-- The actually proved signed physical H_0(vStar) Fourier source
has exactly the original selected e-window plus the separately
bounded outside-e Fourier contribution, with all true factorials,
source Ψ(u/x), arbitrary rho and h=-2 alpha beta.
Only reserved sigma=0 is asserted, as sourced by real B590. -/
theorem parity_original_signed_H_box_eq_inside_e_plus_outside434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinHBox434
      d L E band slot Psi K J α β signed rho Y T =
    parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
      d L E band slot Psi K J α β signed rho Y T +
    parityOriginalShiftTwoSignedBilinearMellinOutsideEBox434
      d L E band slot Psi K J α β signed rho Y T := by
  rw [←parity_original_hminus2_signed_bilinear_mellin_fourier_box_eq_source_H434
    d L E hL hd band slot Psi K J α β signed rho Y T]
  exact parity_original_signed_hminus2_mellin_box_eq_inside_plus_outside434
    d L E band slot Psi K J α β signed rho Y T
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedFourierBilinearTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Individual signed Parity ε=1/E full original B590 f0/f1
allocation model summed over actual positive source u and the
original shifted mn=u+2 alpha beta pairs, with arbitrary Mellin
rho and literal Psi. The B590 mass is the exact signed full
Q 20! factorial allocation mass, not the old odd projector. -/
def parityOriginalShiftTwoSignedBilinearFullMellinAllocated434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (sourceOriginalPureMellinPhase434 rho u *
      ((parityOriginalSignedBufferedAAtU434 d L E band slot signed u:ℝ):ℂ) *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- For BOTH true independently signed Parity ε=1/E original h=-2
source full-vs-box physical B590 Fourier forms, the complex error
before Cauchy is ≤Acoef Bcoef ΣW1(P,u)τ(u+2) × real f0/f1 Fourier
tail allδ,i, uniformly in signed choice and nonzero Mellin rho.
This uses signed Q factorial total variation, not odd positivity.
-/
theorem parity_original_hminus2_signed_mellin_full_minus_box_le_arithmetic_tail434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsiPos : ∀ x, 0 ≤ Psi x)
    (hPsiLe : ∀ x, Psi x ≤ 1)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Acoef Bcoef : ℝ) (hA : 0 ≤ Acoef) (hB : 0 ≤ Bcoef)
    (hα : ∀ m ∈ K, ‖α m‖ ≤ Acoef)
    (hβ : ∀ n ∈ J, ‖β n‖ ≤ Bcoef)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) :
    ‖parityOriginalShiftTwoSignedBilinearFullMellinAllocated434 d L E band slot
        Psi K J α β signed rho Y -
      parityOriginalShiftTwoSignedBilinearMellinFourierBox434 d L E band slot
        Psi K J α β signed rho Y T‖ ≤
    (Acoef*Bcoef) *
      (∑ u ∈ Finset.Ioc 0 Y,
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)) *
      (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∑ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length,
          parityOriginalB590OneCoordinateFourierTail434 δ i T) := by
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let tail : ℝ := ∑ δ : Fin N → Bool, ∑ i : Fin N,
    parityOriginalB590OneCoordinateFourierTail434 δ i T
  let w := fun u => sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u
  let D : ℕ → ℂ := fun u =>
    ((parityOriginalSignedBufferedAAtU434 d L E band slot signed u:ℝ):ℂ) -
      parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α z.1*β z.2
  let P : ℕ → ℂ := fun u => sourceOriginalPureMellinPhase434 rho u
  let S : ℕ → ℂ := fun u => (Psi ((u:ℝ)/Real.exp L):ℂ)
  have ht : 0 ≤ tail := by
    apply Finset.sum_nonneg
    intro δ hd
    apply Finset.sum_nonneg
    intro i hi
    unfold parityOriginalB590OneCoordinateFourierTail434
    exact mul_nonneg
      (setIntegral_nonneg measurableSet_Icc.compl (fun ξ _ => norm_nonneg _))
      (Finset.prod_nonneg (by intro j hj; exact integral_nonneg (fun ξ => norm_nonneg _)))
  have hw (u : ℕ) : 0 ≤ w u := source_original_W1_nonneg _ _
  have hD (u : ℕ) : ‖D u‖ ≤ w u*tail :=
    parity_original_signed_B590_allocated_minus_box_le_W1_tail434
      d L E hL u band slot signed T
  have hB (u : ℕ) : ‖B u‖ ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef :=
    parity_original_shift_two_bilinear_fibre_norm_le_tau434 K J u
      α β Acoef Bcoef hA hB hα hβ
  have hTerm (u : ℕ) :
      ‖(P u*D u*S u)*B u‖ ≤
      (Acoef*Bcoef)*(w u*((u+2).divisors.card:ℝ))*tail := by
    rw [norm_mul,norm_mul,norm_mul]
    have hphase : ‖P u‖ = 1 := source_original_pure_mellin_phase_norm_one434 _ _
    have hΨpos : 0 ≤ Psi ((u:ℝ)/Real.exp L) := hPsiPos _
    have hΨle : Psi ((u:ℝ)/Real.exp L) ≤ 1 := hPsiLe _
    have hΨ : ‖S u‖ = Psi ((u:ℝ)/Real.exp L) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hΨpos]
    rw [hphase,one_mul,hΨ]
    have hWt : 0 ≤ w u*tail := mul_nonneg (hw u) ht
    have hB0 : 0 ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef := by positivity
    calc
      _ ≤ ((w u*tail)*Psi ((u:ℝ)/Real.exp L))*
          (((u+2).divisors.card:ℝ)*Acoef*Bcoef) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (hD u) hΨpos)
          (hB u) (norm_nonneg _) (mul_nonneg hWt hΨpos)
      _ ≤ (w u*tail)*(((u+2).divisors.card:ℝ)*Acoef*Bcoef) :=
        mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hWt hΨle) hB0
      _ = _ := by ring
  unfold parityOriginalShiftTwoSignedBilinearFullMellinAllocated434
    parityOriginalShiftTwoSignedBilinearMellinFourierBox434
  rw [←Finset.sum_sub_distrib]
  have hDiff :
      (∑ u ∈ Finset.Ioc 0 Y,
        ((P u*((parityOriginalSignedBufferedAAtU434 d L E band slot signed u:ℝ):ℂ)*S u)*B u -
          (P u*parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T*S u)*B u)) =
      ∑ u ∈ Finset.Ioc 0 Y, (P u*D u*S u)*B u := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [D]
    ring
  rw [hDiff]
  calc
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y, ‖(P u*D u*S u)*B u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        (Acoef*Bcoef)*(w u*((u+2).divisors.card:ℝ))*tail := by
      apply Finset.sum_le_sum
      intro u hu
      exact hTerm u
    _ = (Acoef*Bcoef) *
        (∑ u ∈ Finset.Ioc 0 Y, w u*((u+2).divisors.card:ℝ))*tail := by
      rw [←Finset.sum_mul,←Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedFourierTailAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- Individually signed ε=1/E ORIGINAL full B590 source-minus-real
N-dimensional Fourier BOX h=-2 alpha-beta discrepancy has arbitrary
inverse-log accuracy `Acoef Bcoef exp(L)L^-A`, UNIFORMLY for any
Mellin rho and either signed choice, using native W1(P,u)τ(u+2)
weighted fourth-divisor moment and signed Q factorial total
variation. Neither signed branch requires positivity. -/
theorem parity_eventually_original_hminus2_signed_mellin_full_minus_box_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      0 < L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E rho : ℝ) (signed : Bool) (Psi : ℝ → ℝ),
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoSignedBilinearFullMellinAllocated434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoSignedBilinearMellinFourierBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_B590_arithmetic_fourier_tail_all_log434 A,
    eventually_gt_atTop (0:ℝ)] with L hBudget hLp
  refine ⟨hLp,?_⟩
  intro band slot E rho signed Psi hPsiPos hPsiLe K J α β
    Acoef Bcoef hA hB hα hβ
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let M : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((u+2).divisors.card:ℝ)
  let T : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      parityOriginalB590OneCoordinateFourierTail434 δ i L
  have hNorm := parity_original_hminus2_signed_mellin_full_minus_box_le_arithmetic_tail434
    d L E hLp band slot Psi hPsiPos hPsiLe
    K J α β Acoef Bcoef hA hB hα hβ signed rho Y L
  have hTail := hBudget band slot
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hA hB
  calc
    _ ≤ (Acoef*Bcoef)*M*T := hNorm
    _ = (Acoef*Bcoef)*(M*T) := by ring
    _ ≤ (Acoef*Bcoef)*(Real.exp L*L^(-A)) :=
      mul_le_mul_of_nonneg_left hTail hAB
    _ = Acoef*Bcoef*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedSourceToHBoxAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The actual signed source B590 buffered h=-2 sum over [0,Y]
reduces to the positive original source (0,Y] without discarding
any genuine contribution: Psi(0)=0 kills exactly the u=0 term,
including for the independent negative ε=E branch and all rho. -/
theorem parity_original_signed_B590_allocated_range_eq_positive434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0=0)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoSignedBilinearMellinB590Allocated434
      d L E band slot Psi K J α β signed rho Y =
    parityOriginalShiftTwoSignedBilinearFullMellinAllocated434
      d L E band slot Psi K J α β signed rho Y := by
  unfold parityOriginalShiftTwoSignedBilinearMellinB590Allocated434
    parityOriginalShiftTwoSignedBilinearFullMellinAllocated434
  rw [parity_original_sum_range_eq_Ioc_of_zero434]
  · apply Finset.sum_congr rfl
    intro u hu
    push_cast
    ring
  · simp [hPsi0]

/-- Each independent ORIGINAL signed Parity ε=1 or ε=E full 20!
Q-factorial source with arbitrary Mellin rho has a genuine
SOURCE-to-physical-H Fourier-box approximation, individually:

‖S_ε,rho - B_H,ε,rho‖ ≤ 2 Acoef Bcoef exp(L) L^-A.

The TRUE signed Rankin SOURCE→full real B590 buffer error costs
AB exp(L)L^-A, and the separately signed real B590→Fourier BOX
Schwartz cutoff error costs the same. Exact signed SOURCE Fourier
Fubini gives physical e^(i rho)×v^(i rho) W1(P,v)ε(v)H_0(vStar).
This is not inferred from the smallness of their odd HALF
DIFFERENCE; BOTH errors are independently proved at source level.
No Parity(4.17) signed correlation bound is asserted. -/
theorem parity_eventually_original_signed_hminus2_source_mellin_to_H_box_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool) (rho : ℝ),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β signed rho
          ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoSignedBilinearMellinHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L‖ ≤
        2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_mellin_source_to_B590_allocated_all_log434
      betaP A hbetaP jQ hBand,
    parity_eventually_original_hminus2_signed_mellin_full_minus_box_all_log434 A]
    with L hSource hBox
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let S : ℂ := parityOriginalShiftTwoSignedBilinearMellinSource434
    d L Psi K J α β signed rho Y
  let P : ℂ := parityOriginalShiftTwoSignedBilinearFullMellinAllocated434
    d L E band slot Psi K J α β signed rho Y
  let B : ℂ := parityOriginalShiftTwoSignedBilinearMellinHBox434
    d L E band slot Psi K J α β signed rho Y L
  have hPsi0 : Psi 0=0 := parity_original_Psi_support_zero434 Psi hSupport
  have hRange : parityOriginalShiftTwoSignedBilinearMellinB590Allocated434
      d L E band slot Psi K J α β signed rho Y = P :=
    parity_original_signed_B590_allocated_range_eq_positive434
      d L E band slot Psi hPsi0 K J α β signed rho Y
  have hHbox : parityOriginalShiftTwoSignedBilinearMellinFourierBox434
      d L E band slot Psi K J α β signed rho Y L = B :=
    parity_original_hminus2_signed_bilinear_mellin_fourier_box_eq_source_H434
      d L E (by nlinarith [hSource.1]) rfl band slot
      Psi K J α β signed rho Y L
  have hFirst : ‖S-P‖ ≤ Acoef*Bcoef*Real.exp L*L^(-A) := by
    rw [←hRange]
    exact hSource.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
      slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  have hSecond : ‖P-B‖ ≤ Acoef*Bcoef*Real.exp L*L^(-A) := by
    rw [←hHbox]
    exact hBox.2 band slot E rho signed Psi hPsiPos hPsiLe
      K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  change ‖S-B‖ ≤ 2*Acoef*Bcoef*Real.exp L*L^(-A)
  calc
    _ = ‖(S-P)+(P-B)‖ := by ring
    _ ≤ ‖S-P‖+‖P-B‖ := norm_add_le _ _
    _ ≤ (Acoef*Bcoef*Real.exp L*L^(-A)) +
      (Acoef*Bcoef*Real.exp L*L^(-A)) := add_le_add hFirst hSecond
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEWindowSourceAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Exact ORIGINAL two independently signed Parity epsilon=1/E
source-original factorial 20! h=-2 bilinear to historical Parity (4.5)
selected e-window Fourier source, at arbitrary genuine Mellin rho:
‖S_epsilon(rho) - B_inside_e_epsilon(rho)‖ <=
  4 Acoef Bcoef exp(L) L^-A.
The first 2AB comes from TRUE signed SOURCE to physical H_0 Fourier
box (actual buffer beta/4 Rankin + full Fourier Schwartz tails);
the second 2AB is true independent signed outside-e Fourier leakage
(retained beta/4 and discarded Ppart Rankin).
This is a real SOURCE pre-Cauchy error, not half-difference projector,
nor an imported universal E theorem 4.1, and does not yet supply
the full Parity (4.7) post-integrated nonzero sigma coefficient identity. -/
theorem parity_eventually_original_signed_hminus2_source_to_inside_e_box_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool) (rho : ℝ),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β signed rho
          ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_hminus2_source_mellin_to_H_box_all_log434
      betaP A hbetaP jQ hBand,
    parity_eventually_original_signed_hminus2_mellin_outside_e_fourier_box_all_log434
      betaP A hbetaP jQ hBand] with L hSource hOutside
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let S : ℂ := parityOriginalShiftTwoSignedBilinearMellinSource434
    d L Psi K J α β signed rho Y
  let H : ℂ := parityOriginalShiftTwoSignedBilinearMellinHBox434
    d L E band slot Psi K J α β signed rho Y L
  let I : ℂ := parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
    d L E band slot Psi K J α β signed rho Y L
  let O : ℂ := parityOriginalShiftTwoSignedBilinearMellinOutsideEBox434
    d L E band slot Psi K J α β signed rho Y L
  have hSourceBound : ‖S-H‖ ≤
      2*Acoef*Bcoef*Real.exp L*L^(-A) :=
    hSource.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
      slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  have hOut : ‖O‖ ≤ 2*Acoef*Bcoef*Real.exp L*L^(-A) :=
    hOutside.2.2 E hElo hEhi Psi hSupport hPsiPos hPsiLe
      band hb slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  have hSplit : H = I+O :=
    parity_original_signed_H_box_eq_inside_e_plus_outside434
      d L E (by nlinarith [hSource.1]) rfl band slot
      Psi K J α β signed rho Y L
  have hDiff : H-I = O := by rw [hSplit]; ring
  change ‖S-I‖ ≤ 4*Acoef*Bcoef*Real.exp L*L^(-A)
  calc
    _ = ‖(S-H)+(H-I)‖ := by ring
    _ ≤ ‖S-H‖+‖H-I‖ := norm_add_le _ _
    _ = ‖S-H‖+‖O‖ := by rw [hDiff]
    _ ≤ 2*Acoef*Bcoef*Real.exp L*L^(-A) +
       2*Acoef*Bcoef*Real.exp L*L^(-A) :=
      add_le_add hSourceBound hOut
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEWindowEFibre -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Original full signed source branch at one true original historical
in-window selected-e allocation, retaining actual 20! Q tuple
factorial, P-W1, epsilon=1/E sign and real Fourier box. -/
def parityOriginalSignedB590InsideEBranchWeight434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot) : ℂ :=
  ((parityActualOriginalSignedFullTupleWeight434 d L u signed z.2 : ℝ):ℂ) *
    parityOriginalB590AllGateFourierBox434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) z.1
      (fun i => (parityActualSourceRemainingFullQTuple434
        d L band slot z.2 i).val) T

/-- True selected-e endpoint coefficient of the full original signed
factorial-labelled Fourier-box branch, with no replacement of the
source Q/P product arithmetic by a presumed independent a_e. -/
def parityOriginalSignedB590InsideEEndpointFibre434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) (e : ℕ) : ℂ :=
  sourceEndpointFibre
    (parityOriginalB590InsideEFullBranchCarrier434 d L E band slot)
    (parityActualOriginalAFullBranchE434 d L band slot)
    (parityOriginalSignedB590InsideEBranchWeight434 d L E u signed band slot T) e

/-- Exact historical e-window selected-e ENDPOINT regrouping of
original r0=20 full labelled Q/P Fourier BOX coefficient at source u.
No Q orbit/factorial collision loss: `Finset.sum_image'` is used with
real source allocated products and original full complex weights. -/
theorem parity_original_signed_B590_inside_e_A_eq_selected_e_fibres434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T =
      ∑ e ∈ parityOriginalB590InsideEFullSelectedSupport434 d L E band slot,
        parityOriginalSignedB590InsideEEndpointFibre434 d L E u signed band slot T e := by
  let S := parityOriginalB590InsideEFullBranchCarrier434 d L E band slot
  let g := parityActualOriginalAFullBranchE434 d L band slot
  let w := parityOriginalSignedB590InsideEBranchWeight434 d L E u signed band slot T
  have hReindex := Finset.sum_image'
    (s := S) (g := g)
    (f := fun e => sourceEndpointFibre S g w e)
    w (by intro z hz; rfl)
  have hS :
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        ∑ δ ∈ parityOriginalB590InsideEWindowAssignments434 d L E band slot f,
          w (δ,f)) =
      ∑ z ∈ S, w z := by
    unfold S parityOriginalB590InsideEFullBranchCarrier434
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [parityOriginalB590InsideEWindowAssignments434,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro δ hδ
    rfl
  calc
    parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T =
      ∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        ∑ δ ∈ parityOriginalB590InsideEWindowAssignments434 d L E band slot f,
          w (δ,f) := by
            unfold parityOriginalSignedB590InsideEAtU434
            apply Finset.sum_congr rfl
            intro f hf
            rw [Finset.mul_sum]
            rfl
    _ = ∑ z ∈ S, w z := hS
    _ = _ := hReindex.symm
end Green64Analytic.Parity

end

end

