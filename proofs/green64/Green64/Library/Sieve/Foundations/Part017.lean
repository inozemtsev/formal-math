module

public import Green64.Library.Sieve.Foundations.Part016
public import Green64.Library.Sieve.Foundations.Part012
public import Green64.Library.Sieve.Foundations.Part015
public import Green64.Library.Sieve.Foundations.Part011
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Weights.Part112
public import Green64.Library.Sieve.Foundations.Part008

@[expose] public section

/-!
# Sieve / Foundations / Part017

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalSignedEWindowOuterAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The TRUE full source-original selected-e historical (4.5) window
Fourier BOX with outer selected e and arbitrary original Mellin rho.
Its inner e-endpoint fibre still retains the ORIGINAL Q/P W1, odd
multiplicity parity and h=-2 alpha beta, and is NOT substituted with
a conjectural independent e coefficient. The Mellin phase is at
original `u=mn-2`; the TRUE source Qproduct gate entails u=e*v. -/
def parityOriginalShiftTwoSignedBilinearMellinInsideEBoxOuter434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ e ∈ parityOriginalB590InsideEFullSelectedSupport434 d L E band slot,
    ∑ u ∈ Finset.Ioc 0 Y,
      (sourceOriginalPureMellinPhase434 rho u *
        parityOriginalSignedB590InsideEEndpointFibre434 d L E u signed band slot T e *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2)

/-- Exact original Parity §4.2 full selected e-FIRST finite source
regrouping with the historical window and arbitrary Mellin rho:
all 20! original labelled Q tuples, true B590 f0/f1 Fourier BOX
integrals, real W1/P odd projector and h=-2 mn=u+2 remain literal.
This equality is independent of Rankin precision and is not a
pointwise Fourier ξ support assertion. -/
theorem parity_original_signed_hminus2_mellin_inside_e_box_eq_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
      d L E band slot Psi K J α β signed rho Y T =
    parityOriginalShiftTwoSignedBilinearMellinInsideEBoxOuter434
      d L E band slot Psi K J α β signed rho Y T := by
  unfold parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
    parityOriginalShiftTwoSignedBilinearMellinInsideEBoxOuter434
  simp_rw [parity_original_signed_B590_inside_e_A_eq_selected_e_fibres434]
  let M := parityOriginalB590InsideEFullSelectedSupport434 d L E band slot
  let F : ℕ → ℕ → ℂ := fun e u =>
    parityOriginalSignedB590InsideEEndpointFibre434 d L E u signed band slot T e
  let P : ℕ → ℂ := fun u => sourceOriginalPureMellinPhase434 rho u
  let S : ℕ → ℂ := fun u => (Psi ((u:ℝ)/Real.exp L):ℂ)
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α z.1*β z.2
  change (∑ u ∈ Finset.Ioc 0 Y,
      (P u * (∑ e ∈ M, F e u) * S u) * B u) =
    ∑ e ∈ M, ∑ u ∈ Finset.Ioc 0 Y,
      (P u * F e u * S u) * B u
  calc
    _ = ∑ u ∈ Finset.Ioc 0 Y,
        ∑ e ∈ M, (P u * F e u * S u) * B u := by
          apply Finset.sum_congr rfl
          intro u hu
          calc
            (P u * (∑ e ∈ M, F e u) * S u) * B u =
                ((∑ e ∈ M, P u * F e u) * S u) * B u := by
                  conv_lhs =>
                    arg 1
                    arg 1
                    rw [Finset.mul_sum]
            _ = (∑ e ∈ M, P u * F e u * S u) * B u := by
                  conv_lhs =>
                    arg 1
                    rw [Finset.sum_mul]
            _ = ∑ e ∈ M, (P u * F e u * S u) * B u := by
                  conv_lhs => rw [Finset.sum_mul]
    _ = _ := Finset.sum_comm

/-- COMPLETE original unsmoothed h=-2 sourceOriginalA, for EVERY
real Mellin rho, approximated by the selected-e-FIRST original
frequency BOX [-L,L]^N with genuine historical (4.5) source support
`E L^-88≤e≤E`, original Q/P factorial, W1 odd Omega parity and
actual finite alpha_m beta_n mn=u+2. Uniform direct source complex
error `<=4 Acoef Bcoef expL L^-A` for arbitrary fixed beta>0 and A.

This establishes selected-e outer support after Fourier cutoff at
nonzero rho, without a false pointwise ξ zero or external coefficient
assumption. The inner endpoint still requires its literal fixed-
frequency Fourier integration identification with native H(vStar)
and historical epsilon convention before Parity(4.7) is complete. -/
theorem parity_eventually_original_signed_hminus2_mellin_source_to_inside_e_outer_all_log434
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
        parityOriginalShiftTwoSignedBilinearMellinInsideEBoxOuter434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_hminus2_source_to_inside_e_box_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  rw [←parity_original_signed_hminus2_mellin_inside_e_box_eq_outer434
    (sourceOriginalLiteralDepth 20 L) L E band slot
    Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowReservedGate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- ORIGINAL Parity ε=1/E signed full-Q Fourier source at a fixed
physical integer u, allocation δ and source frequency ξ. The
signed full labelled Q-tuple weight has its original 20! factorial,
W1(P,u), actual Qproduct gate, and source multiplicity sign. -/
def parityOriginalSignedFullQWindowSourceFourierAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    if parityOriginalHistoricalEWindow434 L E
          (paritySourceOrderedAllocatedE434 δ
            (parityActualSourceRemainingFullQTuple434 d L band slot f)) then
      ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ) *
        paritySourceFullSlotFourierPhase434
          (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ
          (parityActualSourceRemainingFullQTuple434 d L band slot f)
    else 0

/-- The genuine fixed-u SOURCE Parity signed ε=1 or ε=E full Q
factorial Fourier coefficient after moving the reserved prime to its
real source slot. This is the ACTUAL original reserved Q-product gate
and a single explicit W1(P,u)*ε(P,u), not the odd projector. -/
def parityOriginalSignedReservedWindowProductGate434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  (((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed u):ℝ):ℂ) *
    parityOriginalReservedFullQPhysicalWindowGate434 d L E band slot δ ξ 0 u

/-- TRUE original labelled Q source ε=1/E branch, at EACH u,δ,ξ,
exactly equals its reserved-Q full physical gate, with no assumption
that ε=E branch is positive. The source Q-prime labels are moved by
the verified real micro-Q/sorted remaining equivalence, including
original full factorial (20!)^{-(d+1)} in ℝ and its ℂ cast. -/
theorem parity_original_signed_fullQ_window_source_eq_reserved_gate434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalSignedFullQWindowSourceFourierAtU434 d L E u signed band slot δ ξ =
    parityOriginalSignedReservedWindowProductGate434 d L E u signed band slot δ ξ := by
  let D := parityActualOriginalReservedSortedQEquiv434 d L band slot
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let P := sourceOriginalPAllActualBands 20 L
  let Fact : ℝ := ∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)
  let F : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) → ℂ :=
    fun f => if parityOriginalHistoricalEWindow434 L E
        (paritySourceOrderedAllocatedE434 δ
          (parityActualSourceRemainingFullQTuple434 d L band slot f)) then
        ((parityActualOriginalSignedFullTupleWeight434 d L u signed f:ℝ):ℂ) *
          paritySourceFullSlotFourierPhase434 s ξ δ
            (parityActualSourceRemainingFullQTuple434 d L band slot f)
      else 0
  have hEquiv : (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}), F f) =
      ∑ x : ({q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band} ×
        ((i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q∈sourceActualSortedQ 20 d L band slot i})),
        F (D.symm x) := by
    have h := parity_original_reserved_sum_generic434 d L band slot
      (fun x => F (D.symm x))
    simpa only [D,parityActualOriginalReservedSortedQEquiv434,
      Equiv.symm_apply_apply] using h
  unfold parityOriginalSignedFullQWindowSourceFourierAtU434
    parityOriginalSignedReservedWindowProductGate434
  change (∑ f, F f) = _
  rw [hEquiv]
  rw [Fintype.sum_prod_type]
  unfold parityOriginalReservedFullQPhysicalWindowGate434
  rw [Finset.sum_subtype (sourceOriginalQActualBands 20 d L band)
    (by intro p; rfl)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest hrest
  let f := D.symm (p,rest)
  have hD : D f=(p,rest) := D.apply_symm_apply _
  have hfull := parity_actual_original_reserved_sorted_equiv_product434
    d L band slot f
  rw [hD] at hfull
  have hRest := parity_actual_original_reserved_sorted_equiv_rest434
    d L band slot f
  rw [hD] at hRest
  have hFact : (sourceActualSortedFactorial 20 d:ℂ) = (Fact:ℂ) := by
    unfold sourceActualSortedFactorial Fact
    push_cast
    rfl
  unfold F parityActualOriginalSignedFullTupleWeight434
  rw [←hRest,hfull]
  by_cases hwin : parityOriginalHistoricalEWindow434 L E
      (paritySourceOrderedAllocatedE434 δ rest)
  · simp only [hwin, true_and, ite_true]
    by_cases hgate : p.val*(∏ i, (rest i).val) =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u
    · dsimp only [P,s] at hgate ⊢
      simp only [if_pos hgate]
      rw [show sourceOriginalPureMellinPhase434 (0:ℝ) p.val=1 by
        simp [sourceOriginalPureMellinPhase434]]
      rw [hFact]
      dsimp only [Fact]
      push_cast
      ring_nf
    · dsimp only [P,s] at hgate ⊢
      simp only [if_neg hgate]
      norm_num
  · simp only [hwin,false_and,ite_false]
    simp
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowPhysicalAV -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Actual full original signed Q-product/u source Fourier
coefficient equals selected e Fourier Q fibre × independently signed
physical a_v(v), with exact H(vStar), W1(P,v) and true e*vStar
gate. This holds for BOTH ε=1 and ε=E, BEFORE the odd-half-difference,
and keeps all Q labels/factorials/native skipped-Q coefficients. -/
theorem parity_original_signed_reserved_window_gate_eq_e_H_v434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    parityOriginalSignedReservedWindowProductGate434 d L E u signed band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if parityOriginalHistoricalEWindow434 L E z.1 ∧ z.1*z.2=sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        paritySourceQSelectedFourierEFibre434
          (Q:=sourceActualSortedQ 20 d L band slot) δ
          (sourceActualSortedFrequencyScales 20 d L band slot) ξ z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 signed z.2
          (z.2*sourceOriginalPPrimePart
           (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  unfold parityOriginalSignedReservedWindowProductGate434
  rw [parity_original_reserved_fullQ_window_gate_eq_selected_H434
    d L E band slot δ ξ K alpha q χ σ₀ σ₁ 0 u]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hwin : parityOriginalHistoricalEWindow434 L E z.1
  · simp only [hwin, true_and, ite_true]
    by_cases hgate : z.1*z.2=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    · simp only [if_pos hgate]
      have hW := parity_original_signed_actual_gate_P_weight_transfer434
        d L hL hd u hu band slot δ signed z hz hgate
      unfold parityOriginalReservedSignedPhysicalAV434
      have hZero : sourceOriginalPureMellinPhase434 (0:ℝ)
        (z.2*sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)=1 := by
        simp [sourceOriginalPureMellinPhase434]
      rw [hZero]
      rw [hW]
      push_cast
      ring
    · simp only [if_neg hgate]
      ring

  · simp only [hwin, false_and, ite_false]
    ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowFullFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Actual original signed epsilon=1/E B590 FULL Fourier integrand,
restricted to EXACT historic selected-e E*L^-88 ≤ e ≤ E BEFORE
summation and squaring; all original Q factorial labels, P-W1,
P-epsilon parity, f0/f1 Schwartz Fourier gate and frequency phase. -/
def parityOriginalSignedFullQWindowAllGateFourierAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    if parityOriginalHistoricalEWindow434 L E
         (paritySourceOrderedAllocatedE434 δ
          (parityActualSourceRemainingFullQTuple434 d L band slot f)) then
      ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ) *
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot f i).val) ξ
    else 0

/-- True independently signed original full 20! Q/P B590 integrand
with selected-e window factors EXACTLY as an e-only Fourier
coefficient times physical a_v(v) with native H_0(vStar) and W1
at EACH source Fourier allocation and frequency. Both signs are
independent and the reserved sigma is the ACTUAL SOURCE sigma=0.
No integrals are replaced by Fourier values at zero. -/
theorem parity_original_signed_fullQ_window_all_gate_fourier_eq_e_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    parityOriginalSignedFullQWindowAllGateFourierAtU434
      d L E u signed band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if parityOriginalHistoricalEWindow434 L E z.1 ∧
        z.1*z.2 = sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateFourierCoefficient434
          d L E band slot δ ξ z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 signed z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  let C : ℂ := (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
    ((Real.fourierChar (Real.log E *
      (∑ i, ξ i/sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle):ℂ)
  have hSource := parity_original_signed_fullQ_window_source_eq_reserved_gate434
    d L E u signed band slot δ ξ
  have hFactor := parity_original_signed_reserved_window_gate_eq_e_H_v434
    d L E hL hd u hu signed band slot δ ξ K alpha q χ σ₀ σ₁
  calc
    parityOriginalSignedFullQWindowAllGateFourierAtU434
      d L E u signed band slot δ ξ =
        C * parityOriginalSignedFullQWindowSourceFourierAtU434
          d L E u signed band slot δ ξ := by
      unfold parityOriginalSignedFullQWindowAllGateFourierAtU434
        parityOriginalSignedFullQWindowSourceFourierAtU434
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hwin : parityOriginalHistoricalEWindow434 L E
        (paritySourceOrderedAllocatedE434 δ
          (parityActualSourceRemainingFullQTuple434 d L band slot f))
      · simp only [if_pos hwin]
        rw [parity_original_B590_all_gate_integrand_exact434]
        dsimp [C]
        ring
      · simp only [if_neg hwin]
        ring
    _ = C * parityOriginalSignedReservedWindowProductGate434
          d L E u signed band slot δ ξ := by rw [hSource]
    _ = _ := by
      rw [hFactor]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hwin : parityOriginalHistoricalEWindow434 L E z.1
      · simp only [hwin,true_and,ite_true]
        by_cases hgate : z.1*z.2=sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
        · simp only [if_pos hgate]
          unfold parityOriginalSelectedEGateFourierCoefficient434
          dsimp [C]
          ring
        · simp only [if_neg hgate]
          ring
      · simp only [hwin,false_and,ite_false]
        ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowMellinEFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Genuine signed Parity ε=1/E ORIGINAL full 20!-labelled source
B590 Fourier coefficient at any real Mellin rho factors exactly into
selected e^(i rho) Fourier e-only term times physical
v^(i rho) W1(P,v) ε(v) H_0(vStar) on true e*v=u Q-product gate,
with no quotient by the odd projector and no split into alpha/beta.
Reserved prime σ remains 0 until sourced from further transforms. -/
theorem parity_original_signed_fullQ_window_mellin_fourier_eq_e_aV434
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
      parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if parityOriginalHistoricalEWindow434 L E z.1 ∧
        z.1*z.2 = sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateMellinCoefficient434
          d L E band slot δ ξ rho z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  rw [parity_original_signed_fullQ_window_all_gate_fourier_eq_e_H434
    d L E hL hd u hu signed band slot δ ξ K alpha q χ σ₀ σ₁]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  let P := sourceOriginalPAllActualBands 20 L
  let v := z.2*sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  by_cases hwin : parityOriginalHistoricalEWindow434 L E z.1
  · simp only [hwin, true_and, ite_true]
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
  · simp only [hwin, false_and, ite_false]
    ring
end Green64Analytic.Parity

end

end

/-! ## OriginalIntrinsicH -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Canonical actual B509 skipped-Q source coefficient. Its definition
contains precisely the original factorial and source Fourier phases;
there is no external alpha, beta or Dirichlet-character parameter. -/
def parityOriginalIntrinsicResidual434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (r : ℕ) : ℂ :=
  sourceEndpointFibre
    (Finset.univ : Finset (OrderedQSkip
      (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
        band slot).length
      (sourceActualSortedQ 20 d L band slot) δ))
    orderedSkipProduct
    (fun a => sourceActualSortedFactorial 20 d *
      orderedSkipPhase (sourceActualSortedFrequencyScales 20 d L band slot) ξ a) r

/-- Original literal H(t) with prime factor p in the reserved band,
weighted by p^(iσ), and the canonical factorial B509 residual c_r.
This is source-defined for arbitrary σ but σ=0 is the source-derived
value in the present actual original Fourier integrand. -/
def parityOriginalIntrinsicH434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ : ℝ) (t : ℕ) : ℂ :=
  sourceEndpointFibre (parityOriginalReservedHCarrier434 d L band slot δ)
    (fun a : ℕ × ℕ => a.1*a.2)
    (fun a => sourceOriginalPureMellinPhase434 σ a.1 *
      parityOriginalIntrinsicResidual434 d L band slot δ ξ a.2) t

/-- The actual physical signed coefficient independent of α and χ.
The two signed choices retain the genuine W1 and multiplicity sign. -/
def parityOriginalIntrinsicSignedAV434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ rho : ℝ) (signed : Bool) (vStar v : ℕ) : ℂ :=
  sourceOriginalPureMellinPhase434 rho v *
    (((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed v):ℝ):ℂ) *
    parityOriginalIntrinsicH434 d L band slot δ ξ σ vStar

/-- The native prime core's residual is definitionally independent of
its external α, character, and auxiliary endpoint phases. -/
theorem parity_original_native_B509_residual_is_intrinsic434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (α : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (r : ℕ) :
    (sourceNativePrimeCore 20 d L band slot δ ξ K α q χ σ₀ σ₁).residual r =
      parityOriginalIntrinsicResidual434 d L band slot δ ξ r := by
  rfl

/-- Thus the full actual reserved H(t), including p^(iσ), does not
contain alpha_m or the endpoint characters. -/
theorem parity_original_reserved_H_is_intrinsic434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (α : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ) (t : ℕ) :
    parityOriginalReservedH434 d L band slot δ ξ K α q χ σ₀ σ₁ σ t =
      parityOriginalIntrinsicH434 d L band slot δ ξ σ t := by
  rfl

/-- The Parity (4.7) physical a_v is genuinely independent of outer
Type-II alpha_m and beta_n, before invoking any Cauchy inequality. -/
theorem parity_original_signed_physical_AV_is_intrinsic434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (α : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ rho : ℝ)
    (signed : Bool) (vStar v : ℕ) :
    parityOriginalReservedSignedPhysicalAV434 d L band slot δ ξ
      K α q χ σ₀ σ₁ σ rho signed vStar v =
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ
      σ rho signed vStar v := by
  rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalIntrinsicCoeffBounds -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The complete TRUE e-side Fourier/Mellin source coefficient has
precisely the original Schwartz f0/f1 Fourier amplitude; no extra
Mellin loss at any real frequency rho, including e=0. -/
theorem parity_original_intrinsic_e_mellin_coefficient_norm434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (e : ℕ) :
    ‖parityOriginalSelectedEGateMellinCoefficient434 d L E band slot δ ξ rho e‖ =
      ‖parityOriginalSelectedEGateFourierCoefficient434 d L E band slot δ ξ e‖ := by
  unfold parityOriginalSelectedEGateMellinCoefficient434
  rw [norm_mul, source_original_pure_mellin_phase_norm_one434,one_mul]

/-- Parity (4.9) e-side source coefficient at actual full moving Q-depth,
with all original B590 gates, independent of K0, Fourier tail precision,
outer α, beta, physical v and Mellin rho. -/
theorem parity_eventually_original_intrinsic_e_mellin_coeff_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (e : ℕ),
      ‖parityOriginalSelectedEGateMellinCoefficient434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e‖ ≤
        L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖) := by
  filter_upwards [parity_eventually_original_selected_e_gate_coeff_polylog434]
    with L hCoeff
  intro band slot E δ ξ rho e
  rw [parity_original_intrinsic_e_mellin_coefficient_norm434]
  exact hCoeff band slot E δ ξ e

/-- The physically intrinsic a_v obeys the precise W1(v)*tau(vStar)
size bound WITHOUT the auxiliary alpha/character parameters, for
both signed epsilon=1 and epsilon=E and arbitrary real rho,sigma. -/
theorem parity_original_intrinsic_signed_AV_norm_le_W1_tau434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (σ rho : ℝ) (signed : Bool) (vStar v : ℕ) (hv : 0 < vStar) :
    ‖parityOriginalIntrinsicSignedAV434 d L band slot δ ξ σ rho signed vStar v‖ ≤
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
        (vStar.divisors.card:ℝ) := by
  rw [←parity_original_signed_physical_AV_is_intrinsic434
    d L band slot δ ξ (∅ : Finset ℕ) (fun _ => (0:ℂ))
      1 (1 : DirichletCharacter ℂ 1) 0 0 σ rho signed vStar v]
  exact parity_original_signed_physical_aV_norm_le_W1_tau434
    d L hL band slot δ ξ (∅ : Finset ℕ) (fun _ => (0:ℂ))
    1 (1 : DirichletCharacter ℂ 1) 0 0 σ rho signed vStar v hv

/-- Uniform historical (4.9) physical coefficient, now with the
ACTUAL intrinsic H and no spurious alpha/character dependency. -/
theorem parity_eventually_original_intrinsic_signed_AV_polylog_tau434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (σ rho : ℝ) (signed : Bool) (vStar v : ℕ),
        0 < vStar →
      ‖parityOriginalIntrinsicSignedAV434 (sourceOriginalLiteralDepth 20 L)
          L band slot δ ξ σ rho signed vStar v‖ ≤
        L^parityOriginalW1PolylogExponent434 *
          (vStar.divisors.card:ℝ) := by
  filter_upwards [parity_eventually_original_signed_physical_aV_polylog_tau434]
    with L hCoeff
  intro band slot δ ξ σ rho signed vStar v hv
  rw [←parity_original_signed_physical_AV_is_intrinsic434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ
    (∅ : Finset ℕ) (fun _ => (0:ℂ))
    1 (1 : DirichletCharacter ℂ 1) 0 0 σ rho signed vStar v]
  exact hCoeff band slot δ ξ (∅ : Finset ℕ) (fun _ => (0:ℂ))
    1 (1 : DirichletCharacter ℂ 1) 0 0 σ rho signed vStar v hv
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowHBoxIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Original separately signed epsilon 1/E historical Parity(4.5)
e-window full Q/P factorial f0/f1 Fourier source at u and a full
N-dimensional frequency. The source support condition was applied
to the literal allocated Q-product e BEFORE any Fourier integration. -/
def parityOriginalSignedWindowFullSourceFourierAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool,
    parityOriginalSignedFullQWindowAllGateFourierAtU434
      d L E u signed band slot δ ξ

/-- ORIGINAL historical signed Parity(4.7) REAL selected-e physical
integrand (before integration); each a_e(e,δ,ξ) is independent of
v, each a_v(v) contains actual W1(P,v), epsilon(v) and H_0(vStar).
Exact Q product gate e*vStar=ordinaryPart(P,u), both signs. -/
def parityOriginalSignedWindowSourceFourierHAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if parityOriginalHistoricalEWindow434 L E z.1 ∧
          z.1*z.2=sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateFourierCoefficient434 d L E band slot δ ξ z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 signed z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0

/-- Exact e-filtered signed SOURCE integrand equals literal selected-e
times physical W1(v)epsilon(v)H_0(vStar) integrand on the full
B590 f0/f1 Fourier frequency, not merely after taking its norm. -/
theorem parity_original_signed_window_full_source_integrand_eq_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalSignedWindowFullSourceFourierAtU434
      d L E u signed band slot ξ =
    parityOriginalSignedWindowSourceFourierHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁ ξ := by
  unfold parityOriginalSignedWindowFullSourceFourierAtU434
    parityOriginalSignedWindowSourceFourierHAtU434
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_signed_fullQ_window_all_gate_fourier_eq_e_H434
    d L E hL hd u hu signed band slot δ ξ K alpha q χ σ₀ σ₁

/-- Actual historical selected-e N-dimensional REAL Lebesgue
Fourier BOX of the independent signed SOURCE integrand. -/
def parityOriginalSignedWindowPhysicalABoxAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
      parityOriginalSignedWindowFullSourceFourierAtU434
        d L E u signed band slot ξ
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- True independently signed historical e-window Fourier integrand
is integrable, before moving f0/f1 frequencies through the
20!-labelled finite Q sums and the original selected-e support. -/
theorem parity_original_signed_window_full_source_fourier_integrable_on_box434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    Integrable (parityOriginalSignedWindowFullSourceFourierAtU434
      d L E u signed band slot)
      (Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))) := by
  unfold parityOriginalSignedWindowFullSourceFourierAtU434
    parityOriginalSignedFullQWindowAllGateFourierAtU434
  apply integrable_finsetSum
  intro δ hδ
  apply integrable_finsetSum
  intro f hf
  by_cases hwin : parityOriginalHistoricalEWindow434 L E
    (paritySourceOrderedAllocatedE434 δ
      (parityActualSourceRemainingFullQTuple434 d L band slot f))
  · simp only [if_pos hwin]
    exact (parity_original_B590_all_gate_integrable_on_fourier_box434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ
      (fun i => (parityActualSourceRemainingFullQTuple434
        d L band slot f i).val) T).const_mul _
  · simp only [if_neg hwin]
    exact integrable_zero _ _ _

/-- Independent signed e-window Fourier Lebesgue integral equals
physical Parity(4.7) selected-e a_e * a_v convolution termwise,
with actual B509 H_0, source original full factorial and
a_e's e-only Fourier coefficient independent of physical v. -/
theorem parity_original_signed_window_A_box_eq_H_integral434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (T : ℝ) :
    let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
      Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    Integrable (parityOriginalSignedWindowSourceFourierHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁) μ ∧
    parityOriginalSignedWindowPhysicalABoxAtU434 d L E u signed band slot T =
      ∫ ξ, parityOriginalSignedWindowSourceFourierHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ ξ ∂μ := by
  dsimp only
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  have hOld := parity_original_signed_window_full_source_fourier_integrable_on_box434
    d L E u signed band slot T
  have hEq (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
      parityOriginalSignedWindowFullSourceFourierAtU434
        d L E u signed band slot ξ =
      parityOriginalSignedWindowSourceFourierHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ ξ :=
    parity_original_signed_window_full_source_integrand_eq_H434
      d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ ξ
  refine ⟨hOld.congr (Filter.Eventually.of_forall hEq),?_⟩
  unfold parityOriginalSignedWindowPhysicalABoxAtU434
  exact integral_congr_ae (Filter.Eventually.of_forall hEq)
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowB590Integral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Exact Fubini identity for ORIGINAL signed B590 historical selected-e
Fourier BOX: full labelled 20! Q factorial and P W1 epsilon sign,
B590 f0/f1 Fourier kernels and all histories δ. NO discarded Fourier
leakage is treated as zero, NO pointwise Fourier cutoff fabricated.
The true source e-window is E*L^-88 ≤e≤E, and the integral is genuine
N-dimensional Lebesgue on [-T,T]^N. -/
theorem parity_original_signed_inside_e_A_box_eq_real_fourier_integral434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T =
      parityOriginalSignedWindowPhysicalABoxAtU434
        d L E u signed band slot T := by
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let μ : Measure (Fin N → ℝ) :=
    Measure.pi (fun _ : Fin N => (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let F := ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
  let w : F → ℂ := fun f =>
    ((parityActualOriginalSignedFullTupleWeight434 d L u signed f:ℝ):ℂ)
  let R : F → Fin N → ℕ := fun f i =>
    (parityActualSourceRemainingFullQTuple434 d L band slot f i).val
  let G : (Fin N → Bool) → F → (Fin N → ℝ) → ℂ := fun δ f ξ =>
    parityOriginalB590AllGateFourierIntegrand434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ (R f) ξ
  let B : (Fin N → Bool) → F → ℂ := fun δ f =>
    parityOriginalB590AllGateFourierBox434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ (R f) T
  let P : (Fin N → Bool) → F → Prop := fun δ f =>
    parityOriginalHistoricalEWindow434 L E
      (paritySourceOrderedAllocatedE434 δ
        (parityActualSourceRemainingFullQTuple434 d L band slot f))
  have hI (δ : Fin N → Bool) (f : F) : Integrable (G δ f) μ :=
    parity_original_B590_all_gate_integrable_on_fourier_box434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ (R f) T
  have hIf (δ : Fin N → Bool) (f : F) :
      Integrable (fun ξ => if P δ f then w f * G δ f ξ else 0) μ := by
    by_cases hp : P δ f
    · simpa only [if_pos hp] using (hI δ f).const_mul (w f)
    · simp only [if_neg hp]
      have hFun : (fun _ : Fin N → ℝ => (0:ℂ)) =
          (0 : (Fin N → ℝ) → ℂ) := by
        funext ξ
        simp
      rw [hFun]
      exact integrable_zero (Fin N → ℝ) ℂ μ
  have hTerm (δ : Fin N → Bool) (f : F) :
      (∫ ξ, if P δ f then w f * G δ f ξ else 0 ∂μ) =
        if P δ f then w f * B δ f else 0 := by
    by_cases hp : P δ f
    · simp only [if_pos hp]
      exact integral_const_mul (w f) (G δ f)
    · simp only [if_neg hp]
      simp
  have hFin (f : F) :
      (∑ δ : Fin N → Bool, if P δ f then w f * B δ f else 0) =
        w f * (∑ δ ∈ parityOriginalB590InsideEWindowAssignments434
          d L E band slot f, B δ f) := by
    calc
      _ = ∑ δ ∈ (Finset.univ.filter (fun δ => P δ f)), w f * B δ f := by
        simp only [Finset.sum_filter]
      _ = _ := by
        have hSet : (Finset.univ.filter (fun δ : Fin N → Bool => P δ f)) =
            parityOriginalB590InsideEWindowAssignments434 d L E band slot f := by
          ext δ
          simp [P,parityOriginalHistoricalEWindow434,
            parityOriginalB590InsideEWindowAssignments434]
        rw [hSet,Finset.mul_sum]
  have hInt :
      parityOriginalSignedWindowPhysicalABoxAtU434
          d L E u signed band slot T =
        ∑ f : F, w f *
          (∑ δ ∈ parityOriginalB590InsideEWindowAssignments434
            d L E band slot f, B δ f) := by
    unfold parityOriginalSignedWindowPhysicalABoxAtU434
      parityOriginalSignedWindowFullSourceFourierAtU434
      parityOriginalSignedFullQWindowAllGateFourierAtU434
    change (∫ ξ, ∑ δ : Fin N → Bool,
      ∑ f : F, if P δ f then w f * G δ f ξ else 0 ∂μ) = _
    rw [integral_finsetSum Finset.univ (by
      intro δ hd
      exact integrable_finsetSum Finset.univ (by intro f hf; exact hIf δ f))]
    conv_lhs =>
      arg 2
      ext δ
      rw [integral_finsetSum Finset.univ (by intro f hf; exact hIf δ f)]
    simp_rw [hTerm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    exact hFin f
  rw [hInt]
  unfold parityOriginalSignedB590InsideEAtU434
  rfl

/-- The actual signed ORIGINAL inside-e B590 source, not an auxiliary
Fourier-derived object, is exactly the full N-dimensional integral
of historical selected-e physical H_0(vStar) with independent e-only
Fourier coefficient. The sign epsilon=1/E is kept separate throughout. -/
theorem parity_original_signed_inside_e_A_box_eq_physical_H_integral434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (T : ℝ) :
    let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
      Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    Integrable (parityOriginalSignedWindowSourceFourierHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁) μ ∧
    parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T =
      ∫ ξ, parityOriginalSignedWindowSourceFourierHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ ξ ∂μ := by
  have hH := parity_original_signed_window_A_box_eq_H_integral434
    d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ T
  dsimp only at hH ⊢
  refine ⟨hH.1,?_⟩
  rw [parity_original_signed_inside_e_A_box_eq_real_fourier_integral434]
  exact hH.2
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowMellinHBox -/

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
def parityOriginalSignedWindowSourceMellinHAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if parityOriginalHistoricalEWindow434 L E z.1 ∧
          z.1*z.2=sourceOriginalOrdinaryPart
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
theorem parity_original_signed_window_source_mellin_H_integrand_exact434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedWindowFullSourceFourierAtU434
        d L E u signed band slot ξ =
      parityOriginalSignedWindowSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ := by
  unfold parityOriginalSignedWindowFullSourceFourierAtU434
    parityOriginalSignedWindowSourceMellinHAtU434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_signed_fullQ_window_mellin_fourier_eq_e_aV434
    d L E hL hd u hu signed band slot δ ξ K alpha q χ σ₀ σ₁ rho

/-- Full true separately signed SELECTED-E original ε=1/E B590 Fourier BOX
at physical u>0, weighted by the actual Mellin phase u^(i rho),
equals an integrable physical e^(i rho)×v^(i rho) W1ε H_0(vStar)
integral over the REAL N-dimensional source f0/f1 Fourier box.
All source Q labels, factorials and P multiplicity signs retained. -/
theorem parity_original_signed_window_A_box_mellin_H_integral434
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
    Integrable (parityOriginalSignedWindowSourceMellinHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁ rho) μ ∧
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T =
      ∫ ξ, parityOriginalSignedWindowSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ ∂μ := by
  dsimp only
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  have hBase := parity_original_signed_inside_e_A_box_eq_physical_H_integral434
    d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ T
  have hEq (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
      sourceOriginalPureMellinPhase434 rho u *
        parityOriginalSignedWindowSourceFourierHAtU434
          d L E u signed band slot K alpha q χ σ₀ σ₁ ξ =
      parityOriginalSignedWindowSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ := by
    rw [←parity_original_signed_window_full_source_integrand_eq_H434
      d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ ξ]
    exact parity_original_signed_window_source_mellin_H_integrand_exact434
      d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ rho ξ
  have hInt : Integrable
      (parityOriginalSignedWindowSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ rho) μ :=
    (hBase.1.const_mul _).congr (Filter.Eventually.of_forall hEq)
  refine ⟨hInt,?_⟩
  rw [hBase.2]
  rw [←integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall hEq)
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEFirstIntrinsic -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Exact e-support extracted from the genuinely labelled reserved-Q
and skipped-prime source carrier, without inserting an arbitrary cut-off. -/
def parityOriginalIntrinsicEFirstValues434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) : Finset ℕ :=
  (parityOriginalReservedFullQEVStarSupport434 d L band slot δ).image Prod.fst

/-- Fibres of the actual e-source support: no q-label collision or
changed factorial weight is introduced when putting e first. -/
def parityOriginalIntrinsicEFirstFibre434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e : ℕ) : Finset (ℕ × ℕ) :=
  (parityOriginalReservedFullQEVStarSupport434 d L band slot δ).filter
    (fun z => z.1=e)

/-- Exact source finite-fibre Fubini. In particular no artificial
independence of the original e and vStar supports is assumed. -/
theorem parity_original_e_first_finset_product_reindex434
    (S : Finset (ℕ × ℕ)) (a : ℕ → ℂ) (b : (ℕ × ℕ) → ℂ) :
    (∑ z ∈ S, a z.1 * b z) =
      ∑ e ∈ S.image Prod.fst, a e *
        ∑ z ∈ S.filter (fun z => z.1=e), b z := by
  classical
  have hPartition (F : (ℕ × ℕ) → ℂ) :
      (∑ z ∈ S, F z) =
        ∑ e ∈ S.image Prod.fst, ∑ z ∈ S.filter (fun z => z.1=e), F z := by
    calc
      _ = ∑ z ∈ S, ∑ e ∈ S.image Prod.fst,
          if z.1=e then F z else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            have he : z.1 ∈ S.image Prod.fst :=
              Finset.mem_image.mpr ⟨z,hz,rfl⟩
            simp [he]
      _ = ∑ e ∈ S.image Prod.fst, ∑ z ∈ S,
          if z.1=e then F z else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_filter]
  rw [hPartition (fun z => a z.1 * b z)]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hzEq : z.1=e := (Finset.mem_filter.mp hz).2
  rw [hzEq]

/-- Genuine intrinsic physical coefficient at one endpoint (e,vStar)
at fixed source physical u. The gate is the EXACT ordinary Q-product
e*vStar = ordinaryPart(P,u), not a fabricated unrestricted e,v pair. -/
def parityOriginalIntrinsicEVStarAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (z : ℕ × ℕ) : ℂ :=
  if parityOriginalHistoricalEWindow434 L E z.1 ∧
      z.1*z.2=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed z.2
      (z.2*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
  else 0

/-- Original Parity 4.7 branch at a fixed B590 Fourier δ,ξ and Mellin rho:
a_e(e) is OUTSIDE the inner physical vStar fibre and has no dependence
on v, K, alpha, beta, chi, or the latter endpoint Ppart. -/
def parityOriginalSignedIntrinsicEFirstAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) : ℂ :=
  ∑ e ∈ parityOriginalIntrinsicEFirstValues434 d L band slot δ,
    parityOriginalSelectedEGateMellinCoefficient434 d L E band slot δ ξ rho e *
      ∑ z ∈ parityOriginalIntrinsicEFirstFibre434 d L band slot δ e,
        parityOriginalIntrinsicEVStarAtU434 d L E u signed band slot δ ξ rho z

/-- New literal sourceOriginalA signed Fourier-to-e-first H identity,
with TRUE factorial/source coefficient, selected historical e-window,
exact e*vStar=ordinaryPart(P,u), and alpha-independent H_0.
Proof uses the already verified true full-Q source, not the odd projector. -/
theorem parity_original_signed_fullQ_window_mellin_e_first_intrinsic434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) :
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot δ ξ =
      parityOriginalSignedIntrinsicEFirstAtU434
        d L E u signed band slot δ ξ rho := by
  have hSource := parity_original_signed_fullQ_window_mellin_fourier_eq_e_aV434
    d L E hL hd u hu signed band slot δ ξ
    (∅ : Finset ℕ) (fun _ => (0:ℂ)) 1 (1 : DirichletCharacter ℂ 1)
    0 0 rho
  rw [hSource]
  let S := parityOriginalReservedFullQEVStarSupport434 d L band slot δ
  let a : ℕ → ℂ := fun e =>
    parityOriginalSelectedEGateMellinCoefficient434 d L E band slot δ ξ rho e
  let b : (ℕ × ℕ) → ℂ := fun z =>
    parityOriginalIntrinsicEVStarAtU434 d L E u signed band slot δ ξ rho z
  calc
    (∑ z ∈ S, if parityOriginalHistoricalEWindow434 L E z.1 ∧
         z.1*z.2=sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        a z.1 * parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ ∅ (fun _ => (0:ℂ)) 1
          (1 : DirichletCharacter ℂ 1) 0 0 0 rho signed z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
        else 0) = (∑ z ∈ S, a z.1 * b z) := by
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hg : parityOriginalHistoricalEWindow434 L E z.1 ∧
              z.1*z.2=sourceOriginalOrdinaryPart
                (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
          · simp only [if_pos hg]
            unfold b parityOriginalIntrinsicEVStarAtU434
            simp only [if_pos hg]
            rw [parity_original_signed_physical_AV_is_intrinsic434]
          · have hb : b z = 0 := by
              unfold b parityOriginalIntrinsicEVStarAtU434
              rw [if_neg hg]
            simp only [if_neg hg, hb, mul_zero]
    _ = ∑ e ∈ S.image Prod.fst, a e *
        ∑ z ∈ S.filter (fun z => z.1=e), b z :=
      parity_original_e_first_finset_product_reindex434 S a b
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowBilinearHBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The exact **historical SELECTED-e physical** e-only × H(vStar) nonzero-Mellin rho
representation after integrating genuine B590 f0/f1 source Fourier
gates over the real N-dimensional box and summing all original
shift-two factorizations mn=u+2. Source W1/P odd parity and
reserved prime are carried in actual native H(vStar). -/
def parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalSignedWindowSourceMellinHAtU434 d L E u signed band slot K α 1
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
theorem parity_original_hminus2_signed_bilinear_mellin_inside_e_fourier_box_eq_source_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinInsideEBox434 d L E band slot
      Psi K J α β signed rho Y T =
    parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434 d L E band slot
      Psi K J α β signed rho Y T := by
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let H := fun (u : ℕ) (ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
    parityOriginalSignedWindowSourceMellinHAtU434 d L E u signed band slot K α 1
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
        parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T =
        ∫ ξ, H u ξ ∂μ :=
    parity_original_signed_window_A_box_mellin_H_integral434
      d L E hL hd u (hPos u hu) signed band slot K α 1
        (1 : DirichletCharacter ℂ 1) 0 0 rho T
  have hInt (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (fun ξ => H u ξ * C u) μ :=
    (hA u hu).1.mul_const _
  unfold parityOriginalShiftTwoSignedBilinearMellinInsideEBox434
    parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434
  calc
    (∑ u ∈ Finset.Ioc 0 Y,
      (sourceOriginalPureMellinPhase434 rho u *
        parityOriginalSignedB590InsideEAtU434 d L E u signed band slot T *
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

/-! ## OriginalSignedWindowHReindex -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Source-faithful finite family-to-selected-e extraction: a common
true endpoint carrier is the union of the original per-history images.
Every old history and every e with the same product is retained,
without assuming injectivity of the product map or losing multiplicity. -/
theorem parity_signed_finite_family_e_first434
    {A B : Type}
    (SA : Finset A) (SB : A → Finset B)
    (g : B → ℕ) (w : A → B → ℂ) :
    (∑ a ∈ SA, ∑ b ∈ SB a, w a b) =
    ∑ c ∈ SA.biUnion (fun a => (SB a).image g),
      ∑ a ∈ SA, sourceEndpointFibre (SB a) g (w a) c := by
  classical
  let M := SA.biUnion (fun a => (SB a).image g)
  have hsub (a : A) (ha : a ∈ SA) : (SB a).image g ⊆ M :=
    Finset.subset_biUnion_of_mem (fun a => (SB a).image g) ha
  have hzero (a : A) (c : ℕ) (hc : c ∉ (SB a).image g) :
      sourceEndpointFibre (SB a) g (w a) c = 0 := by
    unfold sourceEndpointFibre
    apply Finset.sum_eq_zero
    intro b hb
    have hb' := (Finset.mem_filter.mp hb).2
    exfalso
    exact hc (Finset.mem_image.mpr ⟨b,(Finset.mem_filter.mp hb).1,hb'⟩)
  calc
    _ = ∑ a ∈ SA, ∑ c ∈ (SB a).image g,
          sourceEndpointFibre (SB a) g (w a) c := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (Finset.sum_image' (s := SB a) (g := g)
          (f := fun c => sourceEndpointFibre (SB a) g (w a) c)
          (w a) (by intro b hb; rfl)).symm
    _ = ∑ a ∈ SA, ∑ c ∈ M,
          sourceEndpointFibre (SB a) g (w a) c := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_subset (hsub a ha)
          (by intro c hc hcNot; exact hzero a c hcNot)
    _ = _ := Finset.sum_comm
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowHEFirst -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- EXACT source signed historical e-window carrier of the physically
reserved Parity H(vStar): it is the union over TRUE B590 allocations δ
of actual source (e,vStar) images with E L^-88 <= e <= E.
No originally labelled Q tuple, repeated prime, or reserved p is lost. -/
def parityOriginalSignedWindowHEFirstSupport434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20) : Finset ℕ :=
  (Finset.univ : Finset (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool)).biUnion
    (fun δ => ((parityOriginalReservedFullQEVStarSupport434 d L band slot δ).filter
       (fun z => parityOriginalHistoricalEWindow434 L E z.1)).image Prod.fst)

/-- True selected physical e's satisfy both historical non-strict
endpoints: E L^-88 <= e <= E, even after full Q orbit/factorial
reindexing to the actual reserved-prime H(vStar) carrier. -/
theorem parity_original_signed_window_H_e_range434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (e : ℕ) (he : e ∈ parityOriginalSignedWindowHEFirstSupport434 d L E band slot) :
    E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E := by
  unfold parityOriginalSignedWindowHEFirstSupport434 at he
  rcases Finset.mem_biUnion.mp he with ⟨δ,hδ,heδ⟩
  rcases Finset.mem_image.mp heδ with ⟨z,hz,hE⟩
  have hwin := (Finset.mem_filter.mp hz).2
  rw [hE] at hwin
  exact hwin

/-- A genuine e-fibre at a fixed source u and Fourier allocation:
its e-only factor e^(i rho)*original B590 Fourier selected-Q gate
is explicitly independent of v, while the other factor is the full
physical v^(i rho) W1(v) epsilon(v) H_0(vStar), with original Ppart.
The u gate is retained, not presumed from arbitrary product support. -/
def parityOriginalSignedWindowHAtE434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (e : ℕ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    sourceEndpointFibre
      ((parityOriginalReservedFullQEVStarSupport434 d L band slot δ).filter
       (fun z => parityOriginalHistoricalEWindow434 L E z.1))
      Prod.fst
      (fun z => if z.1*z.2=sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
         parityOriginalSelectedEGateMellinCoefficient434
           d L E band slot δ ξ rho z.1 *
         parityOriginalReservedSignedPhysicalAV434
           d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed z.2
           (z.2*sourceOriginalPPrimePart
             (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
       else 0) e

/-- Complete original Parity(4.7) individually signed Fourier/Mellin
H_0(vStar) source regrouped with ACTUAL selected e OUTERMOST,
all f0/f1 allocations, labelled factorial, original W1/parity,
source product e*vStar=ordinary(P,u), reserved p and B509 residual.
True finite reindexing, not an unjustified independent coefficient
assumption. This is prior to Fourier integration and Cauchy. -/
theorem parity_original_signed_window_H_integrand_eq_e_first434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalSignedWindowSourceMellinHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ =
      ∑ e ∈ parityOriginalSignedWindowHEFirstSupport434 d L E band slot,
        parityOriginalSignedWindowHAtE434
          d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ e := by
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let F : (Fin N → Bool) → Finset (ℕ×ℕ) := fun δ =>
    (parityOriginalReservedFullQEVStarSupport434 d L band slot δ).filter
      (fun z => parityOriginalHistoricalEWindow434 L E z.1)
  let w : (Fin N → Bool) → (ℕ×ℕ) → ℂ := fun δ z =>
    if z.1*z.2=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
      parityOriginalSelectedEGateMellinCoefficient434
        d L E band slot δ ξ rho z.1 *
      parityOriginalReservedSignedPhysicalAV434
        d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed z.2
        (z.2*sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    else 0
  have hOne (δ : Fin N → Bool) :
      (∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
        if parityOriginalHistoricalEWindow434 L E z.1 ∧
          z.1*z.2=sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
          parityOriginalSelectedEGateMellinCoefficient434
            d L E band slot δ ξ rho z.1 *
          parityOriginalReservedSignedPhysicalAV434
            d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed z.2
            (z.2*sourceOriginalPPrimePart
              (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
        else 0) = ∑ z ∈ F δ, w δ z := by
    unfold F
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases he : parityOriginalHistoricalEWindow434 L E z.1
    · simp [he, w]
      rfl
    · simp [he, w]
  unfold parityOriginalSignedWindowSourceMellinHAtU434
    parityOriginalSignedWindowHAtE434 parityOriginalSignedWindowHEFirstSupport434
  calc
    (∑ δ : Fin N → Bool,
      ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
        if parityOriginalHistoricalEWindow434 L E z.1 ∧
          z.1*z.2=sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
          parityOriginalSelectedEGateMellinCoefficient434
            d L E band slot δ ξ rho z.1 *
          parityOriginalReservedSignedPhysicalAV434
            d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed z.2
            (z.2*sourceOriginalPPrimePart
              (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
        else 0) = ∑ δ : Fin N → Bool, ∑ z ∈ F δ, w δ z := by
          apply Finset.sum_congr rfl
          intro δ hδ
          exact hOne δ
    _ = ∑ e ∈ (Finset.univ : Finset (Fin N → Bool)).biUnion
          (fun δ => (F δ).image Prod.fst),
          ∑ δ : Fin N → Bool, sourceEndpointFibre (F δ) Prod.fst (w δ) e :=
      parity_signed_finite_family_e_first434 Finset.univ F Prod.fst w
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowPsiMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The literal historical Parity logarithmic Mellin kernel for the
original smooth Ψ, at the original scale x=exp L and the 2π Fourier
normalization. The only frequency is ρ=2πs; original source uses
σ_reserved=0 until sourced from an independent Fourier transform. -/
def parityOriginalSignedWindowPsiMellinKernel434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (s : ℝ) : ℂ :=
  (𝓕 (parityOriginalLogCutoff434
    (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
  Complex.exp (((-2*Real.pi*s*Real.log (Real.exp L) : ℝ) : ℂ)*Complex.I)

/-- TRUE original Parity Ψ(u/x) source Mellin inversion joined to the
individually SIGNED e-window full reserved-H_0 SOURCE integrand at
ANY genuine u>0, fixed original B590 multi-frequency ξ and any
signed ε=1/E, before h=-2 Cauchy.

The left has original Ψ(u/exp L) and rho=0 physical H; the right is
an actual one-dimensional Lebesgue integral with rho=2πs carried
in BOTH e-only Fourier coefficient and v-side physical H. No sigma
phase is inserted, and the paper's real Fourier 2π is retained. -/
theorem parity_original_signed_window_Psi_Mellin_H_exact434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : 0 < u) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64) :
    ((Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
      parityOriginalSignedWindowSourceMellinHAtU434 d L E u signed
        band slot K alpha q χ σ₀ σ₁ 0 ξ =
    ∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
       L Psi hSmooth hSupport s *
      parityOriginalSignedWindowSourceMellinHAtU434 d L E u signed
        band slot K alpha q χ σ₀ σ₁ (2*Real.pi*s) ξ := by
  let H : ℝ → ℂ := fun rho => parityOriginalSignedWindowSourceMellinHAtU434
    d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ
  let fhat : ℝ → ℂ := fun s => parityOriginalSignedWindowPsiMellinKernel434
    L Psi hSmooth hSupport s
  have hPhase0 : sourceOriginalPureMellinPhase434 (0:ℝ) u = 1 := by
    simp [sourceOriginalPureMellinPhase434]
  have hH0 := parity_original_signed_window_source_mellin_H_integrand_exact434
    d L E hL hd u hu.ne' signed band slot K alpha q χ σ₀ σ₁ 0 ξ
  rw [hPhase0,one_mul] at hH0
  have hH (s : ℝ) : sourceOriginalPureMellinPhase434 (2*Real.pi*s) u * H 0 =
      H (2*Real.pi*s) := by
    dsimp only [H]
    rw [←hH0]
    exact parity_original_signed_window_source_mellin_H_integrand_exact434
      d L E hL hd u hu.ne' signed band slot K alpha q χ σ₀ σ₁ (2*Real.pi*s) ξ
  have hCut := parity_actual_cutoff_mellin_integral434 (Real.exp L)
    (fun t : ℝ => (Psi t : ℂ)) u 1 (Real.exp_pos L) hu (by norm_num)
    hSmooth hSupport
  have hOne (s : ℝ) : sourceOriginalPureMellinPhase434 (-2*Real.pi*s) 1 = 1 := by
    simp [sourceOriginalPureMellinPhase434]
  have hCut' : (Psi ((u:ℝ)/Real.exp L):ℂ) =
      ∫ s : ℝ, fhat s * sourceOriginalPureMellinPhase434 (2*Real.pi*s) u := by
    simpa only [Nat.cast_one,mul_one,hOne,mul_one,
      parityOriginalSignedWindowPsiMellinKernel434,fhat] using hCut
  change (Psi ((u:ℝ)/Real.exp L):ℂ) * H 0 =
    ∫ s : ℝ, fhat s * H (2*Real.pi*s)
  calc
    _ = (∫ s : ℝ, fhat s * sourceOriginalPureMellinPhase434 (2*Real.pi*s) u) * H 0 := by
      rw [hCut']
    _ = ∫ s : ℝ,
        (fhat s * sourceOriginalPureMellinPhase434 (2*Real.pi*s) u) * H 0 := by
      rw [integral_mul_const]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [mul_assoc,hH]

/-- Exact physical source phase relation for the actual independently
signed historical e-selected B590 H_0 integrand, at true u>0 and any
rho. The source phase arises from the true Ψ Mellin decomposition. -/
theorem parity_original_signed_window_H_rho_eq_phase_mul_Hzero434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : 0 < u) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalSignedWindowSourceMellinHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁ rho ξ =
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedWindowSourceMellinHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ 0 ξ := by
  have h0 := parity_original_signed_window_source_mellin_H_integrand_exact434
    d L E hL hd u hu.ne' signed band slot K alpha q χ σ₀ σ₁ 0 ξ
  have hP0 : sourceOriginalPureMellinPhase434 (0:ℝ) u=1 := by
    simp [sourceOriginalPureMellinPhase434]
  rw [hP0,one_mul] at h0
  have hρ := parity_original_signed_window_source_mellin_H_integrand_exact434
    d L E hL hd u hu.ne' signed band slot K alpha q χ σ₀ σ₁ rho ξ
  rw [h0] at hρ
  exact hρ.symm

/-- Actual fixed-u signed H Mellin kernel is INTEGRABLE for the
original smooth Ψ, with full real 2π convention. The Schwartz
Fourier kernel dominates the true H_0 coefficient because the
source Mellin phase is exactly unimodular; there is no invented
L1 bound and no artificial source sigma. -/
theorem parity_original_signed_window_Psi_Mellin_H_integrable434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : 0 < u) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64) :
    Integrable (fun s : ℝ =>
       parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
       parityOriginalSignedWindowSourceMellinHAtU434
         d L E u signed band slot K alpha q χ σ₀ σ₁ (2*Real.pi*s) ξ) := by
  let f : ℝ → ℂ := fun s =>
    parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s
  let C : ℂ := parityOriginalSignedWindowSourceMellinHAtU434
    d L E u signed band slot K alpha q χ σ₀ σ₁ 0 ξ
  have hOld := parity_original_real_Psi_e_v_mellin_integrable434
    (Real.exp L) u 1 Psi hSmooth hSupport
  have hOne (s : ℝ) : sourceOriginalPureMellinPhase434 (2*Real.pi*s) 1=1 := by
    simp [sourceOriginalPureMellinPhase434]
  have hI : Integrable (fun s => f s *
      sourceOriginalPureMellinPhase434 (2*Real.pi*s) u) := by
    apply hOld.congr
    filter_upwards [] with s
    dsimp only [f,parityOriginalSignedWindowPsiMellinKernel434]
    rw [hOne]
    ring
  have hNew : Integrable (fun s =>
      (f s * sourceOriginalPureMellinPhase434 (2*Real.pi*s) u)*C) :=
    hI.mul_const C
  apply hNew.congr
  filter_upwards [] with s
  rw [parity_original_signed_window_H_rho_eq_phase_mul_Hzero434
    d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ (2*Real.pi*s) ξ]
  dsimp only [f,C]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowSourceToHAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- ORIGINAL h=-2 full 20!-labelled independent signed source
is O_A(x L^-A)-close to the REAL Parity (4.5) e-window FILTERED
Fourier/Mellin selected-e and physical a_v(v)=v^(i rho)W1(P,v)
epsilon(v)H_0(vStar) integral, individually for epsilon=1,E.
Actual alpha_m beta_n, Psi(u/x), all Q labels and B590 f0/f1
integrations are retained. This is NOT a universal E Theorem 4.1,
NOT a proof of Parity (4.17) and NOT a nonzero reserved sigma source. -/
theorem parity_eventually_original_signed_hminus2_source_to_selected_e_physical_H_box_all_log434
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
        parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_hminus2_source_to_inside_e_box_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  rw [←parity_original_hminus2_signed_bilinear_mellin_inside_e_fourier_box_eq_source_H434
    (sourceOriginalLiteralDepth 20 L) L E (by nlinarith [h.1]) rfl
    band slot Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEFirstBilinearHBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Complete source e-first integrand after all historical B590 Boolean
assignments, with intrinsic B509/prime convolution and both signed branches. -/
def parityOriginalSignedIntrinsicEFirstFullAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    parityOriginalSignedIntrinsicEFirstAtU434
      d L E u signed band slot δ ξ rho

/-- Every real source Fourier allocation has its exact independently
signed source → e-first × physical H_0(vStar) identity before squaring. -/
theorem parity_original_signed_full_source_mellin_e_first_intrinsic434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedWindowFullSourceFourierAtU434
        d L E u signed band slot ξ =
      parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot rho ξ := by
  unfold parityOriginalSignedWindowFullSourceFourierAtU434
    parityOriginalSignedIntrinsicEFirstFullAtU434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_signed_fullQ_window_mellin_e_first_intrinsic434
    d L E hL hd u hu signed band slot δ ξ rho

/-- The real signed e-first physical source integrand is independent
of outer α_m, β_n, χ even though its older API accepted K and α. -/
theorem parity_original_signed_window_mellin_H_eq_intrinsic_e_first434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (α : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalSignedWindowSourceMellinHAtU434
      d L E u signed band slot K α q χ σ₀ σ₁ rho ξ =
    parityOriginalSignedIntrinsicEFirstFullAtU434
      d L E u signed band slot rho ξ := by
  calc
    _ = sourceOriginalPureMellinPhase434 rho u *
        parityOriginalSignedWindowFullSourceFourierAtU434
          d L E u signed band slot ξ :=
      (parity_original_signed_window_source_mellin_H_integrand_exact434
        d L E hL hd u hu signed band slot K α q χ σ₀ σ₁ rho ξ).symm
    _ = _ := parity_original_signed_full_source_mellin_e_first_intrinsic434
      d L E hL hd u hu signed band slot rho ξ

/-- Historical original h=-2 B590 BOX: genuine original full α_mβ_n
convolution, retained Ψ(u/x), signed ε=1 or ε=E, FULL Fourier measure
and original e-first selected coefficient a_e(e) independent of the
physical coefficient a_v(v). This definition retains the exact source
u, vStar carrier and e*vStar=ordinaryPart(P,u) gate. -/
def parityOriginalShiftTwoSignedBilinearMellinIntrinsicEFirstHBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot rho ξ *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2))
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- Exact integrated Parity 4.7 e-first source for BOTH signed branches,
with no new axiom, no pointwise Fourier truncation, no injected σ. -/
theorem parity_original_signed_hminus2_mellin_H_box_eq_intrinsic_e_first434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434
      d L E band slot Psi K J α β signed rho Y T =
    parityOriginalShiftTwoSignedBilinearMellinIntrinsicEFirstHBox434
      d L E band slot Psi K J α β signed rho Y T := by
  unfold parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434
    parityOriginalShiftTwoSignedBilinearMellinIntrinsicEFirstHBox434
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply Finset.sum_congr rfl
  intro u hu
  have huPos : u ≠ 0 := (Finset.mem_Ioc.mp hu).1.ne'
  rw [parity_original_signed_window_mellin_H_eq_intrinsic_e_first434
    d L E hL hd u huPos signed band slot K α 1
      (1 : DirichletCharacter ℂ 1) 0 0 rho ξ]

/-- The actual source physical Q product equality e*vStar=ordinaryPart(P,u)
forces the precise original affine shift m*n=e*v+2, not an invented
independent e,v Cartesian product. -/
theorem parity_original_e_first_actual_shift_two434
    (L : ℝ) (u e vStar m n : ℕ) (hu : u ≠ 0)
    (hgate : e*vStar = sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (hmn : m*n = u+2) :
    m*n = e*(vStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)+2 := by
  have huEq : e*(vStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)=u := by
    calc
      _ = (e*vStar)*sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u := by ac_rfl
      _ = sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u *
          sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u := by rw [hgate]
      _ = u := source_original_ordinary_times_P_part _ u hu
  simpa only [huEq] using hmn
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEFirstAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Original Parity signed SOURCE approximation by a REAL B590 Fourier
BOX integral with true e-FIRST coefficient a_e(e) and alpha-independent
actual physical a_v(v)=v^(i rho) epsilon(v) W1(v) H_0(vStar).
Both signs are handled INDIVIDUALLY before any square. This carries
original h=-2, full 20!-labelled Q/P source, exact e-window,
beta/4 Ppart Rankin discard and outside-e Fourier leakage.
It does not yet prove the specialized Parity (4.17) correlation theorem,
full historical Psi Mellin inversion or Type II (4.2). -/
theorem parity_eventually_original_signed_hminus2_source_to_intrinsic_e_first_H_box_all_log434
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
        parityOriginalShiftTwoSignedBilinearMellinIntrinsicEFirstHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_hminus2_source_to_selected_e_physical_H_box_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  have hBound := h.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  have hL : 0 < L := by nlinarith [h.1]
  rw [parity_original_signed_hminus2_mellin_H_box_eq_intrinsic_e_first434
    (sourceOriginalLiteralDepth 20 L) L E hL rfl
    band slot Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowHEFirstBilinear -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The ACTUAL independently signed Parity (4.7) SOURCE physical H0
BOX Fourier/Mellin integral with selected e as the outermost
finite sum and all actual original h=-2 alpha_m beta_n fibres.
No postulated independence: a_e(e,delta,xi) is the source native
selected-Q Fourier Mellin coefficient; physical v bears W1/P parity
and the genuine reserved prime H_0(vStar). -/
def parityOriginalShiftTwoSignedBilinearMellinWindowHEFirst434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    ∑ e ∈ parityOriginalSignedWindowHEFirstSupport434 d L E band slot,
      ∑ u ∈ Finset.Ioc 0 Y,
        (parityOriginalSignedWindowHAtE434 d L E u signed band slot K α 1
          (1 : DirichletCharacter ℂ 1) 0 0 rho ξ e *
          (Psi ((u:ℝ)/Real.exp L):ℂ)) *
          (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α z.1*β z.2)
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- Exact N-dimensional REAL Lebesgue Fourier integrals and genuine
source selected-e product support: original signed physical H BOX
is equal to the selected e-FIRST H0 physical integral with full
h=-2 alpha_m beta_n convolution. Neither σ=0 nor the factorial
normalization has been modified. The ε=1/E signs are not combined. -/
theorem parity_original_signed_selected_e_H_box_eq_e_first434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434
      d L E band slot Psi K J α β signed rho Y T =
    parityOriginalShiftTwoSignedBilinearMellinWindowHEFirst434
      d L E band slot Psi K J α β signed rho Y T := by
  let M := parityOriginalSignedWindowHEFirstSupport434 d L E band slot
  let U := Finset.Ioc 0 Y
  let F : ℕ → ℕ → (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) → ℂ :=
    fun e u ξ => parityOriginalSignedWindowHAtE434
      d L E u signed band slot K α 1 (1 : DirichletCharacter ℂ 1) 0 0 rho ξ e
  let S : ℕ → ℂ := fun u => (Psi ((u:ℝ)/Real.exp L):ℂ)
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α z.1*β z.2
  unfold parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434
    parityOriginalShiftTwoSignedBilinearMellinWindowHEFirst434
  apply integral_congr_ae
  filter_upwards [] with ξ
  change (∑ u ∈ U,
      (parityOriginalSignedWindowSourceMellinHAtU434 d L E u signed
        band slot K α 1 (1 : DirichletCharacter ℂ 1) 0 0 rho ξ * S u) * B u) =
    ∑ e ∈ M, ∑ u ∈ U, (F e u ξ * S u) * B u
  calc
    _ = ∑ u ∈ U, ((∑ e ∈ M, F e u ξ) * S u) * B u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [parity_original_signed_window_H_integrand_eq_e_first434
        d L E u signed band slot K α 1 (1 : DirichletCharacter ℂ 1) 0 0 rho ξ]
    _ = ∑ u ∈ U, ∑ e ∈ M, (F e u ξ * S u) * B u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_mul,Finset.sum_mul]
    _ = _ := Finset.sum_comm
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowFinalEFirst -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- ORIGINAL full Q/P factorial source with each ε=1/E branch
is O_A(exp(L)*L^-A)-close to the *ACTUAL* historical e-FIRST physical
Parity (4.7) Fourier B' representation, with true selected-e support
E L^-88<=e<=E, true B590 f0/f1 gates, full Mellin rho,
real N-dimensional Lebesgue box, unchanged Ψ(u/exp L),
full h=-2 α_m β_n, reserved Q prime H_0 and independent signed
W1(P,v)ε(v). No new phase σ≠0, character correlation (4.17),
Cauchy/TypeII or Green64 conclusion is claimed. -/
theorem parity_eventually_original_signed_hminus2_source_to_e_first_physical_H_box_all_log434
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
        parityOriginalShiftTwoSignedBilinearMellinWindowHEFirst434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_hminus2_source_to_selected_e_physical_H_box_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
  rw [←parity_original_signed_selected_e_H_box_eq_e_first434
    (sourceOriginalLiteralDepth 20 L) L E band slot
    Psi K J α β signed rho ⌊2*Real.exp L⌋₊ L]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed rho
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEq417MarkedBridge -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The ACTUAL original Parity W1(P,n) is EXACTLY the full original
one-mark sourceMarkedWeight(q=1/2,ell=1,P,n) used in literal (4.17).
Every original P group is present, and the original distinct-prime
counts and reciprocal group masses agree without normalization loss. -/
theorem parity_original_W1_eq_eq417_one_marked434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (n : ℕ) :
    sourceOriginalW1 P n = sourceMarkedWeight (1/2:ℝ) 1 P n := by
  unfold sourceOriginalW1 sourceMarkedWeight
  apply Finset.prod_congr rfl
  intro g hg
  unfold shiftTwoOriginalGroupFactor groupHarmonic
  simp only [Nat.descFactorial_one, Nat.cast_one, pow_one]
  ring

/-- ORIGINAL signed ε=1 or E(v) from the complete Parity (4.7)
full P-prime valuations, including multiplicities, is exactly
literal Eq(4.17) groupSign(P,signed,v) for BOTH independent signs. -/
theorem parity_original_signed_epsilon_eq_eq417_groupSign434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (signed : Bool) (n : ℕ) :
    parityOriginalPSignedEpsilon434 (Finset.univ.biUnion P) signed n =
      groupSign P signed n := by
  cases signed <;> rfl

/-- Exact physical Parity (4.7) a_v(v) written in literal (4.17)
full marked-weight coordinates, independently for epsilon=1,E.
The W1 and signed parity are not assumed equal to the target or
left as abstract hypotheses, and the original reserved prime H_0
with complete factorial B509 residual is retained. -/
theorem parity_original_signed_aV_eq_eq417_marked_source434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ σ rho : ℝ) (signed : Bool) (vStar v : ℕ) :
    parityOriginalReservedSignedPhysicalAV434 d L band slot δ ξ
      K alpha q χ σ₀ σ₁ σ rho signed vStar v =
    sourceOriginalPureMellinPhase434 rho v *
      (((sourceMarkedWeight (1/2:ℝ) 1
          (sourceOriginalPAllActualBands 20 L) v *
        groupSign (sourceOriginalPAllActualBands 20 L) signed v):ℝ):ℂ) *
      parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar := by
  unfold parityOriginalReservedSignedPhysicalAV434
  rw [parity_original_W1_eq_eq417_one_marked434,
      parity_original_signed_epsilon_eq_eq417_groupSign434]

/-- At every positive physical v, the ORIGINAL nonzero source
Mellin exponential is EXACTLY the complex power used by Parity (4.17).
This derives the phase, rather than inserting a new reserved
p^(i sigma) without an original source identity. -/
theorem parity_original_signed_aV_eq_eq417_imaginary_marked434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ σ rho : ℝ) (signed : Bool)
    (vStar v : ℕ) (hv : 0 < v) :
    parityOriginalReservedSignedPhysicalAV434 d L band slot δ ξ
      K alpha q χ σ₀ σ₁ σ rho signed vStar v =
    imaginaryPower v rho *
      (((sourceMarkedWeight (1/2:ℝ) 1
          (sourceOriginalPAllActualBands 20 L) v *
        groupSign (sourceOriginalPAllActualBands 20 L) signed v):ℝ):ℂ) *
      parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar := by
  rw [parity_native_imaginary_pure_mellin434 v hv rho]
  exact parity_original_signed_aV_eq_eq417_marked_source434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ σ rho signed vStar v

/-- The two ORIGINAL independently signed source P weights are
literally Parity(4.17)'s product of two full original marked and parity
factors, for both signs before the Cauchy square. No e/v split,
additional P cap or sign cancellation is assumed in this identity. -/
theorem parity_original_signed_pair_W1_eq_eq417_marked434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (signed : Bool) (v vp : ℕ) :
    (sourceOriginalW1 P v *
       parityOriginalPSignedEpsilon434 (Finset.univ.biUnion P) signed v) *
    (sourceOriginalW1 P vp *
       parityOriginalPSignedEpsilon434 (Finset.univ.biUnion P) signed vp) =
    sourceMarkedWeight (1/2:ℝ) 1 P v *
       sourceMarkedWeight (1/2:ℝ) 1 P vp *
       groupSign P signed v * groupSign P signed vp := by
  rw [parity_original_W1_eq_eq417_one_marked434,
      parity_original_W1_eq_eq417_one_marked434,
      parity_original_signed_epsilon_eq_eq417_groupSign434,
      parity_original_signed_epsilon_eq_eq417_groupSign434]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalRoughGroupInvariance -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Original Parity (4.17) rough factor m carries NO group-prime
factor if every source group prime is ≤W and m is SOURCE W-rough.
No coprimality with an unspecified or fabricated modulus is assumed. -/
theorem parity_original_actual_rough_avoids_group_prime434
    (W : ℝ) (m p : ℕ) (hm : sourceD20Rough W m)
    (hp : p.Prime) (hpW : (p:ℝ)≤W) : ¬p∣m := by
  intro hd
  have hmin : m.minFac≤p := Nat.minFac_le_of_dvd hp.two_le hd
  have hreal : (m.minFac:ℝ)≤(p:ℝ) := by exact_mod_cast hmin
  exact (not_lt_of_ge (hreal.trans hpW)) hm.2

/-- At ALL source actual group primes, W-rough m is prime-free.
This is the exact arithmetic gateway for Parity §4.6's W1(z)=W1(v)
and epsilon(z)=epsilon(v). -/
theorem parity_original_actual_rough_prime_free_on_P434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (W : ℝ) (m : ℕ) (hm : sourceD20Rough W m)
    (hprime : ∀g p,p∈P g → p.Prime)
    (hW : ∀g p,p∈P g → (p:ℝ)≤W) :
    ∀p∈(Finset.univ.biUnion P), ¬p∣m := by
  intro p hp
  obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
  exact parity_original_actual_rough_avoids_group_prime434 W m p hm
    (hprime g p hpg) (hW g p hpg)

/-- In Parity's original W1, distinct group prime factors are counted
by divisibility. Multiplying the original physical v by a P-prime-
free rough cofactor m cannot change a SINGLE group's distinct-prime
count, even when original v has arbitrary repeated group primes. -/
theorem parity_original_group_omega_mul_prime_free434
    (P : Finset ℕ) (m v : ℕ)
    (hPrime : ∀p∈P,p.Prime)
    (hFree : ∀p∈P, ¬p∣m) :
    shiftTwoGroupOmega P (m*v) = shiftTwoGroupOmega P v := by
  unfold shiftTwoGroupOmega
  congr 1
  ext p
  by_cases hp : p∈P
  · have hpp := hPrime p hp
    have hpm := hFree p hp
    simp only [Finset.mem_filter, hp, true_and]
    rw [hpp.dvd_mul]
    tauto
  · simp [hp]

/-- Exact original Parity §4.6 identity W1(m*v)=W1(v) for a
source-rough cofactor and ALL actual original groups, with no
assumption about the multiplicities of group primes in v. -/
theorem parity_original_W1_mul_rough_cofactor434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (m v : ℕ)
    (hPrime : ∀g p,p∈P g → p.Prime)
    (hFree : ∀g p,p∈P g → ¬p∣m) :
    sourceOriginalW1 P (m*v) = sourceOriginalW1 P v := by
  unfold sourceOriginalW1
  apply Finset.prod_congr rfl
  intro g hg
  unfold shiftTwoOriginalGroupFactor
  rw [parity_original_group_omega_mul_prime_free434
    (P g) m v (hPrime g) (hFree g)]

/-- Exact original Parity §4.6 parity-exponent invariance, where
Ω over P counts prime factors WITH multiplicity. The source rough
factor m has valuation zero at every group prime; no assumption
that v is squarefree and no sign averaging is made. -/
theorem parity_original_P_parity_exponent_mul_prime_free434
    (P : Finset ℕ) (m v : ℕ)
    (hm : m≠0) (hv : v≠0)
    (hFree : ∀p∈P, ¬p∣m) :
    sourceOriginalPParityExponent P (m*v) =
      sourceOriginalPParityExponent P v := by
  unfold sourceOriginalPParityExponent
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.factorization_mul hm hv,Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (hFree p hp)]
  simp

/-- True original SOURCE signed epsilon=1 or E on each endpoint is
invariant under multiplication by P-rough m. This keeps the exact
parity with prime-power multiplicities and BOTH separate signs,
not a mod-2 surrogate or unproved external mask. -/
theorem parity_original_signed_epsilon_mul_prime_free434
    (P : Finset ℕ) (m v : ℕ)
    (hm : m≠0) (hv : v≠0)
    (hFree : ∀p∈P, ¬p∣m) (signed : Bool) :
    parityOriginalPSignedEpsilon434 P signed (m*v) =
      parityOriginalPSignedEpsilon434 P signed v := by
  cases signed
  · rfl
  · unfold parityOriginalPSignedEpsilon434
    rw [parity_original_P_parity_exponent_mul_prime_free434
      P m v hm hv hFree]

/-- Also the B633 core's signed groupSign(P) is EXACTLY unchanged,
not only the source epsilon notation. -/
theorem parity_original_group_sign_mul_prime_free434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (m v : ℕ) (hm : m≠0) (hv : v≠0)
    (hFree : ∀g p,p∈P g → ¬p∣m) (signed : Bool) :
    groupSign P signed (m*v) = groupSign P signed v := by
  cases signed
  · rfl
  · unfold groupSign
    rw [parity_original_P_parity_exponent_mul_prime_free434
      (Finset.univ.biUnion P) m v hm hv (by
        intro p hp
        obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
        exact hFree g p hpg)]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalRoughPPartInvariance -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14500000

/-- If the TRUE original rough cofactor m has no prime factors
in the original P-group union, multiplying its positive physical
v does not change which P-primes divide the complete physical
product z=m*v. This keeps ALL source repeated-prime powers in v. -/
theorem parity_original_P_prime_factors_mul_prime_free434
    (P : Finset ℕ) (m v : ℕ) (hm : m≠0) (hv : v≠0)
    (hFree : ∀p∈P, ¬p∣m) :
    (m*v).primeFactors ∩ P = v.primeFactors ∩ P := by
  have hEmpty : m.primeFactors ∩ P = ∅ := by
    ext p
    constructor
    · intro hp
      have h := Finset.mem_inter.mp hp
      exact False.elim (hFree p h.2 (Nat.mem_primeFactors.mp h.1).2.1)
    · intro hp
      simpa using hp
  rw [Nat.primeFactors_mul hm hv,Finset.union_inter_distrib_right,hEmpty]
  simp

/-- The TRUE original P-part with ALL prime-power multiplicities
is INVARIANT under multiplication by an original P-free cofactor m.
The prime-factor set and exact factorization exponents are proved
equal directly, not from an abstract coprimality axiom. -/
theorem parity_original_P_prime_part_mul_prime_free434
    (P : Finset ℕ) (m v : ℕ) (hm : m≠0) (hv : v≠0)
    (hFree : ∀p∈P, ¬p∣m) :
    sourceOriginalPPrimePart P (m*v) = sourceOriginalPPrimePart P v := by
  unfold sourceOriginalPPrimePart
  rw [parity_original_P_prime_factors_mul_prime_free434 P m v hm hv hFree]
  apply Finset.prod_congr rfl
  intro p hp
  have hFreep : ¬p∣m := hFree p (Finset.mem_inter.mp hp).2
  rw [Nat.factorization_mul hm hv,Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hFreep]
  simp

/-- The TRUE original ordinary (P-free) part of the physical
shifted target z=m*v is m times the ordinary part of v; no
prime-power multiplicity is dropped. This is the other half
of the needed source identity zStar=m*vStar in Parity (4.16).
It is proved by canceling the actual nonzero full P-part after
source factorization, never by a hypothetical factorization gate. -/
theorem parity_original_ordinary_part_mul_prime_free434
    (P : Finset ℕ) (m v : ℕ) (hm : m≠0) (hv : v≠0)
    (hFree : ∀p∈P, ¬p∣m) :
    sourceOriginalOrdinaryPart P (m*v) =
      m*sourceOriginalOrdinaryPart P v := by
  have hp := parity_original_P_prime_part_mul_prime_free434 P m v hm hv hFree
  have hsplitMV := source_original_ordinary_times_P_part P (m*v) (mul_ne_zero hm hv)
  have hsplitV := source_original_ordinary_times_P_part P v hv
  have hPNz : sourceOriginalPPrimePart P v≠0 := by
    intro hz
    rw [hz,mul_zero] at hsplitV
    exact hv hsplitV.symm
  have hPP : 0 < sourceOriginalPPrimePart P v := Nat.pos_of_ne_zero hPNz
  apply Nat.mul_right_cancel hPP
  calc
    sourceOriginalOrdinaryPart P (m*v)*sourceOriginalPPrimePart P v =
      sourceOriginalOrdinaryPart P (m*v)*sourceOriginalPPrimePart P (m*v) := by rw [hp]
    _ = m*v := hsplitMV
    _ = m*(sourceOriginalOrdinaryPart P v*sourceOriginalPPrimePart P v) := by rw [hsplitV]
    _ = (m*sourceOriginalOrdinaryPart P v)*sourceOriginalPPrimePart P v := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPurePpart -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- A true ORIGINAL P-free ordinary part of positive source u has
NO prime factor belonging to P. The proof uses the actual finite
product over primeFactors(u)\\P, preserving every exponent ν_p(u),
not a fake disjoint-primes assumption. -/
theorem parity_original_ordinary_part_avoids_P_prime434
    (P : Finset ℕ) (u p : ℕ) (hu : u≠0)
    (hP : p∈P) (hp : p.Prime) :
    ¬p ∣ sourceOriginalOrdinaryPart P u := by
  have hCop : p.Coprime (sourceOriginalOrdinaryPart P u) := by
    unfold sourceOriginalOrdinaryPart
    apply Nat.Coprime.prod_right
    intro r hr
    have hdata := Finset.mem_sdiff.mp hr
    have hrPrime : r.Prime := (Nat.mem_primeFactors.mp hdata.1).1
    have hpR : p≠r := by
      intro heq
      apply hdata.2
      rw [←heq]
      exact hP
    have hpr : p.Coprime r := (Nat.coprime_primes hp hrPrime).mpr hpR
    exact hpr.pow_right (u.factorization r)
  exact (hp.coprime_iff_not_dvd).mp hCop

/-- Original finite P-prime collection contains only primes, so
its ordinary component contains NONE of their prime factors.
This is the genuine P-cutoff used by Parity, not an arbitrary finite
set containing composite numbers. -/
theorem parity_original_ordinary_part_P_prime_free434
    (P : Finset ℕ) (u : ℕ) (hu : u≠0)
    (hP : ∀p∈P,p.Prime) :
    ∀p∈P,¬p∣sourceOriginalOrdinaryPart P u := by
  intro p hp
  exact parity_original_ordinary_part_avoids_P_prime434 P u p hu hp (hP p hp)

/-- The ORIGINAL selected-P component of u is nonzero whenever
source u>0, including all repeated source group-prime powers. -/
theorem parity_original_P_prime_part_nonzero434
    (P : Finset ℕ) (u : ℕ) (hu : u≠0) :
    sourceOriginalPPrimePart P u≠0 := by
  intro hp0
  have h := source_original_ordinary_times_P_part P u hu
  rw [hp0,mul_zero] at h
  exact hu h.symm

/-- The actual original ordinary part of a positive source integer
is positive. This is required to cancel its P-prime part safely. -/
theorem parity_original_ordinary_part_nonzero434
    (P : Finset ℕ) (u : ℕ) (hu : u≠0) :
    sourceOriginalOrdinaryPart P u≠0 := by
  intro ho0
  have h := source_original_ordinary_times_P_part P u hu
  rw [ho0,zero_mul] at h
  exact hu h.symm

/-- The SOURCE P-part of the genuinely P-free ordinary component
is EXACTLY 1, not merely supported on small primes. -/
theorem parity_original_Ppart_of_ordinary_eq_one434
    (P : Finset ℕ) (u : ℕ) (hu : u≠0)
    (hP : ∀p∈P,p.Prime) :
    sourceOriginalPPrimePart P (sourceOriginalOrdinaryPart P u)=1 := by
  have hFree := parity_original_ordinary_part_P_prime_free434 P u hu hP
  have hSet :
      (sourceOriginalOrdinaryPart P u).primeFactors∩P=∅ := by
    ext p
    constructor
    · intro hp
      obtain ⟨hFactor,hPin⟩ := Finset.mem_inter.mp hp
      exact (hFree p hPin) (Nat.mem_primeFactors.mp hFactor).2.1 |>.elim
    · intro hp
      simpa using hp
  unfold sourceOriginalPPrimePart
  rw [hSet]
  simp

/-- Original physical P-part is idempotent:
Ppart(P,Ppart(P,u))=Ppart(P,u). This follows from the actual full
factorization u=ordinary(P,u)*Ppart(P,u) and SOURCE prime-free
ordinary component, not from an unverified multiplicativity axiom. -/
theorem parity_original_Ppart_idempotent434
    (P : Finset ℕ) (u : ℕ) (hu : u≠0)
    (hP : ∀p∈P,p.Prime) :
    sourceOriginalPPrimePart P (sourceOriginalPPrimePart P u)=
      sourceOriginalPPrimePart P u := by
  let o := sourceOriginalOrdinaryPart P u
  let q := sourceOriginalPPrimePart P u
  have hO : o≠0 := parity_original_ordinary_part_nonzero434 P u hu
  have hQ : q≠0 := parity_original_P_prime_part_nonzero434 P u hu
  have hFree : ∀p∈P,¬p∣o := parity_original_ordinary_part_P_prime_free434 P u hu hP
  have hPart := parity_original_P_prime_part_mul_prime_free434 P o q hO hQ hFree
  have hSplit : o*q=u := source_original_ordinary_times_P_part P u hu
  have hU : sourceOriginalPPrimePart P (o*q)=q := by
    rw [hSplit]
  exact hPart.symm.trans hU

/-- The actual P-free ordinary part of a PURE P-part is exactly
one. This is the native original factorization identity needed
for the reserved skipped-Q vStar = ordinary(P,v) interface. -/
theorem parity_original_ordinary_of_Ppart_eq_one434
    (P : Finset ℕ) (u : ℕ) (hu : u≠0)
    (hP : ∀p∈P,p.Prime) :
    sourceOriginalOrdinaryPart P (sourceOriginalPPrimePart P u)=1 := by
  let q := sourceOriginalPPrimePart P u
  have hQ : q≠0 := parity_original_P_prime_part_nonzero434 P u hu
  have hSplit := source_original_ordinary_times_P_part P q hQ
  have hId := parity_original_Ppart_idempotent434 P u hu hP
  change sourceOriginalPPrimePart P q = q at hId
  rw [hId] at hSplit
  apply Nat.mul_right_cancel (Nat.pos_of_ne_zero hQ)
  simpa only [one_mul] using hSplit

/-- The literal original physical Q-gate e*vStar=ordinary(P,u)
with positive u forces vStar to be P-prime-free. This is DERIVED
from the source Q/P equality and the exact prime-power factorization;
it is not inserted as a separate prime-slot assumption. -/
theorem parity_original_source_vStar_prime_free434
    (P : Finset ℕ) (u e vStar : ℕ) (hu : u≠0)
    (hP : ∀p∈P,p.Prime)
    (hgate : e*vStar=sourceOriginalOrdinaryPart P u) :
    ∀p∈P,¬p∣vStar := by
  have hFree := parity_original_ordinary_part_P_prime_free434 P u hu hP
  intro p hp hd
  have hDiv : p∣sourceOriginalOrdinaryPart P u := by
    rw [←hgate]
    exact dvd_mul_of_dvd_right hd e
  exact hFree p hp hDiv

/-- EXACT original Parity §4.6 reserved-Q/skipped-Q source relation:
  v=vStar*Ppart(P,u)  =>  ordinary(P,v)=vStar,
provided e*vStar=ordinary(P,u) on TRUE positive physical u.
The Q residue and its multiplicity are never removed by hand;
this is derived using actual ordinary/Ppart idempotence and
P-prime-free vStar. -/
theorem parity_original_source_vStar_eq_ordinary_physical_v434
    (P : Finset ℕ) (u e vStar : ℕ) (hu : u≠0)
    (hP : ∀p∈P,p.Prime)
    (hgate : e*vStar=sourceOriginalOrdinaryPart P u) :
    sourceOriginalOrdinaryPart P
      (vStar*sourceOriginalPPrimePart P u)=vStar := by
  let q := sourceOriginalPPrimePart P u
  have hQ : q≠0 := parity_original_P_prime_part_nonzero434 P u hu
  have hO : sourceOriginalOrdinaryPart P u≠0 :=
    parity_original_ordinary_part_nonzero434 P u hu
  have hVS : vStar≠0 := by
    intro hz
    rw [hz,mul_zero] at hgate
    exact hO hgate.symm
  have hFree := parity_original_source_vStar_prime_free434 P u e vStar hu hP hgate
  have hOne := parity_original_ordinary_of_Ppart_eq_one434 P u hu hP
  have hMul := parity_original_ordinary_part_mul_prime_free434 P vStar q hVS hQ hFree
  change sourceOriginalOrdinaryPart P (vStar*q)=vStar*sourceOriginalOrdinaryPart P q at hMul
  rw [hOne,mul_one] at hMul
  exact hMul
end Green64Analytic.Parity

end

end

