module

public import Green64.Library.Sieve.Foundations.Part026
public import Green64.Library.Sieve.Foundations.Part024
public import Green64.Library.Weights.Part005
public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Sieve.Foundations.Part025
public import Green64.Library.Sieve.Foundations.Part020
public import Green64.Library.Sieve.Foundations.Part023

@[expose] public section

/-!
# Sieve / Foundations / Part027

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalFullOddFilteredFourierOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- ORIGINAL Parity(4.16) physical full odd-e/n B633 Fourier
correlation, with ONLY the genuine physically attained binary Z
cells possessing some NONZERO constructed source smoothing
eta_e(e/E)eta_n(n/V). Each cell's B633 kernel, cχ, Q/P/B509,
real Fourier 2π, alpha and both signed epsilons are unchanged.
This is the correct support on which to subsequently truncate
the 3D Fourier frequency and use the source-proved uniform tails. -/
def parityOriginalHistoricalFullOddFilteredB633FourierOuter434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b) : ℂ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          (∑Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
              d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            ∫ζ : EuclideanSpace ℝ (Fin 3),
              parityOriginalHistoricalActualB6333DFourierCell434
                d L U E V hL Z k band slot δ ξ rho α signed Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) χ
                buf a b hBufSmooth hBufSupport ζ)

/-- EXACT original FULL odd-e/n Parity(4.16) B633 Fourier sum may be
restricted to physically attained cells with SOME nonzero source
smoothing weight, because all excluded cells' COMPLETE Fourier
integrals vanish by the source-native true 3D Fourier inversion.

This is an exact complex identity on the full original signed
source; it does NOT claim a truncated Fourier integral vanishes
on a zero-weight cell. Thus subsequent low-frequency truncation
may be performed ONLY after this equality, avoiding a mathematically
invalid high-frequency tail omission or signed-subset inequality. -/
theorem parity_original_historical_full_odd_B633_outer_eq_nonzero_weight434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    parityOriginalHistoricalFullOddB633FourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hBufSmooth hBufSupport =
    parityOriginalHistoricalFullOddFilteredB633FourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hBufSmooth hBufSupport := by
  unfold parityOriginalHistoricalFullOddB633FourierOuter434
    parityOriginalHistoricalFullOddFilteredB633FourierOuter434
  apply Finset.sum_congr rfl
  intro e he
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  apply Finset.sum_congr rfl
  intro m hm
  have hmDyad := hDyad m hm
  have hDyad' : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
    intro mp hmp
    exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro χ hχ
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let S := (parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)
  let P : ℕ → Prop := fun Z => ∃q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0
  let F : ℕ → ℂ := fun Z =>
      ∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginalHistoricalActualB6333DFourierCell434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hBufSmooth hBufSupport ζ
  change (parityShiftTwoMaskCoefficient434 k.natAbs χ)*(∑Z∈S,F Z) =
    (parityShiftTwoMaskCoefficient434 k.natAbs χ)*(∑Z∈S.filter P,F Z)
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Z hZ
  change F Z = if P Z then F Z else 0
  by_cases hp : P Z
  · simp only [if_pos hp]
  · have hNot : Z∉parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k := by
      intro hmem
      exact hp (Finset.mem_filter.mp hmem).2
    have hFullZero : F Z=0 :=
      parity_original_historical_full_odd_zero_weight_B633_full_fourier434
        d L U E V hL band slot δ ξ rho α signed Y e m K J k Z χ heOdd
        hU hE hV hmDyad.1 hmDyad.2.le hDyad' hZ hNot
        buf a b hBufSmooth hBufSupport hBufOne
    simp only [if_neg hp,hFullZero]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFilteredB633CellTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- True original Parity (4.16) B633 Fourier-ball integral on one
actual h=-2 physical e,m,k,Z,chi cell. The B633 pair kernel and
all source Q/P and character conjugations are unchanged. -/
def parityOriginalHistoricalActualB633FourierBall434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L) (Z : ℕ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ, buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℂ :=
  ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
    parityOriginalHistoricalActualB6333DFourierCell434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport ζ

/-- A mathematically exact **per physical k/Z cell** B633 Fourier
truncation inequality. The FULL integral of the literal B633 two-core
kernel equals the actual source weighted h=-2 Cauchy pair times
original conjugate chi(m); the truncated integral has the SAME
pointwise integrand. Thus the cell truncation error is bounded by
the REAL source previously proved eta_e,L eta_n pre-Fourier error,
with factor ||chi(m)||<=1 and NO independent character count:

 ||int_{R^3} B633_cell - int_{||ζ||<=T} B633_cell||
   <= sourceOriginalActualKZ416FourierError.

This is not a Fourier tail estimate on the FULL unrestricted Parity
4.17 sum, only the exact physically supported B633 source cell. -/
theorem parity_original_historical_true_B633_fourier_ball_error_le_source434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hZ : 0<Z) (H : ℕ) (T : ℝ) (hT : 0<T) :
    ‖(∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginalHistoricalActualB6333DFourierCell434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hSmooth hSupport ζ) -
      parityOriginalHistoricalActualB633FourierBall434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport T‖ ≤
    parityOriginalHistoricalActualKZ416FourierError434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport T := by
  let c : ℂ := star (χ (m : ZMod (2*k.natAbs)))
  let W : ℂ := parityOriginalHistoricalActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ
  let f : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
    parityOriginalHistoricalActualKZTwistedFourierIntegrand434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport ζ
  have hFull := parity_original_historical_true_k_Z_chi_B633_fourier_integral434
    d L U E V hL band slot δ ξ rho α signed Y e m K J k Z χ he
    hU hE hV hmLo hmHi hDyad
    buf a b hSmooth hSupport hBufOne hZ
  have hBall : parityOriginalHistoricalActualB633FourierBall434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport T =
      c * ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ := by
    unfold parityOriginalHistoricalActualB633FourierBall434
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ζ
    exact (parity_original_historical_actual_k_z_3d_fourier_eq_B633434
      d L U E V hL band slot δ ξ K J α Y e m he k Z χ rho signed
      hU hZ buf a b hSmooth hSupport ζ).symm
  have hC : ‖c‖≤1 := by
    change ‖star (χ (m : ZMod (2*k.natAbs)))‖ ≤ 1
    rw [norm_star]
    exact DirichletCharacter.norm_le_one χ _
  have hD : 0≤‖W-(∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ)‖ :=
    norm_nonneg _
  have hCauchy : ‖c‖*‖W-(∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ)‖ ≤
      ‖W-(∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ)‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hC hD]
  rw [←hFull,hBall]
  change ‖c*W - c*(∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ)‖ ≤ _
  rw [←mul_sub,norm_mul]
  exact hCauchy
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddB633TruncatedCell -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Literal original Parity(4.16) B633 physical k/Z character
three-dimensional Fourier *BALL-TRUNCATED* integral. This is
constructed ONLY on the genuine nonzero-weight source cells of
the preceding support theorem, not on every formally possible
Z interval. Full source Q/P/B509 and h=-2 complex signed
coefficients, 2π U/U/Z normalization and chi conjugation remain. -/
def parityOriginalHistoricalFullOddB633TruncatedCell434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (Z : ℕ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℂ :=
  ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
    parityOriginalHistoricalActualB6333DFourierCell434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hBufSmooth hBufSupport ζ

/-- The original B633 physically literal Parity(4.16) finite
frequency-ball approximation error is at most the already native
proved source physical χ k/Z Fourier truncation error: the
outer actual conjugate character starχ(m) has norm ≤1 and its
position is exactly tracked by source-to-B633 integrand equality.
No spectral cancellation or use of 4.17 is needed to prove this,
including negative k and either original signed ε branch. -/
theorem parity_original_historical_full_odd_B633_truncated_error_le_source434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (Z : ℕ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (hU : 0<U) (hZ : 0<Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) :
    ‖star (χ (m : ZMod (2*k.natAbs))) *
      parityOriginalHistoricalActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ -
      parityOriginalHistoricalFullOddB633TruncatedCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport T‖ ≤
    parityOriginalHistoricalActualKZ416FourierError434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport T := by
  let B : ℂ := ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginalHistoricalActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport ζ
  let I : ℂ := ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginalHistoricalActualKZTwistedFourierIntegrand434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport ζ
  let W : ℂ := parityOriginalHistoricalActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ
  let c : ℂ := star (χ (m : ZMod (2*k.natAbs)))
  have hIntegrand (ζ : EuclideanSpace ℝ (Fin 3)) :
      c * parityOriginalHistoricalActualKZTwistedFourierIntegrand434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport ζ =
      parityOriginalHistoricalActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport ζ := by
    have hh := parity_original_historical_actual_k_z_3d_fourier_eq_B633434
      d L U E V hL band slot δ ξ K J α Y e m he k Z χ rho signed
      hU hZ buf a b hSmooth hSupport ζ
    simpa only [parityOriginalHistoricalActualB6333DFourierCell434] using hh
  have hInt : B=c*I := by
    dsimp [B,I,c]
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ζ
    exact (hIntegrand ζ).symm
  change ‖c*W-B‖ ≤ ‖W-I‖
  rw [hInt,←mul_sub,norm_mul]
  have hχ : ‖c‖≤1 := by
    have hh : ‖star (χ (m : ZMod (2*k.natAbs)))‖ ≤ 1 := by
      rw [norm_star]
      exact DirichletCharacter.norm_le_one χ _
    exact hh
  calc
    ‖c‖*‖W-I‖ ≤ 1*‖W-I‖ :=
      mul_le_mul_of_nonneg_right hχ (norm_nonneg _)
    _ = ‖W-I‖ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddB633TruncUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Genuine original Parity(4.16) full odd-e/n B633 **BALL-TRUNCATED**
source approximation with fully PROVED per-cell error:
 Acoef² Z L^(2CW1+256+K0+90) * C_H L^[5(K0+90)(H+P+1)]/T^H
on ANY populated actual k/Z physical source cell having a nonzero
constructed eta_e,L*eta_n weight witness. The complex outside
conjugate χ(m) remains and has norm ≤1. No guessed source B_H,
no old sparse selected-Q e/n window, no truncation of all-zero
source cells and no Parity(4.17) spectral saving are assumed. -/
theorem parity_eventually_original_full_odd_B633_ball_trunc_error_uniform434
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
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈parityOriginalHistoricalFullOddEEnvelope434 E → m∈K →
      ∀ (q : ℕ×ℕ),
      q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k Z →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0 →
      ∀ (χ : DirichletCharacter ℂ (2*k.natAbs))
        (A R : ℝ) (hA : 0<A) (hR : 1≤R)
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
      ‖star (χ (m : ZMod (2*k.natAbs))) *
          parityOriginalHistoricalActualKZPhysicalWeightedSource434
            (sourceOriginalLiteralDepth 20 L) L E V hLw
            band slot δ ξ rho α signed ⌊2*Real.exp L⌋₊ e m K
            (parityOriginalHistoricalFullNEnvelope434 V) k Z χ -
        parityOriginalHistoricalFullOddB633TruncatedCell434
          (sourceOriginalLiteralDepth 20 L) L U E V hLw Z k band slot δ ξ
          rho α signed ⌊2*Real.exp L⌋₊ e m K
          (parityOriginalHistoricalFullNEnvelope434 V) χ
          buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ ≤
      Acoef^2*(Z:ℝ)*L^(2*parityOriginalW1PolylogExponent434+256+K0+90) *
        (parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport H *
          L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H) := by
  filter_upwards [parity_eventually_original_full_odd_k_z_416_tail_uniform434
    K0 hK0] with L hBound
  refine ⟨hBound.1,hBound.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hAcoef hAlpha
    hU hV hUV hScale hDyad e m k Z he heMem hm q hq hw
    χ A R hA hR buf hSmooth hSupport hOne hCubeR H hLargeE hLargeN T hT
  let d := sourceOriginalLiteralDepth 20 L
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := ⌊2*Real.exp L⌋₊
  have hZData := (Finset.mem_filter.mp hq).2.2
  have hZscale := hZData.2
  have hZPos := parity_original_historical_actual_z_in_own_dyad434
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hZData.1
  rw [hZscale] at hZPos
  have hOld := hBound.2.2 hLw band slot δ ξ rho U V E K α signed Acoef
    hAcoef hAlpha hU hV hUV hScale hDyad e m k Z he heMem hm q hq hw
    χ A R hA hR buf hSmooth hSupport hOne hCubeR H hLargeE hLargeN T hT
  have hTransfer := parity_original_historical_full_odd_B633_truncated_error_le_source434
    d L U E V hLw Z k band slot δ ξ rho α signed Y e m K J χ he
    hU hZPos.1 buf (-Real.log A) (Real.log A) hSmooth hSupport T
  exact hTransfer.trans hOld
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddFilteredB633TailAggregate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- Finite, COMPLEX signed Fourier families may be truncated as a
whole by summing ACTUAL per-cell nonnegative error bounds. The
finite image, mask and character coefficients are not modified. -/
theorem parity_original_historical_norm_sum_sub_le_finite_error434
    {ι : Type*} (s : Finset ι) (F G : ι → ℂ) (err : ι → ℝ)
    (h : ∀i∈s,‖F i-G i‖≤err i) :
    ‖(∑i∈s,F i)-(∑i∈s,G i)‖ ≤ ∑i∈s,err i := by
  calc
    _ = ‖∑i∈s,(F i-G i)‖ := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑i∈s,err i := norm_sum_le_of_le s h

/-- The TRUE low-frequency truncation of the source FILTERED
full odd-e Parity B633 TWO-CORE 3D Fourier outer. Every k,Z,chi
cell is exactly the one chosen from nonzero actual source
eta_e,L(e/E)*eta_n(n/V) weights BEFORE Fourier truncation; no
zero-weight cell is spuriously thrown away after truncation. -/
def parityOriginalHistoricalFullOddFilteredB633BallOuter434
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
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℂ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          (∑Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
              d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            parityOriginalHistoricalActualB633FourierBall434
              d L U E V hL Z k band slot δ ξ rho α signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupport T)

/-- Literal nonnegative full-e,m,k,chi,Z source error budget for
the FILTERED original physically populated B633 outer. The actual
Parity(2.6) cchi is charged by its exact absolute norm; no invented
#characters factor and no bound on the full (4.17) correlation. -/
def parityOriginalHistoricalFullOddFilteredB633TailMass434
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
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℝ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
              d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            parityOriginalHistoricalActualKZ416FourierError434
              d L U E V hL Z k band slot δ ξ rho α signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupport T)

/-- EXACT FINITE ORIGINAL SOURCE PARITY(4.16) FOURIER TRUNCATION:

 ‖FullOddB633FilteredFourierOuter - FullOddB633FilteredBallOuter‖
 <= sum_(real full-odd e,m,k,chi,Z nonzero source cells)
      |cchi| * genuine source eta_e,L eta_n Fourier tail error.

All terms are literally the original B633 physical pair at z,z+2k
and original Q/P/B509 skipped-Q, b629 fine alpha and signed epsilon.
The only estimates applied are the triangle inequality and
‖chi(m)‖≤1; no independent correlation saving or unsupported
full 4.17 source mask is asserted. This is precisely the native
algebra needed to SUM the already PROVED source polynomial per-cell
B_H/T^H errors without discarding nonzero truncated integrals. -/
theorem parity_original_historical_full_odd_filtered_B633_ball_error_le_mass434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (T : ℝ) (hT : 0<T) :
    ‖parityOriginalHistoricalFullOddFilteredB633FourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hSmooth hSupport -
      parityOriginalHistoricalFullOddFilteredB633BallOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hSmooth hSupport T‖ ≤
    parityOriginalHistoricalFullOddFilteredB633TailMass434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hSmooth hSupport T := by
  unfold parityOriginalHistoricalFullOddFilteredB633FourierOuter434
    parityOriginalHistoricalFullOddFilteredB633BallOuter434
    parityOriginalHistoricalFullOddFilteredB633TailMass434
  apply parity_original_historical_norm_sum_sub_le_finite_error434
  intro e he
  apply parity_original_historical_norm_sum_sub_le_finite_error434
  intro m hm
  apply parity_original_historical_norm_sum_sub_le_finite_error434
  intro k hk
  apply parity_original_historical_norm_sum_sub_le_finite_error434
  intro χ hχ
  let S := parityOriginalHistoricalFullOddNonzeroWeightZCells434
    d L E V hL band slot δ Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k
  let c := parityShiftTwoMaskCoefficient434 k.natAbs χ
  let F : ℕ → ℂ := fun Z =>
    ∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginalHistoricalActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K
        (parityOriginalHistoricalFullNEnvelope434 V) χ
        buf a b hSmooth hSupport ζ
  let G : ℕ → ℂ := fun Z =>
    parityOriginalHistoricalActualB633FourierBall434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) χ
      buf a b hSmooth hSupport T
  let Err : ℕ → ℝ := fun Z =>
    parityOriginalHistoricalActualKZ416FourierError434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) χ
      buf a b hSmooth hSupport T
  have hCell : ∀Z∈S, ‖F Z-G Z‖≤Err Z := by
    intro Z hZ
    have hData := (Finset.mem_filter.mp hZ).2
    obtain ⟨q,hq,hw⟩ := hData
    have heOdd : Odd e := (Finset.mem_filter.mp he).2
    have hqData := Finset.mem_filter.mp hq
    have hqProd := Finset.mem_product.mp hqData.1
    have hmPrime := Finset.mem_filter.mp hqProd.1
    have hNe : m≠q.1 := (Finset.mem_erase.mp hmPrime.1).1.symm
    have hValid := hqData.2.1
    have hPositive := parity_original_historical_supported_canonical_z_positive_shift434
      d L band slot δ Y e m q.1 q.2 heOdd hNe hValid
    have hz : 0<parityOriginalHistoricalCanonicalZ434 e m q.1 q.2 := hPositive.2.1
    have hZscale := hqData.2.2.2
    have hZpos : 0<Z := by
      have hh := (parity_original_historical_actual_z_in_own_dyad434
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hz).1
      rw [hZscale] at hh
      exact hh
    have hmD := hDyad m hm
    have hAllD : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
      intro mp hmp
      exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩
    exact parity_original_historical_true_B633_fourier_ball_error_le_source434
      d L U E V hL band slot δ ξ rho α signed Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) k Z χ heOdd
      hU hE hV hmD.1 hmD.2.le hAllD
      buf a b hSmooth hSupport hOne hZpos 0 T hT
  have hZsum : ‖(∑Z∈S,F Z)-(∑Z∈S,G Z)‖≤∑Z∈S,Err Z :=
    parity_original_historical_norm_sum_sub_le_finite_error434 S F G Err hCell
  change ‖c*(∑Z∈S,F Z)-c*(∑Z∈S,G Z)‖ ≤ ‖c‖*(∑Z∈S,Err Z)
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left hZsum (norm_nonneg c)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddFilteredCharacterTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Parity's ORIGINAL signed shift h=-2 Dirichlet character mask never
charges a phi(2|k|) factor when estimating a family of REAL source
Fourier errors on the SAME finite physical Z cells. The original
cchi has native l1 mass at most 1 whenever k≠0. If the error for
EVERY χ,Z is bounded by a common nonnegative B(Z), then

 sum_χ |cχ| sum_Z error(χ,Z) ≤ sum_Z B(Z).

This is an honest finite real bound: no cancellation is assumed
of the Fourier **arithmetic** correlation, and no inaccurate bound
on a restricted signed complex sum by the unrestricted full sum. -/
theorem parity_original_historical_character_mask_tail_no_phi_loss434
    (k : ℤ) (hk : k≠0) (S : Finset ℕ)
    (err : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℝ)
    (B : ℕ → ℝ)
    (hB : ∀Z∈S,0≤B Z)
    (hErr : ∀χ : DirichletCharacter ℂ (2*k.natAbs),∀Z∈S,err χ Z≤B Z) :
    (∑χ : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
        (∑Z∈S,err χ Z)) ≤ ∑Z∈S,B Z := by
  let M : ℝ := ∑Z∈S,B Z
  have hM : 0≤M := Finset.sum_nonneg (fun Z hZ => hB Z hZ)
  have hEach (χ : DirichletCharacter ℂ (2*k.natAbs)) :
      (∑Z∈S,err χ Z) ≤ M :=
    Finset.sum_le_sum (fun Z hZ => hErr χ Z hZ)
  calc
    _ ≤ ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ * M := by
          apply Finset.sum_le_sum
          intro χ hχ
          exact mul_le_mul_of_nonneg_left (hEach χ) (norm_nonneg _)
    _ = (∑χ : DirichletCharacter ℂ (2*k.natAbs),
        ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖) * M := by
          rw [Finset.sum_mul]
    _ ≤ 1*M := mul_le_mul_of_nonneg_right
      (parity_signed_shift_two_mask_coefficient_mass_le_one434 k hk) hM
    _ = _ := one_mul _
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddFilteredCharacterUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Unconditional ORIGINAL Parity (4.15)--(4.16) character-summed
Fourier-tail budget on any fixed full-odd physical e,m,k source
with at least one nonzero constructed η_e,Lη_n weight per selected
binary Z:

 ∑χ |cχ| ∑Z SOURCE_ERROR(e,m,k,Z,χ,T)
  ≤ Acoef² L^M · C_H L^X/T^H · ∑Z Z,

 M=2*C_W1+256+K0+90; X=5(K0+90)(H+P+1).

The proof uses the **ACTUAL** previously native-verified uniform
per-cell SOURCE theorem, witnesses in EXACT physically populated
nonzero-eta Z cells, and the source-sharp mask l1 mass ≤1. Hence
there is NO φ(2|k|), #characters or independent Γ correction.
All e,m',z,n Q/P/B509 source conditions, b629 alpha and signed
h=-2 Cauchy coefficient are unchanged. This is a TOTAL χ AND Z
error bound at fixed e,m,k, not yet a bound for the outer e,m,k
sum or an unrestricted (4.17) correlation cancellation theorem. -/
theorem parity_eventually_original_full_odd_character_z_tail_polylog434
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
      ∀ (e m : ℕ) (k : ℤ),
      Odd e → e∈parityOriginalHistoricalFullOddEEnvelope434 E →
      m∈K → k≠0 →
      ∀ (A R : ℝ) (hA : 0<A) (hR : 1≤R)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀ (t : ℝ), buf t≠0 →
          -Real.log A≤t ∧ t≤Real.log A),
      (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) →
      (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      ∀ (H : ℕ),
      2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
      (8*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
        (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
        ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L) →
      ∀ (T : ℝ),0<T →
      let S := parityOriginalHistoricalFullOddNonzeroWeightZCells434
        (sourceOriginalLiteralDepth 20 L) L E V hLw band slot δ
        ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k
      let C : ℝ := Acoef^2*
        L^(2*parityOriginalW1PolylogExponent434+256+K0+90) *
        (parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport H *
          L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H)
      (∑χ : DirichletCharacter ℂ (2*k.natAbs),
        ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S,
            parityOriginalHistoricalActualKZ416FourierError434
              (sourceOriginalLiteralDepth 20 L) L U E V hLw Z k band slot δ ξ
              rho α signed ⌊2*Real.exp L⌋₊ e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf (-Real.log A) (Real.log A) hSmooth hSupport T)) ≤
        C*(∑Z∈S,(Z:ℝ)) := by
  filter_upwards [parity_eventually_original_full_odd_k_z_416_tail_uniform434
      K0 hK0] with L hSource
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hAcoef hAlpha
    hU hV hUV hScale hDyad e m k he heMem hm hk
    A R hA hR buf hSmooth hSupport hOne hCube H hLargeE hLargeN T hT
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let S := parityOriginalHistoricalFullOddNonzeroWeightZCells434
    d L E V hLw band slot δ Y e m K J k
  let C : ℝ := Acoef^2*L^(2*parityOriginalW1PolylogExponent434+256+K0+90)*
    (parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hSmooth hSupport H *
      L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H)
  let Err : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℝ := fun χ Z =>
    parityOriginalHistoricalActualKZ416FourierError434
      d L U E V hLw Z k band slot δ ξ rho α signed Y e m K J χ
      buf (-Real.log A) (Real.log A) hSmooth hSupport T
  have hCell (χ : DirichletCharacter ℂ (2*k.natAbs)) (Z : ℕ) (hZ : Z∈S) :
      Err χ Z ≤ C*(Z:ℝ) := by
    have hzData := (Finset.mem_filter.mp hZ).2
    obtain ⟨q,hq,hw⟩ := hzData
    have hEq := hSource.2.2 hLw band slot δ ξ rho U V E K α signed Acoef
      hAcoef hAlpha hU hV hUV hScale hDyad
      e m k Z he heMem hm q hq hw χ
      A R hA hR buf hSmooth hSupport hOne hCube
      H hLargeE hLargeN T hT
    change Err χ Z ≤ _ at hEq
    calc
      _ ≤ Acoef^2*(Z:ℝ)*L^(2*parityOriginalW1PolylogExponent434+256+K0+90) *
        (parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport H *
          L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H) := hEq
      _ = C*(Z:ℝ) := by dsimp [C]; ring
  have hB : ∀Z∈S,0≤C*(Z:ℝ) := by
    intro Z hZ
    have hh := hCell (1 : DirichletCharacter ℂ (2*k.natAbs)) Z hZ
    have hE : 0≤Err 1 Z := by
      dsimp [Err,parityOriginalHistoricalActualKZ416FourierError434]
      exact norm_nonneg _
    exact hE.trans hh
  have hMask := parity_original_historical_character_mask_tail_no_phi_loss434
    k hk S Err (fun Z => C*(Z:ℝ)) hB (fun χ Z hZ => hCell χ Z hZ)
  calc
    _ ≤ ∑Z∈S,C*(Z:ℝ) := hMask
    _ = C*(∑Z∈S,(Z:ℝ)) := by rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFiniteAdjacencyEnergy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Exact directed-to-undirected finite cofactor-row symmetry:
for a symmetric relation on the original rough cofactor carrier K,
the pairwise sum of the SECOND endpoint's nonnegative diagonal
amplitude agrees with the analogous FIRST-endpoint degree sum.
No spectrum, uniform n or multiplicative-energy assumption. -/
theorem parity_original_finite_symmetric_neighbor_swap434
    {ι : Type*} (K : Finset ι) (R : ι → ι → Prop)
    (hSym : ∀ x y, R x y ↔ R y x)
    (a : ι → ℝ) :
    (∑m∈K,∑mp∈K.filter (R m),a mp) =
      ∑mp∈K,∑m∈K.filter (R mp),a mp := by
  calc
    _ = ∑m∈K,∑mp∈K,if R m mp then a mp else 0 := by
      simp only [Finset.sum_filter]
    _ = ∑mp∈K,∑m∈K,if R m mp then a mp else 0 := Finset.sum_comm
    _ = ∑mp∈K,∑m∈K,if R mp m then a mp else 0 := by
      apply Finset.sum_congr rfl
      intro mp hmp
      apply Finset.sum_congr rfl
      intro m hm
      rw [hSym m mp]
    _ = _ := by simp only [←Finset.sum_filter]

/-- A legitimate way to charge an ORIGINAL physical h=-2 signed
Cauchy cofactor ℓ1 graph by the POSITIVE diagonal, PROVIDED the
underlying actual cofactor adjacency has at most D neighbors per
m. This finite graph lemma is unconditional mathematics:

 sum_m sum_(m' adjacent to m) a_m a_m' ≤
    D sum_m a_m².

The proof uses exact symmetry and 2ab≤a²+b²; it avoids both a
factor #K and an unsupported cancellation assumption. Applying it
to real h=-2 SOURCE requires proving that nonzero smoothing window
plus actual m'-m=e*k gives **POLYLOG cofactor degree D** rather
than using the full arbitrary dyadic K×K relation. -/
theorem parity_original_finite_symmetric_pair_energy_le_degree434
    {ι : Type*} (K : Finset ι) (R : ι → ι → Prop)
    (hSym : ∀ x y, R x y ↔ R y x)
    (D : ℝ)
    (hDegree : ∀m∈K,((K.filter (R m)).card:ℝ)≤D)
    (a : ι → ℝ) :
    (∑m∈K,∑mp∈K.filter (R m),a m*a mp) ≤
      D*(∑m∈K,(a m)^2) := by
  have hPair (m mp : ι) : a m*a mp≤((a m)^2+(a mp)^2)/2 := by
    nlinarith [sq_nonneg (a m-a mp)]
  have hFirst :
      (∑m∈K,∑mp∈K.filter (R m),a m*a mp) ≤
      ∑m∈K,∑mp∈K.filter (R m),((a m)^2+(a mp)^2)/2 := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro mp hmp
    exact hPair m mp
  have hSwap := parity_original_finite_symmetric_neighbor_swap434 K R hSym
    (fun m => (a m)^2)
  have hFirstEq :
      (∑m∈K,∑mp∈K.filter (R m),(a m)^2) =
      ∑m∈K,((K.filter (R m)).card:ℝ)*(a m)^2 := by
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hSecondEq :
      (∑m∈K,∑mp∈K.filter (R m),(a mp)^2) =
      ∑m∈K,((K.filter (R m)).card:ℝ)*(a m)^2 := by
    rw [hSwap]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hDiag :
      (∑m∈K,((K.filter (R m)).card:ℝ)*(a m)^2) ≤
      D*(∑m∈K,(a m)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    exact mul_le_mul_of_nonneg_right (hDegree m hm) (sq_nonneg _)
  calc
    _ ≤ ∑m∈K,∑mp∈K.filter (R m),((a m)^2+(a mp)^2)/2 := hFirst
    _ = ∑m∈K,((K.filter (R m)).card:ℝ)*(a m)^2 := by
      simp only [add_div,Finset.sum_add_distrib,←Finset.sum_div]
      rw [hFirstEq,hSecondEq]
      ring
    _ ≤ D*(∑m∈K,(a m)^2) := hDiag
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalBoundedKGraph -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- A TRUE ORIGINAL Parity (4.13) bounded-shift cofactor adjacency
for fixed e>0 and |k|≤N. This is the symmetric finite envelope of
all source physically populated m' satisfying m'-m=e*k, without
inventing a cofactor collision or conditioning on Q/P source gates. -/
def parityOriginalHistoricalBoundedKNeighbors434
    (e N m mp : ℕ) : Prop :=
  ∃ k : ℤ, (mp:ℤ)-(m:ℤ)=(e:ℤ)*k ∧ k.natAbs≤N

/-- Original signed integer k<0 is handled symmetrically: a
legitimate m→m' quotient produces the reverse m'→m quotient -k,
with the SAME natAbs bound. -/
theorem parity_original_historical_bounded_k_neighbors_symm434
    (e N m mp : ℕ) :
    parityOriginalHistoricalBoundedKNeighbors434 e N m mp ↔
      parityOriginalHistoricalBoundedKNeighbors434 e N mp m := by
  constructor
  · rintro ⟨k,hk,habs⟩
    refine ⟨-k,?_,?_⟩
    · calc
        (m:ℤ)-(mp:ℤ) = -((mp:ℤ)-(m:ℤ)) := by ring
        _ = -((e:ℤ)*k) := by rw [hk]
        _ = (e:ℤ)*(-k) := by ring
    · simpa only [Int.natAbs_neg] using habs
  · rintro ⟨k,hk,habs⟩
    refine ⟨-k,?_,?_⟩
    · calc
        (mp:ℤ)-(m:ℤ) = -((m:ℤ)-(mp:ℤ)) := by ring
        _ = -((e:ℤ)*k) := by rw [hk]
        _ = (e:ℤ)*(-k) := by ring
    · simpa only [Int.natAbs_neg] using habs

/-- All original m' inside a genuine fixed m,e k-envelope map
INJECTIVELY via the actual canonical quotient (m'-m)/e into the
signed interval [-N,N]. The e>0 determinant is essential; no
hypothetical finite-combinatorics cap on the full K×K relation. -/
theorem parity_original_historical_bounded_k_neighbor_card434
    (e N m : ℕ) (he : 0<e) (K : Finset ℕ) :
    ((K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m)).card:ℝ) ≤
      (2*N+1:ℕ) := by
  let S := K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m)
  let T : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  let f : ℕ → ℤ := parityOriginalHistoricalOffdiagK434 e m
  have hDet (mp : ℕ) (hp : mp∈S) :
      (mp:ℤ)-(m:ℤ)=(e:ℤ)*f mp ∧ (f mp).natAbs≤N := by
    obtain ⟨k,hk,hbound⟩ := (Finset.mem_filter.mp hp).2
    have heq := parity_original_historical_physical_k_eq_quotient434
      e m mp he k hk
    have hf : f mp = k := heq
    exact ⟨by rw [hf]; exact hk, by rw [hf]; exact hbound⟩
  have hMaps : Set.MapsTo f (S:Set ℕ) (T:Set ℤ) := by
    intro mp hp
    have hd := (hDet mp hp).2
    change f mp ∈ T
    rw [Finset.mem_Icc]
    omega
  have hInj : Set.InjOn f (S:Set ℕ) := by
    intro mp hmp mp' hmp' hEq
    have h1 := (hDet mp hmp).1
    have h2 := (hDet mp' hmp').1
    rw [hEq] at h1
    have hI : (mp:ℤ)=(mp':ℤ) := by omega
    exact_mod_cast hI
  have hCard := Finset.card_le_card_of_injOn f hMaps hInj
  have hTCard : T.card=2*N+1 := by
    dsimp [T]
    rw [Int.card_Icc]
    have hh : (N:ℤ)+1-(-(N:ℤ)) = ((2*N+1:ℕ):ℤ) := by omega
    rw [hh,Int.toNat_natCast]
  rw [hTCard] at hCard
  exact_mod_cast hCard

/-- COMPLETE original bounded-quotient cofactor-pair ENERGY:
for any e>0 and N, without loss #K, the total real original
Cauchy pair mass over all m,m' with m'-m=e*k and |k|≤N obeys

 sum_(m∈K) sum_(m'∈K, bounded quotient)
    a_m a_m' ≤ (2N+1) sum_(m∈K) a_m².

This is a genuine source-relevant bound by the Cauchy positive
DIAGONAL with only polynomial degree loss 2N+1. It applies to the
actual h=-2 original physical Q/P signed coefficients by triangle
and the native exact pair Gram identity; the application to the
FULL six-index Fourier-tail source is still a separate finite
reindex needed before asserting arbitrary inverse-log global saving. -/
theorem parity_original_historical_bounded_k_pair_energy434
    (e N : ℕ) (he : 0<e) (K : Finset ℕ) (a : ℕ → ℝ) :
    (∑m∈K,∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
      a m*a mp) ≤
      (2*N+1:ℕ)*(∑m∈K,(a m)^2) := by
  exact parity_original_finite_symmetric_pair_energy_le_degree434 K
    (parityOriginalHistoricalBoundedKNeighbors434 e N)
    (parity_original_historical_bounded_k_neighbors_symm434 e N)
    (2*N+1:ℕ)
    (fun m hm => parity_original_historical_bounded_k_neighbor_card434 e N m he K)
    a
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddNeighborDegree -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- The ACTUAL original h=-2 full-odd-e source physical cofactor
adjacency: m!=m' and at least one SAME n carrying both genuine
B509 Q/P gates with nonzero constructed η_e,L η_n weight.
This is a two-way physical relation, not an artificial full K×K
pair kernel or an asymmetric selected-Q e condition. -/
def parityOriginalHistoricalFullOddNonzeroPhysicalNeighbor434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e : ℕ) (J : Finset ℕ) (m mp : ℕ) : Prop :=
  m≠mp ∧ ∃n∈J,
    parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp n ∧
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0

/-- Both B509/Q/P endpoints may be exchanged at a fixed source n
with EXACT original h=-2 physical conditions; the nonzero eta_eη_n
weight is common, so this physical cofactor adjacency is symmetric. -/
theorem parity_original_historical_full_odd_nonzero_neighbor_symm434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e : ℕ) (J : Finset ℕ) (m mp : ℕ) :
    parityOriginalHistoricalFullOddNonzeroPhysicalNeighbor434
      d L E V hL band slot δ Y e J m mp ↔
    parityOriginalHistoricalFullOddNonzeroPhysicalNeighbor434
      d L E V hL band slot δ Y e J mp m := by
  constructor
  · rintro ⟨hne,n,hn,hValid,hw⟩
    obtain ⟨u,hu,up,hup,hV,hVp⟩ := hValid
    exact ⟨hne.symm,n,hn,⟨up,hup,u,hu,hVp,hV⟩,hw⟩
  · rintro ⟨hne,n,hn,hValid,hw⟩
    obtain ⟨u,hu,up,hup,hV,hVp⟩ := hValid
    exact ⟨hne.symm,n,hn,⟨up,hup,u,hu,hVp,hV⟩,hw⟩

/-- At fixed TRUE source odd e and original [U,2U) cofactor band,
nonzero constructed e/n smoothing plus populated two-ended Q/P
forces EVERY physical neighbor m' to satisfy

   m'-m=e*k,   |k|≤ ceil(L^(K0+89)).

This is the genuine source proof of the SMALL physical graph degree
condition, not a guessed bound on m'-m or on the number of characters. -/
theorem parity_original_historical_full_odd_nonzero_neighbor_bounded_k434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp : ℕ) (J : Finset ℕ)
    (he : Odd e) (hU : 0<U) (hScale : E=U*L^(-K0))
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)<2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)<2*U)
    (hPhysical : parityOriginalHistoricalFullOddNonzeroPhysicalNeighbor434
      d L E V hL band slot δ Y e J m mp) :
    parityOriginalHistoricalBoundedKNeighbors434
      e (Nat.ceil (L^(K0+89))) m mp := by
  obtain ⟨hne,n,hn,hValid,hw⟩ := hPhysical
  have hEta : parityOriginalHistoricalDyadicEtaEAtLReal434
      L hL ((e:ℝ)/E) ≠ 0 := by
    unfold parityOriginalHistoricalDyadicEtaWeight434 at hw
    intro h0
    exact hw (by rw [h0,zero_mul])
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  have hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k :=
    parity_original_historical_physical_k_exact_cofactor_shift434
      d L band slot δ Y e m mp n he hne hValid
  have hBound : (k.natAbs:ℝ)<L^(K0+89) :=
    parity_original_historical_full_odd_k_bound_polylog434
      L U E K0 e m mp k hL hU hScale hEta
      hmLo hmHi hmpLo hmpHi hDet
  have hN : k.natAbs≤Nat.ceil (L^(K0+89)) := by
    have hh : (k.natAbs:ℝ)≤(Nat.ceil (L^(K0+89)):ℝ) :=
      (le_of_lt hBound).trans (Nat.le_ceil _)
    exact_mod_cast hh
  exact ⟨k,hDet,hN⟩

/-- SOURCE-SPECIFIC POLYLOG PHYSICAL DEGREE after the legal
pre-Gram e/n enlargement, with NO #K or #e factor:

 # {m'∈K: some physical n with nonzero η_eη_n and two Q/P gates}
   ≤ 2*ceil(L^(K0+89))+1.

The proof embeds the ACTUAL symmetric h=-2 physical relation into
the injective e*k quotient cofactor interval [-N,N] and uses the
native exact quotient uniqueness; no correlation cancellation. -/
theorem parity_original_historical_full_odd_physical_neighbor_degree434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e : ℕ) (K J : Finset ℕ)
    (he : Odd e) (hU : 0<U) (hScale : E=U*L^(-K0))
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U)
    (m : ℕ) (hm : m∈K) :
    ((K.filter (parityOriginalHistoricalFullOddNonzeroPhysicalNeighbor434
       d L E V hL band slot δ Y e J m)).card:ℝ) ≤
      (2*Nat.ceil (L^(K0+89))+1:ℕ) := by
  let N := Nat.ceil (L^(K0+89))
  let S := K.filter (parityOriginalHistoricalFullOddNonzeroPhysicalNeighbor434
    d L E V hL band slot δ Y e J m)
  let B := K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m)
  have hSub : S ⊆ B := by
    intro mp hmp
    obtain ⟨hmpK,hP⟩ := Finset.mem_filter.mp hmp
    have hmD := hDyad m hm
    have hmpD := hDyad mp hmpK
    exact Finset.mem_filter.mpr ⟨hmpK,
      parity_original_historical_full_odd_nonzero_neighbor_bounded_k434
        d L U E V K0 hL band slot δ Y e m mp J
        he hU hScale hmD.1 hmD.2 hmpD.1 hmpD.2 hP⟩
  have hCard : (S.card:ℝ) ≤ (B.card:ℝ) := by
    exact_mod_cast Finset.card_le_card hSub
  have hBound := parity_original_historical_bounded_k_neighbor_card434
    e N m he.pos K
  exact hCard.trans hBound

/-- ACTUAL original smoothed signed source h=-2 physical
cofactor PAIR MASS at fixed e,n admits a POLYLOG degree positive
Cauchy diagonal bound, with the true two B509/Q/P endpoints:

 sum_{m in K,m' in K, possibly populated physical e,n}
    a_m a_m' ≤ (2*ceil(L^(K0+89))+1) sum_{m in K} a_m².

This is a source-relevant massive improvement over the crude |K|
loss in aggregate Fourier-tail bounds. Connecting this graph mass to
the full actual e,n,k,Z and character-summed source coefficient
mass remains one precise finite-reindex obligation. -/
theorem parity_original_historical_full_odd_physical_pair_energy_le434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e : ℕ) (K J : Finset ℕ)
    (he : Odd e) (hU : 0<U) (hScale : E=U*L^(-K0))
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U)
    (a : ℕ → ℝ) :
    (∑m∈K,∑mp∈K.filter (parityOriginalHistoricalFullOddNonzeroPhysicalNeighbor434
      d L E V hL band slot δ Y e J m),a m*a mp) ≤
    (2*Nat.ceil (L^(K0+89))+1:ℕ)*(∑m∈K,(a m)^2) := by
  exact parity_original_finite_symmetric_pair_energy_le_degree434 K
    (parityOriginalHistoricalFullOddNonzeroPhysicalNeighbor434
      d L E V hL band slot δ Y e J)
    (parity_original_historical_full_odd_nonzero_neighbor_symm434
      d L E V hL band slot δ Y e J)
    (2*Nat.ceil (L^(K0+89))+1:ℕ)
    (fun m hm => parity_original_historical_full_odd_physical_neighbor_degree434
      d L U E V K0 hL band slot δ Y e K J he hU hScale hDyad m hm)
    a
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddPhysicalMassNoPhi -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Literal TRUE original h=-2 Q/P/B509 two-endpoint signed Cauchy
cofactor ℓ1 mass on an actual physical k/Z cell, BEFORE χ. -/
def parityOriginalHistoricalActualKZRawPairMass434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ) : ℝ :=
  ∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z,
    ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e q.2 m q.1‖

/-- The original χ(m') factor cannot increase the absolute h=-2
B509 physical cofactor pair; it costs no independent character bound. -/
theorem parity_original_historical_real_k_z_chi_cofactor_mass_le_raw434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) ≤
    parityOriginalHistoricalActualKZRawPairMass434
      d L band slot δ ξ rho α signed Y e m K J k Z := by
  unfold parityOriginal3DPhysicalFiniteCoefficientMass434
    parityOriginalHistoricalActualKZRawPairMass434
  apply Finset.sum_le_sum
  intro q hq
  unfold parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_right
    (DirichletCharacter.norm_le_one χ (q.1 : ZMod (2*k.natAbs)))
    (norm_nonneg (parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e q.2 m q.1))
  simpa only [one_mul] using h

/-- SUMMING all original characters on the SAME genuine physical
k/Z cells never costs φ(2|k|). The true Parity(2.6) cχ has ℓ1≤1,
and every twisted χ(m') H0 cofactor mass is bounded by raw mass. -/
theorem parity_original_historical_full_odd_chi_k_z_raw_mass_no_phi434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (hk : k≠0)
    (S : Finset ℕ) :
    (∑χ : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
        (∑Z∈S,
          parityOriginal3DPhysicalFiniteCoefficientMass434
            (parityOriginalHistoricalActualKZPhysicalEventCarrier434
              d L band slot δ Y e m K J k Z)
            (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
              d L band slot δ ξ rho α signed Y e m k χ))) ≤
    ∑Z∈S,parityOriginalHistoricalActualKZRawPairMass434
      d L band slot δ ξ rho α signed Y e m K J k Z := by
  let R : ℕ → ℝ := fun Z =>
    parityOriginalHistoricalActualKZRawPairMass434
      d L band slot δ ξ rho α signed Y e m K J k Z
  let W : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℝ := fun χ Z =>
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  have hR : ∀Z∈S,0≤R Z := by
    intro Z hz
    unfold R parityOriginalHistoricalActualKZRawPairMass434
    exact Finset.sum_nonneg (fun q hq => norm_nonneg _)
  have hW : ∀χ : DirichletCharacter ℂ (2*k.natAbs), ∀Z∈S,
      W χ Z≤R Z := by
    intro χ Z hz
    exact parity_original_historical_real_k_z_chi_cofactor_mass_le_raw434
      d L band slot δ ξ rho α signed Y e m K J k Z χ
  exact parity_original_historical_character_mask_tail_no_phi_loss434
    k hk S W R hR hW


/-- REAL original full-odd h=-2 physically supported signed pair
ℓ1 mass reindexed EXACTLY through the actual attained dyadic Z
image, with no duplicated physical n and no ghost z. This is the
nonnegative analogue of the earlier complex source Fourier reindex. -/
theorem parity_original_historical_full_odd_k_Z_real_mass_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (W : (ℕ×ℕ) → ℝ) :
    (∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,W q) =
    ∑Z∈(parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
      ∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,W q := by
  let S := parityOriginalHistoricalFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
  have h := Finset.sum_image' (s:=S) (g:=g)
    (f:=fun Z => ∑q∈S.filter (fun q=>g q=Z),W q)
    W (by intro q hq; rfl)
  calc
    _ = ∑Z∈S.image g,∑q∈S.filter (fun q=>g q=Z),W q := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Z hZ
      rw [parity_original_historical_full_odd_Z_event_fibre_exact434
        d L band slot δ Y e m K J k Z he]

/-- Physical k/Z cells whose entire constructed SOURCE smoothing
weight vanishes need not be counted in the RAW positive pair mass.
The selected binary dyadic Z set is a subset of ALL true attained
Z images. Comparing nonnegative real norms here is legitimate;
we do not compare restricted COMPLEX signed correlations. -/
theorem parity_original_historical_full_odd_nonzero_Z_raw_mass_le_all434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (he : Odd e) :
    (∑Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
       d L E V hL band slot δ Y e m K J k,
      parityOriginalHistoricalActualKZRawPairMass434
        d L band slot δ ξ rho α signed Y e m K J k Z) ≤
    ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,
      ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e q.2 m q.1‖ := by
  let S := parityOriginalHistoricalFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let P : ℕ → Prop := fun Z => ∃q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0
  let W : (ℕ×ℕ) → ℝ := fun q =>
    ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e q.2 m q.1‖
  let R : ℕ → ℝ := fun Z =>
    parityOriginalHistoricalActualKZRawPairMass434
      d L band slot δ ξ rho α signed Y e m K J k Z
  have hSub : (S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)).filter P ⊆
    S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m) :=
    Finset.filter_subset _ _
  have hPositive : ∀Z∈S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),0≤R Z := by
    intro Z hz
    unfold R parityOriginalHistoricalActualKZRawPairMass434
    exact Finset.sum_nonneg (fun q hq => norm_nonneg _)
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg hSub
    (fun Z hz hnot => hPositive Z hz)
  change (∑Z∈(S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)).filter P,R Z) ≤
    ∑q∈S,W q
  have hReindex := parity_original_historical_full_odd_k_Z_real_mass_reindex434
    d L band slot δ Y e m K J k he W
  change (∑q∈S,W q) = ∑Z∈S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),R Z at hReindex
  exact hLe.trans (le_of_eq hReindex.symm)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddKZTailMassUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 26500000

/-- ORIGINAL Parity(4.16) actual FULL-ODD smooth-source per k/Z/chi
Fourier truncation error is bounded by THE ACTUAL FINITE PHYSICAL
COEFFICIENT ℓ1 MASS, not by a coarse Acoef²*Z estimate:

 Err(e,m,k,Z,chi,T) ≤ mass(e,m,k,Z,chi) * C_H L^X / T^H,
 X=5(K0+90)(H+P+1).

The real source eta_eη_n nonzero weight witness supplies genuine
Z≤8 expL L^(K0+88), k≠0 and 0<Z. The uniform 3D source Fourier
moment was separately proved from actual all-order derivatives;
no assumed decay/correlation-saving lemma is passed in. The exact
H0/Q/P/B509 signed source coefficient is never replaced by a
Z-dependent dummy mass. This sharper TRUE per-cell estimate permits
later use of the actual positive Cauchy diagonal after summing every
k,chi,Z, rather than paying ∑Z Z times exponential #e#K. -/
theorem parity_eventually_original_full_odd_k_z_416_tail_actual_mass_uniform434
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
        (signed : Bool),
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈parityOriginalHistoricalFullOddEEnvelope434 E → m∈K →
      ∀ (q : ℕ×ℕ),
      q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m K
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
      parityOriginalHistoricalActualKZ416FourierError434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw Z k band slot δ ξ
        rho α signed ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) χ
        buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (parityOriginalHistoricalActualKZPhysicalEventCarrier434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k Z)
        (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α
          signed ⌊2*Real.exp L⌋₊ e m k χ) *
        (parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport H *
          L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H) := by
  filter_upwards [eventually_ge_atTop (max ((3:ℝ)^256) (8:ℝ))] with L hLarge
  have hL : 8≤L := le_trans (le_max_right _ _) hLarge
  have hL3 : (3:ℝ)^256≤L := le_trans (le_max_left _ _) hLarge
  refine ⟨hL3,hL,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed hU hV hUV hScale hDyad
    e m k Z he heMem hm q hq hw χ A R hA hR buf hSmooth hSupport
    hOne hCube H hLargeE hLargeN T hT
  let d := sourceOriginalLiteralDepth 20 L
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := ⌊2*Real.exp L⌋₊
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let mass := parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  let C : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Power : ℝ := L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))
  have hLp : 0<L := by linarith
  have hEpos : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hmDyad := hDyad m hm
  have hZrange := parity_original_historical_full_odd_smoothed_actual_Z_window434
    d L U V E K0 hLw band slot δ K J e m k Z he hU hV hUV hScale
    hm hDyad q hq hw
  have hZlegal := parity_original_historical_full_odd_smooth_Z_Parity417_window434
    L (Z:ℝ) K0 hLw hK0 hZrange.1 hZrange.2
  have hZreal : (0:ℝ)<(Z:ℝ) :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-(K0+90)))).trans_le hZlegal.1
  have hZ : 0<Z := by exact_mod_cast hZreal
  have hk : k≠0 := parity_original_historical_nonempty_actual_k_z_nonzero434
    d L band slot δ Y e m K J k Z he ⟨q,hq⟩
  have hBH := parity_original_historical_full_odd_source_BH_uniform_polylog434
    L U E V (Z:ℝ) K0 A hLw hK0 k hk hU hV hUV hScale
    (by exact_mod_cast (Nat.zero_le Z)) hZrange.2.le
    hA buf hSmooth hSupport H hLargeE hLargeN R hR hCube
  have hTbound : parityOriginalHistoricalActualKZ416FourierError434
    d L U E V hLw Z k band slot δ ξ rho α signed Y e m K J χ
    buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
    mass*(parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) :=
    parity_original_historical_actual_k_z_416_error_le_mass434
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

/-! ## OriginalHistoricalFixedFourierMomentNonneg -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The true original Parity (4.14) 3D SOURCE Fourier moment fixed
coefficient is NONNEGATIVE for any fixed smooth log buffer and
radius R≥1. This follows directly from native nonnegative source
geometric constant and each of the five-factor derivative budgets;
not from assuming any Fourier cancellation. Essential for safely
moving one uniform H-tail factor outside the full signed physical
χ,k,Z,e,m coefficient mass via nonnegative finite sums. -/
theorem parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    (A R : ℝ) (buf : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupp : ∀ (s : ℝ), buf s ≠ 0 → -Real.log A ≤ s ∧ s ≤ Real.log A)
    (H : ℕ) (hR : 1≤R) :
    0≤parityOriginalHistoricalActual3DFourierMomentFixedK434
      A R buf hSmooth hSupp H := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let J : ℕ := H+P
  let B := parityOriginalHistoricalFull3DSourceSeminormFixedK434
    A R buf hSmooth hSupp J
  have hGeom := parity_original_3d_source_geometric_constant_nonneg434
  have hB : 0≤B := by
    dsimp [B,parityOriginalHistoricalFull3DSourceSeminormFixedK434]
    have hRpow : 0≤R^P := pow_nonneg (by linarith) _
    have hSum : 0≤∑j∈Finset.range (J+1),
        parityOriginalHistoricalFull3DFixedDerivativeK434 A buf hSmooth hSupp j := by
      apply Finset.sum_nonneg
      intro j hj
      unfold parityOriginalHistoricalFull3DFixedDerivativeK434
      have hBudget := parity_original_historical_five_factor_fixed_budget_ge_one434
        A buf hSmooth hSupp j
      exact mul_nonneg (parity_original_3d_five_factor_combinatorial_nonneg434 j)
        (pow_nonneg (by linarith :
          0≤parityOriginalHistoricalFiveFactorFixedBudget434
            A buf hSmooth hSupp j) 5)
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg
      (by norm_num : (0:ℝ)≤2) J) hGeom)
      (by linarith : 0≤1+R^P)) hSum
  unfold parityOriginalHistoricalActual3DFourierMomentFixedK434
  exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hGeom) hB
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddNonzeroKShort -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- A physically attained original full-odd Parity(4.15) k/Z cell
with at least ONE nonzero ACTUAL constructed η_e(e/E)η_n(n/V)
weight obeys the SOURCE-proved short signed k restriction:
   |k| < L^(K0+89), hence |k|≤ ceil(L^(K0+89)).

No sparse selected-Q e membership or manufactured binary Z support
is inserted, and the original m,m' Q/P/B509 determinant is used. -/
theorem parity_original_historical_full_odd_selected_Z_k_short434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hScale : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (hZ : Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k) :
    (k.natAbs:ℝ)<L^(K0+89) ∧
      k.natAbs≤Nat.ceil (L^(K0+89)) := by
  obtain ⟨q,hq,hw⟩ := (Finset.mem_filter.mp hZ).2
  have hqData := Finset.mem_filter.mp hq
  have hqProd := Finset.mem_product.mp hqData.1
  have hmp := Finset.mem_filter.mp hqProd.1
  have hmpMem := (Finset.mem_erase.mp hmp.1).2
  have hNe : m≠q.1 := (Finset.mem_erase.mp hmp.1).1.symm
  have hk : parityOriginalHistoricalOffdiagK434 e m q.1=k := hmp.2
  have hValid := hqData.2.1
  have hEta : parityOriginalHistoricalDyadicEtaEAtLReal434
      L hL ((e:ℝ)/E) ≠ 0 := by
    unfold parityOriginalHistoricalDyadicEtaWeight434 at hw
    intro h0
    exact hw (by rw [h0,zero_mul])
  have hShift := parity_original_historical_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m q.1 q.2 he hNe hValid
  rw [hk] at hShift
  have hBound := parity_original_historical_full_odd_k_bound_polylog434
    L U E K0 e m q.1 k hL hU hScale hEta
    (hDyad m hm).1 (hDyad m hm).2
    (hDyad q.1 hmpMem).1 (hDyad q.1 hmpMem).2 hShift
  have hN : k.natAbs≤Nat.ceil (L^(K0+89)) := by
    have hr : (k.natAbs:ℝ)≤(Nat.ceil (L^(K0+89)):ℝ) :=
      (le_of_lt hBound).trans (Nat.le_ceil _)
    exact_mod_cast hr
  exact ⟨hBound,hN⟩

/-- Any original full-odd physical k outside |k|≤ ceil(L^(K0+89))
has NO true nonzero η_eη_n Z cell whatsoever. Its complete
SOURCE original weighted signed sum and full B633 integral vanish;
this theorem does NOT discard a potentially nonzero truncated
Fourier integral of a zero-weight cell before exact filtering. -/
theorem parity_original_historical_full_odd_long_k_nonzero_Z_empty434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (hU : 0<U) (hScale : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (hLong : Nat.ceil (L^(K0+89)) < k.natAbs) :
    parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k = ∅ := by
  by_cases hS : (parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k).Nonempty
  · obtain ⟨Z,hZ⟩ := hS
    have hShort := (parity_original_historical_full_odd_selected_Z_k_short434
      d L U E V K0 hL band slot δ Y e m K J k Z
      he hU hScale hm hDyad hZ).2
    omega
  · exact Finset.not_nonempty_iff_eq_empty.mp hS
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalBoundedKRealReindex -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- EXACT original signed k=(m'-m)/e finite image reindex on a
bounded interval |k|≤N for ANY REAL cofactor source weight W.
The cofactor image may contain integer-quotient collisions on
unsupported formal m', but every such fibre is counted exactly;
no injectivity is assumed before Q/P endpoint support is applied. -/
theorem parity_original_historical_bounded_k_real_cofactor_partition434
    (e m : ℕ) (K : Finset ℕ) (N : ℕ) (W : ℕ → ℝ) :
    (∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
      (fun k => k.natAbs≤N),
      ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,W mp) =
    ∑mp∈(K.erase m).filter (fun mp =>
      (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N),W mp := by
  classical
  let S := K.erase m
  let g := parityOriginalHistoricalOffdiagK434 e m
  let p : ℤ → Prop := fun k => k.natAbs≤N
  let T := S.filter (fun mp=>p (g mp))
  have hImage : T.image g=(S.image g).filter p := by
    exact (Finset.filter_image (s:=S) (f:=g) (p:=p)).symm
  have hFibre (mp : ℕ) (hmp : mp∈T) :
      T.filter (fun mp' => g mp'=g mp) =
      S.filter (fun mp' => g mp'=g mp) := by
    have hp := (Finset.mem_filter.mp hmp).2
    ext mp'
    constructor
    · intro hh
      have hmem := Finset.mem_filter.mp hh
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmem.1).1,hmem.2⟩
    · intro hh
      have hmem := Finset.mem_filter.mp hh
      have ht : p (g mp') := by rw [hmem.2]; exact hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hmem.1,ht⟩,hmem.2⟩
  have hReindex :
      (∑k∈T.image g,∑mp∈S.filter (fun mp=>g mp=k),W mp) =
      ∑mp∈T,W mp := by
    apply Finset.sum_image' (s:=T) (g:=g)
      (f:=fun k=>∑mp∈S.filter (fun mp=>g mp=k),W mp)
      W
    intro mp hmp
    rw [hFibre mp hmp]
  change (∑k∈(S.image g).filter p,
      ∑mp∈S.filter (fun mp=>g mp=k),W mp) =
    ∑mp∈T,W mp
  rw [←hImage]
  exact hReindex

/-- Real physical k-events are EXACTLY the nested original m' then
true two-ended n support on the canonical fibre. This identity
preserves every ORIGINAL Q/P/B509 endpoint, including zero raw
weights: no extra source event or independent z is introduced. -/
theorem parity_original_historical_real_k_physical_events_fubini434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (W : ℕ → ℕ → ℝ) :
    (∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,W q.1 q.2) =
    ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
      ∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
        d L band slot δ Y e m mp),W mp n := by
  unfold parityOriginalHistoricalFullOddKPhysicalEvents434
  rw [Finset.sum_filter]
  calc
    _ = ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        ∑n∈J,if parityOriginalHistoricalPhysicalValidN434
          d L band slot δ Y e m mp n then W mp n else 0 := by
          exact Finset.sum_product (parityOriginalHistoricalKPrimeFibre434 e m K k) J
            (fun q : ℕ×ℕ => if parityOriginalHistoricalPhysicalValidN434
              d L band slot δ Y e m q.1 q.2 then W q.1 q.2 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact (Finset.sum_filter (s:=J)
        (p:=parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp)
        (f:=W mp)).symm

/-- No physical k multiplicity is needed in the positive raw
absolute B509 pair mass, provided the k sum is restricted to the
ACTUAL bounded k interval. The full real k,m',n source double
sum equals one canonical bounded-quotient m' image and its genuine
Q/P n-fibre, at fixed e,m; no source term is dropped. -/
theorem parity_original_historical_bounded_k_raw_source_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (N : ℕ) :
    (∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
      (fun k => k.natAbs≤N),
      ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
        ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1‖) =
    ∑mp∈(K.erase m).filter (fun mp=>
      (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N),
      ∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
        d L band slot δ Y e m mp),
        ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp‖ := by
  have hFibre (k : ℤ) :
      (∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
        ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1‖) =
      ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        ∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
          d L band slot δ Y e m mp),
          ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖ :=
    parity_original_historical_real_k_physical_events_fubini434
      d L band slot δ Y e m K J k (fun mp n =>
        ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp‖)
  calc
    _ = ∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
      (fun k => k.natAbs≤N),
      ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        ∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
          d L band slot δ Y e m mp),
          ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hFibre k
    _ = _ := parity_original_historical_bounded_k_real_cofactor_partition434
      e m K N (fun mp =>
        ∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
          d L band slot δ Y e m mp),
          ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddFilteredRawShort -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- The exact nonnegative physical Parity source coefficient cost,
summed over FULL original Dirichlet chi mask and ONLY nonzero-source
smoothed binary Z cells at fixed full-odd selected e,m,k.
Character χ(m') is in its ORIGINAL source position, no φ loss. -/
def parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : ℝ :=
  ∑χ : DirichletCharacter ℂ (2*k.natAbs),
    ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
      (∑Z∈parityOriginalHistoricalFullOddNonzeroWeightZCells434
        d L E V hL band slot δ Y e m K J k,
        parityOriginal3DPhysicalFiniteCoefficientMass434
          (parityOriginalHistoricalActualKZPhysicalEventCarrier434
            d L band slot δ Y e m K J k Z)
          (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
            d L band slot δ ξ rho α signed Y e m k χ))

/-- No SOURCE χ-character multiplicity and no binary Z-image loss:
for EVERY odd e and fixed m, a nonzero signed k has the ORIGINAL
cofactor mass on exactly attained smoothed Z cells bounded by the
true REAL positive pair norm over all Q/P physical (m',n) in its
canonical k-fibre. No false signed-subset comparison occurs. -/
theorem parity_original_historical_full_odd_k_filtered_mass_le_physical434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (hk : k≠0) :
    parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
      d L E V hL band slot δ ξ rho α signed Y e m K J k ≤
    ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,
      ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e q.2 m q.1‖ := by
  let S := parityOriginalHistoricalFullOddNonzeroWeightZCells434
    d L E V hL band slot δ Y e m K J k
  have hChi := parity_original_historical_full_odd_chi_k_z_raw_mass_no_phi434
    d L band slot δ ξ rho α signed Y e m K J k hk S
  have hZ := parity_original_historical_full_odd_nonzero_Z_raw_mass_le_all434
    d L E V hL band slot δ ξ rho α signed Y e m K J k he
  exact hChi.trans hZ

/-- SUM over real original full-odd-e k and χ/Z masks at fixed m:
all selected k beyond |k|>ceil(L^(K0+89)) have EMPTY nonzero
SOURCE eta_eη_n Z support (not merely tiny signed sums). The
original true positive B509 Q/P coefficient mass with all k,χ,Z
can therefore be enlarged only to the exact short-k physical
carrier, with NO false long-k source contribution and NO |K| or
χ-count loss. -/
theorem parity_original_historical_full_odd_k_chi_Z_mass_le_short_raw434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (he : Odd e) (hm : m∈K) (hU : 0<U)
    (hScale : E=U*L^(-K0))
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    (∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
        d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
    ∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
       (fun k=> k.natAbs≤Nat.ceil (L^(K0+89))),
      ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
        ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1‖ := by
  let N := Nat.ceil (L^(K0+89))
  let Sk := parityOriginalHistoricalNonzeroKSupport434 e m K
  let Bk := (parityOriginalHistoricalKSupport434 e m K).filter (fun k=> k.natAbs≤N)
  let mass : ℤ → ℝ := fun k =>
    parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
      d L E V hL band slot δ ξ rho α signed Y e m K J k
  let raw : ℤ → ℝ := fun k =>
    ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,
      ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e q.2 m q.1‖
  have hR : ∀k,0≤ raw k := by
    intro k
    exact Finset.sum_nonneg (fun q hq=>norm_nonneg _)
  have hS : (Sk.filter (fun k=> k.natAbs≤N)) ⊆ Bk := by
    intro k hk
    have hmem := Finset.mem_filter.mp hk
    have hSk := Finset.mem_filter.mp hmem.1
    exact Finset.mem_filter.mpr ⟨hSk.1,hmem.2⟩
  have hBound (k : ℤ) (hk : k∈Sk) :
      mass k ≤ if k.natAbs≤N then raw k else 0 := by
    have hkNonzero := (Finset.mem_filter.mp hk).2
    by_cases hShort : k.natAbs≤N
    · simp only [if_pos hShort]
      exact parity_original_historical_full_odd_k_filtered_mass_le_physical434
        d L E V hL band slot δ ξ rho α signed Y e m K J k he hkNonzero
    · have hLong : N < k.natAbs := by omega
      have hEmpty := parity_original_historical_full_odd_long_k_nonzero_Z_empty434
        d L U E V K0 hL band slot δ Y e m K J k he hU hScale
        hm hDyad hLong
      have hZero : mass k=0 := by
        unfold mass parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
        rw [hEmpty]
        simp
      simp only [if_neg hShort,hZero,le_refl]
  calc
    _ ≤ ∑k∈Sk,if k.natAbs≤N then raw k else 0 :=
      Finset.sum_le_sum (fun k hk=>hBound k hk)
    _ = ∑k∈Sk.filter (fun k=>k.natAbs≤N),raw k := by
      rw [Finset.sum_filter]
    _ ≤ ∑k∈Bk,raw k := Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun k hk hnot=>hR k)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddPairMassDegree -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Fixed genuine source e,n and original cofactor m: the entire
TRUE physical h=-2 B509/Q/P original cofactor pair l1 mass over
source canonical |k|≤N is bounded by its positive symmetric
bounded-k graph row. The physical source determinant is proven
from its two endpoint gates; unsupported m' with no physical n
are harmless because the RHS is a positive real mass, not a
signed complex correlation. -/
theorem parity_original_historical_bounded_k_physical_row_energy434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m : ℕ) (K : Finset ℕ) (N : ℕ) (he : Odd e) :
    (∑mp∈((K.erase m).filter (fun mp =>
        (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N)).filter
          (parityOriginalHistoricalPhysicalValidN434
            d L band slot δ Y e m · n),
      ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp‖) ≤
    ∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
      ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖ *
      ‖α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp‖ := by
  let A : ℕ → ℝ := fun r =>
    ‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖
  let S := ((K.erase m).filter (fun mp =>
    (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N)).filter
      (fun mp => parityOriginalHistoricalPhysicalValidN434
        d L band slot δ Y e m mp n)
  let B := K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m)
  have hSub : S ⊆ B := by
    intro mp hmp
    obtain ⟨hMP,hValid⟩ := Finset.mem_filter.mp hmp
    obtain ⟨hErase,hShort⟩ := Finset.mem_filter.mp hMP
    have hNe : m≠mp := (Finset.mem_erase.mp hErase).1.symm
    have hK := parity_original_historical_physical_k_exact_cofactor_shift434
      d L band slot δ Y e m mp n he hNe hValid
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_erase.mp hErase).2,
       ⟨parityOriginalHistoricalOffdiagK434 e m mp,hK,hShort⟩⟩
  have hPair (mp : ℕ) (hmp : mp∈S) :
      ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp‖ = A m * A mp := by
    exact parity_original_historical_real_physical_pair_norm_product434
      d L band slot δ ξ rho α signed Y e n m mp
  calc
    _ = ∑mp∈S,A m*A mp := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hPair mp hmp
    _ ≤ ∑mp∈B,A m*A mp := Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun mp hmp hnot => mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- SOURCE TRUE positive raw B509 h=-2 physical cofactor MASS,
where k is restricted to the actual polynomial window |k|≤N,
within one full odd selected e. The entire k,m',n source is
controlled by the original diagonal with ONLY (2N+1) loss:

 sum_{m,k short,m',n physical} |α_m A_e,n,m α_m' A_e,n,m'| ≤
    (2N+1) * sum_{n∈FullN,m∈K} |α_m A_e,n,m|².

Proved by exact signed k→m' finite reindex, actual physical n
filter, source Gram pair absolute product, positivity, and the
source-derived bounded-k symmetric cofactor graph degree lemma.
No assumption on #K, #χ or #Z; repeated prime multiplicities
remain inside the original H0/Q/P source. -/
theorem parity_original_historical_bounded_k_physical_mass_le_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e : ℕ) (K J : Finset ℕ) (N : ℕ) (he : Odd e) :
    (∑m∈K,
      ∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
        (fun k=>k.natAbs≤N),
        ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
          d L band slot δ Y e m K J k,
          ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e q.2 m q.1‖) ≤
    (2*N+1:ℕ) *
      (∑n∈J,∑m∈K,
        ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) := by
  let A (n : ℕ) (m : ℕ) : ℝ :=
    ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖
  have hRow (m n : ℕ) :
      (∑mp∈((K.erase m).filter (fun mp=>
        (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N)).filter
          (fun mp=>parityOriginalHistoricalPhysicalValidN434
            d L band slot δ Y e m mp n),
        ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp‖) ≤
      ∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
        A n m*A n mp :=
    parity_original_historical_bounded_k_physical_row_energy434
      d L band slot δ ξ rho α signed Y e n m K N he
  have hReindex (m : ℕ) :
      (∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
        (fun k=>k.natAbs≤N),
        ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
          d L band slot δ Y e m K J k,
          ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e q.2 m q.1‖) =
      ∑mp∈(K.erase m).filter (fun mp=>
        (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N),
        ∑n∈J.filter (parityOriginalHistoricalPhysicalValidN434
          d L band slot δ Y e m mp),
          ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖ :=
    parity_original_historical_bounded_k_raw_source_reindex434
      d L band slot δ ξ rho α signed Y e m K J N
  have hAtM (m : ℕ) (hm : m∈K) :
      (∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
        (fun k=>k.natAbs≤N),
        ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
          d L band slot δ Y e m K J k,
          ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e q.2 m q.1‖) ≤
      ∑n∈J,∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
        A n m*A n mp := by
    rw [hReindex m]
    let S := (K.erase m).filter (fun mp=>
      (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N)
    calc
      _ = ∑n∈J,∑mp∈S.filter (fun mp=>
          parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp n),
          ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖ := by
            simp only [Finset.sum_filter]
            rw [Finset.sum_comm]
            simp only [←Finset.sum_filter]
            rfl
      _ ≤ ∑n∈J,∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
          A n m*A n mp := by
            apply Finset.sum_le_sum
            intro n hn
            exact hRow m n
  have hByN (n : ℕ) :
      (∑m∈K,∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
        A n m*A n mp) ≤
      (2*N+1:ℕ)*(∑m∈K,(A n m)^2) :=
    parity_original_historical_bounded_k_pair_energy434 e N he.pos K (A n)
  calc
    _ ≤ ∑m∈K,∑n∈J,∑mp∈K.filter
          (parityOriginalHistoricalBoundedKNeighbors434 e N m),
          A n m*A n mp := Finset.sum_le_sum hAtM
    _ = ∑n∈J,∑m∈K,∑mp∈K.filter
          (parityOriginalHistoricalBoundedKNeighbors434 e N m),
          A n m*A n mp := Finset.sum_comm
    _ ≤ ∑n∈J,(2*N+1:ℕ)*(∑m∈K,(A n m)^2) :=
      Finset.sum_le_sum (fun n hn=>hByN n)
    _ = (2*N+1:ℕ)*(∑n∈J,∑m∈K,(A n m)^2) := by
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddCharacterMassDiagonal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- The TRUE complete original full odd-e Cauchy-extended SOURCE
raw Fourier coefficient ℓ1 mass, over ALL actual e,m,nonzero k,
all Dirichlet χ and only physically attained binary Z cells with
nonzero original constructed η_eη_n weight. No artificial character
or cofactor count is introduced: this is the exact SOURCE mass
relevant to the aggregate Parity (4.15)--(4.16) Fourier tail. -/
def parityOriginalHistoricalFullOddFilteredCoefficientMass434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) : ℝ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
          d L E V hL band slot δ ξ rho α signed Y e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k

/-- MAIN NEW TRUE ORIGINAL Parity (4.10)--(4.16) source positive
coefficient-mass bridge:

 sum_{all odd e≤2E,m∈K,k!=0,χ,Z with nonzero ηeηn}
      |cχ| sum_{physical m',n} |χ(m') A_source(e,m,m',n)|
 ≤ (2 ceil(L^(K0+89))+1) ×
       sum_{all odd e≤2E,n≤3V,m∈K} |α_m H0(e,n,m)|².

This is an ACTUAL positive diagonal estimate, not an unsupported
signed subset comparison or an artificial uniform Z-cell bound.

Proof chain: native original character ℓ1≤1, exact positive binary
Z image reindex, actual moving η_eη_n support forces short k,
real canonical k→m' quotient reindex, exact source Q/P physical
Gram pair norm, and symmetric bounded-quotient cofactor graph
with degree ≤2 ceil(L^(K0+89))+1. No factor #χ, #Z, #m, #n or #e.
Original r0=20 h=-2 signed ε=1/E, B509 H0, fine b629 α and
multiplicities of all P primes remain untouched. -/
theorem parity_original_historical_full_odd_filtered_coefficient_mass_le_diagonal434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ)
    (hU : 0<U) (hScale : E=U*L^(-K0))
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    parityOriginalHistoricalFullOddFilteredCoefficientMass434
      d L E V hL band slot δ ξ rho α signed Y K ≤
    (2*Nat.ceil (L^(K0+89))+1:ℕ) *
      parityOriginalHistoricalExtendedUnweightedDiagonal434
        d L band slot δ ξ rho K
        (parityOriginalHistoricalFullOddEEnvelope434 E)
        (parityOriginalHistoricalFullNEnvelope434 V) α signed Y := by
  let EFull := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let C : ℝ := (2*Nat.ceil (L^(K0+89))+1:ℕ)
  have heBound (e : ℕ) (he : e∈EFull) :
    (∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
        d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
    C * (∑n∈J,∑m∈K,
        ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) := by
    have heOdd : Odd e := (Finset.mem_filter.mp he).2
    have hStep (m : ℕ) (hm : m∈K) :
        (∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
            d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
        ∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
          (fun k => k.natAbs≤Nat.ceil (L^(K0+89))),
          ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
            d L band slot δ Y e m K J k,
            ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e q.2 m q.1‖ :=
      parity_original_historical_full_odd_k_chi_Z_mass_le_short_raw434
        d L U E V K0 hL band slot δ ξ rho α signed Y e m K J
        heOdd hm hU hScale hDyad
    have hAll :
      (∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
          d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
      ∑m∈K,∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
        (fun k=>k.natAbs≤Nat.ceil (L^(K0+89))),
          ∑q∈parityOriginalHistoricalFullOddKPhysicalEvents434
            d L band slot δ Y e m K J k,
            ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e q.2 m q.1‖ :=
      Finset.sum_le_sum hStep
    have hDegree := parity_original_historical_bounded_k_physical_mass_le_diagonal434
      d L band slot δ ξ rho α signed Y e K J (Nat.ceil (L^(K0+89))) heOdd
    exact hAll.trans hDegree
  unfold parityOriginalHistoricalFullOddFilteredCoefficientMass434
    parityOriginalHistoricalExtendedUnweightedDiagonal434
  change (∑e∈EFull,
    ∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      parityOriginalHistoricalFullOddKChiFilteredCoefficientMass434
        d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
    C*(∑e∈EFull,∑n∈J,∑m∈K,
      ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2)
  calc
    _ ≤ ∑e∈EFull,C*(∑n∈J,∑m∈K,
        ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) :=
      Finset.sum_le_sum heBound
    _ = C*(∑e∈EFull,∑n∈J,∑m∈K,
        ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) := by
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullOddTailToDiagonal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- ORIGINAL h=-2 Parity 4.15--4.16: the FULL real η_eη_n source
Fourier truncation ERRORS, summed over ALL full odd-e,m,k,χ and
physically nonzero-weight Z images, are bounded by ONE global
uniform original SOURCE 3D Fourier H-moment factor times exactly
the SOURCE ℓ1 coefficient mass (not ΣZ Z):

 TotalError ≤ (C_H L^[5(K0+90)(H+P+1)]/T^H) *
  Σ_(e,m,k,χ,Z genuine) |cχ| Σ_(mp,n actual) |χ(mp) A_src|.

The per-cell common Fourier factor is proven from five actual η
source derivatives and is nonnegative; all Fourier frequencies and
physical endpoints use the literal Parity original h=-2 r20 B509
source. Each Z has an ACTUAL nonzero η_eη_n witness and is chosen
BEFORE low-frequency truncation. No unproved (4.17) saving,
complex subset dominance, fake number-of-characters factor or
exponential ΣZ Z majorant is assumed. -/
theorem parity_eventually_original_full_odd_filtered_tail_le_coefficient_mass434
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
        (signed : Bool),
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
      parityOriginalHistoricalFullOddFilteredB633TailMass434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
      Q * parityOriginalHistoricalFullOddFilteredCoefficientMass434
        (sourceOriginalLiteralDepth 20 L) L E V hLw band slot δ ξ rho
        α signed ⌊2*Real.exp L⌋₊ K := by
  filter_upwards [parity_eventually_original_full_odd_k_z_416_tail_actual_mass_uniform434
    K0 hK0] with L hSource
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed hU hV hUV hScale hDyad
    A R hA hR buf hSmooth hSupport hOne hCube H hLargeE hLargeN T hT
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := ⌊2*Real.exp L⌋₊
  let C : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Q : ℝ := C *
    L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H
  let S : ℕ → ℕ → ℤ → Finset ℕ := fun e m k =>
    parityOriginalHistoricalFullOddNonzeroWeightZCells434
      d L E V hLw band slot δ Y e m K J k
  let Mass (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (Z : ℕ) : ℝ :=
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  let Err (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (Z : ℕ) : ℝ :=
    parityOriginalHistoricalActualKZ416FourierError434
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
    have hStep := hSource.2.2 hLw band slot δ ξ rho U V E K α signed
      hU hV hUV hScale hDyad e m k Z heOdd he hm q hq hw χ
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
  unfold parityOriginalHistoricalFullOddFilteredB633TailMass434
    parityOriginalHistoricalFullOddFilteredCoefficientMass434
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

/-! ## OriginalHistoricalFullOddGlobalTailPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 29000000

/-- FULL UNCONDITIONAL ORIGINAL PARITY(4.15)-(4.16) real SOURCE
FOURIER TRUNCATION GLOBAL BOUND. All physical r0=20 h=-2 Q/P/B509
source e,m,k,χ,Z are summed, with correct prior selection of
nonzero η_eη_n cells, original b629 fine-alpha and ε=1 or E.

 ||FULL SOURCE B633 FOURIER - TRUNCATED BALL B633|| ≤
  [C_H L^{5(K0+90)(H+P+1)} / T^H] *
  [2ceil(L^(K0+89))+1] *
  [Acoef² exp L L^(2*C_W1+256)].

The last factor is the PROVED full-odd UNWEIGHTED positive Q/P
Cauchy diagonal; the middle factor is the PROVED physical cofactor
graph degree, and the first is the PROVED uniform original 3D
source Schwartz Fourier moment. Character-mask l1≤1 and exact
binary Z reindex cost NO extra factors. There is no exponential
#e, #m, #k, #χ, or #Z loss. No estimate of the LOW-FREQUENCY
complex Parity(4.17) two-core sum is used or claimed here.

This closes the formerly open GLOBAL (not just per-cell) inverse
polynomial high-frequency Fourier-tail analytic budget before Parity
(4.17), with finite-lower bounds on L depending only on fixed
source buffer A,R and Fourier moment order H. -/
theorem parity_eventually_original_full_odd_global_B633_fourier_tail_polylog434
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
      ‖parityOriginalHistoricalFullOddFilteredB633FourierOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport -
       parityOriginalHistoricalFullOddFilteredB633BallOuter434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport T‖ ≤
      Q * (degree * (Acoef^2*Real.exp L*
        L^(2*parityOriginalW1PolylogExponent434+256))) := by
  filter_upwards [parity_eventually_original_full_odd_filtered_tail_le_coefficient_mass434
      K0 hK0,
    parity_eventually_original_historical_extended_diagonal_polylog434] with
      L hFour hDiag
  refine ⟨hFour.1,hFour.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hAcoef hAlpha
    hU hV hUV hScale hDyad A R hA hR buf hSmooth hSupport hOne hCube
    H hLargeE hLargeN T hT
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let M := parityOriginalHistoricalFullOddFilteredCoefficientMass434
    d L E V hLw band slot δ ξ rho α signed Y K
  let D := parityOriginalHistoricalExtendedUnweightedDiagonal434
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
  have hFirst := parity_original_historical_full_odd_filtered_B633_ball_error_le_mass434
    d L U E V hLw band slot δ ξ rho K α signed Y
    hU hEpos hV hDyad buf (-Real.log A) (Real.log A)
    hSmooth hSupport hOne T hT
  have hFourMass := hFour.2.2 hLw band slot δ ξ rho U V E K α signed
    hU hV hUV hScale hDyad A R hA hR buf hSmooth hSupport hOne hCube
    H hLargeE hLargeN T hT
  have hMass : M≤degree*D :=
    parity_original_historical_full_odd_filtered_coefficient_mass_le_diagonal434
      d L U E V K0 hLw band slot δ ξ rho α signed Y K hU hScale hDyad
  have hDiagActual : D≤X := hDiag.2 band slot δ ξ rho K
    (parityOriginalHistoricalFullOddEEnvelope434 E) J α signed Acoef
    hAcoef hAlpha
  have hTotal : parityOriginalHistoricalFullOddFilteredB633TailMass434
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

/-! ## OriginalHistoricalFourierDegreePower -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The ACTUAL polylog quotient degree 2ceil(L^(K0+89))+1 is
bounded by a fixed factor 4 times L^(K0+89) for all L≥8,K0≥0.
No asymptotic O-notation or unknown exponent is introduced. -/
theorem parity_original_full_odd_actual_degree_le_four_power434
    (L K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0) :
    ((2*Nat.ceil (L^(K0+89))+1:ℕ):ℝ) ≤ 4*L^(K0+89) := by
  have hLp : 0<L := by linarith
  have hOne : (1:ℝ)≤L := by linarith
  have hExpo : (1:ℝ)≤K0+89 := by linarith
  have hLow : L≤L^(K0+89) := by
    have hMono := Real.rpow_le_rpow_of_exponent_le hOne hExpo
    simpa only [Real.rpow_one] using hMono
  let x : ℝ := L^(K0+89)
  have hx : 2≤x := by dsimp [x]; linarith
  have hx0 : 0≤x := by linarith
  have hCeil : (Nat.ceil x:ℝ) < x+1 := Nat.ceil_lt_add_one hx0
  have hCast : ((2*Nat.ceil x+1:ℕ):ℝ)=2*(Nat.ceil x:ℝ)+1 := by
    push_cast
    ring
  change ((2*Nat.ceil x+1:ℕ):ℝ)≤4*x
  rw [hCast]
  linarith

/-- Native exact arbitrary-positive-real Fourier cutoff identity
for any three genuine source polynomial costs A,B,C. Selecting
T=L^(A+B+C+D) for H=1 cancels ALL three costs without an
unproven smallness assumption:

 (L^A L^B L^C)/T = L^(-D).

This is the precise exponent budget used in the full-odd source
3D Fourier tail at arbitrary inverse-logarithmic order D. -/
theorem parity_original_three_source_power_cutoff_ratio434
    (L A B C D : ℝ) (hL : 0<L) :
    L^A*L^B*L^C/L^((A+B+C)+D)=L^(-D) := by
  have hP : L^A*L^B*L^C=L^(A+B+C) := by
    rw [Real.rpow_add hL,Real.rpow_add hL]
  rw [hP]
  exact parity_original_real_polylog_ratio_to_tail434 L (A+B+C) D hL
end Green64Analytic.Parity

end

end

