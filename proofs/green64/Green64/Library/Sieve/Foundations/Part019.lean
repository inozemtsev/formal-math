module

public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Weights.Part113
public import Green64.Library.Sieve.Foundations.Part013

@[expose] public section

/-!
# Sieve / Foundations / Part019

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalDiagonalPointwise -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The source Parity fixed physical u and selected e>0 permits AT
MOST ONE reserved Q/B509 skipped-Q vStar with actual product
`e*vStar=ordinaryPart(P,u)`. No imaginary squarefree hypothesis. -/
theorem parity_original_historical_source_fixed_e_u_vStar_card_le_one434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e u : ℕ) (he : 0<e) :
    ((parityOriginalReservedCartesianVStarSupport434 d L band slot δ).filter
      (fun vStar => e*vStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro vStar hVS vpStar hVP
  have h1 := (Finset.mem_filter.mp hVS).2
  have h2 := (Finset.mem_filter.mp hVP).2
  exact Nat.mul_left_cancel he (h1.trans h2.symm)

/-- The ACTUAL source e*vStar=ordinaryPart(P,u) gate makes
vStar a POSITIVE divisor of u whenever u>0, including all
multiplicities in the physical moving Ppart split. -/
theorem parity_original_historical_source_vStar_divides_u434
    (L : ℝ) (e u vStar : ℕ) (hu : 0<u)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    0<vStar ∧ vStar∣u := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hsplit := source_original_ordinary_times_P_part P u hu.ne'
  have hvPos : 0<vStar := by
    by_contra h
    have hz : vStar=0 := Nat.eq_zero_of_not_pos h
    rw [←hgate,hz] at hsplit
    simp at hsplit
    omega
  have hdiv : vStar ∣ u := by
    refine ⟨e*sourceOriginalPPrimePart P u,?_⟩
    calc
      u = sourceOriginalOrdinaryPart P u*sourceOriginalPPrimePart P u := hsplit.symm
      _ = (e*vStar)*sourceOriginalPPrimePart P u := by rw [hgate]
      _ = vStar*(e*sourceOriginalPPrimePart P u) := by ac_rfl
  exact ⟨hvPos,hdiv⟩

/-- Honest TRUE SOURCE pointwise Parity (4.11) diagonal ingredient:
for every selected e>0, positive u and its true reserved Q×B509
vStar support, the whole signed physical H_0(vStar) sum (not a single
hand-picked term) is ≤L^CW1*tau(u). The actual singleton vStar gate,
original W1 and factorial-cancelled H source and divisor monotonicity
are ALL proved, for either sign and every Fourier/Mellin rho. -/
theorem parity_eventually_original_historical_fixed_e_u_physical_norm_le_tau434 :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (signed : Bool) (u e : ℕ), 0<u → 0<e →
      ‖∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ,
        parityOriginalIntrinsicUnwindowedEVStarAtU434
          (sourceOriginalLiteralDepth 20 L) L u signed band slot δ ξ rho e vStar‖ ≤
        L^parityOriginalW1PolylogExponent434 * (u.divisors.card:ℝ) := by
  filter_upwards [parity_eventually_original_intrinsic_signed_AV_polylog_tau434,
    eventually_gt_atTop (0:ℝ)] with L hAV hL
  refine ⟨hL,?_⟩
  intro band slot δ ξ rho signed u e hu he
  let d := sourceOriginalLiteralDepth 20 L
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let S : Finset ℕ :=
    (parityOriginalReservedCartesianVStarSupport434 d L band slot δ).filter
      (fun vStar => e*vStar=sourceOriginalOrdinaryPart P u)
  let C : ℝ := L^parityOriginalW1PolylogExponent434 * (u.divisors.card:ℝ)
  have hCard : S.card≤1 :=
    parity_original_historical_source_fixed_e_u_vStar_card_le_one434
      d L band slot δ e u he
  have hC : 0≤C := mul_nonneg (Real.rpow_nonneg hL.le _) (Nat.cast_nonneg _)
  have hTerm (vStar : ℕ) (hv : vStar∈S) :
      ‖parityOriginalIntrinsicSignedAV434 d L band slot δ ξ
        0 rho signed vStar (vStar*sourceOriginalPPrimePart P u)‖ ≤ C := by
    have hgate := (Finset.mem_filter.mp hv).2
    have hdiv := parity_original_historical_source_vStar_divides_u434
      L e u vStar hu hgate
    have hBound := hAV band slot δ ξ 0 rho signed vStar
      (vStar*sourceOriginalPPrimePart P u) hdiv.1
    have hTau : ((vStar.divisors.card:ℝ)) ≤ (u.divisors.card:ℝ) := by
      exact_mod_cast b656_divisors_card_mono434 vStar u hu.ne' hdiv.2
    exact hBound.trans (mul_le_mul_of_nonneg_left hTau (Real.rpow_nonneg hL.le _))
  have hSum :
      (∑ vStar ∈ S,
        ‖parityOriginalIntrinsicSignedAV434 d L band slot δ ξ
          0 rho signed vStar (vStar*sourceOriginalPPrimePart P u)‖) ≤
        (S.card:ℝ)*C := by
    have hh := Finset.sum_le_card_nsmul S
      (fun vStar => ‖parityOriginalIntrinsicSignedAV434 d L band slot δ ξ
        0 rho signed vStar (vStar*sourceOriginalPPrimePart P u)‖) C hTerm
    simpa only [nsmul_eq_mul,Nat.cast_ofNat] using hh
  unfold parityOriginalIntrinsicUnwindowedEVStarAtU434
  change ‖∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
    if e*vStar=sourceOriginalOrdinaryPart P u then
      parityOriginalIntrinsicSignedAV434 d L band slot δ ξ
        0 rho signed vStar (vStar*sourceOriginalPPrimePart P u)
    else 0‖ ≤ C
  rw [←Finset.sum_filter]
  change ‖∑ vStar ∈ S,
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ
      0 rho signed vStar (vStar*sourceOriginalPPrimePart P u)‖ ≤ C
  calc
    _ ≤ ∑ vStar ∈ S,
        ‖parityOriginalIntrinsicSignedAV434 d L band slot δ ξ
          0 rho signed vStar (vStar*sourceOriginalPPrimePart P u)‖ := norm_sum_le _ _
    _ ≤ (S.card:ℝ)*C := hSum
    _ ≤ (1:ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) hC
    _ = C := one_mul _
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDiagonalEN -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- For fixed actual h=-2 m,n, the ORIGINAL positive physical
u=m*n-2 inside Parity(4.10) is unique: no arbitrary source u carries
multiple endpoint weights after Cauchy. -/
theorem parity_original_historical_Cauchy_fixed_m_n_u_card_le_one434
    (m n Y : ℕ) :
    ((Finset.Ioc 0 Y).filter (fun u => m*n=u+2)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu up hup
  have huEq := (Finset.mem_filter.mp hu).2
  have hupEq := (Finset.mem_filter.mp hup).2
  omega

/-- COMPLETE physical H0 Parity e,n,m source sum at its actual h=-2
m*n=u+2, now bounded by the single true u=m*n-2 and its complete
ordinary τ(u). The positive source selected e is not replaced by an
abstract parameter; in the final Cauchy it is proved from Q slots.
This is nontrivial even for arbitrary α_m and source negative sign. -/
theorem parity_eventually_original_historical_Cauchy_physical_ENM_tau_bound434 :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (signed : Bool) (Y e m n : ℕ), 0<e →
      ‖parityOriginalHistoricalCauchyPhysicalAtENM434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho signed Y e n m‖ ≤
        L^parityOriginalW1PolylogExponent434 * ((m*n-2).divisors.card:ℝ) := by
  filter_upwards [parity_eventually_original_historical_fixed_e_u_physical_norm_le_tau434]
    with L hL
  refine ⟨hL.1,?_⟩
  intro band slot δ ξ rho signed Y e m n he
  let d := sourceOriginalLiteralDepth 20 L
  let S : Finset ℕ := (Finset.Ioc 0 Y).filter (fun u => m*n=u+2)
  let C : ℝ := L^parityOriginalW1PolylogExponent434 *
    ((m*n-2).divisors.card:ℝ)
  have hC : 0≤C := mul_nonneg (Real.rpow_nonneg hL.1.le _) (Nat.cast_nonneg _)
  by_cases hm : 0 < m
  · by_cases hn : 0 < n
    · have hE : parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m =
          ∑ u ∈ S,
            ∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
              parityOriginalIntrinsicUnwindowedEVStarAtU434
                d L u signed band slot δ ξ rho e vStar := by
        unfold parityOriginalHistoricalCauchyPhysicalAtENM434
        unfold S
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hg : m*n=u+2 <;> simp [hm,hn,hg]
      have hSCard := parity_original_historical_Cauchy_fixed_m_n_u_card_le_one434
        m n Y
      have hU (u : ℕ) (hu : u∈S) :
          ‖∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
              parityOriginalIntrinsicUnwindowedEVStarAtU434
                d L u signed band slot δ ξ rho e vStar‖ ≤ C := by
        have huPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
        have hProduct := (Finset.mem_filter.mp hu).2
        have huEq : u = m*n-2 := by omega
        have hBound := hL.2 band slot δ ξ rho signed u e huPos he
        simpa [C,huEq] using hBound
      have hSNorm :
          (∑ u∈S,
            ‖∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
              parityOriginalIntrinsicUnwindowedEVStarAtU434
                d L u signed band slot δ ξ rho e vStar‖) ≤
          (S.card:ℝ)*C := by
        have h := Finset.sum_le_card_nsmul S
          (fun u => ‖∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434
             d L band slot δ,
             parityOriginalIntrinsicUnwindowedEVStarAtU434
               d L u signed band slot δ ξ rho e vStar‖) C hU
        simpa only [nsmul_eq_mul,Nat.cast_ofNat] using h
      change ‖parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖ ≤ C
      rw [hE]
      calc
        _ ≤ (∑ u∈S,
          ‖∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
            parityOriginalIntrinsicUnwindowedEVStarAtU434
              d L u signed band slot δ ξ rho e vStar‖) := norm_sum_le _ _
        _ ≤ (S.card:ℝ)*C := hSNorm
        _ ≤ (1:ℝ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hSCard) hC
        _ = C := one_mul _
    · have hN : n=0 := Nat.eq_zero_of_not_pos hn
      have hZero : parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m=0 := by
        unfold parityOriginalHistoricalCauchyPhysicalAtENM434
        apply Finset.sum_eq_zero
        intro u hu
        simp [hN]
      rw [hZero,norm_zero]
      exact hC
  · have hM : m=0 := Nat.eq_zero_of_not_pos hm
    have hZero : parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m=0 := by
      unfold parityOriginalHistoricalCauchyPhysicalAtENM434
      apply Finset.sum_eq_zero
      intro u hu
      simp [hM]
    rw [hZero,norm_zero]
    exact hC
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDiagonalDivisorCount -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Original Q-selected e is a divisor of the TRUE physical u,
whenever the genuine source reserved Q×B509 skipped prime vStar
satisfies e*vStar=ordinaryPart(P,u) at positive u. Full P powers are
retained in the proof; no P-free/source-independent support assumption. -/
theorem parity_original_historical_source_physical_gate_e_divides_u434
    (L : ℝ) (e u vStar : ℕ) (hu : 0<u)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    e∣u := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hsplit := source_original_ordinary_times_P_part P u hu.ne'
  refine ⟨vStar*sourceOriginalPPrimePart P u,?_⟩
  calc
    u = sourceOriginalOrdinaryPart P u * sourceOriginalPPrimePart P u := hsplit.symm
    _ = (e*vStar)*sourceOriginalPPrimePart P u := by rw [hgate]
    _ = e*(vStar*sourceOriginalPPrimePart P u) := by ac_rfl

/-- At each TRUE positive physical u, the number of original selected
Q-e integers in Parity's actual historical E-window that can survive the
physical source gate is at most τ(u). In particular there is no
spurious factor proportional to E or to the moving 20! Q depth in the
diagonal (4.11) divisor count. -/
theorem parity_original_historical_actual_e_divisor_card_le_tau434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (u : ℕ) (hu : 0<u) :
    ((parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ).filter (fun e => e∣u)).card ≤ u.divisors.card := by
  apply Finset.card_le_card
  intro e he
  exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp he).2,hu.ne'⟩

/-- Actual original source h=-2 pair COUNT and e-divisor COUNT at
fixed u: arbitrary nonnegative true u-weight (e.g. source W1/H norm)
is charged at most τ(u)τ(u+2) times. This uses real
`parityOriginalShiftTwoPositivePairFibre434` from `m*n=u+2`, the literal
selected-Q historical e-window, and actual divisors of u, not a
hypothetical independent e/n/m counting model. -/
theorem parity_original_historical_actual_diagonal_divisor_count434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (Y : ℕ) (w : ℕ → ℝ)
    (hw : ∀ u ∈ Finset.Ioc 0 Y,0≤w u) :
    (∑ u ∈ Finset.Ioc 0 Y,
      ∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot δ,
      ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        if e∣u then w u else 0) ≤
    ∑ u ∈ Finset.Ioc 0 Y,
      ((u.divisors.card:ℝ) * ((u+2).divisors.card:ℝ))*w u := by
  apply Finset.sum_le_sum
  intro u hu
  let A := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let D := A.filter (fun e => e∣u)
  let P := parityOriginalShiftTwoPositivePairFibre434 K J u
  have hCardE : D.card≤u.divisors.card :=
    parity_original_historical_actual_e_divisor_card_le_tau434
      d L E band slot δ u (Finset.mem_Ioc.mp hu).1
  have hCardP : P.card≤(u+2).divisors.card :=
    parity_original_shift_two_positive_pair_card_le_tau434 K J u
  have hFibre :
      (∑ e ∈ A, ∑ z ∈ P, if e∣u then w u else 0) =
      (D.card:ℝ) * (P.card:ℝ) * w u := by
    calc
      _ = ∑ e ∈ D, ∑ z ∈ P, w u := by
        unfold D
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hediv : e∣u <;>
          simp [hediv]
      _ = (D.card:ℝ) * (P.card:ℝ) * w u := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        push_cast
        ring
  have hMult : (D.card:ℝ)*(P.card:ℝ) ≤
      (u.divisors.card:ℝ)*((u+2).divisors.card:ℝ) := by
    calc
      _ ≤ (u.divisors.card:ℝ)*(P.card:ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hCardE) (Nat.cast_nonneg _)
      _ ≤ (u.divisors.card:ℝ)*((u+2).divisors.card:ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hCardP) (Nat.cast_nonneg _)
  change (∑ e∈A,∑ z∈P,if e∣u then w u else 0) ≤
    (u.divisors.card:ℝ)*((u+2).divisors.card:ℝ)*w u
  rw [hFibre]
  exact mul_le_mul_of_nonneg_right hMult (hw u hu)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDiagonalFibreSupport -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Exact source unwindowed physical H_0(vStar) fibre at fixed e and u.
The original selected Q prime e and Ppart valuations remain untouched. -/
def parityOriginalHistoricalFixedEU434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e u : ℕ) : ℂ :=
  ∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
    parityOriginalIntrinsicUnwindowedEVStarAtU434
      d L u signed band slot δ ξ rho e vStar

/-- If selected e does NOT divide the true positive physical u,
EVERY original reserved prime/B509 skipped Q source term vanishes;
no bound or positivity of the signed source is substituted. -/
theorem parity_original_historical_fixed_e_u_zero_unless_divisor434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e u : ℕ) (hu : 0<u)
    (hNot : ¬ e∣u) :
    parityOriginalHistoricalFixedEU434 d L band slot δ ξ rho signed e u = 0 := by
  unfold parityOriginalHistoricalFixedEU434
  apply Finset.sum_eq_zero
  intro vStar hv
  unfold parityOriginalIntrinsicUnwindowedEVStarAtU434
  have hg : ¬e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u := by
    intro hh
    exact hNot (parity_original_historical_source_physical_gate_e_divides_u434
      L e u vStar hu hh)
  simp only [if_neg hg]

/-- Original actual source h=-2 positive m,n,u gate: at fixed m,n,
there can be at most ONE u with m*n=u+2. This includes exact positive
m,n and u interval from the real Cauchy coefficients. -/
def parityOriginalHistoricalFixedMNUSupport434
    (Y m n : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 Y).filter (fun u => 0 < m ∧ 0 < n ∧ m*n=u+2)

theorem parity_original_historical_fixed_MN_source_u_card_le_one434
    (Y m n : ℕ) :
    (parityOriginalHistoricalFixedMNUSupport434 Y m n).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu up hup
  have h1 := (Finset.mem_filter.mp hu).2.2.2
  have h2 := (Finset.mem_filter.mp hup).2.2.2
  omega

/-- The true original physical source h=-2 Cauchy coefficient
at fixed e,n,m is exactly a sum over its singleton positive-u fibre;
all source factorials, signs and reserved H terms stay in FixedEU. -/
theorem parity_original_historical_Cauchy_ENM_eq_fixed_EU434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ) :
    parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m =
    ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
      parityOriginalHistoricalFixedEU434 d L band slot δ ξ rho signed e u := by
  unfold parityOriginalHistoricalCauchyPhysicalAtENM434
    parityOriginalHistoricalFixedMNUSupport434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : 0 < m ∧ 0 < n ∧ m*n=u+2
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]

/-- Norm squared of ANY complex sum over a true singleton source
fibre is the sum of individual squared norms: no Cauchy multiplicity
or unjustified triangle-square loss. -/
theorem parity_original_complex_singleton_sum_norm_sq434
    {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → ℂ)
    (hS : S.card ≤ 1) :
    ‖∑ x ∈ S, f x‖^2 = ∑ x ∈ S, ‖f x‖^2 := by
  by_cases hEmpty : S = ∅
  · subst S
    simp
  · have hn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨a,ha⟩ := hn
    have hUnique := Finset.card_le_one.mp hS
    have hEq : S = {a} := by
      apply Finset.ext
      intro b
      constructor
      · intro hb
        exact Finset.mem_singleton.mpr (hUnique b hb a ha)
      · intro hb
        have hba : b = a := Finset.mem_singleton.mp hb
        exact hba ▸ ha
    rw [hEq]
    simp

/-- Exact source h=-2 square of physical amplitude becomes a sum
over the genuine positive singleton u=m*n-2, with NO extra factor. -/
theorem parity_original_historical_actual_ENM_norm_sq_eq_U434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ) :
    ‖parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2 =
    ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
      ‖parityOriginalHistoricalFixedEU434 d L band slot δ ξ rho signed e u‖^2 := by
  rw [parity_original_historical_Cauchy_ENM_eq_fixed_EU434]
  exact parity_original_complex_singleton_sum_norm_sq434 _ _
    (parity_original_historical_fixed_MN_source_u_card_le_one434 Y m n)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDiagonalShiftedMoment -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Exact original Parity h=-2 diagonal source moment, with one original
selected e divisor of u, two H(vStar) divisor powers and the true
(m,n) divisor pair at u+2. The eighth source divisor moment pays the
whole arithmetic cost unconditionally, without pointwise tau(u)≪L^C. -/
theorem parity_original_shift_two_tau_cube_times_shift_tau_moment434 (Y : ℕ) :
    (∑ u ∈ Finset.Ioc 0 Y,
      (u.divisors.card:ℝ)^3 * ((u+2).divisors.card:ℝ)) ≤
      ((Y+2:ℕ):ℝ)*(1+Real.log ((Y+2:ℕ):ℝ))^255 := by
  let S : Finset ℕ := Finset.Ioc 0 Y
  have hS : S ⊆ Finset.Ioc 0 (Y+2) := by
    intro u hu
    have hmem := Finset.mem_Ioc.mp hu
    exact Finset.mem_Ioc.mpr ⟨hmem.1,by omega⟩
  have hShift : ∀ u∈S, 0 < (u:ℤ)+(2:ℤ) ∧ (u:ℤ)+2 ≤ ((Y+2:ℕ):ℤ) := by
    intro u hu
    have hmem := Finset.mem_Ioc.mp hu
    omega
  have hMoment := parity_translated_tau_four_product_sum434
    S (Y+2) (2:ℤ) hS hShift
  have hShiftNat (u : ℕ) : ((u:ℤ)+(2:ℤ)).toNat=u+2 := by omega
  simp_rw [hShiftNat] at hMoment
  have hSmall : (∑ u∈S,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) ≤
      ∑ u∈S,(u.divisors.card:ℝ)^4*((u+2).divisors.card:ℝ)^4 := by
    apply Finset.sum_le_sum
    intro u hu
    have hu : 0<u := (Finset.mem_Ioc.mp hu).1
    have hCardU : 1 ≤ (u.divisors.card:ℝ) := by
      have hmem : 1∈u.divisors := Nat.mem_divisors.mpr
        ⟨one_dvd _,hu.ne'⟩
      have hp := Finset.card_pos.mpr ⟨1,hmem⟩
      exact_mod_cast hp
    have hCardV : 1 ≤ ((u+2).divisors.card:ℝ) := by
      have hmem : 1∈(u+2).divisors := Nat.mem_divisors.mpr
        ⟨one_dvd _,by omega⟩
      have hp := Finset.card_pos.mpr ⟨1,hmem⟩
      exact_mod_cast hp
    let a : ℝ := (u.divisors.card:ℝ)
    let b : ℝ := ((u+2).divisors.card:ℝ)
    have ha : a^3 ≤ a^4 := by
      have hzero : 0 ≤ a^3 := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hCardU) hzero]
    have hb : b ≤ b^4 := by
      have hzero : 0 ≤ b+b^2+b^3 := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hCardV) hzero]
    change a^3*b ≤ a^4*b^4
    exact mul_le_mul ha hb (by positivity) (by positivity)
  exact hSmall.trans hMoment
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDiagonalReindex -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The real ORIGINAL h=-2 diagonal over selected e, true n,m pairs
and singleton u=m*n-2 is EXACTLY the same finite arithmetic source
with u first and the genuine m*n=u+2 product fibre. No generic
Dirichlet-convolution replacement, no invented n or e support. -/
theorem parity_original_historical_diagonal_ENM_u_reindex434
    (Q K J : Finset ℕ) (Y : ℕ) (w : ℕ → ℝ) :
    (∑ e ∈ Q, ∑ n ∈ J, ∑ m ∈ K,
      ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
        if e∣u then w u else 0) =
    ∑ u ∈ Finset.Ioc 0 Y,
      ∑ e ∈ Q, ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        if e∣u then w u else 0 := by
  classical
  let U : Finset ℕ := Finset.Ioc 0 Y
  let F : ℕ → ℕ → ℕ → ℕ → ℝ := fun e m n u =>
    if (0 < m ∧ 0 < n ∧ m*n=u+2) then (if e∣u then w u else 0) else 0
  have hOne (e m n : ℕ) :
      (∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
          if e∣u then w u else 0) = ∑ u ∈ U,F e m n u := by
    unfold parityOriginalHistoricalFixedMNUSupport434 U F
    rw [Finset.sum_filter]
  have hPairs (e u : ℕ) :
      (∑ n ∈ J, ∑ m ∈ K, F e m n u) =
      ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        if e∣u then w u else 0 := by
    unfold parityOriginalShiftTwoPositivePairFibre434 F
    rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact (Finset.sum_product K J (fun z : ℕ × ℕ =>
      if (0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2) then
        (if e∣u then w u else 0) else 0)).symm
  calc
    _ = ∑ e ∈ Q, ∑ n ∈ J, ∑ m ∈ K, ∑ u ∈ U,F e m n u := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      exact hOne e m n
    _ = ∑ e ∈ Q, ∑ n ∈ J, ∑ u ∈ U, ∑ m ∈ K,F e m n u := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm
    _ = ∑ e ∈ Q, ∑ u ∈ U, ∑ n ∈ J, ∑ m ∈ K,F e m n u := by
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm
    _ = ∑ u ∈ U, ∑ e ∈ Q, ∑ n ∈ J, ∑ m ∈ K,F e m n u := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro e he
      exact hPairs e u
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalDiagonalFiniteBound -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Source arbitrary selected e support, actual h=-2 positive m*n=u+2
pairs, and true e|u constraint have at most tau(u)*tau(u+2) choices.
The original 20! labelled Q assignments do NOT cost a separate factor
in the positive Cauchy diagonal: only integer e and actual (m,n)
values are being counted. -/
theorem parity_original_historical_actual_e_and_pair_divisor_count434
    (Q K J : Finset ℕ) (Y : ℕ) (w : ℕ → ℝ)
    (hw : ∀ u∈Finset.Ioc 0 Y, 0 ≤ w u) :
    (∑ u∈Finset.Ioc 0 Y, ∑ e∈Q,
      ∑ z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        if e∣u then w u else 0) ≤
    ∑ u∈Finset.Ioc 0 Y,
      ((u.divisors.card:ℝ)*((u+2).divisors.card:ℝ))*w u := by
  apply Finset.sum_le_sum
  intro u hu
  let D := Q.filter (fun e => e∣u)
  let P := parityOriginalShiftTwoPositivePairFibre434 K J u
  have hE : D.card≤u.divisors.card := by
    apply Finset.card_le_card
    intro e he
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp he).2,
      (Finset.mem_Ioc.mp hu).1.ne'⟩
  have hP : P.card≤(u+2).divisors.card :=
    parity_original_shift_two_positive_pair_card_le_tau434 K J u
  have hSum : (∑ e∈Q, ∑ z∈P, if e∣u then w u else 0) =
      (D.card:ℝ)*(P.card:ℝ)*w u := by
    calc
      _ = ∑ e∈D, ∑ z∈P, w u := by
        unfold D
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hd : e∣u <;> simp [hd]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        push_cast
        ring
  change (∑ e∈Q,∑ z∈P,if e∣u then w u else 0) ≤
    (u.divisors.card:ℝ)*((u+2).divisors.card:ℝ)*w u
  rw [hSum]
  have hMult : (D.card:ℝ)*(P.card:ℝ) ≤
      (u.divisors.card:ℝ)*((u+2).divisors.card:ℝ) := by
    calc
      _ ≤ (u.divisors.card:ℝ)*(P.card:ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hE) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast hP) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right hMult (hw u hu)

/-- True original Parity (4.11) finite diagonal, with the REAL entire
source Fourier/H physical coefficient, is bounded by the precise
translated arithmetic tau(u)^3*tau(u+2) moment, not an abstract
Cauchy diagonal condition. The only hypotheses are the explicit
uniform original alpha size A and the source-verified fixed-e,u H
size C*tau(u); both are discharged by actual native inputs below. -/
theorem parity_original_historical_Cauchy_diagonal_finite_tau_moment434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (A C : ℝ)
    (hA : 0≤A) (hC : 0≤C)
    (hα : ∀m∈K,‖α m‖≤A)
    (hPhysical : ∀ e u : ℕ, 0<u → 0<e →
      ‖parityOriginalHistoricalFixedEU434 d L band slot δ ξ rho signed e u‖ ≤
        C*(u.divisors.card:ℝ)) :
    parityOriginalHistoricalCauchyDiagonal434
      d L band slot δ ξ rho K J α signed Y ≤
      A^2*C^2*(∑u∈Finset.Ioc 0 Y,
        (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := by
  let Q := parityOriginalReservedCartesianESupport434 d L band slot δ
  let U := Finset.Ioc 0 Y
  let w : ℕ → ℝ := fun u => A^2*C^2*(u.divisors.card:ℝ)^2
  have hw (u : ℕ) (hu : u∈U) : 0≤w u := by
    dsimp [w]
    positivity
  have hEach (e n m : ℕ) (hm : m∈K) :
      ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2 ≤
      ∑u∈parityOriginalHistoricalFixedMNUSupport434 Y m n,
        if e∣u then w u else 0 := by
    rw [norm_mul, mul_pow]
    rw [parity_original_historical_actual_ENM_norm_sq_eq_U434]
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
      have hCSq : ‖parityOriginalHistoricalFixedEU434
          d L band slot δ ξ rho signed e u‖^2 ≤
          (C*(u.divisors.card:ℝ))^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Nat.cast_nonneg _))).mpr hv
      simp only [if_pos hdiv]
      calc
        _ ≤ A^2*(C*(u.divisors.card:ℝ))^2 :=
          mul_le_mul hASq hCSq (sq_nonneg _) (sq_nonneg _)
        _ = w u := by dsimp [w]; ring
    · have hz := parity_original_historical_fixed_e_u_zero_unless_divisor434
        d L band slot δ ξ rho signed e u huPos hdiv
      simp [hz,hdiv]
  unfold parityOriginalHistoricalCauchyDiagonal434
  change (∑ e∈Q,∑ n∈J,∑ m∈K,
    ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖^2) ≤ _
  calc
    _ ≤ ∑e∈Q,∑n∈J,∑m∈K,
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
      ∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        if e∣u then w u else 0 :=
      parity_original_historical_diagonal_ENM_u_reindex434 Q K J Y w
    _ ≤ ∑u∈U,((u.divisors.card:ℝ)*((u+2).divisors.card:ℝ))*w u :=
      parity_original_historical_actual_e_and_pair_divisor_count434 Q K J Y w hw
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

/-! ## OriginalHistoricalDiagonalXScale -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Entire original h=-2 shifted eighth-divisor-moment budget at the
ACTUAL source physical endpoint Y=floor(2exp L). The fixed numerical
constant is absorbed after L>=3^256; no false pointwise tau≤L^C. -/
theorem parity_original_shift_two_tau_cube_moment_original_x_scale434
    (L : ℝ) (hL : (3:ℝ)^256 ≤ L) :
    (∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) ≤
      Real.exp L * L^256 := by
  let Y := ⌊2*Real.exp L⌋₊
  have hLp : 0 < L := by nlinarith
  have hExp : 0 < Real.exp L := Real.exp_pos _
  have hFloor : (Y:ℝ) ≤ 2*Real.exp L := Nat.floor_le (by positivity)
  have hTwo : 2 ≤ Real.exp L := by
    have hExpLower := Real.add_one_le_exp L
    nlinarith
  have hY : ((Y+2:ℕ):ℝ) ≤ 3*Real.exp L := by
    push_cast
    linarith
  have hYPos : 0 < ((Y+2:ℕ):ℝ) := by
    exact_mod_cast (show 0<Y+2 by omega)
  have hLog : Real.log ((Y+2:ℕ):ℝ) ≤ Real.log 3 + L := by
    have hh := Real.log_le_log hYPos hY
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (Real.exp_ne_zero L),
      Real.log_exp] at hh
    exact hh
  have hlog3 : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  have hYone : 1 ≤ ((Y+2:ℕ):ℝ) := by
    exact_mod_cast (show 1≤Y+2 by omega)
  have hbase : 0 ≤ 1+Real.log ((Y+2:ℕ):ℝ) := by
    have hh := Real.log_nonneg hYone
    linarith
  have hLogBound : 1+Real.log ((Y+2:ℕ):ℝ) ≤ 3*L := by
    have hLge1 : 1≤L := by nlinarith
    linarith
  have hMoment := parity_original_shift_two_tau_cube_times_shift_tau_moment434 Y
  calc
    _ ≤ ((Y+2:ℕ):ℝ)*(1+Real.log ((Y+2:ℕ):ℝ))^255 := hMoment
    _ ≤ (3*Real.exp L)*(3*L)^255 :=
      mul_le_mul hY (pow_le_pow_left₀ hbase hLogBound 255)
        (pow_nonneg (by positivity) _) (by positivity)
    _ = (3:ℝ)^256*Real.exp L*L^255 := by ring
    _ ≤ L*Real.exp L*L^255 := by
      have hh := mul_le_mul_of_nonneg_right hL
        (mul_nonneg hExp.le (pow_nonneg hLp.le 255))
      nlinarith
    _ = Real.exp L*L^256 := by ring

/-- Final unconditional *positive original Parity (4.11) diagonal* bound:
full actual source 20! Q/P factorial, signed epsilon=1 or E,
original h=-2 m*n=u+2, real selected e and H_0(vStar), no assumed
coefficient estimate and no extra e factor. The verified pointwise H
size and true translated eighth-divisor moment yield fixed polylog
C_diag=2*C_W1+256 independent of Parity Fourier/K0 precision. -/
theorem parity_eventually_original_historical_Cauchy_diagonal_polylog434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ), 0≤Acoef →
        (∀m∈K, ‖α m‖≤Acoef) →
      parityOriginalHistoricalCauchyDiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        K J α signed ⌊2*Real.exp L⌋₊ ≤
        Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+256) := by
  filter_upwards [parity_eventually_original_historical_fixed_e_u_physical_norm_le_tau434,
    eventually_ge_atTop ((3:ℝ)^256)] with L hPhys hL
  refine ⟨hL,?_⟩
  intro band slot δ ξ rho K J α signed Acoef hAcoef hα
  let C : ℝ := L^parityOriginalW1PolylogExponent434
  have hLp : 0<L := by nlinarith [hL]
  have hC : 0≤C := Real.rpow_nonneg hLp.le _
  have hFixed (e u : ℕ) (hu : 0<u) (he : 0<e) :
      ‖parityOriginalHistoricalFixedEU434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho signed e u‖ ≤
        C*(u.divisors.card:ℝ) := by
    simpa only [parityOriginalHistoricalFixedEU434,C] using
      (hPhys.2 band slot δ ξ rho signed u e hu he)
  have hFinite := parity_original_historical_Cauchy_diagonal_finite_tau_moment434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K J α
    signed ⌊2*Real.exp L⌋₊ Acoef C hAcoef hC hα hFixed
  have hMoment := parity_original_shift_two_tau_cube_moment_original_x_scale434 L hL
  calc
    _ ≤ Acoef^2*C^2*(∑u∈Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (u.divisors.card:ℝ)^3*((u+2).divisors.card:ℝ)) := hFinite
    _ ≤ Acoef^2*C^2*(Real.exp L*L^256) :=
      mul_le_mul_of_nonneg_left hMoment (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256) := by
      have hPower : C^2*L^256 = L^(2*parityOriginalW1PolylogExponent434+256) := by
        dsimp [C]
        simp only [pow_two, ←Real.rpow_add hLp]
        rw [←Real.rpow_natCast L 256]
        rw [←Real.rpow_add hLp]
        congr 1
        ring
      rw [←hPower]
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalKRange -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Historical Parity (4.13) *real dyadic* k-range is now proved from
his actual e-window E*L^-88<=e<=E, E=U*L^-K0, both m,m'∈[U,2U),
and the integer k obtained from m'-m=e*k. No arbitrary polynomial
k bound is inserted: |k|<L^(K0+88) follows from the original data.
This is the arithmetic/dyadic budget, not yet the complete physical
Cauchy-offdiagonal summation or smooth majorant Fourier pullback. -/
theorem parity_original_historical_k_polylog_from_real_e_window434
    (L U E K0 : ℝ) (e m mp : ℕ) (k : ℤ)
    (hL : 0<L) (hU : 0<U)
    (hE : E=U*L^(-K0))
    (hwin : parityOriginalHistoricalEWindow434 L E e)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)<2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)<2*U)
    (hk : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k) :
    (k.natAbs:ℝ) < L^(K0+88) := by
  have hExpPos : 0<L^(K0+88) := Real.rpow_pos_of_pos hL _
  have hInvPos : 0<L^(-(K0+88)) := Real.rpow_pos_of_pos hL _
  have hEPos : 0<E := by
    rw [hE]
    exact mul_pos hU (Real.rpow_pos_of_pos hL _)
  have heR : 0<(e:ℝ) :=
    (mul_pos hEPos (Real.rpow_pos_of_pos hL _)).trans_le hwin.1
  have hLower : U*L^(-(K0+88)) ≤ (e:ℝ) := by
    have hPow : L^(-K0)*L^(-88:ℝ) = L^(-(K0+88)) := by
      rw [←Real.rpow_add hL]
      congr 1
      ring
    calc
      _ = (U*L^(-K0))*L^(-88:ℝ) := by rw [←hPow]; ring
      _ = E*L^(-88:ℝ) := by rw [hE]
      _ ≤ (e:ℝ) := hwin.1
  have hDiff : |(mp:ℝ)-(m:ℝ)| < U := by
    apply abs_lt.mpr
    constructor <;> linarith
  have hShift : (mp:ℝ)-(m:ℝ) = (e:ℝ)*(k:ℝ) := by
    exact_mod_cast hk
  have hKReal : |(k:ℝ)| = (k.natAbs:ℝ) := by
    simp only [Nat.cast_natAbs,Int.cast_abs]
  have hProd : (e:ℝ)*(k.natAbs:ℝ) < U := by
    calc
      _ = |(e:ℝ)*(k:ℝ)| := by rw [abs_mul,abs_of_pos heR,hKReal]
      _ = |(mp:ℝ)-(m:ℝ)| := by rw [hShift]
      _ < U := hDiff
  have hInverse : L^(-(K0+88))*L^(K0+88)=1 := by
    rw [←Real.rpow_add hL]
    simp
  by_contra hnot
  have hkLower : L^(K0+88) ≤ (k.natAbs:ℝ) := le_of_not_gt hnot
  have hFirst : (U*L^(-(K0+88)))*L^(K0+88) ≤
      (e:ℝ)*L^(K0+88) :=
    mul_le_mul_of_nonneg_right hLower hExpPos.le
  have hSecond : (e:ℝ)*L^(K0+88) ≤ (e:ℝ)*(k.natAbs:ℝ) :=
    mul_le_mul_of_nonneg_left hkLower heR.le
  have hEq : (U*L^(-(K0+88)))*L^(K0+88)=U := by
    calc
      _ = U*(L^(-(K0+88))*L^(K0+88)) := by ring
      _ = U := by rw [hInverse]; ring
  linarith [hProd,hFirst,hSecond]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalKRangeFineMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- FULL source-derived Parity(4.13) integer k-size and (2.6) Fourier
mask for actual b629 fine α and both separate signed branches.
The historical E=U L^-K0, E L^-88<=e<=E and original m,m' dyad
produce the k-polynomial bound, not a new hypothesis on k. Both
m,m' are genuine W-rough fine inputs; source selected e is actual odd
and the character identity is invoked BEFORE any ℓ1 mass estimate.
This proves k-size/mask applicability, NOT the complete offdiagonal
Cauchy cofactor to Eq(4.17) Fourier/cutoff normalization. -/
theorem parity_eventually_original_historical_fine_cauchy_k_range_mask434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (U E : ℝ) (e m mp n u up vStar vpStar : ℕ),
      0<U → E=U*L^(-K0) →
      parityOriginalHistoricalEWindow434 L E e →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      e∈parityOriginalReservedCartesianESupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ →
      0<u → 0<up →
      e*vStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u →
      e*vpStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up →
      m*n=u+2 → mp*n=up+2 → m≠mp →
      ∀ (prime : Bool) (lFine uFine : ℕ), 2≤lFine →
        Real.exp (beta*L)≤(lFine:ℝ) →
      ∀ (K : Finset ℕ),
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) mp ≠ 0 →
      let v := vStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
      let vp := vpStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up
      ∃ k : ℤ, k≠0 ∧
        ((mp:ℤ)-(m:ℤ))=(e:ℤ)*k ∧
        ((vp:ℤ)-(v:ℤ))=k*(n:ℤ) ∧
        ((m:ℤ)*(vp:ℤ)-(mp:ℤ)*(v:ℤ))=2*k ∧
        ((k.natAbs:ℝ)<L^(K0+88)) ∧
        Even k ∧
        (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
          chi (mp : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs))))=1 := by
  filter_upwards [parity_eventually_original_historical_actual_fine_cauchy_fourier_mask434
    S beta gamma (K0+88) hS hbeta hgamma] with L hFine
  refine ⟨hFine.1,?_⟩
  intro band slot δ U E e m mp n u up vStar vpStar
    hU hScale hWin hmLo hmHi hmpLo hmpHi hE hu hup hg hgp
    hmn hmpn hneq prime lFine uFine hL2 hLFine K hα hαp
  obtain ⟨k,hk,hmshift,hvshift,hdet,hMask⟩ :=
    hFine.2 band slot δ e m mp n u up vStar vpStar
      hE hu hup hg hgp hmn hmpn hneq prime lFine uFine
      hL2 hLFine K hα hαp
  have hLp : 0<L := by linarith [hFine.1]
  have hRank := parity_original_historical_k_polylog_from_real_e_window434
    L U E K0 e m mp k hLp hU hScale hWin hmLo hmHi hmpLo hmpHi hmshift
  have hMask' := hMask hRank.le
  exact ⟨k,hk,hmshift,hvshift,hdet,hRank,hMask'.1,hMask'.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagUExpansion -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The true Parity (4.13) original off-diagonal source expansion, with
both genuine positive-u=m*n-2 and u'=m'*n-2 fibres present. No
separable m,m',n distribution and no k sum is assumed in this exact
finite identity. Both complex conjugates and ε=1/E source amplitudes
remain in their original positions after Cauchy. -/
def parityOriginalHistoricalCauchyOffdiagPhysicalUExpanded434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J, ∑ m ∈ K, ∑ mp ∈ K.erase m,
      ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
        ∑ up ∈ parityOriginalHistoricalFixedMNUSupport434 Y mp n,
          (α m * parityOriginalHistoricalFixedEU434
            d L band slot δ ξ rho signed e u) *
          star (α mp * parityOriginalHistoricalFixedEU434
            d L band slot δ ξ rho signed e up)

/-- Genuine original full Cauchy offdiagonal is exactly the complete
positive-u,u' physical endpoint sum; no implicit chosen source u,
no missing Cauchy conjugation and no new signed square hypothesis. -/
theorem parity_original_historical_Cauchy_offdiag_eq_actual_u_uprime434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalCauchyOffdiagonal434
      d L band slot δ ξ rho K J α signed Y =
    parityOriginalHistoricalCauchyOffdiagPhysicalUExpanded434
      d L band slot δ ξ rho K J α signed Y := by
  unfold parityOriginalHistoricalCauchyOffdiagonal434
    parityOriginalHistoricalCauchyOffdiagPhysicalUExpanded434
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro mp hmp
  let Su := parityOriginalHistoricalFixedMNUSupport434 Y m n
  let Sup := parityOriginalHistoricalFixedMNUSupport434 Y mp n
  let F : ℕ → ℂ := fun u => α m *
    parityOriginalHistoricalFixedEU434 d L band slot δ ξ rho signed e u
  let G : ℕ → ℂ := fun up => α mp *
    parityOriginalHistoricalFixedEU434 d L band slot δ ξ rho signed e up
  have hU := parity_original_historical_Cauchy_ENM_eq_fixed_EU434
    d L band slot δ ξ rho signed Y e n m
  have hUp := parity_original_historical_Cauchy_ENM_eq_fixed_EU434
    d L band slot δ ξ rho signed Y e n mp
  rw [hU,hUp]
  have hF : α m*(∑u∈Su,parityOriginalHistoricalFixedEU434
      d L band slot δ ξ rho signed e u) = ∑u∈Su,F u := by
    exact Finset.mul_sum _ _ _
  have hG : star (α mp*(∑up∈Sup,parityOriginalHistoricalFixedEU434
      d L band slot δ ξ rho signed e up)) =
      ∑up∈Sup,star (G up) := by
    rw [Finset.mul_sum]
    rw [star_sum]
  rw [hF,hG]
  calc
    (∑u∈Su,F u)*(∑up∈Sup,star (G up)) =
      ∑u∈Su,F u*(∑up∈Sup,star (G up)) := Finset.sum_mul _ _ _
    _ = ∑u∈Su,∑up∈Sup,F u*star (G up) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagVStar -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Literal original (4.13) physical separated two-endpoint source
before character orthogonality, now with both *actual* reserved Q primes
and B509 skipped-Q vStar/vStar' sums exposed, real α, conjugate α and
signed P-multiplicity factors. No independent v-support, no projected
odd branch and no inserted sigma≠0. -/
def parityOriginalHistoricalCauchyOffdiagPhysicalVStarExpanded434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  let V := parityOriginalReservedCartesianVStarSupport434 d L band slot δ
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J, ∑ m ∈ K, ∑ mp ∈ K.erase m,
      ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
        ∑ up ∈ parityOriginalHistoricalFixedMNUSupport434 Y mp n,
          ∑ vStar ∈ V, ∑ vpStar ∈ V,
            (α m * parityOriginalIntrinsicUnwindowedEVStarAtU434
              d L u signed band slot δ ξ rho e vStar) *
            star (α mp * parityOriginalIntrinsicUnwindowedEVStarAtU434
              d L up signed band slot δ ξ rho e vpStar)

/-- TRUE full h=-2 Cauchy physical offdiagonal after expanding BOTH
original reserved-prime/B509 skipped-Q endpoint sums, retaining the
complete inner source at each exact u=m*n-2 and u'=m'*n-2. -/
theorem parity_original_historical_Cauchy_offdiag_eq_vStar_pair_source434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalCauchyOffdiagonal434
      d L band slot δ ξ rho K J α signed Y =
    parityOriginalHistoricalCauchyOffdiagPhysicalVStarExpanded434
      d L band slot δ ξ rho K J α signed Y := by
  rw [parity_original_historical_Cauchy_offdiag_eq_actual_u_uprime434]
  unfold parityOriginalHistoricalCauchyOffdiagPhysicalUExpanded434
    parityOriginalHistoricalCauchyOffdiagPhysicalVStarExpanded434
  dsimp only
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro mp hmp
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro up hup
  let V := parityOriginalReservedCartesianVStarSupport434 d L band slot δ
  let F : ℕ → ℂ := fun vs => α m *
    parityOriginalIntrinsicUnwindowedEVStarAtU434
      d L u signed band slot δ ξ rho e vs
  let G : ℕ → ℂ := fun vps => α mp *
    parityOriginalIntrinsicUnwindowedEVStarAtU434
      d L up signed band slot δ ξ rho e vps
  have hF : α m*parityOriginalHistoricalFixedEU434
      d L band slot δ ξ rho signed e u = ∑vs∈V,F vs := by
    unfold parityOriginalHistoricalFixedEU434
    exact Finset.mul_sum _ _ _
  have hG : star (α mp*parityOriginalHistoricalFixedEU434
      d L band slot δ ξ rho signed e up) = ∑vps∈V,star (G vps) := by
    unfold parityOriginalHistoricalFixedEU434
    rw [Finset.mul_sum]
    rw [star_sum]
  rw [hF,hG]
  calc
    (∑vs∈V,F vs)*(∑vps∈V,star (G vps)) =
      ∑vs∈V,F vs*(∑vps∈V,star (G vps)) := Finset.sum_mul _ _ _
    _ = ∑vs∈V,∑vps∈V,F vs*star (G vps) := by
      apply Finset.sum_congr rfl
      intro vs hvs
      rw [Finset.mul_sum]
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagGatedVStar -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The TRUE original physical two-ended e*vStar=ord_P(u) source
support, independently at the m*n and m'*n endpoints. No artificial
residue/proxy replacement or extra Ppart bound is included. -/
def parityOriginalHistoricalOffdiagPhysicalVStarGate434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e u : ℕ) : Finset ℕ :=
  (parityOriginalReservedCartesianVStarSupport434 d L band slot δ).filter
    (fun vStar => e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)

/-- Original h=-2 offdiagonal Cauchy as a finite REAL physical source
pair, with the two exact gates in its carriers rather than indicators
inside the coefficient. On the support each factor is genuinely
`v^(i rho) ε(v) W1(v) H_0(vStar)` and `v'^(i rho) ε(v') W1(v') H_0(vStar')`,
with σ=0, full P powers and real α_m/conjugate α_m'. -/
def parityOriginalHistoricalCauchyOffdiagPhysicalGated434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J, ∑ m ∈ K, ∑ mp ∈ K.erase m,
      ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
        ∑ up ∈ parityOriginalHistoricalFixedMNUSupport434 Y mp n,
          ∑ vStar ∈ parityOriginalHistoricalOffdiagPhysicalVStarGate434
            d L band slot δ e u,
            ∑ vpStar ∈ parityOriginalHistoricalOffdiagPhysicalVStarGate434
              d L band slot δ e up,
              (α m * parityOriginalIntrinsicSignedAV434
                d L band slot δ ξ 0 rho signed vStar
                  (vStar*sourceOriginalPPrimePart P u)) *
              star (α mp * parityOriginalIntrinsicSignedAV434
                d L band slot δ ξ 0 rho signed vpStar
                  (vpStar*sourceOriginalPPrimePart P up))

/-- Genuine complete source Cauchy offdiagonal exactly restricts to
both SOURCE physical e*vStar and e*vStar' gates, so all remaining
terms satisfy the historic Parity (4.13) determinant hypotheses. No
cancellation theorem and no false unconditional Type II is asserted. -/
theorem parity_original_historical_Cauchy_offdiag_eq_physical_gated_pair434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalCauchyOffdiagonal434
      d L band slot δ ξ rho K J α signed Y =
    parityOriginalHistoricalCauchyOffdiagPhysicalGated434
      d L band slot δ ξ rho K J α signed Y := by
  rw [parity_original_historical_Cauchy_offdiag_eq_vStar_pair_source434]
  unfold parityOriginalHistoricalCauchyOffdiagPhysicalVStarExpanded434
    parityOriginalHistoricalCauchyOffdiagPhysicalGated434
  dsimp only
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro mp hmp
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro up hup
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let V := parityOriginalReservedCartesianVStarSupport434 d L band slot δ
  let gu : ℕ → Prop := fun vs => e*vs=sourceOriginalOrdinaryPart P u
  let gp : ℕ → Prop := fun vs => e*vs=sourceOriginalOrdinaryPart P up
  let A : ℕ → ℂ := fun vs => α m *
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs
      (vs*sourceOriginalPPrimePart P u)
  let B : ℕ → ℂ := fun vs => α mp *
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs
      (vs*sourceOriginalPPrimePart P up)
  have hTerm (vs vps : ℕ) :
      (α m * parityOriginalIntrinsicUnwindowedEVStarAtU434
        d L u signed band slot δ ξ rho e vs) *
      star (α mp * parityOriginalIntrinsicUnwindowedEVStarAtU434
        d L up signed band slot δ ξ rho e vps) =
      if gu vs then (if gp vps then A vs * star (B vps) else 0) else 0 := by
    change (α m*(if gu vs then
      parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs
        (vs*sourceOriginalPPrimePart P u) else 0)) *
      star (α mp*(if gp vps then
        parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vps
          (vps*sourceOriginalPPrimePart P up) else 0)) = _
    by_cases h1 : gu vs <;> by_cases h2 : gp vps <;>
      simp only [h1,h2,ite_true,ite_false,mul_zero,zero_mul,star_zero]
    · rfl
  change (∑vs∈V,∑vps∈V,
    (α m*parityOriginalIntrinsicUnwindowedEVStarAtU434
      d L u signed band slot δ ξ rho e vs) *
    star (α mp*parityOriginalIntrinsicUnwindowedEVStarAtU434
      d L up signed band slot δ ξ rho e vps)) =
      ∑vs∈V.filter gu,∑vps∈V.filter gp,A vs*star (B vps)
  calc
    _ = ∑vs∈V,∑vps∈V,
        if gu vs then (if gp vps then A vs * star (B vps) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro vs hvs
          apply Finset.sum_congr rfl
          intro vps hvps
          exact hTerm vs vps
    _ = ∑vs∈V, if gu vs then
          (∑vps∈V, if gp vps then A vs*star (B vps) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro vs hvs
          by_cases hg : gu vs <;> simp [hg]
    _ = ∑vs∈V.filter gu,∑vps∈V,if gp vps then A vs*star (B vps) else 0 := by
          rw [Finset.sum_filter]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro vs hvs
          rw [Finset.sum_filter]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagGatedK -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Genuine original historical (4.7)->(4.13) source offdiagonal
support contract, no invented integer k or distinct source v factors:
* e is in the actual selected-Q source and inside the E L^-88 window;
* m*n=u+2 and mp*n=up+2 belong to the TRUE Cauchy integer fibres;
* vStar,vpStar lie in the TWO actual original Q/B509 physical gates;
* b629 original fine α is NONZERO on both actual rough cofactors.
Then the k range, evenness, 2|k| character identity, determinant
and BOTH positive z,z+2k endpoints are proved from this source data.
This is exact applicability, not the final offdiagonal reindex sum. -/
theorem parity_eventually_original_historical_gated_fine_offdiag_k_source434
    (S beta gamma K0 : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (U E : ℝ) (K J : Finset ℕ)
        (e n m mp u up vStar vpStar : ℕ),
      0<U → E=U*L^(-K0) →
      U≤(m:ℝ) → (m:ℝ)<2*U →
      U≤(mp:ℝ) → (mp:ℝ)<2*U →
      e∈parityOriginalHistoricalCauchyActiveESupport434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ →
      n∈J → m∈K → mp∈K.erase m →
      u∈parityOriginalHistoricalFixedMNUSupport434 (⌊2*Real.exp L⌋₊) m n →
      up∈parityOriginalHistoricalFixedMNUSupport434 (⌊2*Real.exp L⌋₊) mp n →
      vStar∈parityOriginalHistoricalOffdiagPhysicalVStarGate434
        (sourceOriginalLiteralDepth 20 L) L band slot δ e u →
      vpStar∈parityOriginalHistoricalOffdiagPhysicalVStarGate434
        (sourceOriginalLiteralDepth 20 L) L band slot δ e up →
      ∀ (prime : Bool) (lFine uFine : ℕ), 2≤lFine →
        Real.exp (beta*L)≤(lFine:ℝ) →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) mp ≠ 0 →
      let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
      let v := vStar*sourceOriginalPPrimePart P u
      let vp := vpStar*sourceOriginalPPrimePart P up
      ∃ k : ℤ, k≠0 ∧
        ((mp:ℤ)-(m:ℤ))=(e:ℤ)*k ∧
        ((vp:ℤ)-(v:ℤ))=k*(n:ℤ) ∧
        ((m:ℤ)*(vp:ℤ)-(mp:ℤ)*(v:ℤ))=2*k ∧
        ((mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ)) ∧
        (k.natAbs:ℝ)<L^(K0+88) ∧
        Even k ∧
        (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
          chi (mp : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs))))=1 ∧
        0<(mp:ℤ)*(v:ℤ) ∧ 0<(mp:ℤ)*(v:ℤ)+2*k := by
  filter_upwards [parity_eventually_original_historical_fine_cauchy_k_range_mask434
      S beta gamma K0 hS hbeta hgamma] with L hFine
  refine ⟨hFine.1,?_⟩
  intro band slot δ U E K J e n m mp u up vStar vpStar
    hU hScale hmLo hmHi hmpLo hmpHi he hn hm hmp hu hup hv hvp
    prime lFine uFine hl hlf hα hαp
  have hE := Finset.mem_filter.mp he
  have hM : m≠mp := (Finset.mem_erase.mp hmp).1.symm
  have huGate := (Finset.mem_filter.mp hv).2
  have hupGate := (Finset.mem_filter.mp hvp).2
  have huData := (Finset.mem_filter.mp hu).2
  have hupData := (Finset.mem_filter.mp hup).2
  have huPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0<up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hmPos : 0 < m := huData.1
  have hmpPos : 0 < mp := hupData.1
  have hSource := hFine.2 band slot δ U E e m mp n u up vStar vpStar
    hU hScale hE.2 hmLo hmHi hmpLo hmpHi hE.1 huPos hupPos
    huGate hupGate huData.2.2 hupData.2.2 hM
    prime lFine uFine hl hlf K hα hαp
  dsimp only at hSource ⊢
  obtain ⟨k,hk,hmshift,hvshift,hdet,hRank,hEven,hMask⟩ := hSource
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let v := vStar*sourceOriginalPPrimePart P u
  let vp := vpStar*sourceOriginalPPrimePart P up
  have heV : e*v=u := by
    dsimp [v]
    calc
      _ = (e*vStar)*sourceOriginalPPrimePart P u := by ac_rfl
      _ = sourceOriginalOrdinaryPart P u * sourceOriginalPPrimePart P u := by rw [huGate]
      _ = u := source_original_ordinary_times_P_part P u huPos.ne'
  have heVP : e*vp=up := by
    dsimp [vp]
    calc
      _ = (e*vpStar)*sourceOriginalPPrimePart P up := by ac_rfl
      _ = sourceOriginalOrdinaryPart P up * sourceOriginalPPrimePart P up := by rw [hupGate]
      _ = up := source_original_ordinary_times_P_part P up hupPos.ne'
  have hvPos : 0<v := Nat.pos_of_mul_pos_left (by rw [heV]; exact huPos)
  have hvpPos : 0<vp := Nat.pos_of_mul_pos_left (by rw [heVP]; exact hupPos)
  have hzPos : 0<(mp:ℤ)*(v:ℤ) := by
    exact mul_pos (by exact_mod_cast hmpPos) (by exact_mod_cast hvPos)
  have hzpEq : (mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ) := by linarith [hdet]
  have hzpPos : 0<(mp:ℤ)*(v:ℤ)+2*k := by
    rw [hzpEq]
    exact mul_pos (by exact_mod_cast hmPos) (by exact_mod_cast hvpPos)
  exact ⟨k,hk,hmshift,hvshift,hdet,hzpEq,hRank,hEven,hMask,hzPos,hzpPos⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagKPartition -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- The CANONICAL integer k attached to the original Parity (4.13)
cofactor m,m' and selected Q integer e. The quotient is well-defined
as an integer even on non-physical input; its physical validity is
proven separately from the original two SOURCE product equations. -/
def parityOriginalHistoricalOffdiagK434 (e m mp : ℕ) : ℤ :=
  ((mp:ℤ)-(m:ℤ))/(e:ℤ)

/-- The actual historically derived offdiagonal k is uniquely equal
to its source cofactor quotient. No duplicate k assignment is possible
once e>0, and we do not presume the quotient a priori divides m'-m. -/
theorem parity_original_historical_physical_k_eq_quotient434
    (e m mp : ℕ) (he : 0<e) (k : ℤ)
    (hk : ((mp:ℤ)-(m:ℤ))=(e:ℤ)*k) :
    parityOriginalHistoricalOffdiagK434 e m mp=k := by
  unfold parityOriginalHistoricalOffdiagK434
  rw [hk]
  exact Int.mul_ediv_cancel_left k (by exact_mod_cast he.ne')

/-- Every genuine historical pair of physical source endpoints with
selected odd e yields THE canonical nonzero signed k and its real
shift/determinant, without any k choice left in the coefficient. -/
theorem parity_original_historical_actual_k_quotient_source434
    (L : ℝ) (e m mp n u up vStar vpStar : ℕ)
    (he : Odd e) (hu : 0<u) (hup : 0<up)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (hgatep : e*vpStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up)
    (hmn : m*n=u+2) (hmpn : mp*n=up+2)
    (hneq : m≠mp) :
    let v := vStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    let vp := vpStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    k≠0 ∧
      ((mp:ℤ)-(m:ℤ))=(e:ℤ)*k ∧
      ((vp:ℤ)-(v:ℤ))=k*(n:ℤ) ∧
      ((m:ℤ)*(vp:ℤ)-(mp:ℤ)*(v:ℤ))=2*k ∧
      ((mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ)) := by
  dsimp only
  obtain ⟨k,hk,hm,hv,hdet,hendpoint⟩ :=
    parity_original_historical_actual_cauchy_offdiag_k434
      L e m mp n u up vStar vpStar he hu hup hgate hgatep hmn hmpn hneq
  have hCanon : parityOriginalHistoricalOffdiagK434 e m mp=k :=
    parity_original_historical_physical_k_eq_quotient434 e m mp he.pos k hm
  rw [hCanon]
  exact ⟨hk,hm,hv,hdet,hendpoint⟩

/-- The ORIGINAL finite cofactor set for one selected e and one m,
partitioned by its exact integer quotient k. A k has one FIBRE of
original m' choices, not an inserted artificial smooth k carrier. -/
def parityOriginalHistoricalKSupport434
    (e m : ℕ) (K : Finset ℕ) : Finset ℤ :=
  (K.erase m).image (parityOriginalHistoricalOffdiagK434 e m)

def parityOriginalHistoricalKPrimeFibre434
    (e m : ℕ) (K : Finset ℕ) (k : ℤ) : Finset ℕ :=
  (K.erase m).filter (fun mp => parityOriginalHistoricalOffdiagK434 e m mp=k)

/-- Exact original finite cofactor→k Fubini, including possible
collisions mp→k and WITHOUT source-unsupported assumptions on
coefficient signs, gcd, e positivity, roughness or Fourier phases.
The two-sided physical source is inserted as the arbitrary function W. -/
theorem parity_original_historical_cofactor_sum_eq_k_fibres434
    (e m : ℕ) (K : Finset ℕ) (W : ℕ → ℂ) :
    (∑ mp∈K.erase m, W mp) =
      ∑ k∈parityOriginalHistoricalKSupport434 e m K,
        ∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,W mp := by
  classical
  let S := K.erase m
  let g := parityOriginalHistoricalOffdiagK434 e m
  have hReindex := Finset.sum_image' (s:=S) (g:=g)
    (f:=fun k => ∑mp∈S.filter (fun mp=>g mp=k),W mp)
    W (by intro mp hmp; rfl)
  simpa only [parityOriginalHistoricalKSupport434,
    parityOriginalHistoricalKPrimeFibre434,S,g] using hReindex.symm

/-- Every selected e support and every fixed m within the original
physical Cauchy has the COMPLETE finite k→m' inverse reindex,
with NO unwanted exclusion of even/odd k before SOURCE support
justifies it. This exact identity is the first k-summing step towards
Parity's (4.13)--(4.17) and is NOT by itself a Type II estimate. -/
theorem parity_original_historical_cauchy_cofactor_k_partition434
    (K J : Finset ℕ) (Q : Finset ℕ)
    (H : ℕ → ℕ → ℕ → ℂ) :
    (∑e∈Q,∑n∈J,∑m∈K,∑mp∈K.erase m,H e n mp) =
    ∑e∈Q,∑n∈J,∑m∈K,
      ∑k∈parityOriginalHistoricalKSupport434 e m K,
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,H e n mp := by
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  exact parity_original_historical_cofactor_sum_eq_k_fibres434 e m K (H e n)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagKGrouped -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- Actual full original h=-2 Cauchy offdiagonal coefficient at one
(e,n,m,m') after exposing BOTH original physical u=m*n-2/u'=m'*n-2
and both H_0(vStar) SOURCE carriers. The true two-endpoint
e*vStar=ord_P(u) condition is inside the physical finite support.
This is the actual complex coefficient, not a norm surrogate. -/
def parityOriginalHistoricalOffdiagPhysicalAtENMMp434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) : ℂ :=
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  ∑ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
    ∑ up ∈ parityOriginalHistoricalFixedMNUSupport434 Y mp n,
      ∑ vStar ∈ parityOriginalHistoricalOffdiagPhysicalVStarGate434
        d L band slot δ e u,
        ∑ vpStar ∈ parityOriginalHistoricalOffdiagPhysicalVStarGate434
          d L band slot δ e up,
          (α m * parityOriginalIntrinsicSignedAV434
            d L band slot δ ξ 0 rho signed vStar
              (vStar*sourceOriginalPPrimePart P u)) *
          star (α mp * parityOriginalIntrinsicSignedAV434
            d L band slot δ ξ 0 rho signed vpStar
              (vpStar*sourceOriginalPPrimePart P up))

/-- Original Parity (4.13) *source* offdiagonal grouped FIRST by its
canonical integer k=(m'-m)/e, after each original selected e,n,m.
Every physical H_0 and genuine W1/parity/alpha/character pair is
unchanged and every cofactor pair m' is counted EXACTLY ONCE in its
corresponding source-derived k fibre. No illegal #k or Fourier-tail
bound is inserted at this finite-reindex stage. -/
def parityOriginalHistoricalCauchyOffdiagKGrouped434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J, ∑ m ∈ K,
      ∑ k ∈ parityOriginalHistoricalKSupport434 e m K,
        ∑ mp ∈ parityOriginalHistoricalKPrimeFibre434 e m K k,
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp

/-- The ACTUAL historical signed source Cauchy square OFFDIAGONAL
is EXACTLY its original k-grouped signed double-core correlation
precursor, with all P, e and m',n physical support retained. The
combinatorial k-partition is proved before using either character
orthogonality or the positive Fourier coefficient-mass bound.
This proves only the outer k-reindex, NOT source Parity (4.17) saving. -/
theorem parity_original_historical_actual_signed_offdiag_eq_k_grouped434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalCauchyOffdiagonal434
      d L band slot δ ξ rho K J α signed Y =
    parityOriginalHistoricalCauchyOffdiagKGrouped434
      d L band slot δ ξ rho K J α signed Y := by
  rw [parity_original_historical_Cauchy_offdiag_eq_physical_gated_pair434]
  unfold parityOriginalHistoricalCauchyOffdiagPhysicalGated434
    parityOriginalHistoricalCauchyOffdiagKGrouped434
  dsimp only
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  exact parity_original_historical_cofactor_sum_eq_k_fibres434 e m K
    (fun mp => parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e n m mp)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagKZero -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- Source-original Parity(4.13) simultaneous physical m*n=u+2,
m'*n=u'+2, e*vStar=ord_P(u), e*vStar'=ord_P(u') makes
k=(m'-m)/e NONZERO on every m'≠m when e is odd. In particular,
canonical k=0 carries zero actual physical Cauchy amplitude,
even if the artificially unfiltered cofactor image contains zero.
No arithmetic or analytic loss is paid for this exact deletion. -/
theorem parity_original_historical_actual_zero_k_physical_source_vanishes434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e n m mp : ℕ)
    (he : Odd e)
    (hmp : mp∈K.erase m)
    (hzero : parityOriginalHistoricalOffdiagK434 e m mp=0) :
    parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e n m mp=0 := by
  unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
  dsimp only
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro up hup
  apply Finset.sum_eq_zero
  intro vStar hvStar
  apply Finset.sum_eq_zero
  intro vpStar hvpStar
  have huP : 0<u :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupP : 0<up :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hmn : m*n=u+2 := (Finset.mem_filter.mp hu).2.2.2
  have hmpn : mp*n=up+2 := (Finset.mem_filter.mp hup).2.2.2
  have hg : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u :=
    (Finset.mem_filter.mp hvStar).2
  have hgp : e*vpStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up :=
    (Finset.mem_filter.mp hvpStar).2
  have hmNe : m≠mp := (Finset.mem_erase.mp hmp).1.symm
  have hK := parity_original_historical_actual_k_quotient_source434
    L e m mp n u up vStar vpStar he huP hupP hg hgp hmn hmpn hmNe
  exact False.elim (hK.1 hzero)

/-- Exact source cofactor m' sum over canonical k=0 has ZERO value,
not merely small norm: every true physical source term is incompatible
with original odd selected e and m'≠m. -/
theorem parity_original_historical_offdiag_zero_k_fibre_sum_zero434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e n m : ℕ) (he : Odd e) :
    (∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K 0,
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp)=0 := by
  apply Finset.sum_eq_zero
  intro mp hmp
  have hp := Finset.mem_filter.mp hmp
  exact parity_original_historical_actual_zero_k_physical_source_vanishes434
    d L band slot δ ξ rho K α signed Y e n m mp
    he hp.1 hp.2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalNonzeroKGrouped -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Original source k-fibre support after removing the impossible
zero quotient. Every genuine physical nonzero Cauchy term remains,
with its exact original integer k and full complex H0 weights. -/
def parityOriginalHistoricalNonzeroKSupport434
    (e m : ℕ) (K : Finset ℕ) : Finset ℤ :=
  (parityOriginalHistoricalKSupport434 e m K).filter (·≠0)

/-- Actual signed original h=-2 Parity (4.13) offdiagonal with
ONLY nonzero canonical source k, all m' in their exact quotient fibre,
complete two-endpoint physical e*vStar source and original W1/parity.
No k,chi,Fourier or physical Ppart cap bounds are assumed here. -/
def parityOriginalHistoricalCauchyOffdiagNonzeroK434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J, ∑ m ∈ K,
      ∑ k ∈ parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑ mp ∈ parityOriginalHistoricalKPrimeFibre434 e m K k,
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp

/-- Source-specific exact odd-e deletion of k=0 from the ENTIRE
historical signed original h=-2 physical Cauchy offdiagonal. This is
NOT a generic k!=0 hypothesis: selected e is true original Q product
with actual Q-slot primes >=4 at every sufficiently large L.
The remaining k grouping is an EXACT equality, not merely a bound. -/
theorem parity_eventually_original_historical_signed_offdiag_nonzero_k_exact434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ) (signed : Bool) (Y : ℕ),
      parityOriginalHistoricalCauchyOffdiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K J α signed Y =
      parityOriginalHistoricalCauchyOffdiagNonzeroK434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K J α signed Y := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434]
    with L hSource
  refine ⟨hSource.1,?_⟩
  intro band slot δ ξ rho K J α signed Y
  rw [parity_original_historical_actual_signed_offdiag_eq_k_grouped434]
  unfold parityOriginalHistoricalCauchyOffdiagKGrouped434
    parityOriginalHistoricalCauchyOffdiagNonzeroK434
  apply Finset.sum_congr rfl
  intro e he
  have heOdd : Odd e := (hSource.2 band slot δ e he).1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  let S := parityOriginalHistoricalKSupport434 e m K
  let W : ℤ → ℂ := fun k =>
    ∑ mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
        α signed Y e n m mp
  have hZero : W 0=0 :=
    parity_original_historical_offdiag_zero_k_fibre_sum_zero434
      (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
      K α signed Y e n m heOdd
  change (∑ k ∈ S, W k) = ∑ k∈S.filter (·≠0),W k
  calc
    _ = ∑ k∈S, if k≠0 then W k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hK : k=0
      · subst k
        simp [hZero]
      · simp [hK]
    _ = _ := by rw [Finset.sum_filter]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagCanonicalZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The canonical ORIGINAL Parity (4.13) physical v=u/e computed from
source h=-2 u=m*n-2, without trying to divide an imaginary vStar
factor or dropping original P-prime powers. The source gate proves
this quotient equals the actual physical v on support. -/
def parityOriginalHistoricalCanonicalV434 (e m n : ℕ) : ℕ :=
  (m*n-2)/e

/-- The canonical original offdiagonal z=m'*v with v=(m*n-2)/e,
from integer e,m,m',n alone. Its source correctness is proved below
under BOTH genuine h=-2 and selected-Q physical product gates. -/
def parityOriginalHistoricalCanonicalZ434 (e m mp n : ℕ) : ℕ :=
  mp*parityOriginalHistoricalCanonicalV434 e m n

/-- For true source e*vStar=ordinaryPart_P(u), positive u and
m*n=u+2, the quotient (m*n-2)/e is EXACTLY physical
vStar*Ppart_P(u). All original multiplicities remain in Ppart. -/
theorem parity_original_historical_canonical_v_eq_source_physical434
    (L : ℝ) (e m n u vStar : ℕ)
    (he : 0<e) (hu : 0<u)
    (hmn : m*n=u+2)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    parityOriginalHistoricalCanonicalV434 e m n =
      vStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hSplit := source_original_ordinary_times_P_part P u hu.ne'
  have hUeq : e*(vStar*sourceOriginalPPrimePart P u)=u := by
    calc
      _ = (e*vStar)*sourceOriginalPPrimePart P u := by ac_rfl
      _ = sourceOriginalOrdinaryPart P u * sourceOriginalPPrimePart P u := by rw [hgate]
      _ = u := hSplit
  have hSub : m*n-2=u := by omega
  unfold parityOriginalHistoricalCanonicalV434
  calc
    (m*n-2)/e = u/e := by rw [hSub]
    _ = (e*(vStar*sourceOriginalPPrimePart P u))/e := by rw [hUeq]
    _ = vStar*sourceOriginalPPrimePart P u := Nat.mul_div_cancel_left _ he

/-- Literal first physical z=m'v from the TRUE original h=-2 source,
not a surrogate z dyadic variable; only original integer data and
the full Ppart of source u enter the equality. -/
theorem parity_original_historical_canonical_z_eq_source_physical434
    (L : ℝ) (e m mp n u vStar : ℕ)
    (he : 0<e) (hu : 0<u)
    (hmn : m*n=u+2)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    parityOriginalHistoricalCanonicalZ434 e m mp n =
      mp*(vStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) := by
  unfold parityOriginalHistoricalCanonicalZ434
  rw [parity_original_historical_canonical_v_eq_source_physical434
    L e m n u vStar he hu hmn hgate]

/-- On BOTH actual source physical endpoints and genuine odd selected
e, the canonical offdiagonal z=m'*(m*n-2)/e and unique original
k=(m'-m)/e satisfy the ORIGINAL physical shift z+2k=m*v' exactly.
No extra congruence or nonzero complex coefficient assumption enters. -/
theorem parity_original_historical_canonical_z_plus_two_k_source434
    (L : ℝ) (e m mp n u up vStar vpStar : ℕ)
    (he : Odd e) (hu : 0<u) (hup : 0<up)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (hgatep : e*vpStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up)
    (hmn : m*n=u+2) (hmpn : mp*n=up+2)
    (hneq : m≠mp) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    (z:ℤ)+2*k = (m:ℤ)*
      ((vpStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up):ℤ) := by
  dsimp only
  have hReal := parity_original_historical_actual_k_quotient_source434
    L e m mp n u up vStar vpStar he hu hup hgate hgatep hmn hmpn hneq
  have hZ := parity_original_historical_canonical_z_eq_source_physical434
    L e m mp n u vStar he.pos hu hmn hgate
  dsimp only at hReal
  rw [hZ]
  exact hReal.2.2.2.2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalOffdiagZGrouped -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- Original source physical z=m'*(m*n-2)/e as an image of the
actual n support, not an arbitrarily extended z dyadic interval.
The endpoint is correct on the true physical Q/P gate and may be
zero away from that support, where the source coefficient vanishes. -/
def parityOriginalHistoricalCanonicalZSupport434
    (e m mp : ℕ) (J : Finset ℕ) : Finset ℕ :=
  J.image (parityOriginalHistoricalCanonicalZ434 e m mp)

/-- Exact n-fibre belonging to a fixed true canonical z. Source
collisions n→z are handled by an explicit finite fibre, not ignored. -/
def parityOriginalHistoricalCanonicalZNFibre434
    (e m mp : ℕ) (J : Finset ℕ) (z : ℕ) : Finset ℕ :=
  J.filter (fun n => parityOriginalHistoricalCanonicalZ434 e m mp n=z)

/-- The original n-sum is EXACTLY its canonical z-fibre decomposition,
without assuming the map is injective or claiming source positive z
before actual physical support is checked. -/
theorem parity_original_historical_n_sum_eq_canonical_z_fibres434
    (e m mp : ℕ) (J : Finset ℕ) (W : ℕ → ℂ) :
    (∑ n∈J,W n) =
      ∑ z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
        ∑ n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,W n := by
  classical
  let g := parityOriginalHistoricalCanonicalZ434 e m mp
  have h := Finset.sum_image' (s:=J) (g:=g)
    (f:=fun z => ∑n∈J.filter (fun n=>g n=z),W n)
    W (by intro n hn; rfl)
  simpa only [parityOriginalHistoricalCanonicalZSupport434,
    parityOriginalHistoricalCanonicalZNFibre434,g] using h.symm

/-- Finite original Parity (4.13) SOURCE transfer from the true original
`e,n,m,k,m'` support to `e,m,k,m',z,n` with z=m'*(m*n-2)/e.
Both normalizations are EXACT finite sums; no spurious factor of
#k, #z, actual α, α-conjugate, H0 or W1 is introduced. -/
theorem parity_original_historical_k_then_z_source_reindex434
    (Q K J : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℂ) :
    (∑e∈Q,∑n∈J,∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,F e n m mp) =
    ∑e∈Q,∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
            ∑n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,
              F e n m mp := by
  calc
    _ = ∑e∈Q,∑m∈K,∑n∈J,
          ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
            ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm
    _ = ∑e∈Q,∑m∈K,
          ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
            ∑n∈J,∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
              F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_comm
    _ = ∑e∈Q,∑m∈K,
          ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
            ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
              ∑n∈J,F e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro mp hmp
      exact parity_original_historical_n_sum_eq_canonical_z_fibres434
        e m mp J (fun n => F e n m mp)

/-- The actual original signed physical h=-2 Cauchy offdiagonal is
fully regrouped over NONZERO source k and canonical source z,
with all n-fibre collisions, m,m',e support and two physical
reserved-prime/B509 H_0 sums left exactly inside. Unlike a generic
convolution, this is the real Parity (4.10)-(4.13) SOURCE object. -/
def parityOriginalHistoricalCauchyOffdiagKZGrouped434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ m ∈ K,
      ∑ k ∈ parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑ mp ∈ parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑ z ∈ parityOriginalHistoricalCanonicalZSupport434 e m mp J,
            ∑ n ∈ parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp

/-- The whole genuine SOURCE historical Parity Cauchy offdiagonal is
EXACTLY its source `k,z` image-fibre sum, for either sign and all
Fourier/Mellin frequencies. This is the first complete finite
k+z reindex; signed character Fourier insertion and final (4.17)
analytic bound are separate obligations. -/
theorem parity_eventually_original_historical_actual_offdiag_eq_k_z_source434 :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ) (signed : Bool) (Y : ℕ),
      parityOriginalHistoricalCauchyOffdiagonal434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K J α signed Y =
      parityOriginalHistoricalCauchyOffdiagKZGrouped434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho K J α signed Y := by
  filter_upwards [parity_eventually_original_historical_signed_offdiag_nonzero_k_exact434]
    with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ rho K J α signed Y
  rw [h.2 band slot δ ξ rho K J α signed Y]
  unfold parityOriginalHistoricalCauchyOffdiagNonzeroK434
    parityOriginalHistoricalCauchyOffdiagKZGrouped434
  exact parity_original_historical_k_then_z_source_reindex434
    (parityOriginalReservedCartesianESupport434
      (sourceOriginalLiteralDepth 20 L) L band slot δ)
    K J (fun e n m mp =>
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α signed
          Y e n m mp)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActiveCauchy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The REAL historical Parity (4.5) source active e-window, rather than
all selected Q source assignments. This is the correct Cauchy square
on which the genuine |k|≪L^(K0+88) bound is available. -/
def parityOriginalHistoricalActiveCauchySquare434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℝ :=
  ∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ n ∈ J,
      ‖∑m∈K,α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- True original h=-2 Cauchy diagonal restricted to the historical
selected e-window, with complete physical H0 and signed W1. -/
def parityOriginalHistoricalActiveCauchyDiagonal434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℝ :=
  ∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ n∈J,∑m∈K,
      ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- TRUE active original Parity (4.13) signed offdiagonal with two
physical H0 source cofactor amplitudes. This is not an invented
E4.1 input; only source e-window truncation changes the outer set. -/
def parityOriginalHistoricalActiveCauchyOffdiag434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑n∈J,∑m∈K,∑mp∈K.erase m,
      (α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m)*
      star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp)

/-- Exact ORIGINAL signed Cauchy inequality with the ACTIVE historical
e-window on BOTH its coefficient mass and physical square. The
old full Q e-carrier is not silently retained on the square side,
so subsequent source-derived polynomial k range is legitimately
available throughout this Cauchy majorant. -/
theorem parity_original_historical_signed_active_e_n_cauchy434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y‖^2 ≤
      (∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          d L E band slot δ ξ rho e * β n‖^2)*
      parityOriginalHistoricalActiveCauchySquare434
        d L E band slot δ ξ rho K J α signed Y := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let S := Q.product J
  let a : (ℕ×ℕ) → ℂ := fun w =>
    parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho w.1*β w.2
  let b : (ℕ×ℕ) → ℂ := fun w =>
    ∑m∈K,α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y w.1 w.2 m
  have hSource := parity_original_historical_cauchy_e_window_restrict_exact434
    d L E band slot δ ξ rho K J α β signed Y
  rw [hSource]
  have hCS := parity_original_complex_finset_cauchy434 S a b
  change ‖∑w∈Q.product J,a w*b w‖^2 ≤
    (∑w∈Q.product J,‖a w‖^2)*(∑w∈Q.product J,‖b w‖^2) at hCS
  have hSum : (∑w∈Q.product J,a w*b w)=
    ∑e∈Q,∑n∈J,a (e,n)*b (e,n) :=
    Finset.sum_product Q J (fun w : ℕ×ℕ => a w*b w)
  have hA : (∑w∈Q.product J,‖a w‖^2)=
    ∑e∈Q,∑n∈J,‖a (e,n)‖^2 :=
    Finset.sum_product Q J (fun w : ℕ×ℕ => ‖a w‖^2)
  have hB : (∑w∈Q.product J,‖b w‖^2)=
    ∑e∈Q,∑n∈J,‖b (e,n)‖^2 :=
    Finset.sum_product Q J (fun w : ℕ×ℕ => ‖b w‖^2)
  rw [hSum,hA,hB] at hCS
  simpa only [Q,a,b,parityOriginalHistoricalActiveCauchySquare434] using hCS

/-- TRUE original active e,n physical Cauchy square has the EXACT
source m=m' nonnegative diagonal and its COMPLETE signed m≠m'
offdiagonal; no discarded e-window contribution has been restored
before squaring, and no separate signed square estimate assumed. -/
theorem parity_original_historical_active_cauchy_square_diag_offdiag434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    ((parityOriginalHistoricalActiveCauchySquare434 d L E band slot δ ξ rho
      K J α signed Y:ℝ):ℂ) =
    ((parityOriginalHistoricalActiveCauchyDiagonal434 d L E band slot δ ξ rho
      K J α signed Y:ℝ):ℂ) +
      parityOriginalHistoricalActiveCauchyOffdiag434
        d L E band slot δ ξ rho K J α signed Y := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let F : ℕ → ℕ → ℕ → ℂ := fun e n m =>
    α m * parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m
  have hOne (e n : ℕ) :
      ((‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ((∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
        (∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp)) :=
    parity_original_historical_actual_e_n_square_diag_offdiag434
      d L band slot δ ξ rho K α signed Y e n
  unfold parityOriginalHistoricalActiveCauchySquare434
    parityOriginalHistoricalActiveCauchyDiagonal434
    parityOriginalHistoricalActiveCauchyOffdiag434
  change ((∑e∈Q,∑n∈J,‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ((∑e∈Q,∑n∈J,∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
        (∑e∈Q,∑n∈J,∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp))
  have hLsum : ((∑e∈Q,∑n∈J,‖∑m∈K,F e n m‖^2:ℝ):ℂ) =
      ∑e∈Q,∑n∈J,((‖∑m∈K,F e n m‖^2:ℝ):ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  have hDsum : ((∑e∈Q,∑n∈J,∑m∈K,‖F e n m‖^2:ℝ):ℂ) =
      ∑e∈Q,∑n∈J,((∑m∈K,‖F e n m‖^2:ℝ):ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  rw [hLsum,hDsum]
  calc
    _ = ∑e∈Q,∑n∈J,
          (((∑m∈K,‖F e n m‖^2:ℝ):ℂ) +
            ∑m∈K,∑mp∈K.erase m,F e n m*star (F e n mp)) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      exact hOne e n
    _ = _ := by simp_rw [Finset.sum_add_distrib]

/-- Source monotonicity in the genuine historical e-window applies
ONLY to the NONNEGATIVE diagonal; no analogous signed offdiagonal
monotonicity is asserted. -/
theorem parity_original_historical_active_diagonal_le_full434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalActiveCauchyDiagonal434 d L E band slot δ ξ rho
      K J α signed Y ≤
    parityOriginalHistoricalCauchyDiagonal434 d L band slot δ ξ rho
      K J α signed Y := by
  unfold parityOriginalHistoricalActiveCauchyDiagonal434
    parityOriginalHistoricalCauchyDiagonal434
    parityOriginalHistoricalCauchyActiveESupport434
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro e he hne
    apply Finset.sum_nonneg
    intro n hn
    apply Finset.sum_nonneg
    intro m hm
    exact sq_nonneg _

/-- Genuine historical e-window restricted diagonal inherits the
source unconditional fixed polylog from the complete original
diagonal, without touching the complex offdiagonal or Ppart losses. -/
theorem parity_eventually_original_historical_active_diagonal_polylog434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ), 0≤Acoef →
        (∀m∈K,‖α m‖≤Acoef) →
      parityOriginalHistoricalActiveCauchyDiagonal434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed ⌊2*Real.exp L⌋₊ ≤
        Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+256) := by
  filter_upwards [parity_eventually_original_historical_Cauchy_diagonal_polylog434]
    with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ E rho K J α signed Acoef hA hα
  exact (parity_original_historical_active_diagonal_le_full434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho K J α
    signed ⌊2*Real.exp L⌋₊).trans
    (h.2 band slot δ ξ rho K J α signed Acoef hA hα)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActiveOffdiagSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- Real source original H_0(vStar) at fixed e,u is EXACTLY the
finite sum over its physically gated actual P/Q vStar support,
not a hypothetical unrestricted physical v. -/
theorem parity_original_historical_fixed_e_u_eq_actual_vStar_gate434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (e u : ℕ) :
    parityOriginalHistoricalFixedEU434 d L band slot δ ξ rho signed e u =
    ∑vs∈parityOriginalHistoricalOffdiagPhysicalVStarGate434 d L band slot δ e u,
      parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs
        (vs*sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) := by
  unfold parityOriginalHistoricalFixedEU434
    parityOriginalHistoricalOffdiagPhysicalVStarGate434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro vs hvs
  unfold parityOriginalIntrinsicUnwindowedEVStarAtU434
  rfl

/-- ORIGINAL h=-2 physical Cauchy coefficient for fixed e,n,m is
the complete true positive u=m*n-2 and gated vStar source sum.
No singleton u is replaced by a made-up (m*n-2) coefficient. -/
theorem parity_original_historical_Cauchy_ENM_eq_gated_u_vStar434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ) :
    parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m =
    ∑u∈parityOriginalHistoricalFixedMNUSupport434 Y m n,
      ∑vs∈parityOriginalHistoricalOffdiagPhysicalVStarGate434
          d L band slot δ e u,
        parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs
          (vs*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) := by
  rw [parity_original_historical_Cauchy_ENM_eq_fixed_EU434]
  apply Finset.sum_congr rfl
  intro u hu
  exact parity_original_historical_fixed_e_u_eq_actual_vStar_gate434
    d L band slot δ ξ rho signed e u

/-- One complete TRUE original offdiagonal cofactor pair at the SAME
selected e,n: product of two physical Cauchy coefficients is exactly
its source (u,u',vStar,vStar') two-gated sum, with original complex
alpha/star(alpha) and separately signed H0 values at both endpoints. -/
theorem parity_original_historical_actual_ENM_pair_eq_gated_source434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool) (Y e n m mp : ℕ) :
    (α m*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m)*
    star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n mp) =
    parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e n m mp := by
  let Su := parityOriginalHistoricalFixedMNUSupport434 Y m n
  let Sup := parityOriginalHistoricalFixedMNUSupport434 Y mp n
  let VA : ℕ → Finset ℕ := fun u =>
    parityOriginalHistoricalOffdiagPhysicalVStarGate434 d L band slot δ e u
  let A : ℕ → ℕ → ℂ := fun u vs =>
    α m*parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs
      (vs*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
  let B : ℕ → ℕ → ℂ := fun up vps =>
    α mp*parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vps
      (vps*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up)
  rw [parity_original_historical_Cauchy_ENM_eq_gated_u_vStar434
      d L band slot δ ξ rho signed Y e n m]
  rw [parity_original_historical_Cauchy_ENM_eq_gated_u_vStar434
      d L band slot δ ξ rho signed Y e n mp]
  have hLeft : α m*(∑u∈Su,∑vs∈VA u,
      parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vs
        (vs*sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)) =
      ∑u∈Su,∑vs∈VA u,A u vs := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
  have hRight : star (α mp*(∑up∈Sup,∑vps∈VA up,
      parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vps
        (vps*sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up))) =
      ∑up∈Sup,∑vps∈VA up,star (B up vps) := by
    rw [Finset.mul_sum,star_sum]
    apply Finset.sum_congr rfl
    intro up hup
    rw [Finset.mul_sum,star_sum]
  rw [hLeft,hRight]
  unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
  dsimp only
  change (∑u∈Su,∑vs∈VA u,A u vs)*
      (∑up∈Sup,∑vps∈VA up,star (B up vps)) =
    ∑u∈Su,∑up∈Sup,∑vs∈VA u,∑vps∈VA up,
      A u vs*star (B up vps)
  calc
    _ = ∑u∈Su,∑vs∈VA u,
          A u vs*(∑up∈Sup,∑vps∈VA up,star (B up vps)) :=
        by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_mul]
    _ = ∑u∈Su,∑vs∈VA u,∑up∈Sup,∑vps∈VA up,
          A u vs*star (B up vps) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro vs hvs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro up hup
      rw [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact Finset.sum_comm

/-- For ANY true original selected e-carrier Q, the historical h=-2
signed Cauchy offdiagonal cofactor source equals its EXACT k,z
source-fibre representation whenever Q is a subset of the original
Q-Cartesian source, every e in Q is odd and has physical source
support. This isolates the crucial e-window needed for Parity (4.13). -/
theorem parity_original_historical_cauchy_offdiag_Q_eq_k_z434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J Q : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (hOdd : ∀e∈Q,Odd e) :
    (∑e∈Q,∑n∈J,∑m∈K,∑mp∈K.erase m,
      (α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m)*
      star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp)) =
    ∑e∈Q,∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑z∈parityOriginalHistoricalCanonicalZSupport434 e m mp J,
            ∑n∈parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp := by
  have hPoint (e : ℕ) (n m mp : ℕ) :
      (α m*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m)*
      star (α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp) =
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp :=
    parity_original_historical_actual_ENM_pair_eq_gated_source434
      d L band slot δ ξ rho α signed Y e n m mp
  calc
    _ = ∑e∈Q,∑n∈J,∑m∈K,∑mp∈K.erase m,
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hPoint e n m mp
    _ = ∑e∈Q,∑n∈J,∑m∈K,
          ∑k∈parityOriginalHistoricalKSupport434 e m K,
            ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      exact parity_original_historical_cofactor_sum_eq_k_fibres434
        e m K (fun mp =>
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp)
    _ = ∑e∈Q,∑n∈J,∑m∈K,
          ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
            ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp := by
      apply Finset.sum_congr rfl
      intro e he
      have heOdd := hOdd e he
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      let S := parityOriginalHistoricalKSupport434 e m K
      let W : ℤ → ℂ := fun k =>
        ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp
      have hZero : W 0=0 :=
        parity_original_historical_offdiag_zero_k_fibre_sum_zero434
          d L band slot δ ξ rho K α signed Y e n m heOdd
      change (∑k∈S,W k) = ∑k∈S.filter (·≠0),W k
      calc
        _ = ∑k∈S,if k≠0 then W k else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hk0 : k=0
          · subst k
            simp [hZero]
          · simp [hk0]
        _ = _ := by rw [Finset.sum_filter]
    _ = _ := parity_original_historical_k_then_z_source_reindex434
      Q K J (fun e n m mp =>
        parityOriginalHistoricalOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActiveOffdiagKZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- TRUE Parity (4.5) active-e original h=-2 Cauchy offdiagonal,
regrouped with canonical nonzero integer k and physical source
z=m'*(m*n-2)/e. The selected e-window is INSIDE the k,z original
source carrier before the Fourier mask, so the polynomial |k| rank
will be source-applicable. -/
def parityOriginalHistoricalActiveCauchyOffdiagKZ434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
    ∑ m ∈ K,
      ∑ k ∈ parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑ mp ∈ parityOriginalHistoricalKPrimeFibre434 e m K k,
          ∑ z ∈ parityOriginalHistoricalCanonicalZSupport434 e m mp J,
            ∑ n ∈ parityOriginalHistoricalCanonicalZNFibre434 e m mp J z,
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp

/-- Kernel-derived full exact original e-window Cauchy offdiagonal
source identity to the canonical k,z image-fibre sum for BOTH signs.
This is NOT the full Parity (4.17) signed cancellation; all physical
H0 and alpha coefficients are still the true original source. -/
theorem parity_eventually_original_historical_active_offdiag_eq_k_z434 :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Y : ℕ),
      parityOriginalHistoricalActiveCauchyOffdiag434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed Y =
      parityOriginalHistoricalActiveCauchyOffdiagKZ434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed Y := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434]
    with L hSource
  refine ⟨hSource.1,?_⟩
  intro band slot δ ξ E rho K J α signed Y
  let Q := parityOriginalHistoricalCauchyActiveESupport434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ
  have hOdd : ∀e∈Q,Odd e := by
    intro e he
    have hCart : e∈parityOriginalReservedCartesianESupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ :=
      (Finset.mem_filter.mp he).1
    exact (hSource.2 band slot δ e hCart).1
  unfold parityOriginalHistoricalActiveCauchyOffdiag434
    parityOriginalHistoricalActiveCauchyOffdiagKZ434
  exact parity_original_historical_cauchy_offdiag_Q_eq_k_z434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
    K J Q α signed Y hOdd

/-- Exact original source historical active Cauchy GRAM consists of
the nonnegative original diagonal and precisely the supported
`k≠0, z=m'*(mn-2)/e` offdiagonal; no imaginary signed cancellation
or universal E theorem has been used. The full SOURCE |k| source
bound, before adding Fourier mask, applies to the active e-window. -/
theorem parity_eventually_original_historical_active_cauchy_square_eq_diag_plus_k_z434 :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (E rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Y : ℕ),
      ((parityOriginalHistoricalActiveCauchySquare434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed Y:ℝ):ℂ) =
      ((parityOriginalHistoricalActiveCauchyDiagonal434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed Y:ℝ):ℂ) +
      parityOriginalHistoricalActiveCauchyOffdiagKZ434
        (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
        K J α signed Y := by
  filter_upwards [parity_eventually_original_historical_active_offdiag_eq_k_z434]
    with L h
  refine ⟨h.1,?_⟩
  intro band slot δ ξ E rho K J α signed Y
  have hSquare := parity_original_historical_active_cauchy_square_diag_offdiag434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho K J α signed Y
  rw [h.2 band slot δ ξ E rho K J α signed Y] at hSquare
  exact hSquare
end Green64Analytic.Parity

end

end

