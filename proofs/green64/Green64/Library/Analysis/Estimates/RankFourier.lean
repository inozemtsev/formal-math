module

public import Green64.Library.Correlation.Part072
public import Green64.Library.Weights.FreeAuxCollisionJoin
public import Green64.Library.Weights.Part012

@[expose] public section

/-!
# Analysis / Estimates / RankFourier

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualRankFourier -/

section

open scoped BigOperators Classical
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- The original harmonic inverse and cutoff are applied to an independently
specified endpoint. Auxiliary dependence is restricted to the explicit c
scale here; it is not erased by the auxiliary probability normalization. -/
def parityHarmonicFourierFirst434 (Z : ℝ) (c : ℕ) (psi : ℝ → ℂ)
    (U : ℕ → ℂ) (w : ℕ) : ℂ :=
  star ((w : ℂ)⁻¹ * psi ((w : ℝ)/(Z*(c : ℝ)))) * U w

/-- Independent circle integral of the two full actual r20 rank endpoints.
The cutoff remains at Z*c, the signed displacement is exactly 2*k*c,
and the base endpoint tests contain no auxiliary argument. -/
def parityActualRankFourierPair434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (q : ℝ) (N : Finset ℕ) (Z : ℝ) (c : ℕ) (k : ℤ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (psi : ℝ → ℂ) : ℂ :=
  ∫ theta : AddCircle (1 : ℝ), fourier (-((2*k)*(c : ℤ))) theta *
    star (sourceNatFourierPoly N
      (parityHarmonicFourierFirst434 Z c psi
        (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F t1 tw true)) theta) *
    sourceNatFourierPoly N
      (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q G t2 tw false) theta
    ∂AddCircle.haarAddCircle

/-- The original native stripped arithmetic and both complete ordered mark
sums factor into the auxiliary-independent full endpoints. Every native
phase and the genuine harmonic inverse is retained exactly. -/
theorem parity_actual_rank_harmonic_endpoint_factor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (q zeta Z : ℝ) (c w wp : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (psi : ℝ → ℂ) :
    let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
    let P := b645ActualBand434 L hS
    let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi c w wp *
      (star (actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu)
        q V (parityFirstRankMark434 J 1 m hmJ fullnu hB r.2.1 r.2.2) w) *
       actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu)
        q V (paritySecondRankMark434 J 1 m hmJ fullnu hA r.1.1 r.1.2) wp) =
    sourceOriginalPureMellinPhase434 zeta c *
      (star (parityHarmonicFourierFirst434 Z c psi
        (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F t1 tw true) w) *
       parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q G t2 tw false wp) := by
  dsimp only
  unfold parityHarmonicStrippedArithmetic434 parityHarmonicSourceArithmetic434
    parityActualRankEndpoint434 parityHarmonicFourierFirst434
  dsimp only
  simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,
    ite_true,Bool.false_eq_true,ite_false,star_mul,star_star]
  ring

private theorem natural_double_fourier
    (S T : Finset ℕ) (a b : ℕ → ℂ) (d : ℤ) :
    (∫ theta : AddCircle (1 : ℝ), fourier (-d) theta *
      star (sourceNatFourierPoly S a theta) * sourceNatFourierPoly T b theta
      ∂AddCircle.haarAddCircle) =
    ∑ w ∈ S,∑ wp ∈ T,if (wp : ℤ)=(w : ℤ)+d then star (a w)*b wp else 0 := by
  have hBase := source_shifted_fourier_finite_identity434
    (S.image (fun n : ℕ => (n : ℤ))) (T.image (fun n : ℕ => (n : ℤ)))
    (fun n => a n.toNat) (fun n => b n.toNat) d
  change (∫ theta : AddCircle (1 : ℝ), fourier (-d) theta *
    star (sourceNatFourierPoly S a theta) * sourceNatFourierPoly T b theta
    ∂AddCircle.haarAddCircle) = _ at hBase
  rw [hBase,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.sum_image]
    · simp only [Int.toNat_natCast]
    · intro a ha b hb hab
      change (a : ℤ) = (b : ℤ) at hab
      exact_mod_cast hab
  · intro a ha b hb hab
    change (a : ℤ) = (b : ℤ) at hab
    exact_mod_cast hab

/-- Exact finite correlation/Fourier equality on the original chosen
natural carrier. The genuine nonzero-shift guard remains explicit, and
no scale-separation or comparison-smallness hypothesis is supplied. -/
theorem parity_actual_rank_pair_fourier434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (q zeta Z : ℝ) (c : ℕ) (k : ℤ) (N : Finset ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (psi : ℝ → ℂ) :
    let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
    let P := b645ActualBand434 L hS
    let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    (∑ w ∈ N,∑ wp ∈ N,if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
      parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi c w wp *
      (star (actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu)
        q V (parityFirstRankMark434 J 1 m hmJ fullnu hB r.2.1 r.2.2) w) *
       actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu)
        q V (paritySecondRankMark434 J 1 m hmJ fullnu hA r.1.1 r.1.2) wp) else 0) =
    if (2*k)=0 then 0 else sourceOriginalPureMellinPhase434 zeta c *
      parityActualRankFourierPair434 L hS J m hmJ nu hA hB r q N Z c k F G t1 t2 tw psi := by
  dsimp only
  by_cases hk : (2*k)=0
  · simp only [hk,ne_eq,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero,ite_true]
  · rw [if_neg hk]
    unfold parityActualRankFourierPair434
    rw [natural_double_fourier,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro wp hwp
    by_cases hs : (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ)
    · simp only [hk,ne_eq,not_false_eq_true,hs,true_and,ite_true]
      exact parity_actual_rank_harmonic_endpoint_factor434 L hS J m hmJ nu hA hB r
        q zeta Z c w wp F G t1 t2 tw psi
    · simp only [hs,and_false,ite_false,mul_zero]

/-- Exact Fourier representation of the already defined actual full rank
main at each original typed auxiliary draw. Both inverse cell masses and
both auxiliary character/cell factors remain in the unmodified scalar. -/
theorem parity_actual_weighted_rank_main_fourier434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi zeta Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
    let P := b645ActualBand434 L hS
    let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    let fullaux := parityActualFreeCollisionAux434 L hS J m hmJ nu aux
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    parityWeightedRankMain434 J 1 m hmJ fullnu Q hA hB xi P V fullaux (1/2) N
      (parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi c)
      (fun w wp => (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ)) =
    if (2*k)=0 then 0 else sourceOriginalPureMellinPhase434 zeta c *
      ∑ r ∈ parityCanonicalRankIndices434 m fullnu Q hA hB xi P V,
        parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
          (sourceOriginalProbeCellA434 m P V fullnu hA)
          (sourceOriginalProbeCellB434 m P V fullnu hB)
          r.1.2 r.2.2 (sourceOriginalProbeDA434 m fullnu fullaux)
          (sourceOriginalProbeDB434 m fullnu fullaux) (fullnu.1.card+fullnu.2.card) *
        parityActualRankFourierPair434 L hS J m hmJ nu hA hB r (1/2) N Z c k F G t1 t2 tw psi := by
  dsimp only
  unfold parityWeightedRankMain434
  simp_rw [parity_actual_rank_pair_fourier434]
  by_cases hk : (2*k)=0
  · simp only [hk,ite_true,mul_zero,Finset.sum_const_zero]
  · simp only [if_neg hk]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
end Green64Analytic.Parity

end

end

