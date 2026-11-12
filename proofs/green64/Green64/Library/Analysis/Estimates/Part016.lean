module

public import Green64.Library.Correlation.Part072
public import Green64.Library.Analysis.Estimates.RankFourier
public import Green64.Library.Weights.Part012
public import Green64.Library.Weights.Part113
public import Green64.Library.Correlation.Part070
public import Green64.Library.Weights.Part045
public import Green64.Library.Weights.Part112
public import Green64.Library.Weights.Part023
public import Green64.Library.Sieve.Foundations.Part004
public import Green64.Library.Weights.Part115
public import Green64.Library.Weights.FreeAuxCollisionJoin
public import Green64.Library.Correlation.Part037
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part109
public import Green64.Library.Weights.Part033
public import Green64.Library.Weights.Part047

@[expose] public section

/-!
# Analysis / Estimates / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FiniteMellinFourier -/

section

open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- The exact scale factor after Mellin separation; no endpoint occurs. -/
def parityScaleMellinFactor434 (Z : ℝ) (c : ℕ) (s : ℝ) : ℂ :=
  Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
    sourceOriginalPureMellinPhase434 (-2*Real.pi*s) c

/-- The first Mellin endpoint contains the harmonic inverse and only an
endpoint-frequency twist. It has no auxiliary scale/product argument. -/
def parityMellinFourierFirst434 (s : ℝ) (U : ℕ → ℂ) (w : ℕ) : ℂ :=
  star ((w : ℂ)⁻¹ * sourceOriginalPureMellinPhase434 (2*Real.pi*s) w) * U w

/-- The two Fourier endpoint sequences are auxiliary-independent. Only
the original signed additive displacement d remains coupled to the draw. -/
def parityMellinFourierPair434 (N : Finset ℕ) (U V : ℕ → ℂ) (d : ℤ) (s : ℝ) : ℂ :=
  ∫ theta : AddCircle (1 : ℝ), fourier (-d) theta *
    star (sourceNatFourierPoly N (parityMellinFourierFirst434 s U) theta) *
    sourceNatFourierPoly N V theta ∂AddCircle.haarAddCircle

/-- Constructive insertion of the actual cutoff Mellin integral through
an arbitrary finite positive Fourier correlation. Every shifted target
membership and positivity guard is retained. Integrability is proved
before the finite sum/integral interchange; there is no Fubini premise. -/
theorem parity_finite_cutoff_mellin_fourier434
    (N : Finset ℕ) (hN : ∀ w ∈ N,0<w) (U V : ℕ → ℂ)
    (Z : ℝ) (c : ℕ) (d : ℤ) (hZ : 0<Z) (hc : 0<c)
    (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u : ℝ,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) :
    let f := parityOriginalLogCutoff434 psi hSmooth hSupport
    Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s *
      (parityScaleMellinFactor434 Z c s * parityMellinFourierPair434 N U V d s)) ∧
    (∫ theta : AddCircle (1 : ℝ),fourier (-d) theta *
      star (sourceNatFourierPoly N (parityHarmonicFourierFirst434 Z c psi U) theta) *
      sourceNatFourierPoly N V theta ∂AddCircle.haarAddCircle) =
    ∫ s : ℝ,(𝓕 f : 𝓢(ℝ,ℂ)) s *
      (parityScaleMellinFactor434 Z c s * parityMellinFourierPair434 N U V d s) := by
  dsimp only
  let f := parityOriginalLogCutoff434 psi hSmooth hSupport
  let B : ℕ → ℝ → ℂ := fun w s =>
    if 0<(w : ℤ)+d ∧ ((w : ℤ)+d).toNat∈N then
      (𝓕 f : 𝓢(ℝ,ℂ)) s * parityScaleMellinFactor434 Z c s *
        (star (parityMellinFourierFirst434 s U w) * V ((w : ℤ)+d).toNat)
    else 0
  have hExpand (s : ℝ) :
      (𝓕 f : 𝓢(ℝ,ℂ)) s *
        (parityScaleMellinFactor434 Z c s * parityMellinFourierPair434 N U V d s) =
      ∑ w ∈ N,B w s := by
    unfold parityMellinFourierPair434
    rw [source_nat_shifted_fourier_identity434 N N _ V d hN]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hg : 0<(w : ℤ)+d ∧ ((w : ℤ)+d).toNat∈N
    · simp only [B,hg,and_self,ite_true]
      ring
    · simp only [B,hg,ite_false,mul_zero]
  have hBform (w : ℕ) (hg : 0<(w : ℤ)+d ∧ ((w : ℤ)+d).toNat∈N) :
      B w = fun s : ℝ =>
        ((𝓕 f : 𝓢(ℝ,ℂ)) s *
          Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
          sourceOriginalPureMellinPhase434 (2*Real.pi*s) w *
          sourceOriginalPureMellinPhase434 (-2*Real.pi*s) c) *
        ((w : ℂ)⁻¹ * star (U w) * V ((w : ℤ)+d).toNat) := by
    funext s
    simp only [B,hg,and_self,ite_true,parityScaleMellinFactor434,
      parityMellinFourierFirst434,star_mul,star_star]
    ring
  have hBI (w : ℕ) (hw : w∈N) : Integrable (B w) := by
    by_cases hg : 0<(w : ℤ)+d ∧ ((w : ℤ)+d).toNat∈N
    · rw [hBform w hg]
      exact (parity_actual_cutoff_mellin_integrable434 Z psi w c hSmooth hSupport).mul_const _
    · simp only [B,hg,ite_false]
      exact integrable_zero _ _ _
  have hVal (w : ℕ) (hw : w∈N) :
      (∫ s : ℝ,B w s) =
      if 0<(w : ℤ)+d ∧ ((w : ℤ)+d).toNat∈N then
        star (parityHarmonicFourierFirst434 Z c psi U w)*V ((w : ℤ)+d).toNat else 0 := by
    by_cases hg : 0<(w : ℤ)+d ∧ ((w : ℤ)+d).toNat∈N
    · rw [hBform w hg,integral_mul_const,
        ←parity_actual_cutoff_mellin_integral434 Z psi w c hZ (hN w hw) hc hSmooth hSupport]
      simp only [hg,and_self,ite_true,parityHarmonicFourierFirst434,star_mul,star_star]
      ring
    · simp only [B,hg,ite_false,integral_zero]
  have hIntSum : Integrable (fun s : ℝ => ∑ w ∈ N,B w s) :=
    integrable_finsetSum N hBI
  refine ⟨hIntSum.congr (Filter.Eventually.of_forall (fun s => (hExpand s).symm)),?_⟩
  calc
    _ = ∑ w ∈ N,if 0<(w : ℤ)+d ∧ ((w : ℤ)+d).toNat∈N then
        star (parityHarmonicFourierFirst434 Z c psi U w)*V ((w : ℤ)+d).toNat else 0 :=
      source_nat_shifted_fourier_identity434 N N _ V d hN
    _ = ∑ w ∈ N,∫ s : ℝ,B w s :=
      Finset.sum_congr rfl (fun w hw => (hVal w hw).symm)
    _ = ∫ s : ℝ,∑ w ∈ N,B w s := (integral_finsetSum N hBI).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun s => (hExpand s).symm))
end Green64Analytic.Parity

end

end

/-! ## ActualRankMellin -/

section

open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- Finite weighted integration, with every required integrability proof
explicit. This algebraic lemma does not supply any analytic saving. -/
theorem parity_finite_mellin_weighted_sum434 {I : Type*} [DecidableEq I]
    (S : Finset I) (f : ℝ → ℂ) (b : I → ℂ) (a : I → ℝ → ℂ)
    (hInt : ∀ i ∈ S, Integrable (fun s : ℝ => f s * a i s)) :
    Integrable (fun s : ℝ => f s * ∑ i ∈ S, b i * a i s) ∧
    (∑ i ∈ S, b i * (∫ s : ℝ, f s * a i s)) =
      ∫ s : ℝ, f s * ∑ i ∈ S, b i * a i s := by
  let B : I → ℝ → ℂ := fun i s => b i * (f s * a i s)
  have hB (i : I) (hi : i ∈ S) : Integrable (B i) := (hInt i hi).const_mul _
  have hForm (s : ℝ) : (∑ i ∈ S, B i s) = f s * ∑ i ∈ S, b i * a i s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by dsimp only [B]; ring)
  have hSum := integrable_finsetSum S hB
  refine ⟨hSum.congr (Filter.Eventually.of_forall hForm), ?_⟩
  calc
    _ = ∑ i ∈ S, ∫ s : ℝ, B i s := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (integral_const_mul _ _).symm
    _ = ∫ s : ℝ, ∑ i ∈ S, B i s := (integral_finsetSum S hB).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hForm)

/-- Actual full rank Mellin amplitude at a genuine typed auxiliary draw.
The endpoints have no auxiliary argument. The complete cell scalar,
both inverse masses, the original Mellin phase and signed 2*k*c shift
remain outside those endpoints. The amplitude is independent of psi. -/
def parityActualRankMellinAtAux434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi zeta Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (s : ℝ) : ℂ :=
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let fullaux := parityActualFreeCollisionAux434 L hS J m hmJ nu aux
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  if (2*k) = 0 then 0 else sourceOriginalPureMellinPhase434 zeta c *
    ∑ r ∈ parityCanonicalRankIndices434 m fullnu Q hA hB xi P V,
      parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
        (sourceOriginalProbeCellA434 m P V fullnu hA)
        (sourceOriginalProbeCellB434 m P V fullnu hB)
        r.1.2 r.2.2 (sourceOriginalProbeDA434 m fullnu fullaux)
        (sourceOriginalProbeDB434 m fullnu fullaux) (fullnu.1.card+fullnu.2.card) *
      (parityScaleMellinFactor434 Z c s *
        parityMellinFourierPair434 N
          (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) F t1 tw true)
          (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) G t2 tw false)
          ((2*k)*(c : ℤ)) s)

/-- Genuine cutoff Mellin insertion for the already defined actual rank
main, for every typed auxiliary draw. Positivity of the actual product
is proved from its original construction, with no nonzero-slice premise.
Both integrability and the equality are conclusions. -/
theorem parity_actual_weighted_rank_main_mellin434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi zeta Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (hN : ∀ n ∈ N, 0 < n) (hZ : 0 < Z)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (psi : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    let f := parityOriginalLogCutoff434 psi hSmooth hSupport
    let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
    let P := b645ActualBand434 L hS
    let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    let fullaux := parityActualFreeCollisionAux434 L hS J m hmJ nu aux
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s *
      parityActualRankMellinAtAux434 L hS J m hmJ nu Q hA hB xi zeta Z k N F G t1 t2 tw aux s) ∧
    parityWeightedRankMain434 J 1 m hmJ fullnu Q hA hB xi P V fullaux (1/2) N
      (parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi c)
      (fun w wp => (2*k) ≠ 0 ∧ (wp : ℤ) = (w : ℤ)+(2*k)*(c : ℤ)) =
      ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s *
        parityActualRankMellinAtAux434 L hS J m hmJ nu Q hA hB xi zeta Z k N F G t1 t2 tw aux s := by
  dsimp only
  let f := parityOriginalLogCutoff434 psi hSmooth hSupport
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let fullaux := parityActualFreeCollisionAux434 L hS J m hmJ nu aux
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let R := parityCanonicalRankIndices434 m fullnu Q hA hB xi P V
  let b : ParityPrimitiveRankIndex434 Q → ℂ := fun r =>
    parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
      (sourceOriginalProbeCellA434 m P V fullnu hA)
      (sourceOriginalProbeCellB434 m P V fullnu hB)
      r.1.2 r.2.2 (sourceOriginalProbeDA434 m fullnu fullaux)
      (sourceOriginalProbeDB434 m fullnu fullaux) (fullnu.1.card+fullnu.2.card)
  let a : ParityPrimitiveRankIndex434 Q → ℝ → ℂ := fun r s =>
    parityScaleMellinFactor434 Z c s *
      parityMellinFourierPair434 N
        (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) F t1 tw true)
        (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) G t2 tw false)
        ((2*k)*(c : ℤ)) s
  have hc : 0 < c := parity_actual_probe_aux_positive434 L hS J m hmJ nu aux
  have hEach (r : ParityPrimitiveRankIndex434 Q) :=
    parity_finite_cutoff_mellin_fourier434 N hN
      (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) F t1 tw true)
      (parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) G t2 tw false)
      Z c ((2*k)*(c : ℤ)) hZ hc psi hSmooth hSupport
  have hSum := parity_finite_mellin_weighted_sum434 R (fun s => (𝓕 f : 𝓢(ℝ,ℂ)) s)
    b a (fun r hr => (hEach r).1)
  by_cases hk : (2*k) = 0
  · constructor
    · simp only [parityActualRankMellinAtAux434,hk,ite_true,mul_zero]
      exact integrable_zero _ _ _
    · rw [parity_actual_weighted_rank_main_fourier434]
      simp only [parityActualRankMellinAtAux434,hk,ite_true,mul_zero,integral_zero]
  · have hForm (s : ℝ) :
        sourceOriginalPureMellinPhase434 zeta c *
          ((𝓕 f : 𝓢(ℝ,ℂ)) s * ∑ r ∈ R, b r * a r s) =
        (𝓕 f : 𝓢(ℝ,ℂ)) s *
          parityActualRankMellinAtAux434 L hS J m hmJ nu Q hA hB xi zeta Z k N F G t1 t2 tw aux s := by
      simp only [parityActualRankMellinAtAux434,hk,ite_false]
      change _ = (𝓕 f : 𝓢(ℝ,ℂ)) s *
        (sourceOriginalPureMellinPhase434 zeta c * ∑ r ∈ R, b r * a r s)
      ring
    refine ⟨(hSum.1.const_mul _).congr (Filter.Eventually.of_forall hForm), ?_⟩
    rw [parity_actual_weighted_rank_main_fourier434,if_neg hk]
    change sourceOriginalPureMellinPhase434 zeta c *
      (∑ r ∈ R, b r * parityActualRankFourierPair434 L hS J m hmJ nu hA hB r
        (1/2) N Z c k F G t1 t2 tw psi) = _
    calc
      _ = sourceOriginalPureMellinPhase434 zeta c *
          (∑ r ∈ R, b r * ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s * a r s) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        exact congrArg (fun z : ℂ => b r*z) (hEach r).2
      _ = sourceOriginalPureMellinPhase434 zeta c *
          (∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s * ∑ r ∈ R, b r*a r s) :=
        congrArg (fun z : ℂ => sourceOriginalPureMellinPhase434 zeta c*z) hSum.2
      _ = ∫ s : ℝ, sourceOriginalPureMellinPhase434 zeta c *
          ((𝓕 f : 𝓢(ℝ,ℂ)) s * ∑ r ∈ R, b r*a r s) := (integral_const_mul _ _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hForm)
end Green64Analytic.Parity

end

end

/-! ## CellLocalizedMellin -/

section

open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

/-- Insert a common CELL-scale cutoff into both endpoint tests without
changing the original finite shifted correlation. This equality is proved
using the original psi support and signed shift, not by defining the
original pairing to be the localized expression. -/
theorem parity_cell_localized_fourier_pair434
    (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n) (U V : ℕ → ℂ)
    (Z Hp : ℝ) (c : ℕ) (k : ℤ) (hZ : 0 < Z) (hHp : 0 < Hp)
    (hclo : Hp ≤ (c : ℝ)) (hchi : (c : ℝ) ≤ Hp*Real.exp 2)
    (hSmall : |2*(k : ℝ)/Z| ≤ (128*Real.exp 2)⁻¹)
    (psi eta : ℝ → ℂ)
    (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (hEta : ∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u = 1) :
    (∫ theta : AddCircle (1 : ℝ), fourier (-((2*k)*(c : ℤ))) theta *
      star (sourceNatFourierPoly N (parityHarmonicFourierFirst434 Z c psi U) theta) *
      sourceNatFourierPoly N V theta ∂AddCircle.haarAddCircle) =
    (∫ theta : AddCircle (1 : ℝ), fourier (-((2*k)*(c : ℤ))) theta *
      star (sourceNatFourierPoly N (parityHarmonicFourierFirst434 Z c psi
        (fun n => eta ((n : ℝ)/(Z*Hp))*U n)) theta) *
      sourceNatFourierPoly N (fun n => eta ((n : ℝ)/(Z*Hp))*V n) theta
      ∂AddCircle.haarAddCircle) := by
  rw [source_nat_shifted_fourier_identity434 N N _ _ _ hN,
    source_nat_shifted_fourier_identity434 N N _ _ _ hN]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hg : 0 < (w : ℤ)+(2*k)*(c : ℤ) ∧ ((w : ℤ)+(2*k)*(c : ℤ)).toNat ∈ N
  · simp only [hg,and_self,ite_true]
    by_cases hPsi : psi ((w : ℝ)/(Z*(c : ℝ))) = 0
    · simp only [parityHarmonicFourierFirst434,hPsi,mul_zero,star_zero,zero_mul]
    · have hShift : (((w : ℤ)+(2*k)*(c : ℤ)).toNat : ℤ) =
          (w : ℤ)+(2*k)*(c : ℤ) := Int.toNat_of_nonneg hg.1.le
      have hWin := parity_cell_scale_signed_window434 Z Hp c w _ k hZ hHp
        hclo hchi hSmall hShift psi hSupport hPsi
      simp only [parityHarmonicFourierFirst434,hEta _ hWin.1,hEta _ hWin.2,one_mul]
  · simp only [hg,ite_false]

/-- Exact original-cutoff Mellin insertion AFTER the proved common-cell
localization. The two endpoint tests depend on Hp fixed by the cells,
but not on the auxiliary product c. Integrability is derived, while c
remains in its exact scale phase and signed Fourier displacement. -/
theorem parity_cell_localized_cutoff_mellin434
    (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n) (U V : ℕ → ℂ)
    (Z Hp : ℝ) (c : ℕ) (k : ℤ) (hZ : 0 < Z) (hHp : 0 < Hp)
    (hclo : Hp ≤ (c : ℝ)) (hchi : (c : ℝ) ≤ Hp*Real.exp 2)
    (hSmall : |2*(k : ℝ)/Z| ≤ (128*Real.exp 2)⁻¹)
    (psi eta : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (hEta : ∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u = 1) :
    let f := parityOriginalLogCutoff434 psi hSmooth hSupport
    Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s *
      (parityScaleMellinFactor434 Z c s * parityMellinFourierPair434 N
        (fun n => eta ((n : ℝ)/(Z*Hp))*U n)
        (fun n => eta ((n : ℝ)/(Z*Hp))*V n) ((2*k)*(c : ℤ)) s)) ∧
    (∫ theta : AddCircle (1 : ℝ), fourier (-((2*k)*(c : ℤ))) theta *
      star (sourceNatFourierPoly N (parityHarmonicFourierFirst434 Z c psi U) theta) *
      sourceNatFourierPoly N V theta ∂AddCircle.haarAddCircle) =
    ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s *
      (parityScaleMellinFactor434 Z c s * parityMellinFourierPair434 N
        (fun n => eta ((n : ℝ)/(Z*Hp))*U n)
        (fun n => eta ((n : ℝ)/(Z*Hp))*V n) ((2*k)*(c : ℤ)) s) := by
  have hc : 0 < c := by exact_mod_cast hHp.trans_le hclo
  have hM := parity_finite_cutoff_mellin_fourier434 N hN
    (fun n => eta ((n : ℝ)/(Z*Hp))*U n)
    (fun n => eta ((n : ℝ)/(Z*Hp))*V n)
    Z c ((2*k)*(c : ℤ)) hZ hc psi hSmooth hSupport
  exact ⟨hM.1,(parity_cell_localized_fourier_pair434 N hN U V Z Hp c k hZ hHp
    hclo hchi hSmall psi eta hSupport hEta).trans hM.2⟩
end Green64Analytic.Parity

end

end

/-! ## ActualCellFourierCarrier -/

section

open scoped BigOperators Classical FourierTransform
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000

/-- The exact positive comparison carrier is contained in the original
B654 global carrier. The already proved dyadic exponential bound supplies
the strict seed upper endpoint; no radius estimate is assumed. -/
theorem parity_actual_comparison_cap_subset434
    (J : ℕ) (Ck L : ℝ) (hL : 0 < L) (M : ℕ)
    (hM : (M : ℝ) ≤ Real.exp (2*L)) :
    Finset.Icc 1 M ⊆ parityPositiveNaturalPositions434
      (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)) := by
  intro n hn
  have h := Finset.mem_Icc.mp hn
  have hlim : (n : ℝ) < (parityDyadicLimit434 L : ℝ) :=
    (show (n : ℝ) ≤ (M : ℝ) by exact_mod_cast h.2).trans_lt
      (hM.trans_lt (parity_dyadic_limit_exp434 L hL))
  have hnlim : n < parityDyadicLimit434 L := by exact_mod_cast hlim
  apply (parity_positive_natural_positions_mem434 _ n).mpr
  exact ⟨by omega,b654_seed_mem_interval_window434 J Ck L 1 (parityDyadicLimit434 L) n
    (Finset.mem_Ico.mpr ⟨h.1,hnlim⟩)⟩

/-- Actual fixed support at Y implies membership of the true positive
source cap ceil(A*Y), including the strict lower endpoint n>0. -/
theorem parity_cell_cutoff_natural_support434
    (A Y : ℝ) (hA : 1 ≤ A) (hY : 0 < Y) (eta : ℝ → ℂ)
    (hSupport : ∀ u : ℝ, eta u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (n : ℕ) (hn : eta ((n : ℝ)/Y) ≠ 0) :
    n ∈ Finset.Icc 1 ⌈A*Y⌉₊ := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hs := hSupport _ hn
  have hlow : 0 < (n : ℝ) :=
    (mul_pos (one_div_pos.mpr hAp) hY).trans_le ((le_div_iff₀ hY).mp hs.1)
  have hhi : (n : ℝ) ≤ (⌈A*Y⌉₊ : ℝ) := ((div_le_iff₀ hY).mp hs.2).trans (Nat.le_ceil _)
  apply Finset.mem_Icc.mpr
  have hn0 : 0 < n := by exact_mod_cast hlow
  exact ⟨by omega,by exact_mod_cast hhi⟩

/-- Exact finite Fourier carrier restriction with a proved support
condition. This uses the imported native definition of sourceNatFourierPoly;
its inherited SourceNatArcEnergy source-mapping debt is unchanged. -/
theorem parity_nat_fourier_restrict_support434
    (N M : Finset ℕ) (hMN : M ⊆ N) (U : ℕ → ℂ)
    (hU : ∀ n ∈ N, n ∉ M → U n = 0) :
    sourceNatFourierPoly N U = sourceNatFourierPoly M U := by
  unfold sourceNatFourierPoly sourceCircleFourierPoly
  symm
  apply Finset.sum_subset (Finset.image_subset_image hMN)
  intro z hz hzM
  obtain ⟨n,hn,hnz⟩ := Finset.mem_image.mp hz
  subst z
  have hnM : n ∉ M := fun h => hzM (Finset.mem_image.mpr ⟨n,h,rfl⟩)
  simp only [Int.toNat_natCast,hU n hn hnM]
  ext theta
  simp only [ContinuousMap.smul_apply,ContinuousMap.zero_apply,smul_eq_mul,zero_mul]

/-- On the actual localized endpoint, the original B654 natural carrier
and the true source comparison carrier give identical Fourier polynomials.
The equality is not an assumed endpoint or support correspondence. -/
theorem parity_actual_cell_fourier_carrier434
    (J : ℕ) (Ck L : ℝ) (hL : 0 < L) (A Y : ℝ) (hA : 1 ≤ A) (hY : 0 < Y)
    (eta : ℝ → ℂ) (hSupport : ∀ u : ℝ, eta u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (hCap : (⌈A*Y⌉₊ : ℝ) ≤ Real.exp (2*L)) (U : ℕ → ℂ) :
    sourceNatFourierPoly
      (parityPositiveNaturalPositions434 (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)))
      (fun n : ℕ => eta ((n : ℝ)/Y)*U n) =
    sourceNatFourierPoly (Finset.Icc 1 ⌈A*Y⌉₊) (fun n : ℕ => eta ((n : ℝ)/Y)*U n) := by
  apply parity_nat_fourier_restrict_support434 _ _
    (parity_actual_comparison_cap_subset434 J Ck L hL _ hCap)
  intro n hn hnM
  have hz : eta ((n : ℝ)/Y) = 0 := by
    by_contra hh
    exact hnM (parity_cell_cutoff_natural_support434 A Y hA hY eta hSupport n hh)
  rw [hz,zero_mul]

/-- Both auxiliary-independent Mellin endpoints transport to exactly the
source comparison cap. The harmonic inverse and Mellin twist stay in the
first endpoint, and the original signed displacement d is unchanged. -/
theorem parity_actual_cell_mellin_pair_carrier434
    (J : ℕ) (Ck L : ℝ) (hL : 0 < L) (A Y : ℝ) (hA : 1 ≤ A) (hY : 0 < Y)
    (eta : ℝ → ℂ) (hSupport : ∀ u : ℝ, eta u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (hCap : (⌈A*Y⌉₊ : ℝ) ≤ Real.exp (2*L)) (U V : ℕ → ℂ) (d : ℤ) (s : ℝ) :
    parityMellinFourierPair434
      (parityPositiveNaturalPositions434 (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)))
      (fun n : ℕ => eta ((n : ℝ)/Y)*U n) (fun n : ℕ => eta ((n : ℝ)/Y)*V n) d s =
    parityMellinFourierPair434 (Finset.Icc 1 ⌈A*Y⌉₊)
      (fun n : ℕ => eta ((n : ℝ)/Y)*U n) (fun n : ℕ => eta ((n : ℝ)/Y)*V n) d s := by
  have hFirst : parityMellinFourierFirst434 s (fun n : ℕ => eta ((n : ℝ)/Y)*U n) =
      fun n : ℕ => eta ((n : ℝ)/Y)*parityMellinFourierFirst434 s U n := by
    funext n
    unfold parityMellinFourierFirst434
    ring
  unfold parityMellinFourierPair434
  simp only [hFirst]
  rw [parity_actual_cell_fourier_carrier434 J Ck L hL A Y hA hY eta hSupport hCap,
    parity_actual_cell_fourier_carrier434 J Ck L hL A Y hA hY eta hSupport hCap]
end Green64Analytic.Parity

end

end

/-! ## ActualCellRankMellin -/

section

open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 28000

/-- The genuine full rank Mellin amplitude with common-cell localization.
For each rank, Hp uses only its two integer cell indices. Both endpoint
sequences use eta(n/(Z*Hp)), never eta chosen at an auxiliary endpoint.
The complete literal scalar retains both masses and both cell gates. -/
def parityActualCellRankMellinAtAux434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi zeta Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (eta : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (s : ℝ) : ℂ :=
  let P := sourceNativeOriginalTb434 20 L
  let V := sourceNativeOriginalVbig434 20 L
  let a := sourceOriginalProbeMemoryAuxValues434 P J m hmJ nu aux
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  if (2*k) = 0 then 0 else sourceOriginalPureMellinPhase434 zeta c *
    ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi P V,
      let Hp := Real.exp ((r.1.1 : ℝ)*hA)*Real.exp ((r.2.1 : ℝ)*hB)
      parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
        (sourceOriginalProbeCellA434 m P V nu hA)
        (sourceOriginalProbeCellB434 m P V nu hB)
        r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu a)
        (sourceOriginalProbeDB434 m nu a) (nu.1.card+nu.2.card) *
      (parityScaleMellinFactor434 Z c s *
        parityMellinFourierPair434 N
          (fun n => eta ((n : ℝ)/(Z*Hp)) *
            parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) F t1 tw true n)
          (fun n => eta ((n : ℝ)/(Z*Hp)) *
            parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) G t2 tw false n)
          ((2*k)*(c : ℤ)) s)

/-- The independently defined original actual rank-main equals the
Mellin integral of its common-cell localized endpoints. The true scalar
itself enforces the literal auxiliary cells; no cell-membership premise
is added for the whole auxiliary sum and no mass factor is discarded. -/
theorem parity_actual_weighted_cell_rank_main_mellin434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    (Q : ℕ) (hA hB xi zeta Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (hN : ∀ n ∈ N, 0 < n) (hZ : 0 < Z) (hA1 : hA ≤ 1) (hB1 : hB ≤ 1)
    (hSmall : |2*(k : ℝ)/Z| ≤ (128*Real.exp 2)⁻¹)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (psi eta : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (hEta : ∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u = 1)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    let f := parityOriginalLogCutoff434 psi hSmooth hSupport
    let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
    let P := b645ActualBand434 L hS
    let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    let fullaux := parityActualFreeCollisionAux434 L hS J m hmJ nu aux
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s *
      parityActualCellRankMellinAtAux434 L hS J m hmJ nu Q hA hB xi zeta Z k N
        F G t1 t2 tw eta aux s) ∧
    parityWeightedRankMain434 J 1 m hmJ fullnu Q hA hB xi P V fullaux (1/2) N
      (parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi c)
      (fun w wp => (2*k) ≠ 0 ∧ (wp : ℤ) = (w : ℤ)+(2*k)*(c : ℤ)) =
      ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s *
        parityActualCellRankMellinAtAux434 L hS J m hmJ nu Q hA hB xi zeta Z k N
          F G t1 t2 tw eta aux s := by
  dsimp only
  simp only [b645ActualBand434,parityActualFreeCollisionAux434]
  let f := parityOriginalLogCutoff434 psi hSmooth hSupport
  let P := sourceNativeOriginalTb434 20 L
  let V := sourceNativeOriginalVbig434 20 L
  let vals := sourceOriginalProbeMemoryAuxValues434 P J m hmJ nu aux
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let R := parityCanonicalRankIndices434 m nu Q hA hB xi P V
  let Hp : ParityPrimitiveRankIndex434 Q → ℝ := fun r =>
    Real.exp ((r.1.1 : ℝ)*hA)*Real.exp ((r.2.1 : ℝ)*hB)
  let b : ParityPrimitiveRankIndex434 Q → ℂ := fun r =>
    parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
      (sourceOriginalProbeCellA434 m P V nu hA)
      (sourceOriginalProbeCellB434 m P V nu hB)
      r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu vals)
      (sourceOriginalProbeDB434 m nu vals) (nu.1.card+nu.2.card)
  let U : ParityPrimitiveRankIndex434 Q → ℕ → ℂ := fun r =>
    parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) F t1 tw true
  let W : ParityPrimitiveRankIndex434 Q → ℕ → ℂ := fun r =>
    parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) G t2 tw false
  let a : ParityPrimitiveRankIndex434 Q → ℝ → ℂ := fun r s =>
    parityScaleMellinFactor434 Z c s * parityMellinFourierPair434 N
      (fun n => eta ((n : ℝ)/(Z*Hp r))*U r n)
      (fun n => eta ((n : ℝ)/(Z*Hp r))*W r n) ((2*k)*(c : ℤ)) s
  have hc : 0 < c := parity_actual_probe_aux_positive434 L hS J m hmJ nu aux
  have hSplit : c = sourceOriginalProbeDA434 m nu vals * sourceOriginalProbeDB434 m nu vals :=
    parity_actual_probe_aux_product_split434 L J m hmJ nu hnu aux
  have hPos : 0 < sourceOriginalProbeDA434 m nu vals ∧ 0 < sourceOriginalProbeDB434 m nu vals := by
    have hprod := hc
    rw [hSplit] at hprod
    constructor
    · by_contra hn
      have hz : sourceOriginalProbeDA434 m nu vals = 0 := by omega
      rw [hz,zero_mul] at hprod
      omega
    · by_contra hn
      have hz : sourceOriginalProbeDB434 m nu vals = 0 := by omega
      rw [hz,mul_zero] at hprod
      omega
  have hInt (r : ParityPrimitiveRankIndex434 Q) :
      Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s * a r s) :=
    (parity_finite_cutoff_mellin_fourier434 N hN
      (fun n => eta ((n : ℝ)/(Z*Hp r))*U r n)
      (fun n => eta ((n : ℝ)/(Z*Hp r))*W r n)
      Z c ((2*k)*(c : ℤ)) hZ hc psi hSmooth hSupport).1
  have hValue (r : ParityPrimitiveRankIndex434 Q) :
      b r * parityActualRankFourierPair434 L hS J m hmJ nu hA hB r
        (1/2) N Z c k F G t1 t2 tw psi =
      b r * ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s * a r s := by
    by_cases hb : b r = 0
    · simp only [hb,zero_mul]
    · have hCells : sourceOriginalLiteralLogCell434 hA r.1.1 (sourceOriginalProbeDA434 m nu vals) ∧
          sourceOriginalLiteralLogCell434 hB r.2.1 (sourceOriginalProbeDB434 m nu vals) := by
        by_contra hh
        have hg := parity_rank_scalar_gated_test434 hA hB r.1.1 r.2.1
          (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
          r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu vals) (sourceOriginalProbeDB434 m nu vals)
          (nu.1.card+nu.2.card) 1
        have hz : b r = 0 := by simpa only [b,if_neg hh,mul_one,mul_zero] using hg
        exact hb hz
      have hScale := parity_literal_cells_product_scale434 hA hB r.1.1 r.2.1
        (sourceOriginalProbeDA434 m nu vals) (sourceOriginalProbeDB434 m nu vals)
        hPos.1 hPos.2 hA1 hB1 hCells.1 hCells.2
      rw [← hSplit] at hScale
      have hLoc := parity_cell_localized_cutoff_mellin434 N hN (U r) (W r) Z (Hp r) c k
        hZ (by dsimp [Hp]; positivity) hScale.1 hScale.2 hSmall
        psi eta hSmooth hSupport hEta
      exact congrArg (fun z : ℂ => b r*z) hLoc.2
  have hSum := parity_finite_mellin_weighted_sum434 R (fun s => (𝓕 f : 𝓢(ℝ,ℂ)) s)
    b a (fun r hr => hInt r)
  have hFourier := parity_actual_weighted_rank_main_fourier434 L hS J m hmJ nu
    Q hA hB xi zeta Z k N F G t1 t2 tw psi aux
  simp only [b645ActualBand434,parityActualFreeCollisionAux434] at hFourier
  simp_rw [parity_full_rank_indices434,parity_full_rank_scalar434] at hFourier
  by_cases hk : (2*k) = 0
  · constructor
    · simp only [parityActualCellRankMellinAtAux434,hk,ite_true,mul_zero]
      exact integrable_zero _ _ _
    · rw [hFourier]
      simp only [parityActualCellRankMellinAtAux434,hk,ite_true,mul_zero,integral_zero]
  · have hForm (s : ℝ) : sourceOriginalPureMellinPhase434 zeta c *
        ((𝓕 f : 𝓢(ℝ,ℂ)) s * ∑ r ∈ R, b r*a r s) =
        (𝓕 f : 𝓢(ℝ,ℂ)) s * parityActualCellRankMellinAtAux434 L hS J m hmJ nu
          Q hA hB xi zeta Z k N F G t1 t2 tw eta aux s := by
      simp only [parityActualCellRankMellinAtAux434,hk,ite_false]
      change _ = (𝓕 f : 𝓢(ℝ,ℂ)) s *
        (sourceOriginalPureMellinPhase434 zeta c * ∑ r ∈ R, b r*a r s)
      ring
    refine ⟨(hSum.1.const_mul _).congr (Filter.Eventually.of_forall hForm),?_⟩
    rw [hFourier,if_neg hk]
    change sourceOriginalPureMellinPhase434 zeta c *
      (∑ r ∈ R, b r*parityActualRankFourierPair434 L hS J m hmJ nu hA hB r
        (1/2) N Z c k F G t1 t2 tw psi) = _
    calc
      _ = sourceOriginalPureMellinPhase434 zeta c *
          (∑ r ∈ R, b r*∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s*a r s) :=
        congrArg (fun z : ℂ => sourceOriginalPureMellinPhase434 zeta c*z)
          (Finset.sum_congr rfl (fun r hr => hValue r))
      _ = sourceOriginalPureMellinPhase434 zeta c *
          (∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s*∑ r ∈ R, b r*a r s) :=
        congrArg (fun z : ℂ => sourceOriginalPureMellinPhase434 zeta c*z) hSum.2
      _ = ∫ s : ℝ, sourceOriginalPureMellinPhase434 zeta c *
          ((𝓕 f : 𝓢(ℝ,ℂ)) s*∑ r ∈ R, b r*a r s) := (integral_const_mul _ _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hForm)
end Green64Analytic.Parity

end

end

/-! ## ActualCellRankMellinFamily -/

section

open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 28000

/-- The genuine actual common-cell localized Mellin/Fourier family amplitude. It is independent
of the original cutoff psi, and each endpoint test is also independent of
the auxiliary draw. Every actual probability atom, both cell masses and
all c-dependent scalar phases and signed shifts are retained. -/
def parityActualCellRankMellinFamily434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (eta : ℝ → ℂ) (s : ℝ) : ℂ :=
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
    ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ) *
      parityActualCellRankMellinAtAux434 L hS J m hmJ nu.val Q h h xi (-xi3) Z k N
        F G (-(rho+xi3)) (-rho) tw eta aux s

/-- Exact common-cell localized Mellin insertion into the independently defined full actual
rank-main family, with integrability proved for the genuine finite sums.
No cell mass is replaced by one; the original auxiliary law is not
normalized away. The positive original B654 carrier is unchanged. -/
theorem parity_actual_cell_rank_main_family_mellin434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (hZ : 0 < Z) (h1 : h ≤ 1)
    (hSmall : |2*(k : ℝ)/Z| ≤ (128*Real.exp 2)⁻¹)
    (F G : PrimeSlotCore) (tw : Bool) (psi eta : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (hEta : ∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u = 1) :
    let f := parityOriginalLogCutoff434 psi hSmooth hSupport
    Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s *
      parityActualCellRankMellinFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s) ∧
    parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw psi =
      ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s *
        parityActualCellRankMellinFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s := by
  dsimp only
  let f := parityOriginalLogCutoff434 psi hSmooth hSupport
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let Fam := sourceOriginalTwoBlockProbePatterns434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m
  let mu := fun (nu : ↥Fam) (aux : ParityActualProbeAux434 L J m hmJ nu.val) =>
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ)
  let a := fun (nu : ↥Fam) (aux : ParityActualProbeAux434 L J m hmJ nu.val) (s : ℝ) =>
    parityActualCellRankMellinAtAux434 L hS J m hmJ nu.val Q h h xi (-xi3) Z k N
      F G (-(rho+xi3)) (-rho) tw eta aux s
  have hN : ∀ n ∈ N, 0 < n := by
    intro n hn
    exact ((parity_positive_natural_positions_mem434 _ n).mp hn).1
  have hEach (nu : ↥Fam) (aux : ParityActualProbeAux434 L J m hmJ nu.val) :=
    parity_actual_weighted_cell_rank_main_mellin434 L hS J m hmJ nu.val nu.property Q h h xi (-xi3) Z k N
      hN hZ h1 h1 hSmall F G (-(rho+xi3)) (-rho) tw psi eta hSmooth hSupport hEta aux
  have hInner (nu : ↥Fam) :=
    parity_finite_mellin_weighted_sum434 Finset.univ (fun s => (𝓕 f : 𝓢(ℝ,ℂ)) s)
      (mu nu) (a nu) (fun aux haux => (hEach nu aux).1)
  have hOuter := parity_finite_mellin_weighted_sum434 (Finset.univ : Finset ↥Fam)
    (fun s => (𝓕 f : 𝓢(ℝ,ℂ)) s) (fun _ => 1)
    (fun nu s => ∑ aux, mu nu aux * a nu aux s) (fun nu hnu => (hInner nu).1)
  constructor
  · change Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s * ∑ nu : ↥Fam,
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val, mu nu aux * a nu aux s)
    simpa only [one_mul] using hOuter.1
  · unfold parityActualWeightedRankMainFamily434
    dsimp only
    change (∑ nu : ↥Fam, ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
      mu nu aux * _) = ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s * ∑ nu : ↥Fam,
        ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val, mu nu aux * a nu aux s
    calc
      _ = ∑ nu : ↥Fam, ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
          mu nu aux * ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s * a nu aux s := by
        apply Finset.sum_congr rfl
        intro nu hnu
        apply Finset.sum_congr rfl
        intro aux haux
        exact congrArg (fun z : ℂ => mu nu aux*z) (hEach nu aux).2
      _ = ∑ nu : ↥Fam, ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s *
          ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val, mu nu aux*a nu aux s :=
        Finset.sum_congr rfl (fun nu hnu => (hInner nu).2)
      _ = _ := by simpa only [one_mul] using hOuter.2

/-- Uniform actual-family localization under only the original Z window
and |k| bound. The exact small signed-shift inequality is proved internally.
This is uniform over any fixed cutoff equal to one on the constructed
common interval, allowing the SAME cutoff returned by the genuine B629
construction to be used. No smallness of the family is a premise. -/
theorem parity_eventually_actual_cell_rank_main_family_mellin434
    (CZ Ck : ℝ) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ L ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi rho xi3 Z : ℝ) (k : ℤ),
        h ≤ 1 → Real.exp L*L^(-CZ) ≤ Z → |(k : ℝ)| ≤ L^Ck →
      ∀ (F G : PrimeSlotCore) (tw : Bool) (psi eta : ℝ → ℂ)
        (hSmooth : ContDiff ℝ ∞ psi)
        (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64),
        (∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u = 1) →
        let f := parityOriginalLogCutoff434 psi hSmooth hSupport
        Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s *
          parityActualCellRankMellinFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s) ∧
        parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw psi =
          ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s *
            parityActualCellRankMellinFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s := by
  filter_upwards [parity_eventually_rank_cell_signed_shift434 CZ Ck hCZ hCk] with L hLarge
  refine ⟨hLarge.1,?_⟩
  intro hS J m hmJ Q h xi rho xi3 Z k hh hZlo hk F G tw psi eta hSmooth hSupport hEta
  have hZ := hLarge.2 Z k hZlo hk
  exact parity_actual_cell_rank_main_family_mellin434 L hS J m hmJ Q h xi rho xi3 Ck Z k
    hZ.1 hh hZ.2 F G tw psi eta hSmooth hSupport hEta
end Green64Analytic.Parity

end

end

/-! ## CellMellinEndpoint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 22000

/-- The exact first Mellin twist shifts only the native outer endpoint
frequency. All original prime-slot arithmetic, complete marks, signs and
rank-row factors stay unchanged. The 2*pi factor is retained literally. -/
theorem parity_actual_rank_endpoint_mellin_shift434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q) (q : ℝ)
    (F : PrimeSlotCore) (t s : ℝ) (tw side : Bool) (n : ℕ) (hn : 0 < n) :
    star (sourceOriginalPureMellinPhase434 (2*Real.pi*s) n) *
      parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F t tw side n =
      parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F (t-2*Real.pi*s) tw side n := by
  rw [← parity_native_imaginary_pure_mellin434 n hn (2*Real.pi*s),
    ← b633_imaginary_power_conjugate434]
  have ht : imaginaryPower n (t-2*Real.pi*s) =
      imaginaryPower n t * imaginaryPower n (-(2*Real.pi*s)) := by
    rw [sub_eq_add_neg,b633_imaginary_power_add434 n hn]
  unfold parityActualRankEndpoint434 parityHarmonicEndpointArithmetic434
  dsimp only
  rw [ht]
  ring

/-- The actual first localized Mellin endpoint is exactly Y^{-1} times
the same full endpoint with frequency t-2*pi*s and physical cutoff
eta(u)/u. This identifies the genuine harmonic normalization required by
B629. The formula also holds at n=0, where both harmonic factors vanish. -/
theorem parity_actual_cell_mellin_first_endpoint434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q) (q : ℝ)
    (F : PrimeSlotCore) (t s Y : ℝ) (hY : 0 < Y) (tw side : Bool)
    (eta : ℝ → ℂ) (n : ℕ) :
    parityMellinFourierFirst434 s
      (fun w => eta ((w : ℝ)/Y)*parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F t tw side w) n =
      (Y : ℂ)⁻¹ * ((eta ((n : ℝ)/Y)/(((n : ℝ)/Y : ℝ) : ℂ)) *
        parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F (t-2*Real.pi*s) tw side n) := by
  by_cases hn0 : n = 0
  · subst n
    simp only [parityMellinFourierFirst434,Nat.cast_zero,zero_div,inv_zero,mul_zero,
      star_zero,zero_mul,div_zero,Complex.ofReal_zero]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
    have hStar : star ((n : ℂ)⁻¹) = (n : ℂ)⁻¹ := by simp
    unfold parityMellinFourierFirst434
    rw [star_mul,hStar]
    calc
      _ = eta ((n : ℝ)/Y)*(n : ℂ)⁻¹ *
          (star (sourceOriginalPureMellinPhase434 (2*Real.pi*s) n) *
            parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F t tw side n) := by ring
      _ = eta ((n : ℝ)/Y)*(n : ℂ)⁻¹ *
          parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F (t-2*Real.pi*s) tw side n := by
        rw [parity_actual_rank_endpoint_mellin_shift434 L hS J m hmJ nu hA hB r q F t s tw side n hn]
      _ = _ := by
        rw [Complex.ofReal_div,Complex.ofReal_natCast]
        field_simp [hYc,hnc]
end Green64Analytic.Parity

end

end

/-! ## HarmonicArcEnergy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 22000

/-- Exact finite Fourier linearity for a literal constant, retaining the
complete coefficient sequence and original finite natural carrier. -/
theorem parity_nat_fourier_const_mul434 (S : Finset ℕ) (a : ℂ) (F : ℕ → ℂ) :
    sourceNatFourierPoly S (fun n=>a*F n)=a • sourceNatFourierPoly S F := by
  unfold sourceNatFourierPoly sourceCircleFourierPoly
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [mul_smul]

/-- The genuine harmonic first-endpoint scalar contributes exactly
Y^{-2} to its real arc energy. No norm or energy bound is assumed. -/
theorem parity_harmonic_arc_energy_scale434 (Y R : ℝ) (hY : 0<Y) (f : ℝ → ℂ) :
    (∫ theta in {theta : ℝ | |theta|≤R},‖(Y : ℂ)⁻¹*f theta‖^2)=
      (Y⁻¹)^2*(∫ theta in {theta : ℝ | |theta|≤R},‖f theta‖^2) := by
  have hscalar : ‖(Y : ℂ)⁻¹‖^2=(Y⁻¹)^2 := by
    simp [norm_inv,abs_of_pos hY]
  simp_rw [norm_mul,mul_pow,hscalar]
  rw [integral_const_mul]

/-- Balanced real Cauchy estimate on an actual compact real arc. The
first energy is B/Y and the second B*Y. The proof integrates the exact
nonnegative square (Y*norm f-norm g)^2, so no square-root or exceptional
zero convention hides a loss. Both integrability obligations follow
from continuity on the finite arc. -/
theorem parity_harmonic_arc_cauchy434
    (Y B R : ℝ) (hY : 0<Y) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hFirst : (∫ theta in {theta : ℝ | |theta|≤R},‖f theta‖^2)≤B/Y)
    (hSecond : (∫ theta in {theta : ℝ | |theta|≤R},‖g theta‖^2)≤B*Y) :
    (∫ theta in {theta : ℝ | |theta|≤R},‖star (f theta)*g theta‖)≤B := by
  have hset : {theta : ℝ | |theta|≤R}=Set.Icc (-R) R := by
    ext theta
    change |theta|≤R ↔ -R≤theta ∧ theta≤R
    exact abs_le
  rw [hset] at hFirst hSecond ⊢
  simp only [norm_mul,norm_star]
  have hfi : IntegrableOn (fun theta=>‖f theta‖^2) (Set.Icc (-R) R) :=
    (hf.norm.pow 2).integrableOn_Icc
  have hgi : IntegrableOn (fun theta=>‖g theta‖^2) (Set.Icc (-R) R) :=
    (hg.norm.pow 2).integrableOn_Icc
  have hprod : IntegrableOn (fun theta=>‖f theta‖*‖g theta‖) (Set.Icc (-R) R) :=
    (hf.norm.mul hg.norm).integrableOn_Icc
  have hpoint (theta : ℝ) :
      (2*Y)*(‖f theta‖*‖g theta‖)≤Y^2*‖f theta‖^2+‖g theta‖^2 := by
    nlinarith [sq_nonneg (Y*‖f theta‖-‖g theta‖)]
  have hi:=integral_mono (hprod.const_mul (2*Y)) ((hfi.const_mul (Y^2)).add hgi) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (hfi.const_mul (Y^2)) hgi,integral_const_mul] at hi
  have hbudget : Y^2*(B/Y)+B*Y=(2*Y)*B := by
    field_simp [hY.ne']
    <;> ring
  have hupper :
      Y^2*(∫ theta in Set.Icc (-R) R,‖f theta‖^2)+
        (∫ theta in Set.Icc (-R) R,‖g theta‖^2)≤(2*Y)*B := by
    calc
      _≤Y^2*(B/Y)+B*Y := add_le_add (mul_le_mul_of_nonneg_left hFirst (sq_nonneg Y)) hSecond
      _=(2*Y)*B := hbudget
  exact (mul_le_mul_iff_right₀ (by positivity : 0<2*Y)).mp (hi.trans hupper)
end Green64Analytic.Parity

end

end

/-! ## HarmonicRankArc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 26000

/-- Exact first-Mellin Fourier carrier transport using the already
proved original carrier theorem. The genuine Mellin/harmonic weight is
kept inside the coefficient and no source positions are discarded. -/
theorem parity_actual_cell_mellin_first_carrier434
    (J : ℕ) (Ck L : ℝ) (hL : 0<L) (A Y : ℝ) (hA : 1≤A) (hY : 0<Y)
    (eta : ℝ → ℂ) (hSupport : ∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A)
    (hCap : (⌈A*Y⌉₊ : ℝ)≤Real.exp (2*L)) (U : ℕ → ℂ) (s : ℝ) :
    sourceNatFourierPoly
      (parityPositiveNaturalPositions434 (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)))
      (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n))=
    sourceNatFourierPoly (Finset.Icc 1 ⌈A*Y⌉₊)
      (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n)) := by
  have hfactor (n : ℕ) :
      parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n) n=
        eta ((n : ℝ)/Y)*parityMellinFourierFirst434 s U n := by
    unfold parityMellinFourierFirst434
    ring
  rw [funext hfactor]
  exact parity_actual_cell_fourier_carrier434 J Ck L hL A Y hA hY eta hSupport hCap
    (parityMellinFourierFirst434 s U)

/-- Two genuine actual B633 Mellin endpoint arc energies on the original
positive harmonic carrier, and their balanced real arc-product bound.
The first endpoint retains the literal harmonic inverse, so its energy
has scale 1/Y while the second has scale Y. Auxiliary cell admissibility
is explicit; the coupled auxiliary multiplier is not normalized away. -/
def ParityB633ActualHarmonicRankCellArc434
    (cfg : SourceComparisonFixed434) (eta : ℝ → ℂ) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma targetSaving Karc Cfreq Ftail : ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma s : ℝ),
    |rho|≤L^Cfreq → |xi1|≤L^Cfreq → |xi2|≤L^Cfreq → |xi3|≤L^Cfreq →
    |sigma|≤L^Cfreq → |s|≤L^Ftail →
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 20 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)) (tw : Bool),
  let Hp:=Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*
      parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 E (-(rho+xi3)) tw true n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 G (-rho) tw false n)
  ∀ (den h : ℕ),0<den → (den : ℝ)≤L^cfg.cm →
    let angle:=fun theta : ℝ=>(((h : ℝ)/(den : ℝ)+theta : ℝ) : AddCircle (1 : ℝ))
    (∫ theta in {theta : ℝ | |theta|≤L^cfg.Carc/Hp},‖first (angle theta)‖^2)≤
      (Karc/Y)*L^(-targetSaving) ∧
    (∫ theta in {theta : ℝ | |theta|≤L^cfg.Carc/Hp},‖second (angle theta)‖^2)≤
      Karc*Y*L^(-targetSaving) ∧
    (∫ theta in {theta : ℝ | |theta|≤L^cfg.Carc/Hp},
      ‖star (first (angle theta))*second (angle theta)‖)≤Karc*L^(-targetSaving)

/-- Construct the same physical cutoff and actual B633 data before L,
transport both exact finite Fourier sequences to the original carrier,
and prove their first/second energies and harmonic arc-product saving.
The cap condition and every transformed-frequency gate are derived; no
Main smallness, major-circle assertion or energy hypothesis is assumed. -/
theorem parity_eventually_B633_actual_harmonic_rank_arc434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck beta gamma targetSaving Cfreq Ftail : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hbeta : 0<beta) (hgamma : 0<gamma) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    ∃ (A : ℝ) (hA : 64≤A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖≤1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0≤K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualHarmonicRankCellArc434 cfg eta L jQ mmax CZ Ck S beta gamma
              targetSaving Karc Cfreq Ftail := by
  dsimp only
  let s0:=⌈Cfreq+1⌉₊
  let s1:=⌈Cfreq⌉₊
  let vexp:=⌈max Cfreq Ftail+1⌉₊
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,hArc⟩ :=
    parity_eventually_B633_actual_rank_marked_arc434 jQ mmax cm CZ Carc Cchi Ck beta gamma
      targetSaving Cfreq Ftail hCZ hCk hcm hCarc hCchi hCchiPos hbeta hgamma
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,?_⟩
  let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  have hCarc0 : 0≤Carc:=(Nat.cast_nonneg cm).trans hCarc
  have hScales:=Filter.eventually_all.mpr
    (fun m : Fin (mmax+1)=>parity_eventually_enlarged_comparison_cell_scales434
      A CZ Carc m.val hA hCZ hCarc0)
  filter_upwards [hArc,hScales] with L hArcL hscale
  refine ⟨hArcL.1,hArcL.2.1,?_⟩
  unfold ParityB633ActualHarmonicRankCellArc434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
    hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
    Qcomp aux hAux hAuxA hAuxB ca cb tw
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let M:=Finset.Icc 1 ⌈A*Y⌉₊
  let U:=fun n : ℕ=>parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
    E (-(rho+xi3)) tw true n
  let V:=fun n : ℕ=>parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
    G (-rho) tw false n
  let Ub:=fun n : ℕ=>(eta ((n : ℝ)/Y)/(((n : ℝ)/Y : ℝ) : ℂ))*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
      E (-(rho+xi3)-2*Real.pi*s) tw true n
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*V n)
  let firstBase:=sourceNatFourierPoly M Ub
  let secondBase:=sourceNatFourierPoly M (fun n : ℕ=>eta ((n : ℝ)/Y)*V n)
  have hgeo:=(hscale ⟨m,by omega⟩).2 Z hZlo hZhi nu hnu hAcell hB xi
    hhA hhB hA1 hB1 ja jb ha hb
  have hL2 : 2≤L:=(hscale ⟨m,by omega⟩).1
  have hLp : 0<L:=by linarith
  have hZ : 0<Z:=(mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hY : 0<Y:=by dsimp [Y,Hp]; positivity
  have hAs : 1≤A:=by linarith
  have hCap : (⌈A*Y⌉₊ : ℝ)≤Real.exp (2*L):=by
    calc
      _≤(Real.exp L)^2:=hgeo.2.1
      _=Real.exp (2*L):=by rw [pow_two,←Real.exp_add];congr 1;ring
  have hFirstScale : first=(Y : ℂ)⁻¹ • firstBase:=by
    unfold first
    rw [parity_actual_cell_mellin_first_carrier434 J Ck L hLp A Y hAs hY eta hSupp hCap U s]
    have heq : parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n)=
        (fun n : ℕ=>(Y : ℂ)⁻¹*Ub n):=by
      funext n
      exact parity_actual_cell_mellin_first_endpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
        E (-(rho+xi3)) s Y hY tw true eta n
    rw [heq]
    exact parity_nat_fourier_const_mul434 M ((Y : ℂ)⁻¹) Ub
  have hSecondCarrier : second=secondBase:=
    parity_actual_cell_fourier_carrier434 J Ck L hLp A Y hAs hY eta hSupp hCap V
  dsimp only
  intro den h hden hdenCap
  let angle:=fun theta : ℝ=>(((h : ℝ)/(den : ℝ)+theta : ℝ) : AddCircle (1 : ℝ))
  let R:=L^cfg.Carc/Hp
  have hFirstBase : (∫ theta in {theta : ℝ | |theta|≤R},‖firstBase (angle theta)‖^2)≤
      Karc*Y*L^(-targetSaving):=
    hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
      ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
      hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw true den h hden hdenCap
  have hSecondBase : (∫ theta in {theta : ℝ | |theta|≤R},‖secondBase (angle theta)‖^2)≤
      Karc*Y*L^(-targetSaving):=
    hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
      ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
      hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw false den h hden hdenCap
  have hFirstValue (theta : ℝ) : first (angle theta)=(Y : ℂ)⁻¹*firstBase (angle theta):=by
    rw [hFirstScale]
    rfl
  have hFirst : (∫ theta in {theta : ℝ | |theta|≤R},‖first (angle theta)‖^2)≤
      (Karc/Y)*L^(-targetSaving):=by
    calc
      _=(Y⁻¹)^2*(∫ theta in {theta : ℝ | |theta|≤R},‖firstBase (angle theta)‖^2):=by
        simp_rw [hFirstValue]
        exact parity_harmonic_arc_energy_scale434 Y R hY (fun theta=>firstBase (angle theta))
      _≤(Y⁻¹)^2*(Karc*Y*L^(-targetSaving)):=
        mul_le_mul_of_nonneg_left hFirstBase (sq_nonneg _)
      _=(Karc/Y)*L^(-targetSaving):=by field_simp [hY.ne']
  have hSecond : (∫ theta in {theta : ℝ | |theta|≤R},‖second (angle theta)‖^2)≤
      Karc*Y*L^(-targetSaving):=by simpa only [hSecondCarrier] using hSecondBase
  refine ⟨hFirst,hSecond,?_⟩
  have hangle : Continuous angle:=by fun_prop
  have hfirst : Continuous (fun theta=>first (angle theta)):=first.continuous.comp hangle
  have hsecond : Continuous (fun theta=>second (angle theta)):=second.continuous.comp hangle
  apply parity_harmonic_arc_cauchy434 Y (Karc*L^(-targetSaving)) R hY
    (fun theta=>first (angle theta)) (fun theta=>second (angle theta)) hfirst hsecond
  · convert hFirst using 1 <;> ring
  · convert hSecond using 1 <;> ring
end Green64Analytic.Parity

end

end

/-! ## HarmonicCircleMajor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 26000

/-- A strengthened instance of the already certified cell-scale bound
gives a STRICT half-period radius. No circle injectivity is assumed. -/
theorem parity_arc_radius_half_of_power_band434
    (L H C : ℝ) (hL : 2≤L) (hH : 0<H)
    (hBand : 2≤H/L^(C+1)) :
    0≤L^C/H ∧ L^C/H<(1/2:ℝ) := by
  have hLp : 0<L:=by linarith
  have hP : 0<L^C:=Real.rpow_pos_of_pos hLp _
  have hP1 : 0<L^(C+1):=Real.rpow_pos_of_pos hLp _
  have h := (le_div_iff₀ hP1).mp hBand
  rw [Real.rpow_add hLp,Real.rpow_one] at h
  refine ⟨div_nonneg hP.le hH.le,?_⟩
  apply (div_lt_iff₀ hH).mpr
  nlinarith [mul_le_mul_of_nonneg_right hL hP.le]

/-- The complete rational major union inherits the REAL arc-product
bound. Apply the certified circle-energy transport to the continuous
square root of norm(F)*norm(G), whose squared norm is exactly the
desired product norm. Both overlap and period wrapping are retained. -/
theorem parity_circle_rational_product_saving434
    (Q : ℕ) (F G : C(AddCircle (1:ℝ),ℂ))
    (Hprime Carc Cexp A K L : ℝ)
    (hL : 1≤L) (hC : 0≤Cexp) (hK : 0≤K)
    (hQ : (Q:ℝ)≤L^Cexp) (hr : 0≤L^Carc/Hprime)
    (hrhalf : L^Carc/Hprime<(1/2:ℝ))
    (hArc : ∀ den h : ℕ,0<den → den≤Q → h<den →
      (∫ beta in {beta : ℝ | |beta|≤L^Carc/Hprime},
        ‖star (F (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ)))*
          G (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖)≤K*L^(-A)) :
    (∫ theta in sourceCircleRationalArcs434 Q (L^Carc/Hprime),
      ‖star (F theta)*G theta‖ ∂AddCircle.haarAddCircle)≤2*K*L^(2*Cexp-A) := by
  let W : C(AddCircle (1:ℝ),ℂ):=
    ⟨fun theta=>((Real.sqrt (‖F theta‖*‖G theta‖):ℝ):ℂ),
      Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (F.continuous.norm.mul G.continuous.norm))⟩
  have hW (theta : AddCircle (1:ℝ)) : ‖W theta‖^2=‖star (F theta)*G theta‖:=by
    change ‖((Real.sqrt (‖F theta‖*‖G theta‖):ℝ):ℂ)‖^2=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _)),norm_mul,norm_star]
  have hBound:=source_circle_major_arc_saving434 Q W Hprime Carc Cexp A K L 1
    hL hC hK (by norm_num) hQ hr hrhalf (fun den h hd hdQ hhd=>by
      simp_rw [hW]
      simpa only [mul_one] using hArc den h hd hdQ hhd)
  simp_rw [hW] at hBound
  simpa only [mul_one] using hBound

/-- Actual first/second harmonic endpoint energies on the COMPLETE
rational major-circle union. The original physical carrier, same eta,
all marks and the original actual auxiliary witness remain explicit.
Overlaps and wrapping arcs are counted by the certified finite-union
inequality, with the exact denominator loss 2*cm. -/
def ParityB633ActualHarmonicRankCellCircleMajor434
    (cfg : SourceComparisonFixed434) (eta : ℝ → ℂ) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma targetSaving Karc Cfreq Ftail : ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma s : ℝ),
    |rho|≤L^Cfreq → |xi1|≤L^Cfreq → |xi2|≤L^Cfreq → |xi3|≤L^Cfreq →
    |sigma|≤L^Cfreq → |s|≤L^Ftail →
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 20 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)) (tw : Bool),
  let Hp:=Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*
      parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 E (-(rho+xi3)) tw true n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 G (-rho) tw false n)
  ∀ Qmajor : ℕ,(Qmajor : ℝ)≤L^cfg.cm →
    let major:=sourceCircleRationalArcs434 Qmajor (L^cfg.Carc/Hp)
    (∫ theta in major,‖first theta‖^2 ∂AddCircle.haarAddCircle)≤
      (2*Karc/Y)*L^(2*(cfg.cm : ℝ)-targetSaving) ∧
    (∫ theta in major,‖second theta‖^2 ∂AddCircle.haarAddCircle)≤
      2*Karc*Y*L^(2*(cfg.cm : ℝ)-targetSaving) ∧
    (∫ theta in major,‖star (first theta)*second theta‖ ∂AddCircle.haarAddCircle)≤
      2*Karc*L^(2*(cfg.cm : ℝ)-targetSaving)

/-- Construct the same physical cutoff and actual operator estimates
before L, derive the strict circle radius from the certified cell geometry
at Carc+1, and integrate both actual rational-arc energy estimates over
their whole measurable major union. No major energy or small-Main
hypothesis is assumed; the exact cost is2*cm in the requested exponent. -/
theorem parity_eventually_B633_actual_harmonic_circle_major434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck beta gamma targetSaving Cfreq Ftail : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hbeta : 0<beta) (hgamma : 0<gamma) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    ∃ (A : ℝ) (hA : 64≤A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖≤1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0≤K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualHarmonicRankCellCircleMajor434 cfg eta L jQ mmax CZ Ck S beta gamma
              targetSaving Karc Cfreq Ftail := by
  dsimp only
  let s0:=⌈Cfreq+1⌉₊
  let s1:=⌈Cfreq⌉₊
  let vexp:=⌈max Cfreq Ftail+1⌉₊
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,hArc⟩ :=
    parity_eventually_B633_actual_harmonic_rank_arc434 jQ mmax cm CZ Carc Cchi Ck beta gamma
      targetSaving Cfreq Ftail hCZ hCk hcm hCarc hCchi hCchiPos hbeta hgamma
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,?_⟩
  let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  have hCarc0 : 0≤Carc:=(Nat.cast_nonneg cm).trans hCarc
  have hScales:=Filter.eventually_all.mpr
    (fun m : Fin (mmax+1)=>parity_eventually_full_comparison_cell_scales434
      CZ (Carc+1) m.val hCZ (by linarith))
  filter_upwards [hArc,hScales] with L hArcL hscale
  refine ⟨hArcL.1,hArcL.2.1,?_⟩
  unfold ParityB633ActualHarmonicRankCellCircleMajor434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
    hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
    Qcomp aux hAux hAuxA hAuxB ca cb tw
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*
      parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 E (-(rho+xi3)) tw true n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 G (-rho) tw false n)
  have hgeo:=(hscale ⟨m,by omega⟩).2 Z hZlo hZhi nu hnu hAcell hB xi
    hhA hhB hA1 hB1 ja jb ha hb
  have hL2 : 2≤L:=(hscale ⟨m,by omega⟩).1
  have hLp : 0<L:=by linarith
  have hL1 : 1≤L:=by linarith
  have hHp : 0<Hp:=by dsimp [Hp];positivity
  have hY : 0<Y:=mul_pos hgeo.1 hHp
  have hBand : 2≤Hp/L^(Carc+1):=hgeo.2.2.2.2.2.2.2.1
  have hRad:=parity_arc_radius_half_of_power_band434 L Hp Carc hL2 hHp hBand
  dsimp only
  intro Qmajor hQ
  let major:=sourceCircleRationalArcs434 Qmajor (L^cfg.Carc/Hp)
  have hQreal : (Qmajor : ℝ)≤L^(cfg.cm : ℝ):=by
    simpa only [Real.rpow_natCast] using hQ
  have hEach (den h : ℕ) (hd : 0<den) (hdQ : den≤Qmajor) :=
    hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
      ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
      hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw den h hd
      ((show (den : ℝ)≤Qmajor by exact_mod_cast hdQ).trans hQ)
  change (∫ theta in major,‖first theta‖^2 ∂AddCircle.haarAddCircle)≤
      (2*Karc/Y)*L^(2*(cfg.cm : ℝ)-targetSaving) ∧
    (∫ theta in major,‖second theta‖^2 ∂AddCircle.haarAddCircle)≤
      2*Karc*Y*L^(2*(cfg.cm : ℝ)-targetSaving) ∧
    (∫ theta in major,‖star (first theta)*second theta‖ ∂AddCircle.haarAddCircle)≤
      2*Karc*L^(2*(cfg.cm : ℝ)-targetSaving)
  refine ⟨?_,?_,?_⟩
  · have hFirst := source_circle_major_arc_saving434 Qmajor first Hp cfg.Carc
      (cfg.cm : ℝ) targetSaving Karc L Y⁻¹ hL1 (Nat.cast_nonneg _) hKarc.le
      (inv_nonneg.mpr hY.le) hQreal hRad.1 hRad.2 (fun den h hd hdQ hhd => by
        have hi := (hEach den h hd hdQ).1
        change (∫ theta in {theta : ℝ | |theta|≤L^cfg.Carc/Hp},
          ‖first (((h : ℝ)/(den : ℝ)+theta : ℝ) : AddCircle (1 : ℝ))‖^2)≤
          (Karc/Y)*L^(-targetSaving) at hi
        simpa only [div_eq_mul_inv] using hi)
    simpa only [major,div_eq_mul_inv,mul_assoc] using hFirst
  · exact source_circle_major_arc_saving434 Qmajor second Hp cfg.Carc
      (cfg.cm : ℝ) targetSaving Karc L Y hL1 (Nat.cast_nonneg _) hKarc.le hY.le
      hQreal hRad.1 hRad.2 (fun den h hd hdQ hhd => (hEach den h hd hdQ).2.1)
  · exact parity_circle_rational_product_saving434 Qmajor first second Hp cfg.Carc
      (cfg.cm : ℝ) targetSaving Karc L hL1 (Nat.cast_nonneg _) hKarc.le
      hQreal hRad.1 hRad.2 (fun den h hd hdQ hhd => (hEach den h hd hdQ).2.2)
end Green64Analytic.Parity

end

end

/-! ## GlobalFreeFrequency -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 22000

/-- The same actual common cutoff has a fixed sup bound after division
by u. The lower support endpoint, not a supplied derivative estimate,
proves this bound. Both zero and nonzero cutoff values are handled. -/
theorem parity_common_cutoff_inverse_bound434
    (A : ℝ) (hA : 1≤A) (eta : ℝ → ℂ)
    (hSupport : ∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A)
    (hNorm : ∀ u : ℝ,‖eta u‖≤1) :
    (∀ u : ℝ,‖eta u/(u : ℂ)‖≤A) ∧
    (∀ u : ℝ,eta u/(u : ℂ)≠0 → 1/A≤u ∧ u≤A) := by
  have hAp : 0<A:=by linarith
  constructor
  · intro u
    by_cases hz : eta u=0
    · simp only [hz,zero_div,norm_zero]
      linarith
    · have hs:=hSupport u hz
      have hu : 0<u:=(one_div_pos.mpr hAp).trans_le hs.1
      have hAu : 1≤u*A:=(div_le_iff₀ hAp).mp hs.1
      have hb : ‖eta u‖≤A*u:=(hNorm u).trans (by nlinarith)
      simpa only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu] using
        (div_le_iff₀ hu).mpr hb
  · intro u hu
    exact hSupport u (by intro hz;apply hu;simp only [hz,zero_div])

/-- Genuine original full global marked budget with completely free
core and outer Mellin frequencies. The data supplies its actual group,
mark, coefficient and mass certificates only. Its bounded sigma/v fields
are not used: this applies the primary original global theorem with the
new arbitrary frequencies and retains the literal phase in Lambda. -/
theorem parity_source_data_free_frequency_global434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hp : ℝ) (hL : 3≤L)
    (d : SourceComparisonData434 ι β cfg x L Y Hp)
    (A M0 : ℝ) (hA : 1≤A) (hM0 : 0≤M0) (psi : ℝ → ℂ)
    (hSupport : ∀ u : ℝ,psi u≠0 → 1/A≤u ∧ u≤A)
    (hNorm : ∀ u : ℝ,‖psi u‖≤M0)
    (N : ℕ) (Ptw : Finset ℕ) (sigma0 sigma1 v : ℝ) :
    (∫ theta : AddCircle (1 : ℝ),
      ‖sourceCircleFourierPoly ((Finset.Icc 1 N).image (fun n : ℕ=>(n : ℤ)))
        (sourceSignedCoefficients434 Ptw true
          (sourceOriginalFullEndpointCoefficients434 d.qBase d.S d.Ts d.Tb cfg.q0
            d.Vs d.Vsmall d.Vbig d.ts d.tb d.coef d.k d.primeSlot d.alphaCut d.c d.chi0
            sigma0 sigma1 (fun n=>psi ((n : ℝ)/Y)*sourcePhase n v))) theta‖^2
      ∂AddCircle.haarAddCircle)≤
      (M0*source_data_weight_constant434 cfg)^2*(A+1)*
        (1+(Real.log (A+1)+3/2))^16*Y*
        L^(2*((cfg.ea : ℝ)+(cfg.ec : ℝ)+2*cfg.C0*Real.log (source_data_weight_constant434 cfg))+16) := by
  have hLp : 0<L:=by linarith
  have hL1 : 1≤L:=by linarith
  have hYp : 0<Y:=by linarith [d.hY]
  have hY1 : 1≤Y:=by linarith [d.hY]
  have hAlpha : ∀ n,‖d.alphaCut n‖≤L^cfg.ea:=by
    intro n
    by_cases hn : n∈Finset.Icc d.lo d.hi
    · simpa [SourceComparisonData434.alphaCut,sourceAlphaDyadicCut,hn] using d.hAlpha n hn
    · simp only [SourceComparisonData434.alphaCut,sourceAlphaDyadicCut,if_neg hn,norm_zero]
      positivity
  have hC : ∀ n,‖d.c n‖≤L^cfg.ec:=fun n=>(d.hcBound n).trans d.hCBudget
  let Lambda:=fun n : ℕ=>psi ((n : ℝ)/Y)*sourcePhase n v
  have hLambda : ∀ n∈Finset.Icc 1 N,‖Lambda n‖≤M0*L^(0 : ℝ):=by
    intro n hn
    simpa only [Lambda,norm_mul,sourcePhase_norm,mul_one,Real.rpow_zero] using hNorm ((n : ℝ)/Y)
  have hCut : ∀ n,Nat.ceil (A*Y)<n → Lambda n=0:=by
    intro n hn
    have hlt : A*Y<(n : ℝ):=(Nat.le_ceil (A*Y)).trans_lt (by exact_mod_cast hn)
    have hr : A<(n : ℝ)/Y:=(lt_div_iff₀ hYp).mpr hlt
    have hz : psi ((n : ℝ)/Y)=0:=by
      by_contra hne
      exact (not_lt_of_ge (hSupport _ hne).2) hr
    simp only [Lambda,hz,zero_mul]
  have hGlobal:=(Classical.choose_spec
    (source_original_full_global_log_budget434 cfg.q0 cfg.vmin cfg.tmax
      cfg.hq0 cfg.hq1 cfg.hv)).2 (ι:=ι) (β:=β)
  have hRaw:=hGlobal d.S d.Ts d.Tb d.Vs d.Vsmall d.Vbig d.ts d.tb d.coef d.k
    d.hk d.hVs d.hts d.htb d.hVsmall d.hVbig d.hcoef
    N d.qBase d.primeSlot Ptw d.alphaCut d.c Lambda d.chi0 sigma0 sigma1 A Y L
    cfg.C0 M0 0 cfg.ea cfg.ec hA hY1 hL1 d.hYmax cfg.hC0 hM0
    d.hSmallGroups d.hBigGroups hAlpha hC hLambda hCut
  rw [source_original_full_signed_fourier434]
  simpa only [ite_true,zero_add,source_data_weight_constant434] using hRaw
end Green64Analytic.Parity

end

end

/-! ## HarmonicRankReplacement -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The unchanged independently defined uncapped harmonic functional is its
literal RAW branch plus the independently defined full rank-main family,
up to every prescribed inverse-log error with exactly one external Z.
Both genuine restoration and collision estimates are requested at A+1
BEFORE L and the full actual B633 operator tuple. Their factor2 is paid
by L>=2. No small-restoration, small-collision or small-main premise is
assumed, and no physical cap, E4.1 or Green64 conclusion is asserted. -/
theorem parity_eventually_actual_harmonic_outer_Z_rank_error434
    (J : ℕ) (S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) (hK : 0≤Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
          (Q:ℝ)≤L^CQ → xi⁻¹≤L^Cxi →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ‖(Z:ℂ)*(parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
            (parityDyadicDepth434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
          parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
            (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
            1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
          parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k E G tw psi)‖≤Z*L^(-A) := by
  filter_upwards [parity_eventually_actual_harmonic_outer_Z_stripped_error434
      J S beta gamma CZ Ck CQ Cxi Cpsi Kpsi (A+1) hSfine hbeta hgamma hCZ hK,
    parity_eventually_actual_stripped_rank_main_saving434
      J S beta gamma CZ Ck CQ Cxi Cpsi Kpsi (A+1) hSfine hbeta hgamma hCZ hK,
    eventually_ge_atTop (2:ℝ)] with L hRest hCollision hL2
  refine ⟨hRest.1,hRest.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi
    tw psi hSupp hPsi
  let F := sourceNativePrimeCore r e L b slot δ ξ Kset
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let H := parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
    (parityDyadicDepth434 L) E G (-(rho+xi3)) (-rho) tw 0 psi
  let R := parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
    1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psi
  let B := ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
    ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
      parityActualWeightedStrippedComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k E G tw psi aux
  let Main := parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k E G tw psi
  have hR : ‖(Z:ℂ)*(H-R-B)‖≤Z*L^(-(A+1)) :=
    hRest.2.2 prime l u hlow r e hr b slot δ ξ Kset q chi s0 s1 xi1 xi2 rho sigma
      hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  have hC : ‖(Z:ℂ)*(B-Main)‖≤Z*L^(-(A+1)) :=
    hCollision.2.2 prime l u hlow r e hr b slot δ ξ Kset q chi s0 s1 xi1 xi2 rho sigma
      hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  have hLp : 0<L := by linarith
  have hZ : 0<Z := (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hPowers : L*L^(-(A+1))=L^(-A) := by
    calc
      _ = L^(1+(-(A+1))) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hLp (1:ℝ) (-(A+1))).symm
      _ = L^(-A) := by congr 1;ring
  change ‖(Z:ℂ)*(H-R-Main)‖≤Z*L^(-A)
  calc
    _ = ‖(Z:ℂ)*(H-R-B)+(Z:ℂ)*(B-Main)‖ := by congr 1;ring
    _ ≤ ‖(Z:ℂ)*(H-R-B)‖+‖(Z:ℂ)*(B-Main)‖ := norm_add_le _ _
    _ ≤ Z*L^(-(A+1))+Z*L^(-(A+1)) := add_le_add hR hC
    _ = Z*(2*L^(-(A+1))) := by ring
    _ ≤ Z*(L*L^(-(A+1))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hLp.le _)) hZ.le
    _ = Z*L^(-A) := by rw [hPowers]

/-- The same genuine actual joined error without the external Z.
Its cancellation is justified by the original positive lower Z window.
The full independent rank main retains the original auxiliary-dependent
scalar, cutoff and displacement; this theorem does not bound main or RAW. -/
theorem parity_eventually_actual_harmonic_rank_error434
    (J : ℕ) (S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) (hK : 0≤Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
          (Q:ℝ)≤L^CQ → xi⁻¹≤L^Cxi →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ‖(parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
            (parityDyadicDepth434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
          parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
            (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
            1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
          parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k E G tw psi)‖≤L^(-A) := by
  filter_upwards [parity_eventually_actual_harmonic_outer_Z_rank_error434
    J S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A hSfine hbeta hgamma hCZ hK] with L hSave
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi
    tw psi hSupp hPsi
  have hLp : 0<L := (Real.exp_pos 2).trans_le hSave.1
  have hZ : 0<Z := (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hs := hSave.2.2 prime l u hlow r e hr b slot δ ξ Kset q chi s0 s1 xi1 xi2 rho sigma
    hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hZ.le] at hs
  by_contra hbad
  exact (not_lt_of_ge hs) (mul_lt_mul_of_pos_left (lt_of_not_ge hbad) hZ)
end Green64Analytic.Parity

end

end

/-! ## ActualCellCoupledKernel -/

section

open scoped BigOperators Classical FourierTransform
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 26000

/-- Exact interchange of a finite auxiliary sum with the circle integral.
The endpoint sequences are the same for every auxiliary label; the signed
shift is allowed to depend on that label. Integrability is proved from
finite Fourier polynomials, rather than supplied as a hypothesis. -/
theorem parity_finite_mellin_circle_reindex434
    {I : Type*} (S : Finset I) (b : I → ℂ) (d : I → ℤ)
    (N : Finset ℕ) (U V : ℕ → ℂ) (s : ℝ) :
    Integrable (fun theta : AddCircle (1 : ℝ) =>
      (∑ a ∈ S, b a*fourier (-(d a)) theta) *
        star (sourceNatFourierPoly N (parityMellinFourierFirst434 s U) theta) *
        sourceNatFourierPoly N V theta) AddCircle.haarAddCircle ∧
    (∑ a ∈ S, b a*parityMellinFourierPair434 N U V (d a) s) =
      ∫ theta : AddCircle (1 : ℝ),
        (∑ a ∈ S, b a*fourier (-(d a)) theta) *
          star (sourceNatFourierPoly N (parityMellinFourierFirst434 s U) theta) *
          sourceNatFourierPoly N V theta ∂AddCircle.haarAddCircle := by
  let W := sourceNatFourierPoly N (parityMellinFourierFirst434 s U)
  let T := sourceNatFourierPoly N V
  let f : I → AddCircle (1 : ℝ) → ℂ := fun a theta =>
    b a*(fourier (-(d a)) theta*star (W theta)*T theta)
  have hInt (a : I) : Integrable (f a) AddCircle.haarAddCircle := by
    have hc : Continuous (f a) :=
      continuous_const.mul (((fourier (-(d a))).continuous.mul W.continuous.star).mul T.continuous)
    simpa only [IntegrableOn,Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hPoint (theta : AddCircle (1 : ℝ)) :
      (∑ a ∈ S, f a theta) =
        (∑ a ∈ S,b a*fourier (-(d a)) theta)*star (W theta)*T theta := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [f]
    ring
  constructor
  · exact (integrable_finsetSum S (fun a ha => hInt a)).congr
      (Filter.Eventually.of_forall hPoint)
  · calc
      _ = ∑ a ∈ S,∫ theta : AddCircle (1 : ℝ),f a theta ∂AddCircle.haarAddCircle := by
        apply Finset.sum_congr rfl
        intro a ha
        unfold parityMellinFourierPair434
        exact (integral_const_mul _ _).symm
      _ = ∫ theta : AddCircle (1 : ℝ),∑ a ∈ S,f a theta ∂AddCircle.haarAddCircle :=
        (integral_finsetSum S (fun a ha => hInt a)).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hPoint)

/-- Independently defined actual cell-gated auxiliary kernel. It contains
all original typed probability atoms, the literal scalar with both inverse
cell masses, the common Mellin phase, scale phase and signed 2*k*c Fourier
character. No endpoint sequence or endpoint cutoff is an argument. -/
def parityActualCellCoupledKernel434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (zeta Z : ℝ) (k : ℤ) (s : ℝ) (theta : AddCircle (1 : ℝ)) : ℂ :=
  let P := sourceNativeOriginalTb434 20 L
  let V := sourceNativeOriginalVbig434 20 L
  ∑ aux : ParityActualProbeAux434 L J m hmJ nu,
    let a := sourceOriginalProbeMemoryAuxValues434 P J m hmJ nu aux
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m V
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    (parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
      (sourceOriginalProbeCellA434 m P V nu hA)
      (sourceOriginalProbeCellB434 m P V nu hB) r.1.2 r.2.2
      (sourceOriginalProbeDA434 m nu a) (sourceOriginalProbeDB434 m nu a)
      (nu.1.card+nu.2.card) *
      (sourceOriginalPureMellinPhase434 zeta c * parityScaleMellinFactor434 Z c s *
        fourier (-((2*k)*(c : ℤ))) theta))

/-- Genuine r20 product-assignment representation of the new kernel.
Both source cell gates and both inverse masses remain visible. The product
DA*DB remains inside the additive Fourier character; this is not a claim
that the coupled character factors into two independent prime products. -/
theorem parity_actual_cell_coupled_kernel_reindex434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (zeta Z : ℝ) (k : ℤ) (s : ℝ) (theta : AddCircle (1 : ℝ)) :
    parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta =
    (-((-1 : ℂ)^(nu.1.card+nu.2.card)) *
      (sourceOriginalTwoCellCoefficient434
        (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hA)
        (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hB) r.1.1 r.2.1 : ℂ)) *
      ∑ a ∈ Fintype.piFinset
        (sourceOriginalProbeAuxPrimeSets434 m nu (sourceNativeOriginalTb434 20 L)),
        (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
          (sourceOriginalProbeAuxV434 m nu (sourceNativeOriginalVbig434 20 L) i)) a : ℂ) *
        (if sourceOriginalLiteralLogCell434 hA r.1.1 (sourceOriginalProbeDA434 m nu a) ∧
            sourceOriginalLiteralLogCell434 hB r.2.1 (sourceOriginalProbeDB434 m nu a) then
          star (r.1.2.2 (sourceOriginalProbeDA434 m nu a : ZMod (r.1.2.1.val+1))) *
            star (r.2.2.2 (sourceOriginalProbeDB434 m nu a : ZMod (r.2.2.1.val+1))) *
            (sourceOriginalPureMellinPhase434 zeta
              (sourceOriginalProbeDA434 m nu a*sourceOriginalProbeDB434 m nu a) *
             parityScaleMellinFactor434 Z
              (sourceOriginalProbeDA434 m nu a*sourceOriginalProbeDB434 m nu a) s *
             fourier (-((2*k)*((sourceOriginalProbeDA434 m nu a*
               sourceOriginalProbeDB434 m nu a : ℕ) : ℤ))) theta)
        else 0) := by
  exact parity_actual_rank_aux_coupled_reindex434 L J m hmJ nu hnu hA hB
    r.1.1 r.2.1 r.1.2 r.2.2
    (fun c => sourceOriginalPureMellinPhase434 zeta c * parityScaleMellinFactor434 Z c s *
      fourier (-((2*k)*(c : ℤ))) theta)
end Green64Analytic.Parity

end

end

/-! ## ActualCellCoupledGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 26000

/-- Reuse the literal source auxiliary-to-Gram equivalence for an
arbitrary JOINT function of DA and DB. The true two harmonic product
masses and every labelled prime slot remain unchanged. -/
theorem parity_aux_gram_product_reindex434
    {G : Type} [DecidableEq G] (m : ℕ)
    (nu : SourceOriginalProbePattern434 G m) (P : G → Finset ℕ) (V : G → ℝ)
    (H : ℕ → ℕ → ℂ) :
    (∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu V i)) a : ℂ) *
      H (sourceOriginalProbeDA434 m nu a) (sourceOriginalProbeDB434 m nu a)) =
    ∑ ab : SourceOriginalGramPrimeTuple434 (fun z : nu.1 => P z.val.1) ×
        SourceOriginalGramPrimeTuple434 (fun z : nu.2 => P z.val.1),
      ((sourceOriginalGramPrimeMass434 (fun z : nu.1 => P z.val.1)
          (fun z p => (1/(p : ℝ))/(V z.val.1)) ab.1 *
        sourceOriginalGramPrimeMass434 (fun z : nu.2 => P z.val.1)
          (fun z p => (1/(p : ℝ))/(V z.val.1)) ab.2 : ℝ) : ℂ) *
      H (sourceOriginalGramPrimeProduct434 (fun z : nu.1 => P z.val.1) ab.1)
        (sourceOriginalGramPrimeProduct434 (fun z : nu.2 => P z.val.1) ab.2) := by
  rw [source_original_true_aux_expectation_fubini434]
  apply Finset.sum_congr rfl
  intro ab hab
  have hDA := source_original_true_aux_split_DA434 m nu P
    ((sourceOriginalTrueAuxPrimeSplitEquiv434 m nu P).symm ab)
  have hDB := source_original_true_aux_split_DB434 m nu P
    ((sourceOriginalTrueAuxPrimeSplitEquiv434 m nu P).symm ab)
  simp only [Equiv.apply_symm_apply] at hDA hDB
  rw [hDA,hDB]

/-- The actual r20 coupled kernel is exactly the true physical A/B Gram
prime expectation of two primitive INPUT cell modes and its original
coupled phase. This is a genuine probability-law transport, with both
inverse cell masses outside and c=DA*DB still inside the additive phase. -/
theorem parity_actual_cell_coupled_kernel_gram434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (zeta Z : ℝ) (k : ℤ) (s : ℝ) (theta : AddCircle (1 : ℝ)) :
    let P := sourceNativeOriginalTb434 20 L
    let V := sourceNativeOriginalVbig434 20 L
    let SA : nu.1 → Finset ℕ := fun z => P z.val.1
    let SB : nu.2 → Finset ℕ := fun z => P z.val.1
    let pa := sourceOriginalGramPrimeProduct434 SA
    let pb := sourceOriginalGramPrimeProduct434 SB
    parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta =
      (-((-1 : ℂ)^(nu.1.card+nu.2.card)) *
        (sourceOriginalTwoCellCoefficient434
          (sourceOriginalProbeCellA434 m P V nu hA)
          (sourceOriginalProbeCellB434 m P V nu hB) r.1.1 r.2.1 : ℂ)) *
      ∑ ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA (fun z p => (1/(p : ℝ))/(V z.val.1)) ab.1 *
          sourceOriginalGramPrimeMass434 SB (fun z p => (1/(p : ℝ))/(V z.val.1)) ab.2 : ℝ) : ℂ) *
        (sourceOriginalPrimitiveInputCellMode434 Q hA r.1.1 r.1.2 (pa ab.1) *
          sourceOriginalPrimitiveInputCellMode434 Q hB r.2.1 r.2.2 (pb ab.2) *
          (sourceOriginalPureMellinPhase434 zeta (pa ab.1*pb ab.2) *
            parityScaleMellinFactor434 Z (pa ab.1*pb ab.2) s *
            fourier (-((2*k)*((pa ab.1*pb ab.2 : ℕ) : ℤ))) theta)) := by
  dsimp only
  let P := sourceNativeOriginalTb434 20 L
  let V := sourceNativeOriginalVbig434 20 L
  let SA : nu.1 → Finset ℕ := fun z => P z.val.1
  let SB : nu.2 → Finset ℕ := fun z => P z.val.1
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let phase : ℕ → ℂ := fun c => sourceOriginalPureMellinPhase434 zeta c *
    parityScaleMellinFactor434 Z c s * fourier (-((2*k)*(c : ℤ))) theta
  let coeff := -((-1 : ℂ)^(nu.1.card+nu.2.card)) *
    (sourceOriginalTwoCellCoefficient434 (sourceOriginalProbeCellA434 m P V nu hA)
      (sourceOriginalProbeCellB434 m P V nu hB) r.1.1 r.2.1 : ℂ)
  let H : ℕ → ℕ → ℂ := fun a b =>
    if sourceOriginalLiteralLogCell434 hA r.1.1 a ∧ sourceOriginalLiteralLogCell434 hB r.2.1 b then
      star (r.1.2.2 (a : ZMod (r.1.2.1.val+1))) *
        star (r.2.2.2 (b : ZMod (r.2.2.1.val+1))) * phase (a*b)
    else 0
  have hModes (a b : ℕ) : H a b =
      sourceOriginalPrimitiveInputCellMode434 Q hA r.1.1 r.1.2 a *
        sourceOriginalPrimitiveInputCellMode434 Q hB r.2.1 r.2.2 b * phase (a*b) := by
    by_cases ha : sourceOriginalLiteralLogCell434 hA r.1.1 a <;>
      by_cases hb : sourceOriginalLiteralLogCell434 hB r.2.1 b <;>
      simp [H,sourceOriginalPrimitiveInputCellMode434,ha,hb]
  have hFub := parity_aux_gram_product_reindex434 m nu P V H
  have hKernel := parity_actual_cell_coupled_kernel_reindex434 L J m hmJ nu hnu hA hB r zeta Z k s theta
  calc
    _ = coeff * ∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P),
        (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
          (sourceOriginalProbeAuxV434 m nu V i)) a : ℂ) *
        H (sourceOriginalProbeDA434 m nu a) (sourceOriginalProbeDB434 m nu a) := hKernel
    _ = coeff * ∑ ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA (fun z p => (1/(p : ℝ))/(V z.val.1)) ab.1 *
          sourceOriginalGramPrimeMass434 SB (fun z p => (1/(p : ℝ))/(V z.val.1)) ab.2 : ℝ) : ℂ) *
        H (pa ab.1) (pb ab.2) := congrArg (fun z : ℂ => coeff*z) hFub
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro ab hab
      rw [hModes]
end Green64Analytic.Parity

end

end

/-! ## ActualCellCoupledCircle -/

section

open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 28000

/-- For each original pattern, move the genuine auxiliary probability sum
inside the circle integral and outside the fixed endpoint tests. The rank
carrier uses the original BIG cell masses; its finite sum is independent
of the draw. The original nonzero 2*k guard is preserved explicitly. -/
theorem parity_actual_cell_rank_aux_circle434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi zeta Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (eta : ℝ → ℂ) (s : ℝ) :
    (∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      parityActualCellRankMellinAtAux434 L hS J m hmJ nu Q hA hB xi zeta Z k N
        F G t1 t2 tw eta aux s) =
    if (2*k) = 0 then 0 else
      ∑ r ∈ parityCanonicalRankIndices434 m nu Q hA hB xi
          (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L),
        let Hp := Real.exp ((r.1.1 : ℝ)*hA)*Real.exp ((r.2.1 : ℝ)*hB)
        ∫ theta : AddCircle (1 : ℝ),
          parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta *
          star (sourceNatFourierPoly N (parityMellinFourierFirst434 s
            (fun n => eta ((n : ℝ)/(Z*Hp))*
              parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) F t1 tw true n)) theta) *
          sourceNatFourierPoly N
            (fun n => eta ((n : ℝ)/(Z*Hp))*
              parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) G t2 tw false n) theta
          ∂AddCircle.haarAddCircle := by
  let P := sourceNativeOriginalTb434 20 L
  let V := sourceNativeOriginalVbig434 20 L
  let vals := fun aux : ParityActualProbeAux434 L J m hmJ nu =>
    sourceOriginalProbeMemoryAuxValues434 P J m hmJ nu aux
  let c := fun aux : ParityActualProbeAux434 L J m hmJ nu =>
    parityActualProbeAuxD434 L J m hmJ nu aux
  let mu := fun aux : ParityActualProbeAux434 L J m hmJ nu =>
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m V
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)
  let R := parityCanonicalRankIndices434 m nu Q hA hB xi P V
  let Hp : ParityPrimitiveRankIndex434 Q → ℝ := fun r =>
    Real.exp ((r.1.1 : ℝ)*hA)*Real.exp ((r.2.1 : ℝ)*hB)
  let b := fun (r : ParityPrimitiveRankIndex434 Q) (aux : ParityActualProbeAux434 L J m hmJ nu) =>
    parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
      (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
      r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu (vals aux))
      (sourceOriginalProbeDB434 m nu (vals aux)) (nu.1.card+nu.2.card)
  let U : ParityPrimitiveRankIndex434 Q → ℕ → ℂ := fun r n =>
    eta ((n : ℝ)/(Z*Hp r))*
      parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) F t1 tw true n
  let W : ParityPrimitiveRankIndex434 Q → ℕ → ℂ := fun r n =>
    eta ((n : ℝ)/(Z*Hp r))*
      parityActualRankEndpoint434 L hS J m hmJ nu hA hB r (1/2) G t2 tw false n
  let B := fun (r : ParityPrimitiveRankIndex434 Q) (aux : ParityActualProbeAux434 L J m hmJ nu) =>
    mu aux*(b r aux*(sourceOriginalPureMellinPhase434 zeta (c aux)*parityScaleMellinFactor434 Z (c aux) s))
  have hKernel (r : ParityPrimitiveRankIndex434 Q) (theta : AddCircle (1 : ℝ)) :
      (∑ aux : ParityActualProbeAux434 L J m hmJ nu,
        B r aux*fourier (-((2*k)*(c aux : ℤ))) theta) =
      parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta := by
    unfold parityActualCellCoupledKernel434
    dsimp only
    apply Finset.sum_congr rfl
    intro aux haux
    change B r aux*fourier (-((2*k)*(c aux : ℤ))) theta =
      mu aux*(b r aux*(sourceOriginalPureMellinPhase434 zeta (c aux)*
        parityScaleMellinFactor434 Z (c aux) s*fourier (-((2*k)*(c aux : ℤ))) theta))
    dsimp only [B]
    ring
  have hEach (r : ParityPrimitiveRankIndex434 Q) :=
    (parity_finite_mellin_circle_reindex434
      (Finset.univ : Finset (ParityActualProbeAux434 L J m hmJ nu))
      (B r) (fun aux => (2*k)*(c aux : ℤ)) N (U r) (W r) s).2
  by_cases hk : (2*k) = 0
  · simp only [parityActualCellRankMellinAtAux434,hk,ite_true,mul_zero,Finset.sum_const_zero]
  · simp only [parityActualCellRankMellinAtAux434,hk,ite_false]
    change (∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      mu aux*(sourceOriginalPureMellinPhase434 zeta (c aux)*
        ∑ r ∈ R,b r aux*(parityScaleMellinFactor434 Z (c aux) s*
          parityMellinFourierPair434 N (U r) (W r) ((2*k)*(c aux : ℤ)) s))) =
      ∑ r ∈ R,∫ theta : AddCircle (1 : ℝ),
        parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta *
          star (sourceNatFourierPoly N (parityMellinFourierFirst434 s (U r)) theta) *
          sourceNatFourierPoly N (W r) theta ∂AddCircle.haarAddCircle
    calc
      _ = ∑ r ∈ R,∑ aux : ParityActualProbeAux434 L J m hmJ nu,
          B r aux*parityMellinFourierPair434 N (U r) (W r) ((2*k)*(c aux : ℤ)) s := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro aux haux
        dsimp only [B]
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hEach r]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun theta => by
          dsimp only
          rw [hKernel r theta])

/-- Independent full actual family formed by rank-dependent endpoint
polynomials paired against the actual coupled auxiliary kernel. The
original pattern family and the nonzero 2*k guard remain literal. -/
def parityActualCellCoupledCircleFamily434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (eta : ℝ → ℂ) (s : ℝ) : ℂ :=
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
    if (2*k) = 0 then 0 else
      ∑ r ∈ parityCanonicalRankIndices434 m nu.val Q h h xi
          (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L),
        let Hp := Real.exp ((r.1.1 : ℝ)*h)*Real.exp ((r.2.1 : ℝ)*h)
        ∫ theta : AddCircle (1 : ℝ),
          parityActualCellCoupledKernel434 L J m hmJ nu.val h h r (-xi3) Z k s theta *
          star (sourceNatFourierPoly N (parityMellinFourierFirst434 s
            (fun n => eta ((n : ℝ)/(Z*Hp))*
              parityActualRankEndpoint434 L hS J m hmJ nu.val h h r (1/2) F (-(rho+xi3)) tw true n)) theta) *
          sourceNatFourierPoly N
            (fun n => eta ((n : ℝ)/(Z*Hp))*
              parityActualRankEndpoint434 L hS J m hmJ nu.val h h r (1/2) G (-rho) tw false n) theta
          ∂AddCircle.haarAddCircle

/-- Exact finite family reindex. All dependencies on the auxiliary draw
are confined to the independently defined coupled kernel; its probability
sum and both cell normalizations have not been discarded. -/
theorem parity_actual_cell_rank_family_circle434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (eta : ℝ → ℂ) (s : ℝ) :
    parityActualCellRankMellinFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s =
      parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s := by
  unfold parityActualCellRankMellinFamily434 parityActualCellCoupledCircleFamily434
  dsimp only
  apply Finset.sum_congr rfl
  intro nu hnu
  exact parity_actual_cell_rank_aux_circle434 L hS J m hmJ nu.val Q h h xi (-xi3) Z k _
    F G (-(rho+xi3)) (-rho) tw eta s

/-- Exact Mellin-circle representation of the unchanged actual Main
family, with integrability inherited through the proved pointwise finite
identity. No low-frequency, minor-arc or small-Main estimate is assumed. -/
theorem parity_actual_rank_main_coupled_mellin434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (hZ : 0 < Z) (h1 : h ≤ 1)
    (hSmall : |2*(k : ℝ)/Z| ≤ (128*Real.exp 2)⁻¹)
    (F G : PrimeSlotCore) (tw : Bool) (psi eta : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (hEta : ∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u = 1) :
    let f := parityOriginalLogCutoff434 psi hSmooth hSupport
    Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s *
      parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s) ∧
    parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw psi =
      ∫ s : ℝ, (𝓕 f : 𝓢(ℝ,ℂ)) s *
        parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s := by
  have hBase := parity_actual_cell_rank_main_family_mellin434 L hS J m hmJ Q h xi rho xi3 Ck Z k
    hZ h1 hSmall F G tw psi eta hSmooth hSupport hEta
  simp_rw [parity_actual_cell_rank_family_circle434] at hBase
  exact hBase
end Green64Analytic.Parity

end

end

/-! ## ActualMainMellinTransfer -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Exact actual-Main low/tail transfer through the ORIGINAL cutoff.
This is the application interface for the subsequently proved actual
circle-family estimates, not an unconditional Main-saving assertion on
its own. The low/all amplitude hypotheses refer to the independently
defined full coupled-circle family. Integrability, unchanged-Main
identity, cell localization, original cutoff mass and arbitrary tail
precision are derived from certified constructions. All fixed budgets
precede L. The same physical external Z occurs exactly once. -/
theorem parity_eventually_actual_main_mellin_transfer434
    (E Cpsi Ftail Cglobal CZ Ck : ℝ) (Kpsi : ℕ → ℝ)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j,0 ≤ Kpsi j) (hCF : Cpsi < Ftail)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi rho xi3 Z : ℝ) (k : ℤ),
        h ≤ 1 → Real.exp L*L^(-CZ) ≤ Z → (k.natAbs : ℝ) ≤ L^Ck →
      ∀ (F G : PrimeSlotCore) (tw : Bool) (psi eta : ℝ → ℂ)
        (hSmooth : ContDiff ℝ ∞ psi)
        (hSupport : ∀ u : ℝ,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64),
        sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        (∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u = 1) →
        (∀ s : ℝ, |s| ≤ L^Ftail →
          ‖parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s‖ ≤
            L^(-b662CutoffSavingExponent434 E Cpsi)) →
        (∀ s : ℝ,
          ‖parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s‖ ≤
            L^Cglobal) →
        ‖parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw psi‖ ≤ L^(-E) ∧
        ‖(Z : ℂ)*parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw psi‖ ≤
          Z*L^(-E) := by
  have hMellin := b662_eventually_fourier_cutoff_saving434 E Cpsi (Real.log (64 : ℝ)) Ftail Kpsi
    hCpsi (Real.log_nonneg (by norm_num)) hKpsi hCF Cglobal
  filter_upwards [hMellin,parity_eventually_rank_cell_signed_shift434 CZ Ck hCZ hCk]
    with L hm hg
  intro hS J m hmJ Q h xi rho xi3 Z k h1 hZlo hk F G tw psi eta hSmooth hSupport hReg hEta hLow hAll
  have hkR : |(k : ℝ)| ≤ L^Ck := by simpa only [Nat.cast_natAbs,Int.cast_abs] using hk
  have hGeometry := hg.2 Z k hZlo hkR
  have hEq := parity_actual_rank_main_coupled_mellin434 L hS J m hmJ Q h xi rho xi3 Ck Z k
    hGeometry.1 h1 hGeometry.2 F G tw psi eta hSmooth hSupport hEta
  let f := parityOriginalLogCutoff434 psi hSmooth hSupport
  let amp := fun s => parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw eta s
  have hInt : Integrable (fun s : ℝ => (𝓕 f : 𝓢(ℝ,ℂ)) s*amp s) := hEq.1
  have hSupp : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-Real.log (64 : ℝ)) (Real.log (64 : ℝ)) :=
    parity_log_cutoff_support434 psi hSupport
  have hB := hm f amp 1 (by norm_num) hSupp hReg hInt
    (by intro s hs; simpa only [one_mul] using hLow s hs)
    (by intro s; simpa only [one_mul] using hAll s)
  have hMain : ‖parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw psi‖ ≤ L^(-E) := by
    rw [hEq.2]
    simpa only [one_mul] using hB
  refine ⟨hMain,?_⟩
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hGeometry.1]
  exact mul_le_mul_of_nonneg_left hMain hGeometry.1.le
end Green64Analytic.Parity

end

end

/-! ## ActualCellCoupledNorm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 28000

/-- A genuinely normalized product average is a contraction, with the
actual two sums as its normalizers. Zero-mass cases are included using
the field convention inv_zero. This proves a bound, not an equality that
would discard a dependent joint test. -/
theorem parity_normalized_product_kernel_norm434
    {A B : Type} [Fintype A] [Fintype B]
    (wa : A → ℝ) (wb : B → ℝ) (ha : ∀ a,0 ≤ wa a) (hb : ∀ b,0 ≤ wb b)
    (f : A × B → ℂ) (hf : ∀ ab,‖f ab‖ ≤ 1) :
    ‖((((∑ a,wa a)⁻¹*(∑ b,wb b)⁻¹ : ℝ) : ℂ) *
      ∑ ab : A × B,((wa ab.1*wb ab.2 : ℝ) : ℂ)*f ab)‖ ≤ 1 := by
  let MA := ∑ a,wa a
  let MB := ∑ b,wb b
  have hMA : 0 ≤ MA := Finset.sum_nonneg (fun a ha' => ha a)
  have hMB : 0 ≤ MB := Finset.sum_nonneg (fun b hb' => hb b)
  have hC : 0 ≤ MA⁻¹*MB⁻¹ := mul_nonneg (inv_nonneg.mpr hMA) (inv_nonneg.mpr hMB)
  have hSum : ‖∑ ab : A × B,((wa ab.1*wb ab.2 : ℝ) : ℂ)*f ab‖ ≤ MA*MB := by
    calc
      _ ≤ ∑ ab : A × B,‖((wa ab.1*wb ab.2 : ℝ) : ℂ)*f ab‖ := norm_sum_le _ _
      _ ≤ ∑ ab : A × B,wa ab.1*wb ab.2 := by
        apply Finset.sum_le_sum
        intro ab hab
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (ha _) (hb _))]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf ab) (mul_nonneg (ha _) (hb _))
      _ = MA*MB := by
        rw [Fintype.sum_prod_type]
        simp only [MA,MB,Finset.mul_sum,Finset.sum_mul]
        exact Finset.sum_comm
  have hNorm : ‖((MA⁻¹*MB⁻¹ : ℝ) : ℂ)‖ = MA⁻¹*MB⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
  have hLast : (MA⁻¹*MB⁻¹)*(MA*MB) ≤ 1 := by
    by_cases hA0 : MA = 0
    · simp only [hA0,inv_zero,zero_mul]; norm_num
    by_cases hB0 : MB = 0
    · simp only [hB0,inv_zero,mul_zero,zero_mul]; norm_num
    have heq : (MA⁻¹*MB⁻¹)*(MA*MB) = 1 := by field_simp
    exact heq.le
  change ‖((MA⁻¹*MB⁻¹ : ℝ) : ℂ) * _‖ ≤ 1
  rw [norm_mul,hNorm]
  exact (mul_le_mul_of_nonneg_left hSum hC).trans hLast

/-- Actual coupled rank-kernel global contraction for EVERY frequency,
circle point and scale. Both normalizers are the genuine original cell
probabilities, proven equal to the corresponding weighted Gram-cell
sums. The proof retains all repeated draws, both cell gates and the full
joint c-dependent phase, including zero-mass cells. No source mass-one,
active-cell lower bound, prime equidistribution or small-Main premise is
assumed. This is only a kernel norm bound; its exact expression remains
unchanged with both inverse cell factors visible. -/
theorem parity_actual_cell_coupled_kernel_norm434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (zeta Z : ℝ) (k : ℤ) (s : ℝ) (theta : AddCircle (1 : ℝ)) :
    ‖parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta‖ ≤ 1 := by
  let P := sourceNativeOriginalTb434 20 L
  let V := sourceNativeOriginalVbig434 20 L
  let SA : nu.1 → Finset ℕ := fun z => P z.val.1
  let SB : nu.2 → Finset ℕ := fun z => P z.val.1
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let wa := sourceOriginalGramPrimeMass434 SA (fun z p => (1/(p : ℝ))/(V z.val.1))
  let wb := sourceOriginalGramPrimeMass434 SB (fun z p => (1/(p : ℝ))/(V z.val.1))
  let WA := fun a : SourceOriginalGramPrimeTuple434 SA =>
    if sourceOriginalLiteralLogCell434 hA r.1.1 (pa a) then wa a else 0
  let WB := fun b : SourceOriginalGramPrimeTuple434 SB =>
    if sourceOriginalLiteralLogCell434 hB r.2.1 (pb b) then wb b else 0
  let phase := fun c : ℕ => sourceOriginalPureMellinPhase434 zeta c *
    parityScaleMellinFactor434 Z c s * fourier (-((2*k)*(c : ℤ))) theta
  let f := fun ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB =>
    star (r.1.2.2 (pa ab.1 : ZMod (r.1.2.1.val+1))) *
      star (r.2.2.2 (pb ab.2 : ZMod (r.2.2.1.val+1))) * phase (pa ab.1*pb ab.2)
  have hV (g : sourceNativeOriginalBigType434 20 L) : 0 ≤ V g := by
    change 0 ≤ ∑ p ∈ P g,(p : ℝ)⁻¹
    exact Finset.sum_nonneg (fun p hp => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hwa (a : SourceOriginalGramPrimeTuple434 SA) : 0 ≤ wa a := by
    apply Finset.prod_nonneg
    intro z hz
    exact div_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)) (hV z.val.1)
  have hwb (b : SourceOriginalGramPrimeTuple434 SB) : 0 ≤ wb b := by
    apply Finset.prod_nonneg
    intro z hz
    exact div_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg _)) (hV z.val.1)
  have hWA (a : SourceOriginalGramPrimeTuple434 SA) : 0 ≤ WA a := by
    dsimp only [WA]
    split_ifs
    · exact hwa a
    · exact le_rfl
  have hWB (b : SourceOriginalGramPrimeTuple434 SB) : 0 ≤ WB b := by
    dsimp only [WB]
    split_ifs
    · exact hwb b
    · exact le_rfl
  have hMassA : sourceOriginalProbeCellA434 m P V nu hA r.1.1 = ∑ a,WA a := by
    simp only [sourceOriginalProbeCellA434,source_original_true_cell_probability_eq_gram_mass434,
      sourceOriginalRealGramCellMass434,sourceOriginalGramPrimeMass434,source_original_true_aux_atom_mu434]
    rfl
  have hMassB : sourceOriginalProbeCellB434 m P V nu hB r.2.1 = ∑ b,WB b := by
    simp only [sourceOriginalProbeCellB434,source_original_true_cell_probability_eq_gram_mass434,
      sourceOriginalRealGramCellMass434,sourceOriginalGramPrimeMass434,source_original_true_aux_atom_mu434]
    rfl
  have hPhase (c : ℕ) : ‖phase c‖ = 1 := by
    have hExp : ‖Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I)‖ = 1 := by
      rw [mul_comm]
      exact Complex.norm_exp_I_mul_ofReal _
    have hFourier : ‖fourier (-((2*k)*(c : ℤ))) theta‖ = 1 := by
      rw [fourier_apply,Circle.norm_coe]
    simp only [phase,parityScaleMellinFactor434,norm_mul,source_original_pure_mellin_phase_norm_one434,
      hExp,hFourier,mul_one,one_mul]
  have hf (ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB) :
      ‖f ab‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul,norm_mul,norm_star,norm_star,hPhase,mul_one]
    exact (mul_le_mul (r.1.2.2.norm_le_one _) (r.2.2.2.norm_le_one _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hPoint (ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB) :
      ((wa ab.1*wb ab.2 : ℝ) : ℂ) *
        (sourceOriginalPrimitiveInputCellMode434 Q hA r.1.1 r.1.2 (pa ab.1) *
          sourceOriginalPrimitiveInputCellMode434 Q hB r.2.1 r.2.2 (pb ab.2) *
          phase (pa ab.1*pb ab.2)) =
      ((WA ab.1*WB ab.2 : ℝ) : ℂ)*f ab := by
    by_cases ha : sourceOriginalLiteralLogCell434 hA r.1.1 (pa ab.1) <;>
      by_cases hb : sourceOriginalLiteralLogCell434 hB r.2.1 (pb ab.2) <;>
      simp [WA,WB,f,sourceOriginalPrimitiveInputCellMode434,ha,hb]
  have hKernel := parity_actual_cell_coupled_kernel_gram434 L J m hmJ nu hnu hA hB r zeta Z k s theta
  have hEq : parityActualCellCoupledKernel434 L J m hmJ nu hA hB r zeta Z k s theta =
      (-((-1 : ℂ)^(nu.1.card+nu.2.card))) *
      (((((∑ a,WA a)⁻¹*(∑ b,WB b)⁻¹ : ℝ) : ℂ)) *
        ∑ ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB,
          ((WA ab.1*WB ab.2 : ℝ) : ℂ)*f ab) := by
    rw [hKernel]
    change (-((-1 : ℂ)^(nu.1.card+nu.2.card)) *
      (sourceOriginalTwoCellCoefficient434 (sourceOriginalProbeCellA434 m P V nu hA)
        (sourceOriginalProbeCellB434 m P V nu hB) r.1.1 r.2.1 : ℂ)) *
      (∑ ab : SourceOriginalGramPrimeTuple434 SA × SourceOriginalGramPrimeTuple434 SB,
        ((wa ab.1*wb ab.2 : ℝ) : ℂ) *
          (sourceOriginalPrimitiveInputCellMode434 Q hA r.1.1 r.1.2 (pa ab.1) *
           sourceOriginalPrimitiveInputCellMode434 Q hB r.2.1 r.2.2 (pb ab.2) *
           phase (pa ab.1*pb ab.2))) = _
    simp_rw [hPoint]
    unfold sourceOriginalTwoCellCoefficient434
    rw [hMassA,hMassB]
    ring
  rw [hEq,norm_mul]
  simp only [norm_neg,norm_pow,norm_one,one_pow,one_mul]
  exact parity_normalized_product_kernel_norm434 WA WB hWA hWB f hf
end Green64Analytic.Parity

end

end

