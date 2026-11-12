module

public import Green64.Library.Weights.LiteralPBandTwoCore
public import Green64.Library.Weights.D61EmptyQSkipChartZero

@[expose] public section

/-!
# Weights / LiteralD61StrippedCore

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LiteralD61StrippedCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Merely records the two ORIGINAL D36 inequalities and the ORIGINAL
terminal clip in a finite support. No coefficient or point is removed
unless the literal B563 alpha at that point is already forced to zero. -/
def b589OriginalD61MaskedK (a eta b0 L : ℝ) (K : Finset ℕ) : Finset ℕ :=
  K.filter (fun m => m ≤ ⌊2*Real.exp L⌋₊+2 ∧
    (Real.exp ((1-eta)*L) ≤ (m:ℝ) ∧ (m:ℝ) ≤ Real.exp ((1-a+b0/4)*L)))

private theorem original_D61_restricted_alpha_identity
    (a eta b0 L : ℝ) (K : Finset ℕ) :
    restrictSequence K (sourceNativeB563OriginalD61Alpha434 a eta b0 L) =
      restrictSequence (b589OriginalD61MaskedK a eta b0 L K)
        (sourceNativeOriginalFullD20Alpha434 (L^(-(1:ℝ)))
          (Real.exp (Real.sqrt L)) ((Real.exp L)^a)) := by
  funext m
  by_cases hk : m ∈ K <;>
    by_cases hc : m ≤ ⌊2*Real.exp L⌋₊+2 <;>
    by_cases hm : Real.exp ((1-eta)*L) ≤ (m:ℝ) ∧
      (m:ℝ) ≤ Real.exp ((1-a+b0/4)*L) <;>
    simp [restrictSequence,b589OriginalD61MaskedK,
      sourceNativeB563OriginalD61Alpha434,sourceD36OriginalCofactorMask,
      sourceNativeOriginalFullD20Alpha434,hk,hc,hm]

/-- EXACT identity for the literal original sigma=1 D61 core.
Both cofactor power masks, b0/4 slack, terminal cutoff, full Delta
and every Q/Fourier/character parameter occur unchanged. -/
theorem b589_original_sigma_one_D61_core_identity434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (a eta b0 : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    sourceNativePrimeCore r d L b slot δ ξ K
      (sourceNativeB563OriginalD61Alpha434 a eta b0 L) q χ σ₀ σ₁ =
    sourceNativePrimeCore r d L b slot δ ξ
      (b589OriginalD61MaskedK a eta b0 L K)
      (sourceNativeOriginalFullD20Alpha434 (L^(-(1:ℝ)))
        (Real.exp (Real.sqrt L)) ((Real.exp L)^a)) q χ σ₀ σ₁ := by
  unfold sourceNativePrimeCore
  congr 1
  exact original_D61_restricted_alpha_identity a eta b0 L K

/-- The ACTUAL sigma=1 D61 pair, not an arbitrary bounded-alpha core,
is controlled by the two stripped quotient divisor squares. The two
original cofactor dyads may be supplied as K,K'; all masks stay inside
both literal alphas, and neither selected product incurs a tau factor. -/
theorem b589_literal_sigma_one_D61_two_core_stripped_bound434
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceOriginalPAllGroupType r L) m)
    (w wp : ℕ) (hw : 0 < w) (hwp : 0 < wp)
    (marks marks' : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (hmarks : marks ∈ bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hmarks' : marks' ∈ bigMarkLists (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp)
    (b b' : Fin (d+1)) (slot slot' : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (δ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → Bool)
    (ξ' : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b' slot').length → ℝ)
    (K K' : Finset ℕ) (a eta b0 : ℝ)
    (hWy : Real.exp (Real.sqrt L) ≤ (Real.exp L)^a)
    (q q' : ℕ) (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q')
    (σ₀ σ₁ σ₀' σ₁' : ℝ) :
    let P := sourceOriginalPAllActualBands r L
    let F := sourceNativePrimeCore r d L b slot δ ξ K
      (sourceNativeB563OriginalD61Alpha434 a eta b0 L) q χ σ₀ σ₁
    let F' := sourceNativePrimeCore r d L b' slot' δ' ξ' K'
      (sourceNativeB563OriginalD61Alpha434 a eta b0 L) q' χ' σ₀' σ₁'
    ‖primeSlotCoreValue P F w * star (primeSlotCoreValue P F' wp)‖ ≤
      ((w/sourceOriginalProbeFreeSourceX434 J ell m hmJ nu marks).divisors.card : ℝ)^2 *
      ((wp/sourceOriginalProbeFreeTargetX434 J ell m hmJ nu marks').divisors.card : ℝ)^2 := by
  dsimp only
  rw [b589_original_sigma_one_D61_core_identity434,
    b589_original_sigma_one_D61_core_identity434]
  exact b589_literal_P_original_two_core_stripped_bound434
    r d L hr hL J ell m hmJ nu w wp hw hwp marks marks' hmarks hmarks'
    b b' slot slot' δ ξ δ' ξ'
    (b589OriginalD61MaskedK a eta b0 L K) (b589OriginalD61MaskedK a eta b0 L K')
    (L^(-(1:ℝ))) (Real.exp (Real.sqrt L)) ((Real.exp L)^a) hWy
    q q' χ χ' σ₀ σ₁ σ₀' σ₁'
end Green64Analytic.ShiftTwoTerminal

end

end

