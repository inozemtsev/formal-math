module

public import Green64.Library.Weights.MarkedFamilySplit
public import Green64.Library.Correlation.Part069

@[expose] public section

/-!
# Weights / FullCoupledSlice

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualFullCoupledSlice -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem decoration_const_mul
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (t : G → ℕ) (q : ℝ) (V : G → ℝ)
    (f : (∀g,Fin (t g) → ℕ) → ℂ) (c : ℂ) (n : ℕ) :
    actualBigMarkDecoration P t q V (fun a=>c*f a) n =
      c*actualBigMarkDecoration P t q V f n := by
  unfold actualBigMarkDecoration
  rw [←Finset.mul_sum]
  ring

private theorem stripped_slice_nested
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) :
    sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp =
    actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) q V
      (fun a=>actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) q V
        (fun b=>sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b) wp) w := by
  unfold sourceB574CanonicalStrippedSlice434 actualBigMarkDecoration
  rw [←Finset.mul_sum]
  ring

/-- Every SMALL base factor is real; retaining star at the source
therefore agrees exactly with B578's nativeCommon convention. -/
theorem b604_actual_small_base_star434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (ell : ℕ) (q : ℝ) (n : ℕ) :
    star (b604ActualSmallBaseFactor434 r L hS ell q n) =
      b604ActualSmallBaseFactor434 r L hS ell q n := by
  simp [b604ActualSmallBaseFactor434,bigMarkPrefactor]

/-- Exact coupled FULL all-P marked sum equals the original BIG full-ban
slice times both actual SMALL factors. This is the finite production
application of the complete-family equivalence, not a norm estimate. -/
theorem b604_actual_full_coupled_slice434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1<L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (q : ℝ) (w wp : ℕ) :
    sourceB574CanonicalStrippedSlice434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
      Q hA hB xi (sourceOriginalPAllActualBands r L) (sourceNativeOriginalAllPMass434 r L)
      (b604ActualLiftedAux434 r L m nu aux) q w wp =
    b604ActualSmallBaseFactor434 r L hS ell q w *
      b604ActualSmallBaseFactor434 r L hS ell q wp *
      sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi
        (sourceNativeOriginalTb434 r L) (sourceNativeOriginalVbig434 r L) aux q w wp := by
  let tb := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
  let R := b604ActualBigMarkRestriction434 r L J ell m hmJ nu
  let K := sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi
    (sourceNativeOriginalTb434 r L) (sourceNativeOriginalVbig434 r L) aux
  have hK (a b : ∀g,Fin (t g) → ℕ) :
      sourceB574CanonicalFreeKernel434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
        Q hA hB xi (sourceOriginalPAllActualBands r L) (sourceNativeOriginalAllPMass434 r L)
        (b604ActualLiftedAux434 r L m nu aux) a b = K (R a) (R b) := by
    have hh := b604_actual_full_ban_Knu_lift434 r L J ell m hmJ nu Q hA hB xi
      (sourceOriginalPAllActualBands r L) (sourceNativeOriginalAllPMass434 r L) aux a b
    rw [b604_actual_BIG_mass_pullback434] at hh
    exact hh
  rw [stripped_slice_nested]
  simp_rw [hK]
  have hInner (a : ∀g,Fin (t g) → ℕ) :=
    b604_actual_all_P_marked_decoration_split434 r L hS hL J ell m hmJ nu q wp (K (R a))
  trans actualBigMarkDecoration (sourceOriginalPAllActualBands r L) t q
    (sourceNativeOriginalAllPMass434 r L)
    (fun a=>b604ActualSmallBaseFactor434 r L hS ell q wp *
      actualBigMarkDecoration (sourceNativeOriginalTb434 r L) tb q
        (sourceNativeOriginalVbig434 r L) (K (R a)) wp) w
  · congr 1
    funext a
    exact hInner a
  rw [b604_actual_all_P_marked_decoration_split434 r L hS hL J ell m hmJ nu q w
    (fun a=>b604ActualSmallBaseFactor434 r L hS ell q wp *
      actualBigMarkDecoration (sourceNativeOriginalTb434 r L) tb q
        (sourceNativeOriginalVbig434 r L) (K a) wp)]
  rw [decoration_const_mul,←stripped_slice_nested]
  ring

/-- The literal B578 BIG marked/projected factor equals the all-P lifted
one with BOTH projectors inside the same complex expression. The source
SMALL factor keeps its native conjugate orientation. -/
theorem b604_actual_B578_projected_slice434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) (hL : 1<L)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (w wp : ℕ) :
    sourceB578ActualPatternProjector434 L m nu w *
      sourceB578ActualPatternProjector434 L m nu wp *
      (star (sourceB578ActualSmallMarkedFactor434 L hS w) *
        sourceB578ActualSmallMarkedFactor434 L hS wp *
        sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi
          (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux (1/2) w wp) =
    ShiftTwoTerminal.b598ActualAllPPatternProjector434 6 L m (b604ActualLiftedPattern434 6 L m nu) w *
      ShiftTwoTerminal.b598ActualAllPPatternProjector434 6 L m (b604ActualLiftedPattern434 6 L m nu) wp *
      sourceB574CanonicalStrippedSlice434 J 1 m hmJ (b604ActualLiftedPattern434 6 L m nu)
        Q hA hB xi (sourceOriginalPAllActualBands 6 L) (sourceNativeOriginalAllPMass434 6 L)
        (b604ActualLiftedAux434 6 L m nu aux) (1/2) w wp := by
  rw [b604_actual_projector_lift434,b604_actual_projector_lift434,
    ←b604_actual_B578_small_factor434,←b604_actual_B578_small_factor434,
    b604_actual_small_base_star434,
    ←b604_actual_full_coupled_slice434 6 L hS hL J 1 m hmJ nu Q hA hB xi aux (1/2) w wp]
end Green64Analytic.SourceBlockSieve

end

end

