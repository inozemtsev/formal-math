module

public import Green64.Library.Correlation.PhysicalSlotLift
public import Green64.Library.Weights.Part098
public import Green64.Library.Weights.Part043

@[expose] public section

/-!
# Weights / MarkedFamilySplit

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualMarkedFamilySplit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

private theorem decoration_count_transport
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (s t : G → ℕ) (ht : s=t)
    (q : ℝ) (V : G → ℝ) (n : ℕ) (f : (∀g,Fin (t g) → ℕ) → ℂ) :
    actualBigMarkDecoration P s q V
      (fun a => f (fun g i => a g (Fin.cast (congrFun ht g).symm i))) n =
      actualBigMarkDecoration P t q V f n := by
  cases ht
  rfl

/-- All literal SMALL base factors, including the distinguished band,
every damping power and every descending-factorial count. -/
def b604ActualSmallBaseFactor434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (ell : ℕ) (q : ℝ) (n : ℕ) : ℂ :=
  ((q^((smallPrimeCount (sourceNativeOriginalS434 r L hS) n:ℤ)-(ell:ℤ)) /
    (sourceNativeOriginalVs434 r L hS)^ell:ℝ):ℂ) *
  bigMarkPrefactor (sourceNativeOriginalTs434 r L hS) (fun _=>ell) q
    (sourceNativeOriginalVsmall434 r L hS) n *
  ((smallPrimeCount (sourceNativeOriginalS434 r L hS) n).descFactorial ell:ℂ) *
  ((∏g,(smallPrimeCount (sourceNativeOriginalTs434 r L hS g) n).descFactorial ell:ℕ):ℂ)

/-- The existing complete-family equivalence and marked-weight split,
applied to the literal lifted physical free counts. No new group law,
mark count, divisor mask or factorial is assumed. -/
theorem b604_actual_all_P_marked_decoration_split434
    (r : ℕ) (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) (hL : 1<L)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (q : ℝ) (n : ℕ)
    (f : (∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) → ℂ) :
    actualBigMarkDecoration (sourceOriginalPAllActualBands r L)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu))
      q (sourceNativeOriginalAllPMass434 r L)
      (fun a => f (b604ActualBigMarkRestriction434 r L J ell m hmJ nu a)) n =
    b604ActualSmallBaseFactor434 r L hS ell q n *
      actualBigMarkDecoration (sourceNativeOriginalTb434 r L)
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) q
        (sourceNativeOriginalVbig434 r L) f n := by
  let e := sourceNativeOriginalCompleteEquiv434 r L hS hL
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ (b604ActualLiftedPattern434 r L m nu)
  let tb := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let ts := Sum.elim (fun _ : Unit=>ell)
    (Sum.elim (fun _ : sourceNativeOriginalTsType434 r L hS=>ell) tb)
  let P := Sum.elim (fun _ : Unit=>sourceNativeOriginalS434 r L hS)
    (Sum.elim (sourceNativeOriginalTs434 r L hS) (sourceNativeOriginalTb434 r L))
  let V := Sum.elim (fun _ : Unit=>sourceNativeOriginalVs434 r L hS)
    (Sum.elim (sourceNativeOriginalVsmall434 r L hS) (sourceNativeOriginalVbig434 r L))
  have ht : (fun i=>t (e i))=ts := b604_actual_complete_free_count434 r L hS hL J ell m hmJ nu
  have hP : (fun i=>sourceOriginalPAllActualBands r L (e i))=P :=
    (source_native_original_complete_family434 r L hS hL).symm
  have hV : (fun i=>sourceNativeOriginalAllPMass434 r L (e i))=V := by
    funext i
    rcases i with u | s | b
    · cases u
      change (∑p∈sourceNativeOriginalS434 r L hS,1/(p:ℝ)) =
        ∑p∈sourceNativeOriginalS434 r L hS,(p:ℝ)⁻¹
      simp only [one_div]
    · change (∑p∈sourceNativeOriginalTs434 r L hS s,1/(p:ℝ)) =
        ∑p∈sourceNativeOriginalTs434 r L hS s,(p:ℝ)⁻¹
      simp only [one_div]
    · change (∑p∈sourceNativeOriginalTb434 r L b,1/(p:ℝ)) =
        ∑p∈sourceNativeOriginalTb434 r L b,(p:ℝ)⁻¹
      simp only [one_div]
  have hr := b605_actual_marked_decoration_group_reindex434 e (sourceOriginalPAllActualBands r L)
    t q (sourceNativeOriginalAllPMass434 r L) n
    (fun a => f (b604ActualBigMarkRestriction434 r L J ell m hmJ nu a))
  rw [←hr,hP,hV]
  have hf :
      (fun a : ∀i,Fin (t (e i)) → ℕ =>
        f (b604ActualBigMarkRestriction434 r L J ell m hmJ nu
          (b605GroupMarkedEquiv434 e t a))) =
      (fun a : ∀i,Fin (t (e i)) → ℕ =>
        f (fun g i => a (Sum.inr (Sum.inr g))
          (Fin.cast (congrFun ht (Sum.inr (Sum.inr g))).symm i))) := by
    funext a
    congr 1
    funext g i
    change b605GroupMarkedEquiv434 e t a (e (Sum.inr (Sum.inr g))) _ = _
    rw [b605_group_marked_equiv_apply434]
    congr 1
  rw [hf]
  trans actualBigMarkDecoration P ts q V (fun a=>f (fun g=>a (.inr (.inr g)))) n
  · exact decoration_count_transport P _ ts ht q V n
      (fun a=>f (fun g=>a (.inr (.inr g))))
  have hs := source_original_marked_weight_split434
    (sourceNativeOriginalS434 r L hS) (sourceNativeOriginalTs434 r L hS)
    (sourceNativeOriginalTb434 r L) q (sourceNativeOriginalVs434 r L hS)
    (sourceNativeOriginalVsmall434 r L hS) (sourceNativeOriginalVbig434 r L)
    ell (fun _=>ell) tb f n
  change actualBigMarkDecoration P ts q V (fun a=>f (fun g=>a (.inr (.inr g)))) n = _
  rw [hs]
  unfold literalSourceWeight
  rw [literal_mark_sum_factor]
  change _ = b604ActualSmallBaseFactor434 r L hS ell q n *
    (bigMarkPrefactor (sourceNativeOriginalTb434 r L) tb q (sourceNativeOriginalVbig434 r L) n * _)
  unfold b604ActualSmallBaseFactor434
  ring

/-- At the original r=6, ell=1 and q=1/2 this is literally B578's
SMALL marked factor, not an upper bound or a redefined coefficient. -/
theorem b604_actual_B578_small_factor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) (n : ℕ) :
    b604ActualSmallBaseFactor434 6 L hS 1 (1/2) n =
      sourceB578ActualSmallMarkedFactor434 L hS n := rfl
end Green64Analytic.SourceBlockSieve

end

end

