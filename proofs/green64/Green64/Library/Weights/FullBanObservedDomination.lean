module

public import Green64.Library.Weights.Part098
public import Green64.Library.Weights.FullBanSelectedUnits

@[expose] public section

/-!
# Weights / FullBanObservedDomination

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FullBanObservedDomination -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- Only the observed product's auxiliary avoidance is retained here.
Hidden-list avoidance will be discarded only after deriving this gate
from the original complete free/auxiliary ban. -/
def b598AvoidedNorm434 (c : G → ℕ) (D : ℕ)
    (f : (∀g,Fin (c g) → ℕ) → ℂ) (a : ∀g,Fin (c g) → ℕ) : ℝ :=
  if (∏g,∏i,a g i).Coprime D then ‖f a‖ else 0

/-- Nonnegative observed majorant retaining both exact selected-unit
filters. It is not a redefinition of the original signed Knu. -/
def b598RetainedObservedKnu434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (D : ℕ)
    (a : ∀g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.2 g) → ℕ)
    (b : ∀g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.1 g) → ℕ) : ℝ :=
  if (∏g,∏i,a g i).Coprime D ∧ (∏g,∏i,b g i).Coprime D
  then ‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux a b‖ else 0

/-- The retained majorant factors into two nonnegative actual columns. -/
theorem b598_retained_observed_columns434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (D : ℕ)
    (a : ∀g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.2 g) → ℕ)
    (b : ∀g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.1 g) → ℕ) :
    b598RetainedObservedKnu434 m nu Q hA hB xi P V aux D a b =
      b598AvoidedNorm434 (sourceOriginalProbeChosenGroupCount434 m nu.2) D
        (b598OriginalSourceColumn434 m nu Q hB xi P V aux) a *
      b598AvoidedNorm434 (sourceOriginalProbeChosenGroupCount434 m nu.1) D
        (b598OriginalTargetColumn434 m nu Q hA xi P V aux) b := by
  unfold b598RetainedObservedKnu434 b598AvoidedNorm434
  rw [b598_grouped_canonical_norm434]
  split_ifs <;> simp_all

omit [DecidableEq G] in

private theorem avoided_nonneg (c : G → ℕ) (D : ℕ)
    (f : (∀g,Fin (c g) → ℕ) → ℂ) (a : ∀g,Fin (c g) → ℕ) :
    0 ≤ b598AvoidedNorm434 c D f a := by
  unfold b598AvoidedNorm434
  split_ifs <;> positivity

private theorem norm_sum_ofReal_nonneg {I : Type} (S : Finset I)
    (f : I → ℝ) (hf : ∀i∈S,0 ≤ f i) :
    ‖∑i∈S,(f i:ℂ)‖ = ∑i∈S,f i := by
  rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg hf)]

/-- The original FULL ban is retained until it proves every selected
mark avoids D. Only then may the remaining hidden bans be removed in
an upper bound. Neither endpoint is assumed coprime to D. -/
theorem b598_full_ban_coupled_observed_domination434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (hPrime : ∀g p,p∈P g → p.Prime)
    (hDisj : ∀g h p,p∈P g → p∈P h → g=h)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (haux : aux∈Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P))
    (D : ℕ) (hD : D=sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux)
    (w wp : ℕ) :
    ‖sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux (1/2) w wp‖ ≤
      ‖actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) (1/2) V
        (fun a => (b598AvoidedNorm434 (sourceOriginalProbeChosenGroupCount434 m nu.2) D
          (b598OriginalSourceColumn434 m nu Q hB xi P V aux)
          (fun g i => a g (b598OriginalObservedBSlot434 J ell m hmJ nu g i)) : ℂ)) w‖ *
      ‖actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) (1/2) V
        (fun b => (b598AvoidedNorm434 (sourceOriginalProbeChosenGroupCount434 m nu.1) D
          (b598OriginalTargetColumn434 m nu Q hA xi P V aux)
          (fun g i => b g (b598OriginalObservedASlot434 J ell m hmJ nu g i)) : ℂ)) wp‖ := by
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let fB := fun a : ∀g,Fin (t g) → ℕ =>
    b598AvoidedNorm434 (sourceOriginalProbeChosenGroupCount434 m nu.2) D
      (b598OriginalSourceColumn434 m nu Q hB xi P V aux)
      (fun g i => a g (b598OriginalObservedBSlot434 J ell m hmJ nu g i))
  let fA := fun b : ∀g,Fin (t g) → ℕ =>
    b598AvoidedNorm434 (sourceOriginalProbeChosenGroupCount434 m nu.1) D
      (b598OriginalTargetColumn434 m nu Q hA xi P V aux)
      (fun g i => b g (b598OriginalObservedASlot434 J ell m hmJ nu g i))
  have hfB (a : ∀g,Fin (t g) → ℕ) : 0 ≤ fB a := avoided_nonneg _ _ _ _
  have hfA (b : ∀g,Fin (t g) → ℕ) : 0 ≤ fA b := avoided_nonneg _ _ _ _
  have hpoint (a : ∀g,Fin (t g) → ℕ) (ha : a∈bigMarkLists P t w)
      (b : ∀g,Fin (t g) → ℕ) (hb : b∈bigMarkLists P t wp) :
      ‖sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b‖ ≤
        fB a*fA b := by
    by_cases hban : sourceB574FreeAuxBan434 J ell m hmJ nu aux a b
    · have hu := b601_original_full_ban_marks_coprime434 P hPrime hDisj
        J ell m hmJ nu aux haux w wp a b ha hb hban
      rw [←hD] at hu
      have hs : (∏g,∏i,a g (b598OriginalObservedBSlot434 J ell m hmJ nu g i)).Coprime D := by
        apply Nat.coprime_prod_left_iff.mpr
        intro g hg
        exact Nat.coprime_prod_left_iff.mpr (fun i _ => hu.1 g _)
      have ht : (∏g,∏i,b g (b598OriginalObservedASlot434 J ell m hmJ nu g i)).Coprime D := by
        apply Nat.coprime_prod_left_iff.mpr
        intro g hg
        exact Nat.coprime_prod_left_iff.mpr (fun i _ => hu.2 g _)
      rw [sourceB574CanonicalFreeKernel434,ite_eq_left hban,b598_original_canonical_grouped434,
        b598_grouped_canonical_norm434]
      dsimp only [fB,fA,b598AvoidedNorm434]
      split_ifs
      exact le_rfl
    · simp only [sourceB574CanonicalFreeKernel434,ite_eq_right hban,norm_zero]
      exact mul_nonneg (hfB a) (hfA b)
  have hsum :
      ‖∑a∈bigMarkLists P t w,∑b∈bigMarkLists P t wp,
        sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b‖ ≤
      (∑a∈bigMarkLists P t w,fB a)*(∑b∈bigMarkLists P t wp,fA b) := by
    calc
      _ ≤ ∑a∈bigMarkLists P t w,‖∑b∈bigMarkLists P t wp,
          sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b‖ := norm_sum_le _ _
      _ ≤ ∑a∈bigMarkLists P t w,∑b∈bigMarkLists P t wp,
          ‖sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b‖ :=
        Finset.sum_le_sum (fun a ha => norm_sum_le _ _)
      _ ≤ ∑a∈bigMarkLists P t w,∑b∈bigMarkLists P t wp,fB a*fA b :=
        Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hpoint a ha b hb))
      _ = _ := by
        simp_rw [←Finset.mul_sum]
        rw [←Finset.sum_mul]
  change ‖bigMarkPrefactor P t (1/2) V w * bigMarkPrefactor P t (1/2) V wp *
      (∑a∈bigMarkLists P t w,∑b∈bigMarkLists P t wp,
        sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b)‖ ≤
      ‖actualBigMarkDecoration P t (1/2) V (fun a => (fB a:ℂ)) w‖ *
      ‖actualBigMarkDecoration P t (1/2) V (fun b => (fA b:ℂ)) wp‖
  simp only [actualBigMarkDecoration,norm_mul]
  rw [norm_sum_ofReal_nonneg _ fB (fun a ha => hfB a),
    norm_sum_ofReal_nonneg _ fA (fun b hb => hfA b)]
  calc
    _ ≤ (‖bigMarkPrefactor P t (1/2) V w‖*‖bigMarkPrefactor P t (1/2) V wp‖) *
      ((∑a∈bigMarkLists P t w,fB a)*(∑b∈bigMarkLists P t wp,fA b)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

