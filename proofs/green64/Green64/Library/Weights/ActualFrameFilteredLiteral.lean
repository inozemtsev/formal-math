module

public import Green64.Library.Correlation.Part047
public import Green64.Library.Weights.SourceEFrameRow

@[expose] public section

/-!
# Weights / ActualFrameFilteredLiteral

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualFrameFilteredLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 20000000

private theorem clean_ite_decidable_irrel {A : Type} (p : Prop)
    (d e : Decidable p) (a b : A) :
    @ite A p d a b = @ite A p e a b := by
  have h : d=e := Subsingleton.elim _ _
  cases h
  rfl

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The actual filtered source E witness sum is EXACTLY its frame
representation on reachable physical states. The CLEAN predicate sees
the full oriented choice, with its true OLD injection and permutation
coefficients, and no orbit averaging is removed by assumption. -/
theorem source_original_SOURCE_MARKED_FILTERED_E_frame_row434
    (keep : (st : FullPhysicalState SP sm BP bm (J+ell) cap) →
      FullOrientedSourceChoice SP sm BP bm J ell m cap patterns st → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F =
    sourceOriginalSourceEFrameFilteredRow434 SP sm BP bm J ell m cap patterns
      keep q rho Vs V mu K zeta theta o k x seen F := by
  classical
  let H : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ := fun z =>
    if keep x z then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z *
      F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
        (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
    else 0
  let W : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ := fun z =>
    if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
        orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z
    then H z else 0
  have he :
      (∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x,W z) =
      ∑ rf : Σ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
          SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
        W (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x rf.1 rf.2) := by
    apply Fintype.sum_equiv (sourceOriginalSourceEFrameEquiv434 SP sm BP bm J ell m cap patterns x)
    intro z
    change W z = W ((sourceOriginalSourceEFrameEquiv434 SP sm BP bm J ell m cap patterns x).symm
      ((sourceOriginalSourceEFrameEquiv434 SP sm BP bm J ell m cap patterns x) z))
    rw [Equiv.symm_apply_apply]
  unfold sourceOriginalMemoryMarkedFilteredE434 sourceOriginalSourceEFrameFilteredRow434
  have hw :
      (∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x,
        if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
            keep x z ∧ orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z then
          sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
            q rho Vs V mu K zeta theta o k x z *
          F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
            (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
        else 0) = ∑ z,W z := by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hl : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z
    <;> by_cases hk : keep x z
    <;> by_cases hb : orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z
    <;> simp [hl,hk,hb,H,W]
  rw [hw,he,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  have hh := source_original_SOURCE_E_frame_sum434 SP sm BP bm J ell m cap patterns
    x seen hx r o k H
  convert hh using 1
  apply Finset.sum_congr rfl
  intro f hf
  dsimp only [W,H,sourceOriginalSourceEFrameAdmissible434]
  exact clean_ite_decidable_irrel _ _ _ _ _

/-- The original no-promotion/no-store restriction is exactly the
same predicate used by the marked projected DIRTY theorem. -/
theorem source_original_SOURCE_MARKED_CLEAN_frame_row434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k x seen F =
    sourceOriginalSourceEFrameCleanRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F := by
  exact source_original_SOURCE_MARKED_FILTERED_E_frame_row434
    SP sm BP bm J ell m cap patterns _ q rho Vs V mu K zeta theta o k x seen hx F
end Green64Analytic.CorrelationSquare

end

end

