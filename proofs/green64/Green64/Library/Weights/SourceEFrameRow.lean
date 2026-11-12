module

public import Green64.Library.Weights.Part027

@[expose] public section

/-!
# Weights / SourceEFrameRow

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSourceEFrameRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000


private theorem ite_decidable_irrel {A : Type} (p : Prop)
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

def sourceOriginalSourceEFrameAdmissible434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (seen : Finset ℕ) (o k : ℤ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r) : Prop :=
  let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f
  sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
    orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z

theorem source_original_SOURCE_E_frame_sum434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (H : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ) :
    (∑ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      if sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f
      then H (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f) else 0) =
    if h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
        sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f then
      H (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r
        (Classical.choose h))
    else 0 := by
  classical
  by_cases h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
      sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f
  · rw [dif_pos h]
    let f := Classical.choose h
    have hf : sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns
        x seen o k r f := Classical.choose_spec h
    rw [Finset.sum_eq_single f]
    · exact if_pos hf
    · intro g hg hgf
      apply if_neg
      intro hlegal
      exact hgf (source_original_SOURCE_E_frame_injections_unique434
        SP sm BP bm J ell m cap patterns x seen hx r o k g f hlegal.1 hf.1)
    · intro hf
      exact False.elim (hf (Finset.mem_univ f))
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro f hf
    exact if_neg (fun hf => h ⟨f,hf⟩)

/-- Literal original marked E with every admissible OLD injection summed
exactly. The remaining frame carrier has no OLD index and no cap parameter;
the original legality, including output capacity, is still checked. -/
def sourceOriginalSourceEFrameRow434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) : ℂ :=
  ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
    if h : ∃ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
        sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f then
      let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r
        (Classical.choose h)
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z *
        F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
          (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
    else 0

/-- Exact all-pattern/all-group original E row, retaining both endpoint
permutation families, joint Knu, actual D/step, phases, birth gate and F.
No sum over OLD injections and no multiplicity loss remain in the frame row. -/
theorem source_original_SOURCE_MARKED_E_frame_row434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) seen)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F =
    sourceOriginalSourceEFrameRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F := by
  let H : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℂ := fun z =>
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x z *
      F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
        (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)
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
  unfold physicalOrientedBirthMarkedE sourceOrientedPhysicalChoices
    sourceOriginalSourceEFrameRow434
  simp only [Finset.sum_filter]
  change (∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x,
    if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z then
      if orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z
      then H z else 0 else 0) = _
  have hw :
      (∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x,
        if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z then
          if orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns seen z
          then H z else 0 else 0) = ∑ z,W z := by
    apply Finset.sum_congr rfl
    intro z hz
    simp only [W,ite_and]
  rw [hw,he,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  have hh := source_original_SOURCE_E_frame_sum434 SP sm BP bm J ell m cap patterns
    x seen hx r o k H
  convert hh using 1
  apply Finset.sum_congr rfl
  intro f hf
  dsimp only [W,sourceOriginalSourceEFrameAdmissible434]
  exact ite_decidable_irrel _ _ _ _ _
end Green64Analytic.CorrelationSquare

end

end

