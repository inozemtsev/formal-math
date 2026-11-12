module

public import Green64.Library.Weights.Part029

@[expose] public section

/-!
# Weights / SourceEBackgroundOperator

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSourceEBackgroundOperator -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

private theorem ite_decidable_irrel {A : Type} (p : Prop)
    (d e : Decidable p) (a b : A) :
    @ite A p d a b = @ite A p e a b := by
  have h : d=e := Subsingleton.elim _ _
  cases h
  rfl

theorem source_original_subtype_sum_if434 {I : Type} [Fintype I]
    (p : I → Prop) (F : I → ℂ) :
    (∑ i : {i // p i},F i.1) = ∑ i,if p i then F i else 0 := by
  rw [←Finset.sum_subtype (Finset.univ.filter p) (by intro i;simp) F,
    Finset.sum_filter]

theorem source_original_SOURCE_MARKED_E_fibre_frames434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen F =
    ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
      sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen r F := by
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
  have hh := source_original_subtype_sum_if434
    (sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r)
    (fun f => H (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f))
  convert hh.symm using 1
  · apply Finset.sum_congr rfl
    intro f hf
    dsimp only [W,sourceOriginalSourceEFrameAdmissible434]
    exact ite_decidable_irrel _ _ _ _ _
  · rfl

def sourceOriginalActiveAvoidsBackground434
    (background : (g : BG) → Finset (BP g))
    (out : FullPhysicalOutput SP sm BP bm (J+ell)) : Prop :=
  ∀ g j,(out.2 g).1 j ∉ background g

theorem source_original_SOURCE_E_frame_active_cut434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (background : (g : BG) → Finset (BP g))
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r
      (fun out s => if sourceOriginalActiveAvoidsBackground434 SP sm BP bm J ell background out
        then F out s else 0) =
    if (∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g) then
      sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen r F else 0 := by
  by_cases h : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g
  · rw [if_pos h]
    unfold sourceOriginalSourceEFrameFibreRow434
    apply Finset.sum_congr rfl
    intro f hf
    dsimp only
    congr 1
    have hactive : sourceOriginalActiveAvoidsBackground434 SP sm BP bm J ell background
        (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k
          (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f.1)) := h
    rw [if_pos hactive]
  · rw [if_neg h]
    unfold sourceOriginalSourceEFrameFibreRow434
    apply Finset.sum_eq_zero
    intro f hf
    dsimp only
    have hactive : ¬sourceOriginalActiveAvoidsBackground434 SP sm BP bm J ell background
        (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k
          (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f.1)) := h
    rw [if_neg hactive,mul_zero]

variable (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
variable (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
variable (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)

local notation "X" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap y
local notation "Y" => sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
  (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background y)
local notation "E" => sourceOriginalCanonicalBackgroundEmbedding434 SP sm BP bm
  (J+ell) cap hcap background y seen hy


/- Exact transfer of the literal original E with its target-active
background-avoidance projector. The sum remains over every original
frame; auxiliary labels are unrestricted, and each frame keeps its
own physical D/step, complete K and marked terminal observation. -/
include hcap hy in
theorem source_original_SOURCE_MARKED_E_background_transfer434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    physicalOrientedBirthMarkedE SP sm BP bm J ell m cap patterns
      q 1 Vs V mu K zeta theta o k X seen
      (fun out s => if sourceOriginalActiveAvoidsBackground434 SP sm BP bm J ell background out
        then F out s else 0) =
    ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
      if (∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g) then
        sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
          q 1 Vs V mu K zeta theta o k Y seen r
          (fun out s => F
            (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background y
              (sourceOrientedStep SP sm BP bm J ell m cap (patterns r.1) r.2.1 X
                r.2.2.1.1 r.2.2.2.1 o k) out) s)
      else 0 := by
  rw [source_original_SOURCE_MARKED_E_fibre_frames434]
  apply Finset.sum_congr rfl
  intro r hr
  rw [source_original_SOURCE_E_frame_active_cut434]
  by_cases ht : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g
  · simp only [if_pos ht]
    exact source_original_SOURCE_E_background_frame_row434
      SP sm BP bm J ell m cap patterns hcap background y seen hy q Vs V mu K
      zeta theta r o k ht F
  · simp only [if_neg ht]
end Green64Analytic.CorrelationSquare

end

end

