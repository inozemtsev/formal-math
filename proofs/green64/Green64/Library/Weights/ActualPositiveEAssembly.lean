module

public import Green64.Library.Correlation.Part051
public import Green64.Library.Weights.ActualRhoOneFullEPacket
public import Green64.Library.Correlation.Part046

@[expose] public section

/-!
# Weights / ActualPositiveEAssembly

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualPositiveEAssembly -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 24000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Full absolute original E row, retaining the literal legality,
coefficient and joint oscillatory K. Only the extra seen cut is absent. -/
def sourceOriginalActualFullERow434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) : ℝ :=
  ∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x,
    if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z then
      ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z‖ else 0

private theorem real_subtype_sum_if434 {I : Type} [Fintype I]
    (p : I → Prop) (F : I → ℝ) :
    (∑ i : {i // p i},F i.1) = ∑ i,if p i then F i else 0 := by
  rw [←Finset.sum_subtype (Finset.univ.filter p) (by intro i;simp) F,
    Finset.sum_filter]

/-- All actual E frames with the global numerical seen gate are
bounded by the full original row. The passage is one exact frame
reindexing followed by removal of a positive indicator. -/
theorem source_original_ABSOLUTE_E_frames_le_full_row434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ) :
    (∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
      sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen r (fun _ _ => 1)) ≤
    sourceOriginalActualFullERow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x := by
  let W : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → ℝ := fun z =>
    if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z then
      ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z‖ else 0
  have he :
      sourceOriginalActualFullERow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x =
      ∑ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
        ∑ f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
          W (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f) := by
    have he' :
        (∑ z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x,W z) =
        ∑ rf : Σ r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns,
            SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r,
          W (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x rf.1 rf.2) := by
      apply Fintype.sum_equiv (sourceOriginalSourceEFrameEquiv434 SP sm BP bm J ell m cap patterns x)
      intro z
      change W z = W ((sourceOriginalSourceEFrameEquiv434 SP sm BP bm J ell m cap patterns x).symm
        ((sourceOriginalSourceEFrameEquiv434 SP sm BP bm J ell m cap patterns x) z))
      rw [Equiv.symm_apply_apply]
    simpa only [sourceOriginalActualFullERow434,W,Fintype.sum_sigma] using he'
  rw [he]
  apply Finset.sum_le_sum
  intro r hr
  unfold sourceOriginalAbsoluteEFrame434
  simp only [mul_one]
  rw [real_subtype_sum_if434
    (sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r)
    (fun f => ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f)‖)]
  apply Finset.sum_le_sum
  intro f hf
  dsimp only [W]
  by_cases ha : sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns
      x seen o k r f
  · rw [if_pos ha,if_pos ha.1]
  · rw [if_neg ha]
    split_ifs
    · exact norm_nonneg _
    · rfl

/-- The complete E row is the sum of actual packets. No independence
of K, legality or any endpoint phase is introduced by this reindexing. -/
theorem source_original_ACTUAL_full_E_row_packets434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) :
    sourceOriginalActualFullERow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x =
    ∑ nu : Nu,∑ aux : SourceBigAux BP J m (patterns nu),
    ∑ bs : BigGroupPerm (BG:=BG) (J+ell),∑ bt : BigGroupPerm (BG:=BG) (J+ell),
    ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalActualFullEPacket434 SP sm BP bm J ell m cap patterns
        nu aux x bs bt ss tt q rho Vs V mu K zeta theta o k := by
  letI : Fintype (sourceOriginalMemoryBigFrameChoice434 BP bm (J+ell) cap x.2) := inferInstance
  letI (nu : Nu) : Fintype (SourceBigAux BP J m (patterns nu)) := inferInstance
  letI : Fintype (BigGroupPerm (BG:=BG) (J+ell)) := inferInstance
  letI : Fintype (GroupPermFamily (G:=SG) (J+ell)) := inferInstance
  letI : Fintype (GroupState SP sm (J+ell)) := inferInstance
  let e : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x ≃
      (Σ nu : Nu,SourceBigAux BP J m (patterns nu) ×
        BigGroupPerm (BG:=BG) (J+ell) × BigGroupPerm (BG:=BG) (J+ell) ×
        GroupPermFamily (G:=SG) (J+ell) × GroupPermFamily (G:=SG) (J+ell) ×
        sourceOriginalMemoryBigFrameChoice434 BP bm (J+ell) cap x.2 ×
          GroupState SP sm (J+ell)) :=
    { toFun := fun ⟨nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩ => ⟨nu,aux,bs,bt,ss,tt,b,zs⟩
      invFun := fun ⟨nu,aux,bs,bt,ss,tt,b,zs⟩ => ⟨nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩
      left_inv := by rintro ⟨nu,aux,⟨bs,bt,b,zs⟩,ss,tt⟩;rfl
      right_inv := by rintro ⟨nu,aux,bs,bt,ss,tt,b,zs⟩;rfl }
  let w := fun z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x =>
    if sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z then
      ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z‖ else 0
  have he := Fintype.sum_equiv e w (fun z => w (e.symm z))
    (by intro z;rw [e.symm_apply_apply])
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,
    sourceOriginalActualFullERow434,sourceOriginalActualFullEPacket434,
    sourceOriginalMemoryFixedPhysicalChoice434,w,e,Equiv.coe_fn_symm_mk] at he ⊢
  convert he using 1 <;> congr <;> exact Subsingleton.elim _ _
end Green64Analytic.CorrelationSquare

end

end

