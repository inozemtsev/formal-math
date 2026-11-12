module

public import Green64.Library.Correlation.Part029

@[expose] public section

/-!
# Weights / GhostReturnLiteralRow

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGhostReturnLiteralRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

namespace GhostReturnLiteralRow

abbrev old {R : Type} : SourceOriginalGhostReturnState434 R → List R
  | .unborn => []
  | .pending r => [r]
  | .retired => []

abbrev seen {R : Type} : SourceOriginalGhostReturnState434 R → Bool
  | .unborn => false
  | .pending _ => true
  | .retired => true

def readState {R : Type} (F : SourceOriginalGhostReturnState434 R → ℂ)
    (l : List R) (s : Bool) : ℂ :=
  match l with
  | [] => if s then F .retired else F .unborn
  | r::_ => F (.pending r)

end GhostReturnLiteralRow

open GhostReturnLiteralRow

@[simp] private theorem zero_nil {R : Type} [DecidableEq R] (a : R) :
    zeroOld ([] : List R) (fun r => r=a) = ∅ := by
  ext i
  exact Fin.elim0 i

@[simp] private theorem zero_single {R : Type} [DecidableEq R] (a r : R) :
    zeroOld [r] (fun x => x=a) = if r=a then {0} else ∅ := by
  ext i
  have hi : i=0 := by
    apply Fin.ext
    have hh := i.isLt
    simp only [List.length_cons,List.length_nil] at hh
    change i.val=0
    omega
  subst i
  simp [zeroOld]

@[simp] private theorem sum_fin_one {R : Type} [Fintype R] (f : R → ℂ) :
    (∑ x : Fin 1 → R,f (x 0)) = ∑ r : R,f r := by
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) R) _ _ (fun x => rfl)

/-- Literal sourceGhostTerm expansion for one numerical prime:
all residues remain in R; its true global birth gate allows at most one
fresh particle and forbids rebirth after pending or retired.
The cap-one sector is closed under that gate from these three states. -/
def sourceOriginalGhostReturnLiteralRow434 {R : Type}
    [Fintype R] [DecidableEq R] (a : R) (eta lambda : ℝ)
    (s : SourceOriginalGhostReturnState434 R)
    (F : SourceOriginalGhostReturnState434 R → ℂ) : ℂ :=
  ∑ A ∈ (zeroOld (old s) (fun r => r=a)).powerset,
  ∑ b ∈ Finset.range 2,
  ∑ fresh : Fin b → R,
    if b=0 ∨ seen s=false then
      sourceGhostTerm (old s) (fun r => r=a) A fresh
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ))
        (fun r => if r=a then (lambda:ℂ) else 0) *
      readState F (afterGhost (old s) A fresh) (seen s || decide (b≠0))
    else 0

theorem source_original_GHOST_RETURN_literal_unborn434
    {R : Type} [Fintype R] [DecidableEq R] (a : R) (eta lambda : ℝ)
    (F : SourceOriginalGhostReturnState434 R → ℂ) :
    sourceOriginalGhostReturnLiteralRow434 a eta lambda .unborn F =
      F .unborn - (eta:ℂ)*(lambda:ℂ)*F (.pending a) := by
  classical
  have hsum : (∑ x : Fin 1 → R, if x 0=a then
      -((eta:ℂ)*(lambda:ℂ)*F (.pending (x 0))) else 0) =
      -((eta:ℂ)*(lambda:ℂ)*F (.pending a)) := by
    rw [sum_fin_one (fun r => if r=a then
      -((eta:ℂ)*(lambda:ℂ)*F (.pending r)) else 0)]
    simp
  simp [sourceOriginalGhostReturnLiteralRow434,old,seen,zero_nil,zero_single,
    sourceGhostTerm,afterGhost,readState,Finset.sum_range_succ,
    Fin.sum_univ_succ,Fin.prod_univ_succ,List.finRange_succ,
    List.ofFn_succ,List.filter_cons,List.filter_nil,hsum]
  <;> ring

theorem source_original_GHOST_RETURN_literal_retired434
    {R : Type} [Fintype R] [DecidableEq R] (a : R) (eta lambda : ℝ)
    (F : SourceOriginalGhostReturnState434 R → ℂ) :
    sourceOriginalGhostReturnLiteralRow434 a eta lambda .retired F = F .retired := by
  classical
  simp [sourceOriginalGhostReturnLiteralRow434,old,seen,zero_nil,zero_single,
    sourceGhostTerm,afterGhost,readState,Finset.sum_range_succ,
    Fin.sum_univ_succ,Fin.prod_univ_succ,List.finRange_succ,List.ofFn_succ,List.filter_cons,List.filter_nil]

theorem source_original_GHOST_RETURN_literal_pending434
    {R : Type} [Fintype R] [DecidableEq R] (a r : R) (eta lambda : ℝ)
    (F : SourceOriginalGhostReturnState434 R → ℂ) :
    sourceOriginalGhostReturnLiteralRow434 a eta lambda (.pending r) F =
      if r=a then (1-(eta:ℂ))*F (.pending r)-(eta:ℂ)*F .retired
      else F (.pending r) := by
  classical
  by_cases h : r=a
  · subst r
    have hpow : ({(0 : Fin 1)} : Finset (Fin 1)).powerset = {∅,{0}} := by decide
    simp [hpow,sourceOriginalGhostReturnLiteralRow434,old,seen,zero_nil,zero_single,
      sourceGhostTerm,afterGhost,readState,Finset.sum_range_succ,
      Fin.sum_univ_succ,Fin.prod_univ_succ,List.finRange_succ,
      List.ofFn_succ,List.filter_cons,List.filter_nil,Finset.univ_unique,Finset.powerset_insert,sub_eq_add_neg]
    <;> ring
  · simp [sourceOriginalGhostReturnLiteralRow434,old,seen,zero_nil,zero_single,h,
      sourceGhostTerm,afterGhost,readState,Finset.sum_range_succ,
      Fin.sum_univ_succ,Fin.prod_univ_succ,List.finRange_succ,
      List.ofFn_succ,List.filter_cons,List.filter_nil,Finset.univ_unique,Finset.powerset_insert,sub_eq_add_neg]

/-- The recurrence used in the baseline identity is precisely the
original signed ghost expansion in this once-born sector. -/
theorem source_original_GHOST_RETURN_literal_real_row434
    {R : Type} [Fintype R] [DecidableEq R] (a : R) (eta lambda : ℝ)
    (F : SourceOriginalGhostReturnState434 R → ℝ)
    (s : SourceOriginalGhostReturnState434 R) :
    sourceOriginalGhostReturnLiteralRow434 a eta lambda s (fun x => (F x:ℂ)) =
      (sourceOriginalGhostReturnRow434 a eta lambda F s : ℂ) := by
  cases s with
  | unborn =>
    rw [source_original_GHOST_RETURN_literal_unborn434]
    simp only [sourceOriginalGhostReturnRow434,Complex.ofReal_sub,Complex.ofReal_mul]
  | pending r =>
    rw [source_original_GHOST_RETURN_literal_pending434]
    simp only [sourceOriginalGhostReturnRow434]
    split_ifs <;> push_cast <;> rfl
  | retired => exact source_original_GHOST_RETURN_literal_retired434 a eta lambda _
end Green64Analytic.CorrelationSquare

end

end

