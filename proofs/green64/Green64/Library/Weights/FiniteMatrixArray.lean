module

public import Green64.Library.Correlation.Part041
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Weights / FiniteMatrixArray

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FiniteMatrixArray -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Chronological product, with the initial row acting first. -/
def b650MatrixChain434 (T : ℕ → Matrix X X ℂ) : ℕ → ℕ → Matrix X X ℂ
  | 0, _ => 1
  | N+1, s => T s * b650MatrixChain434 T N (s+1)

private def b650HeadTailEquiv (N : ℕ) : (Fin (N+1) → X) ≃ X × (Fin N → X) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    cases i using Fin.cases <;> rfl
  right_inv p := by
    cases p
    rfl

/-- Complete finite matrix expansion. Both endpoint functions remain;
in particular the final state is NOT forced to equal the initial state. -/
theorem b650_matrix_chain_array434 (T : ℕ → Matrix X X ℂ)
    (N s : ℕ) (a b : X → ℂ) :
    (∑ x : X, a x * ((b650MatrixChain434 T N s).mulVec b) x) =
    ∑ states : Fin (N+1) → X,
      a (states 0) *
        (∏ i : Fin N, T (s+i.val) (states i.castSucc) (states i.succ)) *
      b (states (Fin.last N)) := by
  induction N generalizing s a with
  | zero =>
    rw [← Equiv.sum_comp (b650HeadTailEquiv (X:=X) 0).symm]
    simp [b650MatrixChain434,b650HeadTailEquiv,Fintype.sum_prod_type]
  | succ N ih =>
    calc
      _ = ∑ x : X, ∑ y : X,
          (a x * T s x y) * ((b650MatrixChain434 T N (s+1)).mulVec b) y := by
        simp only [b650MatrixChain434]
        rw [← Matrix.mulVec_mulVec]
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc]
      _ = ∑ x : X, ∑ tail : Fin (N+1) → X,
          (a x * T s x (tail 0)) *
            (∏ i : Fin N, T (s+1+i.val) (tail i.castSucc) (tail i.succ)) *
          b (tail (Fin.last N)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact ih (s+1) (fun y => a x * T s x y)
      _ = _ := by
        rw [← Equiv.sum_comp (b650HeadTailEquiv (X:=X) (N+1)).symm]
        simp only [Fintype.sum_prod_type,b650HeadTailEquiv,Equiv.coe_fn_symm_mk,
          Fin.cons_zero,Fin.prod_univ_succ,Fin.val_zero,Nat.add_zero,
          Fin.castSucc_zero,Fin.cons_succ,Fin.val_succ]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro tail ht
        have hcs (i : Fin N) : i.succ.castSucc = i.castSucc.succ := rfl
        have hlast : Fin.last (N+1) = (Fin.last N).succ := rfl
        simp only [hcs,hlast,Fin.cons_succ]
        simp only [Nat.add_left_comm,Nat.add_comm,mul_assoc]

/-- Expansion through a finite original frame family at EACH edge.
No absolute value, Cauchy inequality, or character average is taken. -/
theorem b650_matrix_chain_frame_array434 {Frame : Type} [Fintype Frame]
    (K : ℕ → X → X → Frame → ℂ) (N s : ℕ) (a b : X → ℂ) :
    (∑ x : X, a x *
      ((b650MatrixChain434 (fun j => Matrix.of (fun x y => ∑ f : Frame, K j x y f)) N s).mulVec b) x) =
    ∑ states : Fin (N+1) → X, ∑ frames : Fin N → Frame,
      a (states 0) *
        (∏ i : Fin N, K (s+i.val) (states i.castSucc) (states i.succ) (frames i)) *
      b (states (Fin.last N)) := by
  rw [b650_matrix_chain_array434]
  apply Finset.sum_congr rfl
  intro states hs
  simp only [Matrix.of_apply]
  rw [Fintype.prod_sum,Finset.mul_sum,Finset.sum_mul]
end Green64FullPhysicalE

end

end

