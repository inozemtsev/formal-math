module

public import Green64.Library.Analysis.Estimates.LargePrimeBonferroni

@[expose] public section

/-!
# Weights / EulerBonferroniError

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## EulerBonferroniError -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceSieveBarrier
set_option autoImplicit false
set_option maxHeartbeats 20000000

private theorem b624_e_zero (P : Finset ℕ) (w : ℕ → ℝ) :
    b610Elementary434 P w 0 = 1 := by
  simp [b610Elementary434]

private theorem b624_e_insert (P : Finset ℕ) (w : ℕ → ℝ)
    (p : ℕ) (hp : p ∉ P) (r : ℕ) :
    b610Elementary434 (insert p P) w (r+1) =
      b610Elementary434 P w (r+1)+w p*b610Elementary434 P w r := by
  have hd : Disjoint (P.powersetCard (r+1)) ((P.powersetCard r).image (insert p)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hSi
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hSi
    exact hp ((Finset.mem_powersetCard.mp hS).1 (Finset.mem_insert_self _ _))
  have hinj : Set.InjOn (insert p) (↑(P.powersetCard r) : Set (Finset ℕ)) := by
    intro S hS T hT heq
    have hpS : p ∉ S := fun h => hp ((Finset.mem_powersetCard.mp hS).1 h)
    have hpT : p ∉ T := fun h => hp ((Finset.mem_powersetCard.mp hT).1 h)
    have he := congrArg (fun A : Finset ℕ => A.erase p) heq
    simpa [hpS,hpT] using he
  unfold b610Elementary434
  rw [Finset.powersetCard_succ_insert hp,Finset.sum_union hd,Finset.sum_image hinj,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  exact Finset.prod_insert (fun h => hp ((Finset.mem_powersetCard.mp hS).1 h))

private theorem b624_B_zero (P : Finset ℕ) (w : ℕ → ℝ) :
    b610Bonferroni434 P w 0 = 1 := by
  simp [b610Bonferroni434,b624_e_zero]

private theorem b624_B_empty (w : ℕ → ℝ) (R : ℕ) :
    b610Bonferroni434 ∅ w R = 1 := by
  induction R with
  | zero => exact b624_B_zero ∅ w
  | succ R ih =>
    unfold b610Bonferroni434 at *
    rw [Finset.sum_range_succ,ih]
    have he : b610Elementary434 ∅ w (R+1)=0 := by
      have hz : (∅ : Finset ℕ).powersetCard (R+1) = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [b610Elementary434,hz]
    simp [he]

private theorem b624_B_insert (P : Finset ℕ) (w : ℕ → ℝ)
    (p : ℕ) (hp : p ∉ P) (R : ℕ) :
    b610Bonferroni434 (insert p P) w (R+1) =
      b610Bonferroni434 P w (R+1)-w p*b610Bonferroni434 P w R := by
  have hstep (S : Finset ℕ) (j : ℕ) :
      b610Bonferroni434 S w (j+1) =
        b610Bonferroni434 S w j+(-1 : ℝ)^(j+1)*b610Elementary434 S w (j+1) := by
    linarith [b610_adjacent_bonferroni_difference434 S w j]
  induction R with
  | zero =>
    rw [hstep,hstep]
    simp only [b624_B_zero,b624_e_insert P w p hp 0,b624_e_zero]
    ring
  | succ R ih =>
    rw [hstep (insert p P) (R+1),ih,b624_e_insert P w p hp (R+1)]
    rw [hstep P (R+1),hstep P R]
    simp only [pow_succ]
    ring

/-- Complete finite Euler Bonferroni error, with its CORRECT sign and
a full next elementary-symmetric bound. This is finite product algebra,
not an independence claim about physical positions. -/
theorem b624_signed_euler_bonferroni_error434
    (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) (R : ℕ) :
    0 ≤ (-1 : ℝ)^R*(b610Bonferroni434 P w R-(∏ p ∈ P, (1-w p))) ∧
    (-1 : ℝ)^R*(b610Bonferroni434 P w R-(∏ p ∈ P, (1-w p))) ≤
      b610Elementary434 P w (R+1) := by
  revert hw R
  induction P using Finset.induction_on with
  | empty =>
    intro hw R
    rw [b624_B_empty,Finset.prod_empty,sub_self,mul_zero]
    have hz : (∅ : Finset ℕ).powersetCard (R+1) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simp)
    simp [b610Elementary434,hz]
  | @insert p P hp ih =>
    intro hw R
    have hwp := hw p (Finset.mem_insert_self _ _)
    have hwP : ∀ q ∈ P, 0 ≤ w q ∧ w q ≤ 1 :=
      fun q hq => hw q (Finset.mem_insert_of_mem hq)
    cases R with
    | zero =>
      have hi := ih hwP 0
      rw [b624_B_zero,pow_zero,one_mul] at hi
      rw [b624_B_zero,pow_zero,one_mul,Finset.prod_insert hp,
        b624_e_insert P w p hp 0,b624_e_zero,mul_one]
      have hV : 0 ≤ ∏ q ∈ P, (1-w q) :=
        Finset.prod_nonneg (fun q hq => sub_nonneg.mpr (hwP q hq).2)
      constructor
      · nlinarith [mul_nonneg hwp.1 hV]
      · nlinarith [mul_nonneg hwp.1 hi.1]
    | succ R =>
      have hi1 := ih hwP (R+1)
      have hi0 := ih hwP R
      have he :
          (-1 : ℝ)^(R+1) *
            (b610Bonferroni434 (insert p P) w (R+1) -
              (∏ q ∈ insert p P, (1-w q))) =
          (-1 : ℝ)^(R+1) *
            (b610Bonferroni434 P w (R+1) - (∏ q ∈ P, (1-w q))) +
          w p*((-1 : ℝ)^R *
            (b610Bonferroni434 P w R - (∏ q ∈ P, (1-w q)))) := by
        rw [b624_B_insert P w p hp R,Finset.prod_insert hp,pow_succ]
        ring
      rw [he,b624_e_insert P w p hp (R+1)]
      exact ⟨add_nonneg hi1.1 (mul_nonneg hwp.1 hi0.1),
        add_le_add hi1.2 (mul_le_mul_of_nonneg_left hi0.2 hwp.1)⟩

/-- A complete elementary coefficient has an exponential-moment bound.
This avoids an unformalized factorial estimate and is strong enough for
the moving finite-sieve depth. -/
theorem b624_elementary_exponential_moment434
    (P : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    b610Elementary434 P w r * t^r ≤ Real.exp (t*(∑ p ∈ P, w p)) := by
  have hprod (S : Finset ℕ) (hS : S ∈ P.powersetCard r) :
      (∏ p ∈ S, w p)*t^r = ∏ p ∈ S, t*w p := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,(Finset.mem_powersetCard.mp hS).2]
    ring
  calc
    _ = ∑ S ∈ P.powersetCard r, ∏ p ∈ S, t*w p := by
      rw [b610Elementary434,Finset.sum_mul]
      exact Finset.sum_congr rfl hprod
    _ ≤ ∑ S ∈ P.powerset, ∏ p ∈ S, t*w p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro S hS
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1
      · intro S hS hnot
        exact Finset.prod_nonneg (fun p hp =>
          mul_nonneg ht (hw p ((Finset.mem_powerset.mp hS) hp)))
    _ = ∏ p ∈ P, (1+t*w p) := (Finset.prod_one_add P).symm
    _ ≤ ∏ p ∈ P, Real.exp (t*w p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact add_nonneg (by norm_num) (mul_nonneg ht (hw p hp))
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (t*w p)
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]
end Green64Analytic.ShiftTwoTerminal

end

end

