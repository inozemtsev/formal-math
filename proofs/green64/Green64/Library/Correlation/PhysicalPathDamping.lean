module

public import Green64.Library.Sieve.Foundations.Part003

@[expose] public section

/-!
# Correlation / PhysicalPathDamping

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalPathDamping -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Loss at a prime for the actual integer path offsets. Repeated offsets
are kept; their visits multiply their original damping factors. -/
def b637PathResidueLoss434 (visits : Finset ℕ) (eta : ℕ → ℝ)
    (offset : ℕ → ℤ) (p r : ℕ) : ℝ :=
  1-∏ i ∈ visits, if (r:ZMod p)+(offset i:ZMod p)=0 then eta i else 1

private theorem b637_path_loss_unit (visits : Finset ℕ) (eta : ℕ → ℝ)
    (offset : ℕ → ℤ) (heta : ∀ i ∈ visits, 0 ≤ eta i ∧ eta i ≤ 1)
    (p r : ℕ) : 0 ≤ b637PathResidueLoss434 visits eta offset p r ∧
      b637PathResidueLoss434 visits eta offset p r ≤ 1 := by
  let v : ℕ → ℝ := fun i => if (r:ZMod p)+(offset i:ZMod p)=0 then eta i else 1
  have hv : ∀ i ∈ visits, 0 ≤ v i ∧ v i ≤ 1 := by
    intro i hi
    dsimp [v]
    split
    · exact heta i hi
    · norm_num
  have hp0 : 0 ≤ ∏ i ∈ visits, v i := Finset.prod_nonneg (fun i hi => (hv i hi).1)
  have hp1 : (∏ i ∈ visits, v i) ≤ 1 :=
    Finset.prod_le_one₀ (fun i hi => (hv i hi).1) (fun i hi => (hv i hi).2)
  change 0 ≤ 1-(∏ i ∈ visits,v i) ∧ 1-(∏ i ∈ visits,v i) ≤ 1
  constructor <;> linarith

/-- The local loss encodes literal divisibility at n+offset_i. There is no
replacement of the physical integer by an unrelated ratio-fibre variable. -/
theorem b637_physical_path_loss_factor434
    (visits : Finset ℕ) (eta : ℕ → ℝ) (offset : ℕ → ℤ) (p n : ℕ) :
    1-b637PathResidueLoss434 visits eta offset p (n%p) =
      ∏ i ∈ visits, if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1 := by
  simp only [b637PathResidueLoss434,ZMod.natCast_mod,sub_sub_cancel]
  apply Finset.prod_congr rfl
  intro i hi
  have he : ((n:ZMod p)+(offset i:ZMod p)=0) ↔ (p:ℤ) ∣ (n:ℤ)+offset i := by
    simpa only [Int.cast_add,Int.cast_natCast] using
      ZMod.intCast_zmod_eq_zero_iff_dvd ((n:ℤ)+offset i) p
  simp only [he]

private theorem b637_one_sub_product_le (I : Finset ℕ) (v : ℕ → ℝ)
    (hv : ∀ i ∈ I, 0 ≤ v i ∧ v i ≤ 1) :
    1-(∏ i ∈ I, v i) ≤ ∑ i ∈ I, (1-v i) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hvi := hv i (Finset.mem_insert_self _ _)
    have hvI : ∀ j ∈ I, 0 ≤ v j ∧ v j ≤ 1 :=
      fun j hj => hv j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ I, v j) ≤ 1 :=
      Finset.prod_le_one₀ (fun j hj => (hvI j hj).1) (fun j hj => (hvI j hj).2)
    have hh := ih hvI
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    nlinarith [mul_nonneg (sub_nonneg.mpr hvi.2) (sub_nonneg.mpr hprod)]

private theorem b637_range_sum_zmod (p : ℕ) [NeZero p] (f : ℕ → ℝ) :
    (∑ r ∈ Finset.range p, f r) = ∑ r : ZMod p, f r.val := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => exact (Fin.sum_univ_eq_sum_range f (p+1)).symm

/-- Uniform local path budget. It uses the real residues of all visits,
including repeated offsets, and proves lambda_p <= #visits/p. -/
theorem b637_physical_path_residue_budget434
    (visits : Finset ℕ) (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (heta : ∀ i ∈ visits, 0 ≤ eta i ∧ eta i ≤ 1)
    (p : ℕ) (hp : 0 < p) :
    (∀ r, 0 ≤ b637PathResidueLoss434 visits eta offset p r ∧
      b637PathResidueLoss434 visits eta offset p r ≤ 1) ∧
    b637ResidueTotal434 (b637PathResidueLoss434 visits eta offset) p ≤ (visits.card:ℝ) ∧
    0 ≤ b637ResidueMean434 (b637PathResidueLoss434 visits eta offset) p ∧
    b637ResidueMean434 (b637PathResidueLoss434 visits eta offset) p ≤ (visits.card:ℝ)/(p:ℝ) := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hunit := b637_path_loss_unit visits eta offset heta p
  have hsum (i : ℕ) :
      (∑ r ∈ Finset.range p, (1-(if (r:ZMod p)+(offset i:ZMod p)=0 then eta i else 1))) =
        1-eta i := by
    rw [b637_range_sum_zmod]
    simp only [ZMod.natCast_zmod_val]
    have he (r : ZMod p) :
        1-(if r+(offset i:ZMod p)=0 then eta i else 1) =
          if r= -(offset i:ZMod p) then 1-eta i else 0 := by
      by_cases hr : r= -(offset i:ZMod p) <;> simp [add_eq_zero_iff_eq_neg,hr]
    simp_rw [he]
    simp
  have htotal : b637ResidueTotal434 (b637PathResidueLoss434 visits eta offset) p ≤
      (visits.card:ℝ) := by
    calc
      _ ≤ ∑ r ∈ Finset.range p, ∑ i ∈ visits,
          (1-(if (r:ZMod p)+(offset i:ZMod p)=0 then eta i else 1)) := by
        apply Finset.sum_le_sum
        intro r hr
        apply b637_one_sub_product_le
        intro i hi
        split
        · exact heta i hi
        · norm_num
      _ = ∑ i ∈ visits, (1-eta i) := by rw [Finset.sum_comm]; simp_rw [hsum]
      _ ≤ ∑ i ∈ visits, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        linarith [(heta i hi).1]
      _ = _ := by simp
  have htotal0 : 0 ≤ b637ResidueTotal434 (b637PathResidueLoss434 visits eta offset) p :=
    Finset.sum_nonneg (fun r hr => (hunit r).1)
  exact ⟨hunit,htotal,div_nonneg htotal0 (Nat.cast_nonneg p),
    div_le_div_of_nonneg_right htotal (Nat.cast_nonneg p)⟩

/-- Complete quantitative CRT estimate for the literal physical path's
inactive-prime damping and its active root congruence. The prime groups,
visits and every signed offset are unrestricted finite data. -/
theorem b637_physical_path_damping_CRT434
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Q a A B : ℕ) (hQ : 0 < Q) (hAB : A ≤ B)
    (hc : ∀ p ∈ P, Q.Coprime p)
    (visits : Finset ℕ) (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (heta : ∀ i ∈ visits, 0 ≤ eta i ∧ eta i ≤ 1) (K : ℕ) :
    let f := b637PathResidueLoss434 visits eta offset
    |(∑ n ∈ Finset.Ico A B, if Nat.ModEq Q n a then
        ∏ p ∈ P, ∏ i ∈ visits,
          (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1) else 0) -
      ((B-A:ℕ):ℝ)/(Q:ℝ)*(∏ p ∈ P, (1-b637ResidueMean434 f p))| ≤
      ((B-A:ℕ):ℝ)/(Q:ℝ)*
        (Real.exp (2*(∑ p ∈ P, b637ResidueMean434 f p))/(2:ℝ)^(2*K+1)) +
      2*((2*K+2:ℕ):ℝ)*Real.exp 1*
        (1+∑ p ∈ P, b637ResidueTotal434 f p)^(2*K+1) := by
  have h := b637_damped_residue_exponential_error434 P hP Q a A B hQ hAB hc
    (b637PathResidueLoss434 visits eta offset)
    (fun p hp r => b637_path_loss_unit visits eta offset heta p r) K
  simpa only [b637_physical_path_loss_factor434] using h
end Green64Analytic.SourceBlockSieve

end

end

