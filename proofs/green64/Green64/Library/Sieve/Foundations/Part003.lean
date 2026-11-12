module

public import Green64.Library.Analysis.Estimates.PrimeResidueMonomial
public import Green64.Library.Weights.EulerBonferroniError

@[expose] public section

/-!
# Sieve / Foundations / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## DampedResidueCRT -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceSieveBarrier
set_option autoImplicit false
set_option maxHeartbeats 22000000

def b637ResidueTotal434 (f : ℕ → ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ r ∈ Finset.range p, f p r

def b637ResidueMean434 (f : ℕ → ℕ → ℝ) (p : ℕ) : ℝ :=
  b637ResidueTotal434 f p/(p:ℝ)

/-- A genuine quantitative residue-replacement bound for the full damping
product on physical positions with an active congruence. All monomial CRT
errors are proved, and the exact local residue masses are retained.
The last elementary coefficient is the full Bonferroni remainder. -/
theorem b637_damped_residue_product_interval434
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Q a A B : ℕ) (hQ : 0 < Q) (hAB : A ≤ B)
    (hc : ∀ p ∈ P, Q.Coprime p)
    (f : ℕ → ℕ → ℝ) (hf : ∀ p ∈ P, ∀ r, 0 ≤ f p r ∧ f p r ≤ 1)
    (K : ℕ) :
    |(∑ n ∈ Finset.Ico A B,
        if Nat.ModEq Q n a then ∏ p ∈ P, (1-f p (n%p)) else 0) -
      ((B-A:ℕ):ℝ)/(Q:ℝ)*(∏ p ∈ P, (1-b637ResidueMean434 f p))| ≤
      ((B-A:ℕ):ℝ)/(Q:ℝ)*b610Elementary434 P (b637ResidueMean434 f) (2*K+1) +
      2*(∑ j ∈ Finset.range (2*K+2), b610Elementary434 P (b637ResidueTotal434 f) j) := by
  let c : ℝ := ((B-A:ℕ):ℝ)/(Q:ℝ)
  have hc0 : 0 ≤ c := by positivity
  have htot : ∀ p ∈ P, 0 ≤ b637ResidueTotal434 f p := by
    intro p hp
    exact Finset.sum_nonneg (fun r hr => (hf p hp r).1)
  have hmean : ∀ p ∈ P,
      0 ≤ b637ResidueMean434 f p ∧ b637ResidueMean434 f p ≤ 1 := by
    intro p hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast (hP p hp).pos
    have ht : b637ResidueTotal434 f p ≤ (p:ℝ) := by
      calc
        _ ≤ ∑ r ∈ Finset.range p, (1:ℝ) :=
          Finset.sum_le_sum (fun r hr => (hf p hp r).2)
        _ = _ := by simp
    exact ⟨div_nonneg (htot p hp) hp0.le,(div_le_one hp0).mpr ht⟩
  let C : ℕ → ℝ := fun j => ∑ S ∈ P.powersetCard j,
    ∑ n ∈ Finset.Ico A B,
      if Nat.ModEq Q n a then ∏ p ∈ S, f p (n%p) else 0
  let T : ℕ → ℝ := fun R => ∑ j ∈ Finset.range (R+1), (-1:ℝ)^j*C j
  have hC (j : ℕ) :
      |C j-c*b610Elementary434 P (b637ResidueMean434 f) j| ≤
        2*b610Elementary434 P (b637ResidueTotal434 f) j := by
    dsimp only [C,b610Elementary434]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ S ∈ P.powersetCard j,
        |(∑ n ∈ Finset.Ico A B,
          if Nat.ModEq Q n a then ∏ p ∈ S, f p (n%p) else 0) -
          c*(∏ p ∈ S, b637ResidueMean434 f p)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ S ∈ P.powersetCard j,
          2*(∏ p ∈ S, b637ResidueTotal434 f p) := by
        apply Finset.sum_le_sum
        intro S hS
        have hSP := (Finset.mem_powersetCard.mp hS).1
        simpa only [b637ResidueMean434,b637ResidueTotal434,c] using
          b637_active_prime_monomial_interval434 S (fun p hp => hP p (hSP hp))
            Q a A B hQ hAB (fun p hp => hc p (hSP hp)) f
            (fun p hp r => (hf p (hSP hp) r).1)
      _ = _ := by rw [Finset.mul_sum]
  have hTerror (R : ℕ) :
      |T R-c*b610Bonferroni434 P (b637ResidueMean434 f) R| ≤
        2*(∑ j ∈ Finset.range (R+1), b610Elementary434 P (b637ResidueTotal434 f) j) := by
    dsimp only [T,b610Bonferroni434]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    calc
      _ = |∑ j ∈ Finset.range (R+1), (-1:ℝ)^j*
          (C j-c*b610Elementary434 P (b637ResidueMean434 f) j)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ j ∈ Finset.range (R+1), |(-1:ℝ)^j*
          (C j-c*b610Elementary434 P (b637ResidueMean434 f) j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (R+1),
          2*b610Elementary434 P (b637ResidueTotal434 f) j := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hC j
      _ = _ := by rw [Finset.mul_sum]
  have hCpoint (j : ℕ) : C j = ∑ n ∈ Finset.Ico A B,
      if Nat.ModEq Q n a then b610Elementary434 P (fun p => f p (n%p)) j else 0 := by
    dsimp only [C]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases ha : Nat.ModEq Q n a <;> simp [ha,b610Elementary434]
  have hTpoint (R : ℕ) : T R = ∑ n ∈ Finset.Ico A B,
      if Nat.ModEq Q n a then b610Bonferroni434 P (fun p => f p (n%p)) R else 0 := by
    dsimp only [T]
    simp_rw [hCpoint,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases ha : Nat.ModEq Q n a <;> simp [ha,b610Bonferroni434]
  have hsgn0 : (-1:ℝ)^(2*K)=1 := by rw [pow_mul]; norm_num
  have hsgn1 : (-1:ℝ)^(2*K+1)= -1 := by rw [pow_add,hsgn0]; norm_num
  let F : ℝ := ∑ n ∈ Finset.Ico A B,
      if Nat.ModEq Q n a then ∏ p ∈ P, (1-f p (n%p)) else 0
  have hF : T (2*K+1) ≤ F ∧ F ≤ T (2*K) := by
    rw [hTpoint,hTpoint]
    constructor
    · apply Finset.sum_le_sum
      intro n hn
      by_cases ha : Nat.ModEq Q n a
      · simp only [ha,ite_true]
        have hh := (b624_signed_euler_bonferroni_error434 P (fun p => f p (n%p))
          (fun p hp => hf p hp (n%p)) (2*K+1)).1
        rw [hsgn1] at hh
        linarith
      · simp [ha]
    · apply Finset.sum_le_sum
      intro n hn
      by_cases ha : Nat.ModEq Q n a
      · simp only [ha,ite_true]
        have hh := (b624_signed_euler_bonferroni_error434 P (fun p => f p (n%p))
          (fun p hp => hf p hp (n%p)) (2*K)).1
        rw [hsgn0] at hh
        linarith
      · simp [ha]
  have hModel : c*b610Bonferroni434 P (b637ResidueMean434 f) (2*K+1) ≤
      c*(∏ p ∈ P, (1-b637ResidueMean434 f p)) ∧
      c*(∏ p ∈ P, (1-b637ResidueMean434 f p)) ≤
        c*b610Bonferroni434 P (b637ResidueMean434 f) (2*K) := by
    have he := (b624_signed_euler_bonferroni_error434 P _ hmean (2*K)).1
    have ho := (b624_signed_euler_bonferroni_error434 P _ hmean (2*K+1)).1
    rw [hsgn0] at he
    rw [hsgn1] at ho
    exact ⟨mul_le_mul_of_nonneg_left (by linarith) hc0,
      mul_le_mul_of_nonneg_left (by linarith) hc0⟩
  have hgap : c*b610Bonferroni434 P (b637ResidueMean434 f) (2*K) -
      c*b610Bonferroni434 P (b637ResidueMean434 f) (2*K+1) =
        c*b610Elementary434 P (b637ResidueMean434 f) (2*K+1) := by
    have hh := b610_adjacent_bonferroni_difference434 P (b637ResidueMean434 f) (2*K)
    rw [hsgn1] at hh
    calc
      _ = c*(b610Bonferroni434 P (b637ResidueMean434 f) (2*K)-
        b610Bonferroni434 P (b637ResidueMean434 f) (2*K+1)) := by ring
      _ = _ := by congr 1; linarith
  have hEvenError := hTerror (2*K)
  have hOddError := hTerror (2*K+1)
  have hErrorMono :
      2*(∑ j ∈ Finset.range (2*K+1), b610Elementary434 P (b637ResidueTotal434 f) j) ≤
      2*(∑ j ∈ Finset.range (2*K+2), b610Elementary434 P (b637ResidueTotal434 f) j) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.range_mono; omega
    · intro j hj hnj
      exact b610_elementary_nonneg434 P (b637ResidueTotal434 f) htot j
  have he := abs_le.mp (hEvenError.trans hErrorMono)
  have ho := abs_le.mp hOddError
  change |F-c*(∏ p ∈ P, (1-b637ResidueMean434 f p))| ≤ _
  apply abs_le.mpr
  constructor <;> dsimp only [c] at * <;> linarith
end Green64Analytic.SourceBlockSieve

end

end

/-! ## DampedCRTExponential -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceSieveBarrier
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- All finite truncated CRT coefficient masses are bounded at the actual
finite degree. This retains polynomial-in-degree counting, not exp(sum w). -/
theorem b637_truncated_elementary_mass434
    (P : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) (R : ℕ) :
    (∑ j ∈ Finset.range (R+1), b610Elementary434 P w j) ≤
      ((R+1:ℕ):ℝ)*Real.exp 1*(1+∑ p ∈ P, w p)^R := by
  let U : ℝ := 1+∑ p ∈ P, w p
  have hsum0 : 0 ≤ ∑ p ∈ P, w p := Finset.sum_nonneg hw
  have hU1 : 1 ≤ U := by dsimp [U]; linarith
  have hU : 0 < U := lt_of_lt_of_le (by norm_num) hU1
  have ht : 0 < U⁻¹ := inv_pos.mpr hU
  have hscale : U⁻¹*(∑ p ∈ P, w p) ≤ 1 := by
    have hh : (∑ p ∈ P, w p)/U ≤ 1 := (div_le_one hU).mpr (by dsimp [U]; linarith)
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hj (j : ℕ) (hjR : j ≤ R) :
      b610Elementary434 P w j ≤ Real.exp 1*U^R := by
    have hh := b624_elementary_exponential_moment434 P w hw j (U⁻¹) ht.le
    have hbound : b610Elementary434 P w j*(U⁻¹)^j ≤ Real.exp 1 :=
      hh.trans (Real.exp_le_exp.mpr hscale)
    have he : b610Elementary434 P w j ≤ Real.exp 1*U^j := by
      have hd := (le_div_iff₀ (pow_pos ht j)).mpr hbound
      simpa only [inv_pow,div_inv_eq_mul] using hd
    exact he.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU1 hjR) (Real.exp_nonneg _))
  calc
    _ ≤ ∑ j ∈ Finset.range (R+1), Real.exp 1*U^R := by
      apply Finset.sum_le_sum
      intro j hjMem
      exact hj j (Nat.le_of_lt_succ (Finset.mem_range.mp hjMem))
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,U]; ring

/-- Explicit exponentially small Bonferroni term plus complete finite CRT
error for the actual weighted damping product. Every quantity on the right
is computed from the original residue loss functions, with no hCRT input. -/
theorem b637_damped_residue_exponential_error434
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Q a A B : ℕ) (hQ : 0 < Q) (hAB : A ≤ B)
    (hc : ∀ p ∈ P, Q.Coprime p)
    (f : ℕ → ℕ → ℝ) (hf : ∀ p ∈ P, ∀ r, 0 ≤ f p r ∧ f p r ≤ 1)
    (K : ℕ) :
    |(∑ n ∈ Finset.Ico A B,
        if Nat.ModEq Q n a then ∏ p ∈ P, (1-f p (n%p)) else 0) -
      ((B-A:ℕ):ℝ)/(Q:ℝ)*(∏ p ∈ P, (1-b637ResidueMean434 f p))| ≤
      ((B-A:ℕ):ℝ)/(Q:ℝ)*
        (Real.exp (2*(∑ p ∈ P, b637ResidueMean434 f p))/(2:ℝ)^(2*K+1)) +
      2*((2*K+2:ℕ):ℝ)*Real.exp 1*
        (1+∑ p ∈ P, b637ResidueTotal434 f p)^(2*K+1) := by
  have htotal : ∀ p ∈ P, 0 ≤ b637ResidueTotal434 f p := by
    intro p hp
    exact Finset.sum_nonneg (fun r hr => (hf p hp r).1)
  have hmean : ∀ p ∈ P, 0 ≤ b637ResidueMean434 f p := by
    intro p hp
    exact div_nonneg (htotal p hp) (Nat.cast_nonneg p)
  have hm := b624_elementary_exponential_moment434 P (b637ResidueMean434 f)
    hmean (2*K+1) 2 (by norm_num)
  have htail : b610Elementary434 P (b637ResidueMean434 f) (2*K+1) ≤
      Real.exp (2*(∑ p ∈ P, b637ResidueMean434 f p))/(2:ℝ)^(2*K+1) :=
    (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) _)).mpr hm
  have htrunc := b637_truncated_elementary_mass434 P (b637ResidueTotal434 f) htotal (2*K+1)
  have hfinite := b637_damped_residue_product_interval434 P hP Q a A B hQ hAB hc f hf K
  apply hfinite.trans
  have hc0 : (0:ℝ) ≤ ((B-A:ℕ):ℝ)/(Q:ℝ) := by positivity
  have hleft := mul_le_mul_of_nonneg_left htail hc0
  have hright := mul_le_mul_of_nonneg_left htrunc (by norm_num : (0:ℝ) ≤ 2)
  simp only [Nat.add_assoc,one_add_one_eq_two] at hright
  nlinarith only [hleft,hright]
end Green64Analytic.SourceBlockSieve

end

end

