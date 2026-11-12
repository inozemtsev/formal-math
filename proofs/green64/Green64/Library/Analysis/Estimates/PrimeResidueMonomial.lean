module

public import Green64.Library.Sieve.Foundations.WeightedCRTInterval

@[expose] public section

/-!
# Analysis / Estimates / PrimeResidueMonomial

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PrimeResidueMonomial -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 16000000

private theorem b637_sum_residue_val (p : ℕ) [NeZero p] (f : ℕ → ℝ) :
    (∑ r : ZMod p, f r.val) = ∑ r ∈ Finset.range p, f r := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => exact Fin.sum_univ_eq_sum_range f (p+1)


/-- Literal monomial CRT with the active congruence kept in the SAME
integer variable. P can be any remaining prime subset. The active modulus
Q may have prime powers; no independence of physical positions is assumed. -/
theorem b637_active_prime_monomial_interval434
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Q a A B : ℕ) (hQ : 0 < Q) (hAB : A ≤ B)
    (hc : ∀ p ∈ P, Q.Coprime p)
    (f : ℕ → ℕ → ℝ) (hf : ∀ p ∈ P, ∀ r, 0 ≤ f p r) :
    |(∑ n ∈ Finset.Ico A B,
        if Nat.ModEq Q n a then ∏ p ∈ P, f p (n%p) else 0) -
      ((B-A:ℕ):ℝ)/(Q:ℝ)*
        (∏ p ∈ P, (∑ r ∈ Finset.range p, f p r)/(p:ℝ))| ≤
      2*(∏ p ∈ P, ∑ r ∈ Finset.range p, f p r) := by
  let : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  let (p : P) : NeZero p.val := ⟨(hP p.val p.property).ne_zero⟩
  let q : Option P → ℕ := fun i => match i with
    | none => Q
    | some p => p.val
  let instQ : ∀ i, NeZero (q i) := by
    intro i
    cases i with
    | none => exact ⟨Nat.ne_of_gt hQ⟩
    | some p => exact ⟨(hP p.val p.property).ne_zero⟩
  let w : (i : Option P) → ZMod (q i) → ℝ := fun i =>
    match i with
    | none => fun r => if r=(a : ZMod Q) then 1 else 0
    | some p => fun r => f p.val r.val
  have hq : Pairwise (fun i j => (q i).Coprime (q j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some p => exact hc p.val p.property
    | some p =>
      cases j with
      | none => exact (hc p.val p.property).symm
      | some t =>
        apply (hP p.val p.property).coprime_iff_not_dvd.mpr
        intro hdiv
        have heq := (hP t.val t.property).eq_one_or_self_of_dvd p.val hdiv
        rcases heq with h1 | hpq
        · exact (hP p.val p.property).ne_one h1
        · exact hij (congrArg some (Subtype.ext hpq))
  have hw : ∀ i r, 0 ≤ w i r := by
    intro i r
    cases i with
    | none => dsimp [w]; split <;> norm_num
    | some p => exact hf p.val p.property r.val
  have hnat (n : ℕ) : (∏ i : Option P, w i (n : ZMod (q i))) =
      if Nat.ModEq Q n a then ∏ p ∈ P, f p (n%p) else 0 := by
    rw [Fintype.prod_option]
    change (if (n:ZMod Q)=(a:ZMod Q) then (1:ℝ) else 0)*
      (∏ p : P, f p.val (n:ZMod p.val).val) = _
    simp only [ZMod.natCast_eq_natCast_iff,ZMod.val_natCast]
    rw [Finset.prod_coe_sort P (fun p : ℕ => f p (n%p))]
    split <;> simp_all

  have hsum : (∏ i : Option P, ∑ r : ZMod (q i), w i r) =
      ∏ p ∈ P, ∑ r ∈ Finset.range p, f p r := by
    rw [Fintype.prod_option]
    change (∑ r : ZMod Q, if r=(a:ZMod Q) then (1:ℝ) else 0)*
      (∏ p : P, ∑ r : ZMod p.val, f p.val r.val) = _
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,one_mul]
    simp_rw [b637_sum_residue_val]
    exact Finset.prod_coe_sort P (fun p : ℕ => ∑ r ∈ Finset.range p, f p r)

  have hmod : (∏ i : Option P, (q i:ℝ)) = (Q:ℝ)*(∏ p ∈ P, (p:ℝ)) := by
    rw [Fintype.prod_option]
    change (Q:ℝ)*(∏ p : P, (p.val:ℝ)) = _
    rw [Finset.prod_coe_sort P]
  have h := b637_weighted_crt_interval434 q hq A B hAB w hw
  simp only [hnat,hsum,hmod] at h
  rw [Finset.prod_div_distrib]
  simpa only [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm] using h
end Green64Analytic.SourceBlockSieve

end

end

