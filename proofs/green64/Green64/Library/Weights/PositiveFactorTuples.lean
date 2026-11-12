module

public import Mathlib

@[expose] public section

/-!
# Weights / PositiveFactorTuples

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PositiveFactorTuples -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceDivisorMoment

set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- All positive ordered r-tuples with each entry at most N.
No squarefree or distinct-entry condition is imposed. -/
def b594PositiveTuples (r N : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun _ => Finset.Ioc 0 N)

/-- The exact product fibre of the full ordered positive tuple carrier. -/
def b594FactorTuples (r N n : ℕ) : Finset (Fin r → ℕ) :=
  (b594PositiveTuples r N).filter (fun x => ∏ i, x i = n)

@[simp] theorem b594_mem_positiveTuples434
    {r N : ℕ} {x : Fin r → ℕ} :
    x ∈ b594PositiveTuples r N ↔ ∀ i, 0 < x i ∧ x i ≤ N := by
  simp [b594PositiveTuples, Fintype.mem_piFinset]

@[simp] theorem b594_mem_factorTuples434
    {r N n : ℕ} {x : Fin r → ℕ} :
    x ∈ b594FactorTuples r N n ↔
      (∀ i, 0 < x i ∧ x i ≤ N) ∧ ∏ i, x i = n := by
  simp [b594FactorTuples]

theorem b594_positive_tuple_product434
    {r N : ℕ} {x : Fin r → ℕ} (hx : x ∈ b594PositiveTuples r N) :
    0 < ∏ i, x i := by
  apply Finset.prod_pos
  intro i hi
  exact (b594_mem_positiveTuples434.mp hx i).1

private theorem b594_factor_succ_card (r N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    (b594FactorTuples (r+1) N n).card =
      ∑ d ∈ n.divisors, (b594FactorTuples r N d).card := by
  rw [← Finset.card_sigma]
  symm
  apply Finset.card_bij (fun a _ => Fin.cons (n/a.1) a.2)
  · rintro ⟨d,y⟩ ha
    rcases Finset.mem_sigma.mp ha with ⟨hd,hy⟩
    rcases b594_mem_factorTuples434.mp hy with ⟨hypos,hyprod⟩
    have hdn := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hdivpos : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
    apply b594_mem_factorTuples434.mpr
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact ⟨hdivpos, (Nat.div_le_self n d).trans hnN⟩
      · simpa using hypos j
    · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hyprod]
      exact Nat.div_mul_cancel hdn
  · rintro ⟨d,y⟩ ha ⟨e,z⟩ hb he
    have hy : (∏ i, y i) = d := (b594_mem_factorTuples434.mp (Finset.mem_sigma.mp ha).2).2
    have hz : (∏ i, z i) = e := (b594_mem_factorTuples434.mp (Finset.mem_sigma.mp hb).2).2
    have hyz : y = z := (Fin.cons_inj.mp he).2
    have hde : d = e := by rw [← hy, ← hz, hyz]
    cases hde
    cases hyz
    rfl
  · intro x hx
    rcases b594_mem_factorTuples434.mp hx with ⟨hxpos,hxprod⟩
    let d := ∏ i : Fin r, x i.succ
    have hdpos : 0 < d := Finset.prod_pos (fun i _ => (hxpos i.succ).1)
    have hmul : x 0 * d = n := by
      simpa only [Fin.prod_univ_succ] using hxprod
    have hdvd : d ∣ n := ⟨x 0, by simpa [Nat.mul_comm] using hmul.symm⟩
    have hd : d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdvd, Nat.ne_of_gt hn⟩
    have hy : (fun i : Fin r => x i.succ) ∈ b594FactorTuples r N d :=
      b594_mem_factorTuples434.mpr ⟨fun i => hxpos i.succ, rfl⟩
    refine ⟨⟨d,fun i : Fin r => x i.succ⟩, Finset.mem_sigma.mpr ⟨hd,hy⟩, ?_⟩
    have hhead : n/d = x 0 := by rw [← hmul]; exact Nat.mul_div_cancel _ hdpos
    rw [hhead]
    exact Fin.cons_self_tail x

/-- Ordered factorization multiplicity is exactly the actual Dirichlet
power of zeta. The full bounded carrier contains every factorization
because 0<n≤N; repeated prime factors and repeated coordinates remain. -/
theorem b594_factor_tuple_card_zeta434
    (r N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    (b594FactorTuples r N n).card = (ArithmeticFunction.zeta^r) n := by
  induction r generalizing n with
  | zero =>
    by_cases h : n = 1 <;> simp [b594FactorTuples, b594PositiveTuples, h, eq_comm]
  | succ r ih =>
    rw [b594_factor_succ_card r N n hn hnN]
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn := (Nat.mem_divisors.mp hd).1
    exact ih d (Nat.pos_of_dvd_of_pos hdn hn) ((Nat.le_of_dvd hn hdn).trans hnN)


/-- Exact regrouping of every ordered positive tuple by its numerical
product. The weight is arbitrary: positivity is not assumed or used. -/
theorem b594_tuple_sum_by_product434
    (r N B : ℕ) (hBN : B ≤ N) (f : ℕ → ℝ) :
    (∑ x ∈ (b594PositiveTuples r N).filter (fun x => (∏ i, x i) ≤ B),
      f (∏ i, x i)) =
      ∑ n ∈ Finset.Ioc 0 B, ((ArithmeticFunction.zeta^r) n : ℝ) * f n := by
  let S := (b594PositiveTuples r N).filter (fun x => (∏ i, x i) ≤ B)
  have hmap : ∀ x ∈ S, (∏ i, x i) ∈ Finset.Ioc 0 B := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx,hB⟩
    exact Finset.mem_Ioc.mpr ⟨b594_positive_tuple_product434 hx,hB⟩
  change (∑ x ∈ S, f (∏ i, x i)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun x => f (∏ i, x i))]
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_Ioc.mp hn with ⟨hnpos,hnB⟩
  have hf : S.filter (fun x => (∏ i, x i) = n) = b594FactorTuples r N n := by
    ext x
    simp only [S, b594FactorTuples, Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨hx.1.1,hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, by simpa only [hx.2] using hnB⟩,hx.2⟩
  rw [hf]
  calc
    (∑ x ∈ b594FactorTuples r N n, f (∏ i, x i)) =
        ∑ _x ∈ b594FactorTuples r N n, f n := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(b594_mem_factorTuples434.mp hx).2]
    _ = ((ArithmeticFunction.zeta^r) n : ℝ) * f n := by
      rw [Finset.sum_const, nsmul_eq_mul,
        b594_factor_tuple_card_zeta434 r N n hnpos (hnB.trans hBN)]

/-- The full ordered tuple count in an actual residue class, including
all repeated factors, is the corresponding zeta-power progression sum. -/
theorem b594_tuple_progression_card434
    (r N q a : ℕ) :
    ((b594PositiveTuples r N).filter
      (fun x => (∏ i, x i) ≤ N ∧ Nat.ModEq q (∏ i, x i) a)).card =
      ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => Nat.ModEq q n a),
        (ArithmeticFunction.zeta^r) n := by
  let S := (b594PositiveTuples r N).filter
    (fun x => (∏ i, x i) ≤ N ∧ Nat.ModEq q (∏ i, x i) a)
  let T := (Finset.Ioc 0 N).filter (fun n => Nat.ModEq q n a)
  have hmap : ∀ x ∈ S, (∏ i, x i) ∈ T := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx,hN,hres⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨b594_positive_tuple_product434 hx,hN⟩,hres⟩
  change S.card = ∑ n ∈ T, _
  have hcard : S.card = ∑ _x ∈ S, (1:ℕ) := by simp
  rw [hcard]
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1:ℕ))]
  apply Finset.sum_congr rfl
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn,hres⟩
  rcases Finset.mem_Ioc.mp hn with ⟨hnpos,hnN⟩
  have hf : S.filter (fun x => (∏ i, x i) = n) = b594FactorTuples r N n := by
    ext x
    simp only [S, b594FactorTuples, Finset.mem_filter]
    constructor
    · intro hx
      exact ⟨hx.1.1,hx.2⟩
    · intro hx
      exact ⟨⟨hx.1, by simpa only [hx.2] using And.intro hnN hres⟩,hx.2⟩
  rw [hf]
  simpa using b594_factor_tuple_card_zeta434 r N n hnpos hnN

end Green64Analytic.SourceDivisorMoment

end

end

