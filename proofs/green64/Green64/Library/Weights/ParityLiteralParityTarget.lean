module

public import Green64.Library.Weights.RoughMarkedInvariance
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville

@[expose] public section

/-!
# Weights / ParityLiteralParityTarget

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ParityLiteralParityTarget -/

section

open ArithmeticFunction
open scoped BigOperators Classical ArithmeticFunction.Omega
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The generic finite-product argument from the existing source parity
owner, ported narrowly to the already-frozen literal definitions. -/
private theorem b628_cardFactors_finset_prod {I : Type} [DecidableEq I]
    (s : Finset I) (f : I → ℕ) (h : ∀ i∈s, f i≠0) :
    Ω (∏ i∈s, f i)=∑ i∈s, Ω (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      cardFactors_mul (h i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj=>h j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj=>h j (Finset.mem_insert_of_mem hj))]

/-- The literal P-prime-power part counts every valuation, including
repeated P primes. This is the exact existing source identity, now checked
in the production closure without importing the old unported mass chain. -/
theorem b628_original_P_part_cardFactors434 (P : Finset ℕ) (u : ℕ) :
    Ω (sourceOriginalPPrimePart P u)=sourceOriginalPParityExponent P u := by
  let S:=u.primeFactors∩P
  have hPrime : ∀p∈S,p.Prime := by
    intro p hp
    exact (Nat.mem_primeFactors.mp (Finset.mem_inter.mp hp).1).1
  have hPow : ∀p∈S,p^u.factorization p≠0 :=
    fun p hp=>pow_ne_zero _ (hPrime p hp).ne_zero
  change Ω (∏p∈S,p^u.factorization p)=∑p∈P,u.factorization p
  rw [b628_cardFactors_finset_prod S _ hPow]
  calc
    (∑p∈S,Ω (p^u.factorization p))=∑p∈S,u.factorization p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact cardFactors_apply_prime_pow (hPrime p hp)
    _=∑p∈P,u.factorization p := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro p hp hn
      have hnot : p∉u.primeFactors := by
        intro hm
        exact hn (Finset.mem_inter.mpr ⟨hm,hp⟩)
      by_cases hprime : p.Prime
      · by_cases hdiv : p∣u
        · by_cases hu : u=0
          · simp [hu]
          · exact False.elim (hnot (Nat.mem_primeFactors.mpr ⟨hprime,hdiv,hu⟩))
        · exact Nat.factorization_eq_zero_of_not_dvd hdiv
      · exact (Nat.factorization_eq_zero_iff u p).2 (Or.inl hprime)

/-- Exact Omega identity on the literal r=20 coefficient support. All
labelled slots, repeated numerical values, and the entire P-valuation sum
are retained. No squarefreeness or prime extraction is assumed. -/
theorem b628_parity_twenty_slot_omega434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (Q : B→Finset ℕ) (P : G→Finset ℕ) (u : ℕ) (hu : u≠0)
    (hQ : ∀b p,p∈Q b→p.Prime)
    (hc : sourceOriginalOrdinaryCoefficient 20 Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u)≠0) :
    Ω u=Fintype.card B*20+
      sourceOriginalPParityExponent (Finset.univ.biUnion P) u := by
  have ht : ∃f : (b:B)→Fin 20→{p // p∈Q b},
      (∏b:B,∏i:Fin 20,(f b i).val)=
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u := by
    by_contra hn
    exact hc (by simp [sourceOriginalOrdinaryCoefficient,hn])
  obtain ⟨f,hf⟩:=ht
  have hfPrime : ∀b i,(f b i).val.Prime := fun b i=>hQ b _ (f b i).property
  have hf0 : ∀b,(∏i:Fin 20,(f b i).val)≠0 :=
    fun b=>Finset.prod_ne_zero_iff.mpr (fun i _=>(hfPrime b i).ne_zero)
  have hOrd : Ω (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u)=
      Fintype.card B*20 := by
    rw [←hf,b628_cardFactors_finset_prod Finset.univ _ (fun b _=>hf0 b)]
    have heach : ∀b,Ω (∏i:Fin 20,(f b i).val)=20 := by
      intro b
      rw [b628_cardFactors_finset_prod Finset.univ _
        (fun i _=>(hfPrime b i).ne_zero)]
      have hs : (∑i:Fin 20,Ω (f b i).val)=∑_i:Fin 20,1 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact cardFactors_apply_prime (hfPrime b i)
      simpa using hs
    simp [heach]
  have ho0 : sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u≠0 := by
    rw [←hf]
    exact Finset.prod_ne_zero_iff.mpr (fun b _=>hf0 b)
  have hp0 : sourceOriginalPPrimePart (Finset.univ.biUnion P) u≠0 :=
    (b613_original_P_part_prime_support434 (Finset.univ.biUnion P) u).1.ne'
  have hsplit : sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u*
      sourceOriginalPPrimePart (Finset.univ.biUnion P) u=u := by
    simpa only [mul_comm] using
      b613_original_P_ordinary_recombine434 (Finset.univ.biUnion P) u hu
  calc
    Ω u=Ω (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u)+
        Ω (sourceOriginalPPrimePart (Finset.univ.biUnion P) u) := by
      rw [←cardFactors_mul ho0 hp0,hsplit]
    _=Fintype.card B*20+
        sourceOriginalPParityExponent (Finset.univ.biUnion P) u := by
      rw [hOrd,b628_original_P_part_cardFactors434]

/-- On the actual ordinary coefficient support, Liouville is precisely
P-only valuation parity. No Liouville factor is introduced on a rough
cofactor in the endpoint core. -/
theorem b628_parity_liouville_equals_P_phase434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (Q : B→Finset ℕ) (P : G→Finset ℕ) (u : ℕ) (hu : u≠0)
    (hQ : ∀b p,p∈Q b→p.Prime)
    (hc : sourceOriginalOrdinaryCoefficient 20 Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u)≠0) :
    ArithmeticFunction.liouville u=
      (-1:ℤ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) u := by
  rw [ArithmeticFunction.liouville_apply hu,
    b628_parity_twenty_slot_omega434 Q P u hu hQ hc,pow_add]
  have he : Even (Fintype.card B*20) :=
    (Nat.even_mul).2 (Or.inr (by decide))
  rw [he.neg_one_pow,one_mul]

/-- The required negative candidate projector gives the unchanged target
membership at p=u+2. This is a pointwise finite theorem, with no analytic
positive-mass, infinitude, E-correlation, or sieve premise hidden in it. -/
theorem b628_parity_negative_candidate_exact_target434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (Q : B→Finset ℕ) (P : G→Finset ℕ) (u : ℕ)
    (hQ : ∀b p,p∈Q b→p.Prime)
    (hA : 0<sourceOriginalA 20 Q P u) (hp : (u+2).Prime) :
    ArithmeticFunction.liouville u = -1 ∧
      (u+2)∈{p:ℕ | p.Prime ∧ Odd (Ω (p-2))} := by
  have hPodd : Odd (sourceOriginalPParityExponent (Finset.univ.biUnion P) u) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hz : sourceOriginalA 20 Q P u=0 := by
      simp [sourceOriginalA,he.neg_one_pow]
    linarith
  have hu : u≠0 := by
    intro hz
    simp [hz,sourceOriginalPParityExponent] at hPodd
  have hc : sourceOriginalOrdinaryCoefficient 20 Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u)≠0 := by
    intro hz
    have ha0 : sourceOriginalA 20 Q P u=0 := by
      simp [sourceOriginalA,sourceOriginalA0,hz]
    linarith
  have hOmega:=b628_parity_twenty_slot_omega434 Q P u hu hQ hc
  have he : Even (Fintype.card B*20) :=
    (Nat.even_mul).2 (Or.inr (by decide))
  have hOdd : Odd (Ω u) := by rw [hOmega];exact he.add_odd hPodd
  refine ⟨?_,hp,?_⟩
  · rw [ArithmeticFunction.liouville_apply hu,hOdd.neg_one_pow]
  · simpa using hOdd

/-- The epsilon in E is P-only. Removing W-rough endpoint cofactors
preserves both literal valuation exponents and their signed product. The
cofactors' full Liouville values are irrelevant and are not asserted to be 1. -/
theorem b628_parity_rough_endpoint_P_twist434
    (P : Finset ℕ) (W : ℝ) (m mp H Hp : ℕ)
    (hprime : ∀p∈P,p.Prime) (hbelow : ∀p∈P,(p:ℝ)≤W)
    (hm : sourceD20Rough W m) (hmp : sourceD20Rough W mp)
    (hH : 0<H) (hHp : 0<Hp) :
    sourceOriginalPParityExponent P (m*H)=sourceOriginalPParityExponent P H ∧
    sourceOriginalPParityExponent P (mp*Hp)=sourceOriginalPParityExponent P Hp ∧
    (-1:ℂ)^sourceOriginalPParityExponent P (m*H)*
      (-1:ℂ)^sourceOriginalPParityExponent P (mp*Hp)=
        (-1:ℂ)^sourceOriginalPParityExponent P H*
          (-1:ℂ)^sourceOriginalPParityExponent P Hp := by
  have avoid : ∀n,sourceD20Rough W n→∀p∈P,¬p∣n := by
    intro n hn p hp hdiv
    have hmin : (n.minFac:ℝ)≤(p:ℝ) := by
      exact_mod_cast Nat.minFac_le_of_dvd (hprime p hp).two_le hdiv
    exact (not_lt_of_ge (hmin.trans (hbelow p hp))) hn.2
  have hm0 : 0 < m := by have:=hm.1;omega
  have hmp0 : 0 < mp := by have:=hmp.1;omega
  have ha:=(b618_original_P_ordinary_mul434 P m H hm0 hH (avoid m hm)).2.2
  have hb:=(b618_original_P_ordinary_mul434 P mp Hp hmp0 hHp (avoid mp hmp)).2.2
  exact ⟨ha,hb,by rw [ha,hb]⟩

end Green64Analytic.Parity

end

end

