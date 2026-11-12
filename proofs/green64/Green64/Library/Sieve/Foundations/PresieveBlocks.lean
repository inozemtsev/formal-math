module

public import Green64.Library.Weights.Part108
public import Green64.Library.Analysis.Estimates.Part002

@[expose] public section

/-!
# Sieve / Foundations / PresieveBlocks

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualPresieveBlocks -/

section

/-! Native 4.34.1 port of the actual prime blocks used by the original
h = -2 source initial presieve. The finite depth may depend on L; the
weighted block sieve has a single injectively encoded remainder sum. -/
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
open Filter Real Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
/-- An ACTUAL finite alphabet of odd natural primes in the
geometric half-power block, excluding every prime dividing D.
No abstract block-membership assumption is needed. -/
noncomputable def sourceNaturalOddPrimeBlock
    (D : ℕ) (z : ℝ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 3 ⌊z⌋₊).filter (fun p =>
    p.Prime ∧ D.Coprime p ∧
    z^((1/2:ℝ)^(j+1)) < (p:ℝ) ∧
    (p:ℝ) ≤ z^((1/2:ℝ)^j))

theorem source_natural_block_prime
    (D : ℕ) (z : ℝ) (j : ℕ) (p : ℕ)
    (hp : p ∈ sourceNaturalOddPrimeBlock D z j) :
    p.Prime ∧ z^((1/2:ℝ)^(j+1)) < (p:ℝ) ∧
      (p:ℝ) ≤ z^((1/2:ℝ)^j) := by
  have hh := (Finset.mem_filter.mp hp).2
  exact ⟨hh.1,hh.2.2⟩

theorem source_natural_block_odd
    (D : ℕ) (z : ℝ) (j : ℕ) (p : ℕ)
    (hp : p ∈ sourceNaturalOddPrimeBlock D z j) :
    3 ≤ p := by
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1

theorem source_natural_block_coprime
    (D : ℕ) (z : ℝ) (j : ℕ) (p : ℕ)
    (hp : p ∈ sourceNaturalOddPrimeBlock D z j) :
    D.Coprime p := (Finset.mem_filter.mp hp).2.2.1

/-- The complete source odd prime alphabet, before exclusion of p|D. -/
noncomputable def sourceAllOddPrimeSet (z : ℝ) : Finset ℕ :=
  (Finset.Icc 3 ⌊z⌋₊).filter Nat.Prime

/-- Elementary discrete crossing of the half-power thresholds. -/
private theorem source_halfpower_cross :
    ∀ (f : ℕ → ℝ) (p : ℝ) (J : ℕ),
    p ≤ f 0 → f J < p →
    ∃ j, j < J ∧ f (j+1) < p ∧ p ≤ f j := by
  intro f p J
  induction J with
  | zero =>
    intro h0 hJ
    exact False.elim ((not_lt_of_ge h0) hJ)
  | succ J ih =>
    intro h0 hJ
    by_cases hp : p ≤ f J
    · exact ⟨J, Nat.lt_succ_self J, hJ, hp⟩
    · obtain ⟨j,hj,hl,hu⟩ := ih h0 (lt_of_not_ge hp)
      exact ⟨j, Nat.lt_succ_of_lt hj,hl,hu⟩

/-- Every odd prime p≤z coprime to the true assignment modulus
appears in the NATURAL sieve blocks when the final block is below 3.
This proves literal coverage without abstract prime alphabets. -/
theorem source_natural_blocks_cover_coprime
    (J D : ℕ) (z : ℝ) (hz : 1 < z)
    (hLast : z ^ ((1/2:ℝ)^J) < 3)
    (p : ℕ) (hp : p ∈ sourceAllOddPrimeSet z)
    (hCop : D.Coprime p) :
    p ∈ Finset.univ.biUnion
        (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val) := by
  classical
  have hmem := Finset.mem_filter.mp hp
  have hpI : p ∈ Finset.Icc 3 ⌊z⌋₊ := hmem.1
  have hpz : (p:ℝ) ≤ z := by
    have hf : (p:ℝ) ≤ ⌊z⌋₊ := by
      exact_mod_cast (Finset.mem_Icc.mp hpI).2
    exact hf.trans (Nat.floor_le (by linarith : 0 ≤ z))
  have hp3 : (3:ℝ) ≤ p := by
    exact_mod_cast (Finset.mem_Icc.mp hpI).1
  have h0 : (p:ℝ) ≤ z ^ ((1/2:ℝ)^0) := by
    simpa using hpz
  obtain ⟨j,hj,hl,hu⟩ :=
    source_halfpower_cross (fun j => z ^ ((1/2:ℝ)^j))
      (p:ℝ) J h0 (lt_of_lt_of_le hLast hp3)
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨j,hj⟩,Finset.mem_univ _,?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨hpI,hmem.2,hCop,hl,hu⟩

/-- Every actually used odd prime is in the full odd range. -/
theorem source_natural_blocks_subset_all_odd
    (J D : ℕ) (z : ℝ) :
    Finset.univ.biUnion
      (fun j : Fin J => sourceNaturalOddPrimeBlock D z j.val) ⊆
        sourceAllOddPrimeSet z := by
  classical
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨j,hj,hpj⟩
  have h := Finset.mem_filter.mp hpj
  exact Finset.mem_filter.mpr ⟨h.1,h.2.1⟩

/-- The genuine natural-prime blocks with modulus D=1 cover EVERY odd
prime up to z as soon as their last geometric threshold is below 3. -/
theorem source_natural_unit_blocks_cover_all_odd_primes
    (J : ℕ) (z : ℝ) (hz : 1 < z)
    (hLast : z^((1/2:ℝ)^J) < 3) :
    (Finset.univ.biUnion (fun j : Fin J =>
      sourceNaturalOddPrimeBlock 1 z j.val)) = sourceAllOddPrimeSet z := by
  apply Finset.Subset.antisymm
  · exact source_natural_blocks_subset_all_odd J 1 z
  · intro p hp
    exact source_natural_blocks_cover_coprime J 1 z hz hLast p hp
      (by simp)

/-- Every z>1 admits a finite last half-power block below the first odd
prime. The integer block count can be chosen later as z varies. -/
theorem source_exists_natural_halfpower_depth
    (z : ℝ) (hz : 1 < z) :
    ∃ J : ℕ, z^((1/2:ℝ)^J) < 3 := by
  have hpow : Tendsto (fun J : ℕ => (1/2:ℝ)^J) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzc : Tendsto (fun J : ℕ => z^((1/2:ℝ)^J)) atTop (𝓝 1) := by
    have hcont : ContinuousAt (fun a : ℝ => z ^ a) (0:ℝ) :=
      Real.continuousAt_const_rpow (ne_of_gt (by linarith : 0 < z))
    simpa only [Real.rpow_zero, Function.comp_def] using hcont.tendsto.comp hpow
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1
    (hzc.eventually_lt_const (by norm_num : (1:ℝ) < 3))
  exact ⟨N,hN N (le_refl _)⟩

/-- Unconditional reciprocal prime mass in any exact half-power
dyadic block of the imported h=2 block sieve. -/
theorem source_dyadic_prime_mass_le_four
    (z : ℝ) (j : ℕ) (s : Finset ℕ)
    (hz : 1 < z)
    (hp : ∀ p ∈ s, Nat.Prime p ∧
      z^((1/2:ℝ)^(j+1)) < (p:ℝ) ∧
      (p:ℝ) ≤ z^((1/2:ℝ)^j)) :
    (∑ p ∈ s, (p:ℝ)⁻¹) ≤ 4 := by
  have hw : 1 < z^((1/2:ℝ)^(j+1)) :=
    Real.one_lt_rpow hz (by positivity)
  have he : (z^((1/2:ℝ)^(j+1)))^2 =
      z^((1/2:ℝ)^j) := by
    calc
      _ = (z^((1/2:ℝ)^(j+1)))^(2:ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = z^(((1/2:ℝ)^(j+1))*(2:ℝ)) :=
        (Real.rpow_mul (by linarith : 0 ≤ z) _ _).symm
      _ = _ := by congr 1; rw [pow_succ]; ring
  apply source_quadratic_prime_reciprocal_le_four _ s hw
  intro p hps
  exact ⟨(hp p hps).1,(hp p hps).2.1,
      he.symm ▸ (hp p hps).2.2⟩

/-- Actual shifted density 1/(p-1) is at most twice the prime reciprocal. -/
theorem source_shift_two_local_density_le_two_reciprocal
    (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    sourceShiftTwoLocalDensity p ≤ 2*(p:ℝ)⁻¹ := by
  have hpr : (3:ℝ) ≤ p := by exact_mod_cast h3
  have hpos : (0:ℝ) < p := by linarith
  have hden : (0:ℝ) < (p:ℝ)-1 := by linarith
  have hnz : (p:ℝ) ≠ 0 := ne_of_gt hpos
  have hdenz : (p:ℝ)-1 ≠ 0 := ne_of_gt hden
  rw [sourceShiftTwoLocalDensity, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  have hh : (1:ℝ)/((p:ℝ)-1) ≤ 2/(p:ℝ) := by
    apply (div_le_div_iff₀ hden hpos).mpr
    nlinarith
  simpa only [one_div, div_eq_mul_inv, one_mul] using hh

/-- A UNIVERSAL block-mass constant B=8, valid for ALL actual
source half-power prime blocks and all sieve levels z>1. -/
theorem source_shift_two_block_local_density_le_eight
    (z : ℝ) (hz : 1 < z) (J : ℕ)
    (blocks : Fin J → Finset ℕ)
    (hp : ∀ j p, p ∈ blocks j → p.Prime ∧ 3 ≤ p ∧
      z^((1/2:ℝ)^(j.val+1)) < (p:ℝ) ∧
      (p:ℝ) ≤ z^((1/2:ℝ)^j.val)) :
    ∀ j, (∑ p ∈ blocks j, sourceShiftTwoLocalDensity p) ≤ 8 := by
  intro j
  have hM : (∑ p ∈ blocks j, (p:ℝ)⁻¹) ≤ 4 :=
    source_dyadic_prime_mass_le_four z j.val (blocks j) hz
      (fun p hpj =>
        ⟨(hp j p hpj).1,(hp j p hpj).2.2⟩)
  calc
    (∑ p ∈ blocks j, sourceShiftTwoLocalDensity p) ≤
      ∑ p ∈ blocks j, 2*(p:ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hpm
        exact source_shift_two_local_density_le_two_reciprocal p
          (hp j p hpm).1 (hp j p hpm).2.1
    _ = 2*(∑ p ∈ blocks j, (p:ℝ)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ 8 := by linarith

/-- Actual block-sieve divisors are all odd, and their actual sizes lie
in the congruence range when the sieve level does. -/
theorem source_shift_two_block_divisors_in_range
    (P : Finset ℕ) (L z θ : ℝ) (h : ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ 3 ≤ p)
    (hlevel : z^(4*(h : ℝ)+2) ≤ (Real.exp L)^θ) :
    ((∏ p ∈ P, p).divisors.filter
      (fun d : ℕ => Squarefree d ∧ (d : ℝ) ≤ z^(4*(h : ℝ)+2))) ⊆
      (Finset.range (⌊(Real.exp L)^θ⌋₊+1)).filter
        (fun d => Odd d ∧ Squarefree d) := by
  classical
  have hOdd : Odd (∏ p ∈ P, p) := by
    apply Nat.coprime_two_right.mp
    apply Nat.Coprime.prod_left
    intro p hpm
    apply Nat.coprime_two_right.mpr
    exact (hp p hpm).1.odd_of_ne_two (by have := (hp p hpm).2; omega)
  intro d hd
  have h := Finset.mem_filter.mp hd
  have hdiv := (Nat.mem_divisors.mp h.1).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, hOdd.of_dvd_nat hdiv, h.2.1⟩
  have hdle : d ≤ ⌊(Real.exp L)^θ⌋₊ := Nat.le_floor (h.2.2.trans hlevel)
  omega

end Green64Analytic.SourceBlockSieve

end

