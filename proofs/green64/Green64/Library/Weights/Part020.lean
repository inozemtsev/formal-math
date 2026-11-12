module

public import Green64.Library.Weights.Part019
public import Mathlib
public import Green64.Library.Analysis.Estimates.Part004
public import Green64.Library.Weights.Part013
public import Green64.Library.Weights.Part012
public import Green64.Library.Correlation.Part002
public import Mathlib.Tactic.Ring
public import Green64.Library.Analysis.Estimates.Part002

@[expose] public section

/-!
# Weights / Part020

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePOriginalAllGroupCount -/

section

set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- TRUE source P-group count: all indices with BOTH endpoint tests,
not a hypothetical small group type or a j≤j_x restriction. -/
theorem source_original_P_all_group_card_log
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (hL : Real.exp 1 ≤ L) :
    ((sourceOriginalPAllGroupIndices r₀ L).card:ℝ) ≤
      (3 + (Real.log 2)⁻¹) * Real.log L := by
  classical
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using h
  let N : ℕ := sourceOriginalPAllIndexBound L
  have hNat : (sourceOriginalPAllGroupIndices r₀ L).card ≤ N := by
    dsimp [sourceOriginalPAllGroupIndices]
    simpa [Finset.card_range, N] using
      (Finset.card_filter_le (Finset.range (sourceOriginalPAllIndexBound L))
        (sourceOriginalPGroupIndex r₀ L))
  have hReal : ((sourceOriginalPAllGroupIndices r₀ L).card:ℝ) ≤ N := by
    exact_mod_cast hNat
  have harg : 0 ≤ 2 + Real.log L / Real.log 2 := by
    have h := div_nonneg (by linarith : 0 ≤ Real.log L) (le_of_lt h2)
    linarith
  have hceil : (N:ℝ) < 3 + Real.log L / Real.log 2 := by
    have h := Nat.ceil_lt_add_one harg
    change (N:ℝ) < (2 + Real.log L / Real.log 2) + 1 at h
    linarith
  calc
    ((sourceOriginalPAllGroupIndices r₀ L).card:ℝ) ≤ N := hReal
    _ ≤ 3 + Real.log L / Real.log 2 := le_of_lt hceil
    _ = 3 + (Real.log 2)⁻¹ * Real.log L := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ 3 * Real.log L + (Real.log 2)⁻¹ * Real.log L := by
      nlinarith
    _ = (3 + (Real.log 2)⁻¹) * Real.log L := by ring

end Green64Analytic.SourceBlockSieve

end

/-! ## SourcePOriginalAllPolylogFactor -/

section

set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Actual source P-band group type, with the original all-index predicate. -/
abbrev sourceOriginalPAllGroupType (r₀ : ℕ) (L : ℝ) : Type :=
  {j : ℕ // j ∈ sourceOriginalPAllGroupIndices r₀ L}

/-- Uniform fixed-exponent polylog bound for the REAL source group count. -/
theorem source_original_P_all_group_factor_polylog
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (hL : Real.exp 1 ≤ L) :
    (6 * Real.exp 12) ^ (Fintype.card (sourceOriginalPAllGroupType r₀ L)) ≤
      L ^ ((3 + (Real.log 2)⁻¹) * Real.log (6 * Real.exp 12)) := by
  let G := sourceOriginalPAllGroupType r₀ L
  let B : ℝ := 6 * Real.exp 12
  let C : ℝ := 3 + (Real.log 2)⁻¹
  have hLpos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hB : 1 < B := by
    have he : 1 ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
    dsimp [B]
    nlinarith
  have hBpos : 0 < B := by linarith
  have hBlog : 0 ≤ Real.log B := le_of_lt (Real.log_pos hB)
  have hCard : ((Fintype.card G : ℝ)) ≤ C * Real.log L := by
    change ((Fintype.card (sourceOriginalPAllGroupType r₀ L):ℝ)) ≤ _
    rw [show Fintype.card (sourceOriginalPAllGroupType r₀ L) =
      (sourceOriginalPAllGroupIndices r₀ L).card from Fintype.card_coe _]
    exact source_original_P_all_group_card_log r₀ L hr₀ hL
  have hExpBound : Real.log B * (Fintype.card G:ℝ) ≤
      Real.log L * (C * Real.log B) := by
    calc
      Real.log B * (Fintype.card G:ℝ) ≤
          Real.log B * (C * Real.log L) :=
            mul_le_mul_of_nonneg_left hCard hBlog
      _ = Real.log L * (C * Real.log B) := by ring
  change B ^ (Fintype.card G) ≤ L ^ (C * Real.log B)
  calc
    B ^ (Fintype.card G) = B ^ ((Fintype.card G:ℝ)) :=
      (Real.rpow_natCast B _).symm
    _ = Real.exp (Real.log B * (Fintype.card G:ℝ)) :=
      Real.rpow_def_of_pos hBpos _
    _ ≤ Real.exp (Real.log L * (C * Real.log B)) :=
      Real.exp_le_exp.mpr hExpBound
    _ = L ^ (C * Real.log B) :=
      (Real.rpow_def_of_pos hLpos _).symm

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceProductAtomMass -/

section

namespace Green64SourceC6

/-- Literal source support with marked group multiplicities. -/
def sourceAtomValid {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (n : ℕ) : Prop :=
  n ≠ 0 ∧
    (∀ g ∈ G, (∑ p ∈ S g, Nat.factorization n p) = k g) ∧
    (∀ p ∈ n.primeFactors, p ∈ G.biUnion S)

/-- Factorials account exactly for repeated selected group primes. -/
noncomputable def sourceAtomMultiplicityFactor
    {γ : Type*} (S : γ → Finset ℕ) (g : γ) (n : ℕ) : ℝ :=
  ∏ p ∈ S g, ((Nat.factorial (Nat.factorization n p) : ℕ) : ℝ)

/-- One group: k_g!/(V_g^k_g prod_p v_p(n)!). -/
noncomputable def sourceAtomGroupFactor
    {γ : Type*} (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ) (g : γ) (n : ℕ) : ℝ :=
  ((Nat.factorial (k g) : ℕ) : ℝ) /
    (V g ^ (k g) * sourceAtomMultiplicityFactor S g n)

/-- Product atom law exactly in sh:product-atoms,
zero on illegal supports. -/
noncomputable def sourceProductAtomMass
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if sourceAtomValid G S k n then
    (1/(n:ℝ)) * ∏ g ∈ G, sourceAtomGroupFactor S k V g n
  else 0

/-- Source log-power prefactor. Controlling its size in x is
a separate quantitative group-parameter obligation. -/
noncomputable def sourceProductAtomPrefactor
    {γ : Type*} (G : Finset γ) (k : γ → ℕ)
    (V : γ → ℝ) : ℝ :=
  ∏ g ∈ G, (((Nat.factorial (k g) : ℕ) : ℝ) / (V g)^(k g))

/-- Every multiplicity factorial is at least one. -/
theorem source_atom_multiplicity_ge_one
    {γ : Type*} (S : γ → Finset ℕ) (g : γ) (n : ℕ) :
    1 ≤ sourceAtomMultiplicityFactor S g n := by
  unfold sourceAtomMultiplicityFactor
  calc
    (1:ℝ) = ∏ p ∈ S g, (1:ℝ) := by simp
    _ ≤ ∏ p ∈ S g,
      ((Nat.factorial (Nat.factorization n p) : ℕ) : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        norm_num
      · intro p hp
        have h : 1 ≤ Nat.factorial (Nat.factorization n p) := by
          have hp := Nat.factorial_pos (Nat.factorization n p)
          omega
        exact_mod_cast h

theorem source_atom_group_bound
    {γ : Type*} (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ) (g : γ) (n : ℕ)
    (hV : 0 < V g) :
    0 ≤ sourceAtomGroupFactor S k V g n ∧
    sourceAtomGroupFactor S k V g n ≤
      (((Nat.factorial (k g) : ℕ) : ℝ) / (V g)^(k g)) := by
  have hvpow : 0 < V g ^ (k g) := pow_pos hV _
  have hm := source_atom_multiplicity_ge_one S g n
  have hden : V g ^ (k g) ≤
      V g ^ (k g) * sourceAtomMultiplicityFactor S g n := by
    nlinarith [mul_le_mul_of_nonneg_left hm hvpow.le]
  have hpden : 0 < V g ^ (k g) *
      sourceAtomMultiplicityFactor S g n := by
    exact mul_pos hvpow (lt_of_lt_of_le (by norm_num) hm)
  constructor
  · unfold sourceAtomGroupFactor
    positivity
  · unfold sourceAtomGroupFactor
    exact div_le_div_of_nonneg_left
      (by positivity) hvpow hden

/-- Pointwise source reciprocal product-atom envelope, with its
actual repeated-prime factorial formula, no independence shortcut. -/
theorem source_product_atom_pointwise
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (hV : ∀ g ∈ G, 0 < V g) (n : ℕ) :
    0 ≤ sourceProductAtomMass G S k V n ∧
    sourceProductAtomMass G S k V n ≤
      (1/(n:ℝ)) * sourceProductAtomPrefactor G k V := by
  classical
  have hf : ∀ g ∈ G, 0 ≤ sourceAtomGroupFactor S k V g n := by
    intro g hg
    exact (source_atom_group_bound S k V g n (hV g hg)).1
  have he : ∀ g ∈ G,
      sourceAtomGroupFactor S k V g n ≤
        (((Nat.factorial (k g) : ℕ) : ℝ)/(V g)^(k g)) := by
    intro g hg
    exact (source_atom_group_bound S k V g n (hV g hg)).2
  have hprod := Finset.prod_le_prod₀ hf he
  have hprod0 : 0 ≤ sourceProductAtomPrefactor G k V := by
    unfold sourceProductAtomPrefactor
    apply Finset.prod_nonneg
    intro g hg
    have hv := hV g hg
    positivity
  by_cases hv : sourceAtomValid G S k n
  · have hleft : 0 ≤ (1/(n:ℝ)) *
        ∏ g ∈ G, sourceAtomGroupFactor S k V g n := by
      apply mul_nonneg (by positivity)
      exact Finset.prod_nonneg hf
    have hright : (1/(n:ℝ)) *
        ∏ g ∈ G, sourceAtomGroupFactor S k V g n ≤
        (1/(n:ℝ)) * sourceProductAtomPrefactor G k V := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sourceProductAtomPrefactor] using hprod
    simpa only [sourceProductAtomMass, if_pos hv] using
      (And.intro hleft hright)
  · have hz : (0:ℝ) ≤ (1/(n:ℝ)) *
        sourceProductAtomPrefactor G k V :=
      mul_nonneg (by positivity) hprod0
    simpa only [sourceProductAtomMass, if_neg hv] using
      (And.intro (le_refl (0:ℝ)) hz)

end Green64SourceC6

end

/-! ## SourceMultinomialCounts -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- Literal multinomial count-vector distribution for source groups,
including repeated prime labels. -/
noncomputable def sourceMultinomialCountMass
    (S : Finset ℕ) (k : ℕ) (V : ℝ) (v : ℕ → ℕ) : ℝ :=
  (Nat.multinomial S v : ℝ) *
    ∏ p ∈ S, ((1/(p:ℝ))/V) ^ (v p)

/-- Count-vector probabilities sum to one, for every number of slots. -/
theorem source_multinomial_count_normalized
    (S : Finset ℕ) (k : ℕ) (V : ℝ)
    (hV : V = ∑ p ∈ S, (1/(p:ℝ)))
    (hVp : 0 < V) :
    (∑ v ∈ S.piAntidiag k, sourceMultinomialCountMass S k V v) = 1 := by
  have hVnorm : (∑ p ∈ S, ((1/(p:ℝ))/V)) = 1 := by
    rw [← Finset.sum_div, ← hV]
    exact div_self hVp.ne'
  calc
    (∑ v ∈ S.piAntidiag k, sourceMultinomialCountMass S k V v) =
        (∑ p ∈ S, ((1/(p:ℝ))/V)) ^ k := by
          simpa only [sourceMultinomialCountMass] using
            (Finset.sum_pow_eq_sum_piAntidiag S
              (fun p : ℕ => ((1/(p:ℝ))/V)) k).symm
    _ = 1 := by rw [hVnorm]; simp
end Green64SourceC6

end

/-! ## SourceMultinomialFactorial -/

section

namespace Green64SourceC6
open scoped BigOperators

noncomputable def sourceCountProduct (S : Finset ℕ)
    (v : ℕ → ℕ) : ℕ :=
  ∏ p ∈ S, p ^ v p

theorem source_multinomial_factorial
    (S : Finset ℕ) (k : ℕ) (v : ℕ → ℕ)
    (hv : v ∈ S.piAntidiag k) :
    (Nat.multinomial S v : ℝ) =
      (Nat.factorial k : ℝ) /
        (∏ p ∈ S, ((Nat.factorial (v p) : ℕ) : ℝ)) := by
  have hsum : (∑ p ∈ S, v p) = k :=
    (Finset.mem_piAntidiag.mp hv).1
  have hspec := Nat.multinomial_spec S v
  rw [hsum] at hspec
  have hreal :
      (∏ p ∈ S, ((Nat.factorial (v p) : ℕ) : ℝ)) *
        (Nat.multinomial S v : ℝ) = (Nat.factorial k : ℝ) := by
    exact_mod_cast hspec
  have hpos : 0 <
      (∏ p ∈ S, ((Nat.factorial (v p) : ℕ) : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast Nat.factorial_pos (v p)
  exact (eq_div_iff hpos.ne').mpr (by
    simpa only [mul_comm] using hreal)

theorem source_multinomial_reciprocal_product
    (S : Finset ℕ) (k : ℕ) (V : ℝ) (v : ℕ → ℕ)
    (hv : v ∈ S.piAntidiag k) :
    (∏ p ∈ S, ((1/(p:ℝ))/V) ^ v p) =
      (1/(sourceCountProduct S v : ℝ)) / V^k := by
  have hsum : (∑ p ∈ S, v p) = k :=
    (Finset.mem_piAntidiag.mp hv).1
  calc
    (∏ p ∈ S, ((1/(p:ℝ))/V) ^ v p) =
      (∏ p ∈ S, (1/(p:ℝ)) ^ v p) /
        (∏ p ∈ S, V ^ v p) := by
          simp_rw [div_pow]
          exact Finset.prod_div_distrib _ _
    _ = (1/(sourceCountProduct S v : ℝ)) / V^k := by
      simp only [one_div, inv_pow, Finset.prod_inv_distrib,
        Finset.prod_pow_eq_pow_sum, hsum,
        sourceCountProduct, Nat.cast_prod, Nat.cast_pow]

theorem source_multinomial_count_factorial_density
    (S : Finset ℕ) (k : ℕ) (V : ℝ) (v : ℕ → ℕ)
    (hv : v ∈ S.piAntidiag k) :
    sourceMultinomialCountMass S k V v =
      (1/(sourceCountProduct S v : ℝ)) *
        ((Nat.factorial k : ℝ) /
        (V^k * ∏ p ∈ S, ((Nat.factorial (v p) : ℕ) : ℝ))) := by
  unfold sourceMultinomialCountMass
  rw [source_multinomial_factorial S k v hv,
      source_multinomial_reciprocal_product S k V v hv]
  ring
end Green64SourceC6

end

/-! ## SourceCountFactorization -/

section

namespace Green64SourceC6
open scoped BigOperators

theorem source_count_product_factorization
    (S : Finset ℕ) (k : ℕ) (v : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hv : v ∈ S.piAntidiag k) :
    (sourceCountProduct S v).factorization =
      Finsupp.onFinset S v (Finset.mem_piAntidiag.mp hv).2 := by
  let hsupp := (Finset.mem_piAntidiag.mp hv).2
  let f : ℕ →₀ ℕ := Finsupp.onFinset S v hsupp
  have hfprime : ∀ p ∈ f.support, Nat.Prime p := by
    intro p hp
    exact hprime p (Finsupp.support_onFinset_subset hp)
  have heq : f.prod (fun p e => p ^ e) = sourceCountProduct S v := by
    exact Finsupp.prod_onFinset S v hsupp (fun p e => p ^ e)
      (by intro p hp; simp [pow_zero])
  rw [← heq]
  exact Nat.prod_pow_factorization_eq_self hfprime

theorem source_count_product_factorization_at
    (S : Finset ℕ) (k : ℕ) (v : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hv : v ∈ S.piAntidiag k) (p : ℕ) :
    (sourceCountProduct S v).factorization p = v p := by
  rw [source_count_product_factorization S k v hprime hv]
  exact Finsupp.onFinset_apply

theorem source_count_product_injective
    (S : Finset ℕ) (k : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    Set.InjOn (sourceCountProduct S) (S.piAntidiag k) := by
  intro v hv w hw heq
  funext p
  have h1 := source_count_product_factorization_at S k v hprime hv p
  have h2 := source_count_product_factorization_at S k w hprime hw p
  rw [heq] at h1
  exact h1.symm.trans h2

theorem source_count_product_pos
    (S : Finset ℕ) (k : ℕ) (v : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hv : v ∈ S.piAntidiag k) :
    0 < sourceCountProduct S v := by
  unfold sourceCountProduct
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (hprime p hp).pos _
end Green64SourceC6

end

/-! ## SourceOneGroupAtom -/

section

namespace Green64SourceC6
open scoped BigOperators

noncomputable def sourceOneGroupMass (S : Finset ℕ)
    (k : ℕ) (V : ℝ) (n : ℕ) : ℝ :=
  sourceProductAtomMass ({()} : Finset Unit)
    (fun _ => S) (fun _ => k) (fun _ => V) n

theorem source_count_product_one_group_valid
    (S : Finset ℕ) (k : ℕ) (v : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hv : v ∈ S.piAntidiag k) :
    sourceAtomValid ({()} : Finset Unit)
      (fun _ => S) (fun _ => k) (sourceCountProduct S v) := by
  have hpos := source_count_product_pos S k v hprime hv
  have hfac := source_count_product_factorization S k v hprime hv
  have hsum : (∑ p ∈ S, (sourceCountProduct S v).factorization p) = k := by
    simp_rw [source_count_product_factorization_at S k v hprime hv]
    exact (Finset.mem_piAntidiag.mp hv).1
  have hprimes : ∀ p ∈ (sourceCountProduct S v).primeFactors, p ∈ S := by
    intro p hp
    rw [← Nat.support_factorization, hfac] at hp
    exact Finsupp.support_onFinset_subset hp
  unfold sourceAtomValid
  refine ⟨Nat.ne_of_gt hpos, ?_, ?_⟩
  · intro g hg
    exact hsum
  · intro p hp
    simpa using hprimes p hp

theorem source_one_group_atom_eq_multinomial
    (S : Finset ℕ) (k : ℕ) (V : ℝ) (v : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hv : v ∈ S.piAntidiag k) :
    sourceOneGroupMass S k V (sourceCountProduct S v) =
      sourceMultinomialCountMass S k V v := by
  have hvalid := source_count_product_one_group_valid S k v hprime hv
  rw [source_multinomial_count_factorial_density S k V v hv]
  simp only [sourceOneGroupMass, sourceProductAtomMass,
    if_pos hvalid, Finset.prod_singleton, sourceAtomGroupFactor,
    sourceAtomMultiplicityFactor]
  congr 1
  simp_rw [source_count_product_factorization_at S k v hprime hv]
end Green64SourceC6

end

/-! ## SourceOneGroupSupport -/

section

namespace Green64SourceC6
open scoped BigOperators

theorem source_one_group_valid_iff_count_image
    (S : Finset ℕ) (k : ℕ) (n : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    sourceAtomValid ({()} : Finset Unit)
      (fun _ => S) (fun _ => k) n ↔
      n ∈ (S.piAntidiag k).image (sourceCountProduct S) := by
  classical
  constructor
  · intro hv
    rcases hv with ⟨hn, hk, hp⟩
    let v : ℕ → ℕ := fun p => n.factorization p
    have hsum : (∑ p ∈ S, v p) = k := by
      apply hk ()
      simp
    have hsupport : ∀ p, v p ≠ 0 → p ∈ S := by
      intro p h
      have hs : p ∈ n.primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr h
      have hx := hp p hs
      simpa using hx
    have hmem : v ∈ S.piAntidiag k :=
      Finset.mem_piAntidiag.mpr ⟨hsum, hsupport⟩
    have hfactorS : n.factorization.support ⊆ S := by
      intro p h
      exact hsupport p ((Finsupp.mem_support_iff).mp h)
    have heq : sourceCountProduct S v = n := by
      calc
        sourceCountProduct S v = ∏ p ∈ S, p ^ n.factorization p := rfl
        _ = n.factorization.prod (fun p e => p ^ e) := by
          exact (Finsupp.prod_of_support_subset n.factorization hfactorS
            (fun p e => p ^ e) (by intro p hp; simp)).symm
        _ = n := Nat.prod_factorization_pow_eq_self hn
    exact Finset.mem_image.mpr ⟨v, hmem, heq⟩
  · intro hn
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hn
    rw [← heq]
    exact source_count_product_one_group_valid S k v hprime hv
end Green64SourceC6

end

/-! ## SourceOneGroupNormalized -/

section

namespace Green64SourceC6
open scoped BigOperators

theorem source_one_group_atom_full_normalized
    (S : Finset ℕ) (k : ℕ) (V : ℝ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hV : V = ∑ p ∈ S, (1/(p:ℝ)))
    (hVp : 0 < V) :
    (∑ n ∈ (S.piAntidiag k).image (sourceCountProduct S),
      sourceOneGroupMass S k V n) = 1 := by
  classical
  calc
    (∑ n ∈ (S.piAntidiag k).image (sourceCountProduct S),
      sourceOneGroupMass S k V n) =
      ∑ v ∈ S.piAntidiag k,
        sourceOneGroupMass S k V (sourceCountProduct S v) :=
          Finset.sum_image (source_count_product_injective S k hprime)
    _ = ∑ v ∈ S.piAntidiag k,
        sourceMultinomialCountMass S k V v := by
          apply Finset.sum_congr rfl
          intro v hv
          exact source_one_group_atom_eq_multinomial S k V v hprime hv
    _ = 1 := source_multinomial_count_normalized S k V hV hVp

theorem source_one_group_atom_marginal_normalized
    (S F : Finset ℕ) (k : ℕ) (V : ℝ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hV : V = ∑ p ∈ S, (1/(p:ℝ)))
    (hVp : 0 < V) :
    (∑ n ∈ F, sourceOneGroupMass S k V n) ≤ 1 := by
  classical
  let T := (S.piAntidiag k).image (sourceCountProduct S)
  have hzero (n : ℕ) (hn : n ∉ T) :
      sourceOneGroupMass S k V n = 0 := by
    have hnvalid : ¬sourceAtomValid ({()} : Finset Unit)
        (fun _ => S) (fun _ => k) n := by
      intro hvalid
      exact hn ((source_one_group_valid_iff_count_image
        S k n hprime).mp hvalid)
    simp only [sourceOneGroupMass, sourceProductAtomMass,
      if_neg hnvalid]
  have hnonneg (n : ℕ) : 0 ≤ sourceOneGroupMass S k V n := by
    exact (source_product_atom_pointwise
      ({()} : Finset Unit) (fun _ => S) (fun _ => k) (fun _ => V)
      (by intro g hg; exact hVp) n).1
  have heq :
      (∑ n ∈ F, sourceOneGroupMass S k V n) =
      ∑ n ∈ F.filter (fun n => n ∈ T), sourceOneGroupMass S k V n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hx : n ∈ T
    · simp [hx]
    · simp [hx, hzero n hx]
  have hsubset : F.filter (fun n => n ∈ T) ⊆ T := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  calc
    (∑ n ∈ F, sourceOneGroupMass S k V n) =
      ∑ n ∈ F.filter (fun n => n ∈ T), sourceOneGroupMass S k V n := heq
    _ ≤ ∑ n ∈ T, sourceOneGroupMass S k V n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n hn hnot => hnonneg n)
    _ = 1 := source_one_group_atom_full_normalized S k V hprime hV hVp
end Green64SourceC6

end

/-! ## SourceProductAtomL2 -/

section

namespace Green64SourceC6

/-- For the *literal source multinomial product atom*, every normalized
finite marginal in [U,∞) has L² ≤ prefactor/U, with any bounded
complex test b. The normalization is explicit until a source-group
probability construction is imported. -/
theorem source_product_atom_l2
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (hV : ∀ g ∈ G, 0 < V g)
    (s : Finset ℕ) (U : ℕ) (hU : 0 < U)
    (hsupport : ∀ n ∈ s, U ≤ n)
    (b : ℕ → ℂ) (hb : ∀ n ∈ s, ‖b n‖ ≤ 1)
    (hnorm : (∑ n ∈ s, sourceProductAtomMass G S k V n) ≤ 1) :
    (∑ n ∈ s,
       ‖((sourceProductAtomMass G S k V n : ℝ) : ℂ)*b n‖^2) ≤
      sourceProductAtomPrefactor G k V / (U:ℝ) := by
  let μ := sourceProductAtomMass G S k V
  let C := sourceProductAtomPrefactor G k V
  have hUreal : (0:ℝ) < (U:ℝ) := by exact_mod_cast hU
  have hC : 0 ≤ C := by
    unfold C sourceProductAtomPrefactor
    apply Finset.prod_nonneg
    intro g hg
    have hv := hV g hg
    positivity
  have hbound (n : ℕ) (hn : n ∈ s) :
      0 ≤ μ n ∧ μ n ≤ C/(U:ℝ) := by
    have h := source_product_atom_pointwise G S k V hV n
    have hUn : (U:ℝ) ≤ (n:ℝ) := by
      exact_mod_cast hsupport n hn
    have hc : (1/(n:ℝ))*C ≤ C/(U:ℝ) := by
      have ht := div_le_div_of_nonneg_left hC hUreal hUn
      simpa [div_eq_mul_inv, mul_comm] using ht
    exact ⟨h.1, h.2.trans hc⟩
  have hpoint (n : ℕ) (hn : n ∈ s) :
      ‖((μ n : ℝ) : ℂ)*b n‖^2 ≤ (C/(U:ℝ))*μ n := by
    obtain ⟨hmu0,hmuc⟩ := hbound n hn
    have hb0 : 0 ≤ ‖b n‖ := norm_nonneg _
    have hb2 : ‖b n‖^2 ≤ 1 := by
      have h := hb n hn
      nlinarith [sq_nonneg (‖b n‖)]
    have heq : ‖((μ n : ℝ) : ℂ)*b n‖^2 =
        (μ n)^2 * ‖b n‖^2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hmu0]
      ring
    have hmuSq : (μ n)^2 ≤ (C/(U:ℝ))*μ n := by
      nlinarith [mul_nonneg hmu0 (sub_nonneg.mpr hmuc)]
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hb2 (sq_nonneg (μ n))]
  have hsum : (∑ n ∈ s, ‖((μ n : ℝ) : ℂ)*b n‖^2) ≤
        (∑ n ∈ s, (C/(U:ℝ))*μ n) := by
    apply Finset.sum_le_sum
    intro n hn
    exact hpoint n hn
  have hdiv0 : 0 ≤ C/(U:ℝ) := div_nonneg hC hUreal.le
  calc
    _ ≤ (∑ n ∈ s, (C/(U:ℝ))*μ n) := hsum
    _ = (C/(U:ℝ)) * (∑ n ∈ s, μ n) := by
      rw [Finset.mul_sum]
    _ ≤ C/(U:ℝ) := by
      exact (mul_le_mul_of_nonneg_left hnorm hdiv0).trans_eq
        (mul_one _)

end Green64SourceC6

end

/-! ## SourceProductAtomRangeL2 -/

section

namespace Green64SourceC6

/-- The literal source product-atom coefficients on a translated
containing interval (zeros included) have their expected reciprocal
length L² scale, conditional only on the actual atom law's normalization. -/
theorem source_product_atom_cell_l2
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (hV : ∀ g ∈ G, 0 < V g)
    (M P : ℕ) (hM : 0 < M)
    (b : ℕ → ℂ)
    (hb : ∀ n ∈ Finset.Ico M (M+P), ‖b n‖ ≤ 1)
    (hnorm : (∑ n ∈ Finset.Ico M (M+P),
        sourceProductAtomMass G S k V n) ≤ 1) :
    (∑ i ∈ Finset.range P,
      ‖((sourceProductAtomMass G S k V (M+i):ℝ):ℂ)*b (M+i)‖^2) ≤
        sourceProductAtomPrefactor G k V/(M:ℝ) := by
  have h := source_product_atom_l2 G S k V hV
    (Finset.Ico M (M+P)) M hM
    (by intro n hn; exact (Finset.mem_Ico.mp hn).1)
    b hb hnorm
  rw [Finset.sum_Ico_eq_sum_range] at h
  simpa only [Nat.add_sub_cancel_left] using h

end Green64SourceC6

end

/-! ## SourceProductAtomMultiplier -/

section

namespace Green64SourceC6

/-- The source multiplier of TWO genuine multinomial free-product
atoms on translated integer containing cells, with the original complex
orientation. Normalization of the underlying source atom probability
distributions is an explicit bridge premise, not silently assumed. -/
theorem source_product_atom_multiplier
    {γ₁ γ₂ : Type*} [DecidableEq γ₁] [DecidableEq γ₂]
    (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ)
    (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
    (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ)
    (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ)
    (hv₁ : ∀ g ∈ G₁, 0 < V₁ g)
    (hv₂ : ∀ g ∈ G₂, 0 < V₂ g)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (b₁ b₂ : ℕ → ℂ)
    (hb₁ : ∀ n ∈ Finset.Ico M (M+P), ‖b₁ n‖ ≤ 1)
    (hb₂ : ∀ n ∈ Finset.Ico N (N+Q), ‖b₂ n‖ ≤ 1)
    (hn₁ : (∑ n ∈ Finset.Ico M (M+P),
      sourceProductAtomMass G₁ S₁ k₁ V₁ n) ≤ 1)
    (hn₂ : (∑ n ∈ Finset.Ico N (N+Q),
      sourceProductAtomMass G₂ S₂ k₂ V₂ n) ≤ 1)
    (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    ‖∑ i ∈ Finset.range P,
      (((sourceProductAtomMass G₁ S₁ k₁ V₁ (M+i):ℝ):ℂ) * b₁ (M+i)) *
      (∑ j ∈ Finset.range Q,
        (((sourceProductAtomMass G₂ S₂ k₂ V₂ (N+j):ℝ):ℂ) * b₂ (N+j)) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta) * ((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ))‖ ≤
      5 * Real.sqrt (sourceProductAtomPrefactor G₁ k₁ V₁/(M:ℝ)) *
          Real.sqrt (sourceProductAtomPrefactor G₂ k₂ V₂/(N:ℝ)) *
          Real.sqrt ((P:ℝ) + (1+(Q:ℝ)/(r:ℝ)) *
            ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) := by
  let A : ℤ → ℂ := fun z =>
    ((sourceProductAtomMass G₁ S₁ k₁ V₁ z.toNat:ℝ):ℂ)*b₁ z.toNat
  let B : ℤ → ℂ := fun z =>
    ((sourceProductAtomMass G₂ S₂ k₂ V₂ z.toNat:ℝ):ℂ)*b₂ z.toNat
  have hnatM (i : ℕ) : ((M:ℤ)+(i:ℤ)).toNat = M+i := by omega
  have hnatN (j : ℕ) : ((N:ℤ)+(j:ℤ)).toNat = N+j := by omega
  have hA : (∑ i ∈ Finset.range P,
      ‖A ((M:ℤ)+(i:ℤ))‖^2) ≤
       sourceProductAtomPrefactor G₁ k₁ V₁/(M:ℝ) := by
    have h := source_product_atom_cell_l2
      G₁ S₁ k₁ V₁ hv₁ M P hM b₁ hb₁ hn₁
    simpa only [A, hnatM] using h
  have hB : (∑ j ∈ Finset.range Q,
      ‖B ((N:ℤ)+(j:ℤ))‖^2) ≤
       sourceProductAtomPrefactor G₂ k₂ V₂/(N:ℝ) := by
    have h := source_product_atom_cell_l2
      G₂ S₂ k₂ V₂ hv₂ N Q hN b₂ hb₂ hn₂
    simpa only [B, hnatN] using h
  have hmain := source_integer_bilinear_minor_arc
    a r P Q beta (M:ℤ) (N:ℤ) A B hr hcop hbeta
  have hAroot := Real.sqrt_le_sqrt hA
  have hBroot := Real.sqrt_le_sqrt hB
  have hnorm : ‖∑ i ∈ Finset.range P,
      A ((M:ℤ)+(i:ℤ)) *
      (∑ j ∈ Finset.range Q,
        B ((N:ℤ)+(j:ℤ)) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta) *
          (((N:ℤ)+(j:ℤ)):ℝ)) ((M:ℤ)+(i:ℤ)))‖ ≤
      5 * Real.sqrt (sourceProductAtomPrefactor G₁ k₁ V₁/(M:ℝ)) *
          Real.sqrt (sourceProductAtomPrefactor G₂ k₂ V₂/(N:ℝ)) *
          Real.sqrt ((P:ℝ)+(1+(Q:ℝ)/(r:ℝ)) *
            ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) := by
    calc
      _ ≤ 5 * Real.sqrt (∑ i ∈ Finset.range P,
              ‖A ((M:ℤ)+(i:ℤ))‖^2) *
            Real.sqrt (∑ j ∈ Finset.range Q,
              ‖B ((N:ℤ)+(j:ℤ))‖^2) *
            Real.sqrt ((P:ℝ)+(1+(Q:ℝ)/(r:ℝ)) *
              ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) := hmain
      _ ≤ _ := by
        gcongr
  simpa only [A, B, hnatM, hnatN, Int.cast_add, Int.cast_natCast,
    Nat.cast_add] using hnorm

end Green64SourceC6

end

/-! ## SourceActualMultiplier -/

section

namespace Green64SourceC6

/-- Source product-atom C6 multiplier in the exact four-term squared
minor-arc form for dyadic containing intervals. Only the original
probability normalization and bounded test weights remain assumptions.
The atom formula and C6 themselves are proven, not hypotheses. -/
theorem source_actual_product_atom_four_term_sq
    {γ₁ γ₂ : Type*} [DecidableEq γ₁] [DecidableEq γ₂]
    (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ)
    (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
    (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ)
    (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ)
    (hv₁ : ∀ g ∈ G₁, 0 < V₁ g)
    (hv₂ : ∀ g ∈ G₂, 0 < V₂ g)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (b₁ b₂ : ℕ → ℂ)
    (hb₁ : ∀ n ∈ Finset.Ico M (M+P), ‖b₁ n‖ ≤ 1)
    (hb₂ : ∀ n ∈ Finset.Ico N (N+Q), ‖b₂ n‖ ≤ 1)
    (hn₁ : (∑ n ∈ Finset.Ico M (M+P),
      sourceProductAtomMass G₁ S₁ k₁ V₁ n) ≤ 1)
    (hn₂ : (∑ n ∈ Finset.Ico N (N+Q),
      sourceProductAtomMass G₂ S₂ k₂ V₂ n) ≤ 1)
    (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    ‖∑ i ∈ Finset.range P,
      (((sourceProductAtomMass G₁ S₁ k₁ V₁ (M+i):ℝ):ℂ) * b₁ (M+i)) *
      (∑ j ∈ Finset.range Q,
        (((sourceProductAtomMass G₂ S₂ k₂ V₂ (N+j):ℝ):ℂ) * b₂ (N+j)) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta) * ((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ))‖^2 ≤
      50*sourceProductAtomPrefactor G₁ k₁ V₁*
         sourceProductAtomPrefactor G₂ k₂ V₂*
      (1/(N:ℝ)+1/(r:ℝ)+
        Real.log (2*(r:ℝ))/(M:ℝ)+
        (r:ℝ)*Real.log (2*(r:ℝ))/((M:ℝ)*(N:ℝ))) := by
  let X : ℝ := sourceProductAtomPrefactor G₁ k₁ V₁
  let Y : ℝ := sourceProductAtomPrefactor G₂ k₂ V₂
  let T : ℝ := (P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
    ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))
  let U : ℝ := (1/(N:ℝ)+1/(r:ℝ)+Real.log (2*(r:ℝ))/(M:ℝ)+
    (r:ℝ)*Real.log (2*(r:ℝ))/((M:ℝ)*(N:ℝ)))
  let E : ℂ := ∑ i ∈ Finset.range P,
      (((sourceProductAtomMass G₁ S₁ k₁ V₁ (M+i):ℝ):ℂ) * b₁ (M+i)) *
      (∑ j ∈ Finset.range Q,
        (((sourceProductAtomMass G₂ S₂ k₂ V₂ (N+j):ℝ):ℂ) * b₂ (N+j)) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta) * ((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ))
  have hX : 0 ≤ X := by
    dsimp [X,sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    have := hv₁ g hg
    positivity
  have hY : 0 ≤ Y := by
    dsimp [Y,sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    have := hv₂ g hg
    positivity
  have hmain : ‖E‖ ≤
      5 * Real.sqrt (X/(M:ℝ)) * Real.sqrt (Y/(N:ℝ)) *
        Real.sqrt T := by
    simpa only [E,X,Y,T] using
      source_product_atom_multiplier G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
      hv₁ hv₂ M N P Q hM hN b₁ b₂ hb₁ hb₂ hn₁ hn₂
      a r beta hr hcop hbeta
  have hscaled : ‖E‖^2 ≤ 50 * X * Y * U := by
    exact normalized_c6_four_term_sq (‖E‖) X Y (P:ℝ) (Q:ℝ)
      (M:ℝ) (N:ℝ) (r:ℝ) hX hY (by positivity) (by positivity)
      (by exact_mod_cast hM) (by exact_mod_cast hN)
      (by exact_mod_cast hr) (by exact_mod_cast hP)
      (by exact_mod_cast hQ) (norm_nonneg _) (by simpa [T] using hmain)
  simpa only [E,X,Y,U] using hscaled
end Green64SourceC6

end

/-! ## SourceOneGroupC6 -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- Fully physical C6 multiplier for two source one-group product atom
laws. Its normalization is proved, not assumed, at every dyadic cell. -/
theorem source_one_group_product_atom_four_term_sq
    (S₁ S₂ : Finset ℕ) (k₁ k₂ M N P Q : ℕ)
    (V₁ V₂ : ℝ)
    (hp₁ : ∀ p ∈ S₁, Nat.Prime p)
    (hp₂ : ∀ p ∈ S₂, Nat.Prime p)
    (hV₁ : V₁ = ∑ p ∈ S₁, (1/(p:ℝ)))
    (hV₂ : V₂ = ∑ p ∈ S₂, (1/(p:ℝ)))
    (hv₁ : 0 < V₁) (hv₂ : 0 < V₂)
    (hM : 0 < M) (hN : 0 < N) (hP : P ≤ M) (hQ : Q ≤ N)
    (b₁ b₂ : ℕ → ℂ)
    (hb₁ : ∀ n ∈ Finset.Ico M (M+P), ‖b₁ n‖ ≤ 1)
    (hb₂ : ∀ n ∈ Finset.Ico N (N+Q), ‖b₂ n‖ ≤ 1)
    (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    ‖∑ i ∈ Finset.range P,
      (((sourceOneGroupMass S₁ k₁ V₁ (M+i):ℝ):ℂ) * b₁ (M+i)) *
      (∑ j ∈ Finset.range Q,
        (((sourceOneGroupMass S₂ k₂ V₂ (N+j):ℝ):ℂ) * b₂ (N+j)) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta) * ((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ))‖^2 ≤
      50 * ((Nat.factorial k₁ : ℝ)/V₁^k₁) *
           ((Nat.factorial k₂ : ℝ)/V₂^k₂) *
      (1/(N:ℝ)+1/(r:ℝ)+
        Real.log (2*(r:ℝ))/(M:ℝ)+
        (r:ℝ)*Real.log (2*(r:ℝ))/((M:ℝ)*(N:ℝ))) := by
  have hn₁ : (∑ n ∈ Finset.Ico M (M+P),
      sourceProductAtomMass ({()} : Finset Unit)
        (fun _ => S₁) (fun _ => k₁) (fun _ => V₁) n) ≤ 1 := by
    exact source_one_group_atom_marginal_normalized
      S₁ (Finset.Ico M (M+P)) k₁ V₁ hp₁ hV₁ hv₁
  have hn₂ : (∑ n ∈ Finset.Ico N (N+Q),
      sourceProductAtomMass ({()} : Finset Unit)
        (fun _ => S₂) (fun _ => k₂) (fun _ => V₂) n) ≤ 1 := by
    exact source_one_group_atom_marginal_normalized
      S₂ (Finset.Ico N (N+Q)) k₂ V₂ hp₂ hV₂ hv₂
  have h := source_actual_product_atom_four_term_sq
    ({()} : Finset Unit) (fun _ => S₁) (fun _ => k₁) (fun _ => V₁)
    ({()} : Finset Unit) (fun _ => S₂) (fun _ => k₂) (fun _ => V₂)
    (by intro g hg; exact hv₁) (by intro g hg; exact hv₂)
    M N P Q hM hN hP hQ b₁ b₂ hb₁ hb₂ hn₁ hn₂
    a r beta hr hcop hbeta
  simpa only [sourceOneGroupMass, sourceProductAtomPrefactor,
    Finset.prod_singleton] using h
end Green64SourceC6

end

/-! ## SourceMultiGroupCounts -/

section

namespace Green64SourceC6
open scoped BigOperators
open Green64Analytic.SourceAtomLabels

/-- Source group count-vectors include repeats, with prescribed slot
count k_g. The multinomial numerator handles ordering exactly. -/
abbrev sourceGroupCountSpace (S : Finset ℕ) (k : ℕ) :=
  {v : ℕ → ℕ // v ∈ S.piAntidiag k}

noncomputable def sourceMultigroupCountMass
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (v : ∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)) : ℝ :=
  ∏ g : G, sourceMultinomialCountMass
    (S g.val) (k g.val) (V g.val) (v g).val

noncomputable def sourceMultigroupCountProduct
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (v : ∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)) : ℕ :=
  ∏ g : G, sourceCountProduct (S g.val) (v g).val

theorem source_multigroup_count_normalized
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (hV : ∀ g ∈ G, V g = ∑ p ∈ S g, (1/(p:ℝ)))
    (hVp : ∀ g ∈ G, 0 < V g) :
    letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
      (S g.val).piAntidiag (k g.val) |>.fintypeCoeSort
    (∑ v : (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)),
      sourceMultigroupCountMass G S k V v) = 1 := by
  classical
  letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
    ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
  let w : (g : G) → sourceGroupCountSpace (S g.val) (k g.val) → ℝ :=
    fun g v => sourceMultinomialCountMass
      (S g.val) (k g.val) (V g.val) v.val
  have hsingle (g : G) :
      (∑ v : sourceGroupCountSpace (S g.val) (k g.val),
        w g v) = 1 := by
    change (∑ v : sourceGroupCountSpace (S g.val) (k g.val),
      sourceMultinomialCountMass (S g.val) (k g.val) (V g.val) v.val) = 1
    exact (Finset.sum_coe_sort
      ((S g.val).piAntidiag (k g.val))
      (fun v => sourceMultinomialCountMass
        (S g.val) (k g.val) (V g.val) v)).trans
      (source_multinomial_count_normalized
        (S g.val) (k g.val) (V g.val)
        (hV g.val g.property) (hVp g.val g.property))
  calc
    (∑ v : (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)),
      sourceMultigroupCountMass G S k V v) =
      ∏ g : G, ∑ v : sourceGroupCountSpace (S g.val) (k g.val), w g v := by
        simpa only [sourceMultigroupCountMass, w] using (Fintype.prod_sum w).symm
    _ = ∏ _g : G, (1:ℝ) := by simp only [hsingle]
    _ = 1 := by simp
end Green64SourceC6

end

/-! ## SourceMultiGroupFactorization -/

section

namespace Green64SourceC6
open scoped BigOperators

theorem source_multigroup_count_factorization_at
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hdisj : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h))
    (v : ∀ g : G, sourceGroupCountSpace (S g.val) (k g.val))
    (g : G) (p : ℕ) (hp : p ∈ S g.val) :
    (sourceMultigroupCountProduct G S k v).factorization p =
      (v g).val p := by
  classical
  letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
    ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
  let prod : G → ℕ := fun h => sourceCountProduct (S h.val) (v h).val
  have hnonzero : ∀ h ∈ (Finset.univ : Finset G), prod h ≠ 0 := by
    intro h hh
    exact (Nat.ne_of_gt (source_count_product_pos
      (S h.val) (k h.val) (v h).val
      (hprime h.val h.property) (v h).property))
  have hfactor : (∏ h : G, prod h).factorization p =
      ∑ h : G, (prod h).factorization p :=
    Nat.factorization_prod_apply hnonzero
  have heach (h : G) : (prod h).factorization p = (v h).val p :=
    source_count_product_factorization_at
      (S h.val) (k h.val) (v h).val
      (hprime h.val h.property) (v h).property p
  have hzero (h : G) (hne : h ≠ g) : (v h).val p = 0 := by
    have hgn : h.val ≠ g.val := by
      intro he
      exact hne (Subtype.ext he)
    have hnot : p ∉ S h.val := by
      intro hpm
      exact (Finset.disjoint_left.mp
        (hdisj h.val h.property g.val g.property hgn)) hpm hp
    by_contra hz
    exact hnot ((Finset.mem_piAntidiag.mp (v h).property).2 p hz)
  have hsum : (∑ h : G, (v h).val p) = (v g).val p := by
    apply Finset.sum_eq_single g
    · intro h hh hne
      exact hzero h hne
    · simp
  change (∏ h : G, prod h).factorization p = (v g).val p
  rw [hfactor]
  simpa only [heach] using hsum
end Green64SourceC6

end

/-! ## SourceMultiGroupInjection -/

section

namespace Green64SourceC6
open scoped BigOperators

theorem source_multigroup_count_factorization_any
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (v : ∀ g : G, sourceGroupCountSpace (S g.val) (k g.val))
    (p : ℕ) :
    (sourceMultigroupCountProduct G S k v).factorization p =
      ∑ g : G, (v g).val p := by
  classical
  letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
    ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
  let prod : G → ℕ := fun h => sourceCountProduct (S h.val) (v h).val
  have hnonzero : ∀ h ∈ (Finset.univ : Finset G), prod h ≠ 0 := by
    intro h hh
    exact (Nat.ne_of_gt (source_count_product_pos
      (S h.val) (k h.val) (v h).val
      (hprime h.val h.property) (v h).property))
  have hfactor : (∏ h : G, prod h).factorization p =
      ∑ h : G, (prod h).factorization p :=
    Nat.factorization_prod_apply hnonzero
  calc
    (sourceMultigroupCountProduct G S k v).factorization p =
      ∑ h : G, (prod h).factorization p := by
        simpa only [sourceMultigroupCountProduct, prod] using hfactor
    _ = ∑ h : G, (v h).val p := by
      apply Finset.sum_congr rfl
      intro h hh
      exact source_count_product_factorization_at
        (S h.val) (k h.val) (v h).val
        (hprime h.val h.property) (v h).property p

theorem source_multigroup_count_product_injective
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hdisj : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h)) :
    Function.Injective (sourceMultigroupCountProduct G S k) := by
  intro v w heq
  funext g
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ S g.val
  · have hv := source_multigroup_count_factorization_at
      G S k hprime hdisj v g p hp
    have hw := source_multigroup_count_factorization_at
      G S k hprime hdisj w g p hp
    rw [heq] at hv
    exact hv.symm.trans hw
  · have hv : (v g).val p = 0 := by
      by_contra hn
      exact hp ((Finset.mem_piAntidiag.mp (v g).property).2 p hn)
    have hw : (w g).val p = 0 := by
      by_contra hn
      exact hp ((Finset.mem_piAntidiag.mp (w g).property).2 p hn)
    exact hv.trans hw.symm
end Green64SourceC6

end

/-! ## SourceMultiGroupValid -/

section

namespace Green64SourceC6
open scoped BigOperators

theorem source_multigroup_count_product_pos
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (v : ∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)) :
    0 < sourceMultigroupCountProduct G S k v := by
  unfold sourceMultigroupCountProduct
  apply Finset.prod_pos
  intro g hg
  exact source_count_product_pos (S g.val) (k g.val)
    (v g).val (hprime g.val g.property) (v g).property

theorem source_multigroup_count_atom_valid
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hdisj : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h))
    (v : ∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)) :
    sourceAtomValid G S k (sourceMultigroupCountProduct G S k v) := by
  classical
  have hpos := source_multigroup_count_product_pos G S k hprime v
  unfold sourceAtomValid
  refine ⟨Nat.ne_of_gt hpos, ?_, ?_⟩
  · intro g hg
    let g' : G := ⟨g, hg⟩
    have hsum := (Finset.mem_piAntidiag.mp (v g').property).1
    calc
      (∑ p ∈ S g, (sourceMultigroupCountProduct G S k v).factorization p) =
        ∑ p ∈ S g, (v g').val p := by
          apply Finset.sum_congr rfl
          intro p hp
          exact source_multigroup_count_factorization_at
            G S k hprime hdisj v g' p hp
      _ = k g := hsum
  · intro p hp
    have hnonzero : (sourceMultigroupCountProduct G S k v).factorization p ≠ 0 := by
      have hh : p ∈ (sourceMultigroupCountProduct G S k v).factorization.support := by
        simpa only [Nat.support_factorization] using hp
      exact (Finsupp.mem_support_iff).mp hh
    have hfac := source_multigroup_count_factorization_any
      G S k hprime v p
    by_contra hnot
    have hzero (g : G) : (v g).val p = 0 := by
      by_contra hz
      have hmem : p ∈ S g.val :=
        (Finset.mem_piAntidiag.mp (v g).property).2 p hz
      have hUnion : p ∈ G.biUnion S :=
        Finset.mem_biUnion.mpr ⟨g.val,g.property,hmem⟩
      exact hnot hUnion
    have hz : (∑ g : G, (v g).val p) = 0 := by
      simp only [hzero, Finset.sum_const_zero]
    rw [hfac, hz] at hnonzero
    exact hnonzero rfl
end Green64SourceC6

end

/-! ## SourceMultiGroupAtomEquality -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- Crucial source-fidelity theorem: with disjoint prime groups,
the *literal* factorial atom mass equals the normalized multinomial
weight of the unique count-vector family representing its integer
product. Repetitions within groups are fully permitted. -/
theorem source_multigroup_atom_eq_multinomial
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hdisj : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h))
    (v : ∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)) :
    sourceProductAtomMass G S k V
      (sourceMultigroupCountProduct G S k v) =
    sourceMultigroupCountMass G S k V v := by
  classical
  let n := sourceMultigroupCountProduct G S k v
  let d : G → ℕ := fun g => sourceCountProduct (S g.val) (v g).val
  let R : G → ℝ := fun g =>
    (Nat.factorial (k g.val) : ℝ) /
      (V g.val ^ k g.val *
        ∏ p ∈ S g.val, ((Nat.factorial ((v g).val p) : ℕ) : ℝ))
  have hnvalid : sourceAtomValid G S k n :=
    source_multigroup_count_atom_valid G S k hprime hdisj v
  have hgroup (g : G) :
      sourceAtomGroupFactor S k V g.val n = R g := by
    dsimp [R, sourceAtomGroupFactor, sourceAtomMultiplicityFactor]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [source_multigroup_count_factorization_at
      G S k hprime hdisj v g p hp]
  have hprodInv : (∏ g : G, (1/(d g:ℝ))) = 1/(n:ℝ) := by
    have hcast : ((∏ g : G, d g : ℕ) : ℝ) =
        ∏ g : G, (d g : ℝ) := by
      exact Nat.cast_prod d Finset.univ
    calc
      (∏ g : G, (1/(d g:ℝ))) =
          (∏ g : G, (d g:ℝ))⁻¹ := by
            simp only [one_div, Finset.prod_inv_distrib]
      _ = 1/(n:ℝ) := by
        rw [←hcast]
        simp only [one_div]
        congr 1
  calc
    sourceProductAtomMass G S k V n =
        (1/(n:ℝ)) * ∏ g : G, R g := by
          rw [sourceProductAtomMass, if_pos hnvalid]
          congr 1
          calc
            (∏ g ∈ G, sourceAtomGroupFactor S k V g n) =
              ∏ g : G, sourceAtomGroupFactor S k V g.val n := by
                exact (Finset.prod_attach G
                  (fun g => sourceAtomGroupFactor S k V g n)).symm
            _ = ∏ g : G, R g := by
              apply Finset.prod_congr rfl
              intro g hg
              exact hgroup g
    _ = (∏ g : G, 1/(d g:ℝ)) * (∏ g : G, R g) := by
          rw [hprodInv]
    _ = ∏ g : G, (1/(d g:ℝ))*R g := by
          rw [Finset.prod_mul_distrib]
    _ = sourceMultigroupCountMass G S k V v := by
          dsimp [sourceMultigroupCountMass]
          apply Finset.prod_congr rfl
          intro g hg
          exact (source_multinomial_count_factorial_density
            (S g.val) (k g.val) (V g.val) (v g).val
            (v g).property).symm
end Green64SourceC6

end

/-! ## SourceMultiGroupSupport -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- Completeness: every integer satisfying EXACT source group
multiplicity and prime-support conditions arises from the unique
family of multinomial group count-vectors, even with repeats. -/
theorem source_multigroup_atom_valid_iff_count_image
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (n : ℕ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hdisj : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h)) :
    letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
      ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
    sourceAtomValid G S k n ↔
      n ∈ (Finset.univ : Finset
        (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val))).image
        (sourceMultigroupCountProduct G S k) := by
  classical
  letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
    ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
  constructor
  · intro hvalid
    rcases hvalid with ⟨hn, hcount, hsupport⟩
    let v : (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)) :=
      fun g => ⟨(fun p => if p ∈ S g.val then n.factorization p else 0), by
        apply Finset.mem_piAntidiag.mpr
        constructor
        · have hh := hcount g.val g.property
          simpa using hh
        · intro p hp
          by_contra hnots
          simp [hnots] at hp⟩
    have hfac (p : ℕ) :
        (sourceMultigroupCountProduct G S k v).factorization p =
          n.factorization p := by
      by_cases hp : p ∈ G.biUnion S
      · obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
        have h := source_multigroup_count_factorization_at
          G S k hprime hdisj v ⟨g,hg⟩ p hpg
        rw [h]
        simp [v, hpg]
      · have hnzero : n.factorization p = 0 := by
          by_contra hz
          have hpr : p ∈ n.primeFactors := by
            rw [← Nat.support_factorization]
            exact (Finsupp.mem_support_iff).mpr hz
          exact hp (hsupport p hpr)
        have hzero (g : G) : (v g).val p = 0 := by
          have hnot : p ∉ S g.val := by
            intro hpg
            exact hp (Finset.mem_biUnion.mpr ⟨g.val,g.property,hpg⟩)
          simp [v, hnot]
        rw [source_multigroup_count_factorization_any G S k hprime v p]
        simp only [hzero, Finset.sum_const_zero, hnzero]
    have hpos := source_multigroup_count_product_pos G S k hprime v
    have heq : sourceMultigroupCountProduct G S k v = n :=
      Nat.eq_of_factorization_eq (Nat.ne_of_gt hpos) hn hfac
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, heq⟩
  · intro h
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp h
    rw [← heq]
    exact source_multigroup_count_atom_valid G S k hprime hdisj v
end Green64SourceC6

end

/-! ## SourceMultiGroupNormalized -/

section

namespace Green64SourceC6
open scoped BigOperators

theorem source_multigroup_atom_full_normalized
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hdisj : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h))
    (hV : ∀ g ∈ G, V g = ∑ p ∈ S g, (1/(p:ℝ)))
    (hVp : ∀ g ∈ G, 0 < V g) :
    letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
      ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
    (∑ n ∈ (Finset.univ : Finset
        (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val))).image
        (sourceMultigroupCountProduct G S k),
      sourceProductAtomMass G S k V n) = 1 := by
  classical
  letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
    ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
  calc
    (∑ n ∈ (Finset.univ : Finset
        (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val))).image
        (sourceMultigroupCountProduct G S k),
      sourceProductAtomMass G S k V n) =
        ∑ v : (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)),
          sourceProductAtomMass G S k V
            (sourceMultigroupCountProduct G S k v) := by
              apply Finset.sum_image
              intro x hx y hy hxy
              exact source_multigroup_count_product_injective
                G S k hprime hdisj hxy
    _ = ∑ v : (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)),
          sourceMultigroupCountMass G S k V v := by
            apply Finset.sum_congr rfl
            intro v hv
            exact source_multigroup_atom_eq_multinomial
              G S k V hprime hdisj v
    _ = 1 := source_multigroup_count_normalized G S k V hV hVp

/-- Required C6 probability normalizations are now proved for
the literal factorial atom mass of arbitrary disjoint prime groups. -/
theorem source_product_atom_marginal_normalized
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ) (F : Finset ℕ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hdisj : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h))
    (hV : ∀ g ∈ G, V g = ∑ p ∈ S g, (1/(p:ℝ)))
    (hVp : ∀ g ∈ G, 0 < V g) :
    (∑ n ∈ F, sourceProductAtomMass G S k V n) ≤ 1 := by
  classical
  letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
    ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
  let T : Finset ℕ :=
    (Finset.univ : Finset
      (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val))).image
      (sourceMultigroupCountProduct G S k)
  have hzero (n : ℕ) (hn : n ∉ T) :
      sourceProductAtomMass G S k V n = 0 := by
    have hnvalid : ¬sourceAtomValid G S k n := by
      intro hvalid
      exact hn ((source_multigroup_atom_valid_iff_count_image
        G S k n hprime hdisj).mp hvalid)
    simp only [sourceProductAtomMass, if_neg hnvalid]
  have hnonneg (n : ℕ) : 0 ≤ sourceProductAtomMass G S k V n :=
    (source_product_atom_pointwise G S k V hVp n).1
  have heq : (∑ n ∈ F, sourceProductAtomMass G S k V n) =
    ∑ n ∈ F.filter (fun n => n ∈ T), sourceProductAtomMass G S k V n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hh : n ∈ T
    · simp [hh]
    · simp [hh,hzero n hh]
  have hsubset : F.filter (fun n => n ∈ T) ⊆ T := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  calc
    (∑ n ∈ F, sourceProductAtomMass G S k V n) =
      ∑ n ∈ F.filter (fun n => n ∈ T),
        sourceProductAtomMass G S k V n := heq
    _ ≤ ∑ n ∈ T, sourceProductAtomMass G S k V n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n hn hnot => hnonneg n)
    _ = 1 := source_multigroup_atom_full_normalized
      G S k V hprime hdisj hV hVp
end Green64SourceC6

end

/-! ## SourceFullGroupC6 -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- Exact source four-term C6 estimate for TWO arbitrary independent
collections of disjoint prime groups, all slot numbers k_g unrestricted.
Unlike the predecessor, no unproved probability-normalization
assumption occurs. Coefficient tests remain genuinely complex. -/
theorem source_full_multigroup_product_atom_four_term_sq
    {γ₁ γ₂ : Type*} [DecidableEq γ₁] [DecidableEq γ₂]
    (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ)
    (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
    (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ)
    (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ)
    (hp₁ : ∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p)
    (hp₂ : ∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p)
    (hd₁ : ∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h))
    (hd₂ : ∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h))
    (hV₁ : ∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, (1/(p:ℝ)))
    (hV₂ : ∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, (1/(p:ℝ)))
    (hv₁ : ∀ g ∈ G₁, 0 < V₁ g)
    (hv₂ : ∀ g ∈ G₂, 0 < V₂ g)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (b₁ b₂ : ℕ → ℂ)
    (hb₁ : ∀ n ∈ Finset.Ico M (M+P), ‖b₁ n‖ ≤ 1)
    (hb₂ : ∀ n ∈ Finset.Ico N (N+Q), ‖b₂ n‖ ≤ 1)
    (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    ‖∑ i ∈ Finset.range P,
      (((sourceProductAtomMass G₁ S₁ k₁ V₁ (M+i):ℝ):ℂ) * b₁ (M+i)) *
      (∑ j ∈ Finset.range Q,
        (((sourceProductAtomMass G₂ S₂ k₂ V₂ (N+j):ℝ):ℂ) * b₂ (N+j)) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta) * ((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ))‖^2 ≤
      50*sourceProductAtomPrefactor G₁ k₁ V₁*
         sourceProductAtomPrefactor G₂ k₂ V₂*
      (1/(N:ℝ)+1/(r:ℝ)+
        Real.log (2*(r:ℝ))/(M:ℝ)+
        (r:ℝ)*Real.log (2*(r:ℝ))/((M:ℝ)*(N:ℝ))) := by
  have hn₁ :
      (∑ n ∈ Finset.Ico M (M+P),
        sourceProductAtomMass G₁ S₁ k₁ V₁ n) ≤ 1 :=
    source_product_atom_marginal_normalized G₁ S₁ k₁ V₁
      (Finset.Ico M (M+P)) hp₁ hd₁ hV₁ hv₁
  have hn₂ :
      (∑ n ∈ Finset.Ico N (N+Q),
        sourceProductAtomMass G₂ S₂ k₂ V₂ n) ≤ 1 :=
    source_product_atom_marginal_normalized G₂ S₂ k₂ V₂
      (Finset.Ico N (N+Q)) hp₂ hd₂ hV₂ hv₂
  exact source_actual_product_atom_four_term_sq
    G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂ hv₁ hv₂
    M N P Q hM hN hP hQ b₁ b₂ hb₁ hb₂
    hn₁ hn₂ a r beta hr hcop hbeta
end Green64SourceC6

end

/-! ## SourceComplexPushforward -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- Exact complex Fourier/test pushforward for the physical source
product-atom probability. No signs or positivity assumption on the
test, no uniqueness of individual ordered slot arrangements. -/
theorem source_multigroup_complex_test_pushforward
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ)
    (k : γ → ℕ) (V : γ → ℝ)
    (hprime : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hdisj : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h))
    (φ : ℕ → ℂ) :
    letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
      ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
    (∑ v : (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)),
       ((sourceMultigroupCountMass G S k V v : ℝ) : ℂ) *
          φ (sourceMultigroupCountProduct G S k v)) =
    ∑ n ∈ (Finset.univ : Finset
        (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val))).image
        (sourceMultigroupCountProduct G S k),
       ((sourceProductAtomMass G S k V n : ℝ) : ℂ) * φ n := by
  classical
  letI (g : G) : Fintype (sourceGroupCountSpace (S g.val) (k g.val)) :=
    ((S g.val).piAntidiag (k g.val)).fintypeCoeSort
  calc
    (∑ v : (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)),
       ((sourceMultigroupCountMass G S k V v : ℝ) : ℂ) *
          φ (sourceMultigroupCountProduct G S k v)) =
    ∑ v : (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val)),
       ((sourceProductAtomMass G S k V
          (sourceMultigroupCountProduct G S k v) : ℝ) : ℂ) *
          φ (sourceMultigroupCountProduct G S k v) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [source_multigroup_atom_eq_multinomial G S k V hprime hdisj v]
    _ = ∑ n ∈ (Finset.univ : Finset
        (∀ g : G, sourceGroupCountSpace (S g.val) (k g.val))).image
        (sourceMultigroupCountProduct G S k),
       ((sourceProductAtomMass G S k V n : ℝ) : ℂ) * φ n := by
      symm
      apply Finset.sum_image
      intro x hx y hy hxy
      exact source_multigroup_count_product_injective
        G S k hprime hdisj hxy
end Green64SourceC6

end

/-! ## SourcePrefactorBudget -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- Exact prefactor bound for an arbitrary finite family of source
prime groups with fixed maximum free-slot count per group. The
remaining growth of the number of groups is explicit, not hidden. -/
theorem source_prefactor_fixed_slot_bound
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (k : γ → ℕ) (V : γ → ℝ)
    (m₀ : ℕ) (vmin : ℝ)
    (hvmin : 0 < vmin)
    (hk : ∀ g ∈ G, k g ≤ m₀)
    (hV : ∀ g ∈ G, vmin ≤ V g) :
    sourceProductAtomPrefactor G k V ≤
      ((Nat.factorial m₀ : ℝ) *
        (max (1:ℝ) vmin⁻¹)^m₀)^G.card := by
  let K : ℝ := max 1 vmin⁻¹
  have hK : (1:ℝ) ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := by linarith
  have hfact : 0 ≤ (Nat.factorial m₀ : ℝ) := by positivity
  have hpoint (g : γ) (hg : g ∈ G) :
      ((Nat.factorial (k g) : ℝ)/(V g)^k g) ≤
        (Nat.factorial m₀ : ℝ)*K^m₀ := by
    have hVpos : 0 < V g := lt_of_lt_of_le hvmin (hV g hg)
    have hInv : (V g)⁻¹ ≤ K := by
      have hInvMin : (V g)⁻¹ ≤ vmin⁻¹ :=
        (inv_le_inv₀ hVpos hvmin).2 (hV g hg)
      exact hInvMin.trans (le_max_right _ _)
    have hA : (Nat.factorial (k g) : ℝ) ≤ (Nat.factorial m₀ : ℝ) := by
      exact_mod_cast Nat.factorial_le (hk g hg)
    have hB : ((V g)⁻¹)^(k g) ≤ K^m₀ := by
      calc
        _ ≤ K^(k g) := pow_le_pow_left₀ (by positivity) hInv (k g)
        _ ≤ K^m₀ := pow_le_pow_right₀ hK (hk g hg)
    have hR : 0 ≤ ((V g)⁻¹)^(k g) := by positivity
    have hL : 0 ≤ ((Nat.factorial (k g) : ℝ)) := by positivity
    calc
      ((Nat.factorial (k g) : ℝ)/(V g)^k g) =
        ((Nat.factorial (k g) : ℝ))*((V g)⁻¹)^(k g) := by
          simp only [div_eq_mul_inv, inv_pow]
      _ ≤ (Nat.factorial m₀ : ℝ)*K^m₀ :=
        mul_le_mul hA hB hR (by positivity)
  have hpoint0 (g : γ) (hg : g ∈ G) :
      0 ≤ (Nat.factorial (k g) : ℝ)/(V g)^k g := by
    have hv := lt_of_lt_of_le hvmin (hV g hg)
    positivity
  unfold sourceProductAtomPrefactor
  calc
    (∏ g ∈ G, (Nat.factorial (k g) : ℝ)/(V g)^k g) ≤
      ∏ _g ∈ G, ((Nat.factorial m₀ : ℝ)*K^m₀) :=
        Finset.prod_le_prod₀ hpoint0 hpoint
    _ = ((Nat.factorial m₀ : ℝ)*K^m₀)^G.card := by
      rw [Finset.prod_const]
    _ = ((Nat.factorial m₀ : ℝ) *
      (max (1:ℝ) vmin⁻¹)^m₀)^G.card := rfl
end Green64SourceC6

end

/-! ## SourcePrefactorLogPower -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- The exact fixed-power transfer for O(log L) source groups. -/
theorem fixed_power_of_log_card
    (K L C : ℝ) (n : ℕ)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hn : (n:ℝ) ≤ C*Real.log L) :
    K^n ≤ L^(C*Real.log K) := by
  have hKp : 0 < K := by linarith
  have hLp : 0 < L := by linarith
  calc
    K^n = K^((n:ℝ)) := (Real.rpow_natCast K n).symm
    _ ≤ K^(C*Real.log L) :=
      Real.rpow_le_rpow_of_exponent_le hK hn
    _ = L^(C*Real.log K) := by
      rw [Real.rpow_def_of_pos hKp, Real.rpow_def_of_pos hLp]
      congr 1
      ring

/-- The source's fixed m0 and V_g ≥ v_- > 0 give a fixed log-power
prefactor, once |G| ≤ C0 log L, precisely the source T = log L. -/
theorem source_prefactor_log_power
    {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (k : γ → ℕ) (V : γ → ℝ)
    (m₀ : ℕ) (vmin C₀ L : ℝ)
    (hmin : 0 < vmin) (hL : 1 ≤ L) (hC₀ : 0 ≤ C₀)
    (hk : ∀ g ∈ G, k g ≤ m₀)
    (hV : ∀ g ∈ G, vmin ≤ V g)
    (hcard : (G.card:ℝ) ≤ C₀*Real.log L) :
    sourceProductAtomPrefactor G k V ≤
      L^(C₀*Real.log ((Nat.factorial m₀ : ℝ) *
          (max (1:ℝ) vmin⁻¹)^m₀)) := by
  let K : ℝ := (Nat.factorial m₀ : ℝ) *
      (max (1:ℝ) vmin⁻¹)^m₀
  have hf : (1:ℝ) ≤ (Nat.factorial m₀ : ℝ) := by
    have h : Nat.factorial 0 ≤ Nat.factorial m₀ :=
      Nat.factorial_le (Nat.zero_le m₀)
    norm_num at h ⊢
    exact_mod_cast h
  have hh : (1:ℝ) ≤ (max (1:ℝ) vmin⁻¹)^m₀ :=
    one_le_pow₀ (le_max_left _ _)
  have hK : (1:ℝ) ≤ K := by
    dsimp [K]
    nlinarith [mul_nonneg (sub_nonneg.mpr hf) (sub_nonneg.mpr hh)]
  calc
    sourceProductAtomPrefactor G k V ≤ K^G.card :=
      source_prefactor_fixed_slot_bound G k V m₀ vmin hmin hk hV
    _ ≤ L^(C₀*Real.log K) :=
      fixed_power_of_log_card K L C₀ G.card hK hL hC₀ hcard
    _ = _ := rfl
end Green64SourceC6

end

/-! ## SourceLogPowerC6 -/

section

namespace Green64SourceC6
open scoped BigOperators

/-- Source-exact C6 bound for two arbitrary disjoint prime-group blocks,
with the full factorial/source probability normalized in Lean, and the
entire L^C7 scale derived rather than declared. This remains the C6
multiplier component; Fourier major-arc energy is separate. -/
theorem source_full_multigroup_logpower_minor_arc_sq
    {γ₁ γ₂ : Type*} [DecidableEq γ₁] [DecidableEq γ₂]
    (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ)
    (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
    (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ)
    (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ)
    (hp₁ : ∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p)
    (hp₂ : ∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p)
    (hd₁ : ∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h))
    (hd₂ : ∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h))
    (hV₁exact : ∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, (1/(p:ℝ)))
    (hV₂exact : ∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, (1/(p:ℝ)))
    (m₀ : ℕ) (vmin C₀ L : ℝ)
    (hvmin : 0 < vmin) (hL : 1 ≤ L) (hC₀ : 0 ≤ C₀)
    (hk₁ : ∀ g ∈ G₁, k₁ g ≤ m₀)
    (hk₂ : ∀ g ∈ G₂, k₂ g ≤ m₀)
    (hV₁ : ∀ g ∈ G₁, vmin ≤ V₁ g)
    (hV₂ : ∀ g ∈ G₂, vmin ≤ V₂ g)
    (hcard₁ : (G₁.card:ℝ) ≤ C₀*Real.log L)
    (hcard₂ : (G₂.card:ℝ) ≤ C₀*Real.log L)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (b₁ b₂ : ℕ → ℂ)
    (hb₁ : ∀ n ∈ Finset.Ico M (M+P), ‖b₁ n‖ ≤ 1)
    (hb₂ : ∀ n ∈ Finset.Ico N (N+Q), ‖b₂ n‖ ≤ 1)
    (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    let K := (Nat.factorial m₀ : ℝ) * (max (1:ℝ) vmin⁻¹)^m₀
    ‖∑ i ∈ Finset.range P,
      (((sourceProductAtomMass G₁ S₁ k₁ V₁ (M+i):ℝ):ℂ) * b₁ (M+i)) *
      (∑ j ∈ Finset.range Q,
        (((sourceProductAtomMass G₂ S₂ k₂ V₂ (N+j):ℝ):ℂ) * b₂ (N+j)) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta) * ((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ))‖^2 ≤
      50*L^(2*C₀*Real.log K) *
      (1/(N:ℝ)+1/(r:ℝ)+
        Real.log (2*(r:ℝ))/(M:ℝ)+
        (r:ℝ)*Real.log (2*(r:ℝ))/((M:ℝ)*(N:ℝ))) := by
  dsimp only
  let K : ℝ := (Nat.factorial m₀ : ℝ) *
      (max (1:ℝ) vmin⁻¹)^m₀
  let CP : ℝ := C₀*Real.log K
  let B : ℝ := (1/(N:ℝ)+1/(r:ℝ)+
        Real.log (2*(r:ℝ))/(M:ℝ)+
        (r:ℝ)*Real.log (2*(r:ℝ))/((M:ℝ)*(N:ℝ)))
  let P₁ : ℝ := sourceProductAtomPrefactor G₁ k₁ V₁
  let P₂ : ℝ := sourceProductAtomPrefactor G₂ k₂ V₂
  let X : ℂ := ∑ i ∈ Finset.range P,
      (((sourceProductAtomMass G₁ S₁ k₁ V₁ (M+i):ℝ):ℂ) * b₁ (M+i)) *
      (∑ j ∈ Finset.range Q,
        (((sourceProductAtomMass G₂ S₂ k₂ V₂ (N+j):ℝ):ℂ) * b₂ (N+j)) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta) * ((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ))
  have hv₁ : ∀ g ∈ G₁, 0 < V₁ g :=
    fun g hg => lt_of_lt_of_le hvmin (hV₁ g hg)
  have hv₂ : ∀ g ∈ G₂, 0 < V₂ g :=
    fun g hg => lt_of_lt_of_le hvmin (hV₂ g hg)
  have hP₁ : P₁ ≤ L^CP :=
    source_prefactor_log_power G₁ k₁ V₁ m₀ vmin C₀ L
      hvmin hL hC₀ hk₁ hV₁ hcard₁
  have hP₂ : P₂ ≤ L^CP :=
    source_prefactor_log_power G₂ k₂ V₂ m₀ vmin C₀ L
      hvmin hL hC₀ hk₂ hV₂ hcard₂
  have hP₂n : 0 ≤ P₂ := by
    dsimp [P₂, sourceProductAtomPrefactor]
    apply Finset.prod_nonneg
    intro g hg
    have hv := hv₂ g hg
    positivity
  have hLp : 0 < L := by linarith
  have hLpow : 0 ≤ L^CP := (Real.rpow_pos_of_pos hLp CP).le
  have hPprod : P₁*P₂ ≤ (L^CP)*(L^CP) :=
    mul_le_mul hP₁ hP₂ hP₂n hLpow
  have hLog : 0 ≤ Real.log (2*(r:ℝ)) := by
    apply Real.log_nonneg
    have hrr : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    nlinarith
  have hBr : 0 ≤ B := by
    dsimp [B]
    have hm : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    have hn : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hrr : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
    positivity
  have hC6 : ‖X‖^2 ≤ 50*P₁*P₂*B := by
    simpa only [X, P₁, P₂, B] using
      source_full_multigroup_product_atom_four_term_sq
        G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂ hp₁ hp₂ hd₁ hd₂
        hV₁exact hV₂exact hv₁ hv₂
        M N P Q hM hN hP hQ b₁ b₂ hb₁ hb₂
        a r beta hr hcop hbeta
  have hmult : 50*(P₁*P₂)*B ≤ 50*((L^CP)*(L^CP))*B := by
    have h₁ := mul_le_mul_of_nonneg_left hPprod (by norm_num : (0:ℝ) ≤ 50)
    exact mul_le_mul_of_nonneg_right h₁ hBr
  have hdouble : (L^CP)*(L^CP) = L^(2*CP) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  calc
    ‖X‖^2 ≤ 50*P₁*P₂*B := hC6
    _ = 50*(P₁*P₂)*B := by ring
    _ ≤ 50*((L^CP)*(L^CP))*B := hmult
    _ = 50*L^(2*CP)*B := by rw [hdouble]
    _ = _ := by dsimp [CP, K, B]; ring
end Green64SourceC6

end

/-! ## SourceProductAtomMass -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
set_option maxHeartbeats 3500000

/-- Exact marginal normalization after restriction to any integer block. -/
theorem source_product_atom_shifted_mass434 {γ : Type*} [DecidableEq γ]
    (G : Finset γ) (S : γ → Finset ℕ) (k : γ → ℕ) (V : γ → ℝ)
    (hp : ∀ g ∈ G, ∀ p ∈ S g, Nat.Prime p)
    (hd : ∀ g ∈ G, ∀ h ∈ G, g ≠ h → Disjoint (S g) (S h))
    (hV : ∀ g ∈ G, V g = ∑ p ∈ S g, 1/(p:ℝ))
    (hVp : ∀ g ∈ G, 0 < V g) (M P : ℕ) :
    (∑ i ∈ Finset.range P, sourceProductAtomMass G S k V (M+i)) ≤ 1 := by
  let F := (Finset.range P).image (fun i => M+i)
  have hEq : (∑ n ∈ F, sourceProductAtomMass G S k V n) =
      ∑ i ∈ Finset.range P, sourceProductAtomMass G S k V (M+i) := by
    dsimp only [F]
    apply Finset.sum_image
    intro i hi j hj hij
    exact Nat.add_left_cancel hij
  rw [← hEq]
  exact source_product_atom_marginal_normalized G S k V F hp hd hV hVp

/-- The genuine repeated-prime product laws discharge the coefficient-mass
premise in the comparison theorem. No probabilistic normalization is assumed. -/
theorem source_original_product_coefficient_mass434
    {γ₁ γ₂ : Type*} [DecidableEq γ₁] [DecidableEq γ₂]
    (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ) (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
    (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ) (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ)
    (hp₁ : ∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p)
    (hp₂ : ∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p)
    (hd₁ : ∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h))
    (hd₂ : ∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h))
    (hV₁ : ∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, 1/(p:ℝ))
    (hV₂ : ∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, 1/(p:ℝ))
    (hv₁ : ∀ g ∈ G₁, 0 < V₁ g) (hv₂ : ∀ g ∈ G₂, 0 < V₂ g)
    (M N P Q : ℕ) (b₁ b₂ : ℕ → ℂ)
    (hb₁ : ∀ n ∈ Finset.Ico M (M+P), ‖b₁ n‖ ≤ 1)
    (hb₂ : ∀ n ∈ Finset.Ico N (N+Q), ‖b₂ n‖ ≤ 1) :
    (∑ ij ∈ (Finset.range P).product (Finset.range Q),
      ‖sourceProductShiftCoefficient434 M N
        (sourceProductAtomMass G₁ S₁ k₁ V₁)
        (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂ ij‖) ≤ 1 := by
  apply source_product_shift_coefficient_mass434
  · intro i hi
    exact (source_product_atom_pointwise G₁ S₁ k₁ V₁ hv₁ (M+i)).1
  · intro j hj
    exact (source_product_atom_pointwise G₂ S₂ k₂ V₂ hv₂ (N+j)).1
  · exact source_product_atom_shifted_mass434 G₁ S₁ k₁ V₁ hp₁ hd₁ hV₁ hv₁ M P
  · exact source_product_atom_shifted_mass434 G₂ S₂ k₂ V₂ hp₂ hd₂ hV₂ hv₂ N Q
  · intro i hi
    apply hb₁
    rw [Finset.mem_Ico]
    have := Finset.mem_range.mp hi
    omega
  · intro j hj
    apply hb₂
    rw [Finset.mem_Ico]
    have := Finset.mem_range.mp hj
    omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceProductAtomMultiplier -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
set_option maxHeartbeats 5500000

/-- Literal product-atom multiplier, not an assumed minor bound.
The factorial atom law, its mass and its log loss come from native C6. -/
theorem source_product_atom_multiplier_rational434
    {γ₁ γ₂ : Type*} [DecidableEq γ₁] [DecidableEq γ₂]
    (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ)
    (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
    (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ)
    (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ)
    (hp₁ : ∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p)
    (hp₂ : ∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p)
    (hd₁ : ∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h))
    (hd₂ : ∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h))
    (hV₁exact : ∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, 1/(p:ℝ))
    (hV₂exact : ∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, 1/(p:ℝ))
    (m₀ : ℕ) (vmin C₀ L : ℝ)
    (hvmin : 0 < vmin) (hL : 1 ≤ L) (hC₀ : 0 ≤ C₀)
    (hk₁ : ∀ g ∈ G₁, k₁ g ≤ m₀) (hk₂ : ∀ g ∈ G₂, k₂ g ≤ m₀)
    (hV₁ : ∀ g ∈ G₁, vmin ≤ V₁ g) (hV₂ : ∀ g ∈ G₂, vmin ≤ V₂ g)
    (hcard₁ : (G₁.card:ℝ) ≤ C₀*Real.log L)
    (hcard₂ : (G₂.card:ℝ) ≤ C₀*Real.log L)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hP : P ≤ M) (hQ : Q ≤ N)
    (b₁ b₂ : ℕ → ℂ)
    (hb₁ : ∀ n ∈ Finset.Ico M (M+P), ‖b₁ n‖ ≤ 1)
    (hb₂ : ∀ n ∈ Finset.Ico N (N+Q), ‖b₂ n‖ ≤ 1)
    (a k : ℤ) (r : ℕ) (theta Bsave : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hNear : |-(k:ℝ)*theta-(a:ℝ)/(r:ℝ)| ≤ 1/((r:ℝ)^2))
    (hBracket : 1/(N:ℝ)+1/(r:ℝ)+Real.log (2*(r:ℝ))/(M:ℝ)+
      (r:ℝ)*Real.log (2*(r:ℝ))/((M:ℝ)*(N:ℝ)) ≤ 4/L^Bsave) :
    let K := (Nat.factorial m₀:ℝ)*(max (1:ℝ) vmin⁻¹)^m₀
    ‖sourceProductMultiplier434 M N P Q
      (sourceProductAtomMass G₁ S₁ k₁ V₁)
      (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂ k (theta:AddCircle (1:ℝ))‖ ≤
      16*L^(C₀*Real.log K-Bsave/2) := by
  dsimp only
  let K : ℝ := (Nat.factorial m₀:ℝ)*(max (1:ℝ) vmin⁻¹)^m₀
  let B : ℝ := 1/(N:ℝ)+1/(r:ℝ)+Real.log (2*(r:ℝ))/(M:ℝ)+
    (r:ℝ)*Real.log (2*(r:ℝ))/((M:ℝ)*(N:ℝ))
  have hLog : 0 ≤ Real.log (2*(r:ℝ)) := by
    apply Real.log_nonneg
    have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    nlinarith
  have hB : 0 ≤ B := by
    dsimp [B]
    have hm : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    have hn : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
    positivity
  have hSquare := source_full_multigroup_logpower_minor_arc_sq
    G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂ hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact
    m₀ vmin C₀ L hvmin hL hC₀ hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    M N P Q hM hN hP hQ b₁ b₂ hb₁ hb₂ a r
    (-(k:ℝ)*theta-(a:ℝ)/(r:ℝ)) hr hcop hNear
  have hFreq : (a:ℝ)/(r:ℝ)+(-(k:ℝ)*theta-(a:ℝ)/(r:ℝ)) =
      -(k:ℝ)*theta := by ring
  dsimp only at hSquare
  rw [hFreq] at hSquare
  rw [← source_product_multiplier_integer434 M N P Q
    (sourceProductAtomMass G₁ S₁ k₁ V₁)
    (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂ k theta] at hSquare
  apply source_minor_bracket_to_power_saving _ L (C₀*Real.log K) Bsave B
    (norm_nonneg _) hL hB
  · simpa only [K,B,mul_assoc] using hSquare
  · exact hBracket
end Green64Analytic.CorrelationSquare

end

/-! ## SourceProductCard -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin
theorem source_explicit_product_card434 {α β : Type} (A : Finset α) (B : Finset β) :
    (A.product B).card = A.card * B.card := by
  exact Finset.card_product A B
end Green64Analytic.CorrelationMellin

end

/-! ## SourceOriginalBoxCount -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-- Direct cardinality bound for the genuine four-coordinate assignment,
without multiplying by numbers of represented source occurrences. -/
theorem source_original_four_dyadic_assignment_card434
    (N : ℕ) (Q : Finset SourceQuad434)
    (hQ : ∀ z ∈ Q, 0 < z.1.1 ∧ z.1.1 ≤ N ∧
      0 < z.1.2 ∧ z.1.2 ≤ N ∧ 0 < z.2.1 ∧ z.2.1 ≤ N ∧
      0 < z.2.2 ∧ z.2.2 ≤ N) :
    (Q.image sourceQuadDyadIndex434).card ≤ (N.log2+1)^4 := by
  classical
  have hlog (n : ℕ) (hn : 0 < n) (hle : n ≤ N) : n.log2 ≤ N.log2 := by
    by_contra hgt
    have hstep : N.log2+1 ≤ n.log2 := by omega
    have hp : 2^(N.log2+1) ≤ 2^n.log2 :=
      Nat.pow_le_pow_right (by omega) hstep
    have hlo := Nat.log2_self_le (Nat.ne_of_gt hn)
    have hhi : N < 2^(N.log2+1) := Nat.lt_log2_self
    omega
  let J := ((Finset.range (N.log2+1)).product (Finset.range (N.log2+1))).product
    ((Finset.range (N.log2+1)).product (Finset.range (N.log2+1)))
  have hsub : Q.image sourceQuadDyadIndex434 ⊆ J := by
    intro j hj
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hm,hmN,hs,hsN,hp,hpN,hr,hrN⟩ := hQ z hz
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        have := hlog _ hm hmN
        change z.1.1.log2 < N.log2+1
        omega
      · apply Finset.mem_range.mpr
        have := hlog _ hs hsN
        change z.1.2.log2 < N.log2+1
        omega
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        have := hlog _ hp hpN
        change z.2.1.log2 < N.log2+1
        omega
      · apply Finset.mem_range.mpr
        have := hlog _ hr hrN
        change z.2.2.log2 < N.log2+1
        omega
  calc
    _ ≤ J.card := Finset.card_le_card hsub
    _ = _ := by
      change (((Finset.range (N.log2+1)).product (Finset.range (N.log2+1))).product
        ((Finset.range (N.log2+1)).product (Finset.range (N.log2+1)))).card = _
      simp only [source_explicit_product_card434,Finset.card_range]
      ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceProductMultiplierSplit -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 4000000

/-- Exact split of the first product interval, preserving the actual shift. -/
theorem source_product_multiplier_split_first434
    (M N P1 P2 Q : ℕ) (u v : ℕ → ℝ) (b d : ℕ → ℂ) (k : ℤ) :
    sourceProductMultiplier434 M N (P1+P2) Q u v b d k =
    sourceProductMultiplier434 M N P1 Q u v b d k +
      sourceProductMultiplier434 (M+P1) N P2 Q u v b d k := by
  ext theta
  simp only [sourceProductMultiplier434,sourceFiniteShiftMultiplier434,
    ContinuousMap.sum_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,
    Finset.product_eq_sprod,Finset.sum_product,Finset.sum_range_add,
    sourceProductShiftCoefficient434,sourceProductShift434,Nat.add_assoc]

/-- Exact split of the second product interval. No joint coefficient
is introduced, so the two product laws remain independent. -/
theorem source_product_multiplier_split_second434
    (M N P Q1 Q2 : ℕ) (u v : ℕ → ℝ) (b d : ℕ → ℂ) (k : ℤ) :
    sourceProductMultiplier434 M N P (Q1+Q2) u v b d k =
    sourceProductMultiplier434 M N P Q1 u v b d k +
      sourceProductMultiplier434 M (N+Q1) P Q2 u v b d k := by
  ext theta
  simp only [sourceProductMultiplier434,sourceFiniteShiftMultiplier434,
    ContinuousMap.sum_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,
    Finset.product_eq_sprod,Finset.sum_product,Finset.sum_range_add,Finset.sum_add_distrib,
    sourceProductShiftCoefficient434,sourceProductShift434,Nat.add_assoc]

/-- Four dyadic rectangles cover a complete pair of source log cells. -/
theorem source_product_multiplier_four_block434
    (M N : ℕ) (u v : ℕ → ℝ) (b d : ℕ → ℂ) (k : ℤ) :
    sourceProductMultiplier434 M N (3*M) (3*N) u v b d k =
    (sourceProductMultiplier434 M N M N u v b d k +
      sourceProductMultiplier434 M (2*N) M (2*N) u v b d k) +
    (sourceProductMultiplier434 (2*M) N (2*M) N u v b d k +
      sourceProductMultiplier434 (2*M) (2*N) (2*M) (2*N) u v b d k) := by
  rw [show 3*M = M+2*M by omega,source_product_multiplier_split_first434]
  rw [show 3*N = N+2*N by omega,source_product_multiplier_split_second434,
    source_product_multiplier_split_second434]
  simp only [← two_mul]

/-- The finite four-block loss is explicit and independent of x or groups. -/
theorem source_product_multiplier_four_block_bound434
    (M N : ℕ) (u v : ℕ → ℝ) (b d : ℕ → ℂ) (k : ℤ)
    (theta : AddCircle (1:ℝ)) (K : ℝ)
    (h00 : ‖sourceProductMultiplier434 M N M N u v b d k theta‖ ≤ K)
    (h01 : ‖sourceProductMultiplier434 M (2*N) M (2*N) u v b d k theta‖ ≤ K)
    (h10 : ‖sourceProductMultiplier434 (2*M) N (2*M) N u v b d k theta‖ ≤ K)
    (h11 : ‖sourceProductMultiplier434 (2*M) (2*N) (2*M) (2*N) u v b d k theta‖ ≤ K) :
    ‖sourceProductMultiplier434 M N (3*M) (3*N) u v b d k theta‖ ≤ 4*K := by
  rw [source_product_multiplier_four_block434]
  simp only [ContinuousMap.add_apply]
  exact (norm_add_le _ _).trans
    ((add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans (by linarith))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceQSkipGroupFibre -/

section

open scoped BigOperators
namespace Green64Analytic.QSkipFactorial

/-- The one-band factorial bound for an arbitrary finite, labelled slot type. -/
theorem labelled_prime_fibre_card_le_factorial {I : Type} [Fintype I] [DecidableEq I]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (v : ℕ) :
    ((Finset.univ : Finset (I → {p : ℕ // p ∈ Q})).filter
       (fun a => (∏ i, (a i).val) = v)).card ≤ (Fintype.card I).factorial := by
  classical
  let S : Finset (I → {p : ℕ // p ∈ Q}) :=
    Finset.univ.filter (fun a => (∏ i, (a i).val) = v)
  let e := Fintype.equivFin I
  let conv : (I → {p : ℕ // p ∈ Q}) →
      (Fin (Fintype.card I) → {p : ℕ // p ∈ Q}) := fun a j => a (e.symm j)
  have hinj : Function.Injective conv := by
    intro a b h
    funext i
    have hi := congrFun h (e i)
    simpa [conv] using hi
  have hmap : Set.MapsTo conv (↑S) (↑(primeProductFibre (Fintype.card I) Q v)) := by
    intro a ha
    have hp : (∏ i, (a i).val) = v := (Finset.mem_filter.mp ha).2
    have heq : (∏ j : Fin (Fintype.card I), (conv a j).val) =
          (∏ i : I, (a i).val) := by
        simpa only [conv] using
          (Equiv.prod_comp e.symm (fun i : I => (a i).val))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.trans hp⟩
  have hsub : S.card ≤ (primeProductFibre (Fintype.card I) Q v).card :=
    Finset.card_le_card_of_injOn conv hmap (fun _ _ _ _ h => hinj h)
  exact hsub.trans (primeProductFibre_card_le_factorial _ Q hQ v)

/-- Source-compatible group slots, retaining every labelled occurrence. -/
abbrev BandAssignment (m : ℕ) (I : Fin m → Type)
    (Q : Fin m → Finset ℕ) :=
  (g : Fin m) → I g → {p : ℕ // p ∈ Q g}

noncomputable def bandProduct {m : ℕ} {I : Fin m → Type}
    [∀ g, Fintype (I g)] {Q : Fin m → Finset ℕ}
    (a : BandAssignment m I Q) (g : Fin m) : ℕ :=
  ∏ i, (a g i).val

noncomputable def allBandProduct {m : ℕ} {I : Fin m → Type}
    [∀ g, Fintype (I g)] {Q : Fin m → Finset ℕ}
    (a : BandAssignment m I Q) : ℕ := ∏ g, bandProduct a g

/-- The actual cross-band rigidity mechanism: disjoint prime supports imply
    equal bandwise products from equal TOTAL products, with repetitions. -/
theorem band_products_eq_of_disjoint {m : ℕ} {I : Fin m → Type}
    [∀ g, Fintype (I g)] (Q : Fin m → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (hdisj : ∀ g h p, p ∈ Q g → p ∈ Q h → g = h)
    (a b : BandAssignment m I Q)
    (heq : allBandProduct a = allBandProduct b) :
    ∀ g, bandProduct a g = bandProduct b g := by
  classical
  apply components_eq_of_cross_coprime
    (fun g => bandProduct a g) (fun g => bandProduct b g) heq
  intro g h hne
  unfold bandProduct
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro i
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro j
  apply (Nat.coprime_primes
    (hprime g (a g i).val (a g i).property)
    (hprime h (b h j).val (b h j).property)).mpr
  intro hp
  exact hne (hdisj g h (a g i).val (a g i).property
    (hp ▸ (b h j).property))

/-- Exact bound on the POINTWISE band-product assignment fibre. -/
theorem bandwise_fibre_card_le {m : ℕ} {I : Fin m → Type}
    [∀ g, Fintype (I g)] [∀ g, DecidableEq (I g)] (Q : Fin m → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (V : Fin m → ℕ) :
    ((Finset.univ : Finset (BandAssignment m I Q)).filter
      (fun a => ∀ g, bandProduct a g = V g)).card ≤
        ∏ g, (Fintype.card (I g)).factorial := by
  classical
  let S := (Finset.univ : Finset (BandAssignment m I Q)).filter
    (fun a => ∀ g, bandProduct a g = V g)
  let E : {a : BandAssignment m I Q // ∀ g, bandProduct a g = V g} ≃
      ((g : Fin m) → {ag : I g → {p : ℕ // p ∈ Q g} //
        (∏ i, (ag i).val) = V g}) :=
    { toFun := fun a g => ⟨a.val g, a.property g⟩
      invFun := fun b => ⟨fun g => (b g).val, fun g => (b g).property⟩
      left_inv := by intro a; rfl
      right_inv := by intro b; funext g; apply Subtype.ext; rfl }
  have hcard : S.card =
      ∏ g : Fin m, ((Finset.univ : Finset (I g → {p : ℕ // p ∈ Q g})).filter
        (fun ag => (∏ i, (ag i).val) = V g)).card := by
    have hs : S.card = Fintype.card
      {a : BandAssignment m I Q // ∀ g, bandProduct a g = V g} := by
      simpa [S, bandProduct] using
        (Fintype.card_subtype (fun a : BandAssignment m I Q =>
          ∀ g, bandProduct a g = V g)).symm
    rw [hs, Fintype.card_congr E, Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro g hg
    simpa using (Fintype.card_subtype
      (fun ag : I g → {p : ℕ // p ∈ Q g} =>
         (∏ i, (ag i).val) = V g))
  rw [hcard]
  apply Finset.prod_le_prod
  intro g hg
  exact labelled_prime_fibre_card_le_factorial (Q g) (hprime g) (V g)


/-- No labels are removed: the complete fixed-product fibre across pairwise
    disjoint prime bands has at most the product of slot factorials. -/
theorem total_band_fibre_card_le {m : ℕ} {I : Fin m → Type}
    [∀ g, Fintype (I g)] [∀ g, DecidableEq (I g)]
    (Q : Fin m → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (hdisj : ∀ g h p, p ∈ Q g → p ∈ Q h → g = h)
    (v : ℕ) :
    ((Finset.univ : Finset (BandAssignment m I Q)).filter
       (fun a => allBandProduct a = v)).card ≤
        ∏ g, (Fintype.card (I g)).factorial := by
  classical
  let S := (Finset.univ : Finset (BandAssignment m I Q)).filter
    (fun a => allBandProduct a = v)
  by_cases hs : S.Nonempty
  · obtain ⟨a₀, ha₀⟩ := hs
    let V : Fin m → ℕ := fun g => bandProduct a₀ g
    have hsub : S ⊆
       ((Finset.univ : Finset (BandAssignment m I Q)).filter
         (fun a => ∀ g, bandProduct a g = V g)) := by
      intro a ha
      have hp : allBandProduct a = v := (Finset.mem_filter.mp ha).2
      have hp₀ : allBandProduct a₀ = v := (Finset.mem_filter.mp ha₀).2

      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        band_products_eq_of_disjoint Q hprime hdisj a a₀ (hp.trans hp₀.symm)⟩
    exact (Finset.card_le_card hsub).trans (bandwise_fibre_card_le Q hprime V)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [S, he]

/-- The r-slot cap, with a full factorial for EVERY band even if few
    slots survived the allocation or designated-slot removal. -/
theorem total_band_fibre_card_le_factorial_pow {m : ℕ} {I : Fin m → Type}
    [∀ g, Fintype (I g)] [∀ g, DecidableEq (I g)]
    (Q : Fin m → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (hdisj : ∀ g h p, p ∈ Q g → p ∈ Q h → g = h)
    (r : ℕ) (hslots : ∀ g, Fintype.card (I g) ≤ r) (v : ℕ) :
    ((Finset.univ : Finset (BandAssignment m I Q)).filter
       (fun a => allBandProduct a = v)).card ≤ r.factorial ^ m := by
  calc
    _ ≤ ∏ g, (Fintype.card (I g)).factorial :=
      total_band_fibre_card_le Q hprime hdisj v
    _ ≤ ∏ _g : Fin m, r.factorial := by
      apply Finset.prod_le_prod
      intro g hg
      exact Nat.factorial_le (hslots g)
    _ = r.factorial ^ m := by simp

end Green64Analytic.QSkipFactorial

end

/-! ## SourceQSkipResidualNorm -/

section

open scoped BigOperators
namespace Green64Analytic.QSkipFactorial

/-- The complex modulus bound for a full source-shaped labelled fibre;
    no squarefree restriction or loss of repeated labels. -/
theorem band_fibre_weighted_norm_le_one {m : ℕ} {I : Fin m → Type}
    [∀ g, Fintype (I g)] [∀ g, DecidableEq (I g)]
    (Q : Fin m → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (hdisj : ∀ g h p, p ∈ Q g → p ∈ Q h → g = h)
    (r : ℕ) (hslots : ∀ g, Fintype.card (I g) ≤ r)
    (v : ℕ) (phase : BandAssignment m I Q → ℂ)
    (hphase : ∀ a, ‖phase a‖ ≤ 1)
    (normal : ℂ) (hnormal : ‖normal‖ * (r.factorial ^ m : ℝ) ≤ 1) :
    ‖∑ a ∈ ((Finset.univ : Finset (BandAssignment m I Q)).filter
        (fun a => allBandProduct a = v)), normal * phase a‖ ≤ 1 := by
  classical
  let S := (Finset.univ : Finset (BandAssignment m I Q)).filter
      (fun a => allBandProduct a = v)
  have hsum : ‖∑ a ∈ S, normal * phase a‖ ≤
      (S.card : ℝ) * ‖normal‖ := by
    calc
      _ ≤ ∑ a ∈ S, ‖normal * phase a‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ S, ‖normal‖ := by
        apply Finset.sum_le_sum
        intro a ha
        rw [norm_mul]
        calc
          ‖normal‖ * ‖phase a‖ ≤ ‖normal‖ * 1 :=
            mul_le_mul_of_nonneg_left (hphase a) (norm_nonneg normal)
          _ = ‖normal‖ := mul_one _
      _ = (S.card : ℝ) * ‖normal‖ := by simp
  have hcard : S.card ≤ r.factorial ^ m :=
    total_band_fibre_card_le_factorial_pow Q hprime hdisj r hslots v
  have hc : (S.card : ℝ) ≤ (r.factorial ^ m : ℝ) := by exact_mod_cast hcard
  calc
    ‖∑ a ∈ S, normal * phase a‖ ≤ (S.card : ℝ) * ‖normal‖ := hsum
    _ ≤ (r.factorial ^ m : ℝ) * ‖normal‖ :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖normal‖ * (r.factorial ^ m : ℝ) := mul_comm _ _
    _ ≤ 1 := hnormal

/-- Literal scalar from the source factorial formula, not an abstract
    normalization parameter. For original QSkip set r=6, m=d+1. -/
noncomputable def literalSourceFactorial (r m : ℕ) : ℂ :=
  ((∏ _j : Fin m, (1 : ℝ) / (r.factorial : ℝ)) : ℂ)

theorem literalSourceFactorial_norm_mul (r m : ℕ) :
    ‖literalSourceFactorial r m‖ * (r.factorial ^ m : ℝ) = 1 := by
  have hpos : (0 : ℝ) < (r.factorial : ℝ) := by positivity
  unfold literalSourceFactorial
  simp only [Finset.prod_const, Finset.card_fin, norm_pow, norm_div]
  have hfac : ‖(((r.factorial : ℝ) : ℂ))‖ = (r.factorial : ℝ) := by
    simpa [Complex.norm_real, abs_of_pos hpos]
  rw [hfac]
  norm_num
  field_simp

/-- Final abstract factorial-normalized complex fibre bound. The scalar
    is the literal source factorial formula, retaining all m band factors. -/
theorem literal_band_residual_norm_le_one {m : ℕ} {I : Fin m → Type}
    [∀ g, Fintype (I g)] [∀ g, DecidableEq (I g)]
    (Q : Fin m → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (hdisj : ∀ g h p, p ∈ Q g → p ∈ Q h → g = h)
    (r : ℕ) (hslots : ∀ g, Fintype.card (I g) ≤ r)
    (v : ℕ) (phase : BandAssignment m I Q → ℂ)
    (hphase : ∀ a, ‖phase a‖ ≤ 1) :
    ‖∑ a ∈ ((Finset.univ : Finset (BandAssignment m I Q)).filter
       (fun a => allBandProduct a = v)),
          literalSourceFactorial r m * phase a‖ ≤ 1 := by
  exact band_fibre_weighted_norm_le_one Q hprime hdisj r hslots v phase
    hphase (literalSourceFactorial r m)
      (le_of_eq (literalSourceFactorial_norm_mul r m))
end Green64Analytic.QSkipFactorial

end

/-! ## SourceQSkipOrderedBridge -/

section

open scoped BigOperators
namespace Green64Analytic.QSkipFactorial

/-- The literal original QSkip carrier after replacing the source's sorted
    label order by its pre-existing band map (no new prime choices). -/
abbrev SkipLabel (n : ℕ) (δ : Fin n → Bool) :=
  {z : Fin n // ¬ δ z = true}
abbrev GroupSlot (n m : ℕ) (δ : Fin n → Bool)
    (band : Fin n → Fin m) (g : Fin m) :=
  {z : SkipLabel n δ // band z.val = g}
abbrev GroupedOrderedQSkip (n m : ℕ) (δ : Fin n → Bool)
    (band : Fin n → Fin m) (Q : Fin m → Finset ℕ) :=
  (z : SkipLabel n δ) → {p : ℕ // p ∈ Q (band z.val)}

/-- Exact regrouping of the original dependent QSkip function type.
    Both directions preserve every skipped labelled slot and its prime. -/
noncomputable def groupedOrderedQSkipEquiv
    (n m : ℕ) (δ : Fin n → Bool) (band : Fin n → Fin m)
    (Q : Fin m → Finset ℕ) :
    GroupedOrderedQSkip n m δ band Q ≃
    BandAssignment m (GroupSlot n m δ band) Q :=
  { toFun := fun a g z => z.property ▸ (a z.val)
    invFun := fun b z => b (band z.val) ⟨z,rfl⟩
    left_inv := by intro a; funext z; rfl
    right_inv := by
      intro b
      funext g z
      rcases z with ⟨z,h⟩
      cases h
      rfl }

/-- The unchanged ordered source prime product is the full regrouped band
    product. This is independent of allocation and the presence of repeats. -/
theorem groupedOrderedQSkip_product_eq
    (n m : ℕ) (δ : Fin n → Bool) (band : Fin n → Fin m)
    (Q : Fin m → Finset ℕ) (a : GroupedOrderedQSkip n m δ band Q) :
    (∏ z : SkipLabel n δ, (a z).val) =
       allBandProduct (groupedOrderedQSkipEquiv n m δ band Q a) := by
  classical
  let e : SkipLabel n δ ≃
      (g : Fin m) × GroupSlot n m δ band g :=
    (Equiv.sigmaFiberEquiv (fun z : SkipLabel n δ => band z.val)).symm
  calc
    (∏ z : SkipLabel n δ, (a z).val) =
      ∏ x : (g : Fin m) × GroupSlot n m δ band g,
        (a x.2.val).val := by
      have heval (z : SkipLabel n δ) : (e z).2.val = z := rfl
      have hp : (∏ z : SkipLabel n δ, (a z).val) =
          (∏ z : SkipLabel n δ, (a (e z).2.val).val) := by
        apply Finset.prod_congr rfl
        intro z hz
        rw [heval]
      exact hp.trans (Equiv.prod_comp e
        (fun x : (g : Fin m) × GroupSlot n m δ band g =>
          (a x.2.val).val))
    _ = allBandProduct (groupedOrderedQSkipEquiv n m δ band Q a) := by
      rw [Fintype.prod_sigma]
      unfold allBandProduct
      apply Finset.prod_congr rfl
      intro g hg
      unfold bandProduct
      apply Finset.prod_congr rfl
      intro z hz
      rcases z with ⟨z, hzband⟩
      cases hzband
      rfl


/-- Residual bound for EXACT dependent labelled skip tuples after the
    band reindex: the only remaining source prerequisites are prime bands,
    their original disjointness, and the original <=r slot injection. -/
theorem groupedOrderedQSkip_norm_le_one
    (n m : ℕ) (δ : Fin n → Bool) (band : Fin n → Fin m)
    (Q : Fin m → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (hdisj : ∀ g h p, p ∈ Q g → p ∈ Q h → g = h)
    (r : ℕ) (hslots : ∀ g, Fintype.card (GroupSlot n m δ band g) ≤ r)
    (v : ℕ) (phase : GroupedOrderedQSkip n m δ band Q → ℂ)
    (hphase : ∀ a, ‖phase a‖ ≤ 1) :
    ‖∑ a : GroupedOrderedQSkip n m δ band Q,
       if (∏ z : SkipLabel n δ, (a z).val) = v then
         literalSourceFactorial r m * phase a else 0‖ ≤ 1 := by
  classical
  let e := groupedOrderedQSkipEquiv n m δ band Q
  have hsum :
    (∑ a : GroupedOrderedQSkip n m δ band Q,
      if (∏ z : SkipLabel n δ, (a z).val) = v then
        literalSourceFactorial r m * phase a else 0) =
    (∑ a : BandAssignment m (GroupSlot n m δ band) Q,
      if allBandProduct a = v then
        literalSourceFactorial r m * phase (e.symm a) else 0) := by

    apply Fintype.sum_equiv e
    intro a
    simp only [groupedOrderedQSkip_product_eq, e.symm_apply_apply]
    rfl
  rw [hsum]
  have hs := literal_band_residual_norm_le_one Q hprime hdisj
    r hslots v (fun a => phase (e.symm a)) (fun a => hphase (e.symm a))
  simpa only [Finset.sum_filter] using hs

/-- All retained Fourier phases have unit modulus at every real frequency,
    including a totally skipped pattern and repeated primes. -/
theorem groupedSkip_fourier_phase_norm
    (n m : ℕ) (δ : Fin n → Bool) (band : Fin n → Fin m)
    (Q : Fin m → Finset ℕ) (a : GroupedOrderedQSkip n m δ band Q)
    (freq : SkipLabel n δ → ℝ) :
    ‖∏ z : SkipLabel n δ,
      (Real.fourierChar (Real.log ((a z).val : ℝ) * freq z) : ℂ)‖ = 1 := by
  simp

/-- Complete complex Fourier fibre estimate on the literal skipped-label
    dependent type, for any real source frequency allocation. -/
theorem groupedSkip_fourier_fibre_norm_le_one
    (n m : ℕ) (δ : Fin n → Bool) (band : Fin n → Fin m)
    (Q : Fin m → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (hdisj : ∀ g h p, p ∈ Q g → p ∈ Q h → g = h)
    (r : ℕ) (hslots : ∀ g, Fintype.card (GroupSlot n m δ band g) ≤ r)
    (v : ℕ) (freq : SkipLabel n δ → ℝ) :
    ‖∑ a : GroupedOrderedQSkip n m δ band Q,
       if (∏ z : SkipLabel n δ, (a z).val) = v then
         literalSourceFactorial r m *
         (∏ z : SkipLabel n δ,
           (Real.fourierChar (Real.log ((a z).val : ℝ) * freq z) : ℂ))
       else 0‖ ≤ 1 := by
  apply groupedOrderedQSkip_norm_le_one n m δ band Q hprime hdisj
    r hslots v
  intro a
  rw [groupedSkip_fourier_phase_norm n m δ band Q a freq]

/-- The full r-slot cap follows solely from an INJECTIVE original
    (band,slot)-label encoding; deleting slots cannot increase it. -/
theorem groupedSkip_slot_card_le
    (n m r : ℕ) (δ : Fin n → Bool)
    (band : Fin n → Fin m) (slot : Fin n → Fin r)
    (hlabel : Function.Injective (fun z => (band z, slot z))) :
    ∀ g, Fintype.card (GroupSlot n m δ band g) ≤ r := by
  intro g
  have hcard : Fintype.card (GroupSlot n m δ band g) ≤ Fintype.card (Fin r) := by
    apply Fintype.card_le_of_injective
      (fun z : GroupSlot n m δ band g => slot z.val.val)
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply hlabel
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact hxy
  simpa using hcard

end Green64Analytic.QSkipFactorial

end

/-! ## SourceQSkipLiteralSourcePort -/

section

open scoped BigOperators Classical FourierTransform
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal

/-- Literal port: SourcePhysicalSlotPhases.sourceSlotFrequency. -/
noncomputable def sourceSlotFrequency {I : Type} [Fintype I] [LT I] [DecidableLT I]
    (s ξ : I → ℝ) (δ : I → Bool) (j : I) : ℝ :=
  -ξ j/s j - (if δ j then (∑ i, if j < i then ξ i/s i else 0) else 0)

/-- Literal port: SourcePhysicalOrderedGlobal.OrderedQSkip. -/
abbrev OrderedQSkip (n : ℕ) (Q : Fin n → Finset ℕ) (δ : Fin n → Bool) :=
  (i : {i : Fin n // ¬ δ i = true}) → {p // p ∈ Q i.val}

/-- Literal port: SourcePhysicalOrderedGlobal.orderedSkipProduct. -/
noncomputable def orderedSkipProduct {n : ℕ} {Q : Fin n → Finset ℕ}
    {δ : Fin n → Bool} (a : OrderedQSkip n Q δ) : ℕ := ∏ i, (a i).val

/-- Literal port: SourcePhysicalOrderedGlobal.orderedSkipPhase. -/
noncomputable def orderedSkipPhase {n : ℕ} {Q : Fin n → Finset ℕ}
    {δ : Fin n → Bool} (s ξ : Fin n → ℝ) (a : OrderedQSkip n Q δ) : ℂ :=
  ∏ i, (Real.fourierChar (Real.log (a i).val * sourceSlotFrequency s ξ δ i.val) : ℂ)
/-- Literal port: SourcePhysicalEndpointFibres.sourceEndpointFibre. -/
noncomputable def sourceEndpointFibre {A : Type} (S : Finset A)
    (endpoint : A → ℕ) (weight : A → ℂ) (v : ℕ) : ℂ :=
  ∑ a ∈ S with endpoint a = v, weight a

/-- Literal port: SourcePhysicalActualGlobalIntegral.sourceActualSortedFactorial. -/
noncomputable def sourceActualSortedFactorial (r d : ℕ) : ℂ :=
  ((∏ _j : Fin (d+1), (1:ℝ)/(r.factorial:ℝ)):ℂ)

theorem source_actual_sorted_factorial_eq_literal434 (r d : ℕ) :
    sourceActualSortedFactorial r d =
      Green64Analytic.QSkipFactorial.literalSourceFactorial r (d+1) := rfl

end Green64Analytic.ShiftTwoTerminal

namespace Green64Analytic.QSkipFactorial
open Green64Analytic.ShiftTwoTerminal

/-- Exact original source-named QSkip fibre sum, with the existing
sourceSlotFrequency and full factorial. The final actual-sorted-Q
specialization still requires its original native label/band theorem. -/
theorem original_ordered_QSkip_source_fibre_bound434
    (r d n : ℕ) (δ : Fin n → Bool)
    (band : Fin n → Fin (d+1)) (slot : Fin n → Fin r)
    (Q : Fin (d+1) → Finset ℕ)
    (hprime : ∀ g p, p ∈ Q g → p.Prime)
    (hdisj : ∀ g h p, p ∈ Q g → p ∈ Q h → g = h)
    (hlabel : Function.Injective (fun z => (band z, slot z)))
    (s ξ : Fin n → ℝ) (v : ℕ) :
    ‖sourceEndpointFibre
        (Finset.univ : Finset (OrderedQSkip n (fun z => Q (band z)) δ))
        orderedSkipProduct
        (fun a => sourceActualSortedFactorial r d * orderedSkipPhase s ξ a) v‖ ≤ 1 := by
  classical
  have hslots := groupedSkip_slot_card_le n (d+1) r δ band slot hlabel
  have hphase (a : GroupedOrderedQSkip n (d+1) δ band Q) :
      ‖orderedSkipPhase (Q := fun z => Q (band z)) (δ := δ) s ξ a‖ ≤ 1 := by
    have h := groupedSkip_fourier_phase_norm n (d+1) δ band Q a
      (fun z => sourceSlotFrequency s ξ δ z.val)
    simpa only [orderedSkipPhase] using h.le
  have hz := groupedOrderedQSkip_norm_le_one n (d+1) δ band Q
    hprime hdisj r hslots v
    (fun a => orderedSkipPhase (Q := fun z => Q (band z)) (δ := δ) s ξ a) hphase
  rw [source_actual_sorted_factorial_eq_literal434] 
  unfold sourceEndpointFibre
  simp only [Finset.sum_filter]
  simpa only [orderedSkipProduct] using hz
end Green64Analytic.QSkipFactorial

end

end

