module

public import Green64.Library.Weights.Part103

@[expose] public section

/-!
# Weights / Part104

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## Mass005 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics
open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceH2GroupHP.lean; original line 109. -/
theorem source_literal_hp_eq_original
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (hDisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset G)) P) :
    sourceLiteralHP P =
      ∏ g : G,
        ((∏ p ∈ P g, sourceGroupEulerF p) *
          ((∑ p ∈ P g, (((p:ℝ)-(1/2:ℝ))⁻¹)) /
            (∑ p ∈ P g, (p:ℝ)⁻¹))) := by
  classical
  unfold sourceLiteralHP
  rw [Finset.prod_biUnion hDisj, ← Finset.prod_mul_distrib]



/- Exact source owner: SourceShiftTwoXAGroupMassUpper.lean; original line 99. -/
theorem source_original_group_harmonic_mass_product
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (hDisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset G)) P) :
    sourceLiteralHP P =
      ∏ g : G, sourceOriginalGroupHarmonicMass (P g) := by
  rw [source_literal_hp_eq_original P hDisj]
  rfl

/- The actual one-prime odd event has harmonic mass one, so its
normalized mass is bounded below by a fixed, group-independent constant. -/



/- Exact source owner: SourcePGlobalActualEulerHP.lean; original line 10. -/
theorem source_original_global_actual_P_harmonic_tsum_eq_HP
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h3 : ∀ g p, p ∈ P g → 3 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    sourceOriginalPHarmonicTsum P = sourceLiteralHP P := by
  classical
  let V (g : G) := {p // p ∈ P g} → ℕ
  let f (g : G) (e : V g) : ℝ :=
    shiftTwoOriginalGroupFactor (P g)
      (sourceOriginalPPrimePowerProduct (P g) e) /
      ((sourceOriginalPPrimePowerProduct (P g) e:ℝ))
  have hs (g : G) : Summable (f g) :=
    (source_original_P_group_harmonic_tsum_le_Hg
      (P g) (hPrime g) (h3 g) (hPn g)).1
  have hn (g : G) (e : V g) : 0 ≤ f g e := by
    dsimp [f]
    simpa only [div_eq_mul_inv] using
      (source_original_P_harmonic_term_nonneg
        (P g) (hPrime g) (hPn g) e)
  have hProduct := source_tsum_pi_finite_product V f hs hn
  have hGroup (g : G) :
      (∑' e : V g, f g e) =
        sourceOriginalGroupHarmonicMass (P g) :=
    source_original_P_group_harmonic_tsum_eq_Hg
      (P g) (hPrime g) (h3 g) (hPn g)
  have hSetDisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset G)) P := by
    intro g hg h hh hne
    apply Finset.disjoint_left.mpr
    intro p hpg hph
    exact hne (hDisj g h p hpg hph)
  calc
    sourceOriginalPHarmonicTsum P =
      ∑' e : (g : G) → V g,
        ∏ g : G, f g (e g) :=
      source_original_P_global_weighted_tsum_group_reindex
        P hPrime hDisj
    _ = ∏ g : G, ∑' e : V g, f g e := hProduct.2
    _ = ∏ g : G, sourceOriginalGroupHarmonicMass (P g) := by
      apply Finset.prod_congr rfl
      intro g hg
      exact hGroup g
    _ = sourceLiteralHP P :=
      (source_original_group_harmonic_mass_product P hSetDisj).symm



/- Exact source owner: SourcePGlobalNormalizedActualLaw.lean; original line 10. -/
theorem source_original_global_actual_P_normalized_harmonic_law
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h3 : ∀ g p, p ∈ P g → 3 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    Summable (fun n : sourceOriginalPSupported (Finset.univ.biUnion P) =>
      sourceOriginalW1 P n.val / (n.val:ℝ)) ∧
    0 < sourceLiteralHP P ∧
    (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      (sourceOriginalW1 P n.val / (n.val:ℝ)) /
        sourceLiteralHP P) = 1 := by
  classical
  let Pall : Finset ℕ := Finset.univ.biUnion P
  have hAll : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPrime g p hpg
  let E : ((g : G) → {p // p ∈ P g} → ℕ) ≃
      sourceOriginalPSupported Pall :=
    (sourceOriginalPDisjointExponentEquiv P hDisj).trans
      (source_original_P_power_equiv Pall hAll)
  let v (g : G) := {p // p ∈ P g} → ℕ
  let f (g : G) (e : v g) : ℝ :=
    shiftTwoOriginalGroupFactor (P g)
      (sourceOriginalPPrimePowerProduct (P g) e) /
      ((sourceOriginalPPrimePowerProduct (P g) e:ℝ))
  have hs (g : G) : Summable (f g) :=
    (source_original_P_group_harmonic_tsum_le_Hg
      (P g) (hPrime g) (h3 g) (hPn g)).1
  have hn (g : G) (e : v g) : 0 ≤ f g e := by
    dsimp [f]
    simpa only [div_eq_mul_inv] using
      source_original_P_harmonic_term_nonneg (P g)
        (hPrime g) (hPn g) e
  have hProd := source_tsum_pi_finite_product v f hs hn
  let F : sourceOriginalPSupported Pall → ℝ :=
    fun n => sourceOriginalW1 P n.val / (n.val:ℝ)
  have hPoint (e : (g : G) → v g) :
      F (E e) = ∏ g : G, f g (e g) := by
    dsimp [F,E,f]
    change
      sourceOriginalW1 P
        (sourceOriginalPPrimePowerProduct Pall
          (sourceOriginalPDisjointExponentEquiv P hDisj e)) /
          ((sourceOriginalPPrimePowerProduct Pall
            (sourceOriginalPDisjointExponentEquiv P hDisj e)):ℝ) = _
    rw [← source_original_P_global_vector_product_eq
      P hPrime hDisj e]
    exact source_original_P_global_integer_harmonic_factorization
      P hPrime hDisj e
  have hFull : Summable F := by
    apply (E.summable_iff).mp
    change Summable (F ∘ E)
    have heq : (F ∘ E) = (fun e : (g : G) → v g =>
        ∏ g : G, f g (e g)) := by
      funext e
      exact hPoint e
    rw [heq]
    exact hProd.1
  have hProductLower :
      (1:ℝ) ≤ ∏ p ∈ Pall, sourceGroupEulerF p := by
    apply Finset.one_le_prod₀
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact source_group_euler_factor_one_le p (h3 g p hpg)
  have hHPPos : 0 < sourceLiteralHP P :=
    lt_of_lt_of_le (by norm_num)
      (hProductLower.trans (source_literal_hp_ge_base P h3 hPn))
  refine ⟨hFull, hHPPos, ?_⟩
  rw [tsum_div_const]
  change sourceOriginalPHarmonicTsum P / sourceLiteralHP P = 1
  rw [source_original_global_actual_P_harmonic_tsum_eq_HP
    P hPrime h3 hPn hDisj]
  exact div_self (ne_of_gt hHPPos)



/- Exact source owner: SourcePGlobalActualOddFloor.lean; original line 12. -/
theorem source_original_P_global_actual_odd_harmonic_floor
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h3 : ∀ g p, p ∈ P g → 3 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (i : G) (δ : ℝ)
    (hHg : 0 < sourceOriginalGroupHarmonicMass (P i))
    (hOdd : δ ≤
      (∑' n : sourceOriginalPOddSupported (P i),
        shiftTwoOriginalGroupFactor (P i) n.val.val /
          (n.val.val:ℝ)) / sourceOriginalGroupHarmonicMass (P i))
    (hEven : δ ≤
      (∑' n : sourceOriginalPEvenSupported (P i),
        shiftTwoOriginalGroupFactor (P i) n.val.val /
          (n.val.val:ℝ)) / sourceOriginalGroupHarmonicMass (P i)) :
    δ ≤
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) n.val)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
        sourceLiteralHP P := by
  classical
  let A (g : G) := {p // p ∈ P g} → ℕ
  let f (g : G) (e : A g) : ℝ :=
    shiftTwoOriginalGroupFactor (P g)
      (sourceOriginalPPrimePowerProduct (P g) e) /
      ((sourceOriginalPPrimePowerProduct (P g) e):ℝ)
  let k (g : G) (e : A g) : ℕ :=
    sourceOriginalPParityExponent (P g)
      (sourceOriginalPPrimePowerProduct (P g) e)
  have hf (g : G) : Summable (f g) :=
    (source_original_P_group_harmonic_tsum_le_Hg
      (P g) (hPrime g) (h3 g) (hPn g)).1
  have hn (g : G) (e : A g) : 0 ≤ f g e := by
    dsimp [f]
    simpa only [div_eq_mul_inv] using
      source_original_P_harmonic_term_nonneg
        (P g) (hPrime g) (hPn g) e
  have hLocal := source_original_P_group_true_vector_flag_floor
    (P i) δ (hPrime i) (h3 i) (hPn i) hHg hOdd hEven
  have hProdOdd := source_conditional_finite_pi_odd_tsum_floor
    A f k i δ hf hn (by
      intro b
      exact hLocal b)
  have hTotal :
      (∑' e : (g : G) → A g, ∏ g : G, f g (e g)) =
        sourceLiteralHP P := by
    calc
      _ = sourceOriginalPHarmonicTsum P :=
        (source_original_P_global_weighted_tsum_group_reindex
          P hPrime hDisj).symm
      _ = sourceLiteralHP P :=
        source_original_global_actual_P_harmonic_tsum_eq_HP
          P hPrime h3 hPn hDisj
  have hOddReindex :
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) n.val)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) =
      (∑' e : (g : G) → A g,
        if Odd (∑ g : G, k g (e g))
        then ∏ g : G, f g (e g) else 0) := by
    exact source_original_P_global_actual_odd_tsum_reindex
      P hPrime hDisj
  have hHP : 0 < sourceLiteralHP P :=
    (source_original_global_actual_P_normalized_harmonic_law
      P hPrime h3 hPn hDisj).2.1
  apply (le_div_iff₀ hHP).2
  calc
    δ * sourceLiteralHP P =
      δ * (∑' e : (g : G) → A g,
        ∏ g : G, f g (e g)) := by rw [hTotal]
    _ ≤ ∑' e : (g : G) → A g,
        if Odd (∑ g : G, k g (e g))
        then ∏ g : G, f g (e g) else 0 := hProdOdd
    _ = ∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) n.val)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0 :=
      hOddReindex.symm



/- Exact source owner: SourceShiftTwoXAGroupEvenPairs.lean; original line 9. -/
theorem source_group_parity_two_primes
    (P : Finset ℕ) (p q : ℕ) (hp : p.Prime)
    (hq : q.Prime) (hpP : p ∈ P) (hqP : q ∈ P) :
    sourceOriginalPParityExponent P (p*q) = 2 := by
  unfold sourceOriginalPParityExponent
  rw [Nat.factorization_mul hp.ne_zero hq.ne_zero]
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  simp [Nat.Prime.factorization hp, Nat.Prime.factorization hq,
    Finsupp.single_apply, Finset.sum_ite, hpP, hqP]

/- The cross pairs are uniquely indexed by their actual integer
product. Without this injectivity their total mass could overcount. -/



/- Exact source owner: SourceShiftTwoXAGroupEvenPairs.lean; original line 55. -/
theorem source_group_cross_image_even
    (P A B : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (hA : A ⊆ P) (hB : B ⊆ P)
    (n : ℕ) (hn : n ∈ sourceOriginalGroupCrossEvenImages A B) :
    sourceOriginalPParityExponent P n = 2 := by
  rcases Finset.mem_image.mp hn with ⟨⟨p,q⟩, hpq, rfl⟩
  rcases Finset.mem_product.mp hpq with ⟨hp,hq⟩
  exact source_group_parity_two_primes P p q
    (hPrime p (hA hp)) (hPrime q (hB hq)) (hA hp) (hB hq)



/- Exact source owner: SourcePActualParityAtoms.lean; original line 30. -/
theorem source_original_P_cross_even_supported
    (P A B : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (hA : A ⊆ P) (hB : B ⊆ P)
    (n : ℕ) (hn : n ∈ sourceOriginalGroupCrossEvenImages A B) :
    n ≠ 0 ∧ n.primeFactors ⊆ P := by
  rcases Finset.mem_image.mp hn with ⟨⟨p,q⟩,hpq, rfl⟩
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hpq
  have hpPrime := hPrime p (hA hp)
  have hqPrime := hPrime q (hB hq)
  constructor
  · exact mul_ne_zero hpPrime.ne_zero hqPrime.ne_zero
  · intro k hk
    have hData := Nat.mem_primeFactors.mp hk
    rcases (Nat.Prime.dvd_mul hData.1).mp hData.2.1 with hd | hd
    · have hEq : k = p :=
        (Nat.prime_dvd_prime_iff_eq hData.1 hpPrime).mp hd
      exact hEq ▸ hA hp
    · have hEq : k = q :=
        (Nat.prime_dvd_prime_iff_eq hData.1 hqPrime).mp hd
      exact hEq ▸ hB hq



/- Exact source owner: SourcePActualEvenTsum.lean; original line 14. -/
noncomputable def sourceOriginalPEvenCross
    (P A B : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (hA : A ⊆ P) (hB : B ⊆ P)
    (z : {n // n ∈ sourceOriginalGroupCrossEvenImages A B}) :
    sourceOriginalPEvenSupported P :=
  ⟨⟨z.val,
    (source_original_P_cross_even_supported P A B
      hPrime hA hB z.val z.property).1,
    (source_original_P_cross_even_supported P A B
      hPrime hA hB z.val z.property).2⟩,
    by
      change Even (sourceOriginalPParityExponent P z.val)
      rw [source_group_cross_image_even
        P A B hPrime hA hB z.val z.property]
      norm_num⟩



/- Exact source owner: SourcePActualEvenTsum.lean; original line 30. -/
theorem source_original_P_even_cross_injective
    (P A B : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (hA : A ⊆ P) (hB : B ⊆ P) :
    Function.Injective (sourceOriginalPEvenCross P A B hPrime hA hB) := by
  intro z w h
  apply Subtype.ext
  exact congrArg
    (fun n : sourceOriginalPEvenSupported P => n.val.val) h



/- Exact source owner: SourcePActualHarmonicBound.lean; original line 11. -/
theorem source_original_actual_P_group_harmonic_tsum_le_Hg
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty) :
    Summable (fun n : sourceOriginalPSupported P =>
      shiftTwoOriginalGroupFactor P n.val / (n.val:ℝ)) ∧
    (∑' n : sourceOriginalPSupported P,
      shiftTwoOriginalGroupFactor P n.val / (n.val:ℝ)) ≤
        sourceOriginalGroupHarmonicMass P := by
  let E := source_original_P_power_equiv P hPrime
  let f : sourceOriginalPSupported P → ℝ :=
    fun n => shiftTwoOriginalGroupFactor P n.val / (n.val:ℝ)
  have hVec := source_original_P_group_harmonic_tsum_le_Hg
    P hPrime h3 hPn
  have hMatch : (f ∘ E) =
      fun e : {p // p ∈ P} → ℕ =>
        shiftTwoOriginalGroupFactor P
          (sourceOriginalPPrimePowerProduct P e) *
          ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹) := by
    funext e
    simp only [Function.comp_apply]
    rfl
  have hSumm : Summable f :=
    (E.summable_iff).mp (by rw [hMatch]; exact hVec.1)
  have hTsum : (∑' n : sourceOriginalPSupported P, f n) =
      ∑' e : {p // p ∈ P} → ℕ, (f ∘ E) e :=
    (E.tsum_eq f).symm
  have hBound : (∑' n : sourceOriginalPSupported P, f n) ≤
      sourceOriginalGroupHarmonicMass P := by
    rw [hTsum]
    change (∑' e : {p // p ∈ P} → ℕ, (f ∘ E) e) ≤ _
    rw [hMatch]
    exact hVec.2
  exact ⟨hSumm,hBound⟩



/- Exact source owner: SourcePActualEvenTsum.lean; original line 39. -/
theorem source_original_actual_P_even_summable
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty) :
    Summable (fun n : sourceOriginalPEvenSupported P =>
      shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) := by
  have hf := (source_original_actual_P_group_harmonic_tsum_le_Hg
    P hPrime h3 hPn).1
  exact hf.subtype (fun n : sourceOriginalPSupported P =>
    Even (sourceOriginalPParityExponent P n.val))
/- The genuine even-Omega integer harmonic sum dominates
the exact two-distinct-prime atom mass VA*VB/Vg. -/



/- Exact source owner: SourcePActualEvenTsum.lean; original line 50. -/
theorem source_original_actual_P_even_mass_ge_distinct_pair
    (P A B : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty)
    (hA : A ⊆ P) (hB : B ⊆ P) (hAB : Disjoint A B) :
    ((∑ p ∈ A, (p:ℝ)⁻¹) * (∑ q ∈ B, (q:ℝ)⁻¹)) /
      (∑ r ∈ P, (r:ℝ)⁻¹) ≤
    ∑' n : sourceOriginalPEvenSupported P,
      shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ) := by
  classical
  let S := sourceOriginalGroupCrossEvenImages A B
  let F : sourceOriginalPEvenSupported P → ℝ :=
    fun n => shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)
  let f : {n // n ∈ S} → sourceOriginalPEvenSupported P :=
    sourceOriginalPEvenCross P A B hPrime hA hB
  have hf : Summable F :=
    source_original_actual_P_even_summable P hPrime h3 hPn
  have hpositive (n : sourceOriginalPEvenSupported P) :
      0 ≤ F n := by
    dsimp [F]
    unfold shiftTwoOriginalGroupFactor
    positivity
  have hfinite :
      (∑ z : {n // n ∈ S}, F (f z)) ≤ ∑' n, F n := by
    let ss : Finset (sourceOriginalPEvenSupported P) :=
      Finset.univ.image f
    have hSum : (∑ n ∈ ss, F n) =
        ∑ z : {n // n ∈ S}, F (f z) := by
      dsimp [ss]
      rw [Finset.sum_image (fun a ha b hb hab =>
        source_original_P_even_cross_injective P A B
          hPrime hA hB hab)]
    rw [← hSum]
    exact hf.sum_le_tsum ss (fun n hn => hpositive n)
  have hAtom :
      (∑ z : {n // n ∈ S}, F (f z)) =
        (∑ n ∈ S, (n:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P n) := by
    have hh : (∑ z : {n // n ∈ S}, F (f z)) =
        ∑ z : {n // n ∈ S},
          (z.val:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P z.val := by
      apply Finset.sum_congr rfl
      intro z hz
      dsimp [F, f, sourceOriginalPEvenCross]
      ring
    rw [hh]
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach S
        (fun n => (n:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P n))
  have hMass := source_group_actual_even_cross_harmonic_mass
    P A B hPrime hA hB hAB
  rw [hAtom, hMass] at hfinite
  exact hfinite



/- Exact source owner: SourcePActualParityAtoms.lean; original line 9. -/
noncomputable def sourceOriginalPPrimeSupported
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (z : {p // p ∈ P}) : sourceOriginalPSupported P :=
  ⟨z.val, (hPrime z.val z.property).ne_zero, by
    intro q hq
    have hqq := (Nat.mem_primeFactors.mp hq)
    have hEq : q = z.val :=
      (Nat.prime_dvd_prime_iff_eq hqq.1
        (hPrime z.val z.property)).mp hqq.2.1
    exact hEq ▸ z.property⟩



/- Exact source owner: SourceShiftTwoXAGroupParityAtoms.lean; original line 38. -/
theorem source_group_parity_single_prime
    (P : Finset ℕ) (p : ℕ)
    (hPrime : p.Prime) (hp : p ∈ P) :
    sourceOriginalPParityExponent P p = 1 := by
  classical
  unfold sourceOriginalPParityExponent
  simp [Nat.Prime.factorization hPrime, Finsupp.single_apply,
    Finset.sum_ite, hp]

/- Distinct group primes: omega is two, even if the harmonic
weight is the same as at multiplicity one when q0 = 1/2. -/



/- Exact source owner: SourcePActualOddTsum.lean; original line 13. -/
noncomputable def sourceOriginalPOddSingle
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (z : {p // p ∈ P}) : sourceOriginalPOddSupported P :=
  ⟨sourceOriginalPPrimeSupported P hPrime z, by
    change Odd (sourceOriginalPParityExponent P z.val)
    rw [source_group_parity_single_prime P z.val
      (hPrime z.val z.property) z.property]
    norm_num⟩



/- Exact source owner: SourcePActualParityAtoms.lean; original line 20. -/
theorem source_original_P_prime_supported_injective
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) :
    Function.Injective (sourceOriginalPPrimeSupported P hPrime) := by
  intro z w h
  apply Subtype.ext
  exact congrArg
    (fun n : sourceOriginalPSupported P => n.val) h

/- Every source pair p*q with p in A and q in B is an actual
positive P-supported integer, both primes distinct by hAB. -/



/- Exact source owner: SourcePActualOddTsum.lean; original line 22. -/
theorem source_original_P_odd_single_injective
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) :
    Function.Injective (sourceOriginalPOddSingle P hPrime) := by
  intro z w h
  apply (source_original_P_prime_supported_injective P hPrime)
  exact congrArg Subtype.val h

/- Summability for the real, unmodified W1 odd-Ω harmonic sum. -/



/- Exact source owner: SourcePActualOddTsum.lean; original line 30. -/
theorem source_original_actual_P_odd_summable
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty) :
    Summable (fun n : sourceOriginalPOddSupported P =>
      shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) := by
  have hf := (source_original_actual_P_group_harmonic_tsum_le_Hg
    P hPrime h3 hPn).1
  exact hf.subtype (fun n : sourceOriginalPSupported P =>
    Odd (sourceOriginalPParityExponent P n.val))
/- The odd genuine integer event includes all single-prime
terms; the exact original unnormalized mass of these terms is 1. -/



/- Exact source owner: SourcePActualOddTsum.lean; original line 41. -/
theorem source_original_actual_P_odd_mass_ge_one
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty) :
    1 ≤ ∑' n : sourceOriginalPOddSupported P,
      shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ) := by
  classical
  let F : sourceOriginalPOddSupported P → ℝ :=
    fun n => shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)
  let f : {p // p ∈ P} → sourceOriginalPOddSupported P :=
    sourceOriginalPOddSingle P hPrime
  have hf : Summable F :=
    source_original_actual_P_odd_summable P hPrime h3 hPn
  have hpositive (n : sourceOriginalPOddSupported P) :
      0 ≤ F n := by
    dsimp [F]
    unfold shiftTwoOriginalGroupFactor
    positivity
  have hfinite : (∑ z : {p // p ∈ P}, F (f z)) ≤ ∑' n, F n := by
    let s : Finset (sourceOriginalPOddSupported P) :=
      Finset.univ.image f
    have hSum : (∑ n ∈ s, F n) = ∑ z : {p // p ∈ P}, F (f z) := by
      dsimp [s]
      rw [Finset.sum_image (fun a ha b hb hab =>
        source_original_P_odd_single_injective P hPrime hab)]
    rw [← hSum]
    exact hf.sum_le_tsum s (fun n hn => hpositive n)
  have hExact : (∑ z : {p // p ∈ P}, F (f z)) = 1 := by
    have hAttach :
        (∑ z : {p // p ∈ P}, F (f z)) =
          ∑ p ∈ P, (p:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P p := by
      have hh :
          (∑ z : {p // p ∈ P}, F (f z)) =
          (∑ z : {p // p ∈ P},
            (z.val:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P z.val) := by
        apply Finset.sum_congr rfl
        intro z hz
        dsimp [F, f, sourceOriginalPOddSingle, sourceOriginalPPrimeSupported]
        ring
      rw [hh]
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach P
          (fun p => (p:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P p))
    rw [hAttach]
    exact source_group_actual_odd_single_harmonic_mass P hPrime hPn
  exact hExact ▸ hfinite



/- Exact source owner: SourcePActualGroupParityFloor.lean; original line 11. -/
theorem source_original_actual_P_parity_atoms_le_tsum
    (P A B : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty)
    (hA : A ⊆ P) (hB : B ⊆ P) (hAB : Disjoint A B)
    (hH : 0 < sourceOriginalGroupHarmonicMass P) :
    ((∑ p ∈ P, (p:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P p) /
      sourceOriginalGroupHarmonicMass P ≤
      (∑' n : sourceOriginalPOddSupported P,
        shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) /
          sourceOriginalGroupHarmonicMass P) ∧
    ((∑ n ∈ sourceOriginalGroupCrossEvenImages A B,
        (n:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P n) /
      sourceOriginalGroupHarmonicMass P ≤
      (∑' n : sourceOriginalPEvenSupported P,
        shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) /
          sourceOriginalGroupHarmonicMass P) := by
  have hOdd := source_original_actual_P_odd_mass_ge_one
    P hPrime h3 hPn
  have hEven := source_original_actual_P_even_mass_ge_distinct_pair
    P A B hPrime h3 hPn hA hB hAB
  have hOddFinite :
      (∑ p ∈ P, (p:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P p) ≤
      (∑' n : sourceOriginalPOddSupported P,
        shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) := by
    rw [source_group_actual_odd_single_harmonic_mass P hPrime hPn]
    exact hOdd
  have hEvenFinite :
      (∑ n ∈ sourceOriginalGroupCrossEvenImages A B,
        (n:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P n) ≤
      (∑' n : sourceOriginalPEvenSupported P,
        shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) := by
    rw [source_group_actual_even_cross_harmonic_mass
      P A B hPrime hA hB hAB]
    exact hEven
  exact ⟨div_le_div_of_nonneg_right hOddFinite hH.le,
    div_le_div_of_nonneg_right hEvenFinite hH.le⟩

/- Uniform odd and even masses on the TRUE infinite W1 harmonic
integer law for the original inclusive P bands. No finite surrogate
or unproved probability normalization appears. -/



/- Exact source owner: SourcePActualGroupParityFloor.lean; original line 52. -/
theorem source_original_closed_P_actual_tsum_parity_floor :
    ∀ᶠ t : ℝ in atTop,
      let P := sourceOriginalClosedPGroup t
      sourceOriginalPGroupParityDelta ≤
        (∑' n : sourceOriginalPOddSupported P,
          shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) /
          sourceOriginalGroupHarmonicMass P ∧
      sourceOriginalPGroupParityDelta ≤
        (∑' n : sourceOriginalPEvenSupported P,
          shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) /
          sourceOriginalGroupHarmonicMass P := by
  have hLocal := source_original_closed_P_group_uniform_parity_floor
  filter_upwards [hLocal, eventually_ge_atTop (2:ℝ)]
    with t hLocal ht
  let P := sourceOriginalClosedPGroup t
  let A := sourcePrimeLogBand t 1 (11/10)
  let B := sourcePrimeLogBand t (11/10) (6/5)
  have hPrime : ∀ p ∈ P, p.Prime :=
    fun p hp => source_original_P_closed_prime t p hp
  have h3 : ∀ p ∈ P, 3 ≤ p :=
    fun p hp => source_original_P_closed_prime_ge_three t ht p hp
  have hH : 0 < sourceOriginalGroupHarmonicMass P :=
    lt_of_lt_of_le (by norm_num) hLocal.1
  have hPn : P.Nonempty := by
    by_contra hh
    have hE : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    have hE' : sourceOriginalClosedPGroup t = ∅ := hE
    have hMass := hH
    simp [P, sourceOriginalGroupHarmonicMass,hE'] at hMass
  have hA : A ⊆ P :=
    source_original_P_short_band_subset t 1 (11/10)
      (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hB : B ⊆ P :=
    source_original_P_short_band_subset t (11/10) (6/5)
      (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hAB : Disjoint A B :=
    source_original_P_two_halves_disjoint t
  have hAtoms := source_original_actual_P_parity_atoms_le_tsum
    P A B hPrime h3 hPn hA hB hAB hH
  have hMinOdd : sourceOriginalPGroupParityDelta ≤
      1 / ((6/5:ℝ)*Real.exp 4) := by
    unfold sourceOriginalPGroupParityDelta
    exact min_le_left _ _
  have hMinEven : sourceOriginalPGroupParityDelta ≤
      (Real.log (12/11:ℝ)/4)^2 /
        (4*((6/5:ℝ)*Real.exp 4)) := by
    unfold sourceOriginalPGroupParityDelta
    exact min_le_right _ _
  have hOdd := (hMinOdd.trans hLocal.2.2.1).trans hAtoms.1
  have hEven := (hMinEven.trans hLocal.2.2.2).trans hAtoms.2
  exact ⟨hOdd,hEven⟩

/- Algebraic conditioning by arbitrary normalized background parity.
This bound is now from true infinite P-integer W1 harmonic masses;
global W1 disintegration across independent groups is still separate. -/



/- Exact source owner: SourcePGlobalActualOddUniform.lean; original line 14. -/
theorem source_original_P_global_actual_uniform_positive_odd :
    ∀ᶠ t : ℝ in atTop,
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (i : G),
        (∀ g p, p ∈ P g → p.Prime) →
        (∀ g p, p ∈ P g → 3 ≤ p) →
        (∀ g, (P g).Nonempty) →
        (∀ g h p, p ∈ P g → p ∈ P h → g = h) →
        P i = sourceOriginalClosedPGroup t →
        sourceOriginalPGroupParityDelta ≤
          (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
            if Odd (sourceOriginalPParityExponent
              (Finset.univ.biUnion P) n.val)
            then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
            sourceLiteralHP P := by
  filter_upwards [source_original_closed_P_actual_tsum_parity_floor,
    source_original_closed_P_group_uniform_parity_floor]
    with t hParity hBounds G instG decG P i hPrime h3 hPn hDisj hPi
  have hHg : 0 < sourceOriginalGroupHarmonicMass (P i) := by
    rw [hPi]
    exact lt_of_lt_of_le (by norm_num) hBounds.1
  have hOdd : sourceOriginalPGroupParityDelta ≤
      (∑' n : sourceOriginalPOddSupported (P i),
        shiftTwoOriginalGroupFactor (P i) n.val.val /
          (n.val.val:ℝ)) / sourceOriginalGroupHarmonicMass (P i) := by
    rw [hPi]
    exact hParity.1
  have hEven : sourceOriginalPGroupParityDelta ≤
      (∑' n : sourceOriginalPEvenSupported (P i),
        shiftTwoOriginalGroupFactor (P i) n.val.val /
          (n.val.val:ℝ)) / sourceOriginalGroupHarmonicMass (P i) := by
    rw [hPi]
    exact hParity.2
  exact source_original_P_global_actual_odd_harmonic_floor
    P hPrime h3 hPn hDisj i sourceOriginalPGroupParityDelta
    hHg hOdd hEven



/- Exact source owner: SourcePOddSmallMassTransfer.lean; original line 11. -/
theorem source_original_P_odd_small_mass_from_tail
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h3 : ∀ g p, p ∈ P g → 3 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (δ K : ℝ) (hδ : 0 ≤ δ)
    (hOdd : δ ≤
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if Odd (sourceOriginalPParityExponent (Finset.univ.biUnion P) n.val)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
        sourceLiteralHP P)
    (hTail :
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if K < (n.val:ℝ) then sourceOriginalW1 P n.val / (n.val:ℝ)
        else 0) ≤ δ/2) :
    δ/2 ≤
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if Odd (sourceOriginalPParityExponent (Finset.univ.biUnion P) n.val) ∧
             (n.val:ℝ) ≤ K
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
        sourceLiteralHP P := by
  let S := sourceOriginalPSupported (Finset.univ.biUnion P)
  let W : S → ℝ := fun n => sourceOriginalW1 P n.val / (n.val:ℝ)
  have hWnonneg (n : S) : 0 ≤ W n := by
    dsimp [W]
    exact div_nonneg (source_original_W1_nonneg P _)
      (by exact_mod_cast Nat.zero_le n.val)
  have hWsum : Summable W := by
    exact (source_original_global_actual_P_normalized_harmonic_law
      P hPrime h3 hPn hDisj).1
  have hMask (q : S → Prop) :
      Summable (fun n : S => if q n then W n else 0) := by
    classical
    apply hWsum.of_nonneg_of_le
    · intro n
      by_cases hq : q n <;> simp [hq, hWnonneg n]
    · intro n
      by_cases hq : q n <;> simp [hq, hWnonneg n]
  let odd : S → Prop := fun n =>
    Odd (sourceOriginalPParityExponent (Finset.univ.biUnion P) n.val)
  let near : S → Prop := fun n => (n.val:ℝ) ≤ K
  let far : S → Prop := fun n => K < (n.val:ℝ)
  let fOdd : S → ℝ := fun n => if odd n then W n else 0
  let fNear : S → ℝ := fun n => if odd n ∧ near n then W n else 0
  let fFar : S → ℝ := fun n => if far n then W n else 0
  have hsOdd : Summable fOdd := by
    simpa [fOdd, odd, W] using hMask odd
  have hsNear : Summable fNear := by
    simpa [fNear, odd, near, W] using hMask (fun n => odd n ∧ near n)
  have hsFar : Summable fFar := by
    simpa only [fFar] using hMask far
  have hPoint (n : S) : fOdd n ≤ fNear n + fFar n := by
    dsimp [fOdd, fNear, fFar]
    by_cases ho : odd n
    · by_cases hf : far n
      · have hn : ¬near n := not_le.mpr hf
        simp [ho, hf, hn]
      · have hn : near n := le_of_not_gt hf
        simp [ho, hf, hn]
    · by_cases hf : far n
      · simp [ho, hf, hWnonneg n]
      · simp [ho, hf]
  have hPartition : (∑' n : S, fOdd n) ≤
      (∑' n : S, fNear n) + (∑' n : S, fFar n) := by
    calc
      (∑' n : S, fOdd n) ≤ (∑' n : S, (fNear n + fFar n)) :=
        Summable.tsum_le_tsum hPoint hsOdd (hsNear.add hsFar)
      _ = (∑' n : S, fNear n) + (∑' n : S, fFar n) :=
        Summable.tsum_add hsNear hsFar
  have hHP : 0 < sourceLiteralHP P :=
    (source_original_global_actual_P_normalized_harmonic_law
      P hPrime h3 hPn hDisj).2.1
  have hHPone : 1 ≤ sourceLiteralHP P :=
    source_literal_HP_one_le P h3 hPn
  have hOddA : δ * sourceLiteralHP P ≤ (∑' n : S, fOdd n) := by
    have hh := (le_div_iff₀ hHP).mp hOdd
    simpa [S, fOdd, odd, W] using hh
  have hTailA : (∑' n : S, fFar n) ≤ δ/2 := by
    simpa [S, fFar, far, W] using hTail
  have hHalf : δ/2 ≤ (δ/2)*sourceLiteralHP P := by
    have hδhalf : 0 ≤ δ/2 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hHPone) hδhalf]
  have hNear : (δ/2)*sourceLiteralHP P ≤ (∑' n : S, fNear n) := by
    linarith
  apply (le_div_iff₀ hHP).mpr
  simpa [S, fNear, odd, near, W] using hNear



/- Exact source owner: SourcePPolylogTailDecay.lean; original line 10. -/
theorem source_original_P_polylog_tail_tendsto
    (C σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun L : ℝ =>
      L ^ C * Real.exp (-σ * L^(3/5:ℝ))) atTop (𝓝 0) := by
  let a : ℝ := 3/5
  have ha : 0 < a := by dsimp [a]; norm_num
  have ht :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C/a) σ hσ).comp
      (tendsto_rpow_atTop ha)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  change (L^a)^(C/a) * Real.exp (-σ * L^a) =
    L^C * Real.exp (-σ * L^(3/5:ℝ))
  have he : (L^a)^(C/a) = L^C := by
    rw [← Real.rpow_mul hL]
    congr 1
    dsimp [a]
    field_simp
  rw [he]

/- For any fixed sigma and positive epsilon the exact global P-tail
polylog/exponential majorant is eventually below epsilon. -/



/- Exact source owner: SourcePPolylogTailDecay.lean; original line 32. -/
theorem source_original_P_polylog_tail_eventually_small
    (C σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,
      L^C * Real.exp (-σ * L^(3/5:ℝ)) ≤ ε := by
  have hh := source_original_P_polylog_tail_tendsto C σ hσ
  have hopen : Set.Iio ε ∈ 𝓝 (0:ℝ) :=
    IsOpen.mem_nhds isOpen_Iio hε
  filter_upwards [hh.eventually hopen] with L h
  exact le_of_lt h



/- Exact source owner: SourcePOriginalOddSmallEventually.lean; original line 14. -/
theorem source_original_P_odd_small_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (P : sourceOriginalPAllGroupType r₀ L → Finset ℕ)
        (i : sourceOriginalPAllGroupType r₀ L),
        (∀ g p, p ∈ P g → p.Prime) →
        (∀ g p, p ∈ P g → 6 ≤ p) →
        (∀ g, (P g).Nonempty) →
        (∀ g h p, p ∈ P g → p ∈ P h → g = h) →
        (∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4) →
        (∀ g p, p ∈ P g → Real.log (p:ℝ) ≤ L^(2/5:ℝ)) →
        P i = sourceOriginalClosedPGroup
          ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L i.val) →
        sourceOriginalPGroupParityDelta / 2 ≤
          (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
            if Odd (sourceOriginalPParityExponent
                (Finset.univ.biUnion P) n.val) ∧
                (n.val:ℝ) ≤ (Real.exp L)^(1/(132*(r₀:ℝ)))
            then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
          sourceLiteralHP P := by
  let σ : ℝ := 1/(132*(r₀:ℝ))
  let C : ℝ := (3 + (Real.log 2)⁻¹) * Real.log (6 * Real.exp 12)
  have hr : (0:ℝ) < (r₀:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hδ : 0 < sourceOriginalPGroupParityDelta :=
    source_original_P_group_parity_delta_positive
  have hSmall := source_original_P_polylog_tail_eventually_small
    C σ (sourceOriginalPGroupParityDelta/2) hσ (by positivity)
  obtain ⟨T, hOddT⟩ :=
    (Filter.eventually_atTop.1 source_original_P_global_actual_uniform_positive_odd)
  have hPowTop : Tendsto (fun L : ℝ => L^(1/10:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hTbig : ∀ᶠ L : ℝ in atTop, T ≤ L^(1/10:ℝ) :=
    hPowTop.eventually (eventually_ge_atTop T)
  filter_upwards [eventually_ge_atTop (Real.exp (1:ℝ)), hSmall, hTbig]
    with L hL hTailSmall hScaleLarge
  intro P i hPrime h6 hPn hDisj hV4 hLog hPi
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    have hp6 := h6 g p hp
    omega
  have hIdx : sourceOriginalPGroupIndex r₀ L i.val :=
    (Finset.mem_filter.mp i.property).2
  have hscale : L^(1/10:ℝ) ≤
      (3/2:ℝ)*sourceOriginalPGroupScale r₀ L i.val := by
    rcases hIdx with h | h
    · exact h.1
    · have hbase : 1 ≤ L := by
        exact le_trans (by norm_num : (1:ℝ) ≤ Real.exp 1) hL
      exact (Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)).trans h.1
  have hOdd : sourceOriginalPGroupParityDelta ≤
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) n.val)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
        sourceLiteralHP P := by
    exact hOddT _ (hScaleLarge.trans hscale) P i hPrime h3 hPn hDisj hPi
  have hTail :=
    source_original_P_actual_polylog_rankin_tail
      r₀ L σ hr₀ hL hσ P hPrime h6 hPn hDisj hV4 hLog
  have hBound : (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (Real.exp L)^σ < (n.val:ℝ) then
        sourceOriginalW1 P n.val / (n.val:ℝ) else 0) ≤
        sourceOriginalPGroupParityDelta/2 :=
    hTail.trans hTailSmall
  exact source_original_P_odd_small_mass_from_tail
    P hPrime h3 hPn hDisj sourceOriginalPGroupParityDelta
      ((Real.exp L)^σ) hδ.le hOdd hBound



/- Exact source owner: SourcePActualOddSmallEvent.lean; original line 29. -/
theorem source_original_P_actual_odd_small_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ i : sourceOriginalPAllGroupType r₀ L,
        sourceOriginalPGroupParityDelta/2 ≤
          (∑' n : sourceOriginalPSupported
              (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)),
            if Odd (sourceOriginalPParityExponent
                (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) n.val) ∧
                Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
            then sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) n.val /
              (n.val:ℝ) else 0) /
          sourceLiteralHP (sourceOriginalPAllActualBands r₀ L) := by
  have hOddEv := source_original_P_odd_small_eventually r₀ hr₀
  have hLocalEv := source_original_P_all_actual_local_eventually r₀
  filter_upwards [eventually_ge_atTop (1:ℝ), hOddEv, hLocalEv]
    with L hL hOdd hLocal
  intro i
  let P := sourceOriginalPAllActualBands r₀ L
  have hPrime : ∀ g p, p ∈ P g → p.Prime :=
    source_original_P_all_actual_band_prime r₀ L
  have h6 : ∀ g p, p ∈ P g → 6 ≤ p := hLocal.2.1
  have hPn : ∀ g, (P g).Nonempty := hLocal.1
  have hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h :=
    source_original_P_actual_all_disjoint r₀ L hr₀
      (lt_of_lt_of_le (by norm_num) hL)
  have hV4 : ∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4 :=
    hLocal.2.2
  have hLog : ∀ g p, p ∈ P g →
      Real.log (p:ℝ) ≤ L^(2/5:ℝ) :=
    source_original_P_all_actual_band_log r₀ L hL
  have hOddBound := hOdd P i hPrime h6 hPn hDisj hV4 hLog rfl
  have hcut := source_original_P_actual_cutoff_exact r₀ L hr₀
  have hSummands :
      (fun n : sourceOriginalPSupported (Finset.univ.biUnion P) =>
        if Odd (sourceOriginalPParityExponent
            (Finset.univ.biUnion P) n.val) ∧
            (n.val:ℝ) ≤ (Real.exp L)^(1/(132*(r₀:ℝ)))
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) =
      (fun n : sourceOriginalPSupported (Finset.univ.biUnion P) =>
        if Odd (sourceOriginalPParityExponent
            (Finset.univ.biUnion P) n.val) ∧
            Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) := by
    funext n
    have hn : (0:ℝ) < n.val := by
      exact_mod_cast Nat.pos_of_ne_zero n.property.1
    have hlog : ((n.val:ℝ) ≤ (Real.exp L)^(1/(132*(r₀:ℝ)))) ↔
        Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 := by
      rw [hcut]
      exact (Real.log_le_iff_le_exp hn).symm
    simp_rw [hlog]
  dsimp only [P] at hSummands hOddBound
  rw [← hSummands]
  exact hOddBound



/- Exact source owner: SourcePOriginalChosenBand.lean; original line 9. -/
noncomputable def sourceOriginalPChosenIndex (L : ℝ) : ℕ :=
  ⌈((4/5:ℝ)*Real.log L / Real.log 2)⌉₊

/- The dyadic index ceil(4 log L/(5 log 2)) lies inside the ORIGINAL
first P window once L^(1/10) ≥ 44*r₀/15. -/



/- Exact source owner: SourcePOriginalIndexExists.lean; original line 10. -/
theorem source_original_P_dyadic_ceil_bounds
    (L : ℝ) (hL : 1 ≤ L) :
    let j : ℕ := ⌈((4/5:ℝ)*Real.log L / Real.log 2)⌉₊
    L^(4/5:ℝ) ≤ (2:ℝ)^j ∧
    (2:ℝ)^j ≤ 2*L^(4/5:ℝ) := by
  let z : ℝ := (4/5:ℝ)*Real.log L / Real.log 2
  let j : ℕ := ⌈z⌉₊
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hlow : z ≤ (j:ℝ) := Nat.le_ceil z
  have hupp : (j:ℝ) < z+1 := Nat.ceil_lt_add_one hz
  have hfirst : (4/5:ℝ)*Real.log L ≤ Real.log 2*(j:ℝ) := by
    calc
      (4/5:ℝ)*Real.log L =
          Real.log 2 * z := by
            dsimp [z]
            field_simp
      _ ≤ Real.log 2*(j:ℝ) :=
          mul_le_mul_of_nonneg_left hlow h2.le
  have hsecond : Real.log 2*(j:ℝ) ≤
      (4/5:ℝ)*Real.log L + Real.log 2 := by
    calc
      Real.log 2*(j:ℝ) ≤ Real.log 2*(z+1) :=
        mul_le_mul_of_nonneg_left hupp.le h2.le
      _ = (4/5:ℝ)*Real.log L + Real.log 2 := by
        dsimp [z]
        field_simp
  have hj : (2:ℝ)^j =
      Real.exp (Real.log 2*(j:ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  have hLpow : L^(4/5:ℝ) =
      Real.exp (Real.log L*(4/5:ℝ)) :=
    Real.rpow_def_of_pos hLp _
  change L^(4/5:ℝ) ≤ (2:ℝ)^j ∧
     (2:ℝ)^j ≤ 2*L^(4/5:ℝ)
  constructor
  · calc
      L^(4/5:ℝ) = Real.exp ((4/5:ℝ)*Real.log L) := by
        rw [hLpow]; ring
      _ ≤ Real.exp (Real.log 2*(j:ℝ)) :=
        Real.exp_le_exp.mpr hfirst
      _ = (2:ℝ)^j := hj.symm
  · calc
      (2:ℝ)^j = Real.exp (Real.log 2*(j:ℝ)) := hj
      _ ≤ Real.exp ((4/5:ℝ)*Real.log L + Real.log 2) :=
        Real.exp_le_exp.mpr hsecond
      _ = 2*L^(4/5:ℝ) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2), hLpow]
        ring



/- Exact source owner: SourcePOriginalChosenBand.lean; original line 14. -/
theorem source_original_P_chosen_index_valid
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (hL : 1 ≤ L) (hLarge : (44/15:ℝ)*(r₀:ℝ) ≤ L^(1/10:ℝ)) :
    sourceOriginalPGroupIndex r₀ L (sourceOriginalPChosenIndex L) := by
  let j := sourceOriginalPChosenIndex L
  let q : ℝ := (2:ℝ)^j
  let a : ℝ := L^(1/10:ℝ)
  let b : ℝ := L^(4/5:ℝ)
  let c : ℝ := L^(1/5:ℝ)
  let d : ℝ := (r₀:ℝ)*(11/5:ℝ)
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow := source_original_P_dyadic_ceil_bounds L hL
  have hqb : b ≤ q := by simpa only [sourceOriginalPChosenIndex, j, q, b] using hpow.1
  have hq2b : q ≤ 2*b := by simpa only [sourceOriginalPChosenIndex, j, q, b] using hpow.2
  have hden : 0 < d*q := mul_pos hd hq
  have hacb : a*a*b = L := by
    dsimp [a,b]
    calc
      L^(1/10:ℝ)*L^(1/10:ℝ)*L^(4/5:ℝ) =
        L^((1/10:ℝ)+(1/10:ℝ))*L^(4/5:ℝ) := by
          rw [Real.rpow_add hLp]
      _ = L^(((1/10:ℝ)+(1/10:ℝ))+(4/5:ℝ)) :=
        (Real.rpow_add hLp _ _).symm
      _ = L := by norm_num
  have hcb : c*b = L := by
    dsimp [c,b]
    rw [← Real.rpow_add hLp]
    norm_num
  have hTwoD : 2*d ≤ (3/2:ℝ)*a := by
    dsimp [d,a] at *
    nlinarith [hLarge]
  have hAdq : a*(d*q) ≤ (3/2:ℝ)*L := by
    have hDq := mul_le_mul_of_nonneg_left hq2b hd.le
    have hDqA := mul_le_mul_of_nonneg_left hDq ha.le
    have hMul := mul_le_mul_of_nonneg_right hTwoD
      (mul_nonneg ha.le hb.le)
    calc
      a*(d*q) ≤ a*(d*(2*b)) := by nlinarith [hDqA]
      _ ≤ (3/2:ℝ)*(a*a*b) := by nlinarith [hMul]
      _ = (3/2:ℝ)*L := by rw [hacb]
  have hlow : a ≤ (3/2:ℝ)*(L/(d*q)) := by
    calc
      a ≤ ((3/2:ℝ)*L)/(d*q) := (le_div_iff₀ hden).2 hAdq
      _ = (3/2:ℝ)*(L/(d*q)) := by ring
  have hdLower : (9/5:ℝ) ≤ d := by
    dsimp [d]
    have hrCast : (1:ℝ) ≤ r₀ := by exact_mod_cast hr₀
    nlinarith
  have hUpperDen : (9/5:ℝ)*L ≤ c*(d*q) := by
    have hMul1 := mul_le_mul_of_nonneg_right hdLower hLp.le
    have hMul2 := mul_le_mul_of_nonneg_left hqb hc.le
    have hMul3 := mul_le_mul_of_nonneg_left hMul2 hd.le
    calc
      (9/5:ℝ)*L ≤ d*L := hMul1
      _ = d*(c*b) := by rw [hcb]
      _ ≤ d*(c*q) := by nlinarith [hMul3]
      _ = c*(d*q) := by ring
  have hupp : (9/5:ℝ)*(L/(d*q)) ≤ c := by
    calc
      (9/5:ℝ)*(L/(d*q)) = ((9/5:ℝ)*L)/(d*q) := by ring
      _ ≤ c := (div_le_iff₀ hden).2 hUpperDen
  left
  constructor
  · change L^(1/10:ℝ) ≤
      (3/2:ℝ)*sourceOriginalPGroupScale r₀ L j
    simpa only [sourceOriginalPGroupScale, j, a, d, q, mul_assoc] using hlow
  · change (9/5:ℝ)*sourceOriginalPGroupScale r₀ L j ≤ L^(1/5:ℝ)
    simpa only [sourceOriginalPGroupScale, j, c, d, q, mul_assoc] using hupp



/- Exact source owner: SourcePOriginalOddSmallComplete.lean; original line 12. -/
theorem source_original_P_all_actual_groups_nonempty_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      Nonempty (sourceOriginalPAllGroupType r₀ L) := by
  have htend : Tendsto (fun L : ℝ => L^(1/10:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hLarge : ∀ᶠ L : ℝ in atTop,
      (44/15:ℝ)*(r₀:ℝ) ≤ L^(1/10:ℝ) :=
    htend.eventually (eventually_ge_atTop ((44/15:ℝ)*(r₀:ℝ)))
  filter_upwards [eventually_ge_atTop (Real.exp (1:ℝ)), hLarge]
    with L hL hLargeL
  have hOne : 1 ≤ L := by
    have hExp : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
    exact hExp.trans hL
  have hOneStrict : 1 < L := by
    have hExp : 1 < Real.exp (1:ℝ) := by
      have he := Real.exp_strictMono (by norm_num : (0:ℝ) < 1)
      simpa using he
    exact hExp.trans_le hL
  have hIdx := source_original_P_chosen_index_valid
    r₀ L hr₀ hOne hLargeL
  have hMem : sourceOriginalPChosenIndex L ∈
      sourceOriginalPAllGroupIndices r₀ L :=
    (source_original_P_all_groups_mem_iff
      r₀ L hr₀ hOneStrict (sourceOriginalPChosenIndex L)).2 hIdx
  exact ⟨⟨sourceOriginalPChosenIndex L, hMem⟩⟩

/- Full original P harmonic odd-and-small mass for the concrete
source dyadic bands, without any unproved P-group assumptions. -/



/- Exact source owner: SourcePOriginalOddSmallComplete.lean; original line 41. -/
theorem source_original_P_actual_odd_small_full_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalPGroupParityDelta/2 ≤
        (∑' n : sourceOriginalPSupported
            (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)),
          if Odd (sourceOriginalPParityExponent
              (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) n.val) ∧
              Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
          then sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) n.val /
            (n.val:ℝ) else 0) /
        sourceLiteralHP (sourceOriginalPAllActualBands r₀ L) := by
  filter_upwards [
    source_original_P_actual_odd_small_eventually r₀ hr₀,
    source_original_P_all_actual_groups_nonempty_eventually r₀ hr₀]
    with L hEvent hNonempty
  exact hEvent (Classical.choice hNonempty)



/- Exact source owner: SourcePOriginalParityProjection.lean; original line 9. -/
theorem source_original_P_projection_eq_odd_indicator
    (n : ℕ) :
    ((1 - (-1:ℝ)^n)/2) = if Odd n then (1:ℝ) else 0 := by
  rcases Nat.even_or_odd n with he | ho
  · have hn : ¬Odd n := Nat.not_odd_iff_even.mpr he
    simp [hn, Even.neg_one_pow he]
  · simp [ho, Odd.neg_one_pow ho]



/- Exact source owner: SourcePOriginalGoodParityFactor.lean; original line 12. -/
theorem source_original_P_actual_good_parity_factor_full_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      (sourceOriginalPGroupParityDelta/2) *
        sourceLiteralHP (sourceOriginalPAllActualBands r₀ L) ≤
        ∑' n : sourceOriginalPSupported
            (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)),
          if Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 then
            (sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) n.val /
              (n.val:ℝ)) *
            ((1 - (-1:ℝ)^sourceOriginalPParityExponent
              (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) n.val)/2)
          else 0 := by
  filter_upwards [
    source_original_P_actual_odd_small_full_eventually r₀ hr₀,
    source_original_P_all_actual_local_eventually r₀] with L hOdd hLocal
  let P := sourceOriginalPAllActualBands r₀ L
  let Pall : Finset ℕ := Finset.univ.biUnion P
  let S := sourceOriginalPSupported Pall
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    have h6 := hLocal.2.1 g p hp
    omega
  have hHPone : 1 ≤ sourceLiteralHP P :=
    source_literal_HP_one_le P h3 hLocal.1
  have hHPpos : 0 < sourceLiteralHP P := by linarith
  have hBound :
      (sourceOriginalPGroupParityDelta/2)*sourceLiteralHP P ≤
        (∑' n : S,
          if Odd (sourceOriginalPParityExponent Pall n.val) ∧
              Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
          then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) := by
    exact (le_div_iff₀ hHPpos).mp hOdd
  have hPoint :
      (fun n : S =>
        if Odd (sourceOriginalPParityExponent Pall n.val) ∧
            Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) =
      (fun n : S =>
        if Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
        then (sourceOriginalW1 P n.val / (n.val:ℝ)) *
          ((1 - (-1:ℝ)^sourceOriginalPParityExponent Pall n.val)/2)
        else 0) := by
    funext n
    have hi := source_original_P_projection_eq_odd_indicator
      (sourceOriginalPParityExponent Pall n.val)
    by_cases ho : Odd (sourceOriginalPParityExponent Pall n.val)
    · by_cases hs : Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
      · simp [ho, hs, hi]
      · simp [ho, hs]
    · by_cases hs : Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
      · simp [ho, hs, hi]
      · simp [ho, hs]
  change (sourceOriginalPGroupParityDelta/2)*sourceLiteralHP P ≤ _
  rw [← hPoint]
  exact hBound



/- Exact source owner: SourceOriginalQPGoodMassBound.lean; original line 25. -/
theorem source_original_P_good_harmonic_mass_floor_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      (sourceOriginalPGroupParityDelta/2)*
        sourceLiteralHP (sourceOriginalPAllActualBands r₀ L) ≤
      sourceOriginalPActualGoodHarmonicMass r₀ L := by
  filter_upwards [source_original_P_actual_good_parity_factor_full_eventually
    r₀ hr₀] with L hh
  exact hh

/- Combined original Q midpoint and P odd/small harmonic factor.
All objects below are the literal source prime-band/factorial sums.
The remaining bridge to X_A is the already checked free-Q0 prime count. -/



/- Exact source owner: SourceOriginalQJointPositiveRest.lean; original line 10. -/
noncomputable def sourceOriginalQActualRestHarmonicMass
    (r₀ jₓ : ℕ) (L : ℝ)
    (b : Fin (jₓ+1)) (i : Fin r₀) : ℝ :=
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  ∑ rest : (z : I) → {p // p ∈ Q z.val.1},
    (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
      (((∏ z : I, (rest z).val):ℕ):ℝ)

/- Source Q-rest mass restricted only on genuine fixed-index
midpoint prime subwindows; all other slots remain unrestricted. -/



/- Exact source owner: SourceOriginalQActualGeometry.lean; original line 33. -/
theorem source_original_Q_actual_prime
    (r₀ jₓ : ℕ) (L : ℝ)
    (j : Fin (jₓ+1)) (p : ℕ)
    (hp : p ∈ sourceOriginalQActualBands r₀ jₓ L j) :
    p.Prime := (Finset.mem_filter.mp hp).2

/- Inclusive source Q_j endpoints in the original s_j coordinates. -/



/- Exact source owner: SourceOriginalQActualGeometry.lean; original line 20. -/
theorem source_original_Q_actual_scale_eq_P_scale
    (r₀ j : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) :
    sourceOriginalQActualExponent r₀ j * L =
      sourceOriginalPGroupScale r₀ L j := by
  have hr : (r₀:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  unfold sourceOriginalQActualExponent sourceOriginalQ0Scale
    sourceOriginalPGroupScale
  have hp : (2:ℝ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/- Exact prime property for every source Q_j. -/



/- Exact source owner: SourceOriginalQActualGeometry.lean; original line 40. -/
theorem source_original_Q_actual_prime_range
    (r₀ jₓ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (j : Fin (jₓ+1)) (p : ℕ)
    (hp : p ∈ sourceOriginalQActualBands r₀ jₓ L j) :
    Real.exp (sourceOriginalPGroupScale r₀ L j.val) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp ((6/5:ℝ)*sourceOriginalPGroupScale r₀ L j.val) := by
  have hRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
  have hs := source_original_Q_actual_scale_eq_P_scale r₀ j.val L hr₀
  constructor
  · have h := (Nat.ceil_le).1 hRange.1
    rw [← hs]
    exact h
  · have hFloor := (Nat.floor_le (Real.exp_nonneg
        (((6/5:ℝ)*sourceOriginalQActualExponent r₀ j.val)*L)))
    have hCast : (p:ℝ) ≤
      (⌊Real.exp (((6/5:ℝ)*sourceOriginalQActualExponent r₀ j.val)*L)⌋₊:ℝ) := by
        exact_mod_cast hRange.2
    have hComp := hCast.trans hFloor
    have hEq : ((6/5:ℝ)*sourceOriginalQActualExponent r₀ j.val)*L =
        (6/5:ℝ)*sourceOriginalPGroupScale r₀ L j.val := by
      rw [← hs]
      ring
    rw [hEq] at hComp
    exact hComp


end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualPBothParity -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

/-- Boolean form of conditioning on the remaining groups. The flag false
selects odd multiplicity; true selects even multiplicity. -/
theorem parity_bool_parity_split434 (P : Prop) [Decidable P]
    (a c b : Bool) (h : P ↔ a ≠ c) :
    (decide P ≠ b) ↔ a ≠ (if b then !c else c) := by
  cases a <;> cases c <;> cases b <;> simp_all

/-- Both parity events in the genuine finite family of harmonic factors,
with a common conditional lower bound independent of the number of groups. -/
theorem parity_conditional_finite_pi_parity_tsum_floor434
    {G : Type} [Fintype G] [DecidableEq G]
    (A : G → Type) (f : (g : G) → A g → ℝ)
    (k : (g : G) → A g → ℕ)
    (i : G) (δ : ℝ)
    (hf : ∀ g, Summable (f g))
    (hn : ∀ g a, 0 ≤ f g a)
    (hLocal : ∀ b : Bool,
      δ * (∑' a : A i, f i a) ≤
        ∑' a : A i,
          if decide (Odd (k i a)) ≠ b then f i a else 0) (parityFlag : Bool) :
    δ * (∑' x : (g : G) → A g,
      ∏ g : G, f g (x g)) ≤
      ∑' x : (g : G) → A g,
        if (decide (Odd (∑ g : G, k g (x g))) ≠ parityFlag)
        then ∏ g : G, f g (x g) else 0 := by
  classical
  let J := {g : G // g ≠ i}
  let B := (j : J) → A j.val
  let E : ((g : G) → A g) ≃ A i × B :=
    Equiv.piSplitAt i A
  let w : B → ℝ := fun r =>
    ∏ j : J, f j.val (r j)
  let kp : A i → Bool := fun a => decide (Odd (k i a))
  let kq : B → Bool :=
    fun r => if parityFlag then !(decide (Odd (∑ j : J, k j.val (r j))))
      else decide (Odd (∑ j : J, k j.val (r j)))
  let F : ((g : G) → A g) → ℝ :=
    fun x => ∏ g : G, f g (x g)
  have hRest := source_tsum_pi_finite_product
    (fun j : J => A j.val)
    (fun j a => f j.val a)
    (fun j => hf j.val)
    (fun j a => hn j.val a)
  have hW : Summable w := hRest.1
  have hWN : ∀ r : B, 0 ≤ w r := by
    intro r
    dsimp [w]
    apply Finset.prod_nonneg
    intro j hj
    exact hn j.val (r j)
  have hPair : Summable (fun z : A i × B => f i z.1 * w z.2) :=
    Summable.mul_of_nonneg (hf i) hW (hn i) hWN
  have hSplitWeight (z : A i × B) :
      F (E.symm z) = f i z.1 * w z.2 := by
    rcases z with ⟨a,r⟩
    exact source_pi_split_weight A f i a r
  have hSplitOdd (z : A i × B) :
      (decide (Odd (∑ g : G, k g (E.symm z g))) ≠ parityFlag) ↔
        kp z.1 ≠ kq z.2 := by
    rcases z with ⟨a,r⟩
    exact parity_bool_parity_split434 _ _ _ parityFlag
      (source_pi_split_odd_iff A k i a r)
  have hFull :
      (∑' x : (g : G) → A g, F x) =
        (∑' a : A i, f i a) * (∑' r : B, w r) := by
    calc
      _ = ∑' z : A i × B, F (E.symm z) :=
        (E.symm.tsum_eq F).symm
      _ = ∑' z : A i × B, f i z.1 * w z.2 := by
        apply tsum_congr
        intro z
        exact hSplitWeight z
      _ = (∑' a : A i, f i a) * (∑' r : B, w r) :=
        ((hf i).tsum_mul_tsum hW hPair).symm
  have hFlagMass :
      (∑' x : (g : G) → A g,
        if (decide (Odd (∑ g : G, k g (x g))) ≠ parityFlag) then F x else 0) =
      ∑' z : A i × B,
        if kp z.1 ≠ kq z.2 then f i z.1 * w z.2 else 0 := by
    calc
      _ = ∑' z : A i × B,
          if (decide (Odd (∑ g : G, k g (E.symm z g))) ≠ parityFlag)
          then F (E.symm z) else 0 :=
        (E.symm.tsum_eq
          (fun x : (g : G) → A g =>
            if (decide (Odd (∑ g : G, k g (x g))) ≠ parityFlag) then F x else 0)).symm
      _ = ∑' z : A i × B,
          if kp z.1 ≠ kq z.2 then f i z.1 * w z.2 else 0 := by
        apply tsum_congr
        intro z
        rw [hSplitWeight]
        by_cases hh : (decide (Odd (∑ g : G, k g (E.symm z g))) ≠ parityFlag)
        · simp [hh, (hSplitOdd z).mp hh]
        · simp [hh, (hSplitOdd z).not.mp hh]
  have hCond := source_conditional_two_factor_parity_tsum_floor
    (f i) w kp kq δ (hf i) hW (hn i) hWN
    (by
      intro b
      exact hLocal b)
  change δ * (∑' x : (g : G) → A g, F x) ≤
    (∑' x : (g : G) → A g,
      if (decide (Odd (∑ g : G, k g (x g))) ≠ parityFlag) then F x else 0)
  calc
    δ * (∑' x : (g : G) → A g, F x) =
      δ * ((∑' a : A i, f i a) * (∑' r : B, w r)) := by
        rw [hFull]
    _ ≤ ∑' z : A i × B,
        if kp z.1 ≠ kq z.2 then f i z.1 * w z.2 else 0 := by
          convert hCond using 1 <;> ring
    _ = _ := hFlagMass.symm

theorem parity_original_P_global_actual_parity_tsum_reindex434
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h) (parityFlag : Bool) :
    (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (decide (Odd (sourceOriginalPParityExponent
        (Finset.univ.biUnion P) n.val)) ≠ parityFlag)
      then sourceOriginalW1 P n.val / (n.val:ℝ)
      else 0) =
    ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
      if (decide (Odd (∑ g : G, sourceOriginalPParityExponent (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g)))) ≠ parityFlag)
      then ∏ g : G,
        shiftTwoOriginalGroupFactor (P g)
          (sourceOriginalPPrimePowerProduct (P g) (e g)) /
        ((sourceOriginalPPrimePowerProduct (P g) (e g)):ℝ)
      else 0 := by
  classical
  let Pall : Finset ℕ := Finset.univ.biUnion P
  have hAll : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPrime g p hpg
  let E : ((g : G) → {p // p ∈ P g} → ℕ) ≃
    sourceOriginalPSupported Pall :=
    (sourceOriginalPDisjointExponentEquiv P hDisj).trans
      (source_original_P_power_equiv Pall hAll)
  let F : sourceOriginalPSupported Pall → ℝ :=
    fun n => if (decide (Odd (sourceOriginalPParityExponent Pall n.val)) ≠ parityFlag)
      then sourceOriginalW1 P n.val / (n.val:ℝ)
      else 0
  have hPoint (e : (g : G) → {p // p ∈ P g} → ℕ) :
      F (E e) =
      (if (decide (Odd (∑ g : G, sourceOriginalPParityExponent (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g)))) ≠ parityFlag)
      then ∏ g : G,
        shiftTwoOriginalGroupFactor (P g)
          (sourceOriginalPPrimePowerProduct (P g) (e g)) /
        ((sourceOriginalPPrimePowerProduct (P g) (e g)):ℝ)
      else 0) := by
    have hVal : (E e).val =
        sourceOriginalPGlobalVectorProduct P e := by
      change sourceOriginalPPrimePowerProduct Pall
        (sourceOriginalPDisjointExponentEquiv P hDisj e) =
          sourceOriginalPGlobalVectorProduct P e
      exact (source_original_P_global_vector_product_eq
        P hPrime hDisj e).symm
    have hParity : (decide (Odd (sourceOriginalPParityExponent Pall
        (E e).val)) ≠ parityFlag) ↔
      (decide (Odd (∑ g : G, sourceOriginalPParityExponent (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g)))) ≠ parityFlag) := by
      rw [hVal, source_original_P_global_parity_exponent_sum
        P hPrime hDisj e]
    have hWeight :
        sourceOriginalW1 P (E e).val / ((E e).val:ℝ) =
          ∏ g : G,
            shiftTwoOriginalGroupFactor (P g)
              (sourceOriginalPPrimePowerProduct (P g) (e g)) /
              ((sourceOriginalPPrimePowerProduct (P g) (e g)):ℝ) := by
      rw [hVal]
      exact source_original_P_global_integer_harmonic_factorization
        P hPrime hDisj e
    by_cases hh : (decide (Odd (sourceOriginalPParityExponent Pall (E e).val)) ≠ parityFlag)
    · have hSum := hParity.mp hh
      dsimp [F]
      simp only [if_pos hh, if_pos hSum]
      exact hWeight
    · have hSum := hParity.not.mp hh
      dsimp [F]
      simp only [if_neg hh, if_neg hSum]
  calc
    (∑' n : sourceOriginalPSupported Pall, F n) =
      ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
        F (E e) := (E.tsum_eq F).symm
    _ = ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
        if (decide (Odd (∑ g : G, sourceOriginalPParityExponent (P g)
          (sourceOriginalPPrimePowerProduct (P g) (e g)))) ≠ parityFlag)
        then ∏ g : G,
          shiftTwoOriginalGroupFactor (P g)
            (sourceOriginalPPrimePowerProduct (P g) (e g)) /
          ((sourceOriginalPPrimePowerProduct (P g) (e g)):ℝ)
        else 0 := by
          apply tsum_congr
          intro e
          exact hPoint e

theorem parity_original_P_global_actual_parity_harmonic_floor434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h3 : ∀ g p, p ∈ P g → 3 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (i : G) (δ : ℝ)
    (hHg : 0 < sourceOriginalGroupHarmonicMass (P i))
    (hOdd : δ ≤
      (∑' n : sourceOriginalPOddSupported (P i),
        shiftTwoOriginalGroupFactor (P i) n.val.val /
          (n.val.val:ℝ)) / sourceOriginalGroupHarmonicMass (P i))
    (hEven : δ ≤
      (∑' n : sourceOriginalPEvenSupported (P i),
        shiftTwoOriginalGroupFactor (P i) n.val.val /
          (n.val.val:ℝ)) / sourceOriginalGroupHarmonicMass (P i)) (parityFlag : Bool) :
    δ ≤
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if (decide (Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) n.val)) ≠ parityFlag)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
        sourceLiteralHP P := by
  classical
  let A (g : G) := {p // p ∈ P g} → ℕ
  let f (g : G) (e : A g) : ℝ :=
    shiftTwoOriginalGroupFactor (P g)
      (sourceOriginalPPrimePowerProduct (P g) e) /
      ((sourceOriginalPPrimePowerProduct (P g) e):ℝ)
  let k (g : G) (e : A g) : ℕ :=
    sourceOriginalPParityExponent (P g)
      (sourceOriginalPPrimePowerProduct (P g) e)
  have hf (g : G) : Summable (f g) :=
    (source_original_P_group_harmonic_tsum_le_Hg
      (P g) (hPrime g) (h3 g) (hPn g)).1
  have hn (g : G) (e : A g) : 0 ≤ f g e := by
    dsimp [f]
    simpa only [div_eq_mul_inv] using
      source_original_P_harmonic_term_nonneg
        (P g) (hPrime g) (hPn g) e
  have hLocal := source_original_P_group_true_vector_flag_floor
    (P i) δ (hPrime i) (h3 i) (hPn i) hHg hOdd hEven
  have hProdOdd := parity_conditional_finite_pi_parity_tsum_floor434
    A f k i δ hf hn (by
      intro b
      exact hLocal b) parityFlag
  have hTotal :
      (∑' e : (g : G) → A g, ∏ g : G, f g (e g)) =
        sourceLiteralHP P := by
    calc
      _ = sourceOriginalPHarmonicTsum P :=
        (source_original_P_global_weighted_tsum_group_reindex
          P hPrime hDisj).symm
      _ = sourceLiteralHP P :=
        source_original_global_actual_P_harmonic_tsum_eq_HP
          P hPrime h3 hPn hDisj
  have hOddReindex :
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if (decide (Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) n.val)) ≠ parityFlag)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) =
      (∑' e : (g : G) → A g,
        if (decide (Odd (∑ g : G, k g (e g))) ≠ parityFlag)
        then ∏ g : G, f g (e g) else 0) := by
    exact parity_original_P_global_actual_parity_tsum_reindex434
      P hPrime hDisj parityFlag
  have hHP : 0 < sourceLiteralHP P :=
    (source_original_global_actual_P_normalized_harmonic_law
      P hPrime h3 hPn hDisj).2.1
  apply (le_div_iff₀ hHP).2
  calc
    δ * sourceLiteralHP P =
      δ * (∑' e : (g : G) → A g,
        ∏ g : G, f g (e g)) := by rw [hTotal]
    _ ≤ ∑' e : (g : G) → A g,
        if (decide (Odd (∑ g : G, k g (e g))) ≠ parityFlag)
        then ∏ g : G, f g (e g) else 0 := hProdOdd
    _ = ∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if (decide (Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) n.val)) ≠ parityFlag)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0 :=
      hOddReindex.symm

theorem parity_original_P_global_actual_uniform_positive_parity434 :
    ∀ᶠ t : ℝ in atTop,
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (i : G),
        (∀ g p, p ∈ P g → p.Prime) →
        (∀ g p, p ∈ P g → 3 ≤ p) →
        (∀ g, (P g).Nonempty) →
        (∀ g h p, p ∈ P g → p ∈ P h → g = h) →
        P i = sourceOriginalClosedPGroup t → ∀ parityFlag : Bool,
        sourceOriginalPGroupParityDelta ≤
          (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
            if (decide (Odd (sourceOriginalPParityExponent
              (Finset.univ.biUnion P) n.val)) ≠ parityFlag)
            then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
            sourceLiteralHP P := by
  filter_upwards [source_original_closed_P_actual_tsum_parity_floor,
    source_original_closed_P_group_uniform_parity_floor]
    with t hParity hBounds G instG decG P i hPrime h3 hPn hDisj hPi parityFlag
  have hHg : 0 < sourceOriginalGroupHarmonicMass (P i) := by
    rw [hPi]
    exact lt_of_lt_of_le (by norm_num) hBounds.1
  have hOdd : sourceOriginalPGroupParityDelta ≤
      (∑' n : sourceOriginalPOddSupported (P i),
        shiftTwoOriginalGroupFactor (P i) n.val.val /
          (n.val.val:ℝ)) / sourceOriginalGroupHarmonicMass (P i) := by
    rw [hPi]
    exact hParity.1
  have hEven : sourceOriginalPGroupParityDelta ≤
      (∑' n : sourceOriginalPEvenSupported (P i),
        shiftTwoOriginalGroupFactor (P i) n.val.val /
          (n.val.val:ℝ)) / sourceOriginalGroupHarmonicMass (P i) := by
    rw [hPi]
    exact hParity.2
  exact parity_original_P_global_actual_parity_harmonic_floor434
    P hPrime h3 hPn hDisj i sourceOriginalPGroupParityDelta
    hHg hOdd hEven parityFlag
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualPBothParitySmall -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

/-- The same literal Rankin tail leaves a fixed positive proportion of
BOTH multiplicity-parity events. The full P-supported W1/R law, original
moving group family, and exact Delta/12 cutoff are unchanged. -/
theorem parity_original_P_parity_small_mass_from_tail434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h3 : ∀ g p, p ∈ P g → 3 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (δ K : ℝ) (parityFlag : Bool) (hδ : 0 ≤ δ)
    (hOdd : δ ≤
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if (decide (Odd (sourceOriginalPParityExponent (Finset.univ.biUnion P) n.val)) ≠ parityFlag)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
        sourceLiteralHP P)
    (hTail :
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if K < (n.val:ℝ) then sourceOriginalW1 P n.val / (n.val:ℝ)
        else 0) ≤ δ/2) :
    δ/2 ≤
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if (decide (Odd (sourceOriginalPParityExponent (Finset.univ.biUnion P) n.val)) ≠ parityFlag) ∧
             (n.val:ℝ) ≤ K
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
        sourceLiteralHP P := by
  let S := sourceOriginalPSupported (Finset.univ.biUnion P)
  let W : S → ℝ := fun n => sourceOriginalW1 P n.val / (n.val:ℝ)
  have hWnonneg (n : S) : 0 ≤ W n := by
    dsimp [W]
    exact div_nonneg (source_original_W1_nonneg P _)
      (by exact_mod_cast Nat.zero_le n.val)
  have hWsum : Summable W := by
    exact (source_original_global_actual_P_normalized_harmonic_law
      P hPrime h3 hPn hDisj).1
  have hMask (q : S → Prop) :
      Summable (fun n : S => if q n then W n else 0) := by
    classical
    apply hWsum.of_nonneg_of_le
    · intro n
      by_cases hq : q n <;> simp [hq, hWnonneg n]
    · intro n
      by_cases hq : q n <;> simp [hq, hWnonneg n]
  let odd : S → Prop := fun n =>
    (decide (Odd (sourceOriginalPParityExponent (Finset.univ.biUnion P) n.val)) ≠ parityFlag)
  let near : S → Prop := fun n => (n.val:ℝ) ≤ K
  let far : S → Prop := fun n => K < (n.val:ℝ)
  let fOdd : S → ℝ := fun n => if odd n then W n else 0
  let fNear : S → ℝ := fun n => if odd n ∧ near n then W n else 0
  let fFar : S → ℝ := fun n => if far n then W n else 0
  have hsOdd : Summable fOdd := by
    simpa [fOdd, odd, W] using hMask odd
  have hsNear : Summable fNear := by
    simpa [fNear, odd, near, W] using hMask (fun n => odd n ∧ near n)
  have hsFar : Summable fFar := by
    simpa only [fFar] using hMask far
  have hPoint (n : S) : fOdd n ≤ fNear n + fFar n := by
    dsimp [fOdd, fNear, fFar]
    by_cases ho : odd n
    · by_cases hf : far n
      · have hn : ¬near n := not_le.mpr hf
        simp [ho, hf, hn]
      · have hn : near n := le_of_not_gt hf
        simp [ho, hf, hn]
    · by_cases hf : far n
      · simp [ho, hf, hWnonneg n]
      · simp [ho, hf]
  have hPartition : (∑' n : S, fOdd n) ≤
      (∑' n : S, fNear n) + (∑' n : S, fFar n) := by
    calc
      (∑' n : S, fOdd n) ≤ (∑' n : S, (fNear n + fFar n)) :=
        Summable.tsum_le_tsum hPoint hsOdd (hsNear.add hsFar)
      _ = (∑' n : S, fNear n) + (∑' n : S, fFar n) :=
        Summable.tsum_add hsNear hsFar
  have hHP : 0 < sourceLiteralHP P :=
    (source_original_global_actual_P_normalized_harmonic_law
      P hPrime h3 hPn hDisj).2.1
  have hHPone : 1 ≤ sourceLiteralHP P :=
    source_literal_HP_one_le P h3 hPn
  have hOddA : δ * sourceLiteralHP P ≤ (∑' n : S, fOdd n) := by
    have hh := (le_div_iff₀ hHP).mp hOdd
    simpa [S, fOdd, odd, W] using hh
  have hTailA : (∑' n : S, fFar n) ≤ δ/2 := by
    simpa [S, fFar, far, W] using hTail
  have hHalf : δ/2 ≤ (δ/2)*sourceLiteralHP P := by
    have hδhalf : 0 ≤ δ/2 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hHPone) hδhalf]
  have hNear : (δ/2)*sourceLiteralHP P ≤ (∑' n : S, fNear n) := by
    linarith
  apply (le_div_iff₀ hHP).mpr
  simpa [S, fNear, odd, near, W] using hNear

theorem parity_original_P_parity_small_eventually434
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (P : sourceOriginalPAllGroupType r₀ L → Finset ℕ)
        (i : sourceOriginalPAllGroupType r₀ L),
        (∀ g p, p ∈ P g → p.Prime) →
        (∀ g p, p ∈ P g → 6 ≤ p) →
        (∀ g, (P g).Nonempty) →
        (∀ g h p, p ∈ P g → p ∈ P h → g = h) →
        (∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4) →
        (∀ g p, p ∈ P g → Real.log (p:ℝ) ≤ L^(2/5:ℝ)) →
        P i = sourceOriginalClosedPGroup
          ((3/2:ℝ)*sourceOriginalPGroupScale r₀ L i.val) → ∀ parityFlag : Bool,
        sourceOriginalPGroupParityDelta / 2 ≤
          (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
            if (decide (Odd (sourceOriginalPParityExponent
                (Finset.univ.biUnion P) n.val)) ≠ parityFlag) ∧
                (n.val:ℝ) ≤ (Real.exp L)^(1/(132*(r₀:ℝ)))
            then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
          sourceLiteralHP P := by
  let σ : ℝ := 1/(132*(r₀:ℝ))
  let C : ℝ := (3 + (Real.log 2)⁻¹) * Real.log (6 * Real.exp 12)
  have hr : (0:ℝ) < (r₀:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hδ : 0 < sourceOriginalPGroupParityDelta :=
    source_original_P_group_parity_delta_positive
  have hSmall := source_original_P_polylog_tail_eventually_small
    C σ (sourceOriginalPGroupParityDelta/2) hσ (by positivity)
  obtain ⟨T, hOddT⟩ :=
    (Filter.eventually_atTop.1 parity_original_P_global_actual_uniform_positive_parity434)
  have hPowTop : Tendsto (fun L : ℝ => L^(1/10:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hTbig : ∀ᶠ L : ℝ in atTop, T ≤ L^(1/10:ℝ) :=
    hPowTop.eventually (eventually_ge_atTop T)
  filter_upwards [eventually_ge_atTop (Real.exp (1:ℝ)), hSmall, hTbig]
    with L hL hTailSmall hScaleLarge
  intro P i hPrime h6 hPn hDisj hV4 hLog hPi parityFlag
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    have hp6 := h6 g p hp
    omega
  have hIdx : sourceOriginalPGroupIndex r₀ L i.val :=
    (Finset.mem_filter.mp i.property).2
  have hscale : L^(1/10:ℝ) ≤
      (3/2:ℝ)*sourceOriginalPGroupScale r₀ L i.val := by
    rcases hIdx with h | h
    · exact h.1
    · have hbase : 1 ≤ L := by
        exact le_trans (by norm_num : (1:ℝ) ≤ Real.exp 1) hL
      exact (Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)).trans h.1
  have hOdd : sourceOriginalPGroupParityDelta ≤
      (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
        if (decide (Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) n.val)) ≠ parityFlag)
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) /
        sourceLiteralHP P := by
    exact hOddT _ (hScaleLarge.trans hscale) P i hPrime h3 hPn hDisj hPi parityFlag
  have hTail :=
    source_original_P_actual_polylog_rankin_tail
      r₀ L σ hr₀ hL hσ P hPrime h6 hPn hDisj hV4 hLog
  have hBound : (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (Real.exp L)^σ < (n.val:ℝ) then
        sourceOriginalW1 P n.val / (n.val:ℝ) else 0) ≤
        sourceOriginalPGroupParityDelta/2 :=
    hTail.trans hTailSmall
  exact parity_original_P_parity_small_mass_from_tail434
    P hPrime h3 hPn hDisj sourceOriginalPGroupParityDelta
      ((Real.exp L)^σ) parityFlag hδ.le hOdd hBound

theorem parity_original_P_actual_parity_small_eventually434
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      ∀ i : sourceOriginalPAllGroupType r₀ L, ∀ parityFlag : Bool,
        sourceOriginalPGroupParityDelta/2 ≤
          (∑' n : sourceOriginalPSupported
              (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)),
            if (decide (Odd (sourceOriginalPParityExponent
                (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) n.val)) ≠ parityFlag) ∧
                Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
            then sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) n.val /
              (n.val:ℝ) else 0) /
          sourceLiteralHP (sourceOriginalPAllActualBands r₀ L) := by
  have hOddEv := parity_original_P_parity_small_eventually434 r₀ hr₀
  have hLocalEv := source_original_P_all_actual_local_eventually r₀
  filter_upwards [eventually_ge_atTop (1:ℝ), hOddEv, hLocalEv]
    with L hL hOdd hLocal
  intro i parityFlag
  let P := sourceOriginalPAllActualBands r₀ L
  have hPrime : ∀ g p, p ∈ P g → p.Prime :=
    source_original_P_all_actual_band_prime r₀ L
  have h6 : ∀ g p, p ∈ P g → 6 ≤ p := hLocal.2.1
  have hPn : ∀ g, (P g).Nonempty := hLocal.1
  have hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h :=
    source_original_P_actual_all_disjoint r₀ L hr₀
      (lt_of_lt_of_le (by norm_num) hL)
  have hV4 : ∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4 :=
    hLocal.2.2
  have hLog : ∀ g p, p ∈ P g →
      Real.log (p:ℝ) ≤ L^(2/5:ℝ) :=
    source_original_P_all_actual_band_log r₀ L hL
  have hOddBound := hOdd P i hPrime h6 hPn hDisj hV4 hLog rfl parityFlag
  have hcut := source_original_P_actual_cutoff_exact r₀ L hr₀
  have hSummands :
      (fun n : sourceOriginalPSupported (Finset.univ.biUnion P) =>
        if (decide (Odd (sourceOriginalPParityExponent
            (Finset.univ.biUnion P) n.val)) ≠ parityFlag) ∧
            (n.val:ℝ) ≤ (Real.exp L)^(1/(132*(r₀:ℝ)))
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) =
      (fun n : sourceOriginalPSupported (Finset.univ.biUnion P) =>
        if (decide (Odd (sourceOriginalPParityExponent
            (Finset.univ.biUnion P) n.val)) ≠ parityFlag) ∧
            Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
        then sourceOriginalW1 P n.val / (n.val:ℝ) else 0) := by
    funext n
    have hn : (0:ℝ) < n.val := by
      exact_mod_cast Nat.pos_of_ne_zero n.property.1
    have hlog : ((n.val:ℝ) ≤ (Real.exp L)^(1/(132*(r₀:ℝ)))) ↔
        Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 := by
      rw [hcut]
      exact (Real.log_le_iff_le_exp hn).symm
    simp_rw [hlog]
  dsimp only [P] at hSummands hOddBound
  rw [← hSummands]
  exact hOddBound

theorem parity_original_P_actual_parity_small_full_eventually434
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ parityFlag : Bool,
      sourceOriginalPGroupParityDelta/2 ≤
        (∑' n : sourceOriginalPSupported
            (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)),
          if (decide (Odd (sourceOriginalPParityExponent
              (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) n.val)) ≠ parityFlag) ∧
              Real.log (n.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
          then sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) n.val /
            (n.val:ℝ) else 0) /
        sourceLiteralHP (sourceOriginalPAllActualBands r₀ L) := by
  filter_upwards [
    parity_original_P_actual_parity_small_eventually434 r₀ hr₀,
    source_original_P_all_actual_groups_nonempty_eventually r₀ hr₀]
    with L hEvent hNonempty parityFlag
  exact hEvent (Classical.choice hNonempty) parityFlag
end Green64Analytic.SourceBlockSieve

end

end

