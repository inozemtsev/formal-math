module

public import Green64.Library.Weights.Part011
public import Green64.Library.Analysis.Estimates.Part002

@[expose] public section

/-!
# Analysis / Estimates / SourcePrimeFactorialMoment

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePrimeFactorialMoment -/

section

/-!
Real source marked-prime factorial moment.  The bound uses prime
factorization, so repeated primes are counted with multiplicity; no
fixed-order divisor-moment assertion is extrapolated to growing `j`.
-/

namespace Green64Analytic.CorrelationMellin

private theorem prime_factors_perm (l : List ℕ)
    (h : ∀ p ∈ l, Nat.Prime p) :
    (l.prod).primeFactorsList.Perm l := by
  induction l with
  | nil => simp
  | cons p t ih =>
      have hp : Nat.Prime p := h p (by simp)
      have ht : ∀ q ∈ t, Nat.Prime q := by
        intro q hq
        exact h q (by simp [hq])
      have htz : t.prod ≠ 0 := List.prod_ne_zero (by
        intro hz
        exact (ht 0 hz).ne_zero rfl)
      have hmul := Nat.perm_primeFactorsList_mul hp.ne_zero htz
      have htail : (p.primeFactorsList ++ t.prod.primeFactorsList).Perm (p :: t) := by
        simpa [Nat.primeFactorsList_prime hp] using (ih ht).cons p
      simpa [List.prod_cons] using hmul.trans htail

private theorem prime_lists_perm_of_product_eq
    (a b : List ℕ) (ha : ∀ p ∈ a, Nat.Prime p)
    (hb : ∀ p ∈ b, Nat.Prime p) (hprod : a.prod = b.prod) :
    a.Perm b := by
  exact (prime_factors_perm a ha).symm.trans
    (hprod ▸ prime_factors_perm b hb)

/-- Each product of `j` primes has at most `j!` ordered prime-list
representations, even with repeated primes. -/
theorem source_prime_product_fiber_card_le_factorial
    (s : Finset (List ℕ)) (j n : ℕ)
    (hlen : ∀ l ∈ s, l.length = j)
    (hprime : ∀ l ∈ s, ∀ p ∈ l, Nat.Prime p) :
    (s.filter (fun l => l.prod = n)).card ≤ j.factorial := by
  classical
  by_cases hem : (s.filter (fun l => l.prod = n)).Nonempty
  · obtain ⟨ref, href⟩ := hem
    have hrefS : ref ∈ s := (Finset.mem_filter.mp href).1
    have hrefP : ref.prod = n := (Finset.mem_filter.mp href).2
    have hsub : s.filter (fun l => l.prod = n) ⊆ ref.permutations.toFinset := by
      intro l hl
      have hlS : l ∈ s := (Finset.mem_filter.mp hl).1
      have hlP : l.prod = n := (Finset.mem_filter.mp hl).2
      have hperm : l.Perm ref :=
        prime_lists_perm_of_product_eq l ref (hprime l hlS) (hprime ref hrefS)
          (hlP.trans hrefP.symm)
      exact List.mem_toFinset.mpr (List.mem_permutations.mpr hperm)
    calc
      _ ≤ (ref.permutations.toFinset).card := Finset.card_le_card hsub
      _ ≤ ref.permutations.length := List.toFinset_card_le ref.permutations
      _ = j.factorial := by rw [List.length_permutations, hlen ref hrefS]
  · have hz : s.filter (fun l => l.prod = n) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hem
    simp [hz]

def primeTupleList (s : Finset ℕ) (j : ℕ)
    (t : Fin j → {p : ℕ // p ∈ s}) : List ℕ :=
  List.ofFn (fun i => (t i).val)

private theorem primeTupleList_injective (s : Finset ℕ) (j : ℕ) :
    Function.Injective (primeTupleList s j) := by
  intro t u heq
  have hval : (fun i => (t i).val) = (fun i => (u i).val) :=
    List.ofFn_inj.mp heq
  funext i
  exact Subtype.ext (congrFun hval i)


theorem source_prime_tuple_fiber_card_le_factorial
    (s : Finset ℕ) (j n : ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p) :
    ((Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
      (fun t => (primeTupleList s j t).prod = n)).card ≤ j.factorial := by
  classical
  let lists : Finset (List ℕ) := Finset.univ.image (primeTupleList s j)
  have hlen (l : List ℕ) (hl : l ∈ lists) : l.length = j := by
    rcases Finset.mem_image.mp hl with ⟨t, _, rfl⟩
    simp [primeTupleList]
  have hprimes (l : List ℕ) (hl : l ∈ lists) : ∀ p ∈ l, Nat.Prime p := by
    rcases Finset.mem_image.mp hl with ⟨t, _, rfl⟩
    simpa only [primeTupleList, List.forall_mem_ofFn_iff] using
      (fun i : Fin j => hprime (t i).val (t i).property)
  have hm : Set.MapsTo (primeTupleList s j)
      (↑((Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
        (fun t => (primeTupleList s j t).prod = n)))
      (↑(lists.filter (fun l => l.prod = n))) := by
    intro t ht
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩,
      (Finset.mem_filter.mp ht).2⟩
  have hinj : Set.InjOn (primeTupleList s j)
      (↑((Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
        (fun t => (primeTupleList s j t).prod = n))) := by
    intro t _ u _ heq
    exact primeTupleList_injective s j heq
  calc
    _ ≤ (lists.filter (fun l => l.prod = n)).card :=
      Finset.card_le_card_of_injOn (primeTupleList s j) hm hinj
    _ ≤ j.factorial :=
      source_prime_product_fiber_card_le_factorial lists j n hlen hprimes

/-- The exact growing-order `j!` L² coefficient estimate for powers of
a Dirichlet polynomial supported on genuine primes.  There is no
assumption fixing `j`; repeated primes and multinomial multiplicities
are retained in the filtered ordered tuples. -/
theorem source_short_prime_factorial_moment
    (s : Finset ℕ) (j : ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p)
    (w : {p : ℕ // p ∈ s} → ℂ) :
    (∑ n ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).image
        (fun t => (primeTupleList s j t).prod),
      ‖∑ t ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
          (fun t => (primeTupleList s j t).prod = n),
        ∏ i, w (t i)‖ ^ 2) ≤
      (j.factorial : ℝ) * (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2) ^ j := by
  classical
  let idx : (Fin j → {p : ℕ // p ∈ s}) → ℕ :=
    fun t => (primeTupleList s j t).prod
  let c : (Fin j → {p : ℕ // p ∈ s}) → ℂ := fun t => ∏ i, w (t i)
  have hfiber (n : ℕ) (_ : n ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).image idx) :
      (((Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
        (fun t => idx t = n)).card : ℝ) ≤ j.factorial := by
    exact_mod_cast source_prime_tuple_fiber_card_le_factorial s j n hprime
  have hcollapsed := collapsed_fiber_square_bound
    (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})) idx c
    (j.factorial : ℝ) hfiber

  have hnorm (t : Fin j → {p : ℕ // p ∈ s}) :
      ‖c t‖ ^ 2 = ∏ i, ‖w (t i)‖ ^ 2 := by
    calc
      _ = (∏ i, ‖w (t i)‖) ^ 2 := by simp [c, norm_prod]
      _ = ∏ i, ‖w (t i)‖ ^ 2 := by rw [Finset.prod_pow]
  have hpower :
      (∑ t : Fin j → {p : ℕ // p ∈ s}, ‖c t‖ ^ 2) =
        (∑ p : {p : ℕ // p ∈ s}, ‖w p‖ ^ 2) ^ j := by
    simp_rw [hnorm]
    exact (Fintype.sum_pow (fun p : {p : ℕ // p ∈ s} => ‖w p‖ ^ 2) j).symm
  calc
    _ ≤ (j.factorial : ℝ) *
        (∑ t : Fin j → {p : ℕ // p ∈ s}, ‖c t‖ ^ 2) := by
          simpa using hcollapsed
    _ = _ := by rw [hpower]

/-- Multiplicativity of the literal logarithmic phase along any list of
positive integer factors. -/
private theorem sourcePhase_list_prod (l : List ℕ) (t : ℝ)
    (hpos : ∀ p ∈ l, 0 < p) :
    sourcePhase l.prod t = (l.map (fun p => sourcePhase p t)).prod := by
  induction l with
  | nil => simp [sourcePhase]
  | cons p l ih =>
      have hp : 0 < p := hpos p (by simp)
      have hl : ∀ q ∈ l, 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      have hn : 0 < l.prod := by
        exact Nat.pos_of_ne_zero (List.prod_ne_zero (by
          intro hz
          exact (Nat.ne_of_gt (hl 0 hz)) rfl))
      simp only [List.prod_cons, List.map_cons]
      rw [sourcePhase_mul p l.prod hp hn t, ih hl]

/-- The actual prime Dirichlet polynomial, raised to arbitrary growing order,
is precisely the collapsed prime-product polynomial with its original weights. -/
theorem source_short_prime_power_collapsed
    (s : Finset ℕ) (j : ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p)
    (w : {p : ℕ // p ∈ s} → ℂ) (θ : ℝ) :
    (∑ p : {p : ℕ // p ∈ s}, w p * sourcePhase p.val θ)^j =
      ∑ n ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).image
        (fun f => (primeTupleList s j f).prod),
        (∑ f ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
          (fun f => (primeTupleList s j f).prod = n),
          ∏ i, w (f i)) * sourcePhase n θ := by
  classical
  let idx : (Fin j → {p : ℕ // p ∈ s}) → ℕ :=
    fun f => (primeTupleList s j f).prod
  let c : (Fin j → {p : ℕ // p ∈ s}) → ℂ := fun f => ∏ i, w (f i)
  have hphase (f : Fin j → {p : ℕ // p ∈ s}) :
      (∏ i, sourcePhase (f i).val θ) = sourcePhase (idx f) θ := by
    have hposit : ∀ p ∈ primeTupleList s j f, 0 < p := by
      simpa only [primeTupleList, List.forall_mem_ofFn_iff] using
        (fun i : Fin j => (hprime (f i).val (f i).property).pos)
    have hlist := sourcePhase_list_prod (primeTupleList s j f) θ hposit
    simpa only [idx, primeTupleList, List.map_ofFn, List.prod_ofFn,
      Function.comp_apply] using hlist.symm
  have hterm (f : Fin j → {p : ℕ // p ∈ s}) :
      (∏ i, w (f i) * sourcePhase (f i).val θ) =
        c f * sourcePhase (idx f) θ := by
    rw [Finset.prod_mul_distrib, hphase]
  calc
    _ = ∑ f : Fin j → {p : ℕ // p ∈ s},
        ∏ i, (w (f i) * sourcePhase (f i).val θ) :=
      Fintype.sum_pow (fun p : {p : ℕ // p ∈ s} =>
        w p * sourcePhase p.val θ) j
    _ = ∑ f : Fin j → {p : ℕ // p ∈ s},
        c f * sourcePhase (idx f) θ := by
      apply Finset.sum_congr rfl
      intro f _
      exact hterm f
    _ = ∑ n ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).image idx,
          ∑ f ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
            (fun f => idx f = n), c f * sourcePhase (idx f) θ := by
      exact (collapsed_fiber_sum_eq Finset.univ idx
        (fun f => c f * sourcePhase (idx f) θ)).symm
    _ = ∑ n ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).image idx,
          (∑ f ∈ (Finset.univ : Finset (Fin j → {p : ℕ // p ∈ s})).filter
            (fun f => idx f = n), c f) * sourcePhase n θ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]
    _ = _ := rfl

end Green64Analytic.CorrelationMellin

end

