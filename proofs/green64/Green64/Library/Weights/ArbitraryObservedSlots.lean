module

public import Green64.Library.Weights.HiddenSlotMarginal

@[expose] public section

/-!
# Weights / ArbitraryObservedSlots

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ArbitraryObservedSlots -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000
variable {G : Type} [Fintype G] [DecidableEq G]

private theorem b580_mark_lists_permutation_mem
    (P : G → Finset ℕ) (t : G → ℕ) (n : ℕ)
    (π : ∀ g,Equiv.Perm (Fin (t g)))
    (a : ∀ g,Fin (t g) → ℕ) (ha : a∈bigMarkLists P t n) :
    (fun g i => a g (π g i))∈bigMarkLists P t n := by
  apply Fintype.mem_piFinset.mpr
  intro g
  have hg := Fintype.mem_piFinset.mp ha g
  apply Finset.mem_filter.mpr
  refine ⟨Fintype.mem_piFinset.mpr ?_,?_⟩
  · intro i
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 (π g i)
  · exact (Finset.mem_filter.mp hg).2.comp (π g).injective

/-- Exact full-carrier invariance under arbitrary groupwise permutations
of the ORIGINAL ordered mark labels. The coupled test is unchanged. -/
theorem b580_original_all_group_permutation_sum
    (P : G → Finset ℕ) (t : G → ℕ) (n : ℕ)
    (π : ∀ g,Equiv.Perm (Fin (t g)))
    (f : (∀ g,Fin (t g) → ℕ) → ℂ) :
    (∑ a∈bigMarkLists P t n,f (fun g i => a g (π g i))) =
      ∑ a∈bigMarkLists P t n,f a := by
  apply Finset.sum_bij (fun a _ => fun g i => a g (π g i))
  · intro a ha
    exact b580_mark_lists_permutation_mem P t n π a ha
  · intro a ha b hb hab
    funext g i
    have he := congrFun (congrFun hab g) ((π g).symm i)
    simpa only [Equiv.apply_symm_apply] using he
  · intro b hb
    let a := fun g i => b g ((π g).symm i)
    have ha := b580_mark_lists_permutation_mem P t n (fun g => (π g).symm) b hb
    refine ⟨a,ha,?_⟩
    funext g i
    dsimp [a]
    rw [Equiv.symm_apply_apply]
  · intro a ha
    rfl

/-- Exact sum for ANY supplied injective observed-slot maps. All hidden
base and opposite-block probes are counted by (N-c)_r, including their
exclusions against each other and the observed coordinates. -/
theorem b580_original_all_group_observed_slot_sum
    (P : G → Finset ℕ) (c r : G → ℕ) (n : ℕ)
    (s : ∀ g,Fin (c g) → Fin (c g+r g))
    (hs : ∀ g,Function.Injective (s g))
    (f : (∀ g,Fin (c g) → ℕ) → ℂ) :
    (∑ a∈bigMarkLists P (fun g => c g+r g) n,
      f (fun g i => a g (s g i))) =
      ((∏ g,(smallPrimeCount (P g) n-c g).descFactorial (r g):ℕ):ℂ) *
        ∑ a∈bigMarkLists P c n,f a := by
  choose π hπ using fun g => b580_observed_injection_extends_permutation
    (c g) (r g) (s g) (hs g)
  calc
    _ = ∑ a∈bigMarkLists P (fun g => c g+r g) n,
        f (fun g i => a g (Fin.castAdd (r g) i)) := by
      have h := b580_original_all_group_permutation_sum
        P (fun g => c g+r g) n π
        (fun a => f (fun g i => a g (Fin.castAdd (r g) i)))
      simpa only [hπ] using h
    _ = _ := b580_original_all_group_hidden_slot_sum P c r n f

/-- Literal original decoration for arbitrary full counts t and actual
observed labels s. The supplied identity t=c+r exposes ALL hidden slots;
it does not identify them with a single base slot. -/
theorem b580_original_marked_observed_slot_marginal
    (P : G → Finset ℕ) (t c r : G → ℕ) (V : G → ℝ)
    (q : ℝ) (n : ℕ)
    (s : ∀ g,Fin (c g) → Fin (t g))
    (hs : ∀ g,Function.Injective (s g))
    (ht : ∀ g,t g=c g+r g)
    (f : (∀ g,Fin (c g) → ℕ) → ℂ) :
    actualBigMarkDecoration P t q V
      (fun a => f (fun g i => a g (s g i))) n =
      (b580HiddenAllFactor q c r (fun g => smallPrimeCount (P g) n) V:ℂ) *
        (∑ a∈bigMarkLists P c n,f a) /
          ((∏ g,(V g)^(c g):ℝ):ℂ) := by
  have hte : t=(fun g => c g+r g) := funext ht
  subst t
  calc
    _ = actualBigMarkDecoration P (fun g => c g+r g) q V
        (fun a => f (fun g i => a g (Fin.castAdd (r g) i))) n := by
      unfold actualBigMarkDecoration
      rw [b580_original_all_group_observed_slot_sum P c r n s hs f,
        b580_original_all_group_hidden_slot_sum]
    _ = _ := b580_original_marked_hidden_slot_marginal P c r V q n f

/-- Exact B13 endpoint count pattern: observing only B probes leaves
one base slot PLUS every A probe hidden, in each actual group. -/
theorem b580_original_opposite_block_base_marginal
    (P : G → Finset ℕ) (a b : G → ℕ) (V : G → ℝ)
    (q : ℝ) (n : ℕ)
    (s : ∀ g,Fin (b g) → Fin (1+a g+b g))
    (hs : ∀ g,Function.Injective (s g))
    (f : (∀ g,Fin (b g) → ℕ) → ℂ) :
    actualBigMarkDecoration P (fun g => 1+a g+b g) q V
      (fun z => f (fun g i => z g (s g i))) n =
      (b580HiddenAllFactor q b (fun g => 1+a g)
        (fun g => smallPrimeCount (P g) n) V:ℂ) *
        (∑ z∈bigMarkLists P b n,f z) /
          ((∏ g,(V g)^(b g):ℝ):ℂ) := by
  exact b580_original_marked_observed_slot_marginal
    P (fun g => 1+a g+b g) b (fun g => 1+a g) V q n s hs (fun g => by omega) f
end Green64Analytic.CorrelationSquare

end

end

