module

public import Green64.Library.Correlation.Part067
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Weights / HiddenSlotMarginal

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHiddenSlotMarginal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000

private theorem b580_append_injective_iff {α : Type*} {c r : ℕ}
    (a : Fin c → α) (b : Fin r → α) :
    Function.Injective (Fin.append a b) ↔
      Function.Injective a ∧ Function.Injective b ∧
        ∀ i j,a i≠b j := by
  constructor
  · intro h
    refine ⟨?_,?_,?_⟩
    · intro i j hij
      apply Fin.castAdd_injective c r
      apply h
      simpa only [Fin.append_left] using hij
    · intro i j hij
      apply Fin.natAdd_injective r c
      apply h
      simpa only [Fin.append_right] using hij
    · intro i j hij
      have he : Fin.castAdd r i=Fin.natAdd c j := h (by
        simpa only [Fin.append_left,Fin.append_right] using hij)
      have hv := congrArg Fin.val he
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
  · rintro ⟨ha,hb,hab⟩ i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro hij
        exact congrArg (Fin.castAdd r) (ha (by
          simpa only [Fin.append_left] using hij))
      · intro hij
        exact False.elim (hab i j (by
          simpa only [Fin.append_left,Fin.append_right] using hij))
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro hij
        exact False.elim (hab j i (by
          simpa only [Fin.append_left,Fin.append_right] using hij.symm))
      · intro hij
        exact congrArg (Fin.natAdd c) (hb (by
          simpa only [Fin.append_right] using hij))

private theorem b580_support_sdiff (P F : Finset ℕ) (n : ℕ) :
    smallPrimeSupport (P\F) n=smallPrimeSupport P n\F := by
  ext p
  simp only [smallPrimeSupport,Finset.mem_filter,Finset.mem_sdiff]
  tauto

private theorem b580_ordered_append_mem
    (P : Finset ℕ) (c r n : ℕ) (a : Fin c → ℕ) (b : Fin r → ℕ) :
    Fin.append a b∈orderedBigMarks P (c+r) n ↔
      a∈orderedBigMarks P c n ∧
        b∈orderedBigMarks (P\Finset.univ.image a) r n := by
  constructor
  · intro h
    have hp := (Finset.mem_filter.mp h).1
    have hi := (b580_append_injective_iff a b).mp (Finset.mem_filter.mp h).2
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Fintype.mem_piFinset.mpr ?_,hi.1⟩
      intro i
      simpa only [Fin.append_left] using
        Fintype.mem_piFinset.mp hp (Fin.castAdd r i)
    · apply Finset.mem_filter.mpr
      refine ⟨Fintype.mem_piFinset.mpr ?_,hi.2.1⟩
      intro j
      rw [b580_support_sdiff]
      apply Finset.mem_sdiff.mpr
      constructor
      · simpa only [Fin.append_right] using
          Fintype.mem_piFinset.mp hp (Fin.natAdd c j)
      · intro hj
        obtain ⟨i,_,he⟩ := Finset.mem_image.mp hj
        exact hi.2.2 i j he
  · rintro ⟨ha,hb⟩
    have haP := (Finset.mem_filter.mp ha).1
    have hbP := (Finset.mem_filter.mp hb).1
    have hbs (j : Fin r) : b j∈smallPrimeSupport P n\Finset.univ.image a := by
      rw [←b580_support_sdiff]
      exact Fintype.mem_piFinset.mp hbP j
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using Fintype.mem_piFinset.mp haP i
      · simpa only [Fin.append_right] using (Finset.mem_sdiff.mp (hbs j)).1
    · apply (b580_append_injective_iff a b).mpr
      refine ⟨(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2,?_⟩
      intro i j he
      exact (Finset.mem_sdiff.mp (hbs j)).2
        (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩)

variable {G : Type} [Fintype G] [DecidableEq G]

/-- All hidden slots are summed, with distinctness against ALL observed
slots and against each other. Observed coordinates retain their ordered
labels; the test can couple different groups arbitrarily. -/
theorem b580_original_all_group_hidden_slot_sum
    (P : G → Finset ℕ) (c r : G → ℕ) (n : ℕ)
    (f : (∀ g,Fin (c g) → ℕ) → ℂ) :
    (∑ a∈bigMarkLists P (fun g => c g+r g) n,
      f (fun g i => a g (Fin.castAdd (r g) i))) =
      ((∏ g,(smallPrimeCount (P g) n-c g).descFactorial (r g):ℕ):ℂ) *
        ∑ a∈bigMarkLists P c n,f a := by
  let S := bigMarkLists P c n
  let H (a : ∀ g,Fin (c g) → ℕ) :=
    bigMarkLists (fun g => P g\Finset.univ.image (a g)) r n
  have hmem (a : ∀ g,Fin (c g) → ℕ) (b : ∀ g,Fin (r g) → ℕ) :
      (fun g => Fin.append (a g) (b g))∈
        bigMarkLists P (fun g => c g+r g) n ↔
      a∈S ∧ b∈H a := by
    constructor
    · intro h
      have hg (g : G) := (b580_ordered_append_mem (P g) (c g) (r g) n (a g) (b g)).mp
        (Fintype.mem_piFinset.mp h g)
      exact ⟨Fintype.mem_piFinset.mpr (fun g => (hg g).1),
        Fintype.mem_piFinset.mpr (fun g => (hg g).2)⟩
    · rintro ⟨ha,hb⟩
      apply Fintype.mem_piFinset.mpr
      intro g
      exact (b580_ordered_append_mem (P g) (c g) (r g) n (a g) (b g)).mpr
        ⟨Fintype.mem_piFinset.mp ha g,Fintype.mem_piFinset.mp hb g⟩
  have hbij :
      (∑ z∈S.sigma H,f z.1) =
      ∑ a∈bigMarkLists P (fun g => c g+r g) n,
        f (fun g i => a g (Fin.castAdd (r g) i)) := by
    apply Finset.sum_bij (fun z _ => fun g => Fin.append (z.1 g) (z.2 g))
    · intro z hz
      exact (hmem z.1 z.2).mpr (Finset.mem_sigma.mp hz)
    · intro z hz y hy he
      have ha : z.1=y.1 := by
        funext g i
        have hh := congrFun (congrFun he g) (Fin.castAdd (r g) i)
        simpa only [Fin.append_left] using hh
      have hb : z.2=y.2 := by
        funext g i
        have hh := congrFun (congrFun he g) (Fin.natAdd (c g) i)
        simpa only [Fin.append_right] using hh
      exact Sigma.ext ha (heq_of_eq hb)
    · intro a ha
      let a0 : ∀ g,Fin (c g) → ℕ := fun g i => a g (Fin.castAdd (r g) i)
      let b0 : ∀ g,Fin (r g) → ℕ := fun g i => a g (Fin.natAdd (c g) i)
      have he : (fun g => Fin.append (a0 g) (b0 g))=a := by
        funext g i
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · simp only [Fin.append_left,a0]
        · simp only [Fin.append_right,b0]
      have hm := (hmem a0 b0).mp (he.symm ▸ ha)
      exact ⟨⟨a0,b0⟩,Finset.mem_sigma.mpr hm,he⟩
    · intro z hz
      simp only [Fin.append_left]
  have hcard (a : ∀ g,Fin (c g) → ℕ) (ha : a∈S) :
      (H a).card=∏ g,(smallPrimeCount (P g) n-c g).descFactorial (r g) := by
    unfold H
    rw [bigMarkLists_card]
    apply Finset.prod_congr rfl
    intro g _
    have hga := Fintype.mem_piFinset.mp ha g
    have hsub : Finset.univ.image (a g)⊆smallPrimeSupport (P g) n := by
      intro p hp
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hga).1 i
    have hN : smallPrimeCount (P g\Finset.univ.image (a g)) n =
        smallPrimeCount (P g) n-c g := by
      unfold smallPrimeCount
      rw [b580_support_sdiff,Finset.card_sdiff_of_subset hsub,
        Finset.card_image_of_injective _ (Finset.mem_filter.mp hga).2]
      simp
    rw [hN]
  calc
    _ = ∑ z∈S.sigma H,f z.1 := hbij.symm
    _ = ∑ a∈S,
        ((∏ g,(smallPrimeCount (P g) n-c g).descFactorial (r g):ℕ):ℂ)*f a := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro a ha
      change (∑ _b∈H a,f a)=_
      rw [Finset.sum_const,nsmul_eq_mul,hcard a ha]
    _ = _ := by rw [Finset.mul_sum]

/-- Product of the literal group factors after all hidden slots have
been summed; the remaining V^{-c} belongs to the observed carrier. -/
def b580HiddenAllFactor (q : ℝ) (c r N : G → ℕ) (V : G → ℝ) : ℝ :=
  ∏ g,b580HiddenGroupFactor q (c g) (r g) (N g) (V g)

/-- Exact original marked decoration marginal for variable hidden counts.
No source coefficient, physical position, cap, Fourier measure, or
auxiliary parameter inside f is averaged or replaced. -/
theorem b580_original_marked_hidden_slot_marginal
    (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
    (q : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ) :
    actualBigMarkDecoration P (fun g => c g+r g) q V
      (fun a => f (fun g i => a g (Fin.castAdd (r g) i))) n =
      (b580HiddenAllFactor q c r (fun g => smallPrimeCount (P g) n) V:ℂ) *
        (∑ a∈bigMarkLists P c n,f a) /
          ((∏ g,(V g)^(c g):ℝ):ℂ) := by
  unfold actualBigMarkDecoration
  rw [b580_original_all_group_hidden_slot_sum]
  have hp :
      bigMarkPrefactor P (fun g => c g+r g) q V n *
        ((∏ g,(smallPrimeCount (P g) n-c g).descFactorial (r g):ℕ):ℂ) =
      (b580HiddenAllFactor q c r (fun g => smallPrimeCount (P g) n) V:ℂ) /
        ((∏ g,(V g)^(c g):ℝ):ℂ) := by
    unfold bigMarkPrefactor b580HiddenAllFactor b580HiddenGroupFactor
    push_cast
    rw [←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro g _
    rw [pow_add]
    ring
  rw [←mul_assoc,hp]
  ring


/-- Every fixed injective observed-slot map extends to a permutation of
the ORIGINAL full label carrier. No observed subset is chosen by size
alone; the supplied map is preserved pointwise. -/
theorem b580_observed_injection_extends_permutation
    (c r : ℕ) (s : Fin c → Fin (c+r)) (hs : Function.Injective s) :
    ∃ π : Equiv.Perm (Fin (c+r)), ∀ i,π (Fin.castAdd r i)=s i := by
  classical
  let F : Finset (Fin (c+r)) := (Finset.univ.image s)ᶜ
  have hF : F.card=r := by
    dsimp [F]
    rw [Finset.card_compl,Finset.card_image_of_injective _ hs]
    simp
  let e : Fin r ≃ ↥F := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,Fintype.card_coe,hF])
  let b : Fin r → Fin (c+r) := fun i => (e i).val
  have hb : Function.Injective b := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hcross : ∀ i j,s i≠b j := by
    intro i j hij
    have hj : b j∈F := (e j).property
    have hn : b j∉Finset.univ.image s := Finset.mem_compl.mp hj
    exact hn (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hij⟩)
  let f := Fin.append s b
  have hf : Function.Injective f :=
    (b580_append_injective_iff s b).mpr ⟨hs,hb,hcross⟩
  let π : Equiv.Perm (Fin (c+r)) :=
    Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩
  refine ⟨π,?_⟩
  intro i
  change Fin.append s b (Fin.castAdd r i)=s i
  exact Fin.append_left s b i
end Green64Analytic.CorrelationSquare

end

end

