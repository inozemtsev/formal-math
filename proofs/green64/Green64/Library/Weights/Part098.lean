module

public import Green64.Library.Weights.ObservedSlots
public import Green64.Library.Analysis.Estimates.HarmonicLift
public import Green64.Library.Correlation.Part034
public import Green64.Library.Weights.ArbitraryObservedSlots
public import Green64.Library.Weights.Part054

@[expose] public section

/-!
# Weights / Part098

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualProbeProductTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- The already-native original grouped probe equivalence, with the
trivial all-group subtype removed. Its Fin enumeration is unchanged. -/
def b598OriginalProbeGroupedEquiv434 (m : ℕ) (A : Finset (G×Fin m)) :
    (Σ g : G, Fin (sourceOriginalProbeChosenGroupCount434 m A g)) ≃ A := by
  let eu : (Finset.univ : Finset G) ≃ G :=
    Equiv.subtypeUnivEquiv (fun g => Finset.mem_univ g)
  let es : (Σ g : G, Fin (sourceOriginalProbeChosenGroupCount434 m A g)) ≃
      (Σ g : (Finset.univ : Finset G),
        Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) :=
    Equiv.sigmaCongrLeft (β := fun g : (Finset.univ : Finset G) =>
      Fin (sourceOriginalProbeChosenGroupCount434 m A g.val)) eu.symm
  exact es.trans (sourceOriginalProbeGroupSigmaEquiv434 m Finset.univ A
    (by intro z hz; simp [sourceOriginalProbeBlock434]))

@[simp] theorem b598_probe_grouped_equiv_apply434
    (m : ℕ) (A : Finset (G×Fin m)) (g : G)
    (i : Fin (sourceOriginalProbeChosenGroupCount434 m A g)) :
    b598OriginalProbeGroupedEquiv434 m A ⟨g,i⟩ =
      ⟨(g,b598ProbeGroupIndex434 m A g i),b598_probe_group_index_mem434 m A g i⟩ := by
  rfl

@[simp] theorem b598_probe_grouped_equiv_group434
    (m : ℕ) (A : Finset (G×Fin m))
    (z : Σ g : G, Fin (sourceOriginalProbeChosenGroupCount434 m A g)) :
    (b598OriginalProbeGroupedEquiv434 m A z).val.1=z.1 := by
  cases z
  rfl

/-- Reindex one grouped observed tuple onto the actual labelled nu-block. -/
def b598GroupedProbeTuple434 (m : ℕ) (A : Finset (G×Fin m))
    (a : ∀ g, Fin (sourceOriginalProbeChosenGroupCount434 m A g) → ℕ) : A → ℕ :=
  fun z => a ((b598OriginalProbeGroupedEquiv434 m A).symm z).1
    ((b598OriginalProbeGroupedEquiv434 m A).symm z).2

@[simp] theorem b598_grouped_probe_tuple_apply434
    (m : ℕ) (A : Finset (G×Fin m))
    (a : ∀ g, Fin (sourceOriginalProbeChosenGroupCount434 m A g) → ℕ)
    (g : G) (i : Fin (sourceOriginalProbeChosenGroupCount434 m A g)) :
    b598GroupedProbeTuple434 m A a (b598OriginalProbeGroupedEquiv434 m A ⟨g,i⟩)=a g i := by
  exact congrArg
    (fun z : Σ g : G, Fin (sourceOriginalProbeChosenGroupCount434 m A g) => a z.1 z.2)
    ((b598OriginalProbeGroupedEquiv434 m A).symm_apply_apply ⟨g,i⟩)

/-- Numerical products, including every original labelled position,
are preserved by the exact grouped/global probe transport. -/
theorem b598_grouped_probe_product434
    (m : ℕ) (A : Finset (G×Fin m))
    (a : ∀ g, Fin (sourceOriginalProbeChosenGroupCount434 m A g) → ℕ) :
    (∏ z : A,b598GroupedProbeTuple434 m A a z)=∏g,∏i,a g i := by
  have h := (b598OriginalProbeGroupedEquiv434 m A).prod_comp (b598GroupedProbeTuple434 m A a)
  rw [Fintype.prod_sigma] at h
  simpa only [b598_grouped_probe_tuple_apply434] using h.symm

/-- Target A product of the ORIGINAL free marked array, on its supplied
physical slots, equals the grouped observed product exactly. -/
theorem b598_original_target_observed_product434
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (a : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceOriginalProbeFreeTargetX434 J ell m hmJ nu a =
      ∏g,∏i,a g (b598OriginalObservedASlot434 J ell m hmJ nu g i) := by
  unfold sourceOriginalProbeFreeTargetX434
  rw [←(b598OriginalProbeGroupedEquiv434 m nu.1).prod_comp
    (fun z => a z.val.1 (sourceOriginalProbeFreeIndex434 J ell m hmJ nu
      z.val.1 z.val.2 (Or.inl z.property))),Fintype.prod_sigma]
  rfl

/-- Source B product retains its own ORIGINAL free physical positions. -/
theorem b598_original_source_observed_product434
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (a : ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a =
      ∏g,∏i,a g (b598OriginalObservedBSlot434 J ell m hmJ nu g i) := by
  unfold sourceOriginalProbeFreeSourceX434
  rw [←(b598OriginalProbeGroupedEquiv434 m nu.2).prod_comp
    (fun z => a z.val.1 (sourceOriginalProbeFreeIndex434 J ell m hmJ nu
      z.val.1 z.val.2 (Or.inr z.property))),Fintype.prod_sigma]
  rfl

/- Exact product used in the existing harmonic-density theorem. -/
omit [DecidableEq G] in
theorem b598_selected_nat_cast_product434
    (c : G → ℕ) (a : ∀ g,Fin (c g) → ℕ) :
    ((∏g,∏i,a g i:ℕ):ℝ)=b579SelectedPrimeProduct c a := by
  simp [b579SelectedPrimeProduct]
end Green64Analytic.CorrelationSquare

end

end

/-! ## ObservedHarmonicTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- Independent original prime lists at every grouped observed coordinate.
No divisor, distinctness, active-cell or auxiliary avoidance conditioning. -/
def b598RawSelectedGroupLists434 (P : G → Finset ℕ) (c : G → ℕ) :
    Finset (∀ g,Fin (c g) → ℕ) :=
  Fintype.piFinset (fun g => Fintype.piFinset (fun _ : Fin (c g) => P g))

@[simp] theorem b598_mem_raw_selected_group_lists434
    (P : G → Finset ℕ) (c : G → ℕ) (a : ∀ g,Fin (c g) → ℕ) :
    a∈b598RawSelectedGroupLists434 P c ↔ ∀ g i,a g i∈P g := by
  constructor
  · intro ha g i
    exact Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ha g) i
  · intro ha
    exact Fintype.mem_piFinset.mpr (fun g => Fintype.mem_piFinset.mpr (ha g))

/-- Actual observed divisor lists are a subset of the original independent
prime carrier; no selected tuple is introduced before the row estimate. -/
theorem b598_actual_selected_lists_subset_raw434
    (P : G → Finset ℕ) (c : G → ℕ) (n : ℕ) :
    bigMarkLists P c n ⊆ b598RawSelectedGroupLists434 P c := by
  intro a ha
  apply (b598_mem_raw_selected_group_lists434 P c a).mpr
  intro g i
  have hg := Fintype.mem_piFinset.mp ha g
  have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
  exact (Finset.mem_filter.mp hi).1

@[simp] theorem b598_probe_grouped_equiv_symm_group434
    (m : ℕ) (A : Finset (G×Fin m)) (z : A) :
    ((b598OriginalProbeGroupedEquiv434 m A).symm z).1=z.val.1 := by
  have h := b598_probe_grouped_equiv_group434 m A ((b598OriginalProbeGroupedEquiv434 m A).symm z)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The actual independent harmonic mass is preserved exactly by the
original grouped/global probe equivalence, including all repetitions. -/
theorem b598_grouped_probe_harmonic_mass434
    (m : ℕ) (A : Finset (G×Fin m)) (V : G → ℝ)
    (a : ∀ g,Fin (sourceOriginalProbeChosenGroupCount434 m A g) → ℕ) :
    b579SelectedHarmonicMass (sourceOriginalProbeChosenGroupCount434 m A) V a =
      sourceSharedLaw434 (fun z : A => sourcePrimeSharedAtom434 (V z.val.1))
        (b598GroupedProbeTuple434 m A a) := by
  have h := Fintype.prod_equiv (b598OriginalProbeGroupedEquiv434 m A)
    (fun z => (1:ℝ)/((a z.1 z.2:ℝ)*V z.1))
    (fun z => (1:ℝ)/((b598GroupedProbeTuple434 m A a z:ℝ)*V z.val.1)) (by
      intro z
      cases z
      simp only [b598_grouped_probe_tuple_apply434,b598_probe_grouped_equiv_group434])
  rw [Fintype.prod_sigma] at h
  exact h

/-- Full finite harmonic-law reindexing for the original selected probes.
This is an equality of the actual independent law, not an assumption of
independence of physical rows or a renormalization after a restriction. -/
theorem b598_original_grouped_harmonic_sum434
    (m : ℕ) (A : Finset (G×Fin m)) (P : G → Finset ℕ) (V : G → ℝ)
    (f : (A → ℕ) → ℝ) :
    (∑ a∈b598RawSelectedGroupLists434 P (sourceOriginalProbeChosenGroupCount434 m A),
      b579SelectedHarmonicMass (sourceOriginalProbeChosenGroupCount434 m A) V a *
        f (b598GroupedProbeTuple434 m A a)) =
    ∑ a∈Fintype.piFinset (fun z : A => P z.val.1),
      sourceSharedLaw434 (fun z : A => sourcePrimeSharedAtom434 (V z.val.1)) a * f a := by
  apply Finset.sum_bij (fun a _ => b598GroupedProbeTuple434 m A a)
  · intro a ha
    apply Fintype.mem_piFinset.mpr
    intro z
    have hm := (b598_mem_raw_selected_group_lists434 P _ a).mp ha
    have hh := hm ((b598OriginalProbeGroupedEquiv434 m A).symm z).1
      ((b598OriginalProbeGroupedEquiv434 m A).symm z).2
    change b598GroupedProbeTuple434 m A a z∈P ((b598OriginalProbeGroupedEquiv434 m A).symm z).1 at hh
    simpa only [b598_probe_grouped_equiv_symm_group434] using hh
  · intro a ha b hb h
    funext g i
    have hh := congrFun h (b598OriginalProbeGroupedEquiv434 m A ⟨g,i⟩)
    simpa only [b598_grouped_probe_tuple_apply434] using hh
  · intro b hb
    let a := fun g (i : Fin (sourceOriginalProbeChosenGroupCount434 m A g)) =>
      b (b598OriginalProbeGroupedEquiv434 m A ⟨g,i⟩)
    have ha : a∈b598RawSelectedGroupLists434 P (sourceOriginalProbeChosenGroupCount434 m A) := by
      apply (b598_mem_raw_selected_group_lists434 P _ a).mpr
      intro g i
      have h := Fintype.mem_piFinset.mp hb (b598OriginalProbeGroupedEquiv434 m A ⟨g,i⟩)
      simpa only [b598_probe_grouped_equiv_group434] using h
    refine ⟨a,ha,?_⟩
    funext z
    dsimp only [a,b598GroupedProbeTuple434]
    rw [Equiv.apply_symm_apply]
  · intro a ha
    rw [b598_grouped_probe_harmonic_mass434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## HiddenGroupL1Bound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A positive hidden count makes the actual hidden completion vanish
when the observed count exceeds the available distinct divisor primes. -/
theorem b599_hidden_group_zero_of_overfull
    (q V : ℝ) (c r N : ℕ) (hc : N < c) (hr : 1 ≤ r) :
    b580HiddenGroupFactor q c r N V = 0 := by
  have hz : (N-c).descFactorial r = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
  simp only [b580HiddenGroupFactor, hz, Nat.cast_zero, mul_zero, zero_div]

/-- The unsquared original hidden factor is nonnegative. -/
theorem b599_hidden_group_nonneg
    (c r N : ℕ) (V : ℝ) (hV : 0 ≤ V) :
    0 ≤ b580HiddenGroupFactor (1/2) c r N V := by
  unfold b580HiddenGroupFactor
  positivity

/-- One constant bounds the original UNSQUARED completion factor,
uniformly in the observed count and every physical divisor count.
At least one base/opposite slot is hidden, as at the actual endpoints. -/
theorem b599_hidden_group_l1_uniform
    (vmin : ℝ) (rmax : ℕ) (hv : 0 < vmin) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c r N : ℕ) (V : ℝ),
      1 ≤ r → r ≤ rmax → vmin ≤ V →
      0 ≤ b580HiddenGroupFactor (1/2) c r N V ∧
        b580HiddenGroupFactor (1/2) c r N V ≤ C := by
  obtain ⟨C, hC, hbound⟩ := uniform_group_mark_bound
    (1/2:ℝ) vmin rmax (by norm_num) (by norm_num) hv
  refine ⟨C, hC, ?_⟩
  intro c r N V hr hrmax hV
  refine ⟨b599_hidden_group_nonneg c r N V (hv.trans_le hV).le, ?_⟩
  by_cases hc : c ≤ N
  · rw [b580_hidden_factor_eq_marked_tail (1/2) V c r N hc]
    exact (le_abs_self _).trans (hbound r (N-c) V hrmax hV)
  · rw [b599_hidden_group_zero_of_overfull (1/2) V c r N (by omega) hr]
    linarith

/-- Product bound over all actual groups, with the same fixed constant.
No squared marked energy, product cap, or auxiliary square root occurs. -/
theorem b599_hidden_all_group_l1_uniform
    (vmin : ℝ) (rmax : ℕ) (hv : 0 < vmin) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (c r N : G → ℕ) (V : G → ℝ),
      (∀ g, 1 ≤ r g ∧ r g ≤ rmax) → (∀ g, vmin ≤ V g) →
      0 ≤ b580HiddenAllFactor (1/2) c r N V ∧
        b580HiddenAllFactor (1/2) c r N V ≤ C^(Fintype.card G) := by
  obtain ⟨C, hC, hbound⟩ := b599_hidden_group_l1_uniform vmin rmax hv
  refine ⟨C, hC, ?_⟩
  intro G _ _ c r N V hr hV
  have hb (g : G) := hbound (c g) (r g) (N g) (V g)
    (hr g).1 (hr g).2 (hV g)
  constructor
  · exact Finset.prod_nonneg (fun g _ => (hb g).1)
  · calc
      _ ≤ ∏ _g : G, C := by
        exact Finset.prod_le_prod₀ (fun g _ => (hb g).1)
          (fun g _ => (hb g).2)
      _ = _ := by simp

/-- The original marked decoration with its supplied observed-slot maps
has an unsquared L1 bound after summing every hidden slot. The complete
complex test may couple groups; its actual observed values are retained. -/
theorem b599_original_observed_marked_l1_uniform
    (vmin : ℝ) (rmax : ℕ) (hv : 0 < vmin) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (t c r : G → ℕ) (V : G → ℝ) (n : ℕ)
        (s : ∀ g, Fin (c g) → Fin (t g))
        (_hs : ∀ g, Function.Injective (s g))
        (_ht : ∀ g, t g = c g + r g)
        (f : (∀ g, Fin (c g) → ℕ) → ℂ),
      (∀ g, 1 ≤ r g ∧ r g ≤ rmax) → (∀ g, vmin ≤ V g) →
      ‖actualBigMarkDecoration P t (1/2) V
        (fun a => f (fun g i => a g (s g i))) n‖ ≤
        C^(Fintype.card G) *
          (∑ a ∈ bigMarkLists P c n, ‖f a‖) /
            (∏ g, (V g)^(c g)) := by
  obtain ⟨C, hC, hbound⟩ := b599_hidden_all_group_l1_uniform vmin rmax hv
  refine ⟨C, hC, ?_⟩
  intro G _ _ P t c r V n s hs ht f hr hV
  have hVp (g : G) : 0 < V g := hv.trans_le (hV g)
  have hA : 0 < ∏ g, (V g)^(c g) :=
    Finset.prod_pos (fun g _ => pow_pos (hVp g) _)
  have hB := hbound c r (fun g => smallPrimeCount (P g) n) V hr hV
  rw [b580_original_marked_observed_slot_marginal P t c r V
    (1/2) n s hs ht f]
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hB.1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  apply div_le_div_of_nonneg_right _ hA.le
  apply mul_le_mul hB.2 (norm_sum_le _ _) (norm_nonneg _)
  exact pow_nonneg (by linarith : 0 ≤ C) _
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualCoupledCanonicalMarginal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- The actual original B column on the grouped source observed tuple. -/
def b598OriginalSourceColumn434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a : ∀ g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.2 g) → ℕ) : ℂ :=
  sourceOriginalActualPrimitiveGlobalKernel434 Q
    (sourceOriginalProbeActiveCellsB434 m P V nu hB xi) hB
    (sourceOriginalProbeCellB434 m P V nu hB)
    (sourceOriginalProbeDB434 m nu aux) (∏g,∏i,a g i)

/-- The actual original A column on the grouped target observed tuple. -/
def b598OriginalTargetColumn434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (b : ∀ g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.1 g) → ℕ) : ℂ :=
  sourceOriginalActualPrimitiveGlobalKernel434 Q
    (sourceOriginalProbeActiveCellsA434 m P V nu hA xi) hA
    (sourceOriginalProbeCellA434 m P V nu hA)
    (sourceOriginalProbeDA434 m nu aux) (∏g,∏i,b g i)

/-- Literal signed canonical Knu with both actual original cell masses. -/
def b598GroupedCanonicalKnu434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a : ∀ g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.2 g) → ℕ)
    (b : ∀ g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.1 g) → ℕ) : ℂ :=
  sourceOriginalActualPrimitiveComparisonKernel434 Q
    (sourceOriginalProbeActiveCellsA434 m P V nu hA xi)
    (sourceOriginalProbeActiveCellsB434 m P V nu hB xi) hA hB
    (sourceOriginalProbeCellA434 m P V nu hA)
    (sourceOriginalProbeCellB434 m P V nu hB)
    (sourceOriginalProbeDA434 m nu aux) (∏g,∏i,b g i)
    (sourceOriginalProbeDB434 m nu aux) (∏g,∏i,a g i)
    (nu.1.card+nu.2.card)

/-- Exact physical Knu transport, retaining the supplied original slot
locations on both endpoints and its inclusion-exclusion sign. -/
theorem b598_original_canonical_grouped434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux a b =
      b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux
        (fun g i => a g (b598OriginalObservedBSlot434 J ell m hmJ nu g i))
        (fun g i => b g (b598OriginalObservedASlot434 J ell m hmJ nu g i)) := by
  unfold sourceOriginalProbeCanonicalKnu434 sourceOriginalProbeConcreteKnu434
    sourceAuxiliaryOriginalComparisonKnu434 b598GroupedCanonicalKnu434
    sourceOriginalActualPrimitiveComparisonKernel434
  rw [b598_original_target_observed_product434,b598_original_source_observed_product434]

/-- Its norm is exactly the product of the two true canonical columns. -/
theorem b598_grouped_canonical_norm434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a : ∀ g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.2 g) → ℕ)
    (b : ∀ g,Fin (sourceOriginalProbeChosenGroupCount434 m nu.1 g) → ℕ) :
    ‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux a b‖ =
      ‖b598OriginalSourceColumn434 m nu Q hB xi P V aux a‖ *
      ‖b598OriginalTargetColumn434 m nu Q hA xi P V aux b‖ := by
  simp only [b598GroupedCanonicalKnu434,sourceOriginalActualPrimitiveComparisonKernel434,
    norm_mul,norm_neg,norm_pow,norm_one,one_pow,one_mul,
    b598OriginalSourceColumn434,b598OriginalTargetColumn434]
  ring

/-- On clean physical endpoints the FULL original free-list ban is proved
one before factorization. Every hidden slot remains in each decoration. -/
theorem b598_actual_clean_coupled_decoration_norm434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (D w wp : ℕ) (hPrime : ∀ z,(aux z).Prime) (hAuxD : ∀ z,aux z∣D)
    (hclean : D.Coprime w) (hclean' : D.Coprime wp) :
    ‖sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux (1/2) w wp‖ =
      ‖actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) (1/2) V
        (fun a => b598OriginalSourceColumn434 m nu Q hB xi P V aux
          (fun g i => a g (b598OriginalObservedBSlot434 J ell m hmJ nu g i))) w‖ *
      ‖actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) (1/2) V
        (fun b => b598OriginalTargetColumn434 m nu Q hA xi P V aux
          (fun g i => b g (b598OriginalObservedASlot434 J ell m hmJ nu g i))) wp‖ := by
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let fB := fun a : ∀ g,Fin (t g) → ℕ => b598OriginalSourceColumn434 m nu Q hB xi P V aux
    (fun g i => a g (b598OriginalObservedBSlot434 J ell m hmJ nu g i))
  let fA := fun b : ∀ g,Fin (t g) → ℕ => b598OriginalTargetColumn434 m nu Q hA xi P V aux
    (fun g i => b g (b598OriginalObservedASlot434 J ell m hmJ nu g i))
  let sign : ℂ := -(-1:ℂ)^(nu.1.card+nu.2.card)
  have hval (a : ∀ g,Fin (t g) → ℕ) (ha : a∈bigMarkLists P t w)
      (b : ∀ g,Fin (t g) → ℕ) (hb : b∈bigMarkLists P t wp) :
      sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b =
        sign*fB a*fA b := by
    rw [b580_actual_clean_free_kernel_eq_original J ell m hmJ nu Q hA hB xi P V aux
      D w wp hPrime hAuxD hclean hclean' a b ha hb,b598_original_canonical_grouped434]
    dsimp [sign,fA,fB,b598GroupedCanonicalKnu434,
      sourceOriginalActualPrimitiveComparisonKernel434,b598OriginalSourceColumn434,
      b598OriginalTargetColumn434]
    ring
  have hsum :
      (∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,
        sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b) =
      sign*(∑ a∈bigMarkLists P t w,fB a)*(∑ b∈bigMarkLists P t wp,fA b) := by
    calc
      _ = ∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,sign*fB a*fA b := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_congr rfl (fun b hb => hval a ha b hb)
      _ = ∑ a∈bigMarkLists P t w,(sign*fB a)*(∑ b∈bigMarkLists P t wp,fA b) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
      _ = _ := by
        rw [← Finset.sum_mul,← Finset.mul_sum]
  change ‖bigMarkPrefactor P t (1/2) V w * bigMarkPrefactor P t (1/2) V wp *
      (∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,
        sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b)‖ = _
  rw [hsum]
  change _ = ‖actualBigMarkDecoration P t (1/2) V fB w‖ *
    ‖actualBigMarkDecoration P t (1/2) V fA wp‖
  simp only [actualBigMarkDecoration,norm_mul,sign,norm_neg,norm_pow,norm_one,one_pow,one_mul]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## ObservedCoupledHarmonicBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- Exact observed contribution after summing all hidden original slots.
The two selected products compensate only their own harmonic atoms. -/
def b598ObservedCoupledHarmonicMass434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (w wp : ℕ) : ℝ :=
  ∑ a∈bigMarkLists P (sourceOriginalProbeChosenGroupCount434 m nu.2) w,
    ∑ b∈bigMarkLists P (sourceOriginalProbeChosenGroupCount434 m nu.1) wp,
      b579SelectedHarmonicMass (sourceOriginalProbeChosenGroupCount434 m nu.2) V a *
      b579SelectedHarmonicMass (sourceOriginalProbeChosenGroupCount434 m nu.1) V b *
      ((∏g,∏i,a g i : ℕ):ℝ) * ((∏g,∏i,b g i : ℕ):ℝ) *
      ‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux a b‖

/-- Exact density identity for the two actual observed laws. All divisor
and distinctness restrictions still remain in both finite carriers. -/
theorem b598_observed_coupled_harmonic_density434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀g,0 < V g) (hP : ∀g p,p∈P g → 0 < p)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (w wp : ℕ) :
    b598ObservedCoupledHarmonicMass434 m nu Q hA hB xi P V aux w wp =
      (∑ a∈bigMarkLists P (sourceOriginalProbeChosenGroupCount434 m nu.2) w,
        ‖b598OriginalSourceColumn434 m nu Q hB xi P V aux a‖) *
      (∑ b∈bigMarkLists P (sourceOriginalProbeChosenGroupCount434 m nu.1) wp,
        ‖b598OriginalTargetColumn434 m nu Q hA xi P V aux b‖) /
      ((∏g,(V g)^(sourceOriginalProbeChosenGroupCount434 m nu.2 g)) *
       (∏g,(V g)^(sourceOriginalProbeChosenGroupCount434 m nu.1 g))) := by
  let cB := sourceOriginalProbeChosenGroupCount434 m nu.2
  let cA := sourceOriginalProbeChosenGroupCount434 m nu.1
  let VB := ∏g,(V g)^(cB g)
  let VA := ∏g,(V g)^(cA g)
  let fB := b598OriginalSourceColumn434 m nu Q hB xi P V aux
  let fA := b598OriginalTargetColumn434 m nu Q hA xi P V aux
  have hpos {c : G → ℕ} {n : ℕ} {a : ∀g,Fin (c g) → ℕ}
      (ha : a∈bigMarkLists P c n) : ∀g i,0 < a g i := by
    intro g i
    exact hP g (a g i) ((b598_mem_raw_selected_group_lists434 P c a).mp
      (b598_actual_selected_lists_subset_raw434 P c n ha) g i)
  have hterm (a : ∀g,Fin (cB g) → ℕ) (ha : a∈bigMarkLists P cB w)
      (b : ∀g,Fin (cA g) → ℕ) (hb : b∈bigMarkLists P cA wp) :
      b579SelectedHarmonicMass cB V a * b579SelectedHarmonicMass cA V b *
        ((∏g,∏i,a g i : ℕ):ℝ) * ((∏g,∏i,b g i : ℕ):ℝ) *
        ‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux a b‖ =
      (‖fB a‖ * ‖fA b‖) / (VB*VA) := by
    have hdB := b579_selected_harmonic_density cB V a hV (hpos ha)
    have hdA := b579_selected_harmonic_density cA V b hV (hpos hb)
    rw [b598_selected_nat_cast_product434,b598_selected_nat_cast_product434,
      b598_grouped_canonical_norm434]
    calc
      _ = (b579SelectedHarmonicMass cB V a * b579SelectedPrimeProduct cB a) *
          (b579SelectedHarmonicMass cA V b * b579SelectedPrimeProduct cA b) *
          (‖fB a‖ * ‖fA b‖) := by dsimp [fB,fA]; ring
      _ = (VB⁻¹*VA⁻¹)*(‖fB a‖*‖fA b‖) := by rw [hdB,hdA]
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  change (∑a∈bigMarkLists P cB w,∑b∈bigMarkLists P cA wp,_) = _
  calc
    _ = ∑a∈bigMarkLists P cB w,∑b∈bigMarkLists P cA wp,
        (‖fB a‖*‖fA b‖)/(VB*VA) := by
      exact Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hterm a ha b hb))
    _ = _ := by
      simp_rw [← Finset.sum_div]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

/-- On the clean physical sector, the literal full free-list Knu has
an unsquared observed L1 envelope. The same constant is uniform in all
groups, original slot locations, counts and physical endpoint sizes. -/
theorem b598_actual_clean_coupled_l1_uniform434
    (vmin : ℝ) (m : ℕ) (hv : 0 < vmin) :
    ∃ C : ℝ,1 ≤ C ∧
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (J : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
        (_hnu : Disjoint nu.1 nu.2)
        (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
        (_hP : ∀g p,p∈P g → 0 < p) (_hV : ∀g,vmin ≤ V g)
        (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
        (D w wp : ℕ) (_hPrime : ∀z,(aux z).Prime) (_hAuxD : ∀z,aux z∣D)
        (_hclean : D.Coprime w) (_hclean' : D.Coprime wp),
      ‖sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) w wp‖ ≤
        C^(2*Fintype.card G) *
          b598ObservedCoupledHarmonicMass434 m nu Q hA hB xi P V aux w wp := by
  obtain ⟨C,hC,hbound⟩ := b599_original_observed_marked_l1_uniform vmin (m+1) hv
  refine ⟨C,hC,?_⟩
  intro G _ _ J hmJ nu hnu Q hA hB xi P V hP hV aux D w wp hPrime hAuxD hclean hclean'
  let t := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
  let cB := sourceOriginalProbeChosenGroupCount434 m nu.2
  let cA := sourceOriginalProbeChosenGroupCount434 m nu.1
  let rB := fun g => 1+cA g
  let rA := fun g => 1+cB g
  have htB (g : G) : t g=cB g+rB g := by
    dsimp only [t]
    rw [b598_original_free_mark_count434 J 1 m hmJ nu hnu]
    dsimp [cA,cB,rB]
    omega
  have htA (g : G) : t g=cA g+rA g := by
    dsimp only [t]
    rw [b598_original_free_mark_count434 J 1 m hmJ nu hnu]
    dsimp [cA,cB,rA]
    omega
  have hrB (g : G) : 1 ≤ rB g ∧ rB g ≤ m+1 := by
    have hh := source_original_probe_chosen_group_count_le434 m nu.1 g
    dsimp [rB,cA]
    omega
  have hrA (g : G) : 1 ≤ rA g ∧ rA g ≤ m+1 := by
    have hh := source_original_probe_chosen_group_count_le434 m nu.2 g
    dsimp [rA,cB]
    omega
  have hs := hbound P t cB rB V w
    (b598OriginalObservedBSlot434 J 1 m hmJ nu)
    (b598_original_observed_B_slot_injective434 J 1 m hmJ nu) htB
    (b598OriginalSourceColumn434 m nu Q hB xi P V aux) hrB hV
  have ht := hbound P t cA rA V wp
    (b598OriginalObservedASlot434 J 1 m hmJ nu)
    (b598_original_observed_A_slot_injective434 J 1 m hmJ nu) htA
    (b598OriginalTargetColumn434 m nu Q hA xi P V aux) hrA hV
  rw [b598_actual_clean_coupled_decoration_norm434 J 1 m hmJ nu Q hA hB xi P V aux
    D w wp hPrime hAuxD hclean hclean']
  have hVp (g : G) : 0 < V g := hv.trans_le (hV g)
  have hsn : 0 ≤ C^(Fintype.card G) *
      (∑a∈bigMarkLists P cB w,‖b598OriginalSourceColumn434 m nu Q hB xi P V aux a‖) /
      (∏g,(V g)^(cB g)) := le_trans (norm_nonneg _) hs
  calc
    _ ≤ (C^(Fintype.card G) *
        (∑a∈bigMarkLists P cB w,‖b598OriginalSourceColumn434 m nu Q hB xi P V aux a‖) /
        (∏g,(V g)^(cB g))) *
        (C^(Fintype.card G) *
        (∑b∈bigMarkLists P cA wp,‖b598OriginalTargetColumn434 m nu Q hA xi P V aux b‖) /
        (∏g,(V g)^(cA g))) := mul_le_mul hs ht (norm_nonneg _) hsn
    _ = _ := by
      rw [b598_observed_coupled_harmonic_density434 m nu Q hA hB xi P V hVp hP aux w wp]
      rw [show 2*Fintype.card G=Fintype.card G+Fintype.card G by omega,pow_add]
      dsimp only [cA,cB]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## GroupedCanonicalHarmonicL1 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- Original independent selected laws in the exact grouped coordinates
seen by the physical source B and target A endpoints. -/
def b598GroupedCanonicalHarmonicMass434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) : ℝ :=
  ∑ a∈b598RawSelectedGroupLists434 P (sourceOriginalProbeChosenGroupCount434 m nu.2),
    b579SelectedHarmonicMass (sourceOriginalProbeChosenGroupCount434 m nu.2) V a *
    ∑ b∈b598RawSelectedGroupLists434 P (sourceOriginalProbeChosenGroupCount434 m nu.1),
      b579SelectedHarmonicMass (sourceOriginalProbeChosenGroupCount434 m nu.1) V b *
      ‖b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux a b‖

/-- Reindexing is exact, including both actual active-cell masses,
original DA/DB, all repeated independent draws and the sign before norm. -/
theorem b598_grouped_canonical_mass_eq_original434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    b598GroupedCanonicalHarmonicMass434 m nu Q hA hB xi P V aux =
      b584OriginalProbeHarmonicComparisonMass m nu P V Q hA hB xi aux := by
  let K := fun (b : nu.1 → ℕ) (a : nu.2 → ℕ) =>
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V nu hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V nu hB xi) hA hB
      (sourceOriginalProbeCellA434 m P V nu hA)
      (sourceOriginalProbeCellB434 m P V nu hB)
      (sourceOriginalProbeDA434 m nu aux) (∏z,b z)
      (sourceOriginalProbeDB434 m nu aux) (∏z,a z) (nu.1.card+nu.2.card)
  let cA := sourceOriginalProbeChosenGroupCount434 m nu.1
  let cB := sourceOriginalProbeChosenGroupCount434 m nu.2
  have hK (a : ∀g,Fin (cB g) → ℕ) (b : ∀g,Fin (cA g) → ℕ) :
      b598GroupedCanonicalKnu434 m nu Q hA hB xi P V aux a b =
      K (b598GroupedProbeTuple434 m nu.1 b) (b598GroupedProbeTuple434 m nu.2 a) := by
    dsimp only [K,b598GroupedCanonicalKnu434]
    rw [b598_grouped_probe_product434,b598_grouped_probe_product434]
  let muA := fun b : nu.1 → ℕ =>
    sourceSharedLaw434 (fun z : nu.1 => sourcePrimeSharedAtom434 (V z.val.1)) b
  let muB := fun a : nu.2 → ℕ =>
    sourceSharedLaw434 (fun z : nu.2 => sourcePrimeSharedAtom434 (V z.val.1)) a
  change (∑a∈b598RawSelectedGroupLists434 P cB,
      b579SelectedHarmonicMass cB V a *
      ∑b∈b598RawSelectedGroupLists434 P cA,
        b579SelectedHarmonicMass cA V b * _) = _
  calc
    _ = ∑a∈b598RawSelectedGroupLists434 P cB,
      b579SelectedHarmonicMass cB V a *
      ∑b∈b598RawSelectedGroupLists434 P cA,
        b579SelectedHarmonicMass cA V b *
          ‖K (b598GroupedProbeTuple434 m nu.1 b) (b598GroupedProbeTuple434 m nu.2 a)‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      exact Finset.sum_congr rfl (fun b hb => by rw [hK])
    _ = ∑a∈b598RawSelectedGroupLists434 P cB,
      b579SelectedHarmonicMass cB V a *
      ∑b∈Fintype.piFinset (fun z : nu.1 => P z.val.1),muA b *
        ‖K b (b598GroupedProbeTuple434 m nu.2 a)‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      exact b598_original_grouped_harmonic_sum434 m nu.1 P V
        (fun b => ‖K b (b598GroupedProbeTuple434 m nu.2 a)‖)
    _ = ∑b∈Fintype.piFinset (fun z : nu.1 => P z.val.1),muA b *
      ∑a∈b598RawSelectedGroupLists434 P cB,b579SelectedHarmonicMass cB V a *
        ‖K b (b598GroupedProbeTuple434 m nu.2 a)‖ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by
      change _ = ∑b∈Fintype.piFinset (fun z : nu.1 => P z.val.1),muA b *
        ∑a∈Fintype.piFinset (fun z : nu.2 => P z.val.1),muB a * ‖K b a‖
      apply Finset.sum_congr rfl
      intro b hb
      congr 1
      exact b598_original_grouped_harmonic_sum434 m nu.2 P V (fun a => ‖K b a‖)

/-- The literal grouped physical Knu obeys the actual two-column L1
budget Q^4. No inverse xi, inverse cell mass or global kernel cap occurs. -/
theorem b598_grouped_canonical_harmonic_l1_434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀g,0 < V g) (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    b598GroupedCanonicalHarmonicMass434 m nu Q hA hB xi P V aux ≤ (Q:ℝ)^4 := by
  rw [b598_grouped_canonical_mass_eq_original434]
  exact b584_original_probe_two_block_l1 m nu P V hV Q hA hB xi hhA hhB hxi aux

-- Nonnegativity uses the literal reciprocal-prime product, without
-- normalizing any physical restriction of its carrier.
omit [DecidableEq G] in
theorem b598_selected_harmonic_nonneg434
    (c : G → ℕ) (V : G → ℝ) (hV : ∀g,0 ≤ V g)
    (a : ∀g,Fin (c g) → ℕ) :
    0 ≤ b579SelectedHarmonicMass c V a := by
  unfold b579SelectedHarmonicMass
  exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ =>
    one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (hV g))))
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualMarkedGroupReindex -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000
variable {I G : Type}

/-- The exact dependent tuple equivalence for a supplied group equivalence.
The inverse is literal pullback. The forward map uses only the required
dependent count transport; no mark or within-group position is changed. -/
def b605GroupMarkedEquiv434 (e : I ≃ G) (t : G → ℕ) :
    (∀ i,Fin (t (e i)) → ℕ) ≃ (∀ g,Fin (t g) → ℕ) :=
  Equiv.piCongrLeft (fun g => Fin (t g) → ℕ) e

@[simp] theorem b605_group_marked_equiv_symm_apply434
    (e : I ≃ G) (t : G → ℕ) (b : ∀ g,Fin (t g) → ℕ) (i : I) :
    (b605GroupMarkedEquiv434 e t).symm b i = b (e i) := rfl

@[simp] theorem b605_group_marked_equiv_apply434
    (e : I ≃ G) (t : G → ℕ) (a : ∀ i,Fin (t (e i)) → ℕ) (i : I) :
    b605GroupMarkedEquiv434 e t a (e i) = a i := by
  exact congrFun ((b605GroupMarkedEquiv434 e t).symm_apply_apply a) i

variable [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G]

/-- Exact membership of the FULL original ordered marked-list carrier.
All divisor tests and all within-group distinctness conditions survive. -/
theorem b605_group_marked_pullback_mem434
    (e : I ≃ G) (P : G → Finset ℕ) (t : G → ℕ) (n : ℕ)
    (b : ∀ g,Fin (t g) → ℕ) :
    (fun i => b (e i)) ∈ bigMarkLists (fun i => P (e i)) (fun i => t (e i)) n ↔
      b ∈ bigMarkLists P t n := by
  simp only [bigMarkLists,Fintype.mem_piFinset]
  constructor
  · intro hb g
    obtain ⟨i,rfl⟩ := e.surjective g
    exact hb i
  · intro hb i
    exact hb (e i)

/-- Reindexing the full original marked carrier is an equality for any
coupled complex test, including a full auxiliary ban or Knu. -/
theorem b605_group_marked_sum_reindex434
    (e : I ≃ G) (P : G → Finset ℕ) (t : G → ℕ) (n : ℕ)
    (f : (∀ g,Fin (t g) → ℕ) → ℂ) :
    (∑ a ∈ bigMarkLists (fun i => P (e i)) (fun i => t (e i)) n,
      f (b605GroupMarkedEquiv434 e t a)) =
      ∑ b ∈ bigMarkLists P t n,f b := by
  let E := b605GroupMarkedEquiv434 e t
  have hmem (b : ∀ g,Fin (t g) → ℕ) :
      E.symm b ∈ bigMarkLists (fun i => P (e i)) (fun i => t (e i)) n ↔
        b ∈ bigMarkLists P t n :=
    b605_group_marked_pullback_mem434 e P t n b
  apply Finset.sum_bij (fun a _ => E a)
  · intro a ha
    apply (hmem (E a)).mp
    simpa only [Equiv.symm_apply_apply] using ha
  · intro a ha b hb hab
    exact E.injective hab
  · intro b hb
    exact ⟨E.symm b,(hmem b).mpr hb,E.apply_symm_apply b⟩
  · intro a ha
    rfl

/-- The original q damping, every group divisor count and every V power
are preserved exactly by the same supplied group equivalence. -/
theorem b605_group_mark_prefactor_reindex434
    (e : I ≃ G) (P : G → Finset ℕ) (t : G → ℕ)
    (q : ℝ) (V : G → ℝ) (n : ℕ) :
    bigMarkPrefactor (fun i => P (e i)) (fun i => t (e i)) q
      (fun i => V (e i)) n = bigMarkPrefactor P t q V n := by
  unfold bigMarkPrefactor
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

/-- Exact transport of the FULL original marked decoration, before any
norm or marginalization. This is the consumer needed to apply the existing
complete BIG+SMALL family equivalence; that concrete application is B604.
No positivity, normalization or arithmetic premise is introduced. -/
theorem b605_actual_marked_decoration_group_reindex434
    (e : I ≃ G) (P : G → Finset ℕ) (t : G → ℕ)
    (q : ℝ) (V : G → ℝ) (n : ℕ)
    (f : (∀ g,Fin (t g) → ℕ) → ℂ) :
    actualBigMarkDecoration (fun i => P (e i)) (fun i => t (e i)) q
      (fun i => V (e i)) (fun a => f (b605GroupMarkedEquiv434 e t a)) n =
      actualBigMarkDecoration P t q V f n := by
  unfold actualBigMarkDecoration
  rw [b605_group_mark_prefactor_reindex434,b605_group_marked_sum_reindex434]
end Green64Analytic.CorrelationSquare

end

end

