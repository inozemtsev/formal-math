module

public import Green64.Library.Weights.Part058
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-!
# Correlation / MemoryOmissionProduct

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOmissionProduct -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000

private theorem prime_dvd_slot_product434
    {I : Type} [DecidableEq I] (v : I → ℕ) (p : ℕ) (hp : p.Prime)
    (S : Finset I) (h : p ∣ ∏ i ∈ S,v i) :
    ∃ i ∈ S,p ∣ v i := by
  induction S using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one h
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with h | h
    · exact ⟨a,Finset.mem_insert_self _ _,h⟩
    · obtain ⟨i,hi,hpi⟩ := ih h
      exact ⟨i,Finset.mem_insert_of_mem hi,hpi⟩

/-- Exact unique-factorization input to the original omission argument. -/
theorem source_original_memory_prime_subset_product_injective434
    {I : Type} [DecidableEq I] (v : I → ℕ)
    (hp : ∀ i,(v i).Prime) (hinj : Function.Injective v) :
    Function.Injective (fun S : Finset I => ∏ i ∈ S,v i) := by
  intro S T he
  have hsub (A B : Finset I) (hAB : (∏ i ∈ A,v i) = ∏ i ∈ B,v i) : A ⊆ B := by
    intro i hi
    have hd : v i ∣ ∏ j ∈ B,v j := hAB ▸ Finset.dvd_prod_of_mem v hi
    obtain ⟨j,hj,hij⟩ := prime_dvd_slot_product434 v (v i) (hp i) B hd
    have heq : i=j := hinj ((Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp hij)
    simpa only [heq] using hj
  exact Finset.Subset.antisymm (hsub S T he) (hsub T S he.symm)

/-- Literal SMALL-state labels are distinct inside each group. Actual
source separation makes them distinct across groups as well. Hence two
different omitted slot sets have different integer products. -/
theorem source_original_memory_actual_SMALL_omission_injective434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 data)
    [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
    (M : ℕ)
    (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
      (fun _ p => p.val) M) :
    Function.Injective (fun S : Finset (ι × Fin M) =>
      ∏ gi ∈ S,
        (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts gi.1} => p.val)
          M (xs gi.1) gi.2).val) := by
  let v : ι × Fin M → ℕ := fun gi =>
    (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts gi.1} => p.val)
      M (xs gi.1) gi.2).val
  apply source_original_memory_prime_subset_product_injective434 v
  · intro gi
    exact data.hTsPrime gi.1 _ (Green64SmallHaar.marks
      (fun p : {p : ℕ // p ∈ data.Ts gi.1} => p.val) M (xs gi.1) gi.2).property
  · rintro ⟨g,i⟩ ⟨h,j⟩ he
    have hg : g=h := sep.hTT g h _ (Green64SmallHaar.marks
      (fun p : {p : ℕ // p ∈ data.Ts g} => p.val) M (xs g) i).property
      (by change v (g,i) ∈ data.Ts h
          rw [he]
          exact (Green64SmallHaar.marks
        (fun p : {p : ℕ // p ∈ data.Ts h} => p.val) M (xs h) j).property)
    subst h
    have hij : i=j := Green64SmallHaar.marks_injective
      (fun p : {p : ℕ // p ∈ data.Ts g} => p.val) M (xs g) (Subtype.ext he)
    exact Prod.ext rfl hij

/-- Multiply the original promotion congruence by the omitted product.
The coefficient becomes independent of the omission choice. -/
theorem source_original_memory_promotion_omission_equation434
    (p F U DS DB : ℕ) (o k : ℤ) (r : ZMod p)
    (hprod : U*DS=F)
    (hz : r + (o*k*(DS*DB:ℕ):ℤ) = 0) :
    r*(U:ZMod p)+(o*k*(DB*F:ℕ):ℤ)=0 := by
  have hh := congrArg (fun z : ZMod p => z*(U:ZMod p)) hz
  have hprod' : (U:ZMod p)*(DS:ZMod p)=(F:ZMod p) := by
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n:ZMod p)) hprod
  push_cast at hh ⊢
  calc
    _ = (r+(o:ZMod p)*(k:ZMod p)*(DS:ZMod p)*(DB:ZMod p))*(U:ZMod p) := by
      rw [← hprod']
      ring
    _ = 0 := by simpa only [mul_assoc,zero_mul] using hh

/-- One actual old particle admits at most one omitted integer product
below its prime. The constant term must be nonzero; this is the original
invertibility condition and cannot be dropped. -/
theorem source_original_memory_one_particle_omission_unique434
    (p : ℕ) (hp : p.Prime) (r A : ZMod p) (hA : A ≠ 0)
    (U V : ℕ) (hU : U<p) (hV : V<p)
    (hu : r*(U:ZMod p)+A=0) (hv : r*(V:ZMod p)+A=0) : U=V := by
  letI : Fact p.Prime := ⟨hp⟩
  have hr : r ≠ 0 := by
    intro he
    apply hA
    simpa [he] using hu
  have he : (U:ZMod p)=(V:ZMod p) := mul_left_cancel₀ hr (add_right_cancel (hu.trans hv.symm))
  exact (Nat.mod_eq_of_lt hU).symm.trans
    (((ZMod.natCast_eq_natCast_iff' U V p).mp he).trans (Nat.mod_eq_of_lt hV))

/-- The true omission family has binomial choices per SMALL group. -/
theorem source_original_memory_SMALL_omission_family_card434
    {ι : Type} [Fintype ι] (M ell : ℕ) :
    Fintype.card (ι → {S : Finset (Fin M) // S.card=ell}) =
      (M.choose ell)^(Fintype.card ι) := by
  simp [Fintype.card_finset_len]

/-- Integer-product injectivity for the literal family of omitted SMALL
slot sets, including all groups. No probability or norm is used. -/
theorem source_original_memory_actual_SMALL_group_omission_injective434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 data)
    [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
    (M : ℕ)
    (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
      (fun _ p => p.val) M) :
    Function.Injective (fun O : ι → Finset (Fin M) =>
      ∏ g : ι,∏ i ∈ O g,
        (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
          M (xs g) i).val) := by
  classical
  let flat : (ι → Finset (Fin M)) → Finset (ι × Fin M) :=
    fun O => Finset.univ.filter (fun gi => gi.2 ∈ O gi.1)
  let v : ι × Fin M → ℕ := fun gi =>
    (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts gi.1} => p.val)
      M (xs gi.1) gi.2).val
  have hprod (O : ι → Finset (Fin M)) :
      (∏ gi ∈ flat O,v gi) = ∏ g : ι,∏ i ∈ O g,v (g,i) := by
    simp [flat,Finset.prod_filter,Fintype.prod_prod_type]
  intro A B hAB
  have hf : flat A=flat B :=
    source_original_memory_actual_SMALL_omission_injective434 data sep M xs
      (by
        change (∏ gi ∈ flat A,v gi) = ∏ gi ∈ flat B,v gi
        rw [hprod,hprod]
        exact hAB)
  funext g
  ext i
  have hh := congrArg (fun S : Finset (ι × Fin M) => (g,i) ∈ S) hf
  simpa only [flat,Finset.mem_filter,Finset.mem_univ,true_and] using (iff_of_eq hh)

/-- At most one genuine SMALL omission tuple can hit a fixed OLD
particle's promotion congruence. The prime-floor and invertibility
conditions are explicit; weighted DIRTY row/column estimates are separate. -/
theorem source_original_memory_actual_SMALL_one_promotion_choice434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 data)
    [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
    (M ell : ℕ)
    (xs : Green64SmallHaar.GroupState (fun g => {p : ℕ // p ∈ data.Ts g})
      (fun _ p => p.val) M)
    (p : ℕ) (hp : p.Prime) (r A : ZMod p) (hA : A ≠ 0)
    (hFloor : ∀ O : ι → {S : Finset (Fin M) // S.card=ell},
      (∏ g : ι,∏ i ∈ (O g).val,
        (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
          M (xs g) i).val) < p) :
    ((Finset.univ : Finset (ι → {S : Finset (Fin M) // S.card=ell})).filter
      (fun O => r*((∏ g : ι,∏ i ∈ (O g).val,
        (Green64SmallHaar.marks (fun p : {p : ℕ // p ∈ data.Ts g} => p.val)
          M (xs g) i).val : ℕ):ZMod p)+A=0)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro O hO T hT
  have he := source_original_memory_one_particle_omission_unique434 p hp r A hA
    _ _ (hFloor O) (hFloor T) (Finset.mem_filter.mp hO).2 (Finset.mem_filter.mp hT).2
  have hf := source_original_memory_actual_SMALL_group_omission_injective434
    data sep M xs he
  funext g
  exact Subtype.ext (congrFun hf g)

end Green64Analytic.CorrelationSquare

end

end

