module

public import Green64.Library.Analysis.Estimates.AllPrimeHaar
public import Green64.Library.Analysis.Estimates.PrimeCoordinates
public import Green64.Library.Weights.WeightedActualPaths

@[expose] public section

/-!
# Correlation / LocalHaarPhysical

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LocalHaarPhysical -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000

private theorem sum_residue_val (p : ℕ) [NeZero p] (f : ℕ → ℝ) :
    (∑ r : ZMod p, f r.val) = ∑ r ∈ Finset.range p, f r := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => exact Fin.sum_univ_eq_sum_range f (p+1)

private theorem marked_guard_product (N : ℕ) (A : Finset ℕ)
    (hA : A ⊆ Finset.range N) (P : ℕ → Prop) [DecidablePred P] (d : ℕ → ℝ) :
    (if ∀ i ∈ A, P i then
      ∏ i ∈ Finset.range N, if i ∈ A then (1:ℝ) else d i
    else 0) =
    ∏ i ∈ Finset.range N, if i ∈ A then (if P i then (1:ℝ) else 0) else d i := by
  by_cases hall : ∀ i ∈ A, P i
  · rw [ite_eq_left hall]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases ha : i ∈ A
    · simp only [ha,ite_true,hall i ha]
    · simp only [ha,ite_false]
  · rw [ite_eq_right hall]
    push Not at hall
    obtain ⟨i,hi,hn⟩ := hall
    symm
    exact Finset.prod_eq_zero (hA hi) (by simp only [hi,ite_true,hn,ite_false])

/-- Local source Haar factor in physical residue coordinates. The one
anchor is reflected once; marked collisions and all unmarked visits
remain inside the same product. -/
private theorem local_haar_physical (p : ℕ) [NeZero p] (N : ℕ)
    (A : Finset ℕ) (hA : A ⊆ Finset.range N) (q : ℕ → ℝ)
    (offset : ℕ → ℤ) (activeAt : ℕ → Finset ℕ)
    (hact : ∀ i ∈ Finset.range N, p ∈ activeAt i ↔ i ∈ A) :
    memoryPrimeHaar p (fun i => 1-q i) (fun i => (offset i : ZMod p)) A N =
      (∑ r ∈ Finset.range p,
        b641PathPrimeWeight434 (Finset.range N) activeAt q offset p r)/(p:ℝ) := by
  unfold memoryPrimeHaar
  congr 1
  let F (c : ZMod p) : ℝ :=
    if ∀ i ∈ A, (offset i:ZMod p)=c then
      ∏ i ∈ Finset.range N, if i ∈ A then 1 else
        1-(1-q i)*(if (offset i:ZMod p)=c then 1 else 0)
    else 0
  change (∑ c : ZMod p, F c)=_
  calc
    _ = ∑ c : ZMod p, F (-c) := (Equiv.sum_comp (Equiv.neg (ZMod p)) F).symm
    _ = ∑ c : ZMod p,
        b641PathPrimeWeight434 (Finset.range N) activeAt q offset p c.val := by
      apply Finset.sum_congr rfl
      intro c hc
      dsimp only [F]
      rw [marked_guard_product N A hA]
      unfold b641PathPrimeWeight434
      apply Finset.prod_congr rfl
      intro i hi
      have he : (offset i:ZMod p) = -c ↔ (c.val:ZMod p)+(offset i:ZMod p)=0 := by
        rw [ZMod.natCast_zmod_val,add_comm,add_eq_zero_iff_eq_neg]
      simp only [hact i hi]
      by_cases ha : i ∈ A
      · simp only [ha,ite_true,he]
      · simp only [ha,ite_false,he]
        split_ifs <;> ring
    _ = _ := sum_residue_val p _

private theorem mark_visits_subset {G : Type} [Fintype G]
    (P : G → Type) [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
    (M N : ℕ) (marks : Fin (N+1) → (g : G) → {f : Fin M → P g // Function.Injective f})
    (p : Sigma P) : b643MarkVisits434 P M N marks p ⊆ Finset.range (N+1) := by
  intro i hi
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr t.isLt

private theorem mem_mark_visits {G : Type} [Fintype G]
    (P : G → Type) [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
    (M N : ℕ) (marks : Fin (N+1) → (g : G) → {f : Fin M → P g // Function.Injective f})
    (p : Sigma P) (i : Fin (N+1)) :
    i.val ∈ b643MarkVisits434 P M N marks p ↔ ∃ j, (marks i p.1).val j=p.2 := by
  constructor
  · intro hi
    obtain ⟨t,ht,hv⟩ := Finset.mem_image.mp hi
    have he : t=i := Fin.ext hv
    subst t
    exact (Finset.mem_filter.mp ht).2
  · intro hi
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩

/-- The complete SMALL/BIG anchor model equals the physical residue model
over every original numerical prime, at the SAME signed path offsets.
No CRT estimate or independence assumption appears in this equality. -/
theorem b645_actual_all_prime_model434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J ell m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (N : ℕ)
    (ω : B643AllPrimePath434 (SourceNativeMemorySP434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J ell m patterns N) (k : ℤ) :
    b643AllPrimeHaarModel434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J ell m patterns (1/2:ℝ) ω k =
    b645ActualMarkedPathModel434 L hS (J+ell) N
      (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val)
      (b643AllPrimeOffset434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns ω k) := by
  rw [b643_all_prime_haar_product434]
  unfold b645ActualMarkedPathModel434
  rw [b645_actual_full_prime_product434 L hL hS]
  simp only [PhysicalSourcePrime,Fintype.prod_sigma]
  congr 1
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro p hp
    apply local_haar_physical p.val (N+1) _ (mark_visits_subset _ _ _ _ _)
    intro i hi
    rw [b645_actual_small_active_iff434 L hL hS (J+ell) N
      (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val) ⟨i,Finset.mem_range.mp hi⟩ g p]
    exact (mem_mark_visits _ _ _ _ ⟨g,p⟩ ⟨i,Finset.mem_range.mp hi⟩).symm
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro p hp
    apply local_haar_physical p.val (N+1) _ (mark_visits_subset _ _ _ _ _)
    intro i hi
    rw [b645_actual_big_active_iff434 L hL hS (J+ell) N
      (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val) ⟨i,Finset.mem_range.mp hi⟩ g p]
    exact (mem_mark_visits _ _ _ _ ⟨g,p⟩ ⟨i,Finset.mem_range.mp hi⟩).symm
end Green64Analytic.SourceBlockSieve

end

end

