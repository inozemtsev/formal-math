module

public import Green64.Library.Correlation.PhysicalArray
public import Green64.Library.Correlation.LocalHaarPhysical

@[expose] public section

/-!
# Weights / ParityDensity

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualParityDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

private theorem b653_guard_product (N : ℕ) (A : Finset ℕ)
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

/-- At an integer anchor every marked zero and every unmarked damping
factor is exactly its physical divisibility factor, even when a marked
zero fails. No averaging or CRT error enters this local identity. -/
theorem b653_integer_family_integrand434 {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Type) [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
    (mod : (g : G) → P g → ℕ) [∀ g p, NeZero (mod g p)]
    (M N : ℕ) (q : ℝ)
    (marks : Fin (N+1) → (g : G) → {f : Fin M → P g // Function.Injective f})
    (off : ℕ → ℤ) (n : ℤ) :
    memoryIndBIGPhysicalAnchorIntegrand P mod (sourceVisitEta q N) off
      (b643MarkVisits434 P M N marks) (N+1) (fun g p => (n : ZMod (mod g p))) =
    ∏ gp : Sigma P, ∏ i ∈ Finset.range (N+1),
      if i ∈ b643MarkVisits434 P M N marks gp then
        (if (mod gp.1 gp.2 : ℤ) ∣ n+off i then (1:ℝ) else 0)
      else (if (mod gp.1 gp.2 : ℤ) ∣ n+off i then sourceVisitQ q N i else 1) := by
  unfold memoryIndBIGPhysicalAnchorIntegrand
  apply Finset.prod_congr rfl
  intro gp hgp
  have hA : b643MarkVisits434 P M N marks gp ⊆ Finset.range (N+1) := by
    intro i hi
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr t.isLt
  rw [b653_guard_product (N+1) _ hA]
  apply Finset.prod_congr rfl
  intro i hi
  have hz : (n : ZMod (mod gp.1 gp.2))+(off i : ZMod (mod gp.1 gp.2))=0 ↔
      (mod gp.1 gp.2 : ℤ) ∣ n+off i := by
    rw [← Int.cast_add,ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [hz,sourceVisitEta]
  by_cases ha : i ∈ b643MarkVisits434 P M N marks gp
  · simp only [ha,ite_true]
  · simp only [ha,ite_false]
    split_ifs <;> ring
end Green64FullPhysicalE

namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 12000

/-- The actual all-P Parity source integrand at the ONE physical integer n
is precisely the original marked physical density, with actual r=20,
all groups, all ordered mark visits and the unchanged signed offsets. -/
theorem b653_actual_parity_integer_integrand434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J ell m : ℕ) {Nu : Type} [Fintype Nu]
    (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
    (N : ℕ)
    (ω : B643AllPrimePath434 (SourceNativeMemorySP434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J ell m patterns N) (k : ℤ) (n : ℕ) :
    b643AllPrimeAnchorIntegrand434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns (1/2:ℝ) ω k
      (b653IntegerAnchor434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) (n:ℤ)) =
    b645ActualMarkedPathDensity434 L hS (J+ell) N
      (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val)
      (b643AllPrimeOffset434 (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J ell m patterns ω k) n := by
  unfold b643AllPrimeAnchorIntegrand434 b653IntegerAnchor434
  rw [b653_integer_family_integrand434,b653_integer_family_integrand434]
  unfold b645ActualMarkedPathDensity434
  rw [b645_actual_full_prime_product434 L hL hS]
  simp only [Fintype.prod_sigma]
  congr 1
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro p hp
    apply Finset.prod_congr rfl
    intro i hi
    have ha := b645_actual_small_active_iff434 L hL hS (J+ell) N
      (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val) ⟨i,Finset.mem_range.mp hi⟩ g p
    have hm := b643_mark_visit_mem434 (SourceNativeMemorySP434 20 L hS) (J+ell) N ω.1 ⟨g,p⟩ ⟨i,Finset.mem_range.mp hi⟩
    apply if_congr (hm.trans ha.symm) <;> rfl
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro p hp
    apply Finset.prod_congr rfl
    intro i hi
    have ha := b645_actual_big_active_iff434 L hL hS (J+ell) N
      (fun i g => (ω.1 i g).val) (fun i g => (ω.2.1 i g).val) ⟨i,Finset.mem_range.mp hi⟩ g p
    have hm := b643_mark_visit_mem434 (SourceNativeMemoryBP434 20 L) (J+ell) N ω.2.1 ⟨g,p⟩ ⟨i,Finset.mem_range.mp hi⟩
    apply if_congr (hm.trans ha.symm) <;> rfl
end Green64Analytic.SourceBlockSieve

end

end

