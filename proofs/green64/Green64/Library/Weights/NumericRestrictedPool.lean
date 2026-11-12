module

public import Green64.Library.Correlation.PhysicalRestrictedPool

@[expose] public section

/-!
# Weights / NumericRestrictedPool

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalNumericRestrictedPool -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

def sourceOriginalPhysicalNumericRestrictedPoolG434
    (B : Finset P) (eta V : ℝ) (mu : P → ℝ)
    (pending : Multiset (Atom P modulus)) (seen : Finset ℕ)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (pending.toFinset.filter (fun z => z.2=0)) B,
    if ∀ p ∈ d.2.1,modulus p ∉ seen then
      sourceOriginalGroupPrimeBirthWeight434 modulus
        (pending.toFinset.filter (fun z => z.2=0))
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d) *
      F (sourceOriginalGhostPiecePending434 modulus pending.toFinset d.1.1 d.2.1)
        (seen ∪ d.2.1.image modulus)
    else 0

/-- External seen is only required to avoid the TRUE background
subset B. No condition is imposed on its other numerical labels. -/
theorem source_original_NUMERIC_RESTRICTED_POOL_G_pullback434
    (B : Finset P) (hi : Function.Injective modulus)
    (external : Finset ℕ) (hext : ∀ p ∈ B,modulus p ∉ external)
    (eta V : ℝ) (mu : P → ℝ) (pending : Multiset (Atom P modulus)) (seen : Finset P)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalNumericRestrictedPoolG434 modulus B eta V mu pending
      (external ∪ seen.image modulus) F =
    sourceOriginalPhysicalRestrictedPoolG434 modulus B eta V mu pending seen
      (fun out st => F out (external ∪ st.image modulus)) := by
  unfold sourceOriginalPhysicalNumericRestrictedPoolG434 sourceOriginalPhysicalRestrictedPoolG434
  apply Finset.sum_congr rfl
  intro d hd
  have hb : d.2.1 ⊆ B := Finset.mem_powerset.mp d.2.2
  have hg : (∀ p ∈ d.2.1,modulus p ∉ external ∪ seen.image modulus) ↔
      (∀ p ∈ d.2.1,p ∉ seen) := by
    constructor
    · intro h p hp hs
      exact h p hp (Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem modulus hs)))
    · intro h p hp hs
      rcases Finset.mem_union.mp hs with hs|hs
      · exact hext p (hb hp) hs
      · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hs
        have hh : t=p := hi he
        exact h p hp (hh ▸ ht)
  by_cases h : ∀ p ∈ d.2.1,p ∉ seen
  · rw [if_pos h,if_pos (hg.mpr h)]
    dsimp only
    rw [Finset.image_union,Finset.union_assoc]
  · rw [if_neg h,if_neg (fun hh => h (hg.mp hh))]

theorem source_original_NUMERIC_BACKGROUND_POOL_G_return_matrix434
    (B : Finset P) (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (hs : ∀ p,p ∉ B → s p=.retired)
    (hi : Function.Injective modulus) (external : Finset ℕ)
    (hext : ∀ p ∈ B,modulus p ∉ external)
    (eta V : ℝ) (mu : P → ℝ) (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalNumericRestrictedPoolG434 modulus B eta V mu
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (external ∪ (sourceOriginalPrimeProductSeen434 modulus s ∩ B).image modulus) F =
    sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu
      (fun t => F (sourceOriginalPrimeProductPending434 modulus shift t)
        (external ∪ (sourceOriginalPrimeProductSeen434 modulus t ∩ B).image modulus)) := by
  rw [source_original_NUMERIC_RESTRICTED_POOL_G_pullback434 modulus B hi external hext,
    source_original_BACKGROUND_POOL_G_return_matrix434 modulus B shift s hs]

/-- The actual product return kernel cannot revive a coordinate
outside B once it is retired. This is proved from the signed kernel. -/
theorem source_original_BACKGROUND_RETURN_kernel_support434
    (B : Finset P) (shift : ℤ) (s t : SourceOriginalPrimeReturnProductState434 modulus)
    (hs : ∀ p,p ∉ B → s p=.retired)
    (ht : ¬ ∀ p,p ∉ B → t p=.retired)
    (eta V : ℝ) (mu : P → ℝ) :
    (∏ p,sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)) = 0 := by
  obtain ⟨p,hp⟩ := not_forall.mp ht
  have hb : p ∉ B := by
    by_contra h
    apply hp
    intro hn
    exact False.elim (hn h)
  have ht' : t p ≠ .retired := by
    intro he
    exact hp (fun _ => he)
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  rw [hs p hb]
  unfold sourceOriginalPrimeReturnKernel434
  rw [source_original_GHOST_RETURN_literal_retired434]
  exact if_neg (Ne.symm ht')

theorem source_original_BACKGROUND_RETURN_row_congr434
    (B : Finset P) (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (hs : ∀ p,p ∉ B → s p=.retired)
    (eta V : ℝ) (mu : P → ℝ)
    (F G : SourceOriginalPrimeReturnProductState434 modulus → ℂ)
    (hFG : ∀ t,(∀ p,p ∉ B → t p=.retired) → F t=G t) :
    sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F =
    sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu G := by
  unfold sourceOriginalPrimeProductReturnRow434
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : ∀ p,p ∉ B → t p=.retired
  · rw [hFG t h]
  · rw [source_original_BACKGROUND_RETURN_kernel_support434 modulus B shift s t hs h,
      zero_mul,zero_mul]
end Green64Analytic.CorrelationSquare

end

end

