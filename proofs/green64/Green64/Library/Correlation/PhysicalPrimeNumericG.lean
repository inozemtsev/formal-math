module

public import Green64.Library.Correlation.PhysicalPrimeProductG

@[expose] public section

/-!
# Correlation / PhysicalPrimeNumericG

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalPrimeNumericG -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)

/-- Numeric seen membership on an injectively labelled prime pool;
externalSeen may contain all numeric labels outside this pool. -/
theorem source_original_PRIME_PRODUCT_numeric_seen_mem434
    (hi : Function.Injective modulus) (externalSeen : Finset ℕ)
    (hext : ∀ p,modulus p ∉ externalSeen) (p : P) :
    modulus p ∈ externalSeen ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus ↔
      p ∈ sourceOriginalPrimeProductSeen434 modulus s := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact False.elim (hext p h)
    · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp h
      have htEq : t=p := hi he
      simpa only [htEq] using ht
  · intro h
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem modulus h))

theorem source_original_PRIME_PRODUCT_numeric_birth_gate434
    (hi : Function.Injective modulus) (externalSeen : Finset ℕ)
    (hext : ∀ p,modulus p ∉ externalSeen) (born : Finset P) :
    (∀ p ∈ born,modulus p ∉ externalSeen ∪
      (sourceOriginalPrimeProductSeen434 modulus s).image modulus) ↔
    (∀ p ∈ born,p ∉ sourceOriginalPrimeProductSeen434 modulus s) := by
  constructor
  · intro h p hp hs
    exact h p hp ((source_original_PRIME_PRODUCT_numeric_seen_mem434
      modulus s hi externalSeen hext p).mpr hs)
  · intro h p hp hs
    exact h p hp ((source_original_PRIME_PRODUCT_numeric_seen_mem434
      modulus s hi externalSeen hext p).mp hs)

/-- The literal group subset G row with a full numeric seen state,
including seen labels outside the represented prime pool. -/
def sourceOriginalPhysicalProductNumericG434
    (eta V : ℝ) (mu : P → ℝ) (externalSeen : Finset ℕ)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      ((sourceOriginalPrimeProductPending434 modulus shift s).toFinset.filter (fun z => z.2=0))
      Finset.univ,
    if ∀ p ∈ d.2.1,modulus p ∉ externalSeen ∪
        (sourceOriginalPrimeProductSeen434 modulus s).image modulus then
      sourceOriginalGroupPrimeBirthWeight434 modulus
        ((sourceOriginalPrimeProductPending434 modulus shift s).toFinset.filter (fun z => z.2=0))
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d) *
      F (sourceOriginalGhostPiecePending434 modulus
          (sourceOriginalPrimeProductPending434 modulus shift s).toFinset d.1.1 d.2.1)
        ((externalSeen ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus) ∪
          d.2.1.image modulus)
    else 0

/-- Exact passage from label seen to the original numeric seen gate
and observation. The joint F still sees the external seen component. -/
theorem source_original_PRIME_PRODUCT_numeric_G_pullback434
    (hi : Function.Injective modulus) (externalSeen : Finset ℕ)
    (hext : ∀ p,modulus p ∉ externalSeen)
    (eta V : ℝ) (mu : P → ℝ)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalProductNumericG434 modulus shift s eta V mu externalSeen F =
    sourceOriginalPhysicalProductGroupG434 modulus shift s eta V mu
      (fun pending seen => F pending (externalSeen ∪ seen.image modulus)) := by
  unfold sourceOriginalPhysicalProductNumericG434 sourceOriginalPhysicalProductGroupG434
  apply Finset.sum_congr rfl
  intro d hd
  have hg := source_original_PRIME_PRODUCT_numeric_birth_gate434
    modulus s hi externalSeen hext d.2.1
  by_cases h : ∀ p ∈ d.2.1,p ∉ sourceOriginalPrimeProductSeen434 modulus s
  · rw [if_pos h,if_pos (hg.mpr h)]
    dsimp only
    rw [Finset.image_union,Finset.union_assoc]
  · rw [if_neg h,if_neg (fun hh => h (hg.mp hh))]

/-- The exact physical prime tensor row also holds with the original
numeric seen gate and arbitrary outside-pool seen data. -/
theorem source_original_PRIME_PRODUCT_numeric_G_tensor434
    (hi : Function.Injective modulus) (externalSeen : Finset ℕ)
    (hext : ∀ p,modulus p ∉ externalSeen)
    (eta V : ℝ) (mu : P → ℝ)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalProductNumericG434 modulus shift s eta V mu externalSeen F =
    sourceOriginalPhysicalProductLocalG434 modulus shift s eta V mu
      (fun pending seen => F pending (externalSeen ∪ seen.image modulus)) := by
  rw [source_original_PRIME_PRODUCT_numeric_G_pullback434 modulus shift s hi externalSeen hext,
    source_original_PRIME_PRODUCT_physical_G_tensor434]
end Green64Analytic.CorrelationSquare

end

end

