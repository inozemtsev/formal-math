module

public import Green64.Library.Correlation.PhysicalPrimeProduct

@[expose] public section

/-!
# Correlation / PhysicalPrimeProductG

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalPrimeProductG -/

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

private theorem univFiber (p : P) :
    (Finset.univ.filter (fun t : P => t=p))={p} := by ext t;simp

def sourceOriginalProductPrimeLocalChoiceEquiv434 (p : P) :
    SourceOriginalRestrictedPrimeBirthChoice434 modulus
      ((Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))).filter (fun z => z.1=p)) (Finset.univ.filter (fun t => t=p)) ≃
    SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift (s p)) {p} where
  toFun d := (⟨d.1.1,by
    rw [←source_original_PRIME_PRODUCT_zero_fiber434 modulus shift s p]
    exact d.1.2⟩,⟨d.2.1,by rw [←univFiber p];exact d.2.2⟩)
  invFun d := (⟨d.1.1,by
    rw [source_original_PRIME_PRODUCT_zero_fiber434 modulus shift s p]
    exact d.1.2⟩,⟨d.2.1,by rw [univFiber p];exact d.2.2⟩)
  left_inv d := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv d := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

abbrev SourceOriginalProductPrimeLocalChoice434 :=
  (p : P) → SourceOriginalRestrictedPrimeBirthChoice434 modulus
    (sourceOriginalOnePrimeZero434 modulus p shift (s p)) {p}

def sourceOriginalProductPrimeChoiceEquiv434 :
    SourceOriginalRestrictedPrimeBirthChoice434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ ≃
      SourceOriginalProductPrimeLocalChoice434 modulus shift s :=
  (sourceOriginalPrimeFiberEquiv434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ).trans
    (Equiv.piCongrRight (sourceOriginalProductPrimeLocalChoiceEquiv434 modulus shift s))

theorem source_original_PRIME_PRODUCT_G_weight434
    (alpha chi gamma : ℂ) (mu : P → ℂ)
    (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ) :
    sourceOriginalGroupPrimeBirthWeight434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) alpha chi gamma mu
      (sourceOriginalRestrictedPrimeBirthLift434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ d) =
    ∏ p,sourceOriginalGroupPrimeBirthWeight434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift (s p)) alpha chi gamma mu
      (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _
        (sourceOriginalProductPrimeChoiceEquiv434 modulus shift s d p)) := by
  rw [source_original_GROUP_G_prime_fiber_weight434]
  apply Finset.prod_congr rfl
  intro p hp
  unfold sourceOriginalGroupPrimeBirthWeight434 sourceOriginalRestrictedPrimeBirthLift434
  change _^(d.1.1.filter (fun z => z.1=p)).card *
      _^(((Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))).filter (fun z => z.1=p)).card-(d.1.1.filter (fun z => z.1=p)).card) *
      _^(d.2.1.filter (fun t => t=p)).card *
      (∏ t ∈ d.2.1.filter (fun t => t=p),_) = _
  rw [source_original_PRIME_PRODUCT_zero_fiber434]
  rfl

theorem source_original_PRIME_PRODUCT_G_output434
    (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ) :
    sourceOriginalGhostPiecePending434 modulus
      (sourceOriginalPrimeProductPending434 modulus shift s).toFinset d.1.1 d.2.1 =
    ∑ p,sourceOriginalGhostPiecePending434 modulus
      (sourceOriginalOnePrimePending434 modulus p shift (s p)).toFinset
      (sourceOriginalProductPrimeChoiceEquiv434 modulus shift s d p).1.1
      (sourceOriginalProductPrimeChoiceEquiv434 modulus shift s d p).2.1 := by
  rw [source_original_GHOST_PIECE_prime_fiber_output434]
  apply Finset.sum_congr rfl
  intro p hp
  rw [source_original_PRIME_PRODUCT_pending_finset_filter434]
  rfl

private theorem bornFiberNonempty (born : Finset P) (p : P) :
    (born.filter (fun t => t=p)) ≠ ∅ ↔ p ∈ born := by
  constructor
  · intro h
    by_contra hp
    apply h
    apply Finset.ext
    intro t
    constructor
    · intro ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      exact False.elim (hp (he ▸ ht))
    · intro ht
      exact False.elim (Finset.notMem_empty t ht)
  · intro hp he
    have hh : p ∈ born.filter (fun t => t=p) := Finset.mem_filter.mpr ⟨hp,rfl⟩
    rw [he] at hh
    exact Finset.notMem_empty _ hh

/-- The original no-rebirth gate becomes the exact singleton gate of
each already checked physical one-prime row. -/
theorem source_original_PRIME_PRODUCT_G_gate434
    (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ) :
    (∀ p ∈ d.2.1,p ∉ sourceOriginalPrimeProductSeen434 modulus s) ↔
    (∀ p,(sourceOriginalProductPrimeChoiceEquiv434 modulus shift s d p).2.1=∅ ∨
      sourceOriginalOnePrimeSeen434 (s p)=false) := by
  change (∀ p ∈ d.2.1,p ∉ sourceOriginalPrimeProductSeen434 modulus s) ↔
    (∀ p,(d.2.1.filter (fun t => t=p))=∅ ∨ sourceOriginalOnePrimeSeen434 (s p)=false)
  constructor
  · intro h p
    by_cases hb : (d.2.1.filter (fun t => t=p))=∅
    · exact Or.inl hb
    · right
      have hn := h p ((bornFiberNonempty d.2.1 p).mp hb)
      cases hs : sourceOriginalOnePrimeSeen434 (s p) with
      | false => rfl
      | true => exact False.elim (hn ((source_original_PRIME_PRODUCT_seen_mem434 modulus s p).mpr hs))
  · intro h p hp hm
    rcases h p with hb|hs
    · exact ((bornFiberNonempty d.2.1 p).mpr hp) hb
    · have ht := (source_original_PRIME_PRODUCT_seen_mem434 modulus s p).mp hm
      simp [hs] at ht

/-- The complete updated seen set equals the Boolean seen update of
all physical prime coordinates. The joint terminal test is retained. -/
theorem source_original_PRIME_PRODUCT_G_seen_output434
    (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ) :
    sourceOriginalPrimeProductSeen434 modulus s ∪ d.2.1 =
      Finset.univ.filter (fun p =>
        (sourceOriginalOnePrimeSeen434 (s p) ||
          decide ((sourceOriginalProductPrimeChoiceEquiv434 modulus shift s d p).2.1≠∅))=true) := by
  ext p
  change p ∈ sourceOriginalPrimeProductSeen434 modulus s ∪ d.2.1 ↔
    p ∈ Finset.univ.filter (fun p =>
      (sourceOriginalOnePrimeSeen434 (s p) || decide ((d.2.1.filter (fun t => t=p))≠∅))=true)
  simp [sourceOriginalPrimeProductSeen434,bornFiberNonempty]

/-- Literal all-prime group G subset row at rho=1, on the physical
product state. The unseen gate and output are the original ones. -/
def sourceOriginalPhysicalProductGroupG434
    (eta V : ℝ) (mu : P → ℝ) (F : Multiset (Atom P modulus) → Finset P → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ,
    if ∀ p ∈ d.2.1,p ∉ sourceOriginalPrimeProductSeen434 modulus s then
      sourceOriginalGroupPrimeBirthWeight434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s)))
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus (Finset.filter (fun z => z.2=0) (Multiset.toFinset (sourceOriginalPrimeProductPending434 modulus shift s))) Finset.univ d) *
      F (sourceOriginalGhostPiecePending434 modulus
          (sourceOriginalPrimeProductPending434 modulus shift s).toFinset d.1.1 d.2.1)
        (sourceOriginalPrimeProductSeen434 modulus s ∪ d.2.1)
    else 0

/-- Exact tensor sum of the literal physical singleton G choices.
F still observes the joint pending multiset and the whole seen set. -/
def sourceOriginalPhysicalProductLocalG434
    (eta V : ℝ) (mu : P → ℝ) (F : Multiset (Atom P modulus) → Finset P → ℂ) : ℂ :=
  ∑ a : SourceOriginalProductPrimeLocalChoice434 modulus shift s,
    if ∀ p,(a p).2.1=∅ ∨ sourceOriginalOnePrimeSeen434 (s p)=false then
      (∏ p,sourceOriginalGroupPrimeBirthWeight434 modulus
        (sourceOriginalOnePrimeZero434 modulus p shift (s p))
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun t => (mu t:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ (a p))) *
      F (∑ p,sourceOriginalGhostPiecePending434 modulus
          (sourceOriginalOnePrimePending434 modulus p shift (s p)).toFinset (a p).1.1 (a p).2.1)
        (Finset.univ.filter (fun p =>
          (sourceOriginalOnePrimeSeen434 (s p) || decide ((a p).2.1≠∅))=true))
    else 0

theorem source_original_PRIME_PRODUCT_physical_G_tensor434
    (eta V : ℝ) (mu : P → ℝ) (F : Multiset (Atom P modulus) → Finset P → ℂ) :
    sourceOriginalPhysicalProductGroupG434 modulus shift s eta V mu F =
      sourceOriginalPhysicalProductLocalG434 modulus shift s eta V mu F := by
  unfold sourceOriginalPhysicalProductGroupG434 sourceOriginalPhysicalProductLocalG434
  symm
  apply Fintype.sum_equiv (sourceOriginalProductPrimeChoiceEquiv434 modulus shift s).symm
  intro a
  have hw := source_original_PRIME_PRODUCT_G_weight434 modulus shift s
    (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
    ((sourceOriginalProductPrimeChoiceEquiv434 modulus shift s).symm a)
  have ho := source_original_PRIME_PRODUCT_G_output434 modulus shift s
    ((sourceOriginalProductPrimeChoiceEquiv434 modulus shift s).symm a)
  have hs := source_original_PRIME_PRODUCT_G_seen_output434 modulus shift s
    ((sourceOriginalProductPrimeChoiceEquiv434 modulus shift s).symm a)
  have hg := source_original_PRIME_PRODUCT_G_gate434 modulus shift s
    ((sourceOriginalProductPrimeChoiceEquiv434 modulus shift s).symm a)
  simp only [Equiv.apply_symm_apply] at hw ho hs hg
  by_cases h : ∀ p ∈ ((sourceOriginalProductPrimeChoiceEquiv434 modulus shift s).symm a).2.1,
    p ∉ sourceOriginalPrimeProductSeen434 modulus s
  · rw [if_pos h,if_pos (hg.mp h),hw,ho,hs]
  · rw [if_neg h,if_neg (fun hh => h (hg.mpr hh))]
end Green64Analytic.CorrelationSquare

end

end

