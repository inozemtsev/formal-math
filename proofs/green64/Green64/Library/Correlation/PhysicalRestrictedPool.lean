module

public import Green64.Library.Weights.Part060
public import Green64.Library.Correlation.Part031

@[expose] public section

/-!
# Correlation / PhysicalRestrictedPool

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalRestrictedPool -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Original birth restriction represented by an explicit padded seen
state. The true seen observable is recovered by intersection with B. -/
theorem source_original_BACKGROUND_birth_powerset_padding434
    (B seen : Finset P) (hs : seen ⊆ B)
    (W : Finset P → ℂ) (F : Finset P → Finset P → ℂ) :
    (∑ born ∈ B.powerset,
      if ∀ p ∈ born,p ∉ seen then W born * F born (seen ∪ born) else 0) =
    ∑ born ∈ (Finset.univ : Finset P).powerset,
      if ∀ p ∈ born,p ∉ seen ∪ (Finset.univ \ B) then
        W born * F born ((seen ∪ (Finset.univ \ B) ∪ born) ∩ B) else 0 := by
  let f := fun born : Finset P =>
    if ∀ p ∈ born,p ∉ seen ∪ (Finset.univ \ B) then
      W born * F born ((seen ∪ (Finset.univ \ B) ∪ born) ∩ B) else 0
  calc
    _ = ∑ born ∈ B.powerset,f born := by
      apply Finset.sum_congr rfl
      intro born hb
      have hb' := Finset.mem_powerset.mp hb
      have hg : (∀ p ∈ born,p ∉ seen ∪ (Finset.univ \ B)) ↔
          (∀ p ∈ born,p ∉ seen) := by
        constructor
        · intro h p hp hh
          exact h p hp (Finset.mem_union.mpr (Or.inl hh))
        · intro h p hp hh
          rcases Finset.mem_union.mp hh with hh|hh
          · exact h p hp hh
          · exact (Finset.mem_sdiff.mp hh).2 (hb' hp)
      have ho : (seen ∪ (Finset.univ \ B) ∪ born) ∩ B = seen ∪ born := by
        ext p
        have hsp : p ∈ seen → p ∈ B := fun h => hs h
        have hbp : p ∈ born → p ∈ B := fun h => hb' h
        simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ]
        tauto
      dsimp only [f]
      rw [ho]
      by_cases h : ∀ p ∈ born,p ∉ seen
      · rw [if_pos h,if_pos (hg.mpr h)]
      · rw [if_neg h,if_neg (fun hh => h (hg.mp hh))]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr (Finset.subset_univ B))
      intro born hb hnot
      have hg : ¬ ∀ p ∈ born,p ∉ seen ∪ (Finset.univ \ B) := by
        intro h
        apply hnot
        apply Finset.mem_powerset.mpr
        intro p hp
        by_contra hn
        exact h p hp (Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ p,hn⟩)))
      exact if_neg hg

variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

def sourceOriginalPhysicalRestrictedPoolG434
    (B : Finset P) (eta V : ℝ) (mu : P → ℝ)
    (pending : Multiset (Atom P modulus)) (seen : Finset P)
    (F : Multiset (Atom P modulus) → Finset P → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (pending.toFinset.filter (fun z => z.2=0)) B,
    if ∀ p ∈ d.2.1,p ∉ seen then
      sourceOriginalGroupPrimeBirthWeight434 modulus
        (pending.toFinset.filter (fun z => z.2=0))
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d) *
      F (sourceOriginalGhostPiecePending434 modulus pending.toFinset d.1.1 d.2.1)
        (seen ∪ d.2.1)
    else 0

private theorem restrictedPool_sum (B : Finset P) (eta V : ℝ) (mu : P → ℝ)
    (pending : Multiset (Atom P modulus)) (seen : Finset P)
    (F : Multiset (Atom P modulus) → Finset P → ℂ) :
    sourceOriginalPhysicalRestrictedPoolG434 modulus B eta V mu pending seen F =
    ∑ A ∈ (pending.toFinset.filter (fun z => z.2=0)).powerset,
    ∑ born ∈ B.powerset,
      if ∀ p ∈ born,p ∉ seen then
        ((-(eta:ℂ))^A.card *
          (1-(eta:ℂ))^((pending.toFinset.filter (fun z => z.2=0)).card-A.card) *
          (-(eta:ℂ)*(V:ℂ))^born.card * ∏ p ∈ born,(mu p:ℂ)) *
        F (sourceOriginalGhostPiecePending434 modulus pending.toFinset A born) (seen ∪ born)
      else 0 := by
  simp only [sourceOriginalPhysicalRestrictedPoolG434,
    SourceOriginalRestrictedPrimeBirthChoice434,Fintype.sum_prod_type,
    sourceOriginalGroupPrimeBirthWeight434,sourceOriginalRestrictedPrimeBirthLift434]
  rw [Finset.sum_subtype (pending.toFinset.filter (fun z => z.2=0)).powerset
    (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro A hA
  symm
  apply Finset.sum_subtype
  intro born
  rfl

/-- Exact literal restricted-birth G row, with its genuine joint
pending/seen output, as a full pool row with explicitly padded seen. -/
theorem source_original_RESTRICTED_POOL_G_padding434
    (B : Finset P) (eta V : ℝ) (mu : P → ℝ)
    (pending : Multiset (Atom P modulus)) (seen : Finset P) (hs : seen ⊆ B)
    (F : Multiset (Atom P modulus) → Finset P → ℂ) :
    sourceOriginalPhysicalRestrictedPoolG434 modulus B eta V mu pending seen F =
    sourceOriginalPhysicalPrimePoolG434 modulus eta V mu pending
      (seen ∪ (Finset.univ \ B)) (fun out st => F out (st ∩ B)) := by
  change _ = sourceOriginalPhysicalRestrictedPoolG434 modulus Finset.univ eta V mu pending
    (seen ∪ (Finset.univ \ B)) (fun out st => F out (st ∩ B))
  rw [restrictedPool_sum,restrictedPool_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact source_original_BACKGROUND_birth_powerset_padding434 B seen hs
    (fun born => (-(eta:ℂ))^A.card *
      (1-(eta:ℂ))^((pending.toFinset.filter (fun z => z.2=0)).card-A.card) *
      (-(eta:ℂ)*(V:ℂ))^born.card * ∏ p ∈ born,(mu p:ℂ))
    (fun born st => F (sourceOriginalGhostPiecePending434 modulus pending.toFinset A born) st)

def sourceOriginalBackgroundRetiredState434 (B : Finset P)
    (s : SourceOriginalPrimeReturnProductState434 modulus) :
    SourceOriginalPrimeReturnProductState434 modulus :=
  fun p => if p ∈ B then s p else .retired

theorem source_original_BACKGROUND_retired_seen_padding434
    (B : Finset P) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (hs : ∀ p,p ∉ B → s p=.retired) :
    (sourceOriginalPrimeProductSeen434 modulus s ∩ B) ∪ (Finset.univ \ B) =
      sourceOriginalPrimeProductSeen434 modulus s := by
  ext p
  by_cases hp : p ∈ B
  · simp [hp]
  · have hh : p ∈ sourceOriginalPrimeProductSeen434 modulus s := by
      rw [source_original_PRIME_PRODUCT_seen_mem434,hs p hp]
      rfl
    simp [hp,hh]

/-- A true background subset is represented in the return-state space
by retired outside coordinates. The observable still sees only B. -/
theorem source_original_BACKGROUND_POOL_G_return_matrix434
    (B : Finset P) (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (hs : ∀ p,p ∉ B → s p=.retired)
    (eta V : ℝ) (mu : P → ℝ)
    (F : Multiset (Atom P modulus) → Finset P → ℂ) :
    sourceOriginalPhysicalRestrictedPoolG434 modulus B eta V mu
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (sourceOriginalPrimeProductSeen434 modulus s ∩ B) F =
    sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu
      (fun t => F (sourceOriginalPrimeProductPending434 modulus shift t)
        (sourceOriginalPrimeProductSeen434 modulus t ∩ B)) := by
  rw [source_original_RESTRICTED_POOL_G_padding434 modulus B eta V mu _
    _ Finset.inter_subset_right,
    source_original_BACKGROUND_retired_seen_padding434 modulus B s hs,
    source_original_PRIME_POOL_G_return_matrix434]
end Green64Analytic.CorrelationSquare

end

end

