module

public import Green64.Library.Correlation.PhysicalPrimeProductG

@[expose] public section

/-!
# Correlation / PhysicalPrimeStateTransition

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalPrimeStateTransition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (p : P)

def sourceOriginalOnePrimeNext434 (shift : ℤ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (deleted : Finset (Atom P modulus)) (born : Finset P) :
    SourceOriginalGhostReturnState434 (ZMod (modulus p)) :=
  match s with
  | .unborn => if born=∅ then .unborn else .pending (-(shift : ZMod (modulus p)))
  | .pending r => if deleted=∅ then .pending r else .retired
  | .retired => .retired

private theorem singletonCases {U : Type} [DecidableEq U] (a : U)
    (s : Finset U) (hs : s ⊆ {a}) : s=∅ ∨ s={a} := by
  by_cases h : s=∅
  · exact Or.inl h
  · right
    apply Finset.Subset.antisymm hs
    obtain ⟨t,ht⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have he : t=a := Finset.mem_singleton.mp (hs ht)
    subst t
    exact Finset.singleton_subset_iff.mpr ht

/-- An admissible literal singleton subset choice stays in the
once-born state sector, with its true pending multiset and seen flag. -/
theorem source_original_ONE_PRIME_choice_state_output434
    (shift : ℤ) (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift s) {p})
    (hg : d.2.1=∅ ∨ sourceOriginalOnePrimeSeen434 s=false) :
    sourceOriginalGhostPiecePending434 modulus
        (sourceOriginalOnePrimePending434 modulus p shift s).toFinset d.1.1 d.2.1 =
      sourceOriginalOnePrimePending434 modulus p shift
        (sourceOriginalOnePrimeNext434 modulus p shift s d.1.1 d.2.1) ∧
    (sourceOriginalOnePrimeSeen434 s || decide (d.2.1≠∅)) =
      sourceOriginalOnePrimeSeen434
        (sourceOriginalOnePrimeNext434 modulus p shift s d.1.1 d.2.1) := by
  have hborn := singletonCases p d.2.1 (Finset.mem_powerset.mp d.2.2)
  cases s with
  | unborn =>
      have hd : d.1.1=∅ := Finset.subset_empty.mp (by
        simpa [sourceOriginalOnePrimeZero434,sourceOriginalOnePrimePending434] using
          (Finset.mem_powerset.mp d.1.2))
      rcases hborn with hb|hb
      · simp [sourceOriginalOnePrimeNext434,sourceOriginalGhostPiecePending434,
          sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,hd,hb]
      · simp [sourceOriginalOnePrimeNext434,sourceOriginalGhostPiecePending434,
          sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,hd,hb]
  | pending r =>
      have hb : d.2.1=∅ := hg.resolve_right (by simp [sourceOriginalOnePrimeSeen434])
      have hs : d.1.1 ⊆ {⟨p,r+(shift : ZMod (modulus p))⟩} := by
        intro z hz
        have hz' := (Finset.mem_filter.mp ((Finset.mem_powerset.mp d.1.2) hz)).1
        simpa only [sourceOriginalOnePrimePending434,Multiset.toFinset_singleton] using hz'
      rcases singletonCases (⟨p,r+(shift : ZMod (modulus p))⟩ : Atom P modulus) d.1.1 hs with hd|hd
      · simp [sourceOriginalOnePrimeNext434,sourceOriginalGhostPiecePending434,
          sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,hd,hb]
      · simp [sourceOriginalOnePrimeNext434,sourceOriginalGhostPiecePending434,
          sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,hd,hb]
  | retired =>
      have hb : d.2.1=∅ := hg.resolve_right (by simp [sourceOriginalOnePrimeSeen434])
      have hd : d.1.1=∅ := Finset.subset_empty.mp (by
        simpa [sourceOriginalOnePrimeZero434,sourceOriginalOnePrimePending434] using
          (Finset.mem_powerset.mp d.1.2))
      simp [sourceOriginalOnePrimeNext434,sourceOriginalGhostPiecePending434,
        sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,hd,hb]

theorem source_original_ONE_PRIME_state_encoding_injective434 (shift : ℤ) :
    Function.Injective (fun s : SourceOriginalGhostReturnState434 (ZMod (modulus p)) =>
      (sourceOriginalOnePrimePending434 modulus p shift s,sourceOriginalOnePrimeSeen434 s)) := by
  intro s t h
  cases s <;> cases t <;>
    simp_all [sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434]

def sourceOriginalOnePrimeDecode434 (shift : ℤ)
    (pending : Multiset (Atom P modulus)) (seen : Bool) :
    SourceOriginalGhostReturnState434 (ZMod (modulus p)) :=
  if h : ∃ s, sourceOriginalOnePrimePending434 modulus p shift s=pending ∧
      sourceOriginalOnePrimeSeen434 s=seen then h.choose else .unborn

theorem source_original_ONE_PRIME_decode_encode434
    (shift : ℤ) (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) :
    sourceOriginalOnePrimeDecode434 modulus p shift
      (sourceOriginalOnePrimePending434 modulus p shift s)
      (sourceOriginalOnePrimeSeen434 s) = s := by
  have h : ∃ t,sourceOriginalOnePrimePending434 modulus p shift t =
      sourceOriginalOnePrimePending434 modulus p shift s ∧
      sourceOriginalOnePrimeSeen434 t=sourceOriginalOnePrimeSeen434 s := ⟨s,rfl,rfl⟩
  rw [sourceOriginalOnePrimeDecode434,dif_pos h]
  apply source_original_ONE_PRIME_state_encoding_injective434 modulus p shift
  exact Prod.ext h.choose_spec.1 h.choose_spec.2

def sourceOriginalOnePrimeChoiceRow434 (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (F : SourceOriginalGhostReturnState434 (ZMod (modulus p)) → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift s) {p},
    if d.2.1=∅ ∨ sourceOriginalOnePrimeSeen434 s=false then
      sourceOriginalGroupPrimeBirthWeight434 modulus
        (sourceOriginalOnePrimeZero434 modulus p shift s)
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun t => (mu t:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d) *
      F (sourceOriginalOnePrimeNext434 modulus p shift s d.1.1 d.2.1)
    else 0

theorem source_original_ONE_PRIME_choice_return_row434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (F : SourceOriginalGhostReturnState434 (ZMod (modulus p)) → ℂ) :
    sourceOriginalOnePrimeChoiceRow434 modulus p shift eta V mu s F =
    sourceOriginalGhostReturnLiteralRow434 (-(shift : ZMod (modulus p))) eta (V*mu p) s F := by
  have hphys : sourceOriginalOnePrimeChoiceRow434 modulus p shift eta V mu s F =
      sourceOriginalOnePrimePhysicalRow434 modulus p shift eta V mu s
        (fun pending seen => F (sourceOriginalOnePrimeDecode434 modulus p shift pending seen)) := by
    unfold sourceOriginalOnePrimeChoiceRow434 sourceOriginalOnePrimePhysicalRow434
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hg : d.2.1=∅ ∨ sourceOriginalOnePrimeSeen434 s=false
    · rw [if_pos hg,if_pos hg]
      have ho := source_original_ONE_PRIME_choice_state_output434 modulus p shift s d hg
      dsimp only
      rw [ho.1,ho.2,source_original_ONE_PRIME_decode_encode434]
    · rw [if_neg hg,if_neg hg]
  rw [hphys,source_original_PHYSICAL_SINGLE_PRIME_return_row434]
  congr 1
  funext t
  rw [source_original_ONE_PRIME_decode_encode434]
end Green64Analytic.CorrelationSquare

end

end

