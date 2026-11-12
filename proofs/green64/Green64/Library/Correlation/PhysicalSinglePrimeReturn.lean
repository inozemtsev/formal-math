module

public import Green64.Library.Correlation.PhysicalGhostBackgroundSplit
public import Green64.Library.Weights.Part027

@[expose] public section

/-!
# Correlation / PhysicalSinglePrimeReturn

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalSinglePrimeReturn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (p : P)

def sourceOriginalOnePrimePending434 (shift : ℤ) :
    SourceOriginalGhostReturnState434 (ZMod (modulus p)) → Multiset (Atom P modulus)
  | .unborn => 0
  | .pending r => {⟨p,r+(shift : ZMod (modulus p))⟩}
  | .retired => 0

def sourceOriginalOnePrimeSeen434 {R : Type} : SourceOriginalGhostReturnState434 R → Bool
  | .unborn => false
  | .pending _ => true
  | .retired => true

def sourceOriginalOnePrimeZero434 (shift : ℤ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) : Finset (Atom P modulus) :=
  (sourceOriginalOnePrimePending434 modulus p shift s).toFinset.filter (fun z => z.2=0)

/-- Literal restricted prime-subset G row at rho=1 for the singleton
prime pool. Its birth coefficient is V*mu(p), and its output is the
actual pending multiset, not an assumed abstract transition. -/
def sourceOriginalOnePrimePhysicalRow434 (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (F : Multiset (Atom P modulus) → Bool → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 (modulus)
      (sourceOriginalOnePrimeZero434 modulus p shift s) {p},
    if d.2.1=∅ ∨ sourceOriginalOnePrimeSeen434 s=false then
      sourceOriginalGroupPrimeBirthWeight434 modulus
        (sourceOriginalOnePrimeZero434 modulus p shift s)
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun t => (mu t:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d) *
      F (sourceOriginalGhostPiecePending434 modulus
          (sourceOriginalOnePrimePending434 modulus p shift s).toFinset d.1.1 d.2.1)
        (sourceOriginalOnePrimeSeen434 s || decide (d.2.1≠∅))
    else 0

theorem source_original_ONE_PRIME_zero_residue434
    (shift : ℤ) (r : ZMod (modulus p)) :
    (translateAtom (modulus := modulus) shift ⟨p,r⟩).2=0 ↔
      r=-(shift : ZMod (modulus p)) := by
  change r+(shift : ZMod (modulus p))=0 ↔ _
  exact add_eq_zero_iff_eq_neg

private theorem onePrimeZero_pending (shift : ℤ) (r : ZMod (modulus p)) :
    sourceOriginalOnePrimeZero434 modulus p shift (.pending r) =
      if r=-(shift : ZMod (modulus p)) then {⟨p,0⟩} else ∅ := by
  by_cases h : r=-(shift : ZMod (modulus p))
  · subst r
    simp [sourceOriginalOnePrimeZero434,sourceOriginalOnePrimePending434]
  · have hz : r+(shift : ZMod (modulus p))≠0 := by
      intro hz
      exact h (add_eq_zero_iff_eq_neg.mp hz)
    simp [sourceOriginalOnePrimeZero434,sourceOriginalOnePrimePending434,h,hz]

private theorem sumSubtype {U : Type} [DecidableEq U] (T : Finset U)
    [Fintype {u // u ∈ T}] (f : U → ℂ) :
    (∑ u : {u // u ∈ T}, f u.1) = ∑ u ∈ T, f u :=
  (Finset.sum_subtype T (fun _ => Iff.rfl) f).symm

private theorem powersetSingleton {U : Type} [DecidableEq U] (u : U) :
    ({u} : Finset U).powerset = {∅,{u}} := by
  simpa using Finset.powerset_insert (∅ : Finset U) u

private theorem onePrimePhysicalRow_sum (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (F : Multiset (Atom P modulus) → Bool → ℂ) :
    sourceOriginalOnePrimePhysicalRow434 modulus p shift eta V mu s F =
    ∑ A ∈ (sourceOriginalOnePrimeZero434 modulus p shift s).powerset,
    ∑ B ∈ ({p} : Finset P).powerset,
      if B=∅ ∨ sourceOriginalOnePrimeSeen434 s=false then
        ((-(eta:ℂ))^A.card *
          (1-(eta:ℂ))^((sourceOriginalOnePrimeZero434 modulus p shift s).card-A.card) *
          (-(eta:ℂ)*(V:ℂ))^B.card * ∏ t ∈ B,(mu t:ℂ)) *
        F (sourceOriginalGhostPiecePending434 modulus
          (sourceOriginalOnePrimePending434 modulus p shift s).toFinset A B)
          (sourceOriginalOnePrimeSeen434 s || decide (B≠∅))
      else 0 := by
  simp only [sourceOriginalOnePrimePhysicalRow434,
    SourceOriginalRestrictedPrimeBirthChoice434,Fintype.sum_prod_type,
    sourceOriginalGroupPrimeBirthWeight434,sourceOriginalRestrictedPrimeBirthLift434]
  rw [Finset.sum_subtype (sourceOriginalOnePrimeZero434 modulus p shift s).powerset
    (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro A hA
  symm
  apply Finset.sum_subtype
  intro B
  rfl

/-- Exact identification with the previously checked once-born row,
in coordinates before the accumulated actual translation. -/
theorem source_original_PHYSICAL_SINGLE_PRIME_return_row434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (F : Multiset (Atom P modulus) → Bool → ℂ) :
    sourceOriginalOnePrimePhysicalRow434 modulus p shift eta V mu s F =
    sourceOriginalGhostReturnLiteralRow434 (-(shift : ZMod (modulus p))) eta (V*mu p) s
      (fun t => F (sourceOriginalOnePrimePending434 modulus p shift t)
        (sourceOriginalOnePrimeSeen434 t)) := by
  rw [onePrimePhysicalRow_sum]
  cases s with
  | unborn =>
      rw [source_original_GHOST_RETURN_literal_unborn434]
      simp [sourceOriginalOnePrimeZero434,
        sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,
        sourceOriginalGroupPrimeBirthWeight434,sourceOriginalRestrictedPrimeBirthLift434,
        powersetSingleton,sourceOriginalGhostPiecePending434]
      <;> push_cast <;> ring
  | retired =>
      rw [source_original_GHOST_RETURN_literal_retired434]
      simp [sourceOriginalOnePrimeZero434,
        sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,
        sourceOriginalGroupPrimeBirthWeight434,sourceOriginalRestrictedPrimeBirthLift434,
        powersetSingleton,sourceOriginalGhostPiecePending434]
  | pending r =>
      rw [source_original_GHOST_RETURN_literal_pending434]
      by_cases h : r=-(shift : ZMod (modulus p))
      · subst r
        simp [onePrimeZero_pending,
          sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,
          sourceOriginalGroupPrimeBirthWeight434,sourceOriginalRestrictedPrimeBirthLift434,
          powersetSingleton,sourceOriginalGhostPiecePending434]
        <;> ring
      · have hz : r+(shift : ZMod (modulus p))≠0 := by
          intro hz;exact h (add_eq_zero_iff_eq_neg.mp hz)
        simp [onePrimeZero_pending,h,hz,
          sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,
          sourceOriginalGroupPrimeBirthWeight434,sourceOriginalRestrictedPrimeBirthLift434,
          powersetSingleton,sourceOriginalGhostPiecePending434]
end Green64Analytic.CorrelationSquare

end

end

