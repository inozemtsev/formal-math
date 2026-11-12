module

public import Green64.Library.Correlation.PhysicalReindex

@[expose] public section

/-!
# Correlation / PhysicalSum

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalSum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)


local instance b653PhysicalSumFrameFintype434 : Fintype (MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) := by
  unfold MemoryPrimitiveEFrame
  infer_instance

private theorem b653_supported_sum {A B T : Type} [Fintype A] [Fintype B] [AddCommMonoid T]
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q]
    (e : {a // P a} ≃ {b // Q b}) (f : A → T) (g : B → T)
    (hf : ∀ a, ¬P a → f a=0) (hg : ∀ b, ¬Q b → g b=0)
    (he : ∀ a : {a // P a}, f a.val=g (e a).val) :
    (∑ a : A, f a)=∑ b : B, g b := by
  calc
    _ = ∑ a : {a // P a}, f a.val :=
      Finset.sum_congr_set {a | P a} f (fun a => f a.val) (by intros; rfl) hf
    _ = ∑ b : {b // Q b}, g b.val := Fintype.sum_equiv e _ _ he
    _ = _ := (Finset.sum_congr_set {b | Q b} g (fun b => g b.val) (by intros; rfl) hg).symm

/-- Exact full physical return expansion for every positive length.
There is ONE original initial mark mass, no Haar mass, one starting
integer n, FREE final marks, and every original source frame. The only
extra path conditions are the literal finite window and signed return. -/
theorem b653_physical_full_return_sum434 (positions : Finset ℤ) (r : ℕ) (n : ℤ)
    (q : ℝ) (hq : 0 ≤ q) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ) :
    (b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig : ℂ) *
      (∑ states : Fin (r+2) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions,
        ∑ frames : Fin (r+1) → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
          if (states 0).val.1.val=n ∧ (states (Fin.last (r+1))).val.1.val=n then
            ∏ i : Fin (r+1), b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
              q Vsmall Vbig Knu zeta (physicalAlternatingSign i.val) k
              (states i.castSucc) (states i.succ) (frames i)
          else 0) =
    ∑ ω : B643AllPrimePath434 SP BP J ell m patterns (r+1),
      if (∀ t : Fin (r+2), n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val ∈ positions) ∧
          b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (r+1)=0 then
        b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k ω *
        (b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q ω k
          (b653IntegerAnchor434 SP smallMod BP bigMod n) : ℂ)
      else 0 := by
  let SF := (Fin (r+2) → B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) ×
    (Fin (r+1) → MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
  let Ω := B643AllPrimePath434 SP BP J ell m patterns (r+1)
  let P (sf : SF) := b653PhysicalArrayGuard434 SP smallMod BP bigMod J ell m patterns positions n k sf
  let Q (ω : Ω) := b653PhysicalPathGuard434 SP smallMod BP bigMod J ell m patterns positions n k ω
  let W (ω : Ω) := b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta 0 k ω
  let V (ω : Ω) : ℂ := (b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q ω k
    (b653IntegerAnchor434 SP smallMod BP bigMod n) : ℂ)
  let F (sf : SF) : ℂ := if (sf.1 0).val.1.val=n ∧ (sf.1 (Fin.last (r+1))).val.1.val=n then
    b653IntegerArrayWeight434 SP smallMod BP bigMod J ell m patterns positions
      q Vsmall Vbig Knu zeta k sf.1 sf.2 else 0
  let G (ω : Ω) : ℂ := if
    (∀ t : Fin (r+2), n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val ∈ positions) ∧
      b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (r+1)=0 then W ω*V ω else 0
  let e := b653PhysicalReturnEquiv434 SP smallMod BP bigMod J ell m patterns positions (r+1) n k
  have he : (∑ sf : SF, F sf)=∑ ω : Ω, G ω := by
    apply b653_supported_sum P Q e F G
    · intro sf hf
      unfold F
      by_cases hr : (sf.1 0).val.1.val=n ∧ (sf.1 (Fin.last (r+1))).val.1.val=n
      · rw [ite_eq_left hr]
        have hs : ¬ b653IntegerArraySteps434 SP smallMod BP bigMod J ell m patterns positions k sf.1 sf.2 :=
          fun hs => hf ⟨hr.1,hr.2,hs⟩
        rw [b653_integer_array_weight434 SP smallMod BP bigMod J ell m patterns positions r q hq
          Vsmall Vbig Knu zeta k sf.1 sf.2,ite_eq_right hs]
      · exact ite_eq_right hr
    · intro ω hω
      unfold G
      by_cases hw : (∀ t : Fin (r+2), n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k t.val ∈ positions) ∧
          b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns ω k (r+1)=0
      · rw [ite_eq_left hw]
        have ha : ¬ b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns ω k
            (b653IntegerAnchor434 SP smallMod BP bigMod n) := fun ha => hω ⟨hw.1,hw.2,ha⟩
        unfold V
        rw [b643_all_prime_integrand_zero434 SP smallMod BP bigMod J ell m patterns q ω k _ ha,
          Complex.ofReal_zero,mul_zero]
      · exact ite_eq_right hw
    · intro sf
      have hw : (∀ t : Fin (r+2), n+b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns (e sf).val k t.val ∈ positions) ∧
          b643AllPrimeOffset434 SP smallMod BP bigMod J ell m patterns (e sf).val k (r+1)=0 :=
        ⟨(e sf).property.1,(e sf).property.2.1⟩
      dsimp only [F,G]
      rw [ite_eq_left ⟨sf.property.1,sf.property.2.1⟩,ite_eq_left hw]
      rw [b653_integer_array_weight434 SP smallMod BP bigMod J ell m patterns positions r q hq
        Vsmall Vbig Knu zeta k sf.val.1 sf.val.2,ite_eq_left sf.property.2.2,sf.property.1]
      rfl
  calc
    _ = ∑ sf : SF, F sf := by
      rw [Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro states hstates
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frames hframes
      dsimp only [F,b653IntegerArrayWeight434]
      split_ifs <;> simp only [mul_zero]
    _ = ∑ ω : Ω, G ω := he
    _ = _ := rfl
end Green64FullPhysicalE

end

end

