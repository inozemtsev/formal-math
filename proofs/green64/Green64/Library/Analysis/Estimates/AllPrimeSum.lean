module

public import Green64.Library.Analysis.Estimates.AllPrimeHaar

@[expose] public section

/-!
# Analysis / Estimates / AllPrimeSum

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## AllPrimeSum -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000
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

local instance b643AllPrimeSumFrameFintype434 : Fintype (MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) := by
  unfold MemoryPrimitiveEFrame
  infer_instance

private theorem b643_supported_sum {A B T : Type} [Fintype A] [Fintype B] [AddCommMonoid T]
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

private theorem b643_array_transport_eq (q : ℝ) (hq : 0 ≤ q)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (n : ℕ)
    (states : Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell)
    (frames : Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
    (ht : ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns states frames k i) :
    memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
      q Vsmall Vbig Knu zeta theta k states frames =
    (b643AllPrimeHaarMass434 SP smallMod BP bigMod : ℂ) *
    (b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k
      (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) *
     (b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q
      (b643AllPrimePathOf434 SP smallMod BP bigMod J ell m patterns states frames) k
      ((fun g => Green64SmallHaar.residues (smallMod g) (J+ell) ((states 0).1 g)),
       (fun g => Green64SmallHaar.residues (bigMod g) (J+ell) ((states 0).2 g))) : ℂ)) := by
  rw [b643_all_prime_array_weight434 SP smallMod BP bigMod J ell m patterns
    q hq Vsmall Vbig Knu zeta theta k n states frames,ite_eq_left ht]
  rw [b643_all_prime_transport_damping434 SP smallMod BP bigMod J ell m patterns q k states frames ht]
  simp only [b643AllPrimeHaarMass434,Complex.ofReal_mul,Complex.ofReal_prod]

/-- COMPLETE original complex array sum equals the weighted complete-prime
Haar model. Both original initial masses, all original permutations, Nu,
auxiliary bans, signed offsets and the same Knu are retained exactly. -/
theorem b643_all_prime_full_sum434 (q : ℝ) (hq : 0 ≤ q)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (n : ℕ) :
    (∑ states : Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell,
      ∑ frames : Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns,
        memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k states frames) =
    ∑ ω : B643AllPrimePath434 SP BP J ell m patterns (n+1),
      b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω *
      (b643AllPrimeHaarModel434 SP smallMod BP bigMod J ell m patterns q ω k : ℂ) := by
  let SF := (Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell) ×
    (Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
  let OC := B643AllPrimePath434 SP BP J ell m patterns (n+1) ×
    B643AllPrimeAnchor434 SP smallMod BP bigMod
  let P (sf : SF) := ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns sf.1 sf.2 k i
  let Q (oc : OC) := b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns oc.1 k oc.2
  let F (sf : SF) : ℂ := memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
    q Vsmall Vbig Knu zeta theta k sf.1 sf.2
  let G (oc : OC) : ℂ := (b643AllPrimeHaarMass434 SP smallMod BP bigMod : ℂ) *
    (b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k oc.1 *
     (b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q oc.1 k oc.2 : ℂ))
  have he : (∑ sf : SF, F sf)=∑ oc : OC, G oc := by
    apply b643_supported_sum P Q
      (b643AllPrimeTransportEquiv434 SP smallMod BP bigMod J ell m patterns (n+1) k) F G
    · intro sf hf
      unfold F
      rw [b643_all_prime_array_weight434 SP smallMod BP bigMod J ell m patterns
        q hq Vsmall Vbig Knu zeta theta k n sf.1 sf.2,ite_eq_right hf,mul_zero]
    · intro oc hg
      unfold G
      rw [b643_all_prime_integrand_zero434 SP smallMod BP bigMod J ell m patterns
        q oc.1 k oc.2 hg,Complex.ofReal_zero,mul_zero,mul_zero]
    · intro sf
      dsimp only [F,G,b643AllPrimeTransportEquiv434]
      exact b643_array_transport_eq SP smallMod BP bigMod J ell m patterns q hq
        Vsmall Vbig Knu zeta theta k n sf.val.1 sf.val.2 sf.property
  calc
    _ = ∑ sf : SF, F sf := by
      conv_rhs => rw [Fintype.sum_prod_type]
    _ = ∑ oc : OC, G oc := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro ω hω
      dsimp only [G]
      rw [← Finset.mul_sum,← Finset.mul_sum]
      have hh := congrArg Complex.ofReal
        (b643_all_prime_haar_mean434 SP smallMod BP bigMod J ell m patterns q ω k)
      simp only [Complex.ofReal_mul,Complex.ofReal_sum] at hh
      calc
        _ = b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω *
          ((b643AllPrimeHaarMass434 SP smallMod BP bigMod : ℂ) *
          ∑ c : B643AllPrimeAnchor434 SP smallMod BP bigMod,
            (b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q ω k c : ℂ)) := by ring
        _ = _ := by rw [hh]

/-- Exact absolute array mass disintegration. This does not estimate or
replace signed cancellation: it identifies precisely the original mass
that multiplies the relative physical CRT error for every marked path. -/
theorem b643_all_prime_full_norm_sum434 (q : ℝ) (hq : 0 ≤ q)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (n : ℕ) :
    (∑ states : Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell,
      ∑ frames : Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns,
        ‖memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
          q Vsmall Vbig Knu zeta theta k states frames‖) =
    ∑ ω : B643AllPrimePath434 SP BP J ell m patterns (n+1),
      ‖b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω‖ *
      b643AllPrimeHaarModel434 SP smallMod BP bigMod J ell m patterns q ω k := by
  let SF := (Fin (n+2) → MemoryIndependentState SP smallMod BP bigMod J ell) ×
    (Fin (n+1) → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
  let OC := B643AllPrimePath434 SP BP J ell m patterns (n+1) ×
    B643AllPrimeAnchor434 SP smallMod BP bigMod
  let P (sf : SF) := ∀ i, b643AllPrimeRowTransport434 SP smallMod BP bigMod J ell m patterns sf.1 sf.2 k i
  let Q (oc : OC) := b643AllPrimeAnchorAllowed434 SP smallMod BP bigMod J ell m patterns oc.1 k oc.2
  let F (sf : SF) : ℝ := ‖memoryIndOriginalArrayWeight SP smallMod BP bigMod J ell m patterns
    q Vsmall Vbig Knu zeta theta k sf.1 sf.2‖
  let G (oc : OC) : ℝ := b643AllPrimeHaarMass434 SP smallMod BP bigMod *
    (‖b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k oc.1‖ *
     b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q oc.1 k oc.2)
  have he : (∑ sf : SF, F sf)=∑ oc : OC, G oc := by
    apply b643_supported_sum P Q
      (b643AllPrimeTransportEquiv434 SP smallMod BP bigMod J ell m patterns (n+1) k) F G
    · intro sf hf
      unfold F
      rw [b643_all_prime_array_weight434 SP smallMod BP bigMod J ell m patterns
        q hq Vsmall Vbig Knu zeta theta k n sf.1 sf.2,ite_eq_right hf,mul_zero,norm_zero]
    · intro oc hg
      unfold G
      rw [b643_all_prime_integrand_zero434 SP smallMod BP bigMod J ell m patterns
        q oc.1 k oc.2 hg,mul_zero,mul_zero]
    · intro sf
      dsimp only [F,G,b643AllPrimeTransportEquiv434]
      rw [b643_array_transport_eq SP smallMod BP bigMod J ell m patterns q hq
        Vsmall Vbig Knu zeta theta k n sf.val.1 sf.val.2 sf.property]
      rw [norm_mul,norm_mul]
      simp only [Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (b643_all_prime_haar_mass_nonneg434 SP smallMod BP bigMod),
        abs_of_nonneg (b643_all_prime_integrand_nonneg434 SP smallMod BP bigMod J ell m patterns q hq _ k _)]
      rfl
  calc
    _ = ∑ sf : SF, F sf := by
      conv_rhs => rw [Fintype.sum_prod_type]
    _ = ∑ oc : OC, G oc := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro ω hω
      dsimp only [G]
      rw [← Finset.mul_sum,← Finset.mul_sum]
      calc
        _ = ‖b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω‖ *
          (b643AllPrimeHaarMass434 SP smallMod BP bigMod *
          ∑ c : B643AllPrimeAnchor434 SP smallMod BP bigMod,
            b643AllPrimeAnchorIntegrand434 SP smallMod BP bigMod J ell m patterns q ω k c) := by ring
        _ = _ := by rw [b643_all_prime_haar_mean434]

/-- Full original independent root, with positive even walk length,
as the exact weighted all-SMALL/all-BIG prime local model. -/
theorem b643_original_root_all_prime_Haar434 (q : ℝ) (hq : 0 ≤ q)
    (Vsmall : SG → ℝ) (Vbig : BG → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (k : ℤ) (R : ℕ) (hR : 0 < R) :
    memoryIndependentRoot SP smallMod BP bigMod J ell m patterns q Vsmall Vbig Knu zeta theta k R =
    ∑ ω : B643AllPrimePath434 SP BP J ell m patterns (2*R),
      b643AllPrimeWeight434 SP smallMod BP bigMod J ell m patterns Vsmall Vbig Knu zeta theta k ω *
      (b643AllPrimeHaarModel434 SP smallMod BP bigMod J ell m patterns q ω k : ℂ) := by
  rw [memory_independent_root_exact_full_array_sum]
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (show 2*R ≠ 0 by omega)
  rw [hn]
  exact b643_all_prime_full_sum434 SP smallMod BP bigMod J ell m patterns q hq
    Vsmall Vbig Knu zeta theta k n
end Green64FullPhysicalE

end

end

