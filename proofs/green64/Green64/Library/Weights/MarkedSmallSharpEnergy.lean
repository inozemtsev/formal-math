module

public import Green64.Library.Weights.SmallSharpHalf

@[expose] public section

/-!
# Weights / MarkedSmallSharpEnergy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedSmallSharpEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
variable (sizes : BG → ℕ) (prime : (g : BG) → Fin (sizes g) → BP g)
local notation "Small" => GroupState SP sm (J+ell)
local notation "ST" => GroupTorus SP sm
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Torus" => memoryFrozenResidueGroup SP sm BP bm sizes prime
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "BPerm" => BigGroupPerm (BG := BG) (J+ell)

private theorem sum_three_last_first
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (f : X → Y → Z → ℝ) :
    (∑ x,∑ y,∑ z,f x y z) = ∑ z,∑ x,∑ y,f x y z := by
  calc
    _ = ∑ x,∑ z,∑ y,f x y z :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

private theorem marked_family_energy {X : Type} [Fintype X]
    (mu : (g : BG) → BP g → ℝ) (F : X → A → Finset ℕ → ℂ) :
    (∑ x : X,sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu (F x)) =
    ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
      ∑ a : A,sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu a *
        (∑ x : X,‖F x a S‖^2) := by
  unfold sourceOriginalB26NumericActiveEnergy434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  exact (Finset.mul_sum _ _ _).symm

private theorem small_half_point
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (tt : SPerm) (f : Small → A → Finset ℕ → Old → ℂ) (a : A) (S : Finset ℕ) :
    (∑ d : Shared,∑ r : Torus,
      ‖sourceOriginalMarkedSmallHalf434 SP sm BP bm J ell sizes prime q Vs tt f d a S r‖^2) ≤
    sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
      (∑ z : Small × Old,‖f z.1 a S z.2‖^2) := by
  simp only [memoryFrozenResidueGroup,Fintype.sum_prod_type]
  rw [sum_three_last_first]
  calc
    _ ≤ ∑ t : Old,sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
        (∑ xs : Small,‖f xs a S t‖^2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact source_original_SMALL_sharp_half_energy434 SP sm J ell q hq hq1 Vs hVs
        (sourceSmallShared J ell) (source_original_B26_small_shared_card434 J ell)
        tt (fun xs => f xs a S t)
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]

private theorem small_synthesis_point
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (ss : SPerm) (H : Shared → A → Finset ℕ → Torus → ℂ)
    (a : A) (S : Finset ℕ) :
    (∑ z : Small × Old,
      ‖sourceOriginalMarkedSmallSynthesis434 SP sm BP bm J ell sizes prime
        q Vs ss H z.1 a S z.2‖^2) ≤
    sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
      (∑ d : Shared,∑ r : Torus,‖H d a S r‖^2) := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  calc
    _ ≤ ∑ t : Old,sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
        (∑ d : Shared,∑ y : ST,‖H d a S (y,t)‖^2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact source_original_SMALL_sharp_synthesis_energy434 SP sm J ell q hq hq1
        Vs hVs ss (fun d y => H d a S (y,t))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [memoryFrozenResidueGroup,Fintype.sum_prod_type]
      exact (sum_three_last_first _).symm

/-- True target SMALL half-map estimate in the same joint seen/OLD
energy used by the marked BIG theorem. No test is decoupled. -/
theorem source_original_MARKED_SMALL_sharp_half_energy434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (tt : SPerm) (f : Small → A → Finset ℕ → Old → ℂ) :
    (∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu
      (sourceOriginalMarkedSmallHalf434 SP sm BP bm J ell sizes prime q Vs tt f d)) ≤
    sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
      sourceOriginalMarkedSmallBigEnergy434 SP sm BP bm J ell sizes prime mu f := by
  have he := marked_family_energy BP bm J ell mu
    (fun z : Shared × Torus => fun a S =>
      sourceOriginalMarkedSmallHalf434 SP sm BP bm J ell sizes prime q Vs tt f z.1 a S z.2)
  rw [Fintype.sum_prod_type] at he
  unfold sourceOriginalB26NumericResidueEnergy434 sourceOriginalMarkedSmallBigEnergy434
  rw [he,marked_family_energy]
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ a : A,sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu a *
          (sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
            (∑ xs : Small,∑ t : Old,‖f xs a S t‖^2)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left
      · simpa only [Fintype.sum_prod_type] using
          small_half_point SP sm BP bm J ell sizes prime q hq hq1 Vs hVs tt f a S
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (a g i)))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro xs hxs
      apply Finset.sum_congr rfl
      intro t ht
      ring

theorem source_original_MARKED_SMALL_sharp_synthesis_energy434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (ss : SPerm) (H : Shared → A → Finset ℕ → Torus → ℂ) :
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP bm J ell sizes prime mu
      (sourceOriginalMarkedSmallSynthesis434 SP sm BP bm J ell sizes prime q Vs ss H) ≤
    sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
      (∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu (H d)) := by
  have he := marked_family_energy BP bm J ell mu
    (fun z : Shared × Torus => fun a S => H z.1 a S z.2)
  rw [Fintype.sum_prod_type] at he
  unfold sourceOriginalB26NumericResidueEnergy434 sourceOriginalMarkedSmallBigEnergy434
  rw [he,marked_family_energy]
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ a : A,sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu a *
          (sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
            (∑ d : Shared,∑ r : Torus,‖H d a S r‖^2)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left
      · simpa only [Fintype.sum_prod_type] using
          small_synthesis_point SP sm BP bm J ell sizes prime q hq hq1 Vs hVs ss H a S
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (a g i)))
    _ = _ := by
      simp only [memoryFrozenResidueGroup,Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro t ht
      ring


end Green64Analytic.CorrelationSquare

end

end

