module

public import Green64.Library.Weights.Part077

@[expose] public section

/-!
# Weights / MarkedSmallBigHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedSmallBigHilbert -/

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

/-- Joint energy before multiplication by the exact constant of the frozen
physical Fock sector. SMALL states, OLD residues and numerical seen all
remain variables of the same arbitrary complex test. -/
def sourceOriginalMarkedSmallBigEnergy434
    (mu : (g : BG) → BP g → ℝ) (f : Small → A → Finset ℕ → Old → ℂ) : ℝ :=
  ∑ z : Small × Old,sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
    (fun a S => f z.1 a S z.2)

def sourceOriginalMarkedSmallHalf434
    (q : ℝ) (Vs : SG → ℝ) (tt : SPerm)
    (f : Small → A → Finset ℕ → Old → ℂ)
    (d : Shared) (a : A) (S : Finset ℕ) (r : Torus) : ℂ :=
  memoryOriginalSmallPermutedHalfMap SP sm J ell q Vs (sourceSmallShared J ell)
    tt d r.1 (fun xs => f xs a S r.2)

def sourceOriginalMarkedSmallSynthesis434
    (q : ℝ) (Vs : SG → ℝ) (ss : SPerm)
    (H : Shared → A → Finset ℕ → Torus → ℂ)
    (xs : Small) (a : A) (S : Finset ℕ) (t : Old) : ℂ :=
  sourceOriginalSmallEndpointSynthesis434 SP sm J ell q Vs ss
    (fun d y => H d a S (y,t)) xs

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
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
      (∑ z : Small × Old,‖f z.1 a S z.2‖^2) := by
  simp only [memoryFrozenResidueGroup,Fintype.sum_prod_type]
  rw [sum_three_last_first]
  calc
    _ ≤ ∑ t : Old,memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
        (∑ xs : Small,‖f xs a S t‖^2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact source_original_small_permuted_half_energy434 SP sm J ell q hq hq1 Vs hVs
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
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
      (∑ d : Shared,∑ r : Torus,‖H d a S r‖^2) := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  calc
    _ ≤ ∑ t : Old,memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
        (∑ d : Shared,∑ y : ST,‖H d a S (y,t)‖^2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact source_original_SMALL_endpoint_synthesis_energy434 SP sm J ell q hq hq1
        Vs hVs ss (fun d y => H d a S (y,t))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [memoryFrozenResidueGroup,Fintype.sum_prod_type]
      exact (sum_three_last_first _).symm

/-- True target SMALL half-map estimate in the same joint seen/OLD
energy used by the marked BIG theorem. No test is decoupled. -/
theorem source_original_MARKED_SMALL_half_energy434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (tt : SPerm) (f : Small → A → Finset ℕ → Old → ℂ) :
    (∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu
      (sourceOriginalMarkedSmallHalf434 SP sm BP bm J ell sizes prime q Vs tt f d)) ≤
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
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
          (memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
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

theorem source_original_MARKED_SMALL_synthesis_energy434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (ss : SPerm) (H : Shared → A → Finset ℕ → Torus → ℂ) :
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP bm J ell sizes prime mu
      (sourceOriginalMarkedSmallSynthesis434 SP sm BP bm J ell sizes prime q Vs ss H) ≤
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
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
          (memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
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

/-- Actual SMALL endpoint maps around the marked BIG operator, with the
shared SMALL tuple supplying the original dsmall and all OLD residues
translated by the source divisor inside the joint future. -/
def sourceOriginalMarkedSmallBigComposite434
    (aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (o k : ℤ) (q : ℝ) (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (ss tt : SPerm) (sigma tau : BPerm)
    (K : Shared → Torus → A → Finset ℕ → A → ℂ)
    (f : Small → A → Finset ℕ → Old → ℂ) : Small → A → Finset ℕ → Old → ℂ :=
  sourceOriginalMarkedSmallSynthesis434 SP sm BP bm J ell sizes prime q Vs ss
    (fun d => sourceOriginalB26NumericResidueClean434 BP bm J ell m hmJ nu
      (sourceOriginalB26SmallTupleD434 SP sm J ell d) aux o k
      (memoryFrozenResidueShift SP sm BP bm sizes prime) mu sigma tau (K d)
      (sourceOriginalMarkedSmallHalf434 SP sm BP bm J ell sizes prime q Vs tt f d))

/-- Quantitative SMALL+BIG+OLD+numeric-seen energy bound with both
independent endpoint permutations in BOTH prime families. The original
SMALL conditioning cost is paid twice; it is independent of J. -/
theorem source_original_MARKED_SMALL_BIG_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (o k : ℤ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (ss tt : SPerm) (sigma tau : BPerm) (C : ℝ) (hC : 0 ≤ C)
    (K : Shared → Torus → A → Finset ℕ → A → ℂ)
    (hK : ∀ d r a S b,‖K d r a S b‖ ≤ C)
    (f : Small → A → Finset ℕ → Old → ℂ) :
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP bm J ell sizes prime mu
      (sourceOriginalMarkedSmallBigComposite434 SP sm BP bm J ell m hmJ nu sizes prime
        aux o k q Vs mu ss tt sigma tau K f) ≤
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      (C^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalMarkedSmallBigEnergy434 SP sm BP bm J ell sizes prime mu f := by
  let cost := memorySmallGroupConditioningConstant (SG := SG) ell q Vs
  let delta := C^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)
  have hc : 0 ≤ cost := by
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    have hq' : 0 < 1-q := sub_pos.mpr hq1
    positivity
  have hd : 0 ≤ delta := mul_nonneg (sq_nonneg _)
    (Finset.prod_nonneg (fun g _ => pow_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) _))
  let F := sourceOriginalMarkedSmallHalf434 SP sm BP bm J ell sizes prime q Vs tt f
  let H := fun d => sourceOriginalB26NumericResidueClean434 BP bm J ell m hmJ nu
    (sourceOriginalB26SmallTupleD434 SP sm J ell d) aux o k
    (memoryFrozenResidueShift SP sm BP bm sizes prime) mu sigma tau (K d) (F d)
  have hbig (d : Shared) :
      sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu (H d) ≤
      delta*sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu (F d) :=
    source_original_B26_MARKED_ORIGINAL_TORUS_Hilbert434 BP bm J ell m hmJ nu
      SP sm sizes prime hi (sourceOriginalB26SmallTupleD434 SP sm J ell d) aux o k
      mu hmu sigma tau C hC (K d) (hK d) (F d)
  have hs := source_original_MARKED_SMALL_synthesis_energy434 SP sm BP bm J ell
    sizes prime q hq hq1 Vs hVs mu hmu ss H
  have ht := source_original_MARKED_SMALL_half_energy434 SP sm BP bm J ell
    sizes prime q hq hq1 Vs hVs mu hmu tt f
  calc
    _ ≤ cost*(∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu (H d)) := hs
    _ ≤ cost*(∑ d : Shared,delta*sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu (F d)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => hbig d)) hc
    _ = (cost*delta)*(∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP bm J ell mu (F d)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (cost*delta)*(cost*sourceOriginalMarkedSmallBigEnergy434
        SP sm BP bm J ell sizes prime mu f) :=
      mul_le_mul_of_nonneg_left ht (mul_nonneg hc hd)
    _ = _ := by dsimp only [cost,delta]; ring

end Green64Analytic.CorrelationSquare

end

end

