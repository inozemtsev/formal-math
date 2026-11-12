module

public import Green64.Library.Weights.Part077
public import Green64.Library.Weights.MarkedSmallBigHilbert

@[expose] public section

/-!
# Weights / SmallSharpHalf

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalSmallSharpHalf -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Improved conditioning constant for the original q=1/2, ell=1
case. Other parameter choices retain the previously verified constant.
The physical maps and their densities are not redefined. -/
def sourceOriginalSharpSmallConditioningConstant434
    {SG : Type} [Fintype SG] (ell : ℕ) (q : ℝ) (Vs : SG → ℝ) : ℝ :=
  if ell=1 ∧ q=(1:ℝ)/2 then ∏ g : SG, 1/(Vs g)
  else memorySmallGroupConditioningConstant (SG := SG) ell q Vs

/-- Exact discrete geometric envelope: the factorial-over-tail bound
4 used previously at ell=1,q=1/2 can be replaced by 1. -/
theorem source_original_SMALL_half_geometric_envelope434 (r : ℕ) :
    ((1:ℝ)/2)^(r-1)*(r:ℝ) ≤ 1 := by
  cases r with
  | zero => norm_num
  | succ n =>
    have hn : n+1 ≤ 2^n := by
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [pow_succ]
        calc
          n+1+1 ≤ (n+1)*2 := by omega
          _ ≤ 2^n*2 := Nat.mul_le_mul_right 2 ih
    have hnr : ((n+1:ℕ):ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hn
    calc
      _ = ((1:ℝ)/2)^n*((n+1:ℕ):ℝ) := by simp
      _ ≤ ((1:ℝ)/2)^n*2^n := mul_le_mul_of_nonneg_left hnr (by positivity)
      _ = 1 := by rw [←mul_pow]; norm_num

/-- The literal independently permuted SMALL fibre has coefficient
at most 1/V, uniformly in J, prime labels and residue moduli. -/
theorem source_original_SMALL_half_permuted_fibre434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (J : ℕ) (V : ℝ) (hV : 0 < V)
    (shared : Finset (Fin (J+1))) (hshared : shared.card=J)
    (sigma : Equiv.Perm (Fin (J+1))) (d : ↥shared → P)
    (y : SmallTorus modulus) :
    memorySmallConditionalRatio modulus J 1 ((1:ℝ)/2) V y *
      ((memoryOriginalSmallPermutedFibre modulus (J+1) shared sigma d y).card:ℝ) ≤ 1/V := by
  let T := memoryOriginalSmallPermutedFibre modulus (J+1) shared sigma d y
  have hrest : unsharedSlots (J+1) shared=1 := by
    unfold unsharedSlots
    rw [hshared]
    omega
  have hc := source_original_small_permuted_fibre_card434 modulus (J+1) shared sigma d y
  rw [hshared,hrest,Nat.descFactorial_one] at hc
  have hcR : (T.card:ℝ) ≤ ((omega modulus y-J:ℕ):ℝ) := by exact_mod_cast hc
  have he : omega modulus y-(J+1) = (omega modulus y-J)-1 := by omega
  unfold memorySmallConditionalRatio
  rw [pow_one]
  calc
    _ = (((1:ℝ)/2)^(omega modulus y-(J+1))*(T.card:ℝ))/V := by ring
    _ ≤ (((1:ℝ)/2)^(omega modulus y-(J+1))*((omega modulus y-J:ℕ):ℝ))/V :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcR (by positivity)) hV.le
    _ ≤ 1/V := by
      rw [he]
      exact div_le_div_of_nonneg_right
        (source_original_SMALL_half_geometric_envelope434 (omega modulus y-J)) hV.le

theorem source_original_SMALL_sharp_cost_nonneg434
    {SG : Type} [Fintype SG] (ell : ℕ) (q : ℝ) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) :
    0 ≤ sourceOriginalSharpSmallConditioningConstant434 ell q Vs := by
  unfold sourceOriginalSharpSmallConditioningConstant434
  split_ifs
  · exact Finset.prod_nonneg (fun g _ => (one_div_pos.mpr (hVs g)).le)
  · unfold memorySmallGroupConditioningConstant
    apply Finset.prod_nonneg
    intro g hg
    have hq' : 0 < 1-q := sub_pos.mpr hq1
    have hv := hVs g
    positivity

/-- The old SMALL constant is exactly 4 per group times the new
constant at the source q=1/2,ell=1 values. -/
theorem source_original_SMALL_sharp_cost_factor434
    {SG : Type} [Fintype SG] (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) :
    memorySmallGroupConditioningConstant (SG := SG) 1 ((1:ℝ)/2) Vs =
    (4:ℝ)^(Fintype.card SG)*sourceOriginalSharpSmallConditioningConstant434 1 ((1:ℝ)/2) Vs := by
  have he (g : SG) :
      ((1:ℕ).factorial:ℝ)/((1-(1:ℝ)/2)^(1+1)*(Vs g)^1) = 4*(1/(Vs g)) := by
    norm_num
    field_simp [(hVs g).ne']
    <;> ring
  unfold memorySmallGroupConditioningConstant sourceOriginalSharpSmallConditioningConstant434
  rw [if_pos ⟨rfl,rfl⟩]
  simp only [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (J ell : ℕ)

theorem source_original_SMALL_sharp_group_fibre434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (shared : SG → Finset (Fin (J+ell)))
    (hshared : ∀ g,(shared g).card = J)
    (sigma : GroupPermFamily (G := SG) (J+ell))
    (d : (g : SG) → ↥(shared g) → SP g) (y : GroupTorus SP sm) :
    memorySmallGroupConditionalRatio SP sm J ell q Vs y *
      ((memoryOriginalSmallGroupPermutedFibre SP sm (J+ell) shared sigma d y).card:ℝ) ≤
    sourceOriginalSharpSmallConditioningConstant434 ell q Vs := by
  unfold sourceOriginalSharpSmallConditioningConstant434
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    rw [source_original_small_group_permuted_fibre_card434]
    simp only [Nat.cast_prod]
    unfold memorySmallGroupConditionalRatio
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro g hg
      apply mul_nonneg _ (Nat.cast_nonneg _)
      unfold memorySmallConditionalRatio
      have hv := hVs g
      positivity
    · intro g hg
      exact source_original_SMALL_half_permuted_fibre434
        (sm g) J (Vs g) (hVs g) (shared g) (hshared g) (sigma g) (d g) (y g)
  · exact source_original_small_group_permuted_fibre_weight434
      SP sm J ell q hq hq1 Vs hVs shared hshared sigma d y

theorem source_original_SMALL_sharp_half_energy434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (shared : SG → Finset (Fin (J+ell)))
    (hshared : ∀ g,(shared g).card = J)
    (sigma : Green64SmallHaar.GroupPermFamily (G := SG) (J+ell))
    (w : Green64SmallHaar.GroupState SP sm (J+ell) → ℂ) :
    (∑ d : (g : SG) → ↥(shared g) → SP g,
      ∑ y : Green64SmallHaar.GroupTorus SP sm,
        ‖memoryOriginalSmallPermutedHalfMap SP sm J ell
          q Vs shared sigma d y w‖^2) ≤
    sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
      ∑ xs : Green64SmallHaar.GroupState SP sm (J+ell),‖w xs‖^2 := by
  classical
  let a := memorySmallGroupConditionalRatio SP sm J ell q Vs
  let C := sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs
  have ha (y : Green64SmallHaar.GroupTorus SP sm) : 0 ≤ a y := by
    apply Finset.prod_nonneg
    intro g _
    dsimp [memorySmallConditionalRatio]
    exact div_nonneg (pow_nonneg hq.le _) (pow_nonneg (hVs g).le _)
  have hC : 0 ≤ C := source_original_SMALL_sharp_cost_nonneg434 ell q hq1 Vs hVs
  have hh := memory_finite_conditioning_norm_sq
    (memoryOriginalSmallGroupSharedLabels SP sm (J+ell) shared sigma)
    (memoryOriginalSmallGroupResidue SP sm (J+ell))
    a ha C hC
    (fun d y => source_original_SMALL_sharp_group_fibre434
      SP sm J ell q hq hq1 Vs hVs shared hshared sigma d y) w
  have heq (d : (g : SG) → ↥(shared g) → SP g)
      (y : Green64SmallHaar.GroupTorus SP sm) :
      ‖memoryOriginalSmallPermutedHalfMap SP sm J ell
          q Vs shared sigma d y w‖^2 =
      a y * ‖∑ xs ∈ memoryOriginalSmallGroupPermutedFibre SP sm
        (J+ell) shared sigma d y,w xs‖^2 := by
    unfold memoryOriginalSmallPermutedHalfMap
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      memory_original_small_group_endpoint_half_sq SP sm J ell q hq.le Vs hVs]
  simpa only [heq,memoryOriginalSmallGroupPermutedFibre,a,C] using hh

local notation "Small" => GroupState SP sm (J+ell)
local notation "ST" => GroupTorus SP sm
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "Perm" => GroupPermFamily (G := SG) (J+ell)

theorem source_original_SMALL_sharp_synthesis_energy434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) (ss : Perm) (F : Shared → ST → ℂ) :
    (∑ xs : Small,‖sourceOriginalSmallEndpointSynthesis434 SP sm J ell q Vs ss F xs‖^2) ≤
    sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs *
      (∑ d : Shared,∑ y : ST,‖F d y‖^2) := by
  let label := memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss
  let res := memoryOriginalSmallGroupResidue SP sm (J+ell)
  let a := memorySmallGroupConditionalRatio SP sm J ell q Vs
  let cost := sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs
  let T := memoryFiniteConditionalFibre label res
  have hpoint (d : Shared) (y : ST) (xs : Small) (hx : xs ∈ T d y) :
      ‖sourceOriginalSmallEndpointSynthesis434 SP sm J ell q Vs ss F xs‖^2 =
      a y*‖F d y‖^2 := by
    have hx' : label xs=d ∧ res xs=y := by
      simpa only [T,memoryFiniteConditionalFibre,Finset.mem_filter,Finset.mem_univ,true_and] using hx
    change ‖(memoryOriginalSmallGroupPhysicalEndpointHalf SP sm J ell q Vs (res xs):ℂ) *
      F (label xs) (res xs)‖^2 = _
    rw [hx'.1,hx'.2,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      memory_original_small_group_endpoint_half_sq SP sm J ell q hq.le Vs hVs]
  rw [←memory_finite_conditional_partition label res
    (fun xs => ‖sourceOriginalSmallEndpointSynthesis434 SP sm J ell q Vs ss F xs‖^2)]
  calc
    _ = ∑ d : Shared,∑ y : ST,(a y*((T d y).card:ℝ))*‖F d y‖^2 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro y hy
      calc
        _ = ∑ xs ∈ T d y,a y*‖F d y‖^2 :=
          Finset.sum_congr rfl (fun xs hx => hpoint d y xs hx)
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ ∑ d : Shared,∑ y : ST,cost*‖F d y‖^2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro y hy
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact source_original_SMALL_sharp_group_fibre434 SP sm J ell q hq hq1
        Vs hVs (sourceSmallShared J ell) (source_original_B26_small_shared_card434 J ell)
        ss d y
    _ = _ := by simp only [cost,Finset.mul_sum]


end Green64Analytic.CorrelationSquare

end

end

