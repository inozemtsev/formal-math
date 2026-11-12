module

public import Green64.Library.Correlation.MemoryOldTerminalBirthCut
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part063
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Green64.Library.Weights.Part060
public import Green64.Library.Weights.ActualRhoOneFullEPacket

@[expose] public section

/-!
# Correlation / Part050

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOldAllowanceMargin -/

section

open scoped BigOperators
open Filter
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A scalar OLD allowance bound with the threshold before both moving
natural parameters. The source-specific bound M <= L remains an explicit
hypothesis; it is not inferred from the source definitions here. -/
theorem eventually_source_original_MEMORY_OLD_allowance_quarter434
    (CG : ℝ) (hCG : 0 ≤ CG) :
    ∀ᶠ L : ℝ in atTop, ∀ (G M : ℕ),
      (G : ℝ) ≤ CG * Real.log L → (M : ℝ) ≤ L →
      ((G * ((2 * ⌈L ^ (0.52 : ℝ)⌉₊ + 1) * M) : ℕ) : ℝ) ≤ L ^ 2 / 4 := by
  have hp : ∀ᶠ L : ℝ in atTop, 80 * CG ≤ L ^ (0.23 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.23)).eventually
      (eventually_ge_atTop (80 * CG))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hp] with L hL hp
  intro G M hG hM
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLog : Real.log L ≤ 4 * L ^ (0.25 : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hLp (0.25 : ℝ))
    rw [Real.log_rpow hLp] at hh
    linarith
  have hG' : (G : ℝ) ≤ 4 * CG * L ^ (0.25 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hLog hCG
    nlinarith
  have hOne : 1 ≤ L ^ (0.52 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hCeil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hLp.le (0.52 : ℝ))).le
  have hN : ((2 * ⌈L ^ (0.52 : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * L ^ (0.52 : ℝ) := by
    push_cast
    linarith
  have hPow : L ^ (0.25 : ℝ) * L ^ (0.52 : ℝ) * L = L ^ (1.77 : ℝ) := by
    calc
      _ = L ^ ((0.25 : ℝ) + 0.52) * L ^ (1 : ℝ) := by
        rw [Real.rpow_add hLp, Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hLp]; norm_num
  have hPow2 : L ^ (0.23 : ℝ) * L ^ (1.77 : ℝ) = L ^ 2 := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hScale := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hLp.le (1.77 : ℝ))
  rw [hPow2] at hScale
  calc
    _ = (G : ℝ) * ((2 * ⌈L ^ (0.52 : ℝ)⌉₊ + 1 : ℕ) : ℝ) * (M : ℝ) := by
      push_cast
      ring
    _ ≤ (4 * CG * L ^ (0.25 : ℝ)) * (5 * L ^ (0.52 : ℝ)) * L := by
      exact mul_le_mul
        (mul_le_mul hG' hN (Nat.cast_nonneg _) (by positivity))
        hM (Nat.cast_nonneg _) (by positivity)
    _ = 20 * CG * L ^ (1.77 : ℝ) := by rw [← hPow]; ring
    _ ≤ L ^ 2 / 4 := by nlinarith

/-- A concrete positive residual threshold, still uniform before the
moving group and slot counts. H is ceil(L^2/4); the source OLD cutoff is
ceil(L^2). This proves a feasible scalar budget, not source applicability
of M <= L or an operator estimate. -/
theorem eventually_source_original_MEMORY_OLD_positive_margin434
    (CG : ℝ) (hCG : 0 ≤ CG) :
    ∀ᶠ L : ℝ in atTop, ∀ (G M : ℕ),
      (G : ℝ) ≤ CG * Real.log L → (M : ℝ) ≤ L →
      0 < ⌈L ^ 2 / 4⌉₊ ∧
      ⌈L ^ 2 / 4⌉₊ + G * ((2 * ⌈L ^ (0.52 : ℝ)⌉₊ + 1) * M) <
        ⌈L ^ 2⌉₊ := by
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    eventually_source_original_MEMORY_OLD_allowance_quarter434 CG hCG] with L hL hBudget
  intro G M hG hM
  have hL2 : 4 ≤ L ^ 2 := by nlinarith
  have hHlo : L ^ 2 / 4 ≤ (⌈L ^ 2 / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hHhi := Nat.ceil_lt_add_one (show 0 ≤ L ^ 2 / 4 by positivity)
  have hCut : L ^ 2 ≤ (⌈L ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hb := hBudget G M hG hM
  constructor
  · have hh : (0 : ℝ) < (⌈L ^ 2 / 4⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (⌈L ^ 2 / 4⌉₊ : ℝ) +
        ((G * ((2 * ⌈L ^ (0.52 : ℝ)⌉₊ + 1) * M) : ℕ) : ℝ) <
        (⌈L ^ 2⌉₊ : ℝ) := by linarith
    exact_mod_cast hh

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGhostAbsoluteMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 4000000

section Group
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- The complete absolute subset row of the literal restricted G.
Every OLD deletion/retention choice sums to one at rho=1. Only births
cost mass. No OLD-cardinality or fine-cell factor occurs. -/
theorem source_original_RESTRICTED_G_absolute_mass434
    (S : Finset (Atom P modulus)) (B : Finset P)
    (eta V : ℝ) (mu : P → ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hV : 0 ≤ V) (hmu : ∀ p,0 ≤ mu p) :
    (∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus S B,
      ‖sourceOriginalGroupPrimeBirthWeight434 modulus S
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus S B d)‖) =
      ∏ p ∈ B,(1+eta*V*mu p) := by
  have hnorm (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus S B) :
      ‖sourceOriginalGroupPrimeBirthWeight434 modulus S
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus S B d)‖ =
      (eta^d.1.1.card*(1-eta)^(S.card-d.1.1.card)) *
        ((eta*V)^d.2.1.card * ∏ p ∈ d.2.1,mu p) := by
    unfold sourceOriginalGroupPrimeBirthWeight434 sourceOriginalRestrictedPrimeBirthLift434
    rw [show (1:ℂ)-(eta:ℂ)=((1-eta:ℝ):ℂ) by simp]
    simp only [norm_mul,norm_pow,norm_neg,norm_prod,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg he,abs_of_nonneg hV,abs_of_nonneg (sub_nonneg.mpr he1),
      abs_of_nonneg (hmu _)]
    ring
  have hdel :
      (∑ a : {A : Finset (Atom P modulus) // A ∈ S.powerset},
        eta^a.1.card*(1-eta)^(S.card-a.1.card)) = 1 := by
    calc
      _ = ∑ a ∈ S.powerset,eta^a.card*(1-eta)^(S.card-a.card) := Finset.sum_coe_sort _ _
      _ = ∑ a ∈ S.powerset,(∏ z ∈ a,eta)*(∏ z ∈ S \ a,(1-eta)) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.prod_const,Finset.card_sdiff_of_subset (Finset.mem_powerset.mp ha)]
      _ = ∏ z ∈ S,(eta+(1-eta)) := (Finset.prod_add _ _ _).symm
      _ = 1 := by simp
  have hbirth :
      (∑ b : {A : Finset P // A ∈ B.powerset},
        (eta*V)^b.1.card * ∏ p ∈ b.1,mu p) = ∏ p ∈ B,(1+eta*V*mu p) := by
    calc
      _ = ∑ b ∈ B.powerset,(eta*V)^b.card * ∏ p ∈ b,mu p := Finset.sum_coe_sort _ _
      _ = ∑ b ∈ B.powerset,∏ p ∈ b,eta*V*mu p := by
        simp only [Finset.prod_mul_distrib,Finset.prod_const,mul_pow]
      _ = _ := (Finset.prod_one_add B).symm
  simp_rw [hnorm]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,hbirth]
  rw [← Finset.sum_mul,hdel,one_mul]
end Group

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)

/-- Actual all-group active G absolute coefficient mass. This is an
explicit calculated cost, not a norm premise on a joint continuation. -/
theorem source_original_ACTUAL_ACTIVE_G_absolute_mass434
    (q : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ sourceVisitEta q N i) (he1 : sourceVisitEta q N i ≤ 1)
    (hV : ∀ g,0 ≤ V g) (hmu : ∀ g p,0 ≤ mu g p) :
    (∑ b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
      ‖sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y
        q 1 N i V mu b‖) =
    ∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∉ background g),
      (1+sourceVisitEta q N i*V g*mu g p) := by
  have hq : (sourceVisitQ q N i:ℂ)=1-(sourceVisitEta q N i:ℂ) := by
    simp only [sourceVisitEta,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  let w := fun (g : BG) (d : SourceOriginalRestrictedPrimeBirthChoice434 (bm g)
      (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∉ background g))
      (Finset.univ.filter (fun p => p ∉ background g))) =>
    ‖sourceOriginalGroupPrimeBirthWeight434 (bm g) _
      (-((sourceVisitEta q N i:ℝ):ℂ)) (1-((sourceVisitEta q N i:ℝ):ℂ))
      (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)) (fun p => (mu g p:ℂ))
      (sourceOriginalRestrictedPrimeBirthLift434 (bm g) _ _ d)‖
  have hf : (∑ b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
      ∏ g,w g (b g)) = ∏ g,∑ d,w g d := by
    convert (Fintype.prod_sum w).symm using 1 <;> congr <;> exact Subsingleton.elim _ _
  unfold sourceOriginalGhostActiveCoefficient434
  simp only [norm_prod,Complex.ofReal_one,one_pow,div_one,hq]
  change (∑ b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
    ∏ g,w g (b g)) = _
  rw [hf]
  apply Finset.prod_congr rfl
  intro g hg
  exact source_original_RESTRICTED_G_absolute_mass434 (bm g) _ _
    (sourceVisitEta q N i) (V g) (mu g) he he1 (hV g) (hmu g)

/-- The corresponding actual background mass, retaining its own pool. -/
theorem source_original_ACTUAL_BACKGROUND_G_absolute_mass434
    (q : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ sourceVisitEta q N i) (he1 : sourceVisitEta q N i ≤ 1)
    (hV : ∀ g,0 ≤ V g) (hmu : ∀ g p,0 ≤ mu g p) :
    (∑ a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y,
      ‖sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y
        q 1 N i V mu a‖) =
    ∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∈ background g),
      (1+sourceVisitEta q N i*V g*mu g p) := by
  have hq : (sourceVisitQ q N i:ℂ)=1-(sourceVisitEta q N i:ℂ) := by
    simp only [sourceVisitEta,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  let w := fun (g : BG) (d : SourceOriginalRestrictedPrimeBirthChoice434 (bm g)
      (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ background g))
      (Finset.univ.filter (fun p => p ∈ background g))) =>
    ‖sourceOriginalGroupPrimeBirthWeight434 (bm g) _
      (-((sourceVisitEta q N i:ℝ):ℂ)) (1-((sourceVisitEta q N i:ℝ):ℂ))
      (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)) (fun p => (mu g p:ℂ))
      (sourceOriginalRestrictedPrimeBirthLift434 (bm g) _ _ d)‖
  have hf : (∑ b : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y,
      ∏ g,w g (b g)) = ∏ g,∑ d,w g d := by
    convert (Fintype.prod_sum w).symm using 1 <;> congr <;> exact Subsingleton.elim _ _
  unfold sourceOriginalGhostBackgroundCoefficient434
  simp only [norm_prod,Complex.ofReal_one,one_pow,div_one,hq]
  change (∑ b : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y,
    ∏ g,w g (b g)) = _
  rw [hf]
  apply Finset.prod_congr rfl
  intro g hg
  exact source_original_RESTRICTED_G_absolute_mass434 (bm g) _ _
    (sourceVisitEta q N i) (V g) (mu g) he he1 (hV g) (hmu g)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualMixedAbsoluteRows -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 10000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))
local notation "B" => sourceOriginalNumericBackground434 BP bm background

/-- Positive companion of the ACTUAL tilted G, with its unchanged
numerical gates and outputs. Only background births are tilted. -/
def sourceOriginalAbsoluteBackgroundTiltG434
    (y : FullPhysicalOutput SP sm BP bm M)
    (q rho u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ) : ℝ :=
  ∑ ab : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y ×
      SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
    if ((∀ g,∀ p ∈ (ab.1 g).2.1,bm g p ∉ seen ∩ B) ∧
        (∀ g,∀ p ∈ (ab.2 g).2.1,bm g p ∉ seen \ B)) then
      (‖sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V
          (fun g p => u*mu g p) ab.1‖ *
        ‖sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu ab.2‖) *
      A (sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y ab.1 ab.2)
        (((seen ∩ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.1 g).2.1)) ∪
          ((seen \ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.2 g).2.1)))
    else 0

theorem source_original_ACTUAL_TILTED_G_absolute_majorant434
    (y : FullPhysicalOutput SP sm BP bm M)
    (q rho u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ)
    (hFA : ∀ out st,‖F out st‖ ≤ A out st) :
    ‖sourceOriginalActualBackgroundBirthTiltG434 BP bm SP sm M background y
      q rho u N i V mu seen F‖ ≤
    sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y q rho u N i V mu seen A := by
  unfold sourceOriginalActualBackgroundBirthTiltG434 sourceOriginalAbsoluteBackgroundTiltG434
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro ab hab
  split_ifs
  · simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hFA _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · simp only [norm_zero,le_refl]

theorem source_original_ABSOLUTE_G_mono434
    (y : FullPhysicalOutput SP sm BP bm M)
    (q rho u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (A C : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ)
    (hAC : ∀ out st,A out st ≤ C out st) :
    sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y q rho u N i V mu seen A ≤
    sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y q rho u N i V mu seen C := by
  unfold sourceOriginalAbsoluteBackgroundTiltG434
  apply Finset.sum_le_sum
  intro ab hab
  split_ifs
  · exact mul_le_mul_of_nonneg_left (hAC _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · rfl

theorem source_original_ABSOLUTE_G_smul434
    (y : FullPhysicalOutput SP sm BP bm M)
    (q rho u c : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (A : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℝ) :
    sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y q rho u N i V mu seen
      (fun out st => c*A out st) =
    c*sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y q rho u N i V mu seen A := by
  unfold sourceOriginalAbsoluteBackgroundTiltG434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  split_ifs <;> ring

variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Actual E frame companion: all admissible OLD injections, original
joint K and both phases are evaluated before taking the coefficient norm. -/
def sourceOriginalAbsoluteEFrame434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) : ℝ :=
  ∑ f : {f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r //
    sourceOriginalSourceEFrameAdmissible434 SP sm BP bm J ell m cap patterns x seen o k r f},
    let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f.1
    ‖sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x z‖ *
    A (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
      (seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset)

theorem source_original_ACTUAL_E_absolute_majorant434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hFA : ∀ out st,‖F out st‖ ≤ A out st) :
    ‖sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r F‖ ≤
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r A := by
  unfold sourceOriginalSourceEFrameFibreRow434 sourceOriginalAbsoluteEFrame434
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro f hf
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hFA _ _) (norm_nonneg _)

theorem source_original_ABSOLUTE_E_mono434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (A C : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hAC : ∀ out st,A out st ≤ C out st) :
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r A ≤
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r C := by
  unfold sourceOriginalAbsoluteEFrame434
  exact Finset.sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left (hAC _ _) (norm_nonneg _))

theorem source_original_ABSOLUTE_E_smul434
    (q rho c : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) :
    sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r (fun out st => c*A out st) =
    c*sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r A := by
  unfold sourceOriginalAbsoluteEFrame434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  dsimp only
  ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGCostGrowth -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 8000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))

def sourceOriginalActualSplitGBirthCost434
    (q u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℝ :=
  (∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∈ background g),
    (1+sourceVisitEta q N i*V g*(u*mu g p))) *
  (∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∉ background g),
    (1+sourceVisitEta q N i*V g*mu g p))

/-- Explicit bound on the ACTUAL complete G companion, with both real
numeric birth gates retained on the left. No continuation norm premise. -/
theorem source_original_ACTUAL_TILTED_G_mass_bound434
    (y : FullPhysicalOutput SP sm BP bm M)
    (q u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ sourceVisitEta q N i) (he1 : sourceVisitEta q N i ≤ 1)
    (hu : 0 ≤ u) (hV : ∀ g,0 ≤ V g) (hmu : ∀ g p,0 ≤ mu g p)
    (seen : Finset ℕ) :
    sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y q 1 u N i V mu seen
      (fun _ _ => 1) ≤ sourceOriginalActualSplitGBirthCost434 BP background q u N i V mu := by
  unfold sourceOriginalAbsoluteBackgroundTiltG434
  calc
    _ ≤ ∑ ab : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y ×
        SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
      ‖sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q 1 N i V
          (fun g p => u*mu g p) ab.1‖ *
        ‖sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q 1 N i V mu ab.2‖ := by
      apply Finset.sum_le_sum
      intro ab hab
      split_ifs
      · simp only [mul_one,le_refl]
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = (∑ a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y,
      ‖sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q 1 N i V
        (fun g p => u*mu g p) a‖) *
      (∑ b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
      ‖sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q 1 N i V mu b‖) := by
      simp only [Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
      exact Finset.sum_comm
    _ = _ := by
      rw [source_original_ACTUAL_BACKGROUND_G_absolute_mass434 SP sm BP bm M background y
          q N i V (fun g p => u*mu g p) he he1 hV (fun g p => mul_nonneg hu (hmu g p)),
        source_original_ACTUAL_ACTIVE_G_absolute_mass434 SP sm BP bm M background y
          q N i V mu he he1 hV hmu]
      rfl

/-- Growth of the actual G cost, uniform in the background pool, OLD
state, seen and all finite carrier sizes. This is a growing exponential,
not a saving estimate. -/
theorem source_original_ACTUAL_G_birth_cost_exp434
    (q u : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ sourceVisitEta q N i) (hu : 1 ≤ u)
    (hV : ∀ g,0 ≤ V g) (hmu : ∀ g p,0 ≤ mu g p) :
    sourceOriginalActualSplitGBirthCost434 BP background q u N i V mu ≤
      Real.exp (u*sourceVisitEta q N i*(∑ g,∑ p,V g*mu g p)) := by
  let eta := sourceVisitEta q N i
  let w := fun g p => eta*V g*(u*mu g p)
  have hu0 : 0≤u := zero_le_one.trans hu
  have hw (g : BG) (p : BP g) : 0 ≤ w g p :=
    mul_nonneg (mul_nonneg he (hV g)) (mul_nonneg hu0 (hmu g p))
  have hold (g : BG) (p : BP g) : 0 ≤ eta*V g*mu g p :=
    mul_nonneg (mul_nonneg he (hV g)) (hmu g p)
  have hle (g : BG) (p : BP g) : 1+eta*V g*mu g p ≤ 1+w g p := by
    have hh := mul_le_mul_of_nonneg_right hu (hold g p)
    dsimp only [w]
    nlinarith only [hh]
  have hA :
      (∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∉ background g),(1+eta*V g*mu g p)) ≤
      ∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∉ background g),(1+w g p) := by
    apply Finset.prod_le_prod₀
    · intro g hg
      exact Finset.prod_nonneg (fun p hp => add_nonneg zero_le_one (hold g p))
    · intro g hg
      exact Finset.prod_le_prod₀ (fun p hp => add_nonneg zero_le_one (hold g p))
        (fun p hp => hle g p)
  have hsum : (∑ g,∑ p,w g p) = u*eta*(∑ g,∑ p,V g*mu g p) := by
    simp only [Finset.mul_sum,w]
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sum_congr rfl
    intro p hp
    ring
  change
    (∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∈ background g),(1+w g p)) *
    (∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∉ background g),(1+eta*V g*mu g p)) ≤ _
  calc
    _ ≤ (∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∈ background g),(1+w g p)) *
        (∏ g,∏ p ∈ Finset.univ.filter (fun p => p ∉ background g),(1+w g p)) :=
      mul_le_mul_of_nonneg_left hA
        (Finset.prod_nonneg (fun g hg => Finset.prod_nonneg (fun p hp =>
          add_nonneg zero_le_one (hw g p))))
    _ = ∏ g,∏ p,(1+w g p) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro g hg
      exact Finset.prod_filter_mul_prod_filter_not _ _ _
    _ ≤ ∏ g,∏ p,Real.exp (w g p) := by
      apply Finset.prod_le_prod₀
      · intro g hg
        exact Finset.prod_nonneg (fun p hp => add_nonneg zero_le_one (hw g p))
      · intro g hg
        exact Finset.prod_le_prod₀ (fun p hp => add_nonneg zero_le_one (hw g p))
          (fun p hp => by simpa only [add_comm] using Real.add_one_le_exp (w g p))
    _ = Real.exp (∑ g,∑ p,w g p) := by simp only [Real.exp_sum]
    _ = _ := by rw [hsum]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualGSourceBoxCost -/

section

open scoped BigOperators Classical
open Filter
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Source mu-tilde has total G-birth intensity bounded by twice the
numerical harmonic mass, once the literal source baseline is >=1/2. -/
theorem source_original_ACTUAL_source_mu_intensity434
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (q : ℝ) (N : ℕ) (V : BG → ℝ) (hV : ∀ g,0<V g)
    (hb : ∀ g p,(1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p) :
    (∑ g,∑ p,V g*physicalSourceMuTilde BP bm q N V g p) ≤
      2*(∑ g,∑ p,1/(bm g p:ℝ)) := by
  have hp (g : BG) (p : BP g) : (0:ℝ)<bm g p := by exact_mod_cast NeZero.pos (bm g p)
  have hb0 (g : BG) (p : BP g) : 0<physicalSourceBaseline BP bm q N g p := by
    have hh := hb g p
    linarith
  have hh (g : BG) (p : BP g) :
      V g*physicalSourceMuTilde BP bm q N V g p ≤ 2*(1/(bm g p:ℝ)) := by
    have he : V g*physicalSourceMuTilde BP bm q N V g p =
        1/((bm g p:ℝ)*physicalSourceBaseline BP bm q N g p) := by
      unfold physicalSourceMuTilde
      field_simp [ne_of_gt (hV g),ne_of_gt (hp g p),ne_of_gt (hb0 g p)]
    rw [he]
    have ht : 1/((bm g p:ℝ)*physicalSourceBaseline BP bm q N g p) ≤ 2/(bm g p:ℝ) := by
      rw [div_le_div_iff₀ (mul_pos (hp g p) (hb0 g p)) (hp g p)]
      have ht := mul_le_mul_of_nonneg_left (hb g p) (hp g p).le
      nlinarith only [ht]
    simpa only [mul_one_div] using ht
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun g hg => Finset.sum_le_sum (fun p hp => hh g p))

/-- Uniform actual G source-box cost. The threshold is before EVERY
moving family, background pool, physical state, seen, visit and u>=1.
It applies to the full actual G companion, not a resummed model. -/
theorem eventually_source_original_ACTUAL_G_source_box_cost434
    (c : ℝ) (hc : 0<c) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {SG : Type} [Fintype SG] [DecidableEq SG]
      (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
      (q : ℝ) (hq : 0≤q) (hq1 : q≤1) (V : BG → ℝ) (hV : ∀ g,0<V g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hmax : ∀ g p,(bm g p:ℝ) ≤ Real.exp (Real.sqrt L))
      (M : ℕ) (background : (g : BG) → Finset (BP g))
      (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ) (i : ℕ)
      (u : ℝ) (hu : 1≤u),
      sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm M background y
        q 1 u (2*Nat.ceil (L^(0.52:ℝ))) i V
        (physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V)
        seen (fun _ _ => 1) ≤
      Real.exp (2*u*sourceVisitEta q (2*Nat.ceil (L^(0.52:ℝ))) i*(1+Real.sqrt L)) := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro SG _ _ SP _ _ sm _ BG _ _ BP _ _ bm _ hi q hq hq1 V hV hmin hmax
    M background y seen i u hu
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP bm q N V
  have hb (g : BG) (p : BP g) : (1:ℝ)/2 ≤ physicalSourceBaseline BP bm q N g p :=
    (source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p
      (hL (bm g p) (hmin g p))).1
  have hb0 (g : BG) (p : BP g) : 0<physicalSourceBaseline BP bm q N g p := by
    have hh := hb g p
    linarith
  have hmu (g : BG) (p : BP g) : 0 ≤ mu g p := by
    have hv := hV g
    have hp : (0:ℝ)<bm g p := by exact_mod_cast NeZero.pos (bm g p)
    have hb' := hb0 g p
    dsimp only [mu,physicalSourceMuTilde]
    positivity
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  have hsigma : (∑ g,∑ p,1/(bm g p:ℝ)) ≤ 1+Real.sqrt L := by
    have hh := source_original_GHOST_numeric_harmonic_box434
      (fun x : Sigma BP => bm x.1 x.2) Finset.univ hi
      (fun x _ => NeZero.pos _) (Real.exp (Real.sqrt L))
      (Real.one_le_exp_iff.mpr (Real.sqrt_nonneg L)) (fun x _ => hmax x.1 x.2)
    simpa only [Finset.sum_map_toList,Fintype.sum_sigma,Real.log_exp] using hh
  have hmass : (∑ g,∑ p,V g*mu g p) ≤ 2*(1+Real.sqrt L) :=
    (source_original_ACTUAL_source_mu_intensity434 BP bm q N V hV hb).trans
      (mul_le_mul_of_nonneg_left hsigma (by norm_num))
  apply (source_original_ACTUAL_TILTED_G_mass_bound434 SP sm BP bm M background y
    q u N i V mu he.1 he.2 (zero_le_one.trans hu) (fun g => (hV g).le) hmu seen).trans
  apply (source_original_ACTUAL_G_birth_cost_exp434 BP background q u N i V mu he.1 hu
    (fun g => (hV g).le) hmu).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hmass (mul_nonneg (zero_le_one.trans hu) he.1)
  dsimp only [N] at hh ⊢
  nlinarith only [hh]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualBirthTailCostBudget -/

section

open Filter Real
open scoped BigOperators
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A nonempty scalar budget for the explicit G and rho=1 BIG costs.
u=2 and H=ceil(L^2/4) are concrete. The threshold is before the moving
group count. This is NOT yet a bound on the full mixed root: its outer
sums and background-dependent histories must still be assembled. -/
theorem eventually_source_original_ACTUAL_birth_cost_budget434
    (C CG CE B : ℝ) (hC : 1 ≤ C) (hCG : 0 ≤ CG) (hCE : 0 ≤ CE) (hB : 0 ≤ B)
    (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℕ, (G:ℝ) ≤ CG*Real.log L →
      ((2:ℝ)^Nat.ceil (L^2/4))⁻¹ *
      Real.exp (4*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)*(1+Real.sqrt L)) *
      (C*Real.exp (Real.sqrt L))^(d*G*(2*Nat.ceil (L^(0.52:ℝ)))) *
      L^(CE*((2*Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ)) ≤ L^(-B) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  let K := 40+10*(d:ℝ)*CG*(1+Real.log C)+10*CE+2*B
  have hK : 0 ≤ K := by dsimp only [K];positivity
  have hp : ∀ᶠ L : ℝ in atTop, 4*K/Real.log 2 ≤ L^(0.48:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<0.48)).eventually
      (eventually_ge_atTop (4*K/Real.log 2))
  filter_upwards [eventually_ge_atTop (1:ℝ),hp] with L hL hp
  intro G hG
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let H := Nat.ceil (L^2/4)
  let T := L^(0.52:ℝ)*L
  have hP0 : 0 ≤ L^(0.52:ℝ) := Real.rpow_nonneg hLp.le _
  have hP1 : 1 ≤ L^(0.52:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hs0 := Real.sqrt_nonneg L
  have hs1 : 1 ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hsL : Real.sqrt L ≤ L := by nlinarith only [Real.sq_sqrt hLp.le,hs1]
  have hLog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hLog : Real.log L ≤ 2*Real.sqrt L := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLp)
    rw [Real.log_sqrt hLp.le] at hh
    linarith
  have hN1 : ((N+1:ℕ):ℝ) ≤ 5*L^(0.52:ℝ) := by
    have hh := (Nat.ceil_lt_add_one hP0).le
    dsimp only [N]
    push_cast
    linarith
  have hN : (N:ℝ) ≤ 5*L^(0.52:ℝ) := by push_cast at hN1;linarith
  have hG' : (G:ℝ) ≤ 2*CG*Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_left hLog hCG
    nlinarith only [hG,hh]
  have hBase : Real.log C+Real.sqrt L ≤ (1+Real.log C)*Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_left hs1 hlC
    nlinarith only [hh]
  have hGcost : 4*((N+1:ℕ):ℝ)*(1+Real.sqrt L) ≤ 40*T := by
    calc
      _ ≤ 4*(5*L^(0.52:ℝ))*(2*L) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hN1 (by norm_num)
        · linarith
        · positivity
        · positivity
      _ = _ := by dsimp only [T];ring
  have hBig : ((d*G*N:ℕ):ℝ)*(Real.log C+Real.sqrt L) ≤
      10*(d:ℝ)*CG*(1+Real.log C)*T := by
    calc
      _ = (d:ℝ)*(G:ℝ)*(N:ℝ)*(Real.log C+Real.sqrt L) := by push_cast;ring
      _ ≤ (d:ℝ)*(2*CG*Real.sqrt L)*(5*L^(0.52:ℝ))*
          ((1+Real.log C)*Real.sqrt L) := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hG' (Nat.cast_nonneg _)
          · exact hN
          · positivity
          · positivity
        · exact hBase
        · positivity
        · positivity
      _ = _ := by
        dsimp only [T]
        calc
          _ = 10*(d:ℝ)*CG*(1+Real.log C)*L^(0.52:ℝ)*(Real.sqrt L)^2 := by ring
          _ = _ := by rw [Real.sq_sqrt hLp.le];ring
  have hSmall : CE*(N:ℝ)*Real.log L ≤ 10*CE*T := by
    calc
      _ ≤ CE*(5*L^(0.52:ℝ))*(2*L) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hN hCE
        · exact hLog.trans (mul_le_mul_of_nonneg_left hsL (by norm_num))
        · exact hLog0
        · positivity
      _ = _ := by dsimp only [T];ring
  have hGoal : B*Real.log L ≤ 2*B*T := by
    have hLT : L ≤ T := by
      dsimp only [T]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hP1 hLp.le
    have hh := hLog.trans (mul_le_mul_of_nonneg_left (hsL.trans hLT) (by norm_num))
    have hh' := mul_le_mul_of_nonneg_left hh hB
    nlinarith only [hh']
  have hScale : K*T ≤ Real.log 2*(L^2/4) := by
    have hp' : K ≤ (Real.log 2/4)*L^(0.48:ℝ) := by
      have hh := (div_le_iff₀ hlog2).mp hp
      nlinarith only [hh]
    have hT0 : 0 ≤ T := mul_nonneg hP0 hLp.le
    have hh := mul_le_mul_of_nonneg_right hp' hT0
    have he : L^(0.48:ℝ)*T=L^2 := by
      dsimp only [T]
      rw [←mul_assoc,←Real.rpow_add hLp]
      norm_num
      ring
    calc
      _ ≤ (Real.log 2/4)*(L^(0.48:ℝ)*T) := by nlinarith only [hh]
      _ = _ := by rw [he];ring
  have hH : L^2/4 ≤ (H:ℝ) := Nat.le_ceil _
  have hH' := mul_le_mul_of_nonneg_left hH hlog2.le
  have hBudget :
      -(Real.log 2*(H:ℝ)) + 4*((N+1:ℕ):ℝ)*(1+Real.sqrt L) +
      ((d*G*N:ℕ):ℝ)*(Real.log C+Real.sqrt L) +
      CE*(N:ℝ)*Real.log L ≤ -B*Real.log L := by
    dsimp only [K] at hScale
    nlinarith only [hGcost,hBig,hSmall,hGoal,hScale,hH']
  have hpow (a : ℝ) (ha : 0 < a) (n : ℕ) :
      a^n=Real.exp (Real.log a*(n:ℝ)) := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos ha]
  have hBaseLog : Real.log (C*Real.exp (Real.sqrt L))=Real.log C+Real.sqrt L := by
    rw [Real.log_mul (ne_of_gt hCp) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
  change ((2:ℝ)^H)⁻¹ * Real.exp (4*((N+1:ℕ):ℝ)*(1+Real.sqrt L)) *
      (C*Real.exp (Real.sqrt L))^(d*G*N) * L^(CE*(N:ℝ)) ≤ L^(-B)
  rw [hpow 2 (by norm_num) H,←Real.exp_neg,
    hpow (C*Real.exp (Real.sqrt L)) (mul_pos hCp (Real.exp_pos _)) (d*G*N),
    hBaseLog,Real.rpow_def_of_pos hLp,Real.rpow_def_of_pos hLp,
    ←Real.exp_add,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hBudget]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFullBirthBudget -/

section

open Filter Real
open scoped BigOperators
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The complete scalar birth-tail cost, INCLUDING the initial SMALL boundary.
u=2 and H=ceil(L^2/4). Every positive exponent is bounded by K L^(7/4).
All constants precede the threshold, which precedes the moving group count. -/
theorem eventually_source_original_ACTUAL_full_birth_cost_budget434
    (C CG CE CS v B : ℝ) (hC : 1 ≤ C) (hCG : 0 ≤ CG) (hCE : 0 ≤ CE)
    (hCS : 0 ≤ CS) (hv : 0 < v) (hB : 0 ≤ B)
    (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℕ, (G:ℝ) ≤ CG*Real.log L →
      ((2:ℝ)^Nat.ceil (L^2/4))⁻¹ *
      Real.exp (CS*L*Real.log L*(Real.sqrt L+Real.log (max 1 v⁻¹))) *
      Real.exp (4*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ)*(1+Real.sqrt L)) *
      (C*Real.exp (Real.sqrt L))^(d*G*(2*Nat.ceil (L^(0.52:ℝ)))) *
      L^(CE*((2*Nat.ceil (L^(0.52:ℝ)):ℕ):ℝ)) ≤ L^(-B) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  let A : ℝ := max 1 v⁻¹
  have hA1 : 1 ≤ A := le_max_left _ _
  have hlA : 0 ≤ Real.log A := Real.log_nonneg hA1
  let K := 40+10*(d:ℝ)*CG*(1+Real.log C)+10*CE+2*B+4*CS*(1+Real.log A)
  have hK : 0 ≤ K := by dsimp only [K];positivity
  have hp : ∀ᶠ L : ℝ in atTop, 4*K/Real.log 2 ≤ L^(0.25:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<0.25)).eventually
      (eventually_ge_atTop (4*K/Real.log 2))
  filter_upwards [eventually_ge_atTop (1:ℝ),hp] with L hL hp
  intro G hG
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let H := Nat.ceil (L^2/4)
  let T := L^(0.75:ℝ)*L
  have hP0 : 0 ≤ L^(0.75:ℝ) := Real.rpow_nonneg hLp.le _
  have hP1 : 1 ≤ L^(0.75:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hs0 := Real.sqrt_nonneg L
  have hs1 : 1 ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hsL : Real.sqrt L ≤ L := by nlinarith only [Real.sq_sqrt hLp.le,hs1]
  have hLog0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have hLog : Real.log L ≤ 2*Real.sqrt L := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLp)
    rw [Real.log_sqrt hLp.le] at hh
    linarith
  have hN1 : ((N+1:ℕ):ℝ) ≤ 5*L^(0.75:ℝ) := by
    have hh := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg hLp.le (0.52:ℝ))).le
    have hpw : L^(0.52:ℝ) ≤ L^(0.75:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    dsimp only [N]
    push_cast
    linarith
  have hN : (N:ℝ) ≤ 5*L^(0.75:ℝ) := by push_cast at hN1;linarith
  have hG' : (G:ℝ) ≤ 2*CG*Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_left hLog hCG
    nlinarith only [hG,hh]
  have hBase : Real.log C+Real.sqrt L ≤ (1+Real.log C)*Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_left hs1 hlC
    nlinarith only [hh]
  have hGcost : 4*((N+1:ℕ):ℝ)*(1+Real.sqrt L) ≤ 40*T := by
    calc
      _ ≤ 4*(5*L^(0.75:ℝ))*(2*L) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hN1 (by norm_num)
        · linarith
        · positivity
        · positivity
      _ = _ := by dsimp only [T];ring
  have hBig : ((d*G*N:ℕ):ℝ)*(Real.log C+Real.sqrt L) ≤
      10*(d:ℝ)*CG*(1+Real.log C)*T := by
    calc
      _ = (d:ℝ)*(G:ℝ)*(N:ℝ)*(Real.log C+Real.sqrt L) := by push_cast;ring
      _ ≤ (d:ℝ)*(2*CG*Real.sqrt L)*(5*L^(0.75:ℝ))*
          ((1+Real.log C)*Real.sqrt L) := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hG' (Nat.cast_nonneg _)
          · exact hN
          · positivity
          · positivity
        · exact hBase
        · positivity
        · positivity
      _ = _ := by
        dsimp only [T]
        calc
          _ = 10*(d:ℝ)*CG*(1+Real.log C)*L^(0.75:ℝ)*(Real.sqrt L)^2 := by ring
          _ = _ := by rw [Real.sq_sqrt hLp.le];ring
  have hSmall : CE*(N:ℝ)*Real.log L ≤ 10*CE*T := by
    calc
      _ ≤ CE*(5*L^(0.75:ℝ))*(2*L) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hN hCE
        · exact hLog.trans (mul_le_mul_of_nonneg_left hsL (by norm_num))
        · exact hLog0
        · positivity
      _ = _ := by dsimp only [T];ring
  have hGoal : B*Real.log L ≤ 2*B*T := by
    have hLT : L ≤ T := by
      dsimp only [T]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hP1 hLp.le
    have hh := hLog.trans (mul_le_mul_of_nonneg_left (hsL.trans hLT) (by norm_num))
    have hh' := mul_le_mul_of_nonneg_left hh hB
    nlinarith only [hh']
  have hLogQuarter : Real.log L ≤ 4*L^(0.25:ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hLp (0.25:ℝ))
    rw [Real.log_rpow hLp] at hh
    linarith
  have hSmallBase : Real.sqrt L+Real.log A ≤ (1+Real.log A)*Real.sqrt L := by
    have hh := mul_le_mul_of_nonneg_left hs1 hlA
    nlinarith only [hh]
  have hBoundary : CS*L*Real.log L*(Real.sqrt L+Real.log A) ≤
      4*CS*(1+Real.log A)*T := by
    calc
      _ ≤ CS*L*(4*L^(0.25:ℝ))*((1+Real.log A)*Real.sqrt L) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hLogQuarter (mul_nonneg hCS hLp.le)
        · exact hSmallBase
        · positivity
        · positivity
      _ = _ := by
        have he : L^(0.25:ℝ)*Real.sqrt L = L^(0.75:ℝ) := by
          rw [Real.sqrt_eq_rpow,←Real.rpow_add hLp]
          norm_num
        dsimp only [T]
        calc
          _ = 4*CS*(1+Real.log A)*L*(L^(0.25:ℝ)*Real.sqrt L) := by ring
          _ = _ := by rw [he];ring
  have hScale : K*T ≤ Real.log 2*(L^2/4) := by
    have hp' : K ≤ (Real.log 2/4)*L^(0.25:ℝ) := by
      have hh := (div_le_iff₀ hlog2).mp hp
      nlinarith only [hh]
    have hT0 : 0 ≤ T := mul_nonneg hP0 hLp.le
    have hh := mul_le_mul_of_nonneg_right hp' hT0
    have he : L^(0.25:ℝ)*T=L^2 := by
      dsimp only [T]
      rw [←mul_assoc,←Real.rpow_add hLp]
      norm_num
      ring
    calc
      _ ≤ (Real.log 2/4)*(L^(0.25:ℝ)*T) := by nlinarith only [hh]
      _ = _ := by rw [he];ring
  have hH : L^2/4 ≤ (H:ℝ) := Nat.le_ceil _
  have hH' := mul_le_mul_of_nonneg_left hH hlog2.le
  have hBudget :
      -(Real.log 2*(H:ℝ)) + 4*((N+1:ℕ):ℝ)*(1+Real.sqrt L) +
      ((d*G*N:ℕ):ℝ)*(Real.log C+Real.sqrt L) +
      CE*(N:ℝ)*Real.log L +
      CS*L*Real.log L*(Real.sqrt L+Real.log A) ≤ -B*Real.log L := by
    dsimp only [K] at hScale
    nlinarith only [hGcost,hBig,hSmall,hGoal,hBoundary,hScale,hH']
  have hpow (a : ℝ) (ha : 0 < a) (n : ℕ) :
      a^n=Real.exp (Real.log a*(n:ℝ)) := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos ha]
  have hBaseLog : Real.log (C*Real.exp (Real.sqrt L))=Real.log C+Real.sqrt L := by
    rw [Real.log_mul (ne_of_gt hCp) (ne_of_gt (Real.exp_pos _)),Real.log_exp]
  change ((2:ℝ)^H)⁻¹ *
      Real.exp (CS*L*Real.log L*(Real.sqrt L+Real.log A)) * Real.exp (4*((N+1:ℕ):ℝ)*(1+Real.sqrt L)) *
      (C*Real.exp (Real.sqrt L))^(d*G*N) * L^(CE*(N:ℝ)) ≤ L^(-B)
  rw [hpow 2 (by norm_num) H,←Real.exp_neg,
    hpow (C*Real.exp (Real.sqrt L)) (mul_pos hCp (Real.exp_pos _)) (d*G*N),
    hBaseLog,Real.rpow_def_of_pos hLp,Real.rpow_def_of_pos hLp,
    ←Real.exp_add,←Real.exp_add,←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hBudget]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualMixedAbsoluteChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 12000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (background : (g : BG) → Finset (BP g))
local notation "B" => sourceOriginalNumericBackground434 BP bm background

def sourceOriginalAbsoluteBackgroundChain434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ) :
    (n : ℕ) → SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n →
    (start : ℕ) → FullPhysicalOutput SP sm BP bm (J+ell) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ) →
    (FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
  | 0,_,start,_,F => fun y seen =>
      sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm (J+ell) background y
        q 1 u N start V mu seen F
  | n+1,(r,h),start,sk,F => fun y seen =>
      sourceOriginalAbsoluteBackgroundTiltG434 SP sm BP bm (J+ell) background y
        q 1 u N start V mu seen (fun yg sg =>
          let z := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap
            (sourceOriginalRemovePendingBackground434 SP sm BP bm (J+ell) background yg)
          sourceOriginalAbsoluteEFrame434 SP sm BP bm J ell m cap patterns
            q 1 Vs V mu
            (memoryOrientationK BP J ell m patterns K (physicalAlternatingSign start))
            zeta theta (physicalAlternatingSign start) k z (sg \ B) r
            (fun out s =>
              sourceOriginalAbsoluteBackgroundChain434 q u Vs V mu K zeta theta k N n h
                (start+1) (sourceOriginalFrameTargetSkeleton434 SP sm BP bm J ell m patterns r) F
                (sourceOriginalAttachPendingBackground434 SP sm BP bm J ell background yg
                  (sourceOriginalActiveFrameStep434 SP sm BP bm J ell m cap patterns sk r
                    (physicalAlternatingSign start) k) out) (s ∪ (sg ∩ B))))


/-- Entrywise absolute majorant for the FULL actual branching mixed
history. It keeps every original gate, dependent E fibre, joint K and
physical output; no assumed bound on the active continuation is used. -/
theorem source_original_ACTUAL_MIXED_absolute_majorant434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hFA : ∀ out st,‖F out st‖ ≤ A out st)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    ‖sourceOriginalBirthTiltedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk F y seen‖ ≤
    sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk A y seen := by
  induction n generalizing start sk y seen with
  | zero =>
      exact source_original_ACTUAL_TILTED_G_absolute_majorant434
        SP sm BP bm (J+ell) background y q 1 u N start V mu seen F A hFA
  | succ n ih =>
      rcases h with ⟨r,h⟩
      dsimp only [sourceOriginalBirthTiltedBackgroundChain434,sourceOriginalAbsoluteBackgroundChain434]
      apply source_original_ACTUAL_TILTED_G_absolute_majorant434
      intro yg sg
      apply source_original_ACTUAL_E_absolute_majorant434
      intro out st
      exact ih h (start+1) _ _ _

/-- Positivity-based comparison on the same literal mixed chain. -/
theorem source_original_ACTUAL_MIXED_absolute_mono434
    (q u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (A C : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (hAC : ∀ out st,A out st ≤ C out st)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk A y seen ≤
    sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk C y seen := by
  induction n generalizing start sk y seen with
  | zero =>
      exact source_original_ABSOLUTE_G_mono434
        SP sm BP bm (J+ell) background y q 1 u N start V mu seen A C hAC
  | succ n ih =>
      rcases h with ⟨r,h⟩
      dsimp only [sourceOriginalAbsoluteBackgroundChain434]
      apply source_original_ABSOLUTE_G_mono434
      intro yg sg
      apply source_original_ABSOLUTE_E_mono434
      intro out st
      exact ih h (start+1) _ _ _

/-- Exact homogeneity, with no restriction on the scalar or depth. -/
theorem source_original_ACTUAL_MIXED_absolute_smul434
    (q u c : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (A : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℝ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ) :
    sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk (fun out st => c*A out st) y seen =
    c*sourceOriginalAbsoluteBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q u Vs V mu K zeta theta k N n h start sk A y seen := by
  induction n generalizing start sk y seen with
  | zero =>
      exact source_original_ABSOLUTE_G_smul434
        SP sm BP bm (J+ell) background y q 1 u c N start V mu seen A
  | succ n ih =>
      rcases h with ⟨r,h⟩
      dsimp only [sourceOriginalAbsoluteBackgroundChain434]
      simp_rw [ih h,source_original_ABSOLUTE_E_smul434,source_original_ABSOLUTE_G_smul434]
end Green64Analytic.CorrelationSquare

end

end

