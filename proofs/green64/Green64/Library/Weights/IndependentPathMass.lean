module

public import Green64.Library.Weights.IndependentRowMass
public import Green64.Library.Weights.Part072
public import Green64.Library.Correlation.Part019

@[expose] public section

/-!
# Weights / IndependentPathMass

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## IndependentPathMass -/

section

open scoped Classical
open scoped BigOperators
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

private theorem true_initial_mass
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hHs : ∀ g, Vs g = ∑ p : SP g, 1/(sm g p : ℝ))
    (hHb : ∀ g, Vb g = ∑ p : BP g, 1/(bm g p : ℝ)) :
    (∑ _x : MemoryIndependentState SP sm BP bm J ell,
      ‖(groupStateMass SP sm (J+ell) Vs : ℂ) *
        (groupStateMass BP bm (J+ell) Vb : ℂ)‖) ≤ 1 := by
  let ms := groupStateMass SP sm (J+ell) Vs
  let mb := groupStateMass BP bm (J+ell) Vb
  have hms : 0 ≤ ms :=
    Finset.prod_nonneg (fun g _ => (stateMass_positive (sm g) (J+ell) (Vs g) (hVs g)).le)
  have hmb : 0 ≤ mb :=
    Finset.prod_nonneg (fun g _ => (stateMass_positive (bm g) (J+ell) (Vb g) (hVb g)).le)
  have hs := source_original_ACTUAL_SMALL_group_harmonic_mass_le_one434
    SP sm (J+ell) Vs hVs hHs
  have hb := source_original_ACTUAL_SMALL_group_harmonic_mass_le_one434
    BP bm (J+ell) Vb hVb hHb
  have he :
      (∑ _x : MemoryIndependentState SP sm BP bm J ell,
        ‖(ms : ℂ) * (mb : ℂ)‖) =
      (∑ _s : GroupState SP sm (J+ell), ms) *
      (∑ _b : GroupState BP bm (J+ell), mb) := by
    rw [Fintype.sum_prod_type]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hms,
      abs_of_nonneg hmb]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  change (∑ _x : MemoryIndependentState SP sm BP bm J ell, ‖(ms : ℂ) * (mb : ℂ)‖) ≤ 1
  rw [he]
  calc
    _ ≤ 1 * 1 := mul_le_mul hs hb
      (Finset.sum_nonneg (fun _ _ => hmb)) (by norm_num)
    _ = 1 := one_mul 1

/-- The absolute sum is taken before adding different paths; the complete
dependent Nu/aux/permutation records remain in each source path index. -/
theorem b644_original_independent_absolute_paths434
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0 < q) (hq1 : q < 1)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hHb : ∀ g, ∑ p : BP g, 1/(bm g p : ℝ) = Vb g)
    (Knu : SourcePatternK BP J ell m patterns)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu, 0 ≤ Kcap nu)
    (hK : ∀ nu aux s t, ‖Knu nu aux s t‖ ≤ Kcap nu)
    (zeta theta : ℝ) (k : ℤ) (n start : ℕ)
    (x : MemoryIndependentState SP sm BP bm J ell) :
    (∑ p : memoryIndOriginalPathIndex SP sm BP bm J ell m patterns n,
      ‖memoryIndOriginalPathTerm SP sm BP bm J ell m patterns q Vs Vb Knu
        zeta theta k start (fun _ => 1) x n p‖) ≤
    (b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap)^n := by
  classical
  let C := b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap
  have hC := b644_independent_row_budget_nonneg434 J ell m patterns
    q Vs Vb hq hq1 hVs hVb Kcap hK0
  change _ ≤ C^n
  induction n generalizing start x with
  | zero =>
    change (∑ _p : PUnit, ‖(1 : ℂ)‖) ≤ C^0
    simp
  | succ n ih =>
    simp only [memoryIndOriginalPathIndex, memoryIndOriginalPathTerm,
      Fintype.sum_prod_type, norm_mul]
    calc
      _ ≤ ∑ a : MemoryIndependentOriginalRowIndex SP sm BP bm J ell m patterns,
        ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
          zeta theta (physicalAlternatingSign start) k x
          (memoryIndependentOriginalRowOutput SP sm BP bm J ell m patterns a)
          a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1‖ * C^n := by
        apply Finset.sum_le_sum
        intro a ha
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (ih (start+1)
          (memoryIndependentOriginalRowOutput SP sm BP bm J ell m patterns a)) (norm_nonneg _)
      _ = (∑ a : MemoryIndependentOriginalRowIndex SP sm BP bm J ell m patterns,
        ‖memoryIndependentRowScalar SP sm BP bm J ell m patterns q Vs Vb Knu
          zeta theta (physicalAlternatingSign start) k x
          (memoryIndependentOriginalRowOutput SP sm BP bm J ell m patterns a)
          a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1‖) * C^n :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ C * C^n := mul_le_mul_of_nonneg_right
        (b644_original_independent_absolute_row434 SP sm BP bm J ell m patterns
          q Vs Vb hq hq1 hVs hVb hHb Knu Kcap hK0 hK
          zeta theta (physicalAlternatingSign start) k x) (pow_nonneg hC n)
      _ = C^(n+1) := by rw [pow_succ]; ring

/-- Complete initial Haar/V masses are included. No cardinality of a
prime set, marked-state space or permutation family remains in the cost. -/
theorem b644_original_independent_absolute_root_paths434
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0 < q) (hq1 : q < 1)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hHs : ∀ g, Vs g = ∑ p : SP g, 1/(sm g p : ℝ))
    (hHb : ∀ g, Vb g = ∑ p : BP g, 1/(bm g p : ℝ))
    (Knu : SourcePatternK BP J ell m patterns)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu, 0 ≤ Kcap nu)
    (hK : ∀ nu aux s t, ‖Knu nu aux s t‖ ≤ Kcap nu)
    (zeta theta : ℝ) (k : ℤ) (n start : ℕ) :
    (∑ x : MemoryIndependentState SP sm BP bm J ell,
      ∑ p : memoryIndOriginalPathIndex SP sm BP bm J ell m patterns n,
      ‖(groupStateMass SP sm (J+ell) Vs : ℂ) *
        (groupStateMass BP bm (J+ell) Vb : ℂ) *
        memoryIndOriginalPathTerm SP sm BP bm J ell m patterns q Vs Vb Knu
          zeta theta k start (fun _ => 1) x n p‖) ≤
    (b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap)^n := by
  let mass : ℂ := (groupStateMass SP sm (J+ell) Vs : ℂ) *
    (groupStateMass BP bm (J+ell) Vb : ℂ)
  let C := b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap
  have hC := b644_independent_row_budget_nonneg434 J ell m patterns
    q Vs Vb hq hq1 hVs hVb Kcap hK0
  change (∑ x, ∑ p, ‖mass * _‖) ≤ C^n
  calc
    _ ≤ ∑ _x : MemoryIndependentState SP sm BP bm J ell, ‖mass‖ * C^n := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [norm_mul, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (b644_original_independent_absolute_paths434 SP sm BP bm J ell m patterns
          q Vs Vb hq hq1 hVs hVb (fun g => (hHb g).symm) Knu Kcap hK0 hK
          zeta theta k n start x) (norm_nonneg _)
    _ = (∑ _x : MemoryIndependentState SP sm BP bm J ell, ‖mass‖) * C^n :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * C^n := mul_le_mul_of_nonneg_right
      (true_initial_mass SP sm BP bm J ell Vs Vb hVs hVb hHs hHb) (pow_nonneg hC n)
    _ = C^n := one_mul _

local instance : Fintype (MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns) := by
  unfold MemoryPrimitiveEFrame
  infer_instance

/-- Literal unrestricted state/frame arrays, including every zero path
and every full Knu, satisfy the same absolute budget. -/
theorem b644_original_independent_absolute_array434
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0 < q) (hq1 : q < 1)
    (hVs : ∀ g, 0 < Vs g) (hVb : ∀ g, 0 < Vb g)
    (hHs : ∀ g, Vs g = ∑ p : SP g, 1/(sm g p : ℝ))
    (hHb : ∀ g, Vb g = ∑ p : BP g, 1/(bm g p : ℝ))
    (Knu : SourcePatternK BP J ell m patterns)
    (Kcap : Nu → ℝ) (hK0 : ∀ nu, 0 ≤ Kcap nu)
    (hK : ∀ nu aux s t, ‖Knu nu aux s t‖ ≤ Kcap nu)
    (zeta theta : ℝ) (k : ℤ) (n : ℕ) :
    (∑ states : Fin (n+1) → MemoryIndependentState SP sm BP bm J ell,
      ∑ frames : Fin n → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns,
      ‖memoryIndOriginalArrayWeight SP sm BP bm J ell m patterns
        q Vs Vb Knu zeta theta k states frames‖) ≤
    (b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap)^n := by
  let XP := MemoryIndependentState SP sm BP bm J ell ×
    memoryIndOriginalPathIndex SP sm BP bm J ell m patterns n
  let SF := (Fin (n+1) → MemoryIndependentState SP sm BP bm J ell) ×
    (Fin n → MemoryPrimitiveEFrame (SG := SG) BP J ell m patterns)
  let mass : ℂ := (groupStateMass SP sm (J+ell) Vs : ℂ) *
    (groupStateMass BP bm (J+ell) Vb : ℂ)
  let F (xp : XP) : ℝ := ‖mass *
    memoryIndOriginalPathTerm SP sm BP bm J ell m patterns
      q Vs Vb Knu zeta theta k 0 (fun _ => 1) xp.1 n xp.2‖
  let G (sf : SF) : ℝ := ‖memoryIndOriginalArrayWeight SP sm BP bm
    J ell m patterns q Vs Vb Knu zeta theta k sf.1 sf.2‖
  have he : (∑ xp : XP, F xp) = ∑ sf : SF, G sf := by
    apply Fintype.sum_equiv (memoryIndOriginalFullArrayEquiv SP sm BP bm
      J ell m patterns n) F G
    intro xp
    apply congrArg (fun z : ℂ => ‖z‖)
    unfold memoryIndOriginalArrayWeight
    rw [memory_ind_original_path_term_eq_chronological_product]
    apply congrArg (fun z : ℂ => mass*z)
    apply Finset.prod_congr rfl
    intro i hi
    rw [memory_ind_original_chronological_step_eq_readout]
    unfold memoryIndOriginalPathRowScalar
    simp only [Nat.zero_add]
    rfl
  have hb := b644_original_independent_absolute_root_paths434
    SP sm BP bm J ell m patterns q Vs Vb hq hq1 hVs hVb hHs hHb
    Knu Kcap hK0 hK zeta theta k n 0
  have hleft : (∑ xp : XP, F xp) ≤
      (b644IndependentRowBudget434 J ell m patterns q Vs Vb Kcap)^n := by
    dsimp only [XP]
    rw [Fintype.sum_prod_type]
    exact hb
  rw [he] at hleft
  dsimp only [SF] at hleft
  rw [Fintype.sum_prod_type] at hleft
  exact hleft
end Green64Analytic.CorrelationSquare

end

end

