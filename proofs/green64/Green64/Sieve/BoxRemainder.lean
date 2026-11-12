module

public import Green64.Sieve.BoxNormalization

@[expose] public section

/-!
# Explicit finite rectangle remainder

Bound the explicit finite error of the rectangle sieve using the
balanced side lengths. The resulting exponential bounds are smaller
than the scale of the main term.
-/

section

set_option maxHeartbeats 1800000
set_option autoImplicit false
open Filter
open scoped BigOperators Classical Topology
namespace Green64Analytic.Parity
open SourceBlockSieve SourceCRT

noncomputable def boxFiniteError (L T : ℝ) : ℝ :=
  let Z := ⌊(Real.exp (parityOriginalAssignmentTheta434 * L)) ^ (10 : ℝ)⌋₊
  (200 : ℝ) ^ 400 *
    sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L *
    (2 * T * (Z : ℝ) * Real.exp (L / 20) + 4 * (Z : ℝ) ^ 2 * Real.exp (L / 10)) *
    (1 + Real.log (Z : ℝ)) ^ 3

noncomputable def boxErrorConstant (Cside : ℝ) : ℝ :=
  8 * (200 : ℝ) ^ 400 * (2 * Cside + 4)

/-- The fixed numerical choice bounds the floor cutoff,
and also bounds its logarithm without changing the source Z. -/
theorem box_cutoff_bounds (L : ℝ) (hL : 1 ≤ L) :
    let Z := ⌊(Real.exp (parityOriginalAssignmentTheta434 * L)) ^ (10 : ℝ)⌋₊
    1 ≤ Z ∧ (Z : ℝ) ≤ Real.exp (L / 20) ∧
      0 ≤ 1 + Real.log (Z : ℝ) ∧
      (1 + Real.log (Z : ℝ)) ^ 3 ≤ 8 * L ^ 3 := by
  let Z := ⌊(Real.exp (parityOriginalAssignmentTheta434 * L)) ^ (10 : ℝ)⌋₊
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have ht0 : 0 < parityOriginalAssignmentTheta434 := by
    norm_num [parityOriginalAssignmentTheta434]
  have ht : 10 * parityOriginalAssignmentTheta434 ≤ (1 / 20 : ℝ) := by
    norm_num [parityOriginalAssignmentTheta434]
  have he : (Real.exp (parityOriginalAssignmentTheta434 * L)) ^ (10 : ℝ) =
      Real.exp ((10 * parityOriginalAssignmentTheta434) * L) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hpos : 0 ≤ (Real.exp (parityOriginalAssignmentTheta434 * L)) ^ (10 : ℝ) := by
    positivity
  have hone : (1 : ℝ) ≤ (Real.exp (parityOriginalAssignmentTheta434 * L)) ^ (10 : ℝ) := by
    rw [he]
    exact Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) hL0)
  have hZ1 : 1 ≤ Z := (Nat.le_floor_iff hpos).2 (by simpa only [Nat.cast_one] using hone)
  have hZreal : (1 : ℝ) ≤ Z := by exact_mod_cast hZ1
  have hZ0 : (0 : ℝ) < Z := lt_of_lt_of_le (by norm_num) hZreal
  have hZ : (Z : ℝ) ≤ Real.exp (L / 20) := by
    calc
      _ ≤ (Real.exp (parityOriginalAssignmentTheta434 * L)) ^ (10 : ℝ) := Nat.floor_le hpos
      _ = Real.exp ((10 * parityOriginalAssignmentTheta434) * L) := he
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right ht hL0])
  have hlog0 : 0 ≤ Real.log (Z : ℝ) := Real.log_nonneg hZreal
  have hlog : Real.log (Z : ℝ) ≤ L / 20 := by
    simpa only [Real.log_exp] using Real.log_le_log hZ0 hZ
  have h2 : 1 + Real.log (Z : ℝ) ≤ 2 * L := by linarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1 + Real.log (Z : ℝ) by linarith) h2 3
  refine ⟨hZ1, hZ, by linarith, ?_⟩
  nlinarith [hpow]

/-- The finite sum of assignment/CRT errors has the original
6.9 exponential powers under the side-length restriction. -/
theorem box_finite_error_exp_bound
    (Cside L T : ℝ) (hCside : 0 < Cside) (hL : 1 ≤ L)
    (hT0 : 0 ≤ T) (hT : T ≤ Cside * Real.exp ((27 / 50 : ℝ) * L)) :
    boxFiniteError L T ≤
      boxErrorConstant Cside *
        sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L *
        L ^ 3 * (Real.exp ((16 / 25 : ℝ) * L) + Real.exp ((1 / 5 : ℝ) * L)) := by
  let Z := ⌊(Real.exp (parityOriginalAssignmentTheta434 * L)) ^ (10 : ℝ)⌋₊
  have hb := box_cutoff_bounds L hL
  change 1 ≤ Z ∧ (Z : ℝ) ≤ Real.exp (L / 20) ∧
    0 ≤ 1 + Real.log (Z : ℝ) ∧
    (1 + Real.log (Z : ℝ)) ^ 3 ≤ 8 * L ^ 3 at hb
  have hZ0 : (0 : ℝ) ≤ Z := Nat.cast_nonneg _
  have h1 : 2 * T * (Z : ℝ) * Real.exp (L / 20) ≤
      2 * Cside * Real.exp ((16 / 25 : ℝ) * L) := by
    calc
      _ ≤ 2 * (Cside * Real.exp ((27 / 50 : ℝ) * L)) *
          Real.exp (L / 20) * Real.exp (L / 20) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num)) hb.2.1 hZ0
            (by positivity)) (Real.exp_pos _).le
      _ = (2 * Cside) * (Real.exp ((27 / 50 : ℝ) * L) *
          Real.exp (L / 20) * Real.exp (L / 20)) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2 <;> ring
  have h2 : 4 * (Z : ℝ) ^ 2 * Real.exp (L / 10) ≤
      4 * Real.exp ((1 / 5 : ℝ) * L) := by
    calc
      _ ≤ 4 * (Real.exp (L / 20)) ^ 2 * Real.exp (L / 10) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ0 hb.2.1 2) (by norm_num))
          (Real.exp_pos _).le
      _ = 4 * (Real.exp (L / 20) * Real.exp (L / 20) * Real.exp (L / 10)) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2 <;> ring
  have hbracket :
      2 * T * (Z : ℝ) * Real.exp (L / 20) + 4 * (Z : ℝ) ^ 2 * Real.exp (L / 10) ≤
      (2 * Cside + 4) * (Real.exp ((16 / 25 : ℝ) * L) + Real.exp ((1 / 5 : ℝ) * L)) := by
    have h := add_le_add h1 h2
    nlinarith [Real.exp_pos ((16 / 25 : ℝ) * L),
      mul_nonneg hCside.le (Real.exp_pos ((1 / 5 : ℝ) * L)).le]
  have hm := mul_le_mul hbracket hb.2.2.2
    (pow_nonneg hb.2.2.1 3) (by positivity :
      0 ≤ (2 * Cside + 4) * (Real.exp ((16 / 25 : ℝ) * L) + Real.exp ((1 / 5 : ℝ) * L)))
  have hQ := box_HQ_nonneg 20 (sourceOriginalLiteralDepth 20 L) L
  have hs := mul_le_mul_of_nonneg_left hm
    (mul_nonneg (show (0 : ℝ) ≤ 200 ^ 400 by positivity) hQ)
  unfold boxFiniteError boxErrorConstant
  dsimp only
  dsimp [Z] at hs
  convert hs using 1 <;> ring

end Green64Analytic.Parity

end
