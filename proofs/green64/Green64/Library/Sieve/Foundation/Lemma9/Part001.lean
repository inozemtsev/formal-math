module

public import Green64.Library.Sieve.Foundation.Lemma6.Part003
public import Green64.Library.ChenTheorem.Lemma5.Core
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Green64.Library.Sieve.Foundation.Lemma6.Part001

@[expose] public section

/-!
# Sieve / Foundation / Lemma9 / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.Characters -/

section

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Character reduction for Bombieri--Vinogradov

The progression error is first written exactly as an average of twisted
von-Mangoldt sums over all characters.  This finite identity is the bridge
between the progression statement and the primitive-character large sieve.
-/

/-- Subtract the expected main term from the principal character only. -/
noncomputable def adjustedTwistedPsi {q : ℕ}
    (x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  twistedPsi x χ - if χ = 1 then (x : ℂ) else 0

/-- Exact character-orthogonality expansion of `ψ(x; q, a)`. -/
theorem progressionPsi_eq_character_average
    {x q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    (progressionPsi x q a : ℂ) =
      (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedPsi x χ) /
        (Nat.totient q : ℂ) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    (progressionPsi x q a : ℂ) =
        ∑ n ∈ Finset.Icc 1 x,
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            (((if n ≡ a [MOD q] then 1 else 0 : ℝ) : ℂ)) := by
      rw [progressionPsi]
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hna : n ≡ a [MOD q]
      · simp [hna]
      · simp [hna]
    _ = ∑ n ∈ Finset.Icc 1 x,
          (ArithmeticFunction.vonMangoldt n : ℂ) *
            ((∑ χ : DirichletCharacter ℂ q,
                χ (a : ZMod q)⁻¹ * χ (n : ZMod q)) /
              (Nat.totient q : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Chen.residueIndicator_eq_character_average
        (d := q) (x := a) (m := n) hq ha]
      by_cases hna : n ≡ a [MOD q]
      · rw [if_pos hna, if_pos hna.symm]
      · rw [if_neg hna, if_neg (fun han => hna han.symm)]
    _ = (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedPsi x χ) /
        (Nat.totient q : ℂ) := by
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      congr 1
      calc
        ∑ n ∈ Finset.Icc 1 x,
            (ArithmeticFunction.vonMangoldt n : ℂ) *
              ∑ χ : DirichletCharacter ℂ q,
                χ (a : ZMod q)⁻¹ * χ (n : ZMod q) =
            ∑ n ∈ Finset.Icc 1 x,
              ∑ χ : DirichletCharacter ℂ q,
                (ArithmeticFunction.vonMangoldt n : ℂ) *
                  (χ (a : ZMod q)⁻¹ * χ (n : ZMod q)) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [Finset.mul_sum]
        _ = ∑ χ : DirichletCharacter ℂ q,
              ∑ n ∈ Finset.Icc 1 x,
                (ArithmeticFunction.vonMangoldt n : ℂ) *
                  (χ (a : ZMod q)⁻¹ * χ (n : ZMod q)) := by
              rw [Finset.sum_comm]
        _ = ∑ χ : DirichletCharacter ℂ q,
              χ (a : ZMod q)⁻¹ * twistedPsi x χ := by
              apply Finset.sum_congr rfl
              intro χ hχ
              rw [twistedPsi, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro n hn
              ring

/-- Exact character expansion after subtracting the expected principal main
term. -/
theorem progressionError_eq_adjusted_character_average
    {x q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    (progressionPsi x q a : ℂ) -
        (x : ℂ) / (Nat.totient q : ℂ) =
      (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ) /
        (Nat.totient q : ℂ) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have haunit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have hainvunit : IsUnit ((a : ZMod q)⁻¹) := by
    have haunitInt : IsUnit ((a : ℤ) : ZMod q) := by
      simpa only [Int.cast_natCast] using haunit
    simpa only [Int.cast_natCast] using ZMod.isUnit_inv haunitInt
  have hprincipal :
      (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ *
            (if χ = 1 then (x : ℂ) else 0)) = (x : ℂ) := by
    simp_rw [mul_ite, mul_zero]
    rw [Fintype.sum_ite_eq'
      (1 : DirichletCharacter ℂ q)
      (fun χ => χ (a : ZMod q)⁻¹ * (x : ℂ))]
    rw [MulChar.one_apply hainvunit, one_mul]
  rw [progressionPsi_eq_character_average hq ha]
  calc
    (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedPsi x χ) /
          (Nat.totient q : ℂ) -
        (x : ℂ) / (Nat.totient q : ℂ) =
      ((∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * twistedPsi x χ) - (x : ℂ)) /
        (Nat.totient q : ℂ) := by ring
    _ = (∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ) /
        (Nat.totient q : ℂ) := by
      apply congrArg (fun z : ℂ => z / (Nat.totient q : ℂ))
      calc
        (∑ χ : DirichletCharacter ℂ q,
              χ (a : ZMod q)⁻¹ * twistedPsi x χ) - (x : ℂ) =
            (∑ χ : DirichletCharacter ℂ q,
              χ (a : ZMod q)⁻¹ * twistedPsi x χ) -
              ∑ χ : DirichletCharacter ℂ q,
                χ (a : ZMod q)⁻¹ *
                  (if χ = 1 then (x : ℂ) else 0) := by
              rw [hprincipal]
        _ = ∑ χ : DirichletCharacter ℂ q,
              (χ (a : ZMod q)⁻¹ * twistedPsi x χ -
                χ (a : ZMod q)⁻¹ *
                  (if χ = 1 then (x : ℂ) else 0)) := by
              rw [Finset.sum_sub_distrib]
        _ = ∑ χ : DirichletCharacter ℂ q,
              χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ := by
              apply Finset.sum_congr rfl
              intro χ hχ
              rw [adjustedTwistedPsi]
              ring_nf

/-- A reduced progression error is bounded by the average of the adjusted
twisted sums over all characters modulo `q`. -/
theorem progressionError_le_sum_norm_adjustedTwistedPsi
    {x q a : ℕ} (hq : 0 < q) (ha : a.Coprime q) :
    progressionError x q a ≤
      (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖ := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  have hφ : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have haunit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have hainvunit : IsUnit ((a : ZMod q)⁻¹) := by
    have haunitInt : IsUnit ((a : ℤ) : ZMod q) := by
      simpa only [Int.cast_natCast] using haunit
    simpa only [Int.cast_natCast] using ZMod.isUnit_inv haunitInt
  have hcharNorm : ∀ χ : DirichletCharacter ℂ q,
      ‖χ (a : ZMod q)⁻¹‖ = 1 := by
    intro χ
    simpa only [IsUnit.unit_spec] using
      χ.unit_norm_eq_one hainvunit.unit
  have hsum :
      ‖∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ‖ ≤
        ∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖ := by
    calc
      ‖∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ‖ ≤
          ∑ χ : DirichletCharacter ℂ q,
            ‖χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ‖ :=
        norm_sum_le _ _
      _ = ∑ χ : DirichletCharacter ℂ q,
            ‖adjustedTwistedPsi x χ‖ := by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [norm_mul, hcharNorm χ, one_mul]
  calc
    progressionError x q a =
        ‖(progressionPsi x q a : ℂ) -
          (x : ℂ) / (Nat.totient q : ℂ)‖ := by
      rw [progressionError]
      have hcast :
          ((progressionPsi x q a -
              (x : ℝ) / (Nat.totient q : ℝ) : ℝ) : ℂ) =
            (progressionPsi x q a : ℂ) -
              (x : ℂ) / (Nat.totient q : ℂ) := by
        push_cast
        ring
      rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ) /
            (Nat.totient q : ℂ)‖ := by
      rw [progressionError_eq_adjusted_character_average hq ha]
    _ = ‖∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * adjustedTwistedPsi x χ‖ /
            (Nat.totient q : ℝ) := by
      rw [norm_div, Complex.norm_natCast]
    _ ≤ (∑ χ : DirichletCharacter ℂ q,
          ‖adjustedTwistedPsi x χ‖) / (Nat.totient q : ℝ) := by
      exact div_le_div_of_nonneg_right hsum hφ.le
    _ = (Nat.totient q : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖adjustedTwistedPsi x χ‖ := by ring

/-- The same character bound, uniformly over the reduced residue classes. -/
theorem maxProgressionError_le_sum_norm_adjustedTwistedPsi
    {x q : ℕ} (hq : 0 < q) :
    maxProgressionError x q ≤
      (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, ‖adjustedTwistedPsi x χ‖ := by
  classical
  rw [maxProgressionError, dif_neg hq.ne']
  apply Finset.sup'_le
  intro a ha
  rw [reducedProgressionError]
  split_ifs with hac
  · exact progressionError_le_sum_norm_adjustedTwistedPsi hq hac
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun χ _ => norm_nonneg _)

/-- Finite character reduction of the averaged progression error. -/
theorem sum_maxProgressionError_le_character_sum (x Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionError x q) ≤
      ∑ q ∈ Finset.Icc 1 Q,
        (Nat.totient q : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖adjustedTwistedPsi x χ‖ := by
  apply Finset.sum_le_sum
  intro q hq
  exact maxProgressionError_le_sum_norm_adjustedTwistedPsi
    (Finset.mem_Icc.mp hq).1

end Chen.BombieriVinogradov

end

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.VaughanIdentity -/

section

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta Classical

namespace Chen.BombieriVinogradov

/-!
# Vaughan's identity

The analytic proof of Bombieri--Vinogradov starts by splitting the exact
convolution identity `μ * Λ * 1 = Λ` at two cutoffs.  This file records that
algebraic step independently of all subsequent norm estimates.
-/

/-- Restrict an arithmetic function to indices at most `U`. -/
def truncateLE {R : Type*} [Zero R]
    (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

@[simp]
theorem truncateLE_apply {R : Type*} [Zero R]
    (f : ArithmeticFunction R) (U n : ℕ) :
    truncateLE f U n = if n ≤ U then f n else 0 :=
  rfl

/-- Complementary restriction to indices strictly larger than `U`. -/
def truncateGT {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (U : ℕ) : ArithmeticFunction R :=
  f - truncateLE f U

@[simp]
theorem truncateGT_apply {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (U n : ℕ) :
    truncateGT f U n = if U < n then f n else 0 := by
  rw [truncateGT, sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, truncateLE_apply]
  by_cases hn : n ≤ U
  · simp [hn, Nat.not_lt_of_ge hn]
  · have hUn : U < n := Nat.lt_of_not_ge hn
    simp [hn, hUn]

theorem truncateLE_add_truncateGT {R : Type*} [AddGroup R]
    (f : ArithmeticFunction R) (U : ℕ) :
    truncateLE f U + truncateGT f U = f := by
  ext n
  by_cases hn : n ≤ U
  · simp [truncateGT, sub_eq_add_neg, hn]
  · simp [truncateGT, sub_eq_add_neg, hn]

/-- Vaughan's exact decomposition in its standard Type-I/Type-II form.

The first term has the short Möbius variable `d ≤ U`; the next two terms
have all nontrivial convolution variables bounded by `U` and `V`; and the
last term, in which both variables exceed their cutoffs, is Type II. -/
theorem vaughan_identity (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
          ArithmeticFunction.log +
        (truncateLE ArithmeticFunction.vonMangoldt V -
          truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
            truncateLE ArithmeticFunction.vonMangoldt V *
              ArithmeticFunction.zeta) +
        truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
          truncateGT ArithmeticFunction.vonMangoldt V *
            ArithmeticFunction.zeta := by
  let μL : ArithmeticFunction ℝ :=
    truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U
  let μG : ArithmeticFunction ℝ :=
    truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U
  let ΛL : ArithmeticFunction ℝ :=
    truncateLE ArithmeticFunction.vonMangoldt V
  let ΛG : ArithmeticFunction ℝ :=
    truncateGT ArithmeticFunction.vonMangoldt V
  have hμ : μL + μG =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    exact truncateLE_add_truncateGT _ _
  have hΛ : ΛL + ΛG = ArithmeticFunction.vonMangoldt := by
    exact truncateLE_add_truncateGT _ _
  have hlog : (ΛL + ΛG) * ArithmeticFunction.zeta =
      ArithmeticFunction.log := by
    rw [hΛ, ArithmeticFunction.vonMangoldt_mul_zeta]
  have hshort : (μL + μG) * ΛL * ArithmeticFunction.zeta = ΛL := by
    rw [hμ]
    calc
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ΛL *
          ArithmeticFunction.zeta =
          ΛL * ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
            ArithmeticFunction.zeta) := by ring
      _ = ΛL := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
        simp
  change ArithmeticFunction.vonMangoldt =
    μL * ArithmeticFunction.log +
      (ΛL - μL * ΛL * ArithmeticFunction.zeta) +
      μG * ΛG * ArithmeticFunction.zeta
  calc
    ArithmeticFunction.vonMangoldt =
        (μL + μG) * (ΛL + ΛG) * ArithmeticFunction.zeta := by
      rw [hμ, hΛ, mul_assoc, ArithmeticFunction.vonMangoldt_mul_zeta,
        ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
    _ = (μL + μG) * ΛL * ArithmeticFunction.zeta +
          μL * ΛG * ArithmeticFunction.zeta +
          μG * ΛG * ArithmeticFunction.zeta := by
      ring
    _ = ΛL + μL * ΛG * ArithmeticFunction.zeta +
          μG * ΛG * ArithmeticFunction.zeta := by rw [hshort]
    _ = μL * ArithmeticFunction.log +
          (ΛL - μL * ΛL * ArithmeticFunction.zeta) +
          μG * ΛG * ArithmeticFunction.zeta := by
      rw [← hlog]
      ring

/-- First Type-I coefficient in Vaughan's decomposition. -/
noncomputable def vaughanTypeIOne (U : ℕ) : ArithmeticFunction ℝ :=
  truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    ArithmeticFunction.log

/-- Second Type-I coefficient in Vaughan's decomposition. -/
noncomputable def vaughanTypeITwo (U V : ℕ) : ArithmeticFunction ℝ :=
  truncateLE ArithmeticFunction.vonMangoldt V -
    truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
      truncateLE ArithmeticFunction.vonMangoldt V * ArithmeticFunction.zeta

/-- Type-II coefficient, in which both nontrivial convolution variables are
larger than their respective cutoffs. -/
noncomputable def vaughanTypeII (U V : ℕ) : ArithmeticFunction ℝ :=
  truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    truncateGT ArithmeticFunction.vonMangoldt V * ArithmeticFunction.zeta

/-- Pointwise Vaughan identity in the named Type-I/Type-II notation. -/
theorem vonMangoldt_eq_vaughanTypes (U V n : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      vaughanTypeIOne U n + vaughanTypeITwo U V n +
        vaughanTypeII U V n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (vaughan_identity U V)
  simpa only [vaughanTypeIOne, vaughanTypeITwo, vaughanTypeII,
    ArithmeticFunction.add_apply, add_assoc] using h

noncomputable def vaughanTypeIOneSum {q : ℕ}
    (x U : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, (vaughanTypeIOne U n : ℂ) * χ n

noncomputable def vaughanTypeITwoSum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, (vaughanTypeITwo U V n : ℂ) * χ n

noncomputable def vaughanTypeIISum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, (vaughanTypeII U V n : ℂ) * χ n

/-- Vaughan's identity after twisting and summing up to `x`. -/
theorem twistedPsi_eq_vaughanTypes
    {q : ℕ} (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    twistedPsi x χ =
      vaughanTypeIOneSum x U χ + vaughanTypeITwoSum x U V χ +
        vaughanTypeIISum x U V χ := by
  rw [vaughanTypeIOneSum, vaughanTypeITwoSum, vaughanTypeIISum]
  rw [twistedPsi]
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) =
      ∑ n ∈ Finset.Icc 1 x,
        (((vaughanTypeIOne U n : ℝ) : ℂ) +
          ((vaughanTypeITwo U V n : ℝ) : ℂ) +
          ((vaughanTypeII U V n : ℝ) : ℂ)) * χ n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [vonMangoldt_eq_vaughanTypes U V n]
      push_cast
      rfl
    _ = (∑ n ∈ Finset.Icc 1 x,
          (vaughanTypeIOne U n : ℂ) * χ n) +
        (∑ n ∈ Finset.Icc 1 x,
          (vaughanTypeITwo U V n : ℂ) * χ n) +
        ∑ n ∈ Finset.Icc 1 x,
          (vaughanTypeII U V n : ℂ) * χ n := by
      simp_rw [add_mul, Finset.sum_add_distrib]

end Chen.BombieriVinogradov

end

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.Bilinear -/

section

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Bilinear character sums

This file supplies the finite Cauchy--Schwarz layer used after Vaughan's
identity.  It is deliberately stated on one dependent finite set containing
all characters at all moduli, which matches the weights in the character
large sieve.
-/

/-- Characters over all positive moduli at most `Q`. -/
noncomputable def characterIndices (Q : ℕ) :
    Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (Finset.Icc 1 Q).sigma fun _q => Finset.univ

/-- Characters with modulus in the conductor interval `(D,Q]`. -/
noncomputable def characterIndicesIoc (D Q : ℕ) :
    Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (Finset.Ioc D Q).sigma fun _q => Finset.univ

/-- The large-sieve weight, with nonprimitive characters assigned weight
zero. -/
noncomputable def primitiveCharacterWeight
    (i : Σ q : ℕ, DirichletCharacter ℂ q) : ℝ :=
  ((i.1 : ℝ) / (Nat.totient i.1 : ℝ)) *
    if i.2.IsPrimitive then 1 else 0

/-- The `φ(q)⁻¹` weight used on a dyadic conductor interval. -/
noncomputable def primitiveDyadicWeight
    (i : Σ q : ℕ, DirichletCharacter ℂ q) : ℝ :=
  (Nat.totient i.1 : ℝ)⁻¹ * if i.2.IsPrimitive then 1 else 0

theorem primitiveCharacterWeight_nonneg
    (i : Σ q : ℕ, DirichletCharacter ℂ q) :
    0 ≤ primitiveCharacterWeight i := by
  unfold primitiveCharacterWeight
  positivity

theorem primitiveDyadicWeight_nonneg
    (i : Σ q : ℕ, DirichletCharacter ℂ q) :
    0 ≤ primitiveDyadicWeight i := by
  unfold primitiveDyadicWeight
  positivity

/-- Flatten the nested primitive-character mean into the dependent dyadic
index set. -/
theorem sum_characterIndicesIoc_primitiveDyadicWeight_eq
    (D Q : ℕ)
    (F : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ) :
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * F i) =
      ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then F ⟨q, χ⟩ else 0 := by
  rw [characterIndicesIoc, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [primitiveDyadicWeight, hp]
  · simp [primitiveDyadicWeight, hp]

/-- The total `1 / φ(q)` mass of primitive characters on `(D,Q]` is at
most the number of moduli, hence at most `Q`. -/
theorem sum_primitiveDyadicWeight_le
    (D Q : ℕ) (hD : 1 ≤ D) :
    (∑ i ∈ characterIndicesIoc D Q, primitiveDyadicWeight i) ≤ Q := by
  rw [characterIndicesIoc, Finset.sum_sigma]
  calc
    (∑ q ∈ Finset.Ioc D Q,
        ∑ χ : DirichletCharacter ℂ q,
          primitiveDyadicWeight ⟨q, χ⟩) ≤
        ∑ _q ∈ Finset.Ioc D Q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := by
        have := (Finset.mem_Ioc.mp hq).1
        omega
      letI : NeZero q := ⟨hqpos.ne'⟩
      have htot : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      calc
        (∑ χ : DirichletCharacter ℂ q,
            primitiveDyadicWeight ⟨q, χ⟩) ≤
            ∑ _χ : DirichletCharacter ℂ q, (q.totient : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro χ hχ
          by_cases hp : χ.IsPrimitive
          · simp [primitiveDyadicWeight, hp]
          · simp [primitiveDyadicWeight, hp]
        _ = 1 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
          field_simp
    _ = ((Finset.Ioc D Q).card : ℝ) := by simp
    _ ≤ Q := by
      exact_mod_cast (by
        simp only [Nat.card_Ioc]
        omega : (Finset.Ioc D Q).card ≤ Q)

/-- Weighted Cauchy--Schwarz over all primitive characters and moduli. -/
theorem primitiveCharacter_weighted_cauchy_sq
    (Q : ℕ)
    (F G : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ) :
    (∑ i ∈ characterIndices Q,
        primitiveCharacterWeight i * F i * G i) ^ 2 ≤
      (∑ i ∈ characterIndices Q,
          primitiveCharacterWeight i * F i ^ 2) *
        ∑ i ∈ characterIndices Q,
          primitiveCharacterWeight i * G i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (primitiveCharacterWeight_nonneg i) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (primitiveCharacterWeight_nonneg i) (sq_nonneg _)
  · intro i hi
    ring_nf
    exact le_rfl

/-- Weighted Cauchy--Schwarz with the dyadic `φ(q)⁻¹` weight. -/
theorem primitiveCharacter_dyadic_cauchy_sq
    (D Q : ℕ)
    (F G : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ) :
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * F i * G i) ^ 2 ≤
      (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i * F i ^ 2) *
        ∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i * G i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    exact mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
  · intro i hi
    exact mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
  · intro i hi
    ring_nf
    exact le_rfl

/-- A character polynomial on an interval `(M, M+N]`. -/
noncomputable def characterIntervalSum {q : ℕ}
    (M N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Ioc M (M + N), a n * χ n

/-- A rectangular bilinear character sum. -/
noncomputable def bilinearCharacterRectangle {q : ℕ}
    (M N K L : ℕ) (a b : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m ∈ Finset.Ioc M (M + N),
    ∑ n ∈ Finset.Ioc K (K + L),
      a m * b n * χ (m * n)

/-- A rectangular bilinear sum factors into the product of its two character
polynomials. -/
theorem bilinearCharacterRectangle_eq_mul {q : ℕ}
    (M N K L : ℕ) (a b : ℕ → ℂ)
    (χ : DirichletCharacter ℂ q) :
    bilinearCharacterRectangle M N K L a b χ =
      characterIntervalSum M N a χ * characterIntervalSum K L b χ := by
  classical
  rw [bilinearCharacterRectangle, characterIntervalSum,
    characterIntervalSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul]
  ring

/-- The existing character large sieve, rewritten on `characterIndices`. -/
theorem characterIntervalSecondMoment_le
    (Q M N : ℕ) (a : ℕ → ℂ) :
    (∑ i ∈ characterIndices Q,
        primitiveCharacterWeight i *
          ‖characterIntervalSum M N a i.2‖ ^ 2) ≤
      ((Q : ℝ) ^ 2 + Real.pi * N) *
        ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  rw [characterIndices, Finset.sum_sigma]
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        ∑ χ : DirichletCharacter ℂ q,
          primitiveCharacterWeight ⟨q, χ⟩ *
            ‖characterIntervalSum M N a χ‖ ^ 2) =
      ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) / (q.totient : ℝ) *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2
          else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp [primitiveCharacterWeight, characterIntervalSum, hp]
      · simp [primitiveCharacterWeight, characterIntervalSum, hp]
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * N) *
        ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
      Chen.LargeSieve.large_sieve_character Q M N a

/-- The existing dyadic character large sieve, rewritten on the dependent
character index set used by the bilinear argument. -/
theorem characterIntervalSecondMoment_dyadic_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ D → D ≤ Q →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N a i.2‖ ^ 2) ≤
          C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  rcases Chen.LargeSieve.large_sieve_character_dyadic with
    ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N a hD hDQ
  rw [characterIndicesIoc, Finset.sum_sigma]
  calc
    (∑ q ∈ Finset.Ioc D Q,
        ∑ χ : DirichletCharacter ℂ q,
          primitiveDyadicWeight ⟨q, χ⟩ *
            ‖characterIntervalSum M N a χ‖ ^ 2) =
      ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ n‖ ^ 2
          else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      by_cases hp : χ.IsPrimitive
      · simp [primitiveDyadicWeight, characterIntervalSum, hp]
      · simp [primitiveDyadicWeight, characterIntervalSum, hp]
    _ ≤ C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 :=
      hlarge D Q M N a hD hDQ

/-- Unsquared first-moment consequence of the dyadic character large sieve. -/
theorem characterIntervalMean_dyadic_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ D → D ≤ Q →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N a i.2‖) ≤
          Real.sqrt
            ((Q : ℝ) *
              (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
                ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2)) := by
  rcases characterIntervalSecondMoment_dyadic_le with
    ⟨C, hC, hsecond⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N a hD hDQ
  let S : ℝ := ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i * ‖characterIntervalSum M N a i.2‖
  have hcauchy := primitiveCharacter_dyadic_cauchy_sq D Q
    (fun _i => (1 : ℝ))
    (fun i => ‖characterIntervalSum M N a i.2‖)
  have hsq : S ^ 2 ≤
      (Q : ℝ) *
        (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) := by
    dsimp only [S]
    calc
      (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            ‖characterIntervalSum M N a i.2‖) ^ 2 =
          (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i * 1 *
              ‖characterIntervalSum M N a i.2‖) ^ 2 := by simp
      _ ≤ (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i * 1 ^ 2) *
            ∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M N a i.2‖ ^ 2 := hcauchy
      _ ≤ (Q : ℝ) *
            (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) := by
        apply mul_le_mul
        · simpa using sum_primitiveDyadicWeight_le D Q hD
        · exact hsecond D Q M N a hD hDQ
        · exact Finset.sum_nonneg fun i _ =>
            mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
        · positivity
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (norm_nonneg _)
  have hR : 0 ≤
      (Q : ℝ) *
        (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) := by
    positivity
  apply (sq_le_sq₀ hS (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt hR]
  exact hsq

/-- Mean-value bound for rectangular bilinear sums.  Squaring avoids any
loss or side condition from square roots; later dyadic estimates can take
the square root only after inserting concrete nonnegative bounds. -/
theorem bilinearCharacterMean_sq_le
    (Q M N K L : ℕ) (a b : ℕ → ℂ) :
    (∑ i ∈ characterIndices Q,
        primitiveCharacterWeight i *
          ‖characterIntervalSum M N a i.2‖ *
          ‖characterIntervalSum K L b i.2‖) ^ 2 ≤
      (((Q : ℝ) ^ 2 + Real.pi * N) *
          ∑ m ∈ Finset.Ioc M (M + N), ‖a m‖ ^ 2) *
        (((Q : ℝ) ^ 2 + Real.pi * L) *
          ∑ n ∈ Finset.Ioc K (K + L), ‖b n‖ ^ 2) := by
  have hcauchy := primitiveCharacter_weighted_cauchy_sq Q
    (fun i => ‖characterIntervalSum M N a i.2‖)
    (fun i => ‖characterIntervalSum K L b i.2‖)
  refine hcauchy.trans ?_
  apply mul_le_mul
  · exact characterIntervalSecondMoment_le Q M N a
  · exact characterIntervalSecondMoment_le Q K L b
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveCharacterWeight_nonneg i) (sq_nonneg _)
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun n _ => sq_nonneg _)

/-- Dyadic-conductor mean-value bound for rectangular bilinear character
sums. -/
theorem bilinearCharacterMean_dyadic_sq_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N K L : ℕ) (a b : ℕ → ℂ), 1 ≤ D → D ≤ Q →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N a i.2‖ *
              ‖characterIntervalSum K L b i.2‖) ^ 2 ≤
          (C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
              ∑ m ∈ Finset.Ioc M (M + N), ‖a m‖ ^ 2) *
            (C * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc K (K + L), ‖b n‖ ^ 2) := by
  rcases characterIntervalSecondMoment_dyadic_le with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N K L a b hD hDQ
  have hcauchy := primitiveCharacter_dyadic_cauchy_sq D Q
    (fun i => ‖characterIntervalSum M N a i.2‖)
    (fun i => ‖characterIntervalSum K L b i.2‖)
  refine hcauchy.trans ?_
  apply mul_le_mul
  · exact hlarge D Q M N a hD hDQ
  · exact hlarge D Q K L b hD hDQ
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC.le (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)

end Chen.BombieriVinogradov

end

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.Maximal -/

section

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# A maximal dyadic large-sieve layer

The Type-I and Type-II hyperbola sums have an upper endpoint depending on the
other variable.  This file begins the standard Rademacher--Menshov reduction:
an arbitrary prefix of an interval of length `2^L` is controlled by a
recursively defined dyadic energy with only an `L + 1` loss.  The recursive
form avoids choosing and bookkeeping an explicit list of binary blocks.
-/

/-- Sum of squared norms over the dyadic blocks needed by the recursive
prefix decomposition.  At level `L+1`, the full left half is recorded and the
construction recurses into both halves. -/
noncomputable def dyadicPrefixEnergy (f : ℕ → ℂ) : ℕ → ℕ → ℝ
  | M, 0 => ‖∑ n ∈ Finset.Ioc M (M + 1), f n‖ ^ 2
  | M, L + 1 =>
      ‖∑ n ∈ Finset.Ioc M (M + 2 ^ L), f n‖ ^ 2 +
        dyadicPrefixEnergy f M L +
          dyadicPrefixEnergy f (M + 2 ^ L) L

theorem dyadicPrefixEnergy_nonneg
    (f : ℕ → ℂ) (M L : ℕ) :
    0 ≤ dyadicPrefixEnergy f M L := by
  induction L generalizing M with
  | zero =>
      rw [dyadicPrefixEnergy]
      positivity
  | succ L ih =>
      rw [dyadicPrefixEnergy]
      exact add_nonneg
        (add_nonneg (sq_nonneg _) (ih M))
        (ih (M + 2 ^ L))

/-- Weighted two-term Cauchy inequality in the exact form needed by the
dyadic induction. -/
theorem norm_add_sq_le_weighted
    (z w : ℂ) (r : ℝ) (hr : 0 < r) :
    ‖z + w‖ ^ 2 ≤
      (r + 1) * ‖z‖ ^ 2 + (r + 1) / r * ‖w‖ ^ 2 := by
  have htri : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w
  have hsquare :
      ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hid :
      (r + 1) * ‖z‖ ^ 2 + (r + 1) / r * ‖w‖ ^ 2 -
          (‖z‖ + ‖w‖) ^ 2 =
        (r * ‖z‖ - ‖w‖) ^ 2 / r := by
    field_simp [hr.ne']
    ring
  have hweighted :
      (‖z‖ + ‖w‖) ^ 2 ≤
        (r + 1) * ‖z‖ ^ 2 + (r + 1) / r * ‖w‖ ^ 2 := by
    apply sub_nonneg.mp
    rw [hid]
    exact div_nonneg (sq_nonneg _) hr.le
  exact hsquare.trans hweighted

/-- Every prefix of a `2^L`-long interval is bounded by `L+1` times the
dyadic energy.  This is the finite Rademacher--Menshov inequality that will
turn the ordinary character large sieve into a maximal one. -/
theorem norm_sum_Ioc_prefix_sq_le_dyadicPrefixEnergy
    (f : ℕ → ℂ) (M L K : ℕ) (hK : K ≤ 2 ^ L) :
    ‖∑ n ∈ Finset.Ioc M (M + K), f n‖ ^ 2 ≤
      ((L + 1 : ℕ) : ℝ) * dyadicPrefixEnergy f M L := by
  induction L generalizing M K with
  | zero =>
      have hK01 : K = 0 ∨ K = 1 := by omega
      rcases hK01 with rfl | rfl
      · simp [dyadicPrefixEnergy]
      · simp [dyadicPrefixEnergy]
  | succ L ih =>
      let H : ℕ := 2 ^ L
      have hpow : 2 ^ (L + 1) = H + H := by
        dsimp only [H]
        rw [pow_succ]
        omega
      have hKfull : K ≤ H + H := by
        simpa [hpow] using hK
      by_cases hleft : K ≤ H
      · have hbase := ih M K hleft
        have hEleft : 0 ≤ dyadicPrefixEnergy f M L :=
          dyadicPrefixEnergy_nonneg f M L
        have hEright :
            0 ≤ dyadicPrefixEnergy f (M + H) L :=
          dyadicPrefixEnergy_nonneg f (M + H) L
        have hblock :
            0 ≤ ‖∑ n ∈ Finset.Ioc M (M + H), f n‖ ^ 2 := by
          positivity
        rw [dyadicPrefixEnergy]
        dsimp only [H] at hbase hEright ⊢
        have hcoef :
            ((L + 1 : ℕ) : ℝ) ≤ ((L + 1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ (L + 1)
        have hsum :
            dyadicPrefixEnergy f M L ≤
              ‖∑ n ∈ Finset.Ioc M (M + 2 ^ L), f n‖ ^ 2 +
                dyadicPrefixEnergy f M L +
                  dyadicPrefixEnergy f (M + 2 ^ L) L := by
          linarith
        exact hbase.trans
          (mul_le_mul hcoef hsum hEleft (by positivity))
      · have hHK : H ≤ K := by omega
        let K' : ℕ := K - H
        have hK' : K' ≤ H := by
          dsimp only [K']
          omega
        have hend : M + K = (M + H) + K' := by
          dsimp only [K']
          omega
        let A : ℂ := ∑ n ∈ Finset.Ioc M (M + H), f n
        let B : ℂ := ∑ n ∈ Finset.Ioc (M + H) ((M + H) + K'), f n
        have hsplit :
            (∑ n ∈ Finset.Ioc M (M + K), f n) = A + B := by
          rw [hend]
          dsimp only [A, B]
          exact (Finset.sum_Ioc_consecutive f
            (Nat.le_add_right M H)
            (Nat.le_add_right (M + H) K')).symm
        have hB := ih (M + H) K' hK'
        have hr : (0 : ℝ) < L + 1 := by positivity
        have hweighted := norm_add_sq_le_weighted A B (L + 1) hr
        have hEleft : 0 ≤ dyadicPrefixEnergy f M L :=
          dyadicPrefixEnergy_nonneg f M L
        have hEright :
            0 ≤ dyadicPrefixEnergy f (M + H) L :=
          dyadicPrefixEnergy_nonneg f (M + H) L
        rw [hsplit]
        rw [dyadicPrefixEnergy]
        dsimp only [H] at A B hweighted hB hEright ⊢
        calc
          ‖A + B‖ ^ 2 ≤
              (((L : ℝ) + 1) + 1) * ‖A‖ ^ 2 +
                (((L : ℝ) + 1) + 1) / ((L : ℝ) + 1) * ‖B‖ ^ 2 := by
            simpa only [Nat.cast_add, Nat.cast_one] using hweighted
          _ ≤ (((L : ℝ) + 1) + 1) * ‖A‖ ^ 2 +
                (((L : ℝ) + 1) + 1) *
                  dyadicPrefixEnergy f (M + 2 ^ L) L := by
            have hterm :
                (((L : ℝ) + 1) + 1) / ((L : ℝ) + 1) * ‖B‖ ^ 2 ≤
                  (((L : ℝ) + 1) + 1) *
                    dyadicPrefixEnergy f (M + 2 ^ L) L := by
              calc
                (((L : ℝ) + 1) + 1) / ((L : ℝ) + 1) * ‖B‖ ^ 2 ≤
                    (((L : ℝ) + 1) + 1) / ((L : ℝ) + 1) *
                      (((L : ℝ) + 1) *
                        dyadicPrefixEnergy f (M + 2 ^ L) L) := by
                  apply mul_le_mul_of_nonneg_left
                  · simpa only [Nat.cast_add, Nat.cast_one] using hB
                  · positivity
                _ = (((L : ℝ) + 1) + 1) *
                      dyadicPrefixEnergy f (M + 2 ^ L) L := by
                  field_simp
            linarith
          _ ≤ (((L : ℝ) + 1) + 1) *
                (‖A‖ ^ 2 + dyadicPrefixEnergy f M L +
                  dyadicPrefixEnergy f (M + 2 ^ L) L) := by
            nlinarith [sq_nonneg ‖A‖]
          _ = (((L + 1 + 1 : ℕ) : ℝ)) *
                (‖A‖ ^ 2 + dyadicPrefixEnergy f M L +
                  dyadicPrefixEnergy f (M + 2 ^ L) L) := by
            push_cast
            ring

/-- Primitive-character average of the dyadic energy on one conductor
interval. -/
noncomputable def dyadicCharacterEnergyMean
    (D Q M L : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ i ∈ characterIndicesIoc D Q,
    primitiveDyadicWeight i *
      dyadicPrefixEnergy (fun n => a n * i.2 n) M L

theorem dyadicCharacterEnergyMean_nonneg
    (D Q M L : ℕ) (a : ℕ → ℂ) :
    0 ≤ dyadicCharacterEnergyMean D Q M L a := by
  rw [dyadicCharacterEnergyMean]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (primitiveDyadicWeight_nonneg i)
      (dyadicPrefixEnergy_nonneg _ M L)

/-- A fixed prefix second moment is controlled by the averaged dyadic
energy.  The next theorem bounds that energy by repeated applications of the
ordinary dyadic character large sieve. -/
theorem characterPrefixSecondMoment_le_dyadicCharacterEnergyMean
    (D Q M L K : ℕ) (a : ℕ → ℂ) (hK : K ≤ 2 ^ L) :
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖characterIntervalSum M K a i.2‖ ^ 2) ≤
      ((L + 1 : ℕ) : ℝ) * dyadicCharacterEnergyMean D Q M L a := by
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖characterIntervalSum M K a i.2‖ ^ 2) ≤
        ∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            (((L + 1 : ℕ) : ℝ) *
              dyadicPrefixEnergy (fun n => a n * i.2 n) M L) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _
        (primitiveDyadicWeight_nonneg i)
      simpa only [characterIntervalSum] using
        norm_sum_Ioc_prefix_sq_le_dyadicPrefixEnergy
          (fun n => a n * i.2 n) M L K hK
    _ = ((L + 1 : ℕ) : ℝ) *
        dyadicCharacterEnergyMean D Q M L a := by
      rw [dyadicCharacterEnergyMean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem dyadicCharacterEnergyMean_succ
    (D Q M L : ℕ) (a : ℕ → ℂ) :
    dyadicCharacterEnergyMean D Q M (L + 1) a =
      (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i *
          ‖characterIntervalSum M (2 ^ L) a i.2‖ ^ 2) +
        dyadicCharacterEnergyMean D Q M L a +
          dyadicCharacterEnergyMean D Q (M + 2 ^ L) L a := by
  rw [dyadicCharacterEnergyMean, dyadicCharacterEnergyMean,
    dyadicCharacterEnergyMean]
  simp_rw [dyadicPrefixEnergy, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rfl

/-- Repeated use of the ordinary dyadic character large sieve bounds the
entire recursive energy with one further logarithmic loss. -/
theorem dyadicCharacterEnergyMean_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M L : ℕ) (a : ℕ → ℂ), 1 ≤ D → D ≤ Q →
        dyadicCharacterEnergyMean D Q M L a ≤
          C * ((L + 1 : ℕ) : ℝ) *
            ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc M (M + 2 ^ L), ‖a n‖ ^ 2 := by
  rcases characterIntervalSecondMoment_dyadic_le with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M L a hD hDQ
  induction L generalizing M with
  | zero =>
      have hbase := hlarge D Q M 1 a hD hDQ
      simpa [dyadicCharacterEnergyMean, dyadicPrefixEnergy,
        characterIntervalSum] using hbase
  | succ L ih =>
      let H : ℕ := 2 ^ L
      have hpow : 2 ^ (L + 1) = H + H := by
        dsimp only [H]
        rw [pow_succ]
        omega
      have hDpos : (0 : ℝ) < D := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
      let Sleft : ℝ :=
        ∑ n ∈ Finset.Ioc M (M + H), ‖a n‖ ^ 2
      let Sright : ℝ :=
        ∑ n ∈ Finset.Ioc (M + H) ((M + H) + H), ‖a n‖ ^ 2
      have hSleft : 0 ≤ Sleft := by
        dsimp only [Sleft]
        positivity
      have hSright : 0 ≤ Sright := by
        dsimp only [Sright]
        positivity
      let G : ℝ := C * ((Q : ℝ) + ((H + H : ℕ) : ℝ) / (D : ℝ))
      have hG : 0 ≤ G := by
        dsimp only [G]
        positivity
      have hfactor :
          C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) ≤ G := by
        dsimp only [G]
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact add_le_add_right
          (div_le_div_of_nonneg_right
            (by exact_mod_cast Nat.le_add_right H H) hDpos.le) _
      have hblock := hlarge D Q M H a hD hDQ
      have hblock' :
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M H a i.2‖ ^ 2) ≤
            G * Sleft := by
        calc
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M H a i.2‖ ^ 2) ≤
              C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sleft := by
            simpa only [Sleft] using hblock
          _ ≤ G * Sleft :=
            mul_le_mul_of_nonneg_right hfactor hSleft
      have hleft := ih M
      have hright := ih (M + H)
      have hleft' :
          dyadicCharacterEnergyMean D Q M L a ≤
            (((L + 1 : ℕ) : ℝ) * G) * Sleft := by
        calc
          dyadicCharacterEnergyMean D Q M L a ≤
              C * ((L + 1 : ℕ) : ℝ) *
                ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sleft := by
            simpa only [H, Sleft] using hleft
          _ ≤ (((L + 1 : ℕ) : ℝ) * G) * Sleft := by
            have hcoef :
                ((L + 1 : ℕ) : ℝ) *
                    (C * ((Q : ℝ) + (H : ℝ) / (D : ℝ))) ≤
                  ((L + 1 : ℕ) : ℝ) * G :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
            calc
              C * ((L + 1 : ℕ) : ℝ) *
                  ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sleft =
                  (((L + 1 : ℕ) : ℝ) *
                    (C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)))) * Sleft := by ring
              _ ≤ (((L + 1 : ℕ) : ℝ) * G) * Sleft :=
                mul_le_mul_of_nonneg_right hcoef hSleft
      have hright' :
          dyadicCharacterEnergyMean D Q (M + H) L a ≤
            (((L + 1 : ℕ) : ℝ) * G) * Sright := by
        calc
          dyadicCharacterEnergyMean D Q (M + H) L a ≤
              C * ((L + 1 : ℕ) : ℝ) *
                ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sright := by
            simpa only [H, Sright, Nat.add_assoc] using hright
          _ ≤ (((L + 1 : ℕ) : ℝ) * G) * Sright := by
            have hcoef :
                ((L + 1 : ℕ) : ℝ) *
                    (C * ((Q : ℝ) + (H : ℝ) / (D : ℝ))) ≤
                  ((L + 1 : ℕ) : ℝ) * G :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
            calc
              C * ((L + 1 : ℕ) : ℝ) *
                  ((Q : ℝ) + (H : ℝ) / (D : ℝ)) * Sright =
                  (((L + 1 : ℕ) : ℝ) *
                    (C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)))) * Sright := by ring
              _ ≤ (((L + 1 : ℕ) : ℝ) * G) * Sright :=
                mul_le_mul_of_nonneg_right hcoef hSright
      have hsum :
          Sleft + Sright =
            ∑ n ∈ Finset.Ioc M (M + 2 ^ (L + 1)), ‖a n‖ ^ 2 := by
        dsimp only [Sleft, Sright]
        rw [hpow]
        simpa [Nat.add_assoc] using
          Finset.sum_Ioc_consecutive (fun n => ‖a n‖ ^ 2)
            (Nat.le_add_right M H) (Nat.le_add_right (M + H) H)
      rw [dyadicCharacterEnergyMean_succ]
      calc
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M (2 ^ L) a i.2‖ ^ 2) +
            dyadicCharacterEnergyMean D Q M L a +
              dyadicCharacterEnergyMean D Q (M + 2 ^ L) L a ≤
            G * Sleft + (((L + 1 : ℕ) : ℝ) * G) * Sleft +
              (((L + 1 : ℕ) : ℝ) * G) * Sright := by
          exact add_le_add (add_le_add hblock' hleft') hright'
        _ = (((L + 1 + 1 : ℕ) : ℝ) * G) * Sleft +
              (((L + 1 : ℕ) : ℝ) * G) * Sright := by
          push_cast
          ring
        _ ≤ (((L + 1 + 1 : ℕ) : ℝ) * G) * Sleft +
              (((L + 1 + 1 : ℕ) : ℝ) * G) * Sright := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (by exact_mod_cast Nat.le_succ (L + 1)) hG)
              hSright) _
        _ = C * ((L + 1 + 1 : ℕ) : ℝ) *
              ((Q : ℝ) + ((2 ^ (L + 1) : ℕ) : ℝ) / (D : ℝ)) *
                ∑ n ∈ Finset.Ioc M (M + 2 ^ (L + 1)), ‖a n‖ ^ 2 := by
          rw [← hsum]
          dsimp only [G]
          rw [hpow]
          ring

/-- The largest squared character prefix sum among the first `N` terms.
The range is `N + 1`, so the zero-length prefix is included and the indexing
finset is always nonempty. -/
noncomputable def maxCharacterPrefixSq {q : ℕ}
    (M N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) : ℝ :=
  (Finset.range (N + 1)).sup' (by simp)
    (fun K => ‖characterIntervalSum M K a χ‖ ^ 2)

theorem characterIntervalSum_sq_le_maxCharacterPrefixSq {q : ℕ}
    (M N K : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hK : K ≤ N) :
    ‖characterIntervalSum M K a χ‖ ^ 2 ≤
      maxCharacterPrefixSq M N a χ := by
  rw [maxCharacterPrefixSq]
  exact Finset.le_sup'
    (fun J => (‖characterIntervalSum M J a χ‖ ^ 2 : ℝ))
    (Finset.mem_range.2 (Nat.lt_succ_iff.2 hK))

theorem maxCharacterPrefixSq_nonneg {q : ℕ}
    (M N : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
    0 ≤ maxCharacterPrefixSq M N a χ := by
  exact (sq_nonneg ‖characterIntervalSum M 0 a χ‖).trans
    (characterIntervalSum_sq_le_maxCharacterPrefixSq M N 0 a χ
      (Nat.zero_le N))

/-- Pointwise Rademacher--Menshov bound for the maximum over all prefixes of
length at most `N`, where `N` is contained in a dyadic interval of level
`L`. -/
theorem maxCharacterPrefixSq_le_dyadicPrefixEnergy {q : ℕ}
    (M N L : ℕ) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hN : N ≤ 2 ^ L) :
    maxCharacterPrefixSq M N a χ ≤
      ((L + 1 : ℕ) : ℝ) *
        dyadicPrefixEnergy (fun n => a n * χ n) M L := by
  rw [maxCharacterPrefixSq]
  apply Finset.sup'_le
  intro K hK
  have hKN : K ≤ N := by
    exact Nat.le_of_lt_succ (Finset.mem_range.1 hK)
  simpa only [characterIntervalSum] using
    norm_sum_Ioc_prefix_sq_le_dyadicPrefixEnergy
      (fun n => a n * χ n) M L K (hKN.trans hN)

/-- Maximal dyadic character large sieve.  Each character may choose its own
prefix length; the price compared with the ordinary large sieve is only the
square of the dyadic depth. -/
theorem maxCharacterPrefixSecondMoment_dyadic_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N L : ℕ) (a : ℕ → ℂ),
        1 ≤ D → D ≤ Q → N ≤ 2 ^ L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                maxCharacterPrefixSq M N a i.2) ≤
            C * (((L + 1 : ℕ) : ℝ) ^ 2) *
              ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
                ∑ n ∈ Finset.Ioc M (M + 2 ^ L), ‖a n‖ ^ 2 := by
  rcases dyadicCharacterEnergyMean_le with ⟨C, hC, henergy⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N L a hD hDQ hN
  calc
    (∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * maxCharacterPrefixSq M N a i.2) ≤
        ∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            (((L + 1 : ℕ) : ℝ) *
              dyadicPrefixEnergy (fun n => a n * i.2 n) M L) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (maxCharacterPrefixSq_le_dyadicPrefixEnergy M N L a i.2 hN)
        (primitiveDyadicWeight_nonneg i)
    _ = ((L + 1 : ℕ) : ℝ) *
          dyadicCharacterEnergyMean D Q M L a := by
      rw [dyadicCharacterEnergyMean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ((L + 1 : ℕ) : ℝ) *
          (C * ((L + 1 : ℕ) : ℝ) *
            ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc M (M + 2 ^ L), ‖a n‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (henergy D Q M L a hD hDQ) (by positivity)
    _ = C * (((L + 1 : ℕ) : ℝ) ^ 2) *
          ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Ioc M (M + 2 ^ L), ‖a n‖ ^ 2 := by
      ring

/-- Dyadic bilinear large sieve with a character-dependent endpoint in the
second factor.  The square root turns `maxCharacterPrefixSq` back into the
norm of a maximal prefix, while keeping the weighted Cauchy--Schwarz step
entirely over nonnegative real quantities. -/
theorem maximalBilinearCharacterMean_dyadic_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (D Q M R K N L : ℕ) (a b : ℕ → ℂ),
        1 ≤ D → D ≤ Q → N ≤ 2 ^ L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M R a i.2‖ *
                  Real.sqrt (maxCharacterPrefixSq K N b i.2)) ^ 2 ≤
            (C₀ * ((Q : ℝ) + (R : ℝ) / (D : ℝ)) *
                ∑ m ∈ Finset.Ioc M (M + R), ‖a m‖ ^ 2) *
              (C₁ * (((L + 1 : ℕ) : ℝ) ^ 2) *
                ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
                  ∑ n ∈ Finset.Ioc K (K + 2 ^ L), ‖b n‖ ^ 2) := by
  rcases characterIntervalSecondMoment_dyadic_le with
    ⟨C₀, hC₀, hinterval⟩
  rcases maxCharacterPrefixSecondMoment_dyadic_le with
    ⟨C₁, hC₁, hmax⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro D Q M R K N L a b hD hDQ hN
  have hcauchy := primitiveCharacter_dyadic_cauchy_sq D Q
    (fun i => ‖characterIntervalSum M R a i.2‖)
    (fun i => Real.sqrt (maxCharacterPrefixSq K N b i.2))
  refine hcauchy.trans ?_
  apply mul_le_mul
  · exact hinterval D Q M R a hD hDQ
  · calc
      (∑ i ∈ characterIndicesIoc D Q,
          primitiveDyadicWeight i *
            Real.sqrt (maxCharacterPrefixSq K N b i.2) ^ 2) =
          ∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              maxCharacterPrefixSq K N b i.2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.sq_sqrt (maxCharacterPrefixSq_nonneg K N b i.2)]
      _ ≤ C₁ * (((L + 1 : ℕ) : ℝ) ^ 2) *
            ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
              ∑ n ∈ Finset.Ioc K (K + 2 ^ L), ‖b n‖ ^ 2 :=
        hmax D Q K N L b hD hDQ hN
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (primitiveDyadicWeight_nonneg i) (sq_nonneg _)
  · exact mul_nonneg
      (mul_nonneg hC₀.le (by positivity))
      (Finset.sum_nonneg fun m _ => sq_nonneg _)

end Chen.BombieriVinogradov

end

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.TypeI -/

section

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Type-I input for Bombieri--Vinogradov

The short-variable pieces of Vaughan's identity are controlled by uniform
character-prefix estimates and summation by parts.  This file isolates that
analytic input from the later convolution bookkeeping.
-/

/-- Twist a real arithmetic function by a Dirichlet character. -/
noncomputable def characterTwist {q : ℕ}
    (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    ArithmeticFunction ℂ :=
  ⟨fun n => (f n : ℂ) * χ n, by simp⟩

@[simp]
theorem characterTwist_apply {q : ℕ}
    (f : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    characterTwist f χ n = (f n : ℂ) * χ n :=
  rfl

/-- Character twists commute with Dirichlet convolution. -/
theorem characterTwist_mul {q : ℕ}
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) :
    characterTwist (f * g) χ = characterTwist f χ * characterTwist g χ := by
  ext n
  simp only [characterTwist_apply, ArithmeticFunction.mul_apply]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← hprod, Nat.cast_mul]
  rw [map_mul]
  ring

/-- Finite hyperbola identity for a character-twisted convolution. -/
theorem sum_characterTwist_mul_eq_sum_sum {q : ℕ}
    (f g : ArithmeticFunction ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℂ) * χ n) =
      ∑ d ∈ Finset.Ioc 0 N, (f d : ℂ) * χ d *
        ∑ m ∈ Finset.Ioc 0 (N / d), (g m : ℂ) * χ m := by
  change (∑ n ∈ Finset.Ioc 0 N, characterTwist (f * g) χ n) =
    ∑ d ∈ Finset.Ioc 0 N, characterTwist f χ d *
      ∑ m ∈ Finset.Ioc 0 (N / d), characterTwist g χ m
  rw [characterTwist_mul]
  exact ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (characterTwist f χ) (characterTwist g χ) N

/-- Three-factor version of the finite twisted hyperbola identity. -/
theorem sum_characterTwist_mul_mul_eq_sum_sum_sum {q : ℕ}
    (f g h : ArithmeticFunction ℝ)
    (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (((f * g) * h) n : ℂ) * χ n) =
      ∑ d ∈ Finset.Ioc 0 N, (f d : ℂ) * χ d *
        ∑ e ∈ Finset.Ioc 0 (N / d), (g e : ℂ) * χ e *
          ∑ k ∈ Finset.Ioc 0 ((N / d) / e), (h k : ℂ) * χ k := by
  rw [mul_assoc, sum_characterTwist_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sum_characterTwist_mul_eq_sum_sum]

/-- Exact hyperbola expansion of the first Type-I term in Vaughan's
identity.  Its outer coefficient is supported on `d ≤ U`. -/
theorem vaughanTypeIOneSum_eq_hyperbola {q : ℕ}
    (x U : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIOneSum x U χ =
      ∑ d ∈ Finset.Ioc 0 x,
        (truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d : ℂ) *
          χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m := by
  rw [vaughanTypeIOneSum, vaughanTypeIOne]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  exact sum_characterTwist_mul_eq_sum_sum
    (truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U)
    ArithmeticFunction.log χ x

/-- Changing the prefix convention from `range` to `[1,N]` does not alter a
Dirichlet-character sum at a nontrivial modulus. -/
theorem character_sum_Icc_eq_range {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, χ n) = ∑ n ∈ Finset.range (N + 1), χ n := by
  have hzero : χ (0 : ZMod q) = 0 :=
    χ.map_zero' (by omega)
  rw [show Finset.range (N + 1) =
      insert 0 (Finset.Icc 1 N) by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega]
  rw [Finset.sum_insert (by simp), Nat.cast_zero, hzero, zero_add]

/-- Pólya--Vinogradov in the `[1,N]` prefix convention used by the
Bombieri--Vinogradov sums. -/
theorem primitive_character_sum_Icc_norm_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ n‖ ≤
      3 * Real.sqrt q * Real.log (2 * q) := by
  rw [character_sum_Icc_eq_range hq χ N]
  exact primitive_character_prefix_sum_norm_le hχ hq (N + 1)

/-- The total variation of `log` on the positive integers below `N`. -/
theorem sum_log_succ_sub_log_Ioc (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 (N - 1),
      (Real.log (n + 1 : ℕ) - Real.log n)) = Real.log N := by
  have hset : Finset.Ioc 0 (N - 1) =
      (Finset.range N).erase 0 := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_erase, Finset.mem_range]
    omega
  rw [hset]
  calc
    (∑ n ∈ (Finset.range N).erase 0,
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) =
        (∑ n ∈ (Finset.range N).erase 0,
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) +
          (Real.log ((0 + 1 : ℕ) : ℝ) - Real.log (0 : ℝ)) := by norm_num
    _ = ∑ n ∈ Finset.range N,
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) :=
      by
        simpa only [Nat.cast_zero] using
          ((Finset.range N).sum_erase_add (a := 0)
            (fun n => Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))
            (Finset.mem_range.mpr (by omega)))
    _ = Real.log (N : ℝ) - Real.log (0 : ℝ) := by
      convert (Finset.sum_range_sub
        (fun n : ℕ => Real.log (n : ℝ)) N) using 1
      all_goals norm_num
    _ = Real.log N := by rw [Real.log_zero, sub_zero]

/-- Abel summation turns the uniform Pólya--Vinogradov prefix bound into a
logarithmically weighted character-sum bound. -/
theorem primitive_character_log_sum_norm_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) (hN : 2 ≤ N) :
    ‖∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * χ n‖ ≤
      6 * Real.sqrt q * Real.log (2 * q) * Real.log N := by
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  let S : ℕ → ℂ := fun k => ∑ n ∈ Finset.range k, χ n
  have hprefix (k : ℕ) : ‖S k‖ ≤ B := by
    dsimp only [S, B]
    exact primitive_character_prefix_sum_norm_le hχ hq k
  have habel := Finset.sum_Ioc_by_parts
    (f := fun n : ℕ => (Real.log n : ℂ))
    (g := fun n : ℕ => χ n) (m := 0) (n := N) (by omega)
  have hlogone :
      ((Real.log (((0 + 1 : ℕ) : ℝ)) : ℂ)) = 0 := by norm_num
  simp only [smul_eq_mul] at habel
  rw [hlogone, zero_mul, sub_zero] at habel
  have habel' :
      (∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * χ n) =
        (Real.log N : ℂ) * S (N + 1) -
          ∑ n ∈ Finset.Ioc 0 (N - 1),
            ((Real.log (n + 1 : ℕ) - Real.log n : ℝ) : ℂ) * S (n + 1) := by
    simpa only [smul_eq_mul, S, Complex.ofReal_sub] using habel
  rw [habel']
  have hlogN : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hdelta (n : ℕ) (hn : n ∈ Finset.Ioc 0 (N - 1)) :
      0 ≤ Real.log (n + 1 : ℕ) - Real.log n := by
    have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
    exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hnpos)
      (by exact_mod_cast Nat.le_succ n))
  calc
    ‖(Real.log N : ℂ) * S (N + 1) -
        ∑ n ∈ Finset.Ioc 0 (N - 1),
          ((Real.log (n + 1 : ℕ) - Real.log n : ℝ) : ℂ) * S (n + 1)‖ ≤
        ‖(Real.log N : ℂ) * S (N + 1)‖ +
          ‖∑ n ∈ Finset.Ioc 0 (N - 1),
            ((Real.log (n + 1 : ℕ) - Real.log n : ℝ) : ℂ) * S (n + 1)‖ :=
      norm_sub_le _ _
    _ ≤ Real.log N * B +
        ∑ n ∈ Finset.Ioc 0 (N - 1),
          (Real.log (n + 1 : ℕ) - Real.log n) * B := by
      gcongr
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlogN]
        exact mul_le_mul_of_nonneg_left (hprefix (N + 1)) hlogN
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hdelta n hn)]
        exact mul_le_mul_of_nonneg_left (hprefix (n + 1)) (hdelta n hn)
    _ = 2 * B * Real.log N := by
      rw [← Finset.sum_mul, sum_log_succ_sub_log_Ioc N (by omega)]
      ring
    _ = 6 * Real.sqrt q * Real.log (2 * q) * Real.log N := by
      dsimp only [B]
      ring

/-- Totalized form of the logarithmically weighted bound. -/
theorem primitive_character_log_sum_norm_le_all
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc 0 N, (Real.log n : ℂ) * χ n‖ ≤
      6 * Real.sqrt q * Real.log (2 * q) *
        Real.log ((max 2 N : ℕ) : ℝ) := by
  by_cases hN : 2 ≤ N
  · simpa [max_eq_right hN] using
      primitive_character_log_sum_norm_le hχ hq N hN
  · have hsmall : N = 0 ∨ N = 1 := by omega
    have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
    have hnonneg :
        0 ≤ 6 * Real.sqrt q * Real.log (2 * q) * Real.log 2 := by
      positivity
    rcases hsmall with rfl | rfl <;> norm_num <;> exact hnonneg

/-- The exact first Type-I hyperbola sum with the outer support made
explicit. -/
theorem vaughanTypeIOneSum_eq_short_hyperbola {q : ℕ}
    (x U : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIOneSum x U χ =
      ∑ d ∈ Finset.Ioc 0 (min U x),
        (ArithmeticFunction.moebius d : ℂ) * χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m := by
  rw [vaughanTypeIOneSum_eq_hyperbola]
  let term : ℕ → ℂ := fun d =>
    (truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d : ℂ) *
      χ d *
        ∑ m ∈ Finset.Ioc 0 (x / d),
          (ArithmeticFunction.log m : ℂ) * χ m
  calc
    (∑ d ∈ Finset.Ioc 0 x,
        (truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U d : ℂ) *
          χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m) =
        ∑ d ∈ Finset.Ioc 0 (min U x), term d := by
      symm
      apply Finset.sum_subset
      · intro d hd
        have hd' := Finset.mem_Ioc.mp hd
        exact Finset.mem_Ioc.mpr ⟨hd'.1, hd'.2.trans (min_le_right U x)⟩
      · intro d hdx hdnot
        have hddata := Finset.mem_Ioc.mp hdx
        have hUd : U < d := by
          by_contra h
          exact hdnot (Finset.mem_Ioc.mpr
            ⟨hddata.1, le_min (le_of_not_gt h) hddata.2⟩)
        simp [term, truncateLE_apply, Nat.not_le.mpr hUd]
    _ = ∑ d ∈ Finset.Ioc 0 (min U x),
        (ArithmeticFunction.moebius d : ℂ) * χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdU : d ≤ U :=
        (Finset.mem_Ioc.mp hd).2.trans (min_le_left U x)
      simp [term, truncateLE_apply, hdU]

/-- Pointwise Type-I bound for the first Vaughan piece.  The important
feature is the short factor `min U x`. -/
theorem norm_vaughanTypeIOneSum_le
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    (x U : ℕ) (hx : 2 ≤ x) :
    ‖vaughanTypeIOneSum x U χ‖ ≤
      6 * (min U x : ℝ) * Real.sqrt q *
        Real.log (2 * q) * Real.log x := by
  rw [vaughanTypeIOneSum_eq_short_hyperbola]
  let C : ℝ := 6 * Real.sqrt q * Real.log (2 * q) * Real.log x
  have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  calc
    ‖∑ d ∈ Finset.Ioc 0 (min U x),
        (ArithmeticFunction.moebius d : ℂ) * χ d *
          ∑ m ∈ Finset.Ioc 0 (x / d),
            (ArithmeticFunction.log m : ℂ) * χ m‖ ≤
        ∑ d ∈ Finset.Ioc 0 (min U x),
          ‖(ArithmeticFunction.moebius d : ℂ) * χ d *
            ∑ m ∈ Finset.Ioc 0 (x / d),
              (ArithmeticFunction.log m : ℂ) * χ m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Ioc 0 (min U x), C := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hmax : max 2 (x / d) ≤ x :=
        max_le hx (Nat.div_le_self x d)
      have hlogmax :
          Real.log ((max 2 (x / d) : ℕ) : ℝ) ≤ Real.log x := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hmax)
      have hinner := primitive_character_log_sum_norm_le_all
        hχ hq (x / d)
      have hinnerC :
          ‖∑ m ∈ Finset.Ioc 0 (x / d),
              (ArithmeticFunction.log m : ℂ) * χ m‖ ≤ C := by
        exact hinner.trans (by
          dsimp only [C]
          gcongr)
      have hmu : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hchar : ‖χ d‖ ≤ 1 := DirichletCharacter.norm_le_one χ d
      rw [norm_mul, norm_mul]
      calc
        ‖(ArithmeticFunction.moebius d : ℂ)‖ * ‖χ d‖ *
            ‖∑ m ∈ Finset.Ioc 0 (x / d),
              (ArithmeticFunction.log m : ℂ) * χ m‖ ≤
            1 * 1 * C := by gcongr
        _ = C := by ring
    _ = (min U x : ℝ) * C := by simp
    _ = 6 * (min U x : ℝ) * Real.sqrt q *
          Real.log (2 * q) * Real.log x := by
      dsimp only [C]
      ring

/-- The short convolution occurring in Vaughan's second Type-I piece. -/
noncomputable def vaughanTypeIShortCoefficient (U V : ℕ) :
    ArithmeticFunction ℝ :=
  truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    truncateLE ArithmeticFunction.vonMangoldt V

theorem vaughanTypeITwo_eq_shortCoefficient (U V : ℕ) :
    vaughanTypeITwo U V =
      truncateLE ArithmeticFunction.vonMangoldt V -
        vaughanTypeIShortCoefficient U V * ArithmeticFunction.zeta := by
  rfl

/-- The short Type-I convolution is supported on products at most `U*V`. -/
theorem vaughanTypeIShortCoefficient_eq_zero_of_lt
    (U V n : ℕ) (hn : U * V < n) :
    vaughanTypeIShortCoefficient U V n = 0 := by
  rw [vaughanTypeIShortCoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hd : p.1 ≤ U
  · by_cases he : p.2 ≤ V
    · have hpUV : p.1 * p.2 ≤ U * V := Nat.mul_le_mul hd he
      omega
    · simp [truncateLE_apply, hd, he]
  · simp [truncateLE_apply, hd]

/-- Exact hyperbola expansion of Vaughan's second Type-I term. -/
theorem vaughanTypeITwoSum_eq_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeITwoSum x U V χ =
      (∑ n ∈ Finset.Ioc 0 x,
        (truncateLE ArithmeticFunction.vonMangoldt V n : ℂ) * χ n) -
      ∑ m ∈ Finset.Ioc 0 x,
        (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
          ∑ n ∈ Finset.Ioc 0 (x / m), χ n := by
  rw [vaughanTypeITwoSum, vaughanTypeITwo_eq_shortCoefficient]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply]
  push_cast
  simp_rw [add_mul, neg_mul]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    sum_characterTwist_mul_eq_sum_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : n ≠ 0 := (Finset.mem_Ioc.mp hn).1.ne'
  simp [ArithmeticFunction.zeta_apply, hnpos]

/-- The two genuinely short supports in Vaughan's second Type-I term made
explicit.  This is the form used for pointwise Pólya--Vinogradov estimates:
the direct von-Mangoldt piece has length at most `V`, and the outer
convolution variable has length at most `U*V`. -/
theorem vaughanTypeITwoSum_eq_short_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeITwoSum x U V χ =
      (∑ n ∈ Finset.Ioc 0 (min V x),
        (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) -
      ∑ m ∈ Finset.Ioc 0 (min (U * V) x),
        (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
          ∑ n ∈ Finset.Ioc 0 (x / m), χ n := by
  rw [vaughanTypeITwoSum_eq_hyperbola]
  congr 1
  · let term : ℕ → ℂ := fun n =>
      (truncateLE ArithmeticFunction.vonMangoldt V n : ℂ) * χ n
    calc
      (∑ n ∈ Finset.Ioc 0 x,
          (truncateLE ArithmeticFunction.vonMangoldt V n : ℂ) * χ n) =
          ∑ n ∈ Finset.Ioc 0 (min V x), term n := by
        symm
        apply Finset.sum_subset
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Ioc.mpr
            ⟨hn'.1, hn'.2.trans (min_le_right V x)⟩
        · intro n hnx hnnot
          have hndata := Finset.mem_Ioc.mp hnx
          have hVn : V < n := by
            by_contra h
            exact hnnot (Finset.mem_Ioc.mpr
              ⟨hndata.1, le_min (le_of_not_gt h) hndata.2⟩)
          simp [term, truncateLE_apply, Nat.not_le.mpr hVn]
      _ = ∑ n ∈ Finset.Ioc 0 (min V x),
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnV : n ≤ V :=
          (Finset.mem_Ioc.mp hn).2.trans (min_le_left V x)
        simp [term, truncateLE_apply, hnV]
  · let term : ℕ → ℂ := fun m =>
      (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
        ∑ n ∈ Finset.Ioc 0 (x / m), χ n
    change (∑ m ∈ Finset.Ioc 0 x, term m) =
      ∑ m ∈ Finset.Ioc 0 (min (U * V) x), term m
    symm
    apply Finset.sum_subset
    · intro m hm
      have hm' := Finset.mem_Ioc.mp hm
      exact Finset.mem_Ioc.mpr
        ⟨hm'.1, hm'.2.trans (min_le_right (U * V) x)⟩
    · intro m hmx hmnot
      have hmdata := Finset.mem_Ioc.mp hmx
      have hUVm : U * V < m := by
        by_contra h
        exact hmnot (Finset.mem_Ioc.mpr
          ⟨hmdata.1, le_min (le_of_not_gt h) hmdata.2⟩)
      dsimp only [term]
      rw [vaughanTypeIShortCoefficient_eq_zero_of_lt U V m hUVm]
      simp

/-- A cutoff-independent divisor bound for the short coefficient in
Vaughan's second Type-I term. -/
theorem abs_vaughanTypeIShortCoefficient_le
    (U V n : ℕ) :
    |vaughanTypeIShortCoefficient U V n| ≤
      (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanTypeIShortCoefficient]
  rw [vaughanTypeIShortCoefficient, ArithmeticFunction.mul_apply]
  calc
    |∑ p ∈ n.divisorsAntidiagonal,
        truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          truncateLE ArithmeticFunction.vonMangoldt V p.2| ≤
      ∑ p ∈ n.divisorsAntidiagonal,
        |truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          truncateLE ArithmeticFunction.vonMangoldt V p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, Real.log n := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1pos : 0 < p.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
      have hp2pos : 0 < p.2 :=
        Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
      have hp2dvd : p.2 ∣ n :=
        ⟨p.1, by simpa [mul_comm] using hpdata.1.symm⟩
      have hp2le : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp2dvd
      have hlogmono : Real.log (p.2 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp2pos) (by exact_mod_cast hp2le)
      have hmu :
          |truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| ≤ 1 := by
        rw [truncateLE_apply]
        split_ifs
        · change |((ArithmeticFunction.moebius p.1 : ℤ) : ℝ)| ≤ 1
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
        · norm_num
      have hlambda :
          |truncateLE ArithmeticFunction.vonMangoldt V p.2| ≤ Real.log n := by
        rw [truncateLE_apply]
        split_ifs
        · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact ArithmeticFunction.vonMangoldt_le_log.trans hlogmono
        · rw [abs_zero]
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      rw [abs_mul]
      calc
        |truncateLE (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| *
            |truncateLE ArithmeticFunction.vonMangoldt V p.2| ≤
            1 * Real.log n := by gcongr
        _ = Real.log n := one_mul _
    _ = (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by simp

/-- Divisor-square `L²` bound for the short Type-I coefficient. -/
theorem vaughanTypeIShortCoefficient_sq_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V X : ℕ), 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2) ≤
          C * (X : ℝ) * (Real.log (X : ℝ)) ^ 5 := by
  rcases Chen.lemma6_divisorSquareMean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro U V X hX
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 *
          (Real.log (X : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hndata := Finset.mem_Icc.mp hn
      have hlogn : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hndata.1)
      have hlogmono : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast hndata.2)
      have habs := abs_vaughanTypeIShortCoefficient_le U V n
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc
        |vaughanTypeIShortCoefficient U V n| ^ 2 ≤
            ((n.divisorsAntidiagonal.card : ℝ) * Real.log n) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ ≤ ((n.divisorsAntidiagonal.card : ℝ) * Real.log X) ^ 2 := by
          gcongr
        _ = (n.divisorsAntidiagonal.card : ℝ) ^ 2 *
            (Real.log X) ^ 2 := by ring
    _ = (∑ n ∈ Finset.Icc 1 X,
          (n.divisorsAntidiagonal.card : ℝ) ^ 2) *
        (Real.log X) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (C * (X : ℝ) * (Real.log X) ^ 3) *
        (Real.log X) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (hmean X hX) (sq_nonneg _)
    _ = C * (X : ℝ) * (Real.log (X : ℝ)) ^ 5 := by ring

/-- A deliberately coarse `L¹` consequence of the divisor-square estimate.
It is sufficient here because the support length `U*V` will be chosen
polylogarithmic in the final Bombieri--Vinogradov assembly. -/
theorem vaughanTypeIShortCoefficient_norm_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V W : ℕ), W = U * V → 2 ≤ W →
      (∑ m ∈ Finset.Ioc 0 W,
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖) ≤
        C * (W : ℝ) * (Real.log (W : ℝ)) ^ 5 + (W : ℝ) := by
  rcases vaughanTypeIShortCoefficient_sq_mean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro U V W hW hW2
  have hsets : Finset.Ioc 0 W = Finset.Icc 1 W := by
    ext m
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  calc
    (∑ m ∈ Finset.Ioc 0 W,
        ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖) ≤
        ∑ m ∈ Finset.Ioc 0 W,
          (‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      nlinarith [sq_nonneg
        (‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ - (1 / 2 : ℝ))]
    _ = (∑ m ∈ Finset.Icc 1 W,
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ ^ 2) + (W : ℝ) := by
      rw [Finset.sum_add_distrib, hsets]
      simp
    _ ≤ C * (W : ℝ) * (Real.log (W : ℝ)) ^ 5 + (W : ℝ) := by
      exact add_le_add_left (hmean U V W hW2) _

/-- Complete pointwise estimate for Vaughan's second Type-I piece.  Both
outer supports are short; the remaining character prefix is bounded by
Pólya--Vinogradov. -/
theorem norm_vaughanTypeITwoSum_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → 2 ≤ q →
        ∀ (x U V : ℕ), 2 ≤ x → 2 ≤ U * V → U * V ≤ x →
          ‖vaughanTypeITwoSum x U V χ‖ ≤
            (V : ℝ) * Real.log x +
              3 * (C * ((U * V : ℕ) : ℝ) *
                    (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                      ((U * V : ℕ) : ℝ)) *
                Real.sqrt q * Real.log (2 * q) := by
  rcases vaughanTypeIShortCoefficient_norm_sum_le with ⟨C, hC, hcoeff⟩
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ hq x U V hx hUV2 hUVx
  have hUpos : 1 ≤ U := by
    by_contra h
    have : U = 0 := by omega
    subst U
    simp at hUV2
  have hVx : V ≤ x := by
    have hVUV : V ≤ U * V := by
      simpa using Nat.mul_le_mul_right V hUpos
    exact hVUV.trans hUVx
  have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
  have hpvFactor : 0 ≤ 3 * Real.sqrt (q : ℝ) * Real.log (2 * q) := by
    positivity
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hdirect :
      ‖∑ n ∈ Finset.Ioc 0 V,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ ≤
        (V : ℝ) * Real.log x := by
    calc
      ‖∑ n ∈ Finset.Ioc 0 V,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ ≤
          ∑ n ∈ Finset.Ioc 0 V,
            ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc 0 V, Real.log x := by
        apply Finset.sum_le_sum
        intro n hn
        have hndata := Finset.mem_Ioc.mp hn
        have hnx : n ≤ x := hndata.2.trans hVx
        have hlogn : Real.log (n : ℝ) ≤ Real.log (x : ℝ) :=
          Real.log_le_log (by exact_mod_cast hndata.1)
            (by exact_mod_cast hnx)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc
          ArithmeticFunction.vonMangoldt n * ‖χ n‖ ≤
              Real.log n * 1 := by
            gcongr
            · exact ArithmeticFunction.vonMangoldt_le_log
            · exact DirichletCharacter.norm_le_one χ n
          _ ≤ Real.log x := by simpa using hlogn
      _ = (V : ℝ) * Real.log x := by simp
  have hpv (m : ℕ) :
      ‖∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ ≤
        3 * Real.sqrt q * Real.log (2 * q) := by
    have hset : Finset.Ioc 0 (x / m) = Finset.Icc 1 (x / m) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hset]
    exact primitive_character_sum_Icc_norm_le hχ hq (x / m)
  have hcoeff' := hcoeff U V (U * V) rfl hUV2
  have hhyper :
      ‖∑ m ∈ Finset.Ioc 0 (U * V),
          (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
            ∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ ≤
        3 * (C * ((U * V : ℕ) : ℝ) *
              (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
          Real.sqrt q * Real.log (2 * q) := by
    calc
      ‖∑ m ∈ Finset.Ioc 0 (U * V),
          (vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
            ∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ ≤
          ∑ m ∈ Finset.Ioc 0 (U * V),
            ‖(vaughanTypeIShortCoefficient U V m : ℂ) * χ m *
              ∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Ioc 0 (U * V),
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ *
            (3 * Real.sqrt q * Real.log (2 * q)) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul, norm_mul]
        have hchar := DirichletCharacter.norm_le_one χ m
        have hinner := hpv m
        calc
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ * ‖χ m‖ *
              ‖∑ n ∈ Finset.Ioc 0 (x / m), χ n‖ ≤
              ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ * 1 *
                (3 * Real.sqrt q * Real.log (2 * q)) := by
            gcongr
          _ = ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖ *
                (3 * Real.sqrt q * Real.log (2 * q)) := by ring
      _ = (∑ m ∈ Finset.Ioc 0 (U * V),
          ‖(vaughanTypeIShortCoefficient U V m : ℂ)‖) *
            (3 * Real.sqrt q * Real.log (2 * q)) := by
        rw [Finset.sum_mul]
      _ ≤ (C * ((U * V : ℕ) : ℝ) *
              (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
            (3 * Real.sqrt q * Real.log (2 * q)) := by
        apply mul_le_mul_of_nonneg_right hcoeff'
        exact hpvFactor
      _ = 3 * (C * ((U * V : ℕ) : ℝ) *
              (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                ((U * V : ℕ) : ℝ)) *
            Real.sqrt q * Real.log (2 * q) := by ring
  rw [vaughanTypeITwoSum_eq_short_hyperbola,
    min_eq_left hVx, min_eq_left hUVx]
  exact (norm_sub_le _ _).trans (add_le_add hdirect hhyper)

/-- Dyadic rectangular large-sieve estimate for the short coefficient in
Vaughan's second Type-I term. -/
theorem vaughanTypeIShortRectangleMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (U V D Q M N K L : ℕ), 1 ≤ D → D ≤ Q → 2 ≤ M + N →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N
                (fun n => (vaughanTypeIShortCoefficient U V n : ℂ)) i.2‖ *
              ‖characterIntervalSum K L (fun _ => (1 : ℂ)) i.2‖) ^ 2 ≤
          (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
              (C₁ * ((M + N : ℕ) : ℝ) *
                (Real.log ((M + N : ℕ) : ℝ)) ^ 5)) *
            (C₀ * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) * (L : ℝ)) := by
  rcases bilinearCharacterMean_dyadic_sq_le with ⟨C₀, hC₀, hbilinear⟩
  rcases vaughanTypeIShortCoefficient_sq_mean with ⟨C₁, hC₁, hcoeffMean⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro U V D Q M N K L hD hDQ hMN
  have hcoeff :
      (∑ n ∈ Finset.Ioc M (M + N),
        ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2) ≤
          C₁ * ((M + N : ℕ) : ℝ) *
            (Real.log ((M + N : ℕ) : ℝ)) ^ 5 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 (M + N),
          ‖(vaughanTypeIShortCoefficient U V n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 5 :=
        hcoeffMean U V (M + N) hMN
  have hbase := hbilinear D Q M N K L
    (fun n => (vaughanTypeIShortCoefficient U V n : ℂ))
    (fun _ => (1 : ℂ)) hD hDQ
  refine hbase.trans ?_
  apply mul_le_mul
  · gcongr
  · simp
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (mul_nonneg (mul_nonneg hC₁.le (Nat.cast_nonneg (M + N)))
        (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ M + N by omega))) 5))

end Chen.BombieriVinogradov

end

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.MeanValue -/

section

open Filter Real
open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Primitive-character mean value

This file performs the exact triangle-inequality reduction from the adjusted
von-Mangoldt sums to the three pieces of Vaughan's identity.  The remaining
analytic task is to estimate the two Type-I means and the Type-II mean on
dyadic rectangles.
-/

theorem adjustedTwistedPsi_eq_vaughanTypeSums_of_primitive
    {q : ℕ} (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (x U V : ℕ) :
    adjustedTwistedPsi x χ =
      vaughanTypeIOneSum x U χ + vaughanTypeITwoSum x U V χ +
        vaughanTypeIISum x U V χ := by
  letI : NeZero q := ⟨by omega⟩
  have hχne : χ ≠ 1 := by
    intro hχone
    subst χ
    have hone : (1 : ℕ) = q := by
      calc
        1 = (1 : DirichletCharacter ℂ q).conductor := by
          symm
          exact DirichletCharacter.conductor_one
        _ = q := hχ
    omega
  rw [adjustedTwistedPsi, if_neg hχne, sub_zero,
    twistedPsi_eq_vaughanTypes x U V χ]

theorem norm_adjustedTwistedPsi_le_vaughanTypeSums
    {q : ℕ} (hq : 1 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (x U V : ℕ) :
    ‖adjustedTwistedPsi x χ‖ ≤
      ‖vaughanTypeIOneSum x U χ‖ + ‖vaughanTypeITwoSum x U V χ‖ +
        ‖vaughanTypeIISum x U V χ‖ := by
  rw [adjustedTwistedPsi_eq_vaughanTypeSums_of_primitive
    hq χ hχ x U V]
  exact norm_add_le_of_le (norm_add_le _ _) (le_refl _)

/-- Primitive-character mean on a conductor interval `(D,Q]`. -/
noncomputable def primitiveAdjustedMean (x D Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0

noncomputable def primitiveTypeIOneMean (x U D Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0

noncomputable def primitiveTypeITwoMean (x U V D Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0

noncomputable def primitiveTypeIIMean (x U V D Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      if χ.IsPrimitive then ‖vaughanTypeIISum x U V χ‖ else 0

theorem primitiveAdjustedMean_eq_characterIndicesIoc
    (x D Q : ℕ) :
    primitiveAdjustedMean x D Q =
      ∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * ‖adjustedTwistedPsi x i.2‖ := by
  rw [primitiveAdjustedMean,
    sum_characterIndicesIoc_primitiveDyadicWeight_eq]

theorem primitiveTypeIOneMean_eq_characterIndicesIoc
    (x U D Q : ℕ) :
    primitiveTypeIOneMean x U D Q =
      ∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * ‖vaughanTypeIOneSum x U i.2‖ := by
  rw [primitiveTypeIOneMean,
    sum_characterIndicesIoc_primitiveDyadicWeight_eq]

theorem primitiveTypeITwoMean_eq_characterIndicesIoc
    (x U V D Q : ℕ) :
    primitiveTypeITwoMean x U V D Q =
      ∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * ‖vaughanTypeITwoSum x U V i.2‖ := by
  rw [primitiveTypeITwoMean,
    sum_characterIndicesIoc_primitiveDyadicWeight_eq]

theorem primitiveTypeIIMean_eq_characterIndicesIoc
    (x U V D Q : ℕ) :
    primitiveTypeIIMean x U V D Q =
      ∑ i ∈ characterIndicesIoc D Q,
        primitiveDyadicWeight i * ‖vaughanTypeIISum x U V i.2‖ := by
  rw [primitiveTypeIIMean,
    sum_characterIndicesIoc_primitiveDyadicWeight_eq]

theorem primitiveAdjustedMean_nonneg (x D Q : ℕ) :
    0 ≤ primitiveAdjustedMean x D Q := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun χ _ => by split_ifs <;> positivity)

/-- Exact reduction of the primitive mean to Vaughan's three pieces. -/
theorem primitiveAdjustedMean_le_vaughanTypeMeans
    (x U V D Q : ℕ) (hD : 1 ≤ D) :
    primitiveAdjustedMean x D Q ≤
      primitiveTypeIOneMean x U D Q +
        primitiveTypeITwoMean x U V D Q +
          primitiveTypeIIMean x U V D Q := by
  rw [primitiveAdjustedMean, primitiveTypeIOneMean,
    primitiveTypeITwoMean, primitiveTypeIIMean]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  have hqD := (Finset.mem_Ioc.mp hq).1
  have hq1 : 1 < q := lt_of_le_of_lt hD hqD
  have hsum :
      (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) ≤
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) +
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) +
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIISum x U V χ‖ else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro χ hχmem
    by_cases hχ : χ.IsPrimitive
    · simp only [hχ, if_true]
      exact norm_adjustedTwistedPsi_le_vaughanTypeSums
        hq1 χ hχ x U V
    · simp [hχ]
  calc
    (Nat.totient q : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖adjustedTwistedPsi x χ‖ else 0) ≤
      (Nat.totient q : ℝ)⁻¹ *
        ((∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) +
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) +
        (∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIISum x U V χ‖ else 0)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Nat.totient q : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q,
            if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) +
        (Nat.totient q : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q,
            if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) +
        (Nat.totient q : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ q,
            if χ.IsPrimitive then ‖vaughanTypeIISum x U V χ‖ else 0) := by
      ring

/-- The first Vaughan Type-I piece is short enough to be summed over the
whole conductor interval using the pointwise Pólya--Vinogradov bound.  The
factor `1/φ(q)` cancels the number of characters modulo `q`; bounding every
remaining occurrence of `q` by `Q` gives the displayed uniform estimate. -/
theorem primitiveTypeIOneMean_le
    (x U D Q : ℕ) (hx : 2 ≤ x) (hD : 1 ≤ D) (hDQ : D ≤ Q) :
    primitiveTypeIOneMean x U D Q ≤
      6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
        Real.log (2 * Q) * Real.log x := by
  let A : ℝ :=
    6 * (min U x : ℝ) * Real.sqrt Q *
      Real.log (2 * Q) * Real.log x
  have hlogQ : 0 ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * Q by omega))
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  rw [primitiveTypeIOneMean]
  calc
    (∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) ≤
        ∑ _q ∈ Finset.Ioc D Q, A := by
      apply Finset.sum_le_sum
      intro q hqmem
      have hqdata := Finset.mem_Ioc.mp hqmem
      have hq2 : 2 ≤ q := by omega
      have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
      letI : NeZero q := ⟨by omega⟩
      have hpoint :
          ∀ χ : DirichletCharacter ℂ q,
            (if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) ≤ A := by
        intro χ
        by_cases hχ : χ.IsPrimitive
        · rw [if_pos hχ]
          have hraw := norm_vaughanTypeIOneSum_le hχ hq2 x U hx
          refine hraw.trans ?_
          dsimp only [A]
          have hsqrt : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) := by
            exact Real.sqrt_le_sqrt (by exact_mod_cast hqdata.2)
          have hlog : Real.log (2 * (q : ℝ)) ≤
              Real.log (2 * (Q : ℝ)) := by
            apply Real.log_le_log
            · positivity
            · exact_mod_cast Nat.mul_le_mul_left 2 hqdata.2
          gcongr
        · rw [if_neg hχ]
          exact hA
      have hsum :
          (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) ≤
            ∑ _χ : DirichletCharacter ℂ q, A := by
        exact Finset.sum_le_sum fun χ _ => hpoint χ
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have htot : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
      calc
        (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖vaughanTypeIOneSum x U χ‖ else 0) ≤
            (q.totient : ℝ)⁻¹ *
              ∑ _χ : DirichletCharacter ℂ q, A :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htot.le)
        _ = A := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
          field_simp
    _ = ((Finset.Ioc D Q).card : ℝ) * A := by simp
    _ ≤ (Q : ℝ) * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast (by
        simp only [Nat.card_Ioc]
        omega : (Finset.Ioc D Q).card ≤ Q)
    _ = 6 * (Q : ℝ) * (min U x : ℝ) * Real.sqrt Q *
          Real.log (2 * Q) * Real.log x := by
      dsimp only [A]
      ring

/-- Conductor-interval mean bound for Vaughan's second Type-I piece.  As in
`primitiveTypeIOneMean_le`, the reciprocal-totient weight cancels the number
of characters, after which the pointwise short-support estimate is made
uniform by replacing `q` with `Q`. -/
theorem primitiveTypeITwoMean_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x U V D Q : ℕ), 2 ≤ x → 1 ≤ D → D ≤ Q →
        2 ≤ U * V → U * V ≤ x →
          primitiveTypeITwoMean x U V D Q ≤
            (Q : ℝ) *
              ((V : ℝ) * Real.log x +
                3 * (C * ((U * V : ℕ) : ℝ) *
                      (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                        ((U * V : ℕ) : ℝ)) *
                  Real.sqrt Q * Real.log (2 * Q)) := by
  rcases norm_vaughanTypeITwoSum_le with ⟨C, hC, hpointwise⟩
  refine ⟨C, hC, ?_⟩
  intro x U V D Q hx hD hDQ hUV2 hUVx
  let B : ℝ :=
    (V : ℝ) * Real.log x +
      3 * (C * ((U * V : ℕ) : ℝ) *
            (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
              ((U * V : ℕ) : ℝ)) *
        Real.sqrt Q * Real.log (2 * Q)
  have hlogx : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hlogUV : 0 ≤ Real.log ((U * V : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ U * V by omega))
  have hlogQ : 0 ≤ Real.log (2 * (Q : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * Q by omega))
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  rw [primitiveTypeITwoMean]
  calc
    (∑ q ∈ Finset.Ioc D Q, (Nat.totient q : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) ≤
        ∑ _q ∈ Finset.Ioc D Q, B := by
      apply Finset.sum_le_sum
      intro q hqmem
      have hqdata := Finset.mem_Ioc.mp hqmem
      have hq2 : 2 ≤ q := by omega
      letI : NeZero q := ⟨by omega⟩
      have hcharBound :
          ∀ χ : DirichletCharacter ℂ q,
            (if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) ≤ B := by
        intro χ
        by_cases hχ : χ.IsPrimitive
        · rw [if_pos hχ]
          have hraw := hpointwise q inferInstance χ hχ hq2
            x U V hx hUV2 hUVx
          refine hraw.trans ?_
          dsimp only [B]
          have hsqrt : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) :=
            Real.sqrt_le_sqrt (by exact_mod_cast hqdata.2)
          have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) :=
            Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
          have hlog : Real.log (2 * (q : ℝ)) ≤
              Real.log (2 * (Q : ℝ)) := by
            apply Real.log_le_log
            · positivity
            · exact_mod_cast Nat.mul_le_mul_left 2 hqdata.2
          gcongr
        · rw [if_neg hχ]
          exact hB
      have hsum :
          (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) ≤
            ∑ _χ : DirichletCharacter ℂ q, B :=
        Finset.sum_le_sum fun χ _ => hcharBound χ
      have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
        rw [← Nat.card_eq_fintype_card]
        exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
      have htot : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
      calc
        (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q,
              if χ.IsPrimitive then ‖vaughanTypeITwoSum x U V χ‖ else 0) ≤
            (q.totient : ℝ)⁻¹ *
              ∑ _χ : DirichletCharacter ℂ q, B :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr htot.le)
        _ = B := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
          field_simp
    _ = ((Finset.Ioc D Q).card : ℝ) * B := by simp
    _ ≤ (Q : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast (by
        simp only [Nat.card_Ioc]
        omega : (Finset.Ioc D Q).card ≤ Q)
    _ = (Q : ℝ) *
          ((V : ℝ) * Real.log x +
            3 * (C * ((U * V : ℕ) : ℝ) *
                  (Real.log ((U * V : ℕ) : ℝ)) ^ 5 +
                    ((U * V : ℕ) : ℝ)) *
              Real.sqrt Q * Real.log (2 * Q)) := by
      rfl

end Chen.BombieriVinogradov

end

/-! ## ChenTheorem.Lemma9.BombieriVinogradov.TypeII -/

section

open scoped Classical

namespace Chen.BombieriVinogradov

/-!
# Type-II structure for Bombieri--Vinogradov

This file packages the two long factors in Vaughan's identity into a single
coefficient, proves its exact support, and exposes the remaining zeta factor
as a finite hyperbola sum.  This is the input for the subsequent dyadic
rectangle decomposition and character large sieve.
-/

/-- The convolution coefficient carried by the two long variables in
Vaughan's Type-II term. -/
noncomputable def vaughanTypeIICoefficient (U V : ℕ) :
    ArithmeticFunction ℝ :=
  truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    truncateGT ArithmeticFunction.vonMangoldt V

theorem vaughanTypeII_eq_coefficient_mul_zeta (U V : ℕ) :
    vaughanTypeII U V =
      vaughanTypeIICoefficient U V * ArithmeticFunction.zeta := by
  rfl

/-- The standard left factor in the genuinely bilinear form of Vaughan's
Type-II term.  Associating the zeta factor here, rather than after the two
long variables have already been convolved, keeps both variables visible. -/
noncomputable def vaughanTypeIILeftCoefficient (U : ℕ) :
    ArithmeticFunction ℝ :=
  truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
    ArithmeticFunction.zeta

theorem vaughanTypeII_eq_leftCoefficient_mul_longLambda (U V : ℕ) :
    vaughanTypeII U V =
      vaughanTypeIILeftCoefficient U *
        truncateGT ArithmeticFunction.vonMangoldt V := by
  rw [vaughanTypeII, vaughanTypeIILeftCoefficient]
  ac_rfl

/-- The left Type-II coefficient has no support at or below its cutoff. -/
theorem vaughanTypeIILeftCoefficient_eq_zero_of_le
    (U n : ℕ) (hn : n ≤ U) :
    vaughanTypeIILeftCoefficient U n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [vaughanTypeIILeftCoefficient]
  rw [vaughanTypeIILeftCoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
  have hp1dvd : p.1 ∣ n := ⟨p.2, hpdata.1.symm⟩
  have hp1le : p.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp1dvd
  have hp1U : p.1 ≤ U := hp1le.trans hn
  simp [truncateGT_apply, Nat.not_lt.mpr hp1U]

/-- Pointwise divisor bound for the visible left Type-II coefficient. -/
theorem abs_vaughanTypeIILeftCoefficient_le
    (U n : ℕ) :
    |vaughanTypeIILeftCoefficient U n| ≤
      (n.divisorsAntidiagonal.card : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanTypeIILeftCoefficient]
  rw [vaughanTypeIILeftCoefficient, ArithmeticFunction.mul_apply]
  calc
    |∑ p ∈ n.divisorsAntidiagonal,
        truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          ArithmeticFunction.zeta p.2| ≤
        ∑ p ∈ n.divisorsAntidiagonal,
          |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
            ArithmeticFunction.zeta p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2ne : p.2 ≠ 0 :=
        Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
      have hmu :
          |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| ≤ 1 := by
        rw [truncateGT_apply]
        split_ifs
        · change |((ArithmeticFunction.moebius p.1 : ℤ) : ℝ)| ≤ 1
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
        · norm_num
      simpa [ArithmeticFunction.zeta_apply, hp2ne] using hmu
    _ = (n.divisorsAntidiagonal.card : ℝ) := by simp

/-- The divisor-square theorem gives the `L²` input for the standard visible
left factor, without the extra logarithm carried by the grouped coefficient. -/
theorem vaughanTypeIILeftCoefficient_sq_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (U X : ℕ), 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X,
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
        C * (X : ℝ) * (Real.log (X : ℝ)) ^ 3 := by
  rcases Chen.lemma6_divisorSquareMean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro U X hX
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 X,
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (abs_vaughanTypeIILeftCoefficient_le U n) 2
    _ ≤ C * (X : ℝ) * (Real.log (X : ℝ)) ^ 3 := hmean X hX

/-- The Type-II convolution vanishes below the product of its two strict
cutoffs. -/
theorem vaughanTypeIICoefficient_eq_zero_of_le
    (U V n : ℕ) (hn : n ≤ U * V) :
    vaughanTypeIICoefficient U V n = 0 := by
  rw [vaughanTypeIICoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hd : U < p.1
  · by_cases he : V < p.2
    · have huv : U * V < p.1 * p.2 :=
        Nat.mul_lt_mul_of_lt_of_lt hd he
      omega
    · simp [truncateGT_apply, hd, Nat.not_lt.mpr (le_of_not_gt he)]
  · simp [truncateGT_apply, Nat.not_lt.mpr (le_of_not_gt hd)]

/-- A cutoff-independent divisor bound for the Type-II coefficient. -/
theorem abs_vaughanTypeIICoefficient_le
    (U V n : ℕ) :
    |vaughanTypeIICoefficient U V n| ≤
      (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanTypeIICoefficient]
  rw [vaughanTypeIICoefficient, ArithmeticFunction.mul_apply]
  calc
    |∑ p ∈ n.divisorsAntidiagonal,
        truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          truncateGT ArithmeticFunction.vonMangoldt V p.2| ≤
      ∑ p ∈ n.divisorsAntidiagonal,
        |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1 *
          truncateGT ArithmeticFunction.vonMangoldt V p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, Real.log n := by
      apply Finset.sum_le_sum
      intro p hp
      have hpdata := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1pos : 0 < p.1 :=
        Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
      have hp2pos : 0 < p.2 :=
        Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
      have hp2dvd : p.2 ∣ n := ⟨p.1, by simpa [mul_comm] using hpdata.1.symm⟩
      have hp2le : p.2 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp2dvd
      have hlogmono : Real.log (p.2 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast hp2pos) (by exact_mod_cast hp2le)
      have hmu :
          |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| ≤ 1 := by
        rw [truncateGT_apply]
        split_ifs
        · change |((ArithmeticFunction.moebius p.1 : ℤ) : ℝ)| ≤ 1
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
        · norm_num
      have hlambda :
          |truncateGT ArithmeticFunction.vonMangoldt V p.2| ≤ Real.log n := by
        rw [truncateGT_apply]
        split_ifs
        · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact ArithmeticFunction.vonMangoldt_le_log.trans hlogmono
        · rw [abs_zero]
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      rw [abs_mul]
      calc
        |truncateGT (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U p.1| *
            |truncateGT ArithmeticFunction.vonMangoldt V p.2| ≤
            1 * Real.log n := by gcongr
        _ = Real.log n := one_mul _
    _ = (n.divisorsAntidiagonal.card : ℝ) * Real.log n := by simp

/-- The divisor-square mean gives the standard `L²` bound for Vaughan's
Type-II coefficient. -/
theorem vaughanTypeIICoefficient_sq_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ (U V X : ℕ), 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
          C * (X : ℝ) * (Real.log (X : ℝ)) ^ 5 := by
  rcases Chen.lemma6_divisorSquareMean with ⟨C, hC, hmean⟩
  refine ⟨C, hC, ?_⟩
  intro U V X hX
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  calc
    (∑ n ∈ Finset.Icc 1 X,
        ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 X,
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 *
          (Real.log (X : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hndata := Finset.mem_Icc.mp hn
      have hlogn : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hndata.1)
      have hlogmono : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast hndata.2)
      have habs := abs_vaughanTypeIICoefficient_le U V n
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc
        |vaughanTypeIICoefficient U V n| ^ 2 ≤
            ((n.divisorsAntidiagonal.card : ℝ) * Real.log n) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) habs 2
        _ ≤ ((n.divisorsAntidiagonal.card : ℝ) * Real.log X) ^ 2 := by
          gcongr
        _ = (n.divisorsAntidiagonal.card : ℝ) ^ 2 *
            (Real.log X) ^ 2 := by ring
    _ = (∑ n ∈ Finset.Icc 1 X,
          (n.divisorsAntidiagonal.card : ℝ) ^ 2) *
        (Real.log X) ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (C * (X : ℝ) * (Real.log X) ^ 3) *
        (Real.log X) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (hmean X hX) (sq_nonneg _)
    _ = C * (X : ℝ) * (Real.log (X : ℝ)) ^ 5 := by ring

/-- A Type-II dyadic rectangle, specialized to Vaughan's coefficient on one
side and the constant coefficient on the zeta side. -/
theorem vaughanTypeIIRectangleMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (U V D Q M N K L : ℕ), 1 ≤ D → D ≤ Q → 2 ≤ M + N →
        (∑ i ∈ characterIndicesIoc D Q,
            primitiveDyadicWeight i *
              ‖characterIntervalSum M N
                (fun n => (vaughanTypeIICoefficient U V n : ℂ)) i.2‖ *
              ‖characterIntervalSum K L (fun _ => (1 : ℂ)) i.2‖) ^ 2 ≤
          (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
              (C₁ * ((M + N : ℕ) : ℝ) *
                (Real.log ((M + N : ℕ) : ℝ)) ^ 5)) *
            (C₀ * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) * (L : ℝ)) := by
  rcases bilinearCharacterMean_dyadic_sq_le with ⟨C₀, hC₀, hbilinear⟩
  rcases vaughanTypeIICoefficient_sq_mean with ⟨C₁, hC₁, hcoeffMean⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro U V D Q M N K L hD hDQ hMN
  have hcoeff :
      (∑ n ∈ Finset.Ioc M (M + N),
        ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
          C₁ * ((M + N : ℕ) : ℝ) *
            (Real.log ((M + N : ℕ) : ℝ)) ^ 5 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 (M + N),
          ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 5 :=
        hcoeffMean U V (M + N) hMN
  have hbase := hbilinear D Q M N K L
    (fun n => (vaughanTypeIICoefficient U V n : ℂ))
    (fun _ => (1 : ℂ)) hD hDQ
  refine hbase.trans ?_
  apply mul_le_mul
  · gcongr
  · simp
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (mul_nonneg (mul_nonneg hC₁.le (Nat.cast_nonneg (M + N)))
        (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ M + N by omega))) 5))

/-- Rectangular large-sieve estimate for the standard visible Type-II
factors `μ_{>U}*1` and `Λ_{>V}`. -/
theorem vaughanTypeIIVisibleRectangleMean_sq_le :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (U D Q M N K L : ℕ),
        1 ≤ D → D ≤ Q → 2 ≤ M + N → 2 ≤ K + L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M N
                  (fun n => (vaughanTypeIILeftCoefficient U n : ℂ)) i.2‖ *
                ‖characterIntervalSum K L
                  (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) i.2‖) ^ 2 ≤
            (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
                (C₁ * ((M + N : ℕ) : ℝ) *
                  (Real.log ((M + N : ℕ) : ℝ)) ^ 3)) *
              (C₀ * ((Q : ℝ) + (L : ℝ) / (D : ℝ)) *
                ((L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2)) := by
  rcases bilinearCharacterMean_dyadic_sq_le with ⟨C₀, hC₀, hbilinear⟩
  rcases vaughanTypeIILeftCoefficient_sq_mean with ⟨C₁, hC₁, hleftMean⟩
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro U D Q M N K L hD hDQ hMN hKL
  have hleft :
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
        C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2) ≤
          ∑ n ∈ Finset.Icc 1 (M + N),
            ‖(vaughanTypeIILeftCoefficient U n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₁ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 :=
        hleftMean U (M + N) hMN
  have hlambda :
      (∑ n ∈ Finset.Ioc K (K + L),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) ≤
        (L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by
    calc
      (∑ n ∈ Finset.Ioc K (K + L),
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ^ 2) ≤
          ∑ _n ∈ Finset.Ioc K (K + L),
            (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hndata := Finset.mem_Ioc.mp hn
        have hnpos : 0 < n := by omega
        have hlogn : 0 ≤ Real.log (n : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
        have hlogmono : Real.log (n : ℝ) ≤ Real.log ((K + L : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hnpos)
            (by exact_mod_cast hndata.2)
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
          (ArithmeticFunction.vonMangoldt_le_log.trans hlogmono) 2
      _ = (L : ℝ) * (Real.log ((K + L : ℕ) : ℝ)) ^ 2 := by simp
  have hbase := hbilinear D Q M N K L
    (fun n => (vaughanTypeIILeftCoefficient U n : ℂ))
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) hD hDQ
  refine hbase.trans ?_
  apply mul_le_mul
  · gcongr
  · gcongr
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (mul_nonneg (mul_nonneg hC₁.le (Nat.cast_nonneg (M + N)))
        (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ M + N by omega))) 3))

/-- Type-II rectangle estimate with a character-dependent prefix in the
constant-coefficient factor.  This is the form needed at the staircase
boundary of a dyadic cover of `m*n ≤ x`. -/
theorem vaughanTypeIIMaximalRectangleMean_sq_le :
    ∃ C₀ C₁ C₂ : ℝ,
      0 < C₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (U V D Q M N K R L : ℕ),
        1 ≤ D → D ≤ Q → 2 ≤ M + N → R ≤ 2 ^ L →
          (∑ i ∈ characterIndicesIoc D Q,
              primitiveDyadicWeight i *
                ‖characterIntervalSum M N
                  (fun n => (vaughanTypeIICoefficient U V n : ℂ)) i.2‖ *
                Real.sqrt
                  (maxCharacterPrefixSq K R (fun _ => (1 : ℂ)) i.2)) ^ 2 ≤
            (C₀ * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
                (C₂ * ((M + N : ℕ) : ℝ) *
                  (Real.log ((M + N : ℕ) : ℝ)) ^ 5)) *
              (C₁ * (((L + 1 : ℕ) : ℝ) ^ 2) *
                ((Q : ℝ) + ((2 ^ L : ℕ) : ℝ) / (D : ℝ)) *
                  ((2 ^ L : ℕ) : ℝ)) := by
  rcases maximalBilinearCharacterMean_dyadic_sq_le with
    ⟨C₀, C₁, hC₀, hC₁, hmaximal⟩
  rcases vaughanTypeIICoefficient_sq_mean with ⟨C₂, hC₂, hcoeffMean⟩
  refine ⟨C₀, C₁, C₂, hC₀, hC₁, hC₂, ?_⟩
  intro U V D Q M N K R L hD hDQ hMN hR
  have hcoeff :
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
        C₂ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 5 := by
    calc
      (∑ n ∈ Finset.Ioc M (M + N),
          ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2) ≤
          ∑ n ∈ Finset.Icc 1 (M + N),
            ‖(vaughanTypeIICoefficient U V n : ℂ)‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
        · intro n hn hnot
          positivity
      _ ≤ C₂ * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 5 :=
        hcoeffMean U V (M + N) hMN
  have hbase := hmaximal D Q M N K R L
    (fun n => (vaughanTypeIICoefficient U V n : ℂ))
    (fun _ => (1 : ℂ)) hD hDQ hR
  refine hbase.trans ?_
  apply mul_le_mul
  · gcongr
  · simp
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg hC₁.le (sq_nonneg _)) (by positivity))
      (Finset.sum_nonneg fun n _ => sq_nonneg _)
  · exact mul_nonneg (mul_nonneg hC₀.le (by positivity))
      (mul_nonneg (mul_nonneg hC₂.le (Nat.cast_nonneg (M + N)))
        (pow_nonneg (Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ M + N by omega))) 5))

/-- Exact Type-II hyperbola expansion before dyadic subdivision. -/
theorem vaughanTypeIISum_eq_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ =
      ∑ m ∈ Finset.Ioc 0 x,
        (vaughanTypeIICoefficient U V m : ℂ) * χ m *
          ∑ n ∈ Finset.Ioc 0 (x / m), χ n := by
  rw [vaughanTypeIISum, vaughanTypeII_eq_coefficient_mul_zeta]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval, sum_characterTwist_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : n ≠ 0 := (Finset.mem_Ioc.mp hn).1.ne'
  simp [ArithmeticFunction.zeta_apply, hnpos]

/-- Standard two-long-variable form of Vaughan's Type-II sum.  Unlike the
grouped-coefficient expansion above, this exposes the separate supports
`l > U` and `m > V`, which is the form required by the bilinear large sieve. -/
theorem vaughanTypeIISum_eq_visible_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ =
      ∑ l ∈ Finset.Ioc U x,
        (vaughanTypeIILeftCoefficient U l : ℂ) * χ l *
          ∑ m ∈ Finset.Ioc V (x / l),
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ m := by
  rw [vaughanTypeIISum, vaughanTypeII_eq_leftCoefficient_mul_longLambda]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval, sum_characterTwist_mul_eq_sum_sum]
  let term : ℕ → ℂ := fun l =>
    (vaughanTypeIILeftCoefficient U l : ℂ) * χ l *
      ∑ m ∈ Finset.Ioc 0 (x / l),
        (truncateGT ArithmeticFunction.vonMangoldt V m : ℂ) * χ m
  calc
    (∑ l ∈ Finset.Ioc 0 x,
        (vaughanTypeIILeftCoefficient U l : ℂ) * χ l *
          ∑ m ∈ Finset.Ioc 0 (x / l),
            (truncateGT ArithmeticFunction.vonMangoldt V m : ℂ) * χ m) =
        ∑ l ∈ Finset.Ioc U x, term l := by
      symm
      apply Finset.sum_subset
      · intro l hl
        have hl' := Finset.mem_Ioc.mp hl
        exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt hl'.1, hl'.2⟩
      · intro l hlx hlnot
        have hldata := Finset.mem_Ioc.mp hlx
        have hlU : l ≤ U := by
          by_contra h
          exact hlnot (Finset.mem_Ioc.mpr ⟨lt_of_not_ge h, hldata.2⟩)
        dsimp only [term]
        rw [vaughanTypeIILeftCoefficient_eq_zero_of_le U l hlU]
        simp
    _ = ∑ l ∈ Finset.Ioc U x,
        (vaughanTypeIILeftCoefficient U l : ℂ) * χ l *
          ∑ m ∈ Finset.Ioc V (x / l),
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ m := by
      apply Finset.sum_congr rfl
      intro l hl
      dsimp only [term]
      congr 1
      let innerTerm : ℕ → ℂ := fun m =>
        (truncateGT ArithmeticFunction.vonMangoldt V m : ℂ) * χ m
      calc
        (∑ m ∈ Finset.Ioc 0 (x / l),
            (truncateGT ArithmeticFunction.vonMangoldt V m : ℂ) * χ m) =
            ∑ m ∈ Finset.Ioc V (x / l), innerTerm m := by
          symm
          apply Finset.sum_subset
          · intro m hm
            have hm' := Finset.mem_Ioc.mp hm
            exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt hm'.1, hm'.2⟩
          · intro m hmx hmnot
            have hmdata := Finset.mem_Ioc.mp hmx
            have hmV : m ≤ V := by
              by_contra h
              exact hmnot (Finset.mem_Ioc.mpr
                ⟨lt_of_not_ge h, hmdata.2⟩)
            simp [innerTerm, truncateGT_apply, Nat.not_lt.mpr hmV]
        _ = ∑ m ∈ Finset.Ioc V (x / l),
            (ArithmeticFunction.vonMangoldt m : ℂ) * χ m := by
          apply Finset.sum_congr rfl
          intro m hm
          have hmV : V < m := (Finset.mem_Ioc.mp hm).1
          simp [innerTerm, truncateGT_apply, hmV]

/-- The same expansion with the vanishing range `m ≤ U*V` removed. -/
theorem vaughanTypeIISum_eq_long_hyperbola {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ =
      ∑ m ∈ Finset.Ioc (U * V) x,
        (vaughanTypeIICoefficient U V m : ℂ) * χ m *
          ∑ n ∈ Finset.Ioc 0 (x / m), χ n := by
  rw [vaughanTypeIISum_eq_hyperbola]
  symm
  apply Finset.sum_subset
  · intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt hm'.1, hm'.2⟩
  · intro m hm hmlong
    have hmdata := Finset.mem_Ioc.mp hm
    have hmle : m ≤ U * V := by
      by_contra h
      exact hmlong (Finset.mem_Ioc.mpr ⟨lt_of_not_ge h, hmdata.2⟩)
    rw [vaughanTypeIICoefficient_eq_zero_of_le U V m hmle]
    simp

/-- The finite lattice region below the Type-II hyperbola. -/
noncomputable def typeIIHyperbolaPairs (x U V : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc (U * V) x ×ˢ Finset.Ioc 0 x).filter
    (fun p => p.1 * p.2 ≤ x)

/-- Exact two-variable form of the Type-II sum. -/
theorem vaughanTypeIISum_eq_pairSum {q : ℕ}
    (x U V : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTypeIISum x U V χ =
      ∑ p ∈ typeIIHyperbolaPairs x U V,
        (vaughanTypeIICoefficient U V p.1 : ℂ) * χ p.1 * χ p.2 := by
  rw [vaughanTypeIISum_eq_long_hyperbola]
  rw [typeIIHyperbolaPairs, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hm).1
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    constructor
    · intro hn
      exact ⟨⟨hn.1, hn.2.trans (Nat.div_le_self x m)⟩,
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hmpos).mp hn.2⟩
    · intro hn
      exact ⟨hn.1.1, (Nat.le_div_iff_mul_le hmpos).mpr (by
        simpa [Nat.mul_comm] using hn.2)⟩
  · intro n hn
    rfl

end Chen.BombieriVinogradov

end

