module

public import Green64.Library.Analysis.Estimates.Part003

@[expose] public section

/-!
# Weights / ActualSmallHaarJointZero

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSmallHaarJointZero -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 20000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Independent uniform probability density of a finite rectangle
of zero-coordinate conditions on the TRUE full small-prime Haar
torus, with the source per-coordinate modulus, not a made-up
independent numeric law. -/
private def smallZeroCoordDensity434
    (s : Finset P) (p : P) (z : ZMod (modulus p)) : ℝ :=
  (if p ∈ s then (if z = 0 then (1:ℝ) else 0) else 1) /
    (Fintype.card (ZMod (modulus p)):ℝ)

/-- Each coordinate is genuinely uniform: selecting zero costs
1 / modulus(p), while an unrestricted coordinate has total mass 1. -/
private theorem smallZeroCoordDensity_sum434
    (s : Finset P) (p : P) :
    (∑ z : ZMod (modulus p),
      smallZeroCoordDensity434 modulus s p z) =
      if p ∈ s then 1/(Fintype.card (ZMod (modulus p)):ℝ) else 1 := by
  classical
  unfold smallZeroCoordDensity434
  by_cases hp : p ∈ s
  · simp only [if_pos hp]
    rw [←Finset.sum_div]
    simp
  · simp only [if_neg hp]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hpos : (0:ℝ) < Fintype.card (ZMod (modulus p)) := by
      exact_mod_cast (Fintype.card_pos (α := ZMod (modulus p)))
    field_simp [ne_of_gt hpos]

/-- A genuine Haar point has product density over all its prime
coordinates; the normalisation is the exact full torus cardinality. -/
private theorem smallZeroCoordDensity_product434
    (s : Finset P) (y : SmallTorus modulus) :
    (∏ p : P, smallZeroCoordDensity434 modulus s p (y p)) =
    haarAtomMass modulus *
      (if ∀ p ∈ s, y p = 0 then (1:ℝ) else 0) := by
  classical
  let q : P → ℝ := fun p =>
    if p ∈ s then (if y p = 0 then 1 else 0) else 1
  have hcard :
      (∏ p : P, (Fintype.card (ZMod (modulus p)):ℝ)) =
      (Fintype.card (SmallTorus modulus):ℝ) := by
    simp only [SmallTorus,Fintype.card_pi,Nat.cast_prod]
  have hq :
      (∏ p : P, q p) =
      if ∀ p ∈ s, y p = 0 then (1:ℝ) else 0 := by
    by_cases hgood : ∀ p ∈ s, y p = 0
    · simp only [if_pos hgood]
      apply Finset.prod_eq_one
      intro p hp
      by_cases hps : p ∈ s
      · simp only [q,if_pos hps,if_pos (hgood p hps)]
      · simp only [q,if_neg hps]
    · simp only [if_neg hgood]
      push_neg at hgood
      rcases hgood with ⟨p,hp,hy⟩
      exact Finset.prod_eq_zero (Finset.mem_univ p)
        (by simp [q,hp,hy])
  unfold smallZeroCoordDensity434
  calc
    _ = (∏ p : P, q p) /
        (∏ p : P,(Fintype.card (ZMod (modulus p)):ℝ)) := by
        rw [Finset.prod_div_distrib]
    _ = (if ∀ p ∈ s, y p = 0 then (1:ℝ) else 0) /
        (Fintype.card (SmallTorus modulus):ℝ) := by
        rw [hq,hcard]
    _ = _ := by
        unfold haarAtomMass
        ring

/-- EXACT original SMALL Haar probability that every prime in an
arbitrary finite subset simultaneously has residue zero.
The result is the product of their true reciprocal moduli, not
a replacement measure or an assumed independence axiom. -/
theorem source_original_ACTUAL_SMALL_haar_joint_zero434
    (s : Finset P) :
    (∑ y : SmallTorus modulus, haarAtomMass modulus *
      (if ∀ p ∈ s, y p = 0 then (1:ℝ) else 0)) =
    ∏ p : P, (if p ∈ s then 1/(modulus p:ℝ) else 1) := by
  classical
  calc
    _ = ∑ y : SmallTorus modulus,
      ∏ p : P, smallZeroCoordDensity434 modulus s p (y p) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [smallZeroCoordDensity_product434]
    _ = ∏ p : P,∑ z : ZMod (modulus p),
      smallZeroCoordDensity434 modulus s p z := by
        exact (Fintype.prod_sum
          (f := fun p (z : ZMod (modulus p)) =>
            smallZeroCoordDensity434 modulus s p z)).symm
    _ = ∏ p : P, (if p ∈ s then
        1/(Fintype.card (ZMod (modulus p)):ℝ) else 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact smallZeroCoordDensity_sum434 modulus s p
    _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [ZMod.card]
end Green64Analytic.CorrelationSquare

end

end

