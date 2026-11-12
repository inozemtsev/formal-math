module

public import Green64.Library.Correlation.ArbitraryRootCompression

@[expose] public section

/-!
# Weights / FiniteBlockHolder

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FiniteBlockHolder -/

section

open scoped BigOperators
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The mixed-power finite Hölder inequality with its endpoint R=1.
Zero masses are allowed; no division by any block norm is used. -/
theorem b652_mixed_power_sum_holder434
    {ι : Type*} (s : Finset ι) (a d : ι → ℝ) (R : ℕ) (hR : 1 ≤ R)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hd : ∀ i ∈ s, 0 ≤ d i) :
    (∑ i ∈ s, (a i)^(1-(R:ℝ)⁻¹)*(d i)^((R:ℝ)⁻¹)) ≤
      (∑ i ∈ s, a i)^(1-(R:ℝ)⁻¹)*(∑ i ∈ s, d i)^((R:ℝ)⁻¹) := by
  by_cases h1 : R=1
  · simp [h1]
  have hgt : (1:ℝ) < R := by exact_mod_cast (show 1<R by omega)
  have hpos : (0:ℝ) < R := lt_trans zero_lt_one hgt
  let p : ℝ := 1-(R:ℝ)⁻¹
  let q : ℝ := (R:ℝ)⁻¹
  have hq : 0 < q := inv_pos.mpr hpos
  have hp : 0 < p := sub_pos.mpr ((inv_lt_one₀ hpos).mpr hgt)
  have hpq : p+q=1 := by dsimp [p,q]; ring
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s)
    (f := fun i => (a i)^p) (g := fun i => (d i)^q)
    (Real.holderConjugate_one_div hp hq hpq)
    (fun i hi => Real.rpow_nonneg (ha i hi) _)
    (fun i hi => Real.rpow_nonneg (hd i hi) _)
  have hpa : (∑ i ∈ s, ((a i)^p)^(1/p)) = ∑ i ∈ s, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (ha i hi), show p*(1/p)=1 by field_simp, Real.rpow_one]
  have hqd : (∑ i ∈ s, ((d i)^q)^(1/q)) = ∑ i ∈ s, d i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hd i hi), show q*(1/q)=1 by field_simp, Real.rpow_one]
  rw [hpa,hqd] at h
  simpa only [one_div_one_div] using h

private theorem b652_rpow_square434 (x a : ℝ) (hx : 0 ≤ x) :
    (x^a)^2 = x^(a*2) := by
  rw [← Real.rpow_natCast (x^a) 2, ← Real.rpow_mul hx]
  norm_num

/-- The three-exponent block Hölder step in S02, including R=1. The first
factor is the actual sum of second-endpoint squared norms, the second is
the actual sum of first-endpoint squared norms, and the last is the full
sum of block moments. No maximum block count or mark-fibre size occurs. -/
theorem b652_finite_block_holder434
    {ι : Type*} (s : Finset ι) (a b d : ι → ℝ) (R : ℕ) (hR : 1 ≤ R)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hd : ∀ i ∈ s, 0 ≤ d i) :
    (∑ i ∈ s, a i*(b i)^(1-(R:ℝ)⁻¹)*(d i)^((2*(R:ℝ))⁻¹)) ≤
      (∑ i ∈ s, (a i)^2)^((1:ℝ)/2) *
      (∑ i ∈ s, (b i)^2)^((1-(R:ℝ)⁻¹)/2) *
      (∑ i ∈ s, d i)^((2*(R:ℝ))⁻¹) := by
  have hRpos : (0:ℝ) < R := by exact_mod_cast (show 0<R by omega)
  let p : ℝ := 1-(R:ℝ)⁻¹
  let q : ℝ := (2*(R:ℝ))⁻¹
  have hsquare (i : ι) (hi : i∈s) :
      ((b i)^p*(d i)^q)^2 = ((b i)^2)^p*(d i)^((R:ℝ)⁻¹) := by
    rw [mul_pow, b652_rpow_square434 _ _ (hb i hi),
      b652_rpow_square434 _ _ (hd i hi)]
    congr 1
    · rw [← Real.rpow_natCast (b i) 2, ← Real.rpow_mul (hb i hi)]
      congr 1
      norm_num
      ring
    · congr 1
      dsimp [q]
      field_simp
  have hsum : (∑ i ∈ s, ((b i)^p*(d i)^q)^2) ≤
      (∑ i ∈ s, (b i)^2)^p*(∑ i ∈ s, d i)^((R:ℝ)⁻¹) := by
    calc
      _ = ∑ i ∈ s, ((b i)^2)^p*(d i)^((R:ℝ)⁻¹) :=
        Finset.sum_congr rfl hsquare
      _ ≤ _ := b652_mixed_power_sum_holder434 s (fun i => (b i)^2) d R hR
        (fun i _ => sq_nonneg _) hd
  have hB : 0 ≤ ∑ i ∈ s, (b i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hD : 0 ≤ ∑ i ∈ s, d i := Finset.sum_nonneg hd
  have he : Real.sqrt ((∑ i ∈ s, (b i)^2)^p*(∑ i ∈ s, d i)^((R:ℝ)⁻¹)) =
      (∑ i ∈ s, (b i)^2)^(p/2)*(∑ i ∈ s, d i)^q := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg hB _) (Real.rpow_nonneg hD _),
      ← Real.rpow_mul hB, ← Real.rpow_mul hD]
    congr 1
    · congr 1
      ring
    · congr 1
      dsimp [q]
      field_simp
  calc
    _ = ∑ i ∈ s, a i*((b i)^p*(d i)^q) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [p,q]
      ring
    _ ≤ Real.sqrt (∑ i ∈ s, (a i)^2)*Real.sqrt (∑ i ∈ s, ((b i)^p*(d i)^q)^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s a (fun i => (b i)^p*(d i)^q)
    _ ≤ Real.sqrt (∑ i ∈ s, (a i)^2)*
        Real.sqrt ((∑ i ∈ s, (b i)^2)^p*(∑ i ∈ s, d i)^((R:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _)
    _ = _ := by rw [he, Real.sqrt_eq_rpow]; dsimp [p,q]; ring
end Green64Analytic.SpectralEndpoint

end

end

