module

public import Green64.Library.Correlation.Part058
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.MulChar.Lemmas

@[expose] public section

/-!
# Correlation / Part059

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## TrueCofactorCrossCharacterGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The true cross-character phase for the two ORIGINAL cofactor labels at
one physical T Gram entry, with the conjugation exactly as it occurs AFTER
squaring a χ-dependent cofactor pairing. -/
noncomputable def sourceOriginalB437CofactorPairCharacter434
    (q m n : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  χ (m : ZMod q) * star (χ (n : ZMod q))

/-- Exact original residue-only character CROSS projector, not an
unconditional smallness assertion. Both cofactor cross-products are
independently preserved: n*m' ≡ m*n' (mod q), not m=n.
The assumption that m*n' is a unit is an explicit arithmetic input. -/
theorem source_original_B437_exact_cofactor_cross_character_projector434
    (q : ℕ) (hq : 0 < q) (m n mp np : ℕ)
    (hu : IsUnit ((m*np : ℕ) : ZMod q)) :
    ((q.totient : ℂ)⁻¹) *
      (∑ χ : DirichletCharacter ℂ q,
        star (sourceOriginalB437CofactorPairCharacter434 q m n χ) *
          sourceOriginalB437CofactorPairCharacter434 q mp np χ) =
    if ((m*np : ℕ) : ZMod q) = ((n*mp : ℕ) : ZMod q) then 1 else 0 := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hterm (χ : DirichletCharacter ℂ q) :
      star (sourceOriginalB437CofactorPairCharacter434 q m n χ) *
        sourceOriginalB437CofactorPairCharacter434 q mp np χ =
      χ (((m*np : ℕ) : ZMod q)⁻¹) * χ ((n*mp : ℕ) : ZMod q) := by
    have hstar : star (χ ((m*np : ℕ) : ZMod q)) =
        χ (((m*np : ℕ) : ZMod q)⁻¹) := by
      obtain ⟨u,huu⟩ := hu
      rw [← huu]
      simp only [MulChar.star_apply', MulChar.inv_apply,
        Ring.inverse_unit, ZMod.inv_coe_unit]
    calc
      _ = star (χ (m : ZMod q) * χ (np : ZMod q)) *
            (χ (n : ZMod q) * χ (mp : ZMod q)) := by
        dsimp [sourceOriginalB437CofactorPairCharacter434]
        simp only [map_mul,starRingEnd_apply,star_star]
        ring
      _ = star (χ ((m*np : ℕ) : ZMod q)) *
            χ ((n*mp : ℕ) : ZMod q) := by
        simp only [Nat.cast_mul,map_mul]
      _ = _ := by rw [hstar]
  simp_rw [hterm]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu]
  have ht : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.totient_pos.mpr hq)
  split_ifs <;> simp [ht]


/-- The positive 1/φ(q) character density used by the full T post-Cauchy
RMS agrees exactly with the complex inverse totient from orthogonality. -/
theorem source_original_B437_character_real_weight_cast434 (q : ℕ) :
    (‖((q.totient:ℂ)⁻¹)‖:ℂ) = (q.totient:ℂ)⁻¹ := by
  simp only [norm_inv, Complex.norm_natCast, Complex.ofReal_inv,
    Complex.ofReal_natCast]

/-- The normalized COMPLEX χ Gram of cofactor cross terms, with arbitrary
source/target coefficients kept inside the mean; only the TRUE residue
cross-products survive. No positivity, aggregation or counting surrogate. -/
theorem source_original_B437_cross_character_with_coeff434
    (q : ℕ) (hq : 0 < q) (m n mp np : ℕ)
    (hu : IsUnit ((m*np : ℕ) : ZMod q))
    (a b : ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
      (‖((q.totient:ℂ)⁻¹)‖:ℂ) *
        (star (a*sourceOriginalB437CofactorPairCharacter434 q m n χ) *
          (b*sourceOriginalB437CofactorPairCharacter434 q mp np χ))) =
    if ((m*np : ℕ) : ZMod q) = ((n*mp : ℕ) : ZMod q)
    then star a*b else 0 := by
  let w := (‖((q.totient:ℂ)⁻¹)‖:ℂ)
  let hunit := source_original_B437_exact_cofactor_cross_character_projector434
    q hq m n mp np hu
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
          (star a*b) *
          (w * (star (sourceOriginalB437CofactorPairCharacter434 q m n χ) *
            sourceOriginalB437CofactorPairCharacter434 q mp np χ)) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      dsimp only [w]
      simp only [star_mul, map_mul, starRingEnd_apply]
      ring
    _ = (star a*b) *
      (w*∑ χ : DirichletCharacter ℂ q,
          star (sourceOriginalB437CofactorPairCharacter434 q m n χ) *
            sourceOriginalB437CofactorPairCharacter434 q mp np χ) := by
      simp only [Finset.mul_sum]
    _ = (star a*b) * (if ((m*np : ℕ) : ZMod q) = ((n*mp : ℕ) : ZMod q)
       then 1 else 0) := by
      dsimp only [w]
      rw [source_original_B437_character_real_weight_cast434 q]
      exact congrArg (fun z : ℂ => (star a*b)*z) hunit
    _ = _ := by split_ifs <;> ring

/-- The exact REAL χ post-Cauchy cross contribution. This is the source
consumer of the cofactor RMS, not the assembled scalar χ-average. -/
theorem source_original_B437_cross_character_real_average434
    (q : ℕ) (hq : 0 < q) (m n mp np : ℕ)
    (hu : IsUnit ((m*np : ℕ) : ZMod q))
    (a b : ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
      ‖((q.totient:ℂ)⁻¹)‖ *
        (star (a*sourceOriginalB437CofactorPairCharacter434 q m n χ) *
          (b*sourceOriginalB437CofactorPairCharacter434 q mp np χ)).re) =
    if ((m*np : ℕ) : ZMod q) = ((n*mp : ℕ) : ZMod q)
    then (star a*b).re else 0 := by
  have h := congrArg Complex.re
    (source_original_B437_cross_character_with_coeff434 q hq m n mp np hu a b)
  rw [Complex.re_sum] at h
  have hterm (χ : DirichletCharacter ℂ q) :
      (((‖((q.totient:ℂ)⁻¹)‖:ℂ) *
        (star (a*sourceOriginalB437CofactorPairCharacter434 q m n χ) *
          (b*sourceOriginalB437CofactorPairCharacter434 q mp np χ)))).re =
      ‖((q.totient:ℂ)⁻¹)‖ *
        (star (a*sourceOriginalB437CofactorPairCharacter434 q m n χ) *
          (b*sourceOriginalB437CofactorPairCharacter434 q mp np χ)).re := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp_rw [hterm] at h
  by_cases he : ((m*np : ℕ) : ZMod q) = ((n*mp : ℕ) : ZMod q)
  · simpa only [if_pos he] using h
  · simpa only [if_neg he,Complex.zero_re] using h


/-- Expand the SQUARE of the original complex cofactor sum before the
character average: cross terms use conjugated i and un-conjugated j. -/
theorem source_original_B437_true_complex_square_sum_cross434
    {I : Type} (S : Finset I) (b : I → ℂ) :
    ‖∑ i ∈ S, b i‖^2 =
      ∑ i ∈ S, ∑ j ∈ S, (star (b i)*b j).re := by
  have he : ‖∑ i ∈ S, b i‖^2 =
      (star (∑ i ∈ S, b i)*(∑ i ∈ S, b i)).re := by
    simpa only [Complex.ofReal_re,Complex.normSq_eq_norm_sq,←Complex.star_def] using
      congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := ∑ i ∈ S, b i))
  rw [he,star_sum,Finset.sum_mul]
  simp_rw [Finset.mul_sum,Complex.re_sum]

/-- The EXACT normalized character **RMS** of any FINITE genuine cofactor
pair family. The surviving arithmetic is the residue-only cross Gram
`m_i*n_j ≡ n_i*m_j (mod q)` — not `m_i=n_i`, not scalar cancellation,
and not the stronger integer-ratio diagonal. No smallness is claimed.
This is the correct post-Cauchy algebraic target at |k|, including k=±2. -/
theorem source_original_B437_actual_residue_only_mean_square434
    {I : Type} (S : Finset I) (q : ℕ) (hq : 0 < q)
    (m n : I → ℕ) (a : I → ℂ)
    (hunit : ∀ i ∈ S, ∀ j ∈ S,
      IsUnit (((m i)*(n j):ℕ) : ZMod q)) :
    (∑ χ : DirichletCharacter ℂ q,
      ‖((q.totient:ℂ)⁻¹)‖ *
        ‖∑ i ∈ S, a i * sourceOriginalB437CofactorPairCharacter434
          q (m i) (n i) χ‖^2) =
    (∑ i ∈ S, ∑ j ∈ S,
      if (((m i)*(n j):ℕ) : ZMod q) =
         (((n i)*(m j):ℕ) : ZMod q)
      then (star (a i)*a j).re else 0) := by
  classical
  simp_rw [source_original_B437_true_complex_square_sum_cross434,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact source_original_B437_cross_character_real_average434
    q hq (m i) (n i) (m j) (n j) (hunit i hi j hj) (a i) (a j)


/-- At ORIGINAL k = ±2, modulus |k|=2 and all rough cofactors are odd.
Every cofactor cross-ratio survives the χ Gram. Therefore normalized
character RMS equals the norm-square of the entire UNPROJECTED complex
sum, not a logarithmically smaller diagonal. This is an exact k=2 no-go,
not an invented positive lower bound on the actual arithmetic amplitudes. -/
theorem source_original_B437_modulus_two_cofactor_RMS_no_gain434
    {I : Type} (S : Finset I) (m n : I → ℕ) (a : I → ℂ)
    (hodd : ∀ i ∈ S, Odd (m i) ∧ Odd (n i)) :
    (∑ χ : DirichletCharacter ℂ 2,
      ‖(((2 : ℕ).totient:ℂ)⁻¹)‖ *
        ‖∑ i ∈ S, a i * sourceOriginalB437CofactorPairCharacter434
          2 (m i) (n i) χ‖^2) = ‖∑ i ∈ S, a i‖^2 := by
  classical
  have hmod (v : ℕ) (hv : Odd v) : (v : ZMod 2) = 1 := by
    rcases hv with ⟨r,hr⟩
    rw [hr]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp only [h2,zero_mul,zero_add]
  have hunit : ∀ i ∈ S, ∀ j ∈ S,
      IsUnit (((m i)*(n j):ℕ) : ZMod 2) := by
    intro i hi j hj
    have hm := hmod (m i) (hodd i hi).1
    have hn := hmod (n j) (hodd j hj).2
    rw [Nat.cast_mul,hm,hn]
    exact isUnit_one
  have hcross (i j : I) (hi : i ∈ S) (hj : j ∈ S) :
      (((m i)*(n j):ℕ) : ZMod 2) =
        (((n i)*(m j):ℕ) : ZMod 2) := by
    simp only [Nat.cast_mul,
      hmod (m i) (hodd i hi).1,
      hmod (n j) (hodd j hj).2,
      hmod (n i) (hodd i hi).2,
      hmod (m j) (hodd j hj).1]
  have hbase := source_original_B437_actual_residue_only_mean_square434
    S 2 (by decide) m n a hunit
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S,
          if (((m i)*(n j):ℕ) : ZMod 2) =
             (((n i)*(m j):ℕ) : ZMod 2)
          then (star (a i)*a j).re else 0 := hbase
    _ = ∑ i ∈ S, ∑ j ∈ S, (star (a i)*a j).re := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (hcross i j hi hj)]
    _ = ‖∑ i ∈ S, a i‖^2 :=
      (source_original_B437_true_complex_square_sum_cross434 S a).symm
end Green64Analytic.CorrelationSquare

end

end

/-! ## LiteralPhysicalCofactorResidueGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exactly the original SOURCE03 C191/C6 SIGNED ν pairing, expanded into
cofactor indices m,n with the true α(m)χ(m)*conj(α(n)χ(n)) coefficients.
The χ-dependent source/target tests are the actual full free-BIG mark
arrays and retain the unmodified original harmonic law, moving Q, signed
Mellin ζ and physical Fourier θ. Distinct from native T shift 2k. -/
theorem source_original_B438_true_physical_cofactor_residue_Gram434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (hCoprime : ∀ t ∈ K, t.Coprime k.natAbs)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    let S := K.product K
    let A : ℕ × ℕ → ℂ := fun i =>
      (alpha i.1 * star (alpha i.2)) *
        sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient : ℂ)⁻¹)‖ *
        ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k
          (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ F)
          (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ Gt) ν‖^2) =
    ∑ i ∈ S, ∑ j ∈ S,
      if (((i.1*j.2 : ℕ) : ZMod k.natAbs) =
          ((i.2*j.1 : ℕ) : ZMod k.natAbs))
      then (star (A i)*A j).re else 0 := by
  dsimp only
  let S := K.product K
  let A : ℕ × ℕ → ℂ := fun i =>
    (alpha i.1 * star (alpha i.2)) *
      sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν
  have hunit : ∀ i ∈ S, ∀ j ∈ S,
      IsUnit (((i.1*j.2 : ℕ) : ZMod k.natAbs)) := by
    intro i hi j hj
    have hi1 : i.1 ∈ K := (Finset.mem_product.mp hi).1
    have hj2 : j.2 ∈ K := (Finset.mem_product.mp hj).2
    have him : IsUnit (i.1 : ZMod k.natAbs) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hCoprime i.1 hi1)
    have hjn : IsUnit (j.2 : ZMod k.natAbs) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hCoprime j.2 hj2)
    rw [Nat.cast_mul]
    exact him.mul hjn
  have hχ (χ : DirichletCharacter ℂ k.natAbs) :
      sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k
          (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ F)
          (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ Gt) ν =
      ∑ i ∈ S, A i * sourceOriginalB437CofactorPairCharacter434
          k.natAbs i.1 i.2 χ := by
    have h := source_original_B435_true_physical_cofactor_character_superposition434
      d J ell m hmJ Q hA hB xi ζ theta k K alpha χ F Gt ν
    change _ = ∑ i ∈ K.product K,
      ((alpha i.1 * star (alpha i.2)) *
       sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ Q hA hB
          xi ζ theta k (F i.1) (Gt i.2) ν) *
      (χ (i.1 : ZMod k.natAbs) * star (χ (i.2 : ZMod k.natAbs)))
    calc
      _ = ∑ t ∈ K, ∑ u ∈ K,
        (alpha t * χ (t : ZMod k.natAbs)) *
          star (alpha u * χ (u : ZMod k.natAbs)) *
          sourceOriginalTrueNuSignedFullPhysicalPairing434
            d J ell m hmJ Q hA hB xi ζ theta k (F t) (Gt u) ν := h
      _ = ∑ i ∈ K.product K,
          (alpha i.1 * χ (i.1 : ZMod k.natAbs)) *
            star (alpha i.2 * χ (i.2 : ZMod k.natAbs)) *
            sourceOriginalTrueNuSignedFullPhysicalPairing434
              d J ell m hmJ Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν := by
        exact (Finset.sum_product K K (fun i : ℕ×ℕ =>
          (alpha i.1 * χ (i.1 : ZMod k.natAbs)) *
            star (alpha i.2 * χ (i.2 : ZMod k.natAbs)) *
            sourceOriginalTrueNuSignedFullPhysicalPairing434
              d J ell m hmJ Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [A,sourceOriginalB437CofactorPairCharacter434,star_mul]
        ring
  have hrms := source_original_B437_actual_residue_only_mean_square434
    S k.natAbs (Int.natAbs_pos.mpr hk)
    (fun i : ℕ×ℕ => i.1) (fun i : ℕ×ℕ => i.2) A hunit
  simpa only [hχ] using hrms


/-- For the literal source C191 physical cofactor-χ bilinear kernel at
signed k=±2, every odd cofactor cross-product survives the projected
character mean. The normalized χ RMS equals the completely coherent
physical cofactor-pair norm-square. This says character averaging cannot
supply saving; it does NOT assert nonzero signed primitive mass. -/
theorem source_original_B438_k_pm2_physical_cofactor_character_no_gain434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (hk2 : k.natAbs = 2)
    (hoddK : ∀ t ∈ K, Odd t)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    let S := K.product K
    let A : ℕ × ℕ → ℂ := fun i =>
      (alpha i.1 * star (alpha i.2)) *
        sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient : ℂ)⁻¹)‖ *
        ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k
          (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ F)
          (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ Gt) ν‖^2) =
      ‖∑ i ∈ S, A i‖^2 := by
  dsimp only
  let S := K.product K
  let A : ℕ × ℕ → ℂ := fun i =>
    (alpha i.1 * star (alpha i.2)) *
      sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν
  have hoddCast (t : ℕ) (ht : Odd t) : (t : ZMod 2) = 1 := by
    rcases ht with ⟨r,hr⟩
    rw [hr]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp only [h2,zero_mul,zero_add]
  have hCoprime : ∀ t ∈ K, t.Coprime k.natAbs := by
    intro t ht
    rw [hk2]
    apply (ZMod.isUnit_iff_coprime t 2).mp
    rw [hoddCast t (hoddK t ht)]
    exact isUnit_one
  have hOriginal := source_original_B438_true_physical_cofactor_residue_Gram434
    d J ell m hmJ Q hA hB xi ζ theta k hk K alpha hCoprime F Gt ν
  have hCross (i j : ℕ×ℕ) (hi : i ∈ S) (hj : j ∈ S) :
      (((i.1*j.2:ℕ):ZMod k.natAbs) = ((i.2*j.1:ℕ):ZMod k.natAbs)) := by
    have hi1 : i.1 ∈ K := (Finset.mem_product.mp hi).1
    have hi2 : i.2 ∈ K := (Finset.mem_product.mp hi).2
    have hj1 : j.1 ∈ K := (Finset.mem_product.mp hj).1
    have hj2 : j.2 ∈ K := (Finset.mem_product.mp hj).2
    rw [hk2]
    simp only [Nat.cast_mul,
      hoddCast i.1 (hoddK i.1 hi1),
      hoddCast j.2 (hoddK j.2 hj2),
      hoddCast i.2 (hoddK i.2 hi2),
      hoddCast j.1 (hoddK j.1 hj1)]
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S,
          if (((i.1*j.2:ℕ):ZMod k.natAbs) =
              ((i.2*j.1:ℕ):ZMod k.natAbs))
          then (star (A i)*A j).re else 0 := hOriginal
    _ = ∑ i ∈ S, ∑ j ∈ S, (star (A i)*A j).re := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (hCross i j hi hj)]
    _ = ‖∑ i ∈ S, A i‖^2 :=
      (source_original_B437_true_complex_square_sum_cross434 S A).symm
end Green64Analytic.CorrelationSquare

end

end

