module

public import Green64.Library.Correlation.Part060

@[expose] public section

/-!
# Correlation / MaskedPhysicalCofactorVariation

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualMaskedPhysicalCofactorVariation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- EXACT source/target cofactor-mask functions on the original C191 ν
free-BIG harmonic state, preserving the real physical endpoint tests. -/
noncomputable def sourceOriginalB444CofactorMaskedTest434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (K : Finset ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (n : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℂ :=
  if n ∈ K then F n ν a else 0

/-- Literal full two-block FOUR-SIGN physical C191 signed Fourier kernel,
zero-extended off K×K, equals the same physical bilinear kernel with both
original cofactor tests individually masked. No source-mass renormalization. -/
theorem source_original_B444_true_physical_zero_extension_pairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (u v : ℕ) :
    (if (u,v) ∈ K.product K then
      sourceOriginalB441PhysicalFourSignKernel434 d blockA blockB J ell m hmJ
        Q hA hB xi ζ theta k F Gt u v else 0) =
    sourceOriginalB441PhysicalFourSignKernel434 d blockA blockB J ell m hmJ
      Q hA hB xi ζ theta k
      (sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F)
      (sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt) u v := by
  classical
  by_cases hu : u ∈ K
  · by_cases hv : v ∈ K
    · have hmem : (u,v) ∈ K.product K := Finset.mem_product.mpr ⟨hu,hv⟩
      rw [if_pos hmem]
      have hf : sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F u = F u := by
        funext η a
        simp [sourceOriginalB444CofactorMaskedTest434,hu]
      have hg : sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt v = Gt v := by
        funext η a
        simp [sourceOriginalB444CofactorMaskedTest434,hv]
      unfold sourceOriginalB441PhysicalFourSignKernel434
      rw [hf,hg]
    · have hnmem : (u,v) ∉ K.product K := by
        intro hmem
        exact hv (Finset.mem_product.mp hmem).2
      rw [if_neg hnmem]
      have hg : sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt v =
          (fun _ _ => (0:ℂ)) := by
        funext η a
        simp [sourceOriginalB444CofactorMaskedTest434,hv]
      unfold sourceOriginalB441PhysicalFourSignKernel434
      rw [hg]
      simp only [sourceOriginalTrueNuSignedFullPhysicalPairing434,
        mul_zero,zero_mul,Finset.sum_const_zero]
  · have hnmem : (u,v) ∉ K.product K := by
      intro hmem
      exact hu (Finset.mem_product.mp hmem).1
    rw [if_neg hnmem]
    have hf : sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F u =
        (fun _ _ => (0:ℂ)) := by
      funext η a
      simp [sourceOriginalB444CofactorMaskedTest434,hu]
    unfold sourceOriginalB441PhysicalFourSignKernel434
    rw [hf]
    simp only [sourceOriginalTrueNuSignedFullPhysicalPairing434,
      star_zero,mul_zero,zero_mul,Finset.sum_const_zero]


/-- Exact linearity of the original finite ν-family and four independent
endpoint signs under a mixed cofactor second difference. -/
private theorem b444_weighted_full_family_mixed_difference434
    {T N : Type} [Fintype T] (family : Finset N)
    (p : T → ℂ) (r : T → N → ℂ)
    (H : N → ℕ → ℕ → ℂ) (u u₀ v v₀ : ℕ) :
    (∑ tw : T, p tw * (∑ ν ∈ family, r tw ν * H ν u v)) -
    (∑ tw : T, p tw * (∑ ν ∈ family, r tw ν * H ν u v₀)) -
    (∑ tw : T, p tw * (∑ ν ∈ family, r tw ν * H ν u₀ v)) +
    (∑ tw : T, p tw * (∑ ν ∈ family, r tw ν * H ν u₀ v₀)) =
    ∑ tw : T, p tw * (∑ ν ∈ family, r tw ν *
      (H ν u v-H ν u v₀-H ν u₀ v+H ν u₀ v₀)) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro tw htw
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ν hν
  ring


/-- Exact weighted mixed difference of the ZERO-EXTENDED original SOURCE03
physical ν/two-sign kernel as a sum of genuine C191 pairings of the
INDIVIDUALLY DIFFERENCED, masked endpoint cofactor tests. The two original
Fourier/Mellin parameters, Q/P, source V_g harmonic mass and all genuine
ν-sign weights stay unchanged, before ANY norm or Gram square. -/
theorem source_original_B444_true_masked_four_sign_cofactor_mixed434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (u u₀ v v₀ : ℕ) :
    let FM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F
    let GM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt
    let Hzero : ℕ → ℕ → ℂ := fun r s =>
      if (r,s) ∈ K.product K then
        sourceOriginalB441PhysicalFourSignKernel434 d blockA blockB J ell m hmJ
          Q hA hB xi ζ theta k F Gt r s else 0
    Hzero u v - Hzero u v₀ - Hzero u₀ v + Hzero u₀ v₀ =
      ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
        (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
          sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
            sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
              Q hA hB xi ζ theta k
              (fun η a => FM u η a - FM u₀ η a)
              (fun η b => GM v η b - GM v₀ η b) ν) := by
  dsimp only
  let FM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F
  let GM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt
  let Hzero : ℕ → ℕ → ℂ := fun r s =>
    if (r,s) ∈ K.product K then
      sourceOriginalB441PhysicalFourSignKernel434 d blockA blockB J ell m hmJ
        Q hA hB xi ζ theta k F Gt r s else 0
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let p : Bool × Bool → ℂ := sourceOriginalB430ParityCoefficient
  let r : Bool × Bool → SourceOriginalProbePattern434 G m → ℂ :=
    fun tw ν => sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν
  let H : SourceOriginalProbePattern434 G m → ℕ → ℕ → ℂ := fun ν mm nn =>
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k (FM mm) (GM nn) ν
  have hMask (mm nn : ℕ) :
      Hzero mm nn = sourceOriginalB441PhysicalFourSignKernel434
        d blockA blockB J ell m hmJ Q hA hB xi ζ theta k FM GM mm nn := by
    exact source_original_B444_true_physical_zero_extension_pairing434
      d blockA blockB J ell m hmJ Q hA hB xi ζ theta k K F Gt mm nn
  have hν (ν : SourceOriginalProbePattern434 G m) :
      H ν u v - H ν u v₀ - H ν u₀ v + H ν u₀ v₀ =
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k
        (fun η a => FM u η a - FM u₀ η a)
        (fun η b => GM v η b - GM v₀ η b) ν := by
    exact source_original_B443_true_nu_physical_cofactor_mixed_difference434
      d J ell m hmJ Q hA hB xi ζ theta k FM GM ν u u₀ v v₀
  change Hzero u v - Hzero u v₀ - Hzero u₀ v + Hzero u₀ v₀ =
    ∑ tw : Bool × Bool, p tw *
      (∑ ν ∈ family, r tw ν *
        sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
          Q hA hB xi ζ theta k
          (fun η a => FM u η a - FM u₀ η a)
          (fun η b => GM v η b - GM v₀ η b) ν)
  rw [hMask u v, hMask u v₀, hMask u₀ v, hMask u₀ v₀]
  change (∑ tw : Bool × Bool, p tw * (∑ ν ∈ family, r tw ν * H ν u v)) -
    (∑ tw : Bool × Bool, p tw * (∑ ν ∈ family, r tw ν * H ν u v₀)) -
    (∑ tw : Bool × Bool, p tw * (∑ ν ∈ family, r tw ν * H ν u₀ v)) +
    (∑ tw : Bool × Bool, p tw * (∑ ν ∈ family, r tw ν * H ν u₀ v₀)) = _
  calc
    _ = ∑ tw : Bool × Bool, p tw *
        (∑ ν ∈ family, r tw ν *
          (H ν u v - H ν u v₀ - H ν u₀ v + H ν u₀ v₀)) :=
      b444_weighted_full_family_mixed_difference434 family p r H u u₀ v v₀
    _ = _ := by
      apply Finset.sum_congr rfl
      intro tw htw
      congr 1
      apply Finset.sum_congr rfl
      intro ν hmem
      rw [hν ν]
end Green64Analytic.CorrelationSquare

end

end

