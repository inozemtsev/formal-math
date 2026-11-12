module

public import Green64.Library.Correlation.Part059
public import Green64.Library.Correlation.Part058

@[expose] public section

/-!
# Correlation / FullFourSignPhysicalResidueGram

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FullFourSignPhysicalResidueGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Finite Fubini for the exact original pattern and four-sign sums, used
only as a reindexing step in the real physical cofactor residue-only Gram.
No new statistical or arithmetic premise. -/
private theorem b439_weighted_three_sums_comm434
    {T N I : Type} [Fintype T]
    (family : Finset N) (S : Finset I)
    (p : T → ℂ) (r : T → N → ℂ) (h : N → I → ℂ) :
    (∑ tw : T, p tw * (∑ ν ∈ family,
       r tw ν * (∑ i ∈ S, h ν i))) =
    ∑ i ∈ S, ∑ tw : T, p tw * (∑ ν ∈ family,
       r tw ν * h ν i) := by
  classical
  calc
    _ = ∑ tw : T, ∑ ν ∈ family, ∑ i ∈ S,
          p tw * r tw ν * h ν i := by
      apply Finset.sum_congr rfl
      intro tw htw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ tw : T, ∑ i ∈ S, ∑ ν ∈ family,
          p tw * r tw ν * h ν i := by
      apply Finset.sum_congr rfl
      intro tw htw
      exact Finset.sum_comm
    _ = ∑ i ∈ S, ∑ tw : T, ∑ ν ∈ family,
          p tw * r tw ν * h ν i := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro tw htw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      ring

/-- Full SOURCE03 two-block, two independent endpoint signs and genuine
physical ν-residual, resolved at each original cofactor pair (m,n).
The native four-sign projector is applied BEFORE character RMS squaring. -/
noncomputable def sourceOriginalB439FullFourSignCofactorAmplitude434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (alpha : ℕ → ℂ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (i : ℕ × ℕ) : ℂ :=
  (alpha i.1 * star (alpha i.2)) *
    (∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
        sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k
          (F i.1) (Gt i.2) ν))

/-- This is the exact finite cofactor expansion of the LITERAL original
physical C191 two-block ν sum with BOTH independent endpoint parity signs.
Each source characteristic phase χ(m)conjχ(n) stays inside its own cofactor
pair and is extracted only after original ν/permutation weights are summed.
No χ average or square is taken in this identity. -/
theorem source_original_B439_all_nu_four_sign_cofactor_expansion434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (χ : DirichletCharacter ℂ k.natAbs) :
    sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
      hA hB xi ζ theta k K alpha F Gt χ 2 =
    ∑ i ∈ K.product K,
      sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i *
      sourceOriginalB437CofactorPairCharacter434 k.natAbs i.1 i.2 χ := by
  classical
  let S := K.product K
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let p : Bool × Bool → ℂ := sourceOriginalB430ParityCoefficient
  let r : Bool × Bool → SourceOriginalProbePattern434 G m → ℂ :=
    fun tw ν => sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν
  let H : SourceOriginalProbePattern434 G m → ℕ × ℕ → ℂ :=
    fun ν i => sourceOriginalTrueNuSignedFullPhysicalPairing434
      d J ell m hmJ Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν
  let coeff : ℕ × ℕ → ℂ := fun i =>
    (alpha i.1 * star (alpha i.2)) *
      sourceOriginalB437CofactorPairCharacter434 k.natAbs i.1 i.2 χ
  have hν (ν : SourceOriginalProbePattern434 G m) :
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k
        (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ F)
        (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ Gt) ν =
      ∑ i ∈ S, coeff i * H ν i := by
    have hExact := source_original_B435_true_physical_cofactor_character_superposition434
      d J ell m hmJ Q hA hB xi ζ theta k K alpha χ F Gt ν
    change sourceOriginalTrueNuSignedFullPhysicalPairing434
      d J ell m hmJ Q hA hB xi ζ theta k
      (fun η a => ∑ n ∈ K, star (alpha n * χ (n : ZMod k.natAbs)) * F n η a)
      (fun η b => ∑ n ∈ K, star (alpha n * χ (n : ZMod k.natAbs)) * Gt n η b) ν = _
    calc
      _ = ∑ t ∈ K, ∑ u ∈ K,
        (alpha t * χ (t : ZMod k.natAbs)) *
          star (alpha u * χ (u : ZMod k.natAbs)) * H ν (t,u) := by
        simpa only [sourceOriginalB436CofactorTest434,H] using hExact
      _ = ∑ i ∈ S,
        (alpha i.1 * χ (i.1 : ZMod k.natAbs)) *
          star (alpha i.2 * χ (i.2 : ZMod k.natAbs)) * H ν i := by
        exact (Finset.sum_product K K (fun i : ℕ×ℕ =>
          (alpha i.1 * χ (i.1 : ZMod k.natAbs)) *
            star (alpha i.2 * χ (i.2 : ZMod k.natAbs)) * H ν i)).symm
      _ = ∑ i ∈ S, coeff i * H ν i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [coeff,sourceOriginalB437CofactorPairCharacter434]
        simp only [star_mul]
        ring
  have htw (tw : Bool × Bool) :
      sourceOriginalB436ThreePairings434 d blockA blockB J ell m hmJ Q
        hA hB xi ζ theta k K alpha F Gt χ tw 2 =
      ∑ ν ∈ family, r tw ν * (∑ i ∈ S, coeff i * H ν i) := by
    change (∑ ν ∈ family,
      r tw ν * sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k
        (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ F)
        (sourceOriginalB436CofactorTest434 d J ell m hmJ K alpha k χ Gt) ν) = _
    apply Finset.sum_congr rfl
    intro ν hmem
    rw [hν ν]
  have hFactor (i : ℕ×ℕ) :
      (∑ tw : Bool × Bool, p tw *
        (∑ ν ∈ family, r tw ν * (coeff i * H ν i))) =
      coeff i * (∑ tw : Bool × Bool, p tw *
        (∑ ν ∈ family, r tw ν * H ν i)) := by
    calc
      _ = ∑ tw : Bool × Bool, coeff i *
        (p tw * ∑ ν ∈ family, r tw ν * H ν i) := by
        apply Finset.sum_congr rfl
        intro tw htw
        have hinner :
            (∑ ν ∈ family, r tw ν * (coeff i * H ν i)) =
            coeff i * (∑ ν ∈ family, r tw ν * H ν i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ν hmem
          ring
        rw [hinner]
        ring
      _ = _ := by rw [Finset.mul_sum]
  change (∑ tw : Bool × Bool, p tw *
      sourceOriginalB436ThreePairings434 d blockA blockB J ell m hmJ Q
        hA hB xi ζ theta k K alpha F Gt χ tw 2) = _
  calc
    _ = ∑ tw : Bool × Bool, p tw *
          (∑ ν ∈ family, r tw ν * (∑ i ∈ S, coeff i * H ν i)) := by
      apply Finset.sum_congr rfl
      intro tw htwmem
      rw [htw tw]
    _ = ∑ i ∈ S, ∑ tw : Bool × Bool, p tw *
          (∑ ν ∈ family, r tw ν * (coeff i * H ν i)) := by
      exact b439_weighted_three_sums_comm434 family S p r
        (fun ν i => coeff i * H ν i)
    _ = ∑ i ∈ S, coeff i *
          (∑ tw : Bool × Bool, p tw *
            (∑ ν ∈ family, r tw ν * H ν i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hFactor i
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [S,coeff,p,r,H,
        sourceOriginalB439FullFourSignCofactorAmplitude434,
        sourceOriginalB437CofactorPairCharacter434]
      ring


/-- The FULL original C191/C6 physical two-block pattern family with true
(+,-,-,+)/4 signs, original α and OUTER χ on cofactor m is projected BEFORE
squaring; its normalized character RMS equals the exact residue-only
cofactor cross Gram. It is NOT a smallness theorem, nor does it substitute
C191's Fourier frequency -kθ for T's physical integer shift 2k. -/
theorem source_original_B439_true_ALL_nu_four_sign_residue_only_RMS434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (hCoprime : ∀ t ∈ K, t.Coprime k.natAbs)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let S := K.product K
    let A : ℕ × ℕ → ℂ := fun i =>
      sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient : ℂ)⁻¹)‖ *
        ‖sourceOriginalB436ProjectedCoefficient434 d blockA blockB
          J ell m hmJ Q hA hB xi ζ theta k K alpha F Gt χ 2‖^2) =
    ∑ i ∈ S, ∑ j ∈ S,
      if (((i.1*j.2:ℕ):ZMod k.natAbs) =
          ((i.2*j.1:ℕ):ZMod k.natAbs))
      then (star (A i)*A j).re else 0 := by
  dsimp only
  let S := K.product K
  let A : ℕ × ℕ → ℂ := fun i =>
    sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
      J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i
  have hunit : ∀ i ∈ S, ∀ j ∈ S,
      IsUnit (((i.1*j.2:ℕ):ZMod k.natAbs)) := by
    intro i hi j hj
    have hi1 := (Finset.mem_product.mp hi).1
    have hj2 := (Finset.mem_product.mp hj).2
    have him : IsUnit (i.1 : ZMod k.natAbs) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hCoprime i.1 hi1)
    have hjn : IsUnit (j.2 : ZMod k.natAbs) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hCoprime j.2 hj2)
    rw [Nat.cast_mul]
    exact him.mul hjn
  have hrms := source_original_B437_actual_residue_only_mean_square434
    S k.natAbs (Int.natAbs_pos.mpr hk)
    (fun i : ℕ×ℕ => i.1) (fun i : ℕ×ℕ => i.2) A hunit
  have hχ (χ : DirichletCharacter ℂ k.natAbs) :
      sourceOriginalB436ProjectedCoefficient434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k K alpha F Gt χ 2 =
      ∑ i ∈ S, A i * sourceOriginalB437CofactorPairCharacter434
        k.natAbs i.1 i.2 χ := by
    exact source_original_B439_all_nu_four_sign_cofactor_expansion434
      d blockA blockB J ell m hmJ Q hA hB xi ζ theta k K alpha F Gt χ
  simpa only [hχ] using hrms


/-- The literal original two-block C191 four-sign projected physical
cofactor χ RMS at BOTH signed k=±2 has no extra character orthogonality:
the normalized χ second moment is exactly the FULL coherent all-ν,
all-sign physical α-resolved amplitude norm-square. Only arithmetic/Fourier
cancellation INSIDE that sum could still yield saving. -/
theorem source_original_B439_k_pm2_ALL_nu_four_sign_character_no_gain434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (hk2 : k.natAbs = 2) (hoddK : ∀ t ∈ K, Odd t)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let S := K.product K
    let A : ℕ × ℕ → ℂ := fun i =>
      sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient : ℂ)⁻¹)‖ *
        ‖sourceOriginalB436ProjectedCoefficient434 d blockA blockB
          J ell m hmJ Q hA hB xi ζ theta k K alpha F Gt χ 2‖^2) =
      ‖∑ i ∈ S, A i‖^2 := by
  dsimp only
  let S := K.product K
  let A : ℕ × ℕ → ℂ := fun i =>
    sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
      J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i
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
  have hOriginal := source_original_B439_true_ALL_nu_four_sign_residue_only_RMS434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k hk K alpha
    hCoprime F Gt
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

