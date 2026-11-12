module

public import Green64.Library.Correlation.FullFourSignPhysicalResidueGram
public import Green64.Library.Weights.Part045

@[expose] public section

/-!
# Correlation / Part060

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## D20ActualOddCofactorPhysicalRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The NONZERO coefficients of the literal unshortened D20 centered
rough full cell are all odd for 2≤W≤y. No oddness assumption on an
arbitrary K, no reassignment of the original D20 ratio, and n=1 handled. -/
theorem source_original_B440_true_D20_active_cofactors_odd434
    (Δ W y : ℝ) (hWy : W ≤ y) (hW : 2 ≤ W) (j : ℕ) :
    ∀ n ∈ sourceD20ActiveFullCell434 Δ W y j, Odd n := by
  intro n hn
  have hRough : SourceRoughAbove n W :=
    source_D20_active_full_cell_rough434 Δ W y hWy j n hn
  rcases Nat.even_or_odd n with heven | hodd
  · have h2div : 2 ∣ n := even_iff_two_dvd.mp heven
    exact False.elim ((not_lt_of_ge hW) (hRough 2 Nat.prime_two h2div))
  · exact hodd

/-- For the TRUE nonzero D20 centered rough coefficient α=Δ_D20,
at BOTH k=±2 and the FULL original two-block ν/four-sign physical C191
cofactor χ test, the character RMS is exactly the whole coherent signed
physical amplitude. The nonzero-α odd support is DERIVED, not assumed.
The D20 full cells are never re-centered on this nonzero subset. -/
theorem source_original_B440_full_D20_four_sign_kpm2_character_RMS_no_gain434
    (Δ W y : ℝ) (hWy : W ≤ y) (hW : 2 ≤ W) (j : ℕ)
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0) (hk2 : k.natAbs = 2)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let K := sourceD20ActiveFullCell434 Δ W y j
    let alpha : ℕ → ℂ := fun n => (sourceD20FullDelta Δ W y n : ℂ)
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient : ℂ)⁻¹)‖ *
        ‖sourceOriginalB436ProjectedCoefficient434 d blockA blockB J ell m hmJ Q
          hA hB xi ζ theta k K alpha F Gt χ 2‖^2) =
      ‖∑ i ∈ K.product K,
        sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
          J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i‖^2 := by
  dsimp only
  exact source_original_B439_k_pm2_ALL_nu_four_sign_character_no_gain434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k hk
    (sourceD20ActiveFullCell434 Δ W y j)
    (fun n => (sourceD20FullDelta Δ W y n : ℂ))
    hk2 (source_original_B440_true_D20_active_cofactors_odd434 Δ W y hWy hW j)
    F Gt
end Green64Analytic.CorrelationSquare

end

end

/-! ## OriginalD20PhysicalFourSignMixedVariance -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Actual SOURCE03 ALL-two-block, full four-sign physical C191 kernel
on the two original cofactor labels. The signed parity projector is ALREADY
inside H; we do not project a second time. Original Fourier ζ/θ unchanged. -/
noncomputable def sourceOriginalB441PhysicalFourSignKernel434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (mm nn : ℕ) : ℂ :=
  ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
        sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k (F mm) (Gt nn) ν)

/-- The cofactor-resolved B439 amplitude retains exactly both full D20
coefficients, with no sparse-support re-centering. -/
theorem source_original_B441_amplitude_eq_original_full_D20_pair434
    (Δ W y : ℝ)
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (i : ℕ × ℕ) :
    sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
      J ell m hmJ Q hA hB xi ζ theta k
      (fun n => (sourceD20FullDelta Δ W y n : ℂ)) F Gt i =
    sourceD20FullPairCoefficient434 Δ W y
      (sourceOriginalB441PhysicalFourSignKernel434 d blockA blockB J ell m hmJ
        Q hA hB xi ζ theta k F Gt) i := by
  unfold sourceOriginalB439FullFourSignCofactorAmplitude434
    sourceD20FullPairCoefficient434 sourceOriginalB441PhysicalFourSignKernel434
  simp only [Complex.star_def, Complex.conj_ofReal]

/-- A direct quantitative full-cell weighted mixed-variation estimate for
the complete ORIGINAL four-sign/two-block C191 physical signed cofactor
amplitude with the genuine D20 centered coefficients.

The source four-sign projector is already inside the physical kernel H;
`originalD61ParityProjector434 0 (-1)=1` is used here ONLY to specialize
the available D20 mixed-variance lemma, not as a replacement for H's
physical projector. The sparse nonzero support remains zero-extended to
the unchanged COMPLETE D20 cell before the mixed second difference. -/
theorem source_original_B441_full_D20_physical_four_sign_mixed_variance434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (j : ℕ)
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (m₀ t₀ : ℕ) :
    let C := sourceD20LogCell Δ j
    let K := sourceD20ActiveFullCell434 Δ W y j
    let alpha : ℕ → ℂ := fun n => (sourceD20FullDelta Δ W y n : ℂ)
    let H : ℕ → ℕ → ℂ := sourceOriginalB441PhysicalFourSignKernel434
      d blockA blockB J ell m hmJ Q hA hB xi ζ theta k F Gt
    let Hzero : ℕ → ℕ → ℂ := fun u v =>
      if (u,v) ∈ K.product K then H u v else 0
    let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
    let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
    ‖∑ i ∈ K.product K,
      sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i‖^2 ≤
      4*(A*(B-A)/B)^2 *
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖Hzero i.1 i.2-Hzero i.1 t₀-Hzero m₀ i.2+Hzero m₀ t₀‖^2) := by
  dsimp only
  let C := sourceD20LogCell Δ j
  let K := sourceD20ActiveFullCell434 Δ W y j
  let S := K.product K
  let alpha : ℕ → ℂ := fun n => (sourceD20FullDelta Δ W y n : ℂ)
  let H : ℕ → ℕ → ℂ := sourceOriginalB441PhysicalFourSignKernel434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k F Gt
  let Hzero : ℕ → ℕ → ℂ := fun u v =>
    if (u,v) ∈ S then H u v else 0
  let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
  let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
  have hS : S ⊆ C.product C := by
    intro i hi
    rcases Finset.mem_product.mp hi with ⟨him,hin⟩
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp him).1,(Finset.mem_filter.mp hin).1⟩
  have hProj : originalD61ParityProjector434 0 (-1:ℂ) = 1 := by
    norm_num [originalD61ParityProjector434]
  have hVariance :=
    green64_original_D20_sparse_projected_variance_mixed_L2_434
      Δ W y hΔ hWy j j S hS H
      (fun _ => (-1:ℂ)) (fun _ => (-1:ℂ)) 0 m₀ t₀
  simp only [hProj, mul_one] at hVariance
  have hCoefficient (i : ℕ × ℕ) :
      sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i =
      sourceD20FullPairCoefficient434 Δ W y H i := by
    exact source_original_B441_amplitude_eq_original_full_D20_pair434
      Δ W y d blockA blockB J ell m hmJ Q hA hB xi ζ theta k F Gt i
  have hSum : (∑ i ∈ S,
      sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i) =
      (∑ i ∈ S, sourceD20FullPairCoefficient434 Δ W y H i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hCoefficient i
  rw [hSum]
  convert hVariance using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## D20TruePhysicalKTwoRMSMixedBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The actual original two-block physical four-sign cofactor-character
RMS at both k=±2 is bounded directly by the FULL D20 cell-centered
weighted mixed L² energy of the literal C191 signed Fourier kernel.

Combines B440's exact q=2 character coherence with B441's original
unshortened cell, true ν-dependent physical Fourier kernel and the real
signed D20 weights. No arbitrary positive-power saving or hidden mixed
variation hypothesis is used. -/
theorem source_original_B442_k_pm2_physical_RMS_mixed_variance_bound434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (hW : 2 ≤ W) (j : ℕ)
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0) (hk2 : k.natAbs = 2)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (m₀ t₀ : ℕ) :
    let C := sourceD20LogCell Δ j
    let K := sourceD20ActiveFullCell434 Δ W y j
    let alpha : ℕ → ℂ := fun n => (sourceD20FullDelta Δ W y n : ℂ)
    let H : ℕ → ℕ → ℂ := sourceOriginalB441PhysicalFourSignKernel434
      d blockA blockB J ell m hmJ Q hA hB xi ζ theta k F Gt
    let Hzero : ℕ → ℕ → ℂ := fun u v =>
      if (u,v) ∈ K.product K then H u v else 0
    let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
    let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient : ℂ)⁻¹)‖ *
        ‖sourceOriginalB436ProjectedCoefficient434 d blockA blockB
          J ell m hmJ Q hA hB xi ζ theta k K alpha F Gt χ 2‖^2) ≤
      4*(A*(B-A)/B)^2 *
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖Hzero i.1 i.2-Hzero i.1 t₀-Hzero m₀ i.2+Hzero m₀ t₀‖^2) := by
  dsimp only
  have hCoherence := source_original_B440_full_D20_four_sign_kpm2_character_RMS_no_gain434
    Δ W y hWy hW j d blockA blockB J ell m hmJ Q hA hB
    xi ζ theta k hk hk2 F Gt
  have hVariance := source_original_B441_full_D20_physical_four_sign_mixed_variance434
    Δ W y hΔ hWy j d blockA blockB J ell m hmJ Q hA hB
    xi ζ theta k F Gt m₀ t₀
  rw [hCoherence]
  exact hVariance
end Green64Analytic.CorrelationSquare

end

end

/-! ## PhysicalCofactorMixedEndpoint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact mixed second difference of ANY finite complex bilinear pairing.
The physical source is conjugated and the target is not: this is precisely
the orientation of the original C191 and the cofactor χ Gram. -/
theorem source_original_B443_finite_bilinear_mixed_difference434
    {X : Type} (S : Finset X) (w : X → ℂ)
    (F G : ℕ → X → ℂ) (m m₀ t t₀ : ℕ) :
    (∑ x ∈ S, w x * star (F m x) * G t x) -
    (∑ x ∈ S, w x * star (F m x) * G t₀ x) -
    (∑ x ∈ S, w x * star (F m₀ x) * G t x) +
    (∑ x ∈ S, w x * star (F m₀ x) * G t₀ x) =
    ∑ x ∈ S, w x * star (F m x - F m₀ x) * (G t x - G t₀ x) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  simp only [star_sub]
  apply Finset.sum_congr rfl
  intro x hx
  ring


/-- Same physical mixed bilinear identity with a fixed, arbitrary complex
SOURCE03 arithmetic/Fourier error factor in each original state. The error
factor is not separated or bounded and remains within every summand. -/
theorem source_original_B443_finite_physical_kernel_mixed_difference434
    {X : Type} (S : Finset X) (w E : X → ℂ)
    (F G : ℕ → X → ℂ) (u u₀ v v₀ : ℕ) :
    (∑ x ∈ S, w x * star (F u x) * G v x * E x) -
    (∑ x ∈ S, w x * star (F u x) * G v₀ x * E x) -
    (∑ x ∈ S, w x * star (F u₀ x) * G v x * E x) +
    (∑ x ∈ S, w x * star (F u₀ x) * G v₀ x * E x) =
    ∑ x ∈ S, w x * star (F u x - F u₀ x) *
      (G v x - G v₀ x) * E x := by
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  simp only [star_sub]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- The ORIGINAL SOURCE03 C191/C6 ν physical major/minor signed residual
has an exact mixed cofactor difference equal to the SAME genuine physical
pairing with DIFFERENCES of its original source/target mark-sensitive
cofactor tests. This is an exact bilinear identity, not a smoothness
hypothesis. All real Mellin ζ, Fourier θ, moving Q/P and V_g masses survive. -/
theorem source_original_B443_true_nu_physical_cofactor_mixed_difference434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (u u₀ v v₀ : ℕ) :
    let H : ℕ → ℕ → ℂ := fun r s =>
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k (F r) (Gt s) ν
    H u v - H u v₀ - H u₀ v + H u₀ v₀ =
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k
        (fun η a => F u η a - F u₀ η a)
        (fun η b => Gt v η b - Gt v₀ η b) ν := by
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP free
  let mass := sourceOriginalVariableBIGMass434 BP free mu
  let w : X × X → ℂ := fun ab => ((mass ab.1*mass ab.2:ℝ):ℂ)
  let E : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν d.Tb d.Vbig Q (hA ν) (hB ν) xi ζ theta k
      (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
  let f : ℕ → X × X → ℂ := fun r ab => F r ν ab.1
  let g : ℕ → X × X → ℂ := fun s ab => Gt s ν ab.2
  have h := source_original_B443_finite_physical_kernel_mixed_difference434
    (Finset.univ : Finset (X × X)) w E f g u u₀ v v₀
  change (∑ ab : X × X, w ab * star (f u ab) * g v ab * E ab) -
    (∑ ab : X × X, w ab * star (f u ab) * g v₀ ab * E ab) -
    (∑ ab : X × X, w ab * star (f u₀ ab) * g v ab * E ab) +
    (∑ ab : X × X, w ab * star (f u₀ ab) * g v₀ ab * E ab) =
    ∑ ab : X × X, w ab * star (f u ab - f u₀ ab) *
      (g v ab - g v₀ ab) * E ab
  exact h
end Green64Analytic.CorrelationSquare

end

end

