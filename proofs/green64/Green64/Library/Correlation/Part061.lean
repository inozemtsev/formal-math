module

public import Green64.Library.Correlation.Part060
public import Green64.Library.Correlation.MaskedPhysicalCofactorVariation
public import Green64.Library.Weights.Part082
public import Green64.Library.Correlation.Part058
public import Green64.Library.Correlation.FullFourSignPhysicalResidueGram
public import Green64.Library.Correlation.Part059

@[expose] public section

/-!
# Correlation / Part061

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ProjectedPhysicalRMSDifferencedTests -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A direct exact analytic interface for the original physical SOURCE03
four-sign character RMS at signed k=±2: only the genuinely DIFFERENCED
source/target cofactor tests occur in the weighted L² majorant. The
original ν-dependent prime law, ζ/θ, Q and ZERO-EXTENDED full D20 cells are
all literal. No unproved endpoint regularity or decay is assumed. -/
theorem source_original_B445_k_pm2_RMS_differenced_physical_endpoints434
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
    let FM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F
    let GM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt
    let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
    let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient : ℂ)⁻¹)‖ *
        ‖sourceOriginalB436ProjectedCoefficient434 d blockA blockB
          J ell m hmJ Q hA hB xi ζ theta k K alpha F Gt χ 2‖^2) ≤
      4*(A*(B-A)/B)^2 *
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
            (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
              sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
                sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
                  Q hA hB xi ζ theta k
                  (fun η a => FM i.1 η a - FM m₀ η a)
                  (fun η b => GM i.2 η b - GM t₀ η b) ν)‖^2) := by
  dsimp only
  let C := sourceD20LogCell Δ j
  let K := sourceD20ActiveFullCell434 Δ W y j
  let alpha : ℕ → ℂ := fun n => (sourceD20FullDelta Δ W y n : ℂ)
  let H : ℕ → ℕ → ℂ := sourceOriginalB441PhysicalFourSignKernel434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k F Gt
  let Hzero : ℕ → ℕ → ℂ := fun u v =>
    if (u,v) ∈ K.product K then H u v else 0
  let FM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F
  let GM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt
  have hOld := source_original_B442_k_pm2_physical_RMS_mixed_variance_bound434
    Δ W y hΔ hWy hW j d blockA blockB J ell m hmJ Q
    hA hB xi ζ theta k hk hk2 F Gt m₀ t₀
  have hMixed (i : ℕ × ℕ) :
      Hzero i.1 i.2-Hzero i.1 t₀-Hzero m₀ i.2+Hzero m₀ t₀ =
      ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
        (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
          sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
            sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
              Q hA hB xi ζ theta k
              (fun η a => FM i.1 η a-FM m₀ η a)
              (fun η b => GM i.2 η b-GM t₀ η b) ν) := by
    exact source_original_B444_true_masked_four_sign_cofactor_mixed434
      d blockA blockB J ell m hmJ Q hA hB xi ζ theta k K F Gt
      i.1 m₀ i.2 t₀
  have hSum :
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖Hzero i.1 i.2-Hzero i.1 t₀-Hzero m₀ i.2+Hzero m₀ t₀‖^2) =
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
            (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
              sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
                sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
                  Q hA hB xi ζ theta k
                  (fun η a => FM i.1 η a-FM m₀ η a)
                  (fun η b => GM i.2 η b-GM t₀ η b) ν)‖^2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hMixed i]
  rw [← hSum]
  exact hOld
end Green64Analytic.CorrelationSquare

end

end

/-! ## PhysicalC191EndpointDifferenceEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact Hilbert midpoint control for difference of two ORIGINAL complex
cofactor endpoint observables. This is not a bound on their arithmetic
variation in the index; it is the normalization needed to apply C191 to
differenced source/target tests. -/
theorem source_original_B446_complex_difference_half_energy434 (a b : ℂ) :
    ‖(a-b)/2‖^2 ≤ (‖a‖^2+‖b‖^2)/2 := by
  have hnorm : ‖a-b‖ ≤ ‖a‖+‖b‖ := norm_sub_le a b
  have hmid : ‖(a-b)/2‖ = ‖a-b‖/2 := by
    simp only [norm_div]
    norm_num
  rw [hmid]
  have hs : ‖a-b‖^2 ≤ (‖a‖+‖b‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith only [hs,sq_nonneg (‖a‖-‖b‖)]

/-- Under the TRUE nonnegative physical law, taking half the difference
of any two endpoint tests does not cost more than their average L² mass. -/
theorem source_original_B446_finite_weighted_difference_energy434
    {X : Type} (S : Finset X) (w : X → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (F G : X → ℂ) :
    (∑ x ∈ S, w x*‖(F x-G x)/2‖^2) ≤
    ((∑ x ∈ S, w x*‖F x‖^2) +
      (∑ x ∈ S, w x*‖G x‖^2))/2 := by
  calc
    _ ≤ ∑ x ∈ S, w x*((‖F x‖^2+‖G x‖^2)/2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (source_original_B446_complex_difference_half_energy434 (F x) (G x))
        (hw x hx)
    _ = ∑ x ∈ S, (w x*‖F x‖^2+w x*‖G x‖^2)/2 := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by
      rw [← Finset.sum_div,Finset.sum_add_distrib]

/-- ORIGINAL C191 source V_g-normalized harmonic mass, not a counting
measure: the L² norm of the half-difference of two ν-dependent cofactor
tests is bounded by the mean of their true physical endpoint energies. -/
theorem source_original_B446_true_physical_half_difference_energy434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J)
    (F Gt : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (F η a-Gt η a)/2) ν ≤
    (sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ F ν +
     sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ Gt ν)/2 := by
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  have hVpos : ∀ g, 0 < d.Vbig g := fun g => cfg.hv.trans_le (d.hVbig g)
  have hEq : ∀ g, d.Vbig g = ∑ p : BP g, 1/((p.val:ℕ):ℝ) := by
    intro g
    calc
      _ = ∑ p ∈ d.Tb g, 1/(p:ℝ) := hVbig g
      _ = ∑ p : BP g, 1/((p.val:ℕ):ℝ) := by
        simpa only [BP] using
          (Finset.sum_coe_sort (d.Tb g) (fun p : ℕ => (1:ℝ)/(p:ℝ))).symm
  have hmu : ∀ g (p : BP g), 0 ≤ mu g p :=
    (source_original_joint_harmonic_normalized434 BP
      (fun _ p => p.val) d.Vbig hVpos hEq).1
  have hw (a : SourceOriginalVariableBIGState434 BP free) :
      0 ≤ sourceOriginalVariableBIGMass434 BP free mu a :=
    source_original_variable_BIG_mass_nonneg434 BP free mu hmu a
  have h := source_original_B446_finite_weighted_difference_energy434
    (Finset.univ : Finset (SourceOriginalVariableBIGState434 BP free))
    (sourceOriginalVariableBIGMass434 BP free mu)
    (by intro a ha; exact hw a) (F ν) (Gt ν)
  change (∑ a : SourceOriginalVariableBIGState434 BP free,
      sourceOriginalVariableBIGMass434 BP free mu a*‖(F ν a-Gt ν a)/2‖^2) ≤
    ((∑ a : SourceOriginalVariableBIGState434 BP free,
       sourceOriginalVariableBIGMass434 BP free mu a*‖F ν a‖^2) +
     (∑ a : SourceOriginalVariableBIGState434 BP free,
       sourceOriginalVariableBIGMass434 BP free mu a*‖Gt ν a‖^2))/2
  exact h

/-- If two original physical cofactor endpoint tests are individually
L²-normalized, their half difference remains genuinely L²-normalized.
This supplies the exact admissibility interface for C191 on the
*true endpoint increments*, without postulating a new source measure. -/
theorem source_original_B446_true_physical_half_difference_unit434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J)
    (F Gt : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (hF : sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ F ν ≤ 1)
    (hG : sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ Gt ν ≤ 1) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (F η a-Gt η a)/2) ν ≤ 1 := by
  have h := source_original_B446_true_physical_half_difference_energy434
    d hVbig J ell m hmJ F Gt ν
  linarith only [h,hF,hG]
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualMaskedEndpointAdmissibility -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The ORIGINAL actual nonzero-cofactor support cutoff `n∈K` cannot
increase the true V_g-harmonic physical C191 source/target L² mass.
No counting-law replacement, no fake normalisation of the sharp mask. -/
theorem source_original_B447_true_masked_cofactor_energy_le434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J) (K : Finset ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (n : ℕ) (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F n) ν ≤
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ (F n) ν := by
  have h := source_original_B433_true_physical_test_multiplier_energy434
    d hVbig J ell m hmJ
    (fun _ _ => if n ∈ K then (1:ℂ) else 0) (F n)
    (by
      intro η a
      by_cases hn : n ∈ K
      · simp [hn]
      · simp [hn]) ν
  have heq : (fun η a => (if n ∈ K then (1:ℂ) else 0) * F n η a) =
      sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F n := by
    funext η a
    by_cases hn : n ∈ K <;> simp [hn,sourceOriginalB444CofactorMaskedTest434]
  rw [heq] at h
  exact h

/-- The literal C191 physical endpoint DIFFERENCE that appears in B445's
true k=±2 RMS mixed-variation kernel is admissible to the source C191/C6
L² machinery after a factor 1/2, provided the two original unmasked
cofactor tests are individually normalized. The complete sharp support
cutoff has been paid exactly by B433, not replaced by a smooth taper. -/
theorem source_original_B447_true_masked_cofactor_difference_unit434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J) (K : Finset ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (n n₀ : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (hE : sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (F n) ν ≤ 1)
    (hE₀ : sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (F n₀) ν ≤ 1) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a =>
        (sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F n η a -
         sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F n₀ η a)/2)
      ν ≤ 1 := by
  let FM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F
  have hn : sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (FM n) ν ≤ 1 :=
    (source_original_B447_true_masked_cofactor_energy_le434
      d hVbig J ell m hmJ K F n ν).trans hE
  have hn₀ : sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (FM n₀) ν ≤ 1 :=
    (source_original_B447_true_masked_cofactor_energy_le434
      d hVbig J ell m hmJ K F n₀ ν).trans hE₀
  exact source_original_B446_true_physical_half_difference_unit434
    d hVbig J ell m hmJ (FM n) (FM n₀) ν hn hn₀
end Green64Analytic.CorrelationSquare

end

end

/-! ## TruePhysicalC191MixedTestSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

/-- Uniform source C191/C6 signed Fourier saving, for TRUE source/target
D20 sharp-masked cofactor HALF DIFFERENCE endpoint tests, with every
physical moving band/frequency/ν condition inherited unchanged from the
existing full all-ν theorem. No new analytic saving hypothesis is added.
Only per-cofactor ORIGINAL unmasked energy ≤1 is assumed. -/
theorem eventually_source_original_B448_D20_cofactor_endpoint_difference_C191_saving434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal)
    (Cgroup Ck Dgoal : ℝ)
    (hCgroup : 0 ≤ Cgroup) (hCk : 0 < Ck) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, data.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, data.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ data.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hVFloor : cfg.vmin ≤ Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYbound : ∀ g : β, Y ≤ ((loB g+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1)))
    (cofactorSupport : Finset ℕ)
    (sourceFamily targetFamily : ℕ →
      (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hES : ∀ n ν, ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m →
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ (sourceFamily n) ν ≤ 1)
    (hET : ∀ n ν, ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m →
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ (targetFamily n) ν ≤ 1)
    (s s0 t t0 : ℕ)
    (epsSrc epsTgt : Bool)
    (hGroups : (((blockA.card+blockB.card:ℕ)):ℝ) ≤
      Cgroup*Real.log L)
    (hMajorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2)+2*Ck ≤ 2*Bmaj)
    (hMinorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2) ≤ Bout),
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let budget : ℝ :=
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
    let shared := fun ν : SourceOriginalProbePattern434 β m =>
      ((Fintype.card ι)*J) + ∑ g : β,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 β m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    ‖∑ ν ∈ family,
      sign ν * sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        (fun η a =>
          (sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
             cofactorSupport sourceFamily s η a -
           sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
             cofactorSupport sourceFamily s0 η a)/2)
        (fun η b =>
          (sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
             cofactorSupport targetFamily t η b -
           sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
             cofactorSupport targetFamily t0 η b)/2) ν‖^2 ≤
      288006*L^(-Dgoal) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_true_ALL_nu_FOUR_SIGNS_FIXED_FLOOR_saving434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
      Cgroup Ck Dgoal hCgroup hCk
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hCoreL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hVFloor hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice cofactorSupport sourceFamily targetFamily hES hET
    s s0 t t0 epsSrc epsTgt
    hGroups hMajorExp hMinorExp
  let Fs := sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
      cofactorSupport sourceFamily
  let Gs := sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
      cofactorSupport targetFamily
  let sourceTest := fun (ν : SourceOriginalProbePattern434 β m)
      (a : SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) =>
      (Fs s ν a - Fs s0 ν a)/2
  let targetTest := fun (ν : SourceOriginalProbePattern434 β m)
      (a : SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) =>
      (Gs t ν a - Gs t0 ν a)/2
  have hSource : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ≤ 1 := by
    intro ν hν
    constructor
    · exact source_original_B433_true_physical_energy_nonneg434
        data hVbig J ell m hmJ sourceTest ν
    · exact source_original_B447_true_masked_cofactor_difference_unit434
        data hVbig J ell m hmJ cofactorSupport sourceFamily s s0 ν
        (hES s ν hν) (hES s0 ν hν)
  have hTarget : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ≤ 1 := by
    intro ν hν
    constructor
    · exact source_original_B433_true_physical_energy_nonneg434
        data hVbig J ell m hmJ targetTest ν
    · exact source_original_B447_true_masked_cofactor_difference_unit434
        data hVbig J ell m hmJ cofactorSupport targetFamily t t0 ν
        (hET t ν hν) (hET t0 ν hν)
  have h := hCoreL
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hVFloor hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hSource hTarget epsSrc epsTgt
    hGroups hMajorExp hMinorExp
  exact h
end Green64Analytic.CorrelationSquare

end

end

/-! ## FourSignContract -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- If EVERY actual signed endpoint channel satisfies the same squared
Hilbert C191 majorant, the complete (+,-,-,+)/4 projector BEFORE the
norm square satisfies the IDENTICAL bound. No factor four or character
count and no scalar→character RMS transfer. -/
theorem source_original_B449_four_sign_squared_bound434
    (E : Bool × Bool → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hEach : ∀ tw, ‖E tw‖^2 ≤ T) :
    ‖∑ tw : Bool × Bool,
      sourceOriginalB430ParityCoefficient tw * E tw‖^2 ≤ T := by
  have hRoot : (Real.sqrt T)^2 = T := Real.sq_sqrt hT
  have hN (tw : Bool × Bool) : ‖E tw‖ ≤ Real.sqrt T := by
    have hSq := hEach tw
    have hZero := norm_nonneg (E tw)
    have hSqrt := Real.sqrt_nonneg T
    nlinarith only [hSq,hRoot,hZero,hSqrt]
  have hProj :
      ‖∑ tw : Bool × Bool,
        sourceOriginalB430ParityCoefficient tw * E tw‖ ≤ Real.sqrt T := by
    calc
      _ ≤ ∑ tw : Bool × Bool,
        ‖sourceOriginalB430ParityCoefficient tw * E tw‖ := norm_sum_le _ _
      _ = ∑ tw : Bool × Bool,
        ‖sourceOriginalB430ParityCoefficient tw‖ * ‖E tw‖ := by
          simp only [norm_mul]
      _ ≤ ∑ tw : Bool × Bool,
        ‖sourceOriginalB430ParityCoefficient tw‖ * Real.sqrt T := by
          apply Finset.sum_le_sum
          intro tw htw
          exact mul_le_mul_of_nonneg_left (hN tw) (norm_nonneg _)
      _ = Real.sqrt T := by
        rw [← Finset.sum_mul,source_original_B430_parity_mass434,one_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hProj 2).trans_eq hRoot
end Green64Analytic.CorrelationSquare

end

end

/-! ## GenericPhysicalC191FourSignSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

/-- The TRUE source C191/C6 original full two-block/FOUR-sign physical
signed residual estimate for ANY actual mark-sensitive source and target
tests normalized under the literal original reciprocal-prime V_g harmonic
law. This is the exact generic consumer required for SIGNED D20 pooled
tests, without first paying the full D20 L¹ mass V. All original source
arithmetic Fourier and moving-Q budget premises are retained verbatim. -/
theorem eventually_source_original_B473_any_normalized_physical_four_sign_C191_saving434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal)
    (Cgroup Ck Dgoal : ℝ)
    (hCgroup : 0 ≤ Cgroup) (hCk : 0 < Ck) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, data.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, data.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ data.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hVFloor : cfg.vmin ≤ Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYbound : ∀ g : β, Y ≤ ((loB g+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1)))
    (sourceTest targetTest : (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ≤ 1)
    (hGroups : (((blockA.card+blockB.card:ℕ)):ℝ) ≤
      Cgroup*Real.log L)
    (hMajorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2)+2*Ck ≤ 2*Bmaj)
    (hMinorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2) ≤ Bout),
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let budget : ℝ :=
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
    let shared := fun ν : SourceOriginalProbePattern434 β m =>
      ((Fintype.card ι)*J) + ∑ g : β,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun tw : Bool × Bool => fun ν : SourceOriginalProbePattern434 β m =>
      (if tw.1 then (-1:ℂ)^(shared ν) else 1) *
      (if tw.2 then (-1:ℂ)^(shared ν) else 1)
    ‖∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ family,
        sign tw ν *
          sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν)‖^2 ≤
      288006*L^(-Dgoal) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_true_ALL_nu_FOUR_SIGNS_FIXED_FLOOR_saving434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
      Cgroup Ck Dgoal hCgroup hCk
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hOrig
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hVFloor hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hES hET
    hGroups hMajorExp hMinorExp
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 β m =>
    ((Fintype.card ι)*J) + ∑ g : β,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun tw : Bool × Bool => fun ν : SourceOriginalProbePattern434 β m =>
    (if tw.1 then (-1:ℂ)^(shared ν) else 1) *
    (if tw.2 then (-1:ℂ)^(shared ν) else 1)
  let E : Bool × Bool → ℂ := fun tw =>
    ∑ ν ∈ family, sign tw ν *
      sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν
  let T : ℝ := 288006*L^(-Dgoal)
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith only [hL]) _)
  have hSource : ∀ ν ∈ family,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ≤ 1 := by
    intro ν hν
    exact ⟨source_original_B433_true_physical_energy_nonneg434
      data hVbig J ell m hmJ sourceTest ν,hES ν hν⟩
  have hTarget : ∀ ν ∈ family,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ≤ 1 := by
    intro ν hν
    exact ⟨source_original_B433_true_physical_energy_nonneg434
      data hVbig J ell m hmJ targetTest ν,hET ν hν⟩
  have hEach (tw : Bool × Bool) : ‖E tw‖^2 ≤ T := by
    have hh := hOrig x Ydata Hprime data
      loS hiS loB hiB hSmallSubset hBigFull
      hSmallOrder hBigOrder hTsUpper hVbig
      blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
      hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
      hQpositive Vmin hVmin hVFloor hMass hBigLower
      hL hBigUpper hLdyad hQ
      hLoOne hLoLeHi hLoLarge hYbound
      ζ theta k hk S hS hSscale hQchar hBudget
      hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
      hXiChoice sourceTest targetTest hSource hTarget
      tw.1 tw.2 hGroups hMajorExp hMinorExp
    change ‖E tw‖^2 ≤ T at hh
    exact hh
  change ‖∑ tw : Bool × Bool,
    sourceOriginalB430ParityCoefficient tw * E tw‖^2 ≤ T
  exact source_original_B449_four_sign_squared_bound434 E T hT hEach
end Green64Analytic.CorrelationSquare

end

end

/-! ## FourSignTrueC191MixedTestSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

/-- The original all-two-block C191/C6 signed residual with genuine
SHARP-masked cofactor source/target HALF DIFFERENCES, now with the entire
(+,-,-,+)/4 endpoint projector BEFORE the norm square. Exact original
structural/parameter schedule, and no new arithmetic hypothesis. -/
theorem eventually_source_original_B449_all_four_sign_D20_endpoint_difference_C191_saving434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal)
    (Cgroup Ck Dgoal : ℝ)
    (hCgroup : 0 ≤ Cgroup) (hCk : 0 < Ck) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, data.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, data.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ data.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hVFloor : cfg.vmin ≤ Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYbound : ∀ g : β, Y ≤ ((loB g+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1)))
    (cofactorSupport : Finset ℕ)
    (sourceFamily targetFamily : ℕ →
      (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hES : ∀ n ν, ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m →
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ (sourceFamily n) ν ≤ 1)
    (hET : ∀ n ν, ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m →
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ (targetFamily n) ν ≤ 1)
    (s s0 t t0 : ℕ)
    (hGroups : (((blockA.card+blockB.card:ℕ)):ℝ) ≤
      Cgroup*Real.log L)
    (hMajorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2)+2*Ck ≤ 2*Bmaj)
    (hMinorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2) ≤ Bout),
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let budget : ℝ :=
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
    let shared := fun ν : SourceOriginalProbePattern434 β m =>
      ((Fintype.card ι)*J) + ∑ g : β,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun tw : Bool × Bool => fun ν : SourceOriginalProbePattern434 β m =>
      (if tw.1 then (-1:ℂ)^(shared ν) else 1) *
      (if tw.2 then (-1:ℂ)^(shared ν) else 1)
    ‖∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ family,
        sign tw ν *
          sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        (fun η a =>
          (sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
             cofactorSupport sourceFamily s η a -
           sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
             cofactorSupport sourceFamily s0 η a)/2)
        (fun η b =>
          (sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
             cofactorSupport targetFamily t η b -
           sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
             cofactorSupport targetFamily t0 η b)/2) ν)‖^2 ≤
      288006*L^(-Dgoal) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_B448_D20_cofactor_endpoint_difference_C191_saving434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
      Cgroup Ck Dgoal hCgroup hCk
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hOrig
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hVFloor hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice cofactorSupport sourceFamily targetFamily hES hET
    s s0 t t0 hGroups hMajorExp hMinorExp
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 β m =>
    ((Fintype.card ι)*J) + ∑ g : β,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun tw : Bool × Bool => fun ν : SourceOriginalProbePattern434 β m =>
    (if tw.1 then (-1:ℂ)^(shared ν) else 1) *
    (if tw.2 then (-1:ℂ)^(shared ν) else 1)
  let E : Bool × Bool → ℂ := fun tw =>
    ∑ ν ∈ family,
      sign tw ν *
        sourceOriginalTrueNuSignedFullPhysicalPairing434
          data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
          (fun η a =>
            (sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
               cofactorSupport sourceFamily s η a -
             sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
               cofactorSupport sourceFamily s0 η a)/2)
          (fun η b =>
            (sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
               cofactorSupport targetFamily t η b -
             sourceOriginalB444CofactorMaskedTest434 data J ell m hmJ
               cofactorSupport targetFamily t0 η b)/2) ν
  let T : ℝ := 288006*L^(-Dgoal)
  have hT : 0 ≤ T := by
    dsimp [T]
    apply mul_nonneg (by norm_num)
    exact Real.rpow_nonneg (by linarith only [hL]) _
  have hPer (tw : Bool × Bool) : ‖E tw‖^2 ≤ T := by
    have hh := hOrig x Ydata Hprime data
      loS hiS loB hiB hSmallSubset hBigFull
      hSmallOrder hBigOrder hTsUpper hVbig
      blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
      hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
      hQpositive Vmin hVmin hVFloor hMass hBigLower
      hL hBigUpper hLdyad hQ
      hLoOne hLoLeHi hLoLarge hYbound
      ζ theta k hk S hS hSscale hQchar hBudget
      hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
      hXiChoice cofactorSupport sourceFamily targetFamily hES hET
      s s0 t t0 tw.1 tw.2 hGroups hMajorExp hMinorExp
    change ‖E tw‖^2 ≤ T at hh
    exact hh
  change ‖∑ tw : Bool × Bool,
      sourceOriginalB430ParityCoefficient tw * E tw‖^2 ≤ T
  exact source_original_B449_four_sign_squared_bound434 E T hT hPer
end Green64Analytic.CorrelationSquare

end

end

/-! ## PhysicalC191HalfScale -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Exact C191 physical signed source/target pairing sesquilinearity:
halving BOTH original complex endpoint tests scales the original ν
physical pairing by 1/4, with no change to dependent harmonic mass,
original Q, signed ζ/θ Fourier residual, or source state. -/
theorem source_original_B450_physical_half_pairing_scale434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (Fs Gs : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k
      (fun η a => Fs η a/2) (fun η b => Gs η b/2) ν =
    (1/4:ℂ) *
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k Fs Gs ν := by
  unfold sourceOriginalTrueNuSignedFullPhysicalPairing434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  dsimp only
  simp only [div_eq_mul_inv,Complex.star_def,map_mul,map_inv₀,map_ofNat]
  ring


/-- Exactly extract a common scalar after BOTH original ν pattern sum and
the independent four-sign projector, with no cardinality or norm change. -/
theorem source_original_B450_two_stage_weighted_scale434
    {N : Type} (family : Finset N)
    (p : Bool × Bool → ℂ) (sign : Bool × Bool → N → ℂ)
    (H G : N → ℂ) (scale : ℂ)
    (h : ∀ ν ∈ family, H ν = scale * G ν) :
    (∑ tw : Bool × Bool, p tw * (∑ ν ∈ family, sign tw ν * H ν)) =
    scale * (∑ tw : Bool × Bool, p tw * (∑ ν ∈ family, sign tw ν * G ν)) := by
  calc
    _ = ∑ tw : Bool × Bool, p tw *
      (∑ ν ∈ family, sign tw ν * (scale * G ν)) := by
        apply Finset.sum_congr rfl
        intro tw htw
        congr 1
        apply Finset.sum_congr rfl
        intro ν hν
        rw [h ν hν]
    _ = ∑ tw : Bool × Bool, scale *
      (p tw * ∑ ν ∈ family, sign tw ν * G ν) := by
        apply Finset.sum_congr rfl
        intro tw htw
        have hh : (∑ ν ∈ family, sign tw ν * (scale * G ν)) =
            scale * (∑ ν ∈ family, sign tw ν * G ν) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ν hν
          ring
        rw [hh]
        ring
    _ = _ := by rw [Finset.mul_sum]

/-- For the ORIGINAL C191 full two-block ν-family, both independent
endpoint four-sign projector channels and the actual sharp D20 cofactor
support, physical pairing of FULL source/target mixed differences is EXACTLY
four times the pairing of the normalized (half) differences.
This is scalar geometry only: original Fourier ζ/θ and source prime law
are unchanged and no saving bound is postulated here. -/
theorem source_original_B450_full_four_sign_physical_half_scale434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ) (K : Finset ℕ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (s s0 t t0 : ℕ) :
    let FM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F
    let GM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt
    let U := fun (ν : SourceOriginalProbePattern434 G m)
      (a : SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) =>
      FM s ν a - FM s0 ν a
    let V := fun (ν : SourceOriginalProbePattern434 G m)
      (b : SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) =>
      GM t ν b - GM t0 ν b
    (∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
          sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
            Q hA hB xi ζ theta k U V ν)) =
    4 * (∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
          sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
            Q hA hB xi ζ theta k
            (fun η a => U η a/2) (fun η b => V η b/2) ν)) := by
  dsimp only
  let FM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K F
  let GM := sourceOriginalB444CofactorMaskedTest434 d J ell m hmJ K Gt
  let U := fun (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) =>
    FM s ν a-FM s0 ν a
  let V := fun (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) =>
    GM t ν a-GM t0 ν a
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let p : Bool × Bool → ℂ := sourceOriginalB430ParityCoefficient
  let sign : Bool × Bool → SourceOriginalProbePattern434 G m → ℂ :=
    fun tw ν => sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν
  let Full : SourceOriginalProbePattern434 G m → ℂ := fun ν =>
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k U V ν
  let Half : SourceOriginalProbePattern434 G m → ℂ := fun ν =>
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k
      (fun η a => U η a/2) (fun η b => V η b/2) ν
  have hper (ν : SourceOriginalProbePattern434 G m) :
      Full ν = 4*Half ν := by
    have hh := source_original_B450_physical_half_pairing_scale434
      d J ell m hmJ Q hA hB xi ζ theta k U V ν
    change Half ν = (1/4:ℂ)*Full ν at hh
    calc
      Full ν = 4 * ((1/4:ℂ)*Full ν) := by ring
      _ = 4 * Half ν := by rw [←hh]
  change (∑ tw : Bool × Bool, p tw *
      (∑ ν ∈ family, sign tw ν * Full ν)) =
    4 * (∑ tw : Bool × Bool, p tw *
      (∑ ν ∈ family, sign tw ν * Half ν))
  exact source_original_B450_two_stage_weighted_scale434
    family p sign Full Half 4 (fun ν hν => hper ν)
end Green64Analytic.CorrelationSquare

end

end

/-! ## FullCellUnmaskedMixedVariance -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The true nonzero D20 support may be replaced by the WHOLE original
logarithmic cell in a SIGNED pair sum, since each discarded coefficient
is identically zero. The kernel is NOT zero-extended off the sparse support.
This repairs the artificial rough-mask boundary variation in B441. -/
theorem source_original_B452_full_cell_no_sparse_mask_sum434
    (Δ W y : ℝ) (j : ℕ) (H : ℕ → ℕ → ℂ) :
    let C := sourceD20LogCell Δ j
    let K := sourceD20ActiveFullCell434 Δ W y j
    (∑ i ∈ K.product K, sourceD20FullPairCoefficient434 Δ W y H i) =
    (∑ i ∈ C.product C, sourceD20FullPairCoefficient434 Δ W y H i) := by
  dsimp only
  let C := sourceD20LogCell Δ j
  let K := sourceD20ActiveFullCell434 Δ W y j
  have hS : K.product K ⊆ C.product C := by
    intro i hi
    rcases Finset.mem_product.mp hi with ⟨h1,h2⟩
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp h1).1,(Finset.mem_filter.mp h2).1⟩
  have hz (i : ℕ × ℕ) (hi : i ∈ C.product C)
      (hiNot : i ∉ K.product K) :
      sourceD20FullPairCoefficient434 Δ W y H i = 0 := by
    obtain ⟨hi1,hi2⟩ := Finset.mem_product.mp hi
    by_cases h1 : sourceD20FullDelta Δ W y i.1 = 0
    · simp [sourceD20FullPairCoefficient434,h1]
    · have h2 : sourceD20FullDelta Δ W y i.2 = 0 := by
        by_contra hh
        apply hiNot
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨hi1,h1⟩,
           Finset.mem_filter.mpr ⟨hi2,hh⟩⟩
      simp [sourceD20FullPairCoefficient434,h2]
  exact Finset.sum_subset hS hz


/-- Stronger ORIGINAL D20 full-cell variance bound: when the reference
anchors also belong to the complete original cell, no sharp/nonzero support
indicator enters ANY of the four mixed difference terms. The signed sum over
nonzero D20 coefficients is EXACTLY the full-cell centered sum by B452.
Compared with B441, this removes artificial jumps created by extending H
by zero outside the SPARSE support K, which is strictly smaller than C. -/
theorem source_original_B452_true_FULL_cell_unmasked_variance434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (j : ℕ)
    (H : ℕ → ℕ → ℂ) (m₀ t₀ : ℕ)
    (hm₀ : m₀ ∈ sourceD20LogCell Δ j)
    (ht₀ : t₀ ∈ sourceD20LogCell Δ j) :
    let C := sourceD20LogCell Δ j
    let K := sourceD20ActiveFullCell434 Δ W y j
    let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
    let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
    let V := A*(B-A)/B
    ‖∑ i ∈ K.product K,
      sourceD20FullPairCoefficient434 Δ W y H i‖^2 ≤
      4*V^2 * (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
        ‖H i.1 i.2 - H i.1 t₀ - H m₀ i.2 + H m₀ t₀‖^2) := by
  dsimp only
  let C := sourceD20LogCell Δ j
  let K := sourceD20ActiveFullCell434 Δ W y j
  let A : ℝ := ((C.filter (sourceD20Rough y)).card:ℝ)
  let B : ℝ := ((C.filter (sourceD20Rough W)).card:ℝ)
  let V := A*(B-A)/B
  let Hcell : ℕ → ℕ → ℂ := fun u v =>
    if (u,v) ∈ C.product C then H u v else 0
  have hInside (u v : ℕ) (hu : u ∈ C) (hv : v ∈ C) :
      Hcell u v = H u v := by
    exact if_pos (Finset.mem_product.mpr ⟨hu,hv⟩)
  have hMixed (i : ℕ × ℕ) (hi : i ∈ C.product C) :
      Hcell i.1 i.2-Hcell i.1 t₀-Hcell m₀ i.2+Hcell m₀ t₀ =
      H i.1 i.2 - H i.1 t₀ - H m₀ i.2 + H m₀ t₀ := by
    obtain ⟨hi1,hi2⟩ := Finset.mem_product.mp hi
    rw [hInside i.1 i.2 hi1 hi2,
      hInside i.1 t₀ hi1 ht₀,
      hInside m₀ i.2 hm₀ hi2,
      hInside m₀ t₀ hm₀ ht₀]
  have hFull := source_original_B452_full_cell_no_sparse_mask_sum434
    Δ W y j H
  have hP : originalD61ParityProjector434 0 (-1:ℂ) = 1 := by
    norm_num [originalD61ParityProjector434]
  have hBase := green64_original_D20_sparse_projected_variance_mixed_L2_434
    Δ W y hΔ hWy j j (C.product C) (Finset.Subset.rfl) H
    (fun _ => (-1:ℂ)) (fun _ => (-1:ℂ)) 0 m₀ t₀
  simp only [hP,mul_one] at hBase
  have hBase' :
      ‖∑ i ∈ C.product C, sourceD20FullPairCoefficient434 Δ W y H i‖^2 ≤
        (4*V*V) *
        (∑ i ∈ C.product C,
          |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖Hcell i.1 i.2-Hcell i.1 t₀-Hcell m₀ i.2+Hcell m₀ t₀‖^2) := by
    convert hBase using 1 <;> dsimp [Hcell,V,A,B,C] <;> ring
  have hRhs :
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖Hcell i.1 i.2-Hcell i.1 t₀-Hcell m₀ i.2+Hcell m₀ t₀‖^2) =
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖H i.1 i.2-H i.1 t₀-H m₀ i.2+H m₀ t₀‖^2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hMixed i hi]
  calc
    _ = ‖∑ i ∈ C.product C,
         sourceD20FullPairCoefficient434 Δ W y H i‖^2 := by rw [hFull]
    _ ≤ (4*V*V) *
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖Hcell i.1 i.2-Hcell i.1 t₀-Hcell m₀ i.2+Hcell m₀ t₀‖^2) := hBase'
    _ = 4*V^2 *
      (∑ i ∈ C.product C,
        |sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2| *
          ‖H i.1 i.2-H i.1 t₀-H m₀ i.2+H m₀ t₀‖^2) := by
      rw [hRhs]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## TrueFullD20DoubleCentering -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact tensor double-centering for COMPLEX source weights with total
mass zero in both original coordinates. The two anchors may lie OUTSIDE
the original index sets. This is an identity, not a Cauchy bound. -/
theorem source_original_B456_exact_double_centering434
    {M T : Type} (C1 : Finset M) (C2 : Finset T)
    (a : M → ℂ) (b : T → ℂ)
    (ha : (∑ m ∈ C1, a m) = 0)
    (hb : (∑ t ∈ C2, b t) = 0)
    (H : M → T → ℂ) (m₀ : M) (t₀ : T) :
    (∑ m ∈ C1, ∑ t ∈ C2, a m*b t*H m t) =
    ∑ m ∈ C1, ∑ t ∈ C2,
      a m*b t*(H m t-H m t₀-H m₀ t+H m₀ t₀) := by
  classical
  have hZeroRow (m : M) :
      (∑ t ∈ C2, a m*b t*H m t₀) = 0 := by
    calc
      _ = (a m*H m t₀)*(∑ t ∈ C2,b t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = 0 := by rw [hb]; ring
  have hZeroCol :
      (∑ m ∈ C1,∑ t ∈ C2, a m*b t*H m₀ t) = 0 := by
    have hfactor (m : M) :
        (∑ t ∈ C2, a m*b t*H m₀ t) =
          a m*(∑ t ∈ C2,b t*H m₀ t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    simp_rw [hfactor]
    rw [← Finset.sum_mul,ha]
    ring
  have hZeroBoth (m : M) :
      (∑ t ∈ C2, a m*b t*H m₀ t₀) = 0 := by
    calc
      _ = (a m*H m₀ t₀)*(∑ t ∈ C2,b t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ = 0 := by rw [hb]; ring
  have hRow : (∑ m ∈ C1,∑ t ∈ C2, a m*b t*H m t₀) = 0 := by
    simp_rw [hZeroRow]
    simp
  have hBoth : (∑ m ∈ C1,∑ t ∈ C2, a m*b t*H m₀ t₀) = 0 := by
    simp_rw [hZeroBoth]
    simp
  calc
    _ = (∑ m ∈ C1, ∑ t ∈ C2, a m*b t*H m t) -
        (∑ m ∈ C1, ∑ t ∈ C2, a m*b t*H m t₀) -
        (∑ m ∈ C1, ∑ t ∈ C2, a m*b t*H m₀ t) +
        (∑ m ∈ C1, ∑ t ∈ C2, a m*b t*H m₀ t₀) := by
      rw [hRow,hZeroCol,hBoth]
      ring
    _ = _ := by
      simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]

/-- LITERAL ORIGINAL FULL D20 coefficient, centered on its UNCHANGED
logarithmic cell, annihilates all source-only and target-only contributions.
The signed cofactor pair sum equals the same sum of its exact two-dimensional
mixed difference with ARBITRARY anchors, even outside the full cell.
No sparse cofactor support renormalization and no regularity hypothesis. -/
theorem source_original_B456_actual_full_D20_double_centering434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (j : ℕ)
    (H : ℕ → ℕ → ℂ) (m₀ t₀ : ℕ) :
    let C := sourceD20LogCell Δ j
    (∑ i ∈ C.product C, sourceD20FullPairCoefficient434 Δ W y H i) =
    ∑ i ∈ C.product C,
      (sourceD20FullDelta Δ W y i.1 : ℂ) *
      (sourceD20FullDelta Δ W y i.2 : ℂ) *
      (H i.1 i.2-H i.1 t₀-H m₀ i.2+H m₀ t₀) := by
  dsimp only
  let C := sourceD20LogCell Δ j
  have hZeroR := sourceD20_full_delta_zero hΔ hWy j
  have hZero : (∑ n ∈ C, (sourceD20FullDelta Δ W y n : ℂ)) = 0 := by
    exact_mod_cast hZeroR
  have hh := source_original_B456_exact_double_centering434 C C
    (fun n => (sourceD20FullDelta Δ W y n : ℂ))
    (fun n => (sourceD20FullDelta Δ W y n : ℂ))
    hZero hZero H m₀ t₀
  change (∑ i ∈ C.product C,
    (sourceD20FullDelta Δ W y i.1:ℂ) *
    (sourceD20FullDelta Δ W y i.2:ℂ) * H i.1 i.2) = _
  calc
    _ = ∑ m ∈ C, ∑ t ∈ C,
      (sourceD20FullDelta Δ W y m:ℂ) *
      (sourceD20FullDelta Δ W y t:ℂ) * H m t :=
        Finset.sum_product C C (fun i : ℕ × ℕ =>
          (sourceD20FullDelta Δ W y i.1:ℂ) *
          (sourceD20FullDelta Δ W y i.2:ℂ) * H i.1 i.2)
    _ = ∑ m ∈ C, ∑ t ∈ C,
      (sourceD20FullDelta Δ W y m:ℂ) *
      (sourceD20FullDelta Δ W y t:ℂ) *
        (H m t-H m t₀-H m₀ t+H m₀ t₀) := hh
    _ = _ := (Finset.sum_product C C (fun i : ℕ × ℕ =>
      (sourceD20FullDelta Δ W y i.1:ℂ) *
      (sourceD20FullDelta Δ W y i.2:ℂ) *
        (H i.1 i.2-H i.1 t₀-H m₀ i.2+H m₀ t₀))).symm

/-- The same exact mixed-difference formula for the ORIGINAL nonzero
full-D20 cofactor support K, without assuming either reference anchor lies
in C and WITHOUT inserting a sharp support cutoff in the physical kernel. -/
theorem source_original_B456_sparse_sum_unmasked_mixed_anchors_anywhere434
    (Δ W y : ℝ) (hΔ : 0 < Δ) (hWy : W ≤ y) (j : ℕ)
    (H : ℕ → ℕ → ℂ) (m₀ t₀ : ℕ) :
    let C := sourceD20LogCell Δ j
    let K := sourceD20ActiveFullCell434 Δ W y j
    (∑ i ∈ K.product K, sourceD20FullPairCoefficient434 Δ W y H i) =
    ∑ i ∈ C.product C,
      (sourceD20FullDelta Δ W y i.1 : ℂ) *
      (sourceD20FullDelta Δ W y i.2 : ℂ) *
      (H i.1 i.2-H i.1 t₀-H m₀ i.2+H m₀ t₀) := by
  calc
    _ = ∑ i ∈ (sourceD20LogCell Δ j).product (sourceD20LogCell Δ j),
      sourceD20FullPairCoefficient434 Δ W y H i :=
        source_original_B452_full_cell_no_sparse_mask_sum434 Δ W y j H
    _ = _ := source_original_B456_actual_full_D20_double_centering434
      Δ W y hΔ hWy j H m₀ t₀
end Green64Analytic.CorrelationSquare

end

end

/-! ## SignedCofactorPooling -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Exact SOURCE/TARGET pooling of a real signed cofactor coefficient
through the original sesquilinear finite physical pairing. Importantly
α is signed and REAL; no |α| majorant, character-average or denominator
cardinality has been inserted. This is a genuine alternative to B459's
pointwise full-cell weighted mixed variation.

One must bound the L² energy of the SIGNED POOLED endpoint observable,
not separately bound each individual cofactor and lose full cell mass. -/
theorem source_original_B468_finite_signed_pooled_bilinear434
    {X : Type} [Fintype X] (K : Finset ℕ) (alpha : ℕ → ℝ)
    (H : X → X → ℂ) (F G : ℕ → X → ℂ) :
    (∑ ab : X × X, H ab.1 ab.2 *
      star (∑ m ∈ K, (alpha m : ℂ) * F m ab.1) *
      (∑ n ∈ K, (alpha n : ℂ) * G n ab.2)) =
    ∑ m ∈ K, ∑ n ∈ K, ((alpha m * alpha n : ℝ) : ℂ) *
      (∑ ab : X × X, H ab.1 ab.2 * star (F m ab.1) * G n ab.2) := by
  classical
  have hpoint (ab : X × X) :
      H ab.1 ab.2 *
        star (∑ m ∈ K, (alpha m : ℂ) * F m ab.1) *
        (∑ n ∈ K, (alpha n : ℂ) * G n ab.2) =
      ∑ m ∈ K, ∑ n ∈ K, ((alpha m * alpha n : ℝ) : ℂ) *
        (H ab.1 ab.2 * star (F m ab.1) * G n ab.2) := by
    simp only [star_sum,star_mul,Complex.star_def,Complex.conj_ofReal]
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  calc
    _ = ∑ ab : X × X, ∑ m ∈ K, ∑ n ∈ K,
        ((alpha m * alpha n : ℝ) : ℂ) *
        (H ab.1 ab.2 * star (F m ab.1) * G n ab.2) := by
      apply Finset.sum_congr rfl
      intro ab hab
      exact hpoint ab
    _ = ∑ m ∈ K, ∑ n ∈ K, ∑ ab : X × X,
        ((alpha m * alpha n : ℝ) : ℂ) *
        (H ab.1 ab.2 * star (F m ab.1) * G n ab.2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualPhysicalSignedCofactorPool -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The actual SIGNED source/target D20 cofactor observable on the ORIGINAL
physical ν-dependent free-BIG harmonic space, with no absolute value or
sparse-fibre re-centering. This is the coherent endpoint state to which
C191 L²-normalization should be applied, rather than to every cofactor. -/
noncomputable def sourceOriginalB469D20SignedPooledTest434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Δ W y : ℝ) (j : ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℂ :=
  ∑ n ∈ sourceD20ActiveFullCell434 Δ W y j,
    (sourceD20FullDelta Δ W y n : ℂ) * F n ν a

/-- The ORIGINAL complete C191 signed physical pairing of the two
SIGNED pooled D20 cofactor endpoints equals the full double sum with
the ORIGINAL product Δ(m)Δ(t) and UNMODIFIED ν-dependent Fourier residual.
This identity avoids ANY full-cell L1 loss before C191 can act on pooled
endpoint energies; no source/olean T core identity is assumed. -/
theorem source_original_B469_true_C191_signed_D20_pooled_pairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (Δ W y : ℝ) (j : ℕ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    let K := sourceD20ActiveFullCell434 Δ W y j
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k
      (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F)
      (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j Gt) ν =
    ∑ i ∈ K.product K,
      sourceD20FullPairCoefficient434 Δ W y
        (fun mm nn => sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k (F mm) (Gt nn) ν) i := by
  dsimp only
  let K := sourceD20ActiveFullCell434 Δ W y j
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP free
  let mass := sourceOriginalVariableBIGMass434 BP free mu
  let E : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν d.Tb d.Vbig Q (hA ν) (hB ν) xi ζ theta k
      (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
  let H : X → X → ℂ := fun a b => ((mass a*mass b:ℝ):ℂ)*E (a,b)
  have hLeft :
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k
        (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F)
        (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j Gt) ν =
      ∑ ab : X × X,
        H ab.1 ab.2 *
          star (∑ n ∈ K, (sourceD20FullDelta Δ W y n : ℂ) * F n ν ab.1) *
          (∑ t ∈ K, (sourceD20FullDelta Δ W y t : ℂ) * Gt t ν ab.2) := by
    unfold sourceOriginalTrueNuSignedFullPhysicalPairing434
    apply Finset.sum_congr rfl
    intro ab hab
    dsimp only [sourceOriginalB469D20SignedPooledTest434,H,E]
    ring
  have hGeneric := source_original_B468_finite_signed_pooled_bilinear434
    K (sourceD20FullDelta Δ W y) H
    (fun n a => F n ν a) (fun n a => Gt n ν a)
  have hTerm (n t : ℕ) :
      (∑ ab : X × X, H ab.1 ab.2 * star (F n ν ab.1) * Gt t ν ab.2) =
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k (F n) (Gt t) ν := by
    unfold sourceOriginalTrueNuSignedFullPhysicalPairing434
    apply Finset.sum_congr rfl
    intro ab hab
    dsimp only [H,E]
    ring
  calc
    _ = ∑ ab : X × X,
        H ab.1 ab.2 *
          star (∑ n ∈ K, (sourceD20FullDelta Δ W y n : ℂ) * F n ν ab.1) *
          (∑ t ∈ K, (sourceD20FullDelta Δ W y t : ℂ) * Gt t ν ab.2) := hLeft
    _ = ∑ n ∈ K, ∑ t ∈ K,
          ((sourceD20FullDelta Δ W y n * sourceD20FullDelta Δ W y t:ℝ):ℂ) *
          (∑ ab : X × X, H ab.1 ab.2 * star (F n ν ab.1) * Gt t ν ab.2) := hGeneric
    _ = ∑ i ∈ K.product K,
          ((sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2:ℝ):ℂ) *
          (∑ ab : X × X, H ab.1 ab.2 * star (F i.1 ν ab.1) * Gt i.2 ν ab.2) := by
      exact (Finset.sum_product K K (fun i : ℕ × ℕ =>
        ((sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2:ℝ):ℂ) *
          (∑ ab : X × X, H ab.1 ab.2 * star (F i.1 ν ab.1) * Gt i.2 ν ab.2))).symm
    _ = ∑ i ∈ K.product K,
          ((sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2:ℝ):ℂ) *
          sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
            Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hTerm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold sourceD20FullPairCoefficient434
      push_cast
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## AllNuSignedD20Pooling -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- EXACT finite Fubini of SIGNED cofactor weights through BOTH original
ν family and four endpoint signs, preserving their order before the norm.
No |alpha| estimate and no cofactor/pattern state counting factor. -/
theorem source_original_B470_signed_pool_all_signs_Fubini434
    {N I : Type} (family : Finset N) (S : Finset I)
    (p : Bool × Bool → ℂ) (r : Bool × Bool → N → ℂ)
    (c : I → ℂ) (H : N → I → ℂ) :
    (∑ i ∈ S, c i * (∑ tw : Bool × Bool, p tw *
      (∑ ν ∈ family, r tw ν * H ν i))) =
    ∑ tw : Bool × Bool, p tw * (∑ ν ∈ family, r tw ν *
      (∑ i ∈ S, c i * H ν i)) := by
  classical
  calc
    _ = ∑ i ∈ S, ∑ tw : Bool × Bool, ∑ ν ∈ family,
        p tw * r tw ν * c i * H ν i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tw htw
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      ring
    _ = ∑ tw : Bool × Bool, ∑ ν ∈ family, ∑ i ∈ S,
        p tw * r tw ν * c i * H ν i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro tw htw
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro tw htw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν hν
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring


/-- The LITERAL original C191 physical all-two-block ν/four-sign
D20 centered DOUBLE cofactor sum is a single full signed physical pairing
of the two coherently POOLED source and target cofactor endpoint tests.

This equality is exact BEFORE any absolute value, character mean or
Fourier integral; no factor involving the entire D20-cell V is lost.
It identifies a genuine route to a Type-II bound: control the ORIGINAL
harmonic L² energy of each SIGNED pooled endpoint, not all individual
cofactors separately. T's original Q/P core binding remains a separate debt. -/
theorem source_original_B470_full_four_sign_D20_signed_pooling434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (Δ W y : ℝ) (j : ℕ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let K := sourceD20ActiveFullCell434 Δ W y j
    let alpha : ℕ → ℂ := fun n => (sourceD20FullDelta Δ W y n : ℂ)
    (∑ i ∈ K.product K,
      sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i) =
    ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν *
        sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
          Q hA hB xi ζ theta k
          (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F)
          (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j Gt)
          ν) := by
  dsimp only
  let K := sourceD20ActiveFullCell434 Δ W y j
  let alpha : ℕ → ℂ := fun n => (sourceD20FullDelta Δ W y n : ℂ)
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let p : Bool × Bool → ℂ := sourceOriginalB430ParityCoefficient
  let r : Bool × Bool → SourceOriginalProbePattern434 G m → ℂ :=
    fun tw ν => sourceOriginalB436TwoSign434 (ι := ι) J ell m hmJ tw ν
  let c : ℕ × ℕ → ℂ := fun i =>
    ((sourceD20FullDelta Δ W y i.1 * sourceD20FullDelta Δ W y i.2:ℝ):ℂ)
  let H : SourceOriginalProbePattern434 G m → ℕ × ℕ → ℂ := fun ν i =>
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k (F i.1) (Gt i.2) ν
  let PoolF := sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F
  let PoolG := sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j Gt
  have hAmplitude (i : ℕ × ℕ) :
      sourceOriginalB439FullFourSignCofactorAmplitude434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k alpha F Gt i =
      c i*(∑ tw : Bool × Bool, p tw*(∑ ν ∈ family,r tw ν*H ν i)) := by
    change (alpha i.1 * star (alpha i.2)) *
      (∑ tw : Bool × Bool, p tw*(∑ ν ∈ family,r tw ν*H ν i)) = _
    dsimp only [alpha,c]
    simp only [Complex.star_def,Complex.conj_ofReal]
    push_cast
    ring
  have hPool (ν : SourceOriginalProbePattern434 G m) :
      (∑ i ∈ K.product K, c i*H ν i) =
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k PoolF PoolG ν := by
    have hh := source_original_B469_true_C191_signed_D20_pooled_pairing434
      d J ell m hmJ Q hA hB xi ζ theta k Δ W y j F Gt ν
    change sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k PoolF PoolG ν =
      ∑ i ∈ K.product K, sourceD20FullPairCoefficient434 Δ W y
        (fun mm nn => sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k (F mm) (Gt nn) ν) i at hh
    calc
      _ = ∑ i ∈ K.product K, sourceD20FullPairCoefficient434 Δ W y
        (fun mm nn => sourceOriginalTrueNuSignedFullPhysicalPairing434
          d J ell m hmJ Q hA hB xi ζ theta k (F mm) (Gt nn) ν) i := by
        apply Finset.sum_congr rfl
        intro i hi
        unfold sourceD20FullPairCoefficient434
        dsimp only [c,H]
        push_cast
        ring
      _ = _ := hh.symm
  have hFubini := source_original_B470_signed_pool_all_signs_Fubini434
    family (K.product K) p r c H
  calc
    _ = ∑ i ∈ K.product K,
        c i*(∑ tw : Bool × Bool,p tw*(∑ ν ∈ family,r tw ν*H ν i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hAmplitude i
    _ = ∑ tw : Bool × Bool,p tw*(∑ ν ∈ family,r tw ν*
        (∑ i ∈ K.product K,c i*H ν i)) := hFubini
    _ = _ := by
      apply Finset.sum_congr rfl
      intro tw htw
      congr 1
      apply Finset.sum_congr rfl
      intro ν hν
      rw [hPool ν]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SignedPooledEndpointEnergyGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Exact energy of a REAL-SIGNED pooled cofactor endpoint: the original
full coherent norm-square is a signed cofactor CROSS Gram, with every
complex phase and offdiagonal term retained. No triangle inequality,
no |Δ| replacing Δ, no diagonal-only shortcut or cofactor count loss. -/
theorem source_original_B471_finite_real_signed_pooled_L2_Gram434
    {X : Type} (S : Finset X) (w : X → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℝ) (F : ℕ → X → ℂ) :
    (∑ a ∈ S, w a * ‖∑ m ∈ K, (alpha m:ℂ)*F m a‖^2) =
    ∑ m ∈ K, ∑ n ∈ K,
      (alpha m*alpha n) *
      (∑ a ∈ S, w a * (star (F m a)*F n a).re) := by
  classical
  have hPoint (a : X) :
      ‖∑ m ∈ K, (alpha m:ℂ)*F m a‖^2 =
      ∑ m ∈ K, ∑ n ∈ K,
        (alpha m*alpha n) * (star (F m a)*F n a).re := by
    have hh := source_original_B437_true_complex_square_sum_cross434
      K (fun m => (alpha m:ℂ)*F m a)
    calc
      _ = ∑ m ∈ K, ∑ n ∈ K,
            (star ((alpha m:ℂ)*F m a) * ((alpha n:ℂ)*F n a)).re := hh
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
        calc
          _ = (((alpha m*alpha n:ℝ):ℂ) *
            ((starRingEnd ℂ) (F m a)*F n a)).re := by
              congr 1
              push_cast
              ring
          _ = _ := by
            rw [Complex.mul_re]
            simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

  calc
    _ = ∑ a ∈ S, w a * (∑ m ∈ K, ∑ n ∈ K,
         (alpha m*alpha n) * (star (F m a)*F n a).re) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hPoint a]
    _ = ∑ a ∈ S, ∑ m ∈ K, ∑ n ∈ K,
          (alpha m*alpha n) * (w a*(star (F m a)*F n a).re) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ m ∈ K, ∑ n ∈ K, ∑ a ∈ S,
          (alpha m*alpha n) * (w a*(star (F m a)*F n a).re) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]

/-- SOURCE03 exact harmonic BIG-prime L² energy of the TRUE signed
D20-cofactor pooled endpoint. This is the original physical measure
`sourceOriginalVariableBIGMass434`, not counting measure or normalized on
any shortened support. The only quantity to bound before invoking C191
is the coherent two-cofactor signed Gram on the RHS. -/
theorem source_original_B471_true_physical_D20_pooled_energy_Gram434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Δ W y : ℝ) (j : ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    let K := sourceD20ActiveFullCell434 Δ W y j
    let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP free
    let mass := sourceOriginalVariableBIGMass434 BP free mu
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F) ν =
    ∑ n ∈ K, ∑ t ∈ K,
      (sourceD20FullDelta Δ W y n * sourceD20FullDelta Δ W y t) *
        (∑ a : X, mass a*(star (F n ν a)*F t ν a).re) := by
  dsimp only
  let K := sourceD20ActiveFullCell434 Δ W y j
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP free
  let mass := sourceOriginalVariableBIGMass434 BP free mu
  have hh := source_original_B471_finite_real_signed_pooled_L2_Gram434
    (Finset.univ : Finset X) mass K (sourceD20FullDelta Δ W y)
    (fun n a => F n ν a)
  change (∑ a : X, mass a *
      ‖∑ n ∈ K, (sourceD20FullDelta Δ W y n : ℂ)*F n ν a‖^2) = _
  exact hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## TruePooledEnergyNormalization -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- EXACT real scaling of a finite weighted complex L² energy. The
original sign, state weights and cofactor phases remain untouched. -/
theorem source_original_B472_weighted_real_scaled_energy434
    {X : Type} (S : Finset X) (w : X → ℝ)
    (F : X → ℂ) (r : ℝ) :
    (∑ a ∈ S, w a*‖(r:ℂ)*F a‖^2) =
    r^2*(∑ a ∈ S, w a*‖F a‖^2) := by
  calc
    _ = ∑ a ∈ S, r^2*(w a*‖F a‖^2) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
      ring
    _ = _ := by rw [Finset.mul_sum]

/-- Dividing an individual nonnegative energy by 1+the total energy of
a full finite family makes it <=1, with no zero-denominator assumption.
This is an exact constructive normalization, not a Gram smallness claim. -/
theorem source_original_B472_sqrt_total_energy_norm434
    (Etotal E : ℝ) (hTotal : 0 ≤ Etotal) (hE : E ≤ Etotal) :
    ((Real.sqrt (1+Etotal))⁻¹)^2 * E ≤ 1 := by
  have hpos : 0 < 1+Etotal := by linarith
  rw [inv_pow,Real.sq_sqrt hpos.le]
  rw [mul_comm,←div_eq_mul_inv]
  rw [div_le_iff₀ hpos]
  linarith


/-- Exact multiplication of the ORIGINAL source physical V_g-normalized
harmonic free-BIG cofactor endpoint L² energy by a real scalar squared.
No replacement by a uniform counting measure. -/
theorem source_original_B472_true_physical_energy_scale434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (F : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) (r : ℝ) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (r:ℂ)*F η a) ν =
    r^2 * sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ F ν := by
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let free := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP free
  let w := sourceOriginalVariableBIGMass434 BP free mu
  have hh := source_original_B472_weighted_real_scaled_energy434
    (Finset.univ : Finset X) w (F ν) r
  change (∑ a : X, w a*‖(r:ℂ)*F ν a‖^2) =
    r^2*(∑ a : X, w a*‖F ν a‖^2)
  exact hh

/-- The TOTAL TRUE harmonic L² energy of one signed D20-cofactor pooled
physical endpoint over the whole ORIGINAL two-block ν-family. All ν
source harmonic BIG measures remain distinct and genuine. -/
noncomputable def sourceOriginalB472TotalPooledPhysicalEnergy434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (family : Finset (SourceOriginalProbePattern434 G m))
    (Δ W y : ℝ) (j : ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) : ℝ :=
  ∑ ν ∈ family, sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
    (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F) ν

/-- A coherently signed D20 pooled endpoint, normalized by its exact
ORIGINAL total harmonic physical L² energy plus one. The added one ensures
there is never a zero denominator, WITHOUT claiming the raw signed Gram
energy is small. -/
noncomputable def sourceOriginalB472NormalizedPooledPhysicalTest434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (family : Finset (SourceOriginalProbePattern434 G m))
    (Δ W y : ℝ) (j : ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℂ :=
  let E := sourceOriginalB472TotalPooledPhysicalEnergy434 d J ell m hmJ
    family Δ W y j F
  ((Real.sqrt (1+E))⁻¹:ℂ) *
    sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F ν a

/-- Exact ORIGINAL source C191 per-ν harmonic energy admissibility of the
coherently signed D20 cofactor pooled endpoint after scaling by the TRUE
total family harmonic energy plus one. This discharges every individual
ν-dependent C191 L² ≤1 hypothesis without an L¹ cofactor mass bound. -/
theorem source_original_B472_normalized_pooled_physical_energy_le_one434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J)
    (family : Finset (SourceOriginalProbePattern434 G m))
    (Δ W y : ℝ) (j : ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
        family Δ W y j F) ν ≤ 1 := by
  let PoolF := sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F
  let En : SourceOriginalProbePattern434 G m → ℝ := fun η =>
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ PoolF η
  let Etot : ℝ := ∑ η ∈ family, En η
  have hPos (η : SourceOriginalProbePattern434 G m) : 0 ≤ En η :=
    source_original_B433_true_physical_energy_nonneg434
      d hVbig J ell m hmJ PoolF η
  have hEtot : 0 ≤ Etot := by
    apply Finset.sum_nonneg
    intro η hη
    exact hPos η
  have hIndividual : En ν ≤ Etot :=
    Finset.single_le_sum (fun η hη => hPos η) hν
  let r : ℝ := (Real.sqrt (1+Etot))⁻¹
  have hScale := source_original_B472_true_physical_energy_scale434
    d J ell m hmJ PoolF ν r
  have hDef :
      sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
        family Δ W y j F = (fun η a => (r:ℂ)*PoolF η a) := by
    funext η a
    dsimp only [sourceOriginalB472NormalizedPooledPhysicalTest434,
      sourceOriginalB472TotalPooledPhysicalEnergy434,PoolF,En,Etot,r]
    rw [Complex.ofReal_inv]
  rw [hDef]
  change sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (r:ℂ)*PoolF η a) ν ≤ 1
  have hNorm : r^2 * En ν ≤ 1 := by
    change ((Real.sqrt (1+Etot))⁻¹)^2 * En ν ≤ 1
    exact source_original_B472_sqrt_total_energy_norm434
      Etot (En ν) hEtot hIndividual
  calc
    _ = r^2 * En ν := hScale
    _ ≤ 1 := hNorm


/-- Exact source test equality making the real pooled-energy normalization
available to the complete original two-block/four-sign physical consumer,
without relying on implicit real-to-complex inverse coercion. -/
theorem source_original_B472_normalized_pool_eq_real_scale434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (family : Finset (SourceOriginalProbePattern434 G m))
    (Δ W y : ℝ) (j : ℕ)
    (F : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let E := sourceOriginalB472TotalPooledPhysicalEnergy434 d J ell m hmJ
      family Δ W y j F
    let r : ℝ := (Real.sqrt (1+E))⁻¹
    sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
      family Δ W y j F =
      (fun η a => (r:ℂ) *
        sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ
          Δ W y j F η a) := by
  dsimp only
  funext η a
  dsimp only [sourceOriginalB472NormalizedPooledPhysicalTest434,
    sourceOriginalB472TotalPooledPhysicalEnergy434]
  rw [Complex.ofReal_inv]
end Green64Analytic.CorrelationSquare

end

end

/-! ## NormalizedSignedD20C191Saving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

/-- The ORIGINAL SOURCE03 all-two-block four-sign physical C191/C6 signed
saving applied DIRECTLY to coherently SIGNED D20 pooled endpoints after
normalizing by their TRUE TOTAL ν-dependent harmonic L² energy. This keeps
all D20 offdiagonal cofactor cancellation intact and does not lose V⁴.
The original structural/moving Q/ζ/θ/major-minor hypotheses are preserved.
Does not claim actual pooled Gram E_src/E_tgt small, nor T shift 2k identity. -/
theorem eventually_source_original_B474_signed_D20_normalized_pool_four_sign_C191_saving434
    (cfg : SourceComparisonFixed434)
    (Cq CxiNat Cs C4 : ℕ) (gamma d Bmaj : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBmaj : 0 < Bmaj)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0 *
      Real.log (((cfg.tmax.factorial:ℕ):ℝ) *
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Cchar CxiReal Bgoal : ℝ)
    (hCchar : 0 ≤ Cchar) (hCxiReal : 0 ≤ CxiReal)
    (hExpBudget : Bgoal+8*(Cchar+CxiReal) ≤ Bsave)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc)
    (M Bout : ℝ) (hM : 0 ≤ M)
    (hXiExponent :
      2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1 ≤ (CxiNat:ℝ))
    (hMinorExponent :
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal)
    (Cgroup Ck Dgoal : ℝ)
    (hCgroup : 0 ≤ Cgroup) (hCk : 0 < Ck) :
    ∃ K Y : ℝ, 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Ydata Hprime : ℝ)
    (data : SourceComparisonData434 ι β cfg x L Ydata Hprime)
    (loS hiS : ι → ℕ) (loB hiB : β → ℕ)
    (hSmallSubset : ∀ i, data.Ts i ⊆
       sourceOriginalActualPrimeBand434 (loS i) (hiS i))
    (hBigFull : ∀ j, data.Tb j =
       sourceOriginalActualPrimeBand434 (loB j) (hiB j))
    (hSmallOrder : ∀ i j : ι, i ≠ j →
       hiS i ≤ loS j ∨ hiS j ≤ loS i)
    (hBigOrder : ∀ i j : β, i ≠ j →
       hiB i ≤ loB j ∨ hiB j ≤ loB i)
    (hTsUpper : ∀ i : ι, ∀ p ∈ data.Ts i,
       (p:ℝ) ≤ Real.exp (L^cfg.bexp))
    (hVbig : ∀ g : β, data.Vbig g =
       ∑ p ∈ data.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (J ell : ℕ) (hmJ : m ≤ J)
    (hTbLower : ∀ g : β, ∀ p ∈ data.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (hQpoly : (Qchar:ℝ) ≤ L^Cchar)
    (hXipoly : xi⁻¹ ≤ L^CxiReal)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hVFloor : cfg.vmin ≤ Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYbound : ∀ g : β, Y ≤ ((loB g+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1)))
    (Δ W y : ℝ) (j : ℕ)
    (sourceFamily targetFamily : ℕ →
      (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hGroups : (((blockA.card+blockB.card:ℕ)):ℝ) ≤
      Cgroup*Real.log L)
    (hMajorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2)+2*Ck ≤ 2*Bmaj)
    (hMinorExp :
      Dgoal+2*((m:ℝ)*Cgroup*Real.log 2) ≤ Bout),
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let budget : ℝ :=
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
    let shared := fun ν : SourceOriginalProbePattern434 β m =>
      ((Fintype.card ι)*J) + ∑ g : β,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun tw : Bool × Bool => fun ν : SourceOriginalProbePattern434 β m =>
      (if tw.1 then (-1:ℂ)^(shared ν) else 1) *
      (if tw.2 then (-1:ℂ)^(shared ν) else 1)
    ‖∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ family,
        sign tw ν *
          sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        (sourceOriginalB472NormalizedPooledPhysicalTest434 data J ell m hmJ
          family Δ W y j sourceFamily)
        (sourceOriginalB472NormalizedPooledPhysicalTest434 data J ell m hmJ
          family Δ W y j targetFamily) ν)‖^2 ≤
      288006*L^(-Dgoal) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_B473_any_normalized_physical_four_sign_C191_saving434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
      Cgroup Ck Dgoal hCgroup hCk
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hOrig
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hVFloor hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice Δ W y j sourceFamily targetFamily
    hGroups hMajorExp hMinorExp
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let sourceTest := sourceOriginalB472NormalizedPooledPhysicalTest434
    data J ell m hmJ family Δ W y j sourceFamily
  let targetTest := sourceOriginalB472NormalizedPooledPhysicalTest434
    data J ell m hmJ family Δ W y j targetFamily
  have hSource : ∀ ν ∈ family,
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ≤ 1 := by
    intro ν hν
    exact source_original_B472_normalized_pooled_physical_energy_le_one434
      data hVbig J ell m hmJ family Δ W y j sourceFamily ν hν
  have hTarget : ∀ ν ∈ family,
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ≤ 1 := by
    intro ν hν
    exact source_original_B472_normalized_pooled_physical_energy_le_one434
      data hVbig J ell m hmJ family Δ W y j targetFamily ν hν
  have h := hOrig x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hVFloor hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hSource hTarget
    hGroups hMajorExp hMinorExp
  exact h
end Green64Analytic.CorrelationSquare

end

end

/-! ## RealScaledPhysicalC191FourSign -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Exactly scale the ORIGINAL C191 physical sesquilinear source/target
pairing by two INDEPENDENT real factors r,s, retaining every original
harmonic prime mass, moving Q and signed Fourier ζ/θ residual. -/
theorem source_original_B475_physical_real_scaled_pairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (Fs Gs : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) (r s : ℝ) :
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k
      (fun η a => (r:ℂ)*Fs η a) (fun η b => (s:ℂ)*Gs η b) ν =
    ((r*s:ℝ):ℂ) *
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k Fs Gs ν := by
  unfold sourceOriginalTrueNuSignedFullPhysicalPairing434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring

/-- The same exact two-real-factor scaling AFTER the genuine SOURCE03
complete two-block family and both independent (+,-,-,+)/4 endpoint signs.
Crucially this is an equality BEFORE any norm/square. -/
theorem source_original_B475_four_sign_real_scaled_pairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (Fs Gs : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (r s : ℝ) :
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let shared := fun ν : SourceOriginalProbePattern434 G m =>
      ((Fintype.card ι)*J)+∑ g : G,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun tw : Bool × Bool => fun ν : SourceOriginalProbePattern434 G m =>
      (if tw.1 then (-1:ℂ)^(shared ν) else 1) *
      (if tw.2 then (-1:ℂ)^(shared ν) else 1)
    (∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ family, sign tw ν *
        sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
          Q hA hB xi ζ theta k
          (fun η a => (r:ℂ)*Fs η a)
          (fun η b => (s:ℂ)*Gs η b) ν)) =
    ((r*s:ℝ):ℂ) *
      (∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ ν ∈ family, sign tw ν *
        sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
          Q hA hB xi ζ theta k Fs Gs ν)) := by
  dsimp only
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun tw : Bool × Bool => fun ν : SourceOriginalProbePattern434 G m =>
    (if tw.1 then (-1:ℂ)^(shared ν) else 1) *
    (if tw.2 then (-1:ℂ)^(shared ν) else 1)
  let Full : SourceOriginalProbePattern434 G m → ℂ := fun ν =>
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k Fs Gs ν
  let Scaled : SourceOriginalProbePattern434 G m → ℂ := fun ν =>
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k
      (fun η a => (r:ℂ)*Fs η a) (fun η b => (s:ℂ)*Gs η b) ν
  have hPoint (ν : SourceOriginalProbePattern434 G m) :
      Scaled ν = ((r*s:ℝ):ℂ)*Full ν :=
    source_original_B475_physical_real_scaled_pairing434
      d J ell m hmJ Q hA hB xi ζ theta k Fs Gs ν r s
  change (∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
    (∑ ν ∈ family, sign tw ν*Scaled ν)) =
    ((r*s:ℝ):ℂ) * (∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
    (∑ ν ∈ family, sign tw ν*Full ν))
  exact source_original_B450_two_stage_weighted_scale434
    family sourceOriginalB430ParityCoefficient sign Scaled Full
    ((r*s:ℝ):ℂ) (fun ν _ => hPoint ν)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SignedPooledPhysicalScaling -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- The LITERAL original SOURCE03 C191 two-block/four-sign physical
functional on the genuine dependent BIG free-prime harmonic test families.
This retains the actual ν signs, original moving Q/ζ/θ and keeps the
(+,-,-,+)/4 projector INSIDE the physical complex sum. -/
noncomputable def sourceOriginalB476FourSignPhysicalC191434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (Fs Gs : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) : ℂ :=
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J) + ∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun tw : Bool × Bool => fun ν : SourceOriginalProbePattern434 G m =>
    (if tw.1 then (-1:ℂ)^(shared ν) else 1) *
    (if tw.2 then (-1:ℂ)^(shared ν) else 1)
  ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
    (∑ ν ∈ family, sign tw ν *
      sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
        Q hA hB xi ζ theta k Fs Gs ν)

/-- The normalized signed D20 pooled C191 residual is EXACTLY the
original UNNORMALIZED signed pooled physical residual times the product
of the two reciprocal square roots of their TRUE original ν-family
harmonic L² energies. No full cell L¹ or V⁴ estimate is used. -/
theorem source_original_B476_signed_pool_normalization_exact434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (Δ W y : ℝ) (j : ℕ)
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let E1 := sourceOriginalB472TotalPooledPhysicalEnergy434
      d J ell m hmJ family Δ W y j F
    let E2 := sourceOriginalB472TotalPooledPhysicalEnergy434
      d J ell m hmJ family Δ W y j Gt
    let r1 : ℝ := (Real.sqrt (1+E1))⁻¹
    let r2 : ℝ := (Real.sqrt (1+E2))⁻¹
    sourceOriginalB476FourSignPhysicalC191434 d blockA blockB
      J ell m hmJ Q hA hB xi ζ theta k
      (sourceOriginalB472NormalizedPooledPhysicalTest434
        d J ell m hmJ family Δ W y j F)
      (sourceOriginalB472NormalizedPooledPhysicalTest434
        d J ell m hmJ family Δ W y j Gt) =
    ((r1*r2:ℝ):ℂ) *
      sourceOriginalB476FourSignPhysicalC191434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k
        (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F)
        (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j Gt) := by
  dsimp only
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let E1 := sourceOriginalB472TotalPooledPhysicalEnergy434
    d J ell m hmJ family Δ W y j F
  let E2 := sourceOriginalB472TotalPooledPhysicalEnergy434
    d J ell m hmJ family Δ W y j Gt
  let r1 : ℝ := (Real.sqrt (1+E1))⁻¹
  let r2 : ℝ := (Real.sqrt (1+E2))⁻¹
  let PoolF := sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F
  let PoolG := sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j Gt
  have hF := source_original_B472_normalized_pool_eq_real_scale434
    d J ell m hmJ family Δ W y j F
  have hG := source_original_B472_normalized_pool_eq_real_scale434
    d J ell m hmJ family Δ W y j Gt
  change sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
    family Δ W y j F = (fun η a => (r1:ℂ)*PoolF η a) at hF
  change sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
    family Δ W y j Gt = (fun η a => (r2:ℂ)*PoolG η a) at hG
  rw [hF,hG]
  have hh := source_original_B475_four_sign_real_scaled_pairing434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k PoolF PoolG r1 r2
  change sourceOriginalB476FourSignPhysicalC191434 d blockA blockB
    J ell m hmJ Q hA hB xi ζ theta k
    (fun η a => (r1:ℂ)*PoolF η a) (fun η b => (r2:ℂ)*PoolG η b) = _
  exact hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SignedPooledEnergyDescaling -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Exact reversal of the constructive ORIGINAL physical signed-pool
normalization. The only loss is the two TRUE pooled harmonic Gram energies
E1 and E2; no absolute D20 cofactor mass, V^4 or cardinality is inserted.
It creates no arithmetic smallness for those energies. -/
noncomputable def sourceOriginalB477EnergyFactor434 (E1 E2 : ℝ) : ℝ :=
  (Real.sqrt (1+E1))⁻¹ * (Real.sqrt (1+E2))⁻¹

theorem source_original_B477_signed_pool_energy_descaling434
    (E1 E2 T : ℝ) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2) (hT : 0 ≤ T)
    (Z : ℂ)
    (h : ‖(sourceOriginalB477EnergyFactor434 E1 E2 : ℂ) * Z‖^2 ≤ T) :
    ‖Z‖^2 ≤ (1+E1)*(1+E2)*T := by
  have hp1 : 0 < 1+E1 := by linarith
  have hp2 : 0 < 1+E2 := by linarith
  have hs1 : 0 < Real.sqrt (1+E1) := Real.sqrt_pos.2 hp1
  have hs2 : 0 < Real.sqrt (1+E2) := Real.sqrt_pos.2 hp2
  have hr1 : 0 < (Real.sqrt (1+E1))⁻¹ := inv_pos.mpr hs1
  have hr2 : 0 < (Real.sqrt (1+E2))⁻¹ := inv_pos.mpr hs2
  have hNorm : ‖(sourceOriginalB477EnergyFactor434 E1 E2 : ℂ) * Z‖^2 =
      (1/((1+E1)*(1+E2))) * ‖Z‖^2 := by
    unfold sourceOriginalB477EnergyFactor434
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hr1 hr2),mul_pow]
    rw [mul_pow,inv_pow,inv_pow,Real.sq_sqrt hp1.le,Real.sq_sqrt hp2.le]
    field_simp
  rw [hNorm] at h
  have hp : 0 < (1+E1)*(1+E2) := mul_pos hp1 hp2
  have hh : ‖Z‖^2 / ((1+E1)*(1+E2)) ≤ T := by
    simpa [div_eq_mul_inv,mul_comm] using h
  simpa only [mul_comm] using (div_le_iff₀ hp).mp hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualSignedPoolC191Descale -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact constructive descaling for the GENUINE original signed D20
physical two-block/four-sign pooled C191 residual. Only the true two
coherent signed ν-harmonic Gram energies are paid. No full D20 absolute
mass, V^4 or count of source cofactor pairs is introduced. -/
theorem source_original_B478_actual_signed_pool_C191_descaled_bound434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (Δ W y : ℝ) (j : ℕ)
    (hVbig : ∀ g, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (F Gt : (n : ℕ) → (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (T : ℝ) (hT : 0 ≤ T)
    (hBound :
      ‖sourceOriginalB476FourSignPhysicalC191434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k
        (sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
          (sourceOriginalTwoBlockProbePatterns434 blockA blockB m) Δ W y j F)
        (sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
          (sourceOriginalTwoBlockProbePatterns434 blockA blockB m) Δ W y j Gt)‖^2 ≤ T) :
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let E1 := sourceOriginalB472TotalPooledPhysicalEnergy434 d J ell m hmJ
      family Δ W y j F
    let E2 := sourceOriginalB472TotalPooledPhysicalEnergy434 d J ell m hmJ
      family Δ W y j Gt
    ‖sourceOriginalB476FourSignPhysicalC191434 d blockA blockB
        J ell m hmJ Q hA hB xi ζ theta k
        (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F)
        (sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j Gt)‖^2 ≤
      (1+E1)*(1+E2)*T := by
  dsimp only
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let E1 := sourceOriginalB472TotalPooledPhysicalEnergy434 d J ell m hmJ
    family Δ W y j F
  let E2 := sourceOriginalB472TotalPooledPhysicalEnergy434 d J ell m hmJ
    family Δ W y j Gt
  let P1 := sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j F
  let P2 := sourceOriginalB469D20SignedPooledTest434 d J ell m hmJ Δ W y j Gt
  let Z := sourceOriginalB476FourSignPhysicalC191434 d blockA blockB
    J ell m hmJ Q hA hB xi ζ theta k P1 P2
  have hE1 : 0 ≤ E1 := by
    dsimp only [E1,sourceOriginalB472TotalPooledPhysicalEnergy434]
    apply Finset.sum_nonneg
    intro ν hν
    exact source_original_B433_true_physical_energy_nonneg434
      d hVbig J ell m hmJ P1 ν
  have hE2 : 0 ≤ E2 := by
    dsimp only [E2,sourceOriginalB472TotalPooledPhysicalEnergy434]
    apply Finset.sum_nonneg
    intro ν hν
    exact source_original_B433_true_physical_energy_nonneg434
      d hVbig J ell m hmJ P2 ν
  have hScaled := source_original_B476_signed_pool_normalization_exact434
    d blockA blockB J ell m hmJ Q hA hB xi ζ theta k Δ W y j F Gt
  change sourceOriginalB476FourSignPhysicalC191434 d blockA blockB
      J ell m hmJ Q hA hB xi ζ theta k
      (sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
        family Δ W y j F)
      (sourceOriginalB472NormalizedPooledPhysicalTest434 d J ell m hmJ
        family Δ W y j Gt) =
    ((sourceOriginalB477EnergyFactor434 E1 E2 : ℝ):ℂ) * Z at hScaled
  rw [hScaled] at hBound
  change ‖((sourceOriginalB477EnergyFactor434 E1 E2 : ℝ):ℂ)*Z‖^2 ≤ T at hBound
  exact source_original_B477_signed_pool_energy_descaling434
    E1 E2 T hE1 hE2 hT Z hBound
end Green64Analytic.CorrelationSquare

end

end

