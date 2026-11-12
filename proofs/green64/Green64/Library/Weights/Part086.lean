module

public import Green64.Library.Correlation.Part061
public import Green64.Library.Weights.Part043
public import Green64.Library.Correlation.Part060
public import Green64.Library.Correlation.Part059

@[expose] public section

/-!
# Weights / Part086

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## TrueSignedPooledC191EnergyBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64ComparisonPartial Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

/-- Actual original C191+C6 signed D20 cofactor-pool four-sign bound,
UNNORMALIZED. Its only loss is the exact product of genuine signed pooled
ν-dependent harmonic endpoint Gram energies; no D20 total absolute mass
or V⁴ penalty. All SOURCE03 original Q/ζ/θ/four-sign arithmetic assumptions
and the large-L threshold of B474 remain literal. Not yet native T TypeII. -/
theorem eventually_source_original_B479_true_signed_D20_physical_C191_energy_weighted_saving434
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
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let E1 := sourceOriginalB472TotalPooledPhysicalEnergy434
      data J ell m hmJ family Δ W y j sourceFamily
    let E2 := sourceOriginalB472TotalPooledPhysicalEnergy434
      data J ell m hmJ family Δ W y j targetFamily
    ‖sourceOriginalB476FourSignPhysicalC191434 data blockA blockB
       J ell m hmJ Qchar hAvar hBvar xi ζ theta k
       (sourceOriginalB469D20SignedPooledTest434
         data J ell m hmJ Δ W y j sourceFamily)
       (sourceOriginalB469D20SignedPooledTest434
         data J ell m hmJ Δ W y j targetFamily)‖^2 ≤
       (1+E1)*(1+E2)*(288006*L^(-Dgoal)) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_B474_signed_D20_normalized_pool_four_sign_C191_saving434
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
  let T : ℝ := 288006*L^(-Dgoal)
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
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
    hXiChoice Δ W y j sourceFamily targetFamily
    hGroups hMajorExp hMinorExp
  have hNormalized :
      ‖sourceOriginalB476FourSignPhysicalC191434 data blockA blockB
        J ell m hmJ Qchar hAvar hBvar xi ζ theta k sourceTest targetTest‖^2 ≤ T := by
    change ‖sourceOriginalB476FourSignPhysicalC191434 data blockA blockB
      J ell m hmJ Qchar hAvar hBvar xi ζ theta k sourceTest targetTest‖^2 ≤ T at h
    exact h
  have hBudget := source_original_B478_actual_signed_pool_C191_descaled_bound434
    data blockA blockB J ell m hmJ Qchar hAvar hBvar xi ζ theta k
    Δ W y j hVbig sourceFamily targetFamily T hT hNormalized
  exact hBudget
end Green64Analytic.CorrelationSquare

end

end

/-! ## FixedPositionPhysicalHarmonicDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Product of the TRUE numeric prime labels in one original ν-dependent
free-BIG state. Repetitions, when present in the independent harmonic
state space, are retained with their full labelled multiplicities. -/
noncomputable def sourceOriginalB542FreePrimeProduct434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) : ℝ :=
  ∏ g : G, ∏ i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),
    ((a g i).val : ℝ)

/-- The actual V-normalized counting weight of the same free marks,
before source q damping and the genuine physical divisibility/Nodup mask. -/
noncomputable def sourceOriginalB542FreeCountNormalizer434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) : ℝ :=
  ∏ g : G, (d.Vbig g ^
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g)⁻¹

/-- EXACT original physical measure mismatch at a fixed outside position:
μ(a) times the FULL product of the original labelled primes equals the
V-normalized counting weight. A square-root prime product would not
transport an unchanged two-ended Knu kernel to the C191 harmonic pairing. -/
theorem source_original_B542_true_harmonic_counting_density434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    sourceOriginalVariableBIGMass434
      (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
      (sourceOriginalJointHarmonicMu434
        (fun g : G => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) d.Vbig) a *
      sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a =
      sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν := by
  unfold sourceOriginalVariableBIGMass434 sourceOriginalJointHarmonicMu434
    sourceOriginalHarmonicPrimeMu434 sourceOriginalB542FreePrimeProduct434
    sourceOriginalB542FreeCountNormalizer434
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  rw [← Finset.prod_mul_distrib]
  have hp (i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g)) :
      ((1 / ((a g i).val:ℝ)) / d.Vbig g) * ((a g i).val:ℝ) = (d.Vbig g)⁻¹ := by
    have hpn : ((a g i).val:ℝ) ≠ 0 := by
      exact_mod_cast (d.hTbPrime g (a g i).val (a g i).property).ne_zero
    have hV : d.Vbig g ≠ 0 := (cfg.hv.trans_le (d.hVbig g)).ne'
    field_simp
  simp_rw [hp]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,inv_pow]

/-- The corresponding TRUE C191 harmonic L2 energy retains one full
numeric prime product after the fixed-position counting pullback.
The test may contain the entire unchanged D20 signed cofactor sum,
physical q damping, P gate, original mark mask, and sourceCore; none is
replaced by an absolute cofactor sum. -/
theorem source_original_B542_true_C191_counting_pullback_energy434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (test : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
        test η a) ν =
    sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν *
      ∑ a, sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a *
        ‖test ν a‖^2 := by
  unfold sourceOriginalTrueNuSignedFullPhysicalEnergy434
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  have hDensity := source_original_B542_true_harmonic_counting_density434
    d J ell m hmJ ν a
  calc
    _ = (sourceOriginalVariableBIGMass434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
        (sourceOriginalJointHarmonicMu434
          (fun g : G => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) d.Vbig) a *
        sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a) *
        (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a *
          ‖test ν a‖^2) := by ring
    _ = _ := by rw [hDensity]

/-- Exact TWO-END C191 pullback with the SAME original signed
RAW-minus-Knu Fourier kernel. The full prime product is placed inside
each endpoint test; all original k, theta, zeta and canonical Knu
parameters remain unchanged. Physical mark masks or complete signed
D20 endpoint sums may be inserted in the tests without modifying this
identity. This does not equate the full outside-position source sum. -/
theorem source_original_B542_true_C191_counting_pullback_pairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalPairing434 d J ell m hmJ
      Q hA hB xi ζ theta k
      (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
        sourceTest η a)
      (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
        targetTest η a) ν =
    (sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν : ℂ)^2 *
      ∑ ab : (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) ×
        (SourceOriginalVariableBIGState434
          (fun g : G => {p : ℕ // p ∈ d.Tb g})
          (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)),
        star (sourceTest ν ab.1) * targetTest ν ab.2 *
          sourceOriginalProbeSignedMajorFourierError434
            J ell m hmJ ν d.Tb d.Vbig Q (hA ν) (hB ν) xi ζ theta k
            (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val) := by
  unfold sourceOriginalTrueNuSignedFullPhysicalPairing434
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  let μ := sourceOriginalVariableBIGMass434
    (fun g : G => {p : ℕ // p ∈ d.Tb g})
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
    (sourceOriginalJointHarmonicMu434
      (fun g : G => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) d.Vbig)
  let Pn := sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν
  let Cn := sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν
  have h1 : (μ ab.1:ℂ) * (Pn ab.1:ℂ) = (Cn:ℂ) := by
    exact_mod_cast source_original_B542_true_harmonic_counting_density434
      d J ell m hmJ ν ab.1
  have h2 : (μ ab.2:ℂ) * (Pn ab.2:ℂ) = (Cn:ℂ) := by
    exact_mod_cast source_original_B542_true_harmonic_counting_density434
      d J ell m hmJ ν ab.2
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]
  change (μ ab.1:ℂ)*(μ ab.2:ℂ) *
      ((starRingEnd ℂ) (sourceTest ν ab.1) * (Pn ab.1:ℂ)) *
      ((Pn ab.2:ℂ) * targetTest ν ab.2) * _ = _
  calc
    _ = ((μ ab.1:ℂ)*(Pn ab.1:ℂ))*((μ ab.2:ℂ)*(Pn ab.2:ℂ))*
        (starRingEnd ℂ) (sourceTest ν ab.1)*targetTest ν ab.2 *
        sourceOriginalProbeSignedMajorFourierError434
          J ell m hmJ ν d.Tb d.Vbig Q (hA ν) (hB ν) xi ζ theta k
          (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val) := by ring
    _ = _ := by rw [h1,h2]; dsimp only [Cn]; ring

/-- The prime-product distortion is bounded below by the product of
the TRUE BIG-prime lower bound over all actual free labels. This holds
for every original dependent state, including repeated numeric primes. -/
theorem source_original_B542_true_BIG_prime_product_lower434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (hBIG : ∀ g, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (a : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ d.Tb g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    Real.exp (((∑ g : G,
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g : ℕ):ℝ) * L^cfg.cexp) ≤
      sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a := by
  rw [Real.exp_nat_mul, ← Finset.prod_pow_eq_pow_sum]
  unfold sourceOriginalB542FreePrimeProduct434
  apply Finset.prod_le_prod₀
  · intro g hg
    positivity
  · intro g hg
    calc
      _ = ∏ _i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g),
          Real.exp (L^cfg.cexp) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (Real.exp_pos _).le
        · intro i hi
          exact hBIG g (a g i).val (a g i).property

/-- A direct fixed-position lift of the unchanged physical counting
row into C191 has squared-L2 energy distortion at least the genuine
BIG prime-product lower bound relative to V-normalized counting energy. Outside-position averaging has not been interchanged
here; this is a precise obstruction to treating it as a harmless bounded
endpoint test. It is NOT a no-go for the full signed comparison. -/
theorem source_original_B542_true_fixed_position_energy_distortion434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (test : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (hBIG : ∀ g, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ)) :
    Real.exp (((∑ g : G,
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g : ℕ):ℝ) * L^cfg.cexp) *
      (sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν *
        ∑ a, ‖test ν a‖^2) ≤
    sourceOriginalTrueNuSignedFullPhysicalEnergy434 d J ell m hmJ
      (fun η a => (sourceOriginalB542FreePrimeProduct434 d J ell m hmJ η a:ℂ) *
        test η a) ν := by
  rw [source_original_B542_true_C191_counting_pullback_energy434]
  have hV : 0 ≤ sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν := by
    unfold sourceOriginalB542FreeCountNormalizer434
    apply Finset.prod_nonneg
    intro g hg
    exact inv_nonneg.mpr (pow_nonneg (cfg.hv.trans_le (d.hVbig g)).le _)
  have hSum :
      Real.exp (((∑ g : G,
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g : ℕ):ℝ) * L^cfg.cexp) *
        (∑ a, ‖test ν a‖^2) ≤
      ∑ a, sourceOriginalB542FreePrimeProduct434 d J ell m hmJ ν a *
        ‖test ν a‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right
      (source_original_B542_true_BIG_prime_product_lower434 d J ell m hmJ ν hBIG a)
      (sq_nonneg _)
  calc
    _ = sourceOriginalB542FreeCountNormalizer434 d J ell m hmJ ν *
      (Real.exp (((∑ g : G,
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g : ℕ):ℝ) * L^cfg.cexp) *
        (∑ a, ‖test ν a‖^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hSum hV
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualD20ShiftedCofactorExclusion -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The LITERAL ORIGINAL full-cell D20 centered cofactor coefficient
vanishes at n=1. This is derived from original rough-test/proxy support,
not postulated to eliminate the problematic unit divisor. -/
theorem source_original_B488_actual_D20_delta_one_zero434
    (Δ W y : ℝ) (hWy : W ≤ y) :
    sourceD20FullDelta Δ W y 1 = 0 := by
  have hn : ¬ sourceD20Rough W 1 := by
    intro hh
    exact (by norm_num : ¬(2 ≤ (1:ℕ))) hh.1
  have h := sourceD20_delta_support
    (sourceD20LogCell Δ (sourceD20CellIndex Δ 1)) hWy 1 hn
  exact h

/-- On the TRUE original D20 nonzero full-cell cofactor support, a
cofactor cannot divide BOTH the physical integer endpoints z and z+2k
when |2k|≤W, k≠0. This is the actual arithmetic shift-2k gate, not
C191's Fourier phase -kθ. The proof uses the original W-rough property,
actual delta(1)=0, and the strong prime-divisor obstruction. -/
theorem source_original_B488_nonzero_D20_cofactor_cannot_divide_both_shifted434
    (Δ W y : ℝ) (hWy : W ≤ y) (n z : ℕ) (k : ℤ)
    (hDelta : sourceD20FullDelta Δ W y n ≠ 0)
    (hk : k ≠ 0) (hshift : ((2*k).natAbs:ℝ) ≤ W)
    (hpos : 0 < (z:ℤ)+2*k)
    (hnz : n ∣ z)
    (hnshift : n ∣ ((z:ℤ)+2*k).toNat) : False := by
  have hRough : SourceRoughAbove n W :=
    original_D20_full_delta_support_SourceRoughAbove434 Δ W y n hWy hDelta
  have hne : n ≠ 1 := by
    intro he
    subst n
    exact hDelta (source_original_B488_actual_D20_delta_one_zero434 Δ W y hWy)
  obtain ⟨p,hp,hpn⟩ := Nat.exists_prime_and_dvd hne
  have hpz : (p:ℤ) ∣ (z:ℤ) :=
    Int.natCast_dvd_natCast.mpr (hpn.trans hnz)
  have hpzp : (p:ℤ) ∣ (((z:ℤ)+2*k).toNat:ℤ) :=
    Int.natCast_dvd_natCast.mpr (hpn.trans hnshift)
  rw [Int.toNat_of_nonneg hpos.le] at hpzp
  have hpShift : (p:ℤ) ∣ 2*k := by simpa using dvd_sub hpzp hpz
  have hshiftNZ : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have hpAbs : p ≤ (2*k).natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hpShift hshiftNZ
  have hpW : (p:ℝ) ≤ W :=
    (by exact_mod_cast hpAbs : (p:ℝ)≤((2*k).natAbs:ℝ)).trans hshift
  exact (not_le_of_gt (hRough p hp hpn)) hpW


/-- The WHOLE original full D20 logarithmic cell, with no sparse-support
re-centering, has identically zero SAME-cofactor contribution to any true
integer-shifted physical pair (z,z+2k) when |2k|≤W. Every original Δ
coefficient is retained: terms are either identically zero or fail the
simultaneous divisor constraints. The arbitrary factor A_n can be the
complete native Q-only factorial/Mellin/Fourier source cofactor amplitude,
without assuming its bounds or introducing counting losses. -/
theorem source_original_B488_full_D20_shifted_same_cofactor_sum_zero434
    (Δ W y : ℝ) (hWy : W ≤ y) (j z : ℕ) (k : ℤ)
    (hk : k ≠ 0) (hshift : ((2*k).natAbs:ℝ) ≤ W)
    (hpos : 0 < (z:ℤ)+2*k)
    (A : ℕ → ℂ) :
    (∑ n ∈ sourceD20LogCell Δ j,
      if n ∣ z ∧ n ∣ ((z:ℤ)+2*k).toNat then
        (sourceD20FullDelta Δ W y n:ℂ)*A n else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hz : sourceD20FullDelta Δ W y n = 0
  · simp [hz]
  · have hnDiv : ¬(n ∣ z ∧ n ∣ ((z:ℤ)+2*k).toNat) := by
      intro both
      exact source_original_B488_nonzero_D20_cofactor_cannot_divide_both_shifted434
        Δ W y hWy n z k hz hk hshift hpos both.1 both.2
    simp [hnDiv]
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualD20ShiftedCoprimePairs -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64ComparisonPartial Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The ORIGINAL nonzero centered D20 left cofactor m, dividing z, is
coprime to EVERY target cofactor t dividing the physically shifted
endpoint z+2k, for signed k≠0 and |2k|≤W. This holds BEFORE Q/P,
characters, Mellin phases or any averaging, with the exact original
D20 W-rough support; it is the source 4.34.1 counterpart of the native
T rough shifted cofactor coprimality gate. -/
theorem source_original_B489_actual_D20_shifted_cofactor_coprime434
    (Δ W y : ℝ) (hWy : W ≤ y) (m t z : ℕ) (k : ℤ)
    (hDelta : sourceD20FullDelta Δ W y m ≠ 0)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (hpos : 0 < (z:ℤ)+2*k)
    (hmz : m ∣ z) (htz : t ∣ ((z:ℤ)+2*k).toNat) :
    Nat.Coprime m t := by
  have hmRough : SourceRoughAbove m W :=
    original_D20_full_delta_support_SourceRoughAbove434 Δ W y m hWy hDelta
  change Nat.gcd m t = 1
  by_contra hne
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpm : p ∣ m := hpg.trans (Nat.gcd_dvd_left m t)
  have hpt : p ∣ t := hpg.trans (Nat.gcd_dvd_right m t)
  have hpz : (p:ℤ) ∣ (z:ℤ) :=
    Int.natCast_dvd_natCast.mpr (hpm.trans hmz)
  have hpzp : (p:ℤ) ∣ (((z:ℤ)+2*k).toNat:ℤ) :=
    Int.natCast_dvd_natCast.mpr (hpt.trans htz)
  rw [Int.toNat_of_nonneg hpos.le] at hpzp
  have hpShift : (p:ℤ) ∣ 2*k := by simpa using dvd_sub hpzp hpz
  have hshiftNZ : 2*k ≠ 0 := mul_ne_zero (by norm_num) hk
  have hpAbs : p ≤ (2*k).natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hpShift hshiftNZ
  have hpW : (p:ℝ) ≤ W :=
    (by exact_mod_cast hpAbs : (p:ℝ)≤((2*k).natAbs:ℝ)).trans hsmall
  exact (not_le_of_gt (hmRough p hp hpm)) hpW

/-- Exact finite CORRECTED shifted pairing: for all original D20 left
cofactors in the full unshortened cell and all physical right-divisor
cofactors, the coprime selector can be dropped with no loss. If the
original signed coefficient is zero, that term vanishes; otherwise the
physical prime-divisor argument proves coprimality. No character or
Fock/history sector count is spent. -/
theorem source_original_B489_full_D20_shifted_coprime_selector_lossless434
    (Δ W y : ℝ) (hWy : W ≤ y) (j z : ℕ) (k : ℤ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (hpos : 0 < (z:ℤ)+2*k)
    (T : Finset ℕ)
    (hT : ∀ t ∈ T, t ∣ ((z:ℤ)+2*k).toNat)
    (A : ℕ → ℕ → ℂ) :
    (∑ m ∈ (sourceD20LogCell Δ j).filter (fun m => m ∣ z), ∑ t ∈ T,
       if Nat.Coprime m t then
         (sourceD20FullDelta Δ W y m:ℂ)*A m t else 0) =
    (∑ m ∈ (sourceD20LogCell Δ j).filter (fun m => m ∣ z), ∑ t ∈ T,
       (sourceD20FullDelta Δ W y m:ℂ)*A m t) := by
  apply Finset.sum_congr rfl
  intro m hm
  have hmz : m ∣ z := (Finset.mem_filter.mp hm).2
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hdelta : sourceD20FullDelta Δ W y m = 0
  · simp [hdelta]
  · have hco : Nat.Coprime m t :=
      source_original_B489_actual_D20_shifted_cofactor_coprime434
        Δ W y hWy m t z k hdelta hk hsmall hpos
        hmz (hT t ht)
    simp [hco]
end Green64Analytic.CorrelationSquare

end

end

/-! ## NativePrimeSlotCoreIntegrated -/

section

/- Production native Lean4.34.1 integration of the EXACT source T
`SourceActualSingletonCoreDiagnostic434` arithmetic definitions. Every
PrimeSlotCore field and its full m,p-divisor/Q/P/Mellin/residual/fourier
expression is carried literally, with the same names and formula. Only
`roughCutoff` and `rough` are omitted because they are ALREADY provided
by the original source `SourceNativeD61AlphaDefinitions434`, avoiding
the former duplicate-environment import error. This is not a T RMS bound. -/
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Green64Analytic.SourceBlockSieve

noncomputable def shiftTwoGroupOmega (P : Finset ℕ) (u : ℕ) : ℕ :=
  (P.filter (fun p => p ∣ u)).card

noncomputable def sourceOriginalOrdinaryPart (Pall : Finset ℕ)
    (u : ℕ) : ℕ :=
  ∏ p ∈ u.primeFactors \ Pall, p ^ u.factorization p

theorem source_ordinary_part_dvd
    (Pall : Finset ℕ) (u : ℕ) (hu : u ≠ 0) :
    sourceOriginalOrdinaryPart Pall u ∣ u := by
  unfold sourceOriginalOrdinaryPart
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hu]
  exact Finset.prod_dvd_prod_of_subset
    (u.primeFactors \ Pall) u.primeFactors
    (fun p => p ^ u.factorization p) Finset.sdiff_subset

noncomputable def sourceOriginalPParityExponent
    (Pall : Finset ℕ) (u : ℕ) : ℕ :=
  ∑ p ∈ Pall, u.factorization p

end Green64Analytic.SourceBlockSieve
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve

noncomputable def mellin (m : ℕ) (t : ℝ) : ℂ :=
  (m : ℂ) ^ ((-1 : ℂ) + Complex.I * (t : ℂ))

structure CorrelationGroupConstants where
  (a b c d c₀ C₀ vLo vHi q₀ : ℝ)
  ell : ℕ
  habcd : 0 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < 47/100
  hpos : 0 < c₀ ∧ 0 < C₀ ∧ 0 < vLo ∧ 0 < vHi
  hq : 0 < q₀ ∧ q₀ < 1
  hell : 1 ≤ ell

noncomputable def groupHarmonic (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (p : ℝ)⁻¹

noncomputable def sourceMarkedWeight {G : Type} [Fintype G]
    (q : ℝ) (ell : ℕ) (P : G → Finset ℕ) (n : ℕ) : ℝ :=
  ∏ g, q^(shiftTwoGroupOmega (P g) n - ell) *
    ((shiftTwoGroupOmega (P g) n).descFactorial ell : ℝ) /
      (groupHarmonic (P g))^ell

structure PrimeSlotCore where
  (alpha residual : ℕ → ℂ)
  q : ℕ
  character : DirichletCharacter ℂ q
  (sigma₀ sigma₁ : ℝ)
  (lo hi : ℕ)

noncomputable def imaginaryPower (n : ℕ) (t : ℝ) : ℂ :=
  (n : ℂ) ^ (Complex.I * (t : ℂ))

noncomputable def primeSlotCoreValue {G : Type} [Fintype G]
    (P : G → Finset ℕ) (F : PrimeSlotCore) (n : ℕ) : ℂ :=
  let ns := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n
  ∑ m ∈ ns.divisors, ∑ p ∈ (ns/m).divisors,
    if p.Prime ∧ p ∈ Finset.Icc F.lo F.hi then
      F.alpha m * F.character m * imaginaryPower m F.sigma₀ *
        imaginaryPower p F.sigma₁ * F.residual (ns/m/p) else 0

noncomputable def groupSign {G : Type} [Fintype G]
    (P : G → Finset ℕ) (twisted : Bool) (n : ℕ) : ℝ :=
  if twisted then (-1:ℝ)^sourceOriginalPParityExponent
    (Finset.univ.biUnion P) n else 1

noncomputable def sourceCorrelationBaseKernel
    (c : CorrelationGroupConstants)
    (g : ℕ) (P : Fin g → Finset ℕ)
    (F G : PrimeSlotCore) (Z a₁ a₂ : ℝ)
    (k : ℤ) (psi : ℝ → ℂ) (z : ℕ) : ℂ :=
  if 0 < (z : ℤ) + k then
    psi ((z : ℝ)/Z) / (z : ℂ) *
      imaginaryPower z a₁ *
      imaginaryPower (((z : ℤ)+k).toNat) a₂ *
      star (primeSlotCoreValue P F z) *
      primeSlotCoreValue P G (((z : ℤ)+k).toNat) *
      (sourceMarkedWeight c.q₀ c.ell P z *
       sourceMarkedWeight c.q₀ c.ell P (((z : ℤ)+k).toNat) : ℝ)
  else 0

noncomputable def sourceCorrelationTwoTwists
    (c : CorrelationGroupConstants)
    (g : ℕ) (P : Fin g → Finset ℕ)
    (F G : PrimeSlotCore) (tw₁ tw₂ : Bool)
    (Z a₁ a₂ bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ) : ℂ :=
  ∑ z ∈ Finset.Icc 1 ⌊bPsi*Z⌋₊,
    sourceCorrelationBaseKernel c g P F G Z a₁ a₂ k psi z *
      ((groupSign P tw₁ z *
        groupSign P tw₂ (((z : ℤ)+k).toNat)) : ℝ)

noncomputable def sourceCorrelationProjected
    (c : CorrelationGroupConstants)
    (g : ℕ) (P : Fin g → Finset ℕ)
    (F G : PrimeSlotCore)
    (Z a₁ a₂ bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ) : ℂ :=
  ∑ z ∈ Finset.Icc 1 ⌊bPsi*Z⌋₊,
    sourceCorrelationBaseKernel c g P F G Z a₁ a₂ k psi z *
      ((((1-groupSign P true z)/2) *
        ((1-groupSign P true (((z : ℤ)+k).toNat))/2)) : ℝ)


end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## IntegratedPrimeSlotCoreShiftedCoprime -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The exact source T Q/P inner p-divisor sum at one original cofactor m.
Full literal alpha, character, Mellin-0/1 and residual (ns/m/p) factors;
no model surrogate or bound on the remaining inner prime-slot sum. -/
noncomputable def sourceNativePrimeCoreCofactor434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (F : PrimeSlotCore) (z m : ℕ) : ℂ :=
  let ns := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  ∑ p ∈ (ns/m).divisors,
    if p.Prime ∧ p ∈ Finset.Icc F.lo F.hi then
      F.alpha m * F.character m * imaginaryPower m F.sigma₀ *
        imaginaryPower p F.sigma₁ * F.residual (ns/m/p) else 0

/-- Exact original source-native cofactor decomposition of the complete
PrimeSlotCoreValue. This proves the new merged C/T production definition
has the original T m,p-divisor expression without truncating Q/P. -/
theorem source_native_B491_full_QP_core_cofactor_expansion434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (F : PrimeSlotCore) (z : ℕ) :
    primeSlotCoreValue P F z =
    ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      sourceNativePrimeCoreCofactor434 P F z m := by
  rfl

/-- Exact Q/P prime-slot cofactor vanishing when actual left centered
alpha(m) = 0, without any positivity or Fourier conditions. -/
theorem source_native_B491_QP_cofactor_alpha_zero434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (F : PrimeSlotCore) (z m : ℕ) (ha : F.alpha m = 0) :
    sourceNativePrimeCoreCofactor434 P F z m = 0 := by
  simp [sourceNativePrimeCoreCofactor434,ha]

/-- Original T PrimeSlotCore with EXACT ORIGINAL D20 centered alpha,
retaining all character moduli, residuals, two Mellin exponents and
prime-slot Q/P ranges from the source T core. -/
noncomputable def sourceNativeB491ActualD20Core434
    (F : PrimeSlotCore) (Δ W y : ℝ) : PrimeSlotCore :=
  { F with alpha := fun n => (Green64Analytic.SourceBlockSieve.sourceD20FullDelta Δ W y n:ℂ) }


/-- Exact shifted product of the FULL literal native original T Q/P
PrimeSlotCore at z and z+2k, with the ORIGINAL D20 centered left alpha.
At the TRUE physical shift, every non-coprime cofactor pair contributes
identically ZERO; it is legal to insert the coprime selector before ANY
character mean, Mellin/Fourier integral, or parity projector. This keeps
all original p slots, residuals, phases and q-characters, with no
surrogate tests and no cofactor/history counting loss. -/
theorem source_native_B491_actual_D20_shifted_QP_core_coprime_exact434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y)
    (z : ℕ) (k : ℤ) (hz : z ≠ 0)
    (hk : k ≠ 0) (hpos : 0 < (z:ℤ)+2*k)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let FL := sourceNativeB491ActualD20Core434 F Δ W y
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    star (primeSlotCoreValue P FL z) * primeSlotCoreValue P H zR =
    ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
      if Nat.Coprime m t then
        star (sourceNativePrimeCoreCofactor434 P FL z m) *
          sourceNativePrimeCoreCofactor434 P H zR t
      else 0 := by
  dsimp only
  let FL := sourceNativeB491ActualD20Core434 F Δ W y
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  have hzR : zR ≠ 0 := by
    dsimp [zR]
    omega
  have hl : primeSlotCoreValue P FL z =
       ∑ m ∈ nsL.divisors, sourceNativePrimeCoreCofactor434 P FL z m :=
    source_native_B491_full_QP_core_cofactor_expansion434 P FL z
  have hr : primeSlotCoreValue P H zR =
       ∑ t ∈ nsR.divisors, sourceNativePrimeCoreCofactor434 P H zR t :=
    source_native_B491_full_QP_core_cofactor_expansion434 P H zR
  rw [hl,hr,star_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases ha : sourceD20FullDelta Δ W y m = 0
  · have hα : FL.alpha m = 0 := by
      simp [FL,sourceNativeB491ActualD20Core434,ha]
    rw [source_native_B491_QP_cofactor_alpha_zero434 P FL z m hα]
    simp
  · have hmz : m ∣ z :=
      (Nat.mem_divisors.mp hm).1.trans
        (source_ordinary_part_dvd (Finset.univ.biUnion P) z hz)
    have htz : t ∣ zR :=
      (Nat.mem_divisors.mp ht).1.trans
        (source_ordinary_part_dvd (Finset.univ.biUnion P) zR hzR)
    have hc : Nat.Coprime m t :=
      Green64Analytic.CorrelationSquare.source_original_B489_actual_D20_shifted_cofactor_coprime434
        Δ W y hWy m t z k ha hk hsmall hpos hmz htz
    rw [if_pos hc]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## IntegratedPhysicalShiftedProjectedCore -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Exactly the original T physical (+,-,-,+)/4 two-endpoint parity
projected summand at integer shift **2*k**, with the original BIG source
marked weights, two Mellin phases and the full original native PrimeSlotCore.
Its cofactor alpha is the genuine full-cell D20 centered sequence. -/
noncomputable def sourceNativeB492LiteralD20ProjectedSummand434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ) (z : ℕ) : ℂ :=
  let FL := sourceNativeB491ActualD20Core434 F Δ W y
  let zR := ((z:ℤ)+2*k).toNat
  sourceCorrelationBaseKernel c g P FL H Z a1 a2 (2*k) psi z *
    ((((1-groupSign P true z)/2)*
      ((1-groupSign P true zR)/2)) : ℝ)

/-- The *same* literal T projected physical summand, now fully resolved at
original m,t cofactor indices. The only extra selector is exact coprimality,
which is forced by the REAL integer shift 2k when |2k|≤W.
All Q/P prime slots, residuals, source marked weights, Mellin a1/a2,
character moduli and both sign projectors are carried unchanged. -/
noncomputable def sourceNativeB492ProjectedCoprimeTerm434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t : ℕ) : ℂ :=
  let FL := sourceNativeB491ActualD20Core434 F Δ W y
  let zR := ((z:ℤ)+2*k).toNat
  if 0 < (z:ℤ)+2*k then
    if Nat.Coprime m t then
      psi ((z:ℝ)/Z)/(z:ℂ) *
      imaginaryPower z a1 * imaginaryPower zR a2 *
      star (sourceNativePrimeCoreCofactor434 P FL z m) *
      sourceNativePrimeCoreCofactor434 P H zR t *
      (sourceMarkedWeight c.q₀ c.ell P z *
       sourceMarkedWeight c.q₀ c.ell P zR : ℝ) *
      ((((1-groupSign P true z)/2) *
        ((1-groupSign P true zR)/2)) : ℝ)
    else 0
  else 0

/-- Exact physical Q/P source projected expansion into COPRIME original
cofactor pairs for each integer z and signed k, before any sums over
source OLD sectors, characters, φ-normalization, or Fourier integration.
It is a T-native literal physical shift2k identity with actual D20 alpha. -/
theorem source_native_B492_literal_D20_projected_coprime_expansion434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ) (z : ℕ)
    (hz : z ≠ 0) (hk : k ≠ 0)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let zR := ((z:ℤ)+2*k).toNat
    let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
    let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
    sourceNativeB492LiteralD20ProjectedSummand434 c g P F H Δ W y Z a1 a2 k psi z =
      ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
        sourceNativeB492ProjectedCoprimeTerm434 c g P F H Δ W y Z a1 a2 k psi z m t := by
  dsimp only
  let FL := sourceNativeB491ActualD20Core434 F Δ W y
  let zR := ((z:ℤ)+2*k).toNat
  let nsL := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z
  let nsR := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) zR
  by_cases hp : 0 < (z:ℤ)+2*k
  · have hCore := source_native_B491_actual_D20_shifted_QP_core_coprime_exact434
      P F H Δ W y hWy z k hz hk hp hsmall
    change star (primeSlotCoreValue P FL z) * primeSlotCoreValue P H zR =
      ∑ m ∈ nsL.divisors, ∑ t ∈ nsR.divisors,
        if Nat.Coprime m t then
          star (sourceNativePrimeCoreCofactor434 P FL z m) *
            sourceNativePrimeCoreCofactor434 P H zR t else 0 at hCore
    let pref : ℂ := psi ((z:ℝ)/Z)/(z:ℂ) *
      imaginaryPower z a1 * imaginaryPower zR a2
    let w : ℂ := ((sourceMarkedWeight c.q₀ c.ell P z *
       sourceMarkedWeight c.q₀ c.ell P zR : ℝ):ℂ)
    let proj : ℂ := (((1-groupSign P true z)/2) *
      ((1-groupSign P true zR)/2) : ℝ)
    have hPhysical :
      sourceNativeB492LiteralD20ProjectedSummand434 c g P F H Δ W y
          Z a1 a2 k psi z =
      pref * (star (primeSlotCoreValue P FL z) *
              primeSlotCoreValue P H zR) * w * proj := by
      unfold sourceNativeB492LiteralD20ProjectedSummand434
        sourceCorrelationBaseKernel
      simp only [if_pos hp]
      dsimp only [pref,w,proj,zR,FL]
      ring
    rw [hPhysical,hCore]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp only [sourceNativeB492ProjectedCoprimeTerm434,FL,zR]
    rw [if_pos hp]
    by_cases hc : Nat.Coprime m t
    · simp only [if_pos hc]
      dsimp only [pref,w,proj]
      ring
    · simp only [if_neg hc]
      ring
  · simp only [sourceNativeB492LiteralD20ProjectedSummand434,
      sourceNativeB492ProjectedCoprimeTerm434,sourceCorrelationBaseKernel,
      if_neg hp,zero_mul,Finset.sum_const_zero]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## IntegratedFullProjectedShift2k -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The COMPLETE original T native projected physical correlation at
integer shift 2k, integrated in the production original SOURCE03 Lean4.34.1
environment with genuine D20 centered alpha. This is the original finite
z sum, all original Q/P p-slots, residuals, two Mellin exponents, moving
marked prime weights, both parity selectors, and ψ(z/Z). The RHS resolves
every original m,t cofactor and removes exactly the mathematically
forbidden non-coprime pairs BEFORE taking any Fourier or character means.
No approximate amplitude equality or arbitrary sign normalization. -/
theorem source_native_B493_complete_D20_QP_projected_coprime_exact434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let FL := sourceNativeB491ActualD20Core434 F Δ W y
    sourceCorrelationProjected c g P FL H Z a1 a2 bPsi (2*k) psi =
      ∑ z ∈ Finset.Icc 1 ⌊bPsi*Z⌋₊,
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
          (((z:ℤ)+2*k).toNat)).divisors,
          sourceNativeB492ProjectedCoprimeTerm434
            c g P F H Δ W y Z a1 a2 k psi z m t := by
  dsimp only
  unfold sourceCorrelationProjected
  apply Finset.sum_congr rfl
  intro z hz
  have hzpos : 0 < z := (Finset.mem_Icc.mp hz).1
  have hz0 : z ≠ 0 := Nat.ne_of_gt hzpos
  change sourceNativeB492LiteralD20ProjectedSummand434
      c g P F H Δ W y Z a1 a2 k psi z = _
  exact source_native_B492_literal_D20_projected_coprime_expansion434
    c g P F H Δ W y hWy Z a1 a2 k psi z hz0 hk hsmall
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualFourSignProjectedShift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Universal exact original four-sign (+,-,-,+)/4 algebra: the
physical source parity projector is formed BEFORE any absolute value,
character mean or Fourier integration. No averaging error. -/
theorem source_native_B494_complex_four_sign_projector434
    (a : ℂ) (s t : ℝ) :
    a * (((1-s)/2)*((1-t)/2) : ℝ) =
    ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (a * (((if tw.1 then s else 1) *
            (if tw.2 then t else 1)) : ℝ)) := by
  simp [Fintype.sum_prod_type,sourceOriginalB430ParityCoefficient]
  ring


/-- Literal full original T native four-channel identity, with the TRUE
physical integer shift 2k and the original D20 full centered alpha, not
C191's Fourier k-frequency. This is an exact sourceCorrelationProjected
= (ff−tf−ft+tt)/4 identity on ORIGINAL Q/P prime-slot cores, including
marked weights, all Mellin/Fourier factors, and both endpoint parities.
All four endpoint signs are combined before any norm square. -/
theorem source_native_B494_literal_D20_projected_equals_four_channels434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ) :
    let FL := sourceNativeB491ActualD20Core434 F Δ W y
    sourceCorrelationProjected c g P FL H Z a1 a2 bPsi (2*k) psi =
    ∑ tw : Bool × Bool,
      sourceOriginalB430ParityCoefficient tw *
        sourceCorrelationTwoTwists c g P FL H tw.1 tw.2
          Z a1 a2 bPsi (2*k) psi := by
  dsimp only
  let FL := sourceNativeB491ActualD20Core434 F Δ W y
  let S := Finset.Icc 1 ⌊bPsi*Z⌋₊
  let K : ℕ → ℂ := fun z =>
    sourceCorrelationBaseKernel c g P FL H Z a1 a2 (2*k) psi z
  let zR : ℕ → ℕ := fun z => ((z:ℤ)+2*k).toNat
  have hTw (tw : Bool × Bool) (z : ℕ) :
      (if tw.1 then groupSign P true z else 1) *
        (if tw.2 then groupSign P true (zR z) else 1) =
      groupSign P tw.1 z * groupSign P tw.2 (zR z) := by
    rcases tw with ⟨a,b⟩
    cases a <;> cases b <;> rfl
  have hPoint (z : ℕ) :
      K z * (((1-groupSign P true z)/2) *
             ((1-groupSign P true (zR z))/2) : ℝ) =
      ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
        (K z * ((groupSign P tw.1 z * groupSign P tw.2 (zR z)):ℝ)) := by
    calc
      _ = ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
          (K z * (((if tw.1 then groupSign P true z else 1) *
                     (if tw.2 then groupSign P true (zR z) else 1)):ℝ)) :=
          source_native_B494_complex_four_sign_projector434
            (K z) (groupSign P true z) (groupSign P true (zR z))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro tw htw
        rw [hTw tw z]
  change (∑ z ∈ S, K z * (((1-groupSign P true z)/2) *
               ((1-groupSign P true (zR z))/2):ℝ)) =
    ∑ tw : Bool × Bool, sourceOriginalB430ParityCoefficient tw *
      (∑ z ∈ S, K z * ((groupSign P tw.1 z * groupSign P tw.2 (zR z)):ℝ))
  calc
    _ = ∑ z ∈ S, ∑ tw : Bool × Bool,
      sourceOriginalB430ParityCoefficient tw *
        (K z * ((groupSign P tw.1 z * groupSign P tw.2 (zR z)):ℝ)) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hPoint z
    _ = ∑ tw : Bool × Bool, ∑ z ∈ S,
      sourceOriginalB430ParityCoefficient tw *
        (K z * ((groupSign P tw.1 z * groupSign P tw.2 (zR z)):ℝ)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro tw htw
      rw [Finset.mul_sum]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## IntegratedNativeCharacterTwist -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Exactly the original T character field substitution, with all alpha,
Q/P prime bounds, residual, and two Mellin exponents unchanged. -/
noncomputable def sourceNativeWithCharacter434
    (F : PrimeSlotCore) (q : ℕ) (χ : DirichletCharacter ℂ q) : PrimeSlotCore :=
  { F with q := q, character := χ }

/-- Identical original T core with its character factor stripped. -/
noncomputable def sourceNativeWithoutCharacter434 (F : PrimeSlotCore) : PrimeSlotCore :=
  sourceNativeWithCharacter434 F 1 1

/-- A literal source T Q/P m-cofactor amplitude factorizes into
χ(m) times the genuine character-free cofactor amplitude, retaining the
original alpha, p-slot and residual, both Mellin exponents and source P.
NO other physical parameters are changed and no character averaging. -/
theorem source_native_B495_QP_cofactor_character_factor434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (F : PrimeSlotCore) (q : ℕ) (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    sourceNativePrimeCoreCofactor434 P (sourceNativeWithCharacter434 F q χ) z m =
      χ (m : ZMod q) *
        sourceNativePrimeCoreCofactor434 P (sourceNativeWithoutCharacter434 F) z m := by
  have hone : (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 :=
    MulChar.one_apply (by rw [ZMod.isUnit_iff_coprime]; exact Nat.coprime_one_right m)
  dsimp only [sourceNativePrimeCoreCofactor434,sourceNativeWithoutCharacter434,
    sourceNativeWithCharacter434]
  simp only [hone,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> ring

/-- Exact original D20 native core character-twist commutation: replacing
q,χ commutes with replacing alpha by the true sourceD20FullDelta. -/
theorem source_native_B495_D20_alpha_character_commutes434
    (F : PrimeSlotCore) (Δ W y : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) :
    sourceNativeB491ActualD20Core434 (sourceNativeWithCharacter434 F q χ) Δ W y =
    sourceNativeWithCharacter434 (sourceNativeB491ActualD20Core434 F Δ W y) q χ := by
  rfl


/-- Exact genuine Q/P cofactor χ(m) factor for the full source ORIGINAL
D20 centered alpha, with no assumptions on residuals or analytic phases. -/
theorem source_native_B495_D20_QP_cofactor_character_factor434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (F : PrimeSlotCore) (Δ W y : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (z m : ℕ) :
    sourceNativePrimeCoreCofactor434 P
      (sourceNativeB491ActualD20Core434 (sourceNativeWithCharacter434 F q χ) Δ W y)
      z m =
    χ (m : ZMod q) *
      sourceNativePrimeCoreCofactor434 P
        (sourceNativeB491ActualD20Core434 (sourceNativeWithoutCharacter434 F) Δ W y)
        z m := by
  let FD := sourceNativeB491ActualD20Core434 F Δ W y
  have hwithout : sourceNativeB491ActualD20Core434
      (sourceNativeWithoutCharacter434 F) Δ W y =
        sourceNativeWithoutCharacter434 FD := rfl
  rw [source_native_B495_D20_alpha_character_commutes434, hwithout]
  exact source_native_B495_QP_cofactor_character_factor434 P FD q χ z m

/-- Literal physical shift2k original source/native T cofactor term has
EXACT character twist `conj χ(m) * χ(t)` before any averaging, squaring or
position sum, with the original D20 alpha and all Q/P/marked/parity/
Mellin/Fourier factors unchanged. This is NOT a scalar-residual argument. -/
theorem source_native_B495_projected_D20_shifted_cofactor_character_factor434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t : ℕ) :
    sourceNativeB492ProjectedCoprimeTerm434 c g P
      (sourceNativeWithCharacter434 F q χ) (sourceNativeWithCharacter434 H q χ)
      Δ W y Z a1 a2 k psi z m t =
    (star (χ (m : ZMod q))*χ (t : ZMod q)) *
      sourceNativeB492ProjectedCoprimeTerm434 c g P
        (sourceNativeWithoutCharacter434 F) (sourceNativeWithoutCharacter434 H)
        Δ W y Z a1 a2 k psi z m t := by
  by_cases hp : 0 < (z:ℤ)+2*k
  · by_cases hc : Nat.Coprime m t
    · simp only [sourceNativeB492ProjectedCoprimeTerm434,if_pos hp,if_pos hc]
      rw [source_native_B495_D20_QP_cofactor_character_factor434,
          source_native_B495_QP_cofactor_character_factor434,star_mul]
      ring
    · simp [sourceNativeB492ProjectedCoprimeTerm434,hp,hc]
  · simp [sourceNativeB492ProjectedCoprimeTerm434,hp]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## TrueNativeProjectedCharacterCrossGram -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The LITERAL T physical native cofactor character sign, with conjugate
on the source m and ordinary χ on the shifted target t (the opposite
orientation to sourceOriginalB437CofactorPairCharacter434). -/
noncomputable def sourceNativeB496PhysicalPairCharacter434
    (q m t : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  star (χ (m : ZMod q)) * χ (t : ZMod q)

/-- Exact 1/phi(q) REAL post-square character orthogonality for the
native physical source-conjugate orientation. Surviving pairs are
m'*t ≡ t'*m mod q (CROSS RESIDUE ONLY), not integer cofactor equality.
No scalar-sum transfer or premature phase positivity. -/
theorem source_native_B496_physical_cross_character_orthogonality434
    (q : ℕ) (hq : 0 < q) (m t mp tp : ℕ)
    (hu : IsUnit (((mp*t:ℕ) : ZMod q))) (a b : ℂ) :
    (∑ χ : DirichletCharacter ℂ q,
      ‖((q.totient:ℂ)⁻¹)‖ *
        (star (a*sourceNativeB496PhysicalPairCharacter434 q m t χ) *
          (b*sourceNativeB496PhysicalPairCharacter434 q mp tp χ)).re) =
    if (((mp*t:ℕ) : ZMod q) = ((tp*m:ℕ) : ZMod q))
    then (star a*b).re else 0 := by
  have hh := source_original_B437_cross_character_real_average434
    q hq mp tp m t hu (star b) (star a)
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
      ‖((q.totient:ℂ)⁻¹)‖ *
        (star ((star b)*sourceOriginalB437CofactorPairCharacter434 q mp tp χ) *
         ((star a)*sourceOriginalB437CofactorPairCharacter434 q m t χ)).re := by
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [sourceNativeB496PhysicalPairCharacter434,
        sourceOriginalB437CofactorPairCharacter434,
        star_mul,star_star]
      ring
    _ = if (((mp*t:ℕ) : ZMod q) = ((tp*m:ℕ) : ZMod q))
        then (star (star b) * star a).re else 0 := hh
    _ = _ := by
      split_ifs <;> simp only [star_star] <;> congr 1 <;> ring


/-- The ACTUAL original projected T-native Q/P physical cofactor term,
including its shifted integer z+2k endpoint and full D20 alpha, has exact
1/φ(q)-normalized REAL character CROSS Gram: the only surviving condition
is the native cofactor cross congruence mp*t ≡ tp*m mod q. All Q/P prime
slots, residual coefficients, Mellin a1/a2, original BIG marked weights,
physical phases, both sign projector factors and positions z,z' remain
inside the character-free amplitudes. No scalar-average-to-RMS inference. -/
theorem source_native_B496_actual_projected_D20_QP_cofactor_cross_Gram434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (q : ℕ) (hq : 0 < q)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t zp mp tp : ℕ) (hu : IsUnit (((mp*t:ℕ):ZMod q))) :
    let base : ℕ → ℕ → ℕ → ℂ := fun zz mm tt =>
      sourceNativeB492ProjectedCoprimeTerm434 c g P
        (sourceNativeWithoutCharacter434 F) (sourceNativeWithoutCharacter434 H)
        Δ W y Z a1 a2 k psi zz mm tt
    (∑ χ : DirichletCharacter ℂ q,
      ‖((q.totient:ℂ)⁻¹)‖ *
        (star (sourceNativeB492ProjectedCoprimeTerm434 c g P
          (sourceNativeWithCharacter434 F q χ)
          (sourceNativeWithCharacter434 H q χ)
          Δ W y Z a1 a2 k psi z m t) *
         sourceNativeB492ProjectedCoprimeTerm434 c g P
          (sourceNativeWithCharacter434 F q χ)
          (sourceNativeWithCharacter434 H q χ)
          Δ W y Z a1 a2 k psi zp mp tp).re) =
    if (((mp*t:ℕ):ZMod q) = ((tp*m:ℕ):ZMod q)) then
      (star (base z m t)*base zp mp tp).re else 0 := by
  dsimp only
  let base : ℕ → ℕ → ℕ → ℂ := fun zz mm tt =>
    sourceNativeB492ProjectedCoprimeTerm434 c g P
      (sourceNativeWithoutCharacter434 F) (sourceNativeWithoutCharacter434 H)
      Δ W y Z a1 a2 k psi zz mm tt
  have hfactor (χ : DirichletCharacter ℂ q) (zz mm tt : ℕ) :
      sourceNativeB492ProjectedCoprimeTerm434 c g P
        (sourceNativeWithCharacter434 F q χ)
        (sourceNativeWithCharacter434 H q χ)
        Δ W y Z a1 a2 k psi zz mm tt =
      sourceNativeB496PhysicalPairCharacter434 q mm tt χ * base zz mm tt :=
    source_native_B495_projected_D20_shifted_cofactor_character_factor434
      c g P F H Δ W y q χ Z a1 a2 k psi zz mm tt
  have hAvg := source_native_B496_physical_cross_character_orthogonality434
    q hq m t mp tp hu (base z m t) (base zp mp tp)
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
      ‖((q.totient:ℂ)⁻¹)‖ *
      (star (base z m t * sourceNativeB496PhysicalPairCharacter434 q m t χ) *
        (base zp mp tp * sourceNativeB496PhysicalPairCharacter434 q mp tp χ)).re := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hfactor χ z m t,hfactor χ zp mp tp]
      ring
    _ = if (((mp*t:ℕ):ZMod q) = ((tp*m:ℕ):ZMod q)) then
      (star (base z m t)*base zp mp tp).re else 0 := hAvg
    _ = _ := rfl
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualQPCofactorUnitAndRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationD
open Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Original D20 nonzero cofactor support is UNIT modulo every actual
outer-character modulus q with 0<q≤W. Derived from the TRUE source
W-rough cofactor law, not from arbitrary mask transfer. This is the exact
arithmetic hypothesis needed to apply original T post-square character
orthogonality at q=|k|. -/
theorem source_native_B497_actual_D20_nonzero_unit_mod_q434
    (Δ W y : ℝ) (hWy : W ≤ y) (n : ℕ)
    (hn : Green64Analytic.SourceBlockSieve.sourceD20FullDelta Δ W y n ≠ 0)
    (q : ℕ) (hq : 0 < q) (hqW : (q:ℝ) ≤ W) :
    IsUnit (n : ZMod q) := by
  have hRough : SourceRoughAbove n W :=
    original_D20_full_delta_support_SourceRoughAbove434 Δ W y n hWy hn
  rw [ZMod.isUnit_iff_coprime]
  change Nat.gcd n q = 1
  by_contra hne
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left n q)
  have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_right n q)
  have hpW : (p:ℝ) ≤ W :=
    (by exact_mod_cast Nat.le_of_dvd hq hpq : (p:ℝ) ≤ q).trans hqW
  exact (not_le_of_gt (hRough p hp hpn)) hpW

/-- For the TRUE modulus |k|, the cross-product of two original nonzero
D20 cofactors is a unit. Both labels remain the actual shifted physical
cofactor labels (m' from the source, t from the target). -/
theorem source_native_B497_true_shift_q_cross_cofactor_isUnit434
    (Δ W y : ℝ) (hWy : W ≤ y)
    (k : ℤ) (hk : k ≠ 0) (hqW : ((k.natAbs:ℕ):ℝ) ≤ W)
    (mp t : ℕ)
    (hmp : Green64Analytic.SourceBlockSieve.sourceD20FullDelta Δ W y mp ≠ 0)
    (ht : Green64Analytic.SourceBlockSieve.sourceD20FullDelta Δ W y t ≠ 0) :
    IsUnit (((mp*t:ℕ):ZMod k.natAbs)) := by
  have hq : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  have hu1 := source_native_B497_actual_D20_nonzero_unit_mod_q434
    Δ W y hWy mp hmp k.natAbs hq hqW
  have hu2 := source_native_B497_actual_D20_nonzero_unit_mod_q434
    Δ W y hWy t ht k.natAbs hq hqW
  rw [Nat.cast_mul]
  exact hu1.mul hu2


/-- The ACTUAL physical integer-shift-2k original T-native Q/P
post-Cauchy REAL character cross Gram at TRUE original modulus |k|.
Both source and target cofactor alpha fields are the ORIGINAL centered
D20 sequence, and the unit hypothesis is now DISCHARGED arithmetically
from the literal nonzero Δ(mp),Δ(t) and rough cutoff |k|≤W.
The RHS preserves all original Q/P/physical position/marked/Fourier
factors and survives iff `mp*t = tp*m (mod |k|)`, not integer equality.
No scalar cancellation is used to bound the character RMS. -/
theorem source_native_B497_true_modulus_D20_QP_projected_cross_Gram434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hqW : ((k.natAbs:ℕ):ℝ) ≤ W)
    (z m t zp mp tp : ℕ)
    (hmp : Green64Analytic.SourceBlockSieve.sourceD20FullDelta Δ W y mp ≠ 0)
    (ht : Green64Analytic.SourceBlockSieve.sourceD20FullDelta Δ W y t ≠ 0) :
    let HR := sourceNativeB491ActualD20Core434 H Δ W y
    let base : ℕ → ℕ → ℕ → ℂ := fun zz mm tt =>
      sourceNativeB492ProjectedCoprimeTerm434 c g P
        (sourceNativeWithoutCharacter434 F) (sourceNativeWithoutCharacter434 HR)
        Δ W y Z a1 a2 k psi zz mm tt
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        (star (sourceNativeB492ProjectedCoprimeTerm434 c g P
          (sourceNativeWithCharacter434 F k.natAbs χ)
          (sourceNativeWithCharacter434 HR k.natAbs χ)
          Δ W y Z a1 a2 k psi z m t) *
         sourceNativeB492ProjectedCoprimeTerm434 c g P
          (sourceNativeWithCharacter434 F k.natAbs χ)
          (sourceNativeWithCharacter434 HR k.natAbs χ)
          Δ W y Z a1 a2 k psi zp mp tp).re) =
    if (((mp*t:ℕ):ZMod k.natAbs) = ((tp*m:ℕ):ZMod k.natAbs)) then
      (star (base z m t)*base zp mp tp).re else 0 := by
  dsimp only
  let HR := sourceNativeB491ActualD20Core434 H Δ W y
  have hu := source_native_B497_true_shift_q_cross_cofactor_isUnit434
    Δ W y hWy k hk hqW mp t hmp ht
  exact source_native_B496_actual_projected_D20_QP_cofactor_cross_Gram434
    c g P F HR Δ W y k.natAbs (Int.natAbs_pos.mpr hk)
    Z a1 a2 k psi z m t zp mp tp hu
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## NativeModulusTwoNoCharacterGain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationD
open Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Genuine ORIGINAL D20 nonzero full-cell coefficient (at ANY index)
is odd as soon as the true W rough floor is at least two. No re-centering
on cofactor support and no false use of parity symmetry alone. -/
theorem source_native_B498_original_nonzero_D20_cofactor_odd434
    (Δ W y : ℝ) (hWy : W ≤ y) (hW : 2 ≤ W)
    (n : ℕ) (hn : sourceD20FullDelta Δ W y n ≠ 0) : Odd n := by
  have hRough : SourceRoughAbove n W :=
    original_D20_full_delta_support_SourceRoughAbove434 Δ W y n hWy hn
  rcases Nat.even_or_odd n with he | ho
  · have h2 : 2 ∣ n := even_iff_two_dvd.mp he
    exact False.elim ((not_lt_of_ge hW) (hRough 2 Nat.prime_two h2))
  · exact ho

/-- Every Dirichlet character modulo |k|=2 equals one on the true
nonzero original D20 cofactor support: χ(n mod2)=1 for odd n. -/
theorem source_native_B498_nonzero_D20_character_mod2_one434
    (Δ W y : ℝ) (hWy : W ≤ y) (hW : 2 ≤ W)
    (n : ℕ) (hn : sourceD20FullDelta Δ W y n ≠ 0)
    (χ : DirichletCharacter ℂ 2) :
    χ (n : ZMod 2) = 1 := by
  have ho := source_native_B498_original_nonzero_D20_cofactor_odd434
    Δ W y hWy hW n hn
  have hmod : (n : ZMod 2) = 1 := by
    rcases ho with ⟨r,hr⟩
    rw [hr]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp only [h2,zero_mul,zero_add]
  rw [hmod]
  exact map_one χ

/-- The *complete original T Q/P cofactor* at modulus two is independent
of χ once its alpha is the genuine D20 centered sequence and W≥2.
There is no hidden smoothing or replacement of its residual/Mellin/Q/P
prime-slot factors. If alpha is zero, the entire term is exactly zero. -/
theorem source_native_B498_true_D20_QP_cofactor_character_mod2_trivial434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (F : PrimeSlotCore) (Δ W y : ℝ)
    (hWy : W ≤ y) (hW : 2 ≤ W)
    (χ : DirichletCharacter ℂ 2) (z m : ℕ) :
    sourceNativePrimeCoreCofactor434 P
      (sourceNativeB491ActualD20Core434
        (sourceNativeWithCharacter434 F 2 χ) Δ W y) z m =
    sourceNativePrimeCoreCofactor434 P
      (sourceNativeB491ActualD20Core434
        (sourceNativeWithoutCharacter434 F) Δ W y) z m := by
  let F0 := sourceNativeB491ActualD20Core434
    (sourceNativeWithoutCharacter434 F) Δ W y
  have hFactor := source_native_B495_D20_QP_cofactor_character_factor434
    P F Δ W y 2 χ z m
  by_cases hZero : sourceD20FullDelta Δ W y m = 0
  · have hA : F0.alpha m = 0 := by
      simp [F0,sourceNativeB491ActualD20Core434,hZero]
    have hCof := source_native_B491_QP_cofactor_alpha_zero434 P F0 z m hA
    rw [hFactor,hCof]
    simp
  · have hc := source_native_B498_nonzero_D20_character_mod2_one434
      Δ W y hWy hW m hZero χ
    rw [hFactor,hc,one_mul]


/-- At the TRUE native q=2 principal-character sector, the entire
original two-sided D20 Q/P physical shift2k cofactor contribution is
independent of χ, keeping both source and target centered alpha and
all original residuals, Mellin phases, z-position/marked weights and
four-sign projector. No assumption that the amplitude is small. -/
theorem source_native_B498_true_D20_both_endpoints_projected_cofactor_mod2_trivial434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y) (hW : 2 ≤ W)
    (χ : DirichletCharacter ℂ 2)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ) (z m t : ℕ) :
    let HR := sourceNativeB491ActualD20Core434 H Δ W y
    sourceNativeB492ProjectedCoprimeTerm434 c g P
      (sourceNativeWithCharacter434 F 2 χ)
      (sourceNativeWithCharacter434 HR 2 χ)
      Δ W y Z a1 a2 k psi z m t =
    sourceNativeB492ProjectedCoprimeTerm434 c g P
      (sourceNativeWithoutCharacter434 F)
      (sourceNativeWithoutCharacter434 HR)
      Δ W y Z a1 a2 k psi z m t := by
  dsimp only
  let HR := sourceNativeB491ActualD20Core434 H Δ W y
  let FL := sourceNativeB491ActualD20Core434 F Δ W y
  have hs := source_native_B498_true_D20_QP_cofactor_character_mod2_trivial434
    P F Δ W y hWy hW χ z m
  have ht := source_native_B498_true_D20_QP_cofactor_character_mod2_trivial434
    P H Δ W y hWy hW χ ((z:ℤ)+2*k).toNat t
  change sourceNativePrimeCoreCofactor434 P
     (sourceNativeWithCharacter434 HR 2 χ) ((z:ℤ)+2*k).toNat t =
    sourceNativePrimeCoreCofactor434 P
     (sourceNativeWithoutCharacter434 HR) ((z:ℤ)+2*k).toNat t at ht
  by_cases hp : 0 < (z:ℤ)+2*k
  · by_cases hc : Nat.Coprime m t
    · simp only [sourceNativeB492ProjectedCoprimeTerm434,if_pos hp,if_pos hc]
      rw [hs,ht]
    · simp [sourceNativeB492ProjectedCoprimeTerm434,hp,hc]
  · simp [sourceNativeB492ProjectedCoprimeTerm434,hp]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FiniteNativePhysicalCharacterRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Exact post-square character RMS for ANY finite family of the ORIGINAL
T physical cofactor characters χ̄(m)χ(t). No diagonal restriction,
scalar averaging, or sign-positivity shortcut. The only survivors satisfy
m_j*t_i ≡ t_j*m_i modulo q, with the real cross Gram coefficient intact. -/
theorem source_native_B501_finite_physical_character_RMS_residue_only434
    {I : Type} (S : Finset I) (q : ℕ) (hq : 0 < q)
    (m t : I → ℕ) (a : I → ℂ)
    (hunit : ∀ i ∈ S, ∀ j ∈ S,
      IsUnit (((m j)*(t i):ℕ) : ZMod q)) :
    (∑ χ : DirichletCharacter ℂ q,
      ‖((q.totient:ℂ)⁻¹)‖ *
        ‖∑ i ∈ S,
          a i * sourceNativeB496PhysicalPairCharacter434 q (m i) (t i) χ‖^2) =
    (∑ i ∈ S, ∑ j ∈ S,
      if (((m j)*(t i):ℕ) : ZMod q) =
         (((t j)*(m i):ℕ) : ZMod q)
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
  exact source_native_B496_physical_cross_character_orthogonality434
    q hq (m i) (t i) (m j) (t j) (hunit i hi j hj) (a i) (a j)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualNativePhysicalTripleSupport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- ORIGINAL physical T finite three-index (z,m,t) cofactor domain,
with both divisor lists depending on the genuine position z and integer
physical shift 2k. Sigma prevents any replacement by a fictitious
rectangular cofactor box, preserving true Q/P geometry. -/
noncomputable def sourceNativeB502FullPhysicalTriples434
    (g : ℕ) (P : Fin g → Finset ℕ)
    (Z bPsi : ℝ) (k : ℤ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 ⌊bPsi*Z⌋₊).sigma (fun z =>
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors.product
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
      (((z:ℤ)+2*k).toNat)).divisors)

/-- Restricted ORIGINAL T physical triples where BOTH centered D20
cofactor coefficients are genuinely nonzero. No re-centering or sample
proxy. Outside this domain the literal full Q/P term is ZERO. -/
noncomputable def sourceNativeB502ActiveD20PhysicalTriples434
    (g : ℕ) (P : Fin g → Finset ℕ) (Z bPsi : ℝ)
    (k : ℤ) (Δ W y : ℝ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (sourceNativeB502FullPhysicalTriples434 g P Z bPsi k).filter
    (fun s => sourceD20FullDelta Δ W y s.2.1 ≠ 0 ∧
              sourceD20FullDelta Δ W y s.2.2 ≠ 0)

/-- Literal original Q/P physical term is exactly zero when the LEFT
centered D20 cofactor coefficient is zero, even before taking the
character, physical projector, or position sum. -/
theorem source_native_B502_QP_physical_term_zero_left434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t : ℕ) (hd : sourceD20FullDelta Δ W y m = 0) :
    sourceNativeB492ProjectedCoprimeTerm434 c g P F H
      Δ W y Z a1 a2 k psi z m t = 0 := by
  let FL := sourceNativeB491ActualD20Core434 F Δ W y
  have ha : FL.alpha m = 0 := by
    simp [FL,sourceNativeB491ActualD20Core434,hd]
  have hcore := source_native_B491_QP_cofactor_alpha_zero434 P FL z m ha
  by_cases hp : 0 < (z:ℤ)+2*k
  · by_cases hc : Nat.Coprime m t
    · simp only [sourceNativeB492ProjectedCoprimeTerm434,if_pos hp,if_pos hc]
      rw [hcore]
      simp
    · simp [sourceNativeB492ProjectedCoprimeTerm434,hp,hc]
  · simp [sourceNativeB492ProjectedCoprimeTerm434,hp]

/-- Literal original Q/P physical term also vanishes for the RIGHT
centered D20 alpha, when the right PrimeSlotCore has that actual alpha.
All residual and Mellin factors are retained. -/
theorem source_native_B502_QP_physical_term_zero_right434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (hH : ∀ n, H.alpha n = (sourceD20FullDelta Δ W y n:ℂ))
    (Z a1 a2 : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (z m t : ℕ) (hd : sourceD20FullDelta Δ W y t = 0) :
    sourceNativeB492ProjectedCoprimeTerm434 c g P F H
      Δ W y Z a1 a2 k psi z m t = 0 := by
  have ha : H.alpha t = 0 := by rw [hH t,hd]; norm_num
  have hcore := source_native_B491_QP_cofactor_alpha_zero434 P H
    (((z:ℤ)+2*k).toNat) t ha
  by_cases hp : 0 < (z:ℤ)+2*k
  · by_cases hc : Nat.Coprime m t
    · simp only [sourceNativeB492ProjectedCoprimeTerm434,if_pos hp,if_pos hc]
      rw [hcore]
      simp
    · simp [sourceNativeB492ProjectedCoprimeTerm434,hp,hc]
  · simp [sourceNativeB492ProjectedCoprimeTerm434,hp]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FullNativeProjectedPhysicalTripleEquality -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The entire ORIGINAL native projected physical correlation at integer
shift 2k, with both alpha fields equal to literal D20 centered coefficients
and BOTH Dirichlet characters equal to χ, is EXACTLY a finite sum over the
TRUE position-dependent (z,m,t) cofactor triples having nonzero original
Delta on BOTH endpoints. Nothing is re-centered or thrown away: all excluded
terms vanish by the literal Q/P alpha factor. This has the correct
original source marked weights, residuals, p slots, Mellin, ψ and four signs.
The equality holds prior to any character average or norm square. -/
theorem source_native_B503_full_projected_D20_triple_support_exact434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (q : ℕ) (χ : DirichletCharacter ℂ q) :
    let HR := sourceNativeB491ActualD20Core434 H Δ W y
    let FLχ := sourceNativeWithCharacter434 F q χ
    let HRχ := sourceNativeWithCharacter434 HR q χ
    let S := sourceNativeB502ActiveD20PhysicalTriples434 g P Z bPsi k Δ W y
    sourceCorrelationProjected c g P
      (sourceNativeB491ActualD20Core434 FLχ Δ W y) HRχ
      Z a1 a2 bPsi (2*k) psi =
    ∑ s ∈ S,
      sourceNativeB492ProjectedCoprimeTerm434 c g P FLχ HRχ
        Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2 := by
  dsimp only
  let HR := sourceNativeB491ActualD20Core434 H Δ W y
  let FLχ := sourceNativeWithCharacter434 F q χ
  let HRχ := sourceNativeWithCharacter434 HR q χ
  let Zset := Finset.Icc 1 ⌊bPsi*Z⌋₊
  let D : ℕ → Finset (ℕ×ℕ) := fun z =>
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors.product
    (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
       (((z:ℤ)+2*k).toNat)).divisors
  let Sfull : Finset (Σ _ : ℕ, ℕ×ℕ) := Zset.sigma D
  let S : Finset (Σ _ : ℕ, ℕ×ℕ) := Sfull.filter (fun s =>
    sourceD20FullDelta Δ W y s.2.1 ≠ 0 ∧ sourceD20FullDelta Δ W y s.2.2 ≠ 0)
  let B : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB492ProjectedCoprimeTerm434 c g P FLχ HRχ
      Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2
  have hBase := source_native_B493_complete_D20_QP_projected_coprime_exact434
    c g P FLχ HRχ Δ W y hWy Z a1 a2 bPsi k psi hk hsmall
  have hSigma : (∑ z ∈ Zset, ∑ v ∈ D z, B ⟨z,v⟩) =
      ∑ s ∈ Sfull, B s :=
    (Finset.sum_sigma Zset D B).symm
  have hHR : ∀ n, HRχ.alpha n = (sourceD20FullDelta Δ W y n:ℂ) := by
    intro n
    rfl
  have hZero (s : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ Sfull) (hsnot : s ∉ S) :
      B s = 0 := by
    have hfalse : ¬ (sourceD20FullDelta Δ W y s.2.1 ≠ 0 ∧
        sourceD20FullDelta Δ W y s.2.2 ≠ 0) := by
      intro hnonzero
      exact hsnot (Finset.mem_filter.mpr ⟨hs,hnonzero⟩)
    by_cases hm : sourceD20FullDelta Δ W y s.2.1 = 0
    · exact source_native_B502_QP_physical_term_zero_left434
        c g P FLχ HRχ Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2 hm
    · have ht : sourceD20FullDelta Δ W y s.2.2 = 0 := by
        by_contra hnonzero
        exact hfalse ⟨hm,hnonzero⟩
      exact source_native_B502_QP_physical_term_zero_right434
        c g P FLχ HRχ Δ W y hHR Z a1 a2 k psi s.1 s.2.1 s.2.2 ht
  have hFilter : (∑ s ∈ S, B s) = ∑ s ∈ Sfull, B s :=
    Finset.sum_subset (Finset.filter_subset _ _) hZero
  change sourceCorrelationProjected c g P
    (sourceNativeB491ActualD20Core434 FLχ Δ W y) HRχ
    Z a1 a2 bPsi (2*k) psi = ∑ s ∈ S, B s
  calc
    _ = ∑ z ∈ Zset,
      ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
      ∑ t ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
        (((z:ℤ)+2*k).toNat)).divisors,
        B ⟨z,(m,t)⟩ := hBase
    _ = ∑ z ∈ Zset, ∑ v ∈ D z, B ⟨z,v⟩ := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (Finset.sum_product
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P)
          (((z:ℤ)+2*k).toNat)).divisors
        (fun v : ℕ×ℕ => B ⟨z,v⟩)).symm
    _ = ∑ s ∈ Sfull, B s := hSigma
    _ = ∑ s ∈ S, B s := hFilter.symm
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FullNativeShiftedPhysicalCharacterRMS -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The COMPLETE actual physical T source Q/P position sum at integer
shift 2k, original centered D20 alpha on BOTH endpoints, distinct native
m/p prime-slot/mellin/residual factors, marked weights and the FOUR-SIGN
projector, has normalized post-square character RMS EQUAL to the exact
residue-only CROSS Gram over its actual dependent (z,m,t) cofactor triples.
The character is moved out BEFORE squaring, and every surviving cross
condition is m_j*t_i ≡ t_j*m_i mod |k|, not an equality of cofactor pairs.
Both source and target cofactor support are the true unshortened D20
nonzero coefficients. No scalar signed C191 estimate is used; no decay
is asserted for the final signed Gram. -/
theorem source_native_B504_complete_QP_shifted_projected_character_RMS434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (hqW : ((k.natAbs:ℕ):ℝ) ≤ W) :
    let HR := sourceNativeB491ActualD20Core434 H Δ W y
    let S := sourceNativeB502ActiveD20PhysicalTriples434 g P Z bPsi k Δ W y
    let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
      sourceNativeB492ProjectedCoprimeTerm434 c g P
        (sourceNativeWithoutCharacter434 F)
        (sourceNativeWithoutCharacter434 HR)
        Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceCorrelationProjected c g P
          (sourceNativeB491ActualD20Core434
            (sourceNativeWithCharacter434 F k.natAbs χ) Δ W y)
          (sourceNativeWithCharacter434 HR k.natAbs χ)
          Z a1 a2 bPsi (2*k) psi‖^2) =
    ∑ s ∈ S, ∑ v ∈ S,
      if (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
          ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) then
        (star (base s)*base v).re else 0 := by
  dsimp only
  let HR := sourceNativeB491ActualD20Core434 H Δ W y
  let S := sourceNativeB502ActiveD20PhysicalTriples434 g P Z bPsi k Δ W y
  let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB492ProjectedCoprimeTerm434 c g P
      (sourceNativeWithoutCharacter434 F)
      (sourceNativeWithoutCharacter434 HR)
      Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2
  have hunit : ∀ s ∈ S, ∀ v ∈ S,
      IsUnit (((v.2.1)*(s.2.2):ℕ):ZMod k.natAbs) := by
    intro s hs v hv
    have hs2 := (Finset.mem_filter.mp hs).2.2
    have hv1 := (Finset.mem_filter.mp hv).2.1
    exact source_native_B497_true_shift_q_cross_cofactor_isUnit434
      Δ W y hWy k hk hqW v.2.1 s.2.2 hv1 hs2
  have hFactor (χ : DirichletCharacter ℂ k.natAbs)
      (s : Σ _ : ℕ, ℕ×ℕ) :
      sourceNativeB492ProjectedCoprimeTerm434 c g P
        (sourceNativeWithCharacter434 F k.natAbs χ)
        (sourceNativeWithCharacter434 HR k.natAbs χ)
        Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2 =
      base s * sourceNativeB496PhysicalPairCharacter434 k.natAbs
        s.2.1 s.2.2 χ := by
    calc
      _ = (star (χ (s.2.1 : ZMod k.natAbs)) *
          χ (s.2.2 : ZMod k.natAbs)) * base s :=
        source_native_B495_projected_D20_shifted_cofactor_character_factor434
          c g P F HR Δ W y k.natAbs χ Z a1 a2 k psi s.1 s.2.1 s.2.2
      _ = _ := by
        unfold sourceNativeB496PhysicalPairCharacter434
        ring
  have hWhole (χ : DirichletCharacter ℂ k.natAbs) :
      sourceCorrelationProjected c g P
        (sourceNativeB491ActualD20Core434
          (sourceNativeWithCharacter434 F k.natAbs χ) Δ W y)
        (sourceNativeWithCharacter434 HR k.natAbs χ)
        Z a1 a2 bPsi (2*k) psi =
      ∑ s ∈ S, base s * sourceNativeB496PhysicalPairCharacter434
        k.natAbs s.2.1 s.2.2 χ := by
    calc
      _ = ∑ s ∈ S,
        sourceNativeB492ProjectedCoprimeTerm434 c g P
          (sourceNativeWithCharacter434 F k.natAbs χ)
          (sourceNativeWithCharacter434 HR k.natAbs χ)
          Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2 :=
        source_native_B503_full_projected_D20_triple_support_exact434
          c g P F H Δ W y hWy Z a1 a2 bPsi k psi hk hsmall
          k.natAbs χ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hFactor χ s
  have hRMS := source_native_B501_finite_physical_character_RMS_residue_only434
    S k.natAbs (Int.natAbs_pos.mpr hk)
    (fun s => s.2.1) (fun s => s.2.2) base hunit
  calc
    _ = ∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖∑ s ∈ S,
          base s * sourceNativeB496PhysicalPairCharacter434
            k.natAbs s.2.1 s.2.2 χ‖^2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hWhole χ]
    _ = _ := hRMS
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FullNativeModulusTwoNoGain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- For the TRUE original physical T projection at the integer shift 2k
and q=|k|=2, with BOTH alpha sequences equal to the original unshortened
D20 centered cofactor, ALL original z positions and the genuine full
Q/P prime-slot, residual, two Mellin, source BIG marked, and four-sign
projector factors are exactly independent of the Dirichlet character χ.
This is the full physical native corollary of B498, not a scalar C191
proxy or an unproved Fourier identification. No amplitude smallness claim. -/
theorem source_native_B499_actual_full_D20_QP_mod2_character_independence434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (hWy : W ≤ y) (hW : 2 ≤ W)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hk2 : k.natAbs = 2)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (χ : DirichletCharacter ℂ 2) :
    let HR := sourceNativeB491ActualD20Core434 H Δ W y
    sourceCorrelationProjected c g P
      (sourceNativeB491ActualD20Core434
        (sourceNativeWithCharacter434 F 2 χ) Δ W y)
      (sourceNativeWithCharacter434 HR 2 χ)
      Z a1 a2 bPsi (2*k) psi =
    sourceCorrelationProjected c g P
      (sourceNativeB491ActualD20Core434
        (sourceNativeWithoutCharacter434 F) Δ W y)
      (sourceNativeWithoutCharacter434 HR)
      Z a1 a2 bPsi (2*k) psi := by
  dsimp only
  let HR := sourceNativeB491ActualD20Core434 H Δ W y
  have hL := source_native_B493_complete_D20_QP_projected_coprime_exact434
    c g P (sourceNativeWithCharacter434 F 2 χ)
      (sourceNativeWithCharacter434 HR 2 χ)
    Δ W y hWy Z a1 a2 bPsi k psi hk hsmall
  have hR := source_native_B493_complete_D20_QP_projected_coprime_exact434
    c g P (sourceNativeWithoutCharacter434 F)
      (sourceNativeWithoutCharacter434 HR)
    Δ W y hWy Z a1 a2 bPsi k psi hk hsmall
  rw [hL,hR]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro t ht
  exact source_native_B498_true_D20_both_endpoints_projected_cofactor_mod2_trivial434
    c g P F H Δ W y hWy hW χ Z a1 a2 k psi z m t
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualNativeQTwoCharacterRMSNoGain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- On the TRUE native T full Q/P/position/four-sign projected physical
correlation at signed k=±2 (thus original q=|k|=2), both original D20
centered cofactor sequences are odd on nonzero support. The COMPLETE
normalized character RMS equals the complex squared norm of the entire
coherent character-free physical correlation, WITHOUT ANY character gain.
Every original source/target p-slot, residual, Mellin, marked source
weight, physical shift2k and z-position sum is included literally.
This is an EXACT obstruction to character averaging alone; it does NOT
assert signed arithmetic amplitude is nonzero or too large. -/
theorem source_native_B500_actual_full_QP_projected_mod2_character_RMS_no_gain434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ)
    (hWy : W ≤ y) (hW : 2 ≤ W)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hk2 : k.natAbs = 2)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W) :
    let HR := sourceNativeB491ActualD20Core434 H Δ W y
    let x0 := sourceCorrelationProjected c g P
      (sourceNativeB491ActualD20Core434
        (sourceNativeWithoutCharacter434 F) Δ W y)
      (sourceNativeWithoutCharacter434 HR)
      Z a1 a2 bPsi (2*k) psi
    (∑ χ : DirichletCharacter ℂ 2,
      ‖(((2:ℕ).totient:ℂ)⁻¹)‖ *
      ‖sourceCorrelationProjected c g P
        (sourceNativeB491ActualD20Core434
          (sourceNativeWithCharacter434 F 2 χ) Δ W y)
        (sourceNativeWithCharacter434 HR 2 χ)
        Z a1 a2 bPsi (2*k) psi‖^2) = ‖x0‖^2 := by
  dsimp only
  let HR := sourceNativeB491ActualD20Core434 H Δ W y
  let x0 := sourceCorrelationProjected c g P
    (sourceNativeB491ActualD20Core434
      (sourceNativeWithoutCharacter434 F) Δ W y)
    (sourceNativeWithoutCharacter434 HR)
    Z a1 a2 bPsi (2*k) psi
  have hIndep (χ : DirichletCharacter ℂ 2) :
      sourceCorrelationProjected c g P
        (sourceNativeB491ActualD20Core434
          (sourceNativeWithCharacter434 F 2 χ) Δ W y)
        (sourceNativeWithCharacter434 HR 2 χ)
        Z a1 a2 bPsi (2*k) psi = x0 := by
    exact source_native_B499_actual_full_D20_QP_mod2_character_independence434
      c g P F H Δ W y hWy hW Z a1 a2 bPsi k psi hk hk2 hsmall χ
  have hMass : (∑ _χ : DirichletCharacter ℂ 2,
      ‖(((2:ℕ).totient:ℂ)⁻¹)‖) = 1 := by
    have hh := source_original_B430_character_probability_mass434 (2:ℤ) (by norm_num)
    norm_num at hh ⊢
    exact_mod_cast hh
  calc
    _ = ∑ χ : DirichletCharacter ℂ 2,
      ‖(((2:ℕ).totient:ℂ)⁻¹)‖ * ‖x0‖^2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hIndep χ]
    _ = (∑ _χ : DirichletCharacter ℂ 2,
      ‖(((2:ℕ).totient:ℂ)⁻¹)‖) * ‖x0‖^2 := by
      rw [Finset.sum_mul]
    _ = ‖x0‖^2 := by rw [hMass,one_mul]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## CofactorRatioResidueEquivalence -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Crucial equality of TRUE cofactor cross-products modulo any, possibly
COMPOSITE, Dirichlet modulus q with equality of the two cofactor RATIOS.
Only the two source cofactor residues must be units; there is no field
assumption or illegal cancellation in ZMod q. -/
theorem source_native_B505_cross_congruence_iff_unit_ratio434
    (q : ℕ) (u v n t : ZMod q)
    (hu : IsUnit u) (hv : IsUnit v) :
    v*n = t*u ↔ n*u⁻¹ = t*v⁻¹ := by
  constructor
  · intro h
    have hu0 : u*u⁻¹ = 1 := ZMod.mul_inv_of_unit u hu
    have hv0 : v*v⁻¹ = 1 := ZMod.mul_inv_of_unit v hv
    calc
      n*u⁻¹ = (v*n)*(v⁻¹*u⁻¹) := by rw [mul_mul_mul_comm,hv0]; ring
      _ = (t*u)*(v⁻¹*u⁻¹) := by rw [h]
      _ = t*v⁻¹ := by rw [mul_mul_mul_comm,hu0]; ring
  · intro h
    have hu1 : u⁻¹*u = 1 := ZMod.inv_mul_of_unit u hu
    have hv1 : v⁻¹*v = 1 := ZMod.inv_mul_of_unit v hv
    calc
      v*n = (n*u⁻¹)*(v*u) := by
        calc
          v*n = n*v*1 := by ring
          _ = n*v*(u⁻¹*u) := by rw [hu1]
          _ = (n*u⁻¹)*(v*u) := by ring
      _ = (t*v⁻¹)*(v*u) := by rw [h]
      _ = t*u := by
        calc
          (t*v⁻¹)*(v*u) = (t*u)*(v⁻¹*v) := by ring
          _ = t*u := by rw [hv1]; ring

/-- The ORIGINAL T normalized physical character cross-residue condition
is exactly equality of target/source cofactor ratios, assuming both
original source cofactors are actual units mod q. -/
theorem source_native_B505_original_QP_cross_residue_iff_ratio434
    (q m t mp tp : ℕ)
    (hm : IsUnit (m : ZMod q)) (hmp : IsUnit (mp : ZMod q)) :
    (((mp*t:ℕ):ZMod q) = ((tp*m:ℕ):ZMod q)) ↔
      ((t:ZMod q)*(m:ZMod q)⁻¹) =
      ((tp:ZMod q)*(mp:ZMod q)⁻¹) := by
  simpa only [Nat.cast_mul] using
    (source_native_B505_cross_congruence_iff_unit_ratio434
      q (m:ZMod q) (mp:ZMod q) (t:ZMod q) (tp:ZMod q) hm hmp)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## PhysicalCofactorRatioFiberEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Finite signed cross-Gram with a true equivalence-class label rho equals
SUM OF NONNEGATIVE SQUARES of the COHERENT within-label amplitudes.
This is an exact decomposition, not a triangle inequality or a claimed
new saving. Every original complex cofactor phase is retained inside
its own ratio fiber. -/
theorem source_native_B506_finite_ratio_fiber_square_identity434
    {I R : Type} [DecidableEq R]
    (S : Finset I) (rho : I → R) (a : I → ℂ) :
    (∑ i ∈ S, ∑ j ∈ S,
      if rho i = rho j then (star (a i)*a j).re else 0) =
    ∑ r ∈ S.image rho,
      ‖∑ i ∈ S.filter (fun i => rho i = r), a i‖^2 := by
  letI : DecidableEq I := Classical.decEq I
  have hFiber (r : R) :
      ‖∑ i ∈ S.filter (fun i => rho i = r), a i‖^2 =
      ∑ i ∈ S, ∑ j ∈ S,
        if rho i = r ∧ rho j = r then (star (a i)*a j).re else 0 := by
    rw [source_original_B437_true_complex_square_sum_cross434]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hir : rho i = r
    · simp only [hir,ite_true]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjr : rho j = r <;> simp [hir,hjr]
    · simp [hir]
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, ∑ r ∈ S.image rho,
      if rho i = r ∧ rho j = r then (star (a i)*a j).re else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : rho i = rho j
      · have hmemj : rho j ∈ S.image rho := Finset.mem_image.mpr ⟨j,hj,rfl⟩
        simp [h,hmemj]
      · simp [h,show ∀ r, ¬(rho i = r ∧ rho j = r) from by
          intro r hr
          exact h (hr.1.trans hr.2.symm)]
    _ = ∑ i ∈ S, ∑ r ∈ S.image rho, ∑ j ∈ S,
      if rho i = r ∧ rho j = r then (star (a i)*a j).re else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ r ∈ S.image rho, ∑ i ∈ S, ∑ j ∈ S,
      if rho i = r ∧ rho j = r then (star (a i)*a j).re else 0 := by
      exact Finset.sum_comm
    _ = ∑ r ∈ S.image rho,
      ‖∑ i ∈ S.filter (fun i => rho i = r), a i‖^2 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hFiber r).symm
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## NativePhysicalRatioFiberDecomposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The COMPLETE original T-native physical Q/P character RMS at the
true integer shift 2k is exactly the sum of NONNEGATIVE coherent squared
amplitudes of its genuine occupied cofactor RATIO fibers t/m modulo |k|.
All source positions z, dependent divisor lists m,t, physical projectors,
residuals, Mellin parameters, ψ/marked weights and original D20 coefficients
are preserved literally. Composite moduli are permitted: each source
cofactor is an actual unit modulo q by true W-roughness, not by a field
assumption. No artificial positivity has been imposed on cross pairs;
all signed offdiagonal terms within each ratio fiber remain coherent.
This identifies the exact arithmetic object needing new Type II saving. -/
theorem source_native_B507_complete_QP_character_RMS_ratio_fibers434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (hqW : ((k.natAbs:ℕ):ℝ) ≤ W) :
    let HR := sourceNativeB491ActualD20Core434 H Δ W y
    let S := sourceNativeB502ActiveD20PhysicalTriples434 g P Z bPsi k Δ W y
    let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
      sourceNativeB492ProjectedCoprimeTerm434 c g P
        (sourceNativeWithoutCharacter434 F)
        (sourceNativeWithoutCharacter434 HR)
        Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2
    let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
      (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceCorrelationProjected c g P
          (sourceNativeB491ActualD20Core434
            (sourceNativeWithCharacter434 F k.natAbs χ) Δ W y)
          (sourceNativeWithCharacter434 HR k.natAbs χ)
          Z a1 a2 bPsi (2*k) psi‖^2) =
    ∑ r ∈ S.image ratio,
      ‖∑ s ∈ S.filter (fun s => ratio s = r), base s‖^2 := by
  dsimp only
  let HR := sourceNativeB491ActualD20Core434 H Δ W y
  let S := sourceNativeB502ActiveD20PhysicalTriples434 g P Z bPsi k Δ W y
  let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
    sourceNativeB492ProjectedCoprimeTerm434 c g P
      (sourceNativeWithoutCharacter434 F)
      (sourceNativeWithoutCharacter434 HR)
      Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2
  let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
    (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹
  have hUnit (s : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ S) :
      IsUnit (s.2.1 : ZMod k.natAbs) := by
    have hnonzero := (Finset.mem_filter.mp hs).2.1
    exact source_native_B497_actual_D20_nonzero_unit_mod_q434
      Δ W y hWy s.2.1 hnonzero k.natAbs (Int.natAbs_pos.mpr hk) hqW
  have hGram := source_native_B504_complete_QP_shifted_projected_character_RMS434
    c g P F H Δ W y hWy Z a1 a2 bPsi k psi hk hsmall hqW
  have hFibers := source_native_B506_finite_ratio_fiber_square_identity434
    S ratio base
  have hCong (s v : Σ _ : ℕ, ℕ×ℕ) (hs : s ∈ S) (hv : v ∈ S) :
      (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
       ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) ↔ ratio s = ratio v :=
    source_native_B505_original_QP_cross_residue_iff_ratio434
      k.natAbs s.2.1 s.2.2 v.2.1 v.2.2 (hUnit s hs) (hUnit v hv)
  calc
    _ = ∑ s ∈ S, ∑ v ∈ S,
      if (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
          ((v.2.2*s.2.1:ℕ):ZMod k.natAbs)) then
        (star (base s)*base v).re else 0 := hGram
    _ = ∑ s ∈ S, ∑ v ∈ S,
      if ratio s = ratio v then (star (base s)*base v).re else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hc : (((v.2.1*s.2.2:ℕ):ZMod k.natAbs) =
        ((v.2.2*s.2.1:ℕ):ZMod k.natAbs))
      · have hr := (hCong s v hs hv).mp hc
        simp only [if_pos hc,if_pos hr]
      · have hr : ratio s ≠ ratio v := fun he => hc ((hCong s v hs hv).mpr he)
        simp only [if_neg hc,if_neg hr]
    _ = ∑ r ∈ S.image ratio,
      ‖∑ s ∈ S.filter (fun s => ratio s = r), base s‖^2 := hFibers
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FullNativeRMSRatioWithoutExtraCutoff -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The full native Q/P position-summed four-sign character RMS is an
EXACT sum of coherent target/source cofactor RATIO-fiber squared norms,
with no additional cutoff q≤W hypothesis: the ORIGINAL physical shift
gate |2k|≤W itself implies |k|≤W. The only hypotheses beyond original
literal source geometry are 0≠k and the true W≤y. -/
theorem source_native_B508_complete_QP_ratio_fibers_from_actual_shift434
    (c : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (F H : PrimeSlotCore) (Δ W y : ℝ) (hWy : W ≤ y)
    (Z a1 a2 bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    :
    let HR := sourceNativeB491ActualD20Core434 H Δ W y
    let S := sourceNativeB502ActiveD20PhysicalTriples434 g P Z bPsi k Δ W y
    let base : (Σ _ : ℕ, ℕ×ℕ) → ℂ := fun s =>
      sourceNativeB492ProjectedCoprimeTerm434 c g P
        (sourceNativeWithoutCharacter434 F)
        (sourceNativeWithoutCharacter434 HR)
        Δ W y Z a1 a2 k psi s.1 s.2.1 s.2.2
    let ratio : (Σ _ : ℕ, ℕ×ℕ) → ZMod k.natAbs := fun s =>
      (s.2.2 : ZMod k.natAbs) * (s.2.1 : ZMod k.natAbs)⁻¹
    (∑ χ : DirichletCharacter ℂ k.natAbs,
      ‖((k.natAbs.totient:ℂ)⁻¹)‖ *
        ‖sourceCorrelationProjected c g P
          (sourceNativeB491ActualD20Core434
            (sourceNativeWithCharacter434 F k.natAbs χ) Δ W y)
          (sourceNativeWithCharacter434 HR k.natAbs χ)
          Z a1 a2 bPsi (2*k) psi‖^2) =
    ∑ r ∈ S.image ratio,
      ‖∑ s ∈ S.filter (fun s => ratio s = r), base s‖^2 := by
  have hnk : k.natAbs ≤ (2*k).natAbs := by
    rw [Int.natAbs_mul]
    change k.natAbs ≤ 2*k.natAbs
    omega
  have hqW : ((k.natAbs:ℕ):ℝ) ≤ W :=
    (by exact_mod_cast hnk : ((k.natAbs:ℕ):ℝ) ≤ ((2*k).natAbs:ℝ)).trans hsmall
  exact source_native_B507_complete_QP_character_RMS_ratio_fibers434
    c g P F H Δ W y hWy Z a1 a2 bPsi k psi hk hsmall hqW
end Green64Analytic.ShiftTwoTerminal

end

end

