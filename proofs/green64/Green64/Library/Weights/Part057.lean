module

public import Green64.Library.Analysis.Estimates.Part012
public import Green64.Library.Correlation.Part036
public import Green64.Library.Correlation.Part038
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.Part056
public import Green64.Library.Correlation.Part037
public import Green64.Library.Weights.Part017
public import Green64.Library.Analysis.Estimates.B26SmallOldFourierEnergy
public import Green64.Library.Weights.Part042
public import Green64.Library.Correlation.Part029
public import Green64.Library.Correlation.PhysicalSinglePrimeReturn

@[expose] public section

/-!
# Weights / Part057

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalTrueAnyNuOrderedBandsSigned -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- GENUINE original SOURCE03 ν signed RAW-minus-Knu complete
physical Fourier/Mellin residual, with true C191 major, C6 minor,
canonical log mesh, exact GLOBAL count and discarded cost,
with REAL numeric prime interval band geometry replacing
all original abstract hBIG/prime-upper/representative-band/
group-separation hypotheses. BIG groups are complete
prime intervals (loB_g,hiB_g], small groups only subintervals.
Within-family disjointness and small-versus-BIG separation
are deduced from genuine numeric orders and the original
source03 scale exponents. All remaining BIG-band boundary
and meshing hypotheses are explicitly stated source data.
For arbitrary physical mark-sensitive complex tests, full
signed norm² <=2*(2*(epsC191²+72000L^-Bout)+L^-2Bmaj)
times the true harmonic source/target energies.
Still ONE original ν; NOT full four-sign sh:correlation/Green64. -/
theorem eventually_source_original_true_ANY_nu_ORDERED_BANDS_signed_C191_C6_434
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
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal) :
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
    (ν : SourceOriginalProbePattern434 β m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (hXiNat : xi⁻¹ ≤ L^CxiNat)
    (iA : ν.1) (iB : ν.2)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYA : Y ≤ ((loB iA.val.1+1:ℕ):ℝ))
    (hYB : Y ≤ ((loB iB.val.1+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hWidth : hAvar ν + hBvar ν ≤
      L^(-(Bmaj+((4*Cq+C4:ℕ):ℝ))))
    (hWidth1 : hAvar ν + hBvar ν ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount :
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA :
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB :
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1))),
    let BP : β → Type := fun g => {p : ℕ // p ∈ data.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun g p => p.val) data.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => data.Tb z.val.1) (hBvar ν)
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => data.Tb z.val.1) (hAvar ν)
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d) /
      (hAvar ν) +
      ((Fintype.card ν.2:ℝ)*L^d)/(hBvar ν))+4)*xi
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν data.Tb data.Vbig Qchar
        (hAvar ν) (hBvar ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    ∀ sourceTest targetTest : X → ℂ,
    ‖(∑ ab : X × X,
       ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*err ab)‖^2 ≤
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj))) *
        (∑ s : X,w s*‖sourceTest s‖^2) *
        (∑ v : X,w v*‖targetTest v‖^2) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_true_ANY_nu_uniform_mesh_FULL_signed_C191_C6_434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hCoreL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive Vmin hVmin hMass hBigLower
    hL hBigUpper hLdyad hQ hXiNat
    iA iB hLoOne hLoLeHi hLoLarge hYA hYB
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hWidth hWidth1 hZeta
    hLMesh hCount hMeshA hMeshB hXiChoice
  classical
  have hSep := source_original_source03_ordered_prime_bands_admissible434
    cfg x L Ydata Hprime data
    (by linarith : 1 < L) loS hiS loB hiB
    hSmallSubset hBigFull hSmallOrder hBigOrder
    hTsUpper hTbLower
  have hConductor := source_original_source03_big_band_conductor434
    cfg x L Ydata Hprime data Qchar loB hiB hBigFull hBigLower
  have hUpper := source_original_source03_big_band_upper434
    cfg x L Ydata Hprime data d loB hiB hBigFull hBigUpper
  have hBIGA : ∀ z : ν.1, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ Qchar^2 < p := by
    intro z p hp
    exact hConductor z.val.1 p hp
  have hBIGB : ∀ z : ν.2, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ Qchar^2 < p := by
    intro z p hp
    exact hConductor z.val.1 p hp
  have hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d) := by
    intro z p hp
    exact hUpper z.val.1 p hp
  have hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ data.Tb z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d) := by
    intro z p hp
    exact hUpper z.val.1 p hp
  have hBound := hCoreL x Ydata Hprime data hSep hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive Vmin hVmin hMass hBIGA hBIGB
    hL hPrimeUpperA hPrimeUpperB hLdyad hQ hXiNat
    iA iB
    (loB iA.val.1) (hiB iA.val.1)
    (loB iB.val.1) (hiB iB.val.1)
    (hLoOne iA.val.1) (hLoOne iB.val.1)
    (hLoLeHi iA.val.1) (hLoLeHi iB.val.1)
    (hBigUpper iA.val.1) (hBigUpper iB.val.1)
    (hLoLarge iA.val.1) (hLoLarge iB.val.1)
    (hBigLower iA.val.1) (hBigLower iB.val.1)
    hYA hYB (hBigFull iA.val.1) (hBigFull iB.val.1)
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hWidth hWidth1 hZeta
    hLMesh hCount hMeshA hMeshB hXiChoice
  simpa only using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAnyNuCanonicalOrderedBands -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- ORIGINAL ν SOURCE03 physical signed RAW-minus-Knu
complete C191/C6/discarded residual with actual ordered
BIG prime intervals and CANONICAL Mellin log-mesh, where
the true original C191 small-global-width hWidth and
retention xi^-1 ≤ L^CxiNat and hWidth≤1 are no longer
assumptions: all THREE follow directly from the source03
explicit scheduled h=L^-E/2 and xi.
Source03 grouped prime admissibility, true primitive C6
and both physical harmonic laws are retained. Result:
  norm² ≤2*(2*(eps_C191²+72000 L^-Bout)+L^-2Bmaj)
          * Esource*Etarget.
All original integer group-band boundary and C191
irrational-major-arc prerequisites remain explicit.
Not the four-sign/all-ν sh:correlation or Green64. -/
theorem eventually_source_original_true_ANY_nu_CANONICAL_ordered_bands_signed434
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
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal) :
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
    (ν : SourceOriginalProbePattern434 β m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (hQpositive : 0 < Qchar)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hMass : ∀ g : β, Vmin ≤ data.Vbig g)
    (hBigLower : ∀ g : β, Qchar^2 ≤ loB g)
    (hL : 192 ≤ L)
    (hBigUpper : ∀ g : β, (hiB g:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Qchar:ℝ) ≤ L^Cq)
    (iA : ν.1) (iB : ν.2)
    (hLoOne : ∀ g : β, 1 ≤ loB g)
    (hLoLeHi : ∀ g : β, loB g ≤ hiB g)
    (hLoLarge : ∀ g : β,
      Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
    (hYA : Y ≤ ((loB iA.val.1+1:ℕ):ℝ))
    (hYB : Y ≤ ((loB iB.val.1+1:ℕ):ℝ))
    (ζ theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Qchar)
    (hBudget : 3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
      |(k:ℝ)| *L^cfg.Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(Bmaj+(Cq:ℝ))) ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hLMesh : 16*(M+1) ≤ L)
    (hCount :
      ((Fintype.card ν.1+Fintype.card ν.2:ℕ):ℝ) ≤ M)
    (hMeshA :
      hAvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hMeshB :
      hBvar ν = L^(-(Bmaj+(((4*Cq+C4:ℕ):ℝ))))/2)
    (hXiChoice :
      xi = L^(-(2*Bmaj+d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))))/
        (16*(M+1))),
    let BP : β → Type := fun g => {p : ℕ // p ∈ data.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP
      (fun g p => p.val) data.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => data.Tb z.val.1) (hBvar ν)
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => data.Tb z.val.1) (hAvar ν)
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d) /
      (hAvar ν) +
      ((Fintype.card ν.2:ℝ)*L^d)/(hBvar ν))+4)*xi
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν data.Tb data.Vbig Qchar
        (hAvar ν) (hBvar ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    ∀ sourceTest targetTest : X → ℂ,
    ‖(∑ ab : X × X,
       ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*err ab)‖^2 ≤
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj))) *
        (∑ s : X,w s*‖sourceTest s‖^2) *
        (∑ v : X,w v*‖targetTest v‖^2) := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_true_ANY_nu_ORDERED_BANDS_signed_C191_C6_434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hCoreL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive Vmin hVmin hMass hBigLower
    hL hBigUpper hLdyad hQ
    iA iB hLoOne hLoLeHi hLoLarge hYA hYB
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta
    hLMesh hCount hMeshA hMeshB hXiChoice
  classical
  let E : ℝ := Bmaj+(((4*Cq+C4:ℕ):ℝ))
  let h : ℝ := L^(-E)/2
  let xiCanon : ℝ := L^(-(2*Bmaj+d+E))/(16*(M+1))
  have hSchedule := source_original_uniform_mellin_full_parameter_schedule434
    Cq C4 CxiNat
    (Fintype.card ν.1) (Fintype.card ν.2)
    L Bmaj d M hBmaj.le hd hM hLMesh hCount hXiExponent
  obtain ⟨hh,hxiSch,hWidthSch,hXiSch,hDrop⟩ := hSchedule
  have hXiNat : xi⁻¹ ≤ L^CxiNat := by
    rw [hXiChoice]
    simpa only [E,xiCanon] using hXiSch
  have hWidth : hAvar ν+hBvar ν ≤
      L^(-(Bmaj+((4*Cq+C4:ℕ):ℝ))) := by
    rw [hMeshA,hMeshB]
    simpa only [E,h] using hWidthSch
  have hE : 0 ≤ E := by dsimp [E];positivity
  have hLone : 1 ≤ L := by linarith [hL]
  have hPow : L^(-E) ≤ 1 := by
    calc
      _ ≤ L^(0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLone (by linarith [hE])
      _ = 1 := by simp
  have hWidth1 : hAvar ν+hBvar ν ≤ 1 := by
    exact hWidth.trans (by simpa only [E] using hPow)
  have hh := hCoreL x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    ν hν hQpositive Vmin hVmin hMass hBigLower
    hL hBigUpper hLdyad hQ hXiNat
    iA iB hLoOne hLoLeHi hLoLarge hYA hYB
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hWidth hWidth1 hZeta
    hLMesh hCount hMeshA hMeshB hXiChoice
  simpa only using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAllNuPhysicalSignedFamilySum -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The full ORIGINAL ν-dependent joint physical B-source/A-target
signed RAW-minus-Knu Fourier/Mellin residual pairing, retaining
every full free-prime mark, both honest harmonic laws, and fully
arbitrary complex endpoint tests (not functions only of products). -/
noncomputable def sourceOriginalTrueNuSignedFullPhysicalPairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP
    (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w := sourceOriginalVariableBIGMass434 BP t mu
  ∑ ab : X × X,
    ((w ab.1*w ab.2:ℝ):ℂ) *
      star (sourceTest ν ab.1)*targetTest ν ab.2 *
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν d.Tb d.Vbig Q
        (hA ν) (hB ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)

/-- Actual physical squared-L2 energy for arbitrary ν-sensitive
endpoint tests, with the unaltered original reciprocal-prime masses. -/
noncomputable def sourceOriginalTrueNuSignedFullPhysicalEnergy434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (test :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℝ :=
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP
    (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w := sourceOriginalVariableBIGMass434 BP t mu
  ∑ a : X, w a*‖test ν a‖^2

/-- Sharp finite globalization across the EXACT original two-block
SOURCE03 comparison patterns, not the exponentially larger
primitive character/cell family: under the per-ν original
physical signed squared-L2 bound, the total family incurs only
2^(2m(|blockA|+|blockB|)) in the SQUARED norm.
No duplication of RAW by the primitive character count.
The per-ν C191/C6 source arithmetic hypotheses are made
explicit at their application; this finite theorem accepts the
resulting per-ν bounds as its interface. -/
theorem source_original_true_all_nu_physical_signed_L2_sum434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (save : ℝ) (hSave : 0 ≤ save)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ sourceTest ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ targetTest ν ≤ 1)
    (hPerNu : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
          sourceTest targetTest ν‖^2 ≤
      save *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ sourceTest ν *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ targetTest ν) :
    ‖∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
          sourceTest targetTest ν‖^2 ≤
      ((2^(m*(blockA.card+blockB.card)):ℝ)^2)*save := by
  classical
  let fam := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let term := sourceOriginalTrueNuSignedFullPhysicalPairing434
    d J ell m hmJ Q hA hB xi ζ theta k sourceTest targetTest
  let ES := sourceOriginalTrueNuSignedFullPhysicalEnergy434
    d J ell m hmJ sourceTest
  let ET := sourceOriginalTrueNuSignedFullPhysicalEnergy434
    d J ell m hmJ targetTest
  have hEach (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ fam) :
      ‖term ν‖^2 ≤ (1:ℝ)^2*save := by
    obtain ⟨hS0,hS1⟩ := hES ν hν
    obtain ⟨hT0,hT1⟩ := hET ν hν
    have hProd : ES ν * ET ν ≤ 1 := by
      calc
        _ ≤ 1*ET ν := mul_le_mul_of_nonneg_right hS1 hT0
        _ ≤ 1*1 := mul_le_mul_of_nonneg_left hT1 (by norm_num)
        _ = 1 := by ring
    calc
      _ ≤ save * ES ν * ET ν := hPerNu ν hν
      _ = save*(ES ν*ET ν) := by ring
      _ ≤ save*1 := mul_le_mul_of_nonneg_left hProd hSave
      _ = (1:ℝ)^2*save := by ring
  have hSquare := source_original_true_finite_weighted_minor_square434
    fam term (fun _ => (1:ℝ)) save hSave
    (by intro ν hν;norm_num) hEach
  have hCardNat := source_original_two_block_probe_pattern_card434
    blockA blockB m
  have hCard : (fam.card:ℝ) ≤
      (2^(m*(blockA.card+blockB.card)):ℝ) := by
    exact_mod_cast hCardNat
  have hCardSq := pow_le_pow_left₀
    (Nat.cast_nonneg (α:=ℝ) fam.card) hCard 2
  have hScale :
      ((fam.card:ℝ)^2)*save ≤
       (2^(m*(blockA.card+blockB.card)):ℝ)^2*save :=
    mul_le_mul_of_nonneg_right hCardSq hSave
  have hEnergy :
      ‖∑ ν ∈ fam, term ν‖^2 ≤ ((fam.card:ℝ)^2)*save := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one]
      using hSquare
  exact hEnergy.trans hScale
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAllNuCanonicalSignedFamily -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- ALL genuinely indexed original ν SOURCE03 signed RAW-minus-Knu
full-free-mark physical Fourier/Mellin residuals summed with the
true two-block pattern combinatorics, with NO primitive character
multiplicity factor or hidden spectral hMinor premise.
The REAL ordered small/BIG prime group geometry and source03
canonical mesh, C191+C6 and discarded inputs are all explicit:
  squared norm of sum_ν <= 2^(2m(sA+sB)) *
    2*(2*(eps_C191²+72000 L^-Bout)+L^-2Bmaj).
For each ν the actual endpoint tests are arbitrary complex full
mark-sensitive L2-normalized laws; the same original source
prime groups, primitive conductor family and Fourier/Mellin phase
are retained. This is still the SUM OF physical ν signed errors;
the exact identification with the raw+comparison residual of the
paper requires a separate shared-dilation/RAW baseline identity.
Original full four-sign sh:correlation and Green64 are not claimed. -/
theorem eventually_source_original_true_ALL_nu_CANONICAL_ordered_bands_signed434
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
      Bout+2*(d+(Bmaj+(((4*Cq+C4:ℕ):ℝ)))+1) ≤ Bgoal) :
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
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 β m) →
      SourceOriginalVariableBIGState434
        (fun g : β => {p : ℕ // p ∈ data.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν ≤ 1),
    let family := sourceOriginalTwoBlockProbePatterns434
      blockA blockB m
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
    let budget : ℝ :=
      2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
    ‖∑ ν ∈ family,
      sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      ((2^(m*(blockA.card+blockB.card)):ℝ)^2)*budget := by
  obtain ⟨K,Y,hK,hCore⟩ :=
    eventually_source_original_true_ANY_nu_CANONICAL_ordered_bands_signed434
      cfg Cq CxiNat Cs C4 gamma d Bmaj hgamma hd hBmaj
      D Bsave hD C hExponent hSaving
      Cchar CxiReal Bgoal hCchar hCxiReal hExpBudget
      Aarc hAarc hArc M Bout hM hXiExponent hMinorExponent
  refine ⟨K,Y,hK,?_⟩
  filter_upwards [hCore] with L hCoreL
  intro ι β instI instDI instB instDB
    x Ydata Hprime data
    loS hiS loB hiB hSmallSubset hBigFull
    hSmallOrder hBigOrder hTsUpper hVbig
    blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
    hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
    hQpositive Vmin hVmin hMass hBigLower
    hL hBigUpper hLdyad hQ
    hLoOne hLoLeHi hLoLarge hYbound
    ζ theta k hk S hS hSscale hQchar hBudget
    hC4 hDeltaLe hZeta hLMesh hCount hMeshA hMeshB
    hXiChoice sourceTest targetTest hES hET
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-Bmaj)
  let budget : ℝ := 2*(2*(eps^2+72000*L^(-Bout))+L^(-(2*Bmaj)))
  have hLpos : 0 < L := by linarith
  have hSaveNN : 0 ≤ budget := by
    dsimp only [budget,eps]
    positivity
  have hPerNu (ν : SourceOriginalProbePattern434 β m) (hν : ν ∈ family) :
      ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      budget *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν := by
    have hPattern :=
      (source_original_two_block_probe_pattern_mem434
        blockA blockB m ν.1 ν.2).mp hν
    obtain ⟨gA,hgA⟩ := hPattern.1
    obtain ⟨gB,hgB⟩ := hPattern.2.2.1
    let iA : ν.1 := ⟨gA,hgA⟩
    let iB : ν.2 := ⟨gB,hgB⟩
    have hh := hCoreL x Ydata Hprime data
      loS hiS loB hiB hSmallSubset hBigFull
      hSmallOrder hBigOrder hTsUpper hVbig
      blockA blockB hDisjoint m Qchar hm J ell hmJ hTbLower
      hAvar hBvar hhA hhB xi hxi hQpoly hXipoly
      ν hν hQpositive Vmin hVmin hMass hBigLower
      hL hBigUpper hLdyad hQ
      iA iB hLoOne hLoLeHi hLoLarge
      (hYbound iA.val.1) (hYbound iB.val.1)
      ζ theta k hk S hS hSscale hQchar hBudget
      hC4 hDeltaLe hZeta hLMesh
      (hCount ν hν) (hMeshA ν hν) (hMeshB ν hν)
      hXiChoice (sourceTest ν) (targetTest ν)
    change
      ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
        data J ell m hmJ Qchar hAvar hBvar xi ζ theta k
        sourceTest targetTest ν‖^2 ≤
      budget *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ sourceTest ν *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        data J ell m hmJ targetTest ν at hh
    exact hh
  have hFamily :=
    source_original_true_all_nu_physical_signed_L2_sum434
      data blockA blockB J ell m hmJ Qchar
      hAvar hBvar xi ζ theta k
      sourceTest targetTest budget hSaveNN
      hES hET hPerNu
  simpa only [family,eps,budget] using hFamily
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAllNuPhysicalUnitSign -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Every unit-modulus true source03 ν-dependent shared-dilation
parity factor preserves the ALREADY KERNEL-PROVED signed
RAW-minus-Knu full physical C191/C6/discarded family L²
estimate for all full free-prime-mark complex endpoint tests.
This lemma accepts genuine per-ν C191/C6 arithmetic as hPerNu;
its four-sign specialization will use the ACTUAL shared
labelled slot count, not an arbitrary fictitious mode sign.
No independent signed ideal/B transference is claimed. -/
theorem source_original_true_all_nu_physical_unit_sign_L2_sum434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (save : ℝ) (hSave : 0 ≤ save)
    (unitSign : SourceOriginalProbePattern434 G m → ℂ)
    (hUnitSign : ∀ ν ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        ‖unitSign ν‖ = 1)
    (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ sourceTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ sourceTest ν ≤ 1)
    (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 ≤ sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ targetTest ν ∧
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ targetTest ν ≤ 1)
    (hPerNu : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ‖sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
          sourceTest targetTest ν‖^2 ≤
      save *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ sourceTest ν *
      sourceOriginalTrueNuSignedFullPhysicalEnergy434
        d J ell m hmJ targetTest ν) :
    ‖∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
       unitSign ν * sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
          sourceTest targetTest ν‖^2 ≤
      ((2^(m*(blockA.card+blockB.card)):ℝ)^2)*save := by
  classical
  let fam := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let base := sourceOriginalTrueNuSignedFullPhysicalPairing434
    d J ell m hmJ Q hA hB xi ζ theta k sourceTest targetTest
  let term := fun ν => unitSign ν * base ν
  let ES := sourceOriginalTrueNuSignedFullPhysicalEnergy434
    d J ell m hmJ sourceTest
  let ET := sourceOriginalTrueNuSignedFullPhysicalEnergy434
    d J ell m hmJ targetTest
  have hEach (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ fam) :
      ‖term ν‖^2 ≤ (1:ℝ)^2*save := by
    obtain ⟨hS0,hS1⟩ := hES ν hν
    obtain ⟨hT0,hT1⟩ := hET ν hν
    have hProd : ES ν * ET ν ≤ 1 := by
      calc
        _ ≤ 1*ET ν := mul_le_mul_of_nonneg_right hS1 hT0
        _ ≤ 1*1 := mul_le_mul_of_nonneg_left hT1 (by norm_num)
        _ = 1 := by ring
    have hNorm :
        ‖term ν‖^2 = ‖base ν‖^2 := by
      dsimp only [term]
      rw [norm_mul,hUnitSign ν hν,one_mul]
    calc
      _ = ‖base ν‖^2 := hNorm
      _ ≤ save * ES ν * ET ν := hPerNu ν hν
      _ = save*(ES ν*ET ν) := by ring
      _ ≤ save*1 := mul_le_mul_of_nonneg_left hProd hSave
      _ = (1:ℝ)^2*save := by ring
  have hSquare := source_original_true_finite_weighted_minor_square434
    fam term (fun _ => (1:ℝ)) save hSave
    (by intro ν hν;norm_num) hEach
  have hCardNat := source_original_two_block_probe_pattern_card434
    blockA blockB m
  have hCard : (fam.card:ℝ) ≤
      (2^(m*(blockA.card+blockB.card)):ℝ) := by
    exact_mod_cast hCardNat
  have hCardSq := pow_le_pow_left₀
    (Nat.cast_nonneg (α:=ℝ) fam.card) hCard 2
  have hScale :
      ((fam.card:ℝ)^2)*save ≤
       (2^(m*(blockA.card+blockB.card)):ℝ)^2*save :=
    mul_le_mul_of_nonneg_right hCardSq hSave
  have hEnergy :
      ‖∑ ν ∈ fam, term ν‖^2 ≤ ((fam.card:ℝ)^2)*save := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one]
      using hSquare
  exact hEnergy.trans hScale
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuFullPrimitiveRawPhysical -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The authentic SOURCE03 physical pairing with the
whole primitive character-and-cell comparison expectation:
one ν, ALL its genuine jA,χA,jB,χB modes, and arbitrary
mark-sensitive full source/target tests at the unchanged
reciprocal-prime harmonic weights. The raw branch is absent. -/
noncomputable def sourceOriginalTrueNuPhysicalPrimitivePairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP
    (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w := sourceOriginalVariableBIGMass434 BP t mu
  let JA := sourceOriginalProbeActiveCellsA434
    m d.Tb d.Vbig ν (hA ν) xi
  let JB := sourceOriginalProbeActiveCellsB434
    m d.Tb d.Vbig ν (hB ν) xi
  let Char := sourceOriginalActualPrimitiveCharacters434 Q
  let Modes := ((JA.product Char).product (JB.product Char))
  ∑ ab : X × X,
    ((w ab.1*w ab.2:ℝ):ℂ) *
      star (sourceTest ν ab.1)*targetTest ν ab.2 *
      (∑ mode ∈ Modes,
        sourceOriginalTrueNuPrimitiveFourierTerm434
          J ell m hmJ ν d.Tb d.Vbig Q
          (hA ν) (hB ν) xi ζ theta k mode
          (fun g i => (ab.1 g i).val)
          (fun g i => (ab.2 g i).val))

/-- The RAW branch per genuine ν with the SAME
source-B/target-A mark-projection, Mellin/Fourier phase,
sign and full original harmonic source/target law.
No multiplication by the primitive-character count. -/
noncomputable def sourceOriginalTrueNuPhysicalRawPairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP
    (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w := sourceOriginalVariableBIGMass434 BP t mu
  ∑ ab : X × X,
    ((w ab.1*w ab.2:ℝ):ℂ) *
      star (sourceTest ν ab.1)*targetTest ν ab.2 *
      sourceOriginalTrueNuRawFourierTerm434
        J ell m hmJ ν d.Tb d.Vbig Q
        (hA ν) (hB ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)

/-- Exact genuine SOURCE03 physical bilinear decomposition for
one ν: the true joint free-mark RAW-minus-Knu signed pairing
is the auxiliary primitive-character comparison pairing
MINUS the raw pairing ONCE. No analytic estimate is used.
This makes the residual baseline alignment a precise
finite operator identity on full physical measures. -/
theorem source_original_true_nu_physical_primitive_MINUS_RAW434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuSignedFullPhysicalPairing434
      d J ell m hmJ Q hA hB xi ζ theta k
      sourceTest targetTest ν =
    sourceOriginalTrueNuPhysicalPrimitivePairing434
      d J ell m hmJ Q hA hB xi ζ theta k
      sourceTest targetTest ν -
    sourceOriginalTrueNuPhysicalRawPairing434
      d J ell m hmJ Q hA hB xi ζ theta k
      sourceTest targetTest ν := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP
    (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w := sourceOriginalVariableBIGMass434 BP t mu
  let JA := sourceOriginalProbeActiveCellsA434 m d.Tb d.Vbig
    ν (hA ν) xi
  let JB := sourceOriginalProbeActiveCellsB434 m d.Tb d.Vbig
    ν (hB ν) xi
  let Char := sourceOriginalActualPrimitiveCharacters434 Q
  let Modes := ((JA.product Char).product (JB.product Char))
  have hPoint (ab : X × X) :
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν d.Tb d.Vbig Q
        (hA ν) (hB ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val) =
      (∑ mode ∈ Modes,
        sourceOriginalTrueNuPrimitiveFourierTerm434
          J ell m hmJ ν d.Tb d.Vbig Q
          (hA ν) (hB ν) xi ζ theta k mode
          (fun g i => (ab.1 g i).val)
          (fun g i => (ab.2 g i).val)) -
      sourceOriginalTrueNuRawFourierTerm434
        J ell m hmJ ν d.Tb d.Vbig Q
        (hA ν) (hB ν) xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val) := by
    exact source_original_true_nu_exact_primitive_MINUS_RAW434
      J ell m hmJ ν d.Tb d.Vbig Q
      (hA ν) (hB ν) xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  unfold sourceOriginalTrueNuSignedFullPhysicalPairing434
    sourceOriginalTrueNuPhysicalPrimitivePairing434
    sourceOriginalTrueNuPhysicalRawPairing434
  dsimp only
  simp_rw [hPoint]
  simp only [mul_sub,Finset.sum_sub_distrib]
  rfl
end Green64Analytic.CorrelationSquare

end

/-! ## PhysicalRawPrimitiveResidual -/

section

open scoped BigOperators Classical

namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Consumer orientation of the exact physical comparison identity: the
literal RAW pairing is the complete primitive comparison pairing minus the
signed RAW-minus-Knu residual.  RAW is still counted exactly once. -/
theorem source_original_true_nu_physical_RAW_eq_primitive_MINUS_signed434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalTrueNuPhysicalRawPairing434
      d J ell m hmJ Q hA hB xi ζ theta k
      sourceTest targetTest ν =
    sourceOriginalTrueNuPhysicalPrimitivePairing434
      d J ell m hmJ Q hA hB xi ζ theta k
      sourceTest targetTest ν -
    sourceOriginalTrueNuSignedFullPhysicalPairing434
      d J ell m hmJ Q hA hB xi ζ theta k
      sourceTest targetTest ν := by
  rw [source_original_true_nu_physical_primitive_MINUS_RAW434]
  ring

/-- The same exact RAW-once decomposition after summing any finite family of
genuine patterns.  The primitive and residual families are separated only
after the pointwise physical identity, so no character/cell multiplicity is
introduced. -/
theorem source_original_true_family_physical_RAW_eq_primitive_MINUS_signed434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (family : Finset (SourceOriginalProbePattern434 G m)) :
    (∑ ν ∈ family,
      sourceOriginalTrueNuPhysicalRawPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
        sourceTest targetTest ν) =
    (∑ ν ∈ family,
      sourceOriginalTrueNuPhysicalPrimitivePairing434
        d J ell m hmJ Q hA hB xi ζ theta k
        sourceTest targetTest ν) -
    (∑ ν ∈ family,
      sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
        sourceTest targetTest ν) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ν hν
  exact source_original_true_nu_physical_RAW_eq_primitive_MINUS_signed434
    d J ell m hmJ Q hA hB xi ζ theta k sourceTest targetTest ν

/-- Specialization to the literal two-block SOURCE03 pattern family used by
the C191/C6 and all-pattern physical consumers. -/
theorem source_original_true_two_block_physical_RAW_eq_primitive_MINUS_signed434
    {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (xi ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest :
      (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ d.Tb g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalTrueNuPhysicalRawPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
        sourceTest targetTest ν) =
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalTrueNuPhysicalPrimitivePairing434
        d J ell m hmJ Q hA hB xi ζ theta k
        sourceTest targetTest ν) -
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalTrueNuSignedFullPhysicalPairing434
        d J ell m hmJ Q hA hB xi ζ theta k
        sourceTest targetTest ν) := by
  exact source_original_true_family_physical_RAW_eq_primitive_MINUS_signed434
    d J ell m hmJ Q hA hB xi ζ theta k sourceTest targetTest
      (sourceOriginalTwoBlockProbePatterns434 blockA blockB m)

end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26AlignedAllNuComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 44000000

/- Literal full active-state energy, independent of any conditional fibre. -/
noncomputable def sourceOriginalB26FullActiveEnergy434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (F : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℝ :=
  let mu := sourceOriginalJointHarmonicMu434
    (fun g : G => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) d.Vbig
  ∑ s : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}),
    (∏ g : G,∏ i : Fin (J+ell),mu g (s g i))*‖F ν s‖^2

/- Literal CLEAN comparison including original source mass, target shared-copy
law, both full endpoint tests and both endpoint permutations. -/
noncomputable def sourceOriginalB26PermutedFullPairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi ζ : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (sourceTest targetTest : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  let Active := ((g : G) → Fin (J+ell) → BP g)
  ∑ s : Active,∑ v : Active,
    ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v (sigma ν) (tau ν) *
      (star (sourceTest ν s)*targetTest ν v*
        sourceOriginalB26CanonicalComparisonValue434 d.Tb d.Vbig J ell m hmJ ν
          Q (hA ν) (hB ν) xi (c ν) s v (sigma ν) (tau ν) ζ (theta ν) (orientation ν) k)


/-- Applicable genuine-family B26 CLEAN comparison with explicit compatible Q/h/xi, all shared endpoint signs, both endpoint permutations, and a threshold before every moving full prime array. RAW and auxiliary-ban correction are separate. --/
theorem eventually_source_original_B26_ALIGNED_ALL_NU_COMPARISON434
    (cfg : SourceComparisonFixed434)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (J ell : ℕ) (hmJ : m ≤ J)
      (ζ : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (hDivisor : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<c ν)
      (hOrientation : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation ν=1 ∨ orientation ν= -1)
      (hZeta : |ζ| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (sourceTest targetTest :
        (ν : SourceOriginalProbePattern434 G m) →
        ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
      (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        0 ≤ sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ sourceTest ν ∧
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ sourceTest ν ≤ 1)
      (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        0 ≤ sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ targetTest ν ∧
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ targetTest ν ≤ 1)
      (epsSrc epsTgt : Bool),
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let shared := fun ν : SourceOriginalProbePattern434 G m =>
      ((Fintype.card ι)*J) + ∑ g : G,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 G m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    ‖∑ ν ∈ family,
      sign ν * sourceOriginalB26PermutedFullPairing434
        data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
        sourceTest targetTest ν‖^2 ≤ L^(-Bgoal) := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  have hE : 0 ≤ E := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) cfg.hC0)
    (Real.log_nonneg (by norm_num))
  let Bper : ℝ := Bgoal+2*E
  have hPer : 0 ≤ Bper := by dsimp [Bper];linarith
  obtain ⟨Cfactor,Cq,Cs,C4,Cxi,Bsave,D,H,
    hBsave,hD,hH,hSum,hFactor,hMinor,hQexp,hCs,hC4,hFreq,hWidth,hDrop⟩ :=
    source_original_aligned_comparison_MODULUS_exponents434
      cfg Bper dscale Cfreq Ck hPer hd hCk
  have hWidth' : Bsave+((4*Cq+C4:ℕ):ℝ) ≤ H := by linarith
  obtain ⟨Y0,hGlobalEvent⟩ :=
    eventually_source_original_B26_PERMUTED_COMPARISON434
      cfg Cq Cxi Cs C4 Cfactor gamma dscale D Bsave H Bper
      hgamma hd hD hBsave hH hCs hC4 hWidth' hDrop hFactor hMinor hSum
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hGlobalEvent,
    eventually_source_original_ALIGNED_physical_choices434
      Cq Cxi D Ck H gamma cfg.cexp Y0 hD hCk hH hgamma hc hQexp,
    eventually_ge_atTop (1:ℝ)] with L hGlobal hChoices hL
  have hLp : 0 < L := by linarith
  let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  obtain ⟨hQpos,hQlower,hQupper,hh,hwidth,hxi,hXi,hLdyad,hEnds,hPrime,hModes⟩ :=
    hChoices
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J ell hmJ ζ k c theta orientation hDivisor hOrientation hZeta hk
    sigma tau sourceTest targetTest hES hET epsSrc epsTgt
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J) + ∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  refine ⟨hModes k hk,?_⟩
  have hTbUpper : ∀ g, ∀ p ∈ data.Tb g, (p:ℝ) ≤ Real.exp (L^dscale) := by
    intro g p hp
    have hBand := source_original_source03_big_band_upper434
      cfg x L Y Hprime data dscale loB hiB hBigFull hBigUpper
    exact (hBand g p hp).2
  have hBIG : ∀ g, ∀ p ∈ data.Tb g, Q^2<p :=
    fun g p hp => hPrime p (hTbLower g p hp)
  have hZeta4 : |ζ| ≤ L^C4 := by
    calc
      _ ≤ L^Cfreq := hZeta
      _ ≤ L^(C4:ℝ) := Real.rpow_le_rpow_of_exponent_le hL hFreq
      _ = L^C4 := Real.rpow_natCast L C4
  have hPerNu : ∀ ν ∈ family,
      ‖sourceOriginalB26PermutedFullPairing434
        data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
        sourceTest targetTest ν‖^2 ≤
      L^(-Bper)*
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ sourceTest ν*
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ targetTest ν := by
    intro ν hν
    have hMem := (source_original_two_block_probe_pattern_mem434
      blockA blockB m ν.1 ν.2).mp hν
    obtain ⟨za,hza⟩ := hMem.1
    obtain ⟨zb,hzb⟩ := hMem.2.2.1
    let iA : ν.1 := ⟨za,hza⟩
    let iB : ν.2 := ⟨zb,hzb⟩
    have hEA := hEnds (loB iA.val.1) (hLoLarge iA.val.1)
    have hEB := hEnds (loB iB.val.1) (hLoLarge iB.val.1)
    have hResult := hGlobal x Y Hprime data sep hVbig
      blockA blockB hDisjoint m hm ν hν Q h h hh hh xi hxi hXi
      hQupper hLdyad hBIG J ell hmJ
      iA iB (loB iA.val.1) (hiB iA.val.1) (loB iB.val.1) (hiB iB.val.1)
      hEA.1 hEB.1 (hLoLeHi iA.val.1) (hLoLeHi iB.val.1)
      (hBigUpper iA.val.1) (hBigUpper iB.val.1)
      (hLoLarge iA.val.1) (hLoLarge iB.val.1)
      hEA.2.1 hEB.2.1 hEA.2.2 hEB.2.2
      (hBigFull iA.val.1) (hBigFull iB.val.1)
      hTbLower hTbUpper rfl rfl rfl ζ (theta ν) k hZeta4 hQlower
      (c ν) (hDivisor ν hν) (orientation ν) (hOrientation ν hν)
      (sigma ν) (tau ν) (sourceTest ν) (targetTest ν)
    exact hResult
  have hSign : ∀ ν ∈ family, ‖sign ν‖=1 := by
    intro ν hν
    dsimp only [sign]
    rw [norm_mul]
    split_ifs <;> simp
  let term := fun ν : SourceOriginalProbePattern434 G m =>
    sign ν * sourceOriginalB26PermutedFullPairing434
      data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
      sourceTest targetTest ν
  have hEach (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
      ‖term ν‖^2 ≤ (1:ℝ)^2*L^(-Bper) := by
    have hProduct : sourceOriginalB26FullActiveEnergy434
        data J ell m hmJ sourceTest ν *
        sourceOriginalB26FullActiveEnergy434 data J ell m hmJ targetTest ν ≤ 1 :=
      (mul_le_mul_of_nonneg_right (hES ν hν).2 (hET ν hν).1).trans
        (by simpa using (hET ν hν).2)
    have hN : ‖term ν‖^2 = ‖sourceOriginalB26PermutedFullPairing434
        data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
        sourceTest targetTest ν‖^2 := by
      dsimp only [term]
      rw [norm_mul,hSign ν hν,one_mul]
    rw [hN]
    have hh := (hPerNu ν hν).trans
      ((le_of_eq (mul_assoc _ _ _)).trans
        (mul_le_mul_of_nonneg_left hProduct (Real.rpow_nonneg hLp.le _)))
    simpa only [one_pow,one_mul,mul_one] using hh
  have hSquare := source_original_true_finite_weighted_minor_square434
    family term (fun _ => (1:ℝ)) (L^(-Bper)) (Real.rpow_nonneg hLp.le _)
    (by intro ν hν;norm_num) hEach
  have hCard : (family.card:ℝ) ≤ (2:ℝ)^(m*(blockA.card+blockB.card)) := by
    exact_mod_cast source_original_two_block_probe_pattern_card434 blockA blockB m
  have hCardSq := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) family.card) hCard 2
  have hTotal : ‖∑ ν ∈ family,term ν‖^2 ≤
      ((2:ℝ)^(m*(blockA.card+blockB.card)))^2*L^(-Bper) := by
    have hh : ‖∑ ν ∈ family,term ν‖^2 ≤ (family.card:ℝ)^2*L^(-Bper) := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hSquare
    exact hh.trans (mul_le_mul_of_nonneg_right hCardSq (Real.rpow_nonneg hLp.le _))
  have hBlocks : blockA.card+blockB.card ≤ Fintype.card G := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_univ _
  have hBlocksReal : (((blockA.card+blockB.card):ℕ):ℝ) ≤ (Fintype.card G:ℝ) := by
    exact_mod_cast hBlocks
  have hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ cfg.C0*Real.log L :=
    hBlocksReal.trans data.hBigGroups
  have hPower := source_original_probe_two_power_log_bound434
    blockA blockB m L cfg.C0 hL hGroups
  have hmE : (m:ℝ)*cfg.C0*Real.log 2 ≤ E := by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) cfg.hC0
    · exact Real.log_nonneg (by norm_num)
  have hPowBound : (2:ℝ)^(m*(blockA.card+blockB.card)) ≤ L^E :=
    hPower.trans (Real.rpow_le_rpow_of_exponent_le hL hmE)
  have hSquared := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2^(m*(blockA.card+blockB.card)))
    hPowBound 2
  have hAbsorb : ((2:ℝ)^(m*(blockA.card+blockB.card)))^2 * L^(-Bper) ≤
      L^(-Bgoal) := by
    calc
      _ ≤ (L^E)^2*L^(-Bper) :=
        mul_le_mul_of_nonneg_right hSquared (Real.rpow_nonneg hLp.le _)
      _ = L^(2*E-Bper) := by
        rw [← Real.rpow_two,← Real.rpow_mul hLp.le,← Real.rpow_add hLp]
        congr 1
        ring
      _ = L^(-Bgoal) := by
        congr 1
        dsimp [Bper]
        ring
  exact hTotal.trans hAbsorb
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26HomogeneousAllNuComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 44000000

/-- Applicable genuine-family B26 CLEAN comparison with explicit compatible Q/h/xi, all shared endpoint signs, both endpoint permutations, and a threshold before every moving full prime array. RAW and auxiliary-ban correction are separate. --/
theorem eventually_source_original_B26_HOMOGENEOUS_ALL_NU_COMPARISON434
    (cfg : SourceComparisonFixed434)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (J ell : ℕ) (hmJ : m ≤ J)
      (ζ : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (hDivisor : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<c ν)
      (hOrientation : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation ν=1 ∨ orientation ν= -1)
      (hZeta : |ζ| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
      (ES ET : ℝ) (hES0 : 0 ≤ ES) (hET0 : 0 ≤ ET)
      (sourceTest targetTest :
        (ν : SourceOriginalProbePattern434 G m) →
        ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
      (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        0 ≤ sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ sourceTest ν ∧
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ sourceTest ν ≤ ES)
      (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        0 ≤ sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ targetTest ν ∧
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ targetTest ν ≤ ET)
      (epsSrc epsTgt : Bool),
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let shared := fun ν : SourceOriginalProbePattern434 G m =>
      ((Fintype.card ι)*J) + ∑ g : G,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 G m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    ‖∑ ν ∈ family,
      sign ν * sourceOriginalB26PermutedFullPairing434
        data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
        sourceTest targetTest ν‖^2 ≤ L^(-Bgoal)*ES*ET := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  have hE : 0 ≤ E := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) cfg.hC0)
    (Real.log_nonneg (by norm_num))
  let Bper : ℝ := Bgoal+2*E
  have hPer : 0 ≤ Bper := by dsimp [Bper];linarith
  obtain ⟨Cfactor,Cq,Cs,C4,Cxi,Bsave,D,H,
    hBsave,hD,hH,hSum,hFactor,hMinor,hQexp,hCs,hC4,hFreq,hWidth,hDrop⟩ :=
    source_original_aligned_comparison_MODULUS_exponents434
      cfg Bper dscale Cfreq Ck hPer hd hCk
  have hWidth' : Bsave+((4*Cq+C4:ℕ):ℝ) ≤ H := by linarith
  obtain ⟨Y0,hGlobalEvent⟩ :=
    eventually_source_original_B26_PERMUTED_COMPARISON434
      cfg Cq Cxi Cs C4 Cfactor gamma dscale D Bsave H Bper
      hgamma hd hD hBsave hH hCs hC4 hWidth' hDrop hFactor hMinor hSum
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hGlobalEvent,
    eventually_source_original_ALIGNED_physical_choices434
      Cq Cxi D Ck H gamma cfg.cexp Y0 hD hCk hH hgamma hc hQexp,
    eventually_ge_atTop (1:ℝ)] with L hGlobal hChoices hL
  have hLp : 0 < L := by linarith
  let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  obtain ⟨hQpos,hQlower,hQupper,hh,hwidth,hxi,hXi,hLdyad,hEnds,hPrime,hModes⟩ :=
    hChoices
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J ell hmJ ζ k c theta orientation hDivisor hOrientation hZeta hk
    sigma tau ES ET hES0 hET0 sourceTest targetTest hES hET epsSrc epsTgt
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J) + ∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  refine ⟨hModes k hk,?_⟩
  have hTbUpper : ∀ g, ∀ p ∈ data.Tb g, (p:ℝ) ≤ Real.exp (L^dscale) := by
    intro g p hp
    have hBand := source_original_source03_big_band_upper434
      cfg x L Y Hprime data dscale loB hiB hBigFull hBigUpper
    exact (hBand g p hp).2
  have hBIG : ∀ g, ∀ p ∈ data.Tb g, Q^2<p :=
    fun g p hp => hPrime p (hTbLower g p hp)
  have hZeta4 : |ζ| ≤ L^C4 := by
    calc
      _ ≤ L^Cfreq := hZeta
      _ ≤ L^(C4:ℝ) := Real.rpow_le_rpow_of_exponent_le hL hFreq
      _ = L^C4 := Real.rpow_natCast L C4
  have hPerNu : ∀ ν ∈ family,
      ‖sourceOriginalB26PermutedFullPairing434
        data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
        sourceTest targetTest ν‖^2 ≤
      L^(-Bper)*
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ sourceTest ν*
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ targetTest ν := by
    intro ν hν
    have hMem := (source_original_two_block_probe_pattern_mem434
      blockA blockB m ν.1 ν.2).mp hν
    obtain ⟨za,hza⟩ := hMem.1
    obtain ⟨zb,hzb⟩ := hMem.2.2.1
    let iA : ν.1 := ⟨za,hza⟩
    let iB : ν.2 := ⟨zb,hzb⟩
    have hEA := hEnds (loB iA.val.1) (hLoLarge iA.val.1)
    have hEB := hEnds (loB iB.val.1) (hLoLarge iB.val.1)
    have hResult := hGlobal x Y Hprime data sep hVbig
      blockA blockB hDisjoint m hm ν hν Q h h hh hh xi hxi hXi
      hQupper hLdyad hBIG J ell hmJ
      iA iB (loB iA.val.1) (hiB iA.val.1) (loB iB.val.1) (hiB iB.val.1)
      hEA.1 hEB.1 (hLoLeHi iA.val.1) (hLoLeHi iB.val.1)
      (hBigUpper iA.val.1) (hBigUpper iB.val.1)
      (hLoLarge iA.val.1) (hLoLarge iB.val.1)
      hEA.2.1 hEB.2.1 hEA.2.2 hEB.2.2
      (hBigFull iA.val.1) (hBigFull iB.val.1)
      hTbLower hTbUpper rfl rfl rfl ζ (theta ν) k hZeta4 hQlower
      (c ν) (hDivisor ν hν) (orientation ν) (hOrientation ν hν)
      (sigma ν) (tau ν) (sourceTest ν) (targetTest ν)
    exact hResult
  have hSign : ∀ ν ∈ family, ‖sign ν‖=1 := by
    intro ν hν
    dsimp only [sign]
    rw [norm_mul]
    split_ifs <;> simp
  let term := fun ν : SourceOriginalProbePattern434 G m =>
    sign ν * sourceOriginalB26PermutedFullPairing434
      data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
      sourceTest targetTest ν
  have hESET : 0 ≤ ES*ET := mul_nonneg hES0 hET0
  have hEach (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
      ‖term ν‖^2 ≤ (1:ℝ)^2*(L^(-Bper)*(ES*ET)) := by
    have hProduct : sourceOriginalB26FullActiveEnergy434
        data J ell m hmJ sourceTest ν *
        sourceOriginalB26FullActiveEnergy434 data J ell m hmJ targetTest ν ≤ ES*ET :=
      mul_le_mul (hES ν hν).2 (hET ν hν).2 (hET ν hν).1 hES0
    have hN : ‖term ν‖^2 = ‖sourceOriginalB26PermutedFullPairing434
        data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k sigma tau
        sourceTest targetTest ν‖^2 := by
      dsimp only [term]
      rw [norm_mul,hSign ν hν,one_mul]
    rw [hN]
    have hh := (hPerNu ν hν).trans
      ((le_of_eq (mul_assoc _ _ _)).trans
        (mul_le_mul_of_nonneg_left hProduct (Real.rpow_nonneg hLp.le _)))
    simpa only [one_pow,one_mul,mul_one] using hh
  have hSquare := source_original_true_finite_weighted_minor_square434
    family term (fun _ => (1:ℝ)) (L^(-Bper)*(ES*ET))
    (mul_nonneg (Real.rpow_nonneg hLp.le _) hESET)
    (by intro ν hν;norm_num) hEach
  have hCard : (family.card:ℝ) ≤ (2:ℝ)^(m*(blockA.card+blockB.card)) := by
    exact_mod_cast source_original_two_block_probe_pattern_card434 blockA blockB m
  have hCardSq := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) family.card) hCard 2
  have hTotal : ‖∑ ν ∈ family,term ν‖^2 ≤
      ((2:ℝ)^(m*(blockA.card+blockB.card)))^2*(L^(-Bper)*(ES*ET)) := by
    have hh : ‖∑ ν ∈ family,term ν‖^2 ≤ (family.card:ℝ)^2*(L^(-Bper)*(ES*ET)) := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hSquare
    exact hh.trans (mul_le_mul_of_nonneg_right hCardSq
      (mul_nonneg (Real.rpow_nonneg hLp.le _) hESET))
  have hBlocks : blockA.card+blockB.card ≤ Fintype.card G := by
    rw [← Finset.card_union_of_disjoint hDisjoint]
    exact Finset.card_le_univ _
  have hBlocksReal : (((blockA.card+blockB.card):ℕ):ℝ) ≤ (Fintype.card G:ℝ) := by
    exact_mod_cast hBlocks
  have hGroups : (((blockA.card+blockB.card):ℕ):ℝ) ≤ cfg.C0*Real.log L :=
    hBlocksReal.trans data.hBigGroups
  have hPower := source_original_probe_two_power_log_bound434
    blockA blockB m L cfg.C0 hL hGroups
  have hmE : (m:ℝ)*cfg.C0*Real.log 2 ≤ E := by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) cfg.hC0
    · exact Real.log_nonneg (by norm_num)
  have hPowBound : (2:ℝ)^(m*(blockA.card+blockB.card)) ≤ L^E :=
    hPower.trans (Real.rpow_le_rpow_of_exponent_le hL hmE)
  have hSquared := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2^(m*(blockA.card+blockB.card)))
    hPowBound 2
  have hAbsorb : ((2:ℝ)^(m*(blockA.card+blockB.card)))^2 * L^(-Bper) ≤
      L^(-Bgoal) := by
    calc
      _ ≤ (L^E)^2*L^(-Bper) :=
        mul_le_mul_of_nonneg_right hSquared (Real.rpow_nonneg hLp.le _)
      _ = L^(2*E-Bper) := by
        rw [← Real.rpow_two,← Real.rpow_mul hLp.le,← Real.rpow_add hLp]
        congr 1
        ring
      _ = L^(-Bgoal) := by
        congr 1
        dsimp [Bper]
        ring
  calc
    _ ≤ ((2:ℝ)^(m*(blockA.card+blockB.card)))^2*(L^(-Bper)*(ES*ET)) := hTotal
    _ = (((2:ℝ)^(m*(blockA.card+blockB.card)))^2*L^(-Bper))*(ES*ET) := by ring
    _ ≤ L^(-Bgoal)*(ES*ET) := mul_le_mul_of_nonneg_right hAbsorb hESET
    _ = L^(-Bgoal)*ES*ET := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26PermutationMean -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

theorem source_original_B26_big_permutation_mass_nonneg434
    {G : Type} [Fintype G] [DecidableEq G] (M : ℕ) :
    0 ≤ bigEndpointPairMass (BG := G) M := by
  unfold bigEndpointPairMass
  exact Finset.prod_nonneg (fun _ _ =>
    (Green64SmallHaar.permutationPairMass_positive M).le)

theorem source_original_B26_big_permutation_mass_total434
    {G : Type} [Fintype G] [DecidableEq G] (M : ℕ) :
    (∑ st : BigGroupPerm (BG := G) M × BigGroupPerm (BG := G) M,
      bigEndpointPairMass (BG := G) M) = 1 := by
  have h : bigEndpointPairMass (BG := G) M *
      (Fintype.card (BigGroupPerm (BG := G) M) : ℝ)^2 = 1 := by
    have hf : (M.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
    simp only [bigEndpointPairMass,Green64SmallHaar.permutationPairMass,
      BigGroupPerm,Fintype.card_pi,Fintype.card_perm,Fintype.card_fin,Nat.cast_prod]
    rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
    simp [hf]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_prod,Nat.cast_mul]
  nlinarith [h]

/-- The actual BIG double-permutation mean has total mass one.
This finite integration lemma is instantiated with the proved arithmetic
comparison; it does not assume any independence of the two permutations. -/
theorem source_original_B26_big_permutation_mean_square434
    {G : Type} [Fintype G] [DecidableEq G] (M : ℕ)
    (z : BigGroupPerm (BG := G) M → BigGroupPerm (BG := G) M → ℂ)
    (eps ES ET : ℝ) (heps : 0 ≤ eps) (hES : 0 ≤ ES) (hET : 0 ≤ ET)
    (hz : ∀ sigma tau, ‖z sigma tau‖^2 ≤ eps*ES*ET) :
    ‖(bigEndpointPairMass (BG := G) M : ℂ) *
      ∑ sigma : BigGroupPerm (BG := G) M,
        ∑ tau : BigGroupPerm (BG := G) M,z sigma tau‖^2 ≤ eps*ES*ET := by
  classical
  let W := BigGroupPerm (BG := G) M × BigGroupPerm (BG := G) M
  have hmass := source_original_B26_big_permutation_mass_total434 (G := G) M
  have henergy (E : ℝ) :
      (∑ st : W,bigEndpointPairMass (BG := G) M*E) = E := by
    rw [← Finset.sum_mul]
    rw [hmass,one_mul]
  have hh := source_original_B26_homogeneous_shared_integration434
    (fun _ : W => bigEndpointPairMass (BG := G) M)
    (fun _ => ES) (fun _ => ET) (fun st => z st.1 st.2) eps
    (fun _ => source_original_B26_big_permutation_mass_nonneg434 M)
    (fun _ => hES) (fun _ => hET) heps (fun st => hz st.1 st.2)
  rw [henergy ES,henergy ET] at hh
  simpa only [W,Fintype.sum_prod_type,Finset.mul_sum] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26AveragedAllNuComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 44000000

/-- Applicable genuine-family B26 CLEAN comparison with explicit compatible Q/h/xi, all shared endpoint signs, both endpoint permutations, and a threshold before every moving full prime array. RAW and auxiliary-ban correction are separate. --/
theorem eventually_source_original_B26_AVERAGED_ALL_NU_COMPARISON434
    (cfg : SourceComparisonFixed434)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (J ell : ℕ) (hmJ : m ≤ J)
      (ζ : ℝ) (k : ℤ)
      (c : SourceOriginalProbePattern434 G m → ℕ)
      (theta : SourceOriginalProbePattern434 G m → ℝ)
      (orientation : SourceOriginalProbePattern434 G m → ℤ)
      (hDivisor : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m, 0<c ν)
      (hOrientation : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        orientation ν=1 ∨ orientation ν= -1)
      (hZeta : |ζ| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (ES ET : ℝ) (hES0 : 0 ≤ ES) (hET0 : 0 ≤ ET)
      (sourceTest targetTest :
        (ν : SourceOriginalProbePattern434 G m) →
        ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
      (hES : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        0 ≤ sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ sourceTest ν ∧
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ sourceTest ν ≤ ES)
      (hET : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        0 ≤ sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ targetTest ν ∧
        sourceOriginalB26FullActiveEnergy434
          data J ell m hmJ targetTest ν ≤ ET)
      (epsSrc epsTgt : Bool),
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    let shared := fun ν : SourceOriginalProbePattern434 G m =>
      ((Fintype.card ι)*J) + ∑ g : G,
        (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
    let sign := fun ν : SourceOriginalProbePattern434 G m =>
      (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
      (if epsTgt then (-1:ℂ)^(shared ν) else 1)
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    ‖(bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
      ∑ sigma : BigGroupPerm (BG := G) (J+ell),
      ∑ tau : BigGroupPerm (BG := G) (J+ell),
      ∑ ν ∈ family,
      sign ν * sourceOriginalB26PermutedFullPairing434
        data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k (fun _ => sigma) (fun _ => tau)
        sourceTest targetTest ν‖^2 ≤ L^(-Bgoal)*ES*ET := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_HOMOGENEOUS_ALL_NU_COMPARISON434
      cfg gamma dscale Bgoal Cfreq Ck hgamma hd hGoal hCk
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  filter_upwards [hEvent,eventually_ge_atTop (1:ℝ)] with L hMain hL
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm J ell hmJ ζ k c theta orientation hDivisor hOrientation hZeta hk
    ES ET hES0 hET0 sourceTest targetTest hES hET epsSrc epsTgt
  classical
  let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J) + ∑ g : G,
      (sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  let z := fun (sigma tau : BigGroupPerm (BG := G) (J+ell)) =>
    ∑ ν ∈ family,sign ν * sourceOriginalB26PermutedFullPairing434
      data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ c theta orientation k
      (fun _ => sigma) (fun _ => tau) sourceTest targetTest ν
  have hz (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
      k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
      ‖z sigma tau‖^2 ≤ L^(-Bgoal)*ES*ET :=
    hMain x Y Hprime data sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge
      hTbLower hVbig blockA blockB hDisjoint m hm J ell hmJ ζ k c theta orientation
      hDivisor hOrientation hZeta hk (fun _ => sigma) (fun _ => tau)
      ES ET hES0 hET0 sourceTest targetTest hES hET epsSrc epsTgt
  refine ⟨(hz (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)).1,?_⟩
  exact source_original_B26_big_permutation_mean_square434 (J+ell) z
    (L^(-Bgoal)) ES ET (Real.rpow_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans hL) _) hES0 hET0
    (fun sigma tau => (hz sigma tau).2)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26SectorActiveEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell : ℕ) (cap sizes : BG → ℕ)
variable (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
local notation "Small" => Green64SmallHaar.GroupState SP smallMod (J+ell)
local notation "SmallPerm" => Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bigMod sizes prime
local notation "Torus" => memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime

/-- Constant part of the actual frozen-sector mass. OLD residues have
counting measure; each OLD prime occurrence contributes its true mu,
and each group contributes precisely one sizes(g)! denominator. -/
def sourceOriginalB26SectorConstant434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℝ :=
  Green64SmallHaar.groupStateMass SP smallMod (J+ell) Vs *
    ∏ g : BG,(∏ i : Fin (sizes g),mu g (prime g i))/(sizes g).factorial

def sourceOriginalB26ActiveEnergy434
    (mu : (g : BG) → BP g → ℝ) (F : Active → ℂ) : ℝ :=
  ∑ a : Active,(∏ g : BG,∏ i : Fin (J+ell),mu g (a g i))*‖F a‖^2

def sourceOriginalB26SectorEnergy434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (U : Small → Active → Old → ℂ) : ℝ :=
  ∑ a : Active,∑ xs : Small,∑ t : Old,
    sourceOriginalB26SectorMass434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime Vs mu a * ‖U xs a t‖^2

theorem source_original_B26_sector_mass_factor434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (a : Active) :
    sourceOriginalB26SectorMass434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime Vs mu a =
    sourceOriginalB26SectorConstant434 SP smallMod BP J ell sizes prime Vs mu *
      ∏ g : BG,∏ i : Fin (J+ell),mu g (a g i) := by
  unfold sourceOriginalB26SectorMass434 sourceOriginalB26SectorConstant434
    bigGroupStateMass bigStateMass activeMass Green64Fock.fockMass
    Green64Fock.sourceAtomMu Green64Fock.lambdaMass sourceOriginalB26FrozenBigState434
  dsimp only
  rw [Finset.prod_mul_distrib]
  ring

theorem source_original_B26_sector_constant_nonneg434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p) :
    0 ≤ sourceOriginalB26SectorConstant434 SP smallMod BP J ell sizes prime Vs mu := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun g _ =>
      (Green64SmallHaar.stateMass_positive (smallMod g) (J+ell) (Vs g) (hVs g)).le)
  · apply Finset.prod_nonneg
    intro g _
    exact div_nonneg (Finset.prod_nonneg (fun i _ => (hmu g (prime g i)).le))
      (Nat.cast_nonneg _)

theorem source_original_B26_active_energy_nonneg434
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (F : Active → ℂ) :
    0 ≤ sourceOriginalB26ActiveEnergy434 BP J ell mu F := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (Finset.prod_nonneg (fun g _ =>
    Finset.prod_nonneg (fun i _ => (hmu g (a g i)).le))) (sq_nonneg _)

theorem source_original_B26_sector_energy_nonneg434
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (U : Small → Active → Old → ℂ) :
    0 ≤ sourceOriginalB26SectorEnergy434 SP smallMod BP bigMod
      J ell cap sizes hsizes prime Vs mu U := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro xs _
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (source_original_B26_sector_mass_nonneg434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime Vs hVs mu hmu a) (sq_nonneg _)

/-- Both original physical normalizations have been kept. This is the
precise energy bound needed between the two SMALL Fourier endpoint maps. -/
theorem source_original_B26_SMALL_OLD_FOURIER_ACTIVE_ENERGY434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (ss : SmallPerm) (U : Small → Active → Old → ℂ) :
    (sourceOriginalB26SectorConstant434 SP smallMod BP J ell sizes prime Vs mu *
      (Fintype.card Torus:ℝ)) *
      (∑ d : Shared,∑ psi : AddChar Torus ℂ,
        sourceOriginalB26ActiveEnergy434 BP J ell mu
          (fun a => (AddChar.complexBasis Torus).repr
            (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
              J ell sizes prime q Vs ss d U a) psi)) ≤
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs *
      sourceOriginalB26SectorEnergy434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime Vs mu U := by
  have hh := source_original_B26_SMALL_OLD_FOURIER_ENERGY434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime q hq hq1 Vs hVs mu hmu ss U
  rw [sourceOriginalB26SectorEnergy434]
  simp_rw [source_original_B26_sector_mass_factor434] at hh ⊢
  simp only [sourceOriginalB26ActiveEnergy434,Finset.mul_sum] at hh ⊢
  convert hh using 1 <;> ring
end Green64FullPhysicalE

end

end

/-! ## SourceOriginalB26PhysicalTiltBilinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalB26TiltFreeDensity434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) (J ell m : ℕ) (pat : SourcePattern G J m)
    (r : (g : G) → BP g → ℝ)
    (sigma : BigGroupPerm (BG := G) (J+ell))
    (s : (g : G) → Fin (J+ell) → BP g) : ℝ :=
  ∏ g : G, ∏ i : Fin (J+ell),
    if i ∈ sourceBigShared J ell m pat g then 1
    else (r g (s g (sigma g i)))^2

/-- The endpoint-energy cost contains only free-slot density. Shared
densities are already part of the original tilted endpoint measure. -/
theorem source_original_B26_TILT_ENDPOINT_ENERGY_DENSITY434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)]
    (J ell m : ℕ) (pat : SourcePattern G J m)
    (mu r : (g : G) → BP g → ℝ)
    (s : (g : G) → Fin (J+ell) → BP g)
    (sigma : BigGroupPerm (BG := G) (J+ell)) :
    (∏ g : G,∏ i : Fin (J+ell),mu g (s g i)) *
      (sourceOriginalB26TiltEndpoint434 BP J ell m pat r sigma s)^2 =
    (∏ g : G,∏ i : Fin (J+ell),mu g (s g i)*(r g (s g i))^2) *
      sourceOriginalB26TiltFreeDensity434 BP J ell m pat r sigma s := by
  classical
  rw [← source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu s sigma,
    ← source_original_B26_endpoint_permutation_mass434 BP (J+ell)
      (fun g p => mu g p*(r g p)^2) s sigma]
  unfold sourceOriginalB26TiltEndpoint434 sourceOriginalB26TiltFreeDensity434
  simp only [← Finset.prod_pow,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ sourceBigShared J ell m pat g <;> simp only [hi,if_true,if_false] <;> ring

theorem source_original_B26_TILT_ENDPOINT_ENERGY434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)]
    (J ell m : ℕ) (pat : SourcePattern G J m)
    (mu r : (g : G) → BP g → ℝ)
    (sigma : BigGroupPerm (BG := G) (J+ell))
    (U : ((g : G) → Fin (J+ell) → BP g) → ℂ) :
    sourceOriginalB26ActiveEnergy434 BP J ell mu
      (fun s => (sourceOriginalB26TiltEndpoint434 BP J ell m pat r sigma s:ℂ)*U s) =
    ∑ s : ((g : G) → Fin (J+ell) → BP g),
      (∏ g : G,∏ i : Fin (J+ell),mu g (s g i)*(r g (s g i))^2) *
      sourceOriginalB26TiltFreeDensity434 BP J ell m pat r sigma s * ‖U s‖^2 := by
  classical
  unfold sourceOriginalB26ActiveEnergy434
  apply Finset.sum_congr rfl
  intro s _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [← mul_assoc,source_original_B26_TILT_ENDPOINT_ENERGY_DENSITY434]

/-- Exact bilinear transfer for the literal physical mu-tilde, retaining
an arbitrary joint K(s,t). This is an identity, not an assumed Schur cap. -/
theorem source_original_B26_PHYSICAL_TILT_BILINEAR434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ)
    (hb : ∀ g p,0 < physicalSourceBaseline BP modulus q N g p)
    (J ell m : ℕ) (pat : SourcePattern G J m)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (U F : ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (K : ((g : G) → Fin (J+ell) → BP g) →
      ((g : G) → Fin (J+ell) → BP g) → ℂ) :
    let mu := sourceOriginalJointHarmonicMu434 BP modulus V
    let muTilt := physicalSourceMuTilde BP modulus q N V
    let r := sourceOriginalB26PhysicalTiltRoot434 BP modulus q N
    (∑ s,∑ t,
      ((∏ g : G,∏ i : Fin (J+ell),muTilt g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m muTilt pat s t sigma tau *
      (starRingEnd ℂ) (U s)*F t*K s t) =
    ∑ s,∑ t,
      ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau *
      (starRingEnd ℂ)
        ((sourceOriginalB26TiltEndpoint434 BP J ell m pat r sigma s:ℂ)*U s) *
      ((sourceOriginalB26TiltEndpoint434 BP J ell m pat r tau t:ℂ)*F t)*K s t := by
  classical
  dsimp only
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [source_original_B26_PHYSICAL_TILT_JOINT_DENSITY434
    BP modulus q N V hb J ell m pat s t sigma tau]
  simp only [map_mul,Complex.conj_ofReal]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalTiltBaseline -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem source_original_B26_visit_eta_unit434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N i : ℕ) :
    0 ≤ sourceVisitEta q N i ∧ sourceVisitEta q N i ≤ 1 := by
  have hs0 := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q ≤ 1 := by simpa using Real.sqrt_le_sqrt hq1
  unfold sourceVisitEta sourceVisitQ
  split_ifs <;> constructor <;> linarith only [hq,hq1,hs0,hs1]

theorem source_original_B26_visit_sum_unit434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i ∧
    (∑ i ∈ Finset.range (N+1),sourceVisitEta q N i) ≤ ((N+1:ℕ):ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ =>
      (source_original_B26_visit_eta_unit434 q hq hq1 N i).1)
  · calc
      _ ≤ ∑ _i ∈ Finset.range (N+1),(1:ℝ) :=
        Finset.sum_le_sum (fun i _ =>
          (source_original_B26_visit_eta_unit434 q hq hq1 N i).2)
      _ = _ := by simp

/-- The actual baseline includes all N+1 visits, including both boundary
sqrt(q) terms. No probability normalization is imposed on mu-tilde. -/
theorem source_original_B26_physical_baseline_half434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (g : G) (p : BP g)
    (hsize : 2*((N+1:ℕ):ℝ) ≤ (modulus g p:ℝ)) :
    (1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q N g p ∧
    physicalSourceBaseline BP modulus q N g p ≤ 1 := by
  have hp : 0 < (modulus g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  obtain ⟨hA0,hA⟩ := source_original_B26_visit_sum_unit434 q hq hq1 N
  have hhalf : (∑ i ∈ Finset.range (N+1),sourceVisitEta q N i) /
      (modulus g p:ℝ) ≤ 1/2 := (div_le_iff₀ hp).mpr (by linarith only [hA,hsize])
  have hnonneg := div_nonneg hA0 hp.le
  dsimp [physicalSourceBaseline]
  constructor <;> linarith only [hhalf,hnonneg]

/-- Original source depth N=2 ceil(L^0.52). The threshold depends only
on c, before the moving prime alphabet, group count, J, and tests. -/
theorem eventually_source_original_B26_visits_below_BIG434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ p : ℕ,
      Real.exp (L^c) ≤ (p:ℝ) →
      2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) ≤ (p:ℝ) := by
  obtain ⟨L0,hLarge⟩ :=
    source_original_circle_eventual_exp_dominance434 c 2 0 hc (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop L0] with L hL0
  obtain ⟨hL4,hExp⟩ := hLarge L hL0
  have hL : 1 ≤ L := by linarith only [hL4]
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hpow : L^(0.52:ℝ) ≤ L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0.52:ℝ) ≤ 1)
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hLp.le (0.52:ℝ))).le
  have hExp' : 4*L^2 ≤ Real.exp (L^c) := by
    simpa using hExp 1 (by norm_num) (by simp)
  intro p hp
  have hN : 2*((2*Nat.ceil (L^(0.52:ℝ))+1:ℕ):ℝ) ≤ 4*L+6 := by
    push_cast
    linarith only [hceil,hpow]
  have hpoly : 4*L+6 ≤ 4*L^2 := by nlinarith only [hL4,sq_nonneg (L-4)]
  exact hN.trans (hpoly.trans (hExp'.trans hp))

theorem source_original_B26_physical_tilt_root_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (g : G) (p : BP g)
    (hb : (1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q N g p) :
    (sourceOriginalB26PhysicalTiltRoot434 BP modulus q N g p)^2 ≤ 2 := by
  have hb0 : 0 < physicalSourceBaseline BP modulus q N g p := by linarith only [hb]
  rw [sourceOriginalB26PhysicalTiltRoot434,Real.sq_sqrt (inv_nonneg.mpr hb0.le)]
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hb0).mpr (by linarith only [hb])
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalTiltEnergy -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalB26TiltDensityExponent434 (ell tmax : ℕ) (C0 : ℝ) : ℝ :=
  C0*Real.log ((2:ℝ)^(ell+tmax))

theorem source_original_B26_tilt_density_exponent_nonneg434
    (ell tmax : ℕ) (C0 : ℝ) (hC0 : 0 ≤ C0) :
    0 ≤ sourceOriginalB26TiltDensityExponent434 ell tmax C0 :=
  mul_nonneg hC0 (Real.log_nonneg (one_le_pow₀ (by norm_num)))

/-- Only the literal unshared slots are charged. Shared density is
already in the physical endpoint energy, uniformly for every J. -/
theorem source_original_B26_tilt_free_density_count434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) (J ell m tmax : ℕ) (hmJ : m ≤ J) (hm : m ≤ tmax)
    (ν : SourceOriginalProbePattern434 G m)
    (r : (g : G) → BP g → ℝ) (hr : ∀ g p,(r g p)^2 ≤ 2)
    (sigma : BigGroupPerm (BG := G) (J+ell))
    (s : (g : G) → Fin (J+ell) → BP g) :
    sourceOriginalB26TiltFreeDensity434 BP J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) r sigma s ≤
      ((2:ℝ)^(ell+tmax))^(Fintype.card G) := by
  classical
  let E := sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
  have hEach (g : G) :
      (∏ i : Fin (J+ell),if i ∈ E g then 1 else (r g (s g (sigma g i)))^2) ≤
      (2:ℝ)^(ell+tmax) := by
    have hsplit := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin (J+ell) => i ∈ E g)
      (fun i => if i ∈ E g then (1:ℝ) else (r g (s g (sigma g i)))^2)
    have heq :
        (∏ i : Fin (J+ell),if i ∈ E g then 1 else (r g (s g (sigma g i)))^2) =
        ∏ i : {i : Fin (J+ell) // i ∉ E g},(r g (s g (sigma g i.val)))^2 := by
      calc
        _ = ∏ i : {i : Fin (J+ell) // i ∉ E g},
            if i.val ∈ E g then 1 else (r g (s g (sigma g i.val)))^2 := by
          simpa using hsplit.symm
        _ = _ := by
          apply Finset.prod_congr rfl
          intro i _
          rw [if_neg i.property]
    rw [heq]
    have hc : Fintype.card {i : Fin (J+ell) // i ∉ E g} =
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_congr (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g)).symm
    calc
      _ ≤ ∏ _i : {i : Fin (J+ell) // i ∉ E g},(2:ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hr g _)
      _ = (2:ℝ)^(sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) := by simp [hc]
      _ ≤ (2:ℝ)^(ell+tmax) := pow_le_pow_right₀ (by norm_num)
        ((source_original_probe_free_mark_cap434 J ell m hmJ ν g).trans (Nat.add_le_add_left hm ell))
  unfold sourceOriginalB26TiltFreeDensity434
  calc
    _ ≤ ∏ _g : G,(2:ℝ)^(ell+tmax) := Finset.prod_le_prod₀
      (fun g _ => Finset.prod_nonneg (fun i _ => by split_ifs <;> positivity))
      (fun g _ => hEach g)
    _ = _ := by simp

/-- The number of groups may grow with L. The exponent is fixed before
J and before conductor/mesh choices; no finite-cell count occurs. -/
theorem source_original_B26_tilt_free_density_polynomial434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) (J ell m tmax : ℕ) (hmJ : m ≤ J) (hm : m ≤ tmax)
    (ν : SourceOriginalProbePattern434 G m)
    (r : (g : G) → BP g → ℝ) (hr : ∀ g p,(r g p)^2 ≤ 2)
    (sigma : BigGroupPerm (BG := G) (J+ell))
    (s : (g : G) → Fin (J+ell) → BP g)
    (C0 L : ℝ) (hL : 1 ≤ L)
    (hGroups : (Fintype.card G:ℝ) ≤ C0*Real.log L) :
    sourceOriginalB26TiltFreeDensity434 BP J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) r sigma s ≤
      L^(sourceOriginalB26TiltDensityExponent434 ell tmax C0) := by
  let K : ℝ := 2^(ell+tmax)
  have hK1 : 1 ≤ K := one_le_pow₀ (by norm_num)
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hLp : 0 < L := zero_lt_one.trans_le hL
  calc
    _ ≤ K^(Fintype.card G) :=
      source_original_B26_tilt_free_density_count434 BP J ell m tmax hmJ hm ν r hr sigma s
    _ = Real.exp (Real.log K*(Fintype.card G:ℝ)) := by
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos hK]
    _ ≤ Real.exp (Real.log K*(C0*Real.log L)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hGroups (Real.log_nonneg hK1))
    _ = L^(sourceOriginalB26TiltDensityExponent434 ell tmax C0) := by
      rw [Real.rpow_def_of_pos hLp]
      congr 1
      dsimp [sourceOriginalB26TiltDensityExponent434,K]
      ring

/-- Quantitative endpoint estimate for the exact physical tilted law.
No loss involving the shared count J is inserted. -/
theorem source_original_B26_PHYSICAL_TILT_ENDPOINT_CAP434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ) (hV : ∀ g,0 < V g)
    (hb : ∀ g p,(1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q N g p)
    (J ell m tmax : ℕ) (hmJ : m ≤ J) (hm : m ≤ tmax)
    (ν : SourceOriginalProbePattern434 G m)
    (sigma : BigGroupPerm (BG := G) (J+ell))
    (U : ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (C0 L : ℝ) (hL : 1 ≤ L)
    (hGroups : (Fintype.card G:ℝ) ≤ C0*Real.log L) :
    sourceOriginalB26ActiveEnergy434 BP J ell
      (sourceOriginalJointHarmonicMu434 BP modulus V)
      (fun s => (sourceOriginalB26TiltEndpoint434 BP J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
        (sourceOriginalB26PhysicalTiltRoot434 BP modulus q N) sigma s:ℂ)*U s) ≤
    L^(sourceOriginalB26TiltDensityExponent434 ell tmax C0) *
      sourceOriginalB26ActiveEnergy434 BP J ell
        (physicalSourceMuTilde BP modulus q N V) U := by
  classical
  have hb0 (g : G) (p : BP g) : 0 < physicalSourceBaseline BP modulus q N g p := by
    have hh := hb g p
    linarith only [hh]
  have hmu (g : G) (p : BP g) : 0 < physicalSourceMuTilde BP modulus q N V g p := by
    exact one_div_pos.mpr (mul_pos
      (mul_pos (hV g) (Nat.cast_pos.mpr (NeZero.pos _))) (hb0 g p))
  rw [source_original_B26_TILT_ENDPOINT_ENERGY434]
  simp_rw [← source_original_B26_PHYSICAL_TILT_ATOM434 BP modulus q N V _ _ (hb0 _ _)]
  unfold sourceOriginalB26ActiveEnergy434
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have hw : 0 ≤ ∏ g : G,∏ i : Fin (J+ell),physicalSourceMuTilde BP modulus q N V g (s g i) :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => (hmu g _).le))
  have hh := source_original_B26_tilt_free_density_polynomial434 BP J ell m tmax hmJ hm ν
    (sourceOriginalB26PhysicalTiltRoot434 BP modulus q N)
    (fun g p => source_original_B26_physical_tilt_root_bound434 BP modulus q N g p (hb g p))
    sigma s C0 L hL hGroups
  calc
    _ ≤ (∏ g : G,∏ i : Fin (J+ell),physicalSourceMuTilde BP modulus q N V g (s g i)) *
        L^(sourceOriginalB26TiltDensityExponent434 ell tmax C0) * ‖U s‖^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hw) (sq_nonneg _)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostReturnBaseline -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

def sourceOriginalGhostSourceVisits434 {R : Type} (q : ℝ) (N : ℕ)
    (positions : ℕ → R) : List (R × ℝ) :=
  List.ofFn (fun i : Fin (N+1) => (positions i,sourceVisitEta q N i))

theorem source_original_GHOST_SOURCE_visits_sum434
    {R : Type} (q : ℝ) (N : ℕ) (positions : ℕ → R) :
    ((sourceOriginalGhostSourceVisits434 q N positions).map Prod.snd).sum =
      ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i := by
  simp only [sourceOriginalGhostSourceVisits434,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i => sourceVisitEta q N i) (N+1)

theorem source_original_GHOST_SOURCE_visits_unit434
    {R : Type} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (positions : ℕ → R) :
    ∀ v ∈ sourceOriginalGhostSourceVisits434 q N positions,
      0 ≤ v.2 ∧ v.2 ≤ 1 := by
  intro v hv
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
  exact source_original_B26_visit_eta_unit434 q hq hq1 N i

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : BG) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]

/-- A never-active prime's once-born ghost factor, including its exact
original baseline and the TRUE density-coordinate birth mass V_g*mu_tilde.
This is the prime factor to be extracted from the full source chain;
the extraction from mixed E/G witnesses is a separate obligation. -/
def sourceOriginalPhysicalGhostReturnFactor434
    (q : ℝ) (N : ℕ) (Vb : BG → ℝ) (g : BG) (p : BP g)
    (positions : ℕ → ZMod (modulus g p)) : ℝ :=
  physicalSourceBaseline BP modulus q N g p *
    sourceOriginalGhostReturnChain434
      (sourceOriginalGhostSourceVisits434 q N positions)
      (Vb g * physicalSourceMuTilde BP modulus q N Vb g p)
      sourceOriginalGhostReturnVacuum434 .unborn

/-- The source baseline and source tilted measure cancel exactly;
both boundary sqrt(q) visits are retained. No non-return or
independence assumption on the positions is made. -/
theorem source_original_PHYSICAL_GHOST_RETURN_residue_average434
    (q : ℝ) (N : ℕ) (Vb : BG → ℝ) (g : BG) (p : BP g)
    (hV : Vb g ≠ 0)
    (hb : physicalSourceBaseline BP modulus q N g p ≠ 0)
    (positions : ℕ → ZMod (modulus g p)) :
    sourceOriginalPhysicalGhostReturnFactor434 BP modulus q N Vb g p positions =
      (∑ r : ZMod (modulus g p),
        sourceOriginalGhostReturnSurvival434
          (sourceOriginalGhostSourceVisits434 q N positions) r) /
        (modulus g p : ℝ) := by
  have hp : (modulus g p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (modulus g p)
  have hlam : Vb g * physicalSourceMuTilde BP modulus q N Vb g p =
      1/((modulus g p : ℝ)*physicalSourceBaseline BP modulus q N g p) := by
    unfold physicalSourceMuTilde
    field_simp
  have hh := source_original_GHOST_RETURN_BASELINE_residue_average434
    (sourceOriginalGhostSourceVisits434 q N positions)
    (by simpa only [ZMod.card,source_original_GHOST_SOURCE_visits_sum434,
      physicalSourceBaseline] using hb)
  simpa only [sourceOriginalPhysicalGhostReturnFactor434,hlam,ZMod.card,
    source_original_GHOST_SOURCE_visits_sum434,physicalSourceBaseline] using hh

/-- Applicable all-visit bound: at any source depth and for every
position path, the full once-born ghost prime factor is between zero
and one. There is no factor per visit and no fixed-label threshold. -/
theorem source_original_PHYSICAL_GHOST_RETURN_unit434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (Vb : BG → ℝ)
    (g : BG) (p : BP g) (hV : Vb g ≠ 0)
    (hb : physicalSourceBaseline BP modulus q N g p ≠ 0)
    (positions : ℕ → ZMod (modulus g p)) :
    0 ≤ sourceOriginalPhysicalGhostReturnFactor434 BP modulus q N Vb g p positions ∧
      sourceOriginalPhysicalGhostReturnFactor434 BP modulus q N Vb g p positions ≤ 1 := by
  rw [source_original_PHYSICAL_GHOST_RETURN_residue_average434 BP modulus q N Vb g p hV hb]
  have hp : (0:ℝ) < modulus g p := by exact_mod_cast NeZero.pos (modulus g p)
  have ht := source_original_GHOST_SOURCE_visits_unit434 q hq hq1 N positions
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun r _ =>
      (source_original_GHOST_RETURN_survival_unit434 _ ht r).1)) hp.le
  · apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ ∑ _r : ZMod (modulus g p),(1:ℝ) := Finset.sum_le_sum (fun r _ =>
        (source_original_GHOST_RETURN_survival_unit434 _ ht r).2)
      _ = _ := by simp

/-- Any moving finite collection of never-active primes carries no
cardinality loss, once its individual factors have actually been
separated. Separation from the original mixed chain is NOT assumed here. -/
theorem source_original_PHYSICAL_GHOST_RETURN_product_unit434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ) (Vb : BG → ℝ)
    (hV : ∀ g,Vb g ≠ 0)
    (hb : ∀ g p,physicalSourceBaseline BP modulus q N g p ≠ 0)
    (positions : (g : BG) → (p : BP g) → ℕ → ZMod (modulus g p))
    (s : Finset (Sigma BP)) :
    0 ≤ ∏ x ∈ s,sourceOriginalPhysicalGhostReturnFactor434 BP modulus q N Vb x.1 x.2
        (positions x.1 x.2) ∧
      (∏ x ∈ s,sourceOriginalPhysicalGhostReturnFactor434 BP modulus q N Vb x.1 x.2
        (positions x.1 x.2)) ≤ 1 := by
  have hu (x : Sigma BP) := source_original_PHYSICAL_GHOST_RETURN_unit434
    BP modulus q hq hq1 N Vb x.1 x.2 (hV x.1) (hb x.1 x.2) (positions x.1 x.2)
  exact ⟨Finset.prod_nonneg (fun x _ => (hu x).1),
    Finset.prod_le_one₀ (fun x _ => (hu x).1) (fun x _ => (hu x).2)⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalSinglePrimeChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (p : P)

/-- Literal singleton-prime restricted G operator on the physical pending
multiset. No abstract state transition is used in this definition. -/
def sourceOriginalPhysicalSinglePrimeG434 (eta V : ℝ) (mu : P → ℝ)
    (pending : Multiset (Atom P modulus)) (seen : Bool)
    (F : Multiset (Atom P modulus) → Bool → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (pending.toFinset.filter (fun z => z.2=0)) {p},
    if d.2.1=∅ ∨ seen=false then
      sourceOriginalGroupPrimeBirthWeight434 modulus
        (pending.toFinset.filter (fun z => z.2=0))
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun t => (mu t:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d) *
      F (sourceOriginalGhostPiecePending434 modulus pending.toFinset d.1.1 d.2.1)
        (seen || decide (d.2.1≠∅))
    else 0

theorem source_original_PHYSICAL_SINGLE_PRIME_G_pullback434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (F : Multiset (Atom P modulus) → Bool → ℂ) :
    sourceOriginalPhysicalSinglePrimeG434 modulus p eta V mu
      (sourceOriginalOnePrimePending434 modulus p shift s) (sourceOriginalOnePrimeSeen434 s) F =
    sourceOriginalOnePrimePhysicalRow434 modulus p shift eta V mu s F := by
  unfold sourceOriginalPhysicalSinglePrimeG434 sourceOriginalOnePrimePhysicalRow434
    sourceOriginalOnePrimeZero434
  congr 1

/-- Each entry is the true G visit strength followed by the integer
translation supplied by the fixed E-frame history. A last zero shift
retains the final G visit without inserting an extra E step. -/
def sourceOriginalPhysicalSinglePrimeChain434 (V : ℝ) (mu : P → ℝ) :
    List (ℝ × ℤ) →
    (Multiset (Atom P modulus) → Bool → ℂ) →
    Multiset (Atom P modulus) → Bool → ℂ
  | [],F => F
  | v::vs,F => fun pending seen =>
      sourceOriginalPhysicalSinglePrimeG434 modulus p v.1 V mu pending seen
        (fun out s => sourceOriginalPhysicalSinglePrimeChain434 V mu vs F
          (out.map (translateAtom v.2)) s)

def sourceOriginalSinglePrimeVisits434 (shift : ℤ) :
    List (ℝ × ℤ) → List (ZMod (modulus p) × ℝ)
  | [] => []
  | v::vs => (-(shift : ZMod (modulus p)),v.1) ::
      sourceOriginalSinglePrimeVisits434 (shift+v.2) vs

def sourceOriginalSinglePrimeEndShift434 (shift : ℤ) : List (ℝ × ℤ) → ℤ
  | [] => shift
  | v::vs => sourceOriginalSinglePrimeEndShift434 (shift+v.2) vs

theorem source_original_PHYSICAL_SINGLE_PRIME_translate434
    (shift step : ℤ) (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) :
    (sourceOriginalOnePrimePending434 modulus p shift s).map
        (translateAtom (modulus := modulus) step) =
      sourceOriginalOnePrimePending434 modulus p (shift+step) s := by
  cases s <;> simp [sourceOriginalOnePrimePending434,translateAtom,add_assoc]

/-- Exact whole-chain return representation in the original translated
pending coordinates, for an arbitrary joint pending/seen continuation. -/
theorem source_original_PHYSICAL_SINGLE_PRIME_chain_return434
    (V : ℝ) (mu : P → ℝ) (vs : List (ℝ × ℤ)) (shift : ℤ)
    (F : Multiset (Atom P modulus) → Bool → ℂ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) :
    sourceOriginalPhysicalSinglePrimeChain434 modulus p V mu vs F
      (sourceOriginalOnePrimePending434 modulus p shift s) (sourceOriginalOnePrimeSeen434 s) =
    sourceOriginalGhostReturnLiteralChain434 (sourceOriginalSinglePrimeVisits434 modulus p shift vs)
      (V*mu p) (fun t => F
        (sourceOriginalOnePrimePending434 modulus p (sourceOriginalSinglePrimeEndShift434 shift vs) t)
        (sourceOriginalOnePrimeSeen434 t)) s := by
  induction vs generalizing shift s with
  | nil => rfl
  | cons v vs ih =>
      dsimp only [sourceOriginalPhysicalSinglePrimeChain434,
        sourceOriginalSinglePrimeVisits434,sourceOriginalSinglePrimeEndShift434,
        sourceOriginalGhostReturnLiteralChain434]
      rw [source_original_PHYSICAL_SINGLE_PRIME_G_pullback434,
        source_original_PHYSICAL_SINGLE_PRIME_return_row434]
      congr 1
      funext t
      rw [source_original_PHYSICAL_SINGLE_PRIME_translate434]
      exact ih (shift+v.2) t

def sourceOriginalSinglePrimeVacuumObservation434 (H : Bool → ℂ)
    (pending : Multiset (Atom P modulus)) (seen : Bool) : ℂ :=
  if pending=0 then H seen else 0

theorem source_original_PHYSICAL_SINGLE_PRIME_vacuum_terminal434
    (shift : ℤ) (H : Bool → ℂ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) :
    sourceOriginalSinglePrimeVacuumObservation434 modulus H
      (sourceOriginalOnePrimePending434 modulus p shift s) (sourceOriginalOnePrimeSeen434 s) =
      sourceOriginalGhostReturnTerminal434 (H false) (H true) s := by
  cases s <;> simp [sourceOriginalSinglePrimeVacuumObservation434,
    sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434,sourceOriginalGhostReturnTerminal434]

/-- Exact complete marked vacuum pairing for the PHYSICAL singleton G
chain with all intervening integer E translations. -/
theorem source_original_PHYSICAL_SINGLE_PRIME_marked_vacuum434
    (V : ℝ) (mu : P → ℝ) (vs : List (ℝ × ℤ)) (shift : ℤ) (H : Bool → ℂ) :
    sourceOriginalPhysicalSinglePrimeChain434 modulus p V mu vs
      (sourceOriginalSinglePrimeVacuumObservation434 modulus H) 0 false =
      H false + (V*mu p:ℝ) *
        (sourceOriginalGhostReturnLoops434 (sourceOriginalSinglePrimeVisits434 modulus p shift vs):ℂ) *
        H true := by
  have h := source_original_PHYSICAL_SINGLE_PRIME_chain_return434
    modulus p V mu vs shift (sourceOriginalSinglePrimeVacuumObservation434 modulus H) .unborn
  simp only [source_original_PHYSICAL_SINGLE_PRIME_vacuum_terminal434] at h
  simp only [sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434] at h
  rw [h]
  exact (source_original_GHOST_RETURN_literal_chain_terminal434
    (sourceOriginalSinglePrimeVisits434 modulus p shift vs) (V*mu p) (H false) (H true)).2.2

theorem source_original_PHYSICAL_SINGLE_PRIME_visits_sum434
    (shift : ℤ) (vs : List (ℝ × ℤ)) :
    ((sourceOriginalSinglePrimeVisits434 modulus p shift vs).map Prod.snd).sum =
      (vs.map Prod.fst).sum := by
  induction vs generalizing shift with
  | nil => rfl
  | cons v vs ih => simp only [sourceOriginalSinglePrimeVisits434,List.map_cons,List.sum_cons,ih]

theorem source_original_PHYSICAL_SINGLE_PRIME_visits_unit434
    (vs : List (ℝ × ℤ)) (heta : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (shift : ℤ) :
    ∀ v ∈ sourceOriginalSinglePrimeVisits434 modulus p shift vs,0 ≤ v.2 ∧ v.2 ≤ 1 := by
  induction vs generalizing shift with
  | nil => simp [sourceOriginalSinglePrimeVisits434]
  | cons v vs ih =>
      intro w hw
      rcases List.mem_cons.mp hw with rfl|hw
      · exact heta v List.mem_cons_self
      · exact ih (fun z hz => heta z (List.mem_cons_of_mem v hz)) (shift+v.2) w hw

/-- Applicable envelope for the actual translated singleton chain.
The threshold is the explicit scalar baseline; no fixed bound on
number of visits or on the integer translation schedule is present. -/
theorem source_original_PHYSICAL_SINGLE_PRIME_baseline_envelope434
    (V : ℝ) (mu : P → ℝ) (vs : List (ℝ × ℤ)) (shift : ℤ)
    (heta : ∀ v ∈ vs,0 ≤ v.1 ∧ v.1 ≤ 1)
    (hb : 0 < 1-(vs.map Prod.fst).sum/(modulus p:ℝ))
    (hlam : V*mu p =
      1/((modulus p:ℝ)*(1-(vs.map Prod.fst).sum/(modulus p:ℝ))))
    (H : Bool → ℂ) (M : ℝ) (hH : ∀ s,‖H s‖ ≤ M) :
    ‖((1-(vs.map Prod.fst).sum/(modulus p:ℝ):ℝ):ℂ) *
      sourceOriginalPhysicalSinglePrimeChain434 modulus p V mu vs
        (sourceOriginalSinglePrimeVacuumObservation434 modulus H) 0 false‖ ≤ M := by
  have h := source_original_PHYSICAL_SINGLE_PRIME_chain_return434
    modulus p V mu vs shift (sourceOriginalSinglePrimeVacuumObservation434 modulus H) .unborn
  simp only [source_original_PHYSICAL_SINGLE_PRIME_vacuum_terminal434] at h
  simp only [sourceOriginalOnePrimePending434,sourceOriginalOnePrimeSeen434] at h
  rw [h,hlam]
  have hh := source_original_GHOST_RETURN_BASELINE_terminal_envelope434
    (sourceOriginalSinglePrimeVisits434 modulus p shift vs)
    (source_original_PHYSICAL_SINGLE_PRIME_visits_unit434 modulus p vs heta shift)
    (by simpa only [ZMod.card,source_original_PHYSICAL_SINGLE_PRIME_visits_sum434] using hb)
    (H false) (H true) M (hH false) (hH true)
  simpa only [ZMod.card,source_original_PHYSICAL_SINGLE_PRIME_visits_sum434] using hh
end Green64Analytic.CorrelationSquare

end

end

