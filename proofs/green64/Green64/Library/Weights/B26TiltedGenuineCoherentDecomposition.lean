module

public import Green64.Library.Weights.B26TiltedComparisonBlockIdentity

@[expose] public section

/-!
# Weights / B26TiltedGenuineCoherentDecomposition

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26TiltedGenuineCoherentDecomposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

def sourceOriginalB26TiltedCanonicalRawBlock434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (q : ℝ) (N : ℕ)
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (dsmall : ℕ)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1)*
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  ∑ ν ∈ family,sign ν *
    ∑ sigma : BigGroupPerm (BG := G) (J+ell),
    ∑ tau : BigGroupPerm (BG := G) (J+ell),
    ∑ t : ((g : G) → Fin (J+ell) → BP g),
      (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t sigma tau *
      sourceOriginalB26CanonicalRawValue434 data.Tb J ell m hmJ ν
        dsmall s t sigma tau ζ theta o k * f t

def sourceOriginalB26TiltedCanonicalAuxBanBlock434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (q : ℝ) (N : ℕ)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (dsmall : ℕ)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1)*
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  ∑ ν ∈ family,sign ν *
    ∑ sigma : BigGroupPerm (BG := G) (J+ell),
    ∑ tau : BigGroupPerm (BG := G) (J+ell),
    ∑ t : ((g : G) → Fin (J+ell) → BP g),
      (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t sigma tau *
      sourceOriginalB26CanonicalAuxBanError434 data.Tb data.Vbig J ell m hmJ ν
        Q h h xi dsmall s t sigma tau ζ theta o k * f t

/-- Genuine-family enumeration, with each original probe appearing once.
The literal full B26 CLEAN BIG operator equals RAW+comparison-ban.
No arithmetic or smallness premise is used in this identity. -/
theorem source_original_B26_TILTED_GENUINE_COHERENT_RAW_COMPARISON_BAN434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (q : ℝ) (N : ℕ)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
    (dsmall : ℕ)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) :
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
      (fun n : ↥family => sourceOriginalProbeMemoryPattern434 J m hmJ n.val) mu data.Vbig
      (fun n : ↥family => sourceOriginalProbeMemoryCanonicalK434 data.Tb data.Vbig
        J ell m hmJ n.val Q h h xi) dsmall ζ theta o k f s =
    sourceOriginalB26TiltedCanonicalRawBlock434 data q N blockA blockB
      J ell m hmJ Q h xi ζ theta o k false false dsmall f s +
    sourceOriginalB26TiltedCanonicalComparisonBlock434 data q N blockA blockB
      J ell m hmJ Q h xi ζ theta o k false false dsmall f s -
    sourceOriginalB26TiltedCanonicalAuxBanBlock434 data q N blockA blockB
      J ell m hmJ Q h xi ζ theta o k false false dsmall f s := by
  classical
  dsimp only
  rw [source_original_B26_COHERENT_RAW_COMPARISON_BAN434 data.Tb data.Vbig
    J ell m hmJ (fun n : ↥(sourceOriginalTwoBlockProbePatterns434 blockA blockB m) => n.val)
    (fun n => source_original_probe_memory_actual_pattern_disjoint434
      blockA blockB hBlocks m n.val n.property) Q (fun _ => h) (fun _ => h) xi
    (physicalSourceMuTilde _ (fun _ p => p.val) q N data.Vbig)
    dsmall ζ theta o k ho hk f s]
  have hReindex [Fintype ↥(sourceOriginalTwoBlockProbePatterns434 blockA blockB m)]
      (f : SourceOriginalProbePattern434 G m → ℂ) :
      (∑ n : ↥(sourceOriginalTwoBlockProbePatterns434 blockA blockB m),f n.val) =
      ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,f nu := by
    calc
      _ = ∑ n ∈ (sourceOriginalTwoBlockProbePatterns434 blockA blockB m).attach,f n.val := by
        apply Finset.sum_congr (by ext n;simp)
        intro n _
        rfl
      _ = _ := Finset.sum_attach _ _
  simp only [sourceOriginalB26TiltedCanonicalRawBlock434,sourceOriginalB26TiltedCanonicalComparisonBlock434,
    sourceOriginalB26TiltedCanonicalAuxBanBlock434,Bool.false_eq_true,ite_false,one_mul]
  simp only [mul_add,mul_sub,add_mul,sub_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  apply congrArg₂ (fun a b : ℂ => a-b)
  · apply congrArg₂ (fun a b : ℂ => a+b)
    · exact hReindex (fun nu =>
        ∑ sigma : BigGroupPerm (BG := G) (J+ell),
        ∑ tau : BigGroupPerm (BG := G) (J+ell),
        ∑ t : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}),
          (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
          sourceOriginalB26FrozenFreshLaw434 _ J ell m
            (physicalSourceMuTilde _ (fun _ p => p.val) q N data.Vbig)
            (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
          sourceOriginalB26CanonicalRawValue434 data.Tb J ell m hmJ nu dsmall s t sigma tau ζ theta o k * f t)
    · exact hReindex (fun nu =>
        ∑ sigma : BigGroupPerm (BG := G) (J+ell),
        ∑ tau : BigGroupPerm (BG := G) (J+ell),
        ∑ t : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}),
          (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
          sourceOriginalB26FrozenFreshLaw434 _ J ell m
            (physicalSourceMuTilde _ (fun _ p => p.val) q N data.Vbig)
            (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
          sourceOriginalB26CanonicalComparisonValue434 data.Tb data.Vbig J ell m hmJ nu Q h h xi dsmall s t sigma tau ζ theta o k * f t)
  · exact hReindex (fun nu =>
        ∑ sigma : BigGroupPerm (BG := G) (J+ell),
        ∑ tau : BigGroupPerm (BG := G) (J+ell),
        ∑ t : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}),
          (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
          sourceOriginalB26FrozenFreshLaw434 _ J ell m
            (physicalSourceMuTilde _ (fun _ p => p.val) q N data.Vbig)
            (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
          sourceOriginalB26CanonicalAuxBanError434 data.Tb data.Vbig J ell m hmJ nu Q h h xi dsmall s t sigma tau ζ theta o k * f t)
end Green64Analytic.CorrelationSquare

end

end

