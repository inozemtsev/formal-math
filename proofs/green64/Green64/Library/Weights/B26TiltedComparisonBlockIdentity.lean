module

public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Weights.Part055

@[expose] public section

/-!
# Weights / B26TiltedComparisonBlockIdentity

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26TiltedComparisonBlockIdentity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

def sourceOriginalB26TiltedCanonicalComparisonBlock434
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
      sourceOriginalB26CanonicalComparisonValue434 data.Tb data.Vbig J ell m hmJ ν
        Q h h xi dsmall s t sigma tau ζ theta o k * f t

private theorem comparison_sum_reorder434
    {S T P N : Type} [Fintype S] [Fintype T] [Fintype P]
    (family : Finset N) (f : P → P → N → S → T → ℂ) :
    (∑ sigma : P,∑ tau : P,∑ nu ∈ family,∑ s : S,∑ t : T,f sigma tau nu s t) =
    ∑ s : S,∑ nu ∈ family,∑ sigma : P,∑ tau : P,∑ t : T,f sigma tau nu s t := by
  calc
    _ = ∑ sigma : P,∑ tau : P,∑ s : S,∑ nu ∈ family,∑ t : T,f sigma tau nu s t := by
      apply Finset.sum_congr rfl
      intro sigma _
      apply Finset.sum_congr rfl
      intro tau _
      exact Finset.sum_comm
    _ = ∑ sigma : P,∑ s : S,∑ tau : P,∑ nu ∈ family,∑ t : T,f sigma tau nu s t := by
      apply Finset.sum_congr rfl
      intro sigma _
      exact Finset.sum_comm
    _ = ∑ s : S,∑ sigma : P,∑ tau : P,∑ nu ∈ family,∑ t : T,f sigma tau nu s t :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      calc
        _ = ∑ sigma : P,∑ nu ∈ family,∑ tau : P,∑ t : T,f sigma tau nu s t := by
          apply Finset.sum_congr rfl
          intro sigma _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

/-- Exact bilinear identification with the genuine comparison component
of the coherent BIG block, retaining every nu and both permutations. -/
theorem source_original_B26_TILTED_CANONICAL_COMPARISON_FORM_BLOCK434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (q : ℝ) (N : ℕ)
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (dsmall : ℕ)
    (u v : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ) :
    sourceOriginalB26TiltedCanonicalComparisonForm434 data q N blockA blockB
      J ell m hmJ Q h xi ζ theta o k epsSrc epsTgt dsmall u v =
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N data.Vbig
    ∑ s : ((g : G) → Fin (J+ell) → BP g),
      ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) * star (u s) *
      sourceOriginalB26TiltedCanonicalComparisonBlock434 data q N blockA blockB
        J ell m hmJ Q h xi ζ theta o k epsSrc epsTgt dsmall v s := by
  classical
  unfold sourceOriginalB26TiltedCanonicalComparisonForm434 sourceOriginalB26TiltedPermutedFullPairing434
    sourceOriginalB26TiltedCanonicalComparisonBlock434
  dsimp only
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [comparison_sum_reorder434]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro nu hnu
  apply Finset.sum_congr rfl
  intro sigma _
  apply Finset.sum_congr rfl
  intro tau _
  apply Finset.sum_congr rfl
  intro t _
  ring
end Green64Analytic.CorrelationSquare

end

end

