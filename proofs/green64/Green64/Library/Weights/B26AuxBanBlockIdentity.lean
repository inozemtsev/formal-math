module

public import Green64.Library.Weights.B26GenuineCoherentDecomposition
public import Green64.Library.Analysis.Estimates.Part013

@[expose] public section

/-!
# Weights / B26AuxBanBlockIdentity

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26AuxBanBlockIdentity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

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
theorem source_original_B26_CANONICAL_AUX_BAN_FORM_BLOCK434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (dsmall : ℕ)
    (u v : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ) :
    sourceOriginalB26CanonicalAuxBanForm434 data blockA blockB
      J ell m hmJ Q h xi ζ theta o k epsSrc epsTgt dsmall u v =
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
    ∑ s : ((g : G) → Fin (J+ell) → BP g),
      ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) * star (u s) *
      sourceOriginalB26CanonicalAuxBanBlock434 data blockA blockB
        J ell m hmJ Q h xi ζ theta o k epsSrc epsTgt dsmall v s := by
  classical
  unfold sourceOriginalB26CanonicalAuxBanForm434 sourceOriginalB26PermutedAuxBanPairing434
    sourceOriginalB26CanonicalAuxBanBlock434
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

