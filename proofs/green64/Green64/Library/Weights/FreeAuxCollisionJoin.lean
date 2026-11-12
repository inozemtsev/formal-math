module

public import Green64.Library.Weights.Part113
public import Green64.Library.Weights.StrippedCollisionRank

@[expose] public section

/-!
# Weights / FreeAuxCollisionJoin

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FreeAuxCollisionJoin -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 22000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The independent original finite rank-main functional: two genuine
auxiliary-independent endpoint marked tests, with the true rank scalar,
full typed auxiliary law, original c-dependent arithmetic/cutoff/shift,
and original positive interval-window carrier. It is not defined by a
stripped slice or by its collision correction. -/
def parityActualWeightedRankMainFamily434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ) : ℂ :=
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
    ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
      let c := parityActualProbeAuxD434 L J m hmJ nu.val aux
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ)*
      parityWeightedRankMain434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val) Q h h xi
        (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (parityActualFreeCollisionAux434 L hS J m hmJ nu.val aux) (1/2) N
        (parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c)
        (fun w wp=>(2*k)≠0 ∧ (wp:ℤ)=(w:ℤ)+(2*k)*(c:ℤ))

/-- The complete original weighted Stripped family is exactly the
independent rank-main family minus its literal free-auxiliary collision.
The original constructions, full laws and both cell masses are preserved. -/
theorem parity_actual_stripped_family_rank_main_difference434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ) :
    (∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        parityActualWeightedStrippedComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k F G tw psi aux) =
      parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k F G tw psi -
        parityActualFreeCollisionFamily434 L hS J m hmJ Q h xi rho xi3 Z k F G tw psi
          (parityPositiveNaturalPositions434 (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))) := by
  unfold parityActualWeightedRankMainFamily434 parityActualFreeCollisionFamily434
  dsimp only
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro nu hnu
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro aux haux
  rw [parity_actual_weighted_stripped_rank_literal_collision434]
  dsimp only [parityActualFreeCollisionPairSum434,parityActualFreeCollisionAux434]
  ring

/-- Quantitative removal of the original free-auxiliary ban for the genuine
actual weighted Stripped family. This is a proved Z*L^(-A) replacement by
the independent rank-main family, not a collision-smallness premise.
Cutoff and displacement continue to depend on each original auxiliary draw. -/
theorem parity_eventually_actual_stripped_rank_main_saving434
    (J : ℕ) (S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) (hK : 0≤Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
          (Q:ℝ)≤L^CQ → xi⁻¹≤L^Cxi →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ‖(Z:ℂ)*((∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
            (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
          ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
            parityActualWeightedStrippedComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k E G tw psi aux) -
          parityActualWeightedRankMainFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k E G tw psi)‖≤Z*L^(-A) := by
  filter_upwards [parity_eventually_actual_free_collision_outer_Z_saving434 J S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A
    hSfine hbeta hgamma hCZ hK] with L hSave
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  let N := parityPositiveNaturalPositions434 (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  have hN (n : ℕ) (hn : n∈N) : 0<n :=
    ((parity_positive_natural_positions_mem434 _ n).mp hn).1
  have hBound := hSave.2.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi N hN
  rw [parity_actual_stripped_family_rank_main_difference434]
  simpa only [sub_sub_cancel_left,mul_neg,norm_neg] using hBound
end Green64Analytic.Parity

end

end

