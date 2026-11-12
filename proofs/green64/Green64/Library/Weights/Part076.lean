module

public import Green64.Library.Correlation.Part055
public import Green64.Library.Weights.Part068
public import Green64.Library.Weights.Part071
public import Green64.Library.Correlation.Part045
public import Green64.Library.Weights.Part072
public import Green64.Library.Weights.Part070
public import Green64.Library.Weights.Part057
public import Green64.Library.Weights.Part069
public import Green64.Library.Weights.Part075
public import Green64.Library.Weights.Part067
public import Green64.Library.Correlation.Part036
public import Green64.Library.Correlation.PhysicalGAdmissibleHilbert
public import Green64.Library.Correlation.Part050
public import Green64.Library.Weights.Part060

@[expose] public section

/-!
# Weights / Part076

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSourceDIRTYFutureSectorCollapse -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Even AFTER dividing out the true initial Fock/vacuum weight,
the NORMALIZED physical first-DIRTY continuation vanishes
outside the diagonal relative torus sector selected by its
exact total integer Fourier frequency. If the initial weight
vanishes, the normalized future was defined to be exactly zero. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_normalized_off_diagonal_zero434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (tail : Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (freq : ℤ)
    (hoff : sourceOriginalActualSourceDIRTYRelativeTorus434
      u J ell R (a,tail) ≠
        sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) :
    sourceOriginalActualSourceDIRTYNormalizedFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a tail freq = 0 := by
  classical
  let w := sourceOriginalActualSourceDIRTYInitialWeight434
    u J ell R a
  let A := sourceOriginalActualSourceDIRTYPathAmplitude434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T (a,tail) freq
  have hA : A = 0 := by
    by_contra hn
    exact hoff (source_original_ACTUAL_SOURCE_DIRTY_path_diagonal_sector434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T (a,tail) freq hn)
  unfold sourceOriginalActualSourceDIRTYNormalizedFuture434
  by_cases hw : w = 0
  · simp [w,hw]
  · simp [w,A,hw,hA]

/-- The physical RELATIVE-torus filter of the full signed
chronological future is REDUNDANT at the one actual diagonal
key, even BEFORE initial-Fock averaging. All off-key summands
vanish individually; no estimate or TV cost is used. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_future_diagonal_unfiltered434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (freq : ℤ) :
    sourceOriginalActualSourceDIRTYRelativeFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq =
    ∑ tail : Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell,
      sourceOriginalActualSourceDIRTYNormalizedFuture434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T a tail freq := by
  classical
  unfold sourceOriginalActualSourceDIRTYRelativeFuture434
    sourceOriginalSignedCoherentFibreSuffix434
  apply Finset.sum_congr rfl
  intro tail ht
  by_cases hk : sourceOriginalActualSourceDIRTYRelativeTorus434
      u J ell R (a,tail) =
        sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq
  · simp [hk]
  · have hz := source_original_ACTUAL_SOURCE_DIRTY_normalized_off_diagonal_zero434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a tail freq hk
    simp [hk,hz]
/-- Every WRONG relative-torus sector has the ZERO future
from every true initial physical Fock×seen state, not merely
zero global amplitude after cancellation among initial weights. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_future_wrong_sector_zero434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (rel : (g : Option ι) → Green64SmallHaar.SmallTorus
      (fun p : {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g} =>
        p.val)) (freq : ℤ)
    (hwrong : rel ≠ sourceOriginalActualSourceDIRTYDiagonalTorus434
      u freq) :
    sourceOriginalActualSourceDIRTYRelativeFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a rel freq = 0 := by
  classical
  unfold sourceOriginalActualSourceDIRTYRelativeFuture434
    sourceOriginalSignedCoherentFibreSuffix434
  apply Finset.sum_eq_zero
  intro tail ht
  by_cases hk : sourceOriginalActualSourceDIRTYRelativeTorus434
      u J ell R (a,tail) = rel
  · have hneq : sourceOriginalActualSourceDIRTYRelativeTorus434
        u J ell R (a,tail) ≠
        sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq := by
      intro hdiag
      exact hwrong (hk.symm.trans hdiag)
    simp [hk,
      source_original_ACTUAL_SOURCE_DIRTY_normalized_off_diagonal_zero434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T a tail freq hneq]
  · simp [hk]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPhysicalChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16500000

/-- The ACTUAL source03 CLEAN/DIRTY first-insertion matrix
Laurent chain at a genuine physical Fock×cumulative-seen
starting state. Full physical E arithmetic D=SMALL*BIG,
original RAW/comparison joint K, both OLD masks, actual ghost G,
alternating orientation, T and signed integer k remain unchanged.
No independent future history is sampled or inserted. -/
noncomputable def sourceOriginalActualSourceDIRTYPhysicalChain434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell) :
    AddMonoidAlgebra ℂ ℤ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns x z)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let H := sourceOriginalActualSignedHistoryState434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap
  let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell cap cfg.q0 rho u.Vbig mu N N
        (fun out _ => physicalVacuum SP (fun _ p => p.val)
          BP (fun _ p => p.val) J ell out) b)
  exact sourceOriginalSignedLaurentDirtyChain434 C D N 0 F a

/-- The REAL per-initial-state normalized physical coherent
relative torus future at the frequency's TRUE diagonal sector
is exactly the original DIRTY matrix Laurent chain coefficient,
restricted only by the actual initial Fock/vacuum support.
No new operator, hypothetical source law, or path-TV replacement. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_future_diagonal_masked_chain434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell)
    (freq : ℤ) :
    sourceOriginalActualSourceDIRTYRelativeFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq =
    (if sourceOriginalActualSourceDIRTYInitialWeight434
      u J ell R a = 0 then 0 else
        (sourceOriginalActualSourceDIRTYPhysicalChain434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T a).coeff freq) := by
  rw [source_original_ACTUAL_SOURCE_DIRTY_future_diagonal_unfiltered434]
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let C := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let D := sourceOriginalActualProjectedGEScheduleLaurent434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns x z)
    cfg.q0 rho Vs u.Vbig mu K zeta k N T
  let H := sourceOriginalActualSignedHistoryState434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap
  let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell cap cfg.q0 rho u.Vbig mu N N
        (fun out _ => physicalVacuum SP (fun _ p => p.val)
          BP (fun _ p => p.val) J ell out) b)
  let w : H → ℂ := sourceOriginalActualSignedInitialWeight434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap (fun _ => le_rfl) Vs mu
  have hGeneric := source_original_ACTUAL_signed_DIRTY_normalized_future_chain434
    C D F w N 0 a freq
  change (∑ tail : Fin N → H,
      if w a = 0 then 0 else
        sourceOriginalSignedLaurentDIRTYPathAmplitude434
          C D F w N 0 (a,tail) freq / w a) =
    (if w a = 0 then 0 else
        (sourceOriginalSignedLaurentDirtyChain434
          C D N 0 F a).coeff freq)
  exact hGeneric
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYChainHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- UNMASKED actual signed DIRTY MATRIX CHAIN Fourier Hilbert
energy at frequency d. The sum is on THE SAME physically
reachable Fock×seen states with real positive Fock/OLD density
π, and the actual signed original source03 matrix continuation.
It is not an independently sampled random-walk energy. -/
noncomputable def sourceOriginalActualSourceDIRTYChainHilbertEnergy434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (freq : ℤ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  exact sourceOriginalActualSignedTrueTargetEnergy434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g))
    Vs u.Vbig mu
    (fun a => (sourceOriginalActualSourceDIRTYPhysicalChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a).coeff freq)

/-- Removing the zero-initial-vacuum mask in the coherent
physical future can ONLY INCREASE its true Fock/OLD
weighted norm square, since the discarded input states
have zero original Fock prefix and every surviving complex
DIRTY chain coefficient is unchanged. No count of states,
frequency channels, or chronological histories. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_coherent_future_le_chain434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (freq : ℤ) :
    sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq ≤
    sourceOriginalActualSourceDIRTYChainHilbertEnergy434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T freq := by
  classical
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  let H := sourceOriginalActualSourceDIRTYPathState434 u J ell
  let π : H → ℝ := sourceOriginalActualSignedTrueFockDensity434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g)) Vs u.Vbig mu
  let w := sourceOriginalActualSourceDIRTYInitialWeight434
    u J ell R
  let F : H → ℂ := fun a =>
    sourceOriginalActualSourceDIRTYRelativeFuture434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq
  let G : H → ℂ := fun a =>
    (sourceOriginalActualSourceDIRTYPhysicalChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a).coeff freq
  change (∑ a : H, (Real.sqrt (π a)*‖F a‖)^2) ≤
    (∑ a : H, (Real.sqrt (π a)*‖G a‖)^2)
  apply Finset.sum_le_sum
  intro a ha
  have hF : F a = if w a=0 then 0 else G a :=
    source_original_ACTUAL_SOURCE_DIRTY_future_diagonal_masked_chain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a freq
  rw [hF]
  by_cases hw : w a = 0
  · simp [hw]
    exact sq_nonneg _
  · simp [hw]

/-- Correct concrete target is a TRUE finite nonnegative
source signed matrix Hilbert energy, without baseline assumptions. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_chain_Hilbert_nonneg434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (freq : ℤ) :
    0 ≤ sourceOriginalActualSourceDIRTYChainHilbertEnergy434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T freq := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  change 0 ≤ sourceOriginalSignedJointForwardEnergy434
    (sourceOriginalActualSignedTrueFockDensity434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell (fun g => Fintype.card (BP g)) Vs u.Vbig mu)
    (fun a => (sourceOriginalActualSourceDIRTYPhysicalChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a).coeff freq)
  unfold sourceOriginalSignedJointForwardEnergy434
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYMatrixCircleHilbert -/

section

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- TRUE source03 full CIRCLE-Haar signed DIRTY MATRIX Hilbert
energy: integrate the norm-square of the exact Laurent
first-DIRTY chain for EACH original reachable Fock×seen
starting state, with the SAME actual joint physical
Fock/OLD density. No independent samples or history counts.
The complex joint comparison K and all OLD projectors remain
inside the actual noncommutative chronological chain. -/
noncomputable def sourceOriginalActualSourceDIRTYMatrixCircleHilbert434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  let H := sourceOriginalActualSourceDIRTYPathState434 u J ell
  let π : H → ℝ := sourceOriginalActualSignedTrueFockDensity434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g)) Vs u.Vbig mu
  exact ∑ a : H, (Real.sqrt (π a))^2 *
    (∫ theta : AddCircle (1:ℝ),
      ‖sourceOriginalActualLaurentCircle434
        (sourceOriginalActualSourceDIRTYPhysicalChain434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T a) theta‖^2
        ∂(AddCircle.haarAddCircle (T := (1:ℝ))))
/-- For ANY finite signed-frequency window F, the actual
physical DIRTY-chain weighted spectral energy is bounded by
the TRUE full signed matrix circle-Haar Hilbert energy,
with no factor depending on the frequency window, number of
initial states, BIG prime labels, chronology or comparisons. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_matrix_window_le_circle434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (F : Finset ℤ) :
    (∑ freq ∈ F,
      sourceOriginalActualSourceDIRTYChainHilbertEnergy434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T freq) ≤
    sourceOriginalActualSourceDIRTYMatrixCircleHilbert434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  let H := sourceOriginalActualSourceDIRTYPathState434 u J ell
  let π : H → ℝ := sourceOriginalActualSignedTrueFockDensity434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g)) Vs u.Vbig mu
  let M : H → AddMonoidAlgebra ℂ ℤ := fun a =>
    sourceOriginalActualSourceDIRTYPhysicalChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T a
  have h := source_original_ACTUAL_Laurent_finite_window_Hilbert_circle434
    π M F
  change (∑ freq ∈ F, ∑ a : H,
      (Real.sqrt (π a)*‖(M a).coeff freq‖)^2) ≤
    ∑ a : H, (Real.sqrt (π a))^2 *
      (∫ theta : AddCircle (1:ℝ),
        ‖sourceOriginalActualLaurentCircle434 (M a) theta‖^2
          ∂(AddCircle.haarAddCircle (T := (1:ℝ))))
  exact h

/-- The genuine original first-DIRTY physical signed chain
circle-Haar energy is a NONNEGATIVE weighted Fock/OLD Hilbert
quantity, without assuming the target is small. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_matrix_circle_nonneg434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) :
    0 ≤ sourceOriginalActualSourceDIRTYMatrixCircleHilbert434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T := by
  have h := source_original_ACTUAL_SOURCE_DIRTY_matrix_window_le_circle434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T ∅
  simpa using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativePointwiseL2 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- PROVED quantitative, no-history-count, SOURCE03 pointwise
Fourier bound on the EXACT TRUE original first-DIRTY Fock×seen
root. Each frequency selects ONE relative S+Ts torus sector.
The only remaining cost is the real original initial vacuum
energy and the true Fock/OLD-weighted square of the COHERENT
COMPLEX signed chronological future. The complete TRUE BIG
baseline is retained. No arbitrary comparison K independence,
and no false log saving. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_coherent_pointwise_L2_bound434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (freq : ℤ) :
    ‖(sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T).coeff freq‖^2 ≤
    ‖(physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ)‖^2 *
      sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R *
      sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T
        (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq := by
  let rel := sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq
  let Vac := sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R
  let Et := sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T rel freq
  let F := sourceOriginalActualSourceDIRTYRelativeFibreAmplitude434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T rel freq
  let Base : ℂ := (physicalSourceBaselineProduct
    (fun g : β => {p : ℕ // p ∈ u.Tb g})
    (fun _ p => p.val) cfg.q0 (2*R) : ℂ)
  have hVac : 0 ≤ Vac :=
    source_original_ACTUAL_SOURCE_initial_vacuum_energy_nonneg434
      u J ell R hb
  have hEt : 0 ≤ Et :=
    source_original_ACTUAL_SOURCE_DIRTY_relative_target_energy_nonneg434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T rel freq
  have hCS : ‖F‖ ≤ Real.sqrt Vac * Real.sqrt Et :=
    source_original_ACTUAL_SOURCE_DIRTY_relative_vacuum_CS434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T hb rel freq
  have hSq : ‖F‖^2 ≤ Vac*Et := by
    calc
      _ ≤ (Real.sqrt Vac*Real.sqrt Et)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hCS 2
      _ = Vac*Et := by
        rw [mul_pow,Real.sq_sqrt hVac,Real.sq_sqrt hEt]
  have hBase := mul_le_mul_of_nonneg_left hSq (sq_nonneg ‖Base‖)
  rw [source_original_ACTUAL_SOURCE_DIRTY_root_diagonal_relative_energy434]
  change ‖Base‖^2*‖F‖^2 ≤ ‖Base‖^2*Vac*Et
  calc
    _ ≤ ‖Base‖^2*(Vac*Et) := hBase
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYRelativeGlobalL2 -/

section

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- TRUE full source03 Fourier L² bound with a SINGLE actual
initial-vacuum energy factor and the sum of Fock/OLD-weighted
signed COHERENT continuation energies, ONE for each total
frequency's corresponding S+Ts relative-torus sector.
No extra factor #Fock states, #histories, #frequencies, #marks
or #comparison sign patterns. The true BIG baseline stays exact.
The TARGET L² energy has not yet been shown logarithmically small. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_coherent_global_L2_bound434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    let Base : ℂ := physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R)
    (∑ freq ∈ P.coeff.support, ‖P.coeff freq‖^2) ≤
      ‖Base‖^2 *
      sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R *
      ∑ freq ∈ P.coeff.support,
        sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T
          (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq := by
  dsimp only
  let P := sourceOriginalActualSourceDIRTYLaurentRoot434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
  let B : ℝ := ‖(physicalSourceBaselineProduct
    (fun g : β => {p : ℕ // p ∈ u.Tb g})
    (fun _ p => p.val) cfg.q0 (2*R) : ℂ)‖^2
  let Vac := sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R
  let E : ℤ → ℝ := fun freq =>
    sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq
  have hp (freq : ℤ) :
      ‖P.coeff freq‖^2 ≤ (B*Vac)*E freq := by
    have h := source_original_ACTUAL_SOURCE_DIRTY_coherent_pointwise_L2_bound434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T hb freq
    simpa only [P,B,Vac,E,mul_assoc] using h
  change (∑ freq ∈ P.coeff.support, ‖P.coeff freq‖^2) ≤
      (B*Vac)*(∑ freq ∈ P.coeff.support, E freq)
  calc
    _ ≤ ∑ freq ∈ P.coeff.support, (B*Vac)*E freq :=
      Finset.sum_le_sum (fun freq hf => hp freq)
    _ = _ := by rw [Finset.mul_sum]

/-- Same quantitative original source03 result in the PHYSICAL
circle-Haar L² norm, not a synthetic Fourier measure. The
original theta and all dependent RAW/comparison signs remain. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_coherent_circle_L2_bound434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    let Base : ℂ := physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R)
    (∫ t : AddCircle (1:ℝ), ‖sourceOriginalActualLaurentCircle434 P t‖^2
      ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) ≤
      ‖Base‖^2 *
      sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R *
      ∑ freq ∈ P.coeff.support,
        sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T
          (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq := by
  dsimp only
  have hBound := source_original_ACTUAL_SOURCE_DIRTY_coherent_global_L2_bound434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T hb
  have hParse := source_original_ACTUAL_SOURCE_DIRTY_circle_energy434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T
  dsimp only at hBound hParse
  rw [hParse] at hBound
  exact hBound
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03RAWComparisonFree -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- EVERY genuine source03 residual comparison pattern selects at
least one first-J auxiliary free slot C_g in a real BIG probe group.
This follows from the original TWO NONEMPTY subsets of probe
positions, not an invented synthetic comparison hypothesis. -/
theorem source_original_TRUE_source03_some_comparison_has_free_group434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434 blockA blockB m)) :
    ∃ g : G, 0 <
      ((sourceOriginalMemoryRawComparisonPattern434
        blockA blockB J m hmJ (some nu)).free g).card := by
  classical
  obtain ⟨hA, hAs, hB, hBs⟩ :=
    (source_original_two_block_probe_pattern_mem434
      blockA blockB m nu.val.1 nu.val.2).mp nu.property
  obtain ⟨⟨g,j⟩, hj⟩ := hA
  refine ⟨g, ?_⟩
  change 0 < (sourceOriginalProbeFreedSlots434
    J m hmJ nu.val g).card
  apply Finset.card_pos.mpr
  exact ⟨j.castLE hmJ,
    (source_original_probe_freed_first_m_iff434
      J m hmJ nu.val g j).mpr (Or.inl hj)⟩
/-- The exact literal RAW source family index none frees NO
BIG prime slots in ANY original genuine Tb group. -/
theorem source_original_TRUE_source03_RAW_has_no_free_group434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G)
    (J m : ℕ) (hmJ : m ≤ J) (g : G) :
    ((sourceOriginalMemoryRawComparisonPattern434
      blockA blockB J m hmJ none).free g).card = 0 := by
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03RelativeVacuumContract -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 14500000

/-- TRUE canonical source03 Fock/vacuum boundary contraction:
the genuine BIG baseline SQUARED times the EXACT initial
physical Fock/OLD inverse-density energy is at most ONE.
The proof uses the actual harmonic SMALL groups S+Ts, FULL
BIG Tb intervals and original numeric distinct-birth gate,
with no independent history or invented normalization. -/
theorem source_original_TRUE_source03_coherent_initial_baseline_squared_le_one434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (J ell R : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (hb1 : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p ≤ 1) :
    ‖(physicalSourceBaselineProduct
      (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ)‖^2 *
    sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R ≤ 1 := by
  let SP := fun g : Option (Fin n) =>
    {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g}
  let BP := fun g : Fin n => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option (Fin n)) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : Fin n) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  let cap : Fin n → ℕ := fun g => Fintype.card (BP g)
  let Base : ℂ := (physicalSourceBaselineProduct
    BP (fun _ p => p.val) cfg.q0 (2*R) : ℂ)
  let Vac : ℝ := sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R
  have hVs (g : Option (Fin n)) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hVb (g : Fin n) : 0 < u.Vbig g :=
    cfg.hv.trans_le (u.hVbig g)
  have hSmall : ∀ g : Option (Fin n),
      Vs g = ∑ p : SP g, (1:ℝ)/(p.val:ℝ) :=
    source_original_canonical_fields_small_harmonic434 z u hmatch
  have hBig (g : Fin n) :
      (∑ p : BP g, (1:ℝ)/(p.val:ℝ)) = u.Vbig g := by
    exact (source_original_canonical_FINSET_subtype_harmonic434
      (u.Tb g)).trans
      (source_original_canonical_fields_big_harmonic434 z u hmatch g).symm
  have hMass := source_original_ACTUAL_physical_initial_harmonic_mass_le_one434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap cfg.q0 Vs hVs hSmall u.Vbig hVb hBig
    R hb hb1
  have hBase : ‖Base‖ ≤ 1 :=
    source_original_ACTUAL_physical_baseline_norm_le_one434
      BP (fun _ p => p.val) cfg.q0 (2*R) hb hb1
  have hVac : 0 ≤ Vac :=
    source_original_ACTUAL_SOURCE_initial_vacuum_energy_nonneg434
      u J ell R hb
  have hProdNonneg : 0 ≤ ‖Base‖*Vac :=
    mul_nonneg (norm_nonneg _) hVac
  have hContract : ‖Base‖^2*Vac ≤ ‖Base‖*Vac := by
    calc
      _ = ‖Base‖*(‖Base‖*Vac) := by ring
      _ ≤ 1*(‖Base‖*Vac) :=
        mul_le_mul_of_nonneg_right hBase hProdNonneg
      _ = _ := by ring
  change ‖Base‖^2*Vac ≤ 1
  exact hContract.trans hMass
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03RelativeCoherentTargetBound -/

section

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- True canonical source03 pointwise first-DIRTY Fourier
L² contraction DIRECTLY to the Fock/OLD-weighted complex
continuation target of ONE relative S+Ts torus sector.
The complete physical BIG baseline and initial vacuum mass
cost EXACTLY <=1, by original harmonic SMALL+BIG normalization
and the real 0/1 initial-vacuum/Nodup gate.
No #history, #Fock-state, #frequency or K factor is introduced.
The target energy remains to be bounded by a logarithmic saving. -/
theorem source_original_TRUE_source03_relative_coherent_pointwise_target_only434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (hb1 : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p ≤ 1)
    (freq : ℤ) :
    ‖(sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T).coeff freq‖^2 ≤
    sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq := by
  let Vac := sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R
  let Base : ℂ := (physicalSourceBaselineProduct
    (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
    (fun _ p => p.val) cfg.q0 (2*R) : ℂ)
  let E := sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq
  have hBound :=
    source_original_ACTUAL_SOURCE_DIRTY_coherent_pointwise_L2_bound434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T hb freq
  have hContract :=
    source_original_TRUE_source03_coherent_initial_baseline_squared_le_one434
      z u hmatch J ell R hb hb1
  have hE : 0 ≤ E :=
    source_original_ACTUAL_SOURCE_DIRTY_relative_target_energy_nonneg434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
      (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq
  change ‖(sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T).coeff freq‖^2 ≤ E
  calc
    _ ≤ ‖Base‖^2*Vac*E := hBound
    _ = (‖Base‖^2*Vac)*E := by ring
    _ ≤ 1*E := mul_le_mul_of_nonneg_right hContract hE
    _ = E := one_mul E

/-- The ENTIRE exact original source03 physical circle-Haar L²
energy is bounded by the sum of the true signed coherent
relative-sector Fock/OLD continuation energies alone. All
initial/vacuum and baseline normalization already PAID, with
no independent-history or frequency count loss.
An unconditional (given literal canonical groups and positive
physical baseline), non-logarithmic analytic reduction. -/
theorem source_original_TRUE_source03_relative_coherent_circle_target_only434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (hb1 : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p ≤ 1) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
    (∫ t : AddCircle (1:ℝ), ‖sourceOriginalActualLaurentCircle434 P t‖^2
      ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) ≤
      ∑ freq ∈ P.coeff.support,
        sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T
          (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq := by
  dsimp only
  have hParse := source_original_ACTUAL_SOURCE_DIRTY_circle_energy434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
  dsimp only at hParse
  rw [←hParse]
  exact Finset.sum_le_sum (fun freq hf =>
    source_original_TRUE_source03_relative_coherent_pointwise_target_only434
      z u hmatch blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T hb hb1 freq)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03EventuallyRelativeTargetL2 -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- Original source03 first-DIRTY circle-Haar L² contraction
to the TRUE signed coherent relative-sector continuation energy,
with NO baseline-positivity or normalization hypotheses:
for the literal campaign depths R=ceil(L^0.52), T=ceil(L²),
the ACTUAL Tb lower prime band and B26 prime-visit estimates
unconditionally discharge physical b_p in [1/2,1].
All original RAW/comparison joint K channels and Fock×seen
dependence are retained. Still needs a log-saving bound for
the target energy, and requires existing original endpoint
SourceComparisonData plus canonical-field match. -/
theorem eventually_source_original_TRUE_source03_relative_circle_target_only434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ)
    (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 x Y Hp : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0)
        (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
        (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
        (blockA blockB : Finset (Fin n)) (Q : ℕ)
        (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
        (xi rho zeta : ℝ) (k : ℤ),
      let R := Nat.ceil (L^(0.52:ℝ))
      let T := Nat.ceil (L^2)
      let P := sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
      (∫ t : AddCircle (1:ℝ),
        ‖sourceOriginalActualLaurentCircle434 P t‖^2
          ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) ≤
        ∑ freq ∈ P.coeff.support,
          sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
            u blockA blockB J ell m hmJ Q hA hB
            xi rho zeta k R T
            (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq) freq := by
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards
    [eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hVisits
  intro n d vmax c0 x Y Hp z u hmatch blockA blockB Q
    hA hB xi rho zeta k
  dsimp only
  let R := Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let BP := fun g : Fin n => {p : ℕ // p ∈ u.Tb g}
  letI (g : Fin n) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  have hTb : u.Tb = z.Tb := hmatch.2.2.1
  have hmin (g : Fin n) (p : BP g) :
      Real.exp (L^cfg.cexp) ≤ (p.val:ℝ) := by
    have hm : p.val ∈ z.Tb g := by
      simpa only [hTb] using p.property
    exact (z.hBigBand g p.val hm).2.1
  have hbound (g : Fin n) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val)
          cfg.q0 (2*R) g p ∧
        physicalSourceBaseline BP (fun _ p => p.val)
          cfg.q0 (2*R) g p ≤ 1 := by
    exact source_original_B26_physical_baseline_half434
      BP (fun _ p => p.val) cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*R) g p (hVisits p.val (hmin g p))
  have hb (g : Fin n) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p := by
    linarith only [(hbound g p).1]
  have hb1 (g : Fin n) (p : BP g) :
      physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p ≤ 1 := (hbound g p).2
  exact source_original_TRUE_source03_relative_coherent_circle_target_only434
    z u hmatch blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T hb hb1
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03MatrixChainCircleReduction -/

section

open Filter Real
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Stronger TRUE canonical source03 physical first-DIRTY
circle-Haar reduction to the ACTUAL one-start-state DIRTY
MATRIX Laurent chain, rather than an artificial path-wise TV
future. Original FULL G*OLD*E source matrix, joint RAW/comparison
K, seen history and four independently usable sign tests survive.
The sum over initial physical states uses the actual joint
Fock/OLD mass, with NO cardinality factors for the path ensemble.
This is an operator-target bound; no log saving claimed. -/
theorem source_original_TRUE_SOURCE03_DIRTY_circle_le_matrix_frequency_energy434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (hb1 : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p ≤ 1) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
    (∫ t : AddCircle (1:ℝ),
      ‖sourceOriginalActualLaurentCircle434 P t‖^2
        ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) ≤
    ∑ freq ∈ P.coeff.support,
      sourceOriginalActualSourceDIRTYChainHilbertEnergy434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T freq := by
  dsimp only
  have hBase :=
    source_original_TRUE_source03_relative_coherent_circle_target_only434
      z u hmatch blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T hb hb1
  dsimp only at hBase
  calc
    _ ≤ ∑ freq ∈ (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T).coeff.support,
        sourceOriginalActualSourceDIRTYRelativeTargetEnergy434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T
          (sourceOriginalActualSourceDIRTYDiagonalTorus434 u freq)
          freq := hBase
    _ ≤ _ := Finset.sum_le_sum (fun freq hf =>
        source_original_ACTUAL_SOURCE_DIRTY_coherent_future_le_chain434
          u blockA blockB J ell m hmJ Q hA hB
          xi rho zeta k R T freq)
/-- The real initial source03 birth-tail schedule R=ceil(L^0.52)
and T=ceil(L²) requires NO separate BIG baseline positivity
hypothesis. Its entire ORIGINAL first-DIRTY circle-Haar energy
is bounded by genuine finite physical DIRTY Laurent matrix
state-energy at its own true Fourier frequencies, eventually
uniformly over all canonical moving source03 families. -/
theorem eventually_source_original_TRUE_SOURCE03_DIRTY_circle_matrix_energy434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ) (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 x Y Hp : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0)
        (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
        (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
        (blockA blockB : Finset (Fin n)) (Q : ℕ)
        (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
        (xi rho zeta : ℝ) (k : ℤ),
      let R := Nat.ceil (L^(0.52:ℝ))
      let T := Nat.ceil (L^2)
      let P := sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
      (∫ t : AddCircle (1:ℝ),
        ‖sourceOriginalActualLaurentCircle434 P t‖^2
          ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) ≤
        ∑ freq ∈ P.coeff.support,
          sourceOriginalActualSourceDIRTYChainHilbertEnergy434
            u blockA blockB J ell m hmJ Q hA hB
            xi rho zeta k R T freq := by
  have hc : 0 < cfg.cexp :=
    (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards
    [eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hVisits
  intro n d vmax c0 x Y Hp z u hmatch blockA blockB
    Q hA hB xi rho zeta k
  dsimp only
  let R := Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let BP := fun g : Fin n => {p : ℕ // p ∈ u.Tb g}
  letI (g : Fin n) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  have hTb : u.Tb = z.Tb := hmatch.2.2.1
  have hmin (g : Fin n) (p : BP g) :
      Real.exp (L^cfg.cexp) ≤ (p.val:ℝ) := by
    have hmem : p.val ∈ z.Tb g := by
      simpa only [hTb] using p.property
    exact (z.hBigBand g p.val hmem).2.1
  have hb0 (g : Fin n) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val)
          cfg.q0 (2*R) g p ∧
        physicalSourceBaseline BP (fun _ p => p.val)
          cfg.q0 (2*R) g p ≤ 1 :=
    source_original_B26_physical_baseline_half434
      BP (fun _ p => p.val) cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*R) g p (hVisits p.val (hmin g p))
  have hb (g : Fin n) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p := by
    linarith only [(hb0 g p).1]
  have hb1 (g : Fin n) (p : BP g) :
      physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p ≤ 1 := (hb0 g p).2
  exact source_original_TRUE_SOURCE03_DIRTY_circle_le_matrix_frequency_energy434
    z u hmatch blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T hb hb1
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03FullDIRTYMatrixCircle -/

section

open Filter Real
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- ORIGINAL source03 TRUE physical root CIRCLE L² is bounded
by the FULL first-DIRTY physical MATRIX-CHAIN CIRCLE L² norm
weighted over reachable Fock×seen states, with the correct
physical Fock/OLD density and ZERO frequency-window/history
cardinality penalties. The original RAW/comparison dependent
joint K and both OLD gates remain in the actual matrix.
True canonical source groups discharge ALL initial Fock/vacuum
and BIG baseline costs. This is a genuine operator reduction,
not a proof the remaining matrix energy tends to zero. -/
theorem source_original_TRUE_SOURCE03_DIRTY_circle_le_full_matrix_circle434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (hb1 : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p ≤ 1) :
    let P := sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
    (∫ theta : AddCircle (1:ℝ),
      ‖sourceOriginalActualLaurentCircle434 P theta‖^2
        ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) ≤
    sourceOriginalActualSourceDIRTYMatrixCircleHilbert434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T := by
  dsimp only
  have hSrc :=
    source_original_TRUE_SOURCE03_DIRTY_circle_le_matrix_frequency_energy434
      z u hmatch blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T hb hb1
  have hOp :=
    source_original_ACTUAL_SOURCE_DIRTY_matrix_window_le_circle434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T).coeff.support
  dsimp only at hSrc
  exact hSrc.trans hOp
/-- No baseline hypothesis at the REAL campaign R=ceil(L^.52)
and T=ceil(L²): the honest source03 first-DIRTY root has
CIRCLE-Haar L² energy bounded by the genuine time-ordered
physical DIRTY matrix-chain circle Hilbert norm eventually.
This removes the intermediate TRUE path/frequency enumeration
entirely. No claimed log saving of the target operator. -/
theorem eventually_source_original_TRUE_SOURCE03_DIRTY_full_matrix_circle434
    (cfg : SourceComparisonFixed434) (J ell m : ℕ)
    (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 x Y Hp : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434
          n cfg L d vmax c0)
        (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
        (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
        (blockA blockB : Finset (Fin n)) (Q : ℕ)
        (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
        (xi rho zeta : ℝ) (k : ℤ),
      let R := Nat.ceil (L^(0.52:ℝ))
      let T := Nat.ceil (L^2)
      let P := sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
      (∫ theta : AddCircle (1:ℝ),
        ‖sourceOriginalActualLaurentCircle434 P theta‖^2
          ∂(AddCircle.haarAddCircle (T := (1:ℝ)))) ≤
      sourceOriginalActualSourceDIRTYMatrixCircleHilbert434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T := by
  have hc : 0 < cfg.cexp :=
    (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards
    [eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hVisits
  intro n d vmax c0 x Y Hp z u hmatch blockA blockB
    Q hA hB xi rho zeta k
  dsimp only
  let R := Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  let BP := fun g : Fin n => {p : ℕ // p ∈ u.Tb g}
  letI (g : Fin n) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  have hTb : u.Tb = z.Tb := hmatch.2.2.1
  have hmin (g : Fin n) (p : BP g) :
      Real.exp (L^cfg.cexp) ≤ (p.val:ℝ) := by
    have hmem : p.val ∈ z.Tb g := by
      simpa only [hTb] using p.property
    exact (z.hBigBand g p.val hmem).2.1
  have h0 (g : Fin n) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val)
          cfg.q0 (2*R) g p ∧
        physicalSourceBaseline BP (fun _ p => p.val)
          cfg.q0 (2*R) g p ≤ 1 :=
    source_original_B26_physical_baseline_half434
      BP (fun _ p => p.val) cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*R) g p (hVisits p.val (hmin g p))
  have hb (g : Fin n) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p := by
    linarith only [(h0 g p).1]
  have hb1 (g : Fin n) (p : BP g) :
      physicalSourceBaseline BP (fun _ p => p.val)
        cfg.q0 (2*R) g p ≤ 1 := (h0 g p).2
  exact source_original_TRUE_SOURCE03_DIRTY_circle_le_full_matrix_circle434
    z u hmatch blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T hb hb1
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYThetaMatrixBridge -/

section

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The ACTUAL original source03 signed first-DIRTY MATRIX
propagation at one common real theta and one true initial
Fock×seen state: CLEAN G_i P_T E_i P_T before the first
DIRTY insertion, FULL thereafter, and the original final
G_N/vacuum projector. This is NOT a surrogate operator or
independently sampled sequence, and the orientation-dependent
joint RAW/comparison K stays literal. -/
noncomputable def sourceOriginalActualSourceDIRTYThetaMatrixChain434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell) : ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let C := sourceOriginalActualSignedProjectedGESchedule434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns)
    cfg.q0 rho Vs u.Vbig mu K zeta theta k N T
  let D := sourceOriginalActualSignedProjectedGESchedule434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns x z)
    cfg.q0 rho Vs u.Vbig mu K zeta theta k N T
  let F := sourceOriginalActualSignedProjectedTerminalG434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap cfg.q0 rho u.Vbig mu N N
    (fun out _ => physicalVacuum SP (fun _ p => p.val)
      BP (fun _ p => p.val) J ell out)
  exact sourceOriginalSignedMatrixDirtyChain434 C D N 0 F a

/-- NEW exact physical source03 signed matrix identity:
the Fourier/Laurent DIRTY operator at a common real theta
evaluates to the ORIGINAL CLEAN/DIRTY first-insertion
chronological physical matrix chain on the SAME actual state.
No BIG baseline or initial Fock weight appears in this
one-start-state matrix (these remain outside in original root). -/
theorem source_original_ACTUAL_SOURCE_DIRTY_physical_chain_theta_eval434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualSourceDIRTYPhysicalChain434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T a) =
    sourceOriginalActualSourceDIRTYThetaMatrixChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T a := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let H := sourceOriginalActualSignedHistoryState434
    SP (fun _ p => p.val) BP (fun _ p => p.val) J ell cap
  let F : H → AddMonoidAlgebra ℂ ℤ := fun b =>
    AddMonoidAlgebra.single (0:ℤ)
      (sourceOriginalActualSignedProjectedTerminalG434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell cap cfg.q0 rho u.Vbig mu N N
        (fun out _ => physicalVacuum SP (fun _ p => p.val)
          BP (fun _ p => p.val) J ell out) b)
  have h := source_original_ACTUAL_physical_DIRTY_Laurent_chain434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    cfg.q0 rho Vs u.Vbig mu K zeta theta k N T N 0 F a
  change sourceOriginalActualThetaEval434 theta
      (sourceOriginalSignedLaurentDirtyChain434
        (sourceOriginalActualProjectedGEScheduleLaurent434
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap patterns
          (sourceOriginalCleanChoice434 SP (fun _ p => p.val)
            BP (fun _ p => p.val) J ell m cap patterns)
          cfg.q0 rho Vs u.Vbig mu K zeta k N T)
        (sourceOriginalActualProjectedGEScheduleLaurent434
          SP (fun _ p => p.val) BP (fun _ p => p.val)
          J ell m cap patterns
          (fun x z => ¬ sourceOriginalCleanChoice434
            SP (fun _ p => p.val) BP (fun _ p => p.val)
            J ell m cap patterns x z)
          cfg.q0 rho Vs u.Vbig mu K zeta k N T)
        N 0 F a) =
      sourceOriginalActualSourceDIRTYThetaMatrixChain434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T a
  simpa only [sourceOriginalActualSourceDIRTYThetaMatrixChain434,
    F, source_original_ACTUAL_theta_eval_constant434,
    SP,BP,P,Vs,K] using h

/-- The same REAL physical signed matrix at theta is the
unmodified source03 full circle-Haar Laurent amplitude at
its corresponding element in the original AddCircle(1) torus. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_physical_chain_circle_eval434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell) :
    sourceOriginalActualLaurentCircle434
      (sourceOriginalActualSourceDIRTYPhysicalChain434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T a)
      (theta : AddCircle (1:ℝ)) =
    sourceOriginalActualSourceDIRTYThetaMatrixChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T a := by
  rw [source_original_ACTUAL_Laurent_circle_coe434]
  exact source_original_ACTUAL_SOURCE_DIRTY_physical_chain_theta_eval434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T a
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYCanonicalMatrices -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- The SAME true original signed physical CLEAN row used inside
the source03 Fock×seen first-DIRTY matrix, now explicitly named
for a forward Hilbert/Schur proof. Joint K is left dependent. -/
noncomputable def sourceOriginalActualSourceDIRTYCleanKernel434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    ℕ → sourceOriginalActualSourceDIRTYPathState434 u J ell →
      sourceOriginalActualSourceDIRTYPathState434 u J ell → ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  exact sourceOriginalActualSignedProjectedGESchedule434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns)
    cfg.q0 rho Vs u.Vbig mu K zeta theta k N T

/-- The SAME true original signed physical DIRTY row as above,
including actual OLD masks and ghost G_i, at each j. -/
noncomputable def sourceOriginalActualSourceDIRTYDirtyKernel434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    ℕ → sourceOriginalActualSourceDIRTYPathState434 u J ell →
      sourceOriginalActualSourceDIRTYPathState434 u J ell → ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let patterns := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  exact sourceOriginalActualSignedProjectedGESchedule434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap patterns
    (fun x z => ¬ sourceOriginalCleanChoice434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap patterns x z)
    cfg.q0 rho Vs u.Vbig mu K zeta theta k N T

/-- Exact unchanged original terminal G_N/vacuum weight
on the REAL reachable Fock×seen state. -/
noncomputable def sourceOriginalActualSourceDIRTYTerminalVector434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell : ℕ) (rho : ℝ) (R : ℕ) :
    sourceOriginalActualSourceDIRTYPathState434 u J ell → ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  exact sourceOriginalActualSignedProjectedTerminalG434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap cfg.q0 rho u.Vbig mu N N
    (fun out _ => physicalVacuum SP (fun _ p => p.val)
      BP (fun _ p => p.val) J ell out)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYCanonicalMatrixEquiv -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 950000

/-- The small named canonical source03 C, D, F operators are
DEFINITIONALLY identical to the ORIGINAL source03 physical
signed first-DIRTY matrix chain. No hypothesis of independent
K, renewed numerical seen histories, missing OLD projections
or nonphysical Fock/prime labels is introduced. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_named_physical_matrices_eq434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell) :
    sourceOriginalActualSourceDIRTYThetaMatrixChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T a =
    sourceOriginalSignedMatrixDirtyChain434
      (sourceOriginalActualSourceDIRTYCleanKernel434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T)
      (sourceOriginalActualSourceDIRTYDirtyKernel434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T)
      (2*R) 0
      (sourceOriginalActualSourceDIRTYTerminalVector434
        u J ell rho R) a := by
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPhysicalGhostE -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The ORIGINAL source03 ghost G_j complex matrix on the true
reachable Fock×cumulative-seen state carrier, using its SAME
actual N=2R, q0, rho and tilted BIG prime law. -/
noncomputable def sourceOriginalActualSourceDIRTYGhostKernel434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell : ℕ) (rho : ℝ) (R j : ℕ) :
    sourceOriginalActualSourceDIRTYPathState434 u J ell →
      sourceOriginalActualSourceDIRTYPathState434 u J ell → ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  exact sourceOriginalActualSignedGhostMatrix434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap cfg.q0 rho N j u.Vbig mu

/-- The ORIGINAL source03 locally DIRTY E_j, including BOTH
source OLD P_T gates, original literal E physical SMALL/BIG
arithmetic, dependent RAW/comparison K, and visit's
ACTUAL alternate orientation. Excludes G_j, which is
separately named above without discarding any seen state. -/
noncomputable def sourceOriginalActualSourceDIRTYEdgeOnly434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T j : ℕ) :
    sourceOriginalActualSourceDIRTYPathState434 u J ell →
      sourceOriginalActualSourceDIRTYPathState434 u J ell → ℂ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let K := sourceOriginalMemoryRawComparisonK434 u.Tb u.Vbig
    blockA blockB J ell m hmJ Q hA hB xi
  let N := 2*R
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 N u.Vbig
  let pats := sourceOriginalMemoryRawComparisonPattern434
    blockA blockB J m hmJ
  let dirty := fun x z => ¬ sourceOriginalCleanChoice434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap pats x z
  exact sourceOriginalActualSignedOLDMaskedEMatrix434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell m cap pats dirty
    cfg.q0 rho Vs u.Vbig mu
    (memoryOrientationK BP J ell m pats K (physicalAlternatingSign j))
    zeta theta (physicalAlternatingSign j) k T

/-- An EXACT algebraic factorization of the actual source03
signed CLEAN-before-DIRTY edge G_j P_T E_j P_T into the
true ghost G_j and the true DIRTY E_j kernel.
No surrogate row, independent prime history or state reset. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_real_ghost_E_factor434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T j : ℕ) :
    sourceOriginalActualSourceDIRTYDirtyKernel434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T j =
    sourceOriginalSignedMatrixProduct434
      (sourceOriginalActualSourceDIRTYGhostKernel434
        u J ell rho R j)
      (sourceOriginalActualSourceDIRTYEdgeOnly434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T j) := by
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPointwiseMatrix -/

section

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Original source03 DIRTY root as an EXACT Fock×seen
matrix Laurent polynomial bilinear form, not a new operator.
This is an algebraic identity with the unchanged BIG baseline,
true initial signed vacuum weight, actual C/D, original K,
chronological seen and final G_N/vacuum. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_root_matrix_polynomial_exact434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalActualSourceDIRTYLaurentRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T =
    AddMonoidAlgebra.single (0:ℤ)
      (physicalSourceBaselineProduct
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    ∑ a : sourceOriginalActualSourceDIRTYPathState434 u J ell,
      AddMonoidAlgebra.single (0:ℤ)
        (sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R a) *
      sourceOriginalActualSourceDIRTYPhysicalChain434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T a := by
  rfl
/-- UNCONDITIONAL TRUE source03 signed first-DIRTY root at ANY
COMMON θ is exactly BIGbaseline times a single complex
Fock×seen initial-state pairing with the REAL ORIGINAL
signed physical CLEAN-before-DIRTY, FULL-after G*PEP matrix
chain. This is pointwise, not a character or circle average. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_root_theta_initial_pairing434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T) =
    (physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ) *
    ∑ a : sourceOriginalActualSourceDIRTYPathState434 u J ell,
      sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R a *
      sourceOriginalActualSourceDIRTYThetaMatrixChain434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T a := by
  classical
  rw [source_original_ACTUAL_SOURCE_DIRTY_root_matrix_polynomial_exact434]
  rw [map_mul, source_original_ACTUAL_theta_eval_constant434, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_mul, source_original_ACTUAL_theta_eval_constant434,
    source_original_ACTUAL_SOURCE_DIRTY_physical_chain_theta_eval434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYThetaHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Pointwise real-θ positive Hilbert norm of the genuine ORIGINAL
source03 signed CLEAN-before-DIRTY physical matrix chain,
against the ACTUAL reached Fock×cumulative-seen joint density π.
Neither history nor BIG prime labels are averaged independently. -/
noncomputable def sourceOriginalActualSourceDIRTYThetaMatrixHilbert434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  exact sourceOriginalActualSignedTrueTargetEnergy434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell (fun g => Fintype.card (BP g))
    Vs u.Vbig mu
    (fun a => sourceOriginalActualSourceDIRTYThetaMatrixChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T a)

/-- THE TRUE original physical pointwise theta-matrix Hilbert
energy is a nonnegative finite sum of genuine density-weighted
squared complex matrix-chain amplitudes. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_theta_matrix_Hilbert_nonneg434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    0 ≤ sourceOriginalActualSourceDIRTYThetaMatrixHilbert434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  change 0 ≤ sourceOriginalSignedJointForwardEnergy434
    (sourceOriginalActualSignedTrueFockDensity434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell (fun g => Fintype.card (BP g)) Vs u.Vbig mu)
    (fun a => sourceOriginalActualSourceDIRTYThetaMatrixChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T a)
  unfold sourceOriginalSignedJointForwardEnergy434
  exact Finset.sum_nonneg (fun a ha => sq_nonneg _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYCanonicalDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- REAL original source03 physical Fock/OLD mass π on each
authentically reachable Fock×cumulative-seen state, named
separately to avoid multiplying large kernel definitions. -/
noncomputable def sourceOriginalActualSourceDIRTYJointDensity434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (J ell R : ℕ)
    (a : sourceOriginalActualSourceDIRTYPathState434 u J ell) : ℝ := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  exact sourceOriginalActualSignedTrueFockDensity434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap Vs u.Vbig mu a

/-- The already proven true source03 ThetaMatrixHilbert is
DEFINITIONALLY the weighted forward-energy of the TRUE physical
ThetaMatrixChain, with the SAME named joint density above. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_named_joint_energy_eq434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ) :
    sourceOriginalActualSourceDIRTYThetaMatrixHilbert434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T =
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSourceDIRTYJointDensity434 u J ell R)
      (sourceOriginalActualSourceDIRTYThetaMatrixChain434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta theta k R T) := by
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYPointwiseHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- ORIGINAL true physical first-DIRTY Fourier/theta root at
EVERY INDIVIDUAL common real theta, NOT only after circle
averaging, has norm² bounded by true BIG baseline² times
the exact ORIGINAL initial vacuum Fock energy times the
Hilbert norm-square of the same REAL signed physical
matrix first-DIRTY chain on all reached Fock×seen states.
NO history/state count, independent comparison K or fake
orthogonal Fock initial conditions. The remaining TRUE matrix
Hilbert energy is not asserted to be logarithmically small. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_pointwise_physical_Hilbert434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : β => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p) :
    ‖sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T)‖^2 ≤
    ‖(physicalSourceBaselineProduct
      (fun g : β => {p : ℕ // p ∈ u.Tb g})
      (fun _ p => p.val) cfg.q0 (2*R) : ℂ)‖^2 *
    sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R *
    sourceOriginalActualSourceDIRTYThetaMatrixHilbert434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T := by
  let P := sourceOriginalActualSmallPrimeSets434 u
  let SP := fun g : Option ι => {p : ℕ // p ∈ P g}
  let BP := fun g : β => {p : ℕ // p ∈ u.Tb g}
  letI (g : Option ι) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g
      p.val p.property).ne_zero⟩
  letI (g : β) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let cap : β → ℕ := fun g => Fintype.card (BP g)
  let Vs := sourceOriginalActualSmallMass434 u
  let mu := physicalSourceMuTilde BP (fun _ p => p.val)
    cfg.q0 (2*R) u.Vbig
  let H := sourceOriginalActualSourceDIRTYPathState434 u J ell
  let w : H → ℂ := sourceOriginalActualSourceDIRTYInitialWeight434 u J ell R
  let f : H → ℂ := fun a =>
    sourceOriginalActualSourceDIRTYThetaMatrixChain434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T a
  let π : H → ℝ :=
    sourceOriginalActualSignedTrueFockDensity434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap Vs u.Vbig mu
  let Base : ℂ := (physicalSourceBaselineProduct
    BP (fun _ p => p.val) cfg.q0 (2*R) : ℂ)
  let Vac := sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R
  let E := sourceOriginalActualSourceDIRTYThetaMatrixHilbert434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T
  have hVs (g : Option ι) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hVb (g : β) : 0 < u.Vbig g :=
    cfg.hv.trans_le (u.hVbig g)
  have hmu (g : β) (p : BP g) : 0 < mu g p := by
    have hp : (0:ℝ) < (p.val:ℝ) :=
      Nat.cast_pos.mpr (NeZero.pos p.val)
    have hv := hVb g
    have hbp := hb g p
    dsimp [mu,physicalSourceMuTilde]
    positivity
  have hπ (a : H) : 0 < π a :=
    source_original_ACTUAL_signed_true_fock_density_pos434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap Vs u.Vbig mu hVs hVb hmu a
  have hInit := source_original_ACTUAL_initial_signed_dual_energy_vacuum434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap (fun _ => le_rfl) Vs u.Vbig mu hVs hVb hmu
  have hInitial : sourceOriginalSignedJointInverseEnergy434 π w = Vac := by
    change sourceOriginalSignedJointInverseEnergy434 π w =
      sourceOriginalActualPhysicalInitialVacuumEnergy434
        SP (fun _ p => p.val) BP (fun _ p => p.val)
        J ell cap Vs mu at hInit
    exact hInit
  have hE : 0 ≤ E :=
    source_original_ACTUAL_SOURCE_DIRTY_theta_matrix_Hilbert_nonneg434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T
  have hVac : 0 ≤ Vac :=
    source_original_ACTUAL_SOURCE_initial_vacuum_energy_nonneg434
      u J ell R hb
  have hCSraw := source_original_SIGNED_joint_weighted_CS434
    π hπ w f
  have hCS : ‖∑ a : H, w a * f a‖ ≤
      Real.sqrt Vac * Real.sqrt E := by
    change ‖∑ a : H, w a*f a‖ ≤
      Real.sqrt (sourceOriginalSignedJointInverseEnergy434 π w) *
      Real.sqrt (sourceOriginalSignedJointForwardEnergy434 π f) at hCSraw
    rw [hInitial] at hCSraw
    exact hCSraw
  rw [source_original_ACTUAL_SOURCE_DIRTY_root_theta_initial_pairing434]
  change ‖Base * (∑ a : H, w a * f a)‖^2 ≤ ‖Base‖^2 * Vac * E
  have hNorm : ‖Base*(∑ a : H, w a*f a)‖ ≤
      ‖Base‖ * (Real.sqrt Vac * Real.sqrt E) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hCS (norm_nonneg _)
  calc
    _ ≤ (‖Base‖ * (Real.sqrt Vac * Real.sqrt E))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hNorm 2
    _ = ‖Base‖^2*Vac*E := by
      rw [mul_pow,mul_pow,Real.sq_sqrt hVac,Real.sq_sqrt hE]
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03ThetaPointwiseContract -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- ORIGINAL canonical source03 pointwise-θ signed DIRTY
first-insertion root norm² bounded by THE SAME true physical
signed DIRTY MATRIX Hilbert target, with the FULL BIG baseline
and true initial vacuum Fock state EXACTLY PAID by original
SMALL+BIG harmonic normalizations and real Nodup gate.
This is stronger than an averaged-theta-only reduction but
DOES NOT establish the required log decay of operator energy.
The joint RAW/comparison K and independent sign channels
remain literally inside the RHS physical chronology. -/
theorem source_original_TRUE_SOURCE03_DIRTY_theta_pointwise_matrix_bound434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (hb1 : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p ≤ 1) :
    ‖sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T)‖^2 ≤
    sourceOriginalActualSourceDIRTYThetaMatrixHilbert434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T := by
  let E := sourceOriginalActualSourceDIRTYThetaMatrixHilbert434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T
  let Base : ℂ := (physicalSourceBaselineProduct
    (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
    (fun _ p => p.val) cfg.q0 (2*R) : ℂ)
  let Vac := sourceOriginalActualSourceInitialVacuumEnergy434 u J ell R
  have hSrc := source_original_ACTUAL_SOURCE_DIRTY_pointwise_physical_Hilbert434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T hb
  have hContract :=
    source_original_TRUE_source03_coherent_initial_baseline_squared_le_one434
      z u hmatch J ell R hb hb1
  have hE : 0 ≤ E :=
    source_original_ACTUAL_SOURCE_DIRTY_theta_matrix_Hilbert_nonneg434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T
  change ‖sourceOriginalActualThetaEval434 theta
      (sourceOriginalActualSourceDIRTYLaurentRoot434
        u blockA blockB J ell m hmJ Q hA hB
        xi rho zeta k R T)‖^2 ≤ E
  calc
    _ ≤ ‖Base‖^2 * Vac * E := hSrc
    _ = (‖Base‖^2 * Vac) * E := by ring
    _ ≤ 1*E := mul_le_mul_of_nonneg_right hContract hE
    _ = E := one_mul E

/-- Pointwise TRUE source03 FIRST-DIRTY ORIGINAL physical root
`sourceOriginalActualSourcePhysicalDIRTYRoot434` is bounded
by exact physical matrix Hilbert energy at the SAME theta.
The explicitly supplied physical BIG-label injectivity is the
same one used to establish the original source Laurent identity.
No averaging over angles or prime labels. -/
theorem source_original_TRUE_SOURCE03_physical_DIRTY_root_pointwise_Hilbert434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (hi : Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val))
    (blockA blockB : Finset (Fin n)) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 (Fin n) m → ℝ)
    (xi rho zeta theta : ℝ) (k : ℤ) (R T : ℕ)
    (hb : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      0 < physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p)
    (hb1 : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      physicalSourceBaseline
        (fun g : Fin n => {p : ℕ // p ∈ u.Tb g})
        (fun _ p => p.val) cfg.q0 (2*R) g p ≤ 1) :
    ‖sourceOriginalActualSourcePhysicalDIRTYRoot434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T‖^2 ≤
    sourceOriginalActualSourceDIRTYThetaMatrixHilbert434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta theta k R T := by
  rw [←source_original_ACTUAL_SOURCE_DIRTY_Laurent_exact434
    u hi blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T hb]
  exact source_original_TRUE_SOURCE03_DIRTY_theta_pointwise_matrix_bound434
    z u hmatch blockA blockB J ell m hmJ Q hA hB
    xi rho zeta theta k R T hb hb1
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03BIGSigmaInjective -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- NO EXTRA BIG prime index-injectivity hypothesis for ACTUALLY
constructed/canonically matched ORIGINAL source03 data. It is
kernel-proved from the genuine pairwise-disjoint FULL Tb prime
interval groups; different BIG groups CANNOT share one prime label. -/
theorem source_original_TRUE_SOURCE03_BIG_sigma_label_injective434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u) :
    Function.Injective
      (fun z : Sigma (fun g => {p : ℕ // p ∈ u.Tb g}) => z.2.val) := by
  intro a b hval
  cases a with
  | mk ga pa =>
    cases b with
    | mk gb pb =>
      change pa.val = pb.val at hval
      have hga : ga = gb := by
        have hmem : pa.val ∈ u.Tb gb := by
          rw [hval]
          exact pb.property
        have hf :=
          source_original_canonical_fields_ALL_group_index_unique434
            z u hmatch
            (Sum.inr (Sum.inr ga)) (Sum.inr (Sum.inr gb))
            pa.val pa.property hmem
        exact Sum.inr.inj (Sum.inr.inj hf)
      subst gb
      have hp : pa = pb := Subtype.ext hval
      subst pb
      rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03GAdmissiblePolynomial -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- The exact G Hilbert budget is polynomial whenever the actual total
V*mu mass is logarithmic. The exponent is uniform in the visit number. -/
theorem source_original_ADMISSIBLE_G_budget_polynomial434
    {BG : Type} [Fintype BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)]
    (q rho L A : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hgap : Real.sqrt q < rho^2) (hL : 1 < L)
    (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hm : ∀ g p,0 ≤ V g*mu g p)
    (hMass : (∑ g,∑ p,V g*mu g p) ≤ A*Real.log L) :
    (sourceOriginalAdmissibleGHilbertBudget434 BP q rho N i V mu)^2 ≤
      L^(2*A/(rho^2-Real.sqrt q)) := by
  let delta := rho^2-Real.sqrt q
  let beta := (sourceVisitEta q N i)^2/(rho^2-sourceVisitQ q N i)
  have hd : 0 < delta := sub_pos.mpr hgap
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq
  have hs1 : Real.sqrt q ≤ 1 := by nlinarith
  have hqs : q ≤ Real.sqrt q := by nlinarith
  have ht : sourceVisitQ q N i ≤ Real.sqrt q := by
    unfold sourceVisitQ
    split_ifs <;> first | exact le_rfl | exact hqs
  have hden : delta ≤ rho^2-sourceVisitQ q N i := sub_le_sub_left ht _
  have hden0 : 0 < rho^2-sourceVisitQ q N i := hd.trans_le hden
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  have he2 : (sourceVisitEta q N i)^2 ≤ 1 := by nlinarith [he.1,he.2]
  have hb0 : 0 ≤ beta := div_nonneg (sq_nonneg _) hden0.le
  have hb : beta ≤ 1/delta :=
    (div_le_div_of_nonneg_right he2 hden0.le).trans
      (one_div_le_one_div_of_le hd hden)
  have hM0 : 0 ≤ ∑ g,∑ p,V g*mu g p :=
    Finset.sum_nonneg (fun g _ => Finset.sum_nonneg (fun p _ => hm g p))
  have hC0 : 0 ≤ sourceOriginalAdmissibleGHilbertBudget434 BP q rho N i V mu :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun p _ =>
      add_nonneg zero_le_one (mul_nonneg hb0 (hm g p))))
  have hExp : beta*(∑ g,∑ p,V g*mu g p) ≤ (A/delta)*Real.log L := by
    calc
      _ ≤ (1/delta)*(∑ g,∑ p,V g*mu g p) :=
        mul_le_mul_of_nonneg_right hb hM0
      _ ≤ (1/delta)*(A*Real.log L) :=
        mul_le_mul_of_nonneg_left hMass (one_div_pos.mpr hd).le
      _ = _ := by ring
  have hLp : 0 < L := zero_lt_one.trans hL
  have hC : sourceOriginalAdmissibleGHilbertBudget434 BP q rho N i V mu ≤
      L^(A/delta) := by
    calc
      _ ≤ ∏ g,∏ p,Real.exp (beta*(V g*mu g p)) := by
        apply Finset.prod_le_prod₀
        · intro g hg
          exact Finset.prod_nonneg (fun p _ =>
            add_nonneg zero_le_one (mul_nonneg hb0 (hm g p)))
        · intro g hg
          exact Finset.prod_le_prod₀
            (fun p _ => add_nonneg zero_le_one (mul_nonneg hb0 (hm g p)))
            (fun p _ => by simpa only [add_comm] using Real.add_one_le_exp (beta*(V g*mu g p)))
      _ = Real.exp (beta*(∑ g,∑ p,V g*mu g p)) := by
        simp only [Real.exp_sum,Finset.mul_sum]
      _ ≤ Real.exp ((A/delta)*Real.log L) := Real.exp_le_exp.mpr hExp
      _ = L^(A/delta) := by
        rw [Real.rpow_def_of_pos hLp]
        congr 1
        ring
  calc
    _ ≤ (L^(A/delta))^2 := pow_le_pow_left₀ hC0 hC 2
    _ = L^(2*A/delta) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
      congr 1
      ring

/-- The true source03 G matrix, full SMALL S+Ts, FULL BIG prime intervals,
all active arrays and all reachable Fock×seen histories, at admissible
rho. The total REAL BIG mass supplies the polynomial exponent. -/
theorem source_original_TRUE_SOURCE03_G_admissible_polynomial434
    {n : ℕ} {cfg : SourceComparisonFixed434}
    {L d vmax c0 x Y Hp : ℝ}
    (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
    (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
    (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
    (hL : 1 < L) (hvmax : 0 ≤ vmax)
    (rho : ℝ) (hr : 0 < rho) (hgap : Real.sqrt cfg.q0 < rho^2)
    (J ell R j : ℕ)
    (hSize : ∀ g (p : {p : ℕ // p ∈ u.Tb g}),
      2*((2*R+1:ℕ):ℝ) ≤ (p.val:ℝ))
    (f : sourceOriginalActualSourceDIRTYPathState434 u J ell → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSourceDIRTYJointDensity434 u J ell R)
      (sourceOriginalSignedMatrixAction434
        (sourceOriginalActualSourceDIRTYGhostKernel434 u J ell rho R j) f) ≤
    L^(4*vmax*cfg.C0/(rho^2-Real.sqrt cfg.q0)) *
      sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSourceDIRTYJointDensity434 u J ell R) f := by
  classical
  let SP := fun g : Option (Fin n) => {p : ℕ // p ∈ sourceOriginalActualSmallPrimeSets434 u g}
  let BP := fun g : Fin n => {p : ℕ // p ∈ u.Tb g}
  let bm : (g : Fin n) → BP g → ℕ := fun _ p => p.val
  letI (g : Option (Fin n)) (p : SP g) : NeZero p.val :=
    ⟨((source_original_ACTUAL_SMALL_source_bounds434 u).1 g p.val p.property).ne_zero⟩
  letI (g : Fin n) (p : BP g) : NeZero (bm g p) :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let Vs := sourceOriginalActualSmallMass434 u
  let V := u.Vbig
  let mu := physicalSourceMuTilde BP bm cfg.q0 (2*R) V
  let cap : Fin n → ℕ := fun g => Fintype.card (BP g)
  have hVs (g : Option (Fin n)) : 0 < Vs g :=
    cfg.hv.trans_le ((source_original_ACTUAL_SMALL_source_bounds434 u).2.2 g)
  have hV (g : Fin n) : 0 < V g := cfg.hv.trans_le (u.hVbig g)
  have hb (g : Fin n) (p : BP g) : (1:ℝ)/2 ≤
      physicalSourceBaseline BP bm cfg.q0 (2*R) g p :=
    (source_original_B26_physical_baseline_half434 BP bm cfg.q0 cfg.hq0.le cfg.hq1.le
      (2*R) g p (hSize g p)).1
  have hmu (g : Fin n) (p : BP g) : 0 < mu g p := by
    have hp : 0 < (bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hb0 : 0 < physicalSourceBaseline BP bm cfg.q0 (2*R) g p :=
      lt_of_lt_of_le (by norm_num) (hb g p)
    exact one_div_pos.mpr (mul_pos (mul_pos (hV g) hp) hb0)
  have hHarmonic (g : Fin n) : (∑ p : BP g,(1:ℝ)/(bm g p:ℝ))=V g := by
    rw [source_original_canonical_FINSET_subtype_harmonic434]
    exact (source_original_canonical_fields_big_harmonic434 z u hmatch g).symm
  have hMassUpper : (∑ g : Fin n,V g) ≤ vmax*(cfg.C0*Real.log L) := by
    have hVeq : u.Vbig=z.Vbig := hmatch.2.2.2.2.2
    have hv (g : Fin n) : V g ≤ vmax := by
      dsimp only [V]
      rw [hVeq]
      exact (z.hBigMass g).2.le
    calc
      _ ≤ ∑ _g : Fin n,vmax := Finset.sum_le_sum (fun g _ => hv g)
      _ = (n:ℝ)*vmax := by simp
      _ ≤ (cfg.C0*Real.log L)*vmax :=
        mul_le_mul_of_nonneg_right z.hBigLog hvmax
      _ = _ := by ring
  have hIntensity : (∑ g,∑ p : BP g,V g*mu g p) ≤
      (2*vmax*cfg.C0)*Real.log L := by
    calc
      _ ≤ 2*(∑ g,∑ p : BP g,(1:ℝ)/(bm g p:ℝ)) :=
        source_original_ACTUAL_source_mu_intensity434 BP bm cfg.q0 (2*R) V hV hb
      _ = 2*(∑ g,V g) := by simp_rw [hHarmonic]
      _ ≤ 2*(vmax*(cfg.C0*Real.log L)) :=
        mul_le_mul_of_nonneg_left hMassUpper (by norm_num)
      _ = _ := by ring
  have hCost := source_original_ADMISSIBLE_G_budget_polynomial434 BP cfg.q0 rho L
    (2*vmax*cfg.C0) cfg.hq0.le cfg.hq1.le hgap hL (2*R) j V mu
    (fun g p => mul_nonneg (hV g).le (hmu g p).le) hIntensity
  have hpower : 2*(2*vmax*cfg.C0)/(rho^2-Real.sqrt cfg.q0) =
      4*vmax*cfg.C0/(rho^2-Real.sqrt cfg.q0) := by ring
  rw [hpower] at hCost
  have hi := source_original_TRUE_SOURCE03_BIG_sigma_label_injective434 z u hmatch
  have hG := source_original_ACTUAL_G_admissible_Hilbert434
    SP (fun _ p => p.val) BP bm J ell cap hi (fun g => le_refl _)
    cfg.q0 rho cfg.hq0 cfg.hq1 hr hgap (2*R) j Vs V mu hVs hV hmu f
  have hp := source_original_ACTUAL_signed_true_fock_density_pos434
    SP (fun _ p => p.val) BP bm J ell cap Vs V mu hVs hV hmu
  have hE : 0 ≤ sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP (fun _ p => p.val)
        BP bm J ell cap Vs V mu) f := by
    unfold sourceOriginalSignedJointForwardEnergy434
    exact Finset.sum_nonneg (fun a _ => sq_nonneg _)
  exact hG.trans (mul_le_mul_of_nonneg_right hCost hE)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSource03TiltedMarkedCleanHilbert -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
open SourceOriginalSource03CanonicalPrimeSlice434
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The original tilted law is NOT normalized. Its actual mass is at most
3/2 uniformly over all moving prime alphabets in the genuine BIG lower band.
The baseline retains all N+1 visits, including both boundary visits. -/
theorem eventually_source_original_PHYSICAL_TILT_mass_three_halves434
    (c : ℝ) (hc : 0<c) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
        (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
        (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
        (V : G → ℝ) (hV : ∀ g,0<V g)
        (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=V g)
        (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ)),
      let mu := physicalSourceMuTilde BP bm q (2*Nat.ceil (L^(0.52:ℝ))) V
      (∀ g p,0 < mu g p) ∧ ∀ g,(∑ p : BP g,mu g p) ≤ (3:ℝ)/2 := by
  obtain ⟨L0,hLarge⟩ := source_original_circle_eventual_exp_dominance434
    c 2 0 hc (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop L0] with L hL0
  obtain ⟨hL4,hExp⟩ := hLarge L hL0
  have hL : 1 ≤ L := by linarith
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hpow : L^(0.52:ℝ) ≤ L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0.52:ℝ) ≤ 1)
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hLp.le (0.52:ℝ))).le
  have hExp' : 4*L^2 ≤ Real.exp (L^c) := by
    simpa using hExp 1 (by norm_num) (by simp)
  intro G _ _ BP _ _ bm _ q hq hq1 V hV hHarmonic hmin
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP bm q N V
  have hN : 3*((N+1:ℕ):ℝ) ≤ 6*L+9 := by
    dsimp only [N]
    push_cast
    linarith only [hceil,hpow]
  have hpoly : 6*L+9 ≤ 4*L^2 := by nlinarith only [hL4,sq_nonneg (L-4)]
  have hp (g : G) (p : BP g) : 0<(bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hb (g : G) (p : BP g) : (2:ℝ)/3 ≤ physicalSourceBaseline BP bm q N g p := by
    have hsize := hN.trans (hpoly.trans (hExp'.trans (hmin g p)))
    have hA := (source_original_B26_visit_sum_unit434 q hq hq1 N).2
    have hx : (∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)/(bm g p:ℝ) ≤ 1/3 :=
      (div_le_iff₀ (hp g p)).mpr (by linarith only [hA,hsize])
    dsimp only [physicalSourceBaseline]
    linarith only [hx]
  have hb0 (g : G) (p : BP g) : 0<physicalSourceBaseline BP bm q N g p :=
    lt_of_lt_of_le (by norm_num) (hb g p)
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (hV g) (hp g p)) (hb0 g p))
  refine ⟨hmu,?_⟩
  intro g
  have hpoint (p : BP g) : mu g p ≤ ((3:ℝ)/2)/(V g)*(1/(bm g p:ℝ)) := by
    change 1/(V g*(bm g p:ℝ)*physicalSourceBaseline BP bm q N g p) ≤ _
    calc
      _ ≤ ((3:ℝ)/2)/(V g*(bm g p:ℝ)) := by
        rw [div_le_div_iff₀ (mul_pos (mul_pos (hV g) (hp g p)) (hb0 g p))
          (mul_pos (hV g) (hp g p))]
        have hh := mul_le_mul_of_nonneg_left (hb g p) (mul_pos (hV g) (hp g p)).le
        nlinarith only [hh]
      _ = _ := by field_simp <;> ring
  calc
    _ ≤ ∑ p : BP g,((3:ℝ)/2)/(V g)*(1/(bm g p:ℝ)) :=
      Finset.sum_le_sum (fun p _ => hpoint p)
    _ = ((3:ℝ)/2)/(V g)*(∑ p : BP g,1/(bm g p:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ = (3:ℝ)/2 := by rw [hHarmonic g]; field_simp [ne_of_gt (hV g)]

/-- Quantitative original source03 BIG active×NUMERIC-seen bound for each
canonical comparison pattern, with BOTH endpoint permutations averaged.
The true mu-tilde, FULL prime intervals, oriented original phase, joint
canonical Knu, auxiliary ban and any remaining gates are kept.

This is a BIG block estimate, not a claim about the complete Fock/SMALL
evolution or the coherent sum over RAW and all comparison patterns. -/
theorem eventually_source_original_TRUE_SOURCE03_marked_BIG_CLEAN_Hilbert434
    (cfg : SourceComparisonFixed434)
    (J ell m : ℕ) (hmJ : m ≤ J) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (n : ℕ) (d vmax c0 x Y Hp : ℝ)
        (z : SourceOriginalSource03CanonicalPrimeSlice434 n cfg L d vmax c0)
        (u : SourceComparisonData434 (Fin n) (Fin n) cfg x L Y Hp)
        (hmatch : SourceOriginalSource03CanonicalFieldsMatch434 z u)
        (nu : SourceOriginalProbePattern434 (Fin n) m)
        (Q : ℕ) (hA hB xi zeta theta : ℝ)
        (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
        (o k : ℤ) (ho : o=1 ∨ o= -1) (dsmall : ℕ)
        (aux : SourceBigAux (fun g => {p : ℕ // p ∈ u.Tb g}) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
        (keep : BigGroupPerm (BG := Fin n) (J+ell) →
          BigGroupPerm (BG := Fin n) (J+ell) →
          SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ u.Tb g}) J ell →
          Finset ℕ →
          SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ u.Tb g}) J ell → Prop)
        (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ u.Tb g}) J ell → Finset ℕ → ℂ),
      letI (g : Fin n) (p : {p : ℕ // p ∈ u.Tb g}) : NeZero p.val :=
        ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
      let BP := fun g => {p : ℕ // p ∈ u.Tb g}
      let bm : (g : Fin n) → BP g → ℕ := fun _ p => p.val
      let mu := physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) u.Vbig
      sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
        (sourceOriginalB26NumericPermutationMean434 BP bm J ell m hmJ nu mu
          (fun sigma tau => sourceOriginalB26CanonicalNumericCleanK434 J ell m hmJ nu
            u.Tb u.Vbig Q hA hB xi zeta theta o k dsmall aux (keep sigma tau)) f) ≤
      ((Q:ℝ)^4*(xi⁻¹)^2)^2 *
        ((9:ℝ)/16)^(∑ g : Fin n,sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
        sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f := by
  have hc : 0<cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  filter_upwards [eventually_source_original_PHYSICAL_TILT_mass_three_halves434 cfg.cexp hc]
    with L hMass
  intro n d vmax c0 x Y Hp z u hmatch nu Q hA hB xi zeta theta hhA hhB hxi
    o k ho dsmall aux keep f
  dsimp only
  let BP := fun g : Fin n => {p : ℕ // p ∈ u.Tb g}
  let bm : (g : Fin n) → BP g → ℕ := fun _ p => p.val
  letI (g : Fin n) (p : BP g) : NeZero p.val :=
    ⟨(u.hTbPrime g p.val p.property).ne_zero⟩
  let mu := physicalSourceMuTilde BP bm cfg.q0 (2*Nat.ceil (L^(0.52:ℝ))) u.Vbig
  have hV (g : Fin n) : 0<u.Vbig g := cfg.hv.trans_le (u.hVbig g)
  have hHarmonic (g : Fin n) : (∑ p : BP g,1/(bm g p:ℝ))=u.Vbig g := by
    rw [source_original_canonical_FINSET_subtype_harmonic434]
    exact (source_original_canonical_fields_big_harmonic434 z u hmatch g).symm
  have hTb : u.Tb=z.Tb := hmatch.2.2.1
  have hmin (g : Fin n) (p : BP g) : Real.exp (L^cfg.cexp) ≤ (bm g p:ℝ) := by
    have hp : p.val ∈ z.Tb g := by simpa only [hTb] using p.property
    exact (z.hBigBand g p.val hp).2.1
  obtain ⟨hmu,hmuSum⟩ := hMass BP bm cfg.q0 cfg.hq0.le cfg.hq1.le
    u.Vbig hV hHarmonic hmin
  have hi := source_original_TRUE_SOURCE03_BIG_sigma_label_injective434 z u hmatch
  let K := fun sigma tau => sourceOriginalB26CanonicalNumericCleanK434 J ell m hmJ nu
    u.Tb u.Vbig Q hA hB xi zeta theta o k dsmall aux (keep sigma tau)
  have hK : ∀ sigma tau s S t,‖K sigma tau s S t‖ ≤ (Q:ℝ)^4*(xi⁻¹)^2 := by
    intro sigma tau s S t
    dsimp only [K,sourceOriginalB26CanonicalNumericCleanK434]
    split_ifs
    · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k ho]
      exact source_original_memory_CANONICAL_K_norm434 u.Tb u.Vbig J ell m hmJ nu
        Q hA hB xi hhA hhB hxi aux s t
    · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k ho]
      exact source_original_memory_CANONICAL_K_norm434 u.Tb u.Vbig J ell m hmJ nu
        Q hA hB xi hhA hhB hxi aux t s
    · simp only [norm_zero]
      positivity
  have hh := source_original_B26_NUMERIC_permutation_mean_Hilbert434 BP bm J ell m hmJ nu
    hi mu (fun g p => (hmu g p).le) ((Q:ℝ)^4*(xi⁻¹)^2) (by positivity) K hK f
  have hDelta :
      (∏ g : Fin n,((∑ p : BP g,mu g p)^2/4)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) ≤
      ((9:ℝ)/16)^(∑ g : Fin n,sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀
    · intro g hg
      positivity
    · intro g hg
      apply pow_le_pow_left₀ (by positivity)
      have h0 : 0 ≤ ∑ p : BP g,mu g p :=
        Finset.sum_nonneg (fun p _ => (hmu g p).le)
      have h1 : (∑ p : BP g,mu g p) ≤ (3:ℝ)/2 := hmuSum g
      have hsquare := pow_le_pow_left₀ h0 h1 2
      nlinarith only [hsquare]
  have hE : 0 ≤ sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f := by
    apply Finset.sum_nonneg
    intro S hS
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg
      (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => (hmu g (s g i)).le)))
      (sq_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hDelta (sq_nonneg _)) hE)

end Green64Analytic.CorrelationSquare

end

end

