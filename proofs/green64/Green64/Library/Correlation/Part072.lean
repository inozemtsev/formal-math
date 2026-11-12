module

public import Green64.Library.Correlation.PhysicalSharedFreeCarrierSum
public import Green64.Library.Correlation.Part071
public import Green64.Library.Weights.Part112
public import Green64.Library.Correlation.Part070
public import Green64.Library.Correlation.Part045
public import Green64.Library.Weights.Part017
public import Green64.Library.Weights.StrippedRankPair
public import Green64.Library.Correlation.Part036
public import Green64.Library.Weights.Part099
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part111
public import Green64.Library.Weights.Part043
public import Green64.Library.Correlation.Part066
public import Green64.Library.Correlation.Part033
public import Green64.Library.Weights.Part109
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

/-!
# Correlation / Part072

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalSharedFreeWeighted -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Literal weighted B574 restored comparison on the unchanged global
positive interval. The restored slice is the original unrestricted sum of
physical slices; the arithmetic multiplier is now shared-independent.
This definition is a target, and does not redefine the original H_T. -/
def parityActualWeightedRestoredComparison434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) : ℂ :=
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  ∑ w∈N,∑ wp∈N,
    if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
      parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp *
        (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
          (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
        sourceB574CanonicalRestoredSlice434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) Q h h xi
          (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
            (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
          (1/2 : ℝ) w wp
    else 0

/-- Exact extraction of the proved shared-independent arithmetic and
native auxiliary atom from the original unrestricted shared-array sum.
Both inverse cell masses remain inside the literal restored Knu slice. -/
theorem parity_actual_stripped_weight_shared_sum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (w wp : ℕ) :
    let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    (∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
      parityActualStrippedComparisonWeight434 L hS J m hmJ nu Q h xi rho xi3 Z k F G tw psi
        aux (fun g i => s ⟨g,i⟩) w wp)=
    if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
      parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp *
        (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
          (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
        sourceB574CanonicalRestoredSlice434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) Q h h xi
          (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
            (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
          (1/2 : ℝ) w wp
    else 0 := by
  dsimp only
  unfold parityActualStrippedComparisonWeight434
  dsimp only
  split_ifs
  · rw [←Finset.mul_sum]
    rfl
  · simp only [Finset.sum_const_zero]

/-- Genuine exact weighted restoration interface for one actual comparison
probe and one original typed auxiliary draw. It starts at the previously
proved original comparison aggregate, proves seed/cutoff/core/phase/parity
stripping and finite-carrier transport internally, and ends at the literal
B574 restored slice with the full shared-independent arithmetic multiplier.
No unweighted restoration estimate is substituted for a weighted one. -/
theorem parity_eventually_comparison_weighted_restored434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J)
      (nu : ↥(sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
      (aux : ParityActualProbeAux434 L J m hmJ nu.val)
      (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ),
      (k.natAbs : ℝ)≤L^Ck → 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u,psi u≠0 → (1/64:ℝ)≤u ∧ u≤64) →
    ∀ (F G : PrimeSlotCore) (tw : Bool),
      parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi (-xi3) Z k
        (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
        1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi aux =
      parityActualWeightedRestoredComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k F G tw psi aux := by
  filter_upwards [parity_eventually_actual_shared_carrier_sum434 J CZ] with L hCarrier
  refine ⟨hCarrier.1,?_⟩
  intro hS m hmJ nu aux Q h xi rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
  let ss := Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1)
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let R := fun (s : (g : B645ActualGroup434 L hS) × E g → ℕ) (w wp : ℕ) =>
    parityActualStrippedComparisonWeight434 L hS J m hmJ nu.val Q h xi rho xi3 Z k F G tw psi
      aux (fun g i => s ⟨g,i⟩) w wp
  have hfirst : parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi (-xi3) Z k
        (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
        1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi aux =
      ∑ s∈ss,∑ w∈N,∑ wp∈N,R s w wp := by
    unfold parityActualHarmonicComparisonB574434
    dsimp only
    apply Finset.sum_congr rfl
    intro s hs
    have hsmem : ∀ g i,s ⟨g,i⟩∈b645ActualBand434 L hS g := by
      intro g i
      exact (Fintype.mem_piFinset.mp hs) ⟨g,i⟩
    exact hCarrier.2 hS m hmJ nu.val aux (fun g i => s ⟨g,i⟩) hsmem
      Q h xi rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  calc
    _ = ∑ s∈ss,∑ w∈N,∑ wp∈N,R s w wp := hfirst
    _ = ∑ w∈N,∑ wp∈N,∑ s∈ss,R s w wp :=
      (parity_shared_position_sum_order434 N ss R).symm
    _ = _ := by
      unfold parityActualWeightedRestoredComparison434
      dsimp only
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro wp hwp
      exact parity_actual_stripped_weight_shared_sum434 L hS J m hmJ nu.val Q h xi rho xi3 Z k
        F G tw psi aux w wp
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeHarmonicRestoration -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The existing UNCAPPED original physical H_T equals its literal RAW
branch plus the complete weighted B574 restored comparison aggregate.
The original source is unchanged: the shared core/parity/phase stripping,
source-seed elimination and common finite-carrier transport were proved
from the complete physical construction. Actual Ppart cap insertion and
quantitative restored-to-stripped error estimates remain separate. -/
theorem parity_eventually_harmonic_weighted_restored434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ),
      (k.natAbs : ℝ)≤L^Ck → 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u,psi u≠0 → (1/64:ℝ)≤u ∧ u≤64) →
    ∀ (F G : PrimeSlotCore) (tw : Bool),
      parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
        (parityDyadicDepth434 L) F G (-(rho+xi3)) (-rho) tw 0 psi =
      parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
        (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
        1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi +
      ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
        ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
          parityActualWeightedRestoredComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k
            F G tw psi aux := by
  filter_upwards [parity_eventually_comparison_weighted_restored434 J CZ] with L hJoin
  refine ⟨hJoin.1,?_⟩
  intro hS m hmJ Q h xi rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  have hL : 1<L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hJoin.1
  let I := ↥(sourceOriginalTwoBlockProbePatterns434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
  let W := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let R := parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k W
    1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi
  let C := fun nu : I => ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
    parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi (-xi3) Z k W
      1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi aux
  let B := fun nu : I => ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
    parityActualWeightedRestoredComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k
      F G tw psi aux
  have hCB : (∑ nu : I,C nu)=∑ nu : I,B nu := by
    apply Finset.sum_congr rfl
    intro nu hnu
    change (∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
      parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi (-xi3) Z k W
        1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi aux)=_
    apply Finset.sum_congr rfl
    intro aux haux
    exact hJoin.2 hS m hmJ nu aux Q h xi rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  have he := parity_harmonic_physical_B574_comparison_aggregate434 L hL hS J m hmJ
    Q h xi (-xi3) Z Ck k (parityDyadicDepth434 L) F G (-(rho+xi3)) (-rho) tw 0 psi
  change parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
      (parityDyadicDepth434 L) F G (-(rho+xi3)) (-rho) tw 0 psi=R+∑ nu : I,C nu at he
  exact he.trans (congrArg (fun z : ℂ => R+z) hCB)

/-- Exactly ONE external Z survives the complete original H_T join and
all unrestricted shared restoration sums. It is distributed only once
across the RAW branch and the original comparison/auxiliary family. -/
theorem parity_eventually_harmonic_outer_Z_weighted_restored434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ),
      (k.natAbs : ℝ)≤L^Ck → 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u,psi u≠0 → (1/64:ℝ)≤u ∧ u≤64) →
    ∀ (F G : PrimeSlotCore) (tw : Bool),
      (Z : ℂ)*parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
        (parityDyadicDepth434 L) F G (-(rho+xi3)) (-rho) tw 0 psi =
      (Z : ℂ)*parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
        (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
        1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi +
      ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
        ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
          (Z : ℂ)*parityActualWeightedRestoredComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k
            F G tw psi aux := by
  filter_upwards [parity_eventually_harmonic_weighted_restored434 J CZ] with L hJoin
  refine ⟨hJoin.1,?_⟩
  intro hS m hmJ Q h xi rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  have he := hJoin.2 hS m hmJ Q h xi rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  have hscale := congrArg (fun z : ℂ => (Z : ℂ)*z) he
  simpa only [mul_add,Finset.mul_sum] using hscale
end Green64Analytic.Parity

end

end

/-! ## RawPhysicalSlots -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- Literal RAW retains every first-J slot as shared. The additional
endpoint slot remains free; no comparison probe is used in this definition. -/
def parityRawSharedSlots434 (J : ℕ) : Finset (Fin (J+1)) :=
  sourceOriginalSharedSlots434 J 1 ∅

/-- The RAW shared indices are exactly the original first J indices. -/
theorem parity_raw_shared_slot_mem434 (J : ℕ) (i : Fin (J+1)) :
    i ∈ parityRawSharedSlots434 J ↔ i.val < J := by
  classical
  unfold parityRawSharedSlots434 sourceOriginalSharedSlots434
  simp only [Finset.sdiff_empty,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,rfl⟩
    exact j.isLt
  · intro hi
    refine ⟨⟨i.val,hi⟩,?_⟩
    apply Fin.ext
    rfl

/-- There are J shared RAW slots, including when J=0. -/
theorem parity_raw_shared_slot_card434 (J : ℕ) :
    (parityRawSharedSlots434 J).card = J := by
  simpa only [parityRawSharedSlots434,Finset.card_empty,Nat.sub_zero] using
    source_original_shared_slot_card434 J 1 ∅

/-- Enumeration of the genuine RAW free endpoint slot. -/
def parityRawFreeSlotEquiv434 (J : ℕ) :
    Fin 1 ≃ {i : Fin (J+1) // i ∉ parityRawSharedSlots434 J} := by
  simpa only [parityRawSharedSlots434,Finset.card_empty,Nat.add_zero] using
    sourceOriginalFreeSlotEquiv434 J 1 ∅

/-- The complement contains the single genuine endpoint slot. -/
theorem parity_raw_free_slot_card434 (J : ℕ) :
    Fintype.card {i : Fin (J+1) // i ∉ parityRawSharedSlots434 J} = 1 := by
  calc
    _ = Fintype.card (Fin 1) := Fintype.card_congr (parityRawFreeSlotEquiv434 J).symm
    _ = 1 := Fintype.card_fin 1

/-- Every original SMALL RAW shared set is the literal first-J set. -/
theorem parity_raw_small_shared434 {SG : Type} (J : ℕ) (g : SG) :
    sourceSmallShared J 1 g = parityRawSharedSlots434 J := by
  classical
  ext i
  simp only [sourceSmallShared,Finset.mem_filter,Finset.mem_univ,true_and,
    parity_raw_shared_slot_mem434]

/-- The none-index original BIG pattern shares every first-J slot. -/
theorem parity_raw_big_shared434 (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (g : sourceNativeOriginalBigType434 20 L) :
    sourceBigShared J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none) g =
      parityRawSharedSlots434 J := by
  classical
  ext i
  simp [sourceBigShared,sourceOriginalMemoryRawComparisonPattern434,
    parity_raw_shared_slot_mem434]

/-- The original RAW auxiliary product has no factors and equals one.
This concerns only auxiliary draws, not the nontrivial shared product DR. -/
theorem parity_raw_aux_mass_one434 (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (aux : SourceBigAux (SourceNativeMemoryBP434 20 L) J m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none)) :
    sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
      (sourceNativeOriginalVbig434 20 L)
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none) aux = 1 := by
  classical
  unfold sourceAuxMass
  apply Finset.prod_eq_one
  intro g hg
  letI : IsEmpty ↥((sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L)
    (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none).free g) :=
    ⟨fun i => by simpa [sourceOriginalMemoryRawComparisonPattern434] using i.property⟩
  exact Fintype.prod_empty _

/-- The original RAW auxiliary exclusion is vacuous on the full physical
states because its first-J auxiliary index is empty. Endpoint-free slots are
still present in the physical states and in their original half weights. -/
theorem parity_raw_aux_ban434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (aux : SourceBigAux (SourceNativeMemoryBP434 20 L) J m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none))
    (x y : MemoryIndependentState
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1) :
    memoryIndependentAuxBan
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none) aux x y := by
  intro g i j
  exact False.elim (by
    simpa [sourceOriginalMemoryRawComparisonPattern434] using i.property)
end Green64Analytic.Parity

end

end

/-! ## RawPhysicalFrame -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The literal none-index frame with the four original identity permutations. -/
def parityRawIdentityFrame434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) :
    MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ) :=
  parityBaseIdentityFrame434 (SG:=SourceNativeMemorySG434 20 L hS)
    (SourceNativeMemoryBP434 20 L) J 1 m
    (sourceOriginalMemoryRawComparisonPattern434
      (sourceNativeOriginalBigBlockA434 20 L)
      (sourceNativeOriginalBigBlockB434 20 L) J m hmJ)
    (parityHarmonicRawBase434 L J m hmJ)

/-- RAW still has one unshared endpoint mark in each SMALL and BIG group. -/
theorem parity_raw_unshared_slot_count434 (J : ℕ) :
    Green64SmallHaar.unsharedSlots (J+1) (parityRawSharedSlots434 J) = 1 := by
  simp only [Green64SmallHaar.unsharedSlots,parity_raw_shared_slot_card434,
    Nat.add_sub_cancel_left]

/-- The genuine RAW row mass has one inverse original V in every full group. -/
def parityRawUnsharedMass434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) : ℝ :=
  ∏ g : B645ActualGroup434 L hS,
    1 / Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) g

/-- Exact original physical shared labels, including both group families. -/
theorem parity_raw_shared_restriction_iff434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (n np : ℕ)
    (x : ParityActualPositionFibre434 L hS J n)
    (y : ParityActualPositionFibre434 L hS J np) :
    b650NativeFrameShares434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ) x.val y.val
      (parityRawIdentityFrame434 L hS J m hmJ) ↔
    parityPhysicalSharedRestriction434 (J+1) (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
      (parityActualPositionMarks434 L hS J n x) =
    parityPhysicalSharedRestriction434 (J+1) (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
      (parityActualPositionMarks434 L hS J np y) := by
  rw [← parity_physical_shared_guard_restriction434]
  unfold b650NativeFrameShares434 parityRawIdentityFrame434 parityBaseIdentityFrame434
  dsimp only [parityHarmonicRawBase434]
  constructor
  · intro h g i
    cases g with
    | inl g =>
      have hi : i.val∈sourceSmallShared J 1 g := by
        simpa only [parity_raw_small_shared434] using i.property
      exact congrArg Subtype.val (h.1 g i.val hi)
    | inr g =>
      have hi : i.val∈sourceBigShared J 1 m
          (sourceOriginalMemoryRawComparisonPattern434
            (sourceNativeOriginalBigBlockA434 20 L)
            (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none) g := by
        simpa only [parity_raw_big_shared434] using i.property
      exact congrArg Subtype.val (h.2 g i.val hi)
  · intro h
    constructor
    · intro g j hj
      apply Subtype.ext
      exact h (Sum.inl g) ⟨j,by simpa only [parity_raw_small_shared434] using hj⟩
    · intro g j hj
      apply Subtype.ext
      exact h (Sum.inr g) ⟨j,by simpa only [parity_raw_big_shared434] using hj⟩

/-- The labelled shared product is the actual RAW native DR; it is not set to one. -/
theorem parity_raw_readout_shared_divisor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (n : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) :
    sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
      (fun g i => parityActualPositionMarks434 L hS J n x g i.val) =
    parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ) x.val
      (parityRawIdentityFrame434 L hS J m hmJ) := by
  unfold sourceB574SharedDilation434 parityFrameSharedD434
  simp only [parityRawIdentityFrame434,parityBaseIdentityFrame434,parityHarmonicRawBase434,
    Equiv.refl_apply,parity_raw_small_shared434,parity_raw_big_shared434,
    Finset.prod_coe_sort,Fintype.prod_sum_type]
  rfl

/-- The full original RAW divisor is exactly DR, because only DC equals one. -/
theorem parity_raw_frame_divisor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (n : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) :
    b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ) x.val
      (parityRawIdentityFrame434 L hS J m hmJ) =
    sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
      (fun g i => parityActualPositionMarks434 L hS J n x g i.val) := by
  rw [parity_frame_D_factor434,
    parity_actual_RAW_frame_aux_D_one434 L hS J m hmJ _ rfl,mul_one]
  exact (parity_raw_readout_shared_divisor434 L hS J m hmJ n x).symm

/-- Literal RAW physical fibre term, independently retaining the source
harmonic test, the two original row halves, and original Mellin edge with K=1. -/
def parityRawHarmonicFibreTerm434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) (n np : ℕ)
    (x : ParityActualPositionFibre434 L hS J n)
    (y : ParityActualPositionFibre434 L hS J np) : ℂ :=
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E
    (fun g i => parityActualPositionMarks434 L hS J n x g i.val)
  if (2*k)≠0 ∧
      parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
        parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y) ∧
      (np : ℤ)=(n : ℤ)+(2*k)*(d : ℤ) then
    (parityRawUnsharedMass434 L hS : ℂ) *
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi (n : ℤ) (np : ℤ) d *
    (parityActualPositionHalf434 L hS J n (1/2 : ℝ) x : ℂ) *
    (parityActualPositionHalf434 L hS J np (1/2 : ℝ) y : ℂ) *
    originalEdgeScalar 1 zeta 0 d 1 (2*k)
  else 0

/-- The original none-index harmonic summand is the literal RAW fibre term.
No canonical comparison kernel or empty comparison probe is substituted. -/
theorem parity_raw_base_fibre_term434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (positions : Finset ℤ) (n np : parityPositiveNaturalPositions434 positions)
    (x : ParityActualPositionFibre434 L hS J n.val)
    (y : ParityActualPositionFibre434 L hS J np.val) :
    parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
      (parityHarmonicRawBase434 L J m hmJ)
      (parityActualNaturalState434 L hS J positions n x)
      (parityActualNaturalState434 L hS J positions np y) =
    parityRawHarmonicFibreTerm434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n.val np.val x y := by
  classical
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E
    (fun g i => parityActualPositionMarks434 L hS J n.val x g i.val)
  have hD := parity_raw_frame_divisor434 L hS J m hmJ n.val x
  have hsh := parity_raw_shared_restriction_iff434 L hS J m hmJ n.val np.val x y
  have hb := parity_raw_aux_ban434 L hS J m hmJ (parityHarmonicRawAux434 L J m hmJ) x.val y.val
  dsimp only [parityRawIdentityFrame434] at hD hsh
  have ho : (1 : ℤ)=1 ∨ (1 : ℤ)=-1 := Or.inl rfl
  unfold parityHarmonicBaseSummand434 parityRawHarmonicFibreTerm434
  dsimp only
  unfold parityPermutationMarginalScalar434 b650IntegerFrameAllowed434
  dsimp only [parityActualNaturalState434]
  simp only [hD,hsh,ho,true_and,one_mul,memoryOrientationK,ite_true]
  dsimp only [parityHarmonicRawBase434]
  simp only [hb,parity_raw_aux_mass_one434,sourceOriginalMemoryRawComparisonK434,one_mul]
  dsimp only [parityBaseIdentityFrame434]
  simp only [hb,true_or,true_and]
  by_cases hk : (2*k)≠0
  <;> by_cases hs : parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n.val x)=
    parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np.val y)
  <;> by_cases ht : (np.val : ℤ)=(n.val : ℤ)+(2*k)*(d : ℤ)
  all_goals dsimp only [d,E] at hs ht
  all_goals simp only [hk,hs,ht,ite_true,ite_false,true_and,false_and,and_true,and_false,
    zero_mul,mul_zero]
  all_goals
    simp only [parityRawUnsharedMass434,parity_raw_small_shared434,parity_raw_big_shared434,
      parity_raw_unshared_slot_count434,pow_one,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
      parityActualPositionHalf434,Finset.prod_mul_distrib,Complex.ofReal_mul]
  all_goals split_ifs <;> try ring
  all_goals omega
end Green64Analytic.Parity

end

end

/-! ## RawPhysicalNumeric -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Independent literal RAW numeric weight. The original physical shift,
harmonic test, row halves and pure Mellin phase are retained. Its kernel is
one; there is no canonical comparison, auxiliary law, or cell normalization. -/
def parityRawHarmonicNumericWeight434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) (n np d : ℕ) : ℂ :=
  if (2*k)≠0 ∧ (np : ℤ)=(n : ℤ)+(2*k)*(d : ℤ) then
    (parityRawUnsharedMass434 L hS : ℂ) *
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi (n : ℤ) (np : ℤ) d *
    (sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) (1/2 : ℝ) n : ℂ) *
    (sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) (1/2 : ℝ) np : ℂ) *
    sourceOriginalPureMellinPhase434 zeta d
  else 0

/-- Exact physical-to-numeric RAW scalar on every full native fibre pair.
The only shared guard compares all retained marks in BOTH group families. -/
theorem parity_raw_fibre_numeric434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) (n np : ℕ)
    (x : ParityActualPositionFibre434 L hS J n)
    (y : ParityActualPositionFibre434 L hS J np) :
    let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
    let rx := parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)
    let ry := parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y)
    parityRawHarmonicFibreTerm434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n np x y =
      if rx=ry then
        parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n np
          (sourceB574SharedDilation434 (J+1) E (fun g i => rx ⟨g,i⟩))
      else 0 := by
  classical
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E
    (fun g i => parityActualPositionMarks434 L hS J n x g i.val)
  by_cases hs : parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
      parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y)
  · rw [if_pos hs]
    unfold parityRawHarmonicFibreTerm434 parityRawHarmonicNumericWeight434
    dsimp only
    rw [parity_actual_position_half_exact434 L hS J n (1/2 : ℝ) (by norm_num) x,
      parity_actual_position_half_exact434 L hS J np (1/2 : ℝ) (by norm_num) y,
      parity_original_edge_zero_fourier434]
    simp only [one_mul]
    by_cases ht : (2*k)≠0 ∧ (np : ℤ)=(n : ℤ)+(2*k)*(d : ℤ)
    · have hg : (2*k)≠0 ∧
          parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
            parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y) ∧
          (np : ℤ)=(n : ℤ)+(2*k)*(d : ℤ) := ⟨ht.1,hs,ht.2⟩
      rw [if_pos hg]
      dsimp only [parityPhysicalSharedRestriction434]
      dsimp only [d,E] at ht
      simp only [ht.1,ht.2,and_true,ite_true]
      all_goals split_ifs with hk
      all_goals first | rfl | exact False.elim (hk ht.1)
    · have hg : ¬((2*k)≠0 ∧
          parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
            parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y) ∧
          (np : ℤ)=(n : ℤ)+(2*k)*(d : ℤ)) := fun h => ht ⟨h.1,h.2.2⟩
      rw [if_neg hg]
      dsimp only [parityPhysicalSharedRestriction434]
      dsimp only [d,E] at ht
      simp only [ht,ite_false]
  · rw [if_neg hs]
    unfold parityRawHarmonicFibreTerm434
    dsimp only
    have hg : ¬((2*k)≠0 ∧
        parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
          parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y) ∧
        (np : ℤ)=(n : ℤ)+(2*k)*(d : ℤ)) := fun h => hs h.2.1
    rw [if_neg hg]

/-- All full RAW physical fibres disintegrate over every original shared
array and both complete numeric carriers. Dirty and repeated arrays remain
in the sum; their impossible completion fibres vanish without assumptions. -/
theorem parity_raw_fixed_positions_shared434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) (n np : ℕ) :
    let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
    (∑ x : ParityActualPositionFibre434 L hS J n,
      ∑ y : ParityActualPositionFibre434 L hS J np,
        parityRawHarmonicFibreTerm434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n np x y) =
    ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
      ∑ a∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s n,
      ∑ b∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s np,
        parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n np
          (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)) := by
  classical
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let P := b645ActualBand434 L hS
  let R := parityPhysicalSharedRestriction434 (J+1) E
  let W := fun s : (g : B645ActualGroup434 L hS) × E g → ℕ =>
    parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n np
      (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩))
  calc
    _ = ∑ x : ParityActualPositionFibre434 L hS J n,
        ∑ y : ParityActualPositionFibre434 L hS J np,
          if R (parityActualPositionMarks434 L hS J n x)=R (parityActualPositionMarks434 L hS J np y) then
            W (R (parityActualPositionMarks434 L hS J n x)) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact parity_raw_fibre_numeric434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n np x y
    _ = ∑ a∈bigMarkLists P (fun _ => J+1) n,
        ∑ b∈bigMarkLists P (fun _ => J+1) np,
          if R a=R b then W (R a) else 0 :=
      parity_actual_position_pair_reindex434 L hS J n np (fun a b => if R a=R b then W (R a) else 0)
    _ = ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => P i.1),
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W (R a) := by
      simpa only [parity_physical_shared_guard_restriction434] using
        parity_physical_pair_shared_fibres434 P (J+1) E n np (fun a _ => W (R a))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hra : R a=s := by
        rw [parity_physical_completions_restriction_fibre434] at ha
        exact (Finset.mem_filter.mp ha).2
      rw [hra]
end Green64Analytic.Parity

end

end

/-! ## RawPhysicalQuotient -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Actual r20 RAW marks force the full labelled shared product to divide
their physical integer. The proof uses the literal none-frame divisor theorem. -/
theorem parity_raw_shared_readout_divides434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n : ℕ) (x : ParityActualPositionFibre434 L hS J n) :
    sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
      (fun g i => parityActualPositionMarks434 L hS J n x g i.val) ∣ n := by
  let z : B654ActualParityState434 L hS J {(n : ℤ)} :=
    ⟨(⟨(n : ℤ),by simp⟩,x.val),x.property⟩
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L)
    (sourceNativeOriginalBigBlockB434 20 L) J 0 (Nat.zero_le J)
  have hd := parity_actual_frame_shared_divides434 L hL hS J 0 pats
    {(n : ℤ)} z (parityRawIdentityFrame434 L hS J 0 (Nat.zero_le J))
  change (parityFrameSharedD434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 0 pats x.val
    (parityRawIdentityFrame434 L hS J 0 (Nat.zero_le J)) : ℤ) ∣ (n : ℤ) at hd
  rw [← parity_raw_readout_shared_divisor434] at hd
  exact_mod_cast hd

/-- Every member of the complete RAW numeric carrier has genuine shared
divisibility, without a clean-array or injectivity hypothesis on shared labels. -/
theorem parity_raw_completion_shared_divides434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (s : (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J → ℕ)
    (n : ℕ) (a : B645ActualGroup434 L hS → Fin (J+1) → ℕ)
    (ha : a∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1)
      (fun _ => parityRawSharedSlots434 J) s n) :
    sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
      (fun g i => s ⟨g,i⟩) ∣ n := by
  rw [parity_physical_completions_restriction_fibre434] at ha
  obtain ⟨ha,hs⟩ := Finset.mem_filter.mp ha
  let e := parityActualFixedPositionMarksEquiv434 L hS J n
  let x := e.symm ⟨a,ha⟩
  have hx : parityActualPositionMarks434 L hS J n x = a := by
    change (e (e.symm ⟨a,ha⟩)).val=a
    rw [Equiv.apply_symm_apply]
  have hshared : (fun g i => parityActualPositionMarks434 L hS J n x g i.val) =
      (fun g i => s ⟨g,i⟩) := by
    funext g i
    rw [hx]
    exact congrFun hs ⟨g,i⟩
  have hd := parity_raw_shared_readout_divides434 L hL hS J n x
  rw [hshared] at hd
  exact hd

/-- Nondisible physical integers have no RAW completion fibre. -/
theorem parity_raw_completions_empty_of_not_shared_dvd434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (s : (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J → ℕ)
    (n : ℕ)
    (hn : ¬sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J)
      (fun g i => s ⟨g,i⟩) ∣ n) :
    parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1)
      (fun _ => parityRawSharedSlots434 J) s n = ∅ := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    exact False.elim (hn (parity_raw_completion_shared_divides434 L hL hS J s n a ha))
  · intro ha
    simp at ha

/-- Exact multiplication/quotient reindex of BOTH complete RAW endpoint
carriers. Every coupled endpoint weight is retained at its full physical
integers DR*w and DR*wp; no quotient/cardinality loss is introduced. -/
theorem parity_raw_completion_pair_quotient434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (s : (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J → ℕ)
    (positions : Finset ℤ)
    (F : ℕ → ℕ → (B645ActualGroup434 L hS → Fin (J+1) → ℕ) →
      (B645ActualGroup434 L hS → Fin (J+1) → ℕ) → ℂ) :
    let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
    let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
    (∑ n∈parityPositiveNaturalPositions434 positions,
      ∑ np∈parityPositiveNaturalPositions434 positions,
      ∑ a∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s n,
      ∑ b∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s np,
        F n np a b) =
    ∑ w∈paritySharedQuotientPositions434 positions d,
      ∑ wp∈paritySharedQuotientPositions434 positions d,
      ∑ a∈sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1) E
        (fun g i => s ⟨g,i⟩) w,
      ∑ b∈sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1) E
        (fun g i => s ⟨g,i⟩) wp,
        F (d*w) (d*wp) a b := by
  classical
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
  let C := parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s
  have hempty (n : ℕ) (hn : ¬d∣n) : C n=∅ :=
    parity_raw_completions_empty_of_not_shared_dvd434 L hL hS J s n hn
  calc
    _ = ∑ w∈paritySharedQuotientPositions434 positions d,
        ∑ np∈parityPositiveNaturalPositions434 positions,
        ∑ a∈C (d*w),∑ b∈C np,F (d*w) np a b := by
      apply parity_shared_quotient_weighted_sum434 positions d
      intro n hn hnd
      change (∑ np∈parityPositiveNaturalPositions434 positions,
        ∑ a∈C n,∑ b∈C np,F n np a b)=0
      simp only [hempty n hnd,Finset.sum_empty,Finset.sum_const_zero]
    _ = ∑ w∈paritySharedQuotientPositions434 positions d,
        ∑ wp∈paritySharedQuotientPositions434 positions d,
        ∑ a∈C (d*w),∑ b∈C (d*wp),F (d*w) (d*wp) a b := by
      apply Finset.sum_congr rfl
      intro w hw
      apply parity_shared_quotient_weighted_sum434 positions d
      intro np hnp hnpd
      change (∑ a∈C (d*w),∑ b∈C np,F (d*w) np a b)=0
      simp only [hempty np hnpd,Finset.sum_empty,Finset.sum_const_zero]
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## RawPhysicalAggregate -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- Independent full numerical RAW construction: all J shared slots, both
exact finite quotient carriers, both complete labelled endpoint arrays, and
the original RAW numeric weight. A supplied endpoint weight stays evaluated
at the physical integers DR*w and DR*wp. -/
def parityRawHarmonicNumericAggregate434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ)
    (psi : ℝ → ℂ) (Wgt : ℕ → ℕ → ℂ) : ℂ :=
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
    let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
    ∑ w∈paritySharedQuotientPositions434 positions d,
    ∑ wp∈paritySharedQuotientPositions434 positions d,
    ∑ a∈sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1) E (fun g i => s ⟨g,i⟩) w,
    ∑ b∈sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1) E (fun g i => s ⟨g,i⟩) wp,
      Wgt (d*w) (d*wp) *
      parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi (d*w) (d*wp) d

/-- The true original none-index physical RAW sum equals the independent
full numeric shared/quotient construction. This proves the carrier identity
from the original frame, without assuming a desired aggregate equality or
identifying RAW with a comparison kernel of an empty probe. -/
theorem parity_raw_endpoint_weight_numeric_aggregate434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) (Wgt : ℕ → ℕ → ℂ) :
    parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi Wgt =
    parityRawHarmonicNumericAggregate434 L hS J zeta Z k positions lo hi F G t1 t2 tw v psi Wgt := by
  classical
  unfold parityActualEndpointWeightedRawPositiveFibreSum434 parityRawHarmonicNumericAggregate434
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let P := b645ActualBand434 L hS
  let N := parityPositiveNaturalPositions434 positions
  let ss := Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => P i.1)
  let D := fun s : (g : B645ActualGroup434 L hS) × E g → ℕ =>
    sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
  let NW := fun s : (g : B645ActualGroup434 L hS) × E g → ℕ => fun n np : ℕ =>
    parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n np (D s)
  let W := fun s n np => Wgt n np * NW s n np
  calc
    _ = ∑ n : N,∑ np : N,∑ s∈ss,
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n.val,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np.val,W s n.val np.val := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro np hnp
      calc
        _ = Wgt n.val np.val *
          (∑ x : ParityActualPositionFibre434 L hS J n.val,
            ∑ y : ParityActualPositionFibre434 L hS J np.val,
              parityRawHarmonicFibreTerm434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n.val np.val x y) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          rw [parity_raw_base_fibre_term434 L hS J m hmJ Q h xi zeta Z k
            lo hi F G t1 t2 tw v psi positions n np x y]
        _ = Wgt n.val np.val *
          (∑ s∈ss,∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n.val,
            ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np.val,NW s n.val np.val) :=
          congrArg (fun z : ℂ => Wgt n.val np.val*z)
            (parity_raw_fixed_positions_shared434 L hS J zeta Z k lo hi F G t1 t2 tw v psi n.val np.val)
        _ = _ := by simp only [Finset.mul_sum]; rfl
    _ = ∑ n∈N,∑ np∈N,∑ s∈ss,
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W s n np := by
      let B := fun n np : ℕ => ∑ s∈ss,
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W s n np
      change (∑ n : N,∑ np : N,B n.val np.val)=∑ n∈N,∑ np∈N,B n np
      calc
        _ = ∑ n∈N,∑ np : N,B n np.val :=
          Finset.sum_coe_sort N (fun n => ∑ np : N,B n np.val)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          exact Finset.sum_coe_sort N (B n)
    _ = ∑ s∈ss,∑ n∈N,∑ np∈N,
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W s n np :=
      parity_shared_position_sum_order434 N ss (fun s n np =>
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W s n np)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      exact parity_raw_completion_pair_quotient434 L hL hS J s positions
        (fun n np _ _ => W s n np)
end Green64Analytic.Parity

end

end

/-! ## RawPhysicalSlice -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The literal kernel-one RAW physical slice. Both original full-group
prefactors, both squared native physical halves, one shared harmonic inverse,
and both COMPLETE labelled completion sums are retained. -/
def parityRawPhysicalSlice434 {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (P : G → Finset ℕ) (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (s : ∀ g : G,parityRawSharedSlots434 J → ℕ) : ℂ :=
  let E := fun _ : G => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E s
  (∏ g,((V g : ℂ)^(J+1))⁻¹) * (∏ g,((V g : ℂ)^1)⁻¹) *
    (((sourcePhysicalGroupedHalf434 P (J+1) q (d*w))^2 : ℝ) : ℂ) *
    (((sourcePhysicalGroupedHalf434 P (J+1) q (d*wp))^2 : ℝ) : ℂ) * (d : ℂ)⁻¹ *
    (∑ a∈sourceB574LabelledCompletions434 P (J+1) E s w,
      ∑ b∈sourceB574LabelledCompletions434 P (J+1) E s wp,(1 : ℂ))

/-- Genuine full physical RAW envelope from the original dirty B574 law,
with J shared and exactly one free endpoint slot per group. The kernel bound
is one, so no comparison cell loss or Q/xi factor is introduced. -/
theorem parity_raw_physical_slice_bound434 {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (P : G → Finset ℕ) (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (s : ∀ g : G,parityRawSharedSlots434 J → ℕ)
    (hq : 0<q) (hq1 : q≤1) (hV : ∀ g,0≤V g)
    (hP : ∀ g p,p∈P g → p.Prime) (hs : ∀ g i,s g i∈P g)
    (hDisj : ∀ g h p,p∈P g → p∈P h → g=h) :
    ‖parityRawPhysicalSlice434 J P V q w wp s‖ ≤
      q^(-2*((J+1)*Fintype.card G : ℝ)) *
      sourceB574SharedMass434 (J+1) (fun _ : G => parityRawSharedSlots434 J) V s *
      ‖actualBigMarkDecoration P (fun _ => 1) q V (fun _ => 1) w‖ *
      ‖actualBigMarkDecoration P (fun _ => 1) q V (fun _ => 1) wp‖ := by
  unfold parityRawPhysicalSlice434
  dsimp only
  rw [source_B574_true_labelled_completions_exact434 _ _ _ _ w hs hDisj,
    source_B574_true_labelled_completions_exact434 _ _ _ _ wp hs hDisj]
  simpa only [mul_one,Nat.cast_add,Nat.cast_one] using
    source_B574_actual_dirty_physical_harmonic_pair434 P (J+1)
      (fun _ : G => parityRawSharedSlots434 J) s (fun _ => 1)
      (fun _ => parityRawFreeSlotEquiv434 J) V q w wp hq hq1 hV hP hs hDisj
      (fun _ => by rw [parity_raw_shared_slot_card434])
      (fun _ _ => (1 : ℂ)) 1 (by norm_num) (fun _ _ _ _ => by simp)

/-- The single original state mass and the genuine RAW row masses give
exactly BOTH full-P physical prefactors with the correct endpoint-free count. -/
theorem parity_raw_slice_mass_prefactors434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ) :
    ((b657ActualStateMass434 L hS J * parityRawUnsharedMass434 L hS : ℝ) : ℂ) =
      (∏ g : B645ActualGroup434 L hS,
        (((Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
          (sourceNativeOriginalVbig434 20 L) g : ℝ) : ℂ)^(J+1))⁻¹) *
      (∏ g : B645ActualGroup434 L hS,
        (((Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
          (sourceNativeOriginalVbig434 20 L) g : ℝ) : ℂ)^1)⁻¹) := by
  unfold b657ActualStateMass434 b650IntegerStateMass434 parityRawUnsharedMass434
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
  push_cast
  simp only [one_div,pow_one]

/-- Literal numeric RAW scalar supplies one shared inverse and the two
physical half squares. Its endpoint arithmetic stays at DR*w and DR*wp;
only the true shift and cutoff cancel DR, with DC=1. -/
theorem parity_raw_numeric_weight_shared_scalar434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (d w wp : ℕ) (hd : 0<d) (hw : 0<w) (hwp : 0<wp)
    (x : ParityActualPositionFibre434 L hS J (d*w))
    (y : ParityActualPositionFibre434 L hS J (d*wp)) :
    parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi (d*w) (d*wp) d =
      if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
        parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d 1 w wp *
        ((b657ActualStateMass434 L hS J * parityRawUnsharedMass434 L hS : ℝ) : ℂ) *
        (((sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) (1/2 : ℝ) (d*w))^2 : ℝ) : ℂ) *
        (((sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) (1/2 : ℝ) (d*wp))^2 : ℝ) : ℂ) *
        (d : ℂ)⁻¹
      else 0 := by
  have hstep := parity_harmonic_shared_step_iff434 d 1 w wp hd k
  simp only [Nat.mul_one,Nat.cast_one,mul_one] at hstep
  have hp := parity_actual_harmonic_shared_scalar434 L hS J zeta Z lo hi F G t1 t2 tw v psi
    d 1 w wp hd hw hwp x y
  simp only [Nat.mul_one] at hp
  unfold parityRawHarmonicNumericWeight434
  simp only [hstep]
  split_ifs
  · calc
      _ = (parityRawUnsharedMass434 L hS : ℂ) *
          (parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi
            ((d*w : ℕ) : ℤ) ((d*wp : ℕ) : ℤ) d * sourceOriginalPureMellinPhase434 zeta d) *
          (sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) (1/2 : ℝ) (d*w) : ℂ) *
          (sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) (1/2 : ℝ) (d*wp) : ℂ) := by ring
      _ = _ := by
        rw [hp,parity_actual_position_half_exact434 L hS J (d*w) (1/2 : ℝ) (by norm_num) x,
          parity_actual_position_half_exact434 L hS J (d*wp) (1/2 : ℝ) (by norm_num) y]
        push_cast
        ring
  · rfl

/-- Exact RAW completion-sum factorization into the original shared
arithmetic and the independently defined kernel-one physical slice. Empty
or dirty fibres require no exceptional assumption; both sums remain complete. -/
theorem parity_raw_numeric_slice_factor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (s : (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J → ℕ)
    (w wp : ℕ)
    (hd : 0<sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) (fun g i => s ⟨g,i⟩))
    (hw : 0<w) (hwp : 0<wp) :
    let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
    let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
    (∑ a∈sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1) E (fun g i => s ⟨g,i⟩) w,
      ∑ b∈sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1) E (fun g i => s ⟨g,i⟩) wp,
        parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi (d*w) (d*wp) d) =
      if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
        parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d 1 w wp *
        parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2 : ℝ) w wp (fun g i => s ⟨g,i⟩)
      else 0 := by
  classical
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
  let A := parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d 1 w wp
  let B : ℂ := (∏ g,((V g : ℂ)^(J+1))⁻¹) * (∏ g,((V g : ℂ)^1)⁻¹) *
    (((sourcePhysicalGroupedHalf434 P (J+1) (1/2 : ℝ) (d*w))^2 : ℝ) : ℂ) *
    (((sourcePhysicalGroupedHalf434 P (J+1) (1/2 : ℝ) (d*wp))^2 : ℝ) : ℂ) * (d : ℂ)⁻¹
  have hp (a : B645ActualGroup434 L hS → Fin (J+1) → ℕ)
      (ha : a∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) w)
      (b : B645ActualGroup434 L hS → Fin (J+1) → ℕ)
      (hb : b∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) wp) :
      parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi (d*w) (d*wp) d =
        if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then A*B else 0 := by
    change a∈parityPhysicalCompletionsAt434 P (J+1) E s (d*w) at ha
    change b∈parityPhysicalCompletionsAt434 P (J+1) E s (d*wp) at hb
    rw [parity_physical_completions_restriction_fibre434] at ha hb
    let x := (parityActualFixedPositionMarksEquiv434 L hS J (d*w)).symm
      ⟨a,(Finset.mem_filter.mp ha).1⟩
    let y := (parityActualFixedPositionMarksEquiv434 L hS J (d*wp)).symm
      ⟨b,(Finset.mem_filter.mp hb).1⟩
    have h := parity_raw_numeric_weight_shared_scalar434 L hS J zeta Z k lo hi F G
      t1 t2 tw v psi d w wp hd hw hwp x y
    rw [parity_raw_slice_mass_prefactors434] at h
    simpa only [A,B,V,P,mul_assoc] using h
  unfold parityRawPhysicalSlice434
  dsimp only
  change (∑ a∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) w,
    ∑ b∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) wp,
      parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi (d*w) (d*wp) d) =
    if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then A*(B*
      (∑ a∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) w,
       ∑ b∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) wp,(1 : ℂ))) else 0
  by_cases hg : (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k
  · rw [if_pos hg]
    simp only [Finset.mul_sum,mul_one]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    have h := hp a ha b hb
    rw [if_pos hg] at h
    exact h
  · rw [if_neg hg]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have h := hp a ha b hb
    rw [if_neg hg] at h
    exact h
end Green64Analytic.Parity

end

end

/-! ## RawHarmonicPhysical -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- Independent full physical RAW slice aggregate. The two endpoint weights
and endpoint arithmetic remain on the physical integers. Only the proved
signed shift and cutoff use the cancelled common DR and literal DC=1. -/
def parityRawHarmonicPhysicalAggregate434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ)
    (psi : ℝ → ℂ) (Wgt : ℕ → ℕ → ℂ) : ℂ :=
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
    let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
    ∑ w∈paritySharedQuotientPositions434 positions d,
    ∑ wp∈paritySharedQuotientPositions434 positions d,
      if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
        Wgt (d*w) (d*wp) *
        parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d 1 w wp *
        parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2 : ℝ) w wp (fun g i => s ⟨g,i⟩)
      else 0

/-- Genuine original none-index RAW equals the complete independently
defined kernel-one physical-slice aggregate, with all shared labels and both
exact finite carriers. Positivity and shared divisibility are supplied by the
actual carriers; the statement assumes no aggregate identity, clean event,
comparison kernel, or analytic saving. Arbitrary endpoint cap weights remain
at DR*w and DR*wp throughout this exact equality. -/
theorem parity_raw_endpoint_weight_physical_aggregate434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) (Wgt : ℕ → ℕ → ℂ) :
    parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi Wgt =
    parityRawHarmonicPhysicalAggregate434 L hS J zeta Z k positions lo hi F G t1 t2 tw v psi Wgt := by
  rw [parity_raw_endpoint_weight_numeric_aggregate434 L hL hS J m hmJ Q h xi zeta Z k
    positions lo hi F G t1 t2 tw v psi Wgt]
  unfold parityRawHarmonicNumericAggregate434 parityRawHarmonicPhysicalAggregate434
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  apply Finset.sum_congr rfl
  intro s hs
  let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro wp hwp
  have hdw := parity_shared_quotient_positive434 positions d ⟨w,hw⟩
  have hdwp := parity_shared_quotient_positive434 positions d ⟨wp,hwp⟩
  have hslice := parity_raw_numeric_slice_factor434 L hS J zeta Z k lo hi F G
    t1 t2 tw v psi s w wp hdw.1 hdw.2 hdwp.2
  dsimp only at hslice
  calc
    _ = Wgt (d*w) (d*wp) *
      (∑ a∈sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1) E (fun g i => s ⟨g,i⟩) w,
       ∑ b∈sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1) E (fun g i => s ⟨g,i⟩) wp,
         parityRawHarmonicNumericWeight434 L hS J zeta Z k lo hi F G t1 t2 tw v psi (d*w) (d*wp) d) := by
      simp only [Finset.mul_sum]
      rfl
    _ = _ := by
      rw [hslice]
      split_ifs
      · ring
      · simp only [mul_zero]
end Green64Analytic.Parity

end

end

/-! ## ActualProbeAuxGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 22000

/-- Direct size bound for the literal typed auxiliary product. Every
repeated draw is kept, and no nonzero physical slice, completion or
inhabitant of the full physical state space is assumed. -/
theorem parity_actual_typed_aux_D_cap434
    (J m : ℕ) (L : ℝ) (hL : Real.exp 1≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    (parityActualProbeAuxD434 L J m hmJ nu aux:ℝ) ≤
      Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ)) := by
  have hL1 : 1<L := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hL
  have hLp : 0<L := by linarith
  let U : ℝ := L^(2/5:ℝ)
  let C0 : ℝ := 4+(Real.log 2)⁻¹
  have hU : 0≤U := Real.rpow_nonneg hLp.le _
  have hlog : 0≤Real.log L := Real.log_nonneg hL1.le
  have hC0 : 0≤C0 := by
    have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
    dsimp [C0]
    positivity
  have hcounts := source_native_original_group_upper_counts434 20 L hS (by norm_num) hL
  have hGb : (Fintype.card (sourceNativeOriginalBigType434 20 L):ℝ)≤C0*Real.log L := by
    dsimp [C0]
    nlinarith [hcounts.2]
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ nu
  have hprime (g : sourceNativeOriginalBigType434 20 L) (i : pat.free g) :
      ((aux g i).val:ℝ)≤Real.exp U := by
    have hmem : (aux g i).val∈sourceNativeOriginalG434 20 L := by
      rw [source_native_original_G_identity434 20 L hS hL1]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,(aux g i).property⟩)
    exact (b638_actual_full_P_range434 L hL1.le (aux g i).val hmem).2.2
  have hgroup (g : sourceNativeOriginalBigType434 20 L) :
      (∏ i : pat.free g,((aux g i).val:ℝ))≤Real.exp ((J:ℝ)*U) := by
    have hc : Fintype.card (pat.free g)≤J := by
      rw [Fintype.card_coe]
      simpa only [Fintype.card_fin] using Finset.card_le_univ (pat.free g)
    calc
      _ ≤ ∏ _i : pat.free g,Real.exp U :=
        Finset.prod_le_prod₀ (fun i hi=>Nat.cast_nonneg _) (fun i hi=>hprime g i)
      _ = Real.exp ((Fintype.card (pat.free g):ℝ)*U) := by
        rw [Finset.prod_const,Finset.card_univ,←Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hU)
  have hJ : (J:ℝ)≤4*((J+1:ℕ):ℝ) := by push_cast;nlinarith [Nat.cast_nonneg (α:=ℝ) J]
  unfold parityActualProbeAuxD434
  push_cast
  calc
    _ ≤ ∏ _g : sourceNativeOriginalBigType434 20 L,Real.exp ((J:ℝ)*U) :=
      Finset.prod_le_prod₀ (fun g hg=>by positivity) (fun g hg=>hgroup g)
    _ = Real.exp ((Fintype.card (sourceNativeOriginalBigType434 20 L):ℝ)*((J:ℝ)*U)) := by
      rw [Finset.prod_const,Finset.card_univ,←Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ = (Fintype.card (sourceNativeOriginalBigType434 20 L):ℝ)*(J:ℝ)*U := by ring
        _ ≤ (C0*Real.log L)*(J:ℝ)*U :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hGb (Nat.cast_nonneg J)) hU
        _ = (J:ℝ)*(C0*Real.log L*U) := by ring
        _ ≤ (4*((J+1:ℕ):ℝ))*(C0*Real.log L*U) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
        _ = _ := by dsimp [b651ParityDConstant434,C0,U];ring

/-- Every genuine typed auxiliary draw has the required subexponential
product bound before it is integrated. The constant J is fixed before L;
no shared array, physical slice or arithmetic endpoint enters the bound. -/
theorem parity_eventually_actual_typed_aux_sqrt434 (J : ℕ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J)
      (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (aux : ParityActualProbeAux434 L J m hmJ nu),
      0<parityActualProbeAuxD434 L J m hmJ nu aux ∧
      (parityActualProbeAuxD434 L J m hmJ nu aux:ℝ)≤Real.exp (Real.sqrt L) := by
  filter_upwards [b651_eventually_parity_window_sqrt434 J 0 (by norm_num)] with L hW
  refine ⟨hW.1,?_⟩
  intro hS m hmJ nu aux
  refine ⟨parity_actual_probe_aux_positive434 L hS J m hmJ nu aux,?_⟩
  have hL1 : 1≤L := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hW.1
  have he := parity_actual_typed_aux_D_cap434 J m L hW.1 hS hmJ nu aux
  have hstep : Real.exp (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ))≤b651ParityMaxStep434 J 0 L := by
    unfold b651ParityMaxStep434
    simp only [Real.rpow_zero,mul_one]
    nlinarith [Real.exp_pos (b651ParityDConstant434 J*Real.log L*L^(2/5:ℝ))]
  have hw := b651_parity_maxstep_window_bounds434 J 0 L hL1
  exact he.trans (hstep.trans (hw.1.trans (hw.2.trans hW.2)))
end Green64Analytic.Parity

end

end

/-! ## ActualProbeProbabilityBudget -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 26000

/-- The actual complete untilted labelled auxiliary law has nonnegative
atoms and norm mass exactly one. All repeated draws remain; no endpoint
ban, active-cell conditioning or physical completion hypothesis is used. -/
theorem parity_eventually_actual_typed_aux_mass434 (J : ℕ) :
    ∀ᶠ L : ℝ in atTop,1<L ∧
    (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J)
      (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
      (∀ aux : ParityActualProbeAux434 L J m hmJ nu,
        0 ≤ sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
          (sourceNativeOriginalVbig434 20 L)
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux) ∧
      (∑ aux : ParityActualProbeAux434 L J m hmJ nu,
        ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
          (sourceNativeOriginalVbig434 20 L)
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖)=1 := by
  filter_upwards [eventually_source_native_original_group_masses434 20 (by norm_num)] with L hMass
  refine ⟨hMass.1,hMass.2.1,?_⟩
  intro hS m hmJ nu
  have hV (g : sourceNativeOriginalBigType434 20 L) :
      0<sourceNativeOriginalVbig434 20 L g :=
    source_actual_P_uniform_mass_floor_positive.trans_le ((hMass.2.2 hS).2.2 g).1
  have hHarmonic (g : sourceNativeOriginalBigType434 20 L) :
      (∑ p : SourceNativeMemoryBP434 20 L g,1/(p.val:ℝ))=
      sourceNativeOriginalVbig434 20 L g := by
    simpa [sourceNativeOriginalVbig434,SourceNativeMemoryBP434,one_div] using
      (Finset.sum_attach (sourceNativeOriginalTb434 20 L g) (fun p=>(p:ℝ)⁻¹))
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ nu
  have hnonneg := source_original_memory_aux_mass_nonneg434
    (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
    (sourceNativeOriginalVbig434 20 L) hV pat
  refine ⟨hnonneg,?_⟩
  have hsum := source_original_memory_aux_mass_sum_one434
    (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
    (sourceNativeOriginalVbig434 20 L) hV hHarmonic pat
  calc
    _ = ∑ aux : ParityActualProbeAux434 L J m hmJ nu,
        sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
          (sourceNativeOriginalVbig434 20 L) pat aux := by
      apply Finset.sum_congr rfl
      intro aux haux
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnonneg aux)]
    _ = 1 := hsum

/-- The complete two-nonempty-block comparison pattern family costs the
actual BIG-group logarithmic power. RAW is separate; auxiliary draws are
not counted again. The exponent keeps the fixed m, with no factor two. -/
theorem parity_actual_probe_family_card434
    (L : ℝ) (hL : Real.exp 1≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (m : ℕ) :
    ((sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L)
      (sourceNativeOriginalBigBlockB434 20 L) m).card:ℝ)≤
      L^((m:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2) := by
  have hL1 : 1<L := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hL
  have hp := source_native_original_big_partition434 20 L
  have hc : (sourceNativeOriginalBigBlockA434 20 L).card+
      (sourceNativeOriginalBigBlockB434 20 L).card=
      Fintype.card (sourceNativeOriginalBigType434 20 L) := by
    have hh := Finset.card_union_of_disjoint hp.2.1
    rw [hp.1,Finset.card_univ] at hh
    exact hh.symm
  have hg := source_native_original_group_upper_counts434 20 L hS (by norm_num) hL
  apply source_original_probe_family_log_power_card434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    m L (3+(Real.log 2)⁻¹) hL1.le
  rw [hc]
  exact hg.2
end Green64Analytic.Parity

end

end

/-! ## ActualRankFamilyBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 17000000
set_option maxRecDepth 28000

/-- The actual canonical rank carrier has at most Q^4*xi^-2 terms.
Both active-cell counts are derived from their true full prime probability
laws, and the original primitive character counts are proved. Neither of
the two inverse cell coefficients is included or silently discarded here. -/
theorem parity_canonical_rank_card434
    {G : Type} [Fintype G] [DecidableEq G]
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m) (Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g,V g = ∑ p ∈ P g,1/(p : ℝ)) (hVp : ∀ g,0 < V g)
    (hPrime : ∀ g p,p ∈ P g → p.Prime)
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi) :
    ((parityCanonicalRankIndices434 m nu Q hA hB xi P V).card : ℝ) ≤
      (Q : ℝ)^4*(xi⁻¹)^2 := by
  let JA := sourceOriginalProbeActiveCellsA434 m P V nu hA xi
  let JB := sourceOriginalProbeActiveCellsB434 m P V nu hB xi
  let chars := sourceOriginalActualPrimitiveCharacters434 Q
  have hJA : (JA.card : ℝ) ≤ xi⁻¹ :=
    source_original_true_prime_active_cell_card434
      (fun z : nu.1 => P z.val.1) (fun z : nu.1 => V z.val.1)
      hA hhA JA (fun z => hV z.val.1) (fun z => hVp z.val.1)
      (fun z p hp => hPrime z.val.1 p hp) xi hxi
      (fun j hj => (source_original_probe_active_cell_A_mem_iff434 m P V nu hA xi hhA hxi j).mp hj)
  have hJB : (JB.card : ℝ) ≤ xi⁻¹ :=
    source_original_true_prime_active_cell_card434
      (fun z : nu.2 => P z.val.1) (fun z : nu.2 => V z.val.1)
      hB hhB JB (fun z => hV z.val.1) (fun z => hVp z.val.1)
      (fun z p hp => hPrime z.val.1 p hp) xi hxi
      (fun j hj => (source_original_probe_active_cell_B_mem_iff434 m P V nu hB xi hhB hxi j).mp hj)
  have hc : (chars.card : ℝ) ≤ (Q : ℝ)^2 := by
    exact_mod_cast source_original_actual_primitive_count434 Q
  have hCells : (JA.card : ℝ)*(JB.card : ℝ) ≤ xi⁻¹*xi⁻¹ :=
    mul_le_mul hJA hJB (Nat.cast_nonneg _) (inv_nonneg.mpr hxi.le)
  have hChars : (chars.card : ℝ)*(chars.card : ℝ) ≤ (Q : ℝ)^2*(Q : ℝ)^2 :=
    mul_le_mul hc hc (Nat.cast_nonneg _) (sq_nonneg _)
  change (((JA ×ˢ chars) ×ˢ (JB ×ˢ chars)).card : ℝ) ≤ _
  simp only [Finset.card_product,Nat.cast_mul]
  calc
    _ = ((JA.card : ℝ)*(JB.card : ℝ))*((chars.card : ℝ)*(chars.card : ℝ)) := by ring
    _ ≤ (xi⁻¹*xi⁻¹)*((Q : ℝ)^2*(Q : ℝ)^2) :=
      mul_le_mul hCells hChars
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg (inv_nonneg.mpr hxi.le) (inv_nonneg.mpr hxi.le))
    _ = (Q : ℝ)^4*(xi⁻¹)^2 := by ring

/-- Exact canonical-rank to original source expanded-family cost reindex.
The two genuine inverse cell masses, every primitive conductor and every
original pattern remain in their original finite sums. -/
theorem parity_canonical_rank_family_cost_eq434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ) (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ) :
    (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∑ r ∈ parityCanonicalRankIndices434 m nu Q (hA nu) (hB nu) xi P V,
        sourceOriginalTwoCellCoefficient434
          (sourceOriginalProbeCellA434 m P V nu (hA nu))
          (sourceOriginalProbeCellB434 m P V nu (hB nu)) r.1.1 r.2.1) =
      ∑ z ∈ sourceOriginalProbeExpandedFamily434 blockA blockB m Q P V hA hB xi,
        sourceOriginalProbeExpandedCost434 m Q P V hA hB z := by
  simp only [sourceOriginalProbeExpandedFamily434,sourceOriginalActualFourIndexFamily434,
    Finset.sum_sigma,sourceOriginalProbeExpandedCost434,parityCanonicalRankIndices434,
    Finset.product_eq_sprod]

/-- Actual complete r20 family budgets. The first is the number of ranks,
Q^4*xi^-2; the second includes BOTH inverse true cell masses, Q^4*xi^-4.
The actual BIG-group count supplies the explicit fixed-m logarithmic
power, uniformly over pattern-dependent positive cell widths. There is no
extra outer m sum, no J loss and no cardinality cost for auxiliary draws. -/
theorem parity_eventually_actual_rank_family_budget434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (m Q : ℕ)
        (hA hB : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m → ℝ),
        (∀ nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m,0 < hA nu) →
        (∀ nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m,0 < hB nu) →
      ∀ (xi : ℝ), 0 < xi →
      let P := sourceNativeOriginalTb434 20 L
      let V := sourceNativeOriginalVbig434 20 L
      let EF := (m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
      (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m,
        ((parityCanonicalRankIndices434 m nu Q (hA nu) (hB nu) xi P V).card : ℝ)) ≤
          L^EF*((Q : ℝ)^4*(xi⁻¹)^2) ∧
      (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m,
        ∑ r ∈ parityCanonicalRankIndices434 m nu Q (hA nu) (hB nu) xi P V,
          sourceOriginalTwoCellCoefficient434
            (sourceOriginalProbeCellA434 m P V nu (hA nu))
            (sourceOriginalProbeCellB434 m P V nu (hB nu)) r.1.1 r.2.1) ≤
          L^EF*((Q : ℝ)^4*(xi⁻¹)^4) := by
  filter_upwards [eventually_source_native_original_group_masses434 20 (by norm_num),
    eventually_ge_atTop (Real.exp 1)] with L hMass hL
  intro m Q hA hB hhA hhB xi hxi
  dsimp only
  let P := sourceNativeOriginalTb434 20 L
  let V := sourceNativeOriginalVbig434 20 L
  let BA := sourceNativeOriginalBigBlockA434 20 L
  let BB := sourceNativeOriginalBigBlockB434 20 L
  let family := sourceOriginalTwoBlockProbePatterns434 BA BB m
  have hS := hMass.2.1
  have hV (g : sourceNativeOriginalBigType434 20 L) : V g = ∑ p ∈ P g,1/(p : ℝ) := by
    simp only [P,V,sourceNativeOriginalVbig434,one_div]
  have hVp (g : sourceNativeOriginalBigType434 20 L) : 0 < V g :=
    source_actual_P_uniform_mass_floor_positive.trans_le ((hMass.2.2 hS).2.2 g).1
  have hPrime (g : sourceNativeOriginalBigType434 20 L) (p : ℕ) (hp : p ∈ P g) : p.Prime :=
    (source_native_original_Tb_prime_range434 20 L g p hp).1
  have hCard := parity_actual_probe_family_card434 L hL hS m
  have hPartition := source_native_original_big_partition434 20 L
  have hGroupsCard : BA.card+BB.card = Fintype.card (sourceNativeOriginalBigType434 20 L) := by
    have hh := Finset.card_union_of_disjoint hPartition.2.1
    rw [hPartition.1,Finset.card_univ] at hh
    exact hh.symm
  have hGroups : (((BA.card+BB.card : ℕ)) : ℝ) ≤ (3+(Real.log 2)⁻¹)*Real.log L := by
    rw [hGroupsCard]
    exact (source_native_original_group_upper_counts434 20 L hS (by norm_num) hL).2
  have hAmbient := source_original_probe_two_power_log_bound434 BA BB m L
    (3+(Real.log 2)⁻¹) hMass.1.le hGroups
  constructor
  · calc
      _ ≤ ∑ nu ∈ family,((Q : ℝ)^4*(xi⁻¹)^2) := by
        apply Finset.sum_le_sum
        intro nu hnu
        exact parity_canonical_rank_card434 m nu Q P V hV hVp hPrime
          (hA nu) (hB nu) xi (hhA nu hnu) (hhB nu hnu) hxi
      _ = (family.card : ℝ)*((Q : ℝ)^4*(xi⁻¹)^2) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ L^((m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2)*((Q : ℝ)^4*(xi⁻¹)^2) :=
        mul_le_mul_of_nonneg_right hCard (by positivity)
  · rw [parity_canonical_rank_family_cost_eq434]
    have hc := source_original_probe_expanded_family_cost434 BA BB m Q P V
      hV hVp hPrime hA hB hhA hhB xi hxi
    exact hc.trans (mul_le_mul_of_nonneg_right hAmbient (by positivity))
end Green64Analytic.Parity

end

end

/-! ## ActualRankFamilyPower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000
set_option maxRecDepth 26000

/-- Exact real logarithmic-power accounting for four primitive-character
powers and n reciprocal-cell powers. No rounding of the fixed exponents
CQ,Cxi and no hidden multiplicative constant is introduced. -/
theorem parity_rank_cell_real_power_budget434
    (L : ℝ) (hL : 1 ≤ L) (Q : ℕ) (xi CQ Cxi : ℝ) (n : ℕ)
    (hxi : 0 < xi) (hQ : (Q : ℝ) ≤ L^CQ) (hX : xi⁻¹ ≤ L^Cxi) :
    (Q : ℝ)^4*(xi⁻¹)^n ≤ L^(4*CQ+(n : ℝ)*Cxi) := by
  have hLp : 0 < L := by linarith
  have hQ4 : (Q : ℝ)^4 ≤ (L^CQ)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 4
  have hXn : (xi⁻¹)^n ≤ (L^Cxi)^n := pow_le_pow_left₀ (inv_nonneg.mpr hxi.le) hX n
  calc
    _ ≤ (L^CQ)^4*(L^Cxi)^n :=
      mul_le_mul hQ4 hXn (pow_nonneg (inv_nonneg.mpr hxi.le) n)
        (pow_nonneg (Real.rpow_nonneg hLp.le CQ) 4)
    _ = (L^CQ)^((4 : ℕ) : ℝ)*(L^Cxi)^(n : ℝ) := by rw [Real.rpow_natCast,Real.rpow_natCast]
    _ = L^(CQ*((4 : ℕ) : ℝ))*L^(Cxi*(n : ℝ)) := by rw [← Real.rpow_mul hLp.le,← Real.rpow_mul hLp.le]
    _ = L^(4*CQ+(n : ℝ)*Cxi) := by
      rw [← Real.rpow_add hLp]
      congr 1
      norm_num <;> ring

/-- Full genuine actual-r20 outer rank-family powers. Major-arc rank
count costs E_m+4*CQ+2*Cxi. Minor coefficient mass costs
E_m+4*CQ+4*Cxi, retaining BOTH inverse source cell masses. All fixed
CQ,Cxi are chosen before L and the later family; no outer m sum or
auxiliary-family cardinality is introduced. -/
theorem parity_eventually_actual_rank_family_power434 (CQ Cxi : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (m Q : ℕ)
        (hA hB : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m → ℝ),
        (∀ nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m,0 < hA nu) →
        (∀ nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m,0 < hB nu) →
      ∀ (xi : ℝ), 0 < xi → (Q : ℝ) ≤ L^CQ → xi⁻¹ ≤ L^Cxi →
      let P := sourceNativeOriginalTb434 20 L
      let V := sourceNativeOriginalVbig434 20 L
      let EF := (m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
      (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m,
        ((parityCanonicalRankIndices434 m nu Q (hA nu) (hB nu) xi P V).card : ℝ)) ≤
          L^(EF+4*CQ+2*Cxi) ∧
      (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m,
        ∑ r ∈ parityCanonicalRankIndices434 m nu Q (hA nu) (hB nu) xi P V,
          sourceOriginalTwoCellCoefficient434
            (sourceOriginalProbeCellA434 m P V nu (hA nu))
            (sourceOriginalProbeCellB434 m P V nu (hB nu)) r.1.1 r.2.1) ≤
          L^(EF+4*CQ+4*Cxi) := by
  filter_upwards [parity_eventually_actual_rank_family_budget434,eventually_ge_atTop (1 : ℝ)]
    with L hFamily hL
  intro m Q hA hB hhA hhB xi hxi hQ hX
  dsimp only
  have hLp : 0 < L := by linarith
  have hb := hFamily m Q hA hB hhA hhB xi hxi
  dsimp only at hb
  have hMajor : (Q : ℝ)^4*(xi⁻¹)^2 ≤ L^(4*CQ+2*Cxi) := by
    simpa only [Nat.cast_ofNat] using parity_rank_cell_real_power_budget434 L hL Q xi CQ Cxi 2 hxi hQ hX
  have hMinor : (Q : ℝ)^4*(xi⁻¹)^4 ≤ L^(4*CQ+4*Cxi) := by
    simpa only [Nat.cast_ofNat] using parity_rank_cell_real_power_budget434 L hL Q xi CQ Cxi 4 hxi hQ hX
  constructor
  · calc
      _ ≤ L^((m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2)*((Q : ℝ)^4*(xi⁻¹)^2) := hb.1
      _ ≤ L^((m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2)*L^(4*CQ+2*Cxi) :=
        mul_le_mul_of_nonneg_left hMajor (Real.rpow_nonneg hLp.le _)
      _ = L^((m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2+4*CQ+2*Cxi) := by
        rw [← Real.rpow_add hLp]
        congr 1
        ring
  · calc
      _ ≤ L^((m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2)*((Q : ℝ)^4*(xi⁻¹)^4) := hb.2
      _ ≤ L^((m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2)*L^(4*CQ+4*Cxi) :=
        mul_le_mul_of_nonneg_left hMinor (Real.rpow_nonneg hLp.le _)
      _ = L^((m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2+4*CQ+4*Cxi) := by
        rw [← Real.rpow_add hLp]
        congr 1
        ring
end Green64Analytic.Parity

end

end

/-! ## FreeAuxCollisionRescale -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Exact native arithmetic norm under an original P-supported prime
rescaling. Both true ordinary-part cores are invariant, so no artificial
pointwise divisor loss is needed. Auxiliary scale, cutoff and harmonic
reciprocal all rescale together. -/
theorem parity_stripped_arithmetic_supported_norm_rescale434
    (L zeta Z : ℝ) (F G : PrimeSlotCore) (t1 t2 : ℝ)
    (tw : Bool) (psi : ℝ→ℂ) (p D y yp : ℕ)
    (hp : 0<p) (hy : 0<y) (hyp : 0<yp)
    (hP : p.primeFactors⊆sourceNativeOriginalG434 20 L) :
    ‖parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi (p*D) (p*y) (p*yp)‖ =
      (p:ℝ)⁻¹*‖parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi D y yp‖ := by
  have hpR : (p:ℝ)≠0 := by exact_mod_cast hp.ne'
  have hArg : ((p*y:ℕ):ℝ)/(Z*((p*D:ℕ):ℝ))=(y:ℝ)/(Z*(D:ℝ)) := by
    push_cast
    rw [show Z*((p:ℝ)*(D:ℝ))=(p:ℝ)*(Z*(D:ℝ)) by ring]
    exact mul_div_mul_left _ _ hpR
  rw [parity_harmonic_stripped_arithmetic_norm434 L zeta Z F G t1 t2 tw psi (p*D) (p*y) (p*yp)
      (Nat.mul_pos hp hy) (Nat.mul_pos hp hyp),
    parity_harmonic_stripped_arithmetic_norm434 L zeta Z F G t1 t2 tw psi D y yp hy hyp,
    parity_prime_slot_core_supported_mul434 (sourceOriginalPAllActualBands 20 L) F p y hp hy hP,
    parity_prime_slot_core_supported_mul434 (sourceOriginalPAllActualBands 20 L) G p yp hp hyp hP,hArg]
  push_cast
  rw [mul_inv_rev]
  ring

/-- Real-valued version on the exact Ioc carrier of the native harmonic
functional, reusing the original source divisor-image bijection. -/
theorem parity_real_divisible_Ioc_sum434 (p M : ℕ) (hp : 0<p) (f : ℕ→ℝ) :
    (∑ w∈Finset.Ioc 0 M,if p∣w then f w else 0)=
      ∑ y∈Finset.Ioc 0 (M/p),f (p*y) := by
  have hIoc (N : ℕ) : Finset.Ioc 0 N=Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  rw [hIoc M,hIoc (M/p),←Finset.sum_filter,source_auxiliary_divisible_Icc_image434 p M hp]
  exact Finset.sum_image (fun y _ z _ he=>mul_left_cancel₀ hp.ne' he)

/-- True harmonic divisor reindex with the original signed target and
auxiliary-dependent cutoff. The exact p inverse is produced BEFORE any
auxiliary averaging. Endpoint positivity guards are retained on both
sides, so no source or target zero convention is silently changed. -/
theorem parity_stripped_divisible_harmonic_exact434
    (L zeta Z : ℝ) (F G : PrimeSlotCore) (t1 t2 : ℝ)
    (tw : Bool) (psi : ℝ→ℂ) (p D M : ℕ) (k : ℤ)
    (hp : 0<p) (hP : p.primeFactors⊆sourceNativeOriginalG434 20 L) :
    (∑ w∈Finset.Ioc 0 M,
      if p∣w ∧ 0<(w:ℤ)+k*((p*D:ℕ):ℤ) then
        ‖parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi
          (p*D) w (((w:ℤ)+k*((p*D:ℕ):ℤ)).toNat)‖ else 0)=
      (p:ℝ)⁻¹*(∑ y∈Finset.Ioc 0 (M/p),
        if 0<(y:ℤ)+k*(D:ℤ) then
          ‖parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi
            D y (((y:ℤ)+k*(D:ℤ)).toNat)‖ else 0) := by
  classical
  have he : (∑ w∈Finset.Ioc 0 M,
      if p∣w ∧ 0<(w:ℤ)+k*((p*D:ℕ):ℤ) then
        ‖parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi
          (p*D) w (((w:ℤ)+k*((p*D:ℕ):ℤ)).toNat)‖ else 0)=
      ∑ y∈Finset.Ioc 0 (M/p),
        if 0<((p*y:ℕ):ℤ)+k*((p*D:ℕ):ℤ) then
          ‖parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi
            (p*D) (p*y) ((((p*y:ℕ):ℤ)+k*((p*D:ℕ):ℤ)).toNat)‖ else 0 := by
    rw [←parity_real_divisible_Ioc_sum434 p M hp
      (fun w=>if 0<(w:ℤ)+k*((p*D:ℕ):ℤ) then
        ‖parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi
          (p*D) w (((w:ℤ)+k*((p*D:ℕ):ℤ)).toNat)‖ else 0)]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hd : p∣w <;> simp only [hd,ite_true,ite_false,true_and,false_and]
  rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hyp : 0<y := (Finset.mem_Ioc.mp hy).1
  have hpZ : (0:ℤ)<p := by exact_mod_cast hp
  have hs : ((p*y:ℕ):ℤ)+k*((p*D:ℕ):ℤ)=(p:ℤ)*((y:ℤ)+k*(D:ℤ)) := by
    push_cast
    ring
  have hpos : (0<((p*y:ℕ):ℤ)+k*((p*D:ℕ):ℤ)) ↔ 0<(y:ℤ)+k*(D:ℤ) := by
    rw [hs]
    exact mul_pos_iff_of_pos_left hpZ
  by_cases hsmall : 0<(y:ℤ)+k*(D:ℤ)
  · rw [if_pos (hpos.mpr hsmall),if_pos hsmall]
    have hNat : ((((p*y:ℕ):ℤ)+k*((p*D:ℕ):ℤ)).toNat)=p*(((y:ℤ)+k*(D:ℤ)).toNat) := by
      simpa only [Nat.cast_mul,mul_assoc] using
        source_auxiliary_signed_toNat_scaling434 p y D k hp hsmall
    rw [hNat]
    exact parity_stripped_arithmetic_supported_norm_rescale434 L zeta Z F G t1 t2 tw psi p D y
      (((y:ℤ)+k*(D:ℤ)).toNat) hp hyp (by omega) hP
  · rw [if_neg (fun h=>hsmall (hpos.mp h)),if_neg hsmall,mul_zero]
end Green64Analytic.Parity

end

end

/-! ## FullRankLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

variable {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]

/-- Full SMALL+BIG source lifting does not change either active cell family
or either global primitive-character index. -/
theorem parity_full_rank_indices434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m) (Q : ℕ)
    (hA hB xi : ℝ) (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ)
    (Vs : SG → ℝ) (Vb : BG → ℝ) :
    parityCanonicalRankIndices434 m (parityFullProbePattern434 SG m nu) Q hA hB xi
      (Sum.elim Ps Pb) (Sum.elim Vs Vb) =
    parityCanonicalRankIndices434 m nu Q hA hB xi Pb Vb := by
  unfold parityCanonicalRankIndices434
  rw [parity_full_probe_active_A434,parity_full_probe_active_B434]

/-- Both exact inverse cell masses, both complete auxiliary products and
the original inclusion-exclusion sign commute with the full-group lift. -/
theorem parity_full_rank_scalar434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
      (sourceOriginalProbeCellA434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
        (parityFullProbePattern434 SG m nu) hA)
      (sourceOriginalProbeCellB434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
        (parityFullProbePattern434 SG m nu) hB)
      r.1.2 r.2.2
      (sourceOriginalProbeDA434 m (parityFullProbePattern434 SG m nu)
        (parityFullProbeAuxLift434 SG m nu aux))
      (sourceOriginalProbeDB434 m (parityFullProbePattern434 SG m nu)
        (parityFullProbeAuxLift434 SG m nu aux))
      ((parityFullProbePattern434 SG m nu).1.card+(parityFullProbePattern434 SG m nu).2.card) =
    parityPrimitiveRankScalar434 hA hB r.1.1 r.2.1
      (sourceOriginalProbeCellA434 m Pb Vb nu hA) (sourceOriginalProbeCellB434 m Pb Vb nu hB)
      r.1.2 r.2.2 (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
      (nu.1.card+nu.2.card) := by
  have hA : sourceOriginalProbeCellA434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbePattern434 SG m nu) hA = sourceOriginalProbeCellA434 m Pb Vb nu hA := by
    funext j
    exact parity_full_probe_cell_A434 m nu Ps Pb Vs Vb _ j
  have hB : sourceOriginalProbeCellB434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbePattern434 SG m nu) hB = sourceOriginalProbeCellB434 m Pb Vb nu hB := by
    funext j
    exact parity_full_probe_cell_B434 m nu Ps Pb Vs Vb _ j
  rw [hA,hB,parity_full_probe_DA434,parity_full_probe_DB434]
  simp only [parityFullProbePattern434,Finset.card_map]

/-- The genuine first rank mark depends only on its original BIG free
array; the entire SMALL free array is retained by the carrier lift. -/
theorem parity_full_first_rank_mark434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hB : ℝ) (jb : ℤ)
    (cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (small : SG → Fin ell → ℕ)
    (big : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    parityFirstRankMark434 J ell m hmJ (parityFullProbePattern434 SG m nu) hB jb cb
      (parityFullProbeFreeLift434 J ell m hmJ nu small big) =
    parityFirstRankMark434 J ell m hmJ nu hB jb cb big := by
  unfold parityFirstRankMark434
  rw [parity_full_probe_free_source_X434]

/-- The exact second rank mark has the same BIG-only dependence with the
original selected target product; repeated numerical marks are allowed. -/
theorem parity_full_second_rank_mark434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hA : ℝ) (ja : ℤ)
    (ca : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (small : SG → Fin ell → ℕ)
    (big : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    paritySecondRankMark434 J ell m hmJ (parityFullProbePattern434 SG m nu) hA ja ca
      (parityFullProbeFreeLift434 J ell m hmJ nu small big) =
    paritySecondRankMark434 J ell m hmJ nu hA ja ca big := by
  unfold paritySecondRankMark434
  rw [parity_full_probe_free_target_X434]

/-- Independence holds on every complete full array, not merely arrays
supplied as a particular lift. The inverse uses the exact original indices. -/
theorem parity_full_first_rank_mark_extract434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hB : ℝ) (jb : ℤ)
    (cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (a : ∀ g : SG ⊕ BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) g) → ℕ) :
    parityFirstRankMark434 J ell m hmJ (parityFullProbePattern434 SG m nu) hB jb cb a =
    parityFirstRankMark434 J ell m hmJ nu hB jb cb
      ((parityFullProbeFreeArrayEquiv434 J ell m hmJ nu).symm a).2 := by
  obtain ⟨⟨small,big⟩,rfl⟩ := (parityFullProbeFreeArrayEquiv434 J ell m hmJ nu).surjective a
  rw [Equiv.symm_apply_apply]
  exact parity_full_first_rank_mark434 J ell m hmJ nu hB jb cb small big

theorem parity_full_second_rank_mark_extract434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hA : ℝ) (ja : ℤ)
    (ca : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (a : ∀ g : SG ⊕ BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) g) → ℕ) :
    paritySecondRankMark434 J ell m hmJ (parityFullProbePattern434 SG m nu) hA ja ca a =
    paritySecondRankMark434 J ell m hmJ nu hA ja ca
      ((parityFullProbeFreeArrayEquiv434 J ell m hmJ nu).symm a).2 := by
  obtain ⟨⟨small,big⟩,rfl⟩ := (parityFullProbeFreeArrayEquiv434 J ell m hmJ nu).surjective a
  rw [Equiv.symm_apply_apply]
  exact parity_full_second_rank_mark434 J ell m hmJ nu hA ja ca small big

/-- Exact full marked-family marginalization with all SMALL ordered-list
counts and damping/mass factors. BIG tests may couple every BIG group. -/
theorem parity_marked_family_decoration_split434
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ)
    (ts : SG → ℕ) (tb : BG → ℕ) (q : ℝ)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (coef : (∀ g : BG,Fin (tb g) → ℕ) → ℂ) (n : ℕ) :
    actualBigMarkDecoration (Sum.elim Ps Pb) (Sum.elim ts tb) q (Sum.elim Vs Vb)
      (fun a => coef (fun g => a (Sum.inr g))) n =
    bigMarkPrefactor Ps ts q Vs n *
      ((∏ g : SG,(orderedBigMarks (Ps g) (ts g) n).card : ℕ) : ℂ) *
      actualBigMarkDecoration Pb tb q Vb coef n := by
  have hs := source_marked_family_sum_inr434
    (fun g : SG ⊕ BG => orderedBigMarks ((Sum.elim Ps Pb) g) ((Sum.elim ts tb) g) n) coef
  have hs' :
      (∑ a ∈ bigMarkLists (Sum.elim Ps Pb) (Sum.elim ts tb) n,
        coef (fun g => a (Sum.inr g))) =
      ((∏ g : SG,(orderedBigMarks (Ps g) (ts g) n).card : ℕ) : ℂ) *
        (∑ a ∈ bigMarkLists Pb tb n,coef a) := by
    simpa only [bigMarkLists,Sum.elim_inl,Sum.elim_inr] using hs
  have hp : bigMarkPrefactor (Sum.elim Ps Pb) (Sum.elim ts tb) q (Sum.elim Vs Vb) n =
      bigMarkPrefactor Ps ts q Vs n * bigMarkPrefactor Pb tb q Vb n := by
    simp only [bigMarkPrefactor,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
  simp only [actualBigMarkDecoration]
  rw [hs',hp]
  ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FullRankDecoration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- Exact dependent-count transport. Every ordered mark and its chosen
coordinate survives; the test is transported on the complete array. -/
theorem parity_marked_decoration_count_transport434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (t u : G → ℕ) (ht : ∀ g,t g=u g)
    (q : ℝ) (V : G → ℝ) (b : (∀ g,Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    actualBigMarkDecoration P t q V b n =
    actualBigMarkDecoration P u q V
      (fun a => b (fun g i => a g (finCongr (ht g) i))) n := by
  have htu : t=u := funext ht
  subst u
  have hb : (fun a : ∀ g,Fin (t g) → ℕ =>
      b (fun g i => a g (finCongr (ht g) i))) = b := by
    rfl
  rw [hb]

variable {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]

/-- Complete full-group free decoration with the original dependent free
counts, reduced to its BIG test. All SMALL list counts and mass/damping
prefactors remain. The projection uses the actual chosen free indices. -/
theorem parity_full_free_decoration_split434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (q : ℝ)
    (Vs : SG → ℝ) (Vb : BG → ℝ)
    (coef : (∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) → ℂ)
    (n : ℕ) :
    actualBigMarkDecoration (Sum.elim Ps Pb)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ (parityFullProbePattern434 SG m nu))
      q (Sum.elim Vs Vb)
      (fun a => coef ((parityFullProbeFreeArrayEquiv434 J ell m hmJ nu).symm a).2) n =
    bigMarkPrefactor Ps (fun _ => ell) q Vs n *
      ((∏ g : SG,(orderedBigMarks (Ps g) ell n).card : ℕ) : ℂ) *
      actualBigMarkDecoration Pb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
        q Vb coef n := by
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ (parityFullProbePattern434 SG m nu)
  let u := Sum.elim (fun _ : SG => ell) (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
  have ht : ∀ g,t g=u g := by
    intro g
    cases g with
    | inl g => exact parity_full_probe_free_count_small434 J ell m hmJ nu g
    | inr g => exact parity_full_probe_free_count_big434 J ell m hmJ nu g
  have hcoef :
      (fun a : ∀ g,Fin (u g) → ℕ =>
        coef ((parityFullProbeFreeArrayEquiv434 J ell m hmJ nu).symm
          (fun g i => a g (finCongr (ht g) i))).2) =
      (fun a : ∀ g,Fin (u g) → ℕ => coef (fun g => a (Sum.inr g))) := by
    rfl
  rw [parity_marked_decoration_count_transport434 (Sum.elim Ps Pb) t u ht,
    hcoef]
  exact parity_marked_family_decoration_split434 Ps Pb (fun _ => ell)
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) q Vs Vb coef n

/-- The full first endpoint decoration equals its original auxiliary-free
BIG rank decoration times every literal SMALL marked factor. -/
theorem parity_full_first_rank_decoration434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hB : ℝ) (jb : ℤ)
    (cb : Σ r : Fin Q,DirichletCharacter ℂ (r.val+1))
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (q : ℝ)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (n : ℕ) :
    actualBigMarkDecoration (Sum.elim Ps Pb)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ (parityFullProbePattern434 SG m nu))
      q (Sum.elim Vs Vb)
      (parityFirstRankMark434 J ell m hmJ (parityFullProbePattern434 SG m nu) hB jb cb) n =
    bigMarkPrefactor Ps (fun _ => ell) q Vs n *
      ((∏ g : SG,(orderedBigMarks (Ps g) ell n).card : ℕ) : ℂ) *
      actualBigMarkDecoration Pb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
        q Vb (parityFirstRankMark434 J ell m hmJ nu hB jb cb) n := by
  have hb :
      parityFirstRankMark434 J ell m hmJ (parityFullProbePattern434 SG m nu) hB jb cb =
      (fun a => parityFirstRankMark434 J ell m hmJ nu hB jb cb
        ((parityFullProbeFreeArrayEquiv434 J ell m hmJ nu).symm a).2) := by
    funext a
    exact parity_full_first_rank_mark_extract434 J ell m hmJ nu hB jb cb a
  rw [hb]
  exact parity_full_free_decoration_split434 J ell m hmJ nu Ps Pb q Vs Vb _ n

/-- The second full endpoint has the same exact SMALL factor and its
original BIG target rank row. No auxiliary assignment appears in either row. -/
theorem parity_full_second_rank_decoration434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hA : ℝ) (ja : ℤ)
    (ca : Σ r : Fin Q,DirichletCharacter ℂ (r.val+1))
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (q : ℝ)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (n : ℕ) :
    actualBigMarkDecoration (Sum.elim Ps Pb)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ (parityFullProbePattern434 SG m nu))
      q (Sum.elim Vs Vb)
      (paritySecondRankMark434 J ell m hmJ (parityFullProbePattern434 SG m nu) hA ja ca) n =
    bigMarkPrefactor Ps (fun _ => ell) q Vs n *
      ((∏ g : SG,(orderedBigMarks (Ps g) ell n).card : ℕ) : ℂ) *
      actualBigMarkDecoration Pb (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
        q Vb (paritySecondRankMark434 J ell m hmJ nu hA ja ca) n := by
  have hb :
      paritySecondRankMark434 J ell m hmJ (parityFullProbePattern434 SG m nu) hA ja ca =
      (fun a => paritySecondRankMark434 J ell m hmJ nu hA ja ca
        ((parityFullProbeFreeArrayEquiv434 J ell m hmJ nu).symm a).2) := by
    funext a
    exact parity_full_second_rank_mark_extract434 J ell m hmJ nu hA ja ca a
  rw [hb]
  exact parity_full_free_decoration_split434 J ell m hmJ nu Ps Pb q Vs Vb _ n
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FullRankLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000
variable {TS BG : Type} [Fintype TS] [DecidableEq TS] [Fintype BG] [DecidableEq BG]

/-- The exact distinguished-SMALL / other-SMALL factor, including every
ordered list count, is the original literal source weight. This reuses the
original marked-weight theorem and changes neither source construction. -/
theorem parity_full_small_factor_literal434
    (S : Finset ℕ) (Ts : TS → Finset ℕ) (Tb : BG → Finset ℕ)
    (ell : ℕ) (tb : BG → ℕ) (q Vs : ℝ)
    (Vsmall : TS → ℝ) (Vbig : BG → ℝ)
    (b : (∀ g,Fin (tb g) → ℕ) → ℂ) (n : ℕ) :
    bigMarkPrefactor (Sum.elim (fun _ : Unit => S) Ts)
      (fun _ : Unit ⊕ TS => ell) q (Sum.elim (fun _ : Unit => Vs) Vsmall) n *
      ((∏ g : Unit ⊕ TS,
        (orderedBigMarks ((Sum.elim (fun _ : Unit => S) Ts) g) ell n).card : ℕ) : ℂ) *
      actualBigMarkDecoration Tb tb q Vbig b n =
    literalSourceWeight S Ts Tb q Vs Vsmall Vbig (fun _ => ell) tb b ell n := by
  have h := source_original_marked_weight_split434 S Ts Tb q Vs Vsmall Vbig
    ell (fun _ => ell) tb b n
  have h1 := parity_marked_family_decoration_split434 (fun _ : Unit => S)
    (Sum.elim Ts Tb) (fun _ : Unit => ell) (Sum.elim (fun _ : TS => ell) tb)
    q (fun _ : Unit => Vs) (Sum.elim Vsmall Vbig)
    (fun a => b (fun g => a (Sum.inr g))) n
  have h2 := parity_marked_family_decoration_split434 Ts Tb (fun _ : TS => ell)
    tb q Vsmall Vbig b n
  rw [h1,h2] at h
  simpa only [bigMarkPrefactor,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
    Nat.cast_mul,mul_assoc,mul_left_comm,mul_comm] using h

/-- Exact identification of the full first rank endpoint with the
independent original literal source weight used by the B629 endpoint. -/
theorem parity_full_first_rank_literal434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hB : ℝ) (jb : ℤ)
    (cb : Σ r : Fin Q,DirichletCharacter ℂ (r.val+1))
    (S : Finset ℕ) (Ts : TS → Finset ℕ) (Tb : BG → Finset ℕ)
    (q Vs : ℝ) (Vsmall : TS → ℝ) (Vbig : BG → ℝ) (n : ℕ) :
    actualBigMarkDecoration
      (Sum.elim (Sum.elim (fun _ : Unit => S) Ts) Tb)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
        (parityFullProbePattern434 (Unit ⊕ TS) m nu))
      q (Sum.elim (Sum.elim (fun _ : Unit => Vs) Vsmall) Vbig)
      (parityFirstRankMark434 J ell m hmJ (parityFullProbePattern434 (Unit ⊕ TS) m nu)
        hB jb cb) n =
    literalSourceWeight S Ts Tb q Vs Vsmall Vbig (fun _ => ell)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
      (parityFirstRankMark434 J ell m hmJ nu hB jb cb) ell n := by
  rw [parity_full_first_rank_decoration434]
  exact parity_full_small_factor_literal434 S Ts Tb ell _ q Vs Vsmall Vbig _ n

/-- The full second endpoint agrees with the original literal source
weight with its target rank row and the same full SMALL marked factors. -/
theorem parity_full_second_rank_literal434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    {Q : ℕ} (hA : ℝ) (ja : ℤ)
    (ca : Σ r : Fin Q,DirichletCharacter ℂ (r.val+1))
    (S : Finset ℕ) (Ts : TS → Finset ℕ) (Tb : BG → Finset ℕ)
    (q Vs : ℝ) (Vsmall : TS → ℝ) (Vbig : BG → ℝ) (n : ℕ) :
    actualBigMarkDecoration
      (Sum.elim (Sum.elim (fun _ : Unit => S) Ts) Tb)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
        (parityFullProbePattern434 (Unit ⊕ TS) m nu))
      q (Sum.elim (Sum.elim (fun _ : Unit => Vs) Vsmall) Vbig)
      (paritySecondRankMark434 J ell m hmJ (parityFullProbePattern434 (Unit ⊕ TS) m nu)
        hA ja ca) n =
    literalSourceWeight S Ts Tb q Vs Vsmall Vbig (fun _ => ell)
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
      (paritySecondRankMark434 J ell m hmJ nu hA ja ca) ell n := by
  rw [parity_full_second_rank_decoration434]
  exact parity_full_small_factor_literal434 S Ts Tb ell _ q Vs Vsmall Vbig _ n
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualFullRankLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- Actual r20 first rank weight is exactly the original B629 literal
source weight with its distinguished free count1, all other SMALL counts1
and original BIG free counts. There is no auxiliary argument. -/
theorem parity_actual_full_first_rank_literal434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hB : ℝ) (jb : ℤ)
    (cb : Σ r : Fin Q,DirichletCharacter ℂ (r.val+1))
    (q : ℝ) (n : ℕ) :
    actualBigMarkDecoration (b645ActualBand434 L hS)
      (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      q (Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
        (sourceNativeOriginalVbig434 20 L))
      (parityFirstRankMark434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
        hB jb cb) n =
    literalSourceWeight
      (sourceNativeOriginalS434 20 L hS) (sourceNativeOriginalTs434 20 L hS)
      (sourceNativeOriginalTb434 20 L) q (sourceNativeOriginalVs434 20 L hS)
      (sourceNativeOriginalVsmall434 20 L hS) (sourceNativeOriginalVbig434 20 L)
      (fun _ => 1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu)
      (parityFirstRankMark434 J 1 m hmJ nu hB jb cb) 1 n := by
  unfold b645ActualBand434
  rw [parity_full_first_rank_decoration434]
  have h := parity_full_small_factor_literal434
    (sourceNativeOriginalS434 20 L hS) (sourceNativeOriginalTs434 20 L hS)
    (sourceNativeOriginalTb434 20 L) 1
    (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) q
    (sourceNativeOriginalVs434 20 L hS) (sourceNativeOriginalVsmall434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) (parityFirstRankMark434 J 1 m hmJ nu hB jb cb) n
  simpa only [bigMarkPrefactor,Fintype.prod_option,Fintype.prod_sum_type,
    Fintype.prod_unique,SourceNativeMemorySmallSet434,SourceNativeMemorySmallMass434,
    Sum.elim_inl,Sum.elim_inr] using h

/-- The actual r20 target rank endpoint has the same exact original
literal source construction with its auxiliary-independent BIG row. -/
theorem parity_actual_full_second_rank_literal434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA : ℝ) (ja : ℤ)
    (ca : Σ r : Fin Q,DirichletCharacter ℂ (r.val+1))
    (q : ℝ) (n : ℕ) :
    actualBigMarkDecoration (b645ActualBand434 L hS)
      (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      q (Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
        (sourceNativeOriginalVbig434 20 L))
      (paritySecondRankMark434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
        hA ja ca) n =
    literalSourceWeight
      (sourceNativeOriginalS434 20 L hS) (sourceNativeOriginalTs434 20 L hS)
      (sourceNativeOriginalTb434 20 L) q (sourceNativeOriginalVs434 20 L hS)
      (sourceNativeOriginalVsmall434 20 L hS) (sourceNativeOriginalVbig434 20 L)
      (fun _ => 1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu)
      (paritySecondRankMark434 J 1 m hmJ nu hA ja ca) 1 n := by
  unfold b645ActualBand434
  rw [parity_full_second_rank_decoration434]
  have h := parity_full_small_factor_literal434
    (sourceNativeOriginalS434 20 L hS) (sourceNativeOriginalTs434 20 L hS)
    (sourceNativeOriginalTb434 20 L) 1
    (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) q
    (sourceNativeOriginalVs434 20 L hS) (sourceNativeOriginalVsmall434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) (paritySecondRankMark434 J 1 m hmJ nu hA ja ca) n
  simpa only [bigMarkPrefactor,Fintype.prod_option,Fintype.prod_sum_type,
    Fintype.prod_unique,SourceNativeMemorySmallSet434,SourceNativeMemorySmallMass434,
    Sum.elim_inl,Sum.elim_inr] using h
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualRankEndpoint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

/-- The full actual r20 rank endpoint before its scale-dependent cutoff.
It contains the original ordinary-part prime-slot core, native phase, full
valuation parity and every SMALL/BIG marked prefactor and ordered list.
There is no auxiliary draw or auxiliary product argument. -/
def parityActualRankEndpoint434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (q : ℝ) (F : PrimeSlotCore) (t : ℝ) (tw sourceSide : Bool) (n : ℕ) : ℂ :=
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  (groupSign (sourceOriginalPAllActualBands 20 L) tw n : ℂ) *
    parityHarmonicEndpointArithmetic434 L F t n *
    actualBigMarkDecoration (b645ActualBand434 L hS)
      (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu) q
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (if sourceSide then parityFirstRankMark434 J 1 m hmJ fullnu hB r.2.1 r.2.2
       else paritySecondRankMark434 J 1 m hmJ fullnu hA r.1.1 r.1.2) n

/-- Exact binding to the independently defined original FULL endpoint
used by B629. The full r20 P union, prime/interval gates, both divisor sums,
all original masses and distinguished SMALL count1 are preserved. This
identity does not insert physical Ppart caps or assert an arc estimate. -/
theorem parity_actual_rank_endpoint_original434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (q : ℝ) (F : PrimeSlotCore) (t : ℝ) (tw sourceSide : Bool) (n : ℕ) :
    parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F t tw sourceSide n =
      sourceEndpointSign434 (sourceNativeOriginalG434 20 L) tw n *
      sourceOriginalFullEndpointCoefficients434 F.q
        (sourceNativeOriginalS434 20 L hS) (sourceNativeOriginalTs434 20 L hS)
        (sourceNativeOriginalTb434 20 L) q (sourceNativeOriginalVs434 20 L hS)
        (sourceNativeOriginalVsmall434 20 L hS) (sourceNativeOriginalVbig434 20 L)
        (fun _ => 1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu)
        (if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB r.2.1 r.2.2
         else paritySecondRankMark434 J 1 m hmJ nu hA r.1.1 r.1.2) 0
        ((Finset.Icc F.lo F.hi).filter Nat.Prime) F.alpha F.residual F.character
        F.sigma₀ F.sigma₁ (fun u => imaginaryPower u t) (n : ℤ) := by
  have hUnion : Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L) =
      sourceNativeOriginalS434 20 L hS ∪
        Finset.univ.biUnion (sourceNativeOriginalTs434 20 L hS) ∪
        Finset.univ.biUnion (sourceNativeOriginalTb434 20 L) :=
    source_native_original_G_identity434 20 L hS hL
  have hCore := source_native_B523_literal_fock_sourceCore_eq_T_primeSlotCore434
    (sourceOriginalPAllActualBands 20 L) F n
  rw [hUnion] at hCore
  unfold parityActualRankEndpoint434
  dsimp only
  cases sourceSide
  · simp only [Bool.false_eq_true,ite_false,parity_actual_full_second_rank_literal434]
    unfold parityHarmonicEndpointArithmetic434
    rw [parity_native_group_sign_source434,←hCore]
    unfold sourceOriginalFullEndpointCoefficients434 sourceEndpoint sourceNativeOriginalG434
    simp only [Int.toNat_natCast,Nat.zero_add]
    ring
  · simp only [ite_true,parity_actual_full_first_rank_literal434]
    unfold parityHarmonicEndpointArithmetic434
    rw [parity_native_group_sign_source434,←hCore]
    unfold sourceOriginalFullEndpointCoefficients434 sourceEndpoint sourceNativeOriginalG434
    simp only [Int.toNat_natCast,Nat.zero_add]
    ring
end Green64Analytic.Parity

end

end

/-! ## ActualCutoffMellin -/

section

open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff RealInnerProductSpace
open MeasureTheory
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

/- The actual Schwartz cutoff is the already certified
`parityOriginalLogCutoff434` from Green64ParityOriginalCutoff434. Its compact
support and construction are reused unchanged, not reproved here. -/

/-- Exact Fourier convention and sign for the genuine scale Z*c.
The original logarithm separates into a Z scalar, a w endpoint phase,
and an auxiliary c phase with the opposite frequency. -/
theorem parity_cutoff_log_phase_separate434
    (Z : ℝ) (w c : ℕ) (hZ : 0<Z) (hw : 0<w) (hc : 0<c) (s : ℝ) :
    Complex.exp (((2*Real.pi*⟪s,Real.log ((w : ℝ)/(Z*(c : ℝ)))⟫ : ℝ) : ℂ)*Complex.I) =
      Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) w *
        sourceOriginalPureMellinPhase434 (-2*Real.pi*s) c := by
  have hwR : (w : ℝ)≠0 := by exact_mod_cast hw.ne'
  have hcR : (c : ℝ)≠0 := by exact_mod_cast hc.ne'
  rw [Real.inner_apply,Real.log_div hwR (mul_ne_zero hZ.ne' hcR),
    Real.log_mul hZ.ne' hcR]
  unfold sourceOriginalPureMellinPhase434
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Constructive exact Mellin separation of the original cutoff at Z*c.
The base endpoint and auxiliary product receive opposite real frequencies;
the integrable Fourier weight is derived from the actual given psi. -/
theorem parity_actual_cutoff_mellin_integral434
    (Z : ℝ) (psi : ℝ → ℂ) (w c : ℕ)
    (hZ : 0<Z) (hw : 0<w) (hc : 0<c)
    (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u : ℝ,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) :
    psi ((w : ℝ)/(Z*(c : ℝ))) =
      ∫ s : ℝ,
        (𝓕 (parityOriginalLogCutoff434 psi hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
        Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) w *
        sourceOriginalPureMellinPhase434 (-2*Real.pi*s) c := by
  let f := parityOriginalLogCutoff434 psi hSmooth hSupport
  let u := Real.log ((w : ℝ)/(Z*(c : ℝ)))
  have hratio : 0<(w : ℝ)/(Z*(c : ℝ)) := by positivity
  have hInv : (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ))) u = f u := by
    rw [FourierTransform.fourierInv_fourier_eq]
  have hVal : f u=psi ((w : ℝ)/(Z*(c : ℝ))) :=
    parity_original_log_cutoff_positive434 psi hSmooth hSupport _ hratio
  rw [←hVal,←hInv,SchwartzMap.fourierInv_coe,Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with s
  change Complex.exp (((2*Real.pi*⟪s,u⟫ : ℝ) : ℂ)*Complex.I) *
    (𝓕 f : 𝓢(ℝ,ℂ)) s = _
  rw [parity_cutoff_log_phase_separate434 Z w c hZ hw hc s]
  dsimp only [f]
  ring

/-- The separated cutoff integral is genuinely integrable. In particular,
the three scalar Mellin factors incur no additional pointwise norm cost;
quantitative uniform Fourier L1 budgets remain a separate obligation. -/
theorem parity_actual_cutoff_mellin_integrable434
    (Z : ℝ) (psi : ℝ → ℂ) (w c : ℕ)
    (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u : ℝ,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) :
    Integrable (fun s : ℝ =>
      (𝓕 (parityOriginalLogCutoff434 psi hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
      Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
      sourceOriginalPureMellinPhase434 (2*Real.pi*s) w *
      sourceOriginalPureMellinPhase434 (-2*Real.pi*s) c) := by
  let f := (𝓕 (parityOriginalLogCutoff434 psi hSmooth hSupport) : 𝓢(ℝ,ℂ))
  have hcont : Continuous (fun s : ℝ => f s *
      Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
      sourceOriginalPureMellinPhase434 (2*Real.pi*s) w *
      sourceOriginalPureMellinPhase434 (-2*Real.pi*s) c) := by
    unfold sourceOriginalPureMellinPhase434
    fun_prop
  apply f.integrable.mono hcont.aestronglyMeasurable
  filter_upwards [] with s
  simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,
    source_original_pure_mellin_phase_norm_one434,mul_one,le_refl]
end Green64Analytic.Parity

end

end

