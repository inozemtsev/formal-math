module

public import Green64.Library.Correlation.PhysicalSharedFreeCarrier
public import Green64.Library.Correlation.Part071

@[expose] public section

/-!
# Correlation / PhysicalSharedFreeCarrierSum

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalSharedFreeCarrierSum -/

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

/-- The literal B574 physical slice at all actual r20 data. This is only
an explicit parameter specialization, without an auxiliary probability
or an arithmetic factor hidden in the slice. -/
def parityActualB574Physical434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi : ℝ) (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (w wp : ℕ) : ℂ :=
  sourceB574CanonicalPhysicalSlice434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) Q h h xi
    (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
    (1/2 : ℝ) w wp s

/-- The stripped arithmetic multiplies the SAME physical slice, actual
auxiliary atom and quotient shift guard. Only the arithmetic multiplier
is shared-independent; the complete physical slice retains every label. -/
def parityActualStrippedComparisonWeight434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (w wp : ℕ) : ℂ :=
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
    parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp *
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      parityActualB574Physical434 L hS J m hmJ nu Q h xi aux s w wp
  else 0

private theorem finite_pair_extend (A B : Finset ℕ) (hAB : A⊆B) (F : ℕ → ℕ → ℂ)
    (hF : ∀ w∈B,∀ wp∈B,F w wp≠0 → w∈A ∧ wp∈A) :
    (∑ w∈A,∑ wp∈A,F w wp)=∑ w∈B,∑ wp∈B,F w wp := by
  calc
    _ = ∑ w∈B,∑ wp∈A,F w wp := by
      apply Finset.sum_subset hAB
      intro w hw hwA
      apply Finset.sum_eq_zero
      intro wp hwp
      by_contra hn
      exact hwA (hF w hw wp (hAB hwp) hn).1
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_subset hAB
      intro wp hwp hwpA
      by_contra hn
      exact hwpA (hF w hw wp hwp hn).2

/-- The actual quotient double sum is exactly transported to ONE common
positive original interval, independent of the full shared assignment.
The old arithmetic is stripped using its proved physical support identity,
and all newly admitted terms vanish by the original cutoff and frame
radius. Neither equality nor a support estimate is an extra premise. -/
theorem parity_eventually_actual_shared_carrier_sum434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J)
      (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (aux : ParityActualProbeAux434 L J m hmJ nu)
      (s : ∀ g : B645ActualGroup434 L hS,
        sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ),
      (∀ g i,s g i∈b645ActualBand434 L hS g) →
    ∀ (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ),
      (k.natAbs : ℝ)≤L^Ck → 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u,psi u≠0 → (1/64:ℝ)≤u ∧ u≤64) →
    ∀ (F G : PrimeSlotCore) (tw : Bool),
      let d := sourceB574SharedDilation434 (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
      let c := parityActualProbeAuxD434 L J m hmJ nu aux
      let W := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
      (∑ w∈paritySharedQuotientPositions434 W d,
        ∑ wp∈paritySharedQuotientPositions434 W d,
          if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
            parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
              (-(rho+xi3)) (-rho) tw 0 psi d c w wp *
            (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
              (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
            parityActualB574Physical434 L hS J m hmJ nu Q h xi aux s w wp
          else 0)=
      ∑ w∈parityPositiveNaturalPositions434 W,∑ wp∈parityPositiveNaturalPositions434 W,
        parityActualStrippedComparisonWeight434 L hS J m hmJ nu Q h xi rho xi3 Z k F G tw psi aux s w wp := by
  filter_upwards [parity_eventually_actual_shared_scalar_slice434 J CZ,
    parity_eventually_actual_completion_pair_carrier434 J CZ] with L hStrip hCarrier
  refine ⟨hStrip.1,?_⟩
  intro hS m hmJ nu aux s hs Q h xi rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  dsimp only
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let W := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let A := paritySharedQuotientPositions434 W d
  let N := parityPositiveNaturalPositions434 W
  let B := parityActualB574Physical434 L hS J m hmJ nu Q h xi aux s
  let R := parityActualStrippedComparisonWeight434 L hS J m hmJ nu Q h xi rho xi3 Z k F G tw psi aux s
  let mu : ℂ := sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
    (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux
  have hAN : A⊆N := parity_interval_shared_quotient_subset434 J Ck L (parityDyadicLimit434 L) d
  have hpoint (w : ℕ) (hw : w∈A) (wp : ℕ) (hwp : wp∈A) :
      (if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
        parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
          (-(rho+xi3)) (-rho) tw 0 psi d c w wp*mu*B w wp else 0)=R w wp := by
    have hwpos := (parity_shared_quotient_positive434 W d ⟨w,hw⟩).2
    have hwppos := (parity_shared_quotient_positive434 W d ⟨wp,hwp⟩).2
    have he := hStrip.2 hS m hmJ nu aux s hs Q h xi rho xi3 Z hZ hZhi psi hSupp F G tw
      w wp hwpos hwppos
    change parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
        (-(rho+xi3)) (-rho) tw 0 psi d c w wp*B w wp=
      parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp*B w wp at he
    change _=if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
      parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp*mu*B w wp else 0
    split_ifs
    · calc
        _ = mu*(parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
          (-(rho+xi3)) (-rho) tw 0 psi d c w wp*B w wp) := by ring
        _ = _ := by rw [he]; ring
    · rfl
  have hSupport (w : ℕ) (hw : w∈N) (wp : ℕ) (hwp : wp∈N) (hnz : R w wp≠0) :
      w∈A ∧ wp∈A := by
    have hwpos := ((parity_positive_natural_positions_mem434 W w).mp hw).1
    have hwppos := ((parity_positive_natural_positions_mem434 W wp).mp hwp).1
    have hstep : (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) := by
      by_contra ht
      apply hnz
      change (if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
        parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp*mu*B w wp else 0)=0
      simp only [ht,ite_false]
    have hB : B w wp≠0 := by
      intro hz
      apply hnz
      change (if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
        parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp*mu*B w wp else 0)=0
      simp only [hz,mul_zero,ite_self]
    have hpsi : psi ((w : ℝ)/(Z*(c : ℝ)))≠0 := by
      intro hz
      apply hnz
      change (if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
        parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp*mu*B w wp else 0)=0
      simp only [parityHarmonicStrippedArithmetic434,hz,mul_zero,zero_mul,ite_self]
    have hcomp := (parity_B574_physical_slice_completion_support434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) Q h h xi
      (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
      (1/2 : ℝ) w wp s hB).1
    exact hCarrier.2 hS m hmJ nu aux s hs Ck Z k hk hZ hZhi psi hSupp
      w wp hwpos hwppos hcomp hpsi hstep.2
  calc
    _ = ∑ w∈A,∑ wp∈A,R w wp := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro wp hwp
      exact hpoint w hw wp hwp
    _ = ∑ w∈N,∑ wp∈N,R w wp := finite_pair_extend A N hAN R hSupport
end Green64Analytic.Parity

end

end

