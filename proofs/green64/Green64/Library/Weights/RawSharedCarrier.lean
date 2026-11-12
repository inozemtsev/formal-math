module

public import Green64.Library.Weights.Part114
public import Green64.Library.Weights.RawSharedRestoration
public import Green64.Library.Correlation.Part072

@[expose] public section

/-!
# Weights / RawSharedCarrier

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## RawSharedCarrier -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 28000

/-- Independent harmonic restored RAW target. Every shared assignment
remains inside the literal RAW restored slice; the separately proved
arithmetic is independent of it. Wgt is on the quotient endpoints and
is not identified with a physical cap at DR*w and DR*wp. -/
def parityRawRestoredHarmonic434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ → ℂ) (Wgt : ℕ → ℕ → ℂ) : ℂ :=
  ∑ w ∈ N,∑ wp ∈ N,
    if (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
      Wgt w wp*parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi 1 w wp*
      parityRawRestoredSlice434 J (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (1/2) w wp
    else 0

private theorem raw_pair_extend434 (A B : Finset ℕ) (hAB : A ⊆ B) (F : ℕ → ℕ → ℂ)
    (hF : ∀ w ∈ B,∀ wp ∈ B,F w wp ≠ 0 → w ∈ A ∧ wp ∈ A) :
    (∑ w ∈ A,∑ wp ∈ A,F w wp)=∑ w ∈ B,∑ wp ∈ B,F w wp := by
  calc
    _ = ∑ w ∈ B,∑ wp ∈ A,F w wp := by
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

/-- Exact transport of one genuine RAW shared slice from its own physical
quotient carrier to the original common positive carrier. Seed removal and
both endpoint support conditions are derived before the finite reindex. -/
theorem parity_eventually_raw_shared_carrier_sum434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ),
      (∀ g i,s g i ∈ b645ActualBand434 L hS g) →
    ∀ (rho xi3 Ck Z : ℝ) (k : ℤ),(k.natAbs : ℝ) ≤ L^Ck → 0 < Z → Z ≤ Real.exp L*L^CZ →
    ∀ psi : ℝ → ℂ,(∀ u,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) →
    ∀ (F G : PrimeSlotCore) (tw : Bool),
      let d := sourceB574SharedDilation434 (J+1)
        (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
      let W := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
      let B := fun (w wp : ℕ) => parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (1/2) w wp s
      (∑ w ∈ paritySharedQuotientPositions434 W d,∑ wp ∈ paritySharedQuotientPositions434 W d,
        if (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
          parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
            (-(rho+xi3)) (-rho) tw 0 psi d 1 w wp*B w wp else 0)=
      ∑ w ∈ parityPositiveNaturalPositions434 W,∑ wp ∈ parityPositiveNaturalPositions434 W,
        if (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
          parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
            (-(rho+xi3)) (-rho) tw psi 1 w wp*B w wp else 0 := by
  filter_upwards [parity_eventually_raw_shared_scalar_slice434 J CZ,
    parity_eventually_raw_completion_pair_carrier434 J CZ] with L hStrip hCarrier
  refine ⟨hStrip.1,?_⟩
  intro hS s hs rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  dsimp only
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let d := sourceB574SharedDilation434 (J+1) E s
  let W := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let A := paritySharedQuotientPositions434 W d
  let N := parityPositiveNaturalPositions434 W
  let B := fun w wp => parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (1/2) w wp s
  let R := fun (w wp : ℕ) => if (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
    parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
      (-(rho+xi3)) (-rho) tw psi 1 w wp*B w wp else 0
  have hAN : A ⊆ N := parity_interval_shared_quotient_subset434 J Ck L (parityDyadicLimit434 L) d
  have hpoint (w : ℕ) (hw : w ∈ A) (wp : ℕ) (hwp : wp ∈ A) :
      (if (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
        parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
          (-(rho+xi3)) (-rho) tw 0 psi d 1 w wp*B w wp else 0)=R w wp := by
    have hwpos := (parity_shared_quotient_positive434 W d ⟨w,hw⟩).2
    have hwppos := (parity_shared_quotient_positive434 W d ⟨wp,hwp⟩).2
    have he := hStrip.2 hS s hs rho xi3 Z hZ hZhi psi hSupp F G tw w wp hwpos hwppos
    change parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
        (-(rho+xi3)) (-rho) tw 0 psi d 1 w wp*B w wp=
      parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi 1 w wp*B w wp at he
    dsimp only [R]
    split_ifs
    · exact he
    · rfl
  have hSupport (w : ℕ) (hw : w ∈ N) (wp : ℕ) (hwp : wp ∈ N) (hnz : R w wp ≠ 0) :
      w ∈ A ∧ wp ∈ A := by
    have hwpos := ((parity_positive_natural_positions_mem434 W w).mp hw).1
    have hwppos := ((parity_positive_natural_positions_mem434 W wp).mp hwp).1
    have hstep : (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+2*k := by
      by_contra ht
      exact hnz (by simp only [R,if_neg ht])
    have hB : B w wp ≠ 0 := by
      intro hb
      exact hnz (by simp only [R,if_pos hstep,hb,mul_zero])
    have hpsi : psi ((w : ℝ)/Z) ≠ 0 := by
      intro hp
      apply hnz
      simp only [R,if_pos hstep,parityHarmonicStrippedArithmetic434,
        Nat.cast_one,mul_one,hp,mul_zero,zero_mul]
    have hcomp := (parity_raw_physical_completion_support434 J (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2) w wp s hB).1
    exact hCarrier.2 hS s hs Ck Z k hk hZ hZhi psi hSupp w wp hwpos hwppos hcomp hpsi hstep.2
  calc
    _ = ∑ w ∈ A,∑ wp ∈ A,R w wp := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro wp hwp
      exact hpoint w hw wp hwp
    _ = ∑ w ∈ N,∑ wp ∈ N,R w wp := raw_pair_extend434 A N hAN R hSupport

/-- The independently defined full physical uncapped RAW aggregate is
exactly the independent restored RAW harmonic sum on one common carrier.
This proves the equality of the original constructions; it defines neither
functional by the claimed identity and inserts no physical Ppart cap. -/
theorem parity_eventually_raw_harmonic_restored434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (rho xi3 Ck Z : ℝ) (k : ℤ),(k.natAbs : ℝ) ≤ L^Ck → 0 < Z → Z ≤ Real.exp L*L^CZ →
    ∀ psi : ℝ → ℂ,(∀ u,psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64) →
    ∀ (F G : PrimeSlotCore) (tw : Bool),
      parityRawHarmonicPhysicalAggregate434 L hS J (-xi3) Z k
        (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
        1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi (fun _ _ => 1)=
      parityRawRestoredHarmonic434 L hS J rho xi3 Z k
        (parityPositiveNaturalPositions434 (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)))
        F G tw psi (fun _ _ => 1) := by
  filter_upwards [parity_eventually_raw_shared_carrier_sum434 J CZ] with L hCarrier
  refine ⟨hCarrier.1,?_⟩
  intro hS rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  let E := fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J
  let ss := Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1)
  let N := parityPositiveNaturalPositions434 (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let R := fun (s : (g : B645ActualGroup434 L hS) × E g → ℕ) (w wp : ℕ) =>
    if (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
      parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi 1 w wp*
        parityRawPhysicalSlice434 J (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2) w wp (fun g i => s ⟨g,i⟩)
    else 0
  have hfirst : parityRawHarmonicPhysicalAggregate434 L hS J (-xi3) Z k
      (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
      1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi (fun _ _ => 1)=
      ∑ s ∈ ss,∑ w ∈ N,∑ wp ∈ N,R s w wp := by
    unfold parityRawHarmonicPhysicalAggregate434
    dsimp only
    simp only [one_mul]
    apply Finset.sum_congr rfl
    intro s hs
    have hsmem : ∀ g i,s ⟨g,i⟩ ∈ b645ActualBand434 L hS g := by
      intro g i
      exact (Fintype.mem_piFinset.mp hs) ⟨g,i⟩
    exact hCarrier.2 hS (fun g i => s ⟨g,i⟩) hsmem rho xi3 Ck Z k hk hZ hZhi psi hSupp F G tw
  calc
    _ = ∑ s ∈ ss,∑ w ∈ N,∑ wp ∈ N,R s w wp := hfirst
    _ = ∑ w ∈ N,∑ wp ∈ N,∑ s ∈ ss,R s w wp :=
      (parity_shared_position_sum_order434 N ss R).symm
    _ = _ := by
      unfold parityRawRestoredHarmonic434
      dsimp only
      simp only [one_mul]
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro wp hwp
      dsimp only [R]
      split_ifs
      · rw [←Finset.mul_sum]
        rfl
      · simp only [Finset.sum_const_zero]
end Green64Analytic.Parity

end

end

