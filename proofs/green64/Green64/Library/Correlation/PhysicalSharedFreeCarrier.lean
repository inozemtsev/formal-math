module

public import Green64.Library.Weights.Part112
public import Green64.Library.Correlation.Part070

@[expose] public section

/-!
# Correlation / PhysicalSharedFreeCarrier

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalSharedFreeCarrier -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Exact membership in the original divisible-position quotient carrier. -/
theorem parity_shared_quotient_mem_iff434 (positions : Finset ℤ) (d w : ℕ) (hd : 0<d) :
    w∈paritySharedQuotientPositions434 positions d ↔
      0<w ∧ ((d*w : ℕ) : ℤ)∈positions := by
  constructor
  · intro hw
    have h := (parity_positive_natural_positions_mem434 positions (d*w)).mp
      (parity_shared_quotient_mul_mem434 positions d ⟨w,hw⟩)
    exact ⟨(parity_shared_quotient_positive434 positions d ⟨w,hw⟩).2,h.2⟩
  · rintro ⟨hw,hpos⟩
    apply Finset.mem_image.mpr
    refine ⟨d*w,Finset.mem_filter.mpr ⟨?_,⟨w,rfl⟩⟩,?_⟩
    · exact (parity_positive_natural_positions_mem434 positions (d*w)).mpr
        ⟨Nat.mul_pos hd hw,hpos⟩
    · apply Nat.eq_of_mul_eq_mul_left hd
      exact Nat.mul_div_cancel' (show d∣d*w from ⟨w,rfl⟩)

/-- Every positive quotient of the original enlarged physical interval is
in the same enlarged positive interval. This is only a finite carrier
inclusion and loses no original residue or mark data. -/
theorem parity_interval_shared_quotient_subset434
    (J : ℕ) (Ck L : ℝ) (hi d : ℕ) :
    paritySharedQuotientPositions434 (b654ParityIntervalWindow434 J Ck L 1 hi) d ⊆
      parityPositiveNaturalPositions434 (b654ParityIntervalWindow434 J Ck L 1 hi) := by
  intro w hw
  have hp := parity_shared_quotient_positive434 (b654ParityIntervalWindow434 J Ck L 1 hi) d ⟨w,hw⟩
  have hm := (parity_positive_natural_positions_mem434 _ (d*w)).mp
    (parity_shared_quotient_mul_mem434 (b654ParityIntervalWindow434 J Ck L 1 hi) d ⟨w,hw⟩)
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hm.2
  apply (parity_positive_natural_positions_mem434 _ w).mpr
  refine ⟨hp.2,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩
  · have hwI : (1 : ℤ)≤w := by exact_mod_cast hp.2
    have hR : (0 : ℤ)≤(b651ParityPathRadius434 J Ck L : ℤ) := by positivity
    exact le_trans (sub_le_self _ hR) hwI
  · have hwle : w≤d*w := Nat.le_mul_of_pos_left _ hp.1
    exact (show (w : ℤ)≤((d*w : ℕ) : ℤ) by exact_mod_cast hwle).trans hhi

/-- A genuine completion supplies the native frame locality bound with
its original full shared/auxiliary divisor; no summed-matrix cancellation
is used to localize a frame-dependent cutoff. -/
theorem parity_actual_completion_frame_radius434
    (L : ℝ) (hL : Real.exp 1≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (w : ℕ)
    (ha : (sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s w).Nonempty)
    (Ck : ℝ) (k : ℤ) (hk : (k.natAbs : ℝ)≤L^Ck) :
    |(2*k)*((sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s *
      parityActualProbeAuxD434 L J m hmJ nu aux : ℕ) : ℤ)|≤
      (b651ParityPathRadius434 J Ck L : ℤ) := by
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E s
  obtain ⟨a,ha⟩ := ha
  change a∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E
    (fun i => s i.1 i.2) (d*w) at ha
  rw [parity_physical_completions_restriction_fibre434] at ha
  obtain ⟨ha,hs⟩ := Finset.mem_filter.mp ha
  let e := parityActualFixedPositionMarksEquiv434 L hS J (d*w)
  let x := e.symm ⟨a,ha⟩
  have hx : parityActualPositionMarks434 L hS J (d*w) x=a := by
    change (e (e.symm ⟨a,ha⟩)).val=a
    rw [Equiv.apply_symm_apply]
  have hshared : (fun g i => parityActualPositionMarks434 L hS J (d*w) x g i.val)=s := by
    funext g i
    rw [hx]
    exact congrFun hs ⟨g,i⟩
  have hD := parity_actual_probe_frame_divisor434 L hS J m hmJ nu aux (d*w) x
  rw [hshared] at hD
  have hR := parity_actual_frame_radius434 J m Ck L hL hS
    (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu) x.val
    (parityActualProbeIdentityFrame434 L hS J m hmJ nu aux) k hk
  rw [hD] at hR
  exact hR

/-- Nonzero original cutoff, a genuine source completion and the literal
quotient step put BOTH physical endpoints in the unchanged global carrier.
Therefore both positive stripped endpoints lie in its exact quotient
carrier. Every quantitative source/window condition is proved internally. -/
theorem parity_eventually_actual_completion_pair_carrier434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J)
      (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (aux : ParityActualProbeAux434 L J m hmJ nu)
      (s : ∀ g : B645ActualGroup434 L hS,
        sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ),
      (∀ g i,s g i∈b645ActualBand434 L hS g) →
    ∀ (Ck Z : ℝ) (k : ℤ), (k.natAbs : ℝ)≤L^Ck → 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u,psi u≠0 → (1/64:ℝ)≤u ∧ u≤64) →
    ∀ (w wp : ℕ), 0<w → 0<wp →
      (sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s w).Nonempty →
      psi ((w : ℝ)/(Z*(parityActualProbeAuxD434 L J m hmJ nu aux : ℝ)))≠0 →
      (wp : ℤ)=(w : ℤ)+(2*k)*(parityActualProbeAuxD434 L J m hmJ nu aux : ℤ) →
      let d := sourceB574SharedDilation434 (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
      let W := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
      w∈paritySharedQuotientPositions434 W d ∧ wp∈paritySharedQuotientPositions434 W d := by
  filter_upwards [parity_eventually_actual_completion_seed434 J CZ] with L hSeed
  refine ⟨hSeed.1,?_⟩
  intro hS m hmJ nu aux s hs Ck Z k hk hZ hZhi psi hSupp w wp hw hwp hcomp hpsi hstep
  dsimp only
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  have hL1 : 1<L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hSeed.1
  have hd := (parity_actual_labelled_shared_support434 L hL1 hS (J+1) E s hs).1
  have hseed := hSeed.2 hS m hmJ nu aux s hs Z hZ hZhi psi hSupp w hw hcomp hpsi
  have hRadius := parity_actual_completion_frame_radius434 L hSeed.1 hS J m hmJ nu aux s w hcomp Ck k hk
  change ((d*w : ℕ) : ℤ)∈b654ParitySeedPositions434 1 (parityDyadicLimit434 L) at hseed
  change |(2*k)*((d*c : ℕ) : ℤ)|≤(b651ParityPathRadius434 J Ck L : ℤ) at hRadius
  have hphysical : ((d*wp : ℕ) : ℤ)=((d*w : ℕ) : ℤ)+(2*k)*((d*c : ℕ) : ℤ) :=
    (parity_harmonic_shared_step_iff434 d c w wp hd k).mpr hstep
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hseed
  have haI := Finset.mem_Ico.mp ha
  have hnlo : (1 : ℤ)≤((d*w : ℕ) : ℤ) := by omega
  have hnhi : ((d*w : ℕ) : ℤ)<(parityDyadicLimit434 L : ℤ) := by omega
  have hr0 : (0 : ℤ)≤(b651ParityPathRadius434 J Ck L : ℤ) := by positivity
  obtain ⟨hrlo,hrhi⟩ := abs_le.mp hRadius
  constructor
  · apply (parity_shared_quotient_mem_iff434 _ d w hd).mpr
    refine ⟨hw,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩ <;> omega
  · apply (parity_shared_quotient_mem_iff434 _ d wp hd).mpr
    refine ⟨hwp,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩ <;> omega
end Green64Analytic.Parity

end

end

