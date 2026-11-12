module

public import Green64.Library.Correlation.Part073
public import Green64.Library.Weights.Part113

@[expose] public section

/-!
# Correlation / PhysicalSharedFreeCapEnvelope

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalSharedFreeCapEnvelope -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 15000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Every exact physical cap-loss coefficient except the endpoint marked
weights and harmonic cutoff. SharedMass retains 1/DR; the complete native
auxiliary law and both inverse cell masses remain explicit. -/
def parityActualComparisonCapEnvelopeCoefficient434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (xi : ℝ) (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ) : ℝ :=
  (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) *
    sourceB574SharedMass434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)) s *
    ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖ * ((Q:ℝ)^4*(xi⁻¹)^2)

theorem parity_actual_comparison_cap_coefficient_nonneg434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (xi : ℝ) (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ) : 0≤parityActualComparisonCapEnvelopeCoefficient434 L hS J m hmJ nu Q xi aux s := by
  have hV (g : B645ActualGroup434 L hS) :
      0≤Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) g := by
    rw [parity_actual_full_mass_exact434]
    exact Finset.sum_nonneg (fun p hp => by positivity)
  have hMass := source_B574_shared_mass_nonneg434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)) s hV
  unfold parityActualComparisonCapEnvelopeCoefficient434
  positivity

/-- One fixed-shared cap-loss slice on the EXACT original quotient carrier.
The only target restriction is the original signed shift; no target
cardinality or independently chosen surrogate interval is introduced. -/
def parityActualPhysicalComparisonCapLossSlice434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (positions : Finset ℤ) (k : ℤ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ) : ℂ :=
  let d := sourceB574SharedDilation434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  ∑ w∈paritySharedQuotientPositions434 positions d,
  ∑ wp∈paritySharedQuotientPositions434 positions d,
    if (2*k)≠0 ∧ (wp:ℤ)=(w:ℤ)+(2*k)*(c:ℤ) then
      parityActualPhysicalComparisonCapLossTerm434 L hS J m hmJ nu Q h xi rho xi3 Z lo hi F G tw psi aux s w wp
    else 0

/-- The frozen literal comparison cap-loss aggregate is exactly the sum
of these true fixed-shared slices. This is a construction equality, before
any bound is applied. -/
theorem parity_actual_comparison_cap_loss_slices_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (positions : Finset ℤ) (k : ℤ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) :
    parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi (-xi3) Z k
      positions lo hi F G (-(rho+xi3)) (-rho) tw 0 psi aux
      (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np) =
    let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
    ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g=>b645ActualBand434 L hS i.1),
      parityActualPhysicalComparisonCapLossSlice434 L hS J m hmJ nu.val Q h xi rho xi3 Z positions k lo hi F G tw psi aux
        (fun g i=>s ⟨g,i⟩) := by
  rfl

private theorem finite_actual_cap_envelope
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (positions : Finset ℤ) (k : ℤ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : ∀ g : B645ActualGroup434 L hS,
      sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (hd : 0<sourceB574SharedDilation434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s)
    (hPoint : ∀ (w wp : ℕ),0<w → 0<wp →
      let d := sourceB574SharedDilation434 (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
      let c := parityActualProbeAuxD434 L J m hmJ nu aux
      ‖parityActualPhysicalComparisonCapLossTerm434 L hS J m hmJ nu Q h xi rho xi3 Z lo hi F G tw psi aux s w wp‖ ≤
        parityOriginalPhysicalPcapFlags434 L d w wp *
        ((w:ℝ)⁻¹*(w.divisors.card:ℝ)^2*(wp.divisors.card:ℝ)^2*‖psi ((w:ℝ)/(Z*(c:ℝ)))‖) *
        ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖ *
        parityActualPhysicalMarkedEnvelope434 L hS J m hmJ nu Q xi s w wp) :
    let d := sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    let N := paritySharedQuotientPositions434 positions d
    ‖parityActualPhysicalComparisonCapLossSlice434 L hS J m hmJ nu Q h xi rho xi3 Z positions k lo hi F G tw psi aux s‖ ≤
      parityActualComparisonCapEnvelopeCoefficient434 L hS J m hmJ nu Q xi aux s*(d:ℝ)*
        parityMarkedPhysicalPcapHarmonicEnvelope434 (sourceNativeOriginalG434 20 L) L d
          (parityActualFullMarkedWeight434 L hS J m hmJ nu)
          (Z*(c:ℝ)) ((2*k)*(c:ℤ)) psi (N.sup id) := by
  classical
  dsimp only
  let d := sourceB574SharedDilation434 (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let N := paritySharedQuotientPositions434 positions d
  let shift : ℤ := (2*k)*(c:ℤ)
  let C := parityActualComparisonCapEnvelopeCoefficient434 L hS J m hmJ nu Q xi aux s
  let W := parityActualFullMarkedWeight434 L hS J m hmJ nu
  let f := fun n : ℕ => ‖psi ((n:ℝ)/(Z*(c:ℝ)))‖/(n:ℝ)*
    parityMarkedPairWeight434 W shift n*parityOriginalPhysicalPcapFlags434 L d n ((n:ℤ)+shift).toNat
  have hC : 0≤C := parity_actual_comparison_cap_coefficient_nonneg434 L hS J m hmJ nu Q xi aux s
  have hf (n : ℕ) : 0≤f n := by
    have hp := parity_marked_pair_weight_nonneg434 W (fun n=>norm_nonneg _) shift n
    have hflags := parity_original_physical_Pcap_flags_nonneg434 L d n ((n:ℤ)+shift).toNat
    exact mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) hp) hflags
  have hN : N⊆Finset.Ioc 0 (N.sup id) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(parity_shared_quotient_positive434 positions d ⟨n,hn⟩).2,
      Finset.le_sup (f:=id) hn⟩
  have hSum : ‖parityActualPhysicalComparisonCapLossSlice434 L hS J m hmJ nu Q h xi rho xi3 Z positions k lo hi F G tw psi aux s‖ ≤ ∑ n∈N,C*f n := by
    apply parity_finite_signed_shift_norm434 N shift ((2*k)≠0)
      (parityActualPhysicalComparisonCapLossTerm434 L hS J m hmJ nu Q h xi rho xi3 Z lo hi F G tw psi aux s)
      (fun n=>C*f n) (fun n=>mul_nonneg hC (hf n))
    intro n hn np hnp hshift
    have hn0 := (Finset.mem_Ioc.mp (hN hn)).1
    have hnp0 := (Finset.mem_Ioc.mp (hN hnp)).1
    have he : np=((n:ℤ)+shift).toNat := by
      have he := congrArg Int.toNat hshift
      simpa only [Int.toNat_natCast] using he
    have hh := hPoint n np hn0 hnp0
    dsimp only at hh
    apply hh.trans_eq
    change _=C*f n
    rw [he]
    dsimp only [C,f,parityActualComparisonCapEnvelopeCoefficient434,
      parityActualPhysicalMarkedEnvelope434,parityMarkedPairWeight434,W]
    simp only [div_eq_mul_inv]
    ring
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  calc
    _ ≤ ∑ n∈N,C*f n := hSum
    _ ≤ ∑ n∈Finset.Ioc 0 (N.sup id),C*f n :=
      Finset.sum_le_sum_of_subset_of_nonneg hN (fun n hn hnot=>mul_nonneg hC (hf n))
    _ = C*(∑ n∈Finset.Ioc 0 (N.sup id),f n) := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      change C*(∑ n∈Finset.Ioc 0 (N.sup id),f n)=
        C*(d:ℝ)*((d:ℝ)⁻¹*(∑ n∈Finset.Ioc 0 (N.sup id),f n))
      rw [mul_assoc C (d:ℝ),←mul_assoc (d:ℝ),mul_inv_cancel₀ hdR,one_mul]

/-- The true B633 cap-loss slice is bounded by the already proved full
marked physical Pcap harmonic envelope. Its exact quotient carrier is
embedded in Ioc(0,sup N); signed-shift uniqueness pays no extra cardinality.
Every endpoint bound, kernel bound and physical cap flag is derived. -/
theorem parity_eventually_actual_B633_cap_loss_envelope434
    (S beta gamma : ℝ) (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1<L ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ), 1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (J m : ℕ) (hmJ : m≤J)
          (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
          (Q : ℕ) (h xi xi3 Z : ℝ), 0<h → 0<xi →
        ∀ (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ)
          (aux : ParityActualProbeAux434 L J m hmJ nu)
          (s : ∀ g : B645ActualGroup434 L hS,
            sourceOriginalProbeSharedSlots434 J 1 m hmJ
              (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ),
          (∀ g i,s g i∈b645ActualBand434 L hS g) →
        ∀ (positions : Finset ℤ) (k : ℤ),
          let d := sourceB574SharedDilation434 (J+1)
            (sourceOriginalProbeSharedSlots434 J 1 m hmJ
              (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
          let c := parityActualProbeAuxD434 L J m hmJ nu aux
          let N := paritySharedQuotientPositions434 positions d
          ‖parityActualPhysicalComparisonCapLossSlice434 L hS J m hmJ nu Q h xi rho xi3 Z positions k lo hi E G tw psi aux s‖ ≤
            parityActualComparisonCapEnvelopeCoefficient434 L hS J m hmJ nu Q xi aux s*(d:ℝ)*
              parityMarkedPhysicalPcapHarmonicEnvelope434 (sourceNativeOriginalG434 20 L) L d
                (parityActualFullMarkedWeight434 L hS J m hmJ nu)
                (Z*(c:ℝ)) ((2*k)*(c:ℤ)) psi (N.sup id) := by
  filter_upwards [parity_eventually_actual_B633_comparison_cap_loss434 S beta gamma hSfine hbeta hgamma]
    with L hPoint
  refine ⟨hPoint.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS J m hmJ nu Q h xi xi3 Z hh hxi lo hi tw psi aux s hs positions k
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have hd := (parity_actual_labelled_shared_support434 L hPoint.1 hS (J+1)
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s hs).1
  exact finite_actual_cap_envelope L hS J m hmJ nu Q h xi rho xi3 Z positions k lo hi E G tw psi aux s hd
    (hPoint.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
      hS J m hmJ nu Q h xi xi3 Z hh hxi lo hi tw psi aux s hs)
end Green64Analytic.Parity

end

end

