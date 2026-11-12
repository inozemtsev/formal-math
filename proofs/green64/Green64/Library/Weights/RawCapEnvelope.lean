module

public import Green64.Library.Correlation.Part074
public import Green64.Library.Weights.Part113

@[expose] public section

/-!
# Weights / RawCapEnvelope

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## RawCapEnvelope -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 22000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Literal fixed-shared RAW cap loss on BOTH exact quotient carriers.
The original none shift is 2*k, since DC=1. -/
def parityRawCapSlice434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (rho xi3 Z : ℝ) (positions : Finset ℤ) (k : ℤ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ) : ℂ :=
  let d := sourceB574SharedDilation434 (J+1)
    (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
  ∑ w∈paritySharedQuotientPositions434 positions d,
  ∑ wp∈paritySharedQuotientPositions434 positions d,
    if (2*k)≠0 ∧ (wp:ℤ)=(w:ℤ)+2*k then
      parityRawCapTerm434 L hS J rho xi3 Z lo hi F G tw psi s w wp
    else 0

/-- The independently defined literal kernel-one full RAW physical
aggregate is exactly the complete sum of the fixed-shared cap-loss slices.
The original endpoint gates remain at DR*w and DR*wp in every slice. -/
theorem parity_raw_cap_slices_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (rho xi3 Z : ℝ) (positions : Finset ℤ) (k : ℤ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ) :
    parityRawHarmonicPhysicalAggregate434 L hS J (-xi3) Z k positions lo hi F G
      (-(rho+xi3)) (-rho) tw 0 psi (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np) =
      ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J =>
        b645ActualBand434 L hS i.1),
        parityRawCapSlice434 L hS J rho xi3 Z positions k lo hi F G tw psi (fun g i=>s ⟨g,i⟩) := by
  rfl

private theorem finite_raw_cap_envelope
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (rho xi3 Z : ℝ) (positions : Finset ℤ) (k : ℤ) (lo hi : ℕ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ)
    (hd : 0<sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s)
    (hPoint : ∀ (w wp : ℕ),0<w → 0<wp →
      let d := sourceB574SharedDilation434 (J+1)
        (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
      ‖parityRawCapTerm434 L hS J rho xi3 Z lo hi F G tw psi s w wp‖ ≤
        parityOriginalPhysicalPcapFlags434 L d w wp *
        ((w:ℝ)⁻¹*(w.divisors.card:ℝ)^2*(wp.divisors.card:ℝ)^2*‖psi ((w:ℝ)/Z)‖) *
        (parityRawCapCoefficient434 L hS J s * parityRawCapMarkedWeight434 L hS w *
          parityRawCapMarkedWeight434 L hS wp)) :
    let d := sourceB574SharedDilation434 (J+1)
      (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
    let N := paritySharedQuotientPositions434 positions d
    ‖parityRawCapSlice434 L hS J rho xi3 Z positions k lo hi F G tw psi s‖ ≤
      parityRawCapCoefficient434 L hS J s*(d:ℝ)*
        parityMarkedPhysicalPcapHarmonicEnvelope434 (sourceNativeOriginalG434 20 L) L d
          (parityRawCapMarkedWeight434 L hS) Z (2*k) psi (N.sup id) := by
  classical
  dsimp only
  let d := sourceB574SharedDilation434 (J+1)
    (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
  let N := paritySharedQuotientPositions434 positions d
  let C := parityRawCapCoefficient434 L hS J s
  let W := parityRawCapMarkedWeight434 L hS
  let f := fun n : ℕ => ‖psi ((n:ℝ)/Z)‖/(n:ℝ)*
    parityMarkedPairWeight434 W (2*k) n*parityOriginalPhysicalPcapFlags434 L d n ((n:ℤ)+2*k).toNat
  have hC : 0≤C := parity_raw_cap_coefficient_nonneg434 L hS J s
  have hf (n : ℕ) : 0≤f n := by
    have hp := parity_marked_pair_weight_nonneg434 W (fun n=>norm_nonneg _) (2*k) n
    have hflags := parity_original_physical_Pcap_flags_nonneg434 L d n ((n:ℤ)+2*k).toNat
    exact mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) hp) hflags
  have hN : N⊆Finset.Ioc 0 (N.sup id) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(parity_shared_quotient_positive434 positions d ⟨n,hn⟩).2,
      Finset.le_sup (f:=id) hn⟩
  have hSum : ‖parityRawCapSlice434 L hS J rho xi3 Z positions k lo hi F G tw psi s‖ ≤ ∑ n∈N,C*f n := by
    apply parity_finite_signed_shift_norm434 N (2*k) ((2*k)≠0)
      (parityRawCapTerm434 L hS J rho xi3 Z lo hi F G tw psi s)
      (fun n=>C*f n) (fun n=>mul_nonneg hC (hf n))
    intro n hn np hnp hshift
    have hn0 := (Finset.mem_Ioc.mp (hN hn)).1
    have hnp0 := (Finset.mem_Ioc.mp (hN hnp)).1
    have he : np=((n:ℤ)+2*k).toNat := by
      have he := congrArg Int.toNat hshift
      simpa only [Int.toNat_natCast] using he
    have hh := hPoint n np hn0 hnp0
    dsimp only at hh
    apply hh.trans_eq
    change _=C*f n
    rw [he]
    dsimp only [C,f,parityMarkedPairWeight434,W]
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

/-- The true B633 RAW cap loss is bounded by the already proved full
physical marked harmonic envelope. The pointwise and arithmetic inputs
are derived; the exact finite carrier has no target-cardinality loss. -/
theorem parity_eventually_actual_B633_raw_cap_envelope434
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
          (J : ℕ) (xi3 Z : ℝ) (lo hi : ℕ) (tw : Bool) (psi : ℝ→ℂ)
          (s : ∀ g : B645ActualGroup434 L hS,parityRawSharedSlots434 J → ℕ),
          (∀ g i,s g i∈b645ActualBand434 L hS g) →
        ∀ (positions : Finset ℤ) (k : ℤ),
          let d := sourceB574SharedDilation434 (J+1)
            (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s
          let N := paritySharedQuotientPositions434 positions d
          ‖parityRawCapSlice434 L hS J rho xi3 Z positions k lo hi E G tw psi s‖ ≤
            parityRawCapCoefficient434 L hS J s*(d:ℝ)*
              parityMarkedPhysicalPcapHarmonicEnvelope434 (sourceNativeOriginalG434 20 L) L d
                (parityRawCapMarkedWeight434 L hS) Z (2*k) psi (N.sup id) := by
  filter_upwards [parity_eventually_actual_B633_raw_cap_term434 S beta gamma hSfine hbeta hgamma]
    with L hPoint
  refine ⟨hPoint.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS J xi3 Z lo hi tw psi s hs positions k
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have hd := (parity_actual_labelled_shared_support434 L hPoint.1 hS (J+1)
    (fun _ : B645ActualGroup434 L hS => parityRawSharedSlots434 J) s hs).1
  exact finite_raw_cap_envelope L hS J rho xi3 Z positions k lo hi E G tw psi s hd
    (hPoint.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
      hS J xi3 Z lo hi tw psi s hs)
end Green64Analytic.Parity

end

end

