module

public import Green64.Library.Correlation.Part071
public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.OriginalGroupMasses
public import Green64.Library.Weights.Part096
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.Part038
public import Green64.Library.Analysis.Estimates.Part014
public import Green64.Library.Weights.Part095
public import Green64.Library.Weights.Part111
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Correlation.Part070

@[expose] public section

/-!
# Weights / Part112

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualRankAuxCells -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare

/-- Exact expansion of the two original auxiliary cell gates. The source
sign and both inverse cell masses remain in the outer coefficient. -/
theorem parity_rank_scalar_gated_test434
    {Q : ℕ} (hA hB : ℝ) (ja jb : ℤ) (massA massB : ℤ → ℝ)
    (ca cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (DA DB r : ℕ) (H : ℂ) :
    parityPrimitiveRankScalar434 hA hB ja jb massA massB ca cb DA DB r * H =
    (-((-1 : ℂ)^r) * (sourceOriginalTwoCellCoefficient434 massA massB ja jb : ℂ)) *
      (if sourceOriginalLiteralLogCell434 hA ja DA ∧ sourceOriginalLiteralLogCell434 hB jb DB then
        star (ca.2 (DA : ZMod (ca.1.val+1))) * star (cb.2 (DB : ZMod (cb.1.val+1))) * H
      else 0) := by
  by_cases hda : sourceOriginalLiteralLogCell434 hA ja DA <;>
    by_cases hdb : sourceOriginalLiteralLogCell434 hB jb DB <;>
    simp [parityPrimitiveRankScalar434, parityCellCharacter434, hda, hdb, mul_assoc]

end Green64Analytic.SourceBlockSieve
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- Actual finite reindex of the cell-gated rank auxiliary integral, with
the literal source cell masses and arbitrary remaining dependence H(c).
The remaining function can retain the original cutoff and shift at c.
They are transported to c=DA*DB, never integrated by a mass-one argument. -/
theorem parity_actual_rank_aux_coupled_reindex434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (ja jb : ℤ)
    (ca cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) (H : ℕ → ℂ) :
    (∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      (parityPrimitiveRankScalar434 hA hB ja jb
        (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hA)
        (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hB)
        ca cb
        (sourceOriginalProbeDA434 m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
        (sourceOriginalProbeDB434 m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
        (nu.1.card+nu.2.card) * H (parityActualProbeAuxD434 L J m hmJ nu aux))) =
    (-((-1 : ℂ)^(nu.1.card+nu.2.card)) *
      (sourceOriginalTwoCellCoefficient434
        (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hA)
        (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hB) ja jb : ℂ)) *
    ∑ a ∈ Fintype.piFinset
      (sourceOriginalProbeAuxPrimeSets434 m nu (sourceNativeOriginalTb434 20 L)),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu (sourceNativeOriginalVbig434 20 L) i)) a : ℂ) *
      (if sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu a) ∧
          sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu a) then
        star (ca.2 (sourceOriginalProbeDA434 m nu a : ZMod (ca.1.val+1))) *
          star (cb.2 (sourceOriginalProbeDB434 m nu a : ZMod (cb.1.val+1))) *
          H (sourceOriginalProbeDA434 m nu a * sourceOriginalProbeDB434 m nu a)
      else 0) := by
  let massA := sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
    (sourceNativeOriginalVbig434 20 L) nu hA
  let massB := sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
    (sourceNativeOriginalVbig434 20 L) nu hB
  let F : (SourceOriginalProbeAuxIndex434 m nu → ℕ) → ℂ := fun a =>
    parityPrimitiveRankScalar434 hA hB ja jb massA massB ca cb
      (sourceOriginalProbeDA434 m nu a) (sourceOriginalProbeDB434 m nu a)
      (nu.1.card+nu.2.card) * H (sourceOriginalProbeDA434 m nu a * sourceOriginalProbeDB434 m nu a)
  have hDisj := parity_actual_comparison_pattern_disjoint434 L m nu hnu
  calc
    _ = ∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      F (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) := by
      apply Finset.sum_congr rfl
      intro aux _
      dsimp only [F, massA, massB]
      rw [parity_actual_probe_aux_product_split434 L J m hmJ nu hnu aux]
    _ = ∑ a ∈ Fintype.piFinset
      (sourceOriginalProbeAuxPrimeSets434 m nu (sourceNativeOriginalTb434 20 L)),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu (sourceNativeOriginalVbig434 20 L) i)) a : ℂ) * F a :=
      parity_memory_aux_complex_reindex434 (sourceNativeOriginalTb434 20 L)
        (sourceNativeOriginalVbig434 20 L) J m hmJ nu hDisj F
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      dsimp only [F, massA, massB]
      rw [parity_rank_scalar_gated_test434]
      ring

end Green64Analytic.Parity

end

end

/-! ## ActualSharedRestoration -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

/-- Exact equality with the unchanged full original P-band indexing. -/
theorem parity_actual_full_band_source434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g : B645ActualGroup434 L hS) :
    b645ActualBand434 L hS g = sourceOriginalPAllActualBands 20 L
      (sourceNativeOriginalFullEquiv434 20 L hS hL g) := by
  rcases g with g | g
  · cases g <;> rfl
  · rfl

/-- The full actual physical group family has the original exp(L^.1)
prime floor, including the distinguished SMALL group. -/
theorem parity_actual_full_band_prime_floor434
    (L : ℝ) (hL : 1≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g : B645ActualGroup434 L hS) (p : ℕ)
    (hp : p ∈ b645ActualBand434 L hS g) :
    p.Prime ∧ Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) := by
  rcases g with g | g
  · cases g with
    | none =>
      have h := source_native_original_S_prime_range434 20 L hS p hp
      exact ⟨h.1,h.2.1⟩
    | some i =>
      have h := source_native_original_Ts_prime_range434 20 L hS i p hp
      exact ⟨h.1,h.2.1⟩
  · have h := source_native_original_Tb_prime_range434 20 L g p hp
    refine ⟨h.1,le_trans ?_ h.2.1⟩
    exact Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))

/-- Distinct actual SMALL and BIG groups contain disjoint prime bands. -/
theorem parity_actual_full_band_disjoint434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g h : B645ActualGroup434 L hS) (p : ℕ)
    (hpg : p ∈ b645ActualBand434 L hS g)
    (hph : p ∈ b645ActualBand434 L hS h) : g=h := by
  apply (sourceNativeOriginalFullEquiv434 20 L hS hL).injective
  rw [parity_actual_full_band_source434 L hL hS g] at hpg
  rw [parity_actual_full_band_source434 L hL hS h] at hph
  exact source_original_P_actual_all_disjoint 20 L (by norm_num) (by linarith) _ _ p hpg hph

/-- Every actual mass is its original reciprocal-prime sum, with no
renormalization or dropped distinguished group. -/
theorem parity_actual_full_mass_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (g : B645ActualGroup434 L hS) :
    Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) g =
      ∑ p ∈ b645ActualBand434 L hS g,1/(p:ℝ) := by
  rcases g with g | g
  · cases g <;> simp only [one_div] <;> rfl
  · simp only [one_div]; rfl

/-- The true mass floor and upper bound hold for every original actual
full physical group before J,m and the endpoint data are chosen. -/
theorem parity_eventually_actual_full_mass_floor434 :
    ∀ᶠ L : ℝ in atTop, 1<L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (g : B645ActualGroup434 L hS),
        Real.log (6/5:ℝ)/2 ≤
          Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
            (sourceNativeOriginalVbig434 20 L) g ∧
        Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
            (sourceNativeOriginalVbig434 20 L) g ≤ 4 := by
  filter_upwards [eventually_source_native_original_group_masses434 20 (by norm_num)] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro hS g
  have hs := h.2.2 hS
  rcases g with g | g
  · cases g with
    | none => exact ⟨hs.1.1,hs.1.2.1⟩
    | some i => exact ⟨(hs.2.1 i).1,(hs.2.1 i).2.1⟩
  · exact ⟨(hs.2.2 g).1,(hs.2.2 g).2.1⟩

/-- A literal actual full-P shared-restoration difference. It uses the
unchanged B574 sum over unrestricted shared physical slices and the original
stripped canonical slice, with the true BIG auxiliary tuple lifted to all
groups. No error estimate is part of the definition. -/
def parityActualCanonicalSharedRestorationError434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (w wp : ℕ) : ℂ :=
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let a := parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu aux
  sourceB574CanonicalRestoredSlice434 J 1 m hmJ fullnu Q hA hB xi P V a (1/2) w wp -
    sourceB574CanonicalStrippedSlice434 J 1 m hmJ fullnu Q hA hB xi P V a (1/2) w wp

/-- B574's genuine shared collision restoration applies to actual Parity r20
with all geometry and mass premises proved. The displayed error retains the
whole marked endpoint pair, both cell inverse masses, every shared coordinate,
and every auxiliary value. No old r6/sigma1 specialization is used. -/
theorem parity_eventually_actual_canonical_shared_restoration434 :
    ∀ᶠ L : ℝ in atTop, 1<L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (J m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (Q : ℕ) (hA hB xi : ℝ)
        (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (w wp : ℕ),
        0<hA → 0<hB → 0<xi → 0<w → 0<wp →
        let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
        let P := b645ActualBand434 L hS
        let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
        let a := parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu aux
        let I := sourceB574OriginalSharedIndex434 J 1 m hmJ fullnu
        let t := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu
        ‖parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q hA hB xi aux w wp‖ ≤
          ((1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ))+1)*
            ((Q:ℝ)^4*(xi⁻¹)^2)*
            ‖actualBigMarkDecoration P t (1/2) V (fun _=>1) w‖*
            ‖actualBigMarkDecoration P t (1/2) V (fun _=>1) wp‖*
            (((Fintype.card I:ℝ)*
              ((w.log2:ℝ)+(wp.log2:ℝ)+((Finset.univ.image a).card:ℝ))+
              (Fintype.card I:ℝ)^2)/(Real.exp (L^(1/10:ℝ))*(Real.log (6/5:ℝ)/2))) := by
  filter_upwards [parity_eventually_actual_full_mass_floor434] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro hS J m hmJ nu Q hA hB xi aux w wp hhA hhB hxi hw hwp
  simpa only [parityActualCanonicalSharedRestorationError434, Nat.cast_one] using
    (source_B574_actual_canonical_shared_restoration_saving434
    J 1 m hmJ (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
    Q hA hB xi (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu aux)
    (1/2) w wp (Real.exp (L^(1/10:ℝ))) (Real.log (6/5:ℝ)/2)
    hhA hhB hxi (by norm_num) (by norm_num) hw hwp (Real.exp_pos _)
    Green64Analytic.ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
    (fun g p hp => (parity_actual_full_band_prime_floor434 L h.1.le hS g p hp).1)
    (parity_actual_full_mass_exact434 L hS)
    (fun g => (h.2.2 hS g).1)
    (fun g p hp => (parity_actual_full_band_prime_floor434 L h.1.le hS g p hp).2)
    (parity_actual_full_band_disjoint434 L h.1 hS))

end Green64Analytic.SourceBlockSieve

end

end

/-! ## PhysicalSharedFreeCore -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
open Green64FullPhysicalE

/-- The native ordinary part and the source outside part are the same
literal prime-power product; this is a definition binding, not a proxy. -/
theorem parity_native_ordinary_source_outside434 (P : Finset ℕ) (n : ℕ) :
    sourceOriginalOrdinaryPart P n = sourceOutsidePart P n := by
  classical
  unfold sourceOriginalOrdinaryPart sourceOutsidePart
  congr 1
  ext p
  simp only [Finset.mem_sdiff,Finset.mem_filter]

/-- Exact removal of every valuation of a P-supported dilation from the
ordinary part. Repetitions and overlap with w are unrestricted. -/
theorem parity_original_ordinary_supported_mul434
    (P : Finset ℕ) (d w : ℕ) (hd : 0<d) (hw : 0<w)
    (hP : d.primeFactors⊆P) :
    sourceOriginalOrdinaryPart P (d*w)=sourceOriginalOrdinaryPart P w := by
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos hd (b613_original_P_part_prime_support434 P w).1)
  calc
    (d*sourceOriginalPPrimePart P w)*sourceOriginalOrdinaryPart P (d*w) =
        sourceOriginalPPrimePart P (d*w)*sourceOriginalOrdinaryPart P (d*w) := by
          rw [b575_shared_dilation_Ppart P d w hd hw hP]
    _ = d*w := b613_original_P_ordinary_recombine434 P (d*w) (Nat.mul_pos hd hw).ne'
    _ = (d*sourceOriginalPPrimePart P w)*sourceOriginalOrdinaryPart P w := by
      rw [mul_assoc,b613_original_P_ordinary_recombine434 P w hw.ne']

/-- The actual native prime-slot core itself is invariant. Both divisor
sums, the character, alpha, residual and prime/interval gates are retained.
This core is uncapped: physical multiplicative Ppart caps are separate. -/
theorem parity_prime_slot_core_supported_mul434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (d w : ℕ) (hd : 0<d) (hw : 0<w)
    (hP : d.primeFactors⊆Finset.univ.biUnion P) :
    primeSlotCoreValue P F (d*w)=primeSlotCoreValue P F w := by
  unfold primeSlotCoreValue
  rw [parity_original_ordinary_supported_mul434 _ d w hd hw hP]

/-- The native real parity character is exactly the source valuation
character after the real-to-complex inclusion. No distinct-prime count. -/
theorem parity_native_group_sign_source434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (tw : Bool) (n : ℕ) :
    (groupSign P tw n : ℂ)=sourceEndpointSign434 (Finset.univ.biUnion P) tw n := by
  cases tw <;>
    simp [groupSign,sourceEndpointSign434,literalSourceParity,sourceOriginalPParityExponent]

/-- The common native parity cancels the full shared dilation without
any clean/injectivity condition and without a coprimality assumption. -/
theorem parity_native_common_shared_parity434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (tw : Bool)
    (d w wp : ℕ) (hd : 0<d) (hw : 0<w) (hwp : 0<wp) :
    (groupSign P tw (d*w) : ℂ)*(groupSign P tw (d*wp) : ℂ)=
      (groupSign P tw w : ℂ)*(groupSign P tw wp : ℂ) := by
  simp only [parity_native_group_sign_source434]
  exact source_original_true_shared_common_parity434 _ d w wp hd.ne' hw.ne' hwp.ne' tw

/-- All labelled shared arrays in the actual full SMALL+BIG P family
have positive true product and original full-P support. Repeated numeric
values remain separate factors in the B574 definition. -/
theorem parity_actual_labelled_shared_support434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (M : ℕ) (E : B645ActualGroup434 L hS → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g) :
    0<sourceB574SharedDilation434 M E s ∧
      (sourceB574SharedDilation434 M E s).primeFactors⊆sourceNativeOriginalG434 20 L := by
  let I := (g : B645ActualGroup434 L hS) × E g
  let p : I → ℕ := fun i => s i.1 i.2
  have hp : ∀ i,(p i).Prime := fun i =>
    (parity_actual_full_band_prime_floor434 L hL.le hS i.1 (p i) (hs i.1 i.2)).1
  have hmem : ∀ i,p i∈sourceNativeOriginalG434 20 L := by
    intro i
    apply Finset.mem_biUnion.mpr
    refine ⟨sourceNativeOriginalFullEquiv434 20 L hS hL i.1,Finset.mem_univ _,?_⟩
    rw [←parity_actual_full_band_source434 L hL hS i.1]
    exact hs i.1 i.2
  have hprod : sourceB574SharedDilation434 M E s=∏ i : I,p i := by
    unfold sourceB574SharedDilation434
    change (∏ g,∏ i : E g,s g i)=(∏ i : (g : B645ActualGroup434 L hS) × E g,s i.1 i.2)
    rw [Fintype.prod_sigma]
  rw [hprod]
  have h := b656_P_prime_product_support434 (sourceNativeOriginalG434 20 L) p hp hmem
  exact ⟨Nat.pos_of_ne_zero h.1,h.2⟩

/-- Actual r20 core stripping on the unrestricted full labelled shared
carrier used by the proved H_T to B574 aggregate. The endpoint core F is
the unchanged arbitrary native PrimeSlotCore, hence includes the actual
B633 Parity cores with all character and prime-slot parameters. -/
theorem parity_actual_labelled_shared_core434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (M : ℕ) (E : B645ActualGroup434 L hS → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g)
    (F : PrimeSlotCore) (w : ℕ) (hw : 0<w) :
    primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F
      (sourceB574SharedDilation434 M E s*w)=
    primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F w := by
  have hd := parity_actual_labelled_shared_support434 L hL hS M E s hs
  exact parity_prime_slot_core_supported_mul434 _ F _ w hd.1 hw hd.2

/-- The SAME true shared product is retained, not erased, by the literal
physical P part. Both endpoint valuations are kept for subsequent cap
insertion; this is not an assertion that physical caps are invariant. -/
theorem parity_actual_labelled_shared_Pparts434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (M : ℕ) (E : B645ActualGroup434 L hS → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g)
    (w wp : ℕ) (hw : 0<w) (hwp : 0<wp) :
    let d := sourceB574SharedDilation434 M E s
    sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) (d*w)=
      d*sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) w ∧
    sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) (d*wp)=
      d*sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) wp := by
  dsimp only
  have hd := parity_actual_labelled_shared_support434 L hL hS M E s hs
  exact ⟨b575_shared_dilation_Ppart _ _ w hd.1 hw hd.2,
    b575_shared_dilation_Ppart _ _ wp hd.1 hwp hd.2⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## PhysicalSharedFreeArithmetic -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 22000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- On positive natural positions the native complex power is the exact
source Mellin exponential, with the same frequency and no phase proxy. -/
theorem parity_native_imaginary_pure_mellin434 (n : ℕ) (hn : 0<n) (t : ℝ) :
    imaginaryPower n t=sourceOriginalPureMellinPhase434 t n := by
  unfold imaginaryPower sourceOriginalPureMellinPhase434
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne' : (n : ℂ)≠0),
    ←Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- Native source and target powers cancel the true shared Mellin factor
under precisely the Parity frequency balance. The physical complex powers
are used at both endpoints, with their actual conjugation convention. -/
theorem parity_native_shared_phase_cancel434
    (d c w wp : ℕ) (hd : 0<d) (hc : 0<c)
    (t1 t2 zeta : ℝ) (hzeta : zeta=t1-t2) :
    star (imaginaryPower (d*w) t1)*imaginaryPower (d*wp) t2*
      sourceOriginalPureMellinPhase434 zeta (d*c)=
    star (imaginaryPower w t1)*imaginaryPower wp t2*
      sourceOriginalPureMellinPhase434 zeta c := by
  have hdphase : star (imaginaryPower d t1)*imaginaryPower d t2*
      sourceOriginalPureMellinPhase434 zeta d=1 := by
    rw [←parity_native_imaginary_pure_mellin434 d hd zeta,
      ←b633_imaginary_power_conjugate434 d t1,
      ←b633_imaginary_power_add434 d hd (-t1) t2,
      ←b633_imaginary_power_add434 d hd (-t1+t2) zeta]
    have hz : -t1+t2+zeta=0 := by rw [hzeta]; ring
    rw [hz]
    simp [imaginaryPower]
  rw [b633_imaginary_power_mul434,b633_imaginary_power_mul434,
    source_original_pure_mellin_product_factor434 zeta d c hd hc,star_mul]
  calc
    _ = (star (imaginaryPower d t1)*imaginaryPower d t2*
        sourceOriginalPureMellinPhase434 zeta d)*
      (star (imaginaryPower w t1)*imaginaryPower wp t2*
        sourceOriginalPureMellinPhase434 zeta c) := by ring
    _ = _ := by rw [hdphase,one_mul]

/-- The arithmetic scalar evaluated directly at the stripped endpoints.
It uses the original cores, common parity, cutoff and auxiliary-product
phase. It contains no shared assignment, and no physical Ppart caps are
silently inserted into the uncapped original endpoint core. -/
def parityHarmonicStrippedArithmetic434
    (L : ℝ) (zeta Z : ℝ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (psi : ℝ → ℂ) (c w wp : ℕ) : ℂ :=
  (w : ℂ)⁻¹ * star (parityHarmonicSourceArithmetic434 L F t1 tw Z 0 w) *
    psi ((w : ℝ)/(Z*(c : ℝ))) *
    (groupSign (sourceOriginalPAllActualBands 20 L) tw wp : ℂ) *
    parityHarmonicEndpointArithmetic434 L G t2 wp *
    sourceOriginalPureMellinPhase434 zeta c

/-- Exact literal native arithmetic stripping. The original source seed
is still evaluated at DR*w: this theorem does not assume that the finite
source window is invariant under a dilation. Both unrestricted core
values, common valuation parity and native Mellin phases are proved to
lose DR, leaving the same harmonic 1/w and original cutoff at w/(Z*DC). -/
theorem parity_harmonic_shared_arithmetic_strip434
    (L : ℝ) (zeta Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (psi : ℝ → ℂ) (d c w wp : ℕ)
    (hd : 0<d) (hc : 0<c) (hw : 0<w) (hwp : 0<wp)
    (hP : d.primeFactors⊆sourceNativeOriginalG434 20 L)
    (hzeta : zeta=t1-t2) :
    parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw 0 psi d c w wp=
      if ((d*w : ℕ) : ℤ)∈b654ParitySeedPositions434 lo hi then
        parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi c w wp
      else 0 := by
  let P := sourceOriginalPAllActualBands 20 L
  have hF := parity_prime_slot_core_supported_mul434 P F d w hd hw hP
  have hG := parity_prime_slot_core_supported_mul434 P G d wp hd hwp hP
  have hParity := parity_native_common_shared_parity434 P tw d w wp hd hw hwp
  have hPhase := parity_native_shared_phase_cancel434 d c w wp hd hc t1 t2 zeta hzeta
  have hstar (r : ℝ) : star (r : ℂ)=(r : ℂ) := by simp
  unfold parityHarmonicSharedArithmetic434
  by_cases hseed : ((d*w : ℕ) : ℤ)∈b654ParitySeedPositions434 lo hi
  · simp only [hseed,ite_true]
    unfold parityHarmonicStrippedArithmetic434 parityHarmonicSourceArithmetic434
      parityHarmonicEndpointArithmetic434
    change (w : ℂ)⁻¹ * star ((groupSign P tw (d*w) : ℂ)*
        ((((d*w : ℕ) : ℝ)/Z : ℝ) : ℂ)^(-Complex.I*(0 : ℂ))*
        (imaginaryPower (d*w) t1*primeSlotCoreValue P F (d*w)))*
      psi ((w : ℝ)/(Z*(c : ℝ)))*(groupSign P tw (d*wp) : ℂ)*
      (imaginaryPower (d*wp) t2*primeSlotCoreValue P G (d*wp))*
      sourceOriginalPureMellinPhase434 zeta (d*c)=_
    simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,hF,hG,star_mul,hstar]
    calc
      _ = (w : ℂ)⁻¹ *
          ((groupSign P tw (d*w) : ℂ)*(groupSign P tw (d*wp) : ℂ))*
          (star (imaginaryPower (d*w) t1)*imaginaryPower (d*wp) t2*
            sourceOriginalPureMellinPhase434 zeta (d*c))*
          star (primeSlotCoreValue P F w)*primeSlotCoreValue P G wp*
          psi ((w : ℝ)/(Z*(c : ℝ))) := by ring
      _ = (w : ℂ)⁻¹ *
          ((groupSign P tw w : ℂ)*(groupSign P tw wp : ℂ))*
          (star (imaginaryPower w t1)*imaginaryPower wp t2*
            sourceOriginalPureMellinPhase434 zeta c)*
          star (primeSlotCoreValue P F w)*primeSlotCoreValue P G wp*
          psi ((w : ℝ)/(Z*(c : ℝ))) := by rw [hParity,hPhase]
      _ = _ := by ring
  · simp only [hseed,ite_false]

/-- Specialization on the complete actual r20 shared-array carrier and
the actual Parity frequencies. All support and balance obligations are
proved here; no clean event, core replacement or analytic estimate is
introduced. The original finite source seed remains explicit. -/
theorem parity_actual_labelled_shared_arithmetic434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (M : ℕ) (E : B645ActualGroup434 L hS → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g)
    (rho xi3 Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ → ℂ) (c w wp : ℕ)
    (hc : 0<c) (hw : 0<w) (hwp : 0<wp) :
    let d := sourceB574SharedDilation434 M E s
    parityHarmonicSharedArithmetic434 L (-xi3) Z lo hi F G
        (-(rho+xi3)) (-rho) tw 0 psi d c w wp=
      if ((d*w : ℕ) : ℤ)∈b654ParitySeedPositions434 lo hi then
        parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
          (-(rho+xi3)) (-rho) tw psi c w wp
      else 0 := by
  dsimp only
  have hd := parity_actual_labelled_shared_support434 L hL hS M E s hs
  exact parity_harmonic_shared_arithmetic_strip434 L (-xi3) Z lo hi F G
    (-(rho+xi3)) (-rho) tw psi _ c w wp hd.1 hc hw hwp hd.2 (by ring)
end Green64Analytic.Parity

end

end

/-! ## ActualRankAuxMellin -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- A genuine multiplicative conjugate character times the native Mellin
power. The original pure-logarithm phase is recovered on positive inputs. -/
def parityAuxCharacterMellin434 (q : ℕ) (chi : DirichletCharacter ℂ q) (t : ℝ) : ℕ →* ℂ where
  toFun n := star (chi (n : ZMod q)) * imaginaryPower n t
  map_one' := by simp [imaginaryPower]
  map_mul' n n' := by
    simp only [Nat.cast_mul, map_mul, star_mul, b633_imaginary_power_mul434]
    ring

/-- Both labelled products are positive on every actual typed assignment,
including empty selected lists, whose products are one. -/
theorem parity_actual_aux_products_positive434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    0 < sourceOriginalProbeDA434 m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) ∧
    0 < sourceOriginalProbeDB434 m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) := by
  have hpos (z : SourceOriginalProbeAuxIndex434 m nu) :
      0 < sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux z := by
    change 0 < (aux (sourceOriginalProbeMemoryAuxSlot434 J m hmJ nu z).1
      (sourceOriginalProbeMemoryAuxSlot434 J m hmJ nu z).2).val
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  constructor
  · exact Finset.prod_pos (fun z _ => hpos (Sum.inl z))
  · exact Finset.prod_pos (fun z _ => hpos (Sum.inr z))

/-- The one common phase at c=DA*DB shifts both frequencies with the
same sign, while retaining the two conjugated character factors. -/
theorem parity_aux_character_mellin_common_phase434
    (qA qB : ℕ) (chiA : DirichletCharacter ℂ qA) (chiB : DirichletCharacter ℂ qB)
    (tA tB zeta : ℝ) (DA DB : ℕ) (hDA : 0 < DA) (hDB : 0 < DB) :
    parityAuxCharacterMellin434 qA chiA tA DA * parityAuxCharacterMellin434 qB chiB tB DB *
      sourceOriginalPureMellinPhase434 zeta (DA*DB) =
    parityAuxCharacterMellin434 qA chiA (tA+zeta) DA *
      parityAuxCharacterMellin434 qB chiB (tB+zeta) DB := by
  change (star (chiA (DA : ZMod qA)) * imaginaryPower DA tA) *
      (star (chiB (DB : ZMod qB)) * imaginaryPower DB tB) *
        sourceOriginalPureMellinPhase434 zeta (DA*DB) =
    (star (chiA (DA : ZMod qA)) * imaginaryPower DA (tA+zeta)) *
      (star (chiB (DB : ZMod qB)) * imaginaryPower DB (tB+zeta))
  rw [← parity_native_imaginary_pure_mellin434 (DA*DB) (Nat.mul_pos hDA hDB) zeta,
    b633_imaginary_power_mul434,
    b633_imaginary_power_add434 DA hDA tA zeta,
    b633_imaginary_power_add434 DB hDB tB zeta]
  ring

/-- Actual Parity auxiliary Fourier-Mellin product law with the original
common phase at the full native c. Every actual labelled A/B draw, its
prime support and its original V mass remain present. The final prime
sums use the literal source pure Mellin exponential, not a phase proxy.
No cell gate, cutoff or shifted endpoint correlation is discarded. -/
theorem parity_actual_rank_aux_mellin_product_law434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    (qA qB : ℕ) (chiA : DirichletCharacter ℂ qA) (chiB : DirichletCharacter ℂ qB)
    (tA tB zeta : ℝ) :
    (∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      (parityAuxCharacterMellin434 qA chiA tA (sourceOriginalProbeDA434 m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)) *
        parityAuxCharacterMellin434 qB chiB tB (sourceOriginalProbeDB434 m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)) *
        sourceOriginalPureMellinPhase434 zeta (parityActualProbeAuxD434 L J m hmJ nu aux))) =
    (∏ z : nu.1, ∑ p ∈ sourceNativeOriginalTb434 20 L z.val.1,
      (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L z.val.1) p : ℂ) *
        (star (chiA (p : ZMod qA)) * sourceOriginalPureMellinPhase434 (tA+zeta) p)) *
    (∏ z : nu.2, ∑ p ∈ sourceNativeOriginalTb434 20 L z.val.1,
      (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L z.val.1) p : ℂ) *
        (star (chiB (p : ZMod qB)) * sourceOriginalPureMellinPhase434 (tB+zeta) p)) := by
  have hprime (q : ℕ) (chi : DirichletCharacter ℂ q) (t : ℝ)
      (g : sourceNativeOriginalBigType434 20 L) :
      (∑ p ∈ sourceNativeOriginalTb434 20 L g,
        (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L g) p : ℂ) *
          parityAuxCharacterMellin434 q chi t p) =
      ∑ p ∈ sourceNativeOriginalTb434 20 L g,
        (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L g) p : ℂ) *
          (star (chi (p : ZMod q)) * sourceOriginalPureMellinPhase434 t p) := by
    apply Finset.sum_congr rfl
    intro p hp
    change (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L g) p : ℂ) *
      (star (chi (p : ZMod q)) * imaginaryPower p t) = _
    rw [parity_native_imaginary_pure_mellin434 p
      (source_native_original_Tb_prime_range434 20 L g p hp).1.pos t]
  calc
    _ = ∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      (parityAuxCharacterMellin434 qA chiA (tA+zeta) (sourceOriginalProbeDA434 m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)) *
        parityAuxCharacterMellin434 qB chiB (tB+zeta) (sourceOriginalProbeDB434 m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))) := by
      apply Finset.sum_congr rfl
      intro aux _
      congr 1
      rw [parity_actual_probe_aux_product_split434 L J m hmJ nu hnu aux]
      exact parity_aux_character_mellin_common_phase434 qA qB chiA chiB tA tB zeta _ _
        (parity_actual_aux_products_positive434 L J m hmJ nu aux).1
        (parity_actual_aux_products_positive434 L J m hmJ nu aux).2
    _ = (∏ z : nu.1, ∑ p ∈ sourceNativeOriginalTb434 20 L z.val.1,
      (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L z.val.1) p : ℂ) *
        parityAuxCharacterMellin434 qA chiA (tA+zeta) p) *
      (∏ z : nu.2, ∑ p ∈ sourceNativeOriginalTb434 20 L z.val.1,
        (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L z.val.1) p : ℂ) *
          parityAuxCharacterMellin434 qB chiB (tB+zeta) p) :=
      parity_actual_rank_aux_product_law434 L J m hmJ nu hnu _ _
    _ = _ := by
      congr 1
      · exact Finset.prod_congr rfl (fun z _ => hprime qA chiA (tA+zeta) z.val.1)
      · exact Finset.prod_congr rfl (fun z _ => hprime qB chiB (tB+zeta) z.val.1)
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeCaps -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare

/-- The actual original r20 physical P cap. The P part retains every
prime-power valuation, and sigma is exactly 1/44. -/
def parityOriginalPhysicalPcap434 (L : ℝ) (n : ℕ) : Prop :=
  sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n ≤
    ⌊Real.exp (L/44)⌋₊

/-- Both physical endpoint caps, before removing any shared product. -/
def parityOriginalPhysicalPairPcap434 (L : ℝ) (n np : ℕ) : ℂ :=
  if parityOriginalPhysicalPcap434 L n ∧ parityOriginalPhysicalPcap434 L np
  then 1 else 0

/-- On the true P part the support condition in the ORIGINAL B537 R carrier
is automatic. This is an exact source-carrier equivalence for every r and
H, with all multiplicities retained and no size or coprimality premise. -/
theorem parity_original_Ppart_support_mem434
    (r : ℕ) (L : ℝ) (H n : ℕ) :
    sourceOriginalPPrimePart (sourceNativeOriginalG434 r L) n ∈
      sourceActualSortedPPartSupport r L H ↔
    sourceOriginalPPrimePart (sourceNativeOriginalG434 r L) n ≤ H := by
  classical
  have hp := b613_original_P_part_prime_support434 (sourceNativeOriginalG434 r L) n
  constructor
  · intro hn
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
  · intro hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hp.1,hn⟩,?_⟩
    intro q hq
    have hqp := Nat.mem_primeFactors.mp hq
    exact hp.2 q hqp.1 hqp.2.1

/-- The original r20 support R at the literal floor(exp(L/44)) is exactly
our physical cap; no D61 r6 parameter is used. -/
theorem parity_actual_original_Pcap_mem434 (L : ℝ) (n : ℕ) :
    sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n ∈
      sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊ ↔
    parityOriginalPhysicalPcap434 L n :=
  parity_original_Ppart_support_mem434 20 L _ n

/-- Exact factorization of the genuine B521 gated Gram kernel at actual
r20 P and the ORIGINAL R carrier. This identifies the gate factor only;
it does not assert that a complete harmonic frame functional equals the
B521 channel, whose other weights and shift have their own interface. -/
theorem parity_actual_B521_gate_factor434
    (L : ℝ) (F G : PrimeSlotCore) (k : ℤ) (a1 a2 : ℝ)
    (psi : ℕ → ℂ) (z : ℕ) :
    sourceNativeGatedGramKernel (sourceOriginalPAllActualBands 20 L)
      (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
      F G k a1 a2 psi z =
    parityOriginalPhysicalPairPcap434 L z (((z:ℤ)+2*k).toNat) *
      (if 0 < (z:ℤ)+2*k then
        psi z * imaginaryPower z a1 * imaginaryPower (((z:ℤ)+2*k).toNat) a2 *
        star (primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z) *
        primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G (((z:ℤ)+2*k).toNat) *
        ((sourceMarkedWeight (1/2:ℝ) 1 (sourceOriginalPAllActualBands 20 L) z *
          sourceMarkedWeight (1/2:ℝ) 1 (sourceOriginalPAllActualBands 20 L)
            (((z:ℤ)+2*k).toNat):ℝ):ℂ)
      else 0) := by
  classical
  have hmem (n : ℕ) :
      sourceOriginalPPrimePart (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) n ∈
        sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊ ↔
      parityOriginalPhysicalPcap434 L n := parity_actual_original_Pcap_mem434 L n
  unfold sourceNativeGatedGramKernel
  dsimp only
  simp only [hmem]
  unfold parityOriginalPhysicalPairPcap434
  by_cases hz : 0 < (z:ℤ)+2*k <;>
    by_cases h1 : parityOriginalPhysicalPcap434 L z <;>
    by_cases h2 : parityOriginalPhysicalPcap434 L (((z:ℤ)+2*k).toNat) <;>
    simp [hz,h1,h2]

/-- The exact omitted part is the UNION of the two genuine physical cap
failures. Their intersection is counted once, not twice. -/
theorem parity_original_pair_Pcap_complement434 (L : ℝ) (n np : ℕ) :
    1-parityOriginalPhysicalPairPcap434 L n np =
    if ⌊Real.exp (L/44)⌋₊ < sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n ∨
       ⌊Real.exp (L/44)⌋₊ < sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) np
    then (1:ℂ) else 0 := by
  classical
  unfold parityOriginalPhysicalPairPcap434 parityOriginalPhysicalPcap434
  by_cases h1 : sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n ≤ ⌊Real.exp (L/44)⌋₊
  · by_cases h2 : sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) np ≤ ⌊Real.exp (L/44)⌋₊
    · simp [h1,h2,not_lt.mpr h1,not_lt.mpr h2]
    · simp [h1,h2,not_le.mp h2]
  · simp [h1,not_le.mp h1]

/-- Pullback of BOTH original physical caps through the genuine shared
product. The shared labels may repeat and may overlap the free products;
DR remains on BOTH cap arguments. -/
theorem parity_actual_labelled_shared_Pcaps434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (M : ℕ) (E : B645ActualGroup434 L hS → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g)
    (w wp : ℕ) (hw : 0<w) (hwp : 0<wp) :
    let d := sourceB574SharedDilation434 M E s
    parityOriginalPhysicalPairPcap434 L (d*w) (d*wp) =
      if d*sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) w ≤ ⌊Real.exp (L/44)⌋₊ ∧
         d*sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) wp ≤ ⌊Real.exp (L/44)⌋₊
      then 1 else 0 := by
  dsimp only
  have hp := parity_actual_labelled_shared_Pparts434 L hL hS M E s hs w wp hw hwp
  dsimp only at hp
  unfold parityOriginalPhysicalPairPcap434 parityOriginalPhysicalPcap434
  simp only [hp.1,hp.2]
end Green64Analytic.Parity

end

end

/-! ## ParamPhysicalPcap -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 30000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare

/-- The TRUE original physical P-prime-power cap at the freely fixed
Type II exponent beta/4, rather than the old r20 sigma=1/44 cap.
It retains ALL valuations and the same actual moving P-band union. -/
def parityOriginalPhysicalPcapBeta434 (beta L : ℝ) (n : ℕ) : Prop :=
  sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n ≤
    ⌊Real.exp ((beta/4)*L)⌋₊

/-- Both original signed physical endpoints, with the genuine beta cap. -/
def parityOriginalPhysicalPairPcapBeta434
    (beta L : ℝ) (n np : ℕ) : ℂ :=
  if parityOriginalPhysicalPcapBeta434 beta L n ∧
     parityOriginalPhysicalPcapBeta434 beta L np then 1 else 0

/-- Exact identification with the ORIGINAL parameterised B537 P support.
This holds for every beta and every n, not merely for small P-parts. -/
theorem parity_actual_original_beta_Pcap_mem434 (beta L : ℝ) (n : ℕ) :
    sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n ∈
      sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ ↔
    parityOriginalPhysicalPcapBeta434 beta L n :=
  parity_original_Ppart_support_mem434 20 L _ n

/-- A parameterised B521 gated Gram kernel is EXACTLY its ungated
physical source kernel times the TRUE pair cap at both endpoints.
This is an algebraic identity, not yet a Parity (4.17) cancellation bound. -/
theorem parity_actual_B521_beta_gate_factor434
    (beta L : ℝ) (F G : PrimeSlotCore) (k : ℤ) (a1 a2 : ℝ)
    (psi : ℕ → ℂ) (z : ℕ) :
    sourceNativeGatedGramKernel (sourceOriginalPAllActualBands 20 L)
      (sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊)
      F G k a1 a2 psi z =
    parityOriginalPhysicalPairPcapBeta434 beta L z (((z:ℤ)+2*k).toNat) *
      (if 0 < (z:ℤ)+2*k then
        psi z * imaginaryPower z a1 *
          imaginaryPower (((z:ℤ)+2*k).toNat) a2 *
        star (primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z) *
        primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G (((z:ℤ)+2*k).toNat) *
        ((sourceMarkedWeight (1/2:ℝ) 1 (sourceOriginalPAllActualBands 20 L) z *
          sourceMarkedWeight (1/2:ℝ) 1 (sourceOriginalPAllActualBands 20 L)
            (((z:ℤ)+2*k).toNat):ℝ):ℂ)
      else 0) := by
  classical
  have hmem (n : ℕ) :
      sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) n ∈
        sourceActualSortedPPartSupport 20 L ⌊Real.exp ((beta/4)*L)⌋₊ ↔
      parityOriginalPhysicalPcapBeta434 beta L n :=
    parity_actual_original_beta_Pcap_mem434 beta L n
  unfold sourceNativeGatedGramKernel
  dsimp only
  simp only [hmem]
  unfold parityOriginalPhysicalPairPcapBeta434
  by_cases hz : 0 < (z:ℤ)+2*k <;>
    by_cases h1 : parityOriginalPhysicalPcapBeta434 beta L z <;>
    by_cases h2 : parityOriginalPhysicalPcapBeta434 beta L (((z:ℤ)+2*k).toNat) <;>
    simp [hz,h1,h2]

/-- The exact discarded pair set is the union of the two ACTUAL beta
cap failures. No erroneous one-sided cap or double counting. -/
theorem parity_original_pair_Pcap_beta_complement434
    (beta L : ℝ) (n np : ℕ) :
    1-parityOriginalPhysicalPairPcapBeta434 beta L n np =
    if ⌊Real.exp ((beta/4)*L)⌋₊ <
         sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n ∨
       ⌊Real.exp ((beta/4)*L)⌋₊ <
         sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) np
    then (1:ℂ) else 0 := by
  classical
  unfold parityOriginalPhysicalPairPcapBeta434 parityOriginalPhysicalPcapBeta434
  by_cases h1 : sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n ≤
      ⌊Real.exp ((beta/4)*L)⌋₊
  · by_cases h2 : sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) np ≤
        ⌊Real.exp ((beta/4)*L)⌋₊
    · simp [h1,h2,not_lt.mpr h1,not_lt.mpr h2]
    · simp [h1,h2,not_le.mp h2]
  · simp [h1,not_le.mp h1]

/-- Pullback of BOTH parameter-dependent physical P caps through the
Genuine repeated shared group factor D_R, retaining physical endpoints
D_R*w and D_R*w'. No cap commutation is postulated. -/
theorem parity_actual_labelled_shared_Pcaps_beta434
    (beta L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (M : ℕ) (E : B645ActualGroup434 L hS → Finset (Fin M))
    (s : ∀ g,E g → ℕ)
    (hs : ∀ g i,s g i∈b645ActualBand434 L hS g)
    (w wp : ℕ) (hw : 0<w) (hwp : 0<wp) :
    let d := sourceB574SharedDilation434 M E s
    parityOriginalPhysicalPairPcapBeta434 beta L (d*w) (d*wp) =
      if d*sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) w ≤
          ⌊Real.exp ((beta/4)*L)⌋₊ ∧
         d*sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) wp ≤
          ⌊Real.exp ((beta/4)*L)⌋₊
      then 1 else 0 := by
  dsimp only
  have hp := parity_actual_labelled_shared_Pparts434
    L hL hS M E s hs w wp hw hwp
  dsimp only at hp
  unfold parityOriginalPhysicalPairPcapBeta434 parityOriginalPhysicalPcapBeta434
  simp only [hp.1,hp.2]

/-- beta=1/11 recovers EXACTLY the historical fixed sigma=1/44 gate,
which isolates the previous proven special case without extrapolating it. -/
theorem parity_actual_beta_one_eleventh_recovers_old_cap434 (L : ℝ) (n : ℕ) :
    parityOriginalPhysicalPcapBeta434 (1/11) L n ↔
    parityOriginalPhysicalPcap434 L n := by
  have h : ((1/11:ℝ)/4)*L = L/44 := by ring
  simp only [parityOriginalPhysicalPcapBeta434,
    parityOriginalPhysicalPcap434,h]
end Green64Analytic.Parity

end

end

/-! ## ParamOriginalPhysicalDiscard -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Exact original Parity physical cap deletion on the actual r20 P part:
its UNSIGNED original W1 mass is literally the beta/4 source Rankin
tail, with all P-prime-power valuations kept. This is a real physical
coefficient statement, not an abstract parameterised Rankin estimate. -/
theorem parity_actual_original_beta_physical_Pcap_discard_exact434
    (beta L : ℝ) (Y : ℕ) :
    (∑ u ∈ Finset.Ioc 0 Y,
      if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
      else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) =
    ∑ u ∈ (Finset.Ioc 0 Y).filter
      (fun u => ⌊Real.exp ((beta/4)*L)⌋₊ <
        sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u),
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  have hPset : sourceNativeOriginalG434 20 L =
      Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L) := by rfl
  rw [←hPset]
  unfold parityOriginalPhysicalPcapBeta434
  by_cases hc : sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) u ≤
      ⌊Real.exp ((beta/4)*L)⌋₊
  · simp [hc,not_lt.mpr hc]
  · simp [hc,not_le.mp hc]

/-- For ANY beta=b_*>0 and arbitrary inverse-log precision A, the
ENTIRE actual original W1 mass removed by the SAME beta/4 cap used in
B521 physical Parity (4.17) is O(Y L^-A), uniformly in finite Y. This is
only a one-endpoint unsigned original mass bound; it does not assume or
conclude the whole two-endpoint signed character-correlation estimate. -/
theorem parity_eventually_original_beta_physical_Pcap_discard_all_log434
    (beta A : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℕ,
    (∑ u ∈ Finset.Ioc 0 Y,
      if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
      else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) ≤
    (Y:ℝ)*L^(-A) := by
  filter_upwards [parity_actual_P_part_beta_quarter_all_log_saving434
    beta A hbeta] with L hTail
  intro Y
  rw [parity_actual_original_beta_physical_Pcap_discard_exact434]
  exact hTail Y
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeCapped -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 22000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- One literal full physical summand, copied from the independent original
frame construction: source seed, mu0, c1 phase, complete frame scalar,
frame-dependent cutoff, target parity and full endpoint coefficient.
This definition uses no B574 slice or dyadic target. -/
def parityActualOriginalHarmonicFrameTerm434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (x y : B654ActualParityState434 L hS J positions)
    (frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ)) : ℂ :=
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  if x.val.1.val ∈ b654ParitySeedPositions434 lo hi then
    (b657ActualStateMass434 L hS J : ℂ) *
    star (b659ActualParityRootCoefficient434 L hS J F t1 tw 1 Z v x.val.1.val) *
    b650IntegerFrameScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats positions (1/2 : ℝ) (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y frame *
    psi ((x.val.1.val : ℝ)/(Z*(b650NativeFrameD434 SP (fun _ p => p.val)
      BP (fun _ p => p.val) J 1 m pats x.val.2 frame : ℝ))) *
    (groupSign (sourceOriginalPAllActualBands 20 L) tw y.val.1.val.toNat : ℂ) *
    b656IntegerPrimeEndpointCoefficient434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 (sourceOriginalPAllActualBands 20 L) G (1/2 : ℝ) t2 y.val.1.val
  else 0

/-- The capped functional is defined DIRECTLY on all original physical
states and complete primitive frames. Both literal physical Ppart caps
are inserted before any permutation, quotient, shared or B574 reindex. -/
def parityActualCappedHarmonicFrameSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  ∑ x : B654ActualParityState434 L hS J positions,
  ∑ y : B654ActualParityState434 L hS J positions,
  ∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ),
    if parityOriginalPhysicalPcap434 L x.val.1.val.toNat ∧
       parityOriginalPhysicalPcap434 L y.val.1.val.toNat then
      parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi x y frame
    else 0

/-- Literal omitted physical sum: the union of the two original endpoint
cap failures on the same full frame/state carrier, with no double count. -/
def parityActualPhysicalPcapLossFrameSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  ∑ x : B654ActualParityState434 L hS J positions,
  ∑ y : B654ActualParityState434 L hS J positions,
  ∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ),
    if ⌊Real.exp (L/44)⌋₊ < sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) x.val.1.val.toNat ∨
       ⌊Real.exp (L/44)⌋₊ < sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) y.val.1.val.toNat then
      parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi x y frame
    else 0

/-- Exact factorization of the literal frame summand into its original
position/divisor test and its complete scalar. All marks, auxiliary laws,
permutation laws and both inverse cell masses remain in that scalar. -/
theorem parity_actual_original_frame_term_factor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (x y : B654ActualParityState434 L hS J positions)
    (frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ)) :
    let SP := SourceNativeMemorySP434 20 L hS
    let BP := SourceNativeMemoryBP434 20 L
    let pats := sourceOriginalMemoryRawComparisonPattern434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
    let Knu := sourceOriginalMemoryRawComparisonK434
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
    parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi x y frame =
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi x.val.1.val y.val.1.val
      (b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats x.val.2 frame) *
    b650IntegerFrameScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats positions (1/2 : ℝ) (SourceNativeMemorySmallMass434 20 L hS)
      (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y frame := by
  dsimp only
  unfold parityActualOriginalHarmonicFrameTerm434 parityActualHarmonicPositionTest434
  dsimp only
  by_cases hs : x.val.1.val ∈ b654ParitySeedPositions434 lo hi
  · simp only [hs,ite_true]
    ring
  · simp only [hs,ite_false,zero_mul]

/-- Exact original uncapped minus independently constructed capped sum.
The right side is the literal two-endpoint physical cap failure sum. -/
theorem parity_actual_harmonic_frame_cap_difference434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityActualHarmonicFrameSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi -
      parityActualCappedHarmonicFrameSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi =
    parityActualPhysicalPcapLossFrameSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi := by
  classical
  change (∑ x,∑ y,∑ frame,parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi x y frame) - _ = _
  unfold parityActualCappedHarmonicFrameSum434 parityActualPhysicalPcapLossFrameSum434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro frame _
  by_cases h1 : parityOriginalPhysicalPcap434 L x.val.1.val.toNat
  · by_cases h2 : parityOriginalPhysicalPcap434 L y.val.1.val.toNat
    · have hn1 := not_lt.mpr h1
      have hn2 := not_lt.mpr h2
      simp only [h1,h2,and_self,ite_true,sub_self,hn1,hn2,false_or,ite_false]
    · have hn2 := not_le.mp h2
      simp only [h1,h2,and_false,ite_false,sub_zero,hn2,or_true,ite_true]
  · have hn1 := not_le.mp h1
    simp only [h1,false_and,ite_false,sub_zero,hn1,true_or,ite_true]

/-- The new capped H_T is independently the full physical frame/state sum
on the original global interval. The existing uncapped H_T is unchanged. -/
def parityCappedHarmonicPhysical434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  parityActualCappedHarmonicFrameSum434 L hS J m hmJ Q h xi zeta Z k
    (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi

/-- Exact cap insertion difference for the original H_T. This is an
identity on the original physical carrier, not an analytic estimate or
an identification with the complete B521 channel. -/
theorem parity_harmonic_physical_cap_difference434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi -
      parityCappedHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
    parityActualPhysicalPcapLossFrameSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi := by
  rw [parity_controlled_harmonic_eq_frames434]
  exact parity_actual_harmonic_frame_cap_difference434 L hS J m hmJ Q h xi zeta Z k
    (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeCapTransport -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The complete positive physical-fibre sum with a fixed numeric endpoint
weight. The two endpoint positions remain independent; W has no auxiliary,
mark, residue or permutation argument. RAW and comparison base frames,
all original laws and all original scalar factors are retained. -/
def parityActualEndpointWeightedPositiveFibreSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (W : ℕ → ℕ → ℂ) : ℂ :=
  ∑ a : ParityHarmonicBaseFrame434 L J m hmJ,
  ∑ n : parityPositiveNaturalPositions434 positions,
  ∑ np : parityPositiveNaturalPositions434 positions,
  ∑ x : ParityActualPositionFibre434 L hS J n.val,
  ∑ y : ParityActualPositionFibre434 L hS J np.val,
    W n.val np.val * parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi a
      (parityActualNaturalState434 L hS J positions n x)
      (parityActualNaturalState434 L hS J positions np y)

/-- The proved complete four-permutation marginal is valid with every
fixed endpoint weight, in particular both literal original Ppart caps.
This is an exact weighted transport on the original physical carrier. -/
theorem parity_actual_harmonic_endpoint_weight_marginal434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (W : ℕ → ℕ → ℂ) :
    (∑ x : B654ActualParityState434 L hS J positions,
     ∑ y : B654ActualParityState434 L hS J positions,
     ∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ),
       W x.val.1.val.toNat y.val.1.val.toNat *
       parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi x y frame) =
    ∑ a : ParityHarmonicBaseFrame434 L J m hmJ,
    ∑ x : B654ActualParityState434 L hS J positions,
    ∑ y : B654ActualParityState434 L hS J positions,
      W x.val.1.val.toNat y.val.1.val.toNat *
      parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi a x y := by
  classical
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let test := fun n np D => W (Int.toNat n) (Int.toNat np) *
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi n np D
  calc
    _ = ∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS) BP J 1 m pats,
      ∑ x : B654ActualParityState434 L hS J positions,
      ∑ y : B654ActualParityState434 L hS J positions,
        test x.val.1.val y.val.1.val
          (b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats x.val.2 frame) *
        b650IntegerFrameScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
          J 1 m pats positions (1/2 : ℝ) (SourceNativeMemorySmallMass434 20 L hS)
          (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y frame := by
      apply (parity_physical_pair_frame_sum_order434
        (fun (x y : B654ActualParityState434 L hS J positions)
          (frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS) BP J 1 m pats) =>
          W x.val.1.val.toNat y.val.1.val.toNat *
          parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k
            positions lo hi F G t1 t2 tw v psi x y frame)).trans
      apply Finset.sum_congr rfl
      intro frame _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      have ht := parity_actual_original_frame_term_factor434 L hS J m hmJ Q h xi zeta Z k
        positions lo hi F G t1 t2 tw v psi x y frame
      dsimp only at ht
      dsimp only [test]
      exact (congrArg (fun z : ℂ => W x.val.1.val.toNat y.val.1.val.toNat*z) ht).trans
        (mul_assoc _ _ _).symm
    _ = _ := by
      have hmarg := parity_complete_physical_frame_sum_permutation_marginal434
        SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats positions (1/2 : ℝ)
        (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
        Knu zeta 1 (2*k) (fun _ => test)
      apply hmarg.trans
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      change (W x.val.1.val.toNat y.val.1.val.toNat *
        parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi x.val.1.val y.val.1.val
          (b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats x.val.2
            (parityBaseIdentityFrame434 (SG:=SourceNativeMemorySG434 20 L hS) BP J 1 m pats a))) * _ = _
      exact mul_assoc _ _ _

/-- Exact weighted enumeration over both full positive fibres. Positivity
comes from the original coefficients, never from an extra cap or clean
assumption. The complete state marks and residues are unchanged. -/
theorem parity_actual_harmonic_endpoint_weight_positive434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (W : ℕ → ℕ → ℂ) :
    (∑ x : B654ActualParityState434 L hS J positions,
     ∑ y : B654ActualParityState434 L hS J positions,
     ∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ),
       W x.val.1.val.toNat y.val.1.val.toNat *
       parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi x y frame) =
    parityActualEndpointWeightedPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi W := by
  classical
  apply (parity_actual_harmonic_endpoint_weight_marginal434 L hS J m hmJ Q h xi zeta Z k
    positions lo hi F G t1 t2 tw v psi W).trans
  unfold parityActualEndpointWeightedPositiveFibreSum434
  apply Finset.sum_congr rfl
  intro a _
  have he := parity_actual_positive_pair_reindex434 L hS J positions
    (fun x y => W x.val.1.val.toNat y.val.1.val.toNat *
      parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi a x y)
    (by
      intro x y hx
      rw [parity_harmonic_base_summand_source_nonpos434 L hS J m hmJ Q h xi zeta Z k
        positions lo hi F G t1 t2 tw v psi a x y hx,mul_zero])
    (by
      intro x y hy
      rw [parity_harmonic_base_summand_target_nonpos434 L hS J m hmJ Q h xi zeta Z k
        positions lo hi F G t1 t2 tw v psi a x y hy,mul_zero])
  apply he.trans
  apply Finset.sum_congr rfl
  intro n _
  exact Finset.sum_comm

/-- Both independently inserted physical caps survive the full permutation
marginal and positive-fibre reindex as the SAME numeric endpoint factor. -/
theorem parity_actual_capped_harmonic_positive_fibres434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityActualCappedHarmonicFrameSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi =
    parityActualEndpointWeightedPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
      (parityOriginalPhysicalPairPcap434 L) := by
  classical
  calc
    _ = ∑ x : B654ActualParityState434 L hS J positions,
      ∑ y : B654ActualParityState434 L hS J positions,
      ∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ),
        parityOriginalPhysicalPairPcap434 L x.val.1.val.toNat y.val.1.val.toNat *
        parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi x y frame := by
      unfold parityActualCappedHarmonicFrameSum434
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro frame _
      simp only [parityOriginalPhysicalPairPcap434,ite_mul,one_mul,zero_mul]
    _ = _ := parity_actual_harmonic_endpoint_weight_positive434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi (parityOriginalPhysicalPairPcap434 L)

/-- The exact failure-union sum follows the SAME complete reindex with
weight 1 minus the two-endpoint cap. No absolute error estimate is assumed. -/
theorem parity_actual_physical_Pcap_loss_positive_fibres434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityActualPhysicalPcapLossFrameSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi =
    parityActualEndpointWeightedPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
      (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np) := by
  classical
  calc
    _ = ∑ x : B654ActualParityState434 L hS J positions,
      ∑ y : B654ActualParityState434 L hS J positions,
      ∑ frame : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ),
        (1-parityOriginalPhysicalPairPcap434 L x.val.1.val.toNat y.val.1.val.toNat) *
        parityActualOriginalHarmonicFrameTerm434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi x y frame := by
      unfold parityActualPhysicalPcapLossFrameSum434
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro frame _
      rw [parity_original_pair_Pcap_complement434]
      simp only [ite_mul,one_mul,zero_mul]
    _ = _ := parity_actual_harmonic_endpoint_weight_positive434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np)

/-- The new capped H_T is now joined to all actual positive physical
fibres at its original global window, without changing uncapped H_T. -/
theorem parity_capped_harmonic_physical_positive_fibres434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityCappedHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
    parityActualEndpointWeightedPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi
      (parityOriginalPhysicalPairPcap434 L) :=
  parity_actual_capped_harmonic_positive_fibres434 L hS J m hmJ Q h xi zeta Z k
    (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeCapShared -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- Exact weighted full-state to shared-quotient disintegration. A numeric
endpoint weight is evaluated on the PHYSICAL endpoints DR*w and DR*wp
at the target. The full fixed-position marks, repeated shared values,
auxiliary product, parity, cutoff and all masses are retained; the old
unweighted aggregate is not used as a substitute for this weighted proof. -/
theorem parity_actual_harmonic_endpoint_weight_quotient_slices434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) (Wgt : ℕ → ℕ → ℂ) :
    let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
    (∑ n : parityPositiveNaturalPositions434 positions,
      ∑ np : parityPositiveNaturalPositions434 positions,
      ∑ x : ParityActualPositionFibre434 L hS J n.val,
      ∑ y : ParityActualPositionFibre434 L hS J np.val,
        Wgt n.val np.val * parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
          (parityHarmonicComparisonBase434 L J m hmJ nu aux)
          (parityActualNaturalState434 L hS J positions n x)
          (parityActualNaturalState434 L hS J positions np y)) =
    ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
      ∑ w∈paritySharedQuotientPositions434 positions (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)),
      ∑ wp∈paritySharedQuotientPositions434 positions (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)),
        Wgt (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)*w)
          (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)*wp) *
        parityActualHarmonicPhysicalSlice434 L hS J m hmJ nu.val Q h xi zeta Z k lo hi F G
          t1 t2 tw v psi aux w wp (fun g i => s ⟨g,i⟩) := by
  classical
  dsimp only
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
  let P := b645ActualBand434 L hS
  let N := parityPositiveNaturalPositions434 positions
  let ss := Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => P i.1)
  let D := fun s : (g : B645ActualGroup434 L hS) × E g → ℕ =>
    sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
  let K := parityActualFullCanonicalKernel434 L hS J m hmJ nu.val Q h xi aux
  let NW := fun s : (g : B645ActualGroup434 L hS) × E g → ℕ =>
    fun n np : ℕ =>
      parityActualHarmonicNumericWeight434 L hS J m hmJ nu.val zeta Z k lo hi F G
        t1 t2 tw v psi aux n np (D s)
  let W := fun s n np => Wgt n np * NW s n np
  calc
    _ = ∑ n : N,∑ np : N,∑ s∈ss,
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n.val,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np.val,W s n.val np.val*K a b := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro np hnp
      calc
        _ = Wgt n.val np.val *
          (∑ x : ParityActualPositionFibre434 L hS J n.val,
            ∑ y : ParityActualPositionFibre434 L hS J np.val,
              parityActualHarmonicFibreTerm434 L hS J m hmJ nu.val Q h xi zeta Z k lo hi F G
                t1 t2 tw v psi aux n.val np.val x y) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          rw [parity_actual_harmonic_comparison_fibre_term434 L hS J m hmJ nu Q h xi zeta Z k
            lo hi F G t1 t2 tw v psi aux positions n np x y]
        _ = Wgt n.val np.val *
          (∑ s∈ss,∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n.val,
            ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np.val,
              NW s n.val np.val*K a b) :=
          congrArg (fun z : ℂ => Wgt n.val np.val*z)
            (parity_actual_harmonic_fixed_positions_shared434 L hS J m hmJ nu Q h xi zeta Z k
              lo hi F G t1 t2 tw v psi aux n.val np.val)
        _ = _ := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          dsimp only [W]
          ring
    _ = ∑ n∈N,∑ np∈N,∑ s∈ss,
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W s n np*K a b := by
      let B := fun n np : ℕ => ∑ s∈ss,
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W s n np*K a b
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
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W s n np*K a b :=
      parity_shared_position_sum_order434 N ss (fun s n np =>
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W s n np*K a b)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      calc
        _ = ∑ w∈paritySharedQuotientPositions434 positions (D s),
            ∑ wp∈paritySharedQuotientPositions434 positions (D s),
            ∑ a∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) w,
            ∑ b∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) wp,
              W s (D s*w) (D s*wp)*K a b :=
          parity_actual_shared_completion_pair_quotient434 L hL hS J m hmJ nu.val aux s positions
            (fun n np a b => W s n np*K a b)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro w hw
          apply Finset.sum_congr rfl
          intro wp hwp
          calc
            _ = Wgt (D s*w) (D s*wp) *
              (∑ a∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) w,
               ∑ b∈sourceB574LabelledCompletions434 P (J+1) E (fun g i => s ⟨g,i⟩) wp,
                 NW s (D s*w) (D s*wp)*K a b) := by
              simp only [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              dsimp only [W]
              ring
            _ = _ := congrArg (fun z : ℂ => Wgt (D s*w) (D s*wp)*z)
              (parity_actual_harmonic_numeric_physical_slice434 L hS J m hmJ nu Q h xi zeta Z k
                lo hi F G t1 t2 tw v psi aux w wp s)

/-- One genuine comparison aggregate with its original numeric endpoint
weight still on BOTH physical endpoints. For the literal cap weight this
retains Ppart(DR*w) and Ppart(DR*wp), not caps only at w/wp. All full B574
products, two squared dampings and two inverse cell masses are unchanged. -/
def parityActualEndpointWeightedComparisonB574434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) (Wgt : ℕ → ℕ → ℂ) : ℂ :=
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
  let c := parityActualProbeAuxD434 L J m hmJ nu.val aux
  ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
    let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
    ∑ w∈paritySharedQuotientPositions434 positions d,
    ∑ wp∈paritySharedQuotientPositions434 positions d,
      if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
        Wgt (d*w) (d*wp) * parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d c w wp *
        (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
          (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ) *
        sourceB574CanonicalPhysicalSlice434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
          Q h h xi (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu.val
            (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu.val aux))
          (1/2 : ℝ) w wp (fun g i => s ⟨g,i⟩)
      else 0

/-- The complete original comparison-base contribution with a fixed
endpoint weight equals the full B574 physical-slice aggregate. This exact
weighted reindex applies to both physical caps and their failure union;
no cleaning, endpoint replacement or quantitative premise is introduced. -/
theorem parity_actual_harmonic_endpoint_weight_B574_aggregate434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) (Wgt : ℕ → ℕ → ℂ) :
    (∑ n : parityPositiveNaturalPositions434 positions,
      ∑ np : parityPositiveNaturalPositions434 positions,
      ∑ x : ParityActualPositionFibre434 L hS J n.val,
      ∑ y : ParityActualPositionFibre434 L hS J np.val,
        Wgt n.val np.val * parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
          (parityHarmonicComparisonBase434 L J m hmJ nu aux)
          (parityActualNaturalState434 L hS J positions n x)
          (parityActualNaturalState434 L hS J positions np y)) =
    parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k positions lo hi F G
      t1 t2 tw v psi aux Wgt := by
  rw [parity_actual_harmonic_endpoint_weight_quotient_slices434 L hL hS J m hmJ nu Q h xi zeta Z k
    positions lo hi F G t1 t2 tw v psi aux Wgt]
  unfold parityActualEndpointWeightedComparisonB574434
  dsimp only
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro wp hwp
  rw [parity_actual_harmonic_B574_quotient_slice434 L hS J m hmJ nu Q h xi zeta Z k lo hi F G
    t1 t2 tw v psi aux (fun g i => s ⟨g,i⟩) positions ⟨w,hw⟩ ⟨wp,hwp⟩]
  split_ifs
  · ring
  · simp only [mul_zero]
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeCapAggregate -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 26000

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- Literal RAW branch with a fixed physical endpoint weight, retaining
the genuine none-index kernel 1 and the full original positive fibres. -/
def parityActualEndpointWeightedRawPositiveFibreSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (Wgt : ℕ → ℕ → ℂ) : ℂ :=
  ∑ n : parityPositiveNaturalPositions434 positions,
  ∑ np : parityPositiveNaturalPositions434 positions,
  ∑ x : ParityActualPositionFibre434 L hS J n.val,
  ∑ y : ParityActualPositionFibre434 L hS J np.val,
    Wgt n.val np.val * parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi (parityHarmonicRawBase434 L J m hmJ)
      (parityActualNaturalState434 L hS J positions n x)
      (parityActualNaturalState434 L hS J positions np y)

/-- The complete weighted positive-fibre sum separates into the genuine
RAW branch and every original comparison probe and auxiliary draw. Each
comparison is reindexed to its full shared physical B574 slice aggregate. -/
theorem parity_actual_endpoint_weight_positive_B574_split434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (Wgt : ℕ → ℕ → ℂ) :
    parityActualEndpointWeightedPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi Wgt =
    parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi Wgt +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k positions lo hi F G
          t1 t2 tw v psi aux Wgt := by
  classical
  let I : Type := ↥(sourceOriginalTwoBlockProbePatterns434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
  let R := parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
    positions lo hi F G t1 t2 tw v psi Wgt
  let C : (nu : I) → ParityActualProbeAux434 L J m hmJ nu.val → ℂ := fun nu aux =>
    ∑ n : parityPositiveNaturalPositions434 positions,
    ∑ np : parityPositiveNaturalPositions434 positions,
    ∑ x : ParityActualPositionFibre434 L hS J n.val,
    ∑ y : ParityActualPositionFibre434 L hS J np.val,
      Wgt n.val np.val * parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
        ⟨some nu,aux⟩ (parityActualNaturalState434 L hS J positions n x)
        (parityActualNaturalState434 L hS J positions np y)
  let B : (nu : I) → ParityActualProbeAux434 L J m hmJ nu.val → ℂ := fun nu aux =>
    parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k positions lo hi F G
      t1 t2 tw v psi aux Wgt
  have hc (nu : I) (aux : ParityActualProbeAux434 L J m hmJ nu.val) : C nu aux=B nu aux := by
    exact parity_actual_harmonic_endpoint_weight_B574_aggregate434 L hL hS J m hmJ nu Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi aux Wgt
  have hsum : (∑ nu : I,∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,C nu aux) =
      ∑ nu : I,∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,B nu aux :=
    Finset.sum_congr rfl (fun nu _ => Finset.sum_congr rfl (fun aux _ => hc nu aux))
  have hraw :
      parityActualEndpointWeightedPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
        positions lo hi F G t1 t2 tw v psi Wgt = R +
      ∑ nu : I,∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,C nu aux :=
    parity_harmonic_base_sum_raw_split434 L J m hmJ (fun a =>
      ∑ n : parityPositiveNaturalPositions434 positions,
      ∑ np : parityPositiveNaturalPositions434 positions,
      ∑ x : ParityActualPositionFibre434 L hS J n.val,
      ∑ y : ParityActualPositionFibre434 L hS J np.val,
        Wgt n.val np.val *
        parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k
          positions lo hi F G t1 t2 tw v psi a
          (parityActualNaturalState434 L hS J positions n x)
          (parityActualNaturalState434 L hS J positions np y))
  exact hraw.trans (congrArg (fun z : ℂ => R+z) hsum)

/-- Complete original capped H_T equals its literal capped RAW branch
plus ALL comparison/auxiliary/shared B574 physical slices. The cap on
BOTH endpoints is still evaluated at DR*w and DR*wp within the shared
sum; it is not replaced by a cap at the stripped endpoint. -/
theorem parity_capped_harmonic_physical_B574_aggregate434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityCappedHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
    parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi (parityOriginalPhysicalPairPcap434 L) +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k
          (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi aux (parityOriginalPhysicalPairPcap434 L) := by
  exact (parity_capped_harmonic_physical_positive_fibres434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi).trans
    (parity_actual_endpoint_weight_positive_B574_split434 L hL hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi (parityOriginalPhysicalPairPcap434 L))

/-- The exact cap insertion error has the SAME full physical disintegration.
The union of physical cap failures remains inside each complete shared
slice. This gives the true weighted error construction, not a conditional
bound or an equality with a substituted comparison kernel. -/
theorem parity_harmonic_physical_cap_loss_B574_aggregate434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi -
      parityCappedHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
    parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np) +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k
          (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi aux (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np) := by
  exact (parity_harmonic_physical_cap_difference434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi).trans
    ((parity_actual_physical_Pcap_loss_positive_fibres434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi).trans
      (parity_actual_endpoint_weight_positive_B574_split434 L hL hS J m hmJ Q h xi zeta Z k
        (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np)))

/-- Capped H_T with exactly ONE external Z. -/
theorem parity_capped_harmonic_physical_outer_Z_B574434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    (Z : ℂ)*parityCappedHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
    (Z : ℂ)*parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi (parityOriginalPhysicalPairPcap434 L) +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        (Z : ℂ)*parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k
          (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi aux (parityOriginalPhysicalPairPcap434 L) := by
  have he := parity_capped_harmonic_physical_B574_aggregate434 L hL hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi
  simpa only [mul_add,Finset.mul_sum] using congrArg (fun z : ℂ => (Z : ℂ)*z) he

/-- The literal cap insertion error with exactly ONE external Z. -/
theorem parity_harmonic_physical_cap_loss_outer_Z_B574434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    (Z : ℂ)*(parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi -
      parityCappedHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi) =
    (Z : ℂ)*parityActualEndpointWeightedRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np) +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        (Z : ℂ)*parityActualEndpointWeightedComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k
          (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi aux (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np) := by
  have he := parity_harmonic_physical_cap_loss_B574_aggregate434 L hL hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi
  simpa only [mul_add,Finset.mul_sum] using congrArg (fun z : ℂ => (Z : ℂ)*z) he
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeNorm -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare

/-- Exact norm of the actual stripped arithmetic multiplier. Both endpoint
cores have arguments w and wp alone. The auxiliary product occurs only in
the original cutoff and a unit Mellin phase; no shared variable remains.
This equality assumes no core bound and inserts no physical Ppart gate. -/
theorem parity_harmonic_stripped_arithmetic_norm434
    (L zeta Z : ℝ) (F G : PrimeSlotCore) (t1 t2 : ℝ)
    (tw : Bool) (psi : ℝ → ℂ) (c w wp : ℕ) (hw : 0<w) (hwp : 0<wp) :
    ‖parityHarmonicStrippedArithmetic434 L zeta Z F G t1 t2 tw psi c w wp‖=
      (w : ℝ)⁻¹ * ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F w‖ *
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G wp‖ *
      ‖psi ((w : ℝ)/(Z*(c : ℝ)))‖ := by
  have hsign (n : ℕ) : ‖(groupSign (sourceOriginalPAllActualBands 20 L) tw n : ℂ)‖=1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    cases tw <;> simp [groupSign,abs_pow]
  unfold parityHarmonicStrippedArithmetic434 parityHarmonicSourceArithmetic434 parityHarmonicEndpointArithmetic434
  simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one,norm_mul,norm_star,
    norm_inv,Complex.norm_natCast,hsign,b656_imaginary_power_norm434 w hw t1,
    b656_imaginary_power_norm434 wp hwp t2,source_original_pure_mellin_phase_norm_one434,
    one_mul,mul_one]
  ring
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeActualCore -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare

/-- Both genuine B633 Parity endpoint cores have the full tau(n)^2 bound
at EVERY positive natural n, uniformly in the original moving Q data,
actual fine prime/rough alpha, sorted residual, character and frequencies.
The unit coefficient/residual facts are proved by the actual B656 input
theorem and used with D=1,A=C=1. There is no arbitrary norm hypothesis,
no n<=exp(2L) restriction, and P is the full actual r20 original family. -/
theorem parity_eventually_actual_B633_core_tau434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l : ℝ) →
      ∀ (r d : ℕ), 1≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let H := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ n : ℕ, 0<n →
          ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) E n‖≤(n.divisors.card : ℝ)^2 ∧
          ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) H n‖≤(n.divisors.card : ℝ)^2 := by
  filter_upwards [b656_actual_fine_native_and_parity_inputs434 S beta gamma hS hbeta hgamma]
    with L hInput
  refine ⟨hInput.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma
  intro n hn
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let H := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have hh := (hInput.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1).2 xi1 xi2 rho sigma
  have he : B656UnitRoughPrimeCore434 L E := hh.1
  have hg : B656UnitRoughPrimeCore434 L H := hh.2
  constructor
  · simpa only [one_mul,Nat.div_one] using
      b656_prime_core_removed_marks_bound434 (sourceOriginalPAllActualBands 20 L) E
        1 1 zero_le_one zero_le_one he.1 he.2.1 n 1 hn.ne' (by norm_num) (one_dvd n) (by simp)
  · simpa only [one_mul,Nat.div_one] using
      b656_prime_core_removed_marks_bound434 (sourceOriginalPAllActualBands 20 L) H
        1 1 zero_le_one zero_le_one hg.1 hg.2.1 n 1 hn.ne' (by norm_num) (one_dvd n) (by simp)

/-- The actual source scalar has the precise two-endpoint tau-square
harmonic envelope required by weighted restoration. Both bounds and
all unit phase/parity factors are conclusions. The original cutoff is
retained at w/(Z*DC), and its norm is not replaced by a surrogate. -/
theorem parity_eventually_actual_B633_stripped_tau434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l : ℝ) →
      ∀ (r d : ℕ), 1≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let H := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (xi3 Z : ℝ) (tw : Bool) (psi : ℝ → ℂ) (c w wp : ℕ), 0<w → 0<wp →
          ‖parityHarmonicStrippedArithmetic434 L (-xi3) Z E H
            (-(rho+xi3)) (-rho) tw psi c w wp‖≤
            (w : ℝ)⁻¹*(w.divisors.card : ℝ)^2*(wp.divisors.card : ℝ)^2*
              ‖psi ((w : ℝ)/(Z*(c : ℝ)))‖ := by
  filter_upwards [parity_eventually_actual_B633_core_tau434 S beta gamma hS hbeta hgamma]
    with L hCore
  refine ⟨hCore.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma
  intro xi3 Z tw psi c w wp hw hwp
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let H := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have hAll := hCore.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
  have he := (hAll w hw).1
  have hg := (hAll wp hwp).2
  have hPair : ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) E w‖*
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) H wp‖≤
      (w.divisors.card : ℝ)^2*(wp.divisors.card : ℝ)^2 :=
    mul_le_mul he hg (norm_nonneg _) (sq_nonneg _)
  rw [parity_harmonic_stripped_arithmetic_norm434 L (-xi3) Z E H
    (-(rho+xi3)) (-rho) tw psi c w wp hw hwp]
  calc
    _ = (w : ℝ)⁻¹*(‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) E w‖*
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) H wp‖)*
        ‖psi ((w : ℝ)/(Z*(c : ℝ)))‖ := by ring
    _ ≤ (w : ℝ)⁻¹*((w.divisors.card : ℝ)^2*(wp.divisors.card : ℝ)^2)*
        ‖psi ((w : ℝ)/(Z*(c : ℝ)))‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPair (by positivity)) (norm_nonneg _)
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeSeed -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Every original typed auxiliary draw has positive repeated product.
No conditioning or removal of duplicate draws is used. -/
theorem parity_actual_probe_aux_positive434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    0<parityActualProbeAuxD434 L J m hmJ nu aux := by
  exact parity_frame_aux_D_pos434 (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu)
    (parityActualProbeIdentityFrame434 L hS J m hmJ nu aux)

/-- A nonzero literal B574 physical slice has both genuine complete
physical mark carriers. This uses the original definition and does not
assume that a shared assignment is clean. -/
theorem parity_B574_physical_slice_completion_support434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J ell m hmJ nu g → ℕ)
    (hnz : sourceB574CanonicalPhysicalSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp s≠0) :
    (sourceB574LabelledCompletions434 P (J+ell)
      (sourceOriginalProbeSharedSlots434 J ell m hmJ nu) s w).Nonempty ∧
    (sourceB574LabelledCompletions434 P (J+ell)
      (sourceOriginalProbeSharedSlots434 J ell m hmJ nu) s wp).Nonempty := by
  constructor
  · by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hnz
    unfold sourceB574CanonicalPhysicalSlice434
    dsimp only
    rw [he]
    simp only [Finset.sum_empty,mul_zero]
  · by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    apply hnz
    unfold sourceB574CanonicalPhysicalSlice434
    dsimp only
    simp only [he,Finset.sum_empty,Finset.sum_const_zero,mul_zero]

/-- Any actual complete B574 marking reconstructs an original native
physical state with the SAME full DR*DC. Its already proved physical
frame bound therefore applies even to unrestricted shared arrays. -/
theorem parity_actual_completion_full_divisor_window434
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
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s w).Nonempty) :
    ((sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s *
      parityActualProbeAuxD434 L J m hmJ nu aux : ℕ) : ℝ)≤
      (b651ParityWindowSize434 J 0 L : ℝ) := by
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
  have hwindow := b660_actual_parity_frame_D_window434 L hL hS J m 0 (by norm_num)
    (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu) x.val
    (parityActualProbeIdentityFrame434 L hS J m hmJ nu aux)
  rw [hD] at hwindow
  exact hwindow

/-- The original fixed positive seed is automatic on a nonzero cutoff
and a genuine complete physical marking. The prior framewise tail bound
is used at the actual DR*DC; no shared-independent window is assumed. -/
theorem parity_eventually_actual_completion_seed434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J)
      (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (aux : ParityActualProbeAux434 L J m hmJ nu)
      (s : ∀ g : B645ActualGroup434 L hS,
        sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ),
      (∀ g i,s g i∈b645ActualBand434 L hS g) →
    ∀ (Z : ℝ), 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u,psi u≠0 → (1/64:ℝ)≤u ∧ u≤64) →
    ∀ (w : ℕ), 0<w →
      (sourceB574LabelledCompletions434 (b645ActualBand434 L hS) (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s w).Nonempty →
      psi ((w : ℝ)/(Z*(parityActualProbeAuxD434 L J m hmJ nu aux : ℝ)))≠0 →
      (((sourceB574SharedDilation434 (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s*w : ℕ) : ℤ))∈
        b654ParitySeedPositions434 1 (parityDyadicLimit434 L) := by
  filter_upwards [parity_eventually_dyadic_outer_envelope434 J 0 CZ (by norm_num)] with L hEnv
  refine ⟨hEnv.1,?_⟩
  intro hS m hmJ nu aux s hs Z hZ hZhi psi hSupp w hw hcomp hpsi
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  have hL1 : 1<L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hEnv.1
  have hd := (parity_actual_labelled_shared_support434 L hL1 hS (J+1) E s hs).1
  have hc : 0<c := parity_actual_probe_aux_positive434 L hS J m hmJ nu aux
  have hdc : (0 : ℝ)<(d*c : ℕ) := by exact_mod_cast Nat.mul_pos hd hc
  have hcut : psi (((d*w : ℕ) : ℝ)/(Z*((d*c : ℕ) : ℝ)))≠0 := by
    rw [parity_harmonic_cutoff_shared_cancel434 d c w hd.ne' Z]
    exact hpsi
  have hnhi : ((d*w : ℕ) : ℝ)≤64*(Z*((d*c : ℕ) : ℝ)) :=
    (div_le_iff₀ (mul_pos hZ hdc)).mp (hSupp _ hcut).2
  have hwindow : ((d*c : ℕ) : ℝ)≤(b651ParityWindowSize434 J 0 L : ℝ) :=
    parity_actual_completion_full_divisor_window434 L hEnv.1 hS J m hmJ nu aux s w hcomp
  have hLp : 0<L := by linarith
  have hnend : ((d*w : ℕ) : ℝ)<(parityDyadicLimit434 L : ℝ) := by
    calc
      _ ≤ 64*(Z*((d*c : ℕ) : ℝ)) := hnhi
      _ ≤ 64*((Real.exp L*L^CZ)*(b651ParityWindowSize434 J 0 L : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hZhi hwindow hdc.le
            (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hLp.le _))) (by norm_num)
      _ = 64*Real.exp L*L^CZ*(b651ParityWindowSize434 J 0 L : ℝ) := by ring
      _ < Real.exp (2*L) := hEnv.2
      _ < (parityDyadicLimit434 L : ℝ) := parity_dyadic_limit_exp434 L hLp
  apply Finset.mem_image.mpr
  refine ⟨d*w,Finset.mem_Ico.mpr ⟨Nat.mul_pos hd hw,?_⟩,rfl⟩
  exact_mod_cast hnend


/-- On the actual physical slice the finite source seed is now removed
exactly. Together with the proved actual core/parity/phase identities this
makes the complete arithmetic multiplier independent of every shared
assignment. No clean event and no restoration estimate is assumed. -/
theorem parity_eventually_actual_shared_scalar_slice434 (J : ℕ) (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1≤L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (hmJ : m≤J)
      (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (aux : ParityActualProbeAux434 L J m hmJ nu)
      (s : ∀ g : B645ActualGroup434 L hS,
        sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ),
      (∀ g i,s g i∈b645ActualBand434 L hS g) →
    ∀ (Q : ℕ) (h xi rho xi3 Z : ℝ), 0<Z → Z≤Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u,psi u≠0 → (1/64:ℝ)≤u ∧ u≤64) →
    ∀ (F G : PrimeSlotCore) (tw : Bool) (w wp : ℕ), 0<w → 0<wp →
      let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
      let d := sourceB574SharedDilation434 (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ fullnu) s
      let c := parityActualProbeAuxD434 L J m hmJ nu aux
      let B := sourceB574CanonicalPhysicalSlice434 J 1 m hmJ fullnu Q h h xi
        (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
        (1/2 : ℝ) w wp s
      parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
          (-(rho+xi3)) (-rho) tw 0 psi d c w wp*B=
        parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
          (-(rho+xi3)) (-rho) tw psi c w wp*B := by
  filter_upwards [parity_eventually_actual_completion_seed434 J CZ] with L hSeed
  refine ⟨hSeed.1,?_⟩
  intro hS m hmJ nu aux s hs Q h xi rho xi3 Z hZ hZhi psi hSupp F G tw w wp hw hwp
  dsimp only
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ fullnu
  let d := sourceB574SharedDilation434 (J+1) E s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let B := sourceB574CanonicalPhysicalSlice434 J 1 m hmJ fullnu Q h h xi
    (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
    (1/2 : ℝ) w wp s
  change parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
    (-(rho+xi3)) (-rho) tw 0 psi d c w wp*B=
    parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp*B
  by_cases hB : B=0
  · rw [hB,mul_zero,mul_zero]
  by_cases hpsi : psi ((w : ℝ)/(Z*(c : ℝ)))=0
  · have hleft : parityHarmonicSharedArithmetic434 L (-xi3) Z 1 (parityDyadicLimit434 L) F G
        (-(rho+xi3)) (-rho) tw 0 psi d c w wp=0 := by
      unfold parityHarmonicSharedArithmetic434
      split_ifs <;> simp only [hpsi,mul_zero,zero_mul]
    have hright : parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi c w wp=0 := by
      unfold parityHarmonicStrippedArithmetic434
      simp only [hpsi,mul_zero,zero_mul]
    rw [hleft,hright]
  have hcomp := (parity_B574_physical_slice_completion_support434 J 1 m hmJ fullnu
    Q h h xi (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
    (1/2 : ℝ) w wp s hB).1
  have hseed := hSeed.2 hS m hmJ nu aux s hs Z hZ hZhi psi hSupp w hw hcomp hpsi
  have hL1 : 1<L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<1)).trans_le hSeed.1
  have hstrip := parity_actual_labelled_shared_arithmetic434 L hL1 hS (J+1) E s hs
    rho xi3 Z 1 (parityDyadicLimit434 L) F G tw psi c w wp
    (parity_actual_probe_aux_positive434 L hS J m hmJ nu aux) hw hwp
  dsimp only at hstrip
  rw [hstrip,if_pos hseed]
end Green64Analytic.Parity

end

end

