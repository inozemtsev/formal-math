module

public import Green64.Library.Weights.Part111
public import Green64.Library.Correlation.Part070
public import Green64.Library.Weights.SharedRestorationSaving
public import Green64.Library.Weights.Part019

@[expose] public section

/-!
# Correlation / Part071

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PhysicalSharedFreeHarmonic -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- Reordering the three finite original indices retains every physical
 source, target and complete primitive frame exactly once. -/
theorem parity_physical_pair_frame_sum_order434
    {X Y A : Type} [Fintype X] [Fintype Y] [Fintype A]
    (F : X → Y → A → ℂ) :
    (∑ x,∑ y,∑ a,F x y a) = ∑ a,∑ x,∑ y,F x y a := by
  calc
    _ = ∑ x,∑ a,∑ y,F x y a := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The literal position/divisor factor from the already defined original
 harmonic frame sum. Both endpoint cores (including their original P gates),
 source and target phases, c1's harmonic factor, same P parity, single mu0 and
 frame-dependent original cutoff are retained. There is no auxiliary argument. -/
def parityActualHarmonicPositionTest434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (n np : ℤ) (D : ℕ) : ℂ :=
  if n ∈ b654ParitySeedPositions434 lo hi then
    (b657ActualStateMass434 L hS J : ℂ) *
    star (b659ActualParityRootCoefficient434 L hS J F t1 tw 1 Z v n) *
    psi ((n : ℝ)/(Z*(D : ℝ))) *
    (groupSign (sourceOriginalPAllActualBands 20 L) tw np.toNat : ℂ) *
    b656IntegerPrimeEndpointCoefficient434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
      (sourceOriginalPAllActualBands 20 L) G (1/2 : ℝ) t2 np
  else 0

/-- Original RAW and actual two-block comparison base frames after the
 proved four-permutation marginal. All nu and independent auxiliary draws
 remain, with their original scalar, guards and probabilities. -/
def parityActualHarmonicPermutationSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  ∑ a : (nu : SourceOriginalMemoryRawComparisonIndex434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m) ×
      SourceBigAux BP J m (pats nu),
    ∑ x : B654ActualParityState434 L hS J positions,
    ∑ y : B654ActualParityState434 L hS J positions,
      parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi x.val.1.val y.val.1.val
        (b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats x.val.2
          (parityBaseIdentityFrame434 (SG:=SourceNativeMemorySG434 20 L hS) BP J 1 m pats a)) *
      parityPermutationMarginalScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
        J 1 m pats positions (1/2 : ℝ) (SourceNativeMemorySmallMass434 20 L hS)
        (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y a

/-- Equality of the ORIGINAL harmonic frame sum with its actual complete
 permutation marginal. This is a theorem about the existing source functional;
 it does not redefine H_T or its original endpoint tests. -/
theorem parity_actual_harmonic_frames_permutation_marginal434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityActualHarmonicFrameSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi =
      parityActualHarmonicPermutationSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi := by
  classical
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let test := parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi
  calc
    _ = ∑ f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS) BP J 1 m pats,
      ∑ x : B654ActualParityState434 L hS J positions,
      ∑ y : B654ActualParityState434 L hS J positions,
        test x.val.1.val y.val.1.val
          (b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats x.val.2 f) *
        b650IntegerFrameScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
          J 1 m pats positions (1/2 : ℝ) (SourceNativeMemorySmallMass434 20 L hS)
          (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y f := by
      unfold parityActualHarmonicFrameSum434
      dsimp only
      rw [parity_physical_pair_frame_sum_order434]
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      dsimp only [test,parityActualHarmonicPositionTest434]
      by_cases hs : x.val.1.val ∈ b654ParitySeedPositions434 lo hi
      · simp only [hs,ite_true]
        ring
      · simp only [hs,ite_false,zero_mul]
    _ = _ := parity_complete_physical_frame_sum_permutation_marginal434
      SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats positions (1/2 : ℝ)
      (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
      Knu zeta 1 (2*k) (fun _ => test)

/-- Exact H_T-to-permutation-marginal join for the unchanged independently
 defined controlled functional, at every cutoff T. -/
theorem parity_harmonic_physical_permutation_marginal434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
      parityActualHarmonicPermutationSum434 L hS J m hmJ Q h xi zeta Z k
        (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi := by
  rw [parity_controlled_harmonic_eq_frames434,parity_actual_harmonic_frames_permutation_marginal434]

/-- Positivity of the source position is enforced by its ORIGINAL endpoint
 coefficient. It is not an added support or clean-event hypothesis. -/
theorem parity_harmonic_position_test_source_nonpos434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (n np : ℤ) (D : ℕ) (hn : n≤0) :
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi n np D = 0 := by
  unfold parityActualHarmonicPositionTest434 b659ActualParityRootCoefficient434
  simp [b656IntegerPrimeEndpointCoefficient434,not_lt.mpr hn]

/-- The original target prime coefficient similarly eliminates every
 nonpositive target before any natural-position or shared quotient reindex. -/
theorem parity_harmonic_position_test_target_nonpos434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (n np : ℤ) (D : ℕ) (hnp : np≤0) :
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi n np D = 0 := by
  unfold parityActualHarmonicPositionTest434
  simp [b656IntegerPrimeEndpointCoefficient434,not_lt.mpr hnp]


/-- Positive natural positions present in the ORIGINAL signed carrier. -/
def parityPositiveNaturalPositions434 (positions : Finset ℤ) : Finset ℕ :=
  (positions.filter (fun n => 0<n)).image Int.toNat

theorem parity_positive_natural_positions_mem434 (positions : Finset ℤ) (n : ℕ) :
    n ∈ parityPositiveNaturalPositions434 positions ↔ 0<n ∧ (n : ℤ)∈positions := by
  classical
  constructor
  · intro hn
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hn
    obtain ⟨hz,hpos⟩ := Finset.mem_filter.mp hz
    subst n
    refine ⟨by omega,?_⟩
    simpa only [Int.toNat_of_nonneg hpos.le] using hz
  · rintro ⟨hn,hmem⟩
    refine Finset.mem_image.mpr ⟨(n : ℤ),Finset.mem_filter.mpr ⟨hmem,?_⟩,?_⟩
    · exact_mod_cast hn
    · simp

/-- Embed the SAME complete residue state at a positive natural position
 back into the original signed carrier; marks and residues are unchanged. -/
def parityActualNaturalState434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (n : parityPositiveNaturalPositions434 positions)
    (x : ParityActualPositionFibre434 L hS J n.val) : B654ActualParityState434 L hS J positions :=
  ⟨(⟨(n.val : ℤ),(parity_positive_natural_positions_mem434 positions n.val).mp n.property |>.2⟩,
    x.val),x.property⟩

/-- The entire positive physical carrier is exactly the sigma of positive
 original positions and their FULL residue fibres, with no cardinality weight. -/
def parityActualPositivePositionFibreEquiv434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) :
    {x : B654ActualParityState434 L hS J positions // 0<x.val.1.val} ≃
      (n : parityPositiveNaturalPositions434 positions) × ParityActualPositionFibre434 L hS J n.val where
  toFun x := ⟨⟨x.val.val.1.val.toNat,Finset.mem_image.mpr
      ⟨x.val.val.1.val,Finset.mem_filter.mpr ⟨x.val.val.1.property,x.property⟩,rfl⟩⟩,
    ⟨x.val.val.2,by simpa only [Int.toNat_of_nonneg x.property.le] using x.val.property⟩⟩
  invFun nx := ⟨parityActualNaturalState434 L hS J positions nx.1 nx.2,by
    change 0<(nx.1.val : ℤ)
    exact_mod_cast ((parity_positive_natural_positions_mem434 positions nx.1.val).mp nx.1.property).1⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Int.toNat_of_nonneg x.property.le
    · rfl
  right_inv nx := by
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl

/-- Exact finite weighted reindex for a literal source-supported summand.
 The only vanishing condition is algebraic and is discharged below by the
 ORIGINAL endpoint coefficients, never by a clean restoration assumption. -/
theorem parity_actual_positive_position_sum_reindex434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ)
    (F : B654ActualParityState434 L hS J positions → ℂ)
    (hF : ∀ x,x.val.1.val≤0 → F x=0) :
    (∑ x,F x) =
      ∑ n : parityPositiveNaturalPositions434 positions,
      ∑ x : ParityActualPositionFibre434 L hS J n.val,F (parityActualNaturalState434 L hS J positions n x) := by
  classical
  let e := parityActualPositivePositionFibreEquiv434 L hS J positions
  have hz : (∑ x : {x : B654ActualParityState434 L hS J positions // ¬0<x.val.1.val},F x.val)=0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact hF x.val (le_of_not_gt x.property)
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun x : B654ActualParityState434 L hS J positions => 0<x.val.1.val) F
  rw [hz,add_zero] at hs
  calc
    _ = ∑ x : {x : B654ActualParityState434 L hS J positions // 0<x.val.1.val},F x.val := hs.symm
    _ = ∑ nx : (n : parityPositiveNaturalPositions434 positions) × ParityActualPositionFibre434 L hS J n.val,
        F (parityActualNaturalState434 L hS J positions nx.1 nx.2) := by
      apply Fintype.sum_equiv e
      intro x
      change F x.val = F (e.symm (e x)).val
      rw [Equiv.symm_apply_apply]
    _ = _ := Fintype.sum_sigma _

/-- Complete two-endpoint positive position/fibre enumeration, retaining
 the full coupled scalar and its original signed-carrier reconstructions. -/
theorem parity_actual_positive_pair_reindex434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ)
    (F : B654ActualParityState434 L hS J positions → B654ActualParityState434 L hS J positions → ℂ)
    (hF : ∀ x y,x.val.1.val≤0 → F x y=0)
    (hG : ∀ x y,y.val.1.val≤0 → F x y=0) :
    (∑ x,∑ y,F x y) =
      ∑ n : parityPositiveNaturalPositions434 positions,
      ∑ x : ParityActualPositionFibre434 L hS J n.val,
      ∑ np : parityPositiveNaturalPositions434 positions,
      ∑ y : ParityActualPositionFibre434 L hS J np.val,
        F (parityActualNaturalState434 L hS J positions n x) (parityActualNaturalState434 L hS J positions np y) := by
  classical
  calc
    _ = ∑ n : parityPositiveNaturalPositions434 positions,
        ∑ x : ParityActualPositionFibre434 L hS J n.val,
        ∑ y : B654ActualParityState434 L hS J positions,
          F (parityActualNaturalState434 L hS J positions n x) y := by
      apply parity_actual_positive_position_sum_reindex434
      intro x hx
      exact Finset.sum_eq_zero (fun y _ => hF x y hx)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro x _
      exact parity_actual_positive_position_sum_reindex434 L hS J positions
        (F (parityActualNaturalState434 L hS J positions n x))
        (fun y hy => hG _ y hy)



abbrev ParityHarmonicBaseFrame434 (L : ℝ) (J m : ℕ) (hmJ : m ≤ J) :=
  (nu : SourceOriginalMemoryRawComparisonIndex434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m) ×
    SourceBigAux (SourceNativeMemoryBP434 20 L) J m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ nu)

/-- One literal original base-frame summand, with all RAW/comparison and
 auxiliary information explicit and the native complete scalar unchanged. -/
def parityHarmonicBaseSummand434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (a : ParityHarmonicBaseFrame434 L J m hmJ)
    (x y : B654ActualParityState434 L hS J positions) : ℂ :=
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi x.val.1.val y.val.1.val
    (b650NativeFrameD434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 m pats x.val.2
      (parityBaseIdentityFrame434 (SG:=SourceNativeMemorySG434 20 L hS) BP J 1 m pats a)) *
  parityPermutationMarginalScalar434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats positions (1/2 : ℝ) (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta 1 (2*k) x y a

theorem parity_harmonic_base_summand_source_nonpos434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (a : ParityHarmonicBaseFrame434 L J m hmJ)
    (x y : B654ActualParityState434 L hS J positions) (hx : x.val.1.val≤0) :
    parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi a x y=0 := by
  unfold parityHarmonicBaseSummand434
  dsimp only
  rw [parity_harmonic_position_test_source_nonpos434 L hS J Z lo hi F G t1 t2 tw v psi
    x.val.1.val y.val.1.val _ hx,zero_mul]

theorem parity_harmonic_base_summand_target_nonpos434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (a : ParityHarmonicBaseFrame434 L J m hmJ)
    (x y : B654ActualParityState434 L hS J positions) (hy : y.val.1.val≤0) :
    parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi a x y=0 := by
  unfold parityHarmonicBaseSummand434
  dsimp only
  rw [parity_harmonic_position_test_target_nonpos434 L hS J Z lo hi F G t1 t2 tw v psi
    x.val.1.val y.val.1.val _ hy,zero_mul]

/-- Literal positive-position/full-residue-fibre enumeration of all actual
 base-frame summands. Source and target integers are still independent outer
 indices; no quotient shift or B574 restoration has been assumed. -/
def parityActualHarmonicPositiveFibreSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  ∑ a : ParityHarmonicBaseFrame434 L J m hmJ,
    ∑ n : parityPositiveNaturalPositions434 positions,
    ∑ np : parityPositiveNaturalPositions434 positions,
    ∑ x : ParityActualPositionFibre434 L hS J n.val,
    ∑ y : ParityActualPositionFibre434 L hS J np.val,
      parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi a
        (parityActualNaturalState434 L hS J positions n x) (parityActualNaturalState434 L hS J positions np y)

/-- Exact actual harmonic enumeration over the complete positive physical
 fibres. Both positivity restrictions are derived from the original arithmetic
 coefficients; all original P gates, phases, masses and frame data survive. -/
theorem parity_actual_harmonic_positive_fibres434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityActualHarmonicPermutationSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi =
    parityActualHarmonicPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi := by
  classical
  change (∑ a : ParityHarmonicBaseFrame434 L J m hmJ,
    ∑ x : B654ActualParityState434 L hS J positions,
    ∑ y : B654ActualParityState434 L hS J positions,
      parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi a x y) = _
  unfold parityActualHarmonicPositiveFibreSum434
  apply Finset.sum_congr rfl
  intro a _
  have he := parity_actual_positive_pair_reindex434 L hS J positions
    (parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi a)
    (fun x y hx => parity_harmonic_base_summand_source_nonpos434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi a x y hx)
    (fun x y hy => parity_harmonic_base_summand_target_nonpos434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi a x y hy)
  apply he.trans
  apply Finset.sum_congr rfl
  intro n _
  exact Finset.sum_comm

/-- The independently defined ORIGINAL H_T equals the complete literal
 positive physical-fibre sum. This joins the actual harmonic functional to
 the physical carrier used by the proved B574 fixed-shared slice theorem. -/
theorem parity_harmonic_physical_positive_fibres434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
    parityActualHarmonicPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi := by
  rw [parity_harmonic_physical_permutation_marginal434,parity_actual_harmonic_positive_fibres434]


end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeQuotient -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The exact finite original positive-position carrier after dividing
 a genuine shared divisor. Divisibility is enforced before taking the image. -/
def paritySharedQuotientPositions434 (positions : Finset ℤ) (d : ℕ) : Finset ℕ :=
  ((parityPositiveNaturalPositions434 positions).filter (fun n => d∣n)).image (fun n => n/d)

/-- Exact quotient/multiplication bijection on the original finite divisible
 carrier. It even handles d=0 correctly: positivity makes both carriers empty. -/
def paritySharedQuotientPositionEquiv434 (positions : Finset ℤ) (d : ℕ) :
    (↑((parityPositiveNaturalPositions434 positions).filter (fun n => d∣n))) ≃
      (↑(paritySharedQuotientPositions434 positions d)) where
  toFun n := ⟨n.val/d,Finset.mem_image.mpr ⟨n.val,n.property,rfl⟩⟩
  invFun w := ⟨d*w.val,by
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp w.property
    rw [← he,Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]
    exact hn⟩
  left_inv n := by
    apply Subtype.ext
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp n.property).2
  right_inv w := by
    apply Subtype.ext
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp w.property
    change d*w.val/d=w.val
    rw [← he,Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

/-- Multiplication returns the SAME original positive physical integer. -/
theorem parity_shared_quotient_mul_mem434 (positions : Finset ℤ) (d : ℕ)
    (w : paritySharedQuotientPositions434 positions d) :
    d*w.val∈parityPositiveNaturalPositions434 positions :=
  (Finset.mem_filter.mp ((paritySharedQuotientPositionEquiv434 positions d).symm w).property).1

/-- Every actual quotient carrier point has positive d and positive w.
 These facts are derived from the original positive integer support. -/
theorem parity_shared_quotient_positive434 (positions : Finset ℤ) (d : ℕ)
    (w : paritySharedQuotientPositions434 positions d) : 0<d ∧ 0<w.val := by
  have hp := ((parity_positive_natural_positions_mem434 positions (d*w.val)).mp
    (parity_shared_quotient_mul_mem434 positions d w)).1
  constructor
  · by_contra h
    have hz : d=0 := by omega
    simpa only [hz,zero_mul,lt_self_iff_false] using hp
  · by_contra h
    have hz : w.val=0 := by omega
    simpa only [hz,mul_zero,lt_self_iff_false] using hp

/-- A literal finite summand supported on genuine divisible positions is
 reindexed by the proved quotient bijection with no counting factor. -/
theorem parity_shared_quotient_weighted_sum434 (positions : Finset ℤ) (d : ℕ)
    (F : ℕ → ℂ)
    (hF : ∀ n∈parityPositiveNaturalPositions434 positions,¬d∣n → F n=0) :
    (∑ n∈parityPositiveNaturalPositions434 positions,F n) =
      ∑ w∈paritySharedQuotientPositions434 positions d,F (d*w) := by
  classical
  have hfilter : (∑ n∈parityPositiveNaturalPositions434 positions,F n) =
      ∑ n∈(parityPositiveNaturalPositions434 positions).filter (fun n => d∣n),F n := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hd : d∣n
    · simp only [hd,ite_true]
    · simp only [hd,ite_false]
      exact hF n hn hd
  calc
    _ = ∑ n : (↑((parityPositiveNaturalPositions434 positions).filter (fun n => d∣n))),F n.val :=
      hfilter.trans (Finset.sum_coe_sort
        ((parityPositiveNaturalPositions434 positions).filter (fun n => d∣n)) F).symm
    _ = ∑ w : (↑(paritySharedQuotientPositions434 positions d)),F (d*w.val) := by
      apply Fintype.sum_equiv (paritySharedQuotientPositionEquiv434 positions d)
      intro n
      change F n.val=F (d*(n.val/d))
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp n.property).2]
    _ = _ := Finset.sum_coe_sort (paritySharedQuotientPositions434 positions d) (fun w => F (d*w))

/-- An actual identity-permutation frame for one literal comparison pattern.
 It is used only to apply the already proved physical full-mark divisor fact. -/
def parityActualProbeIdentityFrame434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
      (SourceNativeMemoryBP434 20 L) J 1 m
      (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu) :=
  parityBaseIdentityFrame434 (SG:=SourceNativeMemorySG434 20 L hS)
    (SourceNativeMemoryBP434 20 L) J 1 m
    (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu) ⟨(),aux⟩

/-- The true labelled shared dilation of the literal full physical readout
 is exactly its native frame shared divisor, with every SMALL/BIG slot. -/
theorem parity_actual_probe_readout_shared_divisor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (n : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) :
    sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      (fun g i => parityActualPositionMarks434 L hS J n x g i.val) =
    parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu) x.val
      (parityActualProbeIdentityFrame434 L hS J m hmJ nu aux) := by
  exact parity_full_probe_true_shared_dilation434 J 1 m hmJ nu
    (fun g i => (Green64SmallHaar.marks (fun p : SourceNativeMemorySP434 20 L hS g => p.val)
      (J+1) (x.val.1 g) i).val)
    (fun g i => (Green64SmallHaar.marks (fun p : SourceNativeMemoryBP434 20 L g => p.val)
      (J+1) (x.val.2 g) i).val)

/-- Genuine physical shared divisibility, specialized from the already
 proved r20 native full-mark theorem; it is not a new arithmetic premise. -/
theorem parity_actual_probe_shared_readout_divides434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (n : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) :
    sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      (fun g i => parityActualPositionMarks434 L hS J n x g i.val) ∣ n := by
  let z : B654ActualParityState434 L hS J {(n : ℤ)} :=
    ⟨(⟨(n : ℤ),by simp⟩,x.val),x.property⟩
  have hd := parity_actual_frame_shared_divides434 L hL hS J m
    (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu)
    {(n : ℤ)} z (parityActualProbeIdentityFrame434 L hS J m hmJ nu aux)
  change (parityFrameSharedD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu) x.val
      (parityActualProbeIdentityFrame434 L hS J m hmJ nu aux) : ℤ) ∣ (n : ℤ) at hd
  rw [← parity_actual_probe_readout_shared_divisor434] at hd
  exact_mod_cast hd

/-- Any member of the independently defined ACTUAL completion carrier
 forces the complete labelled shared product to divide the physical integer.
 Repeated/dirty shared draws are not assumed clean; impossible fibres are empty. -/
theorem parity_actual_completion_shared_divides434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : (g : B645ActualGroup434 L hS) × sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (n : ℕ) (a : B645ActualGroup434 L hS → Fin (J+1) → ℕ)
    (ha : a∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s n) :
    sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
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
  have hd := parity_actual_probe_shared_readout_divides434 L hL hS J m hmJ nu aux n x
  rw [hshared] at hd
  exact hd

/-- Outside the actual shared-divisible position carrier there are no
 original physical completions. This supplies the quotient sum's vanishing. -/
theorem parity_actual_completions_empty_of_not_shared_dvd434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : (g : B645ActualGroup434 L hS) × sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (n : ℕ)
    (hn : ¬sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      (fun g i => s ⟨g,i⟩) ∣ n) :
    parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s n = ∅ := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    exact False.elim (hn (parity_actual_completion_shared_divides434 L hL hS J m hmJ nu aux s n a ha))
  · intro ha
    simp at ha


/-- Exact finite quotient enumeration of both complete actual endpoint
 completion carriers. Shared divisibility is proved from the physical marks
 inside this theorem; no clean, collision, or divisibility premise is assumed.
 Every original coupled weight is retained at the physical integers DR*w. -/
theorem parity_actual_shared_completion_pair_quotient434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (s : (g : B645ActualGroup434 L hS) × sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (positions : Finset ℤ)
    (F : ℕ → ℕ → (B645ActualGroup434 L hS → Fin (J+1) → ℕ) →
      (B645ActualGroup434 L hS → Fin (J+1) → ℕ) → ℂ) :
    let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
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
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
  let C := parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s
  have hempty (n : ℕ) (hn : ¬d∣n) : C n=∅ :=
    parity_actual_completions_empty_of_not_shared_dvd434 L hL hS J m hmJ nu aux s n hn
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
      intro np hnp hnd
      change (∑ a∈C (d*w),∑ b∈C np,F (d*w) np a b)=0
      simp only [hempty np hnd,Finset.sum_empty,Finset.sum_const_zero]
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeRawSplit -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The actual RAW branch has no freed first-J auxiliary slots. Its sole
 assignment is the empty dependent function, without choosing any prime. -/
def parityHarmonicRawAux434 (L : ℝ) (J m : ℕ) (hmJ : m ≤ J) :
    SourceBigAux (SourceNativeMemoryBP434 20 L) J m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none) :=
  fun _ i => False.elim (by
    simpa [sourceOriginalMemoryRawComparisonPattern434] using i.property)

/-- The RAW auxiliary fibre consists of exactly its empty assignment. -/
theorem parity_harmonic_raw_aux_eq434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (aux : SourceBigAux (SourceNativeMemoryBP434 20 L) J m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none)) :
    aux = parityHarmonicRawAux434 L J m hmJ := by
  funext g i
  exact False.elim (by
    simpa [sourceOriginalMemoryRawComparisonPattern434] using i.property)

/-- The unique original RAW base frame; its index is literally none. -/
def parityHarmonicRawBase434 (L : ℝ) (J m : ℕ) (hmJ : m ≤ J) :
    ParityHarmonicBaseFrame434 L J m hmJ :=
  ⟨none,parityHarmonicRawAux434 L J m hmJ⟩

/-- RAW retains the literal original kernel 1. No canonical comparison
 kernel, including the kernel of an empty probe pair, is substituted. -/
theorem parity_harmonic_raw_kernel_one434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi : ℝ)
    (s t : (g : sourceNativeOriginalBigType434 20 L) →
      Fin (J+1) → SourceNativeMemoryBP434 20 L g) :
    sourceOriginalMemoryRawComparisonK434
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
      (sourceNativeOriginalBigBlockA434 20 L)
      (sourceNativeOriginalBigBlockB434 20 L)
      J 1 m hmJ Q (fun _ => h) (fun _ => h) xi none
      (parityHarmonicRawAux434 L J m hmJ) s t = 1 := rfl

/-- Exact Sigma/Option enumeration: one RAW frame plus every original
 two-block comparison and every one of its dependent auxiliary assignments. -/
theorem parity_harmonic_base_sum_raw_split434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (f : ParityHarmonicBaseFrame434 L J m hmJ → ℂ) :
    (∑ a : ParityHarmonicBaseFrame434 L J m hmJ,f a) =
      f (parityHarmonicRawBase434 L J m hmJ) +
      ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L)
          (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : SourceBigAux (SourceNativeMemoryBP434 20 L) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val),
        f ⟨some nu,aux⟩ := by
  classical
  rw [Fintype.sum_sigma,Fintype.sum_option]
  congr 1
  letI : Subsingleton (SourceBigAux (SourceNativeMemoryBP434 20 L) J m
      (sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) J m hmJ none)) :=
    ⟨fun a b => (parity_harmonic_raw_aux_eq434 L J m hmJ a).trans
      (parity_harmonic_raw_aux_eq434 L J m hmJ b).symm⟩
  exact Fintype.sum_subsingleton _ (parityHarmonicRawAux434 L J m hmJ)

/-- The genuine RAW positive-position/full-residue-fibre sum. The original
 physical summand is evaluated at its unique RAW base; all physical guards,
 masses, phases and both complete endpoint states remain present. -/
def parityActualHarmonicRawPositiveFibreSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) : ℂ :=
  ∑ n : parityPositiveNaturalPositions434 positions,
  ∑ np : parityPositiveNaturalPositions434 positions,
  ∑ x : ParityActualPositionFibre434 L hS J n.val,
  ∑ y : ParityActualPositionFibre434 L hS J np.val,
    parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi (parityHarmonicRawBase434 L J m hmJ)
      (parityActualNaturalState434 L hS J positions n x)
      (parityActualNaturalState434 L hS J positions np y)

/-- Literal RAW plus all comparison auxiliary fibres, before any comparison
 restoration or estimate. This is an exact finite identity. -/
theorem parity_actual_harmonic_positive_fibre_raw_split434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityActualHarmonicPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi =
    parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
        (sourceNativeOriginalBigBlockA434 20 L)
        (sourceNativeOriginalBigBlockB434 20 L) m),
    ∑ aux : SourceBigAux (SourceNativeMemoryBP434 20 L) J m
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val),
    ∑ n : parityPositiveNaturalPositions434 positions,
    ∑ np : parityPositiveNaturalPositions434 positions,
    ∑ x : ParityActualPositionFibre434 L hS J n.val,
    ∑ y : ParityActualPositionFibre434 L hS J np.val,
      parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k
        positions lo hi F G t1 t2 tw v psi ⟨some nu,aux⟩
        (parityActualNaturalState434 L hS J positions n x)
        (parityActualNaturalState434 L hS J positions np y) := by
  exact parity_harmonic_base_sum_raw_split434 L J m hmJ (fun a =>
    ∑ n : parityPositiveNaturalPositions434 positions,
    ∑ np : parityPositiveNaturalPositions434 positions,
    ∑ x : ParityActualPositionFibre434 L hS J n.val,
    ∑ y : ParityActualPositionFibre434 L hS J np.val,
      parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k
        positions lo hi F G t1 t2 tw v psi a
        (parityActualNaturalState434 L hS J positions n x)
        (parityActualNaturalState434 L hS J positions np y))
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeRestored -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option linter.unusedSectionVars false

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Complex-valued exact integration of the ACTUAL native auxiliary law.
 The unconditioned independent original prime product has all repeated
 draws and every labelled A/B coordinate. No endpoint-conditioning occurs. -/
theorem parity_memory_aux_complex_reindex434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m) (hDisj : Disjoint nu.1 nu.2)
    (F : (SourceOriginalProbeAuxIndex434 m nu → ℕ) → ℂ) :
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu),
      (sourceAuxMass _ (fun _ p => p.val) J m V
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      F (sourceOriginalProbeMemoryAuxValues434 P J m hmJ nu aux)) =
    ∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu V i)) a : ℂ) * F a := by
  classical
  let e := sourceOriginalProbeMemoryFlatEquiv434 P J m hmJ nu hDisj
  calc
    _ = ∑ a : (↑(Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P))),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu V i)) a.val : ℂ) * F a.val := by
      apply Fintype.sum_equiv e
      intro aux
      rw [source_original_probe_memory_flat_mass434 P J m hmJ nu hDisj]
      congr 1
      apply congrArg F
      funext z
      exact (source_original_probe_memory_flat_values434 P J m hmJ nu hDisj aux z).symm
    _ = _ := Finset.sum_coe_sort
      (Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P))
      (fun a => (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu V i)) a : ℂ) * F a)


end Green64Analytic.CorrelationSquare
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD

/-- All original shared draws are summed without a clean-event condition.
 This joins the independent full native physical slices to B574's actual
 restored slice, retaining the actual auxiliary probability outside. -/
theorem parity_actual_unrestricted_shared_slice_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hDisj : Disjoint nu.1 nu.2) (Q : ℕ) (hA hB xi : ℝ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (q : ℝ) (hq : 0<q) (w wp : ℕ) :
    (∑ s ∈ Fintype.piFinset
        (fun i : sourceB574OriginalSharedIndex434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) =>
          b645ActualBand434 L hS i.1),
      parityActualCanonicalPhysicalSlice434 L hS J m hmJ nu Q hA hB xi aux q w wp
        (fun g i => s ⟨g,i⟩)) =
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    sourceB574CanonicalRestoredSlice434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
      Q hA hB xi (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
      q w wp := by
  unfold sourceB574CanonicalRestoredSlice434
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact parity_actual_canonical_physical_slice_exact434 L hS J m hmJ nu hDisj Q hA hB xi aux q hq w wp _

/-- Complete actual auxiliary and unrestricted shared-label integration at
 a fixed stripped endpoint pair. This is a proved equality of the original
 native physical sums with the independent original auxiliary product law
 applied to the full-P B574 restored slice. No auxiliary values are deduplicated
 and neither cell reciprocal mass is absorbed or cancelled. -/
theorem parity_actual_aux_shared_slice_reindex434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hDisj : Disjoint nu.1 nu.2) (Q : ℕ) (hA hB xi : ℝ)
    (q : ℝ) (hq : 0<q) (w wp : ℕ) :
    (∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      ∑ s ∈ Fintype.piFinset
        (fun i : sourceB574OriginalSharedIndex434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) =>
          b645ActualBand434 L hS i.1),
        parityActualCanonicalPhysicalSlice434 L hS J m hmJ nu Q hA hB xi aux q w wp
          (fun g i => s ⟨g,i⟩)) =
    ∑ a ∈ Fintype.piFinset
      (sourceOriginalProbeAuxPrimeSets434 m nu (sourceNativeOriginalTb434 20 L)),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu (sourceNativeOriginalVbig434 20 L) i)) a : ℂ) *
      sourceB574CanonicalRestoredSlice434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
        Q hA hB xi (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu a) q w wp := by
  let F : (SourceOriginalProbeAuxIndex434 m nu → ℕ) → ℂ := fun a =>
    sourceB574CanonicalRestoredSlice434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
      Q hA hB xi (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu a) q w wp
  calc
    _ = ∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      F (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) := by
      apply Finset.sum_congr rfl
      intro aux _
      exact parity_actual_unrestricted_shared_slice_exact434 L hS J m hmJ nu hDisj Q hA hB xi aux q hq w wp
    _ = _ := parity_memory_aux_complex_reindex434
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) J m hmJ nu hDisj F


end Green64Analytic.SourceBlockSieve

end

end

/-! ## PhysicalSharedFreeScalar -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The original endpoint arithmetic factor, including its original P gates
 and phase, before the separate native physical half damping. -/
def parityHarmonicEndpointArithmetic434 (L : ℝ) (F : PrimeSlotCore) (t : ℝ) (n : ℕ) : ℂ :=
  imaginaryPower n t * primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F n

/-- Original source arithmetic, P parity and root Mellin phase; no auxiliary
 variable occurs in this endpoint test. The harmonic inverse is kept separate. -/
def parityHarmonicSourceArithmetic434 (L : ℝ) (F : PrimeSlotCore) (t : ℝ)
    (tw : Bool) (Z v : ℝ) (n : ℕ) : ℂ :=
  (groupSign (sourceOriginalPAllActualBands 20 L) tw n : ℂ) *
    (((n : ℝ)/Z : ℝ) : ℂ)^(-Complex.I*(v : ℂ)) *
    parityHarmonicEndpointArithmetic434 L F t n

/-- Literal natural-position arithmetic multiplier from the original
 harmonic frame sum. It keeps the source seed, 1/n, both unmodified endpoint
 arithmetic tests, parity, all phases and the full-D cutoff. -/
def parityHarmonicArithmetic434 (L : ℝ) (Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) (n np D : ℕ) : ℂ :=
  if (n : ℤ)∈b654ParitySeedPositions434 lo hi then
    (n : ℂ)⁻¹ * star (parityHarmonicSourceArithmetic434 L F t1 tw Z v n) *
    psi ((n : ℝ)/(Z*(D : ℝ))) *
    (groupSign (sourceOriginalPAllActualBands 20 L) tw np : ℂ) *
    parityHarmonicEndpointArithmetic434 L G t2 np
  else 0

/-- The genuine shared harmonic scalar has 1/w. Its complete original
 source and target arithmetic tests are still evaluated at DR*w and DR*wp;
 they are not replaced by stripped tests. The original Mellin frame phase
 keeps the FULL DR*DC and the cutoff uses the exactly cancelled DR. -/
def parityHarmonicSharedArithmetic434 (L : ℝ) (zeta Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) (d c w wp : ℕ) : ℂ :=
  if ((d*w : ℕ) : ℤ)∈b654ParitySeedPositions434 lo hi then
    (w : ℂ)⁻¹ * star (parityHarmonicSourceArithmetic434 L F t1 tw Z v (d*w)) *
    psi ((w : ℝ)/(Z*(c : ℝ))) *
    (groupSign (sourceOriginalPAllActualBands 20 L) tw (d*wp) : ℂ) *
    parityHarmonicEndpointArithmetic434 L G t2 (d*wp) *
    sourceOriginalPureMellinPhase434 zeta (d*c)
  else 0

/-- The source's extra endpoint half damping is the SAME native physical
 half damping already used by the row, on every complete actual residue fibre. -/
theorem parity_actual_extra_half_native434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n : ℕ) (q : ℝ) (x : ParityActualPositionFibre434 L hS J n) :
    b656IntegerEndpointDamping434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 q (n : ℤ) =
    parityActualPositionHalf434 L hS J n q x := by
  let y : B654ActualParityState434 L hS J {(n : ℤ)} :=
    ⟨(⟨(n : ℤ),by simp⟩,x.val),x.property⟩
  exact b656_integer_endpoint_damping_native434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 q {(n : ℤ)} y

/-- Exact source arithmetic/native-half decomposition of the actual
 harmonic position factor. Both arithmetic endpoints retain every P gate;
 no auxiliary dependence is introduced into either arithmetic test. -/
theorem parity_actual_harmonic_position_test_halves434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (n np D : ℕ) (hn : 0<n) (hnp : 0<np)
    (x : ParityActualPositionFibre434 L hS J n) (y : ParityActualPositionFibre434 L hS J np) :
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi (n : ℤ) (np : ℤ) D =
    (b657ActualStateMass434 L hS J : ℂ) *
      parityHarmonicArithmetic434 L Z lo hi F G t1 t2 tw v psi n np D *
      (parityActualPositionHalf434 L hS J n (1/2 : ℝ) x : ℂ) *
      (parityActualPositionHalf434 L hS J np (1/2 : ℝ) y : ℂ) := by
  have hnI : (0 : ℤ)<n := by exact_mod_cast hn
  have hnpI : (0 : ℤ)<np := by exact_mod_cast hnp
  unfold parityActualHarmonicPositionTest434 parityHarmonicArithmetic434
  by_cases hs : (n : ℤ)∈b654ParitySeedPositions434 lo hi
  · simp only [hs,ite_true]
    rw [parity_actual_root_coefficient_one_positive434 L hS J F t1 tw Z v (n : ℤ) hnI]
    unfold b656IntegerPrimeEndpointCoefficient434
    simp only [hnI,hnpI,ite_true,Int.toNat_natCast,Int.cast_natCast]
    rw [parity_actual_extra_half_native434 L hS J n (1/2 : ℝ) x,
      parity_actual_extra_half_native434 L hS J np (1/2 : ℝ) y]
    unfold parityHarmonicSourceArithmetic434 parityHarmonicEndpointArithmetic434
    have hstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
    simp only [star_mul,hstar]
    push_cast
    ring
  · simp only [hs,ite_false,mul_zero,zero_mul]

/-- Exact original-cutoff cancellation of a nonzero labelled shared
 dilation. This does not require a cutoff support estimate or any Z bound. -/
theorem parity_harmonic_cutoff_shared_cancel434 (d c w : ℕ) (hd : d≠0) (Z : ℝ) :
    (((d*w : ℕ) : ℝ)/(Z*((d*c : ℕ) : ℝ))) = (w : ℝ)/(Z*(c : ℝ)) := by
  have hdR : (d : ℝ)≠0 := by exact_mod_cast hd
  push_cast
  calc
    _ = ((d : ℝ)*(d : ℝ)⁻¹)*((w : ℝ)/(Z*(c : ℝ))) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [mul_inv_cancel₀ hdR,one_mul]

/-- Exactly one DR inverse is extracted from the original harmonic 1/n.
 The remaining scalar preserves BOTH original physical P gates, endpoint
 phases, parity, original seed and the complete frame Mellin phase. -/
theorem parity_harmonic_arithmetic_shared_factor434
    (L : ℝ) (zeta Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (d c w wp : ℕ) (hd : d≠0) :
    parityHarmonicArithmetic434 L Z lo hi F G t1 t2 tw v psi (d*w) (d*wp) (d*c) *
      sourceOriginalPureMellinPhase434 zeta (d*c) =
    (d : ℂ)⁻¹ * parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d c w wp := by
  unfold parityHarmonicArithmetic434 parityHarmonicSharedArithmetic434
  by_cases hs : ((d*w : ℕ) : ℤ)∈b654ParitySeedPositions434 lo hi
  · simp only [hs,ite_true]
    rw [parity_harmonic_cutoff_shared_cancel434 d c w hd Z]
    simp only [Nat.cast_mul,mul_inv_rev]
    ring
  · simp only [hs,ite_false,mul_zero,zero_mul]

/-- The actual orientation +1, theta=0 frame retains exactly its genuine
 full-divisor Mellin phase and its original complex Knu. -/
theorem parity_original_edge_zero_fourier434 (K : ℂ) (zeta : ℝ) (D : ℕ) (k : ℤ) :
    originalEdgeScalar K zeta 0 D 1 k = K*sourceOriginalPureMellinPhase434 zeta D := by
  rw [source_original_edge_scalar_positive_fourier434]
  simp [Green64SourceC6.integerPhase]

/-- The literal original harmonic position factor together with its native
 edge Mellin phase has the required ONE shared inverse. This is an exact
 algebraic identity at actual full physical states, before any replacement
 of the original endpoint arithmetic or P gates. -/
theorem parity_actual_harmonic_shared_scalar434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (zeta Z : ℝ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (d c w wp : ℕ) (hd : 0<d) (hw : 0<w) (hwp : 0<wp)
    (x : ParityActualPositionFibre434 L hS J (d*w)) (y : ParityActualPositionFibre434 L hS J (d*wp)) :
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi
      ((d*w : ℕ) : ℤ) ((d*wp : ℕ) : ℤ) (d*c) *
      sourceOriginalPureMellinPhase434 zeta (d*c) =
    (b657ActualStateMass434 L hS J : ℂ) * (d : ℂ)⁻¹ *
      parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d c w wp *
      (parityActualPositionHalf434 L hS J (d*w) (1/2 : ℝ) x : ℂ) *
      (parityActualPositionHalf434 L hS J (d*wp) (1/2 : ℝ) y : ℂ) := by
  rw [parity_actual_harmonic_position_test_halves434 L hS J Z lo hi F G t1 t2 tw v psi
    (d*w) (d*wp) (d*c) (Nat.mul_pos hd hw) (Nat.mul_pos hd hwp) x y]
  calc
    _ = (b657ActualStateMass434 L hS J : ℂ) *
      (parityHarmonicArithmetic434 L Z lo hi F G t1 t2 tw v psi (d*w) (d*wp) (d*c) *
        sourceOriginalPureMellinPhase434 zeta (d*c)) *
      (parityActualPositionHalf434 L hS J (d*w) (1/2 : ℝ) x : ℂ) *
      (parityActualPositionHalf434 L hS J (d*wp) (1/2 : ℝ) y : ℂ) := by ring
    _ = _ := by rw [parity_harmonic_arithmetic_shared_factor434 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd.ne']; ring
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeHarmonicSlice -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The original auxiliary labelled product of the chosen actual probe.
 Every draw is retained, including equal values at different free slots. -/
def parityActualProbeAuxD434 (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) : ℕ :=
  ∏ g : sourceNativeOriginalBigType434 20 L,
    ∏ i : (sourceOriginalProbeMemoryPattern434 J m hmJ nu).free g,(aux g i).val

/-- A literal fixed-shared physical harmonic slice. Its defining summand
 uses the original harmonic position test, original native row half weights,
 original edge scalar and complete physical residue fibres. The original
 physical shift and both P gates remain in this construction; no B574 sum
 or extracted shared inverse occurs in its definition. -/
def parityActualHarmonicPhysicalSlice434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (w wp : ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ) : ℂ :=
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let S := fun i : (g : B645ActualGroup434 L hS) × E g => s i.1 i.2
  if (2*k)≠0 ∧ ((d*wp : ℕ) : ℤ)=((d*w : ℕ) : ℤ)+(2*k)*((d*c : ℕ) : ℤ) then
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    (parityActualUnsharedMass434 L hS J m hmJ nu : ℂ) *
    (∑ x : ParityActualPositionFibre434 L hS J (d*w),
      ∑ y : ParityActualPositionFibre434 L hS J (d*wp),
        if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*w) x)=S ∧
          parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*wp) y)=S then
          parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi
            ((d*w : ℕ) : ℤ) ((d*wp : ℕ) : ℤ) (d*c) *
          (parityActualPositionHalf434 L hS J (d*w) (1/2 : ℝ) x : ℂ) *
          (parityActualPositionHalf434 L hS J (d*wp) (1/2 : ℝ) y : ℂ) *
          originalEdgeScalar (parityActualPositionCanonicalKernel434 L hS J m hmJ nu Q h h xi aux x y)
            zeta 0 (d*c) 1 (2*k)
        else 0)
  else 0

/-- Exact cancellation of the positive labelled shared dilation in the
 original signed physical shift, without modifying the auxiliary product. -/
theorem parity_harmonic_shared_step_iff434 (d c w wp : ℕ) (hd : 0<d) (k : ℤ) :
    (((d*wp : ℕ) : ℤ)=((d*w : ℕ) : ℤ)+(2*k)*((d*c : ℕ) : ℤ)) ↔
      ((wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ)) := by
  have hdI : (d : ℤ)≠0 := by exact_mod_cast hd.ne'
  simp only [Nat.cast_mul]
  constructor
  · intro h
    apply mul_left_cancel₀ hdI
    calc
      (d : ℤ)*(wp : ℤ) = (d : ℤ)*(w : ℤ)+(2*k)*((d : ℤ)*(c : ℤ)) := h
      _ = (d : ℤ)*((w : ℤ)+(2*k)*(c : ℤ)) := by ring
  · intro h
    rw [h]
    ring

/-- Literal physical harmonic weights yield exactly the original shared
 arithmetic multiplier times the independently defined physical slice.
 The extra endpoint half factors combine with the row halves into the two
 squares, and only the original harmonic inverse supplies 1/DR. -/
theorem parity_actual_harmonic_physical_slice_factor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (w wp : ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ)
    (hd : 0<sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s)
    (hw : 0<w) (hwp : 0<wp) :
    let d := sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) s
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    parityActualHarmonicPhysicalSlice434 L hS J m hmJ nu Q h xi zeta Z k lo hi F G
      t1 t2 tw v psi aux w wp s =
    if (2*k)≠0 ∧ ((d*wp : ℕ) : ℤ)=((d*w : ℕ) : ℤ)+(2*k)*((d*c : ℕ) : ℤ) then
      parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d c w wp *
      parityActualCanonicalPhysicalSlice434 L hS J m hmJ nu Q h h xi aux (1/2 : ℝ) w wp s
    else 0 := by
  classical
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E s
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let S := fun i : (g : B645ActualGroup434 L hS) × E g => s i.1 i.2
  let A := parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d c w wp
  let Hx := fun x : ParityActualPositionFibre434 L hS J (d*w) =>
    parityActualPositionHalf434 L hS J (d*w) (1/2 : ℝ) x
  let Hy := fun y : ParityActualPositionFibre434 L hS J (d*wp) =>
    parityActualPositionHalf434 L hS J (d*wp) (1/2 : ℝ) y
  let K := fun x : ParityActualPositionFibre434 L hS J (d*w) =>
    fun y : ParityActualPositionFibre434 L hS J (d*wp) =>
      parityActualPositionCanonicalKernel434 L hS J m hmJ nu Q h h xi aux x y
  let T := parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi
    ((d*w : ℕ) : ℤ) ((d*wp : ℕ) : ℤ) (d*c)
  have hp (x : ParityActualPositionFibre434 L hS J (d*w))
      (y : ParityActualPositionFibre434 L hS J (d*wp)) :
      T*(Hx x : ℂ)*(Hy y : ℂ)*originalEdgeScalar (K x y) zeta 0 (d*c) 1 (2*k) =
      ((b657ActualStateMass434 L hS J : ℂ)*(d : ℂ)⁻¹*A) *
        (((Hx x)^2 : ℝ) : ℂ)*(((Hy y)^2 : ℝ) : ℂ)*K x y := by
    rw [parity_original_edge_zero_fourier434]
    calc
      _ = (T*sourceOriginalPureMellinPhase434 zeta (d*c))*(Hx x : ℂ)*(Hy y : ℂ)*K x y := by ring
      _ = _ := by
        rw [parity_actual_harmonic_shared_scalar434 L hS J zeta Z lo hi F G t1 t2 tw v psi
          d c w wp hd hw hwp x y]
        dsimp only [Hx,Hy,A]
        push_cast
        ring
  have hsum :
      (∑ x : ParityActualPositionFibre434 L hS J (d*w),
        ∑ y : ParityActualPositionFibre434 L hS J (d*wp),
          if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*w) x)=S ∧
            parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*wp) y)=S then
            T*(Hx x : ℂ)*(Hy y : ℂ)*originalEdgeScalar (K x y) zeta 0 (d*c) 1 (2*k) else 0) =
      ((b657ActualStateMass434 L hS J : ℂ)*(d : ℂ)⁻¹*A) *
        (∑ x : ParityActualPositionFibre434 L hS J (d*w),
          ∑ y : ParityActualPositionFibre434 L hS J (d*wp),
            if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*w) x)=S ∧
              parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*wp) y)=S then
              (((Hx x)^2 : ℝ) : ℂ)*(((Hy y)^2 : ℝ) : ℂ)*K x y else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    split_ifs
    · rw [hp]
      ring
    · simp
  dsimp only
  unfold parityActualHarmonicPhysicalSlice434 parityActualCanonicalPhysicalSlice434
  dsimp only
  split_ifs
  · rw [hsum]
    push_cast
    ring
  · rfl

/-- For an actual original probe and the exact finite quotient carriers,
 the literal harmonic slice is a full B574 slice with all scalar factors.
 Disjointness and positivity are derived, not supplied as analytic premises. -/
theorem parity_actual_harmonic_B574_quotient_slice434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val) g → ℕ)
    (positions : Finset ℤ)
    (w wp : paritySharedQuotientPositions434 positions (sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)) s)) :
    let d := sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)) s
    let c := parityActualProbeAuxD434 L J m hmJ nu.val aux
    parityActualHarmonicPhysicalSlice434 L hS J m hmJ nu.val Q h xi zeta Z k lo hi F G
      t1 t2 tw v psi aux w.val wp.val s =
    if (2*k)≠0 ∧ (wp.val : ℤ)=(w.val : ℤ)+(2*k)*(c : ℤ) then
      parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d c w.val wp.val *
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ) *
      sourceB574CanonicalPhysicalSlice434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
        Q h h xi (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu.val
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu.val aux))
        (1/2 : ℝ) w.val wp.val s
    else 0 := by
  dsimp only
  let d := sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)) s
  have hw := parity_shared_quotient_positive434 positions d w
  have hwp := parity_shared_quotient_positive434 positions d wp
  rw [parity_actual_harmonic_physical_slice_factor434 L hS J m hmJ nu.val Q h xi zeta Z k
    lo hi F G t1 t2 tw v psi aux w.val wp.val s hw.1 hw.2 hwp.2]
  rw [parity_actual_canonical_physical_slice_exact434 L hS J m hmJ nu.val
    (parity_actual_comparison_pattern_disjoint434 L m nu.val nu.property)
    Q h h xi aux (1/2 : ℝ) (by norm_num) w.val wp.val s]
  have hstep := parity_harmonic_shared_step_iff434 d
    (parityActualProbeAuxD434 L J m hmJ nu.val aux) w.val wp.val hw.1 k
  split_ifs with hp hs hs
  · ring
  · exact False.elim (hs ⟨hp.1,hstep.mp hp.2⟩)
  · exact False.elim (hp ⟨hs.1,hstep.mpr hs.2⟩)
  · rfl
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeFrameSlice -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The actual original comparison base frame, retaining the original
 probe membership and every native auxiliary draw. -/
def parityHarmonicComparisonBase434 (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) : ParityHarmonicBaseFrame434 L J m hmJ :=
  ⟨some nu,aux⟩

/-- Equality of ALL native SMALL/BIG shared labels is exactly equality
 of the complete original numeric shared restriction. This is proved on
 the full physical fibres; no clean or injective shared-array premise occurs. -/
theorem parity_actual_probe_shared_restriction_iff434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (n np : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) (y : ParityActualPositionFibre434 L hS J np) :
    b650NativeFrameShares434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu) x.val y.val
      (parityActualProbeIdentityFrame434 L hS J m hmJ nu aux) ↔
    parityPhysicalSharedRestriction434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      (parityActualPositionMarks434 L hS J n x) =
    parityPhysicalSharedRestriction434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      (parityActualPositionMarks434 L hS J np y) := by
  rw [← parity_physical_shared_guard_restriction434]
  unfold b650NativeFrameShares434 parityActualProbeIdentityFrame434 parityBaseIdentityFrame434
  dsimp only
  constructor
  · intro h g i
    cases g with
    | inl g =>
      have hi : i.val∈sourceSmallShared J 1 g := by
        simpa only [parity_full_probe_shared_small434] using i.property
      exact congrArg Subtype.val (h.1 g i.val hi)
    | inr g =>
      have hi : i.val∈sourceBigShared J 1 m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) g := by
        simpa only [parity_full_probe_shared_big434,source_original_probe_memory_shared_slots434] using i.property
      exact congrArg Subtype.val (h.2 g i.val hi)
  · intro h
    constructor
    · intro g j hj
      apply Subtype.ext
      exact h (Sum.inl g) ⟨j,by simpa only [parity_full_probe_shared_small434] using hj⟩
    · intro g j hj
      apply Subtype.ext
      exact h (Sum.inr g) ⟨j,by
        simpa only [parity_full_probe_shared_big434,source_original_probe_memory_shared_slots434] using hj⟩

/-- The original comparison-frame divisor is precisely the complete
 numeric shared readout times the genuine repeated-draw auxiliary product. -/
theorem parity_actual_probe_frame_divisor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (n : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) :
    b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (fun _ : Unit => sourceOriginalProbeMemoryPattern434 J m hmJ nu) x.val
      (parityActualProbeIdentityFrame434 L hS J m hmJ nu aux) =
    sourceB574SharedDilation434 (J+1)
      (sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
      (fun g i => parityActualPositionMarks434 L hS J n x g i.val) *
    parityActualProbeAuxD434 L J m hmJ nu aux := by
  rw [parity_frame_D_factor434,← parity_actual_probe_readout_shared_divisor434]
  rfl

/-- Literal original comparison harmonic summand on the two complete
 physical residue fibres. Native auxiliary exclusion stays inside the true
 canonical kernel; the full shared guard and physical step stay outside. -/
def parityActualHarmonicFibreTerm434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (n np : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) (y : ParityActualPositionFibre434 L hS J np) : ℂ :=
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E
    (fun g i => parityActualPositionMarks434 L hS J n x g i.val)
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  if (2*k)≠0 ∧
      parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
        parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y) ∧
      (np : ℤ)=(n : ℤ)+(2*k)*((d*c : ℕ) : ℤ) then
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    (parityActualUnsharedMass434 L hS J m hmJ nu : ℂ) *
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi (n : ℤ) (np : ℤ) (d*c) *
    (parityActualPositionHalf434 L hS J n (1/2 : ℝ) x : ℂ) *
    (parityActualPositionHalf434 L hS J np (1/2 : ℝ) y : ℂ) *
    originalEdgeScalar (parityActualPositionCanonicalKernel434 L hS J m hmJ nu Q h h xi aux x y)
      zeta 0 (d*c) 1 (2*k)
  else 0

/-- The actual original H_T comparison base summand is the literal physical
 fibre term. This identifies the original construction before disintegrating
 shared labels or dividing positions; all P gates and phases remain intact. -/
theorem parity_actual_harmonic_comparison_fibre_term434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val)
    (positions : Finset ℤ) (n np : parityPositiveNaturalPositions434 positions)
    (x : ParityActualPositionFibre434 L hS J n.val) (y : ParityActualPositionFibre434 L hS J np.val) :
    parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
      (parityHarmonicComparisonBase434 L J m hmJ nu aux)
      (parityActualNaturalState434 L hS J positions n x) (parityActualNaturalState434 L hS J positions np y) =
    parityActualHarmonicFibreTerm434 L hS J m hmJ nu.val Q h xi zeta Z k lo hi F G
      t1 t2 tw v psi aux n.val np.val x y := by
  classical
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let a := parityHarmonicComparisonBase434 L J m hmJ nu aux
  let f := parityBaseIdentityFrame434 (SG:=SourceNativeMemorySG434 20 L hS)
    (SourceNativeMemoryBP434 20 L) J 1 m pats a
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
  let d := sourceB574SharedDilation434 (J+1) E
    (fun g i => parityActualPositionMarks434 L hS J n.val x g i.val)
  let c := parityActualProbeAuxD434 L J m hmJ nu.val aux
  have hD : b650NativeFrameD434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m pats x.val f=d*c :=
    parity_actual_probe_frame_divisor434 L hS J m hmJ nu.val aux n.val x
  have hsh : b650NativeFrameShares434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m pats x.val y.val f ↔
      parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n.val x)=
        parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np.val y) :=
    parity_actual_probe_shared_restriction_iff434 L hS J m hmJ nu.val aux n.val np.val x y
  dsimp only [pats,a,f,parityHarmonicComparisonBase434,
    sourceOriginalMemoryRawComparisonPattern434] at hD hsh
  have ho : (1 : ℤ)=1 ∨ (1 : ℤ)=-1 := Or.inl rfl
  unfold parityHarmonicBaseSummand434 parityActualHarmonicFibreTerm434
  dsimp only
  unfold parityPermutationMarginalScalar434 b650IntegerFrameAllowed434
  dsimp only [parityHarmonicComparisonBase434,parityActualNaturalState434,
    sourceOriginalMemoryRawComparisonPattern434]
  simp only [hD,hsh,ho,true_and,one_mul,memoryOrientationK,ite_true,
    sourceOriginalMemoryRawComparisonK434]
  dsimp only [parityBaseIdentityFrame434,d,c,E]
  simp only [true_or,true_and]
  rw [parity_original_edge_zero_fourier434,parity_original_edge_zero_fourier434]
  unfold parityActualPositionCanonicalKernel434
  by_cases hk : (2*k)≠0
  <;> by_cases hs : parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n.val x)=
    parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np.val y)
  <;> by_cases ht : (np.val : ℤ)=(n.val : ℤ)+(2*k)*((d*c : ℕ) : ℤ)
  <;> by_cases hb : memoryIndependentAuxBan
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux x.val y.val
  all_goals dsimp only [d,c,E] at hs ht
  all_goals
    simp only [hk,hs,ht,hb,ite_true,ite_false,true_and,false_and,and_true,and_false,
      zero_mul,mul_zero]
  all_goals
    try simp only [parityActualUnsharedMass434,parityActualPositionHalf434,
      Finset.prod_mul_distrib,Complex.ofReal_mul]
  all_goals
    split_ifs <;> try ring
  all_goals omega
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeNumeric -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The unchanged full SMALL+BIG original canonical physical kernel.
 Both original inverse cell masses, all full endpoint products, comparison
 sign and original auxiliary mark exclusion are contained in this kernel. -/
def parityActualFullCanonicalKernel434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi : ℝ) (aux : ParityActualProbeAux434 L J m hmJ nu)
    (a b : B645ActualGroup434 L hS → Fin (J+1) → ℕ) : ℂ :=
  sourceB574CanonicalFullKernel434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
    Q h h xi (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)) a b

/-- Literal original physical-position scalar, with both unmodified
 endpoint tests and original cutoff; its complete row half damping is
 evaluated on the physical integers. This contains no B574 completion sum. -/
def parityActualHarmonicNumericWeight434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (n np d : ℕ) : ℂ :=
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  if (2*k)≠0 ∧ (np : ℤ)=(n : ℤ)+(2*k)*((d*c : ℕ) : ℤ) then
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    (parityActualUnsharedMass434 L hS J m hmJ nu : ℂ) *
    parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi (n : ℤ) (np : ℤ) (d*c) *
    (sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) (1/2 : ℝ) n : ℂ) *
    (sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) (1/2 : ℝ) np : ℂ) *
    sourceOriginalPureMellinPhase434 zeta (d*c)
  else 0

/-- Pointwise physical-to-numeric identity on a complete original pair.
 The only guard is the true equality of the full shared readout; all
 quantities on its support are identified by the previously proved native
 damping and canonical-kernel equalities. -/
theorem parity_actual_harmonic_fibre_numeric434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hDisj : Disjoint nu.1 nu.2)
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (n np : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) (y : ParityActualPositionFibre434 L hS J np) :
    let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
    let rx := parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)
    let ry := parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y)
    parityActualHarmonicFibreTerm434 L hS J m hmJ nu Q h xi zeta Z k lo hi F G
      t1 t2 tw v psi aux n np x y =
    if rx=ry then
      parityActualHarmonicNumericWeight434 L hS J m hmJ nu zeta Z k lo hi F G t1 t2 tw v psi aux n np
        (sourceB574SharedDilation434 (J+1) E (fun g i => rx ⟨g,i⟩)) *
      parityActualFullCanonicalKernel434 L hS J m hmJ nu Q h xi aux
        (parityActualPositionMarks434 L hS J n x) (parityActualPositionMarks434 L hS J np y)
    else 0 := by
  classical
  dsimp only
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E
    (fun g i => parityActualPositionMarks434 L hS J n x g i.val)
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  by_cases hs : parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
    parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y)
  · rw [if_pos hs]
    unfold parityActualHarmonicFibreTerm434 parityActualHarmonicNumericWeight434
    dsimp only
    rw [parity_actual_position_canonical_kernel_exact434 L hS J m hmJ nu hDisj Q h h xi aux x y hs,
      parity_actual_position_half_exact434 L hS J n (1/2 : ℝ) (by norm_num) x,
      parity_actual_position_half_exact434 L hS J np (1/2 : ℝ) (by norm_num) y,
      parity_original_edge_zero_fourier434]
    unfold parityActualFullCanonicalKernel434
    by_cases ht : (2*k)≠0 ∧ (np : ℤ)=(n : ℤ)+(2*k)*((d*c : ℕ) : ℤ)
    · have hg : (2*k)≠0 ∧
          parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
            parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y) ∧
          (np : ℤ)=(n : ℤ)+(2*k)*((d*c : ℕ) : ℤ) := ⟨ht.1,hs,ht.2⟩
      rw [if_pos hg]
      dsimp only [parityPhysicalSharedRestriction434]
      dsimp only [d,c,E] at ht
      simp only [ht.1,ht.2,and_true,ite_true]
      split_ifs with hk
      · ring
      · exact False.elim (hk ht.1)
    · have hg : ¬((2*k)≠0 ∧
          parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
            parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y) ∧
          (np : ℤ)=(n : ℤ)+(2*k)*((d*c : ℕ) : ℤ)) := fun h => ht ⟨h.1,h.2.2⟩
      rw [if_neg hg]
      dsimp only [parityPhysicalSharedRestriction434]
      dsimp only [d,c,E] at ht
      simp only [ht,ite_false,zero_mul]
  · rw [if_neg hs]
    unfold parityActualHarmonicFibreTerm434
    dsimp only
    have hg : ¬((2*k)≠0 ∧
        parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=
          parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y) ∧
        (np : ℤ)=(n : ℤ)+(2*k)*((d*c : ℕ) : ℤ)) := fun h => hs h.2.1
    rw [if_neg hg]

/-- Complete physical fibre pairs disintegrate into ALL original shared
 arrays and their two genuine completion carriers, with the literal harmonic
 scalar. Repeated/dirty draws remain in the sum; there is no clean-family
 condition or expected aggregate identity among the hypotheses. -/
theorem parity_actual_harmonic_fixed_positions_shared434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) (n np : ℕ) :
    let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
    (∑ x : ParityActualPositionFibre434 L hS J n,
      ∑ y : ParityActualPositionFibre434 L hS J np,
        parityActualHarmonicFibreTerm434 L hS J m hmJ nu.val Q h xi zeta Z k lo hi F G
          t1 t2 tw v psi aux n np x y) =
    ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
      ∑ a∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s n,
      ∑ b∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s np,
        parityActualHarmonicNumericWeight434 L hS J m hmJ nu.val zeta Z k lo hi F G t1 t2 tw v psi aux n np
          (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)) *
        parityActualFullCanonicalKernel434 L hS J m hmJ nu.val Q h xi aux a b := by
  classical
  dsimp only
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
  let P := b645ActualBand434 L hS
  let R := parityPhysicalSharedRestriction434 (J+1) E
  let K := parityActualFullCanonicalKernel434 L hS J m hmJ nu.val Q h xi aux
  let W := fun s : (g : B645ActualGroup434 L hS) × E g → ℕ =>
    parityActualHarmonicNumericWeight434 L hS J m hmJ nu.val zeta Z k lo hi F G t1 t2 tw v psi aux n np
      (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩))
  calc
    _ = ∑ x : ParityActualPositionFibre434 L hS J n,
        ∑ y : ParityActualPositionFibre434 L hS J np,
          if R (parityActualPositionMarks434 L hS J n x)=R (parityActualPositionMarks434 L hS J np y) then
            W (R (parityActualPositionMarks434 L hS J n x))*
            K (parityActualPositionMarks434 L hS J n x) (parityActualPositionMarks434 L hS J np y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact parity_actual_harmonic_fibre_numeric434 L hS J m hmJ nu.val
        (parity_actual_comparison_pattern_disjoint434 L m nu.val nu.property)
        Q h xi zeta Z k lo hi F G t1 t2 tw v psi aux n np x y
    _ = ∑ a∈bigMarkLists P (fun _ => J+1) n,
        ∑ b∈bigMarkLists P (fun _ => J+1) np,
          if R a=R b then W (R a)*K a b else 0 :=
      parity_actual_position_pair_reindex434 L hS J n np (fun a b => if R a=R b then W (R a)*K a b else 0)
    _ = ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => P i.1),
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np,W (R a)*K a b := by
      simpa only [parity_physical_shared_guard_restriction434] using
        parity_physical_pair_shared_fibres434 P (J+1) E n np (fun a b => W (R a)*K a b)
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


/-- At the genuine shared multiples the numeric completion sum is the
 independently defined literal physical harmonic slice. The proof reindexes
 BOTH complete physical fibres and uses the unchanged full canonical kernel;
 it assumes no positivity or clean-array property. -/
theorem parity_actual_harmonic_numeric_physical_slice434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) (w wp : ℕ)
    (s : (g : B645ActualGroup434 L hS) × sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val) g → ℕ) :
    let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
    let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
    (∑ a∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s (d*w),
      ∑ b∈parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s (d*wp),
        parityActualHarmonicNumericWeight434 L hS J m hmJ nu.val zeta Z k lo hi F G t1 t2 tw v psi
          aux (d*w) (d*wp) d * parityActualFullCanonicalKernel434 L hS J m hmJ nu.val Q h xi aux a b) =
    parityActualHarmonicPhysicalSlice434 L hS J m hmJ nu.val Q h xi zeta Z k lo hi F G
      t1 t2 tw v psi aux w wp (fun g i => s ⟨g,i⟩) := by
  classical
  dsimp only
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
  let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
  let c := parityActualProbeAuxD434 L J m hmJ nu.val aux
  let P := b645ActualBand434 L hS
  let H := fun n : ℕ => (sourcePhysicalGroupedHalf434 P (J+1) (1/2 : ℝ) n : ℂ)
  let K := parityActualFullCanonicalKernel434 L hS J m hmJ nu.val Q h xi aux
  let T := parityActualHarmonicPositionTest434 L hS J Z lo hi F G t1 t2 tw v psi
    ((d*w : ℕ) : ℤ) ((d*wp : ℕ) : ℤ) (d*c)
  let B := fun a b : B645ActualGroup434 L hS → Fin (J+1) → ℕ =>
    T*H (d*w)*H (d*wp)*sourceOriginalPureMellinPhase434 zeta (d*c)*K a b
  have hsum :
      (∑ x : ParityActualPositionFibre434 L hS J (d*w),
        ∑ y : ParityActualPositionFibre434 L hS J (d*wp),
          if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*w) x)=s ∧
            parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*wp) y)=s then
            T*(parityActualPositionHalf434 L hS J (d*w) (1/2 : ℝ) x : ℂ)*
              (parityActualPositionHalf434 L hS J (d*wp) (1/2 : ℝ) y : ℂ)*
              originalEdgeScalar (parityActualPositionCanonicalKernel434 L hS J m hmJ nu.val Q h h xi aux x y)
                zeta 0 (d*c) 1 (2*k) else 0) =
      ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s (d*w),
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s (d*wp),B a b := by
    calc
      _ = ∑ x : ParityActualPositionFibre434 L hS J (d*w),
          ∑ y : ParityActualPositionFibre434 L hS J (d*wp),
            if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*w) x)=s ∧
              parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*wp) y)=s then
              B (parityActualPositionMarks434 L hS J (d*w) x) (parityActualPositionMarks434 L hS J (d*wp) y)
            else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with hs
        · rw [parity_actual_position_canonical_kernel_exact434 L hS J m hmJ nu.val
            (parity_actual_comparison_pattern_disjoint434 L m nu.val nu.property)
            Q h h xi aux x y (hs.1.trans hs.2.symm),
            parity_actual_position_half_exact434 L hS J (d*w) (1/2 : ℝ) (by norm_num) x,
            parity_actual_position_half_exact434 L hS J (d*wp) (1/2 : ℝ) (by norm_num) y,
            parity_original_edge_zero_fourier434]
          dsimp only [B,H,K,parityActualFullCanonicalKernel434]
          ring
        · rfl
      _ = _ := parity_actual_position_shared_pair_reindex434 L hS J (d*w) (d*wp) E s B
  unfold parityActualHarmonicPhysicalSlice434
  dsimp only
  rw [hsum]
  unfold parityActualHarmonicNumericWeight434
  dsimp only
  split_ifs
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [B,H,K,T]
    ring
  · simp only [zero_mul,Finset.sum_const_zero]
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeAggregate -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- Finite exchange of the two original endpoint positions and the full
 shared-array carrier. No weights or normalization factors are introduced. -/
theorem parity_shared_position_sum_order434 {S : Type} [DecidableEq S]
    (N : Finset ℕ) (ss : Finset S) (F : S → ℕ → ℕ → ℂ) :
    (∑ n∈N,∑ np∈N,∑ s∈ss,F s n np) =
      ∑ s∈ss,∑ n∈N,∑ np∈N,F s n np := by
  calc
    _ = ∑ n∈N,∑ s∈ss,∑ np∈N,F s n np := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- The ORIGINAL comparison base contribution, summed on its complete
 original finite physical carriers, equals ALL fixed-shared harmonic slices
 on the exact quotient carriers. Shared disintegration, original full-mark
 divisibility and both position reindexings are proved internally. -/
theorem parity_actual_harmonic_comparison_quotient_slices434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) :
    let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
    (∑ n : parityPositiveNaturalPositions434 positions,
      ∑ np : parityPositiveNaturalPositions434 positions,
      ∑ x : ParityActualPositionFibre434 L hS J n.val,
      ∑ y : ParityActualPositionFibre434 L hS J np.val,
        parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
          (parityHarmonicComparisonBase434 L J m hmJ nu aux)
          (parityActualNaturalState434 L hS J positions n x)
          (parityActualNaturalState434 L hS J positions np y)) =
    ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
      ∑ w∈paritySharedQuotientPositions434 positions (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)),
      ∑ wp∈paritySharedQuotientPositions434 positions (sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)),
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
  let W := fun s : (g : B645ActualGroup434 L hS) × E g → ℕ =>
    fun n np : ℕ =>
      parityActualHarmonicNumericWeight434 L hS J m hmJ nu.val zeta Z k lo hi F G
        t1 t2 tw v psi aux n np (D s)
  calc
    _ = ∑ n : N,∑ np : N,∑ s∈ss,
        ∑ a∈parityPhysicalCompletionsAt434 P (J+1) E s n.val,
        ∑ b∈parityPhysicalCompletionsAt434 P (J+1) E s np.val,W s n.val np.val*K a b := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro np hnp
      calc
        _ = ∑ x : ParityActualPositionFibre434 L hS J n.val,
            ∑ y : ParityActualPositionFibre434 L hS J np.val,
              parityActualHarmonicFibreTerm434 L hS J m hmJ nu.val Q h xi zeta Z k lo hi F G
                t1 t2 tw v psi aux n.val np.val x y := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          exact parity_actual_harmonic_comparison_fibre_term434 L hS J m hmJ nu Q h xi zeta Z k
            lo hi F G t1 t2 tw v psi aux positions n np x y
        _ = _ := parity_actual_harmonic_fixed_positions_shared434 L hS J m hmJ nu Q h xi zeta Z k
          lo hi F G t1 t2 tw v psi aux n.val np.val
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
          exact parity_actual_harmonic_numeric_physical_slice434 L hS J m hmJ nu Q h xi zeta Z k
            lo hi F G t1 t2 tw v psi aux w wp s

/-- Target B574 aggregate for one original comparison probe and one exact
 auxiliary draw. It keeps the complete original shared-array carrier,
 original finite quotient windows, original P gates at DR*w and DR*wp,
 source seed, all phases, cutoff, native auxiliary mass and full B574 kernel. -/
def parityActualHarmonicComparisonB574434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) : ℂ :=
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu.val)
  let c := parityActualProbeAuxD434 L J m hmJ nu.val aux
  ∑ s∈Fintype.piFinset (fun i : (g : B645ActualGroup434 L hS) × E g => b645ActualBand434 L hS i.1),
    let d := sourceB574SharedDilation434 (J+1) E (fun g i => s ⟨g,i⟩)
    ∑ w∈paritySharedQuotientPositions434 positions d,
    ∑ wp∈paritySharedQuotientPositions434 positions d,
      if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
        parityHarmonicSharedArithmetic434 L zeta Z lo hi F G t1 t2 tw v psi d c w wp *
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

/-- Exact original H_T comparison-base contribution to the full B574
 weighted-slice aggregate. No desired aggregate identity, clean-family
 condition, endpoint replacement, restoration error or E4.1 is assumed. -/
theorem parity_actual_harmonic_comparison_B574_aggregate434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m))
    (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ) (positions : Finset ℤ)
    (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu.val) :
    (∑ n : parityPositiveNaturalPositions434 positions,
      ∑ np : parityPositiveNaturalPositions434 positions,
      ∑ x : ParityActualPositionFibre434 L hS J n.val,
      ∑ y : ParityActualPositionFibre434 L hS J np.val,
        parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
          (parityHarmonicComparisonBase434 L J m hmJ nu aux)
          (parityActualNaturalState434 L hS J positions n x)
          (parityActualNaturalState434 L hS J positions np y)) =
    parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k positions lo hi F G
      t1 t2 tw v psi aux := by
  rw [parity_actual_harmonic_comparison_quotient_slices434 L hL hS J m hmJ nu Q h xi zeta Z k
    positions lo hi F G t1 t2 tw v psi aux]
  unfold parityActualHarmonicComparisonB574434
  dsimp only
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro wp hwp
  exact parity_actual_harmonic_B574_quotient_slice434 L hS J m hmJ nu Q h xi zeta Z k lo hi F G
    t1 t2 tw v psi aux (fun g i => s ⟨g,i⟩) positions ⟨w,hw⟩ ⟨wp,hwp⟩
end Green64Analytic.Parity

end

end

/-! ## PhysicalSharedFreeHarmonicAggregate -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The complete EXISTING UNCAPPED positive physical-fibre sum is its
 literal RAW contribution plus the complete B574 comparison aggregate.
 The RAW kernel remains 1; it is never identified with an empty probe.
 Multiplicative physical Ppart caps are a separate insertion obligation. -/
theorem parity_actual_harmonic_positive_B574_split434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ) (k : ℤ)
    (positions : Finset ℤ) (lo hi : ℕ) (F G : PrimeSlotCore)
    (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityActualHarmonicPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi =
    parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k positions lo hi F G
          t1 t2 tw v psi aux := by
  classical
  let I : Type := ↥(sourceOriginalTwoBlockProbePatterns434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
  let R := parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
    positions lo hi F G t1 t2 tw v psi
  let C : (nu : I) → ParityActualProbeAux434 L J m hmJ nu.val → ℂ := fun nu aux =>
    ∑ n : parityPositiveNaturalPositions434 positions,
    ∑ np : parityPositiveNaturalPositions434 positions,
    ∑ x : ParityActualPositionFibre434 L hS J n.val,
    ∑ y : ParityActualPositionFibre434 L hS J np.val,
      parityHarmonicBaseSummand434 L hS J m hmJ Q h xi zeta Z k positions lo hi F G t1 t2 tw v psi
        ⟨some nu,aux⟩ (parityActualNaturalState434 L hS J positions n x)
        (parityActualNaturalState434 L hS J positions np y)
  let B : (nu : I) → ParityActualProbeAux434 L J m hmJ nu.val → ℂ := fun nu aux =>
    parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k positions lo hi F G
      t1 t2 tw v psi aux
  have hc (nu : I) (aux : ParityActualProbeAux434 L J m hmJ nu.val) : C nu aux=B nu aux := by
    exact parity_actual_harmonic_comparison_B574_aggregate434 L hL hS J m hmJ nu Q h xi zeta Z k
      positions lo hi F G t1 t2 tw v psi aux
  have hsum : (∑ nu : I,∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,C nu aux) =
      ∑ nu : I,∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,B nu aux :=
    Finset.sum_congr rfl (fun nu _ => Finset.sum_congr rfl (fun aux _ => hc nu aux))
  exact (parity_actual_harmonic_positive_fibre_raw_split434 L hS J m hmJ Q h xi zeta Z k
    positions lo hi F G t1 t2 tw v psi).trans (congrArg (fun z : ℂ => R+z) hsum)

/-- The UNCHANGED previously defined UNCAPPED H_T is its literal RAW
 physical contribution plus the complete actual B574 comparison aggregate.
 The proof starts from that independent physical pairing and preserves its
 global window, finite source seed, full shared and auxiliary draws, the
 P-dependent ordinary-part prime/interval cores, parity, phases and cutoff.
 It does not insert the separate multiplicative physical Ppart cap and does
 not assert quantitative weighted restoration or E4.1. -/
theorem parity_harmonic_physical_B574_comparison_aggregate434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
    parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k
          (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi aux := by
  exact (parity_harmonic_physical_positive_fibres434 L hS J m hmJ Q h xi zeta Z Ck k T F G
    t1 t2 tw v psi).trans
    (parity_actual_harmonic_positive_B574_split434 L hL hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi)

/-- The same exact EXISTING UNCAPPED harmonic identity with ONE external Z.
 No endpoint, auxiliary or shared normalization absorbs an additional Z. -/
theorem parity_harmonic_physical_outer_Z_B574434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z Ck : ℝ) (k : ℤ) (T : ℕ)
    (F G : PrimeSlotCore) (t1 t2 : ℝ) (tw : Bool) (v : ℝ) (psi : ℝ → ℂ) :
    (Z : ℂ)*parityHarmonicPhysical434 L hS J m hmJ Q h xi zeta Z Ck k T F G t1 t2 tw v psi =
    (Z : ℂ)*parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi zeta Z k
      (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi +
    ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
      ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
        (Z : ℂ)*parityActualHarmonicComparisonB574434 L hS J m hmJ nu Q h xi zeta Z k
          (b654ParityIntervalWindow434 J Ck L 1 (2^T)) 1 (2^T) F G t1 t2 tw v psi aux := by
  have he := parity_harmonic_physical_B574_comparison_aggregate434 L hL hS J m hmJ Q h xi zeta Z Ck k T F G
    t1 t2 tw v psi
  simpa only [mul_add,Finset.mul_sum] using congrArg (fun z : ℂ => (Z : ℂ)*z) he
end Green64Analytic.Parity

end

end

/-! ## ActualRankAuxLaw -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Green64Analytic.CorrelationSquare

/-- Complex multiplicative tests of the literal independent labelled law.
No prime values are identified and no support or mass is renormalized. -/
theorem parity_complex_shared_product_test434
    {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (mu : I → ℕ → ℝ) (test : I → ℕ → ℂ) :
    (∑ a ∈ Fintype.piFinset P,
      (sourceSharedLaw434 mu a : ℂ) * (∏ i, test i (a i))) =
    ∏ i, ∑ p ∈ P i, (mu i p : ℂ) * test i p := by
  classical
  simp only [sourceSharedLaw434, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum P (fun i p => (mu i p : ℂ) * test i p)).symm

/-- The two literal auxiliary products have the true independent prime
law, including repeated draws and the original V at each labelled slot. -/
theorem parity_original_aux_multiplicative_product434
    {G : Type} [DecidableEq G] (m : ℕ)
    (nu : SourceOriginalProbePattern434 G m) (P : G → Finset ℕ) (V : G → ℝ)
    (fA fB : ℕ →* ℂ) :
    (∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu V i)) a : ℂ) *
      (fA (sourceOriginalProbeDA434 m nu a) *
        fB (sourceOriginalProbeDB434 m nu a))) =
    (∏ z : nu.1, ∑ p ∈ P z.val.1,
      (sourcePrimeSharedAtom434 (V z.val.1) p : ℂ) * fA p) *
    (∏ z : nu.2, ∑ p ∈ P z.val.1,
      (sourcePrimeSharedAtom434 (V z.val.1) p : ℂ) * fB p) := by
  classical
  let test : SourceOriginalProbeAuxIndex434 m nu → ℕ → ℂ :=
    Sum.elim (fun _ => fA) (fun _ => fB)
  have hprod (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
      fA (sourceOriginalProbeDA434 m nu a) * fB (sourceOriginalProbeDB434 m nu a) =
        ∏ i, test i (a i) := by
    simp only [sourceOriginalProbeDA434, sourceOriginalProbeDB434, map_prod,
      SourceOriginalProbeAuxIndex434, Fintype.prod_sum_type, test, Sum.elim_inl, Sum.elim_inr]
  calc
    _ = ∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu V i)) a : ℂ) * (∏ i, test i (a i)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hprod]
    _ = ∏ i : SourceOriginalProbeAuxIndex434 m nu,
      ∑ p ∈ sourceOriginalProbeAuxPrimeSets434 m nu P i,
        (sourcePrimeSharedAtom434 (sourceOriginalProbeAuxV434 m nu V i) p : ℂ) *
          test i p := parity_complex_shared_product_test434 _ _ _
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

end Green64Analytic.CorrelationSquare
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare Green64FullPhysicalE

/-- The full native auxiliary dilation is exactly DA*DB on the actual
r20 comparison family. Disjointness follows from the original blocks. -/
theorem parity_actual_probe_aux_product_split434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    parityActualProbeAuxD434 L J m hmJ nu aux =
      sourceOriginalProbeDA434 m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) *
      sourceOriginalProbeDB434 m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) := by
  have hDisj := parity_actual_comparison_pattern_disjoint434 L m nu hnu
  exact source_original_probe_memory_aux_product_transfer434 J m hmJ nu hDisj
    (fun z => (aux z.1 z.2).val)

/-- Exact actual-r20 tilted auxiliary law. The sum is over the real
SourceBigAux carrier with its original sourceAuxMass, and the right side
contains both complete labelled products of original band prime sums.
This identity only factors the displayed multiplicative test; additional
cell predicates, cutoff and shift dependence require their own Fourier join. -/
theorem parity_actual_rank_aux_product_law434
    (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    (fA fB : ℕ →* ℂ) :
    (∑ aux : ParityActualProbeAux434 L J m hmJ nu,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      (fA (sourceOriginalProbeDA434 m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)) *
        fB (sourceOriginalProbeDB434 m nu
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)))) =
    (∏ z : nu.1, ∑ p ∈ sourceNativeOriginalTb434 20 L z.val.1,
      (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L z.val.1) p : ℂ) * fA p) *
    (∏ z : nu.2, ∑ p ∈ sourceNativeOriginalTb434 20 L z.val.1,
      (sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 20 L z.val.1) p : ℂ) * fB p) := by
  have hDisj := parity_actual_comparison_pattern_disjoint434 L m nu hnu
  calc
    _ = ∑ a ∈ Fintype.piFinset
      (sourceOriginalProbeAuxPrimeSets434 m nu (sourceNativeOriginalTb434 20 L)),
      (sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m nu (sourceNativeOriginalVbig434 20 L) i)) a : ℂ) *
      (fA (sourceOriginalProbeDA434 m nu a) * fB (sourceOriginalProbeDB434 m nu a)) :=
      parity_memory_aux_complex_reindex434 (sourceNativeOriginalTb434 20 L)
        (sourceNativeOriginalVbig434 20 L) J m hmJ nu hDisj _
    _ = _ := parity_original_aux_multiplicative_product434 m nu
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) fA fB

end Green64Analytic.Parity

end

end

