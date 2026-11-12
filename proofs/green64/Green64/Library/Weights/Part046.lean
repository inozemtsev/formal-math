module

public import Green64.Library.Weights.Part014
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.Part017
public import Green64.Library.Sieve.Foundations.Part004
public import Green64.Library.Weights.Part016
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.Part043
public import Mathlib.Logic.Equiv.Prod
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Weights.Part001
public import Green64.Library.Analysis.Estimates.Part004
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
# Weights / Part046

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalTrueDiscardedCellMass -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Source03's ACTUAL finite independent PRIME-label mass
on every globally DISCARDED product-log cell is at most
xi times the number of POSSIBLE cells. No logarithmic
cell is introduced as an external fake index; the cells
are those REALIZED by physical products of the original
finite prime supports, with repetitions allowed.
Crucially, this is a probability MASS estimate, not
an unjustified L² operator contraction on rare cells. -/
theorem source_original_true_discarded_cell_mass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi) :
    (∑ a ∈ Fintype.piFinset S,
      if sourceOriginalLiteralLogCellIndex434 h
        (∏ i : ι, a i) ∈
          sourceOriginalFiniteActiveLogCells434 S mu h xi
      then 0 else sourceSharedLaw434 mu a) ≤
      ((sourceOriginalCandidateLogCells434 S h).card:ℝ)*xi := by
  classical
  let states : Finset (ι → ℕ) := Fintype.piFinset S
  let candidate : Finset ℤ := sourceOriginalCandidateLogCells434 S h
  let idx : (ι → ℕ) → ℤ := fun a =>
    sourceOriginalLiteralLogCellIndex434 h (∏ i : ι, a i)
  let mass : (ι → ℕ) → ℝ := sourceSharedLaw434 mu
  have hcandidate (a : ι → ℕ) (ha : a ∈ states) :
      idx a ∈ candidate := by
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hcell (j : ℤ) :
      (∑ a ∈ states, if idx a = j then mass a else 0) =
      sourceOriginalActualCellProbability434 S mu h j := by
    unfold sourceOriginalActualCellProbability434
    apply Finset.sum_congr rfl
    intro a ha
    have hiff := source_original_literal_log_cell_iff_index434
      h hh (∏ i : ι, a i) j
    by_cases hja : idx a = j
    · have hreal : sourceOriginalLiteralLogCell434 h j (∏ i : ι, a i) :=
        hiff.mpr hja.symm
      simp only [idx,mass, hja, hreal, if_pos]
    · have hnreal : ¬sourceOriginalLiteralLogCell434
          h j (∏ i : ι, a i) := by
        intro ht
        exact hja (hiff.mp ht).symm
      simp only [idx,mass,hja,hnreal,if_neg]
  let retained : Finset ℤ :=
    candidate.filter (fun j =>
      xi ≤ ∑ a ∈ states, if idx a=j then mass a else 0)
  have hretained :
      retained = sourceOriginalFiniteActiveLogCells434 S mu h xi := by
    apply Finset.ext
    intro j
    simp only [retained,sourceOriginalFiniteActiveLogCells434,
      Finset.mem_filter, hcell j]
    rfl
  have hGeneric := source_original_finite_discarded_cell_mass_le434
    states candidate idx mass hcandidate xi hxi.le
  change
    (∑ a ∈ states, if idx a ∈ retained then 0 else mass a) ≤
      (candidate.card:ℝ)*xi at hGeneric
  rw [hretained] at hGeneric
  exact hGeneric
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueDroppedPrimitiveKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The ORIGINAL global character-cell kernel is IDENTICALLY
ZERO for a target value X outside EVERY active cell. Nothing
is assumed about the auxiliary input D, normalization masses,
or character family. This is an exact kernel support identity,
not an approximate character-cancellation statement. -/
theorem source_original_character_cell_kernel_zero_outside_target434
    {Cell Character : Type} [DecidableEq Cell]
    (active : Finset Cell) (chars : Finset Character)
    (cell : Cell → ℕ → Prop) (mass : Cell → ℝ)
    (chi : Character → ℕ → ℂ)
    (D X : ℕ)
    (hOutside : ∀ j ∈ active, ¬cell j X) :
    sourceOriginalCharacterCellKernel434
      active chars cell mass chi D X = 0 := by
  classical
  unfold sourceOriginalCharacterCellKernel434
  apply Finset.sum_eq_zero
  intro j hj
  have hGate : ¬(cell j D ∧ cell j X) := by
    intro h
    exact (hOutside j hj) h.2
  simp only [if_neg hGate]

/-- SOURCE03's actual primitive-character GLOBAL kernel is
exactly zero when its ACTUAL physical output log-product
cell INDEX is not retained. There is no hidden Q²/xi²
normalization loss on the discarded target event. -/
theorem source_original_actual_primitive_global_zero_discarded_target434
    (Q : ℕ) (active : Finset ℤ)
    (h : ℝ) (hh : 0 < h)
    (mass : ℤ → ℝ) (D X : ℕ)
    (hDrop : sourceOriginalLiteralLogCellIndex434 h X ∉ active) :
    sourceOriginalActualPrimitiveGlobalKernel434
      Q active h mass D X = 0 := by
  unfold sourceOriginalActualPrimitiveGlobalKernel434
  apply source_original_character_cell_kernel_zero_outside_target434
  intro j hj hjCell
  have hIndex := (source_original_literal_log_cell_iff_index434
    h hh X j).mp hjCell
  apply hDrop
  simpa only [hIndex] using hj

/-- The actual TWO-GLOBAL original comparison Kν is exactly
ZERO if the target X_A's A-cell OR source X_B's B-cell
is discarded. The original (-1)^card sign and arbitrary
primitive-character levels remain unchanged. -/
theorem source_original_actual_primitive_comparison_zero_discarded434
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ)
    (hDrop :
      sourceOriginalLiteralLogCellIndex434 hA XA ∉ JA ∨
      sourceOriginalLiteralLogCellIndex434 hB XB ∉ JB) :
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB DA XA DB XB r = 0 := by
  unfold sourceOriginalActualPrimitiveComparisonKernel434
  rcases hDrop with hDropA | hDropB
  · rw [source_original_actual_primitive_global_zero_discarded_target434
      Q JA hA hhA massA DA XA hDropA]
    ring
  · rw [source_original_actual_primitive_global_zero_discarded_target434
      Q JB hB hhB massB DB XB hDropB]
    ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueProductDyadPairCount -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- The TRUE set of attainable ORIGINAL SOURCE03 product-dyad
PAIRS is polynomially bounded in L. Each BIG prime coordinate
may range over an arbitrarily large finite prime support, but
only its actual labelled product dyadic index matters.
The source/target products can involve different numbers of
labelled primes, and repeated numerical primes are allowed.
This is not an artificial full box of dyads: the cardinal
counts only genuinely attainable pairs of product-log cells. -/
theorem source_original_true_BIG_product_dyad_pairs_card434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (SB : ιB → Finset ℕ)
    (L d : ℝ) (hL : 1 ≤ L)
    (hPrimeA : ∀ i p, p ∈ SA i →
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ i p, p ∈ SB i →
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    let A := sourceOriginalCandidateLogCells434
      SA (Real.log (2:ℝ))
    let B := sourceOriginalCandidateLogCells434
      SB (Real.log (2:ℝ))
    (A.product B).card ≤
      (Nat.ceil (((Fintype.card ιA:ℝ)*L^d)/Real.log (2:ℝ))+1) *
      (Nat.ceil (((Fintype.card ιB:ℝ)*L^d)/Real.log (2:ℝ))+1) := by
  classical
  have hh : 0 < Real.log (2:ℝ) :=
    Real.log_pos (by norm_num)
  have hA := source_original_true_BIG_candidate_cell_card434
    SA L d (Real.log (2:ℝ)) hL hh hPrimeA
  have hB := source_original_true_BIG_candidate_cell_card434
    SB L d (Real.log (2:ℝ)) hL hh hPrimeB
  dsimp only
  change ((sourceOriginalCandidateLogCells434 SA (Real.log (2:ℝ))) ×ˢ
    (sourceOriginalCandidateLogCells434 SB (Real.log (2:ℝ)))).card ≤
      (Nat.ceil (((Fintype.card ιA:ℝ)*L^d)/Real.log (2:ℝ))+1) *
      (Nat.ceil (((Fintype.card ιB:ℝ)*L^d)/Real.log (2:ℝ))+1)
  rw [Finset.card_product]
  exact Nat.mul_le_mul hA hB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDyadCount -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Quantitative cardinality of the ACTUAL attainable
ν-selected SOURCE B/TARGET A dyadic product family.
The original BIG upper prime scale p≤exp(L^d)
supplies polynomial, not support-exponential, count;
independently labelled repeated prime values are allowed.
No extra uniformity or candidate count hypothesis is assumed. -/
theorem source_original_probe_true_dyad_pair_card434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (L d : ℝ) (hL : 1 ≤ L)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) (Real.log (2:ℝ))
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) (Real.log (2:ℝ))
    (CB.product CA).card ≤
      (Nat.ceil (((Fintype.card ν.2:ℝ)*L^d)/Real.log (2:ℝ))+1) *
      (Nat.ceil (((Fintype.card ν.1:ℝ)*L^d)/Real.log (2:ℝ))+1) := by
  classical
  exact source_original_true_BIG_product_dyad_pairs_card434
    (fun z : ν.2 => P z.val.1)
    (fun z : ν.1 => P z.val.1)
    L d hL hPrimeB hPrimeA

/-- The number of ORIGINAL physically attainable dyad
pairs admits a real-valued polynomial upper bound
explicitly in the two numbers of ν-selected labels.
This is the loss to absorb when the authentic major/minor
signed operator estimates are summed over dyad pairs. -/
theorem source_original_probe_true_dyad_pair_real_bound434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (L d : ℝ) (hL : 1 ≤ L)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d)) :
    let CB := sourceOriginalCandidateLogCells434
      (fun z : ν.2 => P z.val.1) (Real.log (2:ℝ))
    let CA := sourceOriginalCandidateLogCells434
      (fun z : ν.1 => P z.val.1) (Real.log (2:ℝ))
    ((CB.product CA).card:ℝ) ≤
      (((Fintype.card ν.2:ℝ)*L^d)/Real.log (2:ℝ)+2) *
      (((Fintype.card ν.1:ℝ)*L^d)/Real.log (2:ℝ)+2) := by
  classical
  let CB := sourceOriginalCandidateLogCells434
    (fun z : ν.2 => P z.val.1) (Real.log (2:ℝ))
  let CA := sourceOriginalCandidateLogCells434
    (fun z : ν.1 => P z.val.1) (Real.log (2:ℝ))
  have hlog : 0 < Real.log (2:ℝ) := by
    apply Real.log_pos
    norm_num
  have hB := source_original_true_BIG_candidate_cell_real_bound434
    (fun z : ν.2 => P z.val.1)
      L d (Real.log (2:ℝ)) hL hlog hPrimeB
  have hA := source_original_true_BIG_candidate_cell_real_bound434
    (fun z : ν.1 => P z.val.1)
      L d (Real.log (2:ℝ)) hL hlog hPrimeA
  have hBP : 0 ≤ (CB.card:ℝ) := Nat.cast_nonneg _
  have hAP : 0 ≤ (CA.card:ℝ) := Nat.cast_nonneg _
  change ((CB.product CA).card:ℝ) ≤ _
  rw [Finset.product_eq_sprod, Finset.card_product]
  push_cast
  exact mul_le_mul hB hA hAP (by linarith)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueDyadSummation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact quantitative SOURCE03 ν-dependent GLOBAL dyad
summation on its original independent physical free-slot
prime product law. It combines genuine dyadic partition,
source/target weighted-L² energy decomposition and finite
Cauchy–Schwarz. Arbitrary mark-dependent source/target tests
and arbitrary signed joint complex integrand z are allowed.
The sole remaining premise hEach is the mathematically
substantive estimate for each actual dyad pair (C196 still
requires independent proof). This theorem does NOT
secretly assume a full signed comparison estimate. -/
theorem source_original_probe_true_physical_dyad_sum_L2434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hVpos : ∀ g, 0 < V g)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ)
    (z : (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) ×
        (SourceOriginalVariableBIGState434
        (fun g : G => {p : ℕ // p ∈ P g})
        (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) → ℂ)
    (eps : ℝ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let CB := sourceOriginalCandidateLogCells434
      (fun k : ν.2 => P k.val.1) (Real.log (2:ℝ))
    let CA := sourceOriginalCandidateLogCells434
      (fun k : ν.1 => P k.val.1) (Real.log (2:ℝ))
    let idxS : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxT : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    let es : ℤ → ℝ := fun i =>
      ∑ s : X, if idxS s = i
      then w s*‖sourceTest s‖^2 else 0
    let et : ℤ → ℝ := fun j =>
      ∑ v : X, if idxT v = j
      then w v*‖targetTest v‖^2 else 0
    let zpair : ℤ × ℤ → ℂ := fun ij =>
      ∑ ab : X × X,
        if idxS ab.1 = ij.1 ∧ idxT ab.2 = ij.2
        then z ab else 0
    (∀ ij ∈ CB.product CA,
      ‖zpair ij‖^2 ≤ eps^2*es ij.1*et ij.2) →
    ‖∑ ab : X × X, z ab‖^2 ≤
      ((CB.product CA).card:ℝ)*eps^2*
        sourceOriginalVariableBIGEnergy434 BP t mu sourceTest*
        sourceOriginalVariableBIGEnergy434 BP t mu targetTest := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let CB := sourceOriginalCandidateLogCells434
    (fun k : ν.2 => P k.val.1) (Real.log (2:ℝ))
  let CA := sourceOriginalCandidateLogCells434
    (fun k : ν.1 => P k.val.1) (Real.log (2:ℝ))
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 (Real.log (2:ℝ))
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  let es : ℤ → ℝ := fun i =>
    ∑ s : X, if idxS s = i
    then w s*‖sourceTest s‖^2 else 0
  let et : ℤ → ℝ := fun j =>
    ∑ v : X, if idxT v = j
    then w v*‖targetTest v‖^2 else 0
  let zpair : ℤ × ℤ → ℂ := fun ij =>
    ∑ ab : X × X,
      if idxS ab.1 = ij.1 ∧ idxT ab.2 = ij.2
      then z ab else 0
  intro hEach
  have hmuNN (g : G) (p : BP g) : 0 ≤ mu g p :=
    source_original_harmonic_prime_nonneg434
      (fun p : BP g => prime g p) (V g) (hVpos g) p
  have hw (x : X) : 0 ≤ w x :=
    source_original_variable_BIG_mass_nonneg434
      BP t mu hmuNN x
  have hES (i : ℤ) (hi : i ∈ CB) : 0 ≤ es i := by
    dsimp only [es]
    apply Finset.sum_nonneg
    intro s hs
    by_cases hidx : idxS s = i
    · simp only [if_pos hidx]
      exact mul_nonneg (hw s) (sq_nonneg _)
    · simp only [if_neg hidx]
      exact le_refl _
  have hET (j : ℤ) (hj : j ∈ CA) : 0 ≤ et j := by
    dsimp only [et]
    apply Finset.sum_nonneg
    intro v hv
    by_cases hidx : idxT v = j
    · simp only [if_pos hidx]
      exact mul_nonneg (hw v) (sq_nonneg _)
    · simp only [if_neg hidx]
      exact le_refl _
  have hDyadPartition :
      (∑ ij ∈ CB.product CA, zpair ij) =
        ∑ ab : X × X, z ab := by
    exact source_original_probe_true_physical_two_ended_dyad_partition434
      J ell m hmJ ν P z
  have hEnergy := source_original_probe_true_source_target_dyad_energy_partition434
    J ell m hmJ ν P V sourceTest targetTest
  have hEnergyS :
      (∑ i ∈ CB, es i) =
        sourceOriginalVariableBIGEnergy434 BP t mu sourceTest :=
    hEnergy.1
  have hEnergyT :
      (∑ j ∈ CA, et j) =
        sourceOriginalVariableBIGEnergy434 BP t mu targetTest :=
    hEnergy.2
  have hSummation := source_original_finite_attainable_dyad_sum_L2434
    CB CA es et zpair eps hES hET hEach
  rw [← hDyadPartition]
  simpa only [hEnergyS,hEnergyT] using hSummation
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueTwoGlobalCost -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- ACTUAL original source03 two-global-character/cell kernel:
each global free-label block has its own independent genuine
normalized prime law. Once original threshold ν_j>=xi and
#Dirichlet characters<=Q^2 hold in EACH block, the complete FOUR
index expansion has total absolute coefficient mass at most
Q^4*xi^{-4}. This is the TRUE original law, allowing repeated
prime values in different slots. No residual-ideal-family
existence or polynomial pattern-count assertion is made here. -/
theorem source_original_actual_two_global_expansion_cost434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (SB : ιB → Finset ℕ)
    (VA : ιA → ℝ) (VB : ιB → ℝ)
    (hVA : ∀ i, VA i=∑ p ∈ SA i,1/(p:ℝ))
    (hVB : ∀ i, VB i=∑ p ∈ SB i,1/(p:ℝ))
    (hVAp : ∀ i,0 < VA i) (hVBp : ∀ i,0 < VB i)
    (hPrimeA : ∀ i p,p∈SA i → p.Prime)
    (hPrimeB : ∀ i p,p∈SB i → p.Prime)
    (JA JB : Finset ℤ) (qA qB : ℕ)
    (CA : Finset (DirichletCharacter ℂ qA))
    (CB : Finset (DirichletCharacter ℂ qB))
    (hA hB xi Q : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (hxi : 0 < xi) (hQ : 0 ≤ Q)
    (hMassA : ∀ j ∈ JA,xi ≤
      sourceOriginalActualCellProbability434 SA
        (fun i => sourcePrimeSharedAtom434 (VA i)) hA j)
    (hMassB : ∀ j ∈ JB,xi ≤
      sourceOriginalActualCellProbability434 SB
        (fun i => sourcePrimeSharedAtom434 (VB i)) hB j)
    (hCharA : (CA.card:ℝ) ≤ Q^2)
    (hCharB : (CB.card:ℝ) ≤ Q^2) :
    (∑ ja ∈ JA,∑ _ca ∈ CA,∑ jb ∈ JB,∑ _cb ∈ CB,
      sourceOriginalTwoCellCoefficient434
        (sourceOriginalActualCellProbability434 SA
          (fun i => sourcePrimeSharedAtom434 (VA i)) hA)
        (sourceOriginalActualCellProbability434 SB
          (fun i => sourcePrimeSharedAtom434 (VB i)) hB)
        ja jb) ≤ Q^4*(xi⁻¹)^4 := by
  have hTotalA := source_original_true_prime_cell_probability_total434
    SA VA hA hhA JA hVA hVAp hPrimeA
  have hTotalB := source_original_true_prime_cell_probability_total434
    SB VB hB hhB JB hVB hVBp hPrimeB
  have hBase := source_original_two_global_probability_cell_cost434
    JA CA JB CB
    (sourceOriginalActualCellProbability434 SA
      (fun i => sourcePrimeSharedAtom434 (VA i)) hA)
    (sourceOriginalActualCellProbability434 SB
      (fun i => sourcePrimeSharedAtom434 (VB i)) hB)
    xi hxi hMassA hMassB hTotalA hTotalB
  have hChars : (CA.card:ℝ)*(CB.card:ℝ) ≤ Q^4 := by
    calc
      _ ≤ Q^2*Q^2 :=
        mul_le_mul hCharA hCharB (Nat.cast_nonneg _) (sq_nonneg Q)
      _ = Q^4 := by ring
  have hFactor : 0 ≤ (xi⁻¹)^4 := by positivity
  exact hBase.trans (mul_le_mul_of_nonneg_right hChars hFactor)

/-- Active original source03 PRIME probability cells are automatically
bounded in number by xi^{-1}; no explicit TL^d/h count is needed. -/
theorem source_original_true_prime_active_cell_card434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ)
    (h : ℝ) (hh : 0 < h)
    (active : Finset ℤ)
    (hV : ∀ i,V i=∑ p ∈ S i,1/(p:ℝ))
    (hVp : ∀ i,0 < V i)
    (hPrime : ∀ i p,p∈S i → p.Prime)
    (xi : ℝ) (hxi : 0 < xi)
    (hMass : ∀ j∈active,xi ≤
      sourceOriginalActualCellProbability434 S
        (fun i => sourcePrimeSharedAtom434 (V i)) h j) :
    (active.card:ℝ) ≤ xi⁻¹ := by
  exact source_original_probability_active_cell_card434
    active
    (sourceOriginalActualCellProbability434 S
      (fun i => sourcePrimeSharedAtom434 (V i)) h)
    xi hxi hMass
    (source_original_true_prime_cell_probability_total434
      S V h hh active hV hVp hPrime)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveTwoGlobal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12500000

/-- The TRUE source03 TWO independent global prime-label blocks,
with ACTUAL source prime atoms 1/(pV), ACTUAL half-open log cell
probabilities nu_j, and the ACTUAL all-positive-conductor
PRIMITIVE-character family. Total absolute four-index expansion
cost <= Q^4 xi^-4. No character-count or cell-mass normalization
hypothesis is injected: both follow from true source objects. -/
theorem source_original_actual_primitive_two_global_mass434
    {ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (SB : ιB → Finset ℕ)
    (VA : ιA → ℝ) (VB : ιB → ℝ)
    (hVA : ∀ i,VA i=∑ p ∈ SA i,1/(p:ℝ))
    (hVB : ∀ i,VB i=∑ p ∈ SB i,1/(p:ℝ))
    (hVAp : ∀ i,0 < VA i) (hVBp : ∀ i,0 < VB i)
    (hPrimeA : ∀ i p,p ∈ SA i → p.Prime)
    (hPrimeB : ∀ i p,p ∈ SB i → p.Prime)
    (JA JB : Finset ℤ) (hA hB : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (Q : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA,xi ≤
      sourceOriginalActualCellProbability434 SA
        (fun i => sourcePrimeSharedAtom434 (VA i)) hA j)
    (hMassB : ∀ j ∈ JB,xi ≤
      sourceOriginalActualCellProbability434 SB
        (fun i => sourcePrimeSharedAtom434 (VB i)) hB j) :
    (∑ ja ∈ JA,
      ∑ _ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
        ∑ jb ∈ JB,
          ∑ _cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
            sourceOriginalTwoCellCoefficient434
              (sourceOriginalActualCellProbability434 SA
                (fun i => sourcePrimeSharedAtom434 (VA i)) hA)
              (sourceOriginalActualCellProbability434 SB
                (fun i => sourcePrimeSharedAtom434 (VB i)) hB)
              ja jb) ≤ ((Q:ℝ)^4)*(xi⁻¹)^4 := by
  let chars := sourceOriginalActualPrimitiveCharacters434 Q
  have hTotalA := source_original_true_prime_cell_probability_total434
    SA VA hA hhA JA hVA hVAp hPrimeA
  have hTotalB := source_original_true_prime_cell_probability_total434
    SB VB hB hhB JB hVB hVBp hPrimeB
  have hBase := source_original_two_global_probability_cell_cost434
    JA chars JB chars
    (sourceOriginalActualCellProbability434 SA
      (fun i => sourcePrimeSharedAtom434 (VA i)) hA)
    (sourceOriginalActualCellProbability434 SB
      (fun i => sourcePrimeSharedAtom434 (VB i)) hB)
    xi hxi hMassA hMassB hTotalA hTotalB
  have hc : (chars.card:ℝ) ≤ (Q:ℝ)^2 := by
    exact_mod_cast source_original_actual_primitive_count434 Q
  have hCC : (chars.card:ℝ)*(chars.card:ℝ) ≤ (Q:ℝ)^4 := by
    calc
      _ ≤ ((Q:ℝ)^2)*((Q:ℝ)^2) :=
        mul_le_mul hc hc (Nat.cast_nonneg _) (sq_nonneg _)
      _ = (Q:ℝ)^4 := by ring
  change (∑ ja ∈ JA,∑ _ca ∈ chars,
    ∑ jb ∈ JB,∑ _cb ∈ chars,
      sourceOriginalTwoCellCoefficient434
        (sourceOriginalActualCellProbability434 SA
          (fun i => sourcePrimeSharedAtom434 (VA i)) hA)
        (sourceOriginalActualCellProbability434 SB
          (fun i => sourcePrimeSharedAtom434 (VB i)) hB)
        ja jb) ≤ _
  exact hBase.trans
    (mul_le_mul_of_nonneg_right hCC (by positivity))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitivePatternCost -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- Entire SOURCE03 FINITE comparison-pattern family with its TRUE
two independent free-label blocks: each ν has its original source
prime groups and probability laws, both actual log-cell sets,
and TRUE primitive characters of ALL conductors 1..Q.
No hCount(characters), hTotal(nu), or hCell disjointness axioms.
The only remaining external input is the ORIGINAL RESIDUAL-family
total signed-pattern coefficient cost; its existence and bound
are not silently manufactured by this expansion lemma. -/
theorem source_original_actual_primitive_pattern_cost434
    {Pattern ιA ιB : Type}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (patterns : Finset Pattern)
    (SA : Pattern → ιA → Finset ℕ)
    (SB : Pattern → ιB → Finset ℕ)
    (VA : Pattern → ιA → ℝ)
    (VB : Pattern → ιB → ℝ)
    (hVA : ∀ ν ∈ patterns,∀ i,
      VA ν i=∑ p ∈ SA ν i,1/(p:ℝ))
    (hVB : ∀ ν ∈ patterns,∀ i,
      VB ν i=∑ p ∈ SB ν i,1/(p:ℝ))
    (hVAp : ∀ ν ∈ patterns,∀ i,0 < VA ν i)
    (hVBp : ∀ ν ∈ patterns,∀ i,0 < VB ν i)
    (hPrimeA : ∀ ν ∈ patterns,∀ i p,p ∈ SA ν i → p.Prime)
    (hPrimeB : ∀ ν ∈ patterns,∀ i p,p ∈ SB ν i → p.Prime)
    (JA JB : Pattern → Finset ℤ)
    (hA hB : Pattern → ℝ)
    (hhA : ∀ ν ∈ patterns,0 < hA ν)
    (hhB : ∀ ν ∈ patterns,0 < hB ν)
    (Q : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ ν ∈ patterns,∀ j ∈ JA ν,xi ≤
      sourceOriginalActualCellProbability434 (SA ν)
        (fun i => sourcePrimeSharedAtom434 (VA ν i)) (hA ν) j)
    (hMassB : ∀ ν ∈ patterns,∀ j ∈ JB ν,xi ≤
      sourceOriginalActualCellProbability434 (SB ν)
        (fun i => sourcePrimeSharedAtom434 (VB ν i)) (hB ν) j)
    (cost : Pattern → ℝ)
    (hCost : ∀ ν ∈ patterns,0 ≤ cost ν) :
    (∑ ν ∈ patterns,cost ν*
      (∑ ja ∈ JA ν,
        ∑ _ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
          ∑ jb ∈ JB ν,
            ∑ _cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
              sourceOriginalTwoCellCoefficient434
                (sourceOriginalActualCellProbability434 (SA ν)
                  (fun i => sourcePrimeSharedAtom434 (VA ν i)) (hA ν))
                (sourceOriginalActualCellProbability434 (SB ν)
                  (fun i => sourcePrimeSharedAtom434 (VB ν i)) (hB ν))
                ja jb)) ≤
    (∑ ν ∈ patterns,cost ν)*((Q:ℝ)^4*(xi⁻¹)^4) := by
  have hOne (ν : Pattern) (hν : ν ∈ patterns) :
      (∑ ja ∈ JA ν,
        ∑ _ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
          ∑ jb ∈ JB ν,
            ∑ _cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
              sourceOriginalTwoCellCoefficient434
                (sourceOriginalActualCellProbability434 (SA ν)
                  (fun i => sourcePrimeSharedAtom434 (VA ν i)) (hA ν))
                (sourceOriginalActualCellProbability434 (SB ν)
                  (fun i => sourcePrimeSharedAtom434 (VB ν i)) (hB ν))
                ja jb) ≤ ((Q:ℝ)^4)*(xi⁻¹)^4 :=
    source_original_actual_primitive_two_global_mass434
      (SA ν) (SB ν) (VA ν) (VB ν)
      (hVA ν hν) (hVB ν hν) (hVAp ν hν) (hVBp ν hν)
      (hPrimeA ν hν) (hPrimeB ν hν)
      (JA ν) (JB ν) (hA ν) (hB ν)
      (hhA ν hν) (hhB ν hν) Q xi hxi
      (hMassA ν hν) (hMassB ν hν)
  calc
    _ ≤ ∑ ν ∈ patterns,cost ν*((Q:ℝ)^4*(xi⁻¹)^4) := by
      apply Finset.sum_le_sum
      intro ν hν
      exact mul_le_mul_of_nonneg_left (hOne ν hν) (hCost ν hν)
    _ = (∑ ν ∈ patterns,cost ν)*((Q:ℝ)^4*(xi⁻¹)^4) := by
      rw [Finset.sum_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualFourIndexFamily -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The explicit FINITE source03 comparison-pattern index set:
one original residual comparison pattern nu, one original active
cell and TRUE primitive Dirichlet character for EACH of the TWO
global kernel blocks. Nothing is indexed by individual prime groups
inside the two character expansions. -/
noncomputable def sourceOriginalActualFourIndexFamily434
    {Pattern : Type} (patterns : Finset Pattern)
    (JA JB : Pattern → Finset ℤ) (Q : ℕ) :
    Finset (Σ ν : Pattern,
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1)))) := by
  classical
  let C := sourceOriginalActualPrimitiveCharacters434 Q
  exact patterns.sigma (fun ν =>
    ((JA ν).product C).product ((JB ν).product C))

/-- The actual nonnegative absolute coefficient cost of ONE
literal source03 four-index comparison term, including its
signed-pattern-family outer coefficient. The two character
factors have unit modulus and contribute no extra coefficient. -/
noncomputable def sourceOriginalActualFourIndexCost434
    {Pattern : Type} (cost : Pattern → ℝ)
    (massA massB : Pattern → ℤ → ℝ) (Q : ℕ)
    (term : Σ ν : Pattern,
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1))) ×
      (ℤ × (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1)))) : ℝ :=
  cost term.1 *
    sourceOriginalTwoCellCoefficient434 (massA term.1) (massB term.1)
      term.2.1.1 term.2.2.1

/-- EXACT finite reindexing: the true source03 four-index
comparison family has exactly the same total absolute coefficient
mass as the nested sum in the already checked coefficient bound.
There is no omitted multiplicity and no pattern-specific
normalization factor. -/
theorem source_original_actual_four_index_reindex434
    {Pattern : Type} (patterns : Finset Pattern)
    (JA JB : Pattern → Finset ℤ) (Q : ℕ)
    (cost : Pattern → ℝ) (massA massB : Pattern → ℤ → ℝ) :
    (∑ z ∈ sourceOriginalActualFourIndexFamily434 patterns JA JB Q,
      sourceOriginalActualFourIndexCost434 cost massA massB Q z) =
    ∑ ν ∈ patterns,cost ν*
      (∑ ja ∈ JA ν,
        ∑ _ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
          ∑ jb ∈ JB ν,
            ∑ _cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
              sourceOriginalTwoCellCoefficient434
                (massA ν) (massB ν) ja jb) := by
  classical
  let C := sourceOriginalActualPrimitiveCharacters434 Q
  unfold sourceOriginalActualFourIndexFamily434
  change (∑ z ∈ patterns.sigma
      (fun ν => ((JA ν).product C).product ((JB ν).product C)),
      cost z.1 * sourceOriginalTwoCellCoefficient434
        (massA z.1) (massB z.1) z.2.1.1 z.2.2.1) = _
  simp only [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro ν hν
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  simp only [← Finset.mul_sum, C]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMinorPrimitiveModeCost -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Source03 TRUE total absolute coefficient cost for the
exact signed primitive minor factorization C280: the
independently retained A/B cell probability masses sum
to ≤1 and are ≥xi, the ACTUAL original family of
primitive characters has ≤Q² elements per global block.
This proves the unconditional (Q⁴ xi^-4) cost on the
REAL endpoint character values, not a fictitious assumed
polynomial number of terms or a product over groups. -/
theorem source_original_signed_minor_endpoint_l1_cost434
    (Q r : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (massA massB : ℤ → ℝ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (XA XB : ℕ) :
    (∑ i ∈ JA.product (sourceOriginalActualPrimitiveCharacters434 Q),
      ∑ j ∈ JB.product (sourceOriginalActualPrimitiveCharacters434 Q),
        ‖(-((-1:ℂ)^r)) *
          sourceOriginalPrimitiveOutputCellCoefficient434
            Q hA massA i.1 i.2 XA *
          sourceOriginalPrimitiveOutputCellCoefficient434
            Q hB massB j.1 j.2 XB‖) ≤
       ((Q:ℝ)^4)*(xi⁻¹)^4 := by
  classical
  let chars := sourceOriginalActualPrimitiveCharacters434 Q
  let IA := JA.product chars
  let IB := JB.product chars
  have hNorm (i : ℤ × (Σ q : Fin Q,
      DirichletCharacter ℂ (q.val+1))) (hi : i ∈ IA)
      (j : ℤ × (Σ q : Fin Q,
      DirichletCharacter ℂ (q.val+1))) (hj : j ∈ IB) :
      ‖(-((-1:ℂ)^r)) *
          sourceOriginalPrimitiveOutputCellCoefficient434
            Q hA massA i.1 i.2 XA *
          sourceOriginalPrimitiveOutputCellCoefficient434
            Q hB massB j.1 j.2 XB‖ ≤
        sourceOriginalTwoCellCoefficient434
          massA massB i.1 j.1 := by
    have him : i.1 ∈ JA := (Finset.mem_product.mp hi).1
    have hjm : j.1 ∈ JB := (Finset.mem_product.mp hj).1
    have hma : 0 < massA i.1 := hxi.trans_le (hMassA i.1 him)
    have hmb : 0 < massB j.1 := hxi.trans_le (hMassB j.1 hjm)
    exact source_original_signed_primitive_output_pair_norm434
      Q r hA hB massA massB i.1 j.1 i.2 j.2
      XA XB hma hmb
  have hRaw :
      (∑ i ∈ IA, ∑ j ∈ IB,
        ‖(-((-1:ℂ)^r)) *
          sourceOriginalPrimitiveOutputCellCoefficient434
            Q hA massA i.1 i.2 XA *
          sourceOriginalPrimitiveOutputCellCoefficient434
            Q hB massB j.1 j.2 XB‖) ≤
      ∑ i ∈ IA,∑ j ∈ IB,
          sourceOriginalTwoCellCoefficient434
            massA massB i.1 j.1 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hNorm i hi j hj
  have hReindex :
      (∑ i ∈ IA,∑ j ∈ IB,
          sourceOriginalTwoCellCoefficient434
            massA massB i.1 j.1) =
      ∑ ia ∈ JA,∑ ca ∈ chars,
        ∑ ib ∈ JB,∑ cb ∈ chars,
          sourceOriginalTwoCellCoefficient434
            massA massB ia ib := by
    dsimp [IA,IB]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro ia hia
    apply Finset.sum_congr rfl
    intro ca hca
    rw [Finset.sum_product]
  have hCellCost :=
    source_original_two_global_probability_cell_cost434
      JA chars JB chars massA massB
      xi hxi hMassA hMassB hTotalA hTotalB
  have hCount : (chars.card:ℝ) ≤ (Q:ℝ)^2 :=
    by exact_mod_cast source_original_actual_primitive_count434 Q
  have hCharCost : ((chars.card:ℝ)*(chars.card:ℝ)) ≤
      (Q:ℝ)^4 := by
    calc
      _ ≤ ((Q:ℝ)^2)*((Q:ℝ)^2) :=
        mul_le_mul hCount hCount (Nat.cast_nonneg _) (sq_nonneg _)
      _ = (Q:ℝ)^4 := by ring
  have hNonneg : 0 ≤ (xi⁻¹)^4 := by positivity
  calc
    _ ≤ (∑ i ∈ IA,∑ j ∈ IB,
          sourceOriginalTwoCellCoefficient434
            massA massB i.1 j.1) := hRaw
    _ = ∑ ia ∈ JA,∑ ca ∈ chars,
        ∑ ib ∈ JB,∑ cb ∈ chars,
          sourceOriginalTwoCellCoefficient434
            massA massB ia ib := hReindex
    _ ≤ ((chars.card:ℝ)*(chars.card:ℝ))*(xi⁻¹)^4 :=
      hCellCost
    _ ≤ ((Q:ℝ)^4)*(xi⁻¹)^4 :=
      mul_le_mul_of_nonneg_right hCharCost hNonneg
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitivePolynomialBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact fixed-power cost of the source03 TWO GLOBAL primitive
character/cell expansions when the original parameters satisfy
Q≤L^Cq and xi^{-1}≤L^Cxi. The exponent has NO dependence on
J, the number of prime groups, or the number of probe slots. -/
theorem source_original_primitive_two_global_poly_budget434
    (Q : ℕ) (xi L : ℝ) (Cq Cxi : ℕ)
    (hxi : 0 < xi) (hL : 1 ≤ L)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (hX : xi⁻¹ ≤ L^Cxi) :
    (Q:ℝ)^4*(xi⁻¹)^4 ≤ L^(4*(Cq+Cxi)) := by
  have hQ4 : (Q:ℝ)^4 ≤ (L^Cq)^4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hQ _
  have hX4 : (xi⁻¹)^4 ≤ (L^Cxi)^4 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hxi.le) hX _
  have hLnonneg : 0 ≤ L := by linarith
  calc
    _ ≤ (L^Cq)^4*(L^Cxi)^4 :=
      mul_le_mul hQ4 hX4 (pow_nonneg (inv_nonneg.mpr hxi.le) _)
        (pow_nonneg (pow_nonneg hLnonneg _) _)
    _ = (L^Cq*L^Cxi)^4 := by rw [mul_pow]
    _ = (L^(Cq+Cxi))^4 := by rw [pow_add]
    _ = L^((Cq+Cxi)*4) := by rw [pow_mul]
    _ = L^(4*(Cq+Cxi)) := by congr 1; omega

/-- Combining the imported original residual-family coefficient
budget with the PROVED two-global primitive/cell expansion costs
only a further FIXED power of L. This proves the analytical
bookkeeping implication, NOT existence of the residual family. -/
theorem source_original_primitive_pattern_poly_budget434
    (L : ℝ) (Q : ℕ) (xi : ℝ)
    (Cq Cxi Cfamily : ℕ)
    (hxi : 0 < xi) (hL : 1 ≤ L)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (hX : xi⁻¹ ≤ L^Cxi)
    (familyCost expandedCost : ℝ)
    (hFamilyNonneg : 0 ≤ familyCost)
    (hFamily : familyCost ≤ L^Cfamily)
    (hExpansion : expandedCost ≤
      familyCost*((Q:ℝ)^4*(xi⁻¹)^4)) :
    expandedCost ≤ L^(Cfamily+4*(Cq+Cxi)) := by
  have hLnonneg : 0 ≤ L := by linarith
  have hQXi : (Q:ℝ)^4*(xi⁻¹)^4 ≤
      L^(4*(Cq+Cxi)) :=
    source_original_primitive_two_global_poly_budget434
      Q xi L Cq Cxi hxi hL hQ hX
  calc
    _ ≤ familyCost*((Q:ℝ)^4*(xi⁻¹)^4) := hExpansion
    _ ≤ (L^Cfamily)*(L^(4*(Cq+Cxi))) :=
      mul_le_mul hFamily hQXi
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          (pow_nonneg (inv_nonneg.mpr hxi.le) _))
        (pow_nonneg hLnonneg _)
    _ = L^(Cfamily+4*(Cq+Cxi)) := by rw [pow_add]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeVariableCellBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- For the ACTUAL source03 comparison family, the first and second
global product laws live on DIFFERENT, ν-dependent subtype coordinate
families A and B. This is NOT a common fixed abstract ιA,ιB. -/
noncomputable def sourceOriginalProbeCellA434
    {G : Type} [DecidableEq G] (m : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (ν : SourceOriginalProbePattern434 G m)
    (h : ℝ) (j : ℤ) : ℝ :=
  sourceOriginalActualCellProbability434
    (fun z : ν.1 => P z.val.1)
    (fun z : ν.1 => sourcePrimeSharedAtom434 (V z.val.1)) h j

noncomputable def sourceOriginalProbeCellB434
    {G : Type} [DecidableEq G] (m : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (ν : SourceOriginalProbePattern434 G m)
    (h : ℝ) (j : ℤ) : ℝ :=
  sourceOriginalActualCellProbability434
    (fun z : ν.2 => P z.val.1)
    (fun z : ν.2 => sourcePrimeSharedAtom434 (V z.val.1)) h j

/-- No external family-budget hypothesis: each source03 comparison
cost uses the ACTUAL probability of both independently freed blocks,
with real 1/(p*Vg) atoms, all primitive conductors 1..Q, and its
TRUE original pattern-dependent sets of labelled coordinates.
For each ν, the total character/cell coefficient mass is controlled,
then summed over the exactly constructed original probe family. -/
theorem source_original_probe_variable_cell_family_budget434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVpos : ∀ g,0 < V g)
    (hPrime : ∀ g p,p ∈ P g → p.Prime)
    (JA JB : SourceOriginalProbePattern434 G m → Finset ℤ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∀ j ∈ JA ν,xi ≤ sourceOriginalProbeCellA434 m P V ν (hA ν) j)
    (hMassB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∀ j ∈ JB ν,xi ≤ sourceOriginalProbeCellB434 m P V ν (hB ν) j) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∑ ja ∈ JA ν,
        ∑ _ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
          ∑ jb ∈ JB ν,
            ∑ _cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
              sourceOriginalTwoCellCoefficient434
                (sourceOriginalProbeCellA434 m P V ν (hA ν))
                (sourceOriginalProbeCellB434 m P V ν (hB ν))
                ja jb) ≤
      (2 ^ (m*(blockA.card+blockB.card)):ℝ) *
        ((Q:ℝ)^4*(xi⁻¹)^4) := by
  let patterns := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let K : ℝ := (Q:ℝ)^4*(xi⁻¹)^4
  have hOne (ν : SourceOriginalProbePattern434 G m)
      (hν : ν ∈ patterns) :
      (∑ ja ∈ JA ν,
        ∑ _ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
          ∑ jb ∈ JB ν,
            ∑ _cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
              sourceOriginalTwoCellCoefficient434
                (sourceOriginalProbeCellA434 m P V ν (hA ν))
                (sourceOriginalProbeCellB434 m P V ν (hB ν))
                ja jb) ≤ K := by
    change _ ≤ ((Q:ℝ)^4)*(xi⁻¹)^4
    exact source_original_actual_primitive_two_global_mass434
      (fun z : ν.1 => P z.val.1) (fun z : ν.2 => P z.val.1)
      (fun z : ν.1 => V z.val.1) (fun z : ν.2 => V z.val.1)
      (fun z => hV z.val.1) (fun z => hV z.val.1)
      (fun z => hVpos z.val.1) (fun z => hVpos z.val.1)
      (fun z p hp => hPrime z.val.1 p hp)
      (fun z p hp => hPrime z.val.1 p hp)
      (JA ν) (JB ν) (hA ν) (hB ν) (hhA ν hν) (hhB ν hν)
      Q xi hxi (hMassA ν hν) (hMassB ν hν)
  have hCardNat :=
    source_original_two_block_probe_pattern_card434 blockA blockB m
  have hCard :
      (patterns.card:ℝ) ≤ (2 ^ (m*(blockA.card+blockB.card)):ℝ) := by
    exact_mod_cast hCardNat
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  calc
    _ ≤ ∑ ν ∈ patterns,K := by
      apply Finset.sum_le_sum
      intro ν hν
      exact hOne ν hν
    _ = (patterns.card:ℝ)*K := by simp [Finset.sum_const]
    _ ≤ (2 ^ (m*(blockA.card+blockB.card)):ℝ)*K :=
      mul_le_mul_of_nonneg_right hCard hK
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeConcreteKnu -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The LITERAL signed source03 Knu: two independent global
primitive-conductor/log-cell kernels, acting respectively on
DA and the actual TARGET free-probe product XA and DB and the
actual SOURCE free-probe product XB. Pattern sign is
-(-1)^(|A|+|B|). Source/target mark type varies with ν. -/
noncomputable def sourceOriginalProbeConcreteKnu434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) : ℂ :=
  sourceAuxiliaryOriginalComparisonKnu434
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)
    (sourceOriginalActualPrimitiveGlobalKernel434 Q JA hA
      (sourceOriginalProbeCellA434 m P V ν hA))
    (sourceOriginalActualPrimitiveGlobalKernel434 Q JB hB
      (sourceOriginalProbeCellB434 m P V ν hB))
    (sourceOriginalProbeDA434 m ν a)
    (sourceOriginalProbeDB434 m ν a)
    (ν.1.card+ν.2.card)
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν)
    (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν)
    source target

/-- Exact identification with the FULL original ordered physical
source/target lists after assembly with SAME shared labels.
No replacing the source03 comparison coefficient by a positive
majorant; the original inclusion-exclusion sign remains. -/
theorem source_original_probe_concrete_full_Knu_identity434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (shared : ∀ g, sourceOriginalProbeSharedSlots434 J ell m hmJ ν g → ℕ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    sourceOriginalProbeConcreteKnu434 J ell m hmJ ν Q JA JB hA hB
      P V a source target =
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalProbeDA434 m ν a)
      (sourceOriginalProbeOriginalTargetX434 J ell m hmJ ν
        (sourceOriginalProbeAssembledFull434 J ell m hmJ ν shared target))
      (sourceOriginalProbeDB434 m ν a)
      (sourceOriginalProbeOriginalSourceX434 J ell m hmJ ν
        (sourceOriginalProbeAssembledFull434 J ell m hmJ ν shared source))
      (ν.1.card+ν.2.card) := by
  rw [source_original_probe_target_product_identification434,
      source_original_probe_source_product_identification434]
  rfl

/-- Sum of the ACTUAL physical source03 Knu coefficients for EVERY
source residual comparison pattern, with its own varying auxiliary
coordinate type and exact source/target free slot complement.
This is a literal application of the previously verified family
bound, NOT a new hypothesis on Σν sup|Kν|. -/
theorem source_original_probe_concrete_physical_Knu_family_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (P : G → Finset ℕ) (V : G → ℝ)
    (JA JB : SourceOriginalProbePattern434 G m → Finset ℤ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (hMassA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∀ j ∈ JA ν, xi ≤ sourceOriginalProbeCellA434 m P V ν (hA ν) j)
    (hMassB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∀ j ∈ JB ν, xi ≤ sourceOriginalProbeCellB434 m P V ν (hB ν) j)
    (a : (ν : SourceOriginalProbePattern434 G m) →
      SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (source target : (ν : SourceOriginalProbePattern434 G m) →
      ∀ g, Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ‖sourceOriginalProbeConcreteKnu434
        J ell m hmJ ν Q (JA ν) (JB ν) (hA ν) (hB ν)
        P V (a ν) (source ν) (target ν)‖) ≤
    (2 ^ (m*(blockA.card+blockB.card)):ℝ) *
      ((Q:ℝ)^4*(xi⁻¹)^2) := by
  have hh := source_original_probe_actual_physical_family_bound434
    blockA blockB m Q xi hxi
    (fun ν g => sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g)
    JA JB hA hB hhA hhB
    (fun ν => sourceOriginalProbeCellA434 m P V ν (hA ν))
    (fun ν => sourceOriginalProbeCellB434 m P V ν (hB ν))
    hMassA hMassB
    (fun ν => sourceOriginalProbeDA434 m ν (a ν))
    (fun ν => sourceOriginalProbeDB434 m ν (a ν))
    (fun ν => ν.1.card+ν.2.card)
    (fun ν => sourceOriginalProbeFreeTargetX434 J ell m hmJ ν)
    (fun ν => sourceOriginalProbeFreeSourceX434 J ell m hmJ ν)
    source target
  exact hh
end Green64Analytic.CorrelationSquare

end

/-! ## PrimitiveRank -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A literal half-open source cell times its genuine positive-conductor
Dirichlet character. No inverse cell mass is absorbed in this unit factor. -/
def parityCellCharacter434 {Q : ℕ} (h : ℝ) (j : ℤ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) (n : ℕ) : ℂ :=
  if sourceOriginalLiteralLogCell434 h j n then c.2 (n:ZMod (c.1.val+1)) else 0

theorem parity_cell_character_norm434 {Q : ℕ} (h : ℝ) (j : ℤ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) (n : ℕ) :
    ‖parityCellCharacter434 h j c n‖ ≤ 1 := by
  unfold parityCellCharacter434
  split_ifs
  · exact c.2.norm_le_one _
  · norm_num

theorem parity_character_cell_atom_factor434 {Q : ℕ} (h : ℝ) (j : ℤ)
    (mass : ℤ → ℝ)
    (c : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) (D X : ℕ) :
    sourceOriginalCharacterCellAtom434 (sourceOriginalLiteralLogCell434 h) mass
      (fun c n => c.2 (n:ZMod (c.1.val+1))) j c D X =
    (mass j:ℂ)⁻¹ * star (parityCellCharacter434 h j c D) * parityCellCharacter434 h j c X := by
  by_cases hD : sourceOriginalLiteralLogCell434 h j D <;>
    by_cases hX : sourceOriginalLiteralLogCell434 h j X <;>
    simp [sourceOriginalCharacterCellAtom434,parityCellCharacter434,hD,hX]

/-- The complete coefficient outside the two marked endpoints: original
inclusion-exclusion sign, BOTH inverse harmonic cell masses, and the two
separate auxiliary-product factors. -/
def parityPrimitiveRankScalar434 {Q : ℕ} (hA hB : ℝ) (ja jb : ℤ)
    (massA massB : ℤ → ℝ)
    (ca cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) (DA DB r : ℕ) : ℂ :=
  -((-1:ℂ)^r) * (sourceOriginalTwoCellCoefficient434 massA massB ja jb:ℂ) *
    star (parityCellCharacter434 hA ja ca DA) * star (parityCellCharacter434 hB jb cb DB)

/-- The first marked coefficient is conjugated before the first endpoint
is conjugated by the correlation. Both coefficients are independent of
auxiliary labels and their products. -/
def parityFirstRankMark434 {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    {Q : ℕ} (hB : ℝ) (jb : ℤ)
    (cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (a : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) : ℂ :=
  star (parityCellCharacter434 hB jb cb (sourceOriginalProbeFreeSourceX434 J ell m hmJ nu a))

def paritySecondRankMark434 {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    {Q : ℕ} (hA : ℝ) (ja : ℤ)
    (ca : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) : ℂ :=
  parityCellCharacter434 hA ja ca (sourceOriginalProbeFreeTargetX434 J ell m hmJ nu b)

theorem parity_actual_rank_mark_norm434 {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    {Q : ℕ} (hA hB : ℝ) (ja jb : ℤ)
    (ca cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (a : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    ‖parityFirstRankMark434 J ell m hmJ nu hB jb cb a‖ ≤ 1 ∧
    ‖paritySecondRankMark434 J ell m hmJ nu hA ja ca a‖ ≤ 1 := by
  simpa only [parityFirstRankMark434,paritySecondRankMark434,norm_star] using
    And.intro (parity_cell_character_norm434 hB jb cb _)
      (parity_cell_character_norm434 hA ja ca _)

theorem parity_primitive_rank_scalar_bound434 {Q : ℕ} (hA hB : ℝ) (ja jb : ℤ)
    (massA massB : ℤ → ℝ)
    (ca cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) (DA DB r : ℕ)
    (xi : ℝ) (hxi : 0 < xi) (ha : xi ≤ massA ja) (hb : xi ≤ massB jb) :
    ‖parityPrimitiveRankScalar434 hA hB ja jb massA massB ca cb DA DB r‖ ≤ (xi⁻¹)^2 := by
  have hc := source_original_two_cell_coefficient_bound434 massA massB ja jb xi hxi ha hb
  have hA := parity_cell_character_norm434 hA ja ca DA
  have hB := parity_cell_character_norm434 hB jb cb DB
  simp only [parityPrimitiveRankScalar434,norm_mul,norm_neg,norm_pow,norm_one,one_pow,
    one_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc.1]
  calc
    _ ≤ sourceOriginalTwoCellCoefficient434 massA massB ja jb * 1 * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA hc.1) hB (norm_nonneg _)
        (mul_nonneg hc.1 (by norm_num))
    _ ≤ _ := by simpa using hc.2

/-- Exact conjugated rank form of one of the fourfold primitive terms. -/
theorem parity_primitive_term_conjugated_rank434 {Q : ℕ} (hA hB : ℝ) (ja jb : ℤ)
    (massA massB : ℤ → ℝ)
    (ca cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1)) (DA XA DB XB r : ℕ) :
    -((-1:ℂ)^r) * sourceOriginalCharacterCellAtom434
      (sourceOriginalLiteralLogCell434 hA) massA
      (fun c n => c.2 (n:ZMod (c.1.val+1))) ja ca DA XA *
      sourceOriginalCharacterCellAtom434 (sourceOriginalLiteralLogCell434 hB) massB
      (fun c n => c.2 (n:ZMod (c.1.val+1))) jb cb DB XB =
    parityPrimitiveRankScalar434 hA hB ja jb massA massB ca cb DA DB r *
      star (star (parityCellCharacter434 hB jb cb XB)) * parityCellCharacter434 hA ja ca XA := by
  rw [parity_character_cell_atom_factor434,parity_character_cell_atom_factor434]
  simp only [parityPrimitiveRankScalar434,sourceOriginalTwoCellCoefficient434,
    Complex.ofReal_mul,Complex.ofReal_inv,star_star]
  ring

/-- The literal original Knu, before free-ban removal, has exactly TWO
GLOBAL cell/primitive-character expansions. All rank endpoint weights
are independent of aux; only the scalar contains DA and DB. This theorem
is about the unbanned kernel and does not assert a ban-removal estimate. -/
theorem parity_actual_concrete_Knu_rank_expansion434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (JA JB : Finset ℤ) (hA hB : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceOriginalProbeConcreteKnu434 J ell m hmJ nu Q JA JB hA hB P V aux a b =
      ∑ ja ∈ JA,∑ ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
        ∑ jb ∈ JB,∑ cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
          parityPrimitiveRankScalar434 hA hB ja jb
            (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
            ca cb (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
            (nu.1.card+nu.2.card) *
          star (parityFirstRankMark434 J ell m hmJ nu hB jb cb a) *
          paritySecondRankMark434 J ell m hmJ nu hA ja ca b := by
  change sourceOriginalActualPrimitiveComparisonKernel434 _ _ _ _ _ _ _ _ _ _ _ _ = _
  rw [source_original_actual_primitive_comparison_expand434]
  apply Finset.sum_congr rfl
  intro ja hja
  apply Finset.sum_congr rfl
  intro ca hca
  apply Finset.sum_congr rfl
  intro jb hjb
  apply Finset.sum_congr rfl
  intro cb hcb
  exact parity_primitive_term_conjugated_rank434 _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Actual full ordered marked lists, with both original damping/mass
prefactors, give the conjugated rank endpoint pair without any lost factor. -/
theorem parity_actual_rank_marked_pair434 {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    {Q : ℕ} (hA hB : ℝ) (ja jb : ℤ)
    (ca cb : Σ q : Fin Q, DirichletCharacter ℂ (q.val+1))
    (P : G → Finset ℕ) (V : G → ℝ) (q : ℝ) (w wp : ℕ) :
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    bigMarkPrefactor P t q V w * bigMarkPrefactor P t q V wp *
      (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
        star (parityFirstRankMark434 J ell m hmJ nu hB jb cb a) *
          paritySecondRankMark434 J ell m hmJ nu hA ja ca b) =
    star (actualBigMarkDecoration P t q V (parityFirstRankMark434 J ell m hmJ nu hB jb cb) w) *
      actualBigMarkDecoration P t q V (paritySecondRankMark434 J ell m hmJ nu hA ja ca) wp := by
  exact source_two_marked_tests434 _ _ _ _ _ _ _ _
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceOriginalProbeActualActiveCells -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Every ORIGINAL comparison ν has its own finite active A-cell
family: the TRUE product of its A-labelled primes with 1/(pV_g)
weights; no arbitrary externally supplied JA. -/
noncomputable def sourceOriginalProbeActiveCellsA434
    {G : Type} [DecidableEq G] (m : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (ν : SourceOriginalProbePattern434 G m) (h xi : ℝ) : Finset ℤ :=
  sourceOriginalFiniteActiveLogCells434
    (fun z : ν.1 => P z.val.1)
    (fun z : ν.1 => sourcePrimeSharedAtom434 (V z.val.1)) h xi

/-- Independently, the actual active B-cell family comes from the
separate B-labelled global product under the same true prime law. -/
noncomputable def sourceOriginalProbeActiveCellsB434
    {G : Type} [DecidableEq G] (m : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (ν : SourceOriginalProbePattern434 G m) (h xi : ℝ) : Finset ℤ :=
  sourceOriginalFiniteActiveLogCells434
    (fun z : ν.2 => P z.val.1)
    (fun z : ν.2 => sourcePrimeSharedAtom434 (V z.val.1)) h xi

theorem source_original_probe_active_cell_A_mem_iff434
    {G : Type} [DecidableEq G] (m : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (ν : SourceOriginalProbePattern434 G m)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi) (j : ℤ) :
    j ∈ sourceOriginalProbeActiveCellsA434 m P V ν h xi ↔
      xi ≤ sourceOriginalProbeCellA434 m P V ν h j := by
  exact source_original_finite_active_log_cell_mem_iff434
    (fun z : ν.1 => P z.val.1)
    (fun z : ν.1 => sourcePrimeSharedAtom434 (V z.val.1))
    h xi hh hxi j

theorem source_original_probe_active_cell_B_mem_iff434
    {G : Type} [DecidableEq G] (m : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (ν : SourceOriginalProbePattern434 G m)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi) (j : ℤ) :
    j ∈ sourceOriginalProbeActiveCellsB434 m P V ν h xi ↔
      xi ≤ sourceOriginalProbeCellB434 m P V ν h j := by
  exact source_original_finite_active_log_cell_mem_iff434
    (fun z : ν.2 => P z.val.1)
    (fun z : ν.2 => sourcePrimeSharedAtom434 (V z.val.1))
    h xi hh hxi j

/-- No arbitrary active-cell JA/JB mass hypotheses: they are
constructed canonically, for every variable-size ORIGINAL pattern.
This closes the missing finite-exhaustive source03 four-index
character/cell coefficient budget. -/
theorem source_original_probe_canonical_active_expansion_cost434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m Q : ℕ)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVpos : ∀ g,0 < V g)
    (hPrime : ∀ g p,p ∈ P g → p.Prime)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hA ν)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      0 < hB ν)
    (xi : ℝ) (hxi : 0 < xi) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      ∑ ja ∈ sourceOriginalProbeActiveCellsA434 m P V ν (hA ν) xi,
        ∑ _ca ∈ sourceOriginalActualPrimitiveCharacters434 Q,
          ∑ jb ∈ sourceOriginalProbeActiveCellsB434 m P V ν (hB ν) xi,
            ∑ _cb ∈ sourceOriginalActualPrimitiveCharacters434 Q,
              sourceOriginalTwoCellCoefficient434
                (sourceOriginalProbeCellA434 m P V ν (hA ν))
                (sourceOriginalProbeCellB434 m P V ν (hB ν))
                ja jb) ≤
      (2 ^ (m*(blockA.card+blockB.card)):ℝ)*
        ((Q:ℝ)^4*(xi⁻¹)^4) := by
  apply source_original_probe_variable_cell_family_budget434
    blockA blockB m Q P V hV hVpos hPrime
    (fun ν => sourceOriginalProbeActiveCellsA434 m P V ν (hA ν) xi)
    (fun ν => sourceOriginalProbeActiveCellsB434 m P V ν (hB ν) xi)
    hA hB hhA hhB xi hxi
  · intro ν hν j hj
    exact (source_original_probe_active_cell_A_mem_iff434
      m P V ν (hA ν) xi (hhA ν hν) hxi j).mp hj
  · intro ν hν j hj
    exact (source_original_probe_active_cell_B_mem_iff434
      m P V ν (hB ν) xi (hhB ν hν) hxi j).mp hj
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveCellGramFibre -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Actual source03 finite PRIME-labelled slot type. It retains
the actual source support S_i, avoiding fictitious uniform primes. -/
abbrev SourceOriginalGramPrimeTuple434
    {ι : Type} (S : ι → Finset ℕ) :=
  (i : ι) → {p : ℕ // p ∈ S i}

/-- Genuine product of primes in the original indexed marks. -/
noncomputable def sourceOriginalGramPrimeProduct434
    {ι : Type} [Fintype ι]
    (S : ι → Finset ℕ)
    (a : SourceOriginalGramPrimeTuple434 S) : ℕ :=
  ∏ i : ι, (a i).val

/-- Original REAL prime harmonic probability product law,
including the possibility of repeated prime values. -/
noncomputable def sourceOriginalGramPrimeMass434
    {ι : Type} [Fintype ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (a : SourceOriginalGramPrimeTuple434 S) : ℝ :=
  ∏ i : ι, mu i (a i).val

/-- Literal global log-product CELL with two character values:
the offdiagonal Gram entry of the actual SOURCE03 primitive
character frame, prior to conditioning on the cell mass. -/
noncomputable def sourceOriginalGramCellEntry434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ)
    (χ ψ : ℕ → ℂ) : ℂ :=
  ∑ a : SourceOriginalGramPrimeTuple434 S,
    ((sourceOriginalGramPrimeMass434 S mu a : ℝ) : ℂ) *
      (if sourceOriginalLiteralLogCell434 h j
           (sourceOriginalGramPrimeProduct434 S a)
       then star (χ (sourceOriginalGramPrimeProduct434 S a)) *
           ψ (sourceOriginalGramPrimeProduct434 S a)
       else 0)

/-- Exact globally conditioned Gram entry, after replacing the
two characters by their combined product weight.
NOT an appeal to prime equidistribution. -/
theorem source_original_gram_cell_weight_rewrite434
    {ι : Type} [Fintype ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (j : ℤ)
    (χ ψ : ℕ → ℂ) :
    sourceOriginalGramCellEntry434 S mu h j χ ψ =
    ∑ a : SourceOriginalGramPrimeTuple434 S,
      ((sourceOriginalGramPrimeMass434 S mu a : ℝ) : ℂ) *
      (if sourceOriginalLiteralLogCell434 h j
           (sourceOriginalGramPrimeProduct434 S a)
       then star (χ (sourceOriginalGramPrimeProduct434 S a)) *
           ψ (sourceOriginalGramPrimeProduct434 S a)
       else 0) := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueAuxPrimeSplit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The exact ν-dependent auxiliary source03 BIG prime
tuple indexed by A_ν ⊕ B_ν is canonically the product
of the TWO actual labelled source03 physical Gram prime
tuples. No new support, grouping or factorization
assumption is introduced: both sides are the SAME
original marked finite prime draw. -/
noncomputable def sourceOriginalTrueAuxPrimeSplitEquiv434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) :
    ((i : SourceOriginalProbeAuxIndex434 m ν) →
      {p : ℕ // p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P i}) ≃
    (SourceOriginalGramPrimeTuple434
       (fun i : ν.1 => P i.val.1) ×
     SourceOriginalGramPrimeTuple434
       (fun i : ν.2 => P i.val.1)) :=
  Equiv.sumPiEquivProdPi
    (fun i : SourceOriginalProbeAuxIndex434 m ν =>
      {p : ℕ // p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P i})

/-- The true original auxiliary first BIG-block product DA
is EXACTLY the integer product of the first physical
labelled prime tuple after the canonical split. -/
theorem source_original_true_aux_split_DA434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (a : (i : SourceOriginalProbeAuxIndex434 m ν) →
      {p : ℕ // p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P i}) :
    sourceOriginalProbeDA434 m ν (fun i => (a i).val) =
      sourceOriginalGramPrimeProduct434
        (fun i : ν.1 => P i.val.1)
        (sourceOriginalTrueAuxPrimeSplitEquiv434 m ν P a).1 := by
  rfl
/-- The TRUE source auxiliary second BIG-block product DB
is the actual product of B_ν-labelled prime tuple, with
numerical repeated primes preserved. -/
theorem source_original_true_aux_split_DB434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (a : (i : SourceOriginalProbeAuxIndex434 m ν) →
      {p : ℕ // p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P i}) :
    sourceOriginalProbeDB434 m ν (fun i => (a i).val) =
      sourceOriginalGramPrimeProduct434
        (fun i : ν.2 => P i.val.1)
        (sourceOriginalTrueAuxPrimeSplitEquiv434 m ν P a).2 := by
  rfl

/-- The literal original atom 1/(p V_g) agrees with the
finite Gram law (1/p)/V_g over the same source support
for all numerical p, including zeros. -/
theorem source_original_true_aux_atom_mu434
    (p : ℕ) (V : ℝ) :
    sourcePrimeSharedAtom434 V p = (1/(p:ℝ))/V := by
  simp only [sourcePrimeSharedAtom434, div_eq_mul_inv,
    one_div, mul_inv_rev]
  ring
/-- SOURCE03 full auxiliary harmonic product mass factors
EXACTLY as the TWO physical Gram product masses. It is
the same law; the two block measures are not proxies
or independent new replacements. -/
theorem source_original_true_aux_split_mass434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : (i : SourceOriginalProbeAuxIndex434 m ν) →
      {p : ℕ // p ∈ sourceOriginalProbeAuxPrimeSets434 m ν P i}) :
    sourceSharedLaw434
      (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m ν V i))
      (fun i => (a i).val) =
    sourceOriginalGramPrimeMass434
      (fun i : ν.1 => P i.val.1)
      (fun i p => (1/(p:ℝ))/(V i.val.1))
      (sourceOriginalTrueAuxPrimeSplitEquiv434 m ν P a).1 *
    sourceOriginalGramPrimeMass434
      (fun i : ν.2 => P i.val.1)
      (fun i p => (1/(p:ℝ))/(V i.val.1))
      (sourceOriginalTrueAuxPrimeSplitEquiv434 m ν P a).2 := by
  classical
  simp only [sourceSharedLaw434,
    sourceOriginalGramPrimeMass434,
    SourceOriginalProbeAuxIndex434,
    Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    change sourcePrimeSharedAtom434 (V i.val.1)
      ((a (Sum.inl i)).val) =
      (1/(((a (Sum.inl i)).val):ℝ))/(V i.val.1)
    exact source_original_true_aux_atom_mu434 _ _
  · apply Finset.prod_congr rfl
    intro i hi
    change sourcePrimeSharedAtom434 (V i.val.1)
      ((a (Sum.inr i)).val) =
      (1/(((a (Sum.inr i)).val):ℝ))/(V i.val.1)
    exact source_original_true_aux_atom_mu434 _ _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuMellinMinorPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- In the ACTUAL source03 two-BIG-block prime-tuple physical
Fourier sum, the source Mellin factor (D_A D_B)^(i ζ)
splits into two independent UNIT-MODULUS endpoint twists.
The original -k θ Fourier frequency, source/target indices,
independently labelled prime tuples, arbitrary complex
mark-dependent tests and original ν inclusion-exclusion sign
are preserved. This is an EXACT arithmetic identity, and
does not itself assert an off-own-arc C6 bound. -/
theorem source_original_true_nu_mellin_fourier_factor434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (hPrime : ∀ g, ∀ p ∈ P g, p.Prime)
    (ζ theta : ℝ) (k : ℤ)
    (wA fA : SourceOriginalGramPrimeTuple434
      (fun z : ν.1 => P z.val.1) → ℂ)
    (wB fB : SourceOriginalGramPrimeTuple434
      (fun z : ν.2 => P z.val.1) → ℂ) :
    let SA : ν.1 → Finset ℕ := fun z => P z.val.1
    let SB : ν.2 → Finset ℕ := fun z => P z.val.1
    let pa := sourceOriginalGramPrimeProduct434 SA
    let pb := sourceOriginalGramPrimeProduct434 SB
    let sigma : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
    sigma * (∑ ab :
      SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB,
        (wA ab.1 * wB ab.2) * fA ab.1 * fB ab.2 *
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta) (((pa ab.1 * pb ab.2:ℕ):ℤ)) *
        sourceOriginalPureMellinPhase434 ζ
          (pa ab.1*pb ab.2)) =
    sigma * (∑ ab :
      SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB,
        (wA ab.1 * wB ab.2) *
        (fA ab.1*sourceOriginalPureMellinPhase434 ζ (pa ab.1)) *
        (fB ab.2*sourceOriginalPureMellinPhase434 ζ (pb ab.2)) *
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta) (((pa ab.1 * pb ab.2:ℕ):ℤ))) := by
  classical
  dsimp only
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  have hPA (a : SourceOriginalGramPrimeTuple434 SA) :
      0 < pa a := by
    unfold pa sourceOriginalGramPrimeProduct434
    apply Finset.prod_pos
    intro z hz
    exact (hPrime z.val.1 (a z).val (a z).property).pos
  have hPB (a : SourceOriginalGramPrimeTuple434 SB) :
      0 < pb a := by
    unfold pb sourceOriginalGramPrimeProduct434
    apply Finset.prod_pos
    intro z hz
    exact (hPrime z.val.1 (a z).val (a z).property).pos
  congr 1
  apply Finset.sum_congr rfl
  intro ab hab
  rw [source_original_pure_mellin_product_factor434
      ζ (pa ab.1) (pb ab.2) (hPA ab.1) (hPB ab.2)]
  ring

/-- The same literal source03 ν prime-product Mellin twists
are exactly isometries on both physical BIG endpoint energies.
This is true for arbitrary complex tests, not only |f|<=1. -/
theorem source_original_true_nu_mellin_two_energy_eq434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (muA : SourceOriginalGramPrimeTuple434
      (fun z : ν.1 => P z.val.1) → ℝ)
    (muB : SourceOriginalGramPrimeTuple434
      (fun z : ν.2 => P z.val.1) → ℝ)
    (ζ : ℝ)
    (fA : SourceOriginalGramPrimeTuple434
      (fun z : ν.1 => P z.val.1) → ℂ)
    (fB : SourceOriginalGramPrimeTuple434
      (fun z : ν.2 => P z.val.1) → ℂ) :
    (∑ a, muA a * ‖fA a *
      sourceOriginalPureMellinPhase434 ζ
       (sourceOriginalGramPrimeProduct434
         (fun z : ν.1 => P z.val.1) a)‖^2) =
    (∑ a, muA a*‖fA a‖^2) ∧
    (∑ b, muB b * ‖fB b *
      sourceOriginalPureMellinPhase434 ζ
       (sourceOriginalGramPrimeProduct434
         (fun z : ν.2 => P z.val.1) b)‖^2) =
    (∑ b, muB b*‖fB b‖^2) := by
  constructor
  · apply Finset.sum_congr rfl
    intro a ha
    rw [norm_mul, source_original_pure_mellin_phase_norm_one434]
    simp
  · apply Finset.sum_congr rfl
    intro b hb
    rw [norm_mul, source_original_pure_mellin_phase_norm_one434]
    simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalFourierMinorPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The EXACT SOURCE03 physical minor Fourier bilinear
sum is unchanged when writing the C6 integer additive
phase as the genuine shifted-correlation frequency
-k*theta rather than its Dirichlet approximation
a/r+beta. Works for TRUE independently labelled prime
tuples, arbitrary support sets, arbitrary mark-dependent
complex endpoint weights, actual harmonic probabilities,
and arbitrary product-window masks. It never assumes
independence of the test from its tuple.
This is a literal PHASE identity, not a minor saving. -/
theorem source_original_physical_minor_fourier_phase_identity434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (AW BW : Finset ℕ)
    (theta : ℝ) (k a : ℤ) (r : ℕ) (beta : ℝ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta) :
    (∑ vA : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA vA ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
        (∑ vB : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB vB ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
              Green64SourceC6.integerPhase
                (((a:ℝ)/(r:ℝ)+beta)*
                  ((sourceOriginalGramPrimeProduct434 SB vB:ℕ):ℝ))
                ((sourceOriginalGramPrimeProduct434 SA vA:ℕ):ℤ)
          else 0)
      else 0) =
    (∑ vA : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA vA ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
        (∑ vB : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB vB ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
              Green64SourceC6.integerPhase
                (-(k:ℝ)*theta)
                (((sourceOriginalGramPrimeProduct434 SA vA *
                  sourceOriginalGramPrimeProduct434 SB vB):ℕ):ℤ)
          else 0)
      else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro vA hvA
  by_cases hA : sourceOriginalGramPrimeProduct434 SA vA ∈ AW
  · simp only [if_pos hA]
    congr 1
    apply Finset.sum_congr rfl
    intro vB hvB
    by_cases hB : sourceOriginalGramPrimeProduct434 SB vB ∈ BW
    · simp only [if_pos hB]
      rw [source_original_C6_integer_phase_dirichlet_exact434
        theta k a r beta
        (sourceOriginalGramPrimeProduct434 SA vA)
        (sourceOriginalGramPrimeProduct434 SB vB)
        hApprox]
    · simp only [if_neg hB]
  · simp only [if_neg hA]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalProductAtomPushforward -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The TRUE original physical source03 product-atom mass:
push forward the actual independently labelled product-prime
harmonic law through the TRUE integer product D(p).
Distinct prime LABELS can have the same numerical prime
value and are never merged before taking the weighted sum.
This is not a synthetic uniform integer law. -/
noncomputable def sourceOriginalPhysicalProductAtom434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (n : ℕ) : ℝ :=
  ∑ a : SourceOriginalGramPrimeTuple434 S,
    if sourceOriginalGramPrimeProduct434 S a = n
    then sourceOriginalGramPrimeMass434 S mu a else 0

/-- The actual attainable product integers of original
physical labelled prime supports. No fictitious integers,
and no requirement of numerical distinctness. -/
noncomputable def sourceOriginalPhysicalProductAtomSupport434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) : Finset ℕ :=
  (Finset.univ : Finset (SourceOriginalGramPrimeTuple434 S)).image
    (sourceOriginalGramPrimeProduct434 S)

/-- Exact SOURCE03 physical-to-product-atom law, for EVERY
arbitrary complex-valued observable depending on the TRUE
integer product of all selected prime marks. The conditional
product-atom mass is computed from the ORIGINAL physical
harmonic law. This is the essential arithmetic reindexing
before any q>Q minor-arc estimate on integer product sums.
No assumptions on support disjointness, interval geometry
or the test, since this step is an exact finite identity. -/
theorem source_original_physical_product_atom_pushforward434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (F : ℕ → ℂ) :
    (∑ a : SourceOriginalGramPrimeTuple434 S,
      (sourceOriginalGramPrimeMass434 S mu a:ℂ) *
        F (sourceOriginalGramPrimeProduct434 S a)) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      (sourceOriginalPhysicalProductAtom434 S mu n:ℂ)*F n := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let T : Finset ℕ := sourceOriginalPhysicalProductAtomSupport434 S
  have hmem (a : X) : prod a ∈ T := by
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hChoose (a : X) :
      (∑ n ∈ T,
        if prod a=n then (w a:ℂ)*F n else 0) =
      (w a:ℂ)*F (prod a) := by
    simp [hmem a]
  have hAtom (n : ℕ) :
      (sourceOriginalPhysicalProductAtom434 S mu n:ℂ)*F n =
      ∑ a : X, if prod a=n then (w a:ℂ)*F n else 0 := by
    unfold sourceOriginalPhysicalProductAtom434
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    change ((((if prod a=n then w a else 0):ℝ):ℂ)*F n) =
      (if prod a=n then (w a:ℂ)*F n else 0)
    split_ifs <;> simp
  calc
    _ = ∑ a : X, ∑ n ∈ T,
         if prod a=n then (w a:ℂ)*F n else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (hChoose a).symm
    _ = ∑ n ∈ T, ∑ a : X,
         if prod a=n then (w a:ℂ)*F n else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ T,
       (sourceOriginalPhysicalProductAtom434 S mu n:ℂ)*F n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hAtom n).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomRealPushforward -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact REAL-valued pushforward of the original labelled-prime
harmonic product law onto its actual attainable integer products.
No extra factor counting prime tuples: all physical labels are
integrated out with the same source03 masses. -/
theorem source_original_physical_atom_real_pushforward434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (F : ℕ → ℝ) :
    (∑ a : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu a *
        F (sourceOriginalGramPrimeProduct434 S a)) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      sourceOriginalPhysicalProductAtom434 S mu n * F n := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  let T : Finset ℕ := sourceOriginalPhysicalProductAtomSupport434 S
  have hmem (a : X) : prod a ∈ T :=
    Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hPick (a : X) :
      (∑ n ∈ T, if prod a=n then w a*F n else 0) =
        w a*F (prod a) := by
    simp [hmem a]
  have hAtom (n : ℕ) :
      sourceOriginalPhysicalProductAtom434 S mu n *F n =
        ∑ a : X, if prod a=n then w a*F n else 0 := by
    change (∑ a : X, if prod a=n then w a else 0)*F n =
        ∑ a : X, if prod a=n then w a*F n else 0
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : prod a=n
    · simp [h]
    · simp [h]
  calc
    _ = ∑ a : X, ∑ n ∈ T,
          if prod a=n then w a*F n else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact (hPick a).symm
    _ = ∑ n ∈ T, ∑ a : X,
          if prod a=n then w a*F n else 0 := Finset.sum_comm
    _ = ∑ n ∈ T,
          sourceOriginalPhysicalProductAtom434 S mu n*F n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (hAtom n).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalProductAtomCoefficient -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The genuine SOURCE03 coefficient obtained by collapsing a
bounded complex physical prime-tuple test onto an integer-product
atom. Source labels, real harmonic prime weights and repeated
numerical prime values remain unchanged. -/
noncomputable def sourceOriginalPhysicalProductAtomCoefficient434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (n : ℕ) : ℂ :=
  ∑ a : SourceOriginalGramPrimeTuple434 S,
    if sourceOriginalGramPrimeProduct434 S a=n
    then (sourceOriginalGramPrimeMass434 S mu a:ℂ)*f a else 0

/-- Nonnegative original source product atom masses: nothing
about disjoint prime supports or new integer normalization
is assumed. -/
theorem source_original_physical_product_atom_nonneg434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (n : ℕ) :
    0 ≤ sourceOriginalPhysicalProductAtom434 S mu n := by
  unfold sourceOriginalPhysicalProductAtom434
  apply Finset.sum_nonneg
  intro a ha
  split_ifs with h
  · unfold sourceOriginalGramPrimeMass434
    apply Finset.prod_nonneg
    intro i hi
    exact hmu i (a i).val (a i).property
  · exact le_refl _

/-- The exact physical-to-integer minor-arc coefficient
is dominated by the TRUE SOURCE03 product-atom probability
when the original complex endpoint multiplier has norm ≤1.
This permits using product-atom minor-circle estimates
without treating a mark-dependent multiplier as independent
of the prime factorization. Note: an arbitrary L² test need
NOT have this unit supnorm, and is not covered by this lemma. -/
theorem source_original_physical_product_atom_coefficient_bound434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (hf : ∀ a, ‖f a‖ ≤ 1)
    (n : ℕ) :
    ‖sourceOriginalPhysicalProductAtomCoefficient434 S mu f n‖ ≤
      sourceOriginalPhysicalProductAtom434 S mu n := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  have hw (a : X) : 0 ≤ w a := by
    dsimp [w,sourceOriginalGramPrimeMass434]
    apply Finset.prod_nonneg
    intro i hi
    exact hmu i (a i).val (a i).property
  have hBound (a : X) :
      ‖(if prod a=n then (w a:ℂ)*f a else 0)‖ ≤
        (if prod a=n then w a else 0) := by
    by_cases heq : prod a=n
    · simp only [if_pos heq, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (hw a)]
      exact (mul_le_mul_of_nonneg_left (hf a) (hw a)).trans_eq (mul_one _)
    · simp [heq]
  unfold sourceOriginalPhysicalProductAtomCoefficient434
    sourceOriginalPhysicalProductAtom434
  change ‖∑ a : X,
    (if prod a=n then (w a:ℂ)*f a else 0)‖ ≤
    ∑ a : X, if prod a=n then w a else 0
  calc
    _ ≤ ∑ a : X, ‖if prod a=n then (w a:ℂ)*f a else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a : X, if prod a=n then w a else 0 :=
      Finset.sum_le_sum (fun a ha => hBound a)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomL2Coefficient -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The TRUE labelled-prime product-atom coefficient of an
ARBITRARY complex physical L² test is not generally
pointwise ≤ the atom probability. Its correct quantitative
bound is Hilbertian:
  |c(n)|² ≤ atom_mass(n) * full_physical_L²_energy.
This original SOURCE03 inequality is proved using the
actual nonnegative coordinate-dependent harmonic prime law.
No unit-supnorm hypothesis on the source/target test, no
conditional independence assumption and no fake uniform
integer product distribution. It identifies exactly the
normalization loss that must be handled when applying the
existing q>Q product-atom minor-arc bound to L² tests. -/
theorem source_original_physical_product_atom_L2_coefficient_bound434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (n : ℕ) :
    ‖sourceOriginalPhysicalProductAtomCoefficient434 S mu f n‖^2 ≤
    sourceOriginalPhysicalProductAtom434 S mu n *
      (∑ a : SourceOriginalGramPrimeTuple434 S,
         sourceOriginalGramPrimeMass434 S mu a * ‖f a‖^2) := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let event : X → Prop := fun a => prod a=n
  have hw (a : X) : 0 ≤ w a := by
    dsimp [w,sourceOriginalGramPrimeMass434]
    apply Finset.prod_nonneg
    intro i hi
    exact hmu i (a i).val (a i).property
  have hTerm (a : X) :
      ‖if event a then (w a:ℂ)*f a else 0‖ ≤
        w a*(if event a then ‖f a‖ else 0) := by
    by_cases h : event a
    · simp only [if_pos h, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (hw a)]
      rfl
    · simp [h]
  have hN : ‖sourceOriginalPhysicalProductAtomCoefficient434
      S mu f n‖ ≤ (∑ a : X, w a*(if event a then ‖f a‖ else 0)) := by
    unfold sourceOriginalPhysicalProductAtomCoefficient434
    change ‖∑ a : X, if event a then (w a:ℂ)*f a else 0‖ ≤
      (∑ a : X, w a*(if event a then ‖f a‖ else 0))
    calc
      _ ≤ ∑ a : X,
          ‖if event a then (w a:ℂ)*f a else 0‖ :=
        norm_sum_le _ _
      _ ≤ (∑ a : X, w a*(if event a then ‖f a‖ else 0)) :=
        Finset.sum_le_sum (fun a ha => hTerm a)
  have hAtom :
      (∑ a : X, w a*(if event a then (1:ℝ) else 0)) =
      sourceOriginalPhysicalProductAtom434 S mu n := by
    unfold sourceOriginalPhysicalProductAtom434
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : event a
    · simp [event,prod,w,h]
    · simp [event,prod,w,h]
  have hSchur := source_original_finite_rare_event_CS434
    w f event hw
  have hSchurFinal :
      (∑ a : X, w a*(if event a then ‖f a‖ else 0))^2 ≤
        sourceOriginalPhysicalProductAtom434 S mu n *
        (∑ a : X, w a*‖f a‖^2) := by
    calc
      _ ≤ (∑ a : X, w a*
             (if event a then (1:ℝ) else 0)) *
           (∑ a : X, w a*‖f a‖^2) := by
        convert hSchur using 1
        apply congrArg (fun z : ℝ => z^2)
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : event a <;> simp [h]
        apply congrArg
          (fun z : ℝ => z*(∑ x : X, w x*‖f x‖^2))
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : event a <;> simp [h]
      _ = _ :=
         congrArg (fun z : ℝ =>
           z * (∑ a : X, w a*‖f a‖^2)) hAtom
  calc
    _ ≤ (∑ a : X, w a*(if event a then ‖f a‖ else 0))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hN 2
    _ ≤ _ := hSchurFinal
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomFibreEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- SHARP true source03 physical product-atom L2 coefficient bound:
|c(n)|^2 <= mass(n) * ENERGY_OF_THE_FIBRE(n), not only the full
endpoint energy. Entirely arbitrary mark-dependent complex f;
the product fibres are literal inverse images of the integer
product of original independently labelled prime marks.
No unit-supnorm or fake uniform integer-product law. Crucially,
because fibres partition physical marks, this bound can later
be summed without multiplying by the number of attainable
products; exactly what original q>Q minor arc needs. -/
theorem source_original_physical_product_atom_fibre_energy434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (n : ℕ) :
    ‖sourceOriginalPhysicalProductAtomCoefficient434 S mu f n‖^2 ≤
    sourceOriginalPhysicalProductAtom434 S mu n *
      (∑ a : SourceOriginalGramPrimeTuple434 S,
        if sourceOriginalGramPrimeProduct434 S a = n then
          sourceOriginalGramPrimeMass434 S mu a * ‖f a‖^2
        else 0) := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let event : X → Prop := fun a =>
    sourceOriginalGramPrimeProduct434 S a = n
  let g : X → ℂ := fun a => if event a then f a else 0
  have hCoeff :
      sourceOriginalPhysicalProductAtomCoefficient434 S mu g n =
        sourceOriginalPhysicalProductAtomCoefficient434 S mu f n := by
    unfold sourceOriginalPhysicalProductAtomCoefficient434
    apply Finset.sum_congr rfl
    intro a ha
    by_cases he : event a
    · simp [g, event, he]
    · simp [g, event, he]
  have hEnergy :
      (∑ a : X,
        sourceOriginalGramPrimeMass434 S mu a * ‖g a‖^2) =
      (∑ a : X,
        if sourceOriginalGramPrimeProduct434 S a = n then
          sourceOriginalGramPrimeMass434 S mu a * ‖f a‖^2
        else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases he : event a
    · simp [g, event, he]
    · simp [g, event, he]
  have hb := source_original_physical_product_atom_L2_coefficient_bound434
      S mu hmu g n
  rw [hCoeff] at hb
  calc
    _ ≤ sourceOriginalPhysicalProductAtom434 S mu n *
         (∑ a : X,
           sourceOriginalGramPrimeMass434 S mu a * ‖g a‖^2) := hb
    _ = _ := by rw [hEnergy]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomEnergyPartition -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact Hilbert L2 energy partition over the GENUINE
attainable integer products of original source03 physical
labelled prime tuples. The same integer n can arise from
many distinct prime-label configurations; those are all
included in its fibre with their true harmonic weights.
No prime-product support-size multiplier, and no synthetic
uniform integer-product distribution. -/
theorem source_original_physical_atom_energy_partition434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ) :
    (∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      ∑ a : SourceOriginalGramPrimeTuple434 S,
         if sourceOriginalGramPrimeProduct434 S a = n then
           sourceOriginalGramPrimeMass434 S mu a * ‖f a‖^2
         else 0) =
    ∑ a : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu a * ‖f a‖^2 := by
  classical
  exact source_original_finite_dyad_energy_partition434
    (sourceOriginalPhysicalProductAtomSupport434 S)
    (sourceOriginalGramPrimeProduct434 S)
    (fun a => Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    (sourceOriginalGramPrimeMass434 S mu) f
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomL2Disintegration -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The SOURCE03 physical-to-integer-product transformation is
an L² CONTRACTION in its natural atom-weighted Hilbert norm,
including exact handling of zero-mass atoms.
For arbitrary complex mark-dependent f define
c(n)=E_phys[1_(D=n)*f] and original atom μ(n)=Pr[D=n].
Then Σ_{true attainable n, μ(n)>0}|c(n)|²/μ(n)
     <= E_phys |f|².
Unlike the crude C209 pointwise bound, this loses NO factor
equal to the number of attainable integer products. It
is the correct coefficient space for applying a genuine
arithmetic q>Q minor-arc bilinear estimate to physical
L² tests, with repeated numerical primes and all original
harmonic product weights preserved. -/
theorem source_original_physical_product_atom_L2_disintegration434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ) :
    (∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      if sourceOriginalPhysicalProductAtom434 S mu n = 0
      then 0
      else (‖sourceOriginalPhysicalProductAtomCoefficient434 S mu f n‖^2) /
             sourceOriginalPhysicalProductAtom434 S mu n) ≤
    ∑ a : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeMass434 S mu a * ‖f a‖^2 := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let ν : ℕ → ℝ := sourceOriginalPhysicalProductAtom434 S mu
  let c : ℕ → ℂ := sourceOriginalPhysicalProductAtomCoefficient434 S mu f
  let e : ℕ → ℝ := fun n =>
    ∑ a : X,
      if sourceOriginalGramPrimeProduct434 S a = n then
        w a*‖f a‖^2 else 0
  have hw (a : X) : 0 ≤ w a := by
    dsimp [w,sourceOriginalGramPrimeMass434]
    apply Finset.prod_nonneg
    intro i hi
    exact hmu i (a i).val (a i).property
  have hNonneg (n : ℕ) : 0 ≤ e n := by
    dsimp [e]
    apply Finset.sum_nonneg
    intro a ha
    by_cases hx : sourceOriginalGramPrimeProduct434 S a = n
    · simp only [if_pos hx]
      exact mul_nonneg (hw a) (sq_nonneg _)
    · simp [hx]
  have hAtomNonneg (n : ℕ) : 0 ≤ ν n :=
    source_original_physical_product_atom_nonneg434 S mu hmu n
  have hTerm (n : ℕ) :
      (if ν n = 0 then 0 else ‖c n‖^2 / ν n) ≤ e n := by
    by_cases hpos : 0 < ν n
    · have hne : ν n ≠ 0 := ne_of_gt hpos
      simp only [if_neg hne]
      apply (div_le_iff₀ hpos).2
      have hfibre :=
        source_original_physical_product_atom_fibre_energy434
          S mu hmu f n
      change ‖c n‖^2 ≤ ν n * e n at hfibre
      calc
        ‖c n‖^2 ≤ ν n*e n := hfibre
        _ = e n*ν n := mul_comm _ _
    · have heq : ν n = 0 :=
        le_antisymm (le_of_not_gt hpos) (hAtomNonneg n)
      simp only [if_pos heq]
      exact hNonneg n
  calc
    _ ≤ ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
          e n := Finset.sum_le_sum (fun n hn => hTerm n)
    _ = ∑ a : X, w a*‖f a‖^2 := by
      exact source_original_physical_atom_energy_partition434 S mu f
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalAtomWindowL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Arbitrary finite interval / original prime-product atom
window has weighted conditional fibre L² energy at most the
FULL original source03 physical L² energy. An arbitrary
mark-dependent complex f is allowed, and the integer
product need not be injective on tuples. -/
theorem source_original_physical_atom_window_energy_le434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (F : Finset ℕ)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ) :
    (∑ n ∈ F,
      ∑ a : SourceOriginalGramPrimeTuple434 S,
        if sourceOriginalGramPrimeProduct434 S a=n
        then sourceOriginalGramPrimeMass434 S mu a*‖f a‖^2
        else 0) ≤
      (∑ a : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S mu a * ‖f a‖^2) := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let energy : X → ℝ := fun a => w a*‖f a‖^2
  have he (a : X) : 0 ≤ energy a := by
    dsimp [energy,w,sourceOriginalGramPrimeMass434]
    exact mul_nonneg
      (Finset.prod_nonneg (fun i hi => hmu i (a i).val (a i).property))
      (sq_nonneg _)
  have hs (a : X) :
      (∑ n ∈ F, if prod a=n then energy a else 0) =
        (if prod a∈F then energy a else 0) := by
    by_cases ha : prod a∈F
    · simp [ha]
    · simp [ha]
  calc
    _ = ∑ a : X, ∑ n ∈ F,
        if prod a=n then energy a else 0 := by
         exact Finset.sum_comm
    _ = ∑ a : X, if prod a∈F then energy a else 0 := by
         apply Finset.sum_congr rfl
         intro a ha
         exact hs a
    _ ≤ ∑ a : X, energy a := by
         apply Finset.sum_le_sum
         intro a ha
         by_cases hm : prod a∈F
         · simp [hm]
         · simpa [hm] using he a
    _ = _ := rfl

/-- Original PHYSICAL L² endpoint tests have squared integer
atom coefficients obeying a genuine arithmetic-window bound,
provided one has the actual pointwise atom-mass envelope
rho on that window. The theorem *derives* coefficient control
from sharp fibre Cauchy–Schwarz and the true prime product
law; it never assumes the endpoint test is pointwise bounded. -/
theorem source_original_physical_atom_window_coefficient_L2434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hmu : ∀ i p, p ∈ S i → 0 ≤ mu i p)
    (F : Finset ℕ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hAtom : ∀ n∈F,
      sourceOriginalPhysicalProductAtom434 S mu n ≤ rho)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ) :
    (∑ n ∈ F,
      ‖sourceOriginalPhysicalProductAtomCoefficient434 S mu f n‖^2) ≤
      rho*(∑ a : SourceOriginalGramPrimeTuple434 S,
        sourceOriginalGramPrimeMass434 S mu a * ‖f a‖^2) := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let w := sourceOriginalGramPrimeMass434 S mu
  let e : ℕ → ℝ := fun n => ∑ a : X,
    if sourceOriginalGramPrimeProduct434 S a=n
      then w a*‖f a‖^2 else 0
  have he (n : ℕ) : 0 ≤ e n := by
    dsimp [e]
    apply Finset.sum_nonneg
    intro a ha
    by_cases hn : sourceOriginalGramPrimeProduct434 S a=n
    · simp only [if_pos hn]
      exact mul_nonneg
        (by
          unfold w sourceOriginalGramPrimeMass434
          apply Finset.prod_nonneg
          intro i hi
          exact hmu i (a i).val (a i).property)
        (sq_nonneg _)
    · simp [hn]
  have hterm (n : ℕ) (hn : n∈F) :
      ‖sourceOriginalPhysicalProductAtomCoefficient434 S mu f n‖^2
        ≤ rho*e n := by
    have hC := source_original_physical_product_atom_fibre_energy434
      S mu hmu f n
    change _ ≤ sourceOriginalPhysicalProductAtom434 S mu n *e n at hC
    exact hC.trans (mul_le_mul_of_nonneg_right (hAtom n hn) (he n))
  calc
    _ ≤ ∑ n ∈ F, rho*e n :=
      Finset.sum_le_sum (fun n hn => hterm n hn)
    _ = rho*(∑ n ∈ F, e n) := by
      rw [Finset.mul_sum]
    _ ≤ rho*(∑ a : X, w a*‖f a‖^2) := by
      exact mul_le_mul_of_nonneg_left
        (source_original_physical_atom_window_energy_le434
          S mu hmu F f) hrho
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalIntegerBilinear -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The NATIVE exact C6 integer bilinear inequality, with
constant 5, instantiated at the ACTUAL SOURCE03 physical
conditional product-atom coefficients c_A(n),c_B(m) for
arbitrary prime-mark-dependent complex endpoint tests.
No boundedness of f_A or f_B, no fictional C6-mass
equality, no conditions on G/S/k, and no probabilistic
replacement. Arithmetic cancellation applies directly to
integer amplitudes, with their TRUE original phase sign and
2pi convention (native integerPhase).
This estimate is not by itself log saving until the exact
physical atom masses yield upper 1/n envelopes. -/
theorem source_original_physical_integer_bilinear_C6_bound434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (M N P Q : ℕ) (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2)) :
    ‖(∑ i ∈ Finset.range P,
      sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
      (∑ j ∈ Finset.range Q,
        sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
        integerPhase (((a:ℝ)/(r:ℝ)+beta)*((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ)))‖ ≤
    5*Real.sqrt (∑ i ∈ Finset.range P,
      ‖sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i)‖^2) *
      Real.sqrt (∑ j ∈ Finset.range Q,
      ‖sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j)‖^2) *
      Real.sqrt ((P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
        ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) := by
  classical
  let cA := sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA
  let cB := sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB
  let A : ℤ → ℂ := fun z => cA z.toNat
  let B : ℤ → ℂ := fun z => cB z.toNat
  have hA (i : ℕ) : A ((M:ℤ)+(i:ℤ)) = cA (M+i) := by
    change cA (((M:ℤ)+(i:ℤ)).toNat)=cA (M+i)
    simp only [← Int.natCast_add, Int.toNat_natCast]
  have hB (j : ℕ) : B ((N:ℤ)+(j:ℤ)) = cB (N+j) := by
    change cB (((N:ℤ)+(j:ℤ)).toNat)=cB (N+j)
    simp only [← Int.natCast_add, Int.toNat_natCast]
  have hCore := source_integer_bilinear_minor_arc
    a r P Q beta (M:ℤ) (N:ℤ) A B hr hcop hbeta
  simpa only [hA, hB, Int.cast_add, Int.cast_natCast,
    Nat.cast_add, cA, cB] using hCore
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalIntegerMinorEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- ORIGINAL source03 physical integer-product coefficients
satisfy the actual C6 analytic rational minor-arc inequality
with Hilbert endpoint norms as soon as the TRUE physical atom
mass on each integer window has a proved rho envelope.
The spectral saving is NOT assumed: it comes directly from
the fully proved C6 integer bilinear norm and C211/C221 sharp
source03 physical fibre energy. The only remaining arithmetic
hypothesis is an explicit mass envelope for the REAL
ordered-prime group law; no C6 factorial equality is
postulated, and no L² test is assumed pointwise ≤1. -/
theorem source_original_physical_integer_minor_C6_energy434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (hmuA : ∀ i p, p ∈ SA i → 0 ≤ muA i p)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hmuB : ∀ i p, p ∈ SB i → 0 ≤ muB i p)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (M N P Q : ℕ) (a : ℤ) (r : ℕ) (beta : ℝ)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta| ≤ 1/((r:ℝ)^2))
    (rhoA rhoB : ℝ) (hRA : 0 ≤ rhoA) (hRB : 0 ≤ rhoB)
    (hAtomA : ∀ n∈Finset.Ico M (M+P),
      sourceOriginalPhysicalProductAtom434 SA muA n ≤ rhoA)
    (hAtomB : ∀ n∈Finset.Ico N (N+Q),
      sourceOriginalPhysicalProductAtom434 SB muB n ≤ rhoB) :
    let EA : ℝ :=
      ∑ x : SourceOriginalGramPrimeTuple434 SA,
       sourceOriginalGramPrimeMass434 SA muA x * ‖fA x‖^2
    let EB : ℝ :=
      ∑ y : SourceOriginalGramPrimeTuple434 SB,
       sourceOriginalGramPrimeMass434 SB muB y * ‖fB y‖^2
    ‖(∑ i ∈ Finset.range P,
      sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i) *
      (∑ j ∈ Finset.range Q,
        sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j) *
        Green64SourceC6.integerPhase
          (((a:ℝ)/(r:ℝ)+beta)*((N+j:ℕ):ℝ))
          ((M+i:ℕ):ℤ)))‖ ≤
    5*Real.sqrt (rhoA*EA)*Real.sqrt (rhoB*EB)*
      Real.sqrt ((P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
        ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))) := by
  classical
  let EA : ℝ :=
    ∑ x : SourceOriginalGramPrimeTuple434 SA,
       sourceOriginalGramPrimeMass434 SA muA x * ‖fA x‖^2
  let EB : ℝ :=
    ∑ y : SourceOriginalGramPrimeTuple434 SB,
       sourceOriginalGramPrimeMass434 SB muB y * ‖fB y‖^2
  let AA : ℝ := ∑ i ∈ Finset.range P,
    ‖sourceOriginalPhysicalProductAtomCoefficient434 SA muA fA (M+i)‖^2
  let BB : ℝ := ∑ j ∈ Finset.range Q,
    ‖sourceOriginalPhysicalProductAtomCoefficient434 SB muB fB (N+j)‖^2
  let T : ℝ := (P:ℝ)+(1+(Q:ℝ)/(r:ℝ))*
        ((P:ℝ)+(r:ℝ)*Real.log (2*(r:ℝ)))
  have hAA : AA ≤ rhoA*EA := by
    have hW := source_original_physical_atom_window_coefficient_L2434
      SA muA hmuA (Finset.Ico M (M+P))
      rhoA hRA hAtomA fA
    rw [Finset.sum_Ico_eq_sum_range] at hW
    simpa only [Nat.add_sub_cancel_left] using hW
  have hBB : BB ≤ rhoB*EB := by
    have hW := source_original_physical_atom_window_coefficient_L2434
      SB muB hmuB (Finset.Ico N (N+Q))
      rhoB hRB hAtomB fB
    rw [Finset.sum_Ico_eq_sum_range] at hW
    simpa only [Nat.add_sub_cancel_left] using hW
  have hSqrtA : Real.sqrt AA ≤ Real.sqrt (rhoA*EA) :=
    Real.sqrt_le_sqrt hAA
  have hSqrtB : Real.sqrt BB ≤ Real.sqrt (rhoB*EB) :=
    Real.sqrt_le_sqrt hBB
  have hPhase := source_original_physical_integer_bilinear_C6_bound434
    SA muA SB muB fA fB M N P Q a r beta hr hcop hbeta
  change _ ≤ 5*Real.sqrt (rhoA*EA)*
      Real.sqrt (rhoB*EB)*Real.sqrt T
  have hInner :
      5*Real.sqrt AA*Real.sqrt BB ≤
        5*Real.sqrt (rhoA*EA)*Real.sqrt (rhoB*EB) := by
    calc
      _ ≤ 5*Real.sqrt (rhoA*EA)*Real.sqrt BB :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hSqrtA (by norm_num))
          (Real.sqrt_nonneg _)
      _ ≤ 5*Real.sqrt (rhoA*EA)*Real.sqrt (rhoB*EB) :=
        mul_le_mul_of_nonneg_left hSqrtB (by positivity)
  exact hPhase.trans
    (mul_le_mul_of_nonneg_right hInner (Real.sqrt_nonneg T))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalMinorExactAtomFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact SOURCE03 finite integer-window pushforward for a
fully PRIME-MARK-DEPENDENT complex endpoint test.
This is the first algebraic bridge from C271's genuine
grouped product-atom coefficients to the physical
mark-space bilinear sum. It works for ANY finite
integer dyad window and ANY complex phase F(n).
No fake independence or supnorm hypothesis. -/
theorem source_original_physical_atom_finite_window_pullback434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (A : Finset ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ A,
       sourceOriginalPhysicalProductAtomCoefficient434 S mu f n*F n) =
    ∑ a : SourceOriginalGramPrimeTuple434 S,
      if sourceOriginalGramPrimeProduct434 S a ∈ A then
        (sourceOriginalGramPrimeMass434 S mu a:ℂ) *
          f a * F (sourceOriginalGramPrimeProduct434 S a)
      else 0 := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let w : X → ℂ := fun a =>
    (sourceOriginalGramPrimeMass434 S mu a:ℂ)*f a
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  have hChoose (a : X) :
      (∑ n ∈ A,
        (if prod a=n then w a else 0)*F n) =
      if prod a ∈ A then w a*F (prod a) else 0 := by
    by_cases h : prod a ∈ A
    · simp [h, Finset.sum_ite_eq']
    · simp [h]
  calc
    _ = ∑ n ∈ A, ∑ a : X,
        (if prod a=n then w a else 0)*F n := by
          apply Finset.sum_congr rfl
          intro n hn
          unfold sourceOriginalPhysicalProductAtomCoefficient434
          rw [Finset.sum_mul]
    _ = ∑ a : X, ∑ n ∈ A,
        (if prod a=n then w a else 0)*F n :=
      Finset.sum_comm
    _ = ∑ a : X,
        if prod a∈A then w a*F (prod a) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hChoose a
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalProductAtomTestPushforward -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact SOURCE03 physical-to-integer product-atom reindexing
for an ARBITRARY mark-dependent complex multiplier f.
The multiplier f need NOT be independent of the prime
factorization and does NOT factor through the product.
The pushforward coefficient is the actual physical
conditional sum at that product integer, not a fictitious
independent product amplitude. This is an algebraic equality,
not by itself an L²→L² minor-arc saving. -/
theorem source_original_physical_product_atom_test_pushforward434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (F : ℕ → ℂ) :
    (∑ a : SourceOriginalGramPrimeTuple434 S,
      (sourceOriginalGramPrimeMass434 S mu a:ℂ) *
        f a * F (sourceOriginalGramPrimeProduct434 S a)) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 S,
      sourceOriginalPhysicalProductAtomCoefficient434 S mu f n * F n := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let prod : X → ℕ := sourceOriginalGramPrimeProduct434 S
  let w : X → ℝ := sourceOriginalGramPrimeMass434 S mu
  let T : Finset ℕ := sourceOriginalPhysicalProductAtomSupport434 S
  have hmem (a : X) : prod a ∈ T :=
    Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hPick (a : X) :
      (∑ n ∈ T,
        if prod a=n then (w a:ℂ)*f a*F n else 0) =
        (w a:ℂ)*f a*F (prod a) := by
    simp [hmem a]
  have hAtom (n : ℕ) :
      sourceOriginalPhysicalProductAtomCoefficient434 S mu f n*F n =
      ∑ a : X,
        if prod a=n then (w a:ℂ)*f a*F n else 0 := by
    unfold sourceOriginalPhysicalProductAtomCoefficient434
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    change ((if prod a=n then (w a:ℂ)*f a else 0)*F n) =
        (if prod a=n then (w a:ℂ)*f a*F n else 0)
    split_ifs <;> simp
  calc
    _ = ∑ a : X, ∑ n ∈ T,
         if prod a=n then (w a:ℂ)*f a*F n else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (hPick a).symm
    _ = ∑ n ∈ T, ∑ a : X,
         if prod a=n then (w a:ℂ)*f a*F n else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ T,
        sourceOriginalPhysicalProductAtomCoefficient434 S mu f n*F n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (hAtom n).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalReciprocalAtom -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Every ACTUAL ordered original source03 physical labelled
prime tuple has exactly the reciprocal-integer-product
probability mass, times the product of the TRUE group
normalizer inverses. Repeated numerical prime values and
different group-specific normalization V_i remain unchanged.
This is the crucial elementary arithmetic factorization
of the original harmonic 1/(p V_i) law. -/
theorem source_original_actual_prime_tuple_reciprocal_mass434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ)
    (a : SourceOriginalGramPrimeTuple434 S) :
    sourceOriginalGramPrimeMass434 S
        (fun i p => (1/(p:ℝ))/V i) a =
      (1/(sourceOriginalGramPrimeProduct434 S a:ℝ)) *
        (∏ i : ι, (V i)⁻¹) := by
  classical
  unfold sourceOriginalGramPrimeMass434
    sourceOriginalGramPrimeProduct434
  simp only [div_eq_mul_inv, one_mul,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Nat.cast_prod]

/-- The ACTUAL original physical integer-product atom of the
independently labelled harmonic law is exactly a reciprocal
integer weight multiplied by the genuine number of ORDERED
prime-label tuples with that product. This unconditionally
isolates the ONLY remaining arithmetic multiplicity needed
to match the C6 factorial group law:
  µ(n) = (#physical prime tuples with product n)
         / (n * ∏_{slots} V_slot).
No bijection with fictitious uniform prime tuples is used. -/
theorem source_original_actual_physical_atom_card_formula434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ) (n : ℕ) :
    sourceOriginalPhysicalProductAtom434 S
        (fun i p => (1/(p:ℝ))/V i) n =
      ((Finset.univ.filter
         (fun a : SourceOriginalGramPrimeTuple434 S =>
            sourceOriginalGramPrimeProduct434 S a = n)).card:ℝ) *
        ((1/(n:ℝ))*(∏ i : ι, (V i)⁻¹)) := by
  classical
  unfold sourceOriginalPhysicalProductAtom434
  have hterm
      (a : SourceOriginalGramPrimeTuple434 S)
      (ha : sourceOriginalGramPrimeProduct434 S a = n) :
      sourceOriginalGramPrimeMass434 S
        (fun i p => (1/(p:ℝ))/V i) a =
       (1/(n:ℝ))*(∏ i : ι, (V i)⁻¹) := by
     rw [source_original_actual_prime_tuple_reciprocal_mass434,ha]
  calc
    _ = ∑ a ∈ (Finset.univ.filter
         (fun a : SourceOriginalGramPrimeTuple434 S =>
            sourceOriginalGramPrimeProduct434 S a = n)),
         ((1/(n:ℝ))*(∏ i : ι, (V i)⁻¹)) := by
           rw [Finset.sum_filter]
           apply Finset.sum_congr rfl
           intro a ha
           by_cases h : sourceOriginalGramPrimeProduct434 S a = n
           · simp only [if_pos h]
             exact hterm a h
           · simp [h]
    _ = _ := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalIndexedPrimeFibreFactorial -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- TRUE original SOURCE03 product fibres indexed by an ARBITRARY
finite set of labelled prime slots (with DIFFERENT prime
supports at each slot) have at most (number_of_slots)!
members. This follows from uniqueness of prime factorization
of each tuple's actual integer product. No squarefree or
disjoint-support hypothesis; this is a genuine combinatorial
bound, albeit weaker than the needed product of per-group
factorials when the number of groups grows like log L. -/
theorem source_original_indexed_prime_fibre_card_le_factorial434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ)
    (hp : ∀ i p, p∈S i → p.Prime)
    (n : ℕ) :
    ((Finset.univ : Finset (SourceOriginalGramPrimeTuple434 S)).filter
      (fun a => sourceOriginalGramPrimeProduct434 S a=n)).card ≤
        (Fintype.card ι).factorial := by
  classical
  let X := SourceOriginalGramPrimeTuple434 S
  let k := Fintype.card ι
  let e : ι ≃ Fin k := Fintype.equivFin ι
  let T : Finset X := Finset.univ.filter
    (fun a => sourceOriginalGramPrimeProduct434 S a=n)
  let encode : X → List ℕ := fun a =>
    List.ofFn (fun j : Fin k => (a (e.symm j)).val)
  have hEncode : Function.Injective encode := by
    intro a b h
    have hv := List.ofFn_injective h
    funext i
    have hh := congrFun hv (e i)
    have hs : e.symm (e i) = i := e.symm_apply_apply i
    rw [hs] at hh
    exact Subtype.ext hh
  have hProd (a : X) :
      (List.ofFn (fun j : Fin k => (a (e.symm j)).val)).prod =
        sourceOriginalGramPrimeProduct434 S a := by
    rw [List.prod_ofFn]
    unfold sourceOriginalGramPrimeProduct434
    exact (Fintype.prod_equiv e
      (fun i : ι => (a i).val)
      (fun j : Fin k => (a (e.symm j)).val)
      (by
        intro i
        rw [e.symm_apply_apply])).symm
  have hPrime (a : X) (p : ℕ)
      (h : p∈encode a) : p.Prime := by
    obtain ⟨j,hj⟩ :=
      (List.mem_ofFn' (fun j : Fin k => (a (e.symm j)).val) p).mp h
    rw [←hj]
    exact hp (e.symm j) (a (e.symm j)).val
      (a (e.symm j)).property
  have hImage :
      T.image encode ⊆ n.primeFactorsList.permutations.toFinset := by
    intro l hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    have hn : sourceOriginalGramPrimeProduct434 S a=n :=
      (Finset.mem_filter.mp ha).2
    have hperm : List.Perm (encode a) n.primeFactorsList := by
      apply Nat.primeFactorsList_unique
      · exact (hProd a).trans hn
      · intro p hpList
        exact hPrime a p hpList
    exact List.mem_toFinset.mpr
      (List.mem_permutations.mpr hperm)
  by_cases ht : T.Nonempty
  · obtain ⟨a,ha⟩ := ht
    have hLen : n.primeFactorsList.length = k := by
      have hperm : List.Perm (encode a) n.primeFactorsList := by
        apply Nat.primeFactorsList_unique
        · exact (hProd a).trans (Finset.mem_filter.mp ha).2
        · intro p h
          exact hPrime a p h
      have hh := hperm.length_eq
      simpa only [encode, List.length_ofFn] using hh.symm
    calc
      _ = T.card := rfl
      _ = (T.image encode).card :=
        (Finset.card_image_of_injective T hEncode).symm
      _ ≤ n.primeFactorsList.permutations.toFinset.card :=
        Finset.card_le_card hImage
      _ ≤ n.primeFactorsList.permutations.length :=
        List.toFinset_card_le _
      _ = (n.primeFactorsList.length).factorial :=
        List.length_permutations _
      _ = k.factorial := by rw [hLen]
  · have heq : T=∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ k.factorial
    rw [heq]
    exact Nat.zero_le _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalPrimeTupleFactorization -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The EXACT factorization multiplicity at a prime p of an
independently labelled physical prime tuple's integer product.
It equals the number of selected slots whose numerical prime
is p, even when the same numerical p occurs repeatedly.
This is the load-bearing arithmetic step in recovering
PER-GROUP products from a full product when group prime
supports are pairwise disjoint. -/
theorem source_original_prime_tuple_factorization_count434
    {I : Type} [Fintype I]
    (a : I → ℕ) (ha : ∀ i, (a i).Prime) (p : ℕ) :
    (∏ i : I, a i).factorization p =
      ∑ i : I, if a i=p then 1 else 0 := by
  have hnonzero : ∀ i ∈ (Finset.univ : Finset I), a i ≠ 0 := by
    intro i hi
    exact (ha i).ne_zero
  rw [Nat.factorization_prod_apply hnonzero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(ha i).factorization, Finsupp.single_apply]

/-- If an actual prime tuple uses only primes from its genuine
support S, then any prime q outside S has multiplicity ZERO
in its true integer product. Neither squarefreeness nor
pairwise disjointness within the tuple is assumed. -/
theorem source_original_prime_tuple_factorization_outside434
    {I : Type} [Fintype I]
    (S : Finset ℕ) (a : I → ℕ)
    (ha : ∀ i, (a i).Prime ∧ a i ∈ S)
    (q : ℕ) (hq : q ∉ S) :
    (∏ i : I, a i).factorization q = 0 := by
  rw [source_original_prime_tuple_factorization_count434
        a (fun i => (ha i).1) q]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : a i ≠ q := by
    intro hEq
    exact hq (hEq ▸ (ha i).2)
  simp [hne]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalPrimeFactorizationRestriction -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- In an actual indexed tuple of primes, if all slots
OUTSIDE a selected set T have prime values outside S, then
at every p in S the prime multiplicity in the FULL product
equals the multiplicity in the SELECTED product.
The statement permits arbitrary repetition inside T and
arbitrary different prime supports between slots; it needs
only the genuine prime/support separation. -/
theorem source_original_prime_selected_factorization_eq434
    {I : Type} [Fintype I] [DecidableEq I]
    (a : I → ℕ) (ha : ∀ i, (a i).Prime)
    (T : Finset I) (S : Finset ℕ)
    (hout : ∀ i, i ∉ T → a i ∉ S)
    (p : ℕ) (hp : p ∈ S) :
    (∏ i ∈ T, a i).factorization p =
      (∏ i : I, a i).factorization p := by
  have hNonzero : ∀ i ∈ T, a i ≠ 0 := by
    intro i hi
    exact (ha i).ne_zero
  rw [Nat.factorization_prod_apply hNonzero,
    source_original_prime_tuple_factorization_count434 a ha p]
  have hterm (i : I) :
      (a i).factorization p = (if a i=p then 1 else 0) := by
    rw [(ha i).factorization, Finsupp.single_apply]
  simp_rw [hterm]
  apply Finset.sum_subset (Finset.subset_univ T)
  intro i hi hiT
  have hne : a i ≠ p := by
    intro heq
    have hin : a i ∈ S := by simpa [heq] using hp
    exact (hout i hiT) hin
  simp [hne]

/-- A group-selected true prime tuple has NO prime factors
outside its own group support S, even when the group has
identical numerical prime values in different slots. -/
theorem source_original_prime_selected_factorization_outside434
    {I : Type} [Fintype I] [DecidableEq I]
    (a : I → ℕ) (ha : ∀ i, (a i).Prime)
    (T : Finset I) (S : Finset ℕ)
    (hin : ∀ i, i ∈ T → a i ∈ S)
    (p : ℕ) (hp : p ∉ S) :
    (∏ i ∈ T, a i).factorization p = 0 := by
  have hNonzero : ∀ i ∈ T, a i ≠ 0 := by
    intro i hi
    exact (ha i).ne_zero
  rw [Nat.factorization_prod_apply hNonzero]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : a i ≠ p := by
    intro heq
    have hb : a i ∈ S := hin i hi
    exact hp (by simpa [heq] using hb)
  rw [(ha i).factorization, Finsupp.single_apply]
  simp [hne]
end Green64Analytic.CorrelationSquare

end

