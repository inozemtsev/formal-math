module

public import Green64.Library.Weights.Part049
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Green64.Library.Weights.OriginalGroupMasses
public import Green64.Library.Analysis.Estimates.Part011
public import Green64.Library.Weights.OriginalScaleAsymptotics

@[expose] public section

/-!
# Weights / Part050

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalProbeBigProductBounds -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- A TRUE source03 nonempty subset of designated probes in a big
prime-group block has an independently sampled product between
one big prime and an upper bound raised to its EXACT number
of labelled probes. The original auxiliary tuple may repeat the
same numerical prime across different labelled slots. -/
theorem source_original_probe_big_product_bounds434
    {G : Type} [DecidableEq G]
    (block : Finset G) (m : ℕ)
    (C : Finset (G × Fin m))
    (hNon : C.Nonempty)
    (hSub : C ⊆ block.product (Finset.univ : Finset (Fin m)))
    (P : G → Finset ℕ) (Bmin Bmax : ℝ)
    (hBunit : 1 ≤ Bmin)
    (hBounds : ∀ g ∈ block, ∀ p ∈ P g,
      Bmin ≤ (p:ℝ) ∧ (p:ℝ) ≤ Bmax)
    (a : C → ℕ)
    (ha : a ∈ Fintype.piFinset (fun z : C => P z.val.1)) :
    Bmin ≤ (∏ z : C,(a z:ℝ)) ∧
    (∏ z : C,(a z:ℝ)) ≤ Bmax ^ C.card := by
  classical
  have hElem (z : C) : Bmin ≤ (a z:ℝ) ∧ (a z:ℝ) ≤ Bmax := by
    have hg : z.val.1 ∈ block :=
      (Finset.mem_product.mp (hSub z.property)).1
    exact hBounds z.val.1 hg (a z) ((Fintype.mem_piFinset.mp ha) z)
  have hGE : ∀ z : C, 1 ≤ (a z:ℝ) :=
    fun z => hBunit.trans (hElem z).1
  obtain ⟨i,hi⟩ := hNon
  let z : C := ⟨i,hi⟩
  have hLower : (a z:ℝ) ≤ (∏ z : C,(a z:ℝ)) := by
    have h :=
      Finset.prod_le_prod_of_subset_of_one_le₀
        (s:={z}) (t:=(Finset.univ : Finset C))
        (f:=fun z : C => (a z:ℝ))
        (Finset.singleton_subset_iff.mpr (Finset.mem_univ z))
        (by intro i hi; exact (by norm_num : (0:ℝ) ≤ 1).trans (hGE i))
        (by intro i hi hni; exact hGE i)
    simpa only [Finset.prod_singleton] using h
  constructor
  · exact (hElem z).1.trans hLower
  · calc
      (∏ z : C,(a z:ℝ)) ≤
          ∏ _z : C,Bmax :=
        Finset.prod_le_prod₀ (s:=Finset.univ)
          (fun z _ => le_trans (by norm_num : (0:ℝ) ≤ 1) (hGE z))
          (fun z _ => (hElem z).2)
      _ = Bmax ^ C.card := by simp

/-- The source03 original paired comparison is nonempty in BOTH
big-group probe blocks A,B. Hence each independently sampled
original product contains at least ONE true big-group prime.
No conditions are imposed on the separate SMALL groups. -/
theorem source_original_probe_big_two_product_bounds434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (P : G → Finset ℕ) (Bmin Bmax : ℝ)
    (hBunit : 1 ≤ Bmin)
    (hBounds : ∀ g ∈ blockA ∪ blockB,∀ p ∈ P g,
      Bmin ≤ (p:ℝ) ∧ (p:ℝ) ≤ Bmax)
    (aA : ν.1 → ℕ)
    (haA : aA ∈ Fintype.piFinset (fun z : ν.1 => P z.val.1))
    (aB : ν.2 → ℕ)
    (haB : aB ∈ Fintype.piFinset (fun z : ν.2 => P z.val.1)) :
    (Bmin ≤ (∏ z : ν.1,(aA z:ℝ)) ∧
      (∏ z : ν.1,(aA z:ℝ)) ≤ Bmax ^ ν.1.card) ∧
    (Bmin ≤ (∏ z : ν.2,(aB z:ℝ)) ∧
      (∏ z : ν.2,(aB z:ℝ)) ≤ Bmax ^ ν.2.card) := by
  classical
  obtain ⟨hNonA,hSubA,hNonB,hSubB⟩ :=
    (source_original_two_block_probe_pattern_mem434
      blockA blockB m ν.1 ν.2).mp hν
  constructor
  · apply source_original_probe_big_product_bounds434
      blockA m ν.1 hNonA hSubA P Bmin Bmax hBunit
    · intro g hg p hp
      exact hBounds g (Finset.mem_union.mpr (Or.inl hg)) p hp
    · exact haA
  · apply source_original_probe_big_product_bounds434
      blockB m ν.2 hNonB hSubB P Bmin Bmax hBunit
    · intro g hg p hp
      exact hBounds g (Finset.mem_union.mpr (Or.inr hg)) p hp
    · exact haB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeActiveCellScales -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- A truly ACTIVE source03 comparison cell has a product in the
original positive big-prime range, and therefore its exact lower
log-cell boundary j*h lies in
  (log Bmin-h, |C|*log Bmax].
This is a geometric consequence of the original independently
drawn source prime tuples. No externally assumed cell scale U is
used. Equal numerical primes at different labelled coordinates
remain allowed. -/
theorem source_original_big_active_cell_log_scales434
    {G : Type} [DecidableEq G]
    (block : Finset G) (m : ℕ)
    (C : Finset (G × Fin m))
    (hNon : C.Nonempty)
    (hSub : C ⊆ block.product (Finset.univ : Finset (Fin m)))
    (P : G → Finset ℕ) (V : G → ℝ)
    (Bmin Bmax : ℝ) (hMinPos : 0 < Bmin) (hMaxPos : 0 < Bmax)
    (hBunit : 1 ≤ Bmin)
    (hBounds : ∀ g ∈ block,∀ p ∈ P g,
      Bmin ≤ (p:ℝ) ∧ (p:ℝ) ≤ Bmax)
    (h xi : ℝ) (hh : 0 < h)
    (j : ℤ)
    (hj : j ∈ sourceOriginalFiniteActiveLogCells434
      (fun z : C => P z.val.1)
      (fun z : C => sourcePrimeSharedAtom434 (V z.val.1))
      h xi) :
    Real.log Bmin - h < (j:ℝ)*h ∧
    (j:ℝ)*h ≤ (C.card:ℝ)*Real.log Bmax := by
  classical
  obtain ⟨a,ha,hcell⟩ :=
    source_original_active_cell_true_product_witness434
      (fun z : C => P z.val.1)
      (fun z : C => sourcePrimeSharedAtom434 (V z.val.1))
      h xi hh j hj
  obtain ⟨hLower,hUpper⟩ :=
    source_original_probe_big_product_bounds434
      block m C hNon hSub P Bmin Bmax hBunit hBounds a ha
  have hCast : (((∏ z : C,a z):ℕ):ℝ) =
      (∏ z : C,(a z:ℝ)) := by
    simp only [Nat.cast_prod]
  dsimp only [sourceOriginalLiteralLogCell434] at hcell
  rw [hCast] at hcell
  have hPos : 0 < (∏ z : C,(a z:ℝ)) :=
    lt_of_lt_of_le hMinPos hLower
  have hMinLog :
      Real.log Bmin ≤ Real.log (∏ z : C,(a z:ℝ)) :=
    Real.log_le_log hMinPos hLower
  have hMaxLog :
      Real.log (∏ z : C,(a z:ℝ)) ≤
        (C.card:ℝ)*Real.log Bmax := by
    calc
      Real.log (∏ z : C,(a z:ℝ)) ≤ Real.log (Bmax^C.card) :=
        Real.log_le_log hPos hUpper
      _ = (C.card:ℝ)*Real.log Bmax := by
        rw [Real.log_pow]
  constructor
  · have hh' := hcell.2
    linarith
  · exact hcell.1.trans hMaxLog

/-- No additional source03 scale hypothesis for the A comparison
cell: its TRUE active-cell membership plus the original big
prime bounds enforce log U_A > L^c-h_A and
log U_A ≤ |A| L^d, uniformly in J. -/
theorem source_original_probe_active_A_big_scale434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (L c d : ℝ) (hL : 0 ≤ L)
    (hBounds : ∀ g ∈ blockA ∪ blockB,∀ p ∈ P g,
      Real.exp (L^c) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^d))
    (h xi : ℝ) (hh : 0 < h) (j : ℤ)
    (hj : j ∈ sourceOriginalProbeActiveCellsA434 m P V ν h xi) :
    L^c - h < (j:ℝ)*h ∧ (j:ℝ)*h ≤ (ν.1.card:ℝ)*(L^d) := by
  classical
  obtain ⟨hNon,hSub,_,_⟩ :=
    (source_original_two_block_probe_pattern_mem434
      blockA blockB m ν.1 ν.2).mp hν
  have hUnit : (1:ℝ) ≤ Real.exp (L^c) := by
    have h : 0 ≤ L^c := Real.rpow_nonneg hL _
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr h)
  have h := source_original_big_active_cell_log_scales434
    blockA m ν.1 hNon hSub P V
    (Real.exp (L^c)) (Real.exp (L^d))
    (Real.exp_pos _) (Real.exp_pos _) hUnit
    (by
      intro g hg p hp
      exact hBounds g (Finset.mem_union.mpr (Or.inl hg)) p hp)
    h xi hh j hj
  simpa only [Real.log_exp] using h

theorem source_original_probe_active_B_big_scale434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (L c d : ℝ) (hL : 0 ≤ L)
    (hBounds : ∀ g ∈ blockA ∪ blockB,∀ p ∈ P g,
      Real.exp (L^c) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^d))
    (h xi : ℝ) (hh : 0 < h) (j : ℤ)
    (hj : j ∈ sourceOriginalProbeActiveCellsB434 m P V ν h xi) :
    L^c - h < (j:ℝ)*h ∧ (j:ℝ)*h ≤ (ν.2.card:ℝ)*(L^d) := by
  classical
  obtain ⟨_,_,hNon,hSub⟩ :=
    (source_original_two_block_probe_pattern_mem434
      blockA blockB m ν.1 ν.2).mp hν
  have hUnit : (1:ℝ) ≤ Real.exp (L^c) := by
    have h : 0 ≤ L^c := Real.rpow_nonneg hL _
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr h)
  have h := source_original_big_active_cell_log_scales434
    blockB m ν.2 hNon hSub P V
    (Real.exp (L^c)) (Real.exp (L^d))
    (Real.exp_pos _) (Real.exp_pos _) hUnit
    (by
      intro g hg p hp
      exact hBounds g (Finset.mem_union.mpr (Or.inr hg)) p hp)
    h xi hh j hj
  simpa only [Real.log_exp] using h
end Green64Analytic.CorrelationSquare

end

/-! ## SourceNativeOriginalCellBounds -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The original two-block pattern has at most m probes per actual BIG group.
Both blocks together cover the complete independently indexed native BIG family. -/
theorem source_native_original_probe_total_card434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (ν : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 r L) (sourceNativeOriginalBigBlockB434 r L) m) :
    ν.1.card + ν.2.card ≤ m * Fintype.card (sourceNativeOriginalBigType434 r L) := by
  classical
  obtain ⟨_, hA, _, hB⟩ := (source_original_two_block_probe_pattern_mem434
    (sourceNativeOriginalBigBlockA434 r L) (sourceNativeOriginalBigBlockB434 r L)
    m ν.1 ν.2).mp hν
  have ha : ν.1.card ≤ (sourceNativeOriginalBigBlockA434 r L).card*m := by
    simpa [sourceOriginalProbeBlock434, Finset.card_product] using
      Finset.card_le_card hA
  have hb : ν.2.card ≤ (sourceNativeOriginalBigBlockB434 r L).card*m := by
    simpa [sourceOriginalProbeBlock434, Finset.card_product] using
      Finset.card_le_card hB
  have hp := source_native_original_big_partition434 r L
  have hc := Finset.card_union_of_disjoint hp.2.1
  rw [hp.1, Finset.card_univ] at hc
  calc
    _ ≤ (sourceNativeOriginalBigBlockA434 r L).card*m +
        (sourceNativeOriginalBigBlockB434 r L).card*m := Nat.add_le_add ha hb
    _ = m * Fintype.card (sourceNativeOriginalBigType434 r L) := by rw [hc]; ring

/-- Scale bounds for the actual A and B active cells of the full native BIG
family, with its genuine reciprocal laws. No external product-scale premise. -/
theorem source_native_original_active_cell_log_bounds434
    (r : ℕ) (hr : 1 ≤ r) (L : ℝ) (hL : Real.exp 1 ≤ L) (m : ℕ)
    (ν : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 r L) (sourceNativeOriginalBigBlockB434 r L) m)
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hA1 : hA ≤ 1) (hB1 : hB ≤ 1) (ja jb : ℤ)
    (ha : ja ∈ sourceOriginalProbeActiveCellsA434 m
      (sourceNativeOriginalTb434 r L) (sourceNativeOriginalVbig434 r L) ν hA xi)
    (hb : jb ∈ sourceOriginalProbeActiveCellsB434 m
      (sourceNativeOriginalTb434 r L) (sourceNativeOriginalVbig434 r L) ν hB xi) :
    2*L^(3/10:ℝ)-2 < (ja:ℝ)*hA+(jb:ℝ)*hB ∧
      (ja:ℝ)*hA+(jb:ℝ)*hB ≤
        (m:ℝ)*(3+(Real.log 2)⁻¹)*Real.log L*L^(2/5:ℝ) := by
  have hL0 : 0 ≤ L := (Real.exp_pos 1).le.trans hL
  have hp := source_native_original_big_partition434 r L
  have hbounds : ∀ g ∈ sourceNativeOriginalBigBlockA434 r L ∪
      sourceNativeOriginalBigBlockB434 r L, ∀ p ∈ sourceNativeOriginalTb434 r L g,
      Real.exp (L^(3/10:ℝ)) ≤ (p:ℝ) ∧ (p:ℝ) ≤ Real.exp (L^(2/5:ℝ)) := by
    intro g _ p hpg
    exact (source_native_original_Tb_prime_range434 r L g p hpg).2
  have ha' := source_original_probe_active_A_big_scale434
    (sourceNativeOriginalBigBlockA434 r L) (sourceNativeOriginalBigBlockB434 r L)
    m ν hν (sourceNativeOriginalTb434 r L) (sourceNativeOriginalVbig434 r L)
    L (3/10) (2/5) hL0 hbounds hA xi hhA ja ha
  have hb' := source_original_probe_active_B_big_scale434
    (sourceNativeOriginalBigBlockA434 r L) (sourceNativeOriginalBigBlockB434 r L)
    m ν hν (sourceNativeOriginalTb434 r L) (sourceNativeOriginalVbig434 r L)
    L (3/10) (2/5) hL0 hbounds hB xi hhB jb hb
  have hcard : (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      (3+(Real.log 2)⁻¹)*Real.log L := by
    have hi : (sourceNativeOriginalBigIndices434 r L).card ≤
        (sourceOriginalPAllGroupIndices r L).card := Finset.card_filter_le _ _
    have hi' : Fintype.card (sourceNativeOriginalBigType434 r L) ≤
        (sourceOriginalPAllGroupIndices r L).card := by
      simpa only [sourceNativeOriginalBigType434, Fintype.card_coe] using hi
    exact (show (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      ((sourceOriginalPAllGroupIndices r L).card:ℝ) by exact_mod_cast hi').trans
      (source_original_P_all_group_card_log r L hr hL)
  have hcN := source_native_original_probe_total_card434 r L m ν hν
  have hcR : (ν.1.card:ℝ)+(ν.2.card:ℝ) ≤
      (m:ℝ)*(Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) := by
    exact_mod_cast hcN
  have hc := hcR.trans (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg m))
  constructor
  · linarith [ha'.1, hb'.1]
  · have hh := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL0 (2/5:ℝ))
    nlinarith [ha'.2, hb'.2]

/-- The numeric C witness comes from a genuine tuple on the original native
BIG bands. Its support membership, primality, repeated labelled factors and
exact product are retained in the statement, not merely lower estimates. -/
theorem source_native_original_active_cell_numeric_witness434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (C : Finset (sourceNativeOriginalBigType434 r L × Fin m)) (hC : C.Nonempty)
    (h xi : ℝ) (hh : 0 < h) (h1 : h ≤ 1) (j : ℤ)
    (hj : j ∈ sourceOriginalFiniteActiveLogCells434
      (fun z : C => sourceNativeOriginalTb434 r L z.val.1)
      (fun z : C => sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 r L z.val.1)) h xi) :
    ∃ a ∈ Fintype.piFinset (fun z : C => sourceNativeOriginalTb434 r L z.val.1),
      (Finset.range (Fintype.card C)).Nonempty ∧
      (∀ i : Fin (Fintype.card C),
        sourceOriginalProbeIndexedPrime434 a i ∈ sourceNativeOriginalTb434 r L
          ((Fintype.equivFin C).symm i).val.1 ∧
        (sourceOriginalProbeIndexedPrime434 a i).Prime ∧
        Real.exp (L^(3/10:ℝ)) ≤ (sourceOriginalProbeIndexedPrime434 a i:ℝ)) ∧
      (∏ i ∈ Finset.range (Fintype.card C), sourceOriginalProbeIndexedPrime434 a i) =
        (∏ z : C, a z) ∧
      Real.log (((∏ i ∈ Finset.range (Fintype.card C),
        sourceOriginalProbeIndexedPrime434 a i):ℕ):ℝ) ≤
        Real.log (Real.exp ((j:ℝ)*h))+1 := by
  obtain ⟨z0, hz0⟩ := hC
  letI : Nonempty C := ⟨⟨z0,hz0⟩⟩
  obtain ⟨a,ha,hcell⟩ := source_original_active_cell_true_product_witness434
    (fun z : C => sourceNativeOriginalTb434 r L z.val.1)
    (fun z : C => sourcePrimeSharedAtom434 (sourceNativeOriginalVbig434 r L z.val.1))
    h xi hh j hj
  refine ⟨a,ha,source_original_probe_indexed_support_nonempty434,?_,
    source_original_probe_indexed_prime_product434 a,?_⟩
  · intro i
    have hp := (Fintype.mem_piFinset.mp ha) ((Fintype.equivFin C).symm i)
    have hpi : sourceOriginalProbeIndexedPrime434 a i =
        a ((Fintype.equivFin C).symm i) := by
      simp only [sourceOriginalProbeIndexedPrime434, dif_pos i.isLt]
    rw [hpi]
    exact ⟨hp,(source_native_original_Tb_prime_range434 r L _ _ hp).1,
      (source_native_original_Tb_prime_range434 r L _ _ hp).2.1⟩
  · rw [source_original_probe_indexed_prime_product434, Real.log_exp]
    dsimp only [sourceOriginalLiteralLogCell434] at hcell
    linarith [hcell.2]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalComparisonCellScales -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Genuine comparison-cell scales on the full original native BIG family.
The dyad and signed window retain their original definitions. The A/B cells
use the true reciprocal laws; their scales are derived, not assumed.
This proves scale/cap fields only, not a completed endpoint record. -/
theorem eventually_source_native_original_comparison_cell_scales434
    (r : ℕ) (hr : 1 ≤ r) (K : ℝ) (hK : 0 ≤ K) (m : ℕ)
    (Carc : ℝ) (hCarc : 0 ≤ Carc) :
    ∀ᶠ L : ℝ in atTop, 1 < L ∧
      (∃ depth : ℕ, 192*L^(89:ℝ) ≤ (2:ℝ)^depth ∧
        (2:ℝ)^depth ≤ 384*L^(89:ℝ)) ∧
      ∀ (U V : ℝ), Real.exp L/4 ≤ U*V → U*V ≤ 3*Real.exp L →
      ∀ (N j : ℕ), j ≤ N → (2:ℝ)^N ≤ 384*L^(89:ℝ) →
      ∀ (ν : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m),
        ν ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 r L) (sourceNativeOriginalBigBlockB434 r L) m →
      ∀ (hA hB xi : ℝ), 0 < hA → 0 < hB → hA ≤ 1 → hB ≤ 1 →
      ∀ (ja jb : ℤ),
        ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 r L)
          (sourceNativeOriginalVbig434 r L) ν hA xi →
        jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 r L)
          (sourceNativeOriginalVbig434 r L) ν hB xi →
      let Z := sourceCorrectedDyadicScale U V (L^K) j
      let H := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
      let Y := Z*H
      let Ncap := ⌈64*Y⌉₊
      L = Real.log (Real.exp L) ∧ 0 < Z ∧ 0 < H ∧ 4 ≤ Y ∧
      Real.exp (3*L/4) ≤ Y ∧ Y ≤ Real.exp (3*L/2) ∧
      Real.exp L*L^(-(K+91)) ≤ Z ∧
      64*Y ≤ (Ncap:ℝ) ∧ (Ncap:ℝ) ≤ (Real.exp L)^2 ∧
      2 ≤ H/L^Carc ∧ H/L^Carc ≤ Y/(8*64) ∧
      ∀ k ∈ sourceCorrectedSmoothKSet (L^K) (L^(89:ℝ)),
        k ≠ 0 ∧ Even k ∧ 0 < k.natAbs ∧
        (k.natAbs:ℝ) ≤ L^(K+92) ∧ |((2*k:ℤ):ℝ)| * Real.exp 2 ≤ Z/4 := by
  let C0 : ℝ := 3+(Real.log 2)⁻¹
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  filter_upwards [eventually_source_native_cell_scalar_budget434 K Carc C0 m hK hCarc hC0]
    with L hbud
  rcases hbud with ⟨hLexp,hL32,hLlo,hLcap,hLarc,hupper,hlower,hshift⟩
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlog32 : Real.log 32 ≤ Real.log L := Real.log_le_log (by norm_num) hL32
  refine ⟨by linarith, source_corrected_dyadic_depth_exists (L^(89:ℝ))
    (Real.one_le_rpow hL1 (by norm_num)), ?_⟩
  intro U V hUVlo hUVhi N j hj hN ν hν hA hB xi hhA hhB hA1 hB1 ja jb ha hb
  let Z := sourceCorrectedDyadicScale U V (L^K) j
  let S := (ja:ℝ)*hA+(jb:ℝ)*hB
  let H := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let Y := Z*H
  let Ncap := ⌈64*Y⌉₊
  have hd := source_native_original_dyad_bounds434 L K U V hL0 hUVlo hUVhi N j hj hN
  have hdz := source_native_original_dyad_log_bounds434 L K U V hL0 hUVlo hUVhi N j hj hN
  have hc := source_native_original_active_cell_log_bounds434 r hr L hLexp m ν hν
    hA hB xi hhA hhB hA1 hB1 ja jb ha hb
  have hZpos : 0 < Z := hd.1
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hYpos : 0 < Y := mul_pos hZpos hHpos
  have hHexp : H=Real.exp S := by dsimp [H,S]; rw [Real.exp_add]
  have hlogY : Real.log Y = Real.log Z+S := by
    dsimp [Y]
    rw [Real.log_mul hZpos.ne' hHpos.ne',hHexp,Real.log_exp]
  have hp3 : 1 ≤ L^(3/10:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hp4 : 1 ≤ L^(2/5:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hp4non : 0 ≤ L^(2/5:ℝ) := Real.rpow_nonneg hL0.le _
  have hSpos : 0 < S := by dsimp [S]; linarith [hc.1]
  have hKlog : 0 ≤ K*Real.log L := mul_nonneg hK hlog0
  have hZlo : L-Real.log 32 ≤ Real.log Z := by
    have hh : L+K*Real.log L-Real.log 32 ≤ Real.log Z := hdz.1
    linarith
  have hYlo : Real.exp (3*L/4) ≤ Y := by
    rw [← Real.exp_log hYpos]
    apply Real.exp_le_exp.mpr
    rw [hlogY]
    linarith
  have hY4 : 4 ≤ Y := by nlinarith only [hL32,hYlo,Real.add_one_le_exp (3*L/4)]
  have hYhi : Y ≤ Real.exp (3*L/2) := by
    rw [← Real.exp_log hYpos]
    apply Real.exp_le_exp.mpr
    rw [hlogY]
    have hA0 : 0 ≤ (K+89)*Real.log L+Real.log 144 := by
      have : 0 ≤ Real.log (144:ℝ) := Real.log_nonneg (by norm_num)
      positivity
    have hAedge := mul_le_mul_of_nonneg_left hp4 hA0
    have hub := mul_le_mul_of_nonneg_right hupper hp4non
    have hrpow : L^(3/5:ℝ)*L^(2/5:ℝ)=L := by
      rw [← Real.rpow_add hL0]
      norm_num
    have hub' : ((K+89+(m:ℝ)*C0)*Real.log L+Real.log 144)*L^(2/5:ℝ) ≤ L/2 := by
      calc
        _ ≤ (L^(3/5:ℝ)/2)*L^(2/5:ℝ) := hub
        _ = L/2 := by rw [div_mul_eq_mul_div,hrpow]
    have hcS : S ≤ (m:ℝ)*C0*Real.log L*L^(2/5:ℝ) := hc.2
    nlinarith only [hdz.2,hcS,hAedge,hub']
  have hZfield : Real.exp L*L^(-(K+91)) ≤ Z := by
    have he : L+(-(K+91))*Real.log L ≤ Real.log Z := by
      have : 0 ≤ Real.log (32:ℝ) := Real.log_nonneg (by norm_num)
      nlinarith [hdz.1]
    calc
      _ = Real.exp (L+(-(K+91))*Real.log L) := by
        rw [Real.rpow_def_of_pos hL0,Real.exp_add]
        congr 1
        congr 1
        ring
      _ ≤ Real.exp (Real.log Z) := Real.exp_le_exp.mpr he
      _ = Z := Real.exp_log hZpos
  have hCap : 64*Y ≤ (Ncap:ℝ) := Nat.le_ceil _
  have hNcap : (Ncap:ℝ) ≤ (Real.exp L)^2 := by
    have hceil : (Ncap:ℝ) ≤ 64*Y+1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 64*Y)).le
    have hone : 1 ≤ Real.exp (3*L/2) := Real.one_le_exp_iff.mpr (by positivity)
    calc
      _ ≤ 65*Real.exp (3*L/2) := by nlinarith
      _ = Real.exp (Real.log 65+3*L/2) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<65)]
      _ ≤ Real.exp (2*L) := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp L)^2 := by rw [pow_two,← Real.exp_add]; congr 1; ring
  have hpowCarc : 0 < L^Carc := Real.rpow_pos_of_pos hL0 _
  have hHband : 2 ≤ H/L^Carc := by
    apply (le_div_iff₀ hpowCarc).mpr
    calc
      2*L^Carc = Real.exp (Real.log 2+Carc*Real.log L) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos hL0]
        congr 1; congr 1; ring
      _ ≤ Real.exp S := Real.exp_le_exp.mpr (by dsimp [S]; linarith [hc.1])
      _ = H := hHexp.symm
  have hZ512 : (512:ℝ) ≤ Z := by
    rw [← Real.exp_log hZpos,← Real.exp_log (by norm_num : (0:ℝ)<512)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpowCarc1 : 1 ≤ L^Carc := Real.one_le_rpow hL1 hCarc
  have hArc : H/L^Carc ≤ Y/(8*64) := by
    apply (div_le_div_iff₀ hpowCarc (by norm_num : (0:ℝ)<8*64)).mpr
    have h1 : (512:ℝ) ≤ Z*L^Carc := hZ512.trans
      (by nlinarith [mul_le_mul_of_nonneg_left hpowCarc1 hZpos.le])
    have h2 := mul_le_mul_of_nonneg_right h1 hHpos.le
    dsimp [Y]
    nlinarith
  refine ⟨(Real.log_exp L).symm,hZpos,hHpos,hY4,hYlo,hYhi,hZfield,hCap,hNcap,hHband,hArc,?_⟩
  intro k hk
  have hk' := source_corrected_smooth_shift_abs_le (L^K) (L^(89:ℝ))
    (by positivity) k hk
  have hqpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk'.1
  have hp3' : (2:ℝ) ≤ L^(3:ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1:ℝ) ≤ 3)
    rw [Real.rpow_one] at hh
    linarith
  have hqcap : (k.natAbs:ℝ) ≤ L^(K+92) := by
    calc
      _ ≤ 2*L^K*L^(89:ℝ) := hk'.2.2
      _ = 2*L^(K+89) := by rw [Real.rpow_add hL0]; ring
      _ ≤ L^(3:ℝ)*L^(K+89) := mul_le_mul_of_nonneg_right hp3'
        (Real.rpow_nonneg hL0.le _)
      _ = L^(K+92) := by rw [← Real.rpow_add hL0]; congr 1; ring
  have hgraph : |((2*k:ℤ):ℝ)| * Real.exp 2 ≤ Z/4 := by
    have hkreal : |(k:ℝ)| ≤ 2*L^K*L^(89:ℝ) := by
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hk'.2.2
    have hk2 : |((2*k:ℤ):ℝ)| ≤ 4*L^K*L^(89:ℝ) := by
      calc
        |((2*k:ℤ):ℝ)| = 2*|(k:ℝ)| := by norm_num [Int.cast_mul, abs_mul]
        _ ≤ 2*(2*L^K*L^(89:ℝ)) := mul_le_mul_of_nonneg_left hkreal (by norm_num)
        _ = 4*L^K*L^(89:ℝ) := by ring
    have hexp : 512*Real.exp 2*L^(89:ℝ) ≤ Real.exp L := by
      calc
        _ = Real.exp (Real.log 512+2+89*Real.log L) := by
          rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<512),
            Real.rpow_def_of_pos hL0]
          congr 1; congr 1; ring
        _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
    have h1 := mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hL0.le K)
    have h2 := mul_le_mul_of_nonneg_right hk2 (Real.exp_pos 2).le
    nlinarith [hd.2.1]
  exact ⟨hk'.1,hk'.2.1,hqpos,hqcap,hgraph⟩
end Green64Analytic.SourceBlockSieve

end

end

