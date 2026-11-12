module

public import Green64.Library.Weights.StrippedRankPair
public import Green64.Library.Weights.UnbannedMarkedPairCap
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part097
public import Green64.Library.Weights.Part045
public import Green64.Library.Sieve.Foundations.SourceQSkipDesignatedPrimeCell
public import Mathlib
public import Green64.Library.Weights.Part073
public import Green64.Library.Weights.Part048
public import Green64.Library.Correlation.Part058
public import Green64.Library.Weights.Part012
public import Green64.Library.Correlation.Part066
public import Green64.Library.Weights.SourceQSkipActualResidual

@[expose] public section

/-!
# Weights / Part099

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FreeAuxCollision -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD

/-- The literal complementary free-auxiliary collision slice. All original
ordered free marks, both marked prefactors and the entire canonical Knu
are kept. This definition assumes no quantitative collision estimate. -/
def parityCanonicalFreeCollisionSlice434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G→Finset ℕ) (V : G→ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (q : ℝ) (w wp : ℕ) : ℂ :=
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
    (∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,
      if sourceB574FreeAuxBan434 J ell m hmJ nu aux a b then 0
      else sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux a b)

/-- Exact original banned/unbanned partition; the error is a constructed
marked collision sum, not a new hypothesis. -/
theorem parity_canonical_unbanned_collision_partition434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G→Finset ℕ) (V : G→ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (q : ℝ) (w wp : ℕ) :
    sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp +
      parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp =
      b615OriginalUnbannedMarkedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp := by
  unfold sourceB574CanonicalStrippedSlice434 sourceB574CanonicalFreeKernel434
    parityCanonicalFreeCollisionSlice434 b615OriginalUnbannedMarkedSlice434
  dsimp only
  rw [←mul_add]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp

/-- A free auxiliary label can hit an actual ordered marked list only if
it divides that integer. No condition on auxiliary repetitions is used. -/
theorem parity_free_aux_ban_of_no_divisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (P : G→Finset ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (w wp : ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)→ℕ)
    (ha : a∈bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w)
    (hb : b∈bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp)
    (hNo : ∀ z,¬aux z∣w ∧ ¬aux z∣wp) :
    sourceB574FreeAuxBan434 J ell m hmJ nu aux a b := by
  intro z i
  constructor
  · intro he
    apply (hNo z).1
    have h := (source_ordered_marks_mem434 _ _ _ _).mp ((Fintype.mem_piFinset.mp ha) (sourceOriginalProbeAuxGroup434 m nu z))
    simpa only [he] using (h.1 i).2
  · intro he
    apply (hNo z).2
    have h := (source_ordered_marks_mem434 _ _ _ _).mp ((Fintype.mem_piFinset.mp hb) (sourceOriginalProbeAuxGroup434 m nu z))
    simpa only [he] using (h.1 i).2

/-- The actual collision slice vanishes off its true endpoint-divisor
support, before absolute values or auxiliary integration. -/
theorem parity_canonical_free_collision_eq_zero434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G→Finset ℕ) (V : G→ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (q : ℝ) (w wp : ℕ)
    (hNo : ∀ z,¬aux z∣w ∧ ¬aux z∣wp) :
    parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp=0 := by
  unfold parityCanonicalFreeCollisionSlice434
  dsimp only
  have hz : (∑ a∈bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) w,
      ∑ b∈bigMarkLists P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) wp,
        if sourceB574FreeAuxBan434 J ell m hmJ nu aux a b then (0:ℂ)
        else sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux a b)=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    rw [if_pos (parity_free_aux_ban_of_no_divisor434 J ell m hmJ nu P aux w wp a b ha hb hNo)]
  rw [hz,mul_zero]

theorem parity_canonical_free_collision_divisor_support434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G→Finset ℕ) (V : G→ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (q : ℝ) (w wp : ℕ)
    (h : parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp≠0) :
    ∃ z,aux z∣w ∨ aux z∣wp := by
  by_contra hn
  push_neg at hn
  exact h (parity_canonical_free_collision_eq_zero434 J ell m hmJ nu Q hA hB xi P V aux q w wp hn)

/-- The original true-cell/all-conductor bound controls the COMPLETE
collision Knu directly. Both inverse cell masses remain Q^4*xi^-2; no
triangle estimate over an artificial collection of rank coefficients. -/
theorem parity_canonical_free_collision_marked_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G→Finset ℕ) (V : G→ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (q : ℝ) (w wp : ℕ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi) :
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    ‖parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp‖ ≤
      ((Q:ℝ)^4*(xi⁻¹)^2)*‖actualBigMarkDecoration P t q V (fun _=>1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _=>1) wp‖ := by
  dsimp only
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let K := fun a b=>if sourceB574FreeAuxBan434 J ell m hmJ nu aux a b then (0:ℂ)
    else sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux a b
  let cap : ℝ := (Q:ℝ)^4*(xi⁻¹)^2
  have hCap : 0≤ cap := by dsimp only [cap];positivity
  have hK (a b) : ‖K a b‖≤ cap := by
    dsimp only [K]
    split_ifs
    · simpa only [norm_zero] using hCap
    · exact source_original_probe_canonical_Knu_true_uniform434 J ell m hmJ nu Q hA hB xi hhA hhB hxi P V aux a b
  have hrow : ‖∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,K a b‖≤
      cap*(bigMarkLists P t w).card*(bigMarkLists P t wp).card := by
    calc
      _ ≤ ∑ a∈bigMarkLists P t w,‖∑ b∈bigMarkLists P t wp,K a b‖ := norm_sum_le _ _
      _ ≤ ∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,‖K a b‖ :=
        Finset.sum_le_sum (fun a _=>norm_sum_le _ _)
      _ ≤ ∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,cap :=
        Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>hK a b))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul];ring
  have hOne (n : ℕ) : ‖actualBigMarkDecoration P t q V (fun _=>1) n‖=
      ‖bigMarkPrefactor P t q V n‖*(bigMarkLists P t n).card := by simp [actualBigMarkDecoration]
  change ‖bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
    (∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,K a b)‖≤_
  rw [norm_mul,norm_mul]
  calc
    _ ≤ ‖bigMarkPrefactor P t q V w‖*‖bigMarkPrefactor P t q V wp‖*
        (cap*(bigMarkLists P t w).card*(bigMarkLists P t wp).card) :=
      mul_le_mul_of_nonneg_left hrow (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by rw [hOne,hOne];dsimp only [cap];ring

/-- The signed shift by an auxiliary multiple makes the two endpoint
p-divisibility events identical. This uses the true product D. -/
theorem parity_aux_shift_divisor434
    (p D w wp : ℕ) (k : ℤ) (hpD : p∣D) (hwp : 0<wp)
    (hShift : (wp:ℤ)=(w:ℤ)+k*(D:ℤ)) : p∣wp ↔ p∣w := by
  obtain ⟨d,rfl⟩ := hpD
  have he : (w:ℤ)+k*(p:ℤ)*(d:ℤ)=(wp:ℤ) := by
    simpa only [Nat.cast_mul,mul_assoc] using hShift.symm
  have hpos : 0<(w:ℤ)+k*(p:ℤ)*(d:ℤ) := by rw [he];exact_mod_cast hwp
  have h := source_auxiliary_shift_divisibility434 p w d k hpos
  simpa only [he,Int.toNat_natCast] using h

theorem parity_canonical_free_collision_shift_support434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G→Finset ℕ) (V : G→ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (q : ℝ) (D w wp : ℕ) (k : ℤ)
    (hD : ∀ z,aux z∣D) (hwp : 0<wp) (hShift : (wp:ℤ)=(w:ℤ)+k*(D:ℤ))
    (h : parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp≠0) :
    ∃ z,aux z∣w := by
  obtain ⟨z,hz⟩ := parity_canonical_free_collision_divisor_support434 J ell m hmJ nu Q hA hB xi P V aux q w wp h
  refine ⟨z,?_⟩
  exact hz.elim id (parity_aux_shift_divisor434 (aux z) D w wp k (hD z) hwp hShift).mp

/-- Support-aware actual collision majorant with the original Knu bound.
The indicator is not averaged using mass one: its harmonic saving must
come from the genuine p-divisibility and the rescaled cutoff/shift. -/
theorem parity_canonical_free_collision_shift_marked434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G→Finset ℕ) (V : G→ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu→ℕ) (q : ℝ) (D w wp : ℕ) (k : ℤ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
    (hD : ∀ z,aux z∣D) (hwp : 0<wp) (hShift : (wp:ℤ)=(w:ℤ)+k*(D:ℤ)) :
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    ‖parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp‖ ≤
      (if ∃ z,aux z∣w then (1:ℝ) else 0)*
      ((Q:ℝ)^4*(xi⁻¹)^2)*‖actualBigMarkDecoration P t q V (fun _=>1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _=>1) wp‖ := by
  dsimp only
  by_cases hHit : ∃ z,aux z∣w
  · rw [if_pos hHit,one_mul]
    exact parity_canonical_free_collision_marked_bound434 J ell m hmJ nu Q hA hB xi P V aux q w wp hhA hhB hxi
  · have hz : parityCanonicalFreeCollisionSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp=0 := by
      by_contra hn
      exact hHit (parity_canonical_free_collision_shift_support434 J ell m hmJ nu Q hA hB xi P V aux q D w wp k hD hwp hShift hn)
    simp only [hz,norm_zero,if_neg hHit,zero_mul,le_refl]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceQSkipComparisonBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact SOURCE comparison C,hC,hCBudget,hcBound fields, with the actual
sorted QSkip residual at the literal r=6 moving depth and source factorial.
This does not invent a new comparison record or change other fields. -/
theorem source_original_QSkip_comparison_c_fields434
    (cfg : SourceComparisonFixed434) (L : ℝ) (hL : 1 ≤ L)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (i : Fin 6)
    (δ : Fin (sourceOrderedLabels 6
       (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b i).length → Bool)
    (ξ : Fin (sourceOrderedLabels 6
       (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b i).length → ℝ) :
    let d := sourceOriginalLiteralDepth 6 L
    let n := (sourceOrderedLabels 6 (sourceActualSortedScales 6 d L) b i).length
    let Q := sourceActualSortedQ 6 d L b i
    let s := sourceActualSortedFrequencyScales 6 d L b i
    let c : ℕ → ℂ := fun v =>
      sourceEndpointFibre (Finset.univ : Finset (OrderedQSkip n Q δ))
        orderedSkipProduct
        (fun a => sourceActualSortedFactorial 6 d * orderedSkipPhase s (-ξ) a) v
    (0:ℝ) ≤ 1 ∧ 1 ≤ L^cfg.ec ∧ ∀ v, ‖c v‖ ≤ 1 := by
  dsimp only
  refine ⟨by norm_num, one_le_pow₀ hL, ?_⟩
  intro v
  exact source_native_original_six_QSkip_negative_frequency_c434
    L (lt_of_lt_of_le (by norm_num) hL) b i δ ξ v
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## SourceNativeQSkipComparisonData -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Literal ORIGINAL r=6 moving-depth factorial normalized ordered
QSkip complementary-divisor residual c(v), including every
Boolean allocation, original SORTED Q-band label, repeat-valued
prime assignment and NEGATIVE source Fourier frequency -xi.
The object is sourceEndpointFibre itself and NOT an abstract bounded
complex surrogate. -/
noncomputable def sourceNativeOriginalLiteralResidual434
    (L : ℝ)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (δ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L)
      b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L)
      b slot).length → ℝ) : ℕ → ℂ :=
  let d := sourceOriginalLiteralDepth 6 L
  let n := (sourceOrderedLabels 6 (sourceActualSortedScales 6 d L)
    b slot).length
  let Q := sourceActualSortedQ 6 d L b slot
  let s := sourceActualSortedFrequencyScales 6 d L b slot
  fun v => sourceEndpointFibre
    (Finset.univ : Finset (OrderedQSkip n Q δ))
    orderedSkipProduct
    (fun a => sourceActualSortedFactorial 6 d *
      orderedSkipPhase s (-ξ) a) v

/-- Install the ACTUAL ORIGINAL QSkip residual in ANY already
constructed unchanged SOURCE03 comparison record, preserving
its exact endpoint/prime groups/marks, test alpha, characters,
Mellin phases and physical parity field. The sole rewritten
record fields are c, C and their three logical bounds. The
preverified literal source r=6 factorial theorem supplies
   C=1, 0≤C, C≤L^ec, ∀v ||c(v)||≤1
with no assumption on c beyond its exact definition.

This is a correct source-data FIELD adapter; it does NOT
claim construction of the remaining original data fields from
native cells, nor equality to a preexisting generic record's
old c if that old c was not the actual SOURCE03 residual. -/
noncomputable def sourceNativeOriginalComparisonWithActualQSkip434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (hL : 1 ≤ L)
    (data : SourceComparisonData434 ι β cfg x L Y Hprime)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (δ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L)
      b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L)
      b slot).length → ℝ) :
    SourceComparisonData434 ι β cfg x L Y Hprime := by
  have hField := source_original_QSkip_comparison_c_fields434
    cfg L hL b slot δ ξ
  exact { data with
    c := sourceNativeOriginalLiteralResidual434 L b slot δ ξ
    C := 1
    hC := hField.1
    hCBudget := hField.2.1
    hcBound := hField.2.2 }

/-- Every arithmetic field of the original comparison record,
including both endpoint prime families, original signed Ptw and
source D20 alpha, remains definitionally unchanged under exact
c(v) installation. This precludes accidental renormalization of
SourceComparisonData parameters when binding the real factorial
residual. -/
theorem source_native_original_QSkip_comparison_preserves_fields434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (hL : 1 ≤ L)
    (data : SourceComparisonData434 ι β cfg x L Y Hprime)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (δ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L)
      b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L)
      b slot).length → ℝ) :
    let updated := sourceNativeOriginalComparisonWithActualQSkip434
      cfg x L Y Hprime hL data b slot δ ξ
    updated.c = sourceNativeOriginalLiteralResidual434 L b slot δ ξ ∧
    updated.C = 1 ∧
    updated.alpha = data.alpha ∧
    updated.G = data.G ∧
    updated.Ptw = data.Ptw ∧
    updated.S = data.S ∧
    updated.Ts = data.Ts ∧
    updated.Tb = data.Tb ∧
    updated.Vs = data.Vs ∧
    updated.Vsmall = data.Vsmall ∧
    updated.Vbig = data.Vbig ∧
    updated.k = data.k ∧
    updated.qBase = data.qBase ∧
    updated.chi0 = data.chi0 ∧
    updated.sigma0 = data.sigma0 ∧
    updated.sigma1 = data.sigma1 := by
  dsimp [sourceNativeOriginalComparisonWithActualQSkip434]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceQSkipDesignatedExponentGates -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Actual source designated Q_j with r=6: the exponent τ is positive,
η=(6/5)τ is strictly larger, and η<1/4. This is the original
designated Q family (every j, including j=0), not an auxiliary band. -/
theorem original_source_r6_designated_Q_exponent_gates434 (j : ℕ) :
    0 < sourceOriginalQActualExponent 6 j ∧
    sourceOriginalQActualExponent 6 j <
      (6/5:ℝ)*sourceOriginalQActualExponent 6 j ∧
    (6/5:ℝ)*sourceOriginalQActualExponent 6 j < 1/4 := by
  let q : ℝ := (2:ℝ)^j
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hτ : sourceOriginalQActualExponent 6 j = 5/(66*q) := by
    unfold sourceOriginalQActualExponent sourceOriginalQ0Scale
    dsimp [q]
    norm_num
    ring
  have hτpos : 0 < sourceOriginalQActualExponent 6 j := by
    rw [hτ]
    positivity
  have hηeq :
      (6/5:ℝ)*sourceOriginalQActualExponent 6 j = 1/(11*q) := by
    rw [hτ]
    field_simp
    ring
  have hηpos : (0:ℝ) < (1/(11*q)) := by positivity
  have hηlt : (1/(11*q):ℝ) < 1/4 := by
    apply (div_lt_iff₀ (by positivity : 0 < 11*q)).2
    nlinarith
  refine ⟨hτpos, ?_, ?_⟩
  · have hdiff : (1:ℝ) < 6/5 := by norm_num
    nlinarith [mul_pos (by norm_num : (0:ℝ)<1/5) hτpos]
  · rwa [hηeq]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalR6Fixed -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Complete ORIGINAL SOURCE03 fixed comparison configuration for
the REAL designated r=6 Q-band index jQ selected BEFORE L.
All exponent bands and masses are exactly source:
  aexp=1/10, bexp=1/5, cexp=3/10;
  tau=sourceOriginalQActualExponent 6 jQ,
  eta=6/5*tau, C0=4, vmin=log(6/5)/2;
  q0=1/2, A=64, Cpsi=epsi=ea=ec=s1base=0, fcut=3.
The original J shared slots are NOT identified with tmax;
tmax=1+mmax limits only endpoint free marks.

The remaining fixed profile derivative budget Kpsi, Carc,Cchi,
frequency exponents s0,vexp, and shift scale CZ are explicitly
provided by the true source outer/inner Fourier preparation.
Their own physical quantitative gates are NOT claimed here. -/
noncomputable def sourceNativeOriginalR6Fixed434
    (jQ : ℕ) (mmax cm s0 vexp : ℕ)
    (Carc Cχ CZ : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc)
    (hCχ : (cm:ℝ) ≤ Cχ)
    (hCχpos : 0 < Cχ)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    SourceComparisonFixed434 := by
  let τ : ℝ := sourceOriginalQActualExponent 6 jQ
  have hτ := original_source_r6_designated_Q_exponent_gates434 jQ
  have hv : 0 < Real.log (6/5:ℝ)/2 := by
    apply div_pos
    · exact Real.log_pos (by norm_num)
    · norm_num
  exact {
    aexp := 1/10
    bexp := 1/5
    cexp := 3/10
    Carc := Carc
    CZ := CZ
    τ := τ
    η := (6/5:ℝ)*τ
    Cχ := Cχ
    C0 := 4
    q0 := 1/2
    vmin := Real.log (6/5:ℝ)/2
    A := 64
    Cpsi := 0
    Kpsi := Kpsi
    tmax := 1+mmax
    ea := 0
    ec := 0
    s0 := s0
    cm := cm
    s1base := 0
    vexp := vexp
    fcut := 3
    epsi := 0
    hA := by norm_num
    hCpsi := by norm_num
    hKpsi := hKpsi
    hepsi := by norm_num
    hFcut := by norm_num
    haexp := by norm_num
    hab := by norm_num
    hb := by norm_num
    hbc := by norm_num
    hτ := hτ.1
    hτη := hτ.2.1
    hη := hτ.2.2
    hCχ := hCχpos
    hC0 := by norm_num
    hCarc := (Nat.cast_nonneg cm).trans hCarc
    hq0 := by norm_num
    hq1 := by norm_num
    hv := hv
    hcmChar := hCχ
    hcmArc := hCarc
  }

/-- Source fixed original r=6 construction preserves the exact
Q-band exponent and original P harmonic floor as definitional
equalities. No silent use of an arbitrary general admissible τ. -/
theorem source_native_original_r6_fixed_literal_fields434
    (jQ : ℕ) (mmax cm s0 vexp : ℕ)
    (Carc Cχ CZ : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ)
    (hCχpos : 0 < Cχ)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg := sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp
      Carc Cχ CZ hCarc hCχ hCχpos Kpsi hKpsi
    cfg.τ = sourceOriginalQActualExponent 6 jQ ∧
    cfg.η = (6/5:ℝ)*sourceOriginalQActualExponent 6 jQ ∧
    cfg.vmin = Real.log (6/5:ℝ)/2 ∧
    cfg.q0 = 1/2 ∧
    cfg.A = 64 ∧ cfg.tmax = 1+mmax ∧ cfg.C0=4 := by
  dsimp [sourceNativeOriginalR6Fixed434]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CanonicalSliceEventual -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Genuine ORIGINAL SOURCE03 canonical S/Ts/Tb prime slice on the
unbounded exact r=6 cofinal geometric scales L_N=((3/2)*2^N)^10.
Every prime band is the literal original source P_g. The S and
Ts harmonic masses, full BIG integer prime intervals, all group
disjointness and the C0=4 cardinal count constraints are proved
using the actual r=6 source group input, not independently assumed.
No dummy P group, no artificial canonical slice, and no replacement
of the source Q/OLD/CRT/Type II fields.

For any fixed authentic original r=6 source config with its
aexp=1/10, bexp=1/5, cexp=3/10, C0=4, vmin=log(6/5)/2,
we obtain an actual SourceOriginalSource03CanonicalPrimeSlice434
with n=N, T=N, d=2/5, vmax=5, c0=1. This is NOT yet a complete
SourceComparisonData434. -/
theorem eventually_source_native_r6_actual_CANONICAL_prime_slice434
    (cfg : SourceComparisonFixed434)
    (ha : cfg.aexp = 1/10)
    (hb : cfg.bexp = 1/5)
    (hc : cfg.cexp = 3/10)
    (hC0 : cfg.C0 = 4)
    (hv : cfg.vmin = Real.log (6/5:ℝ)/2) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧
      Nonempty (SourceOriginalSource03CanonicalPrimeSlice434
        N cfg (sourceNativeR6CofinalL434 N) (2/5) 5 1) := by
  classical
  have hCof := source_native_r6_cofinal_L_tendsto_atTop434
  filter_upwards [
    eventually_ge_atTop (1:ℕ),
    hCof.eventually (eventually_native_original_ALL_P_masses434 6),
    hCof.eventually (eventually_native_original_ALL_P_two_distinct_primes434 6)]
    with N hN hMass hTwo
  let z := source_native_r6_original_canonical_prime_slice434
    N hN cfg ha hb hc hC0 hv hMass hTwo.2
  exact ⟨hN, ⟨z⟩⟩

/-- The literal fixed SOURCE03 r=6 numerical comparison cfg
automatically meets all five native canonical prime-slice fields.
The original selected designated Q-band jQ, exact factorial
QSkip residual and its own outside-Mellin/Fourier budgets are
held unchanged; no profile is retuned on the cofinal subsequence. -/
theorem eventually_source_native_r6_original_fixed_CANONICAL_slice434
    (jQ mmax cm s0 vexp : ℕ)
    (Carc Cχ CZ : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ)
    (hCχpos : 0 < Cχ)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg := sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp
      Carc Cχ CZ hCarc hCχ hCχpos Kpsi hKpsi
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧
      Nonempty (SourceOriginalSource03CanonicalPrimeSlice434
        N cfg (sourceNativeR6CofinalL434 N) (2/5) 5 1) := by
  dsimp only
  exact eventually_source_native_r6_actual_CANONICAL_prime_slice434
    (sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp
      Carc Cχ CZ hCarc hCχ hCχpos Kpsi hKpsi)
    rfl rfl rfl rfl rfl
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeTrueBIGScalarGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Original SOURCE03 scalar comparison geometry with a GENUINE
nonempty BIG free Hprime=q1*q2, each q_i an actual original BIG
source auxiliary prime:
x=exp L, Z=x, Hprime=U1*U2, Y=Z*Hprime,
Ncap=floor(x^2), A=64.
For ALL sufficiently large L, uniformly in the two chosen
BIG source groups and independent original aux drawings,
the following exact comparison requirements hold:

hY,hYmax,hH,hYstrong,hZ,hNcap,hCap,
hHIdent,hHband,hArcCap.

The source q prime groups, TRUE ORIGINAL factorial c(v),
dyadic alpha/rough support, psi/Fourier/character budgets and
physical K/OLD/CRT signed D61 integral remain SEPARATE.
This lemma is NOT a fabricated full SourceComparisonData434. -/
theorem eventually_native_original_TRUE_BIG_source_scalar_geometry434
    (r : ℕ) (Carc CZ : ℝ)
    (hCarc : 0 ≤ Carc) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∀ (aux : SourceBigAux (SourceNativeMemoryBP434 r L) 1 1
          (source_native_actual_J1_m1_pattern434 r L))
        (g1 g2 : sourceNativeOriginalBigType434 r L),
      let q1 := source_native_original_TRUE_BIG_free_prime434 r L aux g1
      let q2 := source_native_original_TRUE_BIG_free_prime434 r L aux g2
      let U1 : ℝ := (q1:ℝ)
      let U2 : ℝ := (q2:ℝ)
      let Hprime : ℝ := U1*U2
      let x : ℝ := Real.exp L
      let Z : ℝ := x
      let Y : ℝ := Z*Hprime
      let Ncap : ℕ := ⌊x^2⌋₊
      (4:ℝ) ≤ Y ∧
      Y ≤ Real.exp (3*L/2) ∧
      0 < Hprime ∧
      Real.exp (3*L/4) ≤ Y ∧
      x*L^(-CZ) ≤ Z ∧
      (Ncap:ℝ) ≤ x^2 ∧
      64*Y ≤ (Ncap:ℝ) ∧
      Y=Z*Hprime ∧
      2 ≤ Hprime/L^Carc ∧
      Hprime/L^Carc ≤ Y/(8*64) := by
  classical
  have ht := (tendsto_rpow_atTop
    (by norm_num : (0:ℝ)<(3/5:ℝ))).eventually
      (eventually_ge_atTop (8:ℝ))
  filter_upwards [
    ht,
    eventually_native_original_TRUE_BIG_Hprime_hHband434
      r Carc hCarc,
    eventually_ge_atTop (1000:ℝ)]
    with L hLp35 hHband hL1000
  refine ⟨(by linarith : (1:ℝ)≤L), ?_⟩
  intro aux g1 g2
  let q1 := source_native_original_TRUE_BIG_free_prime434 r L aux g1
  let q2 := source_native_original_TRUE_BIG_free_prime434 r L aux g2
  let U1 : ℝ := (q1:ℝ)
  let U2 : ℝ := (q2:ℝ)
  let Hprime : ℝ := U1*U2
  let x : ℝ := Real.exp L
  let Z : ℝ := x
  let Y : ℝ := Z*Hprime
  let Ncap : ℕ := ⌊x^2⌋₊
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hQ1 := source_native_original_TRUE_BIG_free_prime_bounds434
    r L aux g1
  have hQ2 := source_native_original_TRUE_BIG_free_prime_bounds434
    r L aux g2
  have hQ1pos : 0 < U1 := by
    change (0:ℝ) < (q1:ℝ)
    exact_mod_cast hQ1.1.pos
  have hQ2pos : 0 < U2 := by
    change (0:ℝ) < (q2:ℝ)
    exact_mod_cast hQ2.1.pos
  have hHpos : 0 < Hprime := mul_pos hQ1pos hQ2pos
  have hHlo : 1 ≤ Hprime := by
    have h1 : (1:ℝ)≤U1 := by
      change (1:ℝ) ≤ (q1:ℝ)
      exact_mod_cast hQ1.1.one_le
    have h2 : (1:ℝ)≤U2 := by
      change (1:ℝ) ≤ (q2:ℝ)
      exact_mod_cast hQ2.1.one_le
    dsimp [Hprime]
    nlinarith
  have hHhi : Hprime ≤ Real.exp (2*L^(2/5:ℝ)) := by
    dsimp [Hprime,U1,U2]
    calc
      ((q1:ℝ)*(q2:ℝ)) ≤
        Real.exp (L^(2/5:ℝ)) *
        Real.exp (L^(2/5:ℝ)) :=
          mul_le_mul hQ1.2.2 hQ2.2.2
            (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2*L^(2/5:ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hPow : L^(2/5:ℝ)*L^(3/5:ℝ)=L := by
    rw [←Real.rpow_add hLpos]
    norm_num
  have hSmall : 2*L^(2/5:ℝ) ≤ L/4 := by
    have hpow0 : 0 ≤ L^(2/5:ℝ) := Real.rpow_nonneg hLpos.le _
    have hmul := mul_le_mul_of_nonneg_left hLp35 hpow0
    nlinarith [hPow,hmul]
  have hYhi : Y ≤ Real.exp (5*L/4) := by
    change x*Hprime ≤ Real.exp (5*L/4)
    have he : Real.exp (2*L^(2/5:ℝ)) ≤ Real.exp (L/4) :=
      Real.exp_le_exp.mpr hSmall
    calc
      x*Hprime ≤ Real.exp L*Real.exp (2*L^(2/5:ℝ)) :=
        mul_le_mul_of_nonneg_left hHhi (Real.exp_pos _).le
      _ ≤ Real.exp L*Real.exp (L/4) :=
        mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
      _ = Real.exp (5*L/4) := by
        rw [←Real.exp_add]
        congr 1
        ring
  have hYpos : 0 < Y := mul_pos (Real.exp_pos L) hHpos
  have hYlo : Real.exp L ≤ Y := by
    change Real.exp L ≤ Real.exp L*Hprime
    nlinarith [mul_le_mul_of_nonneg_left hHlo (Real.exp_pos L).le]
  have hx2 : x^2 = Real.exp (2*L) := by
    dsimp [x]
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have hCapPower : (128:ℝ) ≤ Real.exp (3*L/4) := by
    have hh := Real.add_one_le_exp (3*L/4)
    nlinarith [hL1000]
  have hCapHalf : 64*Y ≤ x^2/2 := by
    have hBound :
        (128:ℝ)*Real.exp (5*L/4) ≤
          Real.exp (2*L) := by
      have hm := mul_le_mul_of_nonneg_left hCapPower
        (Real.exp_pos (5*L/4)).le
      calc
        (128:ℝ)*Real.exp (5*L/4) ≤
          Real.exp (5*L/4)*Real.exp (3*L/4) := by
            nlinarith [hm]
        _ = Real.exp (2*L) := by
          rw [←Real.exp_add]
          congr 1
          ring
    rw [hx2]
    nlinarith [hYhi,hBound]
  have hFloor : 64*Y ≤ (Ncap:ℝ) := by
    have hfloor : x^2 < (Ncap:ℝ)+1 := by
      exact Nat.lt_floor_add_one (x^2)
    have hxlarge : (2:ℝ) ≤ x^2 := by
      rw [hx2]
      have hh := Real.add_one_le_exp (2*L)
      linarith
    linarith [hCapHalf,hfloor,hxlarge]
  have hHband : 2 ≤ Hprime/L^Carc :=
    hHband.2 aux g1 g2
  have hZcap : x*L^(-CZ) ≤ Z := by
    have hp : L^(-CZ) ≤ 1 := by
      have hh := Real.rpow_le_rpow_of_exponent_le
        hL1 (by linarith : -CZ ≤ (0:ℝ))
      simpa using hh
    change Real.exp L*L^(-CZ) ≤ Real.exp L
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hp (Real.exp_pos L).le)
  have hArc : Hprime/L^Carc ≤ Y/(8*64) := by
    have hLpow : 1 ≤ L^Carc := Real.one_le_rpow hL1 hCarc
    have hExp512 : (512:ℝ) ≤ x := by
      dsimp [x]
      have hh := Real.add_one_le_exp L
      linarith
    have hXA : (512:ℝ) ≤ Z*L^Carc := by
      dsimp [Z]
      nlinarith [mul_le_mul_of_nonneg_left hLpow
        (Real.exp_pos L).le,hExp512]
    have hLpos : 0 < L^Carc := Real.rpow_pos_of_pos hLpos _
    have hDen : (0:ℝ)<8*64 := by norm_num
    apply (div_le_div_iff₀ hLpos hDen).mpr
    dsimp [Y,Z]
    nlinarith [hHpos,hXA]
  have hYmax : Y ≤ Real.exp (3*L/2) := by
    exact hYhi.trans (Real.exp_le_exp.mpr (by linarith))
  have hYstrong : Real.exp (3*L/4) ≤ Y := by
    exact (Real.exp_le_exp.mpr (by linarith)).trans hYlo
  have hY4 : (4:ℝ) ≤ Y := by
    have hExp : (4:ℝ) ≤ Real.exp L := by
      have hh := Real.add_one_le_exp L
      linarith [hL1000]
    exact hExp.trans hYlo
  have hNcap : (Ncap:ℝ) ≤ x^2 := Nat.floor_le (sq_nonneg _)
  exact ⟨hY4,hYmax,hHpos,hYstrong,hZcap,hNcap,hFloor,rfl,
    hHband,hArc⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CanonicalBIGPacket -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Simultaneous source-faithful ORIGINAL r=6 canonical
SOURCE03 prime-slice and genuine independent BIG free sector.

On the SAME unbounded cofinal L_N, N>=2:
  * S + N actual Ts + N actual Tb with exact P prime bands,
    harmonic masses, Fintype group counts and group disjointness;
  * their canonical z.G is literally the entire native original G;
  * source J=1,m=1 free BIG sets are nonempty in EVERY BIG group;
  * all auxiliary primes are source Tb primes and avoid original
    positive endpoint w's prime divisors, with w<=exp(2L);
  * actual four-sign common-J RAW scalar has Re >= 1/2;
  * g1!=g2 are two actual distinct BIG groups in the original
    physical family, so the two source BIG-free factors q1,q2
    genuinely come from independently labelled group slots;
  * x=Z=exp(L), Hprime=q1*q2, Y=x*Hprime,
    Ncap=floor(x²) satisfy all TEN literal original
    SOURCE03 scalar comparison-size and arc constraints.

The theorem does NOT construct Fock/OLD edge legality,
complete SourceComparisonData434, QSkip/K matching or signed
D61 two-Fourier Type II. -/
theorem eventually_source_native_r6_CANONICAL_REAL_BIG_packet434
    (jQ mmax cm s0 vexp : ℕ)
    (Carc Cχ CZ : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ)
    (hCχpos : 0 < Cχ) (hCZ : 0 ≤ CZ)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg := sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp
      Carc Cχ CZ hCarc hCχ hCχpos Kpsi hKpsi
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧
      ∃ (z : SourceOriginalSource03CanonicalPrimeSlice434
            N cfg (sourceNativeR6CofinalL434 N) (2/5) 5 1)
        (w : ℕ)
        (A : SourceNativeOriginalAllP434 6
          (sourceNativeR6CofinalL434 N) → Finset ℕ)
        (aux : SourceBigAux
          (SourceNativeMemoryBP434 6
            (sourceNativeR6CofinalL434 N)) 1 1
          (source_native_actual_J1_m1_pattern434 6
            (sourceNativeR6CofinalL434 N)))
        (g1 g2 : sourceNativeOriginalBigType434 6
          (sourceNativeR6CofinalL434 N)),
      g1 ≠ g2 ∧
      z.G = sourceNativeOriginalG434 6
        (sourceNativeR6CofinalL434 N) ∧
      0 < w ∧
      (w:ℝ) ≤ Real.exp (2*sourceNativeR6CofinalL434 N) ∧
      (∀ g, 0 < (A g).card) ∧
      (∀ g, A g ⊆ w.primeFactors) ∧
      (∀ (g : sourceNativeOriginalBigType434 6
          (sourceNativeR6CofinalL434 N))
          (j : ↥((source_native_actual_J1_m1_pattern434 6
            (sourceNativeR6CofinalL434 N)).free g)),
        (aux g j).val ∉ w.primeFactors) ∧
      (1/2:ℝ) ≤
        (sourceNativeOriginalALLPJTrueProjectedRAW434 6
          (sourceNativeR6CofinalL434 N) 1
          (sourceNativeOriginalG434 6
            (sourceNativeR6CofinalL434 N)) A A).re ∧
      let L := sourceNativeR6CofinalL434 N;
      let q1 := source_native_original_TRUE_BIG_free_prime434 6 L
        aux g1;
      let q2 := source_native_original_TRUE_BIG_free_prime434 6 L
        aux g2;
      let x : ℝ := Real.exp L;
      let Hprime : ℝ := (q1:ℝ)*(q2:ℝ);
      let Y : ℝ := x*Hprime;
      let Ncap : ℕ := ⌊x^2⌋₊;
      (4:ℝ) ≤ Y ∧
      Y ≤ Real.exp (3*L/2) ∧
      0 < Hprime ∧
      Real.exp (3*L/4) ≤ Y ∧
      x*L^(-cfg.CZ) ≤ x ∧
      (Ncap:ℝ) ≤ x^2 ∧
      64*Y ≤ (Ncap:ℝ) ∧
      2 ≤ Hprime/L^cfg.Carc ∧
      Hprime/L^cfg.Carc ≤ Y/(8*64) := by
  classical
  let cfg := sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp
    Carc Cχ CZ hCarc hCχ hCχpos Kpsi hKpsi
  have hCarc0 : 0 ≤ Carc := (Nat.cast_nonneg cm).trans hCarc
  have hT := source_native_r6_cofinal_L_tendsto_atTop434
  filter_upwards [
    hT.eventually (eventually_native_original_ALL_P_masses434 6),
    hT.eventually (eventually_native_original_ALL_P_two_distinct_primes434 6),
    eventually_native_r6_NONVACUOUS_BIG_FREE_J1_RAW_positive434,
    hT.eventually
      (eventually_native_original_TRUE_BIG_source_scalar_geometry434
        6 Carc CZ hCarc0 hCZ),
    eventually_ge_atTop (2:ℕ)] with N hMass hTwo hFree hScalar hN
  let L := sourceNativeR6CofinalL434 N
  let z := source_native_r6_original_canonical_prime_slice434
    N (by omega : 1 ≤ N) cfg rfl rfl rfl rfl rfl
    hMass hTwo.2
  obtain ⟨w,A,pat,aux,hw,hW,hAp,hAsub,hFreeCard,hAux,hZ,hRe⟩ :=
    hFree.2
  let eBig := source_native_r6_cofinal_Tb_Fin_equiv434 N
  let g1 : sourceNativeOriginalBigType434 6 L :=
    eBig ⟨0,by omega⟩
  let g2 : sourceNativeOriginalBigType434 6 L :=
    eBig ⟨1,by omega⟩
  have hneq : g1≠g2 := by
    intro heq
    have hh := eBig.injective heq
    have hv : (⟨0,by omega⟩ : Fin N) = ⟨1,by omega⟩ := hh
    have : (0:ℕ) = 1 := congrArg Fin.val hv
    omega
  have hTb (i : Fin N) :
      z.Tb i = source_native_r6_canonical_Tb434 N i := by
    change sourceOriginalActualPrimeBand434
      (sourceNativeOriginalBigLo434 6 L (eBig i))
      (sourceNativeOriginalBigHi434 6 L (eBig i)) =
      sourceNativeOriginalTb434 6 L (eBig i)
    exact (source_native_original_BIG_root_band_fields434
      6 L hScalar.1 (eBig i)).1.symm
  have hz : z.G = sourceNativeOriginalG434 6 L := by
    have hG : z.G =
      (source_native_r6_canonical_P434 N none ∪
        (Finset.univ : Finset (Fin N)).biUnion
          (fun i => source_native_r6_canonical_P434 N (some i))) ∪
      (Finset.univ : Finset (Fin N)).biUnion
        (fun i => z.Tb i) := by rfl
    rw [hG]
    simp_rw [hTb]
    exact source_native_r6_canonical_prime_union_eq_G434 N
  have hcfg : cfg.Carc=Carc ∧ cfg.CZ=CZ := by
    dsimp [cfg,sourceNativeOriginalR6Fixed434]
    exact ⟨rfl,rfl⟩
  -- The explicit original dependent pattern is by construction
  -- source_native_actual_J1_m1_pattern434. Use definitional
  -- equality of the existing true aux sector, not a surrogate.
  have hpat : pat = source_native_actual_J1_m1_pattern434 6 L := by
    cases pat with
    | mk free free_bound =>
      have hFree : free = (fun _ => ({0} : Finset (Fin 1))) := by
        funext g
        have hc : (free g).card = 1 := hFreeCard g
        have he : free g = Finset.univ :=
          Finset.eq_univ_of_card (free g)
            (by simpa using hc)
        rw [he]
        apply Finset.ext
        intro i
        fin_cases i
        simp
      subst free
      apply congrArg
      exact Subsingleton.elim _ _
  cases hpat
  -- At this point the supplied \`aux\` is the literal original
  -- dependent BIG free auxiliary for J=1,m=1 and each group.
  have hGeom := hScalar.2 aux g1 g2
  dsimp [cfg,sourceNativeOriginalR6Fixed434] at hGeom
  refine ⟨hN,z,w,A,aux,g1,g2,hneq,hz,hw,hW,hAp,hAsub,hAux,hRe,?_⟩
  dsimp only
  rcases hGeom with ⟨h4,hYmax,hHpos,hYstrong,hZcap,hNcap,h64,hYident,hHband,hArc⟩
  exact ⟨h4,hYmax,hHpos,hYstrong,hZcap,hNcap,h64,hHband,hArc⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6CanonicalFockSameBands -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- True SAME-SOURCE bridge: the original SOURCE03 canonical
r=6 prime-slice \`z\`, with exact SMALL S and N Ts plus N BIG
Tb bands, and an ACTUALLY LEGAL source Fock/OLD edge live
AT THE SAME cofinal physical scale L_N.

Unlike independent existence of a canonical slice and a Fock edge,
the physical BIG source endpoint (x.2 g).1 0, its actual BIG target
(b.bigChoice g).1 0 and the independent BIG-free auxiliary aux g 0
are proved to belong to EXACTLY the matching z.Tb group under
the real original Fin N <-> native BIG index equivalence.

The original source J=1,m=1, orientation 1, signed k=2,
full legal Fock tests, active endpoint prime labels and zero OLD
sector are unchanged. This proves a genuine common-source interface,
NOT a nonzero global K_nu, actual comparison-integral or Green64.
-/
theorem eventually_source_native_r6_CANONICAL_FOCK_same_bands434
    (cfg : SourceComparisonFixed434)
    (ha : cfg.aexp = 1/10) (hb : cfg.bexp = 1/5)
    (hc : cfg.cexp = 3/10) (hC0 : cfg.C0 = 4)
    (hv : cfg.vmin = Real.log (6/5:ℝ)/2) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧
      let L := sourceNativeR6CofinalL434 N;
      let hS := source_native_r6_cofinal_SMALL_nonempty434 N;
      let pat := source_native_actual_J1_m1_pattern434 6 L;
      let patterns : Unit → SourcePattern
        (sourceNativeOriginalBigType434 6 L) 1 1 := fun _ => pat;
      ∃ (z : SourceOriginalSource03CanonicalPrimeSlice434
            N cfg L (2/5) 5 1)
        (aux : SourceBigAux (SourceNativeMemoryBP434 6 L) 1 1 pat)
        (x : FullPhysicalState
          (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
          1 (fun _ => 0))
        (b : FullPhysicalEdgeBranch
          (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
          1 (fun _ => 0) x),
      (⟨(),(aux,b)⟩ : SourcePhysicalChoice
          (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
          1 0 1 (fun _ => 0) patterns x) ∈
          legalSourcePhysicalChoices
            (SourceNativeMemorySP434 6 L hS) (fun _ p => p.val)
            (SourceNativeMemoryBP434 6 L) (fun _ p => p.val)
            1 0 1 (fun _ => 0) patterns x 1 2 ∧
      z.G = sourceNativeOriginalG434 6 L ∧
      (∀ i : Fin N,
        let g := source_native_r6_cofinal_Tb_Fin_equiv434 N i;
        ((x.2 g).1 (0:Fin 1)).val ∈ z.Tb i ∧
        ((b.bigChoice g).1 (0:Fin 1)).val ∈ z.Tb i ∧
        (aux g ⟨0,by
          change (0:Fin 1) ∈ ({0} : Finset (Fin 1))
          simp⟩).val
          ∈ z.Tb i) := by
  classical
  have hCof := source_native_r6_cofinal_L_tendsto_atTop434
  filter_upwards [
    eventually_ge_atTop (1:ℕ),
    hCof.eventually (eventually_native_original_ALL_P_masses434 6),
    hCof.eventually (eventually_native_original_ALL_P_two_distinct_primes434 6),
    eventually_source_native_r6_TRUE_FULL_FOCK_legal_nonempty434]
    with N hN hMass hTwo hLegal
  let L := sourceNativeR6CofinalL434 N
  let hS := source_native_r6_cofinal_SMALL_nonempty434 N
  let pat := source_native_actual_J1_m1_pattern434 6 L
  let patterns : Unit → SourcePattern
      (sourceNativeOriginalBigType434 6 L) 1 1 := fun _ => pat
  let z := source_native_r6_original_canonical_prime_slice434
    N hN cfg ha hb hc hC0 hv hMass hTwo.2
  obtain ⟨aux,x,b,hMem,hSmall⟩ := hLegal.2
  have hG : z.G = sourceNativeOriginalG434 6 L := by
    change (source_native_r6_canonical_P434 N none ∪
      (Finset.univ : Finset (Fin N)).biUnion
        (fun i => source_native_r6_canonical_P434 N (some i))) ∪
      (Finset.univ : Finset (Fin N)).biUnion
        (fun i => z.Tb i) =
      sourceNativeOriginalG434 6 L
    have ht : ∀ i, z.Tb i = source_native_r6_canonical_Tb434 N i := by
      intro i
      change sourceOriginalActualPrimeBand434
        (sourceNativeOriginalBigLo434 6 L
          (source_native_r6_cofinal_Tb_Fin_equiv434 N i))
        (sourceNativeOriginalBigHi434 6 L
          (source_native_r6_cofinal_Tb_Fin_equiv434 N i))
        = source_native_r6_canonical_Tb434 N i
      exact (source_native_original_BIG_root_band_fields434
        6 L (by linarith : (1:ℝ)≤L)
        (source_native_r6_cofinal_Tb_Fin_equiv434 N i)).1.symm
    simp_rw [ht]
    exact source_native_r6_canonical_prime_union_eq_G434 N
  have hTb (i : Fin N) :
      z.Tb i = sourceNativeOriginalTb434 6 L
        (source_native_r6_cofinal_Tb_Fin_equiv434 N i) := by
    change sourceOriginalActualPrimeBand434
      (sourceNativeOriginalBigLo434 6 L
        (source_native_r6_cofinal_Tb_Fin_equiv434 N i))
      (sourceNativeOriginalBigHi434 6 L
        (source_native_r6_cofinal_Tb_Fin_equiv434 N i))
      = sourceNativeOriginalTb434 6 L
        (source_native_r6_cofinal_Tb_Fin_equiv434 N i)
    exact (source_native_original_BIG_root_band_fields434
      6 L (by linarith : (1:ℝ)≤L)
      (source_native_r6_cofinal_Tb_Fin_equiv434 N i)).1.symm
  have hPhysical (i : Fin N) :
      let g := source_native_r6_cofinal_Tb_Fin_equiv434 N i
      ((x.2 g).1 (0:Fin 1)).val ∈ z.Tb i ∧
      ((b.bigChoice g).1 (0:Fin 1)).val ∈ z.Tb i ∧
      (aux g ⟨0,by
          change (0:Fin 1) ∈ ({0} : Finset (Fin 1))
          simp⟩).val
        ∈ z.Tb i := by
    dsimp only
    rw [hTb i]
    exact ⟨((x.2 _).1 0).property,
      ((b.bigChoice _).1 0).property,
      (aux _ _).property⟩
  exact ⟨hN,z,aux,x,b,hMem,hG,hPhysical⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalD20ComparisonAlpha -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The exact ORIGINAL full-cell D20 coefficient, with the
unshortened source logarithmic cell ratio, is uniformly bounded
by one, including the zero denominator case. -/
theorem source_native_original_FULL_D20_global_abs_le_one434
    (Δ W y : ℝ) (hWy : W ≤ y) (n : ℕ) :
    |sourceD20FullDelta Δ W y n| ≤ 1 := by
  have hProxy := sourceD20_proxy_bounds
    (sourceD20LogCell Δ (sourceD20CellIndex Δ n)) hWy n
  have hTest : 0 ≤ sourceD19RoughTest y n ∧
      sourceD19RoughTest y n ≤ 1 := by
    unfold sourceD19RoughTest
    split_ifs <;> norm_num
  unfold sourceD20FullDelta sourceD20FullProxy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The original full-cell D20 Delta has TRUE W-rough support
for every positive integer, not only the selected y-rough primes
or an artificially reweighted short complementary-divisor fibre.

The W-rough predicate is the unchanged SOURCE03
SourceRoughAbove test on all prime divisors with multiplicity. -/
theorem source_native_original_FULL_D20_rough_support434
    (Δ W y : ℝ) (hWy : W ≤ y) (n : ℕ)
    (hNonzero : sourceD20FullDelta Δ W y n ≠ 0) :
    SourceRoughAbove n W := by
  have hRough : sourceD20Rough W n := by
    by_contra hn
    have hDeltaZero : sourceD20FullDelta Δ W y n=0 := by
      unfold sourceD20FullDelta sourceD20FullProxy
      exact sourceD20_delta_support
        (sourceD20LogCell Δ (sourceD20CellIndex Δ n)) hWy n hn
    exact hNonzero hDeltaZero
  intro ℓ hPrime hDiv
  have hℓ2 : 2 ≤ ℓ := hPrime.two_le
  have hmin : n.minFac ≤ ℓ := Nat.minFac_le_of_dvd hℓ2 hDiv
  have hℓ : (n.minFac:ℝ) ≤ (ℓ:ℝ) := Nat.cast_le.mpr hmin
  exact hRough.2.trans_le hℓ

/-- A SOURCE03 original D20 alpha field, not an arbitrary
normalized surrogate. The coefficient of each ordinary integer
n is its literal full-logarithmic-cell rough-test minus proxy
Delta, including the prime-factor multiplicity condition. -/
noncomputable def sourceNativeOriginalFullD20Alpha434
    (Δ W y : ℝ) (n : ℕ) : ℂ :=
  (sourceD20FullDelta Δ W y n : ℝ)

theorem source_native_original_FULL_D20_alpha_source_fields434
    (Δ W y : ℝ) (hWy : W ≤ y)
    (L : ℝ) (hL : 1 ≤ L)
    (lo hi : ℕ) :
    (∀ n ∈ Finset.Icc lo hi,
      ‖sourceNativeOriginalFullD20Alpha434 Δ W y n‖ ≤ 1) ∧
    (∀ n,
      sourceAlphaDyadicCut
        (sourceNativeOriginalFullD20Alpha434 Δ W y)
        lo hi n ≠ 0 →
      SourceRoughAbove n W) := by
  constructor
  · intro n hn
    simpa only [sourceNativeOriginalFullD20Alpha434,
      Complex.norm_real,Real.norm_eq_abs] using
      source_native_original_FULL_D20_global_abs_le_one434
        Δ W y hWy n
  · intro n hn
    have hAlpha : sourceNativeOriginalFullD20Alpha434 Δ W y n ≠ 0 := by
      by_contra hn0
      apply hn
      by_cases hmem : n ∈ Finset.Icc lo hi
      · simpa only [sourceAlphaDyadicCut,if_pos hmem] using hn0
      · simp [sourceAlphaDyadicCut,hmem]
    apply source_native_original_FULL_D20_rough_support434
      Δ W y hWy n
    intro hdelta
    apply hAlpha
    simp [sourceNativeOriginalFullD20Alpha434, hdelta]

/-- Exactly the original alpha comparison field hAlpha/hRough
for the fixed r=6 config ea=0 and literal W=exp(sqrt L).
The D20 y threshold remains supplied with W≤y; no shortened
fibre recentering or prime-only replacement occurs. -/
theorem source_native_original_r6_D20_alpha_comparison_fields434
    (cfg : Green64Analytic.CorrelationSquare.SourceComparisonFixed434)
    (hea : cfg.ea = 0) (L Δ y : ℝ)
    (hL : 1 ≤ L) (hΔ : 0 < Δ)
    (hWy : Real.exp (Real.sqrt L) ≤ y)
    (lo hi : ℕ) :
    (∀ n ∈ Finset.Icc lo hi,
      ‖sourceNativeOriginalFullD20Alpha434
        Δ (Real.exp (Real.sqrt L)) y n‖ ≤ L^cfg.ea) ∧
    (∀ n,
      sourceAlphaDyadicCut
        (sourceNativeOriginalFullD20Alpha434
          Δ (Real.exp (Real.sqrt L)) y)
        lo hi n ≠ 0 →
      SourceRoughAbove n (Real.exp (Real.sqrt L))) := by
  obtain ⟨hBound,hRough⟩ :=
    source_native_original_FULL_D20_alpha_source_fields434
      Δ (Real.exp (Real.sqrt L)) y hWy L hL lo hi
  rw [hea]
  simpa only [pow_zero] using And.intro hBound hRough
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualOriginalQCoreNorm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Production consumer of the EXISTING literal Fock divisor bound,
original full-D20 normalization, and actual sorted-Q factorial collision
bound. All allocation bits, signed Fourier frequencies, K restriction,
prime powers, designated Q band, character and Mellin twists are retained.
There is no assumed bound on the core or its residual. -/
theorem b589_actual_full_D20_sorted_Q_core_norm434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (Δ W y : ℝ) (hWy : W ≤ y)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (u : ℕ) (hu : 0 < u) :
    ‖primeSlotCoreValue P
      (sourceNativePrimeCore r d L b slot δ ξ K
        (sourceNativeOriginalFullD20Alpha434 Δ W y) q χ σ₀ σ₁) u‖ ≤
      (u.divisors.card : ℝ)^2 := by
  let alpha := sourceNativeOriginalFullD20Alpha434 Δ W y
  let residual := sourceEndpointFibre
    (Finset.univ : Finset (OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)) orderedSkipProduct
    (fun a => sourceActualSortedFactorial r d *
      orderedSkipPhase (sourceActualSortedFrequencyScales r d L b slot) ξ a)
  have ha : ∀ m, ‖restrictSequence K alpha m‖ ≤ 1 := by
    intro m
    by_cases hm : m ∈ K
    · simpa only [restrictSequence, ite_eq_left hm, alpha,
        sourceNativeOriginalFullD20Alpha434, Complex.norm_real, Real.norm_eq_abs] using
        source_native_original_FULL_D20_global_abs_le_one434 Δ W y hWy m
    · simp only [restrictSequence, ite_eq_right hm, norm_zero, zero_le_one]
  have hc : ∀ v, ‖residual v‖ ≤ 1 := by
    intro v
    exact source_actual_sorted_QSkip_residual_norm_le_one434
      r d L hr hL b slot δ ξ v
  have hcore := sourceCore_divisor_bound
    (sourceOutsidePart (Finset.univ.biUnion P) u) q
    (sourceOriginalQActualBands r d L b) (restrictSequence K alpha) residual
    χ σ₀ σ₁ 1 1 zero_le_one zero_le_one ha hc
  have hEq := source_native_B524_original_sorted_QSkip_Fock_core_equals_T434
    P r d L b slot δ ξ K alpha q χ σ₀ σ₁ u
  dsimp only at hEq
  change ‖sourceCore (sourceOutsidePart (Finset.univ.biUnion P) u)
    (sourceOriginalQActualBands r d L b) (restrictSequence K alpha) residual
    q χ σ₀ σ₁‖ ≤ _ at hcore
  rw [show sourceCore (sourceOutsidePart (Finset.univ.biUnion P) u)
      (sourceOriginalQActualBands r d L b) (restrictSequence K alpha) residual
      q χ σ₀ σ₁ = primeSlotCoreValue P
        (sourceNativePrimeCore r d L b slot δ ξ K alpha q χ σ₀ σ₁) u from hEq] at hcore
  have hd : sourceOutsidePart (Finset.univ.biUnion P) u ∣ u := by
    rw [source_native_B521_fock_outside_eq_T_original_ordinary434]
    exact source_ordinary_part_dvd _ u hu.ne'
  have hcard : ((sourceOutsidePart (Finset.univ.biUnion P) u).divisors.card : ℝ) ≤
      (u.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hu.ne' hd)
  calc
    _ ≤ ((sourceOutsidePart (Finset.univ.biUnion P) u).divisors.card : ℝ)^2 := by
      simpa only [one_mul, alpha] using hcore
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
end Green64Analytic.ShiftTwoTerminal

end

end

