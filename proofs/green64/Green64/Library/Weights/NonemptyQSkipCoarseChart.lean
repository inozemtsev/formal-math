module

public import Green64.Library.Weights.D61EmptyQSkipChartZero
public import Green64.Library.Weights.Part096

@[expose] public section

/-!
# Weights / NonemptyQSkipCoarseChart

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalNonemptyQSkipCoarseChart -/

section

open scoped BigOperators Classical
open Filter
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

/-- The genuine sorted source has r(d+1)-1 ordered labels. In every
numerical Q band, at most r of those labelled coordinates can be skipped.
The designated deletion and repeated numerical prime choices are retained. -/
theorem source_native_B565_actual_Q_label_capacity434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool) :
    (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length = r*(d+1)-1 ∧
    ∀ g : Fin (d+1), Fintype.card
      {i : {i : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
        ¬ δ i = true} //
        (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot i.val).val.1 = g} ≤ r := by
  constructor
  · unfold sourceOrderedLabels
    rw [(List.mergeSort_perm _ _).length_eq]
    simp [Nat.mul_comm]
  · let n := (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
    let band : Fin n → Fin (d+1) := fun z =>
      (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot z).val.1
    let position : Fin n → Fin r := fun z =>
      (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot z).val.2
    have hlabel : Function.Injective (fun z : Fin n => (band z,position z)) := by
      intro z w hzw
      apply (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot).injective
      exact Subtype.ext hzw
    exact Green64Analytic.QSkipFactorial.groupedSkip_slot_card_le n (d+1) r δ band position hlabel

/-- The original active D61 tag bound for ANY actual Q allocation.
The full residual product appears multiplicatively, with the original
D36 upper mask, designated Q band and full capped P-part unchanged. -/
theorem source_native_B565_actual_tag_residual_upper434
    (r d jK : ℕ) (a eta b0 L sigmaT : ℝ)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (hL : 0 ≤ L) (ha : b0 ≤ a) (hsigma : sigmaT ≤ b0/16)
    (hband : (6/5:ℝ)*sourceOriginalQActualExponent r b.val ≤ b0/16)
    (u : SourceQPPhysicalTag (sourceActualSortedQ r d L b slot) δ)
    (hu : u ∈ sourceQPPhysicalTagSet (sourceActualSortedQ r d L b slot) δ
      (sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
      (sourceOriginalQActualBands r d L b)
      (sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊)) :
    ((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ) ≤
      Real.exp ((1-a+3*b0/8)*L)*(orderedSkipProduct u.1.2.2:ℝ) := by
  classical
  let Q := sourceActualSortedQ r d L b slot
  let emptySkip : OrderedQSkip
      (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length Q
      (fun _ => true) := fun i => False.elim (i.property rfl)
  let u0 : SourceQPPhysicalTag Q (fun _ => true) :=
    ((u.1.1,(u.1.2.1,emptySkip)),u.2)
  obtain ⟨hleft,hv⟩ := Finset.mem_product.mp hu
  obtain ⟨hm,hrest⟩ := Finset.mem_product.mp hleft
  obtain ⟨hp,_⟩ := Finset.mem_product.mp hrest
  have hu0 : u0 ∈ sourceQPPhysicalTagSet Q (fun _ => true)
      (sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
      (sourceOriginalQActualBands r d L b)
      (sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊) :=
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hm,
      Finset.mem_product.mpr ⟨hp,Finset.mem_univ _⟩⟩,hv⟩
  have hzero := (source_native_B563_actual_empty_tag_upper434
    r d jK a eta b0 L sigmaT b slot hL ha hsigma hband u0 hu0).1
  have hFactor : ((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ) =
      ((sourceQPTagM u0*sourceQPTagH u0:ℕ):ℝ)*(orderedSkipProduct u.1.2.2:ℝ) := by
    simp only [sourceQPTagM,sourceQPTagH,u0,
      source_native_B563_literal_all_true_QSkip_product434,mul_one]
    push_cast
    ring
  rw [hFactor]
  exact mul_le_mul_of_nonneg_right hzero (Nat.cast_nonneg _)

private theorem B565_nonzero_profile_lower434 (t : ℝ)
    (ht : sourceOriginalB558LiteralDyadicProfile434 t ≠ 0) : 1/2 < t := by
  by_contra h
  have hle : t ≤ 1/2 := le_of_not_gt h
  apply ht
  unfold sourceOriginalB558LiteralDyadicProfile434
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2*t-1 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : t-1 ≤ 0),sub_self]

/-- A nonzero original physical chart forces the actual skipped-Q product
past its exact exponential lower threshold. All original active masks,
full P-part cap and the TRUE UV L^K0 2^j/8 chart formula are retained. -/
theorem source_native_B565_actual_nonzero_chart_residual_lower434
    (r d jK j : ℕ) (a eta b0 L sigmaT K0 U V : ℝ)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (hL : 1 ≤ L) (ha : b0 ≤ a) (hsigma : sigmaT ≤ b0/16)
    (hK0 : 0 ≤ K0) (hUV : Real.exp L/4 ≤ U*V)
    (hband : (6/5:ℝ)*sourceOriginalQActualExponent r b.val ≤ b0/16)
    (u : SourceQPPhysicalTag (sourceActualSortedQ r d L b slot) δ)
    (hu : u ∈ sourceQPPhysicalTagSet (sourceActualSortedQ r d L b slot) δ
      (sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
      (sourceOriginalQActualBands r d L b)
      (sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊))
    (hchart : sourceOriginalB558LiteralDyadicProfile434
      (((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ)/(((U*V)*L^K0/8)*(2:ℝ)^j)) ≠ 0) :
    (L^K0/64)*Real.exp ((a-3*b0/8)*L) < (orderedSkipProduct u.1.2.2:ℝ) := by
  have hLp : 0 < L := by linarith
  have hM : 1 ≤ L^K0 := Real.one_le_rpow hL hK0
  have hTwo : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hUVpos : 0 < U*V := (by positivity : (0:ℝ) < Real.exp L/4).trans_le hUV
  have hBase : 0 < (U*V)*L^K0/8 := by positivity
  have hZ : 0 < ((U*V)*L^K0/8)*(2:ℝ)^j := by positivity
  have hZlow : Real.exp L*L^K0/32 ≤ ((U*V)*L^K0/8)*(2:ℝ)^j := by
    calc
      _ ≤ (U*V)*L^K0/8 := by
        have hh := mul_le_mul_of_nonneg_right hUV (Real.rpow_nonneg hLp.le K0)
        linarith only [hh]
      _ ≤ _ := le_mul_of_one_le_right hBase.le hTwo
  have hPhysical : Real.exp L*L^K0/64 < ((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ) := by
    have hh := (lt_div_iff₀ hZ).mp (B565_nonzero_profile_lower434 _ hchart)
    linarith only [hZlow,hh]
  have hUpper := source_native_B565_actual_tag_residual_upper434
    r d jK a eta b0 L sigmaT b slot δ hLp.le ha hsigma hband u hu
  apply (mul_lt_mul_iff_right₀ (Real.exp_pos ((1-a+3*b0/8)*L))).mp
  calc
    Real.exp ((1-a+3*b0/8)*L)*((L^K0/64)*Real.exp ((a-3*b0/8)*L)) =
        Real.exp L*L^K0/64 := by
      have he : Real.exp ((1-a+3*b0/8)*L)*Real.exp ((a-3*b0/8)*L)=Real.exp L := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp ((1-a+3*b0/8)*L)*Real.exp ((a-3*b0/8)*L))*(L^K0/64) := by ring
        _ = _ := by rw [he]; ring
    _ < ((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ) := hPhysical
    _ ≤ _ := hUpper

private theorem B565_geometric_range434 (n : ℕ) :
    (∑ j ∈ Finset.range n, (1/2:ℝ)^j) = 2*(1-(1/2:ℝ)^n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

private theorem B565_geometric_tail434 (J N : ℕ) :
    (∑ j ∈ Finset.Ico J N, (1/2:ℝ)^j) ≤ 2*(1/2:ℝ)^J := by
  by_cases hJN : J ≤ N
  · rw [Finset.sum_Ico_eq_sub _ hJN,B565_geometric_range434,B565_geometric_range434]
    have hp : (0:ℝ) ≤ (1/2:ℝ)^N := by positivity
    linarith only [hp]
  · rw [Finset.Ico_eq_empty_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hJN))]
    simp only [Finset.sum_empty]
    positivity

/-- The true tail capacity of an arbitrary residual allocation. If all
skipped labels come from numerical bands j>=J, the full repeated QSkip
product is at most exp((12/11)L/2^J). No total skipped-label count or
assumed product budget replaces the original sorted geometry. -/
theorem source_native_B565_actual_QSkip_tail_capacity434
    (r d J : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 ≤ L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (a : OrderedQSkip (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
      (sourceActualSortedQ r d L b slot) δ)
    (htail : ∀ i : {i : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
      ¬ δ i = true},
      J ≤ (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot i.val).val.1.val) :
    (orderedSkipProduct a:ℝ) ≤ Real.exp ((12/11:ℝ)*L/(2:ℝ)^J) := by
  classical
  let n := (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
  let I := {i : Fin n // ¬ δ i = true}
  let label : I → Fin (d+1) × Fin r := fun i =>
    (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot i.val).val
  let C : ℝ := (6/5:ℝ)*sourceOriginalQ0Scale r*L
  let F : Fin (d+1) × Fin r → ℝ := fun z => if J ≤ z.1.val then C*(1/2:ℝ)^z.1.val else 0
  have hrPos : (0:ℝ) < r := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr)
  have hC : 0 ≤ C := by dsimp [C,sourceOriginalQ0Scale]; positivity
  have hlabel : Function.Injective label := by
    intro i k hik
    apply Subtype.ext
    apply (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot).injective
    exact Subtype.ext hik
  have hPrimeUpper (i : I) : ((a i).val:ℝ) ≤ Real.exp (C*(1/2:ℝ)^(label i).1.val) := by
    have hp : (a i).val ∈ sourceOriginalQActualBands r d L (label i).1 := (a i).property
    have hpI := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    have hpR : ((a i).val:ℝ) ≤ Real.exp
        (((6/5:ℝ)*sourceOriginalQActualExponent r (label i).1.val)*L) :=
      (Nat.le_floor_iff (Real.exp_nonneg _)).mp hpI
    convert hpR using 1
    congr 1
    dsimp only [C,sourceOriginalQActualExponent]
    rw [div_pow]
    simp only [one_pow]
    ring
  have hImage : (∑ i : I,C*(1/2:ℝ)^(label i).1.val) =
      ∑ z ∈ (Finset.univ : Finset I).image label,F z := by
    rw [Finset.sum_image (fun i _ k _ hik => hlabel hik)]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [F]
    rw [ite_eq_left (htail i)]
  have hEnlarge : (∑ i : I,C*(1/2:ℝ)^(label i).1.val) ≤
      ∑ z : Fin (d+1) × Fin r,F z := by
    rw [hImage]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro z _ _
    dsimp only [F]
    split_ifs <;> positivity
  have hFull : (∑ z : Fin (d+1) × Fin r,F z) =
      (r:ℝ)*C*(∑ j : Fin (d+1),if J ≤ j.val then (1/2:ℝ)^j.val else 0) := by
    rw [Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [F]
    split_ifs <;> simp [mul_assoc]
  have hTail : (∑ j : Fin (d+1),if J ≤ j.val then (1/2:ℝ)^j.val else 0) ≤
      2*(1/2:ℝ)^J := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if J ≤ j then (1/2:ℝ)^j else 0)]
    rw [← Finset.sum_filter]
    have hset : (Finset.range (d+1)).filter (fun j => J ≤ j) = Finset.Ico J (d+1) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico,and_comm]
    rw [hset]
    exact B565_geometric_tail434 J (d+1)
  have hSum : (∑ i : I,C*(1/2:ℝ)^(label i).1.val) ≤ (12/11:ℝ)*L/(2:ℝ)^J := by
    calc
      _ ≤ ∑ z : Fin (d+1) × Fin r,F z := hEnlarge
      _ = _ := hFull
      _ ≤ (r:ℝ)*C*(2*(1/2:ℝ)^J) := mul_le_mul_of_nonneg_left hTail (mul_nonneg (Nat.cast_nonneg _) hC)
      _ = _ := by
        dsimp only [C,sourceOriginalQ0Scale]
        rw [div_pow]
        simp only [one_pow]
        field_simp
        ring
  calc
    (orderedSkipProduct a:ℝ) = ∏ i : I,((a i).val:ℝ) := by simp only [orderedSkipProduct,Nat.cast_prod]; rfl
    _ ≤ ∏ i : I,Real.exp (C*(1/2:ℝ)^(label i).1.val) :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hPrimeUpper i)
    _ = Real.exp (∑ i : I,C*(1/2:ℝ)^(label i).1.val) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hSum

/-- A fixed finite numerical band cutoff exists for every unchanged
positive D35/D61 witness parameter b0. It is independent of L and of the
moving actual Q depth. -/
theorem source_native_B565_fixed_coarse_cutoff_exists434 (b0 : ℝ) (hb0 : 0 < b0) :
    ∃ J : ℕ, 1 ≤ J ∧ (12/11:ℝ)/(2:ℝ)^J < b0/2 := by
  have hg := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)
  have hp : ∀ᶠ J : ℕ in atTop, 24/(11*b0) < (2:ℝ)^J :=
    hg.eventually (eventually_gt_atTop (24/(11*b0)))
  obtain ⟨J,hJ,hJone⟩ := (hp.and (eventually_ge_atTop (1:ℕ))).exists
  refine ⟨J,hJone,(div_lt_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^J)).mpr ?_⟩
  have hh := (div_lt_iff₀ (by positivity : (0:ℝ) < 11*b0)).mp hJ
  nlinarith only [hh]

/-- Nonzero original active charts require a genuinely large residual
and a skipped label in a FIXED coarse numerical Q band. The selected
prime has the exact original lower band scale and divides the true
physical z. These conclusions hold at all Fourier frequencies because
only the literal chart support is used. -/
theorem eventually_source_native_B565_actual_chart_forces_coarse_skip434
    (b0 : ℝ) (hb0 : 0 < b0) (J : ℕ)
    (hJ : (12/11:ℝ)/(2:ℝ)^J < b0/2) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
    ∀ (r d jK j : ℕ) (a eta sigmaT K0 U V : ℝ)
      (hr : 1 ≤ r) (b : Fin (d+1)) (slot : Fin r)
      (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
      (ha : b0 ≤ a) (hsigma : sigmaT ≤ b0/16)
      (hK0 : 0 ≤ K0) (hUV : Real.exp L/4 ≤ U*V)
      (hband : (6/5:ℝ)*sourceOriginalQActualExponent r b.val ≤ b0/16)
      (u : SourceQPPhysicalTag (sourceActualSortedQ r d L b slot) δ),
      u ∈ sourceQPPhysicalTagSet (sourceActualSortedQ r d L b slot) δ
        (sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
        (sourceOriginalQActualBands r d L b)
        (sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊) →
      sourceOriginalB558LiteralDyadicProfile434
        (((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ)/(((U*V)*L^K0/8)*(2:ℝ)^j)) ≠ 0 →
      Real.exp ((b0/2)*L) < (orderedSkipProduct u.1.2.2:ℝ) ∧
      ∃ i : {i : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
          ¬ δ i = true},
        (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot i.val).val.1.val < J ∧
        (u.1.2.2 i).val.Prime ∧
        Real.exp (sourceOriginalQActualExponent r J*L) ≤ ((u.1.2.2 i).val:ℝ) ∧
        (u.1.2.2 i).val ∣ sourceQPTagM u*sourceQPTagH u := by
  filter_upwards [source_native_B563_chart_threshold_eventually434 (b0/5) (by positivity)]
    with L hScalar
  refine ⟨hScalar.1,?_⟩
  intro r d jK j a eta sigmaT K0 U V hr b slot δ ha hsigma hK0 hUV hband u hu hchart
  have hLpos : 0 < L := by linarith [hScalar.1]
  have hSmallExp : (64:ℝ) ≤ Real.exp ((b0/8)*L) := by
    have heq : (5*(b0/5)/8)*L=(b0/8)*L := by ring
    simpa only [heq] using hScalar.2
  have hExp : (64:ℝ)*Real.exp ((b0/2)*L) ≤ Real.exp ((5*b0/8)*L) := by
    have hh := mul_le_mul_of_nonneg_right hSmallExp (Real.exp_nonneg ((b0/2)*L))
    have heq : Real.exp ((b0/8)*L)*Real.exp ((b0/2)*L)=Real.exp ((5*b0/8)*L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [heq] at hh
  have hLarger : Real.exp ((5*b0/8)*L) ≤ Real.exp ((a-3*b0/8)*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [ha]) hLpos.le)
  have hM : 1 ≤ L^K0 := Real.one_le_rpow hScalar.1 hK0
  have hMin : Real.exp ((b0/2)*L) ≤ (L^K0/64)*Real.exp ((a-3*b0/8)*L) := by
    calc
      _ ≤ Real.exp ((5*b0/8)*L)/64 := by linarith only [hExp]
      _ ≤ Real.exp ((a-3*b0/8)*L)/64 := div_le_div_of_nonneg_right hLarger (by norm_num)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hM (Real.exp_nonneg ((a-3*b0/8)*L))
        nlinarith only [hh]
  have hResidual : Real.exp ((b0/2)*L) < (orderedSkipProduct u.1.2.2:ℝ) :=
    hMin.trans_lt (source_native_B565_actual_nonzero_chart_residual_lower434
      r d jK j a eta b0 L sigmaT K0 U V b slot δ hScalar.1 ha hsigma hK0 hUV hband u hu hchart)
  have hCoarse : ∃ i : {i : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
      ¬ δ i = true},
      (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot i.val).val.1.val < J := by
    by_contra hNo
    have htail : ∀ i : {i : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
        ¬ δ i = true},
        J ≤ (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot i.val).val.1.val := by
      intro i
      exact Nat.le_of_not_gt (fun hi => hNo ⟨i,hi⟩)
    have hCap := source_native_B565_actual_QSkip_tail_capacity434 r d J L hr hLpos.le b slot δ u.1.2.2 htail
    have hTailExp : Real.exp ((12/11:ℝ)*L/(2:ℝ)^J) < Real.exp ((b0/2)*L) := by
      apply Real.exp_lt_exp.mpr
      have hh := mul_lt_mul_of_pos_right hJ hLpos
      convert hh using 1; ring
    exact (not_lt_of_ge hCap) (hTailExp.trans hResidual)
  obtain ⟨i,hi⟩ := hCoarse
  let g := (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot i.val).val.1
  have hp : (u.1.2.2 i).val ∈ sourceOriginalQActualBands r d L g := (u.1.2.2 i).property
  have hpPrime : (u.1.2.2 i).val.Prime :=
    source_native_B537_actual_Q_band_prime434 r d L b slot i.val _ (u.1.2.2 i).property
  have hPow : (2:ℝ)^g.val ≤ (2:ℝ)^J := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hi)
  have hQ0 : 0 ≤ sourceOriginalQ0Scale r := by unfold sourceOriginalQ0Scale; positivity
  have hExponent : sourceOriginalQActualExponent r J ≤ sourceOriginalQActualExponent r g.val :=
    div_le_div_of_nonneg_left hQ0 (by positivity) hPow
  have hpLower : Real.exp (sourceOriginalQActualExponent r J*L) ≤ ((u.1.2.2 i).val:ℝ) := by
    calc
      _ ≤ Real.exp (sourceOriginalQActualExponent r g.val*L) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hExponent hLpos.le)
      _ = Real.exp (sourceOriginalPGroupScale r L g.val) := by
        rw [source_original_Q_actual_scale_eq_P_scale434 r g.val L hr]
      _ ≤ _ := (source_original_Q_actual_prime_range434 r d L hr g _ hp).1
  have hpSkip : (u.1.2.2 i).val ∣ orderedSkipProduct u.1.2.2 :=
    Finset.dvd_prod_of_mem (fun z => (u.1.2.2 z).val) (Finset.mem_univ i)
  have hSkipZ : orderedSkipProduct u.1.2.2 ∣ sourceQPTagM u*sourceQPTagH u := by
    refine ⟨u.1.1*u.1.2.1*u.2,?_⟩
    simp only [sourceQPTagM,sourceQPTagH]
    ring
  exact ⟨hResidual,i,hi,hpPrime,hpLower,hpSkip.trans hSkipZ⟩

/-- Entire original active P-gated channels and their pre-square signed
projector vanish when all skipped labels lie beyond the fixed coarse
cutoff. The original full Delta, active D36 mask, P-part cap, all genuine
frequency substitutions, modulus abs(k), and physical shift 2k remain.
This removes only these actual allocations and asserts no ungated RAW
or general nonempty-allocation RMS estimate. -/
theorem eventually_source_native_B565_actual_tail_frequency_channels_zero434
    (b0 : ℝ) (hb0 : 0 < b0) (J : ℕ)
    (hJ : (12/11:ℝ)/(2:ℝ)^J < b0/2) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (r d jK j : ℕ) (a eta sigmaT K0 U V : ℝ)
      (hr : 1 ≤ r) (b : Fin (d+1)) (slot : Fin r)
      (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
      (ha : b0 ≤ a) (hsigma : sigmaT ≤ b0/16)
      (hK0 : 0 ≤ K0) (hUV : Real.exp L/4 ≤ U*V)
      (hband : (6/5:ℝ)*sourceOriginalQActualExponent r b.val ≤ b0/16)
      (htail : ∀ i : {i : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length //
        ¬ δ i = true},
        J ≤ (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot i.val).val.1.val)
      (xi : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
      (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs) (rho : ℝ) (zeta : Fin 3 → ℝ),
      let alpha := sourceNativeB563OriginalD61Alpha434 a eta b0 L
      let K := sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK
      let Q := sourceActualSortedQ r d L b slot
      let R := sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊
      let S := (sourceQPPhysicalTagSet Q δ K (sourceOriginalQActualBands r d L b) R).image
        (fun u => sourceQPTagM u*sourceQPTagH u)
      let P := sourceOriginalPAllActualBands r L
      let F := sourceNativePrimeCore r d L b slot δ
        (fun i => -xi i) K alpha k.natAbs chi (2*Real.pi*rho-2*Real.pi*zeta 1) 0
      let G := sourceNativePrimeCore r d L b slot δ
        (fun i => -xi i) K alpha k.natAbs chi (2*Real.pi*zeta 0+2*Real.pi*rho) 0
      let Z := ((U*V)*L^K0/8)*(2:ℝ)^j
      let psi : ℕ → ℂ := fun z => (sourceOriginalB558LiteralDyadicProfile434 ((z:ℝ)/Z):ℂ)
      (∀ tw1 tw2, sourceNativeGatedChannel S P R F G k
        (2*Real.pi*rho+2*Real.pi*zeta 2) (-(2*Real.pi*rho)) psi tw1 tw2=0) ∧
      sourceNativeB522GatedPhysicalProjected434 S P R F G k
        (2*Real.pi*rho+2*Real.pi*zeta 2) (-(2*Real.pi*rho)) psi=0 := by
  filter_upwards [eventually_source_native_B565_actual_chart_forces_coarse_skip434 b0 hb0 J hJ]
    with L hForce
  intro r d jK j a eta sigmaT K0 U V hr b slot δ ha hsigma hK0 hUV hband htail xi k chi rho zeta
  dsimp only
  have hpsi : ∀ z ∈ (sourceQPPhysicalTagSet (sourceActualSortedQ r d L b slot) δ
      (sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
      (sourceOriginalQActualBands r d L b)
      (sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊)).image
        (fun u => sourceQPTagM u*sourceQPTagH u),
      sourceOriginalB558LiteralDyadicProfile434
        ((z:ℝ)/(((U*V)*L^K0/8)*(2:ℝ)^j))=0 := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    by_contra hchart
    obtain ⟨_,i,hi,_⟩ := hForce.2 r d jK j a eta sigmaT K0 U V hr b slot δ
      ha hsigma hK0 hUV hband u hu hchart
    exact Nat.not_lt_of_ge (htail i) hi
  constructor
  · intro tw1 tw2
    unfold sourceNativeGatedChannel
    apply Finset.sum_eq_zero
    intro z hz
    simp only [sourceNativeGatedGramKernel,hpsi z hz,Complex.ofReal_zero,zero_mul,ite_self]
  · unfold sourceNativeB522GatedPhysicalProjected434
    apply Finset.sum_eq_zero
    intro z hz
    simp only [sourceNativeGatedGramKernel,hpsi z hz,Complex.ofReal_zero,zero_mul,ite_self]
end Green64Analytic.ShiftTwoTerminal

end

end

