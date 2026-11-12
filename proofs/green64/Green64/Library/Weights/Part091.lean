module

public import Green64.Library.Weights.Part090
public import Green64.Library.Correlation.B26FrozenCleanPhysicalFourier
public import Green64.Library.Weights.Part056
public import Green64.Library.Weights.B26FullRowTranspose
public import Green64.Library.Correlation.Part042
public import Green64.Library.Weights.Part018
public import Green64.Library.Weights.B26GenuineCoherentDecomposition
public import Green64.Library.Weights.B26OriginalRawNoneSplit
public import Green64.Library.Weights.B26CleanSmallCoherentPairing
public import Green64.Library.Analysis.Estimates.Part013

@[expose] public section

/-!
# Weights / Part091

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredIdealEndpointPair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalUnfilteredIdealPermInverse434
    {G : Type} (M : ℕ) : BigGroupPerm (BG := G) M ≃ BigGroupPerm (BG := G) M where
  toFun sigma g := (sigma g).symm
  invFun sigma g := (sigma g).symm
  left_inv sigma := by funext g; simp
  right_inv sigma := by funext g; simp

theorem source_original_unfiltered_ideal_endpoint_inverse_mean434
    {G : Type} [Fintype G] [DecidableEq G] (BP : G → Type) (M : ℕ)
    (f : ((g : G) → Fin M → BP g) → ℂ) (x : (g : G) → Fin M → BP g) :
    (Fintype.card (BigGroupPerm (BG := G) M) : ℂ)⁻¹ *
      ∑ sigma : BigGroupPerm (BG := G) M,
        f ((sourceOriginalB26EndpointPermutationEquiv434 BP M sigma).symm x) =
      sourceOriginalUnfilteredIdealEndpointMean434 BP M f x := by
  unfold sourceOriginalUnfilteredIdealEndpointMean434
  congr 1
  apply Fintype.sum_equiv (sourceOriginalUnfilteredIdealPermInverse434 (G := G) M)
  intro sigma
  rfl

/-- Exact mean-of-pairings identity for an arbitrary JOINT kernel and the
original product source density. Neither the kernel nor the tests factor.
The two endpoint permutation ensembles are independent. -/
theorem source_original_unfiltered_ideal_ENDPOINT_PAIR_MEAN434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ)
    (K : SourceOriginalJointBigState434 BP M → SourceOriginalJointBigState434 BP M → ℂ)
    (F H : SourceOriginalJointBigState434 BP M → ℂ) :
    let n : ℂ := (Fintype.card (BigGroupPerm (BG := G) M) : ℂ)⁻¹
    (∑ sigma : BigGroupPerm (BG := G) M, ∑ tau : BigGroupPerm (BG := G) M,
      n*n * (∑ s, ∑ t, (sourceOriginalJointBigMass434 BP mu s : ℂ) *
        (K (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)) *
          star (F s) * H t))) =
    ∑ s, ∑ t, (sourceOriginalJointBigMass434 BP mu s : ℂ) *
      (K s t * star (sourceOriginalUnfilteredIdealEndpointMean434 BP M F s) *
        sourceOriginalUnfilteredIdealEndpointMean434 BP M H t) := by
  dsimp only
  let n : ℂ := (Fintype.card (BigGroupPerm (BG := G) M) : ℂ)⁻¹
  have hn : star n = n := by simp [n]
  have hre (sigma tau : BigGroupPerm (BG := G) M) :
      (∑ s, ∑ t, (sourceOriginalJointBigMass434 BP mu s : ℂ) *
        (K (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)) * star (F s) * H t)) =
      ∑ s, ∑ t, (sourceOriginalJointBigMass434 BP mu s : ℂ) *
        (K s t * star (F ((sourceOriginalB26EndpointPermutationEquiv434 BP M sigma).symm s)) *
          H ((sourceOriginalB26EndpointPermutationEquiv434 BP M tau).symm t)) := by
    apply Fintype.sum_equiv (sourceOriginalB26EndpointPermutationEquiv434 BP M sigma)
    intro s
    apply Fintype.sum_equiv (sourceOriginalB26EndpointPermutationEquiv434 BP M tau)
    intro t
    have hm : sourceOriginalJointBigMass434 BP mu
        (sourceOriginalB26EndpointPermutationEquiv434 BP M sigma s) =
        sourceOriginalJointBigMass434 BP mu s :=
      source_original_B26_endpoint_permutation_mass434 BP M mu s sigma
    simp only [hm, Equiv.symm_apply_apply]
    rfl
  simp_rw [hre]
  simp_rw [← source_original_unfiltered_ideal_endpoint_inverse_mean434 BP M]
  change (∑ sigma, ∑ tau, n*n * (∑ s, ∑ t, _)) = _
  simp only [star_mul, star_sum, Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext sigma
    rw [Finset.sum_comm]
    arg 2
    ext s
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  apply Finset.sum_congr rfl
  intro tau htau
  simp [n]
  ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealFreeRatio -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- Explicit uniform bound on the common-density residual. It uses all
M=J+ell slots as a valid upper bound for the free count; J is fixed before
L in the eventual theorem. The definition itself charges only free slots. -/
theorem source_original_unfiltered_ideal_FREE_RATIO_BOUNDS434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) (J ell m : ℕ) (pat : SourcePattern G J m)
    (r : (g : G) → BP g → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (hr1 : ∀ g p,1 ≤ r g p) (hrR : ∀ g p,r g p ≤ R)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    1 ≤ sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m pat r s t sigma tau ∧
    sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m pat r s t sigma tau ≤
      R^(2*((J+ell)*Fintype.card G)) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hp1 (g : G) (i : Fin (J+ell)) :
      1 ≤ (if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else r g (s g (sigma g i))*r g (t g (tau g i))) := by
    split_ifs
    · exact le_rfl
    · exact one_le_mul_of_one_le_of_one_le (hr1 g _) (hr1 g _)
  have hpR (g : G) (i : Fin (J+ell)) :
      (if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else r g (s g (sigma g i))*r g (t g (tau g i))) ≤ R^2 := by
    split_ifs
    · exact one_le_pow₀ hR
    · simpa only [pow_two] using mul_le_mul (hrR g _) (hrR g _)
        (zero_le_one.trans (hr1 g _)) hR0
  constructor
  · have hh : (∏ _g : G,∏ _i : Fin (J+ell),(1:ℝ)) ≤
        sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m pat r s t sigma tau := by
      apply Finset.prod_le_prod₀
      · intro g _; positivity
      · intro g _
        exact Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => hp1 g i)
    simpa only [Finset.prod_const_one] using hh
  · unfold sourceOriginalUnfilteredIdealFreeRatio434
    calc
      _ ≤ ∏ _g : G,∏ _i : Fin (J+ell),R^2 := by
        apply Finset.prod_le_prod₀
        · intro g _
          exact Finset.prod_nonneg (fun i _ => zero_le_one.trans (hp1 g i))
        · intro g _
          exact Finset.prod_le_prod₀ (fun i _ => zero_le_one.trans (hp1 g i))
            (fun i _ => hpR g i)
      _ = R^(2*((J+ell)*Fintype.card G)) := by
        simp only [Finset.prod_const,Fintype.card_fin,Finset.card_univ,← pow_mul]
        congr 1
        ring

/-- The correction to the common unfiltered signed family is small when
the original tilted atom ratios are close to one. This is a pointwise
estimate, not yet the full physical norm perturbation. -/
theorem source_original_unfiltered_ideal_FREE_RATIO_DEFECT434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) (J ell m : ℕ) (pat : SourcePattern G J m)
    (r : (g : G) → BP g → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (hr1 : ∀ g p,1 ≤ r g p) (hrR : ∀ g p,r g p ≤ R)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    ‖((sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m pat r s t sigma tau:ℝ):ℂ)-1‖ ≤
      R^(2*((J+ell)*Fintype.card G))-1 := by
  obtain ⟨hlo,hhi⟩ := source_original_unfiltered_ideal_FREE_RATIO_BOUNDS434
    BP J ell m pat r R hR hr1 hrR s t sigma tau
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hlo)]
  exact sub_le_sub_right hhi 1

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealFrozenDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern G J m)
local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Frame" => SourceOriginalB26FrozenFrame434 BP J ell m patterns

/-- The actual frozen weight, including auxiliary ban, arbitrary full K,
phase, auxiliary mass and both permutation masses, has the common density
factorization. No part of the signed family is omitted. -/
theorem source_original_unfiltered_ideal_FROZEN_COMMON_WEIGHT434
    (mu r : (g : G) → BP g → ℝ) (V : G → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (s : Active) (h : Frame) (t : Active) :
    ((∏ g,∏ i,mu g (s g i)*(r g (s g i))^2:ℝ):ℂ) *
      sourceOriginalB26FrozenBigWeight434 BP bm J ell m patterns
        (fun g p => mu g p*(r g p)^2) V K dsmall zeta theta o k s h t =
    ((∏ g,∏ i,mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenBigWeight434 BP bm J ell m patterns
        mu V K dsmall zeta theta o k s h t *
      (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ) *
      (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r t:ℂ) *
      (sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m (patterns h.1)
        r s t h.2.2.1 h.2.2.2:ℂ) := by
  unfold sourceOriginalB26FrozenBigWeight434
  dsimp only
  split_ifs
  · have he := source_original_unfiltered_ideal_COMMON_DENSITY434 BP J ell m
      (patterns h.1) mu r s t h.2.2.1 h.2.2.2
    linear_combination
      ((sourceAuxMass BP bm J m V (patterns h.1) h.2.1:ℂ)*
        (bigEndpointPairMass (BG := G) (J+ell):ℂ)*
        originalEdgeScalar
          (K h.1 h.2.1 (fun g i => s g (h.2.2.1 g i)) (fun g i => t g (h.2.2.2 g i)))
          zeta theta (sourceOriginalB26FrozenD434 BP bm J ell m dsmall
            (patterns h.1) h.2.1 s h.2.2.1) o k)*he
  · simp

/-- Exact signed correction after a SINGLE common change of density.
This definition uses the actual frozen frame and weight, with no absolute
value or family-count estimate built into it. -/
def sourceOriginalUnfilteredIdealFrozenTiltError434
    (mu r : (g : G) → BP g → ℝ) (V : G → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (F H : Active → ℂ) : ℂ :=
  ∑ s : Active,∑ h : Frame,∑ t : Active,
    ((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*
      star ((sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s)*
      sourceOriginalB26FrozenBigWeight434 BP bm J ell m patterns
        mu V K dsmall zeta theta o k s h t*
      ((sourceOriginalUnfilteredIdealFreeRatio434 BP J ell m (patterns h.1)
        r s t h.2.2.1 h.2.2.2:ℂ)-1)*
      ((sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r t:ℂ)*H t)

/-- Literal full frozen pairing = harmonic full-family pairing at common
tests + an explicit signed correction. Applying the primary estimate to
the first term therefore preserves all cancellation across patterns. -/
theorem source_original_unfiltered_ideal_FROZEN_COMMON_PAIR434
    (mu r : (g : G) → BP g → ℝ) (V : G → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (F H : Active → ℂ) :
    (∑ s : Active,((∏ g,∏ i,mu g (s g i)*(r g (s g i))^2:ℝ):ℂ)*star (F s)*
      sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns
        (fun g p => mu g p*(r g p)^2) V K dsmall zeta theta o k H s) =
    (∑ s : Active,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*
      star ((sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r s:ℂ)*F s)*
      sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V K
        dsmall zeta theta o k
          (fun t => (sourceOriginalUnfilteredIdealCommonDensity434 BP (J+ell) r t:ℂ)*H t) s) +
    sourceOriginalUnfilteredIdealFrozenTiltError434 BP bm J ell m patterns
      mu r V K dsmall zeta theta o k F H := by
  unfold sourceOriginalB26FrozenBigBlock434 sourceOriginalUnfilteredIdealFrozenTiltError434
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro t _
  have he := source_original_unfiltered_ideal_FROZEN_COMMON_WEIGHT434 BP bm J ell m
    patterns mu r V K dsmall zeta theta o k s h t
  have hstar (a : ℝ) : star (a:ℂ) = (a:ℂ) := Complex.conj_ofReal a
  simp only [star_mul,hstar]
  linear_combination (star (F s)*H t)*he

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealHybrid -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The literal hybrid assignment: target in A, source everywhere else.
The full head product is evaluated after this splice. -/
def sourceOriginalUnfilteredIdealHybrid434
    {G : Type} [DecidableEq G] (BP : G → Type)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (s t : (g : G) → Fin (J+ell) → BP g) :
    (g : G) → Fin (J+ell) → BP g :=
  fun g i => if ∃ j : Fin m, (g,j) ∈ ν.1 ∧ (j.castLE hmJ).castAdd ell = i
    then t g i else s g i

theorem source_original_unfiltered_ideal_hybrid_A434
    {G : Type} [DecidableEq G] (BP : G → Type)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (a : ν.1) :
    sourceOriginalUnfilteredIdealHybrid434 BP J ell m hmJ ν s t
      a.val.1 (a.val.2.castLE hmJ |>.castAdd ell) =
      t a.val.1 (a.val.2.castLE hmJ |>.castAdd ell) := by
  unfold sourceOriginalUnfilteredIdealHybrid434
  exact if_pos ⟨a.val.2, a.property, rfl⟩

theorem source_original_unfiltered_ideal_hybrid_B434
    {G : Type} [DecidableEq G] (BP : G → Type)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (hd : Disjoint ν.1 ν.2)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (b : ν.2) :
    sourceOriginalUnfilteredIdealHybrid434 BP J ell m hmJ ν s t
      b.val.1 (b.val.2.castLE hmJ |>.castAdd ell) =
      s b.val.1 (b.val.2.castLE hmJ |>.castAdd ell) := by
  unfold sourceOriginalUnfilteredIdealHybrid434
  apply if_neg
  rintro ⟨j, hj, he⟩
  have hjb : j = b.val.2 := Fin.ext (congrArg (fun z : Fin (J+ell) => z.val) he)
  subst j
  exact Finset.disjoint_left.mp hd hj b.property

theorem source_original_unfiltered_ideal_hybrid_shared434
    {G : Type} [DecidableEq G] (BP : G → Type)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (g : G) (i : Fin (J+ell))
    (hi : i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g) :
    sourceOriginalUnfilteredIdealHybrid434 BP J ell m hmJ ν s t g i = s g i := by
  unfold sourceOriginalUnfilteredIdealHybrid434
  apply if_neg
  rintro ⟨j, hj, he⟩
  exact source_original_probe_freed_membership434 J ell m hmJ ν g j
    (Or.inl hj) (he.symm ▸ hi)

/-- The free-index machinery reads the original designated slot exactly. -/
theorem source_original_unfiltered_ideal_free_value434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g})
    (g : G) (j : Fin m) (hj : (g,j) ∈ ν.1 ∨ (g,j) ∈ ν.2) :
    sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν s g
      (sourceOriginalProbeFreeIndex434 J ell m hmJ ν g j hj) =
      (s g ((j.castLE hmJ).castAdd ell)).val := by
  simp [sourceOriginalProbeMemoryFreeValues434, sourceOriginalProbeFreeIndex434,
    sourceOriginalProbeMemoryFreeEquiv434]

/-- Partition the complete first-J product into retained and freed slots. -/
theorem source_original_unfiltered_ideal_head_product434
    {G R : Type} [Fintype G] [DecidableEq G] [CommMonoid R]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (w : G → Fin (J+ell) → R) :
    (∏ g : G, ∏ i : Fin J, w g (i.castAdd ell)) =
      (∏ g : G, ∏ i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g, w g i) *
      (∏ g : G, ∏ i : sourceOriginalProbeFreedSlots434 J m hmJ ν g,
        w g (i.val.castAdd ell)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  unfold sourceOriginalProbeSharedSlots434 sourceOriginalSharedSlots434
  rw [Finset.prod_image]
  · rw [Finset.prod_coe_sort (sourceOriginalProbeFreedSlots434 J m hmJ ν g)
      (fun i : Fin J => w g (i.castAdd ell))]
    exact (Finset.prod_sdiff (Finset.subset_univ _)).symm
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun z : Fin (J+ell) => z.val) he)

/-- Exact hybrid divisor identity for the ACTUAL canonical RAW term.
It keeps all group couplings, ordered multiplicities and both endpoint
permutations. No independence or cancellation hypothesis is used. -/
theorem source_original_unfiltered_ideal_raw_divisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hd : Disjoint ν.1 ν.2)
    (dsmall : ℕ)
    (s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma *
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
          (fun g i => t g (tau g i))) *
       sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
          (fun g i => s g (sigma g i)))) =
    dsmall * ∏ g : G, ∏ i : Fin J,
      (sourceOriginalUnfilteredIdealHybrid434 (fun g => {p : ℕ // p ∈ P g})
        J ell m hmJ ν (fun g i => s g (sigma g i))
          (fun g i => t g (tau g i)) g (i.castAdd ell)).val := by
  let ss := fun g i => s g (sigma g i)
  let tt := fun g i => t g (tau g i)
  let w := sourceOriginalUnfilteredIdealHybrid434
    (fun g => {p : ℕ // p ∈ P g}) J ell m hmJ ν ss tt
  have hshared :
      (∏ g : G, ∏ i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g,
        (w g i).val) =
      (∏ g : G, ∏ i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g,
        (ss g i).val) := by
    apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg Subtype.val
      (source_original_unfiltered_ideal_hybrid_shared434 _ J ell m hmJ ν ss tt g i hi)
  have hfree :
      (∏ g : G, ∏ i : sourceOriginalProbeFreedSlots434 J m hmJ ν g,
        (w g (i.val.castAdd ell)).val) =
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν tt) *
       sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν ss)) := by
    rw [source_original_probe_memory_aux_product_transfer434 J m hmJ ν hd
      (fun z => (w z.1 (z.2.val.castAdd ell)).val)]
    unfold sourceOriginalProbeFreeTargetX434 sourceOriginalProbeFreeSourceX434
    apply congrArg₂ (fun a b : ℕ => a*b)
    · apply Finset.prod_congr rfl
      intro a ha
      change (w a.val.1 ((a.val.2.castLE hmJ).castAdd ell)).val = _
      rw [source_original_unfiltered_ideal_free_value434]
      exact congrArg Subtype.val
        (source_original_unfiltered_ideal_hybrid_A434 _ J ell m hmJ ν ss tt a)
    · apply Finset.prod_congr rfl
      intro b hb
      change (w b.val.1 ((b.val.2.castLE hmJ).castAdd ell)).val = _
      rw [source_original_unfiltered_ideal_free_value434]
      exact congrArg Subtype.val
        (source_original_unfiltered_ideal_hybrid_B434 _ J ell m hmJ ν hd ss tt b)
  change _ = dsmall * ∏ g : G, ∏ i : Fin J, (w g (i.castAdd ell)).val
  rw [source_original_unfiltered_ideal_head_product434 J ell m hmJ ν
    (fun g i => (w g i).val), hshared, hfree]
  simp only [sourceOriginalB26CanonicalSharedDivisor434, ss, tt, mul_assoc]

/-- The complete joint phase in the actual RAW replacement is the full
head-product phase of the hybrid assignment; it is not separable. -/
theorem source_original_unfiltered_ideal_raw_value434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hd : Disjoint ν.1 ν.2)
    (dsmall : ℕ)
    (s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ζ theta : ℝ) (o k : ℤ) :
    sourceOriginalB26CanonicalRawValue434 P J ell m hmJ ν dsmall s t sigma tau ζ theta o k =
      originalEdgeScalar (-((-1:ℂ)^(ν.1.card+ν.2.card))) ζ theta
        (dsmall * ∏ g : G, ∏ i : Fin J,
          (sourceOriginalUnfilteredIdealHybrid434 (fun g => {p : ℕ // p ∈ P g})
            J ell m hmJ ν (fun g i => s g (sigma g i))
              (fun g i => t g (tau g i)) g (i.castAdd ell)).val) o k := by
  unfold sourceOriginalB26CanonicalRawValue434
  rw [source_original_unfiltered_ideal_raw_divisor434 P J ell m hmJ ν hd]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealOrientation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
variable (J ell m : ℕ) (hmJ : m ≤ J) (blockA blockB : Finset G)
variable (V : G → ℝ) (Q : ℕ) (h xi : ℝ)
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "patsA" => sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
local notation "patsB" => sourceOriginalMemoryRawComparisonPattern434 blockB blockA J m hmJ
local notation "KA" => sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q
  (fun _ => h) (fun _ => h) xi
local notation "KB" => sourceOriginalMemoryRawComparisonK434 P V blockB blockA J ell m hmJ Q
  (fun _ => h) (fun _ => h) xi

/-- Exact full K transpose for the unrestricted frozen weight; no history
or within-fresh-batch restriction is silently removed. -/
theorem source_original_unfiltered_ideal_FROZEN_WEIGHT_TRANSPOSE434
    (mu : (g : G) → BP g → ℝ) (dsmall : ℕ)
    (zeta theta : ℝ) (o k : ℤ)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (r : SourceOriginalB26FrozenFrame434 BP J ell m patsA) :
    sourceOriginalB26FrozenBigWeight434 BP (fun _ => Subtype.val) J ell m patsB
      mu V KB dsmall zeta theta o k s
      (sourceOriginalB26FullFrameSwapEquiv434 P J ell m hmJ blockA blockB r) t =
    sourceOriginalB26FrozenBigWeight434 BP (fun _ => Subtype.val) J ell m patsA
      mu V (fun v aux u w => KA v aux w u) dsmall zeta theta o k s r t := by
  rcases r with ⟨v,aux,sigma,tau⟩
  cases v with
  | none => rfl
  | some v =>
    change SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ v.val) at aux
    have he : sourceOriginalB26FullFrameSwapEquiv434 P J ell m hmJ blockA blockB
        ⟨some v,aux,sigma,tau⟩ =
      ⟨some (sourceOriginalProbeSwapFamilyEquiv434 blockA blockB m v),
        sourceOriginalProbeSwapAux434 P J m hmJ v.val aux,sigma,tau⟩ := rfl
    rw [he]
    unfold sourceOriginalB26FrozenBigWeight434
    dsimp only [sourceOriginalMemoryRawComparisonPattern434,
      sourceOriginalMemoryRawComparisonK434, sourceOriginalProbeSwapFamilyEquiv434]
    simp only [Equiv.coe_fn_mk]
    simp only [source_original_B26_full_K_swap_divisor434,
      source_original_B26_full_K_swap_aux_mass434, source_original_B26_full_K_swap_aux_ban434,
      source_original_B26_full_K_transpose434, source_original_B26_full_K_swap_pattern434]

theorem source_original_unfiltered_ideal_FROZEN_BLOCK_TRANSPOSE434
    (mu : (g : G) → BP g → ℝ) (dsmall : ℕ)
    (zeta theta : ℝ) (o k : ℤ)
    (H : ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (s : (g : G) → Fin (J+ell) → BP g) :
    sourceOriginalB26FrozenBigBlock434 BP (fun _ => Subtype.val) J ell m patsB
      mu V KB dsmall zeta theta o k H s =
    sourceOriginalB26FrozenBigBlock434 BP (fun _ => Subtype.val) J ell m patsA
      mu V (fun v aux u w => KA v aux w u) dsmall zeta theta o k H s := by
  unfold sourceOriginalB26FrozenBigBlock434
  let e := sourceOriginalB26FullFrameSwapEquiv434 P J ell m hmJ blockA blockB
  have he := e.sum_comp (fun r => ∑ t, sourceOriginalB26FrozenBigWeight434
    BP (fun _ => Subtype.val) J ell m patsB mu V KB dsmall zeta theta o k s r t * H t)
  rw [← he]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro t ht
  rw [source_original_unfiltered_ideal_FROZEN_WEIGHT_TRANSPOSE434]

/-- Original memoryOrientationK on the full frozen family, including
RAW-none, all auxiliary arguments, full endpoint swap and scalar conjugation. -/
theorem source_original_unfiltered_ideal_FROZEN_MEMORY_ORIENTATION434
    (mu : (g : G) → BP g → ℝ) (dsmall : ℕ)
    (zeta theta : ℝ) (o k : ℤ)
    (H : ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (s : (g : G) → Fin (J+ell) → BP g) :
    sourceOriginalB26FrozenBigBlock434 BP (fun _ => Subtype.val) J ell m patsA
      mu V (memoryOrientationK BP J ell m patsA KA o) dsmall zeta theta o k H s =
    if o=1 then
      sourceOriginalB26FrozenBigBlock434 BP (fun _ => Subtype.val) J ell m patsA
        mu V KA dsmall zeta theta o k H s
    else
      sourceOriginalB26FrozenBigBlock434 BP (fun _ => Subtype.val) J ell m patsB
        mu V KB dsmall zeta theta o k H s := by
  by_cases ho : o=1
  · simp only [memoryOrientationK, if_pos ho]
  · simp only [memoryOrientationK, if_neg ho]
    exact (source_original_unfiltered_ideal_FROZEN_BLOCK_TRANSPOSE434
      P J ell m hmJ blockA blockB V Q h xi mu dsmall zeta theta o k H s).symm

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealResample -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Literal coordinate-resampling transition, on a finite dependent product.
The entries outside S are copied; entries in S use their original laws. -/
def sourceOriginalUnfilteredIdealResampleKernel434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (S : Finset I)
    (x y : (i : I) → B i) : ℂ :=
  ∏ i, if i ∈ S then mu i (y i) else if y i = x i then 1 else 0

def sourceOriginalUnfilteredIdealResample434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (S : Finset I)
    (f : ((i : I) → B i) → ℂ) (x : (i : I) → B i) : ℂ :=
  ∑ y, sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y * f y

/-- Exact normalization, allowing zero atoms and empty alphabets whenever
the stated normalization can hold. -/
theorem source_original_unfiltered_ideal_resample_mass434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (S : Finset I) (x : (i : I) → B i) :
    (∑ y, sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y) = 1 := by
  unfold sourceOriginalUnfilteredIdealResampleKernel434
  rw [← Fintype.prod_sum (fun i (b : B i) =>
    if i ∈ S then mu i b else if b = x i then (1:ℂ) else 0)]
  apply Finset.prod_eq_one
  intro i hi
  by_cases hs : i ∈ S
  · simpa only [if_pos hs] using hnorm i
  · simp [hs]

/-- Composing actual resampling kernels integrates all unused coordinates.
The laws need not be uniform or strictly positive. -/
theorem source_original_unfiltered_ideal_resample_comp434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (S T : Finset I) (x z : (i : I) → B i) :
    (∑ y, sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y *
      sourceOriginalUnfilteredIdealResampleKernel434 B mu T y z) =
      sourceOriginalUnfilteredIdealResampleKernel434 B mu (S ∪ T) x z := by
  unfold sourceOriginalUnfilteredIdealResampleKernel434
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : B i) =>
    (if i ∈ S then mu i b else if b = x i then (1:ℂ) else 0) *
    (if i ∈ T then mu i (z i) else if z i = b then 1 else 0))]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T
  · simp only [hs, ht, if_true, Finset.mem_union, true_or]
    rw [← Finset.sum_mul, hnorm i, one_mul]
  · simp only [hs, ht, if_true, if_false, Finset.mem_union, true_or]
    simp [mul_ite, eq_comm]
  · simp only [hs, ht, if_true, if_false, Finset.mem_union, or_true]
    simp [ite_mul]
  · simp only [hs, ht, if_true, if_false, Finset.mem_union, or_self]
    simp [ite_mul]

/-- A surviving copy factor forces literal equality of that coordinate. -/
theorem source_original_unfiltered_ideal_resample_copy434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (S : Finset I)
    (x y : (i : I) → B i)
    (h : sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y ≠ 0)
    (i : I) (hi : i ∉ S) : y i = x i := by
  by_contra he
  apply h
  unfold sourceOriginalUnfilteredIdealResampleKernel434
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, he]

/-- The asymmetric intermediate assignment, before integrating unused entries. -/
def sourceOriginalUnfilteredIdealSplice434
    {I : Type} [DecidableEq I] (B : I → Type) (S : Finset I)
    (x z : (i : I) → B i) : (i : I) → B i :=
  fun i => if i ∈ S then z i else x i

/-- Exact asymmetric unused-coordinate integration with a fully joint phase.
The phase only ignores coordinates resampled at BOTH steps. It is never
commuted through a mean. This finite lemma will be instantiated with tails. -/
theorem source_original_unfiltered_ideal_joint_phase_comp434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (S T : Finset I) (Phi : ((i : I) → B i) → ℂ)
    (hPhi : ∀ u v, (∀ i, i ∉ S ∩ T → u i = v i) → Phi u = Phi v)
    (x z : (i : I) → B i) :
    (∑ y, sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y *
      Phi y * sourceOriginalUnfilteredIdealResampleKernel434 B mu T y z) =
      sourceOriginalUnfilteredIdealResampleKernel434 B mu (S ∪ T) x z *
        Phi (sourceOriginalUnfilteredIdealSplice434 B S x z) := by
  have hp (y : (i : I) → B i) :
      sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y * Phi y *
        sourceOriginalUnfilteredIdealResampleKernel434 B mu T y z =
      (sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y *
        sourceOriginalUnfilteredIdealResampleKernel434 B mu T y z) *
        Phi (sourceOriginalUnfilteredIdealSplice434 B S x z) := by
    by_cases hs : sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y = 0
    · simp [hs]
    by_cases ht : sourceOriginalUnfilteredIdealResampleKernel434 B mu T y z = 0
    · simp [ht]
    have he : Phi y = Phi (sourceOriginalUnfilteredIdealSplice434 B S x z) := by
      apply hPhi
      intro i hi
      by_cases his : i ∈ S
      · have hit : i ∉ T := fun hit => hi (Finset.mem_inter.mpr ⟨his, hit⟩)
        simpa only [sourceOriginalUnfilteredIdealSplice434, if_pos his] using
          (source_original_unfiltered_ideal_resample_copy434 B mu T y z ht i hit).symm
      · simpa only [sourceOriginalUnfilteredIdealSplice434, if_neg his] using
          source_original_unfiltered_ideal_resample_copy434 B mu S x y hs i his
    rw [he]
    ring
  simp_rw [hp]
  rw [← Finset.sum_mul, source_original_unfiltered_ideal_resample_comp434 B mu hnorm]

/-- The corresponding exact operator identity, with the phase in its original
position BETWEEN the two actual resampling operations. -/
theorem source_original_unfiltered_ideal_joint_phase_operator434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (S T : Finset I) (Phi : ((i : I) → B i) → ℂ)
    (hPhi : ∀ u v, (∀ i, i ∉ S ∩ T → u i = v i) → Phi u = Phi v)
    (f : ((i : I) → B i) → ℂ) (x : (i : I) → B i) :
    sourceOriginalUnfilteredIdealResample434 B mu S
      (fun y => Phi y * sourceOriginalUnfilteredIdealResample434 B mu T f y) x =
    ∑ z, sourceOriginalUnfilteredIdealResampleKernel434 B mu (S ∪ T) x z *
      Phi (sourceOriginalUnfilteredIdealSplice434 B S x z) * f z := by
  unfold sourceOriginalUnfilteredIdealResample434
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    _ = (∑ y, sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y *
        Phi y * sourceOriginalUnfilteredIdealResampleKernel434 B mu T y z) * f z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := by rw [source_original_unfiltered_ideal_joint_phase_comp434 B mu hnorm S T Phi hPhi]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealMasks -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A selected original probe at its actual first-J slot. -/
def sourceOriginalUnfilteredIdealAt434
    {G : Type} [DecidableEq G] (J ell m : ℕ) (hmJ : m ≤ J)
    (A : Finset (G × Fin m)) (g : G) (i : Fin (J+ell)) : Prop :=
  ∃ j : Fin m, (g,j) ∈ A ∧ (j.castLE hmJ).castAdd ell = i

/-- The resampling mask consists of selected probes and all trailing slots. -/
def sourceOriginalUnfilteredIdealMask434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (A : Finset (G × Fin m)) :
    Finset (Σ _g : G, Fin (J+ell)) :=
  Finset.univ.filter (fun z => J ≤ z.2.val ∨
    sourceOriginalUnfilteredIdealAt434 J ell m hmJ A z.1 z.2)

/-- The literal retained set is precisely the head minus both selected blocks. -/
theorem source_original_unfiltered_ideal_shared_iff434
    {G : Type} [DecidableEq G] (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) (i : Fin (J+ell)) :
    i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g ↔
      i.val < J ∧ ¬ sourceOriginalUnfilteredIdealAt434 J ell m hmJ ν.1 g i ∧
        ¬ sourceOriginalUnfilteredIdealAt434 J ell m hmJ ν.2 g i := by
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have hjf : j ∉ sourceOriginalProbeFreedSlots434 J m hmJ ν g :=
      (Finset.mem_sdiff.mp hj).2
    have hh : i.val < J := by
      rw [← hji]
      exact j.isLt
    refine ⟨hh, ?_, ?_⟩
    · rintro ⟨r, hr, hri⟩
      exact source_original_probe_freed_membership434 J ell m hmJ ν g r
        (Or.inl hr) (hri.symm ▸ hi)
    · rintro ⟨r, hr, hri⟩
      exact source_original_probe_freed_membership434 J ell m hmJ ν g r
        (Or.inr hr) (hri.symm ▸ hi)
  · rintro ⟨hh, ha, hb⟩
    let j : Fin J := ⟨i.val, hh⟩
    have hji : j.castAdd ell = i := Fin.ext rfl
    rw [← hji, sourceOriginalProbeSharedSlots434, source_original_shared_slot_mem434]
    intro hf
    obtain ⟨r, hr, hrj⟩ := Finset.mem_image.mp hf
    have hr' := (Finset.mem_filter.mp hr).2
    have hri : (r.castLE hmJ).castAdd ell = i :=
      (congrArg (fun a : Fin J => a.castAdd ell) hrj).trans hji
    rcases hr' with h | h
    · exact ha ⟨r, h, hri⟩
    · exact hb ⟨r, h, hri⟩

/-- The two actual resampling masks overlap only in the trailing slots. -/
theorem source_original_unfiltered_ideal_head_not_inter434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (hd : Disjoint ν.1 ν.2) (g : G) (i : Fin J) :
    (⟨g,i.castAdd ell⟩ : Σ _g : G, Fin (J+ell)) ∉
      sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.1 ∩
      sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.2 := by
  intro hi
  have hh : ¬ J ≤ (i.castAdd ell).val := by simpa using Nat.not_le.mpr i.isLt
  have ha := (Finset.mem_inter.mp hi).1
  have hb := (Finset.mem_inter.mp hi).2
  simp only [sourceOriginalUnfilteredIdealMask434, Finset.mem_filter,
    Finset.mem_univ, true_and, hh, false_or] at ha hb
  obtain ⟨a, ha, hai⟩ := ha
  obtain ⟨b, hb, hbi⟩ := hb
  have hab : a = b := Fin.ext
    (congrArg (fun z : Fin (J+ell) => z.val) (hai.trans hbi.symm))
  subst b
  exact Finset.disjoint_left.mp hd ha hb

/-- The union mask is exactly the complement of original shared-copy slots. -/
theorem source_original_unfiltered_ideal_union_mask434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (g : G) (i : Fin (J+ell)) :
    (⟨g,i⟩ : Σ _g : G, Fin (J+ell)) ∈
      sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.1 ∪
      sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.2 ↔
      i ∉ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g := by
  rw [source_original_unfiltered_ideal_shared_iff434]
  simp only [sourceOriginalUnfilteredIdealMask434, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [not_and_or, not_not, not_lt]
  tauto

/-- The literal original fresh law is this exact dependent-coordinate kernel. -/
theorem source_original_unfiltered_ideal_fresh_kernel434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ)
    (s t : (g : G) → Fin (J+ell) → BP g) :
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) =
    sourceOriginalUnfilteredIdealResampleKernel434
      (fun z : Σ _g : G, Fin (J+ell) => BP z.1)
      (fun z p => (mu z.1 p : ℂ))
      (sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.1 ∪
        sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.2)
      (fun z => s z.1 z.2) (fun z => t z.1 z.2) := by
  unfold sourceOriginalB26FrozenFreshLaw434 sourceOriginalUnfilteredIdealResampleKernel434
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Equiv.refl_symm, Equiv.refl_apply,
    source_original_probe_memory_shared_slots434,
    source_original_unfiltered_ideal_union_mask434]
  by_cases hs : i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g <;>
    simp only [hs, not_true_eq_false, not_false_eq_true, if_true, if_false]
  by_cases he : t g i = s g i <;> simp_all

/-- Uncurrying the actual dependent BIG carrier loses no state or multiplicity. -/
def sourceOriginalUnfilteredIdealFlatEquiv434
    {G : Type} (BP : G → Type) (M : ℕ) :
    ((g : G) → Fin M → BP g) ≃
      ((z : Σ _g : G, Fin M) → BP z.1) where
  toFun s z := s z.1 z.2
  invFun s g i := s ⟨g,i⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealRawComposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Actual joint head-product phase, allowing its real RAW sign as coefficient. -/
def sourceOriginalUnfilteredIdealHeadPhase434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (J ell : ℕ)
    (K : ℂ) (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ)
    (x : (z : Σ _g : G, Fin (J+ell)) → {p : ℕ // p ∈ P z.1}) : ℂ :=
  originalEdgeScalar K ζ theta
    (dsmall * ∏ g : G, ∏ i : Fin J, (x ⟨g,i.castAdd ell⟩).val) o k

/-- The regularity required in the finite integration lemma is DERIVED for
the actual joint phase: only trailing entries can occur in both masks. -/
theorem source_original_unfiltered_ideal_head_phase_ignores_inter434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hd : Disjoint ν.1 ν.2)
    (K : ℂ) (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ)
    (x y : (z : Σ _g : G, Fin (J+ell)) → {p : ℕ // p ∈ P z.1})
    (hxy : ∀ z, z ∉ sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.1 ∩
      sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.2 → x z = y z) :
    sourceOriginalUnfilteredIdealHeadPhase434 P J ell K dsmall ζ theta o k x =
      sourceOriginalUnfilteredIdealHeadPhase434 P J ell K dsmall ζ theta o k y := by
  unfold sourceOriginalUnfilteredIdealHeadPhase434
  congr 2
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg Subtype.val (hxy ⟨g,i.castAdd ell⟩
    (source_original_unfiltered_ideal_head_not_inter434 J ell m hmJ ν hd g i))

/-- The actual RAW scalar on the physical carrier is precisely the head phase
at the asymmetric resampling splice. No property of Phi is postulated. -/
theorem source_original_unfiltered_ideal_raw_splice_phase434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hd : Disjoint ν.1 ν.2)
    (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ)
    (s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    sourceOriginalB26CanonicalRawValue434 P J ell m hmJ ν dsmall s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) ζ theta o k =
    sourceOriginalUnfilteredIdealHeadPhase434 P J ell
      (-((-1:ℂ)^(ν.1.card+ν.2.card))) dsmall ζ theta o k
      (sourceOriginalUnfilteredIdealSplice434
        (fun z : Σ _g : G, Fin (J+ell) => {p : ℕ // p ∈ P z.1})
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.1)
        (fun z => s z.1 z.2) (fun z => t z.1 z.2)) := by
  rw [source_original_unfiltered_ideal_raw_value434 P J ell m hmJ ν hd]
  unfold sourceOriginalUnfilteredIdealHeadPhase434
  congr 2
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  have hh : ¬ J ≤ (i.castAdd ell).val := Nat.not_le.mpr i.isLt
  have hmask : (⟨g,i.castAdd ell⟩ : Σ _g : G, Fin (J+ell)) ∈
      sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.1 ↔
      sourceOriginalUnfilteredIdealAt434 J ell m hmJ ν.1 g (i.castAdd ell) := by
    exact (Finset.mem_filter.trans (by simp only [Finset.mem_univ, true_and,
      hh, false_or]))
  simp only [sourceOriginalUnfilteredIdealSplice434, hmask,
    sourceOriginalUnfilteredIdealAt434, sourceOriginalUnfilteredIdealHybrid434,
    Equiv.refl_apply]


/-- EXACT original per-pattern RAW operator adapter, with the true shared/fresh
law, asymmetric target-A/source-B phase, both tail means and all numerical
multiplicities. The coefficient sign remains INSIDE the actual edge scalar.
No family-saving hypothesis is present. -/
theorem source_original_unfiltered_ideal_LITERAL_RAW_COMPOSITION434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hd : Disjoint ν.1 ν.2)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hnorm : ∀ g, ∑ p, mu g p = 1)
    (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    let B := fun z : Σ _g : G, Fin (J+ell) => {p : ℕ // p ∈ P z.1}
    let e := sourceOriginalUnfilteredIdealFlatEquiv434
      (fun g => {p : ℕ // p ∈ P g}) (J+ell)
    let w := fun z (p : B z) => (mu z.1 p : ℂ)
    let SA := sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.1
    let SB := sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.2
    let Phi := sourceOriginalUnfilteredIdealHeadPhase434 P J ell
      (-((-1:ℂ)^(ν.1.card+ν.2.card))) dsmall ζ theta o k
    (∑ t, sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
      sourceOriginalB26CanonicalRawValue434 P J ell m hmJ ν dsmall s t
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) ζ theta o k * f t) =
    sourceOriginalUnfilteredIdealResample434 B w SA
      (fun x => Phi x *
        sourceOriginalUnfilteredIdealResample434 B w SB (fun y => f (e.symm y)) x)
      (e s) := by
  classical
  dsimp only
  let B := fun z : Σ _g : G, Fin (J+ell) => {p : ℕ // p ∈ P z.1}
  let e := sourceOriginalUnfilteredIdealFlatEquiv434
    (fun g => {p : ℕ // p ∈ P g}) (J+ell)
  let w := fun z (p : B z) => (mu z.1 p : ℂ)
  have hw : ∀ z, ∑ p, w z p = 1 := by
    intro z
    dsimp only [w, B]
    exact_mod_cast hnorm z.1
  rw [source_original_unfiltered_ideal_joint_phase_operator434 B w hw _ _ _
    (source_original_unfiltered_ideal_head_phase_ignores_inter434
      P J ell m hmJ ν hd _ dsmall ζ theta o k)]
  apply Fintype.sum_equiv e
  intro t
  rw [source_original_unfiltered_ideal_fresh_kernel434,
    source_original_unfiltered_ideal_raw_splice_phase434 P J ell m hmJ ν hd]
  rfl

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealFrozenDecomposition -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Genuine Option-none split at the literal frozen BIG level. -/
theorem source_original_unfiltered_ideal_frozen_none_split434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi : ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
    sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      mu V (sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q
        (fun _ => h) (fun _ => h) xi)
      dsmall ζ theta o k f s =
    sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
      (sourceOriginalB26RawNonePattern434 (G := G) J m)
      mu V (fun _ _ _ _ => 1) dsmall ζ theta o k f s +
    sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
      (fun n : ↥family => sourceOriginalProbeMemoryPattern434 J m hmJ n.val)
      mu V (fun n : ↥family => sourceOriginalProbeMemoryCanonicalK434 P V
        J ell m hmJ n.val Q h h xi) dsmall ζ theta o k f s := by
  classical
  dsimp only
  unfold sourceOriginalB26FrozenBigBlock434
  simp only [SourceOriginalB26FrozenFrame434, Fintype.sum_sigma,
    Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_unique]
  rfl

/-- Exact complete original harmonic frozen-family decomposition, retaining
the genuine RAW-none, every canonical signed comparison, and the actual
auxiliary-versus-both-endpoints ban. This is an equality, not a saving premise. -/
theorem source_original_unfiltered_ideal_FULL_FROZEN_DECOMPOSITION434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}), NeZero p.val]
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi ζ theta : ℝ)
    (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0) (dsmall : ℕ)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) :
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
    sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
      (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
      mu data.Vbig
      (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB J ell m hmJ Q
        (fun _ => h) (fun _ => h) xi) dsmall ζ theta o k f s =
    sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
      (sourceOriginalB26RawNonePattern434 (G := G) J m) mu data.Vbig
      (fun _ _ _ _ => 1) dsmall ζ theta o k f s +
    sourceOriginalB26CanonicalRawBlock434 data blockA blockB
      J ell m hmJ Q h xi ζ theta o k false false dsmall f s +
    sourceOriginalB26CanonicalComparisonBlock434 data blockA blockB
      J ell m hmJ Q h xi ζ theta o k false false dsmall f s -
    sourceOriginalB26CanonicalAuxBanBlock434 data blockA blockB
      J ell m hmJ Q h xi ζ theta o k false false dsmall f s := by
  dsimp only
  rw [source_original_unfiltered_ideal_frozen_none_split434]
  rw [source_original_B26_GENUINE_COHERENT_RAW_COMPARISON_BAN434
    data blockA blockB hBlocks J ell m hmJ Q h xi ζ theta o k ho hk]
  ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealResampleAlgebra -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_unfiltered_ideal_resample_union434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (S T : Finset I) (f : ((i : I) → B i) → ℂ) :
    sourceOriginalUnfilteredIdealResample434 B mu S
      (sourceOriginalUnfilteredIdealResample434 B mu T f) =
      sourceOriginalUnfilteredIdealResample434 B mu (S ∪ T) f := by
  funext x
  unfold sourceOriginalUnfilteredIdealResample434
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    _ = (∑ y, sourceOriginalUnfilteredIdealResampleKernel434 B mu S x y *
        sourceOriginalUnfilteredIdealResampleKernel434 B mu T y z) * f z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = _ := by rw [source_original_unfiltered_ideal_resample_comp434 B mu hnorm]

theorem source_original_unfiltered_ideal_resample_empty434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (f : ((i : I) → B i) → ℂ) :
    sourceOriginalUnfilteredIdealResample434 B mu ∅ f = f := by
  funext x
  have hk (y : (i : I) → B i) :
      sourceOriginalUnfilteredIdealResampleKernel434 B mu ∅ x y =
        if y = x then 1 else 0 := by
    by_cases he : y = x
    · subst y
      simp [sourceOriginalUnfilteredIdealResampleKernel434]
    · rw [if_neg he]
      by_contra hn
      apply he
      funext i
      exact source_original_unfiltered_ideal_resample_copy434 B mu ∅ x y hn i (by simp)
  simp only [sourceOriginalUnfilteredIdealResample434, hk, ite_mul, one_mul, zero_mul]
  simp

/-- The singleton matrix is exactly the original coordinate update average. -/
theorem source_original_unfiltered_ideal_resample_singleton434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (i : I)
    (f : ((i : I) → B i) → ℂ) (x : (i : I) → B i) :
    sourceOriginalUnfilteredIdealResample434 B mu {i} f x =
      ∑ b : B i, mu i b * f (Function.update x i b) := by
  classical
  let update : B i → ((j : I) → B j) := fun b => Function.update x i b
  have hinj : Function.Injective update := by
    intro a b hab
    simpa [update] using congrFun hab i
  have hkernel (b : B i) :
      sourceOriginalUnfilteredIdealResampleKernel434 B mu {i} x (update b) = mu i b := by
    unfold sourceOriginalUnfilteredIdealResampleKernel434
    rw [Finset.prod_eq_single i]
    · simp [update]
    · intro j hj hji
      simp [hji, update, Function.update_of_ne hji]
    · simp
  have hzero (y : (j : I) → B j)
      (hy : y ∉ Finset.univ.image update) :
      sourceOriginalUnfilteredIdealResampleKernel434 B mu {i} x y = 0 := by
    by_contra hn
    have he : update (y i) = y := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [update]
      · have hyj := source_original_unfiltered_ideal_resample_copy434 B mu {i} x y hn j
          (by simpa using hji)
        simp [update, Function.update_of_ne hji, hyj]
    exact hy (Finset.mem_image.mpr ⟨y i, Finset.mem_univ _, he⟩)
  unfold sourceOriginalUnfilteredIdealResample434
  calc
    _ = ∑ y ∈ Finset.univ.image update,
        sourceOriginalUnfilteredIdealResampleKernel434 B mu {i} x y * f y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y hy hn
      rw [hzero y hn, zero_mul]
    _ = _ := by
      rw [Finset.sum_image (fun a ha b hb he => hinj he)]
      simp only [hkernel]
      rfl

theorem source_original_unfiltered_ideal_resample_linear434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (S : Finset I)
    (a b : ℂ) (f h : ((i : I) → B i) → ℂ) :
    sourceOriginalUnfilteredIdealResample434 B mu S (fun x => a*f x+b*h x) =
      (fun x => a*sourceOriginalUnfilteredIdealResample434 B mu S f x +
        b*sourceOriginalUnfilteredIdealResample434 B mu S h x) := by
  funext x
  simp only [sourceOriginalUnfilteredIdealResample434, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem source_original_unfiltered_ideal_resample_sum434
    {I K : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (S : Finset I)
    (a : Finset K) (f : K → ((i : I) → B i) → ℂ) :
    sourceOriginalUnfilteredIdealResample434 B mu S (fun x => ∑ k ∈ a, f k x) =
      (fun x => ∑ k ∈ a, sourceOriginalUnfilteredIdealResample434 B mu S (f k) x) := by
  funext x
  simp only [sourceOriginalUnfilteredIdealResample434, Finset.mul_sum]
  exact Finset.sum_comm

/-- Actual one-group list of means equals the complete resampling kernel,
including repeated list entries (idempotence uses normalization). -/
theorem source_original_unfiltered_ideal_mean_list434
    {P : Type} [Fintype P] [DecidableEq P] {M : ℕ}
    (mu : P → ℂ) (hnorm : ∑ p, mu p = 1)
    (K : List (Fin M)) (f : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu ∅ K f =
      sourceOriginalUnfilteredIdealResample434 (fun _ : Fin M => P)
        (fun _ p => mu p) K.toFinset f := by
  induction K generalizing f with
  | nil =>
    simpa [sourceOriginalHoeffdingList434] using
      (source_original_unfiltered_ideal_resample_empty434
        (fun _ : Fin M => P) (fun _ p => mu p) f).symm
  | cons i K ih =>
    have hsingle :
        sourceOriginalHoeffdingMode434 mu ∅ i f =
        sourceOriginalUnfilteredIdealResample434 (fun _ : Fin M => P)
          (fun _ p => mu p) {i} f := by
      funext x
      simp only [sourceOriginalHoeffdingMode434, Finset.notMem_empty, if_false]
      exact (source_original_unfiltered_ideal_resample_singleton434
        (fun _ : Fin M => P) (fun _ p => mu p) i f x).symm
    change sourceOriginalHoeffdingList434 mu ∅ K
      (sourceOriginalHoeffdingMode434 mu ∅ i f) = _
    rw [hsingle, ih, source_original_unfiltered_ideal_resample_union434 _ _ (fun _ => hnorm)]
    congr 1
    simp [Finset.union_comm]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealBalance -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalUnfilteredIdealRealKernel434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℝ) (S : Finset I) (x y : (i : I) → B i) : ℝ :=
  ∏ i, if i ∈ S then mu i (y i) else if y i = x i then 1 else 0

theorem source_original_unfiltered_ideal_kernel_real434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℝ) (S : Finset I) (x y : (i : I) → B i) :
    (sourceOriginalUnfilteredIdealRealKernel434 B mu S x y : ℂ) =
      sourceOriginalUnfilteredIdealResampleKernel434 B (fun i b => (mu i b : ℂ)) S x y := by
  unfold sourceOriginalUnfilteredIdealRealKernel434 sourceOriginalUnfilteredIdealResampleKernel434
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hs : i ∈ S <;> by_cases he : y i = x i <;> simp [hs, he]

/-- Exact detailed balance in the original product law, including zero masses. -/
theorem source_original_unfiltered_ideal_detailed_balance434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℝ) (S : Finset I) (x y : (i : I) → B i) :
    (∏ i, mu i (x i)) * sourceOriginalUnfilteredIdealRealKernel434 B mu S x y =
      (∏ i, mu i (y i)) * sourceOriginalUnfilteredIdealRealKernel434 B mu S y x := by
  unfold sourceOriginalUnfilteredIdealRealKernel434
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hs : i ∈ S
  · simp only [hs, if_true]
    ring
  · by_cases he : y i = x i
    · simp [hs, he]
    · simp [hs, he, Ne.symm he]

/-- Conditional resampling is self-adjoint with the actual product mass.
A subsequent arbitrary phase remains in the second argument; no commuting
of a phase with conditional expectation is used. -/
theorem source_original_unfiltered_ideal_RESAMPLE_SELF_ADJOINT434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℝ) (S : Finset I)
    (F H : ((i : I) → B i) → ℂ) :
    (∑ x, ((∏ i, mu i (x i) : ℝ) : ℂ) * star (F x) *
      sourceOriginalUnfilteredIdealResample434 B (fun i b => (mu i b : ℂ)) S H x) =
    ∑ x, ((∏ i, mu i (x i) : ℝ) : ℂ) *
      star (sourceOriginalUnfilteredIdealResample434 B (fun i b => (mu i b : ℂ)) S F x) * H x := by
  simp only [sourceOriginalUnfilteredIdealResample434,
    ← source_original_unfiltered_ideal_kernel_real434, star_sum, star_mul,
    Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  have hb := source_original_unfiltered_ideal_detailed_balance434 B mu S x y
  have hbc : ((∏ i, mu i (x i) : ℝ) : ℂ) *
      (sourceOriginalUnfilteredIdealRealKernel434 B mu S x y : ℂ) =
      ((∏ i, mu i (y i) : ℝ) : ℂ) *
      (sourceOriginalUnfilteredIdealRealKernel434 B mu S y x : ℂ) := by
    exact_mod_cast hb
  calc
    _ = (((∏ i, mu i (x i) : ℝ) : ℂ) *
        (sourceOriginalUnfilteredIdealRealKernel434 B mu S x y : ℂ)) * (star (F x) * H y) := by simp only [Complex.star_def]; ring
    _ = _ := by rw [hbc]; simp only [Complex.star_def]; ring

/-- All unused-coordinate/tail averages contract in the original law.
This is a derived finite-kernel statement, with no Hilbert budget premise. -/
theorem source_original_unfiltered_ideal_RESAMPLE_CONTRACT434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℝ) (hmu : ∀ i b, 0 ≤ mu i b)
    (hnorm : ∀ i, ∑ b, mu i b = 1) (S : Finset I)
    (f : ((i : I) → B i) → ℂ) :
    (∑ x, (∏ i, mu i (x i)) *
      ‖sourceOriginalUnfilteredIdealResample434 B (fun i b => (mu i b : ℂ)) S f x‖^2) ≤
    ∑ x, (∏ i, mu i (x i)) * ‖f x‖^2 := by
  let q := sourceOriginalUnfilteredIdealRealKernel434 B mu S
  let w := fun x : (i : I) → B i => ∏ i, mu i (x i)
  have hq (x y : (i : I) → B i) : 0 ≤ q x y := by
    apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> first | exact hmu i _ | norm_num
  have hw (x : (i : I) → B i) : 0 ≤ w x :=
    Finset.prod_nonneg (fun i _ => hmu i _)
  have htotal (x : (i : I) → B i) : ∑ y, q x y = 1 := by
    have hc := source_original_unfiltered_ideal_resample_mass434 B
      (fun i b => (mu i b : ℂ)) (fun i => by exact_mod_cast hnorm i) S x
    simp only [← source_original_unfiltered_ideal_kernel_real434] at hc
    exact_mod_cast hc
  have hstationary (y : (i : I) → B i) : (∑ x, w x * q x y) = w y := by
    calc
      _ = ∑ x, w y * q y x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact source_original_unfiltered_ideal_detailed_balance434 B mu S x y
      _ = w y := by rw [← Finset.mul_sum, htotal y, mul_one]
  have hj (x : (i : I) → B i) :
      ‖sourceOriginalUnfilteredIdealResample434 B (fun i b => (mu i b : ℂ)) S f x‖^2 ≤
        ∑ y, q x y * ‖f y‖^2 := by
    have hc := source_original_finite_weighted_complex_kernel_CS434
      (q x) (hq x) (fun _ => 1) f
    simp only [one_mul, norm_one, one_pow, mul_one, htotal, one_mul] at hc
    simpa only [sourceOriginalUnfilteredIdealResample434, q,
      ← source_original_unfiltered_ideal_kernel_real434] using hc
  calc
    _ ≤ ∑ x, w x * (∑ y, q x y * ‖f y‖^2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hj x) (hw x)
    _ = ∑ y, (∑ x, w x * q x y) * ‖f y‖^2 := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = _ := by simp only [hstationary]; rfl

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealDifferenceExpansion -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Ordered products of the actual coordinate differences on dependent alphabets. -/
def sourceOriginalUnfilteredIdealDifferenceList434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) :
    List I → (((i : I) → B i) → ℂ) → (((i : I) → B i) → ℂ)
  | [], f => f
  | i :: K, f => sourceOriginalUnfilteredIdealDifferenceList434 B mu K
      (fun x => f x - sourceOriginalUnfilteredIdealResample434 B mu {i} f x)

/-- Full signed subset expansion; all cancellations occur before any norm.
No multiplier, including the joint phase, is moved through a difference. -/
theorem source_original_unfiltered_ideal_difference_expansion434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (K : List I) (hK : K.Nodup) (f : ((i : I) → B i) → ℂ)
    (x : (i : I) → B i) :
    sourceOriginalUnfilteredIdealDifferenceList434 B mu K f x =
      ∑ S ∈ K.toFinset.powerset,
        (-1:ℂ)^S.card * sourceOriginalUnfilteredIdealResample434 B mu S f x := by
  induction K generalizing f with
  | nil =>
    simp [sourceOriginalUnfilteredIdealDifferenceList434,
      source_original_unfiltered_ideal_resample_empty434]
  | cons i K ih =>
    obtain ⟨hi, hK⟩ := List.nodup_cons.mp hK
    have hit : i ∉ K.toFinset := by simpa using hi
    have hlin (S : Finset I) :
        sourceOriginalUnfilteredIdealResample434 B mu S
          (fun y => f y - sourceOriginalUnfilteredIdealResample434 B mu {i} f y) =
        (fun y => sourceOriginalUnfilteredIdealResample434 B mu S f y -
          sourceOriginalUnfilteredIdealResample434 B mu (insert i S) f y) := by
      have hl := source_original_unfiltered_ideal_resample_linear434 B mu S 1 (-1) f
        (sourceOriginalUnfilteredIdealResample434 B mu {i} f)
      simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hl
      rw [source_original_unfiltered_ideal_resample_union434 B mu hnorm] at hl
      simpa [Finset.union_comm] using hl
    change sourceOriginalUnfilteredIdealDifferenceList434 B mu K
      (fun y => f y - sourceOriginalUnfilteredIdealResample434 B mu {i} f y) x = _
    rw [ih hK]
    simp_rw [hlin]
    rw [List.toFinset_cons, Finset.sum_powerset_insert hit]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    have his : i ∉ S := fun hs => hit ((Finset.mem_powerset.mp hS) hs)
    rw [Finset.card_insert_of_notMem his, pow_succ]
    ring

/-- The full alternating subset sum with the original trailing average is
exactly probe differences applied to that average. -/
theorem source_original_unfiltered_ideal_difference_tail_expansion434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (K : List I) (hK : K.Nodup) (T : Finset I)
    (f : ((i : I) → B i) → ℂ) (x : (i : I) → B i) :
    sourceOriginalUnfilteredIdealDifferenceList434 B mu K
      (sourceOriginalUnfilteredIdealResample434 B mu T f) x =
      ∑ S ∈ K.toFinset.powerset,
        (-1:ℂ)^S.card * sourceOriginalUnfilteredIdealResample434 B mu (S ∪ T) f x := by
  rw [source_original_unfiltered_ideal_difference_expansion434 B mu hnorm K hK]
  simp only [source_original_unfiltered_ideal_resample_union434 B mu hnorm]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealOneGroup -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_unfiltered_ideal_mode_append434
    {P : Type} [Fintype P] [DecidableEq P] {M : ℕ}
    (mu : P → ℂ) (S : Finset (Fin M)) (K L : List (Fin M))
    (f : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu S (K++L) f =
      sourceOriginalHoeffdingList434 mu S L (sourceOriginalHoeffdingList434 mu S K f) := by
  induction K generalizing f with
  | nil => rfl
  | cons i K ih =>
    change sourceOriginalHoeffdingList434 mu S (K++L)
      (sourceOriginalHoeffdingMode434 mu S i f) = _
    exact ih _

theorem source_original_unfiltered_ideal_differences_modes434
    {P : Type} [Fintype P] [DecidableEq P] {M : ℕ}
    (mu : P → ℂ) (S : Finset (Fin M)) (K : List (Fin M))
    (hK : ∀ i ∈ K, i ∈ S) (f : (Fin M → P) → ℂ) :
    sourceOriginalUnfilteredIdealDifferenceList434
      (fun _ : Fin M => P) (fun _ p => mu p) K f =
      sourceOriginalHoeffdingList434 mu S K f := by
  induction K generalizing f with
  | nil => rfl
  | cons i K ih =>
    have hi : i ∈ S := hK i (by simp)
    have ht : ∀ j ∈ K, j ∈ S := fun j hj => hK j (by simp [hj])
    have hs :
        (fun x => f x - sourceOriginalUnfilteredIdealResample434
          (fun _ : Fin M => P) (fun _ p => mu p) {i} f x) =
        sourceOriginalHoeffdingMode434 mu S i f := by
      funext x
      simp only [sourceOriginalHoeffdingMode434, if_pos hi, sourceOriginalBigCoordinateDiff434]
      congr 1
      exact source_original_unfiltered_ideal_resample_singleton434
        (fun _ : Fin M => P) (fun _ p => mu p) i f x
    change sourceOriginalUnfilteredIdealDifferenceList434 _ _ K _ = _
    rw [hs, ih ht]
    rfl

/-- One complete signed block sum is the exact selected-Hoeffding survivor.
The SAME-group tail mean is applied after symmetrization downstream. -/
theorem source_original_unfiltered_ideal_ONE_GROUP_ALTERNATING434
    {P : Type} [Fintype P] [DecidableEq P] {M : ℕ}
    (mu : P → ℂ) (hnorm : ∑ p, mu p = 1)
    (S T : Finset (Fin M)) (hd : Disjoint S T)
    (f : (Fin M → P) → ℂ) :
    (fun x => ∑ A ∈ S.powerset, (-1:ℂ)^A.card *
      sourceOriginalUnfilteredIdealResample434
        (fun _ : Fin M => P) (fun _ p => mu p) (A∪T) f x) =
    sourceOriginalHoeffdingList434 mu S (S∪T).toList f := by
  have he :
      (fun x => ∑ A ∈ S.powerset, (-1:ℂ)^A.card *
        sourceOriginalUnfilteredIdealResample434
          (fun _ : Fin M => P) (fun _ p => mu p) (A∪T) f x) =
      sourceOriginalUnfilteredIdealDifferenceList434
        (fun _ : Fin M => P) (fun _ p => mu p) S.toList
        (sourceOriginalUnfilteredIdealResample434
          (fun _ : Fin M => P) (fun _ p => mu p) T f) := by
    funext x
    simpa only [Finset.toList_toFinset] using
      (source_original_unfiltered_ideal_difference_tail_expansion434
        (fun _ : Fin M => P) (fun _ p => mu p) (fun _ => hnorm)
        S.toList (Finset.nodup_toList _) T f x).symm
  rw [he, source_original_unfiltered_ideal_differences_modes434 mu S S.toList (by simp)]
  have ht :
      sourceOriginalUnfilteredIdealResample434
        (fun _ : Fin M => P) (fun _ p => mu p) T f =
      sourceOriginalHoeffdingList434 mu S T.toList f := by
    rw [← Finset.toList_toFinset T]
    rw [← source_original_unfiltered_ideal_mean_list434 mu hnorm]
    simp only [Finset.toList_toFinset]
    apply source_original_hoeffding_list_subset_ext434
    intro i hi
    simp only [Finset.mem_toList] at hi
    simp only [Finset.notMem_empty, false_iff]
    exact fun hs => Finset.disjoint_left.mp hd hs hi
  rw [ht, ← source_original_unfiltered_ideal_mode_append434,
    source_original_unfiltered_ideal_list_selected434 mu hnorm,
    source_original_unfiltered_ideal_list_selected434 mu hnorm]
  congr 1
  ext R
  simp only [Finset.mem_filter, List.mem_append, Finset.mem_toList,
    Finset.mem_union, or_comm]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealGroupLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact disintegration of a resampling mask confined to one original group.
Every other group is frozen, while the test may couple all groups. -/
theorem source_original_unfiltered_ideal_GROUP_RESAMPLE434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℂ) (g : G) (S : Finset (Fin M))
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (x : SourceOriginalJointBigState434 BP M) :
    sourceOriginalUnfilteredIdealResample434
      (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => mu z.1 p)
      (S.image (fun i => (⟨g,i⟩ : Σ _g : G, Fin M)))
      (fun y => f (fun h i => y ⟨h,i⟩)) (fun z => x z.1 z.2) =
    sourceOriginalUnfilteredIdealResample434
      (fun _ : Fin M => BP g) (fun _ p => mu g p) S
      (fun u => f (Function.update x g u)) (x g) := by
  let B := fun z : Σ _g : G, Fin M => BP z.1
  let w := fun z (p : B z) => mu z.1 p
  let mask := S.image (fun i => (⟨g,i⟩ : Σ _g : G, Fin M))
  let base : (z : Σ _g : G, Fin M) → B z := fun z => x z.1 z.2
  let upd : (Fin M → BP g) → ((z : Σ _g : G, Fin M) → B z) :=
    fun u z => Function.update x g u z.1 z.2
  have hinj : Function.Injective upd := by
    intro u v he
    funext i
    have h := congrFun he ⟨g,i⟩
    simpa [upd] using h
  have hmem (i : Fin M) : (⟨g,i⟩ : Σ _g : G, Fin M) ∈ mask ↔ i ∈ S := by
    simp [mask, Sigma.mk.inj_iff]
  have hnot (h : G) (hh : h ≠ g) (i : Fin M) :
      (⟨h,i⟩ : Σ _g : G, Fin M) ∉ mask := by
    intro hz
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hz
    exact hh (congrArg Sigma.fst he).symm
  have hk (u : Fin M → BP g) :
      sourceOriginalUnfilteredIdealResampleKernel434 B w mask base (upd u) =
      sourceOriginalUnfilteredIdealResampleKernel434
        (fun _ : Fin M => BP g) (fun _ p => mu g p) S (x g) u := by
    unfold sourceOriginalUnfilteredIdealResampleKernel434
    rw [Fintype.prod_sigma]
    rw [Finset.prod_eq_single g]
    · apply Finset.prod_congr rfl
      intro i hi
      simp [hmem, w, base, upd]
    · intro h hh hne
      apply Finset.prod_eq_one
      intro i hi
      simp [hnot h hne i, w, base, upd, Function.update_of_ne hne]
    · simp
  have hz (y : (z : Σ _g : G, Fin M) → B z) (hy : y ∉ Finset.univ.image upd) :
      sourceOriginalUnfilteredIdealResampleKernel434 B w mask base y = 0 := by
    by_contra hn
    have he : upd (fun i => y ⟨g,i⟩) = y := by
      funext z
      rcases z with ⟨h,i⟩
      by_cases hh : h = g
      · subst h
        simp [upd]
      · have hyi := source_original_unfiltered_ideal_resample_copy434 B w mask base y hn
          ⟨h,i⟩ (hnot h hh i)
        simpa [upd, base, Function.update_of_ne hh] using hyi.symm
    exact hy (Finset.mem_image.mpr ⟨(fun i => y ⟨g,i⟩), Finset.mem_univ _, he⟩)
  change (∑ y, sourceOriginalUnfilteredIdealResampleKernel434 B w mask base y *
      f (fun h i => y ⟨h,i⟩)) = _
  calc
    _ = ∑ y ∈ Finset.univ.image upd,
        sourceOriginalUnfilteredIdealResampleKernel434 B w mask base y *
          f (fun h i => y ⟨h,i⟩) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y hy hyn
      rw [hz y hyn, zero_mul]
    _ = _ := by
      rw [Finset.sum_image (fun a ha b hb he => hinj he)]
      simp only [hk]
      rfl

/-- The original single-group survivor is exactly its alternating mask sum
inside the full dependent physical coordinate carrier. -/
theorem source_original_unfiltered_ideal_GROUP_ALTERNATING434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ) (hnorm : ∀ g, ∑ p, mu g p = 1)
    (g : G) (S T : Finset (Fin M)) (hd : Disjoint S T)
    (f : SourceOriginalJointBigState434 BP M → ℂ)
    (x : SourceOriginalJointBigState434 BP M) :
    (∑ A ∈ S.powerset, (-1:ℂ)^A.card *
      sourceOriginalUnfilteredIdealResample434
        (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ))
        ((A∪T).image (fun i => (⟨g,i⟩ : Σ _g : G, Fin M)))
        (fun y => f (fun h i => y ⟨h,i⟩)) (fun z => x z.1 z.2)) =
    sourceOriginalUnfilteredIdealGroup434 BP mu g S T f x := by
  simp_rw [source_original_unfiltered_ideal_GROUP_RESAMPLE434 BP M
    (fun g p => (mu g p : ℂ)) g]
  have hn : ∑ p, (mu g p : ℂ) = 1 := by exact_mod_cast hnorm g
  exact congrFun (source_original_unfiltered_ideal_ONE_GROUP_ALTERNATING434
    (fun p => (mu g p : ℂ)) hn S T hd (fun u => f (Function.update x g u))) (x g)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealPairAlgebra -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

def sourceOriginalUnfilteredIdealPair434
    {X : Type} [Fintype X] (w : X → ℝ) (Phi F H : X → ℂ) : ℂ :=
  ∑ x, (w x : ℂ) * star (F x) * Phi x * H x

theorem source_original_unfiltered_ideal_pair_CS434
    {X : Type} [Fintype X] (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (Phi : X → ℂ) (hPhi : ∀ x, ‖Phi x‖ = 1) (F H : X → ℂ) :
    ‖sourceOriginalUnfilteredIdealPair434 w Phi F H‖^2 ≤
      (∑ x, w x * ‖F x‖^2) * (∑ x, w x * ‖H x‖^2) := by
  have h := source_original_finite_weighted_complex_kernel_CS434
    w hw (fun x => star (F x) * Phi x) H
  simpa only [sourceOriginalUnfilteredIdealPair434, mul_assoc,
    norm_mul, norm_star, hPhi, mul_one] using h

theorem source_original_unfiltered_ideal_pair_resample434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℝ) (S T : Finset I)
    (Phi F H : ((i : I) → B i) → ℂ) :
    (∑ x, ((∏ i, mu i (x i) : ℝ) : ℂ) * star (F x) *
      sourceOriginalUnfilteredIdealResample434 B (fun i b => (mu i b : ℂ)) S
        (fun y => Phi y * sourceOriginalUnfilteredIdealResample434 B
          (fun i b => (mu i b : ℂ)) T H y) x) =
    sourceOriginalUnfilteredIdealPair434 (fun x => ∏ i, mu i (x i)) Phi
      (sourceOriginalUnfilteredIdealResample434 B (fun i b => (mu i b : ℂ)) S F)
      (sourceOriginalUnfilteredIdealResample434 B (fun i b => (mu i b : ℂ)) T H) := by
  rw [source_original_unfiltered_ideal_RESAMPLE_SELF_ADJOINT434]
  simp only [sourceOriginalUnfilteredIdealPair434, mul_assoc]

/-- Finite alternating sums in both slots retain the full coupled phase. -/
theorem source_original_unfiltered_ideal_pair_alternating434
    {X I K : Type} [Fintype X] [DecidableEq I] [DecidableEq K]
    (w : X → ℝ) (Phi : X → ℂ)
    (A : Finset (Finset I)) (B : Finset (Finset K))
    (F : Finset I → X → ℂ) (H : Finset K → X → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, (-1:ℂ)^a.card * (-1:ℂ)^b.card *
      sourceOriginalUnfilteredIdealPair434 w Phi (F a) (H b)) =
    sourceOriginalUnfilteredIdealPair434 w Phi
      (fun x => ∑ a ∈ A, (-1:ℂ)^a.card * F a x)
      (fun x => ∑ b ∈ B, (-1:ℂ)^b.card * H b x) := by
  simp only [sourceOriginalUnfilteredIdealPair434, star_sum, star_mul,
    star_pow, star_neg, star_one, Finset.mul_sum, Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext a
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem source_original_unfiltered_ideal_pair_sum_left434
    {X I : Type} [Fintype X] [DecidableEq I]
    (w : X → ℝ) (Phi : X → ℂ) (A : Finset (Finset I))
    (F : Finset I → X → ℂ) (H : X → ℂ) :
    (∑ a ∈ A, (-1:ℂ)^a.card *
      sourceOriginalUnfilteredIdealPair434 w Phi (F a) H) =
    sourceOriginalUnfilteredIdealPair434 w Phi
      (fun x => ∑ a ∈ A, (-1:ℂ)^a.card * F a x) H := by
  simp only [sourceOriginalUnfilteredIdealPair434, star_sum, star_mul,
    star_pow, star_neg, star_one, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem source_original_unfiltered_ideal_pair_sum_right434
    {X I : Type} [Fintype X] [DecidableEq I]
    (w : X → ℝ) (Phi : X → ℂ) (A : Finset (Finset I))
    (F : X → ℂ) (H : Finset I → X → ℂ) :
    (∑ a ∈ A, (-1:ℂ)^a.card *
      sourceOriginalUnfilteredIdealPair434 w Phi F (H a)) =
    sourceOriginalUnfilteredIdealPair434 w Phi F
      (fun x => ∑ a ∈ A, (-1:ℂ)^a.card * H a x) := by
  simp only [sourceOriginalUnfilteredIdealPair434, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem source_original_unfiltered_ideal_three_square434 (a b c : ℂ) :
    ‖a+b-c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have h : ‖a+b-c‖ ≤ ‖a‖+‖b‖+‖c‖ :=
    le_trans (norm_sub_le _ _) (by have h := norm_add_le a b; linarith)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith only [hs, sq_nonneg (‖a‖-‖b‖), sq_nonneg (‖a‖-‖c‖),
    sq_nonneg (‖b‖-‖c‖)]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealParameterBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 200000

/-- Probe order is chosen from the fixed count constant and requested
accuracy, before any endpoint length or moving source prime data. -/
theorem source_original_unfiltered_ideal_choose_order434
    (A c : ℝ) (hc : 0 < c) :
    ∃ m : ℕ, 1 ≤ m ∧ A ≤ c*Real.log ((m+1:ℕ):ℝ) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (Real.exp (A/c)))
  have hm1 : (1:ℝ) ≤ (m:ℝ) := (le_max_left _ _).trans hm.le
  have hmnat : 1 ≤ m := by exact_mod_cast hm1
  have hexp : Real.exp (A/c) ≤ ((m+1:ℕ):ℝ) := by
    have he := (le_max_right (1:ℝ) (Real.exp (A/c))).trans hm.le
    push_cast
    linarith
  have hh := Real.log_le_log (Real.exp_pos (A/c)) hexp
  rw [Real.log_exp, div_le_iff₀ hc] at hh
  exact ⟨m,hmnat,by nlinarith only [hh]⟩

/-- Explicit absorption of the true 3*(9+1+1) squared-pairing budget.
The arithmetic slack is two powers of L, not an assumed smallness factor. -/
theorem source_original_unfiltered_ideal_absorb_33_434
    (L E : ℝ) (hL : 33 ≤ L) :
    33*L^(-(2*E+2)) ≤ L^(-(2*E)) := by
  have hLp : 0 < L := by linarith
  have hsq : (33:ℝ) ≤ L^2 := by nlinarith
  calc
    _ ≤ L^2 * L^(-(2*E+2)) :=
      mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hLp.le _)
    _ = L^(-(2*E)) := by
      rw [← Real.rpow_two, ← Real.rpow_add hLp]
      congr 1
      ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealProbeExpansion -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalUnfilteredIdealProbeEmbedding434
    {G : Type} (J ell m : ℕ) (hmJ : m ≤ J) :
    G × Fin m ↪ (Σ _g : G, Fin (J+ell)) where
  toFun z := ⟨z.1,(z.2.castLE hmJ).castAdd ell⟩
  inj' := by
    rintro ⟨g,i⟩ ⟨h,j⟩ he
    have hg := congrArg Sigma.fst he
    have hi := congrArg (fun z : Σ _g : G, Fin (J+ell) => z.2.val) he
    dsimp only at hg hi
    subst h
    congr
    exact Fin.ext hi

theorem source_original_unfiltered_ideal_mask_image434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (A : Finset (G × Fin m)) :
    sourceOriginalUnfilteredIdealMask434 J ell m hmJ A =
      A.image (sourceOriginalUnfilteredIdealProbeEmbedding434 J ell m hmJ) ∪
        sourceOriginalUnfilteredIdealMask434 J ell m hmJ ∅ := by
  ext z
  rcases z with ⟨g,i⟩
  have him :
      (⟨g,i⟩ : Σ _g : G, Fin (J+ell)) ∈
        A.image (sourceOriginalUnfilteredIdealProbeEmbedding434 J ell m hmJ) ↔
      sourceOriginalUnfilteredIdealAt434 J ell m hmJ A g i := by
    constructor
    · intro hz
      obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hz
      rcases r with ⟨h,j⟩
      have hg : h = g := congrArg Sigma.fst he
      subst h
      have hi : (j.castLE hmJ).castAdd ell = i :=
        congrArg (fun z : Σ _g : G, Fin (J+ell) => z.2) he
      exact ⟨j,hr,hi⟩
    · rintro ⟨j,hj,hi⟩
      exact Finset.mem_image.mpr ⟨(g,j),hj,by
        change (⟨g,(j.castLE hmJ).castAdd ell⟩ : Σ _g : G, Fin (J+ell)) = ⟨g,i⟩
        rw [hi]⟩
  simp only [Finset.mem_union, him, sourceOriginalUnfilteredIdealMask434,
    Finset.mem_filter, Finset.mem_univ, true_and]
  have he : ¬ sourceOriginalUnfilteredIdealAt434 J ell m hmJ (∅ : Finset (G × Fin m)) g i := by
    rintro ⟨j,hj,_⟩
    exact Finset.notMem_empty _ hj
  simp only [he, or_false]
  exact or_comm

/-- The actual block powerset, with its actual sign and slot casts, is
exactly a product of probe differences after ALL original tail averages.
This includes repeated numerical primes as separate coordinate labels. -/
theorem source_original_unfiltered_ideal_ACTUAL_PROBE_EXPANSION434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (block : Finset G)
    (mu : (g : G) → BP g → ℂ) (hnorm : ∀ g, ∑ p, mu g p = 1)
    (f : ((z : Σ _g : G, Fin (J+ell)) → BP z.1) → ℂ)
    (x : (z : Σ _g : G, Fin (J+ell)) → BP z.1) :
    let B := fun z : Σ _g : G, Fin (J+ell) => BP z.1
    let w := fun z (p : B z) => mu z.1 p
    let probes := (sourceOriginalProbeBlock434 block m).image
      (sourceOriginalUnfilteredIdealProbeEmbedding434 J ell m hmJ)
    let tails := sourceOriginalUnfilteredIdealMask434 J ell m hmJ (∅ : Finset (G × Fin m))
    (∑ A ∈ (sourceOriginalProbeBlock434 block m).powerset,
      (-1:ℂ)^A.card *
        sourceOriginalUnfilteredIdealResample434 B w
          (sourceOriginalUnfilteredIdealMask434 J ell m hmJ A) f x) =
    sourceOriginalUnfilteredIdealDifferenceList434 B w probes.toList
      (sourceOriginalUnfilteredIdealResample434 B w tails f) x := by
  dsimp only
  rw [source_original_unfiltered_ideal_difference_tail_expansion434
    (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => mu z.1 p)
    (fun z => hnorm z.1) _ (Finset.nodup_toList _)]
  rw [Finset.toList_toFinset, Finset.powerset_image,
    Finset.sum_image (fun a ha b hb he =>
      Finset.image_injective (sourceOriginalUnfilteredIdealProbeEmbedding434 J ell m hmJ).injective he)]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.card_image_of_injective _ (sourceOriginalUnfilteredIdealProbeEmbedding434 J ell m hmJ).injective,
    source_original_unfiltered_ideal_mask_image434 J ell m hmJ A]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealSectorTransfer -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap sizes : BG → ℕ)
variable (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)
local notation "Small" => Green64SmallHaar.GroupState SP sm (J+ell)
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Torus" => memoryFrozenResidueGroup SP sm BP bm sizes prime

/-- The literal Fourier pairing has exactly the normalization of the
existing SMALL/OLD transfer. This retains every indexed Fock occurrence. -/
theorem source_original_unfiltered_ideal_SECTOR_LIFTED_PAIR434
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (U F : Small → Active → Old → ℂ) :
    sourceOriginalB26SectorCleanPair434 SP sm BP bm J ell m cap
      sizes hsizes prime patterns mu V K q Vs zeta theta o k U F =
    sourceOriginalB26SmallOldLiftedPair434 SP sm BP bm J ell sizes prime q Vs mu
      (fun d psi u v => ∑ a : Active,
        ((∏ g,∏ i,mu g (a g i):ℝ):ℂ)*star (u a)*
          sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V K
            (sourceOriginalB26SmallTupleD434 SP sm J ell d) zeta
            (theta+sourceOriginalB26ModeAngle434 SP sm BP bm sizes prime psi/(2*Real.pi))
            o k v a) U F := by
  rw [source_original_B26_CLEAN_SMALL_PHYSICAL_FOURIER_PAIR434
    SP sm BP bm J ell m cap sizes hsizes prime patterns mu V K q hq Vs hVs]
  simp_rw [source_original_B26_sector_mass_factor434]
  unfold sourceOriginalB26SmallOldLiftedPair434
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ss _
  apply Finset.sum_congr rfl
  intro tt _
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi _
  apply Finset.sum_congr rfl
  intro a _
  simp only [starRingEnd_apply]
  ring

/-- A literal unmarked rho=1 CLEAN sector bound. The exact BIG estimate
is its only arithmetic premise; the eventual canonical theorem below
discharges that premise. No Fourier-cardinality or Fock-size loss occurs. -/
theorem source_original_unfiltered_ideal_SECTOR_TRANSFER434
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (eps : ℝ) (heps : 0 ≤ eps)
    (hBig : ∀ (d : ℕ), 0 < d → ∀ (t : ℝ) (u v : Active → ℂ),
      ‖(∑ a : Active,((∏ g,∏ i,mu g (a g i):ℝ):ℂ)*star (u a)*
        sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V K
          d zeta t o k v a)‖^2 ≤
      eps*sourceOriginalB26ActiveEnergy434 BP J ell mu u*
        sourceOriginalB26ActiveEnergy434 BP J ell mu v)
    (U F : Small → Active → Old → ℂ) :
    ‖sourceOriginalB26SectorCleanPair434 SP sm BP bm J ell m cap
      sizes hsizes prime patterns mu V K q Vs zeta theta o k U F‖^2 ≤
    eps*(memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2*
      sourceOriginalB26SectorEnergy434 SP sm BP bm J ell cap sizes hsizes prime Vs mu U*
      sourceOriginalB26SectorEnergy434 SP sm BP bm J ell cap sizes hsizes prime Vs mu F := by
  rw [source_original_unfiltered_ideal_SECTOR_LIFTED_PAIR434
    SP sm BP bm J ell m cap sizes hsizes prime patterns mu V K q hq.le Vs hVs]
  apply source_original_B26_SMALL_OLD_TRANSFER434 SP sm BP bm J ell cap sizes hsizes prime
    q hq hq1 Vs hVs mu hmu eps heps
  intro d psi u v
  exact hBig _ (Green64Analytic.CorrelationSquare.source_original_B26_small_tuple_positive434
    SP sm J ell d) _ u v

/-- The same bound for the original ordered physical CLEAN coefficient
and symmetric output, with the original sector mass and both endpoint tests.
No restriction on repeated OLD prime tuples has been introduced. -/
theorem source_original_unfiltered_ideal_LITERAL_SECTOR_TRANSFER434
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p) (V : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (eps : ℝ) (heps : 0 ≤ eps)
    (hBig : ∀ (d : ℕ), 0 < d → ∀ (t : ℝ) (u v : Active → ℂ),
      ‖(∑ a : Active,((∏ g,∏ i,mu g (a g i):ℝ):ℂ)*star (u a)*
        sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V K
          d zeta t o k v a)‖^2 ≤
      eps*sourceOriginalB26ActiveEnergy434 BP J ell mu u*
        sourceOriginalB26ActiveEnergy434 BP J ell mu v)
    (U : FullPhysicalState SP sm BP bm (J+ell) cap → ℂ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ) :
    ‖sourceOriginalB26LiteralSectorCleanPair434 SP sm BP bm J ell m cap
      sizes hsizes prime patterns mu V K q Vs zeta theta o k U F‖^2 ≤
    eps*(memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2*
      sourceOriginalB26SectorEnergy434 SP sm BP bm J ell cap sizes hsizes prime Vs mu
        (sourceOriginalB26SourcePullback434 SP sm BP bm J ell cap sizes hsizes prime U)*
      sourceOriginalB26SectorEnergy434 SP sm BP bm J ell cap sizes hsizes prime Vs mu
        (sourceOriginalB26TargetPullback434 SP sm BP bm J ell cap sizes hsizes prime F) := by
  rw [source_original_B26_CLEAN_LITERAL_SECTOR_PAIR434]
  exact source_original_unfiltered_ideal_SECTOR_TRANSFER434 SP sm BP bm J ell m cap
    sizes hsizes prime patterns mu hmu V K q hq hq1 Vs hVs zeta theta o k eps heps hBig _ _

end Green64FullPhysicalE

end

end

/-! ## SourceOriginalUnfilteredIdealSignedFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_unfiltered_ideal_powerset_empty_split434
    {I : Type} [DecidableEq I] (S : Finset I) (f : Finset I → ℂ) :
    (∑ A ∈ S.powerset, f A) = f ∅ + ∑ A ∈ S.powerset.filter Finset.Nonempty, f A := by
  have he : S.powerset.filter Finset.Nonempty = S.powerset.erase ∅ := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.nonempty_iff_ne_empty]
    exact and_comm
  rw [he, add_comm]
  exact (Finset.sum_erase_add S.powerset f (by simp)).symm

/-- The full two-block cancellation identity, with no bounds taken termwise. -/
theorem source_original_unfiltered_ideal_rectangle434
    {I : Type} [DecidableEq I] (A B : Finset I) (r : Finset I → Finset I → ℂ) :
    r ∅ ∅ - (∑ a ∈ A.powerset.filter Finset.Nonempty,
      ∑ b ∈ B.powerset.filter Finset.Nonempty, r a b) =
    (∑ a ∈ A.powerset, r a ∅) + (∑ b ∈ B.powerset, r ∅ b) -
      (∑ a ∈ A.powerset, ∑ b ∈ B.powerset, r a b) := by
  rw [source_original_unfiltered_ideal_powerset_empty_split434 A,
    source_original_unfiltered_ideal_powerset_empty_split434 B,
    source_original_unfiltered_ideal_powerset_empty_split434 A]
  simp_rw [source_original_unfiltered_ideal_powerset_empty_split434 B]
  rw [Finset.sum_add_distrib]
  ring

/-- Both scalar orientations preserve the real alternating sign. This does
not assert the separate memoryOrientationK block-swap bridge. -/
theorem source_original_unfiltered_ideal_raw_sign434
    (n : ℕ) (D : ℕ) (zeta theta : ℝ) (o k : ℤ) :
    originalEdgeScalar (-((-1:ℂ)^n)) zeta theta D o k =
      -((-1:ℂ)^n) * originalEdgeScalar 1 zeta theta D o k := by
  unfold originalEdgeScalar originalOrientedKernel
  split_ifs <;> simp <;> ring

theorem source_original_unfiltered_ideal_resample_scalar434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (S : Finset I) (c : ℂ)
    (f : ((i : I) → B i) → ℂ) :
    sourceOriginalUnfilteredIdealResample434 B mu S (fun x => c*f x) =
      (fun x => c*sourceOriginalUnfilteredIdealResample434 B mu S f x) := by
  funext x
  simp only [sourceOriginalUnfilteredIdealResample434, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Signed factorization of the ORIGINAL per-pattern row. -/
theorem source_original_unfiltered_ideal_LITERAL_RAW_SIGNED434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hd : Disjoint ν.1 ν.2)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hnorm : ∀ g, ∑ p, mu g p = 1)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    let B := fun z : Σ _g : G, Fin (J+ell) => {p : ℕ // p ∈ P z.1}
    let e := sourceOriginalUnfilteredIdealFlatEquiv434
      (fun g => {p : ℕ // p ∈ P g}) (J+ell)
    let w := fun z (p : B z) => (mu z.1 p : ℂ)
    let SA := sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.1
    let SB := sourceOriginalUnfilteredIdealMask434 J ell m hmJ ν.2
    let Phi := sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k
    (∑ t, sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
      sourceOriginalB26CanonicalRawValue434 P J ell m hmJ ν dsmall s t
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta theta o k * f t) =
    -((-1:ℂ)^ν.1.card * (-1:ℂ)^ν.2.card) *
      sourceOriginalUnfilteredIdealResample434 B w SA
        (fun x => Phi x *
          sourceOriginalUnfilteredIdealResample434 B w SB (fun y => f (e.symm y)) x)
        (e s) := by
  dsimp only
  rw [source_original_unfiltered_ideal_LITERAL_RAW_COMPOSITION434 P J ell m hmJ ν hd mu hnorm]
  simp_rw [sourceOriginalUnfilteredIdealHeadPhase434,
    source_original_unfiltered_ideal_raw_sign434]
  simp only [mul_assoc, source_original_unfiltered_ideal_resample_scalar434, pow_add]

/-- Literal complete comparison-RAW row plus its positive empty-mask row,
summed over the ACTUAL full two-block family, equals exactly three residual
full-powerset sums. The joint phase remains between the two averages.
The separate frozen RAW-none identification is still needed downstream. -/
theorem source_original_unfiltered_ideal_ACTUAL_SIGNED_FAMILY_RESIDUAL434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (blockA blockB : Finset G)
    (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hnorm : ∀ g, ∑ p, mu g p = 1)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    let B := fun z : Σ _g : G, Fin (J+ell) => {p : ℕ // p ∈ P z.1}
    let e := sourceOriginalUnfilteredIdealFlatEquiv434
      (fun g => {p : ℕ // p ∈ P g}) (J+ell)
    let w := fun z (p : B z) => (mu z.1 p : ℂ)
    let Phi := sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k
    let r := fun A B' : Finset (G × Fin m) =>
      (-1:ℂ)^A.card * (-1:ℂ)^B'.card *
      sourceOriginalUnfilteredIdealResample434 B w
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ A)
        (fun x => Phi x * sourceOriginalUnfilteredIdealResample434 B w
          (sourceOriginalUnfilteredIdealMask434 J ell m hmJ B') (fun y => f (e.symm y)) x) (e s)
    r ∅ ∅ +
      (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        ∑ t, sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
        sourceOriginalB26CanonicalRawValue434 P J ell m hmJ ν dsmall s t
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta theta o k * f t) =
      (∑ A ∈ (sourceOriginalProbeBlock434 blockA m).powerset, r A ∅) +
      (∑ B' ∈ (sourceOriginalProbeBlock434 blockB m).powerset, r ∅ B') -
      (∑ A ∈ (sourceOriginalProbeBlock434 blockA m).powerset,
        ∑ B' ∈ (sourceOriginalProbeBlock434 blockB m).powerset, r A B') := by
  dsimp only
  have hr := source_original_unfiltered_ideal_rectangle434
    (sourceOriginalProbeBlock434 blockA m) (sourceOriginalProbeBlock434 blockB m)
    (fun A B' => (-1:ℂ)^A.card * (-1:ℂ)^B'.card *
      sourceOriginalUnfilteredIdealResample434
        (fun z : Σ _g : G, Fin (J+ell) => {p : ℕ // p ∈ P z.1})
        (fun z p => (mu z.1 p : ℂ))
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ A)
        (fun x => sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k x *
          sourceOriginalUnfilteredIdealResample434
            (fun z : Σ _g : G, Fin (J+ell) => {p : ℕ // p ∈ P z.1})
            (fun z p => (mu z.1 p : ℂ))
            (sourceOriginalUnfilteredIdealMask434 J ell m hmJ B')
            (fun y => f ((sourceOriginalUnfilteredIdealFlatEquiv434
              (fun g => {p : ℕ // p ∈ P g}) (J+ell)).symm y)) x)
        ((sourceOriginalUnfilteredIdealFlatEquiv434
          (fun g => {p : ℕ // p ∈ P g}) (J+ell)) s))
  rw [← hr, sub_eq_add_neg]
  congr 1
  conv_rhs => rw [← Finset.sum_product', ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro ν hν
  have hd := source_original_probe_memory_actual_pattern_disjoint434
    blockA blockB hBlocks m ν hν
  rw [source_original_unfiltered_ideal_LITERAL_RAW_SIGNED434 P J ell m hmJ ν hd mu hnorm]
  ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealOperatorAlgebra -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_unfiltered_ideal_difference_append434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (K L : List I)
    (f : ((i : I) → B i) → ℂ) :
    sourceOriginalUnfilteredIdealDifferenceList434 B mu (K++L) f =
      sourceOriginalUnfilteredIdealDifferenceList434 B mu L
        (sourceOriginalUnfilteredIdealDifferenceList434 B mu K f) := by
  induction K generalizing f with
  | nil => rfl
  | cons i K ih =>
    change sourceOriginalUnfilteredIdealDifferenceList434 B mu (K++L) _ = _
    exact ih _

/-- Probe differences commute with coordinate means, never with a phase. -/
theorem source_original_unfiltered_ideal_difference_mean_commute434
    {I : Type} [Fintype I] [DecidableEq I]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (K : List I) (hK : K.Nodup) (T : Finset I)
    (f : ((i : I) → B i) → ℂ) :
    sourceOriginalUnfilteredIdealDifferenceList434 B mu K
      (sourceOriginalUnfilteredIdealResample434 B mu T f) =
    sourceOriginalUnfilteredIdealResample434 B mu T
      (sourceOriginalUnfilteredIdealDifferenceList434 B mu K f) := by
  have he (h : ((i : I) → B i) → ℂ) :
      sourceOriginalUnfilteredIdealDifferenceList434 B mu K h =
      (fun x => ∑ S ∈ K.toFinset.powerset,
        (-1:ℂ)^S.card * sourceOriginalUnfilteredIdealResample434 B mu S h x) := by
    funext x
    exact source_original_unfiltered_ideal_difference_expansion434 B mu hnorm K hK h x
  rw [he, he, source_original_unfiltered_ideal_resample_sum434]
  simp_rw [source_original_unfiltered_ideal_resample_scalar434,
    source_original_unfiltered_ideal_resample_union434 B mu hnorm]
  funext x
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.union_comm]

/-- Full alternating expansion after an injective coordinate relabeling. -/
theorem source_original_unfiltered_ideal_difference_image434
    {I A : Type} [Fintype I] [DecidableEq I] [DecidableEq A]
    (B : I → Type) [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (mu : (i : I) → B i → ℂ) (hnorm : ∀ i, ∑ b, mu i b = 1)
    (e : A ↪ I) (S T : Finset A) (f : ((i : I) → B i) → ℂ) :
    sourceOriginalUnfilteredIdealDifferenceList434 B mu (S.image e).toList
      (sourceOriginalUnfilteredIdealResample434 B mu (T.image e) f) =
    (fun x => ∑ U ∈ S.powerset, (-1:ℂ)^U.card *
      sourceOriginalUnfilteredIdealResample434 B mu ((U∪T).image e) f x) := by
  funext x
  rw [source_original_unfiltered_ideal_difference_tail_expansion434
    B mu hnorm _ (Finset.nodup_toList _), Finset.toList_toFinset, Finset.powerset_image,
    Finset.sum_image (fun a ha b hb he => Finset.image_injective e.injective he)]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.card_image_of_injective _ e.injective, Finset.image_union]

def sourceOriginalUnfilteredIdealGroupEmbedding434
    {G : Type} (M : ℕ) (g : G) : Fin M ↪ (Σ _g : G, Fin M) where
  toFun i := ⟨g,i⟩
  inj' := by intro i j he; exact congrArg (fun z : Σ _g : G, Fin M => z.2) he

/-- Exact conjugacy from the selected original joint group operator to
probe differences and local tail means on the flat physical coordinates. -/
theorem source_original_unfiltered_ideal_GROUP_DIFFERENCES434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ) (hnorm : ∀ g, ∑ p, mu g p = 1)
    (g : G) (S T : Finset (Fin M)) (hd : Disjoint S T)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    (fun y => sourceOriginalUnfilteredIdealGroup434 BP mu g S T f (fun h i => y ⟨h,i⟩)) =
    sourceOriginalUnfilteredIdealDifferenceList434
      (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ))
      (S.image (sourceOriginalUnfilteredIdealGroupEmbedding434 M g)).toList
      (sourceOriginalUnfilteredIdealResample434
        (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ))
        (T.image (sourceOriginalUnfilteredIdealGroupEmbedding434 M g))
        (fun y => f (fun h i => y ⟨h,i⟩))) := by
  rw [source_original_unfiltered_ideal_difference_image434 _ _
    (fun z => by exact_mod_cast hnorm z.1)]
  funext y
  have h := source_original_unfiltered_ideal_GROUP_ALTERNATING434 BP M mu hnorm
    g S T hd f (fun h i => y ⟨h,i⟩)
  exact h.symm

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealGroupLists -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalUnfilteredIdealProbeList434
    {G : Type} [DecidableEq G] (M : ℕ) (probes : G → Finset (Fin M)) :
    List G → List (Σ _g : G, Fin M)
  | [] => []
  | g::gs => ((probes g).image (sourceOriginalUnfilteredIdealGroupEmbedding434 M g)).toList ++
      sourceOriginalUnfilteredIdealProbeList434 M probes gs

def sourceOriginalUnfilteredIdealTailSet434
    {G : Type} [DecidableEq G] (M : ℕ) (tails : G → Finset (Fin M)) :
    List G → Finset (Σ _g : G, Fin M)
  | [] => ∅
  | g::gs => (tails g).image (sourceOriginalUnfilteredIdealGroupEmbedding434 M g) ∪
      sourceOriginalUnfilteredIdealTailSet434 M tails gs

theorem source_original_unfiltered_ideal_group_image_mem434
    {G : Type} [DecidableEq G] (M : ℕ) (g h : G)
    (S : Finset (Fin M)) (i : Fin M) :
    (⟨h,i⟩ : Σ _g : G, Fin M) ∈
      S.image (sourceOriginalUnfilteredIdealGroupEmbedding434 M g) ↔ h=g ∧ i∈S := by
  constructor
  · intro hz
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hz
    have hg : g=h := congrArg Sigma.fst he
    have hi : j=i := congrArg (fun z : Σ _g : G, Fin M => z.2) he
    exact ⟨hg.symm, hi ▸ hj⟩
  · rintro ⟨rfl,hi⟩
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩

theorem source_original_unfiltered_ideal_probe_list_mem434
    {G : Type} [DecidableEq G] (M : ℕ) (probes : G → Finset (Fin M))
    (gs : List G) (z : Σ _g : G, Fin M) :
    z ∈ sourceOriginalUnfilteredIdealProbeList434 M probes gs ↔
      z.1 ∈ gs ∧ z.2 ∈ probes z.1 := by
  induction gs with
  | nil => simp [sourceOriginalUnfilteredIdealProbeList434]
  | cons g gs ih =>
    rcases z with ⟨h,i⟩
    simp only [sourceOriginalUnfilteredIdealProbeList434, List.mem_append,
      Finset.mem_toList, source_original_unfiltered_ideal_group_image_mem434,
      ih, List.mem_cons]
    constructor
    · rintro (⟨rfl,hi⟩ | ⟨hh,hi⟩)
      · exact ⟨Or.inl rfl,hi⟩
      · exact ⟨Or.inr hh,hi⟩
    · rintro ⟨hh,hi⟩
      rcases hh with rfl | hh
      · exact Or.inl ⟨rfl,hi⟩
      · exact Or.inr ⟨hh,hi⟩

theorem source_original_unfiltered_ideal_probe_list_nodup434
    {G : Type} [DecidableEq G] (M : ℕ) (probes : G → Finset (Fin M))
    (gs : List G) (hgs : gs.Nodup) :
    (sourceOriginalUnfilteredIdealProbeList434 M probes gs).Nodup := by
  induction gs with
  | nil => simp [sourceOriginalUnfilteredIdealProbeList434]
  | cons g gs ih =>
    obtain ⟨hg,hgs⟩ := List.nodup_cons.mp hgs
    rw [sourceOriginalUnfilteredIdealProbeList434, List.nodup_append]
    refine ⟨Finset.nodup_toList _, ih hgs, ?_⟩
    intro z hz v hv he
    subst v
    have hzg := hv
    rcases z with ⟨h,i⟩
    have he := (source_original_unfiltered_ideal_group_image_mem434 M g h (probes g) i).mp
      (Finset.mem_toList.mp hz)
    have ht := (source_original_unfiltered_ideal_probe_list_mem434 M probes gs ⟨h,i⟩).mp hzg
    exact hg (he.1 ▸ ht.1)

/-- Iterated group survivors are exactly the global product of probe
differences and the means of the tails in those groups. -/
theorem source_original_unfiltered_ideal_GROUPS_DIFFERENCES434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ) (hnorm : ∀ g, ∑ p, mu g p = 1)
    (probes tails : G → Finset (Fin M)) (hd : ∀ g, Disjoint (probes g) (tails g))
    (gs : List G) (f : SourceOriginalJointBigState434 BP M → ℂ) :
    (fun y => sourceOriginalUnfilteredIdealGroups434 BP mu probes tails gs f (fun h i => y ⟨h,i⟩)) =
    sourceOriginalUnfilteredIdealDifferenceList434
      (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ))
      (sourceOriginalUnfilteredIdealProbeList434 M probes gs)
      (sourceOriginalUnfilteredIdealResample434
        (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ))
        (sourceOriginalUnfilteredIdealTailSet434 M tails gs)
        (fun y => f (fun h i => y ⟨h,i⟩))) := by
  let B := fun z : Σ _g : G, Fin M => BP z.1
  let w := fun z (p : B z) => (mu z.1 p : ℂ)
  have hw : ∀ z, ∑ p, w z p = 1 := by
    intro z
    dsimp only [w, B]
    exact_mod_cast hnorm z.1
  induction gs generalizing f with
  | nil =>
    simp only [sourceOriginalUnfilteredIdealGroups434, sourceOriginalUnfilteredIdealProbeList434,
      sourceOriginalUnfilteredIdealTailSet434, sourceOriginalUnfilteredIdealDifferenceList434,
      source_original_unfiltered_ideal_resample_empty434]
  | cons g gs ih =>
    change (fun y : (z : Σ _g : G, Fin M) → BP z.1 => sourceOriginalUnfilteredIdealGroups434 BP mu probes tails gs
      (sourceOriginalUnfilteredIdealGroup434 BP mu g (probes g) (tails g) f)
      (fun h i => y ⟨h,i⟩)) = _
    rw [ih, source_original_unfiltered_ideal_GROUP_DIFFERENCES434 BP M mu hnorm g
      (probes g) (tails g) (hd g)]
    rw [← source_original_unfiltered_ideal_difference_mean_commute434 B w hw
      _ (Finset.nodup_toList _) (sourceOriginalUnfilteredIdealTailSet434 M tails gs)]
    rw [source_original_unfiltered_ideal_resample_union434 B w hw,
      ← source_original_unfiltered_ideal_difference_append434]
    congr 2
    exact Finset.union_comm _ _

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealFullTailGain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_unfiltered_ideal_flat_energy434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    (∑ y : (z : Σ _g : G, Fin M) → BP z.1,
      (∏ z : Σ _g : G, Fin M, mu z.1 (y z)) * ‖f (fun g i => y ⟨g,i⟩)‖^2) =
    sourceOriginalJointBigEnergy434 BP mu f := by
  unfold sourceOriginalJointBigEnergy434
  apply Fintype.sum_equiv (sourceOriginalUnfilteredIdealFlatEquiv434 BP M).symm
  intro y
  rw [Complex.normSq_eq_norm_sq]
  congr 1
  rw [Fintype.prod_sigma]
  rfl

/-- All tail averages are applied AFTER the group survivor product.
Repeated means are idempotent, so same-group symmetry is never assumed
after a tail average. -/
theorem source_original_unfiltered_ideal_ALL_TAILS_AFTER_GROUPS434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ) (hnorm : ∀ g, ∑ p, mu g p = 1)
    (probes tails : G → Finset (Fin M)) (hd : ∀ g, Disjoint (probes g) (tails g))
    (gs : List G) (hgs : gs.Nodup) (Tall : Finset (Σ _g : G, Fin M))
    (hsub : sourceOriginalUnfilteredIdealTailSet434 M tails gs ⊆ Tall)
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    sourceOriginalUnfilteredIdealResample434
      (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ)) Tall
      (fun y => sourceOriginalUnfilteredIdealGroups434 BP mu probes tails gs f
        (fun g i => y ⟨g,i⟩)) =
    sourceOriginalUnfilteredIdealDifferenceList434
      (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ))
      (sourceOriginalUnfilteredIdealProbeList434 M probes gs)
      (sourceOriginalUnfilteredIdealResample434
        (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ)) Tall
        (fun y => f (fun g i => y ⟨g,i⟩))) := by
  have hw : ∀ z : Σ _g : G, Fin M, ∑ p, (mu z.1 p : ℂ) = 1 := by
    intro z
    exact_mod_cast hnorm z.1
  rw [source_original_unfiltered_ideal_GROUPS_DIFFERENCES434 BP M mu hnorm probes tails hd gs]
  rw [← source_original_unfiltered_ideal_difference_mean_commute434 _ _ hw _
    (source_original_unfiltered_ideal_probe_list_nodup434 M probes gs hgs)]
  rw [source_original_unfiltered_ideal_resample_union434 _ _ hw,
    Finset.union_eq_left.mpr hsub]

/-- Quantitative gain for the actual simultaneous endpoint mean with ALL
original tail averages and the grouped physical probe differences. -/
theorem source_original_unfiltered_ideal_FULL_TAIL_LOG_GAIN434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g) (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    (M : ℕ) (probes tails : G → Finset (Fin M))
    (hd : ∀ g, Disjoint (probes g) (tails g))
    (gs : List G) (hgs : gs.Nodup) (m ell : ℕ)
    (hcard : ∀ g ∈ gs, (probes g).card = m ∧ (tails g).card = ell)
    (Tall : Finset (Σ _g : G, Fin M))
    (hsub : sourceOriginalUnfilteredIdealTailSet434 M tails gs ⊆ Tall)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hc : 0 ≤ c) (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcount : c*Real.log LL ≤ (gs.length:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (f : SourceOriginalJointBigState434 BP M → ℂ) :
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    (∑ y : (z : Σ _g : G, Fin M) → BP z.1,
      (∏ z : Σ _g : G, Fin M, mu z.1 (y z)) *
      ‖sourceOriginalUnfilteredIdealDifferenceList434
        (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ))
        (sourceOriginalUnfilteredIdealProbeList434 M probes gs)
        (sourceOriginalUnfilteredIdealResample434
          (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => (mu z.1 p : ℂ)) Tall
          (fun x => sourceOriginalUnfilteredIdealEndpointMean434 BP M f
            (fun g i => x ⟨g,i⟩))) y‖^2) ≤
    LL^(-A) * sourceOriginalJointBigEnergy434 BP mu f := by
  dsimp only
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  obtain ⟨hpos,hnorm⟩ := source_original_joint_harmonic_normalized434 BP prime V hV hEq
  rw [← source_original_unfiltered_ideal_ALL_TAILS_AFTER_GROUPS434 BP M mu hnorm
    probes tails hd gs hgs Tall hsub]
  calc
    _ ≤ ∑ y : (z : Σ _g : G, Fin M) → BP z.1,
        (∏ z : Σ _g : G, Fin M, mu z.1 (y z)) *
        ‖sourceOriginalUnfilteredIdealGroups434 BP mu probes tails gs
          (sourceOriginalUnfilteredIdealEndpointMean434 BP M f) (fun g i => y ⟨g,i⟩)‖^2 :=
      source_original_unfiltered_ideal_RESAMPLE_CONTRACT434
        (fun z : Σ _g : G, Fin M => BP z.1) (fun z p => mu z.1 p)
        (fun z p => hpos z.1 p) (fun z => hnorm z.1) Tall _
    _ = sourceOriginalJointBigEnergy434 BP mu
        (sourceOriginalUnfilteredIdealGroups434 BP mu probes tails gs
          (sourceOriginalUnfilteredIdealEndpointMean434 BP M f)) :=
      source_original_unfiltered_ideal_flat_energy434 BP M mu _
    _ ≤ _ := source_original_unfiltered_ideal_ACTUAL_MEAN_COORDINATE_LOG434
      BP prime V hV hEq probes tails hd gs hgs m ell hcard LL A c hLL hc hm hell
      hcount hbudget f

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealRawBilinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem source_original_unfiltered_ideal_flat_pair434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ)
    (F : SourceOriginalJointBigState434 BP M → ℂ)
    (H : ((z : Σ _g : G, Fin M) → BP z.1) → ℂ) :
    (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      H (fun z => s z.1 z.2)) =
    ∑ x, ((∏ z : Σ _g : G, Fin M, mu z.1 (x z) : ℝ) : ℂ) *
      star (F (fun g i => x ⟨g,i⟩)) * H x := by
  apply Fintype.sum_equiv (sourceOriginalUnfilteredIdealFlatEquiv434 BP M)
  intro s
  rw [Fintype.prod_sigma]
  rfl

/-- True asymmetric per-pattern bilinear identity, with arbitrary correlated
tests and the actual full joint phase. -/
theorem source_original_unfiltered_ideal_RAW_PATTERN_PAIR434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m) (hd : Disjoint nu.1 nu.2)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ) (hnorm : ∀ g, ∑ p, mu g p = 1)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let B := fun z : Σ _g : G, Fin (J+ell) => BP z.1
    let w := fun x : (z : Σ _g : G, Fin (J+ell)) → BP z.1 =>
      ∏ z : Σ _g : G, Fin (J+ell), mu z.1 (x z)
    let E := fun A : Finset (G × Fin m) =>
      sourceOriginalUnfilteredIdealResample434 B (fun z p => (mu z.1 p : ℂ))
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ A)
    (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      (∑ t, sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
        sourceOriginalB26CanonicalRawValue434 P J ell m hmJ nu dsmall s t
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta theta o k * H t)) =
    -((-1:ℂ)^nu.1.card * (-1:ℂ)^nu.2.card) *
      sourceOriginalUnfilteredIdealPair434 w
        (sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k)
        (E nu.1 (fun x => F (fun g i => x ⟨g,i⟩)))
        (E nu.2 (fun x => H (fun g i => x ⟨g,i⟩))) := by
  dsimp only
  simp_rw [source_original_unfiltered_ideal_LITERAL_RAW_SIGNED434 P J ell m hmJ nu hd mu hnorm]
  let c : ℂ := -((-1:ℂ)^nu.1.card * (-1:ℂ)^nu.2.card)
  let B := fun z : Σ _g : G, Fin (J+ell) => {p : ℕ // p ∈ P z.1}
  let w := fun z (p : B z) => (mu z.1 p : ℂ)
  let E := fun A : Finset (G × Fin m) =>
    sourceOriginalUnfilteredIdealResample434 B w
      (sourceOriginalUnfilteredIdealMask434 J ell m hmJ A)
  let Z := fun x => sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k x *
    E nu.2 (fun y => H (fun g i => y ⟨g,i⟩)) x
  change (∑ s, (sourceOriginalJointBigMass434 _ mu s : ℂ) * star (F s) *
    (c * E nu.1 Z (fun z => s z.1 z.2))) = c * _
  calc
    _ = c * (∑ s, (sourceOriginalJointBigMass434 _ mu s : ℂ) *
        star (F s) * E nu.1 Z (fun z => s z.1 z.2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = c * (∑ x, ((∏ z : Σ _g : G, Fin (J+ell), mu z.1 (x z) : ℝ) : ℂ) *
        star (F (fun g i => x ⟨g,i⟩)) * E nu.1 Z x) := by
      rw [source_original_unfiltered_ideal_flat_pair434]
    _ = _ := congrArg (fun z : ℂ => c*z)
      (source_original_unfiltered_ideal_pair_resample434 B (fun z p => mu z.1 p)
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ nu.1)
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ nu.2) _ _ _)

/-- Finite signed rectangle at the bilinear level; no phase commutation. -/
theorem source_original_unfiltered_ideal_PAIR_RECTANGLE434
    {X I : Type} [Fintype X] [DecidableEq I]
    (w : X → ℝ) (Phi : X → ℂ) (A B : Finset I)
    (F H : Finset I → X → ℂ) :
    sourceOriginalUnfilteredIdealPair434 w Phi (F ∅) (H ∅) -
      (∑ a ∈ A.powerset.filter Finset.Nonempty,
        ∑ b ∈ B.powerset.filter Finset.Nonempty,
          (-1:ℂ)^a.card * (-1:ℂ)^b.card *
            sourceOriginalUnfilteredIdealPair434 w Phi (F a) (H b)) =
    sourceOriginalUnfilteredIdealPair434 w Phi
      (fun x => ∑ a ∈ A.powerset, (-1:ℂ)^a.card * F a x) (H ∅) +
    sourceOriginalUnfilteredIdealPair434 w Phi (F ∅)
      (fun x => ∑ b ∈ B.powerset, (-1:ℂ)^b.card * H b x) -
    sourceOriginalUnfilteredIdealPair434 w Phi
      (fun x => ∑ a ∈ A.powerset, (-1:ℂ)^a.card * F a x)
      (fun x => ∑ b ∈ B.powerset, (-1:ℂ)^b.card * H b x) := by
  have h := source_original_unfiltered_ideal_rectangle434 A B
    (fun a b => (-1:ℂ)^a.card * (-1:ℂ)^b.card *
      sourceOriginalUnfilteredIdealPair434 w Phi (F a) (H b))
  simp only [Finset.card_empty, pow_zero, mul_one, one_mul] at h
  rw [source_original_unfiltered_ideal_pair_sum_left434,
    source_original_unfiltered_ideal_pair_sum_right434,
    source_original_unfiltered_ideal_pair_alternating434 w Phi A.powerset B.powerset F H] at h
  exact h

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealDivisorPair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 200000

/-- Literal arbitrary positive SMALL divisor and nonzero signed k reduce
to dsmall=k=1 at a rescaled arbitrary real frequency, with unit Mellin
factor. Thus comparison precision may legitimately use Ck=0. -/
theorem source_original_unfiltered_ideal_DIVISOR_PAIR_NORM434
    {G N : Type} [Fintype G] [DecidableEq G] [Fintype N]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) [∀ g p, NeZero (prime g p)]
    (J ell m : ℕ) (patterns : N → SourcePattern G J m)
    (mu : (g : G) → BP g → ℝ) (V : G → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (dsmall : ℕ) (hdsmall : 0 < dsmall)
    (zeta theta : ℝ) (o k : ℤ) (hk : k ≠ 0)
    (F H : ((g : G) → Fin (J+ell) → BP g) → ℂ) :
    ‖(∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      sourceOriginalB26FrozenBigBlock434 BP prime J ell m patterns mu V K
        dsmall zeta theta o k H s)‖ =
    ‖(∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      sourceOriginalB26FrozenBigBlock434 BP prime J ell m patterns mu V K
        1 zeta ((k:ℝ)*(dsmall:ℝ)*theta) o 1 H s)‖ := by
  have he :
      (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
        sourceOriginalB26FrozenBigBlock434 BP prime J ell m patterns mu V K
          dsmall zeta theta o k H s) =
      sourceOriginalB26SmallMellin434 dsmall zeta o *
        (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
          sourceOriginalB26FrozenBigBlock434 BP prime J ell m patterns mu V K
            1 zeta ((k:ℝ)*(dsmall:ℝ)*theta) o 1 H s) := by
    simp_rw [source_original_B26_FROZEN_BIG_DIVISOR_REDUCTION434
      BP prime J ell m patterns mu V K dsmall hdsmall zeta theta o k hk]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [he, norm_mul, source_original_B26_SMALL_MELLIN_norm_one434, one_mul]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealRawNone -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem source_original_unfiltered_ideal_empty_pattern434
    {G : Type} [DecidableEq G] (J m : ℕ) (hmJ : m ≤ J) :
    sourceOriginalProbeMemoryPattern434 J m hmJ ((∅,∅) : SourceOriginalProbePattern434 G m) =
      sourceOriginalB26RawNonePattern434 (G := G) J m PUnit.unit := by
  unfold sourceOriginalProbeMemoryPattern434 sourceOriginalB26RawNonePattern434
  congr 1
  funext g
  simp [sourceOriginalProbeFreedSlots434]

theorem source_original_unfiltered_ideal_empty_raw_value434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    sourceOriginalB26CanonicalRawValue434 P J ell m hmJ (∅,∅)
      dsmall s t sigma tau zeta theta o k =
    -originalEdgeScalar 1 zeta theta
      (dsmall * ∏ g : G, ∏ i : Fin J, (s g (sigma g (i.castAdd ell))).val) o k := by
  have hh : sourceOriginalUnfilteredIdealHybrid434 (fun g => {p : ℕ // p ∈ P g})
      J ell m hmJ (∅,∅) (fun g i => s g (sigma g i))
        (fun g i => t g (tau g i)) = (fun g i => s g (sigma g i)) := by
    funext g i
    apply if_neg
    rintro ⟨j,hj,_⟩
    exact Finset.notMem_empty (g,j) hj
  have hr := source_original_unfiltered_ideal_raw_value434 P J ell m hmJ
    (∅,∅) (by simp) dsmall s t sigma tau zeta theta o k
  rw [hh] at hr
  simp only [Finset.card_empty, zero_add, pow_zero] at hr
  have hs := source_original_unfiltered_ideal_raw_sign434 0
    (dsmall * ∏ g : G, ∏ i : Fin J, (s g (sigma g (i.castAdd ell))).val) zeta theta o k
  simp only [pow_zero, neg_one_mul] at hs
  exact hr.trans hs

/-- Exact endpoint covariance of the actual signed hybrid RAW value. -/
theorem source_original_unfiltered_ideal_raw_permuted434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (dsmall : ℕ)
    (s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ) :
    sourceOriginalB26CanonicalRawValue434 P J ell m hmJ ν dsmall s t sigma tau zeta theta o k =
    sourceOriginalB26CanonicalRawValue434 P J ell m hmJ ν dsmall
      (fun g i => s g (sigma g i)) (fun g i => t g (tau g i))
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta theta o k := by
  simp only [sourceOriginalB26CanonicalRawValue434,
    sourceOriginalB26CanonicalSharedDivisor434, Equiv.refl_apply]

end Green64Analytic.CorrelationSquare

end

end

