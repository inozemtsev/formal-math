module

public import Green64.Library.Weights.Part091
public import Green64.Library.Weights.Part054
public import Green64.Library.Weights.B26AuxBanBlockIdentity
public import Green64.Library.Weights.Part057
public import Green64.Library.Analysis.Estimates.Part013
public import Green64.Library.Weights.Part078
public import Green64.Library.Correlation.Part008
public import Green64.Library.Weights.Part043
public import Green64.Library.Weights.Part090

@[expose] public section

/-!
# Weights / Part092

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredIdealSlots -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

def sourceOriginalUnfilteredIdealProbeSlots434 (J ell m : ℕ) (hmJ : m ≤ J) :
    Finset (Fin (J+ell)) :=
  Finset.univ.image (fun j : Fin m => (j.castLE hmJ).castAdd ell)

def sourceOriginalUnfilteredIdealTailSlots434 (J ell : ℕ) :
    Finset (Fin (J+ell)) :=
  Finset.univ.filter (fun i => J ≤ i.val)

theorem source_original_unfiltered_ideal_slots_disjoint434
    (J ell m : ℕ) (hmJ : m ≤ J) :
    Disjoint (sourceOriginalUnfilteredIdealProbeSlots434 J ell m hmJ)
      (sourceOriginalUnfilteredIdealTailSlots434 J ell) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
  have h := (Finset.mem_filter.mp ht).2
  have hj' := j.isLt
  change J ≤ j.val at h
  omega

theorem source_original_unfiltered_ideal_probe_slots_card434
    (J ell m : ℕ) (hmJ : m ≤ J) :
    (sourceOriginalUnfilteredIdealProbeSlots434 J ell m hmJ).card = m := by
  unfold sourceOriginalUnfilteredIdealProbeSlots434
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j he
    exact Fin.ext (congrArg (fun z : Fin (J+ell) => z.val) he)

theorem source_original_unfiltered_ideal_tail_slots_image434 (J ell : ℕ) :
    sourceOriginalUnfilteredIdealTailSlots434 J ell =
      Finset.univ.image (fun j : Fin ell => j.natAdd J) := by
  ext i
  constructor
  · intro hi
    have h := (Finset.mem_filter.mp hi).2
    have hii := i.isLt
    let j : Fin ell := ⟨i.val-J, by omega⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change J+(i.val-J) = i.val
    omega
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    simp [sourceOriginalUnfilteredIdealTailSlots434]

theorem source_original_unfiltered_ideal_tail_slots_card434 (J ell : ℕ) :
    (sourceOriginalUnfilteredIdealTailSlots434 J ell).card = ell := by
  rw [source_original_unfiltered_ideal_tail_slots_image434,
    Finset.card_image_of_injective]
  · simp
  · intro i j he
    apply Fin.ext
    have h := congrArg (fun z : Fin (J+ell) => z.val) he
    change J+i.val = J+j.val at h
    omega

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealActualMasks -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem source_original_unfiltered_ideal_original_probe_list434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (block : Finset G) :
    (sourceOriginalUnfilteredIdealProbeList434 (J+ell)
      (fun _ : G => sourceOriginalUnfilteredIdealProbeSlots434 J ell m hmJ) block.toList).toFinset =
    (sourceOriginalProbeBlock434 block m).image
      (sourceOriginalUnfilteredIdealProbeEmbedding434 J ell m hmJ) := by
  ext z
  rcases z with ⟨g,i⟩
  rw [List.mem_toFinset, source_original_unfiltered_ideal_probe_list_mem434]
  simp only [Finset.mem_toList]
  constructor
  · rintro ⟨hg,hi⟩
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hi
    refine Finset.mem_image.mpr ⟨(g,j), Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩, ?_⟩
    change (⟨g,(j.castLE hmJ).castAdd ell⟩ : Σ _g : G, Fin (J+ell)) = ⟨g,i⟩
    rw [he]
  · intro hz
    obtain ⟨⟨h,j⟩,hj,he⟩ := Finset.mem_image.mp hz
    have hg : h = g := congrArg Sigma.fst he
    subst h
    have hi : (j.castLE hmJ).castAdd ell = i :=
      congrArg (fun z : Σ _g : G, Fin (J+ell) => z.2) he
    exact ⟨(Finset.mem_product.mp hj).1,
      Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hi⟩⟩

theorem source_original_unfiltered_ideal_original_tail_subset434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (gs : List G) :
    sourceOriginalUnfilteredIdealTailSet434 (J+ell)
      (fun _ : G => sourceOriginalUnfilteredIdealTailSlots434 J ell) gs ⊆
    sourceOriginalUnfilteredIdealMask434 J ell m hmJ (∅ : Finset (G × Fin m)) := by
  induction gs with
  | nil => simp [sourceOriginalUnfilteredIdealTailSet434]
  | cons g gs ih =>
    intro z hz
    rcases Finset.mem_union.mp hz with hg | ht
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hg
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Or.inl ?_⟩
      exact (Finset.mem_filter.mp hi).2
    · exact ih ht

/-- Literal signed subset operator = the grouped original coordinate
differences after the all-group tail mean. -/
theorem source_original_unfiltered_ideal_ACTUAL_MASK_LIST434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (block : Finset G)
    (mu : (g : G) → BP g → ℂ) (hnorm : ∀ g, ∑ p, mu g p = 1)
    (f : ((z : Σ _g : G, Fin (J+ell)) → BP z.1) → ℂ) :
    (fun x => ∑ A ∈ (sourceOriginalProbeBlock434 block m).powerset,
      (-1:ℂ)^A.card *
        sourceOriginalUnfilteredIdealResample434
          (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => mu z.1 p)
          (sourceOriginalUnfilteredIdealMask434 J ell m hmJ A) f x) =
    sourceOriginalUnfilteredIdealDifferenceList434
      (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => mu z.1 p)
      (sourceOriginalUnfilteredIdealProbeList434 (J+ell)
        (fun _ : G => sourceOriginalUnfilteredIdealProbeSlots434 J ell m hmJ) block.toList)
      (sourceOriginalUnfilteredIdealResample434
        (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => mu z.1 p)
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ (∅ : Finset (G × Fin m))) f) := by
  funext x
  rw [source_original_unfiltered_ideal_ACTUAL_PROBE_EXPANSION434 BP J ell m hmJ block mu hnorm]
  rw [source_original_unfiltered_ideal_difference_expansion434 _ _ (fun z => hnorm z.1)
    _ (Finset.nodup_toList _)]
  rw [source_original_unfiltered_ideal_difference_expansion434 _ _ (fun z => hnorm z.1)
    _ (source_original_unfiltered_ideal_probe_list_nodup434 _ _ _ (Finset.nodup_toList _))]
  rw [Finset.toList_toFinset, source_original_unfiltered_ideal_original_probe_list434]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealActualBlockGain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The literal full alternating subset operator from the original block.
It includes all physical tail slots and retains numerical multiplicities. -/
def sourceOriginalUnfilteredIdealBlock434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (block : Finset G)
    (mu : (g : G) → BP g → ℝ)
    (f : ((z : Σ _g : G, Fin (J+ell)) → BP z.1) → ℂ)
    (x : (z : Σ _g : G, Fin (J+ell)) → BP z.1) : ℂ :=
  ∑ A ∈ (sourceOriginalProbeBlock434 block m).powerset,
    (-1:ℂ)^A.card *
      sourceOriginalUnfilteredIdealResample434
        (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => (mu z.1 p : ℂ))
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ A) f x

/-- Negative log-power for the ACTUAL original signed subset operator,
after the actual independent endpoint mean and every original tail average.
No symmetry, projection equality, or family-saving estimate is postulated. -/
theorem source_original_unfiltered_ideal_ACTUAL_BLOCK_LOG_GAIN434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (prime : (g : G) → BP g → ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g) (hEq : ∀ g, V g = ∑ p : BP g, 1/(prime g p:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J) (block : Finset G)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hc : 0 ≤ c) (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcount : c*Real.log LL ≤ (block.card:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (f : SourceOriginalJointBigState434 BP (J+ell) → ℂ) :
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    (∑ y : (z : Σ _g : G, Fin (J+ell)) → BP z.1,
      (∏ z : Σ _g : G, Fin (J+ell), mu z.1 (y z)) *
      ‖sourceOriginalUnfilteredIdealBlock434 BP J ell m hmJ block mu
        (fun x => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) f
          (fun g i => x ⟨g,i⟩)) y‖^2) ≤
    LL^(-A) * sourceOriginalJointBigEnergy434 BP mu f := by
  dsimp only
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  obtain ⟨hpos,hnorm⟩ := source_original_joint_harmonic_normalized434 BP prime V hV hEq
  have hw : ∀ g, ∑ p, (mu g p : ℂ) = 1 := by
    intro g
    exact_mod_cast hnorm g
  have he := source_original_unfiltered_ideal_ACTUAL_MASK_LIST434 BP J ell m hmJ block
    (fun g p => (mu g p : ℂ)) hw
    (fun x => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) f (fun g i => x ⟨g,i⟩))
  have hep (y : (z : Σ _g : G, Fin (J+ell)) → BP z.1) := congrFun he y
  change (∑ y, (∏ z : Σ _g : G, Fin (J+ell), mu z.1 (y z)) *
    ‖sourceOriginalUnfilteredIdealBlock434 BP J ell m hmJ block mu _ y‖^2) ≤ _
  unfold sourceOriginalUnfilteredIdealBlock434
  simp_rw [hep]
  apply source_original_unfiltered_ideal_FULL_TAIL_LOG_GAIN434 BP prime V hV hEq (J+ell)
    (fun _ => sourceOriginalUnfilteredIdealProbeSlots434 J ell m hmJ)
    (fun _ => sourceOriginalUnfilteredIdealTailSlots434 J ell)
    (fun _ => source_original_unfiltered_ideal_slots_disjoint434 J ell m hmJ)
    block.toList (Finset.nodup_toList _) m ell
    (fun g hg => ⟨source_original_unfiltered_ideal_probe_slots_card434 J ell m hmJ,
      source_original_unfiltered_ideal_tail_slots_card434 J ell⟩)
    _ (source_original_unfiltered_ideal_original_tail_subset434 J ell m hmJ block.toList)
    LL A c hLL hc hm hell
    (by simpa using hcount) hbudget f

/-- The unprojected RAW endpoint test, with the true endpoint mean and
the complete tail mean, is contractive in the same density. -/
theorem source_original_unfiltered_ideal_ACTUAL_TAIL_MEAN_CONTRACT434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p, 0 ≤ mu g p)
    (hnorm : ∀ g, ∑ p, mu g p = 1)
    (f : SourceOriginalJointBigState434 BP (J+ell) → ℂ) :
    (∑ y : (z : Σ _g : G, Fin (J+ell)) → BP z.1,
      (∏ z : Σ _g : G, Fin (J+ell), mu z.1 (y z)) *
      ‖sourceOriginalUnfilteredIdealResample434
        (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => (mu z.1 p : ℂ))
        (sourceOriginalUnfilteredIdealMask434 J ell m hmJ (∅ : Finset (G × Fin m)))
        (fun x => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) f
          (fun g i => x ⟨g,i⟩)) y‖^2) ≤
    sourceOriginalJointBigEnergy434 BP mu f := by
  calc
    _ ≤ ∑ y : (z : Σ _g : G, Fin (J+ell)) → BP z.1,
        (∏ z : Σ _g : G, Fin (J+ell), mu z.1 (y z)) *
        ‖sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) f (fun g i => y ⟨g,i⟩)‖^2 :=
      source_original_unfiltered_ideal_RESAMPLE_CONTRACT434
        (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => mu z.1 p)
        (fun z p => hmu z.1 p) (fun z => hnorm z.1) _ _
    _ = sourceOriginalJointBigEnergy434 BP mu
        (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) f) :=
      source_original_unfiltered_ideal_flat_energy434 BP (J+ell) mu _
    _ ≤ _ := source_original_unfiltered_ideal_endpoint_mean_contract434 BP (J+ell) mu hmu f

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealResidualGain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The exact three residual pairings; both endpoint means and every original
tail average are retained. Phi is multiplied between the endpoint tests. -/
def sourceOriginalUnfilteredIdealResidual434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (blockA blockB : Finset G)
    (mu : (g : G) → BP g → ℝ)
    (Phi : ((z : Σ _g : G, Fin (J+ell)) → BP z.1) → ℂ)
    (F H : SourceOriginalJointBigState434 BP (J+ell) → ℂ) : ℂ :=
  let B := fun z : Σ _g : G, Fin (J+ell) => BP z.1
  let w := fun x : (z : Σ _g : G, Fin (J+ell)) → BP z.1 =>
    ∏ z : Σ _g : G, Fin (J+ell), mu z.1 (x z)
  let f := fun x => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F
    (fun g i => x ⟨g,i⟩)
  let h := fun x => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H
    (fun g i => x ⟨g,i⟩)
  let U := sourceOriginalUnfilteredIdealResample434 B (fun z p => (mu z.1 p : ℂ))
    (sourceOriginalUnfilteredIdealMask434 J ell m hmJ (∅ : Finset (G × Fin m)))
  let PA := sourceOriginalUnfilteredIdealBlock434 BP J ell m hmJ blockA mu
  let PB := sourceOriginalUnfilteredIdealBlock434 BP J ell m hmJ blockB mu
  sourceOriginalUnfilteredIdealPair434 w Phi (PA f) (U h) +
    sourceOriginalUnfilteredIdealPair434 w Phi (U f) (PB h) -
    sourceOriginalUnfilteredIdealPair434 w Phi (PA f) (PB h)

/-- Quantitative original-harmonic residual bound. All gain premises are
original structural counts, normalization, and a fixed numerical budget;
there is no assumed norm estimate or assumed family cancellation. -/
theorem source_original_unfiltered_ideal_RESIDUAL_LOG_GAIN434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g)
    (hEq : ∀ g, V g = ∑ p : {p : ℕ // p ∈ P g}, 1/(p.val:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J) (blockA blockB : Finset G)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcountA : c*Real.log LL ≤ (blockA.card:ℝ))
    (hcountB : c*Real.log LL ≤ (blockB.card:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (F H : SourceOriginalJointBigState434 (fun g => {p : ℕ // p ∈ P g}) (J+ell) → ℂ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) V
    ‖sourceOriginalUnfilteredIdealResidual434 BP J ell m hmJ blockA blockB mu
      (sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k) F H‖^2 ≤
      9*LL^(-A)*sourceOriginalJointBigEnergy434 BP mu F*
        sourceOriginalJointBigEnergy434 BP mu H := by
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let X := (z : Σ _g : G, Fin (J+ell)) → BP z.1
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) V
  let w := fun x : X => ∏ z : Σ _g : G, Fin (J+ell), mu z.1 (x z)
  let Phi := sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k
  let f := fun x : X => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F
    (fun g i => x ⟨g,i⟩)
  let h := fun x : X => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H
    (fun g i => x ⟨g,i⟩)
  let U := sourceOriginalUnfilteredIdealResample434
    (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => (mu z.1 p : ℂ))
    (sourceOriginalUnfilteredIdealMask434 J ell m hmJ (∅ : Finset (G × Fin m)))
  let a := sourceOriginalUnfilteredIdealBlock434 BP J ell m hmJ blockA mu f
  let b := sourceOriginalUnfilteredIdealBlock434 BP J ell m hmJ blockB mu h
  let EF := sourceOriginalJointBigEnergy434 BP mu F
  let EH := sourceOriginalJointBigEnergy434 BP mu H
  let delta := LL^(-A)
  obtain ⟨hmu,hnorm⟩ := source_original_joint_harmonic_normalized434
    BP (fun _ p => p.val) V hV hEq
  have hw (x : X) : 0 ≤ w x := Finset.prod_nonneg (fun z _ => hmu z.1 (x z))
  have hPhi (x : X) : ‖Phi x‖=1 := by
    exact (source_original_edge_scalar_norm434 1 zeta theta _ o k ho).trans norm_one
  have hEF : 0 ≤ EF := source_original_joint_big_energy_nonneg434 BP mu hmu F
  have hEH : 0 ≤ EH := source_original_joint_big_energy_nonneg434 BP mu hmu H
  have hd0 : 0 ≤ delta := Real.rpow_nonneg (zero_le_one.trans hLL) _
  have hd1 : delta ≤ 1 := by
    calc
      _ ≤ LL^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hLL (neg_nonpos.mpr hA)
      _ = 1 := Real.rpow_zero _
  have ha : (∑ x : X, w x * ‖a x‖^2) ≤ delta*EF :=
    source_original_unfiltered_ideal_ACTUAL_BLOCK_LOG_GAIN434 BP (fun _ p => p.val)
      V hV hEq J ell m hmJ blockA LL A c hLL hc hm hell hcountA hbudget F
  have hb : (∑ x : X, w x * ‖b x‖^2) ≤ delta*EH :=
    source_original_unfiltered_ideal_ACTUAL_BLOCK_LOG_GAIN434 BP (fun _ p => p.val)
      V hV hEq J ell m hmJ blockB LL A c hLL hc hm hell hcountB hbudget H
  have hf : (∑ x : X, w x * ‖U f x‖^2) ≤ EF :=
    source_original_unfiltered_ideal_ACTUAL_TAIL_MEAN_CONTRACT434 BP J ell m hmJ
      mu hmu hnorm F
  have hh : (∑ x : X, w x * ‖U h x‖^2) ≤ EH :=
    source_original_unfiltered_ideal_ACTUAL_TAIL_MEAN_CONTRACT434 BP J ell m hmJ
      mu hmu hnorm H
  have hnn (v : X → ℂ) : 0 ≤ ∑ x, w x * ‖v x‖^2 :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
  have h1 : ‖sourceOriginalUnfilteredIdealPair434 w Phi a (U h)‖^2 ≤ delta*EF*EH :=
    (source_original_unfiltered_ideal_pair_CS434 w hw Phi hPhi a (U h)).trans
      (mul_le_mul ha hh (hnn _) (mul_nonneg hd0 hEF))
  have h2 : ‖sourceOriginalUnfilteredIdealPair434 w Phi (U f) b‖^2 ≤ delta*EF*EH := by
    calc
      _ ≤ (∑ x, w x * ‖U f x‖^2) * (∑ x, w x * ‖b x‖^2) :=
        source_original_unfiltered_ideal_pair_CS434 w hw Phi hPhi (U f) b
      _ ≤ EF*(delta*EH) := mul_le_mul hf hb (hnn _) hEF
      _ = delta*EF*EH := by ring
  have h3 : ‖sourceOriginalUnfilteredIdealPair434 w Phi a b‖^2 ≤ delta*EF*EH := by
    calc
      _ ≤ (∑ x, w x * ‖a x‖^2) * (∑ x, w x * ‖b x‖^2) :=
        source_original_unfiltered_ideal_pair_CS434 w hw Phi hPhi a b
      _ ≤ (delta*EF)*(delta*EH) := mul_le_mul ha hb (hnn _) (mul_nonneg hd0 hEF)
      _ = delta*(delta*EF*EH) := by ring
      _ ≤ 1*(delta*EF*EH) :=
        mul_le_mul_of_nonneg_right hd1 (mul_nonneg (mul_nonneg hd0 hEF) hEH)
      _ = delta*EF*EH := one_mul _
  have ht := source_original_unfiltered_ideal_three_square434
    (sourceOriginalUnfilteredIdealPair434 w Phi a (U h))
    (sourceOriginalUnfilteredIdealPair434 w Phi (U f) b)
    (sourceOriginalUnfilteredIdealPair434 w Phi a b)
  change ‖sourceOriginalUnfilteredIdealPair434 w Phi a (U h) +
    sourceOriginalUnfilteredIdealPair434 w Phi (U f) b -
    sourceOriginalUnfilteredIdealPair434 w Phi a b‖^2 ≤ 9*delta*EF*EH
  nlinarith only [ht,h1,h2,h3]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealRawFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

def sourceOriginalUnfilteredIdealRawPatternForm434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (nu : SourceOriginalProbePattern434 G m)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ) : ℂ :=
  ∑ s, (sourceOriginalJointBigMass434 _ mu s : ℂ) * star (F s) *
    (∑ t, sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
      sourceOriginalB26CanonicalRawValue434 P J ell m hmJ nu dsmall s t
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta theta o k * H t)

/-- The true unaveraged hybrid-RAW family, with the negative of the empty
signed comparison value supplying the positive RAW term. The literal
Option-none adapter is proved separately, before any frozen-block claim. -/
def sourceOriginalUnfilteredIdealRawForm434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (blockA blockB : Finset G)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ) : ℂ :=
  -sourceOriginalUnfilteredIdealRawPatternForm434 P J ell m hmJ mu
    (∅,∅) dsmall zeta theta o k F H +
  ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
    sourceOriginalUnfilteredIdealRawPatternForm434 P J ell m hmJ mu
      nu dsmall zeta theta o k F H

/-- Exact full signed original family equals the three residual pairings.
The true independent endpoint means are on the two tests, and the fully
coupled head phase is never commuted across a coordinate mean. -/
theorem source_original_unfiltered_ideal_RAW_FORM_RESIDUAL434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ) (hnorm : ∀ g, ∑ p, mu g p = 1)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ) :
    sourceOriginalUnfilteredIdealRawForm434 P J ell m hmJ blockA blockB mu
      dsmall zeta theta o k
      (sourceOriginalUnfilteredIdealEndpointMean434 _ (J+ell) F)
      (sourceOriginalUnfilteredIdealEndpointMean434 _ (J+ell) H) =
    sourceOriginalUnfilteredIdealResidual434 (fun g => {p : ℕ // p ∈ P g})
      J ell m hmJ blockA blockB mu
      (sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k) F H := by
  let BP := fun g => {p : ℕ // p ∈ P g}
  let X := (z : Σ _g : G, Fin (J+ell)) → BP z.1
  let w := fun x : X => ∏ z : Σ _g : G, Fin (J+ell), mu z.1 (x z)
  let Phi := sourceOriginalUnfilteredIdealHeadPhase434 P J ell 1 dsmall zeta theta o k
  let E := fun A : Finset (G × Fin m) =>
    sourceOriginalUnfilteredIdealResample434
      (fun z : Σ _g : G, Fin (J+ell) => BP z.1) (fun z p => (mu z.1 p : ℂ))
      (sourceOriginalUnfilteredIdealMask434 J ell m hmJ A)
  let f := fun x : X => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F
    (fun g i => x ⟨g,i⟩)
  let h := fun x : X => sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H
    (fun g i => x ⟨g,i⟩)
  let R := fun a b : Finset (G × Fin m) =>
    sourceOriginalUnfilteredIdealPair434 w Phi (E a f) (E b h)
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  have hp (nu : SourceOriginalProbePattern434 G m) (hd : Disjoint nu.1 nu.2) :
      sourceOriginalUnfilteredIdealRawPatternForm434 P J ell m hmJ mu
        nu dsmall zeta theta o k
        (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F)
        (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H) =
      -((-1:ℂ)^nu.1.card * (-1:ℂ)^nu.2.card) * R nu.1 nu.2 :=
    source_original_unfiltered_ideal_RAW_PATTERN_PAIR434 P J ell m hmJ nu hd mu hnorm
      dsmall zeta theta o k _ _
  have hp0 := hp (∅,∅) (by simp)
  simp only [Finset.card_empty, pow_zero, one_mul, neg_one_mul] at hp0
  have hsum :
      (∑ nu ∈ family, sourceOriginalUnfilteredIdealRawPatternForm434 P J ell m hmJ mu
        nu dsmall zeta theta o k
        (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F)
        (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H)) =
      -(∑ a ∈ (sourceOriginalProbeBlock434 blockA m).powerset.filter Finset.Nonempty,
        ∑ b ∈ (sourceOriginalProbeBlock434 blockB m).powerset.filter Finset.Nonempty,
          (-1:ℂ)^a.card * (-1:ℂ)^b.card * R a b) := by
    rw [← Finset.sum_product', ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro nu hnu
    rw [hp nu (source_original_probe_memory_actual_pattern_disjoint434
      blockA blockB hBlocks m nu hnu)]
    ring
  unfold sourceOriginalUnfilteredIdealRawForm434
  rw [hp0, hsum, neg_neg, ← sub_eq_add_neg]
  exact source_original_unfiltered_ideal_PAIR_RECTANGLE434 w Phi
    (sourceOriginalProbeBlock434 blockA m) (sourceOriginalProbeBlock434 blockB m)
    (fun a => E a f) (fun b => E b h)

/-- Quantitative signed RAW-none-plus-comparison-replacement gain on the
actual original harmonic alphabets, before adding the two analytic errors. -/
theorem source_original_unfiltered_ideal_RAW_FORM_LOG_GAIN434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, 0 < V g)
    (hEq : ∀ g, V g = ∑ p : {p : ℕ // p ∈ P g}, 1/(p.val:ℝ))
    (J ell m : ℕ) (hmJ : m ≤ J) (blockA blockB : Finset G)
    (hBlocks : Disjoint blockA blockB)
    (LL A c : ℝ) (hLL : 1 ≤ LL) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hcountA : c*Real.log LL ≤ (blockA.card:ℝ))
    (hcountB : c*Real.log LL ≤ (blockB.card:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) V
    ‖sourceOriginalUnfilteredIdealRawForm434 P J ell m hmJ blockA blockB mu
      dsmall zeta theta o k
      (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F)
      (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H)‖^2 ≤
      9*LL^(-A)*sourceOriginalJointBigEnergy434 BP mu F*
        sourceOriginalJointBigEnergy434 BP mu H := by
  dsimp only
  obtain ⟨hmu,hnorm⟩ := source_original_joint_harmonic_normalized434
    (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) V hV hEq
  rw [source_original_unfiltered_ideal_RAW_FORM_RESIDUAL434 P J ell m hmJ
    blockA blockB hBlocks _ hnorm]
  exact source_original_unfiltered_ideal_RESIDUAL_LOG_GAIN434 P V hV hEq
    J ell m hmJ blockA blockB LL A c hLL hA hc hm hell hcountA hcountB hbudget
    dsmall zeta theta o k ho F H

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealEndpointBlock -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem source_original_unfiltered_ideal_pair_mass434
    {G : Type} [Fintype G] [DecidableEq G] (M : ℕ) :
    (bigEndpointPairMass (BG := G) M : ℂ) =
      (Fintype.card (BigGroupPerm (BG := G) M) : ℂ)⁻¹ *
      (Fintype.card (BigGroupPerm (BG := G) M) : ℂ)⁻¹ := by
  have hn : (Fintype.card (BigGroupPerm (BG := G) M) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := BigGroupPerm (BG := G) M)
  have hr : bigEndpointPairMass (BG := G) M *
      (Fintype.card (BigGroupPerm (BG := G) M) : ℝ)^2 = 1 := by
    have hf : (M.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
    simp only [bigEndpointPairMass, Green64SmallHaar.permutationPairMass,
      BigGroupPerm, Fintype.card_pi, Fintype.card_perm, Fintype.card_fin, Nat.cast_prod]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    simp [hf]
  have h : (bigEndpointPairMass (BG := G) M : ℂ) *
      (Fintype.card (BigGroupPerm (BG := G) M) : ℂ)^2 = 1 := by exact_mod_cast hr
  calc
    _ = 1 / (Fintype.card (BigGroupPerm (BG := G) M) : ℂ)^2 :=
      (eq_div_iff (pow_ne_zero 2 hn)).2 h
    _ = _ := by rw [one_div, ← inv_pow, pow_two]

/-- Endpoint means in the exact row/block order of the original operator. -/
theorem source_original_unfiltered_ideal_ENDPOINT_BLOCK_MEAN434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (M : ℕ) (mu : (g : G) → BP g → ℝ)
    (K : SourceOriginalJointBigState434 BP M → SourceOriginalJointBigState434 BP M → ℂ)
    (F H : SourceOriginalJointBigState434 BP M → ℂ) :
    (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      (∑ sigma : BigGroupPerm (BG := G) M, ∑ tau : BigGroupPerm (BG := G) M,
        ∑ t, (bigEndpointPairMass (BG := G) M : ℂ) *
          K (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)) * H t)) =
    ∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) *
      star (sourceOriginalUnfilteredIdealEndpointMean434 BP M F s) *
      (∑ t, K s t * sourceOriginalUnfilteredIdealEndpointMean434 BP M H t) := by
  have he := source_original_unfiltered_ideal_ENDPOINT_PAIR_MEAN434 BP M mu K F H
  dsimp only at he
  rw [← source_original_unfiltered_ideal_pair_mass434 M] at he
  simp only [Finset.mul_sum] at he ⊢
  calc
    _ = ∑ sigma : BigGroupPerm (BG := G) M, ∑ tau : BigGroupPerm (BG := G) M,
        ∑ s, ∑ t, (bigEndpointPairMass (BG := G) M : ℂ) *
          ((sourceOriginalJointBigMass434 BP mu s : ℂ) *
            (K (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)) *
              star (F s) * H t)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sigma hsigma
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro tau htau
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := by
      rw [he]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      ring

def sourceOriginalUnfilteredIdealRawPatternBlock434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (nu : SourceOriginalProbePattern434 G m)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) : ℂ :=
  ∑ sigma : BigGroupPerm (BG := G) (J+ell),
    ∑ tau : BigGroupPerm (BG := G) (J+ell), ∑ t,
      (bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
      sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
      sourceOriginalB26CanonicalRawValue434 P J ell m hmJ nu
        dsmall s t sigma tau zeta theta o k * H t

theorem source_original_unfiltered_ideal_RAW_PATTERN_BLOCK_PAIR434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (nu : SourceOriginalProbePattern434 G m)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ) :
    (∑ s, (sourceOriginalJointBigMass434 _ mu s : ℂ) * star (F s) *
      sourceOriginalUnfilteredIdealRawPatternBlock434 P J ell m hmJ mu nu
        dsmall zeta theta o k H s) =
    sourceOriginalUnfilteredIdealRawPatternForm434 P J ell m hmJ mu nu
      dsmall zeta theta o k
      (sourceOriginalUnfilteredIdealEndpointMean434 _ (J+ell) F)
      (sourceOriginalUnfilteredIdealEndpointMean434 _ (J+ell) H) := by
  have hp (s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g})
      (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
      sourceOriginalB26CanonicalRawValue434 P J ell m hmJ nu dsmall s t sigma tau zeta theta o k =
      sourceOriginalB26CanonicalRawValue434 P J ell m hmJ nu dsmall
        (fun g i => s g (sigma g i)) (fun g i => t g (tau g i))
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta theta o k := by
    simp only [sourceOriginalB26CanonicalRawValue434,
      sourceOriginalB26CanonicalSharedDivisor434, Equiv.refl_apply]
  let K := fun s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g} =>
    sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
    sourceOriginalB26CanonicalRawValue434 P J ell m hmJ nu dsmall s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) zeta theta o k
  have he := source_original_unfiltered_ideal_ENDPOINT_BLOCK_MEAN434
    (fun g => {p : ℕ // p ∈ P g}) (J+ell) mu K F H
  calc
    _ = ∑ s, (sourceOriginalJointBigMass434 _ mu s : ℂ) * star (F s) *
        (∑ sigma : BigGroupPerm (BG := G) (J+ell), ∑ tau : BigGroupPerm (BG := G) (J+ell),
          ∑ t, (bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
            K (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)) * H t) := by
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      apply Finset.sum_congr rfl
      intro sigma hsigma
      apply Finset.sum_congr rfl
      intro tau htau
      apply Finset.sum_congr rfl
      intro t ht
      rw [source_original_B26_fresh_law_permuted434, hp]
      dsimp only [K]
      ring
    _ = _ := by
      rw [he]
      rfl

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealNoneBlock -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem source_original_unfiltered_ideal_none_shared434
    {G : Type} [DecidableEq G] (J ell m : ℕ) (hmJ : m ≤ J) (g : G) :
    sourceBigShared J ell m (sourceOriginalB26RawNonePattern434 (G := G) J m PUnit.unit) g =
      Finset.univ.image (fun i : Fin J => i.castAdd ell) := by
  rw [← source_original_unfiltered_ideal_empty_pattern434 J m hmJ,
    source_original_probe_memory_shared_slots434]
  simp [sourceOriginalProbeSharedSlots434, sourceOriginalSharedSlots434,
    sourceOriginalProbeFreedSlots434]

/-- Literal positive RAW-none frozen block is the negative empty signed
replacement block. The empty auxiliary carrier has exactly one element,
its auxiliary mass is one and its two-endpoint ban is vacuous. -/
theorem source_original_unfiltered_ideal_FROZEN_NONE_BLOCK434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k ≠ 0)
    (H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    sourceOriginalB26FrozenBigBlock434 (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell m (sourceOriginalB26RawNonePattern434 (G := G) J m) mu V
      (fun _ _ _ _ => 1) dsmall zeta theta o k H s =
    -sourceOriginalUnfilteredIdealRawPatternBlock434 P J ell m hmJ mu
      (∅,∅) dsmall zeta theta o k H s := by
  let BP := fun g => {p : ℕ // p ∈ P g}
  let pats : PUnit → SourcePattern G J m := sourceOriginalB26RawNonePattern434 (G := G) J m
  have hempty (n : PUnit) (g : G) (j : (pats n).free g) : False :=
    Finset.notMem_empty j.val j.property
  let aux0 (n : PUnit) : SourceBigAux BP J m (pats n) :=
    fun g j => False.elim (hempty n g j)
  letI (n : PUnit) : Unique (SourceBigAux BP J m (pats n)) :=
    { default := aux0 n
      uniq := fun a => by funext g j; exact False.elim (hempty n g j) }
  have hmass (n : PUnit) (aux : SourceBigAux BP J m (pats n)) :
      sourceAuxMass BP (fun _ p => p.val) J m V (pats n) aux = 1 := by
    apply Finset.prod_eq_one
    intro g hg
    apply Finset.prod_eq_one
    intro j hj
    exact False.elim (hempty n g j)
  have hban (n : PUnit) (aux : SourceBigAux BP J m (pats n))
      (t : (g : G) → Fin (J+ell) → BP g) :
      sourceOriginalB26FrozenAuxBan434 BP J ell m (pats n) aux s t := by
    intro g j i
    exact False.elim (hempty n g j)
  have hD (aux : SourceBigAux BP J m (pats PUnit.unit))
      (sigma : BigGroupPerm (BG := G) (J+ell)) :
      sourceOriginalB26FrozenD434 BP (fun _ p => p.val) J ell m dsmall
        (pats PUnit.unit) aux s sigma =
      dsmall * ∏ g : G, ∏ i : Fin J, (s g (sigma g (i.castAdd ell))).val := by
    unfold sourceOriginalB26FrozenD434
    congr 1
    apply Finset.prod_congr rfl
    intro g hg
    have hz : (∏ j : (pats PUnit.unit).free g, (aux g j).val) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      exact False.elim (hempty PUnit.unit g j)
    rw [hz, mul_one, source_original_unfiltered_ideal_none_shared434 J ell m hmJ]
    rw [Finset.prod_image]
    intro i hi j hj he
    exact Fin.ext (congrArg (fun z : Fin (J+ell) => z.val) he)
  have hweight (aux : SourceBigAux BP J m (pats PUnit.unit))
      (sigma tau : BigGroupPerm (BG := G) (J+ell))
      (t : (g : G) → Fin (J+ell) → BP g) :
      sourceOriginalB26FrozenBigWeight434 BP (fun _ p => p.val) J ell m pats mu V
        (fun _ _ _ _ => 1) dsmall zeta theta o k s
        ⟨PUnit.unit,aux,sigma,tau⟩ t =
      (bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu (pats PUnit.unit) s t sigma tau *
        originalEdgeScalar 1 zeta theta
          (dsmall * ∏ g : G, ∏ i : Fin J, (s g (sigma g (i.castAdd ell))).val) o k := by
    unfold sourceOriginalB26FrozenBigWeight434
    dsimp only
    rw [if_pos ⟨ho,hk,hban PUnit.unit aux t⟩, hmass, hD]
    simp only [Complex.ofReal_one, one_mul]
  have hneg : -sourceOriginalUnfilteredIdealRawPatternBlock434 P J ell m hmJ mu
      (∅,∅) dsmall zeta theta o k H s =
      ∑ sigma : BigGroupPerm (BG := G) (J+ell),
        ∑ tau : BigGroupPerm (BG := G) (J+ell), ∑ t,
          (bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
          sourceOriginalB26FrozenFreshLaw434 BP J ell m mu (pats PUnit.unit) s t sigma tau *
          originalEdgeScalar 1 zeta theta
            (dsmall * ∏ g : G, ∏ i : Fin J, (s g (sigma g (i.castAdd ell))).val) o k * H t := by
    unfold sourceOriginalUnfilteredIdealRawPatternBlock434
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    apply Finset.sum_congr rfl
    intro tau htau
    apply Finset.sum_congr rfl
    intro t ht
    rw [source_original_unfiltered_ideal_empty_raw_value434]
    have hp := congrArg (fun pat : SourcePattern G J m =>
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau)
      (source_original_unfiltered_ideal_empty_pattern434 (G := G) J m hmJ)
    rw [hp]
    ring
  change sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val)
    J ell m pats mu V (fun _ _ _ _ => 1) dsmall zeta theta o k H s = _
  rw [hneg]
  unfold sourceOriginalB26FrozenBigBlock434
  simp only [SourceOriginalB26FrozenFrame434, Fintype.sum_sigma,
    Fintype.sum_prod_type, Fintype.sum_unique]
  simp_rw [hweight]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealFrozenPair -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Literal frozen positive RAW-none plus every signed comparison RAW term,
with independent endpoint permutations, equals the proven harmonic form. -/
theorem source_original_unfiltered_ideal_FROZEN_RAW_PAIR434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}), NeZero p.val]
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
    (dsmall : ℕ)
    (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ) :
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
    (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      (sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
        (sourceOriginalB26RawNonePattern434 (G := G) J m) mu data.Vbig
        (fun _ _ _ _ => 1) dsmall zeta theta o k H s +
      sourceOriginalB26CanonicalRawBlock434 data blockA blockB
        J ell m hmJ Q h xi zeta theta o k false false dsmall H s)) =
    sourceOriginalUnfilteredIdealRawForm434 data.Tb J ell m hmJ blockA blockB mu
      dsmall zeta theta o k
      (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F)
      (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H) := by
  dsimp only
  simp_rw [source_original_unfiltered_ideal_FROZEN_NONE_BLOCK434
    data.Tb data.Vbig J ell m hmJ _ dsmall zeta theta o k ho hk]
  simp only [sourceOriginalB26CanonicalRawBlock434, Bool.false_eq_true, ite_false, one_mul]
  change (∑ s, (sourceOriginalJointBigMass434 _ _ s : ℂ) * star (F s) *
    (-sourceOriginalUnfilteredIdealRawPatternBlock434 data.Tb J ell m hmJ _
      (∅,∅) dsmall zeta theta o k H s +
      ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalUnfilteredIdealRawPatternBlock434 data.Tb J ell m hmJ _
          nu dsmall zeta theta o k H s)) = _
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.mul_sum]
  rw [source_original_unfiltered_ideal_RAW_PATTERN_BLOCK_PAIR434]
  unfold sourceOriginalUnfilteredIdealRawForm434
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro nu hnu
  exact source_original_unfiltered_ideal_RAW_PATTERN_BLOCK_PAIR434
    data.Tb J ell m hmJ _ nu dsmall zeta theta o k F H

/-- Exact form decomposition of the ORIGINAL complete frozen harmonic family:
positive Option-none, full signed canonical K, and true two-endpoint ban.
No norm estimate is a premise of this identity. -/
theorem source_original_unfiltered_ideal_FULL_FROZEN_PAIR434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}), NeZero p.val]
    (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
    (dsmall : ℕ)
    (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ) :
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
    (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ) mu data.Vbig
        (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
          J ell m hmJ Q (fun _ => h) (fun _ => h) xi)
        dsmall zeta theta o k H s) =
    sourceOriginalUnfilteredIdealRawForm434 data.Tb J ell m hmJ blockA blockB mu
      dsmall zeta theta o k
      (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F)
      (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H) +
    sourceOriginalB26CanonicalComparisonForm434 data blockA blockB
      J ell m hmJ Q h xi zeta theta o k false false dsmall F H -
    sourceOriginalB26CanonicalAuxBanForm434 data blockA blockB
      J ell m hmJ Q h xi zeta theta o k false false dsmall F H := by
  dsimp only
  simp_rw [source_original_unfiltered_ideal_FULL_FROZEN_DECOMPOSITION434
    data blockA blockB hBlocks J ell m hmJ Q h xi zeta theta o k ho hk dsmall]
  rw [← source_original_unfiltered_ideal_FROZEN_RAW_PAIR434 data blockA blockB
    J ell m hmJ Q h xi zeta theta o k ho hk dsmall F H,
    source_original_B26_CANONICAL_COMPARISON_FORM_BLOCK434,
    source_original_B26_CANONICAL_AUX_BAN_FORM_BLOCK434]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rfl

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealFullSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A genuine eventual saving for the ORIGINAL full frozen harmonic family.
The proof adds the already established actual comparison and auxiliary-ban
errors to the newly proved signed RAW family; no family-saving assumption
is made. This unit-divisor theorem precedes the exact divisor/orientation
adapters. The structural lower block counts are explicit, since they are
not fields of bare SourceComparisonData434. -/
theorem eventually_source_original_unfiltered_ideal_FULL_UNIT434
    (cfg : SourceComparisonFixed434)
    (gamma dscale A Cfreq Cslots c : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (m : ℕ) (hm : 1 ≤ m) (hcap : m ≤ cfg.tmax)
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ)) :
    ∃ (D HH : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ HH ∧
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}), NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (hcountA : c*Real.log L ≤ (blockA.card:ℝ))
      (hcountB : c*Real.log L ≤ (blockB.card:ℝ))
      (J ell : ℕ) (hmJ : m ≤ J) (hell : 1 ≤ ell)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (zeta theta : ℝ) (hZeta : |zeta| ≤ L^Cfreq)
      (o : ℤ) (ho : o=1 ∨ o= -1)
      (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
    ‖(∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
        (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ) mu data.Vbig
        (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
          J ell m hmJ Q (fun _ => h) (fun _ => h) xi)
        1 zeta theta o 1 H s)‖^2 ≤
      33*L^(-A)*sourceOriginalJointBigEnergy434 BP mu F*
        sourceOriginalJointBigEnergy434 BP mu H := by
  obtain ⟨D,HH,Cq,Cxi,hD,hHH,hCmp⟩ :=
    eventually_source_original_B26_AVERAGED_ALL_NU_COMPARISON434
      cfg gamma dscale A Cfreq 0 hgamma hd hA (by norm_num)
  refine ⟨D,HH,Cq,Cxi,hD,hHH,?_⟩
  filter_upwards [hCmp,
    eventually_source_original_B26_AVERAGED_ALL_NU_AUX_BAN434 cfg Cslots A Cq Cxi,
    eventually_ge_atTop (1:ℝ)] with L hCmp hBan hL
  dsimp only at hCmp ⊢
  simp only [add_zero] at hCmp
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hCmp⟩ := hCmp
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hBlocks hcountA hcountB J ell hmJ hell hSlots
    zeta theta hZeta o ho F H
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  let EF := sourceOriginalJointBigEnergy434 BP mu F
  let EH := sourceOriginalJointBigEnergy434 BP mu H
  have hVpos (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hVEq (g : G) : data.Vbig g = ∑ p : BP g, 1/(p.val:ℝ) := by
    rw [hVbig]
    simpa [BP] using (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).symm
  obtain ⟨hmu,hnorm⟩ := source_original_joint_harmonic_normalized434
    BP (fun _ p => p.val) data.Vbig hVpos hVEq
  have hEF : 0 ≤ EF := source_original_joint_big_energy_nonneg434 BP mu hmu F
  have hEH : 0 ≤ EH := source_original_joint_big_energy_nonneg434 BP mu hmu H
  have hFull (T : ((g : G) → Fin (J+ell) → BP g) → ℂ)
      (nu : SourceOriginalProbePattern434 G m) :
      sourceOriginalB26FullActiveEnergy434 data J ell m hmJ (fun _ => T) nu =
      sourceOriginalJointBigEnergy434 BP mu T := by
    simp only [sourceOriginalB26FullActiveEnergy434, sourceOriginalJointBigEnergy434,
      sourceOriginalJointBigMass434, sourceOriginalRealBigProductMass434, Complex.normSq_eq_norm_sq]
    rfl
  have hAct (T : ((g : G) → Fin (J+ell) → BP g) → ℂ) :
      sourceOriginalB26ActiveEnergy434 BP J ell mu T =
      sourceOriginalJointBigEnergy434 BP mu T := by
    simp only [sourceOriginalB26ActiveEnergy434, sourceOriginalJointBigEnergy434,
      sourceOriginalJointBigMass434, sourceOriginalRealBigProductMass434, Complex.normSq_eq_norm_sq]
  have hRaw := source_original_unfiltered_ideal_RAW_FORM_LOG_GAIN434
    data.Tb data.Vbig hVpos hVEq J ell m hmJ blockA blockB hBlocks
    L A c hL hA hc hm hell hcountA hcountB hbudget 1 zeta theta o 1 ho F H
  have hError :
      ‖sourceOriginalB26CanonicalComparisonForm434 data blockA blockB
        J ell m hmJ Q h xi zeta theta o 1 false false 1 F H‖^2 ≤ L^(-A)*EF*EH := by
    have he := (hCmp x Y Hprime data sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge
      hTbLower hVbig blockA blockB hBlocks m hcap J ell hmJ zeta 1
      (fun _ => 1) (fun _ => theta) (fun _ => o)
      (fun _ _ => Nat.zero_lt_one) (fun _ _ => ho) hZeta (by simp)
      EF EH hEF hEH (fun _ => F) (fun _ => H)
      (fun nu _ => by rw [hFull]; exact ⟨hEF,le_rfl⟩)
      (fun nu _ => by rw [hFull]; exact ⟨hEH,le_rfl⟩) false false).2
    exact he
  have hAux :
      ‖sourceOriginalB26CanonicalAuxBanForm434 data blockA blockB
        J ell m hmJ Q h xi zeta theta o 1 false false 1 F H‖^2 ≤ L^(-A)*EF*EH := by
    have hb := hBan x Y Hprime data hVbig hTbLower blockA blockB hBlocks
      J ell m hmJ hcap hSlots Q h xi hh hxi hQupper hXi
      zeta theta o 1 ho false false 1 F H
    change _ ≤ L^(-A)*sourceOriginalB26ActiveEnergy434 BP J ell mu F*
      sourceOriginalB26ActiveEnergy434 BP J ell mu H at hb
    rw [hAct, hAct] at hb
    exact hb
  rw [source_original_unfiltered_ideal_FULL_FROZEN_PAIR434 data blockA blockB
    hBlocks J ell m hmJ Q h xi zeta theta o 1 ho (by norm_num) 1 F H]
  have ht := source_original_unfiltered_ideal_three_square434
    (sourceOriginalUnfilteredIdealRawForm434 data.Tb J ell m hmJ blockA blockB mu
      1 zeta theta o 1 (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) F)
        (sourceOriginalUnfilteredIdealEndpointMean434 BP (J+ell) H))
    (sourceOriginalB26CanonicalComparisonForm434 data blockA blockB
      J ell m hmJ Q h xi zeta theta o 1 false false 1 F H)
    (sourceOriginalB26CanonicalAuxBanForm434 data blockA blockB
      J ell m hmJ Q h xi zeta theta o 1 false false 1 F H)
  change _ ≤ 33*L^(-A)*EF*EH
  change _ ≤ 9*L^(-A)*EF*EH at hRaw
  nlinarith only [ht,hRaw,hError,hAux]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealQuantitative -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Eventual negative log-power squared pairing for the ORIGINAL harmonic
BIG RAW-none PLUS full canonical two-block comparison family, including
the actual auxiliary-versus-endpoint ban, both independent endpoint means,
the full asymmetric K, both memoryOrientationK orientations, every
positive SMALL divisor and every nonzero signed k.

The fixed source constants and block-count constant precede m and the
canonical precisions. Then J,ell are fixed, and only then L tends to infinity.
Cap transport changes no original prime alphabet, mass or endpoint.
The displayed full-band, roughness, separation and lower-count hypotheses
are the original source geometry, not a new analytic saving premise. -/
theorem eventually_source_original_unfiltered_ideal_FULL_SIGNED_FROZEN434
    (cfg : SourceComparisonFixed434)
    (gamma dscale E Cfreq c : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale) (hE : 0 < E) (hc : 0 < c) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi : ℕ), 1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
    ∀ (J ell : ℕ) (hmJ : m ≤ J) (hell : 1 ≤ ell),
    ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι]
      [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}), NeZero p.val]
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g, data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g, loB g ≤ hiB g)
      (hBigUpper : ∀ g, (hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g, Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g, ∀ p ∈ data.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g, data.Vbig g = ∑ p ∈ data.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (hcountA : c*Real.log L ≤ (blockA.card:ℝ))
      (hcountB : c*Real.log L ≤ (blockB.card:ℝ))
      (zeta theta : ℝ) (hZeta : |zeta| ≤ L^Cfreq)
      (dsmall : ℕ) (hdsmall : 0 < dsmall)
      (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
      (F H : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let K := sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
      J ell m hmJ Q (fun _ => h) (fun _ => h) xi
    ‖(∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
      sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m pats mu data.Vbig
        (memoryOrientationK BP J ell m pats K o) dsmall zeta theta o k H s)‖^2 ≤
      L^(-(2*E))*sourceOriginalJointBigEnergy434 BP mu F*
        sourceOriginalJointBigEnergy434 BP mu H := by
  let A := 2*E+2
  have hA : 0 ≤ A := by dsimp [A]; linarith
  obtain ⟨m,hm,hbudget⟩ := source_original_unfiltered_ideal_choose_order434 A c hc
  let cfg' := sourceOriginalUnfilteredIdealCap434 cfg m
  obtain ⟨D,HH,Cq,Cxi,hD,hHH,hEvent⟩ :=
    eventually_source_original_unfiltered_ideal_FULL_UNIT434
      cfg' gamma dscale A Cfreq 1 c hgamma hd hA hc.le m hm
      (source_original_unfiltered_ideal_cap_contains434 cfg m) hbudget
  refine ⟨m,D,HH,Cq,Cxi,hm,hD,hHH,?_⟩
  intro J ell hmJ hell
  filter_upwards [hEvent, eventually_ge_atTop (max (33:ℝ) ((J+ell:ℕ):ℝ))]
    with L hMain hLarge
  have hL33 : 33 ≤ L := (le_max_left _ _).trans hLarge
  have hL : 1 ≤ L := by linarith
  have hSlots : ((J+ell:ℕ):ℝ) ≤ L^(1:ℝ) := by
    rw [Real.rpow_one]
    exact (le_max_right _ _).trans hLarge
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data instNZ
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hBlocks hcountA hcountB zeta theta hZeta dsmall hdsmall o k ho hk F H
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  let EF := sourceOriginalJointBigEnergy434 BP mu F
  let EH := sourceOriginalJointBigEnergy434 BP mu H
  let data' := sourceOriginalUnfilteredIdealData434 data m
  letI : ∀ g (p : {p : ℕ // p ∈ data'.Tb g}), NeZero p.val :=
    fun g p => ⟨(data'.hTbPrime g p.val p.property).ne_zero⟩
  have sep' : SourceOriginalSource03GroupSeparation434 data' :=
    ⟨sep.hTT,sep.hBB,sep.hTB⟩
  have hunit (BA BB : Finset G) (hdis : Disjoint BA BB)
      (hBA : c*Real.log L ≤ (BA.card:ℝ)) (hBB : c*Real.log L ≤ (BB.card:ℝ))
      (t : ℝ) :
      ‖(∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
        sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
          (sourceOriginalMemoryRawComparisonPattern434 BA BB J m hmJ) mu data.Vbig
          (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig BA BB
            J ell m hmJ Q (fun _ => h) (fun _ => h) xi) 1 zeta t o 1 H s)‖^2 ≤
      33*L^(-A)*EF*EH := by
    exact hMain x Y Hprime data' sep' loB hiB hBigFull hLoLeHi hBigUpper hLoLarge
      hTbLower hVbig BA BB hdis hBA hBB J ell hmJ hell hSlots zeta t hZeta o ho F H
  have hall (BA BB : Finset G) (hdis : Disjoint BA BB)
      (hBA : c*Real.log L ≤ (BA.card:ℝ)) (hBB : c*Real.log L ≤ (BB.card:ℝ)) :
      ‖(∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
        sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
          (sourceOriginalMemoryRawComparisonPattern434 BA BB J m hmJ) mu data.Vbig
          (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig BA BB
            J ell m hmJ Q (fun _ => h) (fun _ => h) xi) dsmall zeta theta o k H s)‖^2 ≤
      33*L^(-A)*EF*EH := by
    rw [source_original_unfiltered_ideal_DIVISOR_PAIR_NORM434
      BP (fun _ p => p.val) J ell m _ mu data.Vbig _ dsmall hdsmall zeta theta o k hk]
    exact hunit BA BB hdis hBA hBB ((k:ℝ)*(dsmall:ℝ)*theta)
  have hor := source_original_unfiltered_ideal_FROZEN_MEMORY_ORIENTATION434
    data.Tb J ell m hmJ blockA blockB data.Vbig Q h xi mu dsmall zeta theta o k H
  have hbefore :
      ‖(∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
        sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
          (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ) mu data.Vbig
          (memoryOrientationK BP J ell m
            (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ)
            (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
              J ell m hmJ Q (fun _ => h) (fun _ => h) xi) o)
          dsmall zeta theta o k H s)‖^2 ≤ 33*L^(-A)*EF*EH := by
    by_cases ho1 : o=1
    · simpa only [memoryOrientationK, if_pos ho1] using
        hall blockA blockB hBlocks hcountA hcountB
    · simp only [memoryOrientationK, if_neg ho1]
      have hs := source_original_unfiltered_ideal_FROZEN_BLOCK_TRANSPOSE434
        data.Tb J ell m hmJ blockA blockB data.Vbig Q h xi mu dsmall zeta theta o k H
      have heq :
          (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
            sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
              (sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ) mu data.Vbig
              (fun v aux u w => sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockA blockB
                J ell m hmJ Q (fun _ => h) (fun _ => h) xi v aux w u)
              dsmall zeta theta o k H s) =
          (∑ s, (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) *
            sourceOriginalB26FrozenBigBlock434 BP (fun _ p => p.val) J ell m
              (sourceOriginalMemoryRawComparisonPattern434 blockB blockA J m hmJ) mu data.Vbig
              (sourceOriginalMemoryRawComparisonK434 data.Tb data.Vbig blockB blockA
                J ell m hmJ Q (fun _ => h) (fun _ => h) xi)
              dsmall zeta theta o k H s) := by
        apply Finset.sum_congr rfl
        intro s hs'
        exact congrArg (fun z : ℂ => (sourceOriginalJointBigMass434 BP mu s : ℂ) * star (F s) * z)
          (hs s).symm
      rw [heq]
      exact hall blockB blockA hBlocks.symm hcountB hcountA
  have hmu (g : G) (p : BP g) : 0 ≤ mu g p := by
    exact div_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
      (cfg.hv.trans_le (data.hVbig g)).le
  have hEF : 0 ≤ EF := source_original_joint_big_energy_nonneg434 BP mu hmu F
  have hEH : 0 ≤ EH := source_original_joint_big_energy_nonneg434 BP mu hmu H
  change _ ≤ L^(-(2*E))*EF*EH
  calc
    _ ≤ 33*L^(-A)*EF*EH := hbefore
    _ = (33*L^(-A))*(EF*EH) := by ring
    _ ≤ L^(-(2*E))*(EF*EH) :=
      mul_le_mul_of_nonneg_right
        (source_original_unfiltered_ideal_absorb_33_434 L E hL33) (mul_nonneg hEF hEH)
    _ = _ := by ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealTargetNodup -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] [DecidableEq Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Filter the TARGET after orienting the kernel. The numerical list,
including repetitions, is precisely the CLEAN birth batch. -/
def sourceOriginalUnfilteredIdealTargetNodupK434
    (K : SourcePatternK BP J ell m patterns) : SourcePatternK BP J ell m patterns :=
  fun nu aux s t =>
    if (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns nu) t).Nodup
    then K nu aux s t else 0

/-- The birth-list equality on every original CLEAN witness, not just a
chosen parameterization of frozen frames. -/
theorem source_original_unfiltered_ideal_CLEAN_BIRTHS434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hc : memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z) :
    orientedEFreshBirths SP sm BP bm J ell m cap patterns z =
      sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns z.1)
        (fun g i => (z.2.2.1.bigChoice g).1 (z.2.2.1.tauBig g i)) := by
  unfold orientedEFreshBirths sourceOriginalMarkedCleanBirthNumbers434
  congr 1
  funext g
  simp only [orientedFresh,orientedUnshared,(hc g).2,Finset.sdiff_empty]

/-- The true fresh-batch filter can be absorbed into arbitrary K with
both scalar orientations. Conjugation fixes its real zero/one indicator. -/
theorem source_original_unfiltered_ideal_CLEAN_NODUP_COEFFICIENT434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hc : memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z) :
    sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
      q rho Vs V mu (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns K)
        zeta theta o k x z =
    if (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x z else 0 := by
  have he := source_original_unfiltered_ideal_CLEAN_BIRTHS434
    SP sm BP bm J ell m cap patterns x z hc
  unfold sourceOrientedPhysicalCoefficient
  dsimp only [sourceOriginalUnfilteredIdealTargetNodupK434]
  rw [← he]
  by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup
  · simp only [if_pos hn]
  · simp only [if_neg hn,Green64SmallHaar.groupPermutedKernel,
      originalEdgeScalar,originalOrientedKernel,zero_mul,star_zero,ite_self,mul_zero]

/-- A NEW seen-erased ordered CLEAN row: all original legality is retained,
the global seen-disjointness condition is removed, and the true fresh LIST
Nodup remains. No reachable-history or initial inventory restriction appears. -/
def sourceOriginalUnfilteredIdealLocalClean434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ) : ℂ :=
  ∑ z ∈ sourceOrientedPhysicalChoices SP sm BP bm J ell m cap patterns x o k,
    if memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z ∧
      (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup then
      sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns
        q rho Vs V mu (memoryOrientationK BP J ell m patterns K o) zeta theta o k x z *
        F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
    else 0

/-- Exact bridge to all existing arbitrary-K CLEAN/Fourier identities.
Orientation is applied BEFORE the target filter, including on negative edges. -/
theorem source_original_unfiltered_ideal_LOCAL_CLEAN_AS_TARGET_K434
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → ℂ) :
    sourceOriginalUnfilteredIdealLocalClean434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x F =
    ∑ z ∈ sourceOrientedPhysicalChoices SP sm BP bm J ell m cap patterns x o k,
      if memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z then
        sourceOrientedPhysicalCoefficient SP sm BP bm J ell m cap patterns q rho Vs V mu
          (sourceOriginalUnfilteredIdealTargetNodupK434 BP bm J ell m patterns
            (memoryOrientationK BP J ell m patterns K o)) zeta theta o k x z *
          F (sourceOrientedPhysicalOutput SP sm BP bm J ell m cap patterns x o k z)
      else 0 := by
  unfold sourceOriginalUnfilteredIdealLocalClean434
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hc : memorySourceCleanChoice SP sm BP bm J ell m cap patterns x z
  · rw [if_pos hc,source_original_unfiltered_ideal_CLEAN_NODUP_COEFFICIENT434
      SP sm BP bm J ell m cap patterns q rho Vs V mu _ zeta theta o k x z hc]
    by_cases hn : (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).Nodup
    · simp only [hc,hn,and_self,if_pos]
    · simp only [hc,hn,and_false,if_false,zero_mul]
  · simp only [hc,false_and,if_false]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Exact product expectation, for dependent finite alphabets and numerical tests. -/
theorem source_original_physical_product_test434
    {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Type) [∀ i,Fintype (P i)]
    (value : (i : I) → P i → ℕ) (mu : (i : I) → P i → ℝ)
    (test : I → ℕ → ℝ) :
    (∑ x : (i : I) → P i,(∏ i,mu i (x i))*(∏ i,test i (value i (x i)))) =
      ∏ i,∑ p : P i,mu i p*test i (value i p) := by
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (p : P i) => mu i p*test i (value i p))).symm

/-- Two distinct coordinates remain independent even when the alphabets overlap numerically. -/
theorem source_original_physical_pair_test434
    {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Type) [∀ i,Fintype (P i)]
    (value : (i : I) → P i → ℕ) (mu : (i : I) → P i → ℝ)
    (hmass : ∀ i,∑ p : P i,mu i p=1)
    (i j : I) (hne : i≠j) (f g : ℕ → ℝ) :
    (∑ x : (i : I) → P i,(∏ k,mu k (x k))*f (value i (x i))*g (value j (x j))) =
      (∑ p : P i,mu i p*f (value i p))*(∑ p : P j,mu j p*g (value j p)) := by
  have h := source_original_physical_product_test434 P value mu
    (fun k p => (if k=i then f p else 1)*(if k=j then g p else 1))
  have hrow (k : I) :
      (∑ p : P k,mu k p*((if k=i then f (value k p) else 1)*
        (if k=j then g (value k p) else 1))) =
      (if k=i then ∑ p : P i,mu i p*f (value i p) else 1)*
      (if k=j then ∑ p : P j,mu j p*g (value j p) else 1) := by
    by_cases hi : k=i
    · subst k; simp only [ite_true,if_neg hne,mul_one]
    · by_cases hj : k=j
      · subst k; simp only [if_neg hi,ite_true,one_mul]
      · simp only [if_neg hi,if_neg hj,mul_one,hmass]
  simp only [hrow,Finset.prod_mul_distrib,Finset.prod_ite_eq',
    Finset.mem_univ,ite_true] at h
  simpa only [mul_assoc] using h

/-- Equality of two numerical values costs at most one atom, not the size of either alphabet. -/
theorem source_original_physical_pair_collision434
    {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Type) [∀ i,Fintype (P i)] [∀ i,DecidableEq (P i)]
    (value : (i : I) → P i → ℕ) (hinj : ∀ i,Function.Injective (value i))
    (mu : (i : I) → P i → ℝ) (hmu : ∀ i p,0 ≤ mu i p)
    (hmass : ∀ i,∑ p : P i,mu i p=1)
    (i j : I) (hne : i≠j) (eta : ℝ) (heta : 0 ≤ eta)
    (hcap : ∀ p : P j,mu j p≤eta) :
    (∑ x : (i : I) → P i,if value i (x i)=value j (x j)
      then ∏ k,mu k (x k) else 0) ≤ eta := by
  have hpoint (x : (i : I) → P i) :
      (if value i (x i)=value j (x j) then ∏ k,mu k (x k) else 0) =
      ∑ p : P i,(∏ k,mu k (x k))*
        (if value i (x i)=value i p then 1 else 0)*
        (if value j (x j)=value i p then 1 else 0) := by
    rw [Finset.sum_eq_single (x i)]
    · by_cases he : value i (x i)=value j (x j) <;> simp [he,eq_comm]
    · intro p hp hnep
      have hn : value i (x i)≠value i p := fun h => hnep ((hinj i h).symm)
      simp only [if_neg hn,mul_zero,zero_mul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hfiber (v : ℕ) :
      (∑ p : P j,mu j p*(if value j p=v then 1 else 0)) ≤ eta := by
    by_cases hex : ∃ p : P j,value j p=v
    · obtain ⟨p,hp⟩ := hex
      rw [Finset.sum_eq_single p]
      · simpa only [if_pos hp,mul_one] using hcap p
      · intro q hq hne
        have hn : value j q≠v := fun hh => hne (hinj j (hh.trans hp.symm))
        simp only [if_neg hn,mul_zero]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · have hn (p : P j) : value j p≠v := fun hh => hex ⟨p,hh⟩
      simpa only [hn,ite_false,mul_zero,Finset.sum_const_zero] using heta
  calc
    _ = ∑ x : (i : I) → P i,∑ p : P i,(∏ k,mu k (x k))*
        (if value i (x i)=value i p then 1 else 0)*
        (if value j (x j)=value i p then 1 else 0) := Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = ∑ p : P i,∑ x : (k : I) → P k,(∏ k,mu k (x k))*
        (if value i (x i)=value i p then 1 else 0)*
        (if value j (x j)=value i p then 1 else 0) := Finset.sum_comm
    _ = ∑ p : P i,mu i p*(∑ q : P j,mu j q*(if value j q=value i p then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [source_original_physical_pair_test434 P value mu hmass i j hne
        (fun v => if v=value i p then 1 else 0) (fun v => if v=value i p then 1 else 0)]
      have he : (∑ q : P i,mu i q*(if value i q=value i p then 1 else 0))=mu i p := by
        simp only [(hinj i).eq_iff,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq']
        simp
      rw [he]
    _ ≤ ∑ p : P i,mu i p*eta :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hfiber _) (hmu i p))
    _ = eta := by rw [← Finset.sum_mul,hmass,one_mul]

/-- A true list with distinct coordinate indices fails Nodup only through a pair of distinct draws. -/
theorem source_original_physical_list_collision_cover434
    {I : Type} (l : List I) (hl : l.Nodup) (v : I → ℕ)
    (hbad : ¬(l.map v).Nodup) :
    ∃ i∈l,∃ j∈l,i≠j ∧ v i=v j := by
  classical
  by_contra hn
  apply hbad
  clear hbad
  induction l with
  | nil => simp
  | cons a l ih =>
    have hla := List.nodup_cons.mp hl
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      obtain ⟨b,hb,he⟩ := List.mem_map.mp hmem
      have hne : a≠b := by intro h; subst b; exact hla.1 hb
      exact hn ⟨a,by simp,b,by simp [hb],hne,he.symm⟩
    · apply ih hla.2
      intro hex
      obtain ⟨i,hi,j,hj,hne,he⟩ := hex
      exact hn ⟨i,by simp [hi],j,by simp [hj],hne,he⟩

/-- Finite numerical LIST collision bound. No assumption that different alphabets are disjoint. -/
theorem source_original_physical_list_collision434
    {I : Type} [Fintype I] [DecidableEq I]
    (P : I → Type) [∀ i,Fintype (P i)] [∀ i,DecidableEq (P i)]
    (value : (i : I) → P i → ℕ) (hinj : ∀ i,Function.Injective (value i))
    (mu : (i : I) → P i → ℝ) (hmu : ∀ i p,0 ≤ mu i p)
    (hmass : ∀ i,∑ p : P i,mu i p=1)
    (l : List I) (hl : l.Nodup) (eta : ℝ) (heta : 0 ≤ eta)
    (hcap : ∀ i∈l,∀ p : P i,mu i p≤eta) :
    (∑ x : (i : I) → P i,
      if ¬(l.map (fun i => value i (x i))).Nodup then ∏ i,mu i (x i) else 0) ≤
      (Fintype.card I:ℝ)^2*eta := by
  let event := fun (x : (i : I) → P i) (ij : I×I) =>
    ij.1∈l ∧ ij.2∈l ∧ ij.1≠ij.2 ∧ value ij.1 (x ij.1)=value ij.2 (x ij.2)
  have hu := source_finite_weighted_bad_union434
    (Finset.univ : Finset ((i : I) → P i)) (Finset.univ : Finset (I×I))
    (fun x => ∏ i,mu i (x i))
    (fun x => ¬(l.map (fun i => value i (x i))).Nodup) event
    (fun x _ => Finset.prod_nonneg (fun i _ => hmu i _))
    (by
      intro x _ hb
      obtain ⟨i,hi,j,hj,hne,he⟩ :=
        source_original_physical_list_collision_cover434 l hl _ hb
      exact ⟨(i,j),Finset.mem_univ _,hi,hj,hne,he⟩)
  have hu2 : (∑ x : (i : I) → P i,
      if ¬(l.map (fun i => value i (x i))).Nodup then ∏ i,mu i (x i) else 0) ≤
      ∑ ij : I×I,∑ x : (i : I) → P i,if event x ij then ∏ i,mu i (x i) else 0 := by
    convert hu using 1
    · apply Finset.sum_congr rfl
      intro x _
      by_cases h : (l.map (fun i => value i (x i))).Nodup <;> simp [h]
    · apply Finset.sum_congr rfl
      intro ij _
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : event x ij <;> simp [h]
  apply hu2.trans
  calc
    _ ≤ ∑ ij : I×I,eta := by
      apply Finset.sum_le_sum
      intro ij _
      obtain ⟨i,j⟩ := ij
      by_cases hi : i∈l
      · by_cases hj : j∈l
        · by_cases hij : i≠j
          · simpa [event,hi,hj,hij] using
              source_original_physical_pair_collision434 P value hinj mu hmu hmass
                i j hij eta heta (hcap j hj)
          · simpa [event,hij] using heta
        · simpa [event,hj] using heta
      · simpa [event,hi] using heta
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,
        nsmul_eq_mul,Nat.cast_mul]; ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalFresh -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ)
variable (J ell m : ℕ)

/-- The indices of the true numerical birth list, before applying values. -/
def sourceOriginalUnfilteredPhysicalBirthIndices434 (pat : SourcePattern G J m) :
    List (Σ _g : G,Fin (J+ell)) :=
  (Finset.univ : Finset G).toList.flatMap (fun g =>
    (Finset.univ \ sourceBigShared J ell m pat g).toList.map (fun i => ⟨g,i⟩))

theorem source_original_physical_birth_indices_mem434
    (pat : SourcePattern G J m) (g : G) (i : Fin (J+ell)) :
    (⟨g,i⟩ : Σ _g : G,Fin (J+ell)) ∈ sourceOriginalUnfilteredPhysicalBirthIndices434 J ell m pat ↔
      i ∉ sourceBigShared J ell m pat g := by
  simp [sourceOriginalUnfilteredPhysicalBirthIndices434]

/-- Every coordinate is listed exactly once. This says nothing about repeated numerical values. -/
theorem source_original_physical_birth_indices_nodup434
    (pat : SourcePattern G J m) :
    (sourceOriginalUnfilteredPhysicalBirthIndices434 J ell m pat).Nodup := by
  unfold sourceOriginalUnfilteredPhysicalBirthIndices434
  apply List.nodup_flatMap.mpr
  constructor
  · intro g _
    exact List.Nodup.map (fun i j h => by cases h; rfl) (Finset.nodup_toList _)
  · apply List.Pairwise.imp ?_ (Finset.nodup_toList (Finset.univ : Finset G))
    intro g h hne
    apply List.disjoint_left.mpr
    intro z hz ht
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hz
    obtain ⟨j,hj,hf⟩ := List.mem_map.mp ht
    exact hne (congrArg Sigma.fst (he.trans hf.symm))

/-- An equality of LISTS, preserving all repetitions. -/
theorem source_original_physical_birth_list_map434
    (pat : SourcePattern G J m) (t : SourceOriginalB26Active434 BP J ell) :
    (sourceOriginalUnfilteredPhysicalBirthIndices434 J ell m pat).map
      (fun z => bm z.1 (t z.1 z.2)) =
    sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m pat t := by
  simp only [sourceOriginalUnfilteredPhysicalBirthIndices434,
    sourceOriginalMarkedCleanBirthNumbers434,List.map_flatMap,List.map_map,Function.comp_def]

/-- Positive real form of the actual frozen fresh law in canonical target coordinates. -/
def sourceOriginalUnfilteredPhysicalFresh434
    (mu : (g : G) → BP g → ℝ) (pat : SourcePattern G J m)
    (s t : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) : ℝ :=
  ∏ g,∏ i : Fin (J+ell),if i ∈ sourceBigShared J ell m pat g then
    (if t g (tau g i)=s g (sigma g i) then 1 else 0) else mu g (t g (tau g i))

theorem source_original_physical_fresh_cast434
    (mu : (g : G) → BP g → ℝ) (pat : SourcePattern G J m)
    (s t : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat s t sigma tau : ℂ) =
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau := by
  rw [source_original_B26_fresh_law_permuted434]
  unfold sourceOriginalUnfilteredPhysicalFresh434 sourceOriginalB26FrozenFreshLaw434
  push_cast
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem source_original_physical_fresh_nonneg434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (pat : SourcePattern G J m)
    (s t : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    0 ≤ sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat s t sigma tau := by
  apply Finset.prod_nonneg
  intro g _
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> first | positivity | exact hmu _ _

/-- Exact total mass of the original frozen target law. -/
theorem source_original_physical_fresh_row_mass434
    (mu : (g : G) → BP g → ℝ) (hmass : ∀ g,∑ p : BP g,mu g p=1)
    (pat : SourcePattern G J m) (s : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∑ t,sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat s t sigma tau)=1 := by
  let e := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  have hr : (∑ t,sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat s t sigma tau) =
      ∑ t : SourceOriginalB26Active434 BP J ell,∏ g,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then
          (if t g i=s g (sigma g i) then 1 else 0) else mu g (t g i) := by
    apply Fintype.sum_equiv e
    intro t
    rfl
  rw [hr,← Fintype.prod_sum (fun (g : G) (t : Fin (J+ell) → BP g) =>
    ∏ i : Fin (J+ell),if i ∈ sourceBigShared J ell m pat g then
      (if t i=s g (sigma g i) then (1:ℝ) else 0) else mu g (t i))]
  have hg (g : G) :
      (∑ t : Fin (J+ell) → BP g,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then
          (if t i=s g (sigma g i) then (1:ℝ) else 0) else mu g (t i))=1 := by
    rw [← Fintype.prod_sum (fun (i : Fin (J+ell)) (p : BP g) =>
      if i ∈ sourceBigShared J ell m pat g then
        (if p=s g (sigma g i) then (1:ℝ) else 0) else mu g p)]
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ sourceBigShared J ell m pat g
    · simp [hi]
    · simpa only [if_neg hi] using hmass g
  simp only [hg,Finset.prod_const_one]

/-- Literal numerical birth-LIST collision probability in each actual fixed frozen row.
The source state is arbitrary and may contain repeated active/OLD values. -/
theorem source_original_physical_FRESH_LIST_COLLISION434
    (hinj : ∀ g,Function.Injective (bm g))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hmass : ∀ g,∑ p : BP g,mu g p=1)
    (eta : ℝ) (heta : 0 ≤ eta) (hcap : ∀ g p,mu g p ≤ eta)
    (pat : SourcePattern G J m) (s : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∑ t,if ¬(sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m pat
        (fun g i => t g (tau g i))).Nodup then
      sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat s t sigma tau else 0) ≤
      (((J+ell)*Fintype.card G:ℕ):ℝ)^2*eta := by
  let I := Σ _g : G,Fin (J+ell)
  let P : I → Type := fun z => BP z.1
  let value : (z : I) → P z → ℕ := fun z => bm z.1
  let law : (z : I) → P z → ℝ := fun z p =>
    if z.2 ∈ sourceBigShared J ell m pat z.1 then
      (if p=s z.1 (sigma z.1 z.2) then 1 else 0) else mu z.1 p
  let l := sourceOriginalUnfilteredPhysicalBirthIndices434 J ell m pat
  have hlaw (z : I) (p : P z) : 0 ≤ law z p := by
    dsimp only [law]
    split_ifs <;> first | positivity | exact hmu _ _
  have hlawmass (z : I) : ∑ p : P z,law z p=1 := by
    dsimp only [law,P]
    by_cases h : z.2 ∈ sourceBigShared J ell m pat z.1
    · simp [h]
    · simpa only [if_neg h] using hmass z.1
  have hlawcap (z : I) (hz : z∈l) (p : P z) : law z p ≤ eta := by
    have hf := (source_original_physical_birth_indices_mem434 J ell m pat z.1 z.2).mp hz
    simpa only [law,if_neg hf] using hcap z.1 p
  have hb := source_original_physical_list_collision434 P value (fun z => hinj z.1)
    law hlaw hlawmass l (source_original_physical_birth_indices_nodup434 J ell m pat)
    eta heta hlawcap
  let e := (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau).trans
    (sourceOriginalUnfilteredIdealFlatEquiv434 BP (J+ell))
  have he :
      (∑ t,if ¬(sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m pat
          (fun g i => t g (tau g i))).Nodup then
        sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat s t sigma tau else 0) =
      ∑ x : (z : I) → P z,if ¬(l.map (fun z => value z (x z))).Nodup then
        ∏ z,law z (x z) else 0 := by
    apply Fintype.sum_equiv e
    intro t
    have hb := source_original_physical_birth_list_map434 BP bm J ell m pat
      (fun g i => t g (tau g i))
    change (l.map (fun z => value z (e t z))) =
      sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m pat
        (fun g i => t g (tau g i)) at hb
    rw [hb]
    by_cases hn : (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m pat
        (fun g i => t g (tau g i))).Nodup
    · simp [hn]
    · simp only [hn,not_false_eq_true,ite_true]
      dsimp only [law,e,Equiv.trans_apply,sourceOriginalUnfilteredIdealFlatEquiv434,
        sourceOriginalB26EndpointPermutationEquiv434,sourceOriginalUnfilteredPhysicalFresh434]
      rw [Fintype.prod_sigma]
      rfl
  rw [he]
  convert hb using 1
  simp only [I,Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,Nat.cast_mul]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ)
variable (J ell m : ℕ)

/-- Detailed balance is an exact identity after swapping both endpoint permutations. -/
theorem source_original_physical_fresh_balance434
    (mu : (g : G) → BP g → ℝ) (pat : SourcePattern G J m)
    (s t : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∏ g,∏ i,mu g (s g i))*sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat s t sigma tau =
    (∏ g,∏ i,mu g (t g i))*sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat t s tau sigma := by
  rw [← source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu s sigma,
    ← source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu t tau]
  unfold sourceOriginalUnfilteredPhysicalFresh434
  simp_rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hs : i ∈ sourceBigShared J ell m pat g
  · by_cases he : t g (tau g i)=s g (sigma g i)
    · simp [hs,he]
    · simp [hs,he,Ne.symm he]
  · simp [hs,mul_comm]

/-- The weighted target marginal is the ORIGINAL active law. -/
theorem source_original_physical_fresh_column434
    (mu : (g : G) → BP g → ℝ) (hmass : ∀ g,∑ p : BP g,mu g p=1)
    (pat : SourcePattern G J m) (t : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∑ s,(∏ g,∏ i,mu g (s g i))*
      sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat s t sigma tau) =
      ∏ g,∏ i,mu g (t g i) := by
  simp_rw [source_original_physical_fresh_balance434 BP J ell m mu pat]
  rw [← Finset.mul_sum,source_original_physical_fresh_row_mass434 BP J ell m mu hmass,
    mul_one]

/-- One-sided rarity in a finite positive coupling costs its square root in norm.
No independence or factorization of the complex joint multiplier is assumed. -/
theorem source_original_physical_schur434
    {A B : Type} [Fintype A] [Fintype B]
    (wA : A → ℝ) (wB : B → ℝ) (joint : A → B → ℝ)
    (hjoint : ∀ s t,0 ≤ joint s t)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hrow : ∀ s,∑ t,joint s t ≤ eps*wA s)
    (hcol : ∀ t,∑ s,joint s t ≤ wB t)
    (C : ℝ) (hC : 0 ≤ C)
    (F : A → ℂ) (H : B → ℂ) (K : A → B → ℂ)
    (hK : ∀ s t,‖K s t‖ ≤ C) :
    ‖∑ s,∑ t,(joint s t:ℂ)*(star (F s)*H t*K s t)‖^2 ≤
      C^2*eps*(∑ s,wA s*‖F s‖^2)*(∑ t,wB t*‖H t‖^2) := by
  have hp (z : A×B) :
      ‖star (F z.1)*H z.2*K z.1 z.2‖^2 ≤ C^2*‖F z.1‖^2*‖H z.2‖^2 := by
    rw [norm_mul,norm_mul,norm_star,mul_pow,mul_pow]
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hK z.1 z.2) 2)
      (mul_nonneg (sq_nonneg ‖F z.1‖) (sq_nonneg ‖H z.2‖))
    nlinarith only [hh]
  have hb := source_original_B26_homogeneous_shared_integration434
    (fun z : A×B => joint z.1 z.2)
    (fun z => ‖F z.1‖^2) (fun z => ‖H z.2‖^2)
    (fun z => star (F z.1)*H z.2*K z.1 z.2) (C^2)
    (fun z => hjoint _ _) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (sq_nonneg C) hp
  have hs :
      (∑ z : A×B,joint z.1 z.2*‖F z.1‖^2) ≤
      eps*(∑ s,wA s*‖F s‖^2) := by
    rw [Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    simp only [Prod.fst,Prod.snd]
    rw [← Finset.sum_mul]
    convert mul_le_mul_of_nonneg_right (hrow s) (sq_nonneg ‖F s‖) using 1 <;> ring
  have ht :
      (∑ z : A×B,joint z.1 z.2*‖H z.2‖^2) ≤ ∑ t,wB t*‖H t‖^2 := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    simp only [Prod.fst,Prod.snd]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol t) (sq_nonneg _)
  have hs0 : 0 ≤ ∑ z : A×B,joint z.1 z.2*‖F z.1‖^2 :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hjoint _ _) (sq_nonneg _))
  have ht0 : 0 ≤ ∑ z : A×B,joint z.1 z.2*‖H z.2‖^2 :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hjoint _ _) (sq_nonneg _))
  have hboth := mul_le_mul hs ht ht0 (le_trans hs0 hs)
  have hc := mul_le_mul_of_nonneg_left hboth (sq_nonneg C)
  rw [Fintype.sum_prod_type] at hb
  calc
    _ ≤ C^2*(∑ z : A×B,joint z.1 z.2*‖F z.1‖^2)*
      (∑ z : A×B,joint z.1 z.2*‖H z.2‖^2) := hb
    _ ≤ C^2*(eps*(∑ s,wA s*‖F s‖^2))*(∑ t,wB t*‖H t‖^2) := by
      nlinarith only [hc]
    _ = _ := by ring

/-- Actual frozen bad-birth bilinear bound, with both original endpoint permutations. -/
theorem source_original_physical_FRESH_BAD_PAIR434
    (hinj : ∀ g,Function.Injective (bm g))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hmass : ∀ g,∑ p : BP g,mu g p=1)
    (eta : ℝ) (heta : 0 ≤ eta) (hcap : ∀ g p,mu g p ≤ eta)
    (pat : SourcePattern G J m)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (C : ℝ) (hC : 0 ≤ C)
    (F H : SourceOriginalB26Active434 BP J ell → ℂ)
    (K : SourceOriginalB26Active434 BP J ell → SourceOriginalB26Active434 BP J ell → ℂ)
    (hK : ∀ s t,‖K s t‖ ≤ C) :
    ‖∑ s,∑ t,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau*
      (if ¬(sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m pat
          (fun g i => t g (tau g i))).Nodup then star (F s)*H t*K s t else 0)‖^2 ≤
      C^2*((((J+ell)*Fintype.card G:ℕ):ℝ)^2*eta)*
        sourceOriginalB26ActiveEnergy434 BP J ell mu F*
        sourceOriginalB26ActiveEnergy434 BP J ell mu H := by
  let A := SourceOriginalB26Active434 BP J ell
  let w := fun s : A => ∏ g,∏ i,mu g (s g i)
  let bad := fun t : A => ¬(sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m pat
    (fun g i => t g (tau g i))).Nodup
  let B := sourceOriginalUnfilteredPhysicalFresh434 BP J ell m mu pat
  let joint := fun s t : A => if bad t then w s*B s t sigma tau else 0
  let eps := ((((J+ell)*Fintype.card G:ℕ):ℝ)^2*eta)
  have hw (s : A) : 0 ≤ w s :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g _))
  have hB (s t : A) : 0 ≤ B s t sigma tau :=
    source_original_physical_fresh_nonneg434 BP J ell m mu hmu pat s t sigma tau
  have hjoint (s t : A) : 0 ≤ joint s t := by
    dsimp only [joint]; split_ifs
    · exact mul_nonneg (hw s) (hB s t)
    · exact le_rfl
  have hrow (s : A) : ∑ t,joint s t ≤ eps*w s := by
    have hb := source_original_physical_FRESH_LIST_COLLISION434
      BP bm J ell m hinj mu hmu hmass eta heta hcap pat s sigma tau
    have he : (∑ t,joint s t) = w s*(∑ t,if bad t then B s t sigma tau else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [joint]
      split_ifs <;> simp
    rw [he]
    change (∑ t,if bad t then B s t sigma tau else 0) ≤ eps at hb
    nlinarith only [mul_le_mul_of_nonneg_left hb (hw s)]
  have hcol (t : A) : ∑ s,joint s t ≤ w t := by
    calc
      _ ≤ ∑ s,w s*B s t sigma tau := by
        apply Finset.sum_le_sum
        intro s _
        dsimp only [joint]
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hw s) (hB s t)
      _ = _ := source_original_physical_fresh_column434 BP J ell m mu hmass pat t sigma tau
  have hb := source_original_physical_schur434 w w joint hjoint eps
    (mul_nonneg (sq_nonneg _) heta) hrow hcol C hC F H K hK
  have he :
      (∑ s,∑ t,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau*
        (if bad t then star (F s)*H t*K s t else 0)) =
      ∑ s,∑ t,(joint s t:ℂ)*(star (F s)*H t*K s t) := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [← source_original_physical_fresh_cast434 BP J ell m mu pat]
    dsimp only [joint,w,B]
    by_cases h : bad t <;> simp [h]
  rw [he]
  exact hb
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredPhysicalFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Removed numerical birth-LIST part of K, applied after the full orientation. -/
def sourceOriginalUnfilteredPhysicalBadK434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : G) → BP g → ℕ) (J ell m : ℕ)
    {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern G J m)
    (K : SourcePatternK BP J ell m patterns) : SourcePatternK BP J ell m patterns :=
  fun nu aux s t => if ¬(sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns nu) t).Nodup
    then K nu aux s t else 0

/-- The full actual frozen bad-birth family costs Csum² epsilon in squared pairing.
Adapted from the pinned AbsoluteCap434 averaging proof, replacing its frame bound
by the proved actual one-sided collision estimate. -/
theorem source_original_physical_FROZEN_BAD_FAMILY434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (J ell m : ℕ) (hinj : ∀ g,Function.Injective (bm g))
    {Nu : Type} [Fintype Nu] [DecidableEq Nu]
    (patterns : Nu → SourcePattern G J m)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hnorm : ∀ g,∑ p : BP g,mu g p=1)
    (eta : ℝ) (heta : 0 ≤ eta) (hcap : ∀ g p,mu g p ≤ eta)
    (V : G → ℝ) (hV : ∀ g,0 < V g)
    (hVeq : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (K : SourcePatternK BP J ell m patterns)
    (C : Nu → ℝ) (hC : ∀ nu,0 ≤ C nu)
    (hK : ∀ nu aux s t, ‖K nu aux s t‖ ≤ C nu)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (F H : SourceOriginalB26Active434 BP J ell → ℂ) :
    ‖(∑ s,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*star (F s)*
      sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V
        (sourceOriginalUnfilteredPhysicalBadK434 BP bm J ell m patterns K)
        dsmall zeta theta o k H s)‖^2 ≤
    (∑ nu,C nu)^2*((((J+ell)*Fintype.card G:ℕ):ℝ)^2*eta)*sourceOriginalB26ActiveEnergy434 BP J ell mu F*
      sourceOriginalB26ActiveEnergy434 BP J ell mu H := by
  let eps := ((((J+ell)*Fintype.card G:ℕ):ℝ)^2*eta)
  have heps : 0 ≤ eps := mul_nonneg (sq_nonneg _) heta
  let Active := SourceOriginalB26Active434 BP J ell
  let Frame := SourceOriginalB26FrozenFrame434 BP J ell m patterns
  let w := fun h : Frame =>
    ‖(sourceAuxMass BP bm J m V (patterns h.1) h.2.1:ℂ)*
      (bigEndpointPairMass (BG := G) (J+ell):ℂ)‖
  let kap := fun (h : Frame) (s t : Active) =>
    if (o=1 ∨ o= -1) ∧ k≠0 ∧
        sourceOriginalB26FrozenAuxBan434 BP J ell m (patterns h.1) h.2.1 s t then
      originalEdgeScalar
        (K h.1 h.2.1 (fun g i => s g (h.2.2.1 g i)) (fun g i => t g (h.2.2.2 g i)))
        zeta theta (sourceOriginalB26FrozenD434 BP bm J ell m dsmall
          (patterns h.1) h.2.1 s h.2.2.1) o k
    else 0
  let z := fun h : Frame => ∑ s : Active,∑ t : Active,
    ((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu (patterns h.1)
        s t h.2.2.1 h.2.2.2*
        (if ¬(sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns h.1)
          (fun g i => t g (h.2.2.2 g i))).Nodup then star (F s)*H t*kap h s t else 0)
  let EF := sourceOriginalB26ActiveEnergy434 BP J ell mu F
  let EH := sourceOriginalB26ActiveEnergy434 BP J ell mu H
  have hEF : 0 ≤ EF := Finset.sum_nonneg (fun s _ =>
    mul_nonneg (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g _)))
      (sq_nonneg _))
  have hEH : 0 ≤ EH := Finset.sum_nonneg (fun s _ =>
    mul_nonneg (Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g _)))
      (sq_nonneg _))
  have hw (h : Frame) : 0 ≤ w h := norm_nonneg _
  have hwC (h : Frame) :
      (w h:ℂ)=(sourceAuxMass BP bm J m V (patterns h.1) h.2.1:ℂ)*
        (bigEndpointPairMass (BG := G) (J+ell):ℂ) := by
    have hPm : 0 ≤ bigEndpointPairMass (BG := G) (J+ell) :=
      (groupPermutationPairMass_positive (G := G) (J+ell)).le
    dsimp only [w]
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (source_original_memory_aux_mass_nonneg434
        BP bm J m V hV (patterns h.1) h.2.1),
      abs_of_nonneg hPm]
    push_cast
    rfl
  have hsum (T : Nu → ℝ) : (∑ h : Frame,w h*T h.1)=∑ nu,T nu := by
    simp only [Frame,SourceOriginalB26FrozenFrame434,Fintype.sum_sigma,
      Fintype.sum_prod_type,w]
    apply Finset.sum_congr rfl
    intro nu _
    simp_rw [← Finset.sum_mul]
    rw [source_original_memory_BIG_AUX_total_mass434 BP bm J ell m V hV hVeq]
    exact one_mul _
  have hkap (h : Frame) (s t : Active) : ‖kap h s t‖ ≤ C h.1 := by
    dsimp only [kap]
    split_ifs with hg
    · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k hg.1]
      exact hK _ _ _ _
    · simpa only [norm_zero] using hC h.1
  have hz (h : Frame) : ‖z h‖^2 ≤ eps*(C h.1*EF)*(C h.1*EH) := by
    have hb := source_original_physical_FRESH_BAD_PAIR434 BP bm J ell m
      hinj mu hmu hnorm eta heta hcap (patterns h.1) h.2.2.1 h.2.2.2
      (C h.1) (hC h.1) F H (kap h) (hkap h)
    change ‖z h‖^2 ≤ (C h.1)^2*eps*EF*EH at hb
    calc
      _ ≤ (C h.1)^2*eps*EF*EH := hb
      _ = _ := by ring
  have hh := source_original_B26_homogeneous_shared_integration434
    w (fun h => C h.1*EF) (fun h => C h.1*EH) z eps hw
    (fun h => mul_nonneg (hC h.1) hEF)
    (fun h => mul_nonneg (hC h.1) hEH) heps hz
  have hleft :
      (∑ s,((∏ g,∏ i,mu g (s g i):ℝ):ℂ)*star (F s)*
        sourceOriginalB26FrozenBigBlock434 BP bm J ell m patterns mu V
          (sourceOriginalUnfilteredPhysicalBadK434 BP bm J ell m patterns K)
          dsmall zeta theta o k H s) =
      ∑ h : Frame,(w h:ℂ)*z h := by
    unfold sourceOriginalB26FrozenBigBlock434
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    dsimp only [z]
    rw [hwC]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    unfold sourceOriginalB26FrozenBigWeight434
    dsimp only [kap,sourceOriginalUnfilteredPhysicalBadK434]
    by_cases hn : (sourceOriginalMarkedCleanBirthNumbers434 BP bm J ell m (patterns h.1)
      (fun g i => t g (h.2.2.2 g i))).Nodup
    · simp [hn,originalEdgeScalar,originalOrientedKernel]
    · simp only [hn,not_false_eq_true,ite_true]
      split_ifs <;> ring
  rw [hleft]
  have hEFsum : (∑ h : Frame,w h*(C h.1*EF))=(∑ nu,C nu)*EF := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul,hsum]
  have hEHsum : (∑ h : Frame,w h*(C h.1*EH))=(∑ nu,C nu)*EH := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul,hsum]
  rw [hEFsum,hEHsum] at hh
  change _ ≤ (∑ nu,C nu)^2*eps*EF*EH
  nlinarith only [hh]
end Green64Analytic.CorrelationSquare

end

end

