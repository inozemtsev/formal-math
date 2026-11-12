module

public import Green64.Library.Correlation.Part070
public import Green64.Library.Weights.Part054
public import Green64.Library.Correlation.Part042
public import Green64.Library.Weights.FineAlpha
public import Green64.Library.Analysis.Estimates.Part014
public import Green64.Library.Correlation.Part065
public import Green64.Library.Weights.Part109
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part100
public import Green64.Library.Weights.Part047
public import Green64.Library.Weights.Part046
public import Green64.Library.Weights.FineMarkedArc

@[expose] public section

/-!
# Weights / Part110

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FullPatternLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 24000
set_option linter.unusedSectionVars false

/-- Original BIG probes retain their first-m indices when included in the
full SMALL+BIG group carrier. This is an embedding of labelled slots. -/
def parityProbeInrEmbedding434 (SG BG : Type) (m : ℕ) :
    (BG × Fin m) ↪ ((SG ⊕ BG) × Fin m) where
  toFun z := (Sum.inr z.1,z.2)
  inj' := by
    intro x y h
    apply Prod.ext
    · exact Sum.inr.inj (congrArg (fun z : (SG ⊕ BG) × Fin m => z.1) h)
    · exact congrArg (fun z : (SG ⊕ BG) × Fin m => z.2) h

/-- The full original pattern selects the same A/B BIG slots and no SMALL
slot. Its Finset maps preserve every label and both pattern cardinalities. -/
def parityFullProbePattern434 (SG : Type) {BG : Type} (m : ℕ)
    (nu : SourceOriginalProbePattern434 BG m) :
    SourceOriginalProbePattern434 (SG ⊕ BG) m :=
  (nu.1.map (parityProbeInrEmbedding434 SG BG m),
   nu.2.map (parityProbeInrEmbedding434 SG BG m))

variable {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]

@[simp] theorem parity_probe_map_mem_inr434 (m : ℕ)
    (s : Finset (BG × Fin m)) (g : BG) (j : Fin m) :
    (Sum.inr g,j) ∈ s.map (parityProbeInrEmbedding434 SG BG m) ↔ (g,j) ∈ s := by
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_map.mp h
    have hz' : z=(g,j) := (parityProbeInrEmbedding434 SG BG m).injective he
    exact hz' ▸ hz
  · intro h
    exact Finset.mem_map.mpr ⟨(g,j),h,rfl⟩

@[simp] theorem parity_probe_map_mem_inl434 (m : ℕ)
    (s : Finset (BG × Fin m)) (g : SG) (j : Fin m) :
    (Sum.inl g,j) ∉ s.map (parityProbeInrEmbedding434 SG BG m) := by
  intro h
  obtain ⟨z,hz,he⟩ := Finset.mem_map.mp h
  have hh := congrArg Prod.fst he
  cases hh

/-- No SMALL first-J slot is freed by an original BIG comparison. -/
@[simp] theorem parity_full_probe_freed_small434
    (J m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : SG) :
    sourceOriginalProbeFreedSlots434 J m hmJ (parityFullProbePattern434 SG m nu) (Sum.inl g)=∅ := by
  simp only [sourceOriginalProbeFreedSlots434,parityFullProbePattern434,
    parity_probe_map_mem_inl434,false_or,Finset.filter_false,Finset.image_empty]

/-- BIG freed slots are identical, not merely equinumerous. -/
@[simp] theorem parity_full_probe_freed_big434
    (J m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : BG) :
    sourceOriginalProbeFreedSlots434 J m hmJ (parityFullProbePattern434 SG m nu) (Sum.inr g)=
      sourceOriginalProbeFreedSlots434 J m hmJ nu g := by
  simp only [sourceOriginalProbeFreedSlots434,parityFullProbePattern434,
    parity_probe_map_mem_inr434]

/-- The lifted SMALL shared set is exactly the physical SMALL first-J set. -/
@[simp] theorem parity_full_probe_shared_small434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : SG) :
    sourceOriginalProbeSharedSlots434 J ell m hmJ (parityFullProbePattern434 SG m nu) (Sum.inl g)=
      sourceSmallShared J ell g := by
  unfold sourceOriginalProbeSharedSlots434
  rw [parity_full_probe_freed_small434]
  ext i
  simp only [sourceOriginalSharedSlots434,Finset.sdiff_empty,Finset.mem_image,
    Finset.mem_univ,true_and,sourceSmallShared,Finset.mem_filter,true_and]
  constructor
  · rintro ⟨j,rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩

@[simp] theorem parity_full_probe_shared_big434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : BG) :
    sourceOriginalProbeSharedSlots434 J ell m hmJ (parityFullProbePattern434 SG m nu) (Sum.inr g)=
      sourceOriginalProbeSharedSlots434 J ell m hmJ nu g := by
  simp only [sourceOriginalProbeSharedSlots434,parity_full_probe_freed_big434]

@[simp] theorem parity_full_probe_free_count_small434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : SG) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ (parityFullProbePattern434 SG m nu) (Sum.inl g)=ell := by
  simp [sourceOriginalProbeFreeMarkCount434]

@[simp] theorem parity_full_probe_free_count_big434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : BG) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ (parityFullProbePattern434 SG m nu) (Sum.inr g)=
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g := by
  simp only [sourceOriginalProbeFreeMarkCount434,parity_full_probe_freed_big434]

theorem parity_full_probe_shared_count_small434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : SG) :
    (sourceOriginalProbeSharedSlots434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inl g)).card=J := by
  unfold sourceOriginalProbeSharedSlots434
  rw [parity_full_probe_freed_small434,source_original_shared_slot_card434]
  simp

/-- The complete shared product on the combined carrier is exactly the
original SMALL product times the original BIG product, retaining all slots. -/
theorem parity_full_probe_shared_product434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (s : SG → Fin (J+ell) → ℕ) (b : BG → Fin (J+ell) → ℕ) :
    (∏ g : SG ⊕ BG, ∏ j ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) g, Sum.elim s b g j) =
    (∏ g : SG, ∏ j ∈ sourceSmallShared J ell g, s g j) *
    (∏ g : BG, ∏ j ∈ sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) g, b g j) := by
  rw [Fintype.prod_sum_type]
  simp only [parity_full_probe_shared_small434,parity_full_probe_shared_big434,
    Sum.elim_inl,Sum.elim_inr,source_original_probe_memory_shared_slots434]


/-- B574's TRUE labelled dilation on the lifted shared carrier is exactly
the original complete SMALL/BIG shared product. This retains repeated
numeric values in the definition and introduces no set-product surrogate. -/
theorem parity_full_probe_true_shared_dilation434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (s : SG → Fin (J+ell) → ℕ) (b : BG → Fin (J+ell) → ℕ) :
    sourceB574SharedDilation434 (J+ell)
      (sourceOriginalProbeSharedSlots434 J ell m hmJ (parityFullProbePattern434 SG m nu))
      (fun g j => Sum.elim s b g j.val) =
    (∏ g : SG, ∏ j ∈ sourceSmallShared J ell g, s g j) *
    (∏ g : BG, ∏ j ∈ sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) g, b g j) := by
  unfold sourceB574SharedDilation434
  simp only [Finset.prod_coe_sort]
  exact parity_full_probe_shared_product434 J ell m hmJ nu s b

/-- Both original V normalizations retain their complete SMALL factors. -/
theorem parity_full_probe_mass_prefactors434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (Vs : SG → ℂ) (Vb : BG → ℂ) :
    (∏ g : SG ⊕ BG, ((Sum.elim Vs Vb g)^(J+ell))⁻¹) *
      (∏ g : SG ⊕ BG, ((Sum.elim Vs Vb g)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ (parityFullProbePattern434 SG m nu) g)⁻¹) =
    ((∏ g : SG, (Vs g^(J+ell))⁻¹)*(∏ g : BG, (Vb g^(J+ell))⁻¹)) *
      ((∏ g : SG, (Vs g^ell)⁻¹)*
        (∏ g : BG, (Vb g^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)⁻¹)) := by
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
    parity_full_probe_free_count_small434,parity_full_probe_free_count_big434]

/-- Exact selected-coordinate equivalence; no numerical prime values enter. -/
def parityProbeSelectionEquiv434 (SG : Type) {BG : Type} (m : ℕ) (s : Finset (BG × Fin m)) :
    s ≃ s.map (parityProbeInrEmbedding434 SG BG m) :=
  s.equivMap (parityProbeInrEmbedding434 SG BG m)

/-- The complete A+B auxiliary family is transported as a sum of two
labelled bijections. Repeated numerical draws are unrestricted. -/
def parityFullProbeAuxEquiv434 (SG : Type) {BG : Type} (m : ℕ)
    (nu : SourceOriginalProbePattern434 BG m) :
    SourceOriginalProbeAuxIndex434 m nu ≃
      SourceOriginalProbeAuxIndex434 m (parityFullProbePattern434 SG m nu) :=
  Equiv.sumCongr (parityProbeSelectionEquiv434 SG m nu.1)
    (parityProbeSelectionEquiv434 SG m nu.2)

def parityFullProbeAuxLift434 (SG : Type) {BG : Type} (m : ℕ)
    (nu : SourceOriginalProbePattern434 BG m)
    (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    SourceOriginalProbeAuxIndex434 m (parityFullProbePattern434 SG m nu) → ℕ :=
  fun z => a ((parityFullProbeAuxEquiv434 SG m nu).symm z)

@[simp] theorem parity_full_probe_aux_lift_apply434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) (z : SourceOriginalProbeAuxIndex434 m nu) :
    parityFullProbeAuxLift434 SG m nu a (parityFullProbeAuxEquiv434 SG m nu z)=a z := by
  unfold parityFullProbeAuxLift434
  rw [Equiv.symm_apply_apply]

@[simp] theorem parity_full_probe_aux_group434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m) (z : SourceOriginalProbeAuxIndex434 m nu) :
    sourceOriginalProbeAuxGroup434 m (parityFullProbePattern434 SG m nu)
      (parityFullProbeAuxEquiv434 SG m nu z) =
      Sum.inr (sourceOriginalProbeAuxGroup434 m nu z) := by
  cases z <;> rfl

@[simp] theorem parity_full_probe_aux_V434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (z : SourceOriginalProbeAuxIndex434 m nu) :
    sourceOriginalProbeAuxV434 m (parityFullProbePattern434 SG m nu) (Sum.elim Vs Vb)
      (parityFullProbeAuxEquiv434 SG m nu z)=sourceOriginalProbeAuxV434 m nu Vb z := by
  cases z <;> rfl

@[simp] theorem parity_full_probe_aux_prime_sets434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (z : SourceOriginalProbeAuxIndex434 m nu) :
    sourceOriginalProbeAuxPrimeSets434 m (parityFullProbePattern434 SG m nu) (Sum.elim Ps Pb)
      (parityFullProbeAuxEquiv434 SG m nu z)=sourceOriginalProbeAuxPrimeSets434 m nu Pb z := by
  cases z <;> rfl

/-- The full true auxiliary probability of each repeated labelled draw
is preserved. Neither cell membership nor endpoint bans are conditioned. -/
theorem parity_full_probe_aux_law434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Vs : SG → ℝ) (Vb : BG → ℝ) (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    sourceSharedLaw434
      (fun z => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m (parityFullProbePattern434 SG m nu) (Sum.elim Vs Vb) z))
      (parityFullProbeAuxLift434 SG m nu a) =
    sourceSharedLaw434
      (fun z => sourcePrimeSharedAtom434 (sourceOriginalProbeAuxV434 m nu Vb z)) a := by
  unfold sourceSharedLaw434
  rw [←Equiv.prod_comp (parityFullProbeAuxEquiv434 SG m nu)]
  simp only [parity_full_probe_aux_V434,parity_full_probe_aux_lift_apply434]

theorem parity_full_probe_aux_membership434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    parityFullProbeAuxLift434 SG m nu a ∈
      Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m
        (parityFullProbePattern434 SG m nu) (Sum.elim Ps Pb)) ↔
    a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu Pb) := by
  simp only [Fintype.mem_piFinset]
  constructor
  · intro h z
    simpa only [parity_full_probe_aux_lift_apply434,parity_full_probe_aux_prime_sets434] using
      h (parityFullProbeAuxEquiv434 SG m nu z)
  · intro h z
    obtain ⟨w,rfl⟩ := (parityFullProbeAuxEquiv434 SG m nu).surjective z
    simpa only [parity_full_probe_aux_lift_apply434,parity_full_probe_aux_prime_sets434] using h w


/-- Exact transport of the complete true auxiliary expectation, for an
arbitrary coupled integrand. All repeated draws are retained, and no
endpoint independence or factorization of the integrand is assumed. -/
theorem parity_full_probe_weighted_assignment_sum434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (F : (SourceOriginalProbeAuxIndex434 m (parityFullProbePattern434 SG m nu) → ℕ) → ℂ) :
    (∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m
        (parityFullProbePattern434 SG m nu) (Sum.elim Ps Pb)),
      (sourceSharedLaw434
        (fun z => sourcePrimeSharedAtom434
          (sourceOriginalProbeAuxV434 m (parityFullProbePattern434 SG m nu) (Sum.elim Vs Vb) z))
        a : ℂ)*F a) =
    (∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu Pb),
      (sourceSharedLaw434
        (fun z => sourcePrimeSharedAtom434 (sourceOriginalProbeAuxV434 m nu Vb z)) a : ℂ)*
      F (parityFullProbeAuxLift434 SG m nu a)) := by
  symm
  refine Finset.sum_bij (fun a _ => parityFullProbeAuxLift434 SG m nu a) ?_ ?_ ?_ ?_
  · intro a ha
    exact (parity_full_probe_aux_membership434 m nu Ps Pb a).mpr ha
  · intro a ha b hb hab
    funext z
    have hz := congrFun hab (parityFullProbeAuxEquiv434 SG m nu z)
    simpa only [parity_full_probe_aux_lift_apply434] using hz
  · intro b hb
    let a : SourceOriginalProbeAuxIndex434 m nu → ℕ :=
      fun z => b (parityFullProbeAuxEquiv434 SG m nu z)
    have he : parityFullProbeAuxLift434 SG m nu a=b := by
      funext z
      dsimp only [parityFullProbeAuxLift434,a]
      rw [Equiv.apply_symm_apply]
    refine ⟨a,?_,he⟩
    apply (parity_full_probe_aux_membership434 m nu Ps Pb a).mp
    rw [he]
    exact hb
  · intro a ha
    rw [parity_full_probe_aux_law434]

@[simp] theorem parity_full_probe_DA434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    sourceOriginalProbeDA434 m (parityFullProbePattern434 SG m nu)
      (parityFullProbeAuxLift434 SG m nu a)=sourceOriginalProbeDA434 m nu a := by
  unfold sourceOriginalProbeDA434
  symm
  apply Fintype.prod_equiv (parityProbeSelectionEquiv434 SG m nu.1)
  intro z
  exact (parity_full_probe_aux_lift_apply434 m nu a (Sum.inl z)).symm

@[simp] theorem parity_full_probe_DB434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    sourceOriginalProbeDB434 m (parityFullProbePattern434 SG m nu)
      (parityFullProbeAuxLift434 SG m nu a)=sourceOriginalProbeDB434 m nu a := by
  unfold sourceOriginalProbeDB434
  symm
  apply Fintype.prod_equiv (parityProbeSelectionEquiv434 SG m nu.2)
  intro z
  exact (parity_full_probe_aux_lift_apply434 m nu a (Sum.inr z)).symm

@[simp] theorem parity_full_probe_target_X434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (s : SG → Fin (J+ell) → ℕ) (b : BG → Fin (J+ell) → ℕ) :
    sourceOriginalProbeOriginalTargetX434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      (Sum.elim s b)=sourceOriginalProbeOriginalTargetX434 J ell m hmJ nu b := by
  exact (Equiv.prod_comp (parityProbeSelectionEquiv434 SG m nu.1)
    (fun z => (Sum.elim s b) z.val.1 ((z.val.2.castLE hmJ).castAdd ell))).symm

@[simp] theorem parity_full_probe_source_X434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (s : SG → Fin (J+ell) → ℕ) (b : BG → Fin (J+ell) → ℕ) :
    sourceOriginalProbeOriginalSourceX434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      (Sum.elim s b)=sourceOriginalProbeOriginalSourceX434 J ell m hmJ nu b := by
  exact (Equiv.prod_comp (parityProbeSelectionEquiv434 SG m nu.2)
    (fun z => (Sum.elim s b) z.val.1 ((z.val.2.castLE hmJ).castAdd ell))).symm

/-- Source cell probabilities are invariant under an explicit coordinate
bijection, proved by reindexing the complete finite assignment sum and its
complete labelled products. No independence or product-law premise is used. -/
theorem parity_actual_cell_probability_equiv434
    {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (e : I ≃ K) (S : K → Finset ℕ) (mu : K → ℕ → ℝ) (h : ℝ) (j : ℤ) :
    sourceOriginalActualCellProbability434 S mu h j =
    sourceOriginalActualCellProbability434 (fun i => S (e i)) (fun i => mu (e i)) h j := by
  unfold sourceOriginalActualCellProbability434
  refine Finset.sum_bij (fun a _ => fun i => a (e i)) ?_ ?_ ?_ ?_
  · intro a ha
    exact Fintype.mem_piFinset.mpr fun i => (Fintype.mem_piFinset.mp ha) (e i)
  · intro a ha b hb hab
    funext k
    obtain ⟨i,rfl⟩ := e.surjective k
    exact congrFun hab i
  · intro b hb
    refine ⟨fun k => b (e.symm k),?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro k
      simpa only [e.apply_symm_apply] using (Fintype.mem_piFinset.mp hb) (e.symm k)
    · funext i
      simp only [e.symm_apply_apply]
  · intro a ha
    have hprod : (∏ i : I, a (e i))=∏ k : K,a k := Equiv.prod_comp e a
    have hmass : sourceSharedLaw434 (fun i => mu (e i)) (fun i => a (e i)) =
        sourceSharedLaw434 mu a := Equiv.prod_comp e (fun k => mu k (a k))
    rw [hprod,hmass]

theorem parity_actual_candidate_cells_equiv434
    {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (e : I ≃ K) (S : K → Finset ℕ) (h : ℝ) :
    sourceOriginalCandidateLogCells434 S h =
    sourceOriginalCandidateLogCells434 (fun i => S (e i)) h := by
  ext j
  simp only [sourceOriginalCandidateLogCells434,Finset.mem_image]
  constructor
  · rintro ⟨a,ha,hj⟩
    refine ⟨fun i => a (e i),?_,?_⟩
    · exact Fintype.mem_piFinset.mpr fun i => (Fintype.mem_piFinset.mp ha) (e i)
    · simpa only [Equiv.prod_comp e a] using hj
  · rintro ⟨b,hb,hj⟩
    refine ⟨fun k => b (e.symm k),?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro k
      simpa only [e.apply_symm_apply] using (Fintype.mem_piFinset.mp hb) (e.symm k)
    · simpa only [Equiv.prod_comp e.symm b] using hj

theorem parity_actual_active_cells_equiv434
    {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (e : I ≃ K) (S : K → Finset ℕ) (mu : K → ℕ → ℝ) (h xi : ℝ) :
    sourceOriginalFiniteActiveLogCells434 S mu h xi =
    sourceOriginalFiniteActiveLogCells434 (fun i => S (e i)) (fun i => mu (e i)) h xi := by
  unfold sourceOriginalFiniteActiveLogCells434
  rw [parity_actual_candidate_cells_equiv434 e S h]
  apply Finset.filter_congr
  intro j hj
  rw [parity_actual_cell_probability_equiv434 e S mu h j]

/-- The A-cell mass is the literal original mass after full-group lifting. -/
@[simp] theorem parity_full_probe_cell_A434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (h : ℝ) (j : ℤ) :
    sourceOriginalProbeCellA434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbePattern434 SG m nu) h j =
    sourceOriginalProbeCellA434 m Pb Vb nu h j := by
  exact parity_actual_cell_probability_equiv434 (parityProbeSelectionEquiv434 SG m nu.1)
    (fun z => (Sum.elim Ps Pb) z.val.1)
    (fun z => sourcePrimeSharedAtom434 ((Sum.elim Vs Vb) z.val.1)) h j

@[simp] theorem parity_full_probe_cell_B434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (h : ℝ) (j : ℤ) :
    sourceOriginalProbeCellB434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbePattern434 SG m nu) h j =
    sourceOriginalProbeCellB434 m Pb Vb nu h j := by
  exact parity_actual_cell_probability_equiv434 (parityProbeSelectionEquiv434 SG m nu.2)
    (fun z => (Sum.elim Ps Pb) z.val.1)
    (fun z => sourcePrimeSharedAtom434 ((Sum.elim Vs Vb) z.val.1)) h j

@[simp] theorem parity_full_probe_active_A434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (h xi : ℝ) :
    sourceOriginalProbeActiveCellsA434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbePattern434 SG m nu) h xi =
    sourceOriginalProbeActiveCellsA434 m Pb Vb nu h xi := by
  exact parity_actual_active_cells_equiv434 (parityProbeSelectionEquiv434 SG m nu.1)
    (fun z => (Sum.elim Ps Pb) z.val.1)
    (fun z => sourcePrimeSharedAtom434 ((Sum.elim Vs Vb) z.val.1)) h xi

@[simp] theorem parity_full_probe_active_B434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (h xi : ℝ) :
    sourceOriginalProbeActiveCellsB434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbePattern434 SG m nu) h xi =
    sourceOriginalProbeActiveCellsB434 m Pb Vb nu h xi := by
  exact parity_actual_active_cells_equiv434 (parityProbeSelectionEquiv434 SG m nu.2)
    (fun z => (Sum.elim Ps Pb) z.val.1)
    (fun z => sourcePrimeSharedAtom434 ((Sum.elim Vs Vb) z.val.1)) h xi

/-- BOTH reciprocal cell masses remain in the exact kernel coefficient. -/
theorem parity_full_probe_two_inverse_masses434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hA hB : ℝ) (jA jB : ℤ) :
    (sourceOriginalProbeCellA434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbePattern434 SG m nu) hA jA : ℂ)⁻¹ *
    (sourceOriginalProbeCellB434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbePattern434 SG m nu) hB jB : ℂ)⁻¹ =
    (sourceOriginalProbeCellA434 m Pb Vb nu hA jA : ℂ)⁻¹ *
    (sourceOriginalProbeCellB434 m Pb Vb nu hB jB : ℂ)⁻¹ := by
  rw [parity_full_probe_cell_A434,parity_full_probe_cell_B434]

/-- The original full auxiliary endpoint ban ignores no BIG marked slot
and imposes no added SMALL ban: every selected coordinate lies in BIG. -/
theorem parity_full_probe_aux_ban434
    (M m : ℕ) (nu : SourceOriginalProbePattern434 BG m)
    (ss st : SG → Fin M → ℕ) (bs bt : BG → Fin M → ℕ)
    (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    sourceOriginalProbeAuxEndpointBan434 M m (parityFullProbePattern434 SG m nu)
      (Sum.elim ss bs) (Sum.elim st bt) (parityFullProbeAuxLift434 SG m nu a) ↔
    sourceOriginalProbeAuxEndpointBan434 M m nu bs bt a := by
  constructor
  · intro h z i
    have hz := h (parityFullProbeAuxEquiv434 SG m nu z) i
    simpa only [parity_full_probe_aux_lift_apply434,parity_full_probe_aux_group434,Sum.elim_inr] using hz
  · intro h z i
    obtain ⟨w,rfl⟩ := (parityFullProbeAuxEquiv434 SG m nu).surjective z
    simpa only [parity_full_probe_aux_lift_apply434,parity_full_probe_aux_group434,Sum.elim_inr] using h w i

/-- Exact equality of the full physical B574 canonical Knu under the
SMALL+BIG lift. Both true active cell families, both reciprocal masses,
all primitive characters, DA, DB, original physical XA/XB, inclusion-
exclusion sign, and the original full auxiliary ban are retained. -/
theorem parity_full_probe_canonical_physical_kernel434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (Q : ℕ) (hA hB xi : ℝ)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (ss st : SG → Fin (J+ell) → ℕ) (bs bt : BG → Fin (J+ell) → ℕ) :
    sourceB574CanonicalFullKernel434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      Q hA hB xi (Sum.elim Ps Pb) (Sum.elim Vs Vb)
      (parityFullProbeAuxLift434 SG m nu a) (Sum.elim ss bs) (Sum.elim st bt) =
    sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi Pb Vb a bs bt := by
  have hmassA :
      sourceOriginalProbeCellA434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
        (parityFullProbePattern434 SG m nu) hA =
      sourceOriginalProbeCellA434 m Pb Vb nu hA := by
    funext j
    exact parity_full_probe_cell_A434 m nu Ps Pb Vs Vb hA j
  have hmassB :
      sourceOriginalProbeCellB434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
        (parityFullProbePattern434 SG m nu) hB =
      sourceOriginalProbeCellB434 m Pb Vb nu hB := by
    funext j
    exact parity_full_probe_cell_B434 m nu Ps Pb Vs Vb hB j
  unfold sourceB574CanonicalFullKernel434
  rw [parity_full_probe_aux_ban434,parity_full_probe_active_A434,parity_full_probe_active_B434,
    hmassA,hmassB,parity_full_probe_DA434,parity_full_probe_DB434,
    parity_full_probe_target_X434,parity_full_probe_source_X434]
  simp only [parityFullProbePattern434,Finset.card_map]


/-- Original block indices are lifted through the same injective group map. -/
def parityFullProbeBlock434 (SG : Type) {BG : Type} (block : Finset BG) : Finset (SG ⊕ BG) :=
  block.map ⟨Sum.inr,Sum.inr_injective⟩

theorem parity_full_probe_block434 (block : Finset BG) (m : ℕ) :
    sourceOriginalProbeBlock434 (parityFullProbeBlock434 SG block) m =
      (sourceOriginalProbeBlock434 block m).map (parityProbeInrEmbedding434 SG BG m) := by
  ext z
  rcases z with ⟨g,j⟩
  cases g with
  | inl g =>
    simp only [parity_probe_map_mem_inl434,sourceOriginalProbeBlock434]
    simp [parityFullProbeBlock434]
  | inr g =>
    simp only [parity_probe_map_mem_inr434,sourceOriginalProbeBlock434]
    simp [parityFullProbeBlock434]

/-- The actual nonempty two-block comparison family is preserved exactly,
not replaced by a family with extra SMALL probes or empty comparisons. -/
theorem parity_full_probe_family_membership434
    (blockA blockB : Finset BG) (m : ℕ) (nu : SourceOriginalProbePattern434 BG m) :
    parityFullProbePattern434 SG m nu ∈
      sourceOriginalTwoBlockProbePatterns434
        (parityFullProbeBlock434 SG blockA) (parityFullProbeBlock434 SG blockB) m ↔
    nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m := by
  rw [source_original_two_block_probe_pattern_mem434,
    source_original_two_block_probe_pattern_mem434]
  simp only [parityFullProbePattern434,parity_full_probe_block434,
    Finset.map_nonempty,Finset.map_subset_map]

theorem parity_full_probe_disjoint434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m) :
    Disjoint (parityFullProbePattern434 SG m nu).1 (parityFullProbePattern434 SG m nu).2 ↔
      Disjoint nu.1 nu.2 :=
  Finset.disjoint_map (parityProbeInrEmbedding434 SG BG m)

theorem parity_full_probe_cardinalities434
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m) :
    (parityFullProbePattern434 SG m nu).1.card=nu.1.card ∧
    (parityFullProbePattern434 SG m nu).2.card=nu.2.card := by
  simp only [parityFullProbePattern434,Finset.card_map,and_self]
end Green64Analytic.CorrelationSquare


namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The combined r20 carrier is literally the full original actual P
family under its established group equivalence. No band or prime is changed. -/
theorem parity_actual_combined_prime_family434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) :
    b645ActualBand434 L hS =
      fun g => sourceOriginalPAllActualBands 20 L
        (sourceNativeOriginalFullEquiv434 20 L hS hL g) := by
  funext g
  rcases g with g | g
  · cases g <;> rfl
  · rfl

/-- At the actual Parity value ell=1 every SMALL group retains exactly one
free endpoint mark and J shared marks, including the distinguished group. -/
theorem parity_actual_full_probe_small_counts434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (g : SourceNativeMemorySG434 20 L hS) :
    sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) (Sum.inl g)=1 ∧
    (sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) (Sum.inl g)).card=J :=
  ⟨parity_full_probe_free_count_small434 J 1 m hmJ nu g,
   parity_full_probe_shared_count_small434 J 1 m hmJ nu g⟩

/-- Literal r20 Parity specialization of the full physical canonical Knu
lift, with the actual SMALL/BIG prime families and genuine masses. -/
theorem parity_actual_full_probe_canonical_physical_kernel434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi : ℝ)
    (a : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (ss st : SourceNativeMemorySG434 20 L hS → Fin (J+1) → ℕ)
    (bs bt : sourceNativeOriginalBigType434 20 L → Fin (J+1) → ℕ) :
    sourceB574CanonicalFullKernel434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
      Q hA hB xi (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu a)
      (Sum.elim ss bs) (Sum.elim st bt) =
    sourceB574CanonicalFullKernel434 J 1 m hmJ nu Q hA hB xi
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) a bs bt :=
  parity_full_probe_canonical_physical_kernel434 J 1 m hmJ nu Q hA hB xi
    (SourceNativeMemorySmallSet434 20 L hS) (sourceNativeOriginalTb434 20 L)
    (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    a ss st bs bt
end Green64Analytic.SourceBlockSieve

end

end

/-! ## PhysicalSharedFree -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 24000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell : ℕ)

/-- Every original physical state is exactly one physical integer and its
complete SMALL/BIG ordered divisor marks. No residue average or fibre-count
normalization is introduced. -/
def parityPhysicalPositionMarksEquiv434 (positions : Finset ℤ) :
    B650IntegerPhysicalState434 SP sm BP bm J ell positions ≃
      (n : positions) × B650IntegerMarks434 SP sm BP bm J ell n.val where
  toFun x := ⟨x.val.1,
    b650IntegerStateMarksEquiv434 SP sm BP bm J ell x.val.1.val
      ⟨x.val.2,x.property⟩⟩
  invFun z :=
    let s := (b650IntegerStateMarksEquiv434 SP sm BP bm J ell z.1.val).symm z.2
    ⟨(z.1,s.val),s.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((b650IntegerStateMarksEquiv434 SP sm BP bm J ell x.val.1.val).symm_apply_apply
          ⟨x.val.2,x.property⟩)
  right_inv z := by
    apply Sigma.ext rfl
    exact heq_of_eq
      ((b650IntegerStateMarksEquiv434 SP sm BP bm J ell z.1.val).apply_symm_apply z.2)

/-- Literal finite weighted reindex of the whole physical carrier. The
unchanged physical mass mu0 occurs exactly once on each side. -/
theorem parity_physical_position_marks_weighted_sum434
    (positions : Finset ℤ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (F : B650IntegerPhysicalState434 SP sm BP bm J ell positions → ℂ) :
    (∑ x, (b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig : ℂ)*F x) =
      ∑ n : positions, ∑ marks : B650IntegerMarks434 SP sm BP bm J ell n.val,
        (b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig : ℂ)*
          F ((parityPhysicalPositionMarksEquiv434 SP sm BP bm J ell positions).symm
            ⟨n,marks⟩) := by
  let e := parityPhysicalPositionMarksEquiv434 SP sm BP bm J ell positions
  have h := Fintype.sum_equiv e
    (fun x => (b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig : ℂ)*F x)
    (fun z => (b650IntegerStateMass434 (SG:=SG) (BG:=BG) J ell Vsmall Vbig : ℂ)*F (e.symm z))
    (fun x => by rw [e.symm_apply_apply])
  exact h.trans (Fintype.sum_sigma _)

/-- Reorder all original endpoint marks using the given independent SMALL
and BIG permutation families. Divisibility and ordered injectivity are exact. -/
def parityIntegerMarksPermutationEquiv434 (n : ℤ)
    (ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (sb : BigGroupPerm (BG:=BG) (J+ell)) :
    B650IntegerMarks434 SP sm BP bm J ell n ≃
      B650IntegerMarks434 SP sm BP bm J ell n where
  toFun x :=
    ((fun g => ⟨fun i => (x.1 g).val (ss g i),
      (x.1 g).property.1.comp (ss g).injective,
      fun i => (x.1 g).property.2 (ss g i)⟩),
     (fun g => ⟨fun i => (x.2 g).val (sb g i),
      (x.2 g).property.1.comp (sb g).injective,
      fun i => (x.2 g).property.2 (sb g i)⟩))
  invFun x :=
    ((fun g => ⟨fun i => (x.1 g).val ((ss g).symm i),
      (x.1 g).property.1.comp (ss g).symm.injective,
      fun i => (x.1 g).property.2 ((ss g).symm i)⟩),
     (fun g => ⟨fun i => (x.2 g).val ((sb g).symm i),
      (x.2 g).property.1.comp (sb g).symm.injective,
      fun i => (x.2 g).property.2 ((sb g).symm i)⟩))
  left_inv x := by
    apply Prod.ext
    · funext g
      apply Subtype.ext
      funext i
      exact congrArg (x.1 g).val ((ss g).apply_symm_apply i)
    · funext g
      apply Subtype.ext
      funext i
      exact congrArg (x.2 g).val ((sb g).apply_symm_apply i)
  right_inv x := by
    apply Prod.ext
    · funext g
      apply Subtype.ext
      funext i
      exact congrArg (x.1 g).val ((ss g).symm_apply_apply i)
    · funext g
      apply Subtype.ext
      funext i
      exact congrArg (x.2 g).val ((sb g).symm_apply_apply i)

/-- A true permutation bijection of the SAME finite physical carrier,
including every residue constraint. Position is fixed literally. -/
def parityPhysicalMarkPermutationEquiv434 (positions : Finset ℤ)
    (ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (sb : BigGroupPerm (BG:=BG) (J+ell)) :
    B650IntegerPhysicalState434 SP sm BP bm J ell positions ≃
      B650IntegerPhysicalState434 SP sm BP bm J ell positions :=
  (parityPhysicalPositionMarksEquiv434 SP sm BP bm J ell positions).trans
    ((Equiv.sigmaCongrRight fun n : positions =>
      parityIntegerMarksPermutationEquiv434 SP sm BP bm J ell n.val ss sb).trans
        (parityPhysicalPositionMarksEquiv434 SP sm BP bm J ell positions).symm)

theorem parity_physical_mark_permutation_position434
    (positions : Finset ℤ)
    (ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (sb : BigGroupPerm (BG:=BG) (J+ell))
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    (parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions ss sb x).val.1 = x.val.1 := rfl

theorem parity_physical_mark_permutation_small434
    (positions : Finset ℤ)
    (ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (sb : BigGroupPerm (BG:=BG) (J+ell))
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions) (g : SG) (i : Fin (J+ell)) :
    Green64SmallHaar.marks (sm g) (J+ell)
      ((parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions ss sb x).val.2.1 g) i =
      Green64SmallHaar.marks (sm g) (J+ell) (x.val.2.1 g) (ss g i) := rfl

theorem parity_physical_mark_permutation_big434
    (positions : Finset ℤ)
    (ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (sb : BigGroupPerm (BG:=BG) (J+ell))
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions) (g : BG) (i : Fin (J+ell)) :
    Green64SmallHaar.marks (bm g) (J+ell)
      ((parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions ss sb x).val.2.2 g) i =
      Green64SmallHaar.marks (bm g) (J+ell) (x.val.2.2 g) (sb g i) := rfl

theorem parity_physical_mark_permutation_small_damping434
    (positions : Finset ℤ)
    (ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (sb : BigGroupPerm (BG:=BG) (J+ell))
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions) (q : ℝ) (g : SG) :
    Green64SmallHaar.endpointDamping (sm g) (J+ell) q
      ((parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions ss sb x).val.2.1 g) =
      Green64SmallHaar.endpointDamping (sm g) (J+ell) q (x.val.2.1 g) := by
  unfold Green64SmallHaar.endpointDamping
  congr 2
  congr 1
  funext p
  exact (x.property.1 g p).symm

theorem parity_physical_mark_permutation_big_damping434
    (positions : Finset ℤ)
    (ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (sb : BigGroupPerm (BG:=BG) (J+ell))
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions) (q : ℝ) (g : BG) :
    Green64SmallHaar.endpointDamping (bm g) (J+ell) q
      ((parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions ss sb x).val.2.2 g) =
      Green64SmallHaar.endpointDamping (bm g) (J+ell) q (x.val.2.2 g) := by
  unfold Green64SmallHaar.endpointDamping
  congr 2
  congr 1
  funext p
  exact (x.property.2 g p).symm

/-- The literal auxiliary ban is invariant under reordering complete marked
lists. This is the original mark-exclusion guard, not an auxiliary-divisibility
guard and not a clean-event assumption. -/
theorem parity_physical_mark_permutation_aux_ban434
    (positions : Finset ℤ) (m : ℕ) (pat : SourcePattern BG J m)
    (aux : SourceBigAux BP J m pat)
    (ss ts : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (sb tb : BigGroupPerm (BG:=BG) (J+ell))
    (x y : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    memoryIndependentAuxBan SP sm BP bm J ell m pat aux
      (parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions ss sb x).val.2
      (parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions ts tb y).val.2 ↔
    memoryIndependentAuxBan SP sm BP bm J ell m pat aux x.val.2 y.val.2 := by
  change (∀ g j i,
      aux g j ≠ Green64SmallHaar.marks (bm g) (J+ell) (x.val.2.2 g) (sb g i) ∧
      aux g j ≠ Green64SmallHaar.marks (bm g) (J+ell) (y.val.2.2 g) (tb g i)) ↔ _
  constructor
  · intro h g j i
    constructor
    · simpa only [Equiv.apply_symm_apply] using (h g j ((sb g).symm i)).1
    · simpa only [Equiv.apply_symm_apply] using (h g j ((tb g).symm i)).2
  · intro h g j i
    exact ⟨(h g j (sb g i)).1,(h g j (tb g i)).2⟩

variable (m : ℕ) {Nu : Type} [Fintype Nu]
variable (patterns : Nu → SourcePattern BG J m)

/-- Keep exactly the original pattern and auxiliary assignment while setting
all four endpoint permutation families to identity. Their probability laws
remain in the native scalar and are not silently divided out. -/
def parityFrameIdentityPermutations434
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns :=
  (f.1,(fun _ => Equiv.refl _),(fun _ => Equiv.refl _),
    (fun _ => Equiv.refl _),(fun _ => Equiv.refl _))

def parityPhysicalFrameSourceReindex434 (positions : Finset ℤ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    B650IntegerPhysicalState434 SP sm BP bm J ell positions ≃
      B650IntegerPhysicalState434 SP sm BP bm J ell positions :=
  parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions f.2.2.2.1 f.2.1

def parityPhysicalFrameTargetReindex434 (positions : Finset ℤ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    B650IntegerPhysicalState434 SP sm BP bm J ell positions ≃
      B650IntegerPhysicalState434 SP sm BP bm J ell positions :=
  parityPhysicalMarkPermutationEquiv434 SP sm BP bm J ell positions f.2.2.2.2 f.2.2.1

/-- The full original divisor, including repeated auxiliary values, is exactly
preserved after the physical carrier absorbs the source permutations. -/
theorem parity_frame_source_reindex_D434
    (positions : Finset ℤ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (x : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    b650NativeFrameD434 SP sm BP bm J ell m patterns
      (parityPhysicalFrameSourceReindex434 SP sm BP bm J ell m patterns positions f x).val.2
      (parityFrameIdentityPermutations434 (SG:=SG) BP J ell m patterns f) =
    b650NativeFrameD434 SP sm BP bm J ell m patterns x.val.2 f := rfl

theorem parity_frame_reindex_shared_guard434
    (positions : Finset ℤ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (x y : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    b650NativeFrameShares434 SP sm BP bm J ell m patterns
      (parityPhysicalFrameSourceReindex434 SP sm BP bm J ell m patterns positions f x).val.2
      (parityPhysicalFrameTargetReindex434 SP sm BP bm J ell m patterns positions f y).val.2
      (parityFrameIdentityPermutations434 (SG:=SG) BP J ell m patterns f) ↔
    b650NativeFrameShares434 SP sm BP bm J ell m patterns x.val.2 y.val.2 f := Iff.rfl

theorem parity_frame_reindex_aux_ban434
    (positions : Finset ℤ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (x y : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    memoryIndependentAuxBan SP sm BP bm J ell m (patterns f.1.1) f.1.2
      (parityPhysicalFrameSourceReindex434 SP sm BP bm J ell m patterns positions f x).val.2
      (parityPhysicalFrameTargetReindex434 SP sm BP bm J ell m patterns positions f y).val.2 ↔
    memoryIndependentAuxBan SP sm BP bm J ell m (patterns f.1.1) f.1.2 x.val.2 y.val.2 :=
  parity_physical_mark_permutation_aux_ban434 SP sm BP bm J ell positions m
    (patterns f.1.1) f.1.2 f.2.2.2.1 f.2.2.2.2 f.2.1 f.2.2.1 x y

/-- All source real factors are retained: the auxiliary law, both complete
permutation-pair laws, target V powers, and both endpoint half dampings. -/
theorem parity_frame_reindex_real_weight434
    (positions : Finset ℤ) (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (x y : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    b650NativeRealFrameWeight434 SP sm BP bm J ell m patterns q Vsmall Vbig
      (parityPhysicalFrameSourceReindex434 SP sm BP bm J ell m patterns positions f x).val.2
      (parityPhysicalFrameTargetReindex434 SP sm BP bm J ell m patterns positions f y).val.2
      (parityFrameIdentityPermutations434 (SG:=SG) BP J ell m patterns f) =
    b650NativeRealFrameWeight434 SP sm BP bm J ell m patterns q Vsmall Vbig x.val.2 y.val.2 f := by
  unfold b650NativeRealFrameWeight434 parityFrameIdentityPermutations434
  dsimp only
  simp only [parityPhysicalFrameSourceReindex434,parityPhysicalFrameTargetReindex434,
    parity_physical_mark_permutation_small_damping434,
    parity_physical_mark_permutation_big_damping434]

/-- Exact equivalence of the original physical frame guard, with the same
signed step o*k*D, shared marks and auxiliary endpoint ban. -/
theorem parity_frame_reindex_allowed434
    (positions : Finset ℤ) (o k : ℤ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (x y : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    b650IntegerFrameAllowed434 SP sm BP bm J ell m patterns positions o k
      (parityPhysicalFrameSourceReindex434 SP sm BP bm J ell m patterns positions f x)
      (parityPhysicalFrameTargetReindex434 SP sm BP bm J ell m patterns positions f y)
      (parityFrameIdentityPermutations434 (SG:=SG) BP J ell m patterns f) ↔
    b650IntegerFrameAllowed434 SP sm BP bm J ell m patterns positions o k x y f := by
  unfold b650IntegerFrameAllowed434
  change (o = 1 ∨ o = -1) ∧ k ≠ 0 ∧
    memoryIndependentAuxBan SP sm BP bm J ell m (patterns f.1.1) f.1.2
      ((parityPhysicalFrameSourceReindex434 SP sm BP bm J ell m patterns positions f x).val.2)
      ((parityPhysicalFrameTargetReindex434 SP sm BP bm J ell m patterns positions f y).val.2) ∧ _ ↔ _
  rw [parity_frame_reindex_aux_ban434,parity_frame_reindex_shared_guard434,
    parity_frame_source_reindex_D434]
  rfl

/-- Source-exact conjugacy of the actual full frame scalar under its four
endpoint mark permutations. The original Knu, phase and all real laws remain. -/
theorem parity_frame_reindex_scalar434
    (positions : Finset ℤ) (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (x y : B650IntegerPhysicalState434 SP sm BP bm J ell positions) :
    b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k
      (parityPhysicalFrameSourceReindex434 SP sm BP bm J ell m patterns positions f x)
      (parityPhysicalFrameTargetReindex434 SP sm BP bm J ell m patterns positions f y)
      (parityFrameIdentityPermutations434 (SG:=SG) BP J ell m patterns f) =
    b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k x y f := by
  simp only [b650IntegerFrameScalar434,parity_frame_reindex_allowed434,
    parity_frame_reindex_real_weight434,parity_frame_source_reindex_D434]
  rfl

/-- Exact physical pair-sum reindex for one complete frame and every literal
position/divisor test. Original harmonic coefficients, parity, source cutoff,
mu0 and all other position factors can be supplied as that test; no norm or
cancellation premise, clean event, or multiplicity correction appears. -/
theorem parity_frame_physical_pair_sum_identity_permutations434
    (positions : Finset ℤ) (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (test : ℤ → ℤ → ℕ → ℂ) :
    (∑ x : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      ∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
        test x.val.1.val y.val.1.val
          (b650NativeFrameD434 SP sm BP bm J ell m patterns x.val.2 f)*
        b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k x y f) =
    ∑ x : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      ∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
        test x.val.1.val y.val.1.val
          (b650NativeFrameD434 SP sm BP bm J ell m patterns x.val.2
            (parityFrameIdentityPermutations434 (SG:=SG) BP J ell m patterns f))*
        b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k x y
          (parityFrameIdentityPermutations434 (SG:=SG) BP J ell m patterns f) := by
  apply Fintype.sum_equiv (parityPhysicalFrameSourceReindex434 SP sm BP bm J ell m patterns positions f)
  intro x
  apply Fintype.sum_equiv (parityPhysicalFrameTargetReindex434 SP sm BP bm J ell m patterns positions f)
  intro y
  rw [parity_frame_reindex_scalar434,parity_frame_source_reindex_D434]
  rfl



/-- The same nu and auxiliary draw with all four endpoint permutations equal
 to the identity. This only packages the literal full frame carrier. -/
def parityBaseIdentityFrame434
    (a : (nu : Nu) × SourceBigAux BP J m (patterns nu)) :
    MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns :=
  (a,(fun _ => Equiv.refl _),(fun _ => Equiv.refl _),
    (fun _ => Equiv.refl _),(fun _ => Equiv.refl _))

/-- The literal physical frame scalar after summing its four uniform
 permutation laws. All auxiliary laws, unshared masses, endpoint dampings,
 shared and auxiliary guards, D, original phase and Knu remain present. -/
def parityPermutationMarginalScalar434
    (positions : Finset ℤ) (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (x y : B650IntegerPhysicalState434 SP sm BP bm J ell positions)
    (a : (nu : Nu) × SourceBigAux BP J m (patterns nu)) : ℂ :=
  let f := parityBaseIdentityFrame434 (SG:=SG) BP J ell m patterns a
  if b650IntegerFrameAllowed434 SP sm BP bm J ell m patterns positions o k x y f then
    ((sourceAuxMass BP bm J m Vbig (patterns a.1) a.2 *
      (∏ g : BG, 1/(Vbig g)^Green64SmallHaar.unsharedSlots (J+ell)
        (sourceBigShared J ell m (patterns a.1) g)) *
      (∏ g : SG, 1/(Vsmall g)^Green64SmallHaar.unsharedSlots (J+ell)
        (sourceSmallShared J ell g)) *
      (∏ g : SG, Green64SmallHaar.endpointDamping (sm g) (J+ell) q (x.val.2.1 g) *
        Green64SmallHaar.endpointDamping (sm g) (J+ell) q (y.val.2.1 g)) *
      (∏ g : BG, Green64SmallHaar.endpointDamping (bm g) (J+ell) q (x.val.2.2 g) *
        Green64SmallHaar.endpointDamping (bm g) (J+ell) q (y.val.2.2 g)) : ℝ) : ℂ) *
    originalEdgeScalar
      (memoryOrientationK BP J ell m patterns Knu o a.1 a.2
        (fun g j => Green64SmallHaar.marks (bm g) (J+ell) (x.val.2.2 g) j)
        (fun g j => Green64SmallHaar.marks (bm g) (J+ell) (y.val.2.2 g) j))
      zeta 0 (b650NativeFrameD434 SP sm BP bm J ell m patterns x.val.2 f) o k
  else 0

theorem parity_identity_frame_scalar_mass_factor434
    (positions : Finset ℤ) (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (x y : B650IntegerPhysicalState434 SP sm BP bm J ell positions)
    (f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k
      x y (parityFrameIdentityPermutations434 (SG:=SG) BP J ell m patterns f) =
    (bigEndpointPairMass (BG:=BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G:=SG) (J+ell) : ℂ) *
    parityPermutationMarginalScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k
      x y f.1 := by
  unfold b650IntegerFrameScalar434 parityPermutationMarginalScalar434
    parityFrameIdentityPermutations434 parityBaseIdentityFrame434
  dsimp only
  split_ifs
  · simp only [b650NativeRealFrameWeight434,Complex.ofReal_mul,Equiv.refl_apply]
    ring
  · simp

/-- Exact total mass of the four original permutation families, including
 the empty-group cases. No factorial correction is introduced. -/
theorem parity_four_permutation_laws_total434 :
    (∑ _bs : BigGroupPerm (BG:=BG) (J+ell),
      ∑ _bt : BigGroupPerm (BG:=BG) (J+ell),
      ∑ _ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell),
      ∑ _st : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell),
        (bigEndpointPairMass (BG:=BG) (J+ell) : ℂ) *
        (Green64SmallHaar.groupPermutationPairMass (G:=SG) (J+ell) : ℂ)) = 1 := by
  calc
    _ = ((bigEndpointPairMass (BG:=BG) (J+ell) : ℂ) *
        (Fintype.card (BigGroupPerm (BG:=BG) (J+ell)) : ℂ)^2) *
      ((Green64SmallHaar.groupPermutationPairMass (G:=SG) (J+ell) : ℂ) *
        (Fintype.card (Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell)) : ℂ)^2) := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
          ring
    _ = 1 := by
      have hb := bigEndpointPairMass_normalized (BG:=BG) (J+ell)
      have hs := Green64SmallHaar.groupPermutationPairMass_normalized (G:=SG) (J+ell)
      convert congrArg₂ (fun a b : ℂ => a*b) hb hs using 1
      <;> simp

/-- Full finite physical state/frame enumeration after integrating the four
 actual permutation laws. The nu and every auxiliary draw stay explicit.
 The arbitrary literal position/divisor test may carry mu0, both endpoint
 coefficients, parity, harmonic factor and cutoff. -/
theorem parity_complete_physical_frame_sum_permutation_marginal434
    (positions : Finset ℤ) (q : ℝ) (Vsmall : SG → ℝ) (Vbig : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (o k : ℤ)
    (test : ((nu : Nu) × SourceBigAux BP J m (patterns nu)) → ℤ → ℤ → ℕ → ℂ) :
    (∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns,
      ∑ x : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      ∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
        test f.1 x.val.1.val y.val.1.val
          (b650NativeFrameD434 SP sm BP bm J ell m patterns x.val.2 f) *
        b650IntegerFrameScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k x y f) =
    ∑ a : (nu : Nu) × SourceBigAux BP J m (patterns nu),
      ∑ x : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      ∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
        test a x.val.1.val y.val.1.val
          (b650NativeFrameD434 SP sm BP bm J ell m patterns x.val.2
            (parityBaseIdentityFrame434 (SG:=SG) BP J ell m patterns a)) *
        parityPermutationMarginalScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k x y a := by
  classical
  let C := fun a : (nu : Nu) × SourceBigAux BP J m (patterns nu) =>
    ∑ x : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
    ∑ y : B650IntegerPhysicalState434 SP sm BP bm J ell positions,
      test a x.val.1.val y.val.1.val
        (b650NativeFrameD434 SP sm BP bm J ell m patterns x.val.2
          (parityBaseIdentityFrame434 (SG:=SG) BP J ell m patterns a)) *
      parityPermutationMarginalScalar434 SP sm BP bm J ell m patterns positions q Vsmall Vbig Knu zeta o k x y a
  let W : ℂ := (bigEndpointPairMass (BG:=BG) (J+ell) : ℂ) *
    (Green64SmallHaar.groupPermutationPairMass (G:=SG) (J+ell) : ℂ)
  calc
    _ = ∑ f : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns, W * C f.1 := by
      apply Finset.sum_congr rfl
      intro f _
      rw [parity_frame_physical_pair_sum_identity_permutations434]
      simp only [parity_identity_frame_scalar_mass_factor434]
      dsimp only [C,W]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      dsimp only [parityFrameIdentityPermutations434,parityBaseIdentityFrame434]
      ring
    _ = ∑ a : (nu : Nu) × SourceBigAux BP J m (patterns nu), C a := by
      simp only [MemoryPrimitiveEFrame,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      simp only [← Finset.sum_mul]
      change ((∑ _bs : BigGroupPerm (BG:=BG) (J+ell),
        ∑ _bt : BigGroupPerm (BG:=BG) (J+ell),
        ∑ _ss : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell),
        ∑ _st : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell),
          (bigEndpointPairMass (BG:=BG) (J+ell) : ℂ) *
          (Green64SmallHaar.groupPermutationPairMass (G:=SG) (J+ell) : ℂ)) * C a) = C a
      rw [parity_four_permutation_laws_total434,one_mul]
    _ = _ := rfl

end Green64FullPhysicalE

end

end

/-! ## PhysicalSharedFreeFibres -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 24000

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD

variable {G : Type} [Fintype G] [DecidableEq G]

/-- Restrict every original ordered endpoint list to its labelled shared
 slots. The indexing retains group and slot labels, including repeated values. -/
def parityPhysicalSharedRestriction434 (M : ℕ) (E : G → Finset (Fin M))
    (a : G → Fin M → ℕ) : (i : G) × E i → ℕ :=
  fun i => a i.1 i.2

/-- Full original physical ordered lists at a fixed physical position n,
 with specified labelled shared values. This does not impose a clean event. -/
def parityPhysicalCompletionsAt434 (P : G → Finset ℕ) (M : ℕ)
    (E : G → Finset (Fin M)) (s : (i : G) × E i → ℕ) (n : ℕ) :
    Finset (G → Fin M → ℕ) :=
  Fintype.piFinset (fun g => (orderedBigMarks (P g) M n).filter
    (fun a => ∀ i : E g, a i = s ⟨g,i⟩))

theorem parity_physical_completions_restriction_fibre434
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : (i : G) × E i → ℕ) (n : ℕ) :
    parityPhysicalCompletionsAt434 P M E s n =
      (bigMarkLists P (fun _ => M) n).filter
        (fun a => parityPhysicalSharedRestriction434 M E a = s) := by
  classical
  ext a
  constructor
  · intro h
    have ha := Fintype.mem_piFinset.mp h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun g => (Finset.mem_filter.mp (ha g)).1),?_⟩
    funext i
    exact (Finset.mem_filter.mp (ha i.1)).2 i.2
  · intro h
    obtain ⟨ha,hs⟩ := Finset.mem_filter.mp h
    apply Fintype.mem_piFinset.mpr
    intro g
    refine Finset.mem_filter.mpr ⟨(Fintype.mem_piFinset.mp ha) g,?_⟩
    intro i
    exact congrFun hs ⟨g,i⟩

theorem parity_physical_shared_restriction_mem434
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (n : ℕ) (a : G → Fin M → ℕ)
    (ha : a ∈ bigMarkLists P (fun _ => M) n) :
    parityPhysicalSharedRestriction434 M E a ∈
      Fintype.piFinset (fun i : (g : G) × E g => P i.1) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact ((source_ordered_marks_mem434 (P i.1) M n (a i.1)).mp
    ((Fintype.mem_piFinset.mp ha) i.1)).1 i.2 |>.1

/-- The physical shared guard is equality of the two complete labelled
 restrictions, without removing repeated shared draws. -/
theorem parity_physical_shared_guard_restriction434
    (M : ℕ) (E : G → Finset (Fin M)) (a b : G → Fin M → ℕ) :
    (∀ g (i : E g), a g i = b g i) ↔
      parityPhysicalSharedRestriction434 M E a = parityPhysicalSharedRestriction434 M E b := by
  constructor
  · intro h
    funext i
    exact h i.1 i.2
  · intro h g i
    exact congrFun h ⟨g,i⟩

/-- Finite disintegration of a literal equality guard into its two fibres.
 Only the source image membership is needed; target values outside the shared
 carrier cannot contribute to the equality guard. -/
theorem parity_finite_shared_pair_fibre_sum434
    {A B S : Type} [DecidableEq A] [DecidableEq B] [DecidableEq S]
    (as : Finset A) (bs : Finset B) (ss : Finset S)
    (r : A → S) (t : B → S)
    (hr : ∀ a ∈ as, r a ∈ ss) (F : A → B → ℂ) :
    (∑ a ∈ as, ∑ b ∈ bs, if r a = t b then F a b else 0) =
      ∑ s ∈ ss, ∑ a ∈ as with r a = s, ∑ b ∈ bs with t b = s, F a b := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hr]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := (Finset.mem_filter.mp ha).2
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ha',eq_comm]

/-- Exact unrestricted shared-label decomposition of two independently
 defined physical full-list carriers. The original source and target ordered
 divisors, coupled kernel and all repeated shared draws are retained. -/
theorem parity_physical_pair_shared_fibres434
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M)) (n np : ℕ)
    (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) :
    (∑ a ∈ bigMarkLists P (fun _ => M) n,
      ∑ b ∈ bigMarkLists P (fun _ => M) np,
        if ∀ g (i : E g),a g i=b g i then F a b else 0) =
    ∑ s ∈ Fintype.piFinset (fun i : (g : G) × E g => P i.1),
      ∑ a ∈ parityPhysicalCompletionsAt434 P M E s n,
      ∑ b ∈ parityPhysicalCompletionsAt434 P M E s np,F a b := by
  simp only [parity_physical_completions_restriction_fibre434,
    parity_physical_shared_guard_restriction434]
  exact parity_finite_shared_pair_fibre_sum434 _ _ _ _ _
    (fun a ha => parity_physical_shared_restriction_mem434 P M E n a ha) F

/-- At the true labelled shared dilation, the independently defined physical
 position fibre is exactly B574's original full labelled completion carrier. -/
theorem parity_physical_completions_eq_B574434
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : (i : G) × E i → ℕ) (w : ℕ) :
    parityPhysicalCompletionsAt434 P M E s
      (sourceB574SharedDilation434 M E (fun g i => s ⟨g,i⟩)*w) =
    sourceB574LabelledCompletions434 P M E (fun g i => s ⟨g,i⟩) w := rfl

/-- Exact numeric realization of a physical ordered typed mark list at a
 natural physical integer. The only interface is the label/value equivalence;
 the original prime divisibility and injectivity predicates are preserved. -/
def parityTypedOrderedMarksEquiv434
    {Label : Type} (P : Finset ℕ) (modulus : Label → ℕ)
    (e : Label ≃ {p : ℕ // p ∈ P}) (he : ∀ l,(e l).val=modulus l)
    (M n : ℕ) :
    {f : Fin M → Label // Function.Injective f ∧ ∀ i,(modulus (f i) : ℤ) ∣ (n : ℤ)} ≃
      {a : Fin M → ℕ // a ∈ orderedBigMarks P M n} where
  toFun f := ⟨fun i => (e (f.val i)).val, by
    apply (source_ordered_marks_mem434 P M n _).mpr
    constructor
    · intro i
      refine ⟨(e (f.val i)).property,?_⟩
      rw [he]
      exact_mod_cast f.property.2 i
    · intro i j hij
      apply f.property.1
      apply e.injective
      exact Subtype.ext hij⟩
  invFun a := ⟨fun i => e.symm ⟨a.val i,
      ((source_ordered_marks_mem434 P M n a.val).mp a.property).1 i |>.1⟩, by
    constructor
    · intro i j hij
      apply ((source_ordered_marks_mem434 P M n a.val).mp a.property).2
      have h := congrArg (fun l => (e l).val) hij
      simpa only [e.apply_symm_apply] using h
    · intro i
      rw [← he]
      simp only [e.apply_symm_apply]
      exact_mod_cast (((source_ordered_marks_mem434 P M n a.val).mp a.property).1 i).2⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    exact e.symm_apply_apply (f.val i)
  right_inv a := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (e.apply_symm_apply ⟨a.val i,
      ((source_ordered_marks_mem434 P M n a.val).mp a.property).1 i |>.1⟩)

/-- Exact product carrier realization, keeping every original ordered mark
 at every group. This is a bijection, so no fibre cardinality enters a sum. -/
def parityTypedGroupMarksEquiv434
    (P : G → Finset ℕ) (Label : G → Type)
    (modulus : (g : G) → Label g → ℕ)
    (e : ∀ g,Label g ≃ {p : ℕ // p ∈ P g})
    (he : ∀ g l,(e g l).val=modulus g l) (t : G → ℕ) (n : ℕ) :
    ((g : G) → {f : Fin (t g) → Label g //
      Function.Injective f ∧ ∀ i,(modulus g (f i) : ℤ) ∣ (n : ℤ)}) ≃
      (↑(bigMarkLists P t n)) :=
  (Equiv.piCongrRight (fun g => parityTypedOrderedMarksEquiv434 (P g) (modulus g)
    (e g) (he g) (t g) n)).trans
      (sourceFiniteListFamilyEquiv434 (fun g => orderedBigMarks (P g) (t g) n)).symm


/-- Combine the two independently defined SMALL and BIG original numeric
 list carriers by Sum.elim, retaining all group labels and ordered slots. -/
def paritySmallBigNumericMarksEquiv434
    {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (M n : ℕ) :
    (↑(bigMarkLists Ps (fun _ => M) n)) × (↑(bigMarkLists Pb (fun _ => M) n)) ≃
      (↑(bigMarkLists (Sum.elim Ps Pb) (fun _ => M) n)) where
  toFun ab := ⟨Sum.elim ab.1.val ab.2.val,by
    apply Fintype.mem_piFinset.mpr
    intro g
    cases g with
    | inl g => exact (Fintype.mem_piFinset.mp ab.1.property) g
    | inr g => exact (Fintype.mem_piFinset.mp ab.2.property) g⟩
  invFun a :=
    (⟨fun g => a.val (Sum.inl g),Fintype.mem_piFinset.mpr
      (fun g => (Fintype.mem_piFinset.mp a.property) (Sum.inl g))⟩,
     ⟨fun g => a.val (Sum.inr g),Fintype.mem_piFinset.mpr
      (fun g => (Fintype.mem_piFinset.mp a.property) (Sum.inr g))⟩)
  left_inv ab := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv a := by
    apply Subtype.ext
    funext g
    cases g <;> rfl

/-- Full B650 integer-mark fibre to the original SMALL+BIG numeric carrier.
 All injections and physical divisibility conditions are transported by
 genuine equivalences, never by cardinality bounds. -/
def parityIntegerFullNumericMarksEquiv434
    {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]
    (SP : SG → Type) (BP : BG → Type)
    (sm : (g : SG) → SP g → ℕ) (bm : (g : BG) → BP g → ℕ)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ)
    (es : ∀ g,SP g ≃ {p : ℕ // p ∈ Ps g})
    (eb : ∀ g,BP g ≃ {p : ℕ // p ∈ Pb g})
    (hes : ∀ g l,(es g l).val=sm g l)
    (heb : ∀ g l,(eb g l).val=bm g l) (J ell n : ℕ) :
    Green64FullPhysicalE.B650IntegerMarks434 SP sm BP bm J ell (n : ℤ) ≃
      (↑(bigMarkLists (Sum.elim Ps Pb) (fun _ => J+ell) n)) :=
  (Equiv.prodCongr
    (parityTypedGroupMarksEquiv434 Ps SP sm es hes (fun _ => J+ell) n)
    (parityTypedGroupMarksEquiv434 Pb BP bm eb heb (fun _ => J+ell) n)).trans
      (paritySmallBigNumericMarksEquiv434 Ps Pb (J+ell) n)
end Green64Analytic.CorrelationSquare

namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD

/-- Exact r20, ell=1 realization of every physical ordered mark at a fixed
 natural position in the FULL original P family, including distinguished S. -/
def parityActualIntegerNumericMarksEquiv434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n : ℕ) :
    B650IntegerMarks434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 (n : ℤ) ≃
    (↑(bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) n)) :=
  parityIntegerFullNumericMarksEquiv434
    (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L)
    (fun _ p => p.val) (fun _ p => p.val)
    (SourceNativeMemorySmallSet434 20 L hS) (sourceNativeOriginalTb434 20 L)
    (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
    (fun _ _ => rfl) (fun _ _ => rfl) J 1 n

/-- Actual complete physical residue fibre, not only a mark-only surrogate,
 is bijective to the original full ordered divisor list carrier. -/
def parityActualFixedPositionMarksEquiv434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n : ℕ) :
    {x : MemoryIndependentState
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 //
      b650IntegerResidueAt434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 (n : ℤ) x} ≃
    (↑(bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) n)) :=
  (b650IntegerStateMarksEquiv434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 (n : ℤ)).trans
      (parityActualIntegerNumericMarksEquiv434 L hS J n)

/-- The bijection reads the literal original endpoint marks; it does not
 relabel primes, remove multiplicities, or alter residue coordinates. -/
theorem parity_actual_fixed_position_mark_readout434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n : ℕ)
    (x : {x : MemoryIndependentState
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 //
      b650IntegerResidueAt434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 (n : ℤ) x}) :
    (parityActualFixedPositionMarksEquiv434 L hS J n x).val =
    Sum.elim
      (fun g i => (Green64SmallHaar.marks (fun p : SourceNativeMemorySP434 20 L hS g => p.val)
        (J+1) (x.val.1 g) i).val)
      (fun g i => (Green64SmallHaar.marks (fun p : SourceNativeMemoryBP434 20 L g => p.val)
        (J+1) (x.val.2 g) i).val) := rfl

/-- Exact finite weighted reindex at a genuine physical integer. The weight
 may be the entire coupled scalar with all damping, endpoint coefficients,
 auxiliary tests, mu0 and reciprocal shared dilation retained. -/
theorem parity_actual_fixed_position_weighted_reindex434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n : ℕ)
    (F : {x : MemoryIndependentState
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 //
      b650IntegerResidueAt434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 (n : ℤ) x} → ℂ) :
    (∑ x,F x) =
      ∑ a : (↑(bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) n)),
        F ((parityActualFixedPositionMarksEquiv434 L hS J n).symm a) := by
  apply Fintype.sum_equiv (parityActualFixedPositionMarksEquiv434 L hS J n)
  intro x
  rw [Equiv.symm_apply_apply]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## IntervalRestriction -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- An extra interval is imposed AFTER full-cell normalization. The two
cut endpoints are intersected; no mean is recomputed on a partial cell.
The identity includes empty and disjoint intervals. -/
theorem parity_interval_cut_fine_alpha434
    (prime : Bool) (L S gamma : ℝ) (l u a b : ℕ) :
    restrictSequence (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma l u) =
      b629ActualFineAlpha434 prime L S gamma (max a l) (min b u) := by
  funext n
  by_cases h1 : n ∈ Finset.Icc a b
  · by_cases h2 : n ∈ Finset.Icc l u
    · have h3 : n ∈ Finset.Icc (max a l) (min b u) := by
        simp only [Finset.mem_Icc] at h1 h2 ⊢
        omega
      simp only [restrictSequence, h1, ite_true, b629ActualFineAlpha434, h2, h3]
    · have h3 : n ∉ Finset.Icc (max a l) (min b u) := by
        simp only [Finset.mem_Icc] at h1 h2 ⊢
        omega
      simp only [restrictSequence, h1, ite_true, b629ActualFineAlpha434, h2, h3, ite_false]
  · have h3 : n ∉ Finset.Icc (max a l) (min b u) := by
      simp only [Finset.mem_Icc] at h1 ⊢
      omega
    simp only [restrictSequence, h1, ite_false, b629ActualFineAlpha434, h3]

/-- Actual full character/Mellin cancellation survives EVERY additional
interval, uniformly and with exactly the original logarithmic saving.
This is not a statement for an arbitrary finite subset. -/
theorem parity_interval_cut_discrepancy434
    (B S beta gamma : ℝ) (hB : 0 < B) (hS : 2*B < S)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, ∀ (prime : Bool) (l u : ℕ),
      2 ≤ l → u ≤ 2*l → Real.exp (beta*L) ≤ (l:ℝ) →
      (u:ℝ) ≤ Real.exp (2*L) → ∀ a b : ℕ,
      SourceAlphaDiscrepancy L B (Real.exp L)
        (restrictSequence (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma l u)) := by
  filter_upwards [b629_actual_fine_source_discrepancy434 B S beta gamma hB hS hbeta hgamma]
    with L h
  intro prime l u hl hu hlow hhigh a b
  rw [parity_interval_cut_fine_alpha434]
  apply h prime (max a l) (min b u)
  · exact hl.trans (le_max_right a l)
  · exact (min_le_right b u).trans (hu.trans (Nat.mul_le_mul_left 2 (le_max_right a l)))
  · exact hlow.trans (Nat.cast_le.mpr (le_max_right a l))
  · exact (Nat.cast_le.mpr (min_le_right b u)).trans hhigh

/-- The literal native QSkip prime core has precisely this interval-cut
fine coefficient. All Q slots, its factorial residual, character and
Mellin factors remain those of sourceNativePrimeCore. -/
theorem parity_native_interval_alpha434
    (r d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin r)
    (delta : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) band slot).length → ℝ)
    (prime : Bool) (S gamma : ℝ) (l u a b q : ℕ)
    (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ) :
    (sourceNativePrimeCore r d L band slot delta freq (Finset.Icc a b)
      (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1).alpha =
      b629ActualFineAlpha434 prime L S gamma (max a l) (min b u) := by
  exact parity_interval_cut_fine_alpha434 prime L S gamma l u a b

/-- The actual Parity input package, with precision chosen AFTER the desired
saving and BEFORE L and all intervals/QSkip data. Both E-first and Parity
second cores keep the same literal fine alpha. Norm-one and rough support
are discharged together with the all-character, all-interval discrepancy.
In particular q may be the actual extra-mask modulus 2*|k|. -/
theorem parity_native_interval_fine_inputs434
    (B beta gamma : ℝ) (hB : 0 < B) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ S : ℝ, 2*B+3 < S ∧
    ∀ᶠ L : ℝ in atTop, ∀ (prime : Bool) (l u : ℕ),
      2 ≤ l → u ≤ 2*l → Real.exp (beta*L) ≤ (l:ℝ) →
      (u:ℝ) ≤ Real.exp (2*L) →
      ∀ (a b r d : ℕ) (band : Fin (d+1)) (slot : Fin r)
        (delta : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) band slot).length → ℝ)
        (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 xi1 xi2 rho sigma : ℝ),
      let F := sourceNativePrimeCore r d L band slot delta freq (Finset.Icc a b)
        (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
      let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
      F.alpha = b629ActualFineAlpha434 prime L S gamma (max a l) (min b u) ∧
      Ecore.alpha = F.alpha ∧ Gcore.alpha = F.alpha ∧
      SourceAlphaDiscrepancy L B (Real.exp L) F.alpha ∧
      SourceAlphaDiscrepancy L B (Real.exp L) Ecore.alpha ∧
      SourceAlphaDiscrepancy L B (Real.exp L) Gcore.alpha ∧
      (∀ n : ℕ, ‖F.alpha n‖ ≤ 1 ∧
        (F.alpha n ≠ 0 → sourceD20Rough (Real.exp (Real.sqrt L)) n)) := by
  let S : ℝ := 2*B+4
  have hS : 2*B < S := by dsimp [S]; linarith
  have hS0 : 0 < S := by dsimp [S]; linarith
  refine ⟨S, by dsimp [S]; linarith, ?_⟩
  filter_upwards [parity_interval_cut_discrepancy434 B S beta gamma hB hS hbeta hgamma,
    b629_actual_fine_coefficient_and_rough_support434 S beta gamma hS0 hbeta hgamma]
    with L hdisc hcoeff
  intro prime l u hl hu hlow hhigh a b r d band slot delta freq q chi s0 s1 xi1 xi2 rho sigma
  dsimp only
  let F := sourceNativePrimeCore r d L band slot delta freq (Finset.Icc a b)
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  have hd : SourceAlphaDiscrepancy L B (Real.exp L) F.alpha :=
    hdisc prime l u hl hu hlow hhigh a b
  refine ⟨parity_native_interval_alpha434 r d L band slot delta freq prime S gamma l u a b q chi s0 s1,
    rfl, rfl, hd, hd, hd, ?_⟩
  intro n
  change ‖F.alpha n‖ ≤ 1 ∧ (F.alpha n ≠ 0 → _)
  have hc := hcoeff prime l u hlow n
  by_cases hn : n ∈ Finset.Icc a b
  · have he : F.alpha n = b629ActualFineAlpha434 prime L S gamma l u n := by
      simp only [F, sourceNativePrimeCore, restrictSequence, hn, ite_true]
    rw [he]
    refine ⟨hc.1, ?_⟩
    intro hnonzero
    have hmem : n ∈ Finset.Icc l u := by
      by_contra hnot
      exact hnonzero (by simp only [b629ActualFineAlpha434, hnot, ite_false])
    have hn2 : 2 ≤ n := hl.trans (Finset.mem_Icc.mp hmem).1
    have hr := hc.2 hnonzero
    exact ⟨hn2, hr n.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)⟩
  · have he : F.alpha n = 0 := by
      simp only [F, sourceNativePrimeCore, restrictSequence, hn, ite_false]
    simp only [he, norm_zero, zero_le_one, ne_eq, not_true_eq_false, false_implies, and_self]
end Green64Analytic.Parity

end

end

/-! ## ActualComparisonData -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin Green64Analytic.ShiftTwoTerminal
open Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000

/-- The exact r20 canonical comparison data, including the true native
QSkip residual, extra character mask and correctly conjugated source-row
coefficient (or the target selector). The cofactor interval is applied
only after full-cell centering. The explicit row restoration cost remains
sourceB578CanonicalRowScale434; it is not discarded by this record. -/
def ParityActualComparisonCellRecords434
    (cfg : SourceComparisonFixed434) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma : ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (sigma0 sigma1 v1 : ℝ),
    |sigma0|≤L^cfg.s0 → |sigma1|≤L^cfg.s1base → |v1|≤L^cfg.vexp →
  ∀ (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
    (∀ u, psi u≠0 → 1/cfg.A≤u ∧ u≤ cfg.A) →
    sourceLogDerivativeBudget cfg.Cpsi cfg.Kpsi L (fun u=>psi (Real.exp u)) →
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
  ∀ (Qcomp : ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 20 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (target : ∀g, Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g) → ℕ) (tw sourceSide : Bool),
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let P := sourceNativeOriginalTb434 20 L
  let Vm := sourceNativeOriginalVbig434 20 L
  let row := sourceB578ActualPairCoef434 J 1 m hmJ nu Qcomp hA hB xi P Vm aux sourceSide target
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  ∃ data : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L (Z*Hp) Hp,
    data.Z=Z ∧ data.Ncap=⌈64*(Z*Hp)⌉₊ ∧
    data.G=sourceNativeOriginalG434 20 L ∧
    data.Ptw=(if tw then sourceNativeOriginalG434 20 L else ∅) ∧
    data.S=sourceNativeOriginalS434 20 L hFamily ∧
    data.Ts=sourceNativeOriginalTs434 20 L hFamily ∧ data.Tb=P ∧
    data.Vs=sourceNativeOriginalVs434 20 L hFamily ∧
    data.Vsmall=sourceNativeOriginalVsmall434 20 L hFamily ∧ data.Vbig=Vm ∧
    data.ts=(fun _=>1) ∧ data.tb=sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu ∧
    HEq data.coef row ∧ data.k=0 ∧
    data.alpha=b629ActualFineAlpha434 prime L S gamma lFine uFine ∧
    data.lo=a ∧ data.hi=b ∧ data.alphaCut=F.alpha ∧
    data.F1=Finset.range (Fintype.card nu.1) ∧ data.F2=Finset.range (Fintype.card nu.2) ∧
    data.p1=sourceOriginalProbeIndexedPrime434 (fun z : nu.1=>aux (Sum.inl z)) ∧
    data.p2=sourceOriginalProbeIndexedPrime434 (fun z : nu.2=>aux (Sum.inr z)) ∧
    data.U1=Real.exp ((ja:ℝ)*hA) ∧ data.U2=Real.exp ((jb:ℝ)*hB) ∧
    data.primeSlot=sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band ∧
    data.c=(fun n=>star (F.residual n)) ∧ data.C=1 ∧ data.qBase=2*k.natAbs ∧
    HEq data.chi0 (chi.ringHomComp (starRingEnd ℂ)) ∧
    data.sigma0=sigma0 ∧ data.sigma1=sigma1 ∧ data.v1=v1 ∧ data.psi1=psi

/-- Construct the complete genuine Parity comparison data uniformly over
all active cells, all original marked rows, all QSkip Fourier data and
both parity choices. The input hypotheses are source size/regularity
conditions only. There is no existing data record, sup, norm, discrepancy,
prime-mass, cancellation or endpoint-equality assumption. -/
theorem parity_eventually_actual_comparison_data434
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi Ck Cpsi S beta gamma : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm:ℝ))
    (hCarc : (cm:ℝ)≤Carc) (hCchi : (cm:ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hCpsi : 0≤Cpsi) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀j,0≤Kpsi j) :
    let cfg := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
      hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ParityActualComparisonCellRecords434 cfg L jQ mmax CZ Ck S beta gamma := by
  let cfg := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
  have hCarc0 : 0≤Carc := (Nat.cast_nonneg cm).trans hCarc
  have hScales := Filter.eventually_all.mpr
    (fun m : Fin (mmax+1) => parity_eventually_full_comparison_cell_scales434 CZ Carc m.val hCZ hCarc0)
  filter_upwards [hScales,
    parity_eventually_comparison_arc_gates434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
      hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi,
    eventually_source_native_original_group_masses434 20 (by norm_num),
    parity_eventually_fixed_Q_fields434 jQ,
    b629_actual_fine_coefficient_and_rough_support434 S beta gamma hS hbeta hgamma,
    eventually_ge_atTop (max (Real.exp 2) 4)] with L hscale hArcL hmass hQ hcoeff hL
  have hL4 : 4≤L := (le_max_right _ _).trans hL
  have hLe2 : Real.exp 2≤L := (le_max_left _ _).trans hL
  have hL1 : 1≤L := by linarith
  have hLp : 0<L := by linarith
  refine ⟨hmass.2.1,hQ.2.1,?_⟩
  unfold ParityActualComparisonCellRecords434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hA hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hK chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1
    psi hSmooth hSupport hBudget prime lFine uFine a b hFineLow
    Qcomp aux hAux hAuxA hAuxB target tw sourceSide
  dsimp only
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let Y := Z*Hp
  let Ncap : ℕ := ⌈64*Y⌉₊
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  have hsc := (hscale ⟨m,by omega⟩).2 Z hZlo hZhi nu hnu hA hB xi hhA hhB hA1 hB1 ja jb ha hb
  dsimp only at hsc
  rcases hsc with ⟨hZpos,hHpos,hY4,hYstrong,hYmax,hcap,hNcap,hHband,hArcCap⟩
  have hGroups := source_B578_actual_group_counts_Cfour434 20 L hLe2 hFamily
  have hMass := hmass.2.2 hFamily
  have hG := source_native_original_G_identity434 20 L hFamily hmass.1
  have hSG : sourceNativeOriginalS434 20 L hFamily ⊆ sourceNativeOriginalG434 20 L := by
    rw [hG]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have hDisj := source_native_original_small_group_disjoint434 20 L hFamily (by norm_num) hmass.1
  have hPcap := source_B578_actual_P_below_comparison_cap434 20 L Y hL4 Ncap hYstrong hcap
  have hQcap := parity_Qslot_below_comparison_cap434
    (sourceOriginalLiteralDepth 20 L) L hL1 band Y Ncap hYstrong hcap
  have hQfields := hQ.2.2 (sourceOriginalLiteralDepth 20 L) band hband
  dsimp only at hQfields
  rcases hQfields with ⟨hI,hSlot,hIBand,hLong,hSlotMin⟩
  obtain ⟨hAne,_,hBne,_⟩ := (source_original_two_block_probe_pattern_mem434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    m nu.1 nu.2).mp hnu
  let aA : nu.1 → ℕ := fun z=>aux (Sum.inl z)
  let aB : nu.2 → ℕ := fun z=>aux (Sum.inr z)
  have hFA : (Finset.range (Fintype.card nu.1)).Nonempty := by
    have hc : 0<Fintype.card nu.1 := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hAne
    exact ⟨0,Finset.mem_range.mpr hc⟩
  have hFB : (Finset.range (Fintype.card nu.2)).Nonempty := by
    have hc : 0<Fintype.card nu.2 := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hBne
    exact ⟨0,Finset.mem_range.mpr hc⟩
  have hPrA : ∀i : Fin (Fintype.card nu.1),
      sourceOriginalProbeIndexedPrime434 aA i ∈ sourceNativeOriginalTb434 20 L
        ((Fintype.equivFin nu.1).symm i).val.1 ∧
      (sourceOriginalProbeIndexedPrime434 aA i).Prime ∧
      Real.exp (L^(3/10:ℝ)) ≤ (sourceOriginalProbeIndexedPrime434 aA i:ℝ) := by
    intro i
    have hp : aA ((Fintype.equivFin nu.1).symm i) ∈ sourceNativeOriginalTb434 20 L
        ((Fintype.equivFin nu.1).symm i).val.1 :=
      (Fintype.mem_piFinset.mp hAux) (Sum.inl ((Fintype.equivFin nu.1).symm i))
    have hr := source_native_original_Tb_prime_range434 20 L _ _ hp
    simpa only [sourceOriginalProbeIndexedPrime434,dite_eq_left i.isLt] using ⟨hp,hr.1,hr.2.1⟩
  have hPrB : ∀i : Fin (Fintype.card nu.2),
      sourceOriginalProbeIndexedPrime434 aB i ∈ sourceNativeOriginalTb434 20 L
        ((Fintype.equivFin nu.2).symm i).val.1 ∧
      (sourceOriginalProbeIndexedPrime434 aB i).Prime ∧
      Real.exp (L^(3/10:ℝ)) ≤ (sourceOriginalProbeIndexedPrime434 aB i:ℝ) := by
    intro i
    have hp : aB ((Fintype.equivFin nu.2).symm i) ∈ sourceNativeOriginalTb434 20 L
        ((Fintype.equivFin nu.2).symm i).val.1 :=
      (Fintype.mem_piFinset.mp hAux) (Sum.inr ((Fintype.equivFin nu.2).symm i))
    have hr := source_native_original_Tb_prime_range434 20 L _ _ hp
    simpa only [sourceOriginalProbeIndexedPrime434,dite_eq_left i.isLt] using ⟨hp,hr.1,hr.2.1⟩
  have hCellA : Real.log (((∏i ∈ Finset.range (Fintype.card nu.1),
      sourceOriginalProbeIndexedPrime434 aA i):ℕ):ℝ) ≤
      Real.log (Real.exp ((ja:ℝ)*hA))+1 := by
    rw [source_original_probe_indexed_prime_product434,Real.log_exp]
    change Real.log (sourceOriginalProbeDA434 m nu aux:ℝ) ≤ (ja:ℝ)*hA+1
    have hu := hAuxA.2
    linarith
  have hCellB : Real.log (((∏i ∈ Finset.range (Fintype.card nu.2),
      sourceOriginalProbeIndexedPrime434 aB i):ℕ):ℝ) ≤
      Real.log (Real.exp ((jb:ℝ)*hB))+1 := by
    rw [source_original_probe_indexed_prime_product434,Real.log_exp]
    change Real.log (sourceOriginalProbeDB434 m nu aux:ℝ) ≤ (jb:ℝ)*hB+1
    have hu := hAuxB.2
    linarith
  have hAlpha : ∀ n, ‖b629ActualFineAlpha434 prime L S gamma lFine uFine n‖≤1 :=
    fun n=>(hcoeff prime lFine uFine hFineLow n).1
  have hRough : ∀ n, sourceAlphaDyadicCut
      (b629ActualFineAlpha434 prime L S gamma lFine uFine) a b n≠0 →
      SourceRoughAbove n (Real.exp (Real.sqrt L)) := by
    intro n hn
    apply (hcoeff prime lFine uFine hFineLow n).2
    intro hz
    apply hn
    simp [sourceAlphaDyadicCut,hz]
  have hQSkip : ∀ n, ‖star (F.residual n)‖≤1 := by
    intro n
    rw [norm_star]
    exact source_native_residual_norm_le_one 20 (sourceOriginalLiteralDepth 20 L) L
      (by norm_num) hLp band slot delta freq (Finset.Icc a b)
      (b629ActualFineAlpha434 prime L S gamma lFine uFine) (2*k.natAbs) chi 0 0 n
  have hqfields := parity_mask_modulus_budget434 L Ck cm (by linarith) hcm k hk hK
  let data : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L Y Hp := {
    Z := Z
    hY := hY4
    hYmax := hYmax
    hH := hHpos
    hYstrong := hYstrong
    hZ := hZlo
    hYIdent := rfl
    hSmallGroups := hGroups.1
    hBigGroups := hGroups.2
    lo := a
    hi := b
    Ncap := Ncap
    alpha := b629ActualFineAlpha434 prime L S gamma lFine uFine
    hNcap := hNcap
    hCap := hcap
    hAlpha := by intro n hn; simpa [cfg,parityComparisonFixed434,sourceNativeOriginalR6Fixed434] using hAlpha n
    G := sourceNativeOriginalG434 20 L
    Ptw := if tw then sourceNativeOriginalG434 20 L else ∅
    S := sourceNativeOriginalS434 20 L hFamily
    primeSlot := sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band
    Ts := sourceNativeOriginalTs434 20 L hFamily
    Tb := sourceNativeOriginalTb434 20 L
    Vs := sourceNativeOriginalVs434 20 L hFamily
    Vsmall := sourceNativeOriginalVsmall434 20 L hFamily
    Vbig := sourceNativeOriginalVbig434 20 L
    ts := fun _=>1
    tb := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
    coef := sourceB578ActualPairCoef434 J 1 m hmJ nu Qcomp hA hB xi
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) aux sourceSide target
    k := 0
    qBase := 2*k.natAbs
    c := fun n=>star (F.residual n)
    chi0 := chi.ringHomComp (starRingEnd ℂ)
    hBase := hqfields.1
    hBaseCap := hqfields.2
    hk := by change 0+1≤1+mmax; omega
    hVs := hMass.1.1
    hts := fun _=>by change 1≤1+mmax; omega
    htb := fun g=>(source_original_probe_free_mark_cap434 J 1 m hmJ nu g).trans (by change 1+m≤1+mmax; omega)
    hVsmall := fun i=>(hMass.2.1 i).1
    hVbig := fun g=>(hMass.2.2 g).1
    hcoef := fun a=>source_B578_actual_pair_coef_norm434 J 1 m hmJ nu Qcomp hA hB xi
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) aux sourceSide target a hhA hhB hxi
    C := 1
    hC := by norm_num
    hCBudget := by change (1:ℝ)≤L^0; simp
    hcBound := hQSkip
    sigma0 := sigma0
    sigma1 := sigma1
    hSigma0 := hsigma0
    hSigma1 := hsigma1
    hModScale := hArcL.2.1
    hSG := hSG
    hSPrime := fun p hp=>(source_native_original_S_prime_range434 20 L hFamily p hp).1
    hSN := fun p hp=>hPcap p (hSG hp)
    hPN := hQcap
    hRough := hRough
    hGroup := fun p hp=>(source_native_original_G_bound434 20 L hL1 p hp).2
    hLong := hLong
    I := Set.Icc (Real.exp (cfg.τ*L)) (Real.exp (cfg.η*L))
    hI := hI
    hSmall := fun p hp=>(source_native_original_S_prime_range434 20 L hFamily p hp).2
    hSlot := hSlot
    hIBand := hIBand
    F1 := Finset.range (Fintype.card nu.1)
    F2 := Finset.range (Fintype.card nu.2)
    p1 := sourceOriginalProbeIndexedPrime434 aA
    p2 := sourceOriginalProbeIndexedPrime434 aB
    U1 := Real.exp ((ja:ℝ)*hA)
    U2 := Real.exp ((jb:ℝ)*hB)
    hF1 := hFA
    hF2 := hFB
    hp1 := fun i hi=>(hPrA ⟨i,Finset.mem_range.mp hi⟩).2.1.one_le
    hp2 := fun i hi=>(hPrB ⟨i,Finset.mem_range.mp hi⟩).2.1.one_le
    hmin1 := fun i hi=>(hPrA ⟨i,Finset.mem_range.mp hi⟩).2.2
    hmin2 := fun i hi=>(hPrB ⟨i,Finset.mem_range.mp hi⟩).2.2
    hU1 := Real.exp_pos _
    hU2 := Real.exp_pos _
    hcell1 := hCellA
    hcell2 := hCellB
    hHIdent := rfl
    psi1 := psi
    hSmooth := hSmooth
    hSupport := hSupport
    v1 := v1
    hv1 := hv1
    hBudget := hBudget
    hG := hG
    hParity := by cases tw <;> simp
    hTsPrime := fun i p hp=>(source_native_original_Ts_prime_range434 20 L hFamily i p hp).1
    hTbPrime := fun g p hp=>(source_native_original_Tb_prime_range434 20 L g p hp).1
    hOrigW := hArcL.2.2.1
    hOrigSmall := hArcL.2.2.2.1
    hOrigLong := hArcL.2.2.2.2
    hSlotMin := hSlotMin
    hHband := hHband
    hArcCap := hArcCap
    hDisjS := fun i p hp hpi=>Finset.disjoint_left.mp (hDisj.1 i) hp hpi
    hDisjB := fun g p hp hpg=>Finset.disjoint_left.mp (hDisj.2.1 g) hp hpg }
  refine ⟨data,?_⟩
  dsimp only [data]
  repeat' constructor
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualCellGroupData -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 26000

/-- Two independently active ORIGINAL cells have a joint complete
prime assignment. The proof uses positivity of their actual cell masses
and the exact Gram law; no normalized surrogate law, no clean/injective
restriction and no assumed auxiliary witness occurs. -/
theorem parity_active_cells_joint_aux434
    {G : Type} [DecidableEq G] (m : ℕ)
    (nu : SourceOriginalProbePattern434 G m) (P : G → Finset ℕ) (V : G → ℝ)
    (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (ja jb : ℤ)
    (hja : ja ∈ sourceOriginalProbeActiveCellsA434 m P V nu hA xi)
    (hjb : jb ∈ sourceOriginalProbeActiveCellsB434 m P V nu hB xi) :
    ∃ aux : SourceOriginalProbeAuxIndex434 m nu → ℕ,
      aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P) ∧
      sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) ∧
      sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) := by
  let SA : nu.1 → Finset ℕ := fun z => P z.val.1
  let SB : nu.2 → Finset ℕ := fun z => P z.val.1
  have hMassA : 0 < sourceOriginalProbeCellA434 m P V nu hA ja :=
    hxi.trans_le ((source_original_probe_active_cell_A_mem_iff434 m P V nu hA xi hhA hxi ja).mp hja)
  have hMassB : 0 < sourceOriginalProbeCellB434 m P V nu hB jb :=
    hxi.trans_le ((source_original_probe_active_cell_B_mem_iff434 m P V nu hB xi hhB hxi jb).mp hjb)
  obtain ⟨a,ha⟩ : ∃ a : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalLiteralLogCell434 hA ja (sourceOriginalGramPrimeProduct434 SA a) := by
    by_contra h
    push_neg at h
    have hz : sourceOriginalProbeCellA434 m P V nu hA ja = 0 := by
      simp only [sourceOriginalProbeCellA434,source_original_true_cell_probability_eq_gram_mass434,
        sourceOriginalRealGramCellMass434]
      apply Finset.sum_eq_zero
      intro a ha
      exact if_neg (h a)
    exact (ne_of_gt hMassA) hz
  obtain ⟨b,hb⟩ : ∃ b : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalLiteralLogCell434 hB jb (sourceOriginalGramPrimeProduct434 SB b) := by
    by_contra h
    push_neg at h
    have hz : sourceOriginalProbeCellB434 m P V nu hB jb = 0 := by
      simp only [sourceOriginalProbeCellB434,source_original_true_cell_probability_eq_gram_mass434,
        sourceOriginalRealGramCellMass434]
      apply Finset.sum_eq_zero
      intro b hb
      exact if_neg (h b)
    exact (ne_of_gt hMassB) hz
  let aux : SourceOriginalProbeAuxIndex434 m nu → ℕ :=
    Sum.elim (fun z => (a z).val) (fun z => (b z).val)
  refine ⟨aux,?_,ha,hb⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  cases i with
  | inl z => exact (a z).property
  | inr z => exact (b z).property

/-- A genuine r20 fixed record used only to certify the original group
geometry. Its zero cutoff and zero endpoint frequencies do not replace
any endpoint of the actual coupled kernel. The requested minor exponent
will use only its literal C0=4, vmin and tmax=1+mmax fields. -/
def parityCellKernelGroupFixed434 (mmax : ℕ) (Carc : ℝ) (hCarc : 1 ≤ Carc) :
    SourceComparisonFixed434 :=
  parityComparisonFixed434 0 mmax 1 0 0 0 0 Carc 1 (by simpa only [Nat.cast_one] using hCarc)
    (by norm_num) (by norm_num) 0 (by norm_num) (fun _ => 0) (by intro j; rfl)

/-- Construct a true original r20 group certificate for every pair of
active cells. The auxiliary assignment is derived, the actual comparison
data are constructed by the certified source theorem with zero cutoff,
and only the six original prime/mass fields are retained. No external
data, endpoint, arc estimate or nonzero-completion premise remains. -/
theorem parity_eventually_actual_cell_group_data434
    (mmax : ℕ) (Carc : ℝ) (hCarc : 1 ≤ Carc) :
    let cfg := parityCellKernelGroupFixed434 mmax Carc hCarc
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
      ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
        nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
      ∀ (hA hB xi : ℝ), 0 < hA → 0 < hB → 0 < xi → hA ≤ 1 → hB ≤ 1 →
      ∀ (ja jb : ℤ),
        ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hA xi →
        jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hB xi →
      let Hp := Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
      ∃ data : SourceComparisonData434 (sourceNativeOriginalTsType434 20 L hS)
          (sourceNativeOriginalBigType434 20 L) cfg (Real.exp L) L (Real.exp L*Hp) Hp,
        SourceB636ParityActualGroupFields434 L hS data := by
  let cfg := parityCellKernelGroupFixed434 mmax Carc hCarc
  have hd := parity_eventually_actual_comparison_data434 0 mmax 1 0 0 0
    0 Carc 1 0 0 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [Nat.cast_one] using hCarc) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => 0) (by intro j; rfl)
  filter_upwards [hd,eventually_ge_atTop (1 : ℝ)] with L hdL hL
  refine ⟨hdL.1,?_⟩
  intro hS J m hmJ hm nu hnu hA hB xi hhA hhB hxi hA1 hB1 ja jb hja hjb
  dsimp only
  obtain ⟨aux,hAux,hAuxA,hAuxB⟩ := parity_active_cells_joint_aux434 m nu
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    hA hB xi hhA hhB hxi ja jb hja hjb
  have hZeroBudget : sourceLogDerivativeBudget cfg.Cpsi cfg.Kpsi L
      (fun _ : ℝ => (0 : ℂ)) := by
    intro j u
    simpa using mul_nonneg (cfg.hKpsi j)
      (Real.rpow_nonneg (by linarith : 0 ≤ L) (cfg.Cpsi*((j : ℝ)+1)))
  have hZlo : Real.exp L*L^(-(0 : ℝ)) ≤ Real.exp L := by simp
  have hZhi : Real.exp L ≤ Real.exp L*L^(0 : ℝ) := by simp
  have hK : ((1 : ℤ).natAbs : ℝ) ≤ L^(0 : ℝ) := by norm_num
  have hSigma0 : |(0 : ℝ)| ≤ L^cfg.s0 := by
    change |(0 : ℝ)| ≤ L^(0 : ℕ)
    norm_num
  have hSigma1 : |(0 : ℝ)| ≤ L^cfg.s1base := by
    change |(0 : ℝ)| ≤ L^(0 : ℕ)
    norm_num
  have hVexp : |(0 : ℝ)| ≤ L^cfg.vexp := by
    change |(0 : ℝ)| ≤ L^(0 : ℕ)
    norm_num
  have hFine : Real.exp ((1 : ℝ)*L) ≤ (⌈Real.exp L⌉₊ : ℝ) := by
    simpa only [one_mul] using Nat.le_ceil (Real.exp L)
  obtain ⟨data,hFields⟩ := hdL.2.2 hS (Real.exp L) hZlo hZhi J m hmJ hm nu hnu
    hA hB xi hhA hhB hxi hA1 hB1 ja jb hja hjb
    (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth 20 L+1)) rfl
    (⟨0,by norm_num⟩ : Fin 20) (fun _ => false) (fun _ => 0)
    1 (by norm_num) hK 1 0 0 0 hSigma0 hSigma1 hVexp
    (fun _ => 0) contDiff_const (by intro u hu; exact False.elim (hu rfl)) hZeroBudget
    false ⌈Real.exp L⌉₊ 0 0 0 hFine 0 aux hAux hAuxA hAuxB (fun _ _ => 0) false true
  rcases hFields with ⟨_,_,_,_,hSD,hTs,hTb,hVs,hVm,hVb,_⟩
  exact ⟨data,hSD,hTs,hTb,hVs,hVm,hVb⟩
end Green64Analytic.Parity

end

end

/-! ## ActualRankArc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin Green64Analytic.ShiftTwoTerminal
open Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000

/-- Genuine r20 Parity endpoint records for the exact primitive rank factors,
with arbitrary-log signed rational-arc saving. The marked coefficients use
only actual endpoint marked products; all DA/DB dependence and both inverse
cell masses stay outside them, as parity_actual_concrete_Knu_rank_expansion434
proves. The auxiliary assignments here witness source geometry only. -/
def ParityActualRankComparisonCellArc434
    (cfg : SourceComparisonFixed434) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma targetSaving Karc : ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (sigma0 sigma1 v1 : ℝ),
    |sigma0|≤L^cfg.s0 → |sigma1|≤L^cfg.s1base → |v1|≤L^cfg.vexp →
  ∀ (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
    (∀ u, psi u≠0 → 1/cfg.A≤u ∧ u≤ cfg.A) →
    sourceLogDerivativeBudget cfg.Cpsi cfg.Kpsi L (fun u=>psi (Real.exp u)) →
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 20 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)) (tw sourceSide : Bool),
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let P := sourceNativeOriginalTb434 20 L
  let Vm := sourceNativeOriginalVbig434 20 L
  let row := if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB jb cb
    else paritySecondRankMark434 J 1 m hmJ nu hA ja ca
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  ∃ data : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L (Z*Hp) Hp,
    (data.Z=Z ∧ data.Ncap=⌈64*(Z*Hp)⌉₊ ∧
    data.G=sourceNativeOriginalG434 20 L ∧
    data.Ptw=(if tw then sourceNativeOriginalG434 20 L else ∅) ∧
    data.S=sourceNativeOriginalS434 20 L hFamily ∧
    data.Ts=sourceNativeOriginalTs434 20 L hFamily ∧ data.Tb=P ∧
    data.Vs=sourceNativeOriginalVs434 20 L hFamily ∧
    data.Vsmall=sourceNativeOriginalVsmall434 20 L hFamily ∧ data.Vbig=Vm ∧
    data.ts=(fun _=>1) ∧ data.tb=sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu ∧
    HEq data.coef row ∧ data.k=0 ∧
    data.alpha=b629ActualFineAlpha434 prime L S gamma lFine uFine ∧
    data.lo=a ∧ data.hi=b ∧ data.alphaCut=F.alpha ∧
    data.F1=Finset.range (Fintype.card nu.1) ∧ data.F2=Finset.range (Fintype.card nu.2) ∧
    data.p1=sourceOriginalProbeIndexedPrime434 (fun z : nu.1=>aux (Sum.inl z)) ∧
    data.p2=sourceOriginalProbeIndexedPrime434 (fun z : nu.2=>aux (Sum.inr z)) ∧
    data.U1=Real.exp ((ja:ℝ)*hA) ∧ data.U2=Real.exp ((jb:ℝ)*hB) ∧
    data.primeSlot=sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band ∧
    data.c=(fun n=>star (F.residual n)) ∧ data.C=1 ∧ data.qBase=2*k.natAbs ∧
    HEq data.chi0 (chi.ringHomComp (starRingEnd ℂ)) ∧
    data.sigma0=sigma0 ∧ data.sigma1=sigma1 ∧ data.v1=v1 ∧ data.psi1=psi) ∧
    data.endpoint = sourceOriginalFullEndpointCoefficients434 (2*k.natAbs)
      (sourceNativeOriginalS434 20 L hFamily) (sourceNativeOriginalTs434 20 L hFamily) P cfg.q0
      (sourceNativeOriginalVs434 20 L hFamily) (sourceNativeOriginalVsmall434 20 L hFamily) Vm
      (fun _=>1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) row 0
      (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band)
      F.alpha (fun n=>star (F.residual n)) (chi.ringHomComp (starRingEnd ℂ)) sigma0 sigma1
      (fun n=>psi ((n:ℝ)/(Z*Hp))*sourcePhase n v1) ∧
    ∀ (eps : Bool) (den h : ℕ), 0 < den → (den:ℝ) ≤ L^cfg.cm →
      (∫ theta in {theta : ℝ | |theta| ≤ L^cfg.Carc/Hp},
        ‖sourceCircleFourierPoly data.support
          (sourceSignedCoefficients434 data.Ptw eps data.endpoint)
          (((h:ℝ)/(den:ℝ)+theta:ℝ):AddCircle (1:ℝ))‖^2) ≤
        Karc*(Z*Hp)*L^(-targetSaving)

/-- Construct and estimate the actual aux-independent rank endpoint pair.
The only input bounds are source sizes, frequencies and smooth-cutoff budgets.
B and fine precision S are chosen after targetSaving and before L. This is
the full marked arc ingredient; free-ban errors and integration of the
source physical correlation are not premises or conclusions. -/
theorem parity_eventually_actual_rank_marked_arc434
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi Ck Cpsi beta gamma targetSaving : ℝ)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hcm : Ck+1 ≤ (cm:ℝ))
    (hCarc : (cm:ℝ) ≤ Carc) (hCchi : (cm:ℝ) ≤ Cchi) (hCchiPos : 0 < Cchi)
    (hCpsi : 0 ≤ Cpsi) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
      hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
    ∃ Karc : ℝ, 0 < Karc ∧ ∃ B : ℕ, ∃ S : ℝ,
      2*((B:ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ParityActualRankComparisonCellArc434 cfg L jQ mmax CZ Ck S beta gamma targetSaving Karc := by
  let cfg := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
  obtain ⟨Karc,hKarc,B,S,hSB,X0,hX0,hArc⟩ :=
    b629_actual_fine_full_marked_signed_arc434 cfg targetSaving beta gamma hbeta hgamma
  have hS : 0 < S := by have := Nat.cast_nonneg (α:=ℝ) B; linarith
  have hData := parity_eventually_actual_comparison_data434
    jQ mmax cm s0 s1 vexp CZ Carc Cchi Ck Cpsi S beta gamma
    hCZ hCk hcm hCarc hCchi hCchiPos hCpsi hS hbeta hgamma Kpsi hKpsi
  refine ⟨Karc,hKarc,B,S,hSB,?_⟩
  filter_upwards [hData,hArc,eventually_ge_atTop (max 3 (Real.log X0))]
    with L hd hArcL hLarge
  have hL : 3 ≤ L := (le_max_left _ _).trans hLarge
  have hx : X0 ≤ Real.exp L := by
    have hlog : Real.log X0 ≤ L := (le_max_right _ _).trans hLarge
    simpa only [Real.exp_log (by linarith : 0 < X0)] using Real.exp_le_exp.mpr hlog
  refine ⟨hd.1,hd.2.1,?_⟩
  unfold ParityActualRankComparisonCellArc434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hA hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hK chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1
    psi hSmooth hSupport hBudget prime lFine uFine a b hFineLow hl hu hub
    Qcomp aux hAux hAuxA hAuxB ca cb tw sourceSide
  dsimp only
  obtain ⟨data,hfields⟩ := hd.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu
    hA hB xi hhA hhB hxi hA1 hB1 ja jb ha hb band hband slot delta freq k hk hK
    chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1 psi hSmooth hSupport hBudget
    prime lFine uFine a b hFineLow Qcomp aux hAux hAuxA hAuxB (fun _ _=>0) tw true
  let rank := if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB jb cb
    else paritySecondRankMark434 J 1 m hmJ nu hA ja ca
  have hRank : ∀ marks, ‖rank marks‖ ≤ 1 := by
    intro marks
    have hh := parity_actual_rank_mark_norm434 J 1 m hmJ nu hA hB ja jb ca cb marks
    cases sourceSide
    · exact hh.2
    · exact hh.1
  let ranked : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L (Z*(Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)))
      (Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)) :=
    { data with
      tb := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
      coef := rank
      htb := fun g=>(source_original_probe_free_mark_cap434 J 1 m hmJ nu g).trans
        (by change 1+m ≤ 1+mmax; omega)
      hcoef := hRank }
  obtain ⟨hz,hcap,hG,hTw,hSdata,hTs,hTb,hVs,hVm,hVb,hts,htb,hcoef,hk,hAlpha,
    hlo,hhi,hcut,hF1,hF2,hp1,hp2,hU1,hU2,hQ,hc,hC,hq,hchi,hs0,hs1,hv,hpsi⟩ := hfields
  refine ⟨ranked,?_,?_,?_⟩
  · exact ⟨hz,hcap,hG,hTw,hSdata,hTs,hTb,hVs,hVm,hVb,hts,rfl,HEq.rfl,hk,hAlpha,
      hlo,hhi,hcut,hF1,hF2,hp1,hp2,hU1,hU2,hQ,hc,hC,hq,hchi,hs0,hs1,hv,hpsi⟩
  · dsimp only [ranked,SourceComparisonData434.endpoint,SourceComparisonData434.cutoff]
    simp only [hpsi,hv]
    congr 1
  · intro eps den h hden hDenCap
    exact hArcL (Real.exp L) hx (Real.log_exp L).symm hL prime lFine uFine
      hl hu hFineLow hub _ _ ranked hAlpha eps den h hden hDenCap
end Green64Analytic.SourceBlockSieve

end

end

/-! ## EnlargedComparisonGeometry -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 26000

/-- Enlarge only the fixed physical cutoff support. Every Parity exponent,
mass, ordered-Q field and character modulus parameter is unchanged. -/
def parityEnlargedComparisonFixed434 (cfg : SourceComparisonFixed434)
    (A : ℝ) (hA : 1 ≤ A) : SourceComparisonFixed434 :=
  { cfg with A := A, hA := hA }

/-- Exact data transport to a larger actual finite carrier and a genuine
new smooth cutoff. No endpoint, prime, group, residual, character, phase,
auxiliary geometry or rank field is changed. The actual eventual theorem
below derives the new cap and arc-window conditions. -/
def parityEnlargedComparisonData434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (A : ℝ) (hA : 1 ≤ A) (Ncap : ℕ)
    (hNcap : (Ncap : ℝ) ≤ x^2) (hCap : A*Y ≤ (Ncap : ℝ))
    (hOldCap : d.Ncap ≤ Ncap)
    (hArcCap : Hprime/L^cfg.Carc ≤ Y/(8*A))
    (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ u, psi u≠0 → 1/A≤u ∧ u≤A)
    (hBudget : sourceLogDerivativeBudget cfg.Cpsi cfg.Kpsi L
      (fun u => psi (Real.exp u))) :
    SourceComparisonData434 ι β (parityEnlargedComparisonFixed434 cfg A hA) x L Y Hprime :=
  { d with
    Ncap := Ncap
    hNcap := hNcap
    hCap := hCap
    hSN := fun p hp => (d.hSN p hp).trans hOldCap
    hPN := fun p hp => (d.hPN p hp).trans hOldCap
    psi1 := psi
    hSmooth := hSmooth
    hSupport := hSupport
    hBudget := hBudget
    hArcCap := hArcCap }

/-- A fixed multiplicative scale in [1/L,L] is absorbed in exactly one
additional logarithmic-window power. This is an exact real inequality. -/
theorem parity_scaled_polynomial_Z_window434
    (L CZ Z a : ℝ) (hL : 1 ≤ L)
    (hZlo : Real.exp L*L^(-CZ) ≤ Z) (hZhi : Z ≤ Real.exp L*L^CZ)
    (haLo : 1/L ≤ a) (haHi : a ≤ L) :
    Real.exp L*L^(-(CZ+1)) ≤ a*Z ∧ a*Z ≤ Real.exp L*L^(CZ+1) := by
  have hLp : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hap : 0<a := (div_pos zero_lt_one hLp).trans_le haLo
  have hZp : 0<Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hlo : L^(-(CZ+1)) = L^(-CZ)/L := by
    rw [show -(CZ+1) = -CZ + (-1) by ring, Real.rpow_add hLp,
      Real.rpow_neg_one, div_eq_mul_inv]
  have hhi : L^(CZ+1) = L^CZ*L := by
    rw [Real.rpow_add hLp, Real.rpow_one]
  constructor
  · calc
      Real.exp L*L^(-(CZ+1)) = (1/L)*(Real.exp L*L^(-CZ)) := by rw [hlo]; ring
      _ ≤ a*(Real.exp L*L^(-CZ)) :=
        mul_le_mul_of_nonneg_right haLo (by positivity)
      _ ≤ a*Z := mul_le_mul_of_nonneg_left hZlo hap.le
  · calc
      a*Z ≤ L*(Real.exp L*L^CZ) := mul_le_mul haHi hZhi hZp.le hLp.le
      _ = Real.exp L*L^(CZ+1) := by rw [hhi]; ring

/-- Genuine enlarged-cap geometry for every actual r20 active cell.
The scale A is fixed BEFORE L. The two rescaled applications reuse the
certified cell-scale theorem; no new data, support or arc-smallness premise
is introduced. In particular Ncap is exactly ceil(A*Z*H), not an upper
bound supplied by the caller. -/
theorem parity_eventually_enlarged_comparison_cell_scales434
    (A CZ Carc : ℝ) (m : ℕ) (hA : 64 ≤ A) (hCZ : 0 ≤ CZ) (hCarc : 0 ≤ Carc) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ Z : ℝ, Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
      ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
        nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
      ∀ (hA hB xi : ℝ), 0<hA → 0<hB → hA≤1 → hB≤1 →
      ∀ (ja jb : ℤ),
        ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hA xi →
        jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hB xi →
      let H := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
      let Y := Z*H
      A*Y ≤ (⌈A*Y⌉₊ : ℝ) ∧ (⌈A*Y⌉₊ : ℝ) ≤ (Real.exp L)^2 ∧
        H/L^Carc ≤ Y/(8*A) := by
  let a : ℝ := A/64
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hap : 0<a := lt_of_lt_of_le zero_lt_one ha
  have hAp : 0<A := by linarith
  have hCZ1 : 0 ≤ CZ+1 := by linarith
  filter_upwards [parity_eventually_full_comparison_cell_scales434 (CZ+1) Carc m hCZ1 hCarc,
    eventually_ge_atTop (max 2 a)] with L hs hLarge
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hLarge
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0<L := by linarith
  have haL : a ≤ L := (le_max_right _ _).trans hLarge
  have hInvL : 1/L ≤ 1 := (div_le_one hLp).mpr hL1
  have hInvA : 1/a ≤ 1 := (div_le_one hap).mpr ha
  have hInv : 1/L ≤ 1/a := (div_le_div_iff₀ hLp hap).mpr (by simpa using haL)
  refine ⟨hL2,?_⟩
  intro Z hZlo hZhi nu hnu hA' hB xi hhA hhB hA1 hB1 ja jb hjA hjB
  let H := Real.exp ((ja:ℝ)*hA')*Real.exp ((jb:ℝ)*hB)
  have hup := parity_scaled_polynomial_Z_window434 L CZ Z a hL1 hZlo hZhi
    (hInvL.trans ha) haL
  have hdown := parity_scaled_polynomial_Z_window434 L CZ Z (1/a) hL1 hZlo hZhi
    hInv (hInvA.trans hL1)
  have hSup := hs.2 (a*Z) hup.1 hup.2 nu hnu hA' hB xi hhA hhB hA1 hB1 ja jb hjA hjB
  have hSdown := hs.2 ((1/a)*Z) hdown.1 hdown.2 nu hnu hA' hB xi hhA hhB hA1 hB1 ja jb hjA hjB
  dsimp only at hSup hSdown ⊢
  have hNcap := hSup.2.2.2.2.2.2.1
  have hArc := hSdown.2.2.2.2.2.2.2.2
  change (⌈64*((a*Z)*H)⌉₊ : ℝ) ≤ (Real.exp L)^2 at hNcap
  change H/L^Carc ≤ (((1/a)*Z)*H)/(8*64) at hArc
  have heq : 64*((a*Z)*H) = A*(Z*H) := by dsimp [a]; ring
  rw [heq] at hNcap
  have heqDown : (((1/a)*Z)*H)/(8*64) = (Z*H)/(8*A) := by
    dsimp [a]
    field_simp <;> ring
  rw [heqDown] at hArc
  exact ⟨Nat.le_ceil _,hNcap,hArc⟩
end Green64Analytic.Parity

end

end

