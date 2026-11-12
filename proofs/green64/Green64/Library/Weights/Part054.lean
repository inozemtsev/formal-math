module

public import Green64.Library.Correlation.Part042
public import Green64.Library.Correlation.Part037
public import Green64.Library.Weights.Part049
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.Part043
public import Green64.Library.Correlation.Part028

@[expose] public section

/-!
# Weights / Part054

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalProbeAuxEndpointBan -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Group of an actual selected auxiliary coordinate. -/
def sourceOriginalProbeAuxGroup434
    {G : Type} (m : ℕ) (ν : SourceOriginalProbePattern434 G m) :
    SourceOriginalProbeAuxIndex434 m ν → G :=
  Sum.elim (fun a => a.val.1) (fun b => b.val.1)

/-- Only the two actual endpoint lists in this group are forbidden.
No distinctness condition is imposed on auxiliary values. -/
noncomputable def sourceOriginalProbeEndpointValues434
    {G : Type} (M : ℕ) (s t : G → Fin M → ℕ) (g : G) : Finset ℕ :=
  Finset.univ.image (s g) ∪ Finset.univ.image (t g)

def sourceOriginalProbeAuxEndpointBan434
    {G : Type} (M m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (s t : G → Fin M → ℕ) (a : SourceOriginalProbeAuxIndex434 m ν → ℕ) : Prop :=
  ∀ z i, a z ≠ s (sourceOriginalProbeAuxGroup434 m ν z) i ∧
    a z ≠ t (sourceOriginalProbeAuxGroup434 m ν z) i

theorem source_original_probe_endpoint_values_card434
    {G : Type} (M : ℕ) (s t : G → Fin M → ℕ) (g : G) :
    (sourceOriginalProbeEndpointValues434 M s t g).card  ≤  2*M := by
  have h := Finset.card_union_le (Finset.univ.image (s g)) (Finset.univ.image (t g))
  have hs := Finset.card_image_le (s := (Finset.univ : Finset (Fin M))) (f := s g)
  have ht := Finset.card_image_le (s := (Finset.univ : Finset (Fin M))) (f := t g)
  simp only [Finset.card_univ,Fintype.card_fin] at hs ht
  exact h.trans (by omega)

/-- Direct union bound for independent coordinates avoiding their own
forbidden sets. Repeated draws are retained exactly. -/
theorem source_shared_avoidance_mass434
    {I : Type} [Fintype I] [DecidableEq I]
    (S B : I → Finset ℕ) (V : I → ℝ) (Pmin vmin : ℝ)
    (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ i,V i=∑ p ∈ S i,1/(p:ℝ))
    (hVmin : ∀ i,vmin ≤ V i)
    (hPmin : ∀ i p,p∈S i → Pmin ≤ (p:ℝ)) :
    (∑ a ∈ Fintype.piFinset S,
      if ∀ i,a i ∉ B i then 0 else
        sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434 (V i)) a)  ≤ 
      (∑ i : I,(B i).card : ℝ)/(Pmin*vmin) := by
  classical
  let mu := fun i => sourcePrimeSharedAtom434 (V i)
  have hm (i : I) : (∑ p ∈ S i,mu i p)=1 :=
    source_prime_shared_atom_total434 (S i) (V i) (hV i) (hv.trans_le (hVmin i)).ne'
  have hnn : ∀ i p,p∈S i → 0 ≤ mu i p := by
    intro i p hp
    have hv' := hv.trans_le (hVmin i)
    dsimp [mu,sourcePrimeSharedAtom434]
    positivity
  have hcov : ∀ a ∈ Fintype.piFinset S,
      ¬(∀ i,a i ∉ B i) → ∃ i ∈ (Finset.univ : Finset I),a i ∈ B i := by
    intro a ha hb
    push_neg at hb
    obtain ⟨i,hi⟩ := hb
    exact ⟨i,Finset.mem_univ _,hi⟩
  have hu := source_finite_weighted_bad_union434
    (Fintype.piFinset S) Finset.univ (sourceSharedLaw434 mu)
    (fun a => ¬(∀ i,a i ∉ B i)) (fun a i => a i ∈ B i)
    (source_shared_law_nonneg434 S mu hnn) hcov
  have he : (∑ a ∈ Fintype.piFinset S,
      if ∀ i,a i ∉ B i then 0 else sourceSharedLaw434 mu a) =
    ∑ a ∈ Fintype.piFinset S,
      if ¬(∀ i,a i ∉ B i) then sourceSharedLaw434 mu a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : ∀ i,a i ∉ B i <;> simp [h]
  have hU : (∑ a ∈ Fintype.piFinset S,
      if ¬(∀ i,a i ∉ B i) then sourceSharedLaw434 mu a else 0) ≤
      ∑ i : I,∑ a ∈ Fintype.piFinset S,
        if a i ∈ B i then sourceSharedLaw434 mu a else 0 := by
    convert hu using 1
    · apply Finset.sum_congr rfl
      intro a ha
      by_cases hc : ∀ i,a i ∉ B i <;> simp [hc]
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hc : a i ∈ B i <;> simp [hc]
  rw [he]
  apply hU.trans
  calc
    _ = ∑ i : I,∑ p ∈ S i,if p∈B i then mu i p else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact source_shared_law_excluded_mass434 S mu hm i (B i)
    _  ≤  ∑ i : I,(B i).card*(1/(Pmin*vmin)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact source_excluded_atom_card_bound434 (S i) (B i) (mu i)
        (1/(Pmin*vmin)) (by positivity)
        (fun p hp => source_prime_shared_atom_le434 Pmin vmin (V i) p
          hP hv (hPmin i p hp) (hVmin i))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Actual canonical endpoint-ban loss, for every moving J and ell.
There is no auxiliary-distinctness loss and no group-count multiplier. -/
theorem source_original_probe_aux_endpoint_ban_mass434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ) (Pmin vmin : ℝ)
    (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin ≤ V g)
    (hPmin : ∀ g p,p∈P g → Pmin ≤ (p:ℝ))
    (s t : G → Fin (J+ell) → ℕ) :
    (∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m ν P),
      if sourceOriginalProbeAuxEndpointBan434 (J+ell) m ν s t a then 0 else
        sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
          (sourceOriginalProbeAuxV434 m ν V i)) a)  ≤ 
      ((ν.1.card+ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) / (Pmin*vmin) := by
  classical
  let B := fun z : SourceOriginalProbeAuxIndex434 m ν =>
    sourceOriginalProbeEndpointValues434 (J+ell) s t (sourceOriginalProbeAuxGroup434 m ν z)
  have hb (a : SourceOriginalProbeAuxIndex434 m ν → ℕ) :
      sourceOriginalProbeAuxEndpointBan434 (J+ell) m ν s t a ↔
        ∀ z,a z ∉ B z := by
    simp only [sourceOriginalProbeAuxEndpointBan434,B,sourceOriginalProbeEndpointValues434,
      Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,not_or,not_exists]
    constructor
    · intro h z
      exact ⟨fun i hi => (h z i).1 hi.symm, fun i hi => (h z i).2 hi.symm⟩
    · intro h z i
      exact ⟨fun hi => (h z).1 i hi.symm,fun hi => (h z).2 i hi.symm⟩
  simp_rw [hb]
  have hvz : ∀ z,vmin ≤ sourceOriginalProbeAuxV434 m ν V z := by
    intro z; cases z with
    | inl a => exact hVmin a.val.1
    | inr b => exact hVmin b.val.1
  have hh := source_shared_avoidance_mass434
    (sourceOriginalProbeAuxPrimeSets434 m ν P) B (sourceOriginalProbeAuxV434 m ν V)
    Pmin vmin hP hv (source_original_probe_aux_V_mass434 m ν P V hV) hvz
    (source_original_probe_aux_true_min434 m ν P Pmin hPmin)
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (mul_pos hP hv).le
  calc
    _ ≤ ∑ z : SourceOriginalProbeAuxIndex434 m ν,((2*(J+ell):ℕ):ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact_mod_cast source_original_probe_endpoint_values_card434
        (J+ell) s t (sourceOriginalProbeAuxGroup434 m ν z)
    _ = _ := by simp [SourceOriginalProbeAuxIndex434,Fintype.card_sum,Nat.cast_add]
end Green64Analytic.CorrelationSquare

end

/-! ## PhysicalSharedHarmonicEnvelope -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The full labelled shared product retains repeated numerical values. -/
def sourceB574SharedDilation434 {G : Type} [Fintype G]
    (M : ℕ) (E : G → Finset (Fin M)) (s : ∀ g,E g → ℕ) : ℕ :=
  ∏ g,∏ i : E g,s g i

/-- The genuine independent harmonic shared law, without distinctness conditioning. -/
def sourceB574SharedMass434 {G : Type} [Fintype G]
    (M : ℕ) (E : G → Finset (Fin M)) (V : G → ℝ)
    (s : ∀ g,E g → ℕ) : ℝ :=
  ∏ g,∏ i : E g,sourcePrimeSharedAtom434 (V g) (s g i)

/-- Unlike a contraction by D_R^{-1}, this exact identity keeps the
harmonic dilution needed by the actual dirty shared probability estimate. -/
theorem source_B574_labelled_harmonic_mass_exact434
    {G : Type} [Fintype G] [DecidableEq G]
    (M : ℕ) (E : G → Finset (Fin M)) (V : G → ℝ)
    (s : ∀ g,E g → ℕ) :
    (∏ g,((V g:ℂ)^((E g).card))⁻¹)*
      ((sourceB574SharedDilation434 M E s:ℕ):ℂ)⁻¹ =
    (sourceB574SharedMass434 M E V s:ℂ) := by
  classical
  simp only [sourceB574SharedDilation434,sourceB574SharedMass434,
    sourcePrimeSharedAtom434,Nat.cast_prod,Complex.ofReal_mul,
    one_div,mul_inv_rev,Finset.prod_mul_distrib,Finset.prod_inv_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_coe]
  push_cast
  rfl

/-- Nonnegative true shared probability, also for repeated draws. -/
theorem source_B574_shared_mass_nonneg434
    {G : Type} [Fintype G]
    (M : ℕ) (E : G → Finset (Fin M)) (V : G → ℝ)
    (s : ∀ g,E g → ℕ) (hV : ∀ g,0 ≤ V g) :
    0 ≤ sourceB574SharedMass434 M E V s := by
  apply Finset.prod_nonneg
  intro g hg
  apply Finset.prod_nonneg
  intro i hi
  dsimp [sourcePrimeSharedAtom434]
  exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (hV g))

/-- Physical dirty shared rows with their reciprocal D_R RETAINED.
The right side is the true independent shared probability times the
positive original marked endpoint masses. Distinct support counts are
inside sourcePhysicalGroupedHalf434; no valuation parity is substituted. -/
theorem source_B574_actual_dirty_physical_harmonic_pair434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hV : ∀ g,0 ≤ V g)
    (hP : ∀ g p,p ∈ P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h)
    (hM : ∀ g,(E g).card+t g=M)
    (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ a ∈ sourceGlobalSharedCompletions434 P M E s w,
      ∀ b ∈ sourceGlobalSharedCompletions434 P M E s wp,‖F a b‖ ≤ B) :
    let d := sourceB574SharedDilation434 M E s
    ‖(∏ g,((V g:ℂ)^M)⁻¹)*(∏ g,((V g:ℂ)^(t g))⁻¹)*
      (((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ):ℂ)*
      (((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ):ℂ)*(d:ℂ)⁻¹*
      (∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
        ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b)‖ ≤
    q^(-2*(M*Fintype.card G:ℝ))*sourceB574SharedMass434 M E V s*
      B*‖actualBigMarkDecoration P t q V (fun _ => 1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _ => 1) wp‖ := by
  dsimp only
  let d := sourceB574SharedDilation434 M E s
  let A : ℂ := (∏ g,((V g:ℂ)^M)⁻¹)*(∏ g,((V g:ℂ)^(t g))⁻¹)*
    (((sourcePhysicalGroupedHalf434 P M q (d*w))^2:ℝ):ℂ)*
    (((sourcePhysicalGroupedHalf434 P M q (d*wp))^2:ℝ):ℂ)
  let I : ℂ := ∏ g,((V g:ℂ)^((E g).card))⁻¹
  let p1 : ℂ := bigMarkPrefactor P t q V w
  let p2 : ℂ := bigMarkPrefactor P t q V wp
  let R : ℂ := ∑ a ∈ sourceGlobalSharedCompletions434 P M E s w,
    ∑ b ∈ sourceGlobalSharedCompletions434 P M E s wp,F a b
  let Q : ℝ := q^(-2*(M*Fintype.card G:ℝ))
  have hQ : 0 ≤ Q := (Real.rpow_pos_of_pos hq _).le
  have hEnv : ‖A‖ ≤ Q*‖I*p1*p2‖ :=
    source_dirty_physical_scalar_envelope434 P M d t (fun g => (E g).card)
      V q w wp hq hq1 hM
  have hRow : ‖p1*p2*R‖ ≤
      B*‖actualBigMarkDecoration P t q V (fun _ => 1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _ => 1) wp‖ :=
    source_actual_dirty_two_row_positive_majorant434 P M E s t e V q w wp
      hP hs hDisj F B hB hF
  have hMass : ‖I*(d:ℂ)⁻¹‖ = sourceB574SharedMass434 M E V s := by
    rw [source_B574_labelled_harmonic_mass_exact434 M E V s,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (source_B574_shared_mass_nonneg434 M E V s hV)]
  change ‖A*(d:ℂ)⁻¹*R‖ ≤ _
  calc
    _ = ‖A‖*‖(d:ℂ)⁻¹‖*‖R‖ := by simp only [norm_mul]
    _ ≤ (Q*‖I*p1*p2‖)*‖(d:ℂ)⁻¹‖*‖R‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hEnv (norm_nonneg _)) (norm_nonneg _)
    _ = Q*‖I*(d:ℂ)⁻¹‖*‖p1*p2*R‖ := by simp only [norm_mul]; ring
    _ ≤ Q*‖I*(d:ℂ)⁻¹‖*(B*
        ‖actualBigMarkDecoration P t q V (fun _ => 1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _ => 1) wp‖) :=
      mul_le_mul_of_nonneg_left hRow (mul_nonneg hQ (norm_nonneg _))
    _ = _ := by rw [hMass]; dsimp only [Q]; ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## CanonicalSharedRestoration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000

variable {G : Type} [Fintype G] [DecidableEq G]

/-- Original full distinct marked lists at the TRUE labelled shared position. -/
def sourceB574LabelledCompletions434
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (w : ℕ) : Finset (G → Fin M → ℕ) :=
  Fintype.piFinset (fun g =>
    (orderedBigMarks (P g) M (sourceB574SharedDilation434 M E s*w)).filter
      (fun a => ∀ i : E g,a i=s g i))

/-- Repeated shared labels give an empty physical carrier. Consequently the
set-product carrier used by the existing list bijection agrees with the
true labelled-product carrier, on both clean AND dirty shared draws. -/
theorem source_B574_true_labelled_completions_exact434
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : ∀ g,E g → ℕ) (w : ℕ)
    (hs : ∀ g i,s g i ∈ P g)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h) :
    sourceB574LabelledCompletions434 P M E s w =
      sourceGlobalSharedCompletions434 P M E s w := by
  classical
  by_cases hinj : ∀ g,Function.Injective (s g)
  · have hd := source_shared_global_labelled_product434 P M E s hs hinj hDisj
    unfold sourceB574LabelledCompletions434 sourceGlobalSharedCompletions434
      sourceB574SharedDilation434
    rw [hd]
  · have hnew : sourceB574LabelledCompletions434 P M E s w = ∅ := by
      ext a
      constructor
      · intro ha
        exfalso
        apply hinj
        intro g i j hij
        have h := Finset.mem_filter.mp ((Fintype.mem_piFinset.mp ha) g)
        have hInj := (source_ordered_marks_mem434 (P g) M _ (a g)).mp h.1
        apply Subtype.ext
        apply hInj.2
        exact (h.2 i).trans (hij.trans (h.2 j).symm)
      · simp
    have hold : sourceGlobalSharedCompletions434 P M E s w = ∅ := by
      ext a
      constructor
      · intro ha
        exact (hinj (source_global_physical_shared_injective434 P M E s w a ha)).elim
      · simp
    rw [hnew,hold]

/-- The original auxiliary ban on the true pattern-dependent free lists.
Auxiliary values may repeat; no pairwise-distinct auxiliary condition occurs. -/
def sourceB574FreeAuxBan434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) : Prop :=
  ∀ z i,aux z ≠ a (sourceOriginalProbeAuxGroup434 m nu z) i ∧
    aux z ≠ b (sourceOriginalProbeAuxGroup434 m nu z) i

/-- The actual full physical canonical Knu with its original endpoint ban. -/
def sourceB574CanonicalFullKernel434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : G → Fin (J+ell) → ℕ) : ℂ :=
  if sourceOriginalProbeAuxEndpointBan434 (J+ell) m nu a b aux then
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V nu hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V nu hB xi) hA hB
      (sourceOriginalProbeCellA434 m P V nu hA)
      (sourceOriginalProbeCellB434 m P V nu hB)
      (sourceOriginalProbeDA434 m nu aux)
      (sourceOriginalProbeOriginalTargetX434 J ell m hmJ nu b)
      (sourceOriginalProbeDB434 m nu aux)
      (sourceOriginalProbeOriginalSourceX434 J ell m hmJ nu a)
      (nu.1.card+nu.2.card)
  else 0

/-- The unchanged canonical Knu after removing shared labels, with the free ban. -/
def sourceB574CanonicalFreeKernel434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) : ℂ :=
  if sourceB574FreeAuxBan434 J ell m hmJ nu aux a b then
    sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux a b
  else 0

/-- The actual full physical canonical cap is proved, not hypothesized.
Both active cell masses and all primitive characters remain literal. -/
theorem source_B574_canonical_full_kernel_norm434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : G → Fin (J+ell) → ℕ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi) :
    ‖sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi P V aux a b‖ ≤
      (Q:ℝ)^4*(xi⁻¹)^2 := by
  unfold sourceB574CanonicalFullKernel434
  split_ifs
  · exact source_original_actual_primitive_physical_Knu_bound434
      (fun _ : G => J+ell) Q xi hxi
      (sourceOriginalProbeActiveCellsA434 m P V nu hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V nu hB xi) hA hB hhA hhB
      (sourceOriginalProbeCellA434 m P V nu hA)
      (sourceOriginalProbeCellB434 m P V nu hB)
      (fun j hj => (source_original_probe_active_cell_A_mem_iff434 m P V nu hA xi hhA hxi j).mp hj)
      (fun j hj => (source_original_probe_active_cell_B_mem_iff434 m P V nu hB xi hhB hxi j).mp hj)
      (sourceOriginalProbeDA434 m nu aux) (sourceOriginalProbeDB434 m nu aux)
      (nu.1.card+nu.2.card)
      (sourceOriginalProbeOriginalTargetX434 J ell m hmJ nu)
      (sourceOriginalProbeOriginalSourceX434 J ell m hmJ nu) a b
  · simp only [norm_zero]; positivity

theorem source_B574_canonical_free_kernel_norm434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi) :
    ‖sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b‖ ≤
      (Q:ℝ)^4*(xi⁻¹)^2 := by
  unfold sourceB574CanonicalFreeKernel434
  split_ifs
  · exact source_original_probe_canonical_Knu_true_uniform434
      J ell m hmJ nu Q hA hB xi hhA hhB hxi P V aux a b
  · simp only [norm_zero]; positivity

/-- Full auxiliary exclusion splits exactly into shared and free exclusion.
No shared endpoint hit is silently folded into the free auxiliary ban. -/
theorem source_B574_assembled_aux_ban434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J ell m hmJ nu g → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (hsaux : ∀ z i,aux z ≠ s (sourceOriginalProbeAuxGroup434 m nu z) i) :
    sourceOriginalProbeAuxEndpointBan434 (J+ell) m nu
      (sourceOriginalProbeAssembledFull434 J ell m hmJ nu s a)
      (sourceOriginalProbeAssembledFull434 J ell m hmJ nu s b) aux ↔
    sourceB574FreeAuxBan434 J ell m hmJ nu aux a b := by
  classical
  let E := sourceOriginalProbeSharedSlots434 J ell m hmJ nu
  let e := sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ nu
  constructor
  · intro h z i
    let g := sourceOriginalProbeAuxGroup434 m nu z
    have hh := h z (e g i)
    have hleft := congrFun (source_shared_extract_assemble434 (E g) (s g) (e g) (a g)) i
    have hright := congrFun (source_shared_extract_assemble434 (E g) (s g) (e g) (b g)) i
    change aux z ≠ sourceSharedAssemble434 (E g) (s g) (e g) (a g) (e g i) ∧
      aux z ≠ sourceSharedAssemble434 (E g) (s g) (e g) (b g) (e g i) at hh
    rw [hleft,hright] at hh
    exact hh
  · intro h z i
    let g := sourceOriginalProbeAuxGroup434 m nu z
    change aux z ≠ sourceSharedAssemble434 (E g) (s g) (e g) (a g) i ∧
      aux z ≠ sourceSharedAssemble434 (E g) (s g) (e g) (b g) i
    by_cases hi : i ∈ E g
    · simp only [sourceSharedAssemble434,dite_eq_left hi]
      exact ⟨hsaux z ⟨i,hi⟩,hsaux z ⟨i,hi⟩⟩
    · simp only [sourceSharedAssemble434,dite_eq_right hi]
      exact h z ((e g).symm ⟨i,hi⟩)

/-- Canonical physical Knu becomes precisely the original free Knu on a
shared-auxiliary-clean draw. Its inclusion-exclusion sign is unchanged. -/
theorem source_B574_canonical_assembled_kernel434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J ell m hmJ nu g → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (hsaux : ∀ z i,aux z ≠ s (sourceOriginalProbeAuxGroup434 m nu z) i) :
    sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi P V aux
      (sourceOriginalProbeAssembledFull434 J ell m hmJ nu s a)
      (sourceOriginalProbeAssembledFull434 J ell m hmJ nu s b) =
    sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b := by
  unfold sourceB574CanonicalFullKernel434 sourceB574CanonicalFreeKernel434
  rw [source_B574_assembled_aux_ban434 J ell m hmJ nu aux s a b hsaux]
  split_ifs
  · exact (source_original_probe_canonical_full_physical_identity434
      J ell m hmJ nu Q hA hB xi P V aux s a b).symm
  · rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## CanonicalPhysicalSlice -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 12000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- Literal full physical marked slice, including the complete original ban,
true repeated shared dilation, distinct-count half damping and one D_R inverse. -/
def sourceB574CanonicalPhysicalSlice434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J ell m hmJ nu g → ℕ) : ℂ :=
  let E := sourceOriginalProbeSharedSlots434 J ell m hmJ nu
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let d := sourceB574SharedDilation434 (J+ell) E s
  (∏ g,((V g:ℂ)^(J+ell))⁻¹)*(∏ g,((V g:ℂ)^(t g))⁻¹)*
    (((sourcePhysicalGroupedHalf434 P (J+ell) q (d*w))^2:ℝ):ℂ)*
    (((sourcePhysicalGroupedHalf434 P (J+ell) q (d*wp))^2:ℝ):ℂ)*(d:ℂ)⁻¹*
    (∑ a ∈ sourceB574LabelledCompletions434 P (J+ell) E s w,
      ∑ b ∈ sourceB574LabelledCompletions434 P (J+ell) E s wp,
        sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi P V aux a b)

/-- Original stripped marked comparison slice with its actual free-list ban.
There is no artificial shared-law normalization or changed canonical Knu. -/
def sourceB574CanonicalStrippedSlice434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) : ℂ :=
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
    (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
      sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b)

/-- The physical kernel's harmonic-weighted bound with EVERY actual pattern
slot count and its proved canonical cap. No hEnvelope or hKnu premise. -/
theorem source_B574_canonical_physical_slice_bound434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J ell m hmJ nu g → ℕ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
    (hq : 0<q) (hq1 : q≤1) (hV : ∀ g,0≤V g)
    (hP : ∀ g p,p∈P g → p.Prime)
    (hs : ∀ g i,s g i∈P g)
    (hDisj : ∀ g h p,p∈P g → p∈P h → g=h) :
    let E := sourceOriginalProbeSharedSlots434 J ell m hmJ nu
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    ‖sourceB574CanonicalPhysicalSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp s‖ ≤
      q^(-2*((J+ell)*Fintype.card G:ℝ))*sourceB574SharedMass434 (J+ell) E V s*
        ((Q:ℝ)^4*(xi⁻¹)^2)*
        ‖actualBigMarkDecoration P t q V (fun _=>1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _=>1) wp‖ := by
  dsimp only
  unfold sourceB574CanonicalPhysicalSlice434
  dsimp only
  rw [source_B574_true_labelled_completions_exact434 _ _ _ _ w hs hDisj,
    source_B574_true_labelled_completions_exact434 _ _ _ _ wp hs hDisj]
  simpa only [Nat.cast_add] using source_B574_actual_dirty_physical_harmonic_pair434 P (J+ell)
    (sourceOriginalProbeSharedSlots434 J ell m hmJ nu) s
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu)
    (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ nu)
    V q w wp hq hq1 hV hP hs hDisj
    (source_original_probe_shared_free_card434 J ell m hmJ nu)
    (sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi P V aux)
    ((Q:ℝ)^4*(xi⁻¹)^2) (by positivity)
    (fun a _ b _ => source_B574_canonical_full_kernel_norm434
      J ell m hmJ nu Q hA hB xi P V aux a b hhA hhB hxi)

/-- A true marked-list mass bound for the unchanged stripped canonical slice. -/
theorem source_B574_canonical_stripped_slice_bound434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi) :
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    ‖sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp‖ ≤
      ((Q:ℝ)^4*(xi⁻¹)^2)*
        ‖actualBigMarkDecoration P t q V (fun _=>1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _=>1) wp‖ := by
  dsimp only
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let K := sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux
  let cap : ℝ := (Q:ℝ)^4*(xi⁻¹)^2
  have hrow : ‖∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,K a b‖ ≤
      cap*(bigMarkLists P t w).card*(bigMarkLists P t wp).card := by
    calc
      _ ≤ ∑ a ∈ bigMarkLists P t w,‖∑ b ∈ bigMarkLists P t wp,K a b‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,‖K a b‖ :=
        Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,cap :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
          source_B574_canonical_free_kernel_norm434 J ell m hmJ nu Q hA hB xi P V aux a b hhA hhB hxi))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
  have hOne (n : ℕ) : ‖actualBigMarkDecoration P t q V (fun _=>1) n‖ =
      ‖bigMarkPrefactor P t q V n‖*(bigMarkLists P t n).card := by
    simp [actualBigMarkDecoration]
  change ‖bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
    (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,K a b)‖ ≤ _
  rw [norm_mul,norm_mul]
  calc
    _ ≤ ‖bigMarkPrefactor P t q V w‖*‖bigMarkPrefactor P t q V wp‖*
        (cap*(bigMarkLists P t w).card*(bigMarkLists P t wp).card) :=
      mul_le_mul_of_nonneg_left hrow (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by rw [hOne,hOne]; dsimp only [cap]; ring

/-- Actual clean shared restoration is exact for the full canonical kernel,
its physical marked carrier and its full original auxiliary endpoint ban. -/
theorem source_B574_canonical_clean_slice_exact434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J ell m hmJ nu g → ℕ)
    (hq : 0<q) (hP : ∀ g p,p∈P g → p.Prime)
    (hs : ∀ g i,s g i∈P g)
    (hInj : ∀ g,Function.Injective (s g))
    (hAvoid : ∀ g i,¬s g i∣w) (hAvoid' : ∀ g i,¬s g i∣wp)
    (hDisj : ∀ g h p,p∈P g → p∈P h → g=h)
    (hsaux : ∀ z i,aux z ≠ s (sourceOriginalProbeAuxGroup434 m nu z) i) :
    sourceB574CanonicalPhysicalSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp s =
      (sourceB574SharedMass434 (J+ell)
        (sourceOriginalProbeSharedSlots434 J ell m hmJ nu) V s:ℂ)*
      sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp := by
  let C := sourceOriginalProbeFreedSlots434 J m hmJ nu
  let E := sourceOriginalProbeSharedSlots434 J ell m hmJ nu
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  have hd := source_shared_global_labelled_product434 P (J+ell) E s hs hInj hDisj
  have h := source_original_clean_global_pairing434 P J ell C s w wp q V hq hP hs hInj
    hAvoid hAvoid' hDisj (sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi P V aux)
  let d₀ := ∏ p ∈ Finset.univ.biUnion (fun g => sourceSharedPrimeSet434 (E g) (s g)),p
  change (∏ g,((V g:ℂ)^(J+ell))⁻¹)*(∏ g,((V g:ℂ)^(t g))⁻¹)*
      (d₀:ℂ)⁻¹*(((sourcePhysicalGroupedHalf434 P (J+ell) q (d₀*w))^2:ℝ):ℂ)*
      (((sourcePhysicalGroupedHalf434 P (J+ell) q (d₀*wp))^2:ℝ):ℂ)*
      (∑ a ∈ sourceGlobalSharedCompletions434 P (J+ell) E s w,
        ∑ b ∈ sourceGlobalSharedCompletions434 P (J+ell) E s wp,
          sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi P V aux a b) =
    (∏ g,∏ i : E g,((V g:ℂ)*(s g i:ℂ))⁻¹)*
      bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
      (∑ a ∈ bigMarkLists P t w,∑ b ∈ bigMarkLists P t wp,
        sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi P V aux
          (sourceOriginalProbeAssembledFull434 J ell m hmJ nu s a)
          (sourceOriginalProbeAssembledFull434 J ell m hmJ nu s b)) at h
  change (∏ p ∈ Finset.univ.biUnion (fun g => sourceSharedPrimeSet434 (E g) (s g)),p) =
    sourceB574SharedDilation434 (J+ell) E s at hd
  have hMass : (∏ g,∏ i : E g,((V g:ℂ)*(s g i:ℂ))⁻¹) =
      (sourceB574SharedMass434 (J+ell) E V s:ℂ) := by
    unfold sourceB574SharedMass434 sourcePrimeSharedAtom434
    push_cast
    simp only [one_div,mul_comm]
  change d₀ = sourceB574SharedDilation434 (J+ell) E s at hd
  rw [hd] at h
  simp_rw [source_B574_canonical_assembled_kernel434 J ell m hmJ nu Q hA hB xi P V aux s _ _ hsaux] at h
  rw [hMass] at h
  unfold sourceB574CanonicalPhysicalSlice434 sourceB574CanonicalStrippedSlice434
  dsimp only
  rw [source_B574_true_labelled_completions_exact434 _ _ _ _ w hs hDisj,
    source_B574_true_labelled_completions_exact434 _ _ _ _ wp hs hDisj]
  convert h using 1 <;> dsimp only [C,E,t,sourceOriginalProbeSharedSlots434,
    sourceOriginalProbeFreeMarkCount434,sourceOriginalProbeFreeMarkEquiv434] <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## ActualCanonicalRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- Explicit normalization cost of the actual canonical row.  The cost is
retained outside the row; this definition asserts no analytic saving. -/
def sourceB578CanonicalRowScale434 (Q : ℕ) (xi : ℝ) : ℝ :=
  max 1 ((Q:ℝ)^4*(xi⁻¹)^2)

/-- The entire original canonical Knu row with its actual free auxiliary ban,
with a fixed genuine target list.  No delta basis replaces this row. -/
def sourceB578CanonicalRow434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (a : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) : ℂ :=
  sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b /
    (sourceB578CanonicalRowScale434 Q xi:ℂ)

/-- The unit test bound is derived for the full actual row, not assumed. -/
theorem source_B578_actual_canonical_row_norm434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi) :
    ‖sourceB578CanonicalRow434 J ell m hmJ nu Q hA hB xi P V aux b a‖ ≤ 1 := by
  have hs : 0 < sourceB578CanonicalRowScale434 Q xi :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  unfold sourceB578CanonicalRow434
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  apply (div_le_one hs).mpr
  exact (source_B574_canonical_free_kernel_norm434
    J ell m hmJ nu Q hA hB xi P V aux a b hhA hhB hxi).trans (le_max_right _ _)

/-- Exact recovery of the full row, including its explicit normalization cost. -/
theorem source_B578_actual_canonical_row_rescale434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (a b : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi P V aux a b =
      (sourceB578CanonicalRowScale434 Q xi:ℂ)*
        sourceB578CanonicalRow434 J ell m hmJ nu Q hA hB xi P V aux b a := by
  have hs : sourceB578CanonicalRowScale434 Q xi ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  unfold sourceB578CanonicalRow434
  have hc : (sourceB578CanonicalRowScale434 Q xi:ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp

/-- The full stripped physical slice is exactly the sum of full canonical
rows over the actual target marked carrier.  The scale is not discarded. -/
theorem source_B578_actual_canonical_slice_rows434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) :
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp =
      (sourceB578CanonicalRowScale434 Q xi:ℂ)*bigMarkPrefactor P t q V wp*
        ∑ b ∈ bigMarkLists P t wp,
          actualBigMarkDecoration P t q V
            (sourceB578CanonicalRow434 J ell m hmJ nu Q hA hB xi P V aux b) w := by
  dsimp only
  unfold sourceB574CanonicalStrippedSlice434 actualBigMarkDecoration
  dsimp only
  rw [Finset.sum_comm]
  simp_rw [source_B578_actual_canonical_row_rescale434
    J ell m hmJ nu Q hA hB xi P V aux]
  simp_rw [←Finset.mul_sum]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## CanonicalConjugateRowPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- The correct actual endpoint coefficient pair for the full original Knu:
true/source is conjugate(Knu(row,target)/kappa); false/target is the actual
marked-list selector.  Conjugating the FIRST endpoint then restores Knu,
not its conjugate or its square. -/
def sourceB578ActualPairCoef434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (sourceSide : Bool)
    (target a : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) : ℂ :=
  if sourceSide then star (sourceB578CanonicalRow434 J ell m hmJ nu Q hA hB xi P V aux target a)
  else if a=target then 1 else 0

theorem source_B578_actual_pair_coef_norm434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (sourceSide : Bool)
    (target a : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi) :
    ‖sourceB578ActualPairCoef434 J ell m hmJ nu Q hA hB xi P V aux sourceSide target a‖ ≤ 1 := by
  cases sourceSide
  · simp only [sourceB578ActualPairCoef434,Bool.false_eq_true,ite_false]
    split_ifs <;> norm_num
  · simpa only [sourceB578ActualPairCoef434,ite_true,norm_star] using
      source_B578_actual_canonical_row_norm434 J ell m hmJ nu Q hA hB xi P V aux a target hhA hhB hxi

/-- Full original marked canonical slice as the ACTUAL conjugated endpoint
pair, with full target carrier and the exact kappa retained outside the sum.
This is the correct physical row adapter for the B524 ordinary-core bridge;
the B538 hardcoded RAW W1 kernel cannot replace these endpoint weights. -/
theorem source_B578_actual_canonical_conjugated_pairing434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) :
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp =
      (sourceB578CanonicalRowScale434 Q xi:ℂ)*
        ∑ b ∈ bigMarkLists P t wp,
          star (actualBigMarkDecoration P t q V
            (sourceB578ActualPairCoef434 J ell m hmJ nu Q hA hB xi P V aux true b) w)*
          actualBigMarkDecoration P t q V
            (sourceB578ActualPairCoef434 J ell m hmJ nu Q hA hB xi P V aux false b) wp := by
  dsimp only
  rw [source_B578_actual_canonical_slice_rows434]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hstar : star (actualBigMarkDecoration P
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) q V
      (sourceB578ActualPairCoef434 J ell m hmJ nu Q hA hB xi P V aux true b) w) =
      actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) q V
        (sourceB578CanonicalRow434 J ell m hmJ nu Q hA hB xi P V aux b) w := by
    simp only [sourceB578ActualPairCoef434,ite_true,actualBigMarkDecoration,
      star_mul,source_big_mark_prefactor_star434,star_sum,star_star]
    ring
  have htarget : actualBigMarkDecoration P
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) q V
      (sourceB578ActualPairCoef434 J ell m hmJ nu Q hA hB xi P V aux false b) wp =
      bigMarkPrefactor P (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) q V wp := by
    simp [sourceB578ActualPairCoef434,actualBigMarkDecoration,hb]
  rw [hstar,htarget,mul_comm]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalProbeMemoryAuxBan -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Actual Memory assignments reindexed onto the literal independent
finite prime-support family, preserving each numerical value. -/
noncomputable def sourceOriginalProbeMemoryFlatEquiv434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2) :
    SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) ≃
    ↥(Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m ν P)) :=
  (sourceOriginalProbeMemoryPrimeAssignmentEquiv434 P J m hmJ ν hDisj).trans
    ((sourceOriginalTrueAuxPrimeSplitEquiv434 m ν P).symm.trans
      (sourceFiniteListFamilyEquiv434 (sourceOriginalProbeAuxPrimeSets434 m ν P)).symm)

theorem source_original_probe_memory_flat_values434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν))
    (z : SourceOriginalProbeAuxIndex434 m ν) :
    (sourceOriginalProbeMemoryFlatEquiv434 P J m hmJ ν hDisj aux).val z =
      (aux (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν z).1
        (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν z).2).val := by
  cases z <;> rfl

theorem source_original_probe_memory_flat_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (V : G → ℝ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)) :
    sourceAuxMass _ (fun _ p => p.val) J m V
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux =
    sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
      (sourceOriginalProbeAuxV434 m ν V i))
      (sourceOriginalProbeMemoryFlatEquiv434 P J m hmJ ν hDisj aux).val := by
  rw [source_original_probe_memory_assignment_mass434
    _ (fun _ p => p.val) J m hmJ ν hDisj V aux]
  simp only [sourceSharedLaw434,SourceOriginalProbeAuxIndex434,Fintype.prod_sum_type]
  rfl

/-- Weighted finite equality for arbitrary joint real tests on every
actual auxiliary slot. -/
theorem source_original_probe_memory_flat_sum_real434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (V : G → ℝ) (F : (SourceOriginalProbeAuxIndex434 m ν → ℕ) → ℝ) :
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      sourceAuxMass _ (fun _ p => p.val) J m V
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux *
      F (sourceOriginalProbeMemoryFlatEquiv434 P J m hmJ ν hDisj aux).val) =
    ∑ a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m ν P),
      sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m ν V i)) a * F a := by
  classical
  let e := sourceOriginalProbeMemoryFlatEquiv434 P J m hmJ ν hDisj
  calc
    _ = ∑ a : ↥(Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m ν P)),
      sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m ν V i)) a.val * F a.val := by
      apply Fintype.sum_equiv e
      intro aux
      rw [source_original_probe_memory_flat_mass434 P J m hmJ ν hDisj]
    _ = _ := Finset.sum_coe_sort
      (Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m ν P))
      (fun a => sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434
        (sourceOriginalProbeAuxV434 m ν V i)) a * F a)

/-- The original subtype-valued B26 ban is EXACTLY the groupwise
numerical endpoint ban after the true assignment equivalence. -/
theorem source_original_probe_memory_flat_ban434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν))
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    sourceOriginalB26FrozenAuxBan434 _ J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t ↔
    sourceOriginalProbeAuxEndpointBan434 (J+ell) m ν
      (fun g i => (s g i).val) (fun g i => (t g i).val)
      (sourceOriginalProbeMemoryFlatEquiv434 P J m hmJ ν hDisj aux).val := by
  constructor
  · intro h z i
    rw [source_original_probe_memory_flat_values434]
    cases z with
    | inl a =>
      exact ⟨fun he => (h _ _ i).1 (Subtype.ext he),
        fun he => (h _ _ i).2 (Subtype.ext he)⟩
    | inr b =>
      exact ⟨fun he => (h _ _ i).1 (Subtype.ext he),
        fun he => (h _ _ i).2 (Subtype.ext he)⟩
  · intro h g j i
    have hzall : ∀ z : (Σ g : G,sourceOriginalProbeFreedSlots434 J m hmJ ν g),
        aux z.1 z.2 ≠ s z.1 i ∧ aux z.1 z.2 ≠ t z.1 i := by
      intro z
      obtain ⟨u,hu⟩ := (source_original_probe_memory_aux_slot_bijective434
        J m hmJ ν hDisj).surjective z
      subst z
      have hh := h u i
      rw [source_original_probe_memory_flat_values434] at hh
      cases u with
      | inl a =>
        exact ⟨fun he => hh.1 (congrArg Subtype.val he),
          fun he => hh.2 (congrArg Subtype.val he)⟩
      | inr b =>
        exact ⟨fun he => hh.1 (congrArg Subtype.val he),
          fun he => hh.2 (congrArg Subtype.val he)⟩
    exact hzall ⟨g,j⟩

/-- The finite lost mass of the LITERAL B26 auxiliary/active ban.
No fake distinct auxiliary law or hidden fixed slot-count threshold. -/
theorem source_original_B26_actual_aux_ban_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ)
    [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (V : G → ℝ) (Pmin vmin : ℝ)
    (hP : 0 < Pmin) (hv : 0 < vmin)
    (hV : ∀ g,V g = ∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin ≤ V g)
    (hPmin : ∀ g p,p ∈ P g → Pmin ≤ (p:ℝ))
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      if sourceOriginalB26FrozenAuxBan434 _ J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t then 0 else
      sourceAuxMass _ (fun _ p => p.val) J m V
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux) ≤
      ((ν.1.card+ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) / (Pmin*vmin) := by
  classical
  have he := source_original_probe_memory_flat_sum_real434 P J m hmJ ν hDisj V
    (fun a => if sourceOriginalProbeAuxEndpointBan434 (J+ell) m ν
      (fun g i => (s g i).val) (fun g i => (t g i).val) a then 0 else 1)
  simp only [mul_ite,mul_zero,mul_one] at he
  simp_rw [← source_original_probe_memory_flat_ban434] at he
  rw [he]
  exact source_original_probe_aux_endpoint_ban_mass434
    J ell m ν P V Pmin vmin hP hv hV hVmin hPmin _ _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26CanonicalAuxBan -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option stderrAsMessages false

/-- Literal original edge phases have unit modulus in both orientations,
including the complete conjugation of complex K in orientation -1. -/
theorem source_original_edge_scalar_norm434
    (K : ℂ) (ζ theta : ℝ) (n : ℕ) (o k : ℤ) (ho : o=1 ∨ o= -1) :
    ‖originalEdgeScalar K ζ theta n o k‖ = ‖K‖ := by
  rcases ho with rfl | rfl
  · rw [source_original_edge_scalar_positive_fourier434,norm_mul,norm_mul,
      Green64SourceC6.integerPhase_unit,source_original_pure_mellin_phase_norm_one434]
    ring
  · rw [source_original_edge_scalar_negative_conjugate434,norm_star,
      source_original_edge_scalar_positive_fourier434,norm_mul,norm_mul,
      Green64SourceC6.integerPhase_unit,source_original_pure_mellin_phase_norm_one434]
    ring

noncomputable def sourceOriginalProbeMemoryAuxValues434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν)) :
    SourceOriginalProbeAuxIndex434 m ν → ℕ :=
  fun z => (aux (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν z).1
    (sourceOriginalProbeMemoryAuxSlot434 J m hmJ ν z).2).val

noncomputable def sourceOriginalProbeMemoryFreeValues434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (s : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ :=
  fun g i => (s g (sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ ν g i).val).val

/-- The genuine two-GLOBAL source coefficient in the literal Memory
SourcePatternK carrier. Both full independently permuted endpoint lists
and all actual auxiliary coordinates remain arguments. -/
noncomputable def sourceOriginalProbeMemoryCanonicalK434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν))
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g}) : ℂ :=
  sourceOriginalProbeCanonicalKnu434 J ell m hmJ ν Q hA hB xi P V
    (sourceOriginalProbeMemoryAuxValues434 P J m hmJ ν aux)
    (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν s)
    (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν t)

/-- The exact discarded auxiliary contribution in a literal B26
oriented scalar. Its joint ban is estimated separately. -/
noncomputable def sourceOriginalB26CanonicalAuxBanError434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ζ theta : ℝ) (o k : ℤ) : ℂ :=
  ∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
    (sourceAuxMass _ (fun _ p => p.val) J m V
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux : ℂ) *
    (if sourceOriginalB26FrozenAuxBan434 _ J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t then 0 else
     originalEdgeScalar
      (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux
        (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
      ζ theta
      (sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s sigma) o k)

/-- Genuine finite B26 ban error, with the true harmonic measure,
actual Knu, both original endpoint permutations, full divisor,
and either orientation. No operator-smallness premise is assumed. -/
theorem source_original_B26_canonical_aux_ban_error_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (Pmin vmin : ℝ) (hP : 0 < Pmin) (hv : 0 < vmin)
    (hV : ∀ g,V g = ∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin ≤ V g)
    (hPmin : ∀ g p,p ∈ P g → Pmin ≤ (p:ℝ))
    (dsmall : ℕ) (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ζ theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) :
    ‖sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ ν
      Q hA hB xi dsmall s t sigma tau ζ theta o k‖ ≤
    ((ν.1.card+ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) / (Pmin*vmin) *
      ((Q:ℝ)^4*(xi⁻¹)^2) := by
  classical
  run_tac dbg_trace "BAN_START"
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let w := sourceAuxMass (fun g => {p : ℕ // p ∈ P g})
    (fun _ p => p.val) J m V pat
  let ban := fun aux => sourceOriginalB26FrozenAuxBan434 _ J ell m pat aux s t
  let B : ℝ := (Q:ℝ)^4*(xi⁻¹)^2
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  run_tac dbg_trace "BAN_LETS"
  have hw (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m pat) :
      0 ≤ w aux := by
    dsimp [w,sourceAuxMass]
    apply Finset.prod_nonneg
    intro g hg
    apply Finset.prod_nonneg
    intro j hj
    have hvg := hv.trans_le (hVmin g)
    positivity
  run_tac dbg_trace "BAN_MASS_POSITIVE"
  have hK (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m pat) :
      ‖originalEdgeScalar
        (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux
          (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
        ζ theta (sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
          pat aux s sigma) o k‖ ≤ B := by
    run_tac dbg_trace "BAN_K_BEFORE_NORM"
    rw [source_original_edge_scalar_norm434 _ _ _ _ _ _ ho]
    run_tac dbg_trace "BAN_K_AFTER_NORM"
    exact source_original_probe_canonical_Knu_true_uniform434
      J ell m hmJ ν Q hA hB xi hhA hhB hxi P V _ _ _
  run_tac dbg_trace "BAN_K_DONE"
  unfold sourceOriginalB26CanonicalAuxBanError434
  run_tac dbg_trace "BAN_UNFOLD"
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ aux, (if ban aux then 0 else w aux)*B := by
      run_tac dbg_trace "BAN_POINTWISE_ACTUAL"
      apply Finset.sum_le_sum
      intro aux haux
      by_cases hb : ban aux
      · have hb' : sourceOriginalB26FrozenAuxBan434 _ J ell m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t := hb
        simp only [if_pos hb',if_pos hb,mul_zero,norm_zero,zero_mul,le_refl]
      · have hb' : ¬sourceOriginalB26FrozenAuxBan434 _ J ell m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t := hb
        rw [if_neg hb',if_neg hb,norm_mul,Complex.norm_real,Real.norm_eq_abs]
        rw [abs_of_nonneg (hw aux)]
        exact mul_le_mul_of_nonneg_left (hK aux) (hw aux)
    _ = (∑ aux,if ban aux then 0 else w aux)*B := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (source_original_B26_actual_aux_ban_mass434
        P J ell m hmJ ν hDisj V Pmin vmin hP hv hV hVmin hPmin s t) hBnonneg
end Green64Analytic.CorrelationSquare

end

/-! ## CanonicalCollisionIdentification -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The B381 collision coefficient is exactly the already verified canonical
B26 auxiliary-ban error, multiplied only by the original endpoint-pair mass
and the genuine fresh target law. Thus the existing quantitative theorem
applies to the literal collision term; no new probability interface appears. -/
theorem source_original_B381_collision_eq_canonical_aux_ban_error434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ)
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t =>
        sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hB xi aux s t
    (∑ aux : SourceBigAux BP J m pat,
      sourceOriginalB26FrozenAuxCollisionWeight434 BP bm J ell m patterns
        mu V K dsmall zeta theta o k a
        (⟨(),aux,sigma,tau⟩ :
          SourceOriginalB26FrozenFrame434 BP J ell m patterns) b) =
    (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat
        a b sigma tau *
      sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ ν
        Q hA hB xi dsmall a b sigma tau zeta theta o k := by
  dsimp only
  unfold sourceOriginalB26FrozenAuxCollisionWeight434
    sourceOriginalB26CanonicalAuxBanError434
  dsimp only
  simp only [ho,hk,true_and,if_pos,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aux haux
  by_cases hb :
      sourceOriginalB26FrozenAuxBan434 (fun g => {p : ℕ // p ∈ P g})
        J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux a b
  · simp [hb]
  · simp [hb, hk] <;> ring

/-- Quantitative fixed-endpoint form of the same identification. It keeps
the true joint canonical K, full dependent divisor and either orientation.
Only the normalized endpoint-pair mass and literal fresh law remain. -/
theorem source_original_B381_collision_canonical_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m≤J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ)
    (a b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t =>
        sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
          Q hA hB xi aux s t
    ‖(∑ aux : SourceBigAux BP J m pat,
      sourceOriginalB26FrozenAuxCollisionWeight434 BP bm J ell m patterns
        mu V K dsmall zeta theta o k a
        (⟨(),aux,sigma,tau⟩ :
          SourceOriginalB26FrozenFrame434 BP J ell m patterns) b)‖ ≤
    bigEndpointPairMass (BG := G) (J+ell) *
      ‖sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat
        a b sigma tau‖ *
      (((ν.1.card+ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin) * ((Q:ℝ)^4*(xi⁻¹)^2)) := by
  dsimp only
  rw [source_original_B381_collision_eq_canonical_aux_ban_error434
    P V J ell m hmJ ν Q hA hB xi mu dsmall a b sigma tau
    zeta theta o k ho hk]
  have hmass : 0 ≤ bigEndpointPairMass (BG := G) (J+ell) := by
    unfold bigEndpointPairMass
    exact Finset.prod_nonneg (fun _ _ =>
      (Green64SmallHaar.permutationPairMass_positive (J+ell)).le)
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hmass]
  exact mul_le_mul_of_nonneg_left
    (source_original_B26_canonical_aux_ban_error_bound434
      P V J ell m hmJ ν hDisj Q hA hB xi hhA hhB hxi
      Pmin vmin hP hv hV hVmin hPmin dsmall a b sigma tau
      zeta theta o k ho)
    (mul_nonneg
      hmass (norm_nonneg _))

end Green64Analytic.CorrelationSquare

end

end

/-! ## AuxDependentCollisionTestBound -/

section

open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The actual B26 collision with a test that may depend on the whole AUX
coordinate. This keeps the original source harmonic law, moving source D,
canonical joint Knu and either physical orientation. In particular, a Fock/
OLD or character test cannot be pulled outside the AUX sum by fiat. -/
def sourceOriginalB26CanonicalAuxTestError434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ)
    (test : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) → ℂ) : ℂ :=
  ∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
    (sourceAuxMass _ (fun _ p => p.val) J m V
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux : ℂ) *
      (if sourceOriginalB26FrozenAuxBan434 _ J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t then 0 else
       originalEdgeScalar
        (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux
          (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
        zeta theta
        (sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s sigma)
        o k * test aux)

/-- Uniform quantitative B26 collision bound, with an AUX-dependent test
*inside* the canonical finite sum. Thus no cancellation between different
AUX values is needed. It applies whenever the actual physical test admits
an independent pointwise norm bound. -/
theorem source_original_B26_canonical_aux_dependent_test_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hB xi : ℝ) (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (Pmin vmin : ℝ) (hP : 0 < Pmin) (hv : 0 < vmin)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVmin : ∀ g, vmin ≤ V g)
    (hPmin : ∀ g p, p ∈ P g → Pmin ≤ (p:ℝ))
    (dsmall : ℕ) (s t : ∀ g, Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (test : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hTest : ∀ aux, ‖test aux‖ ≤ M) :
    ‖sourceOriginalB26CanonicalAuxTestError434 P V J ell m hmJ ν
      Q hA hB xi dsmall s t sigma tau zeta theta o k test‖ ≤
    (((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) / (Pmin*vmin)) *
      ((Q:ℝ)^4*(xi⁻¹)^2) * M := by
  classical
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let w := sourceAuxMass (fun g => {p : ℕ // p ∈ P g})
    (fun _ p => p.val) J m V pat
  let ban := fun aux => sourceOriginalB26FrozenAuxBan434 _ J ell m pat aux s t
  let B : ℝ := (Q:ℝ)^4*(xi⁻¹)^2
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hw (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m pat) :
      0 ≤ w aux := by
    dsimp [w, sourceAuxMass]
    apply Finset.prod_nonneg
    intro g hg
    apply Finset.prod_nonneg
    intro j hj
    have hvg := hv.trans_le (hVmin g)
    positivity
  have hK (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m pat) :
      ‖originalEdgeScalar
        (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux
          (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
        zeta theta
        (sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
          pat aux s sigma) o k‖ ≤ B := by
    rw [source_original_edge_scalar_norm434 _ _ _ _ _ _ ho]
    exact source_original_probe_canonical_Knu_true_uniform434
      J ell m hmJ ν Q hA hB xi hhA hhB hxi P V _ _ _
  have hBM : 0 ≤ B*M := mul_nonneg hBnonneg hM
  unfold sourceOriginalB26CanonicalAuxTestError434
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ aux, (if ban aux then 0 else w aux) * (B*M) := by
      apply Finset.sum_le_sum
      intro aux haux
      by_cases hb : ban aux
      · have hb' : sourceOriginalB26FrozenAuxBan434 _ J ell m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t := hb
        simp only [if_pos hb', if_pos hb, mul_zero, norm_zero, zero_mul, le_refl]
      · have hb' : ¬ sourceOriginalB26FrozenAuxBan434 _ J ell m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t := hb
        rw [if_neg hb', if_neg hb, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw aux), norm_mul]
        apply mul_le_mul_of_nonneg_left _ (hw aux)
        calc
          ‖originalEdgeScalar
            (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux
              (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
            zeta theta
            (sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
              pat aux s sigma) o k‖ * ‖test aux‖ ≤ B*‖test aux‖ :=
                mul_le_mul_of_nonneg_right (hK aux) (norm_nonneg _)
          _ ≤ B*M := mul_le_mul_of_nonneg_left (hTest aux) hBnonneg
    _ = (∑ aux, if ban aux then 0 else w aux) * (B*M) := by rw [Finset.sum_mul]
    _ ≤ (((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * (B*M) :=
      mul_le_mul_of_nonneg_right
        (source_original_B26_actual_aux_ban_mass434
          P J ell m hmJ ν hDisj V Pmin vmin hP hv hV hVmin hPmin s t) hBM
    _ = (((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2) * M := by dsimp [B]; ring

end Green64Analytic.CorrelationSquare

end

end

