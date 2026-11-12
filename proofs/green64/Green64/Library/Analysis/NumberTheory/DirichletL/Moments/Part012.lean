module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.AddedZeroUniform -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

theorem uniform_tuple_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ N →
      ∀ (S : Finset (Fin (n + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin (n + 2) → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  let D (n : ℕ) := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose
  have hD (n : ℕ) : 0 < D n := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.1
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  let C := 1 + (Finset.range (N + 1)).sup' hne D
  have hzero : D 0 ≤ (Finset.range (N + 1)).sup' hne D :=
    Finset.le_sup' D (by simp : 0 ∈ Finset.range (N + 1))
  refine ⟨C, by dsimp [C]; linarith [hD 0], ?_⟩
  intro n hn S hS β B Y T hB hY hT hβ hN
  have hDn : D n ≤ C := by
    have h := Finset.le_sup' D (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    dsimp only [C]
    linarith
  have he := (tuple_added_zero_energy (n + 2) (by omega) ε hε).choose_spec.2
    S hS β B Y T hB hY hT hβ hN
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hT.le)
  exact mul_le_mul_of_nonneg_right hDn (sq_nonneg _)

abbrev Tuple (ι : Type*) := (ι ⊕ Fin 2) → Ideal O

def coordinateEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    ι ⊕ Fin 2 ≃ Fin (n + 2) := (e.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv

def tupleEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    Tuple ι ≃ (Fin (n + 2) → Ideal O) :=
  (coordinateEquiv e).arrowCongr (Equiv.refl (Ideal O))

def finiteTupleProduct {ι : Type*} [Fintype ι] (v : Tuple ι) : Ideal O := ∏ i, v i

lemma tupleEquiv_slot {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (i : ι) :
    tupleEquiv e v ((e i).castAdd 2) = v (Sum.inl i) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inl i) = (e i).castAdd 2 := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inl, finSumFinEquiv_apply_left]
  rw [← h, Equiv.symm_apply_apply]

lemma tupleEquiv_plain {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) (v : Tuple ι) (j : Fin 2) :
    tupleEquiv e v (j.natAdd n) = v (Sum.inr j) := by
  change v ((coordinateEquiv e).symm _) = _
  have h : coordinateEquiv e (Sum.inr j) = j.natAdd n := by
    simp only [coordinateEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Equiv.refl_apply]
  rw [← h, Equiv.symm_apply_apply]

theorem tupleProduct_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (v : Tuple ι) :
    tupleProduct (tupleEquiv e v) = finiteTupleProduct v := by
  exact (coordinateEquiv e).symm.prod_comp v

def originalFiniteCoefficient {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j, ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j)) *
    idealWeight c χ R t (finiteTupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * v (Sum.inr 0)) (b₂ * v (Sum.inr 1)) *
    (if s ∣ finiteTupleProduct v then 1 else 0)

theorem originalCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) :
    originalCoefficient n c χ R t (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j))
      (fun j => P (e.symm j)) W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (tupleEquiv e v) =
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v := by
  have hslot (j : Fin n) : tupleEquiv e v (j.castAdd 2) = v (Sum.inl (e.symm j)) := by
    simpa only [Equiv.apply_symm_apply] using tupleEquiv_slot e v (e.symm j)
  have hp₀ : (⟨n, by omega⟩ : Fin (n + 2)) = (0 : Fin 2).natAdd n := by ext; simp
  have hp₁ : (⟨n + 1, by omega⟩ : Fin (n + 2)) = (1 : Fin 2).natAdd n := by ext; simp
  simp only [originalCoefficient, originalFiniteCoefficient, tupleProduct_reindex,
    hslot, hp₀, hp₁, tupleEquiv_plain]
  rw [e.symm.prod_comp (fun j => ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j))]

lemma reindex_supported {ι : Type*} [Fintype ι] {n : ℕ} (e : ι ≃ Fin n)
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) :
    ∀ w ∈ S.image (tupleEquiv e), Supported (tupleProduct w) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  rw [tupleProduct_reindex]
  exact hS v hv

def finiteGaussZero {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) : ℂ :=
  gaussPolynomial (Finset.univ : Finset S)
    (fun v => primaryGenerator (finiteTupleProduct v.val))
    (fun v => (supported_span_primaryGenerator_iff (finiteTupleProduct v.val)).mpr (hS v.val v.property))
    (fun v => β v.val) 0

theorem finiteGaussZero_reindex {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι))
    (hS : ∀ v ∈ S, Supported (finiteTupleProduct v)) (β : Tuple ι → ℂ) :
    finiteGaussZero S hS β =
      idealAddedZero (tupleColumns (S.image (tupleEquiv e)))
        (tupleColumns_supported _ (reindex_supported e S hS))
        (tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w))) := by
  rw [← actual_tuple_gauss_eq_columns (S.image (tupleEquiv e)) (reindex_supported e S hS)
    (fun w => β ((tupleEquiv e).symm w))]
  unfold finiteGaussZero gaussPolynomial
  apply Finset.sum_bij (fun v _ => (⟨tupleEquiv e v.val,
    Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩ : S.image (tupleEquiv e)))
  · intros; exact Finset.mem_univ _
  · intro v hv w hw he
    apply Subtype.ext
    exact (tupleEquiv e).injective (congrArg Subtype.val he)
  · intro w hw
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp w.property
    exact ⟨⟨v, hv⟩, Finset.mem_univ _, Subtype.ext he⟩
  · intro v hv
    simp only [Equiv.symm_apply_apply, tupleProduct_reindex]

theorem uniform_finite_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (B Y T : ℝ), 0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_tuple_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β B Y T hB hY hT hβ hN
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β]
  apply he (Fintype.card ι) hn _ (reindex_supported e S hS) _ B Y T hB hY hT
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [Equiv.symm_apply_apply] using hβ v hv
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    simpa only [tupleProduct_reindex] using hN v hv

theorem originalFiniteCoefficient_norm_le {ι : Type*} [Fintype ι]
    (c : O) (hc : c ≠ 0) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : ι → ℝ) (B₁ B₂ : ℝ) (hBslot : ∀ j, 0 ≤ Bslot j)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Tuple ι) (hv : finiteTupleProduct v ≠ 0) :
    ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  let e := Fintype.equivFin ι
  rw [← originalCoefficient_reindex e]
  have he := originalCoefficient_norm_le (Fintype.card ι) c hc χ R t
    (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j => Bslot (e.symm j)) B₁ B₂
    (fun j => hBslot _) hB₁ hB₂ (fun j I => hν _ I) (fun j x => hWslot _ x) hW₁ hW₂
    (tupleEquiv e v) (by rwa [tupleProduct_reindex])
  simpa only [e.symm.prod_comp Bslot] using he

theorem original_subset_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) →
      ‖(Real.sqrt T : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ _ Y T
    (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hY hT _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

theorem empty_finiteTupleProduct {α : Type*} (v : Tuple (∅ : Finset α)) :
    finiteTupleProduct v = v (Sum.inr 0) * v (Sum.inr 1) := by
  simp only [finiteTupleProduct, Fintype.prod_sum_type, Fin.prod_univ_two]
  have he : (∏ j : (∅ : Finset α), v (Sum.inl j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    exact False.elim (Finset.notMem_empty j.val j.property)
  rw [he, one_mul]

lemma reindexCoefficient_mask {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (s : Ideal O)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I = 0 := by
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨hwS, hwI⟩ := Finset.mem_filter.mp hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwS
  simp only [Equiv.symm_apply_apply]
  apply hmask v hv
  rwa [← tupleProduct_reindex e v, hwI]

lemma reindexColumns_norm {ι : Type*} [Fintype ι] {n : ℕ}
    (e : ι ≃ Fin n) (S : Finset (Tuple ι)) (Y : ℝ)
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y) :
    ∀ I ∈ tupleColumns (S.image (tupleEquiv e)), (Ideal.absNorm I : ℝ) ≤ Y := by
  intro I hI
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  simpa only [tupleProduct_reindex] using hN v hv

theorem finiteGaussZero_nonzero_mask_norm {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Y : ℝ) (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Y)
    (hz : finiteGaussZero S hS β ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_norm _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Y (reindexColumns_norm e S Y hN) hz

theorem finiteGaussZero_nonzero_mask_dyad {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
    (β : Tuple ι → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0)
    (Z a s₀ θ : ℝ) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ))
    (hz : finiteGaussZero S hS β ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  let e := Fintype.equivFin ι
  rw [finiteGaussZero_reindex e S hS β] at hz
  exact idealAddedZero_nonzero_mask_dyad _ _ _ s hs
    (fun I _ => reindexCoefficient_mask e S β s hmask I) Z a s₀ θ hZ hNs
    (reindexColumns_norm e S (Z ^ (a + θ)) hN) hz

lemma originalFiniteCoefficient_mask {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Tuple ι) (hs : ¬s ∣ finiteTupleProduct v) :
    originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalFiniteCoefficient, hs, ite_false, mul_zero]

theorem uniform_finite_source_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι ≤ N →
      ∀ (S : Finset (Tuple ι)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (β : Tuple ι → ℂ) (s : Ideal O), Squarefree s →
      (∀ v ∈ S, ¬s ∣ finiteTupleProduct v → β v = 0) →
      ∀ (B Z a s₀ θ : ℝ), 0 ≤ B → 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS β‖ ^ 2 ≤
        C * B ^ 2 * Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_energy N ε hε
  refine ⟨C, hC, ?_⟩
  intro ι inst hn S hS β s hs hmask B Z a s₀ θ hB hZ hNs hβ hN
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  by_cases hz : finiteGaussZero S hS β = 0
  · rw [hz, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) (Real.rpow_nonneg hZ0.le _)
  · obtain ⟨ha, hss⟩ := finiteGaussZero_nonzero_mask_dyad S hS β s hs hmask Z a s₀ θ hZ hNs hN hz
    have hY : 1 ≤ Z ^ (a + θ) := Real.one_le_rpow hZ.le (by linarith)
    have hb := he hn S hS β B (Z ^ (a + θ)) (Z ^ a) hB hY
      (Real.rpow_pos_of_pos hZ0 _) hβ hN
    have hp : (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) =
        Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by
      rw [← Real.rpow_neg hZ0.le, ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
      congr 1
      ring
    calc
      _ ≤ C * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 + ε : ℝ) := hb
      _ = C * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3 + ε * (a + θ)) := by rw [mul_assoc, hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ.le
          (by linarith [added_zero_exponent a s₀ θ ha hss]))
        (mul_nonneg hC.le (sq_nonneg _))

theorem original_subset_source_energy {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O), Squarefree s →
      ∀ (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Z a s₀ θ : ℝ), 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 *
          Z ^ (a - s₀ + 2 * θ + ε * (a + θ)) := by
  obtain ⟨C, hC, he⟩ := uniform_finite_source_energy A.card ε hε
  refine ⟨C, hC, ?_⟩
  intro J hJA c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s hs Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Z a s₀ θ hZ hNs hN
  have hcard : Fintype.card J ≤ A.card := by
    simpa only [Fintype.card_coe] using Finset.card_le_card hJA
  apply he hcard S hS _ s hs
    (fun v _ => originalFiniteCoefficient_mask c χ R t
      (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
      W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v)
    _ Z a s₀ θ (mul_nonneg (Finset.prod_nonneg hBslot) (by positivity)) hZ hNs _ hN
  intro v hv
  have hb := originalFiniteCoefficient_norm_le c hc χ R t
    (fun j : J => ν j.val) (fun j : J => Wslot j.val) (fun j : J => P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s (fun j : J => Bslot j.val) B₁ B₂
    (fun j => hBslot j.val j.property) hB₁ hB₂
    (fun j I => hν j.val j.property I) (fun j x => hWslot j.val j.property x)
    hW₁ hW₂ v (hS v hv).1
  simpa only [Finset.prod_coe_sort J Bslot] using hb

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RadicalFamily -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstFamily CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem elementCoeff_power_pos (χ : Character) (e : ℕ) (he : 0<e) (n : O) :
    elementCoeff (χ.power e) n=(elementCoeff χ n)^e := by
  by_cases hn : IsUnit (Ideal.Quotient.mk χ.modulus n)
  · exact elementCoeff_power_of_unit χ e n hn
  · have hz : elementCoeff χ n=0 := MulChar.map_nonunit _ hn
    have hp : elementCoeff (χ.power e) n=0 := MulChar.map_nonunit _ hn
    rw [hp,hz,zero_pow (Nat.ne_zero_of_lt he)]

theorem exists_product_presentation {ι : Type*} (S : Finset ι) (base : Character)
    (χ : ι→Character) (e : ι→ℕ) (he : ∀i∈S,0<e i)
    (M : Ideal O) (hb : M≤base.modulus) (hχ : ∀i∈S,M≤(χ i).modulus) :
    ∃τ : Character,M≤τ.modulus ∧ ∀n:O,
      elementCoeff τ n=elementCoeff base n*∏i∈S,(elementCoeff (χ i) n)^(e i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨base,hb,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨τ,hτ,ht⟩ := ih (fun i hi=>he i (Finset.mem_insert_of_mem hi))
      (fun i hi=>hχ i (Finset.mem_insert_of_mem hi))
    refine ⟨τ.product ((χ a).power (e a)),le_inf hτ (hχ a (Finset.mem_insert_self _ _)),?_⟩
    intro n
    rw [elementCoeff_product,elementCoeff_power_pos _ _ (he a (Finset.mem_insert_self _ _)),
      ht,Finset.prod_insert ha]
    ring

theorem single_row_on_base (η : Character) (m p n : O)
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (hn : rowTwist (elementHom η) m 1 1 n≠0) :
    rowTwist (elementHom (η.power 0)) m 1 p n=idealRowHom p (Ideal.span {n}) := by
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  have hη : elementCoeff η n≠0 := left_ne_zero_of_mul hn
  have hunit := MulChar.apply_ne_zero_iff.mp hη
  have hp : elementCoeff (η.power 0) n=1 := by
    rw [elementCoeff_power_of_unit η 0 n hunit,pow_zero]
  have hm : IsCoprime m n := by
    by_contra h
    apply hn
    rw [rowTwist_extract_sixth_mask _ m 1 1 n hs]
    simp [coprimalityMask,h]
  rw [rowTwist_extract_sixth_mask _ m 1 p n hs]
  change elementCoeff (η.power 0) n*coprimalityMask m n*idealRowHom (1^4*p) _=_
  rw [hp,one_pow,one_mul]
  simp [coprimalityMask,hm]

theorem row_product_formula {ι : Type*} (S : Finset ι)
    (η : Character) (m : O) (p : ι→O) (e : ι→ℕ)
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m) (n : O) :
    rowTwist (elementHom η) m 1 1 n*
      (∏i∈S,(rowTwist (elementHom (η.power 0)) m 1 (p i) n)^(e i))=
      rowTwist (elementHom η) m 1 (∏i∈S,(p i)^(e i)) n := by
  conv_rhs => rw [rowTwist_row_factor]
  by_cases hn : rowTwist (elementHom η) m 1 1 n=0
  · rw [hn,zero_mul,zero_mul]
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  congr 1
  simp_rw [single_row_on_base η m _ n hmLam hm2 hn]
  induction S using Finset.induction_on with
  | empty => simpa using (idealRowHom_one_supported (Ideal.span {n}) hs).symm
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,idealRowHom_argument_mul,
      idealRowHom_argument_pow _ _ _ hs,ih]

theorem exists_radical_row_presentation {ι : Type*} [Fintype ι]
    (η : Character) (m : O) (hm : m≠0) (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (p : ι→O) (hp : ∀i,Supported (Ideal.span {p i}))
    (e : ι→ℕ) (he : ∀i,0<e i) :
    ∃τ : Character,
      η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*(∏i,Ideal.span {p i})≤τ.modulus ∧
      τ.modulus.absNorm≤η.modulus.absNorm*(Ideal.span {m}).absNorm*
        (Ideal.span {(72:O)}).absNorm*∏i,(Ideal.span {p i}).absNorm ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (∏i,(p i)^(e i)) n := by
  obtain ⟨base,hbase,hbasec⟩ := exists_supported_row_presentation η m 1 hm
    CenteredMomentAddedZero.supported_one_element hmLam hm2
  choose χ hχ hc using fun i=>exists_supported_row_presentation (η.power 0) m (p i) hm
    (hp i) hmLam hm2
  let B := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}
  let M := B*∏i,Ideal.span {p i}
  have hb : M≤base.modulus := by
    rw [hbase,Ideal.span_singleton_one,←Ideal.one_eq_top,mul_one]
    exact Ideal.mul_le_left
  have hch (i : ι) : M≤(χ i).modulus := by
    rw [hχ i]
    change B*(∏j,Ideal.span {p j})≤B*Ideal.span {p i}
    apply Ideal.dvd_iff_le.mp
    exact mul_dvd_mul_left B (Finset.dvd_prod_of_mem (fun j=>Ideal.span {p j}) (Finset.mem_univ i))
  obtain ⟨τ,hM,ht⟩ := exists_product_presentation Finset.univ base χ e (fun i _=>he i) M hb
    (fun i _=>hch i)
  have hMn : M≠0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (Finset.prod_ne_zero_iff.mpr (fun i _=>(hp i).1))
  refine ⟨τ,hM,?_,?_⟩
  · have hd : τ.modulus∣M := Ideal.dvd_iff_le.mpr hM
    have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hMn))
      (map_dvd Ideal.absNorm hd)
    simpa only [M,B,map_mul,map_prod] using hn
  · intro n
    rw [ht,hbasec]
    simp_rw [hc]
    exact row_product_formula Finset.univ η m p e hmLam hm2 n

end SevenEighths.CenteredMomentRadicalFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceMass -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceMass
open CenteredMomentAddedZero CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

def idealBall (H : ℝ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).toFinset.filter
    (fun I => I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H)

@[simp] theorem mem_idealBall (H : ℝ) (I : Ideal O) :
    I ∈ idealBall H ↔ I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_,h⟩
    apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).mem_toFinset.mpr
    exact_mod_cast h.2.trans (Nat.le_ceil H)

lemma idealBall_card (H : ℝ) (hH : 0 ≤ H) :
    ((idealBall H).card : ℝ) ≤ 128*H := by
  by_cases hs : (idealBall H).Nonempty
  · obtain ⟨I,hI⟩ := hs
    have hI := (mem_idealBall H I).mp hI
    have hn : (1:ℝ) ≤ Ideal.absNorm I := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)
    exact DescentFiberCost.finite_ideal_count_real _ H (hn.trans hI.2)
      (fun J hJ => ((mem_idealBall H J).mp hJ).1)
      (fun J hJ => ((mem_idealBall H J).mp hJ).2)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

def tupleBox {r : ℕ} (H : Fin r → ℝ) : Finset (Fin r → Ideal O) :=
  Fintype.piFinset (fun i => idealBall (H i))

@[simp] lemma mem_tupleBox {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O) :
    v ∈ tupleBox H ↔ ∀ i, v i ≠ 0 ∧ (Ideal.absNorm (v i):ℝ) ≤ H i := by
  simp [tupleBox]

lemma tupleBox_card {r : ℕ} (H : Fin r → ℝ) (hH : ∀ i, 0 ≤ H i) :
    ((tupleBox H).card:ℝ) ≤ 128^r * ∏ i, H i := by
  simp only [tupleBox,Fintype.card_piFinset,Nat.cast_prod]
  calc
    (∏ i, ((idealBall (H i)).card:ℝ)) ≤ ∏ i, 128*H i :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => idealBall_card _ (hH i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

def profileProduct {r : ℕ} (W : Fin r → ℝ → ℂ) (q : Fin r → ℝ)
    (v : Fin r → Ideal O) : ℂ := ∏ i, W i ((Ideal.absNorm (v i):ℝ)/q i)

lemma profileProduct_mem_box {r : ℕ} (W : Fin r → ℝ → ℂ) (b q : Fin r → ℝ)
    (hq : ∀ i, 0<q i) (hzero : ∀ i, W i 0=0)
    (hs : ∀ i x, W i x ≠ 0 → x ≤ b i)
    (v : Fin r → Ideal O) (hv : profileProduct W q v ≠ 0) :
    v ∈ tupleBox (fun i => b i*q i) := by
  apply (mem_tupleBox _ _).mpr
  intro i
  have hw : W i ((Ideal.absNorm (v i):ℝ)/q i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hv) i (Finset.mem_univ i)
  refine ⟨?_,(div_le_iff₀ (hq i)).mp (hs i _ hw)⟩
  intro hz
  apply hw
  simp only [hz,map_zero,Nat.cast_zero,zero_div,hzero]

lemma profileProduct_norm_le {r : ℕ} (W : Fin r → ℝ → ℂ) (q B : Fin r → ℝ)
    (hW : ∀ i x, ‖W i x‖ ≤ B i) (v : Fin r → Ideal O) :
    ‖profileProduct W q v‖ ≤ ∏ i, B i := by
  rw [profileProduct,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hW i _)

theorem profileProduct_mass {r : ℕ} (W : Fin r → ℝ → ℂ) (b q B : Fin r → ℝ)
    (hb : ∀ i, 0≤b i) (hq : ∀ i, 0<q i) (hB : ∀ i, 0≤B i)
    (hzero : ∀ i, W i 0=0) (hs : ∀ i x, W i x ≠ 0 → x≤b i)
    (hW : ∀ i x, ‖W i x‖≤B i) (S : Finset (Fin r → Ideal O)) :
    (∑ v ∈ S, ‖profileProduct W q v‖) ≤
      (∏ i, B i) * (128^r * ∏ i, b i*q i) := by
  let F := S.filter (fun v => profileProduct W q v ≠ 0)
  have hsum : (∑ v ∈ S, ‖profileProduct W q v‖) = ∑ v ∈ F, ‖profileProduct W q v‖ := by
    symm
    apply Finset.sum_filter_of_ne
    intro v _ hv
    exact norm_ne_zero_iff.mp hv
  have hsub : F ⊆ tupleBox (fun i => b i*q i) := by
    intro v hv
    exact profileProduct_mem_box W b q hq hzero hs v (Finset.mem_filter.mp hv).2
  have hcard : (F.card:ℝ) ≤ 128^r * ∏ i, b i*q i :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (tupleBox_card _ (fun i => mul_nonneg (hb i) (hq i).le))
  rw [hsum]
  calc
    _ ≤ ∑ _v ∈ F, ∏ i, B i := Finset.sum_le_sum (fun v _ => profileProduct_norm_le W q B hW v)
    _ = (F.card:ℝ)*(∏ i, B i) := by simp
    _ ≤ (128^r * ∏ i, b i*q i)*(∏ i, B i) :=
      mul_le_mul_of_nonneg_right hcard (Finset.prod_nonneg (fun i _ => hB i))
    _ = _ := by ring

def sourceProfiles {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) :
    Fin (N+2) → ℝ → ℂ := Fin.append Wslot ![W₁,W₂]

def sourceScales {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    Fin (N+2) → ℝ :=
  Fin.append P ![X₁/(Ideal.absNorm B₁:ℝ),X₂/(Ideal.absNorm B₂:ℝ)]

def sourceBounds {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) : Fin (N+2) → ℝ :=
  Fin.append b ![b₁,b₂]

lemma sourceProfiles_product {N : ℕ} (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O) :
    profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v =
      (∏ j : Fin N, Wslot j ((Ideal.absNorm (v (j.castAdd 2)):ℝ)/P j)) *
      (W₁ ((Ideal.absNorm (B₁*v ⟨N,by omega⟩):ℝ)/X₁) *
       W₂ ((Ideal.absNorm (B₂*v ⟨N+1,by omega⟩):ℝ)/X₂)) := by
  simp only [profileProduct,Fin.prod_univ_add,sourceProfiles,sourceScales,
    Fin.append_left,Fin.append_right,Fin.prod_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,map_mul,Nat.cast_mul,div_div_eq_mul_div]
  have h₀ : Fin.natAdd N (0:Fin 2)=⟨N,by omega⟩ := by ext; simp
  have h₁ : Fin.natAdd N (1:Fin 2)=⟨N+1,by omega⟩ := by ext; simp
  rw [h₀,h₁]
  congr 2 <;> congr 1 <;> ring

lemma sourceBounds_product {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ) :
    (∏ i, sourceBounds b b₁ b₂ i) = (∏ j,b j)*b₁*b₂ := by
  simp only [sourceBounds,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceScales_product {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∏ i, sourceScales P X₁ X₂ B₁ B₂ i) =
      (∏ j,P j)*(X₁*X₂)/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂) := by
  simp only [sourceScales,Fin.prod_univ_add,Fin.append_left,Fin.append_right,
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  ring

lemma sourceBounds_nonneg {N : ℕ} (b : Fin N → ℝ) (b₁ b₂ : ℝ)
    (hb : ∀ j, 0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) :
    ∀ i, 0≤ sourceBounds b b₁ b₂ i := by
  simp only [Fin.forall_fin_add,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hb,hb₁,hb₂⟩

lemma sourceScales_pos {N : ℕ} (P : Fin N → ℝ) (X₁ X₂ : ℝ) (B₁ B₂ : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : B₁≠0) (hB₂ : B₂≠0) :
    ∀ i, 0<sourceScales P X₁ X₂ B₁ B₂ i := by
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  simp only [Fin.forall_fin_add,sourceScales,Fin.append_left,Fin.append_right,Fin.forall_fin_two]
  exact ⟨hP,div_pos hX₁ hn₁,div_pos hX₂ hn₂⟩

theorem originalCoefficient_factor (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v =
      (∏ j,ν j (v (j.castAdd 2))) * idealWeight c χ R t (tupleProduct v) *
      (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v -
       profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v) *
      (if s∣tupleProduct v then 1 else 0) := by
  rw [originalCoefficient,Finset.prod_mul_distrib,sourceProfiles_product,sourceProfiles_product]
  unfold idealRectangle
  ring

def sourcePool {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : Finset (Fin (N+2) → Ideal O) :=
  ((tupleBox (fun i => sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i)) ∪
    tupleBox (fun i => sourceBounds b b₁ b₂ i*sourceScales P Y₁ Y₂ B₁ B₂ i)).filter
      (fun v => ∀ j,ν j (v (j.castAdd 2)) ≠ 0)

lemma sourcePool_slot {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (j : Fin N) :
    ν j (v (j.castAdd 2)) ≠ 0 := (Finset.mem_filter.mp hv).2 j

lemma sourcePool_nonzero {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) : tupleProduct v ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with h|h <;>
    exact ((mem_tupleBox _ _).mp h i).1

theorem originalCoefficient_mem_sourcePool (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v ≠ 0) :
    v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [originalCoefficient_factor] at hv
  have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
  have hd := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  apply Finset.mem_filter.mpr
  refine ⟨?_,fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)⟩
  apply Finset.mem_union.mpr
  by_cases hx : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v = 0
  · apply Or.inr
    have hy : profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v ≠ 0 := by
      intro hy; exact hd (by rw [hx,hy,sub_self])
    exact profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂) hzero hs v hy
  · exact Or.inl (profileProduct_mem_box _ _ _ (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂) hzero hs v hx)

def sourceRadius {N : ℕ} (b P : Fin N → ℝ) (b₁ b₂ T : ℝ) (B₁ B₂ : Ideal O) : ℝ :=
  (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)

lemma source_coordinate_product {N : ℕ} (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ T : ℝ) (B₁ B₂ : Ideal O) (hT : X₁*X₂=T) :
    (∏ i,sourceBounds b b₁ b₂ i*sourceScales P X₁ X₂ B₁ B₂ i) =
      sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rw [Finset.prod_mul_distrib,sourceBounds_product,sourceScales_product,hT]
  unfold sourceRadius
  ring

lemma tupleBox_product_bound {r : ℕ} (H : Fin r → ℝ) (v : Fin r → Ideal O)
    (hv : v ∈ tupleBox H) : (Ideal.absNorm (tupleProduct v):ℝ) ≤ ∏ i,H i := by
  simp only [tupleProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => ((mem_tupleBox H v).mp hv i).2)

theorem sourcePool_product_bound {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) (v : Fin (N+2) → Ideal O)
    (hv : v ∈ sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (Ideal.absNorm (tupleProduct v):ℝ) ≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).1 with hx|hy
  · exact (tupleBox_product_bound _ v hx).trans_eq (source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX)
  · exact (tupleBox_product_bound _ v hy).trans_eq (source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY)

theorem originalCoefficient_profile_norm_le (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : tupleProduct v≠0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
      ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
  have hn : ‖∏ j,ν j (v (j.castAdd 2))‖≤1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hν j _)
  have hw := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  rw [originalCoefficient_factor,norm_mul,norm_mul,norm_mul]
  have hm : ‖(if s∣tupleProduct v then 1 else 0 : ℂ)‖≤1 := by split_ifs <;> norm_num
  have hnw : ‖∏ j,ν j (v (j.castAdd 2))‖*‖idealWeight c χ R t (tupleProduct v)‖≤1 := by
    simpa only [one_mul] using mul_le_mul hn hw (norm_nonneg _) zero_le_one
  calc
    _ ≤ (1*‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v-
        profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hnw (norm_nonneg _)) hm (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      simpa only [one_mul,mul_one] using norm_sub_le
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v)
        (profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v)

def sourceMassConstant {N : ℕ} (b D : Fin N → ℝ) (b₁ b₂ D₁ D₂ : ℝ) : ℝ :=
  2*128^(N+2)*(∏ j,D j)*D₁*D₂*(∏ j,b j)*b₁*b₂

theorem originalCoefficient_mass (N : ℕ) (c : O) (hc : c≠0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (hν : ∀ j I, ‖ν j I‖≤1)
    (Wslot : Fin N → ℝ → ℂ) (P b D : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hb : ∀ j, 0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂)
    (hD : ∀ j, 0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (hW : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤ sourceBounds D D₁ D₂ i)
    (S : Finset (Fin (N+2) → Ideal O)) :
    (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
      sourceMassConstant b D b₁ b₂ D₁ D₂ *
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  have hpoint (v : Fin (N+2) → Ideal O) :
      ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ ≤
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖ := by
    by_cases hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=0
    · rw [hv,norm_zero]; positivity
    · have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
      exact originalCoefficient_profile_norm_le N c hc χ R t ν hν Wslot P W₁ W₂
        X₁ X₂ Y₁ Y₂ B₁ B₂ s v (sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm)
  have hx := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P X₁ X₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hX₁ hX₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  have hy := profileProduct_mass (sourceProfiles Wslot W₁ W₂) (sourceBounds b b₁ b₂)
    (sourceScales P Y₁ Y₂ B₁ B₂) (sourceBounds D D₁ D₂)
    (sourceBounds_nonneg b b₁ b₂ hb hb₁ hb₂) (sourceScales_pos _ _ _ _ _ hP hY₁ hY₂ hB₁ hB₂)
    (sourceBounds_nonneg D D₁ D₂ hD hD₁ hD₂) hzero hs hW S
  rw [source_coordinate_product b P b₁ b₂ X₁ X₂ T B₁ B₂ hX,sourceBounds_product] at hx
  rw [source_coordinate_product b P b₁ b₂ Y₁ Y₂ T B₁ B₂ hY,sourceBounds_product] at hy
  calc
    _ ≤ ∑ v ∈ S, (‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P X₁ X₂ B₁ B₂) v‖+
        ‖profileProduct (sourceProfiles Wslot W₁ W₂) (sourceScales P Y₁ Y₂ B₁ B₂) v‖) :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact (add_le_add hx hy).trans_eq (by unfold sourceRadius sourceMassConstant; ring)

theorem sourcePool_original_slots {N : ℕ} (ν : Fin N → Ideal O → ℂ)
    (pool : Fin N → Finset (Ideal O)) (hpool : ∀ j I, I∉pool j → ν j I=0)
    (b P : Fin N → ℝ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Fin (N+2) → Ideal O) (hv : v∈sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    ∀ j, v (j.castAdd 2)∈pool j := by
  intro j
  by_contra h
  exact sourcePool_slot _ _ _ _ _ _ _ _ _ _ _ v hv j (hpool j _ h)

theorem tuple_weighted_regroup {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (F : Ideal O → ℂ) :
    (∑ v ∈ S, β v*F (tupleProduct v)) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I*F I := by
  symm
  simp only [tupleCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v=I), β v*F (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

theorem tupleCoefficient_mass {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) :
    (∑ I ∈ tupleColumns S, ‖tupleCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma tupleCoefficient_eq_zero_outside {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) (hI : I∉tupleColumns S) :
    tupleCoefficient S β I=0 := by
  apply Finset.sum_eq_zero
  intro v hv
  exact False.elim (hI (Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2⟩))

theorem source_column_support {N : ℕ} (ν : Fin N → Ideal O → ℂ) (b P : Fin N → ℝ)
    (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (β : (Fin (N+2) → Ideal O) → ℂ) (I : Ideal O)
    (hI : tupleCoefficient (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) β I ≠ 0) :
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm : I∈tupleColumns (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) := by
    by_contra h; exact hI (tupleCoefficient_eq_zero_outside _ _ _ h)
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hm
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hv,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hv⟩

theorem original_source_eq_columns (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (F : Ideal O → ℂ) :
    (∑' v : Fin (N+2) → Ideal O,
      originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v * F (tupleProduct v)) =
    ∑ I ∈ tupleColumns (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂),
      tupleCoefficient (sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
        (originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I * F I := by
  rw [← tuple_weighted_regroup]
  apply tsum_eq_sum
  intro v hv
  have hz : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v = 0 := by
    by_contra hn
    exact hv (originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hn)
  rw [hz,zero_mul]

lemma smooth_annular_bound (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ D : ℝ, 0≤D ∧ (∀ x, ‖W x‖≤D) ∧ W 0=0 ∧ (∀ x, W x≠0 → x≤b) := by
  let D := SchwartzMap.seminorm ℝ 0 0 (CenteredMomentLattice.normPowerProfile W a b ha hs hW 0)
  refine ⟨D,apply_nonneg _ _,?_,?_,?_⟩
  · intro x
    rw [← CenteredMomentTwist.normPowerProfile_norm W a b ha hs hW 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  · by_contra hz
    have h := (hs hz).1
    linarith
  · intro x hx
    exact (hs hx).2

theorem smooth_source_mass_uniform (N : ℕ)
    (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : Fin N → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (hb : ∀ j, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ), (∀ j I, ‖ν j I‖≤1) →
      ∀ (P : Fin N → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Fin (N+2) → Ideal O),
      (∑ v ∈ S, ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) ∧
      (∑ I ∈ tupleColumns S, ‖tupleCoefficient S
        (originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  choose D hD hDbound hDzero hDsupport using
    fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDbound₁,hzero₁,hsupport₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDbound₂,hzero₂,hsupport₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  have hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDzero (And.intro hzero₁ hzero₂)
  have hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDsupport (And.intro hsupport₁ hsupport₂)
  have hbound : ∀ i x, ‖sourceProfiles Wslot W₁ W₂ i x‖≤ sourceBounds D D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro hDbound (And.intro hDbound₁ hDbound₂)
  let C₀ := sourceMassConstant b D b₁ b₂ D₁ D₂
  have hprodD : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  have hprodb : 0≤∏ j,b j := Finset.prod_nonneg (fun j _ => hb j)
  have hC₀ : 0≤C₀ := by
    dsimp only [C₀,sourceMassConstant]
    positivity
  refine ⟨1+C₀,by positivity,?_⟩
  intro c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hm := originalCoefficient_mass N c hc χ R t ν hν Wslot P b D W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s hb hb₁ hb₂ hD hD₁ hD₂
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound S
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏ j,P j := Finset.prod_nonneg (fun j _ => (hP j).le)
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by positivity
  have hbigger : C₀*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) ≤
      (1+C₀)*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (by linarith : C₀≤1+C₀) hraw
  have hmass := hm.trans hbigger
  exact ⟨hmass,(tupleCoefficient_mass S _).trans hmass⟩

theorem originalCoefficient_original_masks (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (tupleProduct v) R ∧ s∣tupleProduct v ∧ ∀ j, ν j (v (j.castAdd 2))≠0 := by
  refine ⟨?_,?_,?_⟩
  · by_contra h
    apply hv
    simp only [originalCoefficient,idealWeight,h,ite_false,zero_mul,mul_zero]
  · by_contra h
    apply hv
    simp only [originalCoefficient,h,ite_false,mul_zero]
  · rw [originalCoefficient_factor] at hv
    have hslots := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1).1
    exact fun j => (Finset.prod_ne_zero_iff.mp hslots) j (Finset.mem_univ j)

theorem originalCoefficient_product_bound (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P b : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j, 0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hzero : ∀ i, sourceProfiles Wslot W₁ W₂ i 0=0)
    (hs : ∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i)
    (v : Fin (N+2) → Ideal O)
    (hv : originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    tupleProduct v≠0 ∧ (Ideal.absNorm (tupleProduct v):ℝ)≤ sourceRadius b P b₁ b₂ T B₁ B₂ := by
  have hm := originalCoefficient_mem_sourcePool N c χ R t ν Wslot P b W₁ W₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hzero hs v hv
  exact ⟨sourcePool_nonzero _ _ _ _ _ _ _ _ _ _ _ v hm,
    sourcePool_product_bound _ _ _ _ _ _ _ _ _ _ _ _ hX hY v hm⟩

theorem sourceProfiles_annular_support (N : ℕ) (Wslot : Fin N → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : Fin N → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) :
    (∀ i, sourceProfiles Wslot W₁ W₂ i 0=0) ∧
    (∀ i x, sourceProfiles Wslot W₁ W₂ i x≠0 → x≤ sourceBounds b b₁ b₂ i) := by
  have hz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
    by_contra h
    have h' := (hs h).1
    linarith
  constructor
  · simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,Fin.forall_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (Wslot j) (a j) (b j) (ha j) (hsSlot j))
        (And.intro (hz W₁ a₁ b₁ ha₁ hs₁) (hz W₂ a₂ b₂ ha₂ hs₂))
  · simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j x (hx : Wslot j x≠0) => (hsSlot j hx).2)
        (And.intro (fun x (hx : W₁ x≠0) => (hs₁ hx).2) (fun x (hx : W₂ x≠0) => (hs₂ hx).2))

theorem sourcePool_prime_slots {N : ℕ} (ν : Fin N → Ideal O → ℂ)
    (pool : Fin N → Finset (Ideal O)) (hpool : ∀ j I, I∉pool j → ν j I=0)
    (hprime : ∀ j I, I∈pool j → Prime I)
    (hdisjoint : Pairwise (Function.onFun Disjoint pool))
    (b P : Fin N → ℝ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Fin (N+2) → Ideal O) (hv : v∈sourcePool ν b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂) :
    (∀ j : Fin N, Prime (v (j.castAdd 2))) ∧ Function.Injective (fun j : Fin N => v (j.castAdd 2)) := by
  have hm := sourcePool_original_slots ν pool hpool b P b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v hv
  refine ⟨fun j => hprime j _ (hm j),?_⟩
  intro i j he
  by_contra hij
  have hmj : v (i.castAdd 2)∈pool j := by
    rw [show v (i.castAdd 2)=v (j.castAdd 2) from he]
    exact hm j
  exact Finset.disjoint_left.mp (hdisjoint hij) (hm i) hmj

open CenteredMomentAddedZeroUniform

def finiteColumns {ι : Type*} [Fintype ι] (S : Finset (Tuple ι)) : Finset (Ideal O) :=
  S.image finiteTupleProduct

def finiteColumnCoefficient {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), β v

lemma finiteColumnCoefficient_mass {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) :
    (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S β I‖) ≤ ∑ v ∈ S, ‖β v‖ := by
  calc
    _ ≤ ∑ I ∈ finiteColumns S, ∑ v ∈ S.filter (fun v => finiteTupleProduct v=I), ‖β v‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

lemma finite_original_mass_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (S : Finset (Tuple ι)) :
    (∑ v ∈ S.image (tupleEquiv e), ‖originalCoefficient n c χ R t
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) =
    ∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖ := by
  rw [Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [originalCoefficient_reindex]

theorem smooth_finite_source_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j, 0<a j) (hb : ∀ j, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : ι → Ideal O → ℂ), (∀ j I, ‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      (∑ v ∈ S, ‖originalFiniteCoefficient c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  obtain ⟨C,hC,hbound⟩ := smooth_source_mass_uniform (Fintype.card ι)
    (fun j => Wslot (e.symm j)) W₁ W₂ (fun j => a (e.symm j)) (fun j => b (e.symm j))
    a₁ b₁ a₂ b₂ (fun j => ha _) (fun j => hb _) ha₁ hb₁ ha₂ hb₂
    (fun j => hsSlot _) hs₁ hs₂ (fun j => hWslot _) hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hm := (hbound c hc χ R t (fun j => ν (e.symm j)) (fun j I => hν _ I)
    (fun j => P (e.symm j)) X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP _)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (S.image (tupleEquiv e))).1
  rw [finite_original_mass_reindex] at hm
  simpa only [e.symm.prod_comp P] using hm

theorem smooth_subset_source_mass_uniform {α : Type*} (A : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈A, 0<a j) (hb : ∀ j∈A, 0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈A, Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈A, ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ, 0<C ∧ ∀ J : Finset α, J⊆A →
      ∀ (c : O), c≠0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ), (∀ j∈J, ∀ I, ‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J, 0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple J),
      (∑ v ∈ S, ‖originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
        (fun j : J => Wslot j.val) (fun j : J => P j.val)
        W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) ∧
      (∑ I ∈ finiteColumns S, ‖finiteColumnCoefficient S
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖) ≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) := by
  have hfamily (J : Finset α) (hJ : J⊆A) := smooth_finite_source_mass_uniform
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂
  let D (J : Finset α) : ℝ := if hJ : J⊆A then (hfamily J hJ).choose else 1
  have hD (J : Finset α) : 0<D J := by
    dsimp only [D]
    split_ifs with hJ
    · exact (hfamily J hJ).choose_spec.1
    · norm_num
  let C := 1+∑ J∈A.powerset,D J
  have hsum : 0≤∑ J∈A.powerset,D J := Finset.sum_nonneg (fun J _ => (hD J).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro J hJ c hc χ R t ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hDC : D J≤C := by
    have hle := Finset.single_le_sum (fun K _ => (hD K).le) (Finset.mem_powerset.mpr hJ)
    dsimp only [C]
    linarith
  have hm := (hfamily J hJ).choose_spec.2 c hc χ R t (fun j : J => ν j.val)
    (fun j I => hν j.val j.property I) (fun j : J => P j.val)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have he : D J=(hfamily J hJ).choose := by simp only [D,dite_eq_left hJ]
  rw [← he,Finset.prod_coe_sort] at hm
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏ j∈J,P j := Finset.prod_nonneg (fun j hj => (hP j hj).le)
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) := by positivity
  have hm' := hm.trans (show D J*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) ≤
      C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j) from
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hDC hraw)
  exact ⟨hm',(finiteColumnCoefficient_mass S _).trans hm'⟩

theorem finiteColumns_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (S : Finset (Tuple ι)) :
    tupleColumns (S.image (tupleEquiv e))=finiteColumns S := by
  simp only [tupleColumns,finiteColumns,Finset.image_image]
  congr 1
  funext v
  exact tupleProduct_reindex e v

theorem finiteColumnCoefficient_reindex {ι : Type*} [Fintype ι] {n : ℕ} (e : ι≃Fin n)
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O) :
    tupleCoefficient (S.image (tupleEquiv e)) (fun w => β ((tupleEquiv e).symm w)) I =
      finiteColumnCoefficient S β I := by
  unfold tupleCoefficient finiteColumnCoefficient
  have hset : (S.image (tupleEquiv e)).filter (fun w => tupleProduct w=I) =
      (S.filter (fun v => finiteTupleProduct v=I)).image (tupleEquiv e) := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨v,hv,rfl⟩,hprod⟩
      exact ⟨v,⟨hv,by simpa only [tupleProduct_reindex] using hprod⟩,rfl⟩
    · rintro ⟨v,⟨hv,hprod⟩,rfl⟩
      exact ⟨⟨v,hv,rfl⟩,by simpa only [tupleProduct_reindex] using hprod⟩
  rw [hset,Finset.sum_image (fun v _ w _ he => (tupleEquiv e).injective he)]
  simp only [Equiv.symm_apply_apply]

end SevenEighths.CenteredMomentSourceMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Dictionary.InverseAssignedCount -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.DetectorDictionaryInverseAssignedCount
local notation "O" => ActualEisensteinCubic.O

def assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) : Finset (ι → Ideal O) := Fintype.piFinset L

@[simp] theorem mem_assignedTuples {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (q : ι → Ideal O) :
    q ∈ assignedTuples L ↔ ∀ i, q i ∈ L i := by
  simp [assignedTuples]

def assignedConstant (K : ℕ) (b : ℝ) : ℝ := (128*b)^K

theorem assignedConstant_pos (K : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    0 < assignedConstant K b := by
  unfold assignedConstant
  positivity

theorem list_card_le (L : Finset (Ideal O)) {H : ℝ} (hH : 0 ≤ H)
    (hL : ∀ I ∈ L, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ H) :
    (L.card : ℝ) ≤ 128*H := by
  apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (t :=
    CenteredMomentSourceMass.idealBall H) ?_))
    (CenteredMomentSourceMass.idealBall_card H hH)
  intro I hI
  exact (CenteredMomentSourceMass.mem_idealBall H I).mpr (hL I hI)

theorem assigned_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples L).card : ℝ) ≤ assignedConstant K b * U^(∑ i, ell i) := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hbase : 1 ≤ 128*b := by linarith
  simp only [assignedTuples, Fintype.card_piFinset, Nat.cast_prod]
  calc
    (∏ i, ((L i).card : ℝ)) ≤ ∏ i, 128*(b*U^(ell i)) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => list_card_le (L i) (by positivity) (hL i))
    _ = (128*b)^(Fintype.card ι) * U^(∑ i, ell i) := by
      simp_rw [← mul_assoc]
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hUp]
      simp
    _ ≤ assignedConstant K b * U^(∑ i, ell i) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbase hK)
        (Real.rpow_nonneg hUp.le _)

def assignedCoefficient {ι : Type*} [Fintype ι]
    (a : ι → Ideal O → ℂ) (q : ι → Ideal O) : ℂ := ∏ i, a i (q i)

theorem assignedCoefficient_norm_le_one {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (a : ι → Ideal O → ℂ)
    (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (q : ι → Ideal O) (hq : q ∈ assignedTuples L) :
    ‖assignedCoefficient a q‖ ≤ 1 := by
  rw [assignedCoefficient, norm_prod]
  simpa using Finset.prod_le_prod₀ (fun i _ => norm_nonneg (a i (q i)))
    (fun i _ => ha i (q i) ((mem_assignedTuples L q).mp hq i))

theorem restricted_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤
      assignedConstant K b * U^(∑ i, ell i) := by
  calc
    (∑ q ∈ T, ‖assignedCoefficient a q‖) ≤ ∑ _q ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => assignedCoefficient_norm_le_one L a ha q (hT hq))
    _ = (T.card : ℝ) := by simp
    _ ≤ ((assignedTuples L).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hT)
    _ ≤ _ := assigned_card_le K hb hU hK ell L hL

theorem restricted_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖) * U^(-(∑ i, ell i)) ≤
      assignedConstant K b := by
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  calc
    _ ≤ (assignedConstant K b * U^(∑ i, ell i)) * U^(-(∑ i, ell i)) :=
      mul_le_mul_of_nonneg_right (restricted_mass_le K hb hU hK ell L hL a ha T hT)
        (Real.rpow_nonneg hUp.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hUp]; simp

theorem restricted_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1)
    (T : Finset (ι → Ideal O)) (hT : T ⊆ assignedTuples L) :
    (∑ q ∈ T, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b := by
  rw [← Finset.sum_mul]
  exact restricted_normalized_mass_le K hb hU hK ell L hL a ha T hT

theorem slots_normalized_mass_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : σ → Ideal O → ℂ) (ha : ∀ i ∈ J, ∀ I ∈ L i, ‖a i I‖ ≤ 1)
    (T : Finset (J → Ideal O)) (hT : T ⊆ assignedTuples (fun i : J => L i)) :
    (∑ q ∈ T, ‖assignedCoefficient (fun i : J => a i) q‖) * U^(-(∑ i ∈ J, ell i)) ≤
      assignedConstant K b := by
  simpa only [Finset.sum_coe_sort] using
    restricted_normalized_mass_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI) (fun i : J => a i)
      (fun i I hI => ha i i.property I hI) T hT

theorem assigned_sum_normalized_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {ι : Type*} [Fintype ι] (hK : Fintype.card ι ≤ K)
    (ell : ι → ℝ) (L : ι → Finset (Ideal O))
    (hL : ∀ i I, I ∈ L i → I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i))
    (a : ι → Ideal O → ℂ) (ha : ∀ i I, I ∈ L i → ‖a i I‖ ≤ 1) :
    (∑ q ∈ assignedTuples L, ‖assignedCoefficient a q‖ * U^(-(∑ i, ell i))) ≤
      assignedConstant K b :=
  restricted_sum_normalized_le K hb hU hK ell L hL a ha _ (Finset.Subset.refl _)

theorem slots_card_le (K : ℕ) {b U : ℝ} (hb : 1 ≤ b) (hU : 1 ≤ U)
    {σ : Type*} (J : Finset σ) (hJ : J.card ≤ K)
    (ell : σ → ℝ) (L : σ → Finset (Ideal O))
    (hL : ∀ i ∈ J, ∀ I ∈ L i, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ b*U^(ell i)) :
    ((assignedTuples (fun i : J => L i)).card : ℝ) ≤
      assignedConstant K b * U^(∑ i ∈ J, ell i) := by
  simpa only [Finset.sum_coe_sort] using
    assigned_card_le K hb hU (by simpa using hJ)
      (fun i : J => ell i) (fun i : J => L i)
      (fun i I hI => hL i i.property I hI)

theorem assignedTuples_eq_empty {ι : Type*} [Fintype ι]
    (L : ι → Finset (Ideal O)) (i : ι) (hi : L i = ∅) :
    assignedTuples L = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have h := (mem_assignedTuples L q).mp hq i
  simp only [hi, Finset.notMem_empty] at h

theorem assignedTuples_card_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (L : ι → Finset (Ideal O)) : (assignedTuples L).card = 1 := by
  simp [assignedTuples]

end SevenEighths.DetectorDictionaryInverseAssignedCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceProfileMass -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceProfileMass
open ActualEisensteinCubic CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
local notation "O" => ActualEisensteinCubic.O

 theorem primary_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (I : Ideal O) :
    primaryIdealCharacter 1 χ I=1 := by
  rw [primaryIdealCharacter_apply]
  have he : Ideal.Quotient.mk (Ideal.span {(1:O)}) (CompletedGauss.primaryGenerator I)=1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(1:O)}))]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_one]
    trivial
  rw [he,map_one]

 theorem idealWeight_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (R I : Ideal O) :
    CenteredMomentRectangle.idealWeight 1 χ R 0 I=(if IsCoprime I R then 1 else 0) := by
  simp only [idealWeight,primary_mod_one,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]

def profileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))*
    (if s∣finiteTupleProduct v then 1 else 0)

 theorem profileCoefficient_eq_original {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      originalFiniteCoefficient 1 (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  rw [originalFiniteCoefficient,idealWeight_mod_one]
  rfl

theorem profile_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      (∑ v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  obtain ⟨C,hC,ht⟩ := smooth_finite_source_mass_uniform Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  simp_rw [profileCoefficient_eq_original]
  exact ht 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S

end SevenEighths.CenteredMomentSourceProfileMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAbsoluteEnergy
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one_all (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) : ‖rowWeight η m A z t I‖ ≤ 1 := by
  by_cases hI : I=0
  · subst I
    rw [map_zero,norm_zero]
    norm_num
  · exact CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A z t I hI

theorem radial_norm_summable (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖Φ (‖eisEmbedding z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

theorem radial_weight_lattice_bound_all (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O, ‖Φ (‖eisEmbedding z‖^2/K)‖) ≤ diagonalControl Φ*max 1 K := by
  by_cases hlarge : 1≤K
  · simpa only [max_eq_right hlarge] using radial_weight_lattice_bound Φ K hlarge
  have hsmall : K≤1 := (not_le.mp hlarge).le
  let B := 4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hB : 0≤B := by dsimp [B]; positivity
  have hp (z : O) : ‖Φ (‖eisEmbedding z‖^2/K)‖ ≤
      B*((1+1*‖eisEmbedding z‖^2)^2)⁻¹ := by
    have hq : 0≤‖eisEmbedding z‖^2/K := div_nonneg (sq_nonneg _) hK.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl Φ (‖eisEmbedding z‖^2/K)
    simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hq] at hh
    norm_num only [show (2:ℝ)^2=4 by norm_num] at hh
    change (1+‖eisEmbedding z‖^2/K)^2*‖Φ (‖eisEmbedding z‖^2/K)‖≤B at hh
    have hq' : ‖eisEmbedding z‖^2≤‖eisEmbedding z‖^2/K := by
      apply (le_div_iff₀ hK).mpr
      exact mul_le_of_le_one_right (sq_nonneg _) hsmall
    have hden : (1+1*‖eisEmbedding z‖^2)^2≤(1+‖eisEmbedding z‖^2/K)^2 := by
      simp only [one_mul]
      gcongr
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hh
  have hb := (radial_norm_summable Φ K hK).tsum_le_tsum hp
    ((scaled_eisenstein_cauchy_summable 1 (by norm_num)).mul_left B)
  rw [tsum_mul_left] at hb
  have hc := scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
  simp only [one_mul] at hc hb
  have ht := hb.trans (mul_le_mul_of_nonneg_left hc hB)
  rw [max_eq_left hsmall,mul_one]
  dsimp only [B] at ht
  unfold diagonalControl
  nlinarith

theorem finite_hecke_polynomial_norm (η : Character) (m A z : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    ‖∑ I∈S,c I*rowWeight η m A z t I‖ ≤ ∑ I∈S,‖c I‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)

theorem finite_hecke_energy_summable (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun z : O => (∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
      (norm_nonneg _)
  · exact (radial_norm_summable Φ K hK).mul_left _

theorem finite_hecke_energy_absolute (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    ‖finiteHeckeEnergy η m A t S c Φ K‖ ≤
      diagonalControl Φ*max 1 K*(∑ I∈S,‖c I‖)^2 := by
  have hs := (finite_hecke_energy_summable η m A t S c Φ K hK).norm
  calc
    _ ≤ ∑' z : O, ‖((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
        Φ (‖eisEmbedding z‖^2/K)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' z : O,(∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖ := by
      apply hs.tsum_le_tsum _ ((radial_norm_summable Φ K hK).mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
        (norm_nonneg _)
    _ = (∑ I∈S,‖c I‖)^2*(∑' z : O,‖Φ (‖eisEmbedding z‖^2/K)‖) := tsum_mul_left
    _ ≤ (∑ I∈S,‖c I‖)^2*(diagonalControl Φ*max 1 K) :=
      mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg _)
    _ = _ := by ring

theorem smooth_subset_source_absolute_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (K : ℝ),0<K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let E := finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      ‖E‖≤C*max 1 K*H^2 ∧ ‖E‖/H≤C*max 1 K*H := by
  obtain ⟨D,hD,hm⟩ := smooth_subset_source_mass_uniform F Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  let C := (diagonalControl Φ+1)*D^2
  have hd := diagonalControl_nonneg Φ
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S K hK H E
  have hmass := (hm J hJ 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S).2
  have hmass' : (∑ I∈finiteColumns S,‖finiteColumnCoefficient S
      (profileCoefficient R (fun j : J => ν j.val) (fun j : J => Wslot j.val)
        (fun j : J => P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖)≤D*H := by
    simpa only [finiteColumnCoefficient,profileCoefficient_eq_original,H,mul_assoc] using hmass
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hNB₁ : 0<(Ideal.absNorm B₁:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hNB₂ : 0<(Ideal.absNorm B₂:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hprod : 0<∏ j∈J,P j := Finset.prod_pos hP
  have hH : 0<H := by dsimp only [H]; positivity
  have hmax : 0≤ max 1 K := le_trans zero_le_one (le_max_left _ _)
  have he : ‖E‖≤C*max 1 K*H^2 := by
    apply (finite_hecke_energy_absolute η m A t (finiteColumns S) _ Φ K hK).trans
    calc
      _ ≤ diagonalControl Φ*max 1 K*(D*H)^2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass' 2)
          (mul_nonneg hd hmax)
      _ ≤ (diagonalControl Φ+1)*max 1 K*(D*H)^2 := by gcongr; linarith
      _ = C*max 1 K*H^2 := by dsimp only [C]; ring
  refine ⟨he,?_⟩
  apply (div_le_iff₀ hH).mpr
  convert he using 1; ring

end SevenEighths.CenteredMomentAbsoluteEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonProfile -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonProfile
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonPrimeSlots CenteredMomentCommonAllocationBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def liveIndices (B : Tuple ι) : Finset ι := Finset.univ.filter (fun i => B (Sum.inl i)=1)

def remainingTuple (B u : Tuple ι) : Tuple (liveIndices B) :=
  Sum.elim (fun i => u (Sum.inl i.val)) (fun j => u (Sum.inr j))

@[simp] theorem remainingTuple_slot (B u : Tuple ι) (i : liveIndices B) :
    remainingTuple B u (Sum.inl i)=u (Sum.inl i.val) := rfl

@[simp] theorem remainingTuple_plain (B u : Tuple ι) (j : Fin 2) :
    remainingTuple B u (Sum.inr j)=u (Sum.inr j) := rfl

theorem remaining_product (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    finiteTupleProduct u=finiteTupleProduct (remainingTuple B u) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,remainingTuple,
    Sum.elim_inl,Sum.elim_inr]
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => u (Sum.inl i))]
  congr 1
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply hf i
  intro hBi
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBi⟩)

theorem slot_profiles_split (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (β : ι → Ideal O → ℂ) :
    (∏ i,β i (B (Sum.inl i)*u (Sum.inl i)))=
      (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),β i (B (Sum.inl i)))*
        ∏ i : liveIndices B,β i.val (u (Sum.inl i.val)) := by
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => β i (u (Sum.inl i)))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1)
    (fun i => β i (B (Sum.inl i)*u (Sum.inl i))),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hf i (Finset.mem_filter.mp hi).2,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]

theorem profile_common_allocation (B u : Tuple ι) (C R s : Ideal O)
    (hB : finiteTupleProduct B=C) (hsC : s∣C)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
        profileCoefficient R (fun i : liveIndices B => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 (remainingTuple B u) := by
  have hprod : finiteTupleProduct (fun i => B i*u i)=C*finiteTupleProduct (remainingTuple B u) := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct u=_
    rw [hB,remaining_product B u hf]
  have hdiv : s∣C*finiteTupleProduct (remainingTuple B u) := dvd_mul_of_dvd_left hsC _
  unfold profileCoefficient
  rw [slot_profiles_split B u hf (fun i I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)),hprod]
  simp only [hdiv,ite_true,one_dvd,mul_one,remainingTuple_slot,remainingTuple_plain,
    IsCoprime.mul_left_iff]
  rw [mul_assoc B₁,mul_assoc B₂]
  by_cases hC : IsCoprime C R <;>
    by_cases hu : IsCoprime (finiteTupleProduct (remainingTuple B u)) R <;>
    simp_all only [true_and,false_and,ite_true,ite_false,mul_zero,zero_mul,mul_one]
  ring

theorem actual_frozen_slots (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : Tuple ι) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,IdealMobiusDivisorSum.primeSupport (B i)⊆IdealMobiusDivisorSum.primeSupport C)
    (u : Tuple ι) (hu : u∈residualBoxes S C B hB)
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) :
    ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 := by
  intro i hi
  rcases prime_coordinate_cases S hS C hC B hB hBs u hu (Sum.inl i) (hp i) with h|h
  · exact False.elim (hi h.1)
  · exact h.1

end SevenEighths.CenteredMomentCommonProfile

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonPuncture -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPuncture
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O

 theorem residualBoxes_filter {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0) :
    residualBoxes S C B hB=
      (Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i))).filter
        (fun u => IsCoprime C (∏ i,u i)) := by
  ext u
  simp only [residualBoxes,Fintype.mem_piFinset,Finset.mem_filter,
    IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  exact forall_and

theorem residualBoxes_sum {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (F : (ι → Ideal O) → ℂ) :
    (∑ u∈residualBoxes S C B hB,F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        (if IsCoprime C (∏ i,u i) then 1 else 0)*F u := by
  rw [residualBoxes_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp

theorem profileCoefficient_puncture {ι : Type*} [Fintype ι]
    (C R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    (if IsCoprime C (finiteTupleProduct v) then 1 else 0)*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  unfold profileCoefficient
  rw [IsCoprime.mul_right_iff,show IsCoprime C (finiteTupleProduct v) ↔ IsCoprime (finiteTupleProduct v) C from isCoprime_comm]
  by_cases hC : IsCoprime (finiteTupleProduct v) C <;>
    by_cases hR : IsCoprime (finiteTupleProduct v) R <;> simp [hC,hR]

theorem residual_profile_sum {ι : Type*} [Fintype ι]
    (S : (ι ⊕ Fin 2) → Finset (Ideal O)) (C : Ideal O) (B : Tuple ι) (hB : ∀ i,B i≠0)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (F : Tuple ι → ℂ) :
    (∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u*F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u*F u := by
  have he (u : Tuple ι) :
      (if IsCoprime C (∏ i,u i) then 1 else 0)*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u=
        profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u :=
    profileCoefficient_puncture C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u
  rw [residualBoxes_sum]
  simp_rw [← mul_assoc,he]
  apply Finset.sum_congr
  · ext u
    simp only [Fintype.mem_piFinset]
  · intro u hu
    rfl

end SevenEighths.CenteredMomentCommonPuncture

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PositiveSummability -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentPositiveSummability
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceMass
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile CenteredMomentDivisorRetained
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction CenteredMomentDivisorAllocation
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma plain_finite_norm (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b X:ℝ)
    (hs:Function.support W⊆Set.Iic b) (hX:0<X) :
    ‖rowTwistedSum η m A z W t X‖≤∑I∈idealBall (b*X),‖W ((Ideal.absNorm I:ℝ)/X)‖ := by
  rw [rowTwistedSum_eq_weight,tsum_eq_sum (s:=idealBall (b*X)) ?_]
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)
  · intro I hI
    by_cases h0:I=0
    · subst I
      simp only [map_zero,zero_mul]
    · have hw:W ((Ideal.absNorm I:ℝ)/X)=0 := by
        by_contra hn
        have hh:=hs hn
        have hbound:(Ideal.absNorm I:ℝ)≤b*X:=(div_le_iff₀ hX).mp hh
        exact hI ((mem_idealBall _ _).mpr ⟨h0,hbound⟩)
      rw [hw,mul_zero]

lemma slot_finite_norm (η:Character) (m A z:O) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) :
    ‖rowSlot η m A z S β t‖≤∑I∈S,‖β I‖ := by
  rw [rowSlot_eq_weight]
  exact finite_hecke_polynomial_norm η m A z t S β

lemma bounded_radial_summable (F:O→ℂ) (B:ℝ) (hF:∀z,‖F z‖≤B)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (f:=fun z:O=>B^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    split_ifs
    · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2)
        (Complex.abs_re_le_norm _) (abs_nonneg _) (sq_nonneg _)
    · simp only [norm_zero]
      positivity
  · exact (radial_norm_summable Φ K hK).mul_left _

lemma product_bounded {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (c:ℂ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) :
    ∃B:ℝ,∀z:O,‖c*((rowTwistedSum η m A z W₁ t X₁*
      rowTwistedSum η m A z W₂ t X₂)*∏i,rowSlot η m A z (S i) (β i) t)‖≤B := by
  refine ⟨‖c‖*((∑I∈idealBall (b₁*X₁),‖W₁ ((Ideal.absNorm I:ℝ)/X₁)‖)*
    (∑I∈idealBall (b₂*X₂),‖W₂ ((Ideal.absNorm I:ℝ)/X₂)‖)*
    ∏i,∑I∈S i,‖β i I‖),?_⟩
  intro z
  rw [norm_mul,norm_mul,norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact mul_le_mul (plain_finite_norm η m A z t W₁ b₁ X₁ hs₁ hX₁)
      (plain_finite_norm η m A z t W₂ b₂ X₂ hs₂ hX₂) (norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>slot_finite_norm η m A z t (S i) (β i))
  · positivity
  · positivity

 theorem retained_positive_summable {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  unfold retainedPositiveRow positiveSlotRow
  simp_rw [←clipped_rowTwistedSum η m A _ W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A _ W₂ t X₂ hX₂]
  obtain ⟨B,hB⟩:=product_bounded η m A t
    (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem allocated_positive_summable {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (D:Ideal O) (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hN (j:Fin 2):(0:ℝ)<Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedPositiveRow
  exact retained_positive_summable η m A t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) _ _ _ keep Φ K hK

end SevenEighths.CenteredMomentPositiveSummability

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.InductionEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentInductionEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability
open CenteredMomentCounting CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def energy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (X₁ X₂:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
    (Φ (‖eisEmbedding z‖^2/K)).re else 0

lemma plain_absolute (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b B X:ℝ)
    (hb:0≤b) (hB:0≤B) (hX:0<X) (hs:Function.support W⊆Set.Iic b)
    (hW:∀x,‖W x‖≤B) : ‖rowTwistedSum η m A z W t X‖≤(128*b*B)*X := by
  rw [rowTwistedSum_eq_weight]
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) B (mul_nonneg hb hX.le) hB (by change rowWeight η m A z t (0:Ideal O)*_=0; rw [map_zero,zero_mul])
    (fun I=>by rw [norm_mul]; exact (mul_le_mul (rowWeight_norm_le_one_all η m A z t I)
      (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    (fun I hi=>(div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hi)))
  convert hh using 1 ; ring

omit [DecidableEq ι] in
lemma positive_squared_absolute (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i) := by
  let L:ℝ:=(128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i)
  let T:ℝ:=X₁*X₂*∏i,P i
  have hL:0≤L:=mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hB i)))
  have hT:0<T:=mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hsum:‖(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏i,rowSlot η m A z (S i) (β i) t‖≤L*T := by
    rw [norm_mul,norm_mul,norm_prod]
    have hp:=Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _=>norm_nonneg (rowSlot η m A z (S i) (β i) t))
      (fun i _=>rowSlot_bound η m A z (S i) (β i) t (b i*P i) (B i)
        (mul_nonneg (hb i) (hP i).le) (hB i) (hβ i) (hN i))
    have hq:=mul_le_mul
      (mul_le_mul (plain_absolute η m A z t W₁ b₁ B₁ X₁ hb₁ hB₁ hX₁ hs₁ hW₁)
        (plain_absolute η m A z t W₂ b₂ B₂ X₂ hb₂ hB₂ hX₂ hs₂ hW₂) (norm_nonneg _) (by positivity))
      hp (by positivity) (by positivity)
    apply hq.trans_eq
    simp only [mul_left_comm (B _) (b _),mul_assoc,Finset.prod_mul_distrib]
    dsimp [L,T]
    simp only [Finset.prod_mul_distrib]
    ring
  unfold positiveSlotRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hT]
  calc
    _≤(L*T)^2/T:=div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsum 2) hT.le
    _=L^2*T:=by field_simp

omit [DecidableEq ι] in
theorem energy_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K≤
      diagonalControl Φ*max 1 K*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)) := by
  let E:ℝ:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤E:=
    positive_squared_absolute η m A z t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂
      hX₁ hX₂ hs₁ hs₂ hW₁ hW₂ S β P b B hP hb hB hβ hN
  have hs:=bounded_radial_summable
    (fun z:O=>positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂) (Real.sqrt E)
    (fun z=>Real.le_sqrt_of_sq_le (hp z)) keep Φ K hK
  have hbnd:=hs.tsum_le_tsum (g:=fun z:O=>E*‖Φ (‖eisEmbedding z‖^2/K)‖) (fun z=>by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left E)
  rw [tsum_mul_left] at hbnd
  exact hbnd.trans ((mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) hE).trans_eq (mul_comm _ _))

end SevenEighths.CenteredMomentInductionEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentPositiveSummability
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Radial where
  keep : O→Prop
  profile : 𝓢(ℝ,ℂ)
  scale : ℝ
  scale_pos : 0<scale
  nonneg : ∀z:O,0≤(profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/scale)).re

def Radial.weight (r:Radial) (z:O) : ℝ :=
  if r.keep z then (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0

lemma Radial.weight_nonneg (r:Radial) (z:O) : 0≤ r.weight z := by
  unfold Radial.weight
  split_ifs
  · exact r.nonneg z
  · rfl

def finiteData (s:Data ι) (r:Radial) (S:Finset O) : Data ι :=
  {s with rows:=S,weight:=r.weight,weight_nonneg:=fun z _=>r.weight_nonneg z}

def energy (s:Data ι) (r:Radial) (D:Ideal O) : ℝ :=
  ∑'z:O,r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    CenteredMomentDivisorRowEnergy.maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def childEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑'z:O,r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

lemma child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    Summable (fun z:O=>r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)) := by
  have hX:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  have hY:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  convert hX.add hY using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma finite_child_le (s:Data ι) (r:Radial) (S:Finset O) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    (finiteData s r S).childEnergy D a≤ childEnergy s r D a := by
  exact sum_le_hasSum S (fun z _=>mul_nonneg (r.weight_nonneg z)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))) (child_summable s r D a).hasSum

lemma energy_nonneg (s:Data ι) (r:Radial) (D:Ideal O) : 0≤energy s r D :=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))

lemma child_nonneg (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤ childEnergy s r D a :=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentEligibleEnergy.actual_source_from_children N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro S
  exact hbound (finiteData s r S) D hD E hE
    (fun a ha=>(finite_child_le s r S D a).trans (hchild a ha))

 theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      Real.sqrt (energy s r D)≤C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s r D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤ s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=>div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s r D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end SevenEighths.CenteredMomentRadialEligibleEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.BottomStage -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentBottomStage
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentInductionEnergy CenteredMomentAbsoluteEnergy QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

 def positiveEnergy (s:Data ι) (r:Radial) : ℝ :=
  CenteredMomentInductionEnergy.energy s.η s.m s.A s.t s.W₁ s.W₂ s.slots s.coefficient s.P
    s.X₁ s.X₂ r.keep r.profile r.scale

 def profileMass (s:Data ι) (B₁ B₂:ℝ) : ℝ :=
  ((128*max 0 s.b₁*B₁)*(128*max 0 s.b₂*B₂)*(∏i,128*max 0 (s.hi i)*s.M i))^2

 theorem actual_absolute (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hW₁:∀x,‖s.W₁ x‖≤B₁) (hW₂:∀x,‖s.W₂ x‖≤B₂) :
    positiveEnergy s r≤diagonalControl r.profile*max 1 r.scale*profileMass s B₁ B₂*
      (s.X₁*s.X₂*∏i,s.P i) := by
  have hs₁:Function.support s.W₁⊆Set.Iic (max 0 s.b₁):=
    by
      intro x hx
      change x≤ max 0 s.b₁
      have hs:x≤ s.b₁:=s.support₁ hx
      exact hs.trans (le_max_right 0 s.b₁)
  have hs₂:Function.support s.W₂⊆Set.Iic (max 0 s.b₂):=
    by
      intro x hx
      change x≤ max 0 s.b₂
      have hs:x≤ s.b₂:=s.support₂ hx
      exact hs.trans (le_max_right 0 s.b₂)
  have hN:∀i,∀I∈s.slots i,s.coefficient i I≠0 →
      (Ideal.absNorm I:ℝ)≤ max 0 (s.hi i)*s.P i:=by
    intro i I hI hn
    have hw:s.W i ((Ideal.absNorm I:ℝ)/s.P i)≠0:=by
      intro hw
      apply hn
      simp only [Data.coefficient,hw,mul_zero]
    have hs:=s.support i hw
    exact (div_le_iff₀ (s.P_pos i)).mp (hs.2.trans (le_max_right _ _))
  have hh:=energy_absolute s.η s.m s.A s.t s.W₁ s.W₂
    (max 0 s.b₁) (max 0 s.b₂) B₁ B₂ s.X₁ s.X₂ (le_max_left _ _) (le_max_left _ _) hB₁ hB₂
    s.X₁_pos s.X₂_pos hs₁ hs₂ hW₁ hW₂
    s.slots s.coefficient s.P (fun i=>max 0 (s.hi i)) s.M s.P_pos
    (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i)) s.coefficient_bound
    hN r.keep r.profile r.scale r.scale_pos
  exact hh.trans_eq (by unfold profileMass;ring)

 theorem actual_bottom_band (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hW₁:∀x,‖s.W₁ x‖≤B₁) (hW₂:∀x,‖s.W₂ x‖≤B₂)
    (Z m M σ:ℝ) (hZ:1<Z) (hK:1≤ r.scale) (hm:m≤σ)
    (hrow:r.scale≤Z^m) (hsource:s.X₁*s.X₂*∏i,s.P i≤Z^M) :
    positiveEnergy s r≤(diagonalControl r.profile*profileMass s B₁ B₂)*Z^(M+σ) := by
  have hh:=actual_absolute s r B₁ B₂ hB₁ hB₂ hW₁ hW₂
  rw [max_eq_right hK] at hh
  have hp:0≤profileMass s B₁ B₂:=sq_nonneg _
  have hd:0≤diagonalControl r.profile:=diagonalControl_nonneg _
  have hs:0≤ s.X₁*s.X₂*∏i,s.P i:=(mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))).le
  have hpow:r.scale*(s.X₁*s.X₂*∏i,s.P i)≤Z^(M+σ):=by
    apply (mul_le_mul hrow hsource hs (Real.rpow_nonneg (by linarith) _)).trans
    rw [←Real.rpow_add (zero_lt_one.trans hZ)]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply hh.trans
  calc
    _=(diagonalControl r.profile*profileMass s B₁ B₂)*(r.scale*(s.X₁*s.X₂*∏i,s.P i)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hpow (mul_nonneg hd hp)

end SevenEighths.CenteredMomentBottomStage

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CoreFloor -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCoreFloor
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

 def zeroRow (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ):ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)

 def zeroEnergy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):ℝ :=
  ∑'z:O,if r.keep z then ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2*
    (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0

 theorem zero_energy_eq (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r=
    energy η m A t W₁ W₂ (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ r.keep r.profile r.scale:=by
  simp [zeroEnergy,energy,zeroRow,positiveSlotRow]

 theorem zero_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁)(hb₂:0≤b₂)(hB₁:0≤B₁)(hB₂:0≤B₂)
    (hX₁:0<X₁)(hX₂:0<X₂)(hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂)(hW₁:∀x,‖W₁ x‖≤B₁)(hW₂:∀x,‖W₂ x‖≤B₂)
    (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r≤
      diagonalControl r.profile*max 1 r.scale*((128*b₁*B₁)*(128*b₂*B₂))^2*(X₁*X₂):=by
  rw [zero_energy_eq]
  have h:=energy_absolute (ι:=Fin 0) η m A t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂
    hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
    (fun _=>∅) (fun _=>0) (fun _=>1) (fun _=>1) (fun _=>1)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    r.keep r.profile r.scale r.scale_pos
  simpa only [Fin.prod_univ_zero,mul_one,mul_assoc] using h

 theorem zero_padded_core (η:Character) (mask A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂:ℝ) (hb₁:0≤b₁)(hb₂:0≤b₂)(hB₁:0≤B₁)(hB₂:0≤B₂)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hW₁:∀x,‖W₁ x‖≤B₁)(hW₂:∀x,‖W₂ x‖≤B₂)
    (r:Radial)(Z m q n₁ n₂ ρ δ:ℝ)(hZ:1<Z)(hm:0≤ m)(hq:0≤q)
    (hscale:r.scale=Z^m)(hfloor:m+q≤ρ)(hcore:n₁+n₂≤ m+q+δ):
    zeroEnergy η mask A t W₁ W₂ (Z^n₁) (Z^n₂) r≤
      (diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*Z^(m+q+ρ+δ):=by
  have hZ0:0<Z:=zero_lt_one.trans hZ
  have h:=zero_absolute η mask A t W₁ W₂ b₁ b₂ B₁ B₂ (Z^n₁) (Z^n₂)
    hb₁ hb₂ hB₁ hB₂ (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    hs₁ hs₂ hW₁ hW₂ r
  rw [hscale,max_eq_right (Real.one_le_rpow hZ.le hm)] at h
  have hp:Z^m*(Z^n₁*Z^n₂)≤Z^(m+q+ρ+δ):=by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply h.trans
  calc
    _=(diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*(Z^m*(Z^n₁*Z^n₂)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hp (mul_nonneg (diagonalControl_nonneg _) (sq_nonneg _))

 theorem whole_slot_norm {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A z:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
    (S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)(P:ι→ℝ)(hP:∀i,0<P i):
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2=
      ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2 *
        (∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i):=by
  have hp:0<∏i,P i:=Finset.prod_pos (fun i _=>hP i)
  unfold positiveSlotRow zeroRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos (mul_pos hX₁ hX₂) hp),
    CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos hX₁ hX₂)]
  rw [norm_mul,norm_prod,mul_pow,Finset.prod_div_distrib,Finset.prod_pow]
  ring

 theorem slot_energy_reduction {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁)(hX₂:0<X₂)(S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)
    (P:ι→ℝ)(hP:∀i,0<P i)(r:Radial)(E:ℝ)
    (hslots:∀z,r.keep z→(∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i)≤E):
    energy η m A t W₁ W₂ S β P X₁ X₂ r.keep r.profile r.scale≤
      E*zeroEnergy η m A t W₁ W₂ X₁ X₂ r:=by
  obtain ⟨B,hB⟩:=product_bounded (ι:=Fin 0) η m A t (Real.sqrt (X₁*X₂):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ (fun _=>∅) (fun _=>0)
  have hz:∀z,‖zeroRow η m A z t W₁ W₂ X₁ X₂‖≤B:=by
    simpa [zeroRow] using hB
  have hsum:=bounded_radial_summable _ B hz r.keep r.profile r.scale r.scale_pos
  obtain ⟨B',hB'⟩:=product_bounded η m A t (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hspos:=bounded_radial_summable _ B' hB' r.keep r.profile r.scale r.scale_pos
  change Summable (fun z:O=>if r.keep z then
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0) at hspos
  unfold energy zeroEnergy
  rw [←tsum_mul_left]
  apply hspos.tsum_le_tsum _ (hsum.mul_left E)
  intro z
  by_cases hk:r.keep z
  · simp only [ite_eq_left hk]
    rw [whole_slot_norm η m A z t W₁ W₂ X₁ X₂ hX₁ hX₂ S β P hP]
    have hb:=mul_le_mul_of_nonneg_left (hslots z hk)
      (sq_nonneg ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖)
    have hh:=mul_le_mul_of_nonneg_right hb (r.nonneg z)
    nlinarith only [hh]
  · simp [hk]

end SevenEighths.CenteredMomentCoreFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RadialCenteredEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialCenteredEnergy
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRowEnergy CenteredMomentDivisorRectangle
open CenteredMomentHeckeSlots CenteredMomentPositiveSummability CenteredMomentActiveAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def centeredChildEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):ℝ:=
  ∑'z:O,r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2

lemma centered_child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):
    Summable (fun z:O=>r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2):=by
  have hN (j:Fin 2):(0:ℝ)<Ideal.absNorm (selectedPlain D a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  let c:ℂ:=(Real.sqrt ((s.X₁*s.X₂/selectedNorm D a)*∏i:liveIndices D a,s.P i):ℂ)⁻¹
  obtain ⟨BX,hBX⟩:=product_bounded s.η s.m s.A s.t c s.W₁ s.W₂ s.b₁ s.b₂
    (s.X₁/Ideal.absNorm (selectedPlain D a 0)) (s.X₂/Ideal.absNorm (selectedPlain D a 1))
    s.support₁ s.support₂ (div_pos s.X₁_pos (hN 0)) (div_pos s.X₂_pos (hN 1))
    (fun i:liveIndices D a=>s.slots i) (fun i:liveIndices D a=>s.coefficient i)
  obtain ⟨BY,hBY⟩:=product_bounded s.η s.m s.A s.t c s.W₁ s.W₂ s.b₁ s.b₂
    (s.Y₁/Ideal.absNorm (selectedPlain D a 0)) (s.Y₂/Ideal.absNorm (selectedPlain D a 1))
    s.support₁ s.support₂ (div_pos s.Y₁_pos (hN 0)) (div_pos s.Y₂_pos (hN 1))
    (fun i:liveIndices D a=>s.slots i) (fun i:liveIndices D a=>s.coefficient i)
  have hF (z:O):‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖≤BX+BY:=by
    unfold residualCenteredRow centeredSlotRow
    change ‖c*((_ - _)*_)‖≤_
    rw [sub_mul,mul_sub]
    exact (norm_sub_le _ _).trans (add_le_add (hBX z) (hBY z))
  have hs:=bounded_radial_summable _ (BX+BY) hF r.keep r.profile r.scale r.scale_pos
  convert hs using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma centered_child_nonneg (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):0≤ centeredChildEnergy s r D a:=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))

def restrict (r:Radial) (p:O→Prop):Radial:={r with keep:=fun z=>r.keep z ∧ p z}

 theorem centered_child_split (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (p:O→Prop):
    centeredChildEnergy s r D a=centeredChildEnergy s (restrict r p) D a+
      centeredChildEnergy s (restrict r (fun z=>¬p z)) D a:=by
  unfold centeredChildEnergy
  rw [←Summable.tsum_add (centered_child_summable s (restrict r p) D a)
    (centered_child_summable s (restrict r (fun z=>¬p z)) D a)]
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hp:p z <;> simp [Radial.weight,restrict,hk,hp]

 theorem actual_source_centered (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*
        ∑a∈s.toSource.active D,((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
          centeredChildEnergy s r D a:=by
  obtain ⟨C,hC,hbase⟩:=active_allocated_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro rows
  have hb:=hbase s.η s.m s.A s.t s.slots s.coefficient D hD s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    rows (fun z=>r.weight z/(s.X₁*s.X₂*∏i,s.P i)) (fun z _=>div_nonneg (r.weight_nonneg z) hraw.le)
  have he (z:O) (x:ℂ):(r.weight z/(s.X₁*s.X₂*∏i,s.P i))*‖x‖^2=
      r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*x‖^2:=by
    rw [normalized_norm_sq _ hraw];ring
  simp_rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0≤(∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P:=
    div_nonneg (sq_nonneg _) (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))).le
  calc
    _≤∑z∈rows,r.weight z*((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
      ‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=by
      apply Finset.sum_le_sum
      intro z hz
      have hh:=mul_le_mul_of_nonneg_left
        (allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
          (fun i=>(zero_le_one.trans (s.M_ge_one i))) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
          s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
          s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)) (r.weight_nonneg z)
      convert hh using 1 ; ring
    _=((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
      ∑z∈rows,r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intros;ring
    _≤_:=mul_le_mul_of_nonneg_left (sum_le_hasSum rows
      (fun z _=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _)) (centered_child_summable s r D a).hasSum) hf

 theorem actual_source_from_centered_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,centeredChildEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P:=by
  obtain ⟨C,hC,hbound⟩:=actual_source_centered N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply (hbound s r D hD).trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      have hsq:(∏i∈frozenIndices D a,s.M i)^2≤ s.profileFactor:=by
        have hh:=pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
        have hf:1≤2*(max 1 s.b₁*max 1 s.b₂):=by
          have ht:=one_le_mul_of_one_le_of_one_le (le_max_left 1 s.b₁) (le_max_left 1 s.b₂)
          linarith
        exact hh.trans (le_mul_of_one_le_left (sq_nonneg _) hf)
      exact mul_le_mul (div_le_div_of_nonneg_right hsq (s.reduction_pos D a).le)
        (hchild a ha) (centered_child_nonneg s r D a) (div_nonneg s.profile_nonneg (s.reduction_pos D a).le)
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

end SevenEighths.CenteredMomentRadialCenteredEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RadialPointwiseEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseEnergy
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentSlotRatios CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma inverse_reduction (s:Data ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.toSource.active D)
    (Z:ℝ) (hZ:1<Z) :
    1/formalReductionFactor D a s.P≤Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ) := by
  have hh:=s.toSource.active_pair_weight s.toSource D hD a a ha ha Z hZ
  rw [show formalReductionFactor D a s.P*formalReductionFactor D a s.P=
    (formalReductionFactor D a s.P)^2 by ring,Real.sqrt_sq (s.reduction_pos D a).le] at hh
  convert hh using 1
  congr 2
  ring

 theorem actual_pointwise_divisor (N:ℕ) (hι:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
        (s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  obtain ⟨C₁,hC₁,henergy⟩:=CenteredMomentRadialEligibleEnergy.actual_source_from_children N hι ε hε
  obtain ⟨C₂,hC₂,hcard⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s r D hD E Z hE hZ hc
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
  have hsz:((s.toSource.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.toSource.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard D hD.ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hs:(∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)≤
      (C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by
    calc
      _≤∑a∈s.toSource.active D,Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=>inverse_reduction s D hD a ha Z hZ)
      _=((s.toSource.active D).card:ℝ)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by simp
      _≤_:=mul_le_mul_of_nonneg_right hsz (div_nonneg (Real.rpow_nonneg (by linarith) _) hn.le)
  apply (henergy s r D hD E hE hc).trans
  calc
    _≤C₁*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ((C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ))):=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hp) s.profile_nonneg) hE)
    _=_:=by
      have he:(Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε):=by
        rw [←Real.rpow_add hn];congr 1;ring
      calc
        _=(C₁*C₂)*((Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε)*
          Z^(s.toSource.allowance Z)*(s.profileFactor*E)/(Ideal.absNorm D:ℝ):=by ring
        _=_:=by rw [he]

end SevenEighths.CenteredMomentRadialPointwiseEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RadialPointwiseUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseUniform
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentRadialPointwiseEnergy CenteredMomentUniformDivisorShell
open CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Bound (ι:Type*) [Fintype ι] [DecidableEq ι] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
    ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
    energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
      (s.profileFactor*E)/(Ideal.absNorm D:ℝ)

 theorem uniform_subset (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J:Finset ι,Bound J C ε := by
  have he (J:Finset ι):∃C:ℝ,0<C ∧ Bound J C ε:=
    actual_pointwise_divisor (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose C hC hb using he
  let D:ℝ:=1+∑J:Finset ι,C J
  have hs:0≤∑J:Finset ι,C J:=Finset.sum_nonneg (fun J _=>(hC J).le)
  refine ⟨D,by dsimp [D];linarith,?_⟩
  intro J s r I hI E Z hE hZ hc
  have hd:C J≤D:=by
    have hh:=Finset.single_le_sum (fun J _=>(hC J).le) (Finset.mem_univ J)
    dsimp [D];linarith
  apply (hb J s r I hI E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (Nat.cast_nonneg _) _)

 theorem actual_uniform_divisor (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J:Finset ι) (s:Data J),(∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      ∀(r:Radial) (D:Ideal O),Squarefree D → ∀E Z:ℝ,0≤E → 1<Z →
      (Ideal.absNorm D:ℝ)≤Z^B → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*Z^δ*(s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨C,hC,hbound⟩:=uniform_subset (ι:=ι) ε hε
  let A:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*A,by dsimp [A];positivity,?_⟩
  intro J s hlo hhi r D hD E Z hE hZ hN hc
  have hz:0<Z:=zero_lt_one.trans hZ
  have ha:Z^(s.toSource.allowance Z)≤A:=by
    dsimp [A]
    rw [←numerical_allowance Z _ hZ]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (subset_allowance J s.toSource lo hi hlo hhi Z hZ)
  have hp:(Ideal.absNorm D:ℝ)^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have he:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  apply (hbound J s r D hD E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  calc
    _≤C*Z^δ*A:=mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) ha
      (Real.rpow_nonneg hz.le _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentRadialPointwiseUniform

end

end OAI

end

