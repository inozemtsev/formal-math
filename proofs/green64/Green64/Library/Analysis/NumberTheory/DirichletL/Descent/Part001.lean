module

public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part017

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.Poisson -/

section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels
open SecondPassArithmetic

noncomputable local instance markedQuotientField (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Field (ActualEisensteinCubic.O ⧸ P) := Ideal.Quotient.field P

noncomputable local instance markedQuotientFintype (P : Ideal ActualEisensteinCubic.O)
    [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

theorem ideal_divisibility_local_zeroMark
    (P A : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hA : CompletedGauss.primaryGenerator A ≠ 0) :
    zeroMark (Ideal.Quotient.mk P (CompletedGauss.primaryGenerator A)) =
      if P ∣ A then 1 else 0 := by
  have hd : P ∣ A ↔ CompletedGauss.primaryGenerator A ∈ P := by
    calc
      P ∣ A ↔ A ≤ P := Ideal.dvd_iff_le
      _ ↔ Ideal.span {CompletedGauss.primaryGenerator A} ≤ P := by
        rw [(CompletedGauss.primaryGenerator_spec A hA).1]
      _ ↔ _ := Ideal.span_singleton_le_iff_mem P
  simp only [zeroMark, Ideal.Quotient.eq_zero_iff_mem, hd]

theorem actual_marked_active_eq
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      -LocalReflectionBrackets.activeRow (CompletedGauss.actualSextic P hg) ψ 0 σ ε x := by
  simpa only [localReflectionActive, localFourier,
    LocalReflectionBrackets.activeRow, pow_zero] using
    marked_active_eq_neg_trivial (CompletedGauss.actualSextic P hg) ψ hψ σ ε x

theorem actual_marked_active_norm
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    ‖localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x‖ =
      (LocalReflectionBrackets.rootCard (ActualEisensteinCubic.O ⧸ P))⁻¹ *
        if x = 0 then 0 else 1 := by
  rw [actual_marked_active_eq P hg ψ hψ σ ε x, norm_neg,
    LocalReflectionBrackets.canonical_A5_norm_eq_bracket P hg hchar ψ hψ 0
      (by norm_num) σ ε x, LocalReflectionBrackets.norm_bracket_zero]

theorem actual_marked_active_formula
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ ε : (ActualEisensteinCubic.O ⧸ P)ˣ) (x : ActualEisensteinCubic.O ⧸ P) :
    localReflectionActive zeroMark (CompletedGauss.actualSextic P hg) ψ σ ε x =
      (LocalReflectionBrackets.rootCard (ActualEisensteinCubic.O ⧸ P) : ℂ)⁻¹ *
        LocalReflectionBrackets.tau (CompletedGauss.actualSextic P hg) ψ 2 *
        (((CompletedGauss.actualSextic P hg) ^ 2)⁻¹)
          ((σ : ActualEisensteinCubic.O ⧸ P) * (ε : ActualEisensteinCubic.O ⧸ P) * x) := by
  rw [actual_marked_active_eq P hg ψ hψ σ ε x,
    LocalReflectionBrackets.canonical_A5_normalized P hg hchar ψ hψ 0 (by norm_num)]
  simp only [LocalReflectionBrackets.phase, LocalReflectionBrackets.bracket,
    show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
  ring

theorem actual_marked_gauss_phase_norm
    (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hchar : ringChar (ActualEisensteinCubic.O ⧸ P) ≠ 2)
    (ψ : AddChar (ActualEisensteinCubic.O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    ‖LocalReflectionBrackets.tau (CompletedGauss.actualSextic P hg) ψ 2‖ = 1 := by
  have h := LocalReflectionBrackets.canonical_phase_norm P hg hchar ψ hψ 0 (by norm_num) 1
  simpa only [LocalReflectionBrackets.phase, show (0 : ℕ) ≠ 4 by decide,
    ↓reduceIte, Units.val_one, map_one, mul_one, norm_neg] using h

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop

omit [DecidableEq ι] in
theorem row_slot_cross_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (i k : ι) (hik : i ≠ k) :
    MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 = 1 := by
  have hs : MixedCrossSeparation.crossSymbol p hg i k ^ 2 =
      MixedCrossSeparation.crossSymbol p hg k i ^ 2 :=
    canonicalSextic_sq_reciprocity_primary (Ideal.span {p i}) (Ideal.span {p k})
      (hg i) (hg k) (p i) (p k) rfl rfl (hpr i) (hpr k)
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol, map_pow, ite_eq_right hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  calc
    _ = MixedCrossSeparation.crossSymbol p hg i k ^ 6 := by rw [← hs]; ring
    _ = 1 := h6

omit [DecidableEq ι] in
theorem row_slot_product_phase
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1) (R P : Finset ι) (hRP : Disjoint R P) :
    (∏ i ∈ R, ∏ k ∈ P,
      MixedCrossSeparation.crossSymbol p hg i k ^ 4 *
        MixedCrossSeparation.crossSymbol p hg k i ^ 2) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro k hk
  exact row_slot_cross_phase p hcop hg hpr i k (fun h =>
    (Finset.disjoint_left.mp hRP) hi (h.symm ▸ hk))

theorem canonicalSourceCoefficient_mark_priority
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A S : Finset ι) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f
      (fun U => H U * primeMark I L a (A ∪ U)) S =
    ∑ J ∈ I.powerset, primeMark J L a A *
      canonicalSourceCoefficient p hp hcop hg Ψ m f
        (fun U => H U * primeMark (I \ J) L a (U \ A)) S := by
  simp only [canonicalSourceCoefficient, primeMark_priority, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem marked_disjoint_source_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (F M B A₁ A₂ : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (C₁ C₂ : Finset ι → ℂ) (I₁ I₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ K : ℝ) (hK : 0 < K) :
    disjointCanonicalSource p hp hcop hg F M B v ε₁ ε₂
      (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
      (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K =
    ∑ D ∈ M.powerset,
      (UniqueFactorizationMonoid.moebius (∏ i ∈ D, Ideal.span {p i}) : ℂ) /
        (primeProductNorm p D : ℂ) *
      ∑' h : ActualEisensteinCubic.O,
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂
          (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
          (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) h := by
  exact disjointCanonicalSource_poisson p hp hcop hg hinj hc F M B v ε₁ ε₂
    (fun U => C₁ U * primeMark I₁ L₁ a₁ (A₁ ∪ U))
    (fun U => C₂ U * primeMark I₂ L₂ a₂ (A₂ ∪ U)) W V₁ V₂ X₁ X₂ K hK

end

end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Canonical -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def finiteCanonicalMarkedRow (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedChildRow p hp hcop hg pool Ψ m
    (fun U => primeMark slots lists a U * W (primeProductNorm p U / X)) f k

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_actual_columns
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X =
      ∑ U ∈ pool.powerset,
        columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k)
          (Ideal.span {∏ i ∈ U, p i}) *
        (primeMark slots lists a U * W (primeProductNorm p U / X)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  have he := CanonicalRowCompletion.columnWeight_finset p hp hcop hg hpr U Ψ m f k
    (fun U => primeMark slots lists a U * W (primeProductNorm p U / X))
  symm
  convert he using 1 ; simp only [secondChildColumn, canonicalSourceCoefficient] ; ring

theorem secondChildSum_marked_canonical
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMark slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
      finiteCanonicalMarkedRow p hp hcop hg (F \ V) Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ (A ∪ V)) a W (X / primeProductNorm p V) := by
  unfold secondChildSum finiteCanonicalMarkedRow fixedChildRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  have hd : Disjoint V N := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hn)).2 hi)
  have hn : primeProductNorm p (V ∪ N) / X = primeProductNorm p N / (X / primeProductNorm p V) := by
    rw [primeProductNorm_union p V N hd]
    simp only [div_div_eq_mul_div]
    ring
  have hmark := primeMark_priority slots lists a (A ∪ V) N
  simp only [primeMark_residual_lists] at hmark
  simp only [secondChildColumn, ← Finset.union_assoc, hn]
  rw [hmark]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_pool
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg (pool \ B) Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X :=
  fixedChildRow_restore_killed_pool p hp hcop hg pool B Ψ m f k _ hB

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_lists
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots (fun i => lists i \ B) a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  by_cases hd : Disjoint B U
  · have he : U \ B = U := Finset.sdiff_eq_self_of_disjoint hd.symm
    simp only [secondChildColumn, ← primeMark_residual_lists, he]
  · obtain ⟨i, hiB, hiU⟩ := Finset.not_disjoint_iff.mp hd
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB),
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB)]

theorem secondChildSum_marked_fixed_pool
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMark slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V) := by
  rw [secondChildSum_marked_canonical]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  have hV (i : ι) (hi : i ∈ V) : (m * r) * (c * e * ∏ j ∈ V, p j) ∈ Ideal.span {p i} :=
    Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hi) (c * e)) (m * r))
  rw [finiteCanonicalMarkedRow_restore_pool p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV]
  have hlists : (fun i => lists i \ (A ∪ V)) = (fun i => (lists i \ A) \ V) := by
    funext i
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [hlists]
  exact finiteCanonicalMarkedRow_restore_lists p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CompletePool -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem marked_selected_column_sum (F : Finset (Ideal O))
    (hF : ∀I∈F,CanonicalQuadraticSieve.Admissible I)
    (Ψ : O →* ℂ) (m f z : O) (W : ℕ → ℂ) (d : Ideal O → ℂ) :
    let p := CanonicalQuadraticSieve.poolPrimary F
    let hp := CanonicalQuadraticSieve.poolPrimary_ne_zero F hF
    letI : ∀i:ConcretePrimeRowBridge.primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
    let hcop := CanonicalQuadraticSieve.poolPrimary_coprime F hF
    let hg := CanonicalQuadraticSieve.poolPrimary_good F hF
    (∑I∈F,columnWeight (rowTwist Ψ m f z) I * W (Ideal.absNorm I)*d I) =
      ∑S∈(Finset.univ:Finset (ConcretePrimeRowBridge.primePool F)).powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (fun T=>InitialMeanSquare.selectedIdealTest F W T*d (∏i∈T,i.val)) S *
          finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z := by
  dsimp only
  let : ∀i:ConcretePrimeRowBridge.primePool F,
      (Ideal.span {CanonicalQuadraticSieve.poolPrimary F i}).IsMaximal :=
    fun i=>by rw [CanonicalQuadraticSieve.poolPrimary_span F hF i]; infer_instance
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI=>(hF I hI).2.1)]
  apply Finset.sum_congr rfl
  intro S hS
  have hspan : (Ideal.span {∏i∈S,CanonicalQuadraticSieve.poolPrimary F i}) = ∏i∈S,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>CanonicalQuadraticSieve.poolPrimary_span F hF i)
  have hpr (i:ConcretePrimeRowBridge.primePool F) :
      ConcretePrimeRowBridge.goodLambda^2∣CanonicalQuadraticSieve.poolPrimary F i-1 :=
    (primaryPrime_spec i.val (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF i)).2.2.2
  have h := columnWeight_finset (CanonicalQuadraticSieve.poolPrimary F)
    (CanonicalQuadraticSieve.poolPrimary_ne_zero F hF)
    (CanonicalQuadraticSieve.poolPrimary_coprime F hF)
    (CanonicalQuadraticSieve.poolPrimary_good F hF) hpr S Ψ m f z
    (fun T=>InitialMeanSquare.selectedIdealTest F W T*d (∏i∈T,i.val))
  rw [hspan] at h
  rw [←h]
  unfold InitialMeanSquare.selectedIdealTest
  split_ifs <;> simp ; ring

theorem marked_weighted_column_tsum_eq (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀ P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0 → t≤b) (hD : b*X≤D) (d : Ideal O → ℂ) :
    (∑' I:Ideal O,columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)*d I) =
      ∑ I∈InitialMeanSquare.outsideSquarefreeIdeals S D,
        columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)*d I := by
  apply tsum_eq_sum
  intro I hI
  have hz : columnWeight (rowTwist Ψ m f z) I*W ((Ideal.absNorm I:ℝ)/X)=0 := by
    by_contra hn
    exact hI (weighted_column_support S D hSp Ψ m f z hm W b X hX hW hD hn)
  rw [hz,zero_mul]

theorem marked_complete_pool_eq_global (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0 → t≤b) (hD : b*X≤D) (d : Ideal O → ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>W (primeProductNorm (poolPrimary F) T/X)*d (∏i∈T,i.val)) f z =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      W ((Ideal.absNorm I:ℝ)/X)*d I := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  symm
  rw [marked_weighted_column_tsum_eq S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W b X hX hW hD d]
  have he := marked_selected_column_sum F hF Ψ (m*excludedGenerator S) f z (fun n=>W (n/X)) d
  dsimp only at he
  rw [he]
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  rw [canonicalSourceCoefficient_fixed_mask _ _ _ _ Ψ m (excludedGenerator S) f _ T
    (outside_pool_fixed_mask S D hbad hSp T)]
  have ht := InitialMeanSquare.selectedIdealTest_outside S D hbad hSp W b X hX hW hD T
  simp only [canonicalSourceCoefficient,secondChildColumn]
  rw [ht]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GeneratorTransport -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_label_transfer (Ψ : Eis →* ℂ) (m a f k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ m (a*f) k H S =
      secondChildColumn p hp hcop hg Ψ m f (a^4*k) H S := by
  simp only [secondChildColumn, finiteSquarefreeRow, map_mul, map_pow,
    Finset.prod_mul_distrib, Finset.prod_pow, mul_pow]
  ring

theorem secondChildColumn_puncture_unit (Ψ : Eis →* ℂ) (u : Eisˣ) (m f k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ ((u:Eis)*m) f k H S =
      secondChildColumn p hp hcop hg Ψ m f k H S := by
  have he : Ideal.span {((u:Eis)*m)} = Ideal.span {m} :=
    Ideal.span_singleton_mul_left_unit u.isUnit m
  simp only [secondChildColumn,rowCoprimeMask_congr_span p S he]

theorem secondChildColumn_generator_unit (Ψ : Eis →* ℂ) (u : Eisˣ) (m f d k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ m ((u:Eis)*f) ((u:Eis)*d*k) H S =
      secondChildColumn p hp hcop hg Ψ m f (d*((u:Eis)^5*k)) H S := by
  rw [secondChildColumn_label_transfer]
  congr 1
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_label_transfer (F : Finset ι) (Ψ : Eis →* ℂ)
    (m a f k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (coeff : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m (a*f) k slots lists coeff W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f (a^4*k) slots lists coeff W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_label_transfer]

theorem generator_eq_unit_primary (I : Ideal Eis) (e : Eis)
    (he : Ideal.span {e} = I) (hI : primaryGenerator I ≠ 0) :
    ∃ u : Eisˣ, e = (u:Eis)*primaryGenerator I := by
  have ha : Associated (primaryGenerator I) e :=
    Ideal.span_singleton_eq_span_singleton.mp ((primaryGenerator_spec I hI).1.trans he.symm)
  obtain ⟨u,hu⟩ := ha
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩

lemma normalized_generator_row_norm (u : Eisˣ) (d k : Eis) :
    ‖ConcreteTraceCRT.eisEmbedding (d*((u:Eis)^5*k))‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*k)‖ := by
  have he : d*((u:Eis)^5*k) = ((u^5:Eisˣ):Eis)*(d*k) := by
    change d*((u:Eis)^5*k) = (u:Eis)^5*(d*k)
    ring
  rw [he,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.MarkedFourier -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
open CubicEisenstein hiding summand
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem completed_summand_primary_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (I J : Ideal Eis) (h : summand Ψ W X I J ≠ 0) :
    primaryGenerator (I * J ^ 3) ≠ 0 := by
  have hI : primaryGenerator I ≠ 0 := by
    intro hz
    apply h
    simp [summand, columnWeight, squarefreeGaussCoefficient, hz]
  have hJ : primaryGenerator J ≠ 0 := by
    intro hz
    apply h
    rw [summand, cubeWeight_zero_of_primaryGenerator_zero Ψ J hz]
    ring
  rw [primaryGenerator_mul, show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from
    map_pow primaryGeneratorHom J 3]
  exact mul_ne_zero hI (pow_ne_zero _ hJ)

theorem markedCompletedT_congr_primary (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d e : Ideal Eis → ℂ) (h : ∀ A, primaryGenerator A ≠ 0 → d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hz : summand Ψ W X I J = 0
  · simp only [hz, zero_mul]
  · rw [h (I * J ^ 3) (completed_summand_primary_support Ψ W X I J hz)]

theorem markedCompletedT_quotient_fourier (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})] (F : (Eis ⧸ Ideal.span {c}) → ℂ)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => F (Ideal.Quotient.mk _ (primaryGenerator A))) =
      ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
        completedFixedFrequency Ψ c hc h W X := by
  have hinv (n : Eis) :
      F (Ideal.Quotient.mk _ n) =
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
          fixedRowFourierPhase c hc h n :=
    (finiteAdditiveFourier_inversion (quotientTrace c hc)
      (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) F (Ideal.Quotient.mk _ n)).symm
  have hp (p : Ideal Eis × Ideal Eis) :
      summand Ψ W X p.1 p.2 * F (Ideal.Quotient.mk _ (primaryGenerator (p.1 * p.2 ^ 3))) =
      ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc) F h *
        (summand Ψ W X p.1 p.2 * fixedRowFourierPhase c hc h
          (primaryGenerator p.1 * primaryGenerator p.2 ^ 3)) := by
    rw [primaryGenerator_mul, show primaryGenerator (p.2 ^ 3) = primaryGenerator p.2 ^ 3 from
      map_pow primaryGeneratorHom p.2 3, hinv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [markedCompletedT_eq_tsum Ψ W hW X hX]
  simp_rw [hp]
  rw [Summable.tsum_finsetSum]
  · simp only [tsum_mul_left, completedFixedFrequency]
  · intro h hh
    exact (completedFixedFrequency_summable Ψ c hc h W hW X hX).mul_left _

theorem finiteAdditiveFourierCoeff_zero_delta {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (h : R) :
    finiteAdditiveFourierCoeff ψ (fun x => if x = 0 then 1 else 0) h =
      (Fintype.card R : ℂ)⁻¹ := by
  simp [finiteAdditiveFourierCoeff]

theorem markedCompletedT_divisor_fourier (c : Eis) (hc : c ≠ 0)
    [Fintype (Eis ⧸ Ideal.span {c})]
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => if Ideal.span {c} ∣ A then 1 else 0) =
      (Fintype.card (Eis ⧸ Ideal.span {c}) : ℂ)⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, completedFixedFrequency Ψ c hc h W X := by
  have hmark : markedCompletedT Ψ W X (fun A => if Ideal.span {c} ∣ A then 1 else 0) =
      markedCompletedT Ψ W X (fun A =>
        if Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator A) = 0 then 1 else 0) := by
    apply markedCompletedT_congr_primary
    intro A hA
    have hd : Ideal.span {c} ∣ A ↔
        Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator A) = 0 := by
      calc
        _ ↔ A ≤ Ideal.span {c} := Ideal.dvd_iff_le
        _ ↔ Ideal.span {primaryGenerator A} ≤ Ideal.span {c} := by
          rw [(primaryGenerator_spec A hA).1]
        _ ↔ primaryGenerator A ∈ Ideal.span {c} := Ideal.span_singleton_le_iff_mem _
        _ ↔ _ := (Ideal.Quotient.eq_zero_iff_mem).symm
    simp only [hd]
  rw [hmark, markedCompletedT_quotient_fourier c hc
    (fun x : Eis ⧸ Ideal.span {c} => if x = 0 then (1 : ℂ) else 0) Ψ W hW X hX]
  simp only [finiteAdditiveFourierCoeff_zero_delta, Finset.mul_sum]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.MarkedStratum -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CubicEisenstein LocalReflectionBrackets CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section Local
variable {F : Type*} [Field F] [Fintype F]

def markedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ zeroMark h * frequencyMultiplier χ ψ σ ε x h

theorem markedFrequencyRow_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    markedFrequencyRow χ ψ σ ε x 0 = (Fintype.card F : ℂ)⁻¹ := by
  simp [markedFrequencyRow, frequencyMultiplier, finiteAdditiveFourierCoeff, zeroMark]

theorem markedFrequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    (∑ h : Fˣ, markedFrequencyRow χ ψ σ ε x h) =
      localReflectionActive zeroMark χ ψ σ ε x := by
  unfold markedFrequencyRow finiteAdditiveFourierCoeff frequencyMultiplier localReflectionActive localFourier
  simp only [Units.ne_zero, ite_false,  Units.val_inv_eq_inv_val,
    Finset.mul_sum, neg_mul]
  apply Finset.sum_congr rfl
  intro h hh
  ring

def mixedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (marked : Bool) (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  if marked then markedFrequencyRow χ ψ σ ε x h else frequencyRow χ ψ j σ ε x h

end Local

noncomputable local instance markedStratumField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) :=
  Ideal.Quotient.field P
noncomputable local instance markedStratumFintype (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) :=
  Fintype.ofFinite _

theorem actual_mixed_frequency_units (P : Ideal Eis) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (hc : ringChar (Eis ⧸ P) ≠ 2)
    (ψ : AddChar (Eis ⧸ P) ℂ) (hψ : ψ.IsPrimitive) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (Eis ⧸ P)ˣ) (x : Eis ⧸ P) :
    (∑ h : (Eis ⧸ P)ˣ, mixedFrequencyRow (actualSextic P hg) ψ marked j σ ε x h) =
      if marked then
        (rootCard (Eis ⧸ P) : ℂ)⁻¹ * tau (actualSextic P hg) ψ 2 *
          (((actualSextic P hg) ^ 2)⁻¹) ((σ : Eis ⧸ P) * (ε : Eis ⧸ P) * x)
      else (((actualSextic P hg)⁻¹) ^ 2) σ *
        phase (actualSextic P hg) ψ j ε * bracket (actualSextic P hg) j x := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_units P hg hc ψ hψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    rw [markedFrequencyRow_units, actual_marked_active_formula P hg hc ψ hψ σ ε x]

theorem actual_mixed_frequency_zero (P : Ideal Eis) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P) (hc : ringChar (Eis ⧸ P) ≠ 2)
    (ψ : AddChar (Eis ⧸ P) ℂ) (marked : Bool)
    (j : ℕ) (hj : j < 6) (σ ε : (Eis ⧸ P)ˣ) (x : Eis ⧸ P) :
    mixedFrequencyRow (actualSextic P hg) ψ marked j σ ε x 0 =
      if marked then (Fintype.card (Eis ⧸ P) : ℂ)⁻¹
      else if j = 0 then 1 - (Fintype.card (Eis ⧸ P) : ℂ)⁻¹ else 0 := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact canonical_frequencyRow_zero P hg hc ψ j hj σ ε x
  · simp only [mixedFrequencyRow, ite_true]
    exact markedFrequencyRow_zero _ _ _ _ _

theorem actual_mixed_active_stratum {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hc : ∀ i, ringChar (Eis ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (Eis ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (marked : ι → Bool) (j : ι → ℕ) (hj : ∀ i, j i < 6)
    (A : Finset ι) (σ ε : ∀ i, (Eis ⧸ P i)ˣ) (x : ∀ i, Eis ⧸ P i) :
    (∑ h ∈ FixedRayActiveSet.activeStratum (fun i => Eis ⧸ P i) A,
      ∏ i, mixedFrequencyRow (actualSextic (P i) (hg i)) (ψ i) (marked i) (j i)
        (σ i) (ε i) (x i) (h i)) =
      (∏ i ∈ A, if marked i then
        (rootCard (Eis ⧸ P i) : ℂ)⁻¹ * tau (actualSextic (P i) (hg i)) (ψ i) 2 *
          (((actualSextic (P i) (hg i)) ^ 2)⁻¹)
            ((σ i : Eis ⧸ P i) * (ε i : Eis ⧸ P i) * x i)
        else (((actualSextic (P i) (hg i))⁻¹) ^ 2) (σ i) *
          phase (actualSextic (P i) (hg i)) (ψ i) (j i) (ε i) *
            bracket (actualSextic (P i) (hg i)) (j i) (x i)) *
      (∏ i ∈ (Finset.univ : Finset ι) \ A,
        if marked i then (Fintype.card (Eis ⧸ P i) : ℂ)⁻¹
        else if j i = 0 then 1 - (Fintype.card (Eis ⧸ P i) : ℂ)⁻¹ else 0) := by
  rw [FixedRayActiveSet.sum_active_stratum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact actual_mixed_frequency_units (P i) (hg i) (hc i) (ψ i) (hψ i)
      (marked i) (j i) (hj i) (σ i) (ε i) (x i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact actual_mixed_frequency_zero (P i) (hg i) (hc i) (ψ i)
      (marked i) (j i) (hj i) (σ i) (ε i) (x i)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.MarkedTwists -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem markedCompletedT_monoid (Ψ φ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun A => φ (primaryGenerator A)) = completedT (φ * Ψ) W X := by
  unfold markedCompletedT completedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  change summand Ψ W X I J * φ (primaryGenerator (I * J ^ 3)) = _
  rw [summand_mul_fixed_twist, primaryGenerator_mul,
    show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from map_pow primaryGeneratorHom J 3]
  exact mul_comm _ _

theorem whole_prime_mark_eq_mask_complement (p : Eis) (hp : Prime p)
    (A : Ideal Eis) (hA : primaryGenerator A ≠ 0) :
    (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
      1 - coprimalityMask p (primaryGenerator A) := by
  have hd : Ideal.span {p} ∣ A ↔ p ∣ primaryGenerator A := by
    calc
      _ ↔ A ≤ Ideal.span {p} := Ideal.dvd_iff_le
      _ ↔ Ideal.span {primaryGenerator A} ≤ Ideal.span {p} := by
        rw [(primaryGenerator_spec A hA).1]
      _ ↔ _ := by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  change (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
    1 - (if IsCoprime p (primaryGenerator A) then 1 else 0)
  rw [hp.coprime_iff_not_dvd]
  by_cases h : p ∣ primaryGenerator A <;> simp [hd, h]

theorem markedCompletedT_prime_product_twists {ι : Type*}
    (S : Finset ι) (p : ι → Eis) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        completedT ((∏ i ∈ T, coprimalityMask (p i)) * Ψ) W X := by
  have he : markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      markedCompletedT Ψ W X (fun A =>
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          (∏ i ∈ T, coprimalityMask (p i)) (primaryGenerator A)) := by
    apply markedCompletedT_congr_primary
    intro A hA
    calc
      _ = ∏ i ∈ S, (1 - coprimalityMask (p i) (primaryGenerator A)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact whole_prime_mark_eq_mask_complement (p i) (hp i hi) A hA
      _ = _ := by
        rw [Finset.prod_sub]
        simp
  rw [he, markedCompletedT_finset_sum S.powerset Ψ W hW X hX]
  apply Finset.sum_congr rfl
  intro T hT
  rw [markedCompletedT_const_mul, markedCompletedT_monoid]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.MarkedReflection -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*}

def markTwist (p : ι → Eis) (T : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ T, coprimalityMask (p i)

theorem markTwist_norm (p : ι → Eis) (T : Finset ι) (x : Eis) : ‖markTwist p T x‖ ≤ 1 := by
  simp only [markTwist, MonoidHom.finsetProd_apply, norm_prod]
  exact Finset.prod_le_one₀ (fun i hi => norm_nonneg _) (fun i hi => coprimalityMask_norm _ _)

theorem markTwist_periodic (p : ι → Eis) (S T : Finset ι) (hTS : T ⊆ S) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i ∈ S, p i}) (markTwist p T) := by
  intro x y hxy
  simp only [markTwist, MonoidHom.finsetProd_apply]
  apply Finset.prod_congr rfl
  intro i hi
  apply coprimalityMask_periodic (p i) x y
  apply Ideal.mem_span_singleton.mpr
  exact (Finset.dvd_prod_of_mem p (hTS hi)).trans (Ideal.mem_span_singleton.mp hxy)

def markedThetaQuotient (p : ι → Eis) (S : Finset ι) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) : ℂ :=
  fixedThetaQuotient Ψ c x * ∏ i ∈ S, if p i ∣ Quotient.out x then 1 else 0

theorem markedThetaQuotient_twists (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i)) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) :
    markedThetaQuotient p S Ψ c x =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * fixedThetaQuotient (markTwist p T * Ψ) c x := by
  have hmark (i : ι) (hi : i ∈ S) :
      (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
        1 - coprimalityMask (p i) (Quotient.out x) := by
    change (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
      1 - (if IsCoprime (p i) (Quotient.out x) then 1 else 0)
    rw [(hp i hi).coprime_iff_not_dvd]
    by_cases h : p i ∣ Quotient.out x <;> simp [h]
  unfold markedThetaQuotient
  rw [Finset.prod_congr rfl hmark, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [show markTwist p T * Ψ = Ψ * markTwist p T from mul_comm _ _]
  simp only [fixedThetaQuotient, fixedThetaTwist_mul, markTwist, MonoidHom.finsetProd_apply]
  ring

theorem markedCompletedT_canonical_reflection (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (v0 v1 : ℝ) (hv0 : 0 < v0) (hWs : Function.support W ⊆ Set.Icc v0 v1)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Ψ c) h *
          (finiteTwistCusp c hc h).smoothedKernel W X := by
  have hnorm (T : Finset ι) : ∀ x, ‖(markTwist p T * Ψ) x‖ ≤ 1 := by
    intro x
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_right (markTwist_norm p T x) (norm_nonneg _)).trans
      ((one_mul _).le.trans (hΨ x))
  have hper (T : Finset ι) (hT : T ∈ S.powerset) :
      CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i ∈ S, p i})
        (markTwist p T * Ψ) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [markTwist_periodic p S T (Finset.mem_powerset.mp hT) x y (Ideal.mul_le_right hxy),
      hperiod x y (Ideal.mul_le_left hxy)]
  have hcoeff (h : Eis ⧸ Ideal.span {c}) :
      finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Ψ c) h =
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          finiteAdditiveFourierCoeff (quotientTrace c hc)
            (fixedThetaQuotient (markTwist p T * Ψ) c) h := by
    unfold finiteAdditiveFourierCoeff
    simp_rw [markedThetaQuotient_twists p S hp Ψ c]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]
  rw [markedCompletedT_prime_product_twists S p hp Ψ W hWcompact X hX]
  change (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * completedT (markTwist p T * Ψ) W X) = _
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (thetaDerivativeScalar⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc)
          (fixedThetaQuotient (markTwist p T * Ψ) c) h *
            (finiteTwistCusp c hc h).smoothedKernel W X) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [completedT_canonical_smoothed_reflection _ (hnorm T) _ (hper T hT)
        c hc hcQ W v0 v1 hv0 hWs hW X hX]
    _ = _ := by
      simp_rw [hcoeff]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro T hT
      ring

end
end SevenEighths.InverseMoment

end OAI

end

