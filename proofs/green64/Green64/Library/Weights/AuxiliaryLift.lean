module

public import Green64.Library.Weights.BigPatternLift

@[expose] public section

/-!
# Weights / AuxiliaryLift

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualAuxiliaryLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The literal labelled probe equivalence onto the lifted finite set. -/
def b604ActualProbeSubtypeEquiv434 (r : ℕ) (L : ℝ) (m : ℕ)
    (A : Finset (sourceNativeOriginalBigType434 r L × Fin m)) :
    A ≃ A.map (b604ActualBigProbeEmbedding434 r L m) :=
  Equiv.ofBijective
    (fun z => ⟨b604ActualBigProbeEmbedding434 r L m z.val,
      Finset.mem_map.mpr ⟨z.val,z.property,rfl⟩⟩)
    ⟨by
      intro z z' he
      apply Subtype.ext
      exact (b604ActualBigProbeEmbedding434 r L m).injective (congrArg Subtype.val he),
     by
      intro z
      obtain ⟨z',hz',he⟩ := Finset.mem_map.mp z.property
      exact ⟨⟨z',hz'⟩,Subtype.ext he⟩⟩

@[simp] theorem b604_actual_probe_subtype_value434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (A : Finset (sourceNativeOriginalBigType434 r L × Fin m)) (z : A) :
    (b604ActualProbeSubtypeEquiv434 r L m A z).val =
      (sourceNativeOriginalBigToAll434 r L z.val.1,z.val.2) := rfl

/-- Each original auxiliary coordinate survives once, including repeated values. -/
def b604ActualAuxEquiv434 (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m) :
    SourceOriginalProbeAuxIndex434 m nu ≃
      SourceOriginalProbeAuxIndex434 m (b604ActualLiftedPattern434 r L m nu) :=
  Equiv.sumCongr (b604ActualProbeSubtypeEquiv434 r L m nu.1)
    (b604ActualProbeSubtypeEquiv434 r L m nu.2)

/-- Reindex only the labelled coordinates; no auxiliary value is changed. -/
def b604ActualLiftedAux434 (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    SourceOriginalProbeAuxIndex434 m (b604ActualLiftedPattern434 r L m nu) → ℕ :=
  fun z => aux ((b604ActualAuxEquiv434 r L m nu).symm z)

@[simp] theorem b604_actual_lifted_aux_apply434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (z : SourceOriginalProbeAuxIndex434 m nu) :
    b604ActualLiftedAux434 r L m nu aux (b604ActualAuxEquiv434 r L m nu z)=aux z := by
  simp only [b604ActualLiftedAux434,Equiv.symm_apply_apply]

@[simp] theorem b604_actual_aux_group_lift434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (z : SourceOriginalProbeAuxIndex434 m nu) :
    sourceOriginalProbeAuxGroup434 m (b604ActualLiftedPattern434 r L m nu)
      (b604ActualAuxEquiv434 r L m nu z) =
    sourceNativeOriginalBigToAll434 r L (sourceOriginalProbeAuxGroup434 m nu z) := by
  cases z <;> rfl

/-- The exact two original auxiliary products are preserved separately. -/
theorem b604_actual_aux_products_lift434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    sourceOriginalProbeDA434 m (b604ActualLiftedPattern434 r L m nu)
      (b604ActualLiftedAux434 r L m nu aux)=sourceOriginalProbeDA434 m nu aux ∧
    sourceOriginalProbeDB434 m (b604ActualLiftedPattern434 r L m nu)
      (b604ActualLiftedAux434 r L m nu aux)=sourceOriginalProbeDB434 m nu aux := by
  constructor
  · symm
    apply Fintype.prod_equiv (b604ActualProbeSubtypeEquiv434 r L m nu.1)
    intro z
    exact (b604_actual_lifted_aux_apply434 r L m nu aux (Sum.inl z)).symm
  · symm
    apply Fintype.prod_equiv (b604ActualProbeSubtypeEquiv434 r L m nu.2)
    intro z
    exact (b604_actual_lifted_aux_apply434 r L m nu aux (Sum.inr z)).symm

/-- Exact original product-prime auxiliary carrier, with repetitions retained. -/
theorem b604_actual_aux_carrier_lift434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (P : sourceOriginalPAllGroupType r L → Finset ℕ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    b604ActualLiftedAux434 r L m nu aux ∈ Fintype.piFinset
      (sourceOriginalProbeAuxPrimeSets434 m (b604ActualLiftedPattern434 r L m nu) P) ↔
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (fun g => P (sourceNativeOriginalBigToAll434 r L g))) := by
  simp only [Fintype.mem_piFinset]
  constructor
  · intro h z
    have hz := h (b604ActualAuxEquiv434 r L m nu z)
    rw [b604_actual_lifted_aux_apply434] at hz
    cases z <;> exact hz
  · intro h z
    obtain ⟨z,rfl⟩ := (b604ActualAuxEquiv434 r L m nu).surjective z
    rw [b604_actual_lifted_aux_apply434]
    cases z <;> exact h _

/-- The full original auxiliary harmonic law, including every V and p,
is exactly preserved; it is not renormalized by the lift. -/
theorem b604_actual_aux_harmonic_lift434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (V : sourceOriginalPAllGroupType r L → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    sourceSharedLaw434 (fun z => sourcePrimeSharedAtom434
      (sourceOriginalProbeAuxV434 m (b604ActualLiftedPattern434 r L m nu) V z))
      (b604ActualLiftedAux434 r L m nu aux) =
    sourceSharedLaw434 (fun z => sourcePrimeSharedAtom434
      (sourceOriginalProbeAuxV434 m nu (fun g => V (sourceNativeOriginalBigToAll434 r L g)) z)) aux := by
  unfold sourceSharedLaw434
  symm
  apply Fintype.prod_equiv (b604ActualAuxEquiv434 r L m nu)
  intro z
  rw [b604_actual_lifted_aux_apply434]
  cases z <;> rfl

/-- The source two-block family itself is lifted, not assumed anew. -/
theorem b604_actual_pattern_membership_lift434
    (r : ℕ) (L : ℝ) (m : ℕ)
    (blockA blockB : Finset (sourceNativeOriginalBigType434 r L))
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 r L) m)
    (hnu : nu∈sourceOriginalTwoBlockProbePatterns434 blockA blockB m) :
    b604ActualLiftedPattern434 r L m nu ∈ sourceOriginalTwoBlockProbePatterns434
      (blockA.map (b604ActualBigGroupEmbedding434 r L))
      (blockB.map (b604ActualBigGroupEmbedding434 r L)) m := by
  obtain ⟨ha,ha',hb,hb'⟩ :=
    (source_original_two_block_probe_pattern_mem434 blockA blockB m nu.1 nu.2).mp hnu
  apply (source_original_two_block_probe_pattern_mem434 _ _ _ _ _).mpr
  refine ⟨ha.map,?_,hb.map,?_⟩
  · intro z hz
    obtain ⟨z',hz',he⟩ := Finset.mem_map.mp hz
    subst z
    have hg := (Finset.mem_product.mp (ha' hz')).1
    exact Finset.mem_product.mpr ⟨Finset.mem_map.mpr ⟨z'.1,hg,rfl⟩,Finset.mem_univ _⟩
  · intro z hz
    obtain ⟨z',hz',he⟩ := Finset.mem_map.mp hz
    subst z
    have hg := (Finset.mem_product.mp (hb' hz')).1
    exact Finset.mem_product.mpr ⟨Finset.mem_map.mpr ⟨z'.1,hg,rfl⟩,Finset.mem_univ _⟩

/-- The actual source block disjointness is preserved by the same injection. -/
theorem b604_actual_blocks_disjoint_lift434
    (r : ℕ) (L : ℝ)
    (blockA blockB : Finset (sourceNativeOriginalBigType434 r L))
    (h : Disjoint blockA blockB) :
    Disjoint (blockA.map (b604ActualBigGroupEmbedding434 r L))
      (blockB.map (b604ActualBigGroupEmbedding434 r L)) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hz
  obtain ⟨b,hb,he'⟩ := Finset.mem_map.mp hz'
  have hab := (b604ActualBigGroupEmbedding434 r L).injective (he.trans he'.symm)
  subst b
  exact Finset.disjoint_left.mp h ha hb
end Green64Analytic.SourceBlockSieve

end

end

