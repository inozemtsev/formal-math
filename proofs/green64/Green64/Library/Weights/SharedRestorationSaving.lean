module

public import Green64.Library.Weights.Part054
public import Green64.Library.Weights.Part043

@[expose] public section

/-!
# Weights / SharedRestorationSaving

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualSharedRestorationSaving -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 12000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- All literal shared labels of the original pattern, across every group. -/
abbrev sourceB574OriginalSharedIndex434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m) :=
  Σ g : G, sourceOriginalProbeSharedSlots434 J ell m hmJ nu g

/-- Sum of the original full physical slices over unrestricted labelled draws.
Repeated shared values are present in this carrier; their full marked
completions vanish, rather than silently changing the draw distribution. -/
def sourceB574CanonicalRestoredSlice434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) : ℂ :=
  let I := sourceB574OriginalSharedIndex434 J ell m hmJ nu
  ∑ a ∈ Fintype.piFinset (fun i : I => P i.1),
    sourceB574CanonicalPhysicalSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp
      (fun g i => a ⟨g,i⟩)

private theorem finite_restoration_error
    {A : Type} [DecidableEq A] (F : Finset A) (mu : A → ℝ)
    (good : A → Prop) [DecidablePred good] (physical : A → ℂ)
    (stripped : ℂ) (B : ℝ)
    (htotal : ∑ a ∈ F,mu a = 1)
    (hclean : ∀ a ∈ F,good a → physical a = (mu a:ℂ)*stripped)
    (herr : ∀ a ∈ F,‖physical a-(mu a:ℂ)*stripped‖ ≤ mu a*B) :
    ‖(∑ a ∈ F,physical a)-stripped‖ ≤
      B*(1-∑ a ∈ F,if good a then mu a else 0) := by
  have hsum : (∑ a ∈ F,physical a)-stripped =
      ∑ a ∈ F,(physical a-(mu a:ℂ)*stripped) := by
    rw [Finset.sum_sub_distrib,←Finset.sum_mul]
    have hc : (∑ a ∈ F,(mu a:ℂ)) = 1 := by exact_mod_cast htotal
    rw [hc,one_mul]
  calc
    _ = ‖∑ a ∈ F,(physical a-(mu a:ℂ)*stripped)‖ := congrArg norm hsum
    _ ≤ ∑ a ∈ F,‖physical a-(mu a:ℂ)*stripped‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ F,if good a then 0 else mu a*B := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : good a
      · simp only [ite_eq_left h,hclean a ha h,sub_self,norm_zero,le_refl]
      · simpa only [ite_eq_right h] using herr a ha
    _ = (∑ a ∈ F,(mu a-if good a then mu a else 0))*B := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : good a <;> simp [h]
    _ = _ := by rw [Finset.sum_sub_distrib,htotal]; ring

/-- Actual physical shared restoration with its explicit lost probability.
This theorem has no assumed kernel cap, physical envelope, independence
surrogate, or RMS premise: all are the literal canonical objects above.
Damping uses distinct P-divisor counts; no valuation-parity identity is used
to replace that damping. The error is measured against the original stripped
canonical marked slice with the same positive marked endpoint masses. -/
theorem source_B574_actual_canonical_shared_restoration_saving434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ)
    (Pmin vmin : ℝ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
    (hq : 0<q) (hq1 : q≤1) (hw : 0<w) (hwp : 0<wp)
    (hPmin : 0<Pmin) (hvmin : 0<vmin)
    (hP : ∀ g p,p∈P g → p.Prime)
    (hV : ∀ g,V g = ∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPrimeMin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (hDisj : ∀ g h p,p∈P g → p∈P h → g=h) :
    let I := sourceB574OriginalSharedIndex434 J ell m hmJ nu
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    ‖sourceB574CanonicalRestoredSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp -
      sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp‖ ≤
      (q^(-2*((J+ell)*Fintype.card G:ℝ))+1)*((Q:ℝ)^4*(xi⁻¹)^2)*
        ‖actualBigMarkDecoration P t q V (fun _=>1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _=>1) wp‖*
        (((Fintype.card I:ℝ)*
          ((w.log2:ℝ)+(wp.log2:ℝ)+((Finset.univ.image aux).card:ℝ))+
          (Fintype.card I:ℝ)^2)/(Pmin*vmin)) := by
  dsimp only
  let I := sourceB574OriginalSharedIndex434 J ell m hmJ nu
  let E := sourceOriginalProbeSharedSlots434 J ell m hmJ nu
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let S : I → Finset ℕ := fun i => P i.1
  let mu : (I → ℕ) → ℝ :=
    sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434 (V i.1))
  let av := Finset.univ.image aux
  let good : (I → ℕ) → Prop := fun a =>
    Function.Injective a ∧ ∀ i,¬a i∣w ∧ ¬a i∣wp ∧ a i∉av
  let physical : (I → ℕ) → ℂ := fun a =>
    sourceB574CanonicalPhysicalSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp
      (fun g i => a ⟨g,i⟩)
  let stripped := sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp
  let loss : ℝ := q^(-2*((J+ell)*Fintype.card G:ℝ))
  let base : ℝ := ((Q:ℝ)^4*(xi⁻¹)^2)*
    ‖actualBigMarkDecoration P t q V (fun _=>1) w‖*
    ‖actualBigMarkDecoration P t q V (fun _=>1) wp‖
  let B : ℝ := (loss+1)*base
  have hV0 (g : G) : 0≤V g := (hvmin.trans_le (hVmin g)).le
  have hbase : 0≤base := by dsimp [base]; positivity
  have hBnonneg : 0≤B := by dsimp [B,loss]; positivity
  have hmassPoint (a : I → ℕ) :
      mu a = sourceB574SharedMass434 (J+ell) E V (fun g i=>a ⟨g,i⟩) := by
    change (∏ i : Σ g : G,E g,sourcePrimeSharedAtom434 (V i.1) (a i)) =
      ∏ g,∏ i : E g,sourcePrimeSharedAtom434 (V g) (a ⟨g,i⟩)
    exact Fintype.prod_sigma _
  have hmu0 (a : I → ℕ) : 0 ≤ mu a := by
    rw [hmassPoint]
    exact source_B574_shared_mass_nonneg434 (J+ell) E V (fun g i=>a ⟨g,i⟩) hV0
  have htotal : ∑ a ∈ Fintype.piFinset S,mu a = 1 :=
    source_shared_law_total434 S (fun i=>sourcePrimeSharedAtom434 (V i.1))
      (fun i=>source_prime_shared_atom_total434 (P i.1) (V i.1) (hV i.1)
        (hvmin.trans_le (hVmin i.1)).ne')
  have hs (a : I → ℕ) (ha : a∈Fintype.piFinset S) :
      ∀ g i,a ⟨g,i⟩∈P g := fun g i => (Fintype.mem_piFinset.mp ha) ⟨g,i⟩
  have hclean (a : I → ℕ) (ha : a∈Fintype.piFinset S) (hg : good a) :
      physical a = (mu a:ℂ)*stripped := by
    have hi : ∀ g,Function.Injective (fun i : E g=>a ⟨g,i⟩) := by
      intro g i j hij
      have he : (⟨g,i⟩:I)=⟨g,j⟩ := hg.1 hij
      simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he
    have haux : ∀ z i,aux z≠a ⟨sourceOriginalProbeAuxGroup434 m nu z,i⟩ := by
      intro z i he
      exact (hg.2 ⟨sourceOriginalProbeAuxGroup434 m nu z,i⟩).2.2
        (Finset.mem_image.mpr ⟨z,Finset.mem_univ z,he⟩)
    change sourceB574CanonicalPhysicalSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp _ =
      (mu a:ℂ)*sourceB574CanonicalStrippedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp
    rw [hmassPoint]
    exact source_B574_canonical_clean_slice_exact434 J ell m hmJ nu Q hA hB xi P V aux q w wp
      (fun g i=>a ⟨g,i⟩) hq hP (hs a ha) hi
      (fun g i=>(hg.2 ⟨g,i⟩).1) (fun g i=>(hg.2 ⟨g,i⟩).2.1) hDisj haux
  have hstripped : ‖stripped‖≤base :=
    source_B574_canonical_stripped_slice_bound434 J ell m hmJ nu Q hA hB xi P V aux q w wp
      hhA hhB hxi
  have herr (a : I → ℕ) (ha : a∈Fintype.piFinset S) :
      ‖physical a-(mu a:ℂ)*stripped‖ ≤ mu a*B := by
    have hp := source_B574_canonical_physical_slice_bound434 J ell m hmJ nu
      Q hA hB xi P V aux q w wp (fun g i=>a ⟨g,i⟩)
      hhA hhB hxi hq hq1 hV0 hP (hs a ha) hDisj
    change ‖physical a‖ ≤ loss*sourceB574SharedMass434 (J+ell) E V (fun g i=>a ⟨g,i⟩)*
      ((Q:ℝ)^4*(xi⁻¹)^2)*
      ‖actualBigMarkDecoration P t q V (fun _=>1) w‖*
      ‖actualBigMarkDecoration P t q V (fun _=>1) wp‖ at hp
    rw [←hmassPoint] at hp
    have hp' : ‖physical a‖≤ mu a*(loss*base) := hp.trans_eq (by dsimp [base]; ring)
    have hk : ‖(mu a:ℂ)*stripped‖≤ mu a*base := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hmu0 a)]
      exact mul_le_mul_of_nonneg_left hstripped (hmu0 a)
    calc
      _ ≤ ‖physical a‖+‖(mu a:ℂ)*stripped‖ := norm_sub_le _ _
      _ ≤ mu a*(loss*base)+mu a*base := add_le_add hp' hk
      _ = _ := by dsimp [B]; ring
  have herror := finite_restoration_error (Fintype.piFinset S) mu good physical stripped B
    htotal hclean herr
  have hdefect := source_actual_shared_clean_defect434 S (fun i=>V i.1)
    w wp av Pmin vmin hw hwp hPmin hvmin
    (fun i p hp=>hP i.1 p hp) (fun i=>hV i.1) (fun i=>hVmin i.1)
    (fun i p hp=>hPrimeMin i.1 p hp)
  have hfin := herror.trans (mul_le_mul_of_nonneg_left hdefect hBnonneg)
  change ‖(∑ a ∈ Fintype.piFinset S,physical a)-stripped‖ ≤ _
  convert hfin using 1; dsimp only [B,base,loss,av,t]; ring
end Green64Analytic.CorrelationSquare

end

end

