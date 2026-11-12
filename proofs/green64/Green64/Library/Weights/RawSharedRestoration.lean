module

public import Green64.Library.Weights.Part114
public import Green64.Library.Correlation.Part072
public import Green64.Library.Weights.Part112
public import Green64.Library.Weights.Part043

@[expose] public section

/-!
# Weights / RawSharedRestoration

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## RawSharedRestoration -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 26000

/-- The genuine unrestricted RAW shared sum. There are J shared labels and
one free endpoint mark per original group. Repeated draws remain in the
carrier and no comparison pattern, auxiliary variable or cell is inserted. -/
def parityRawRestoredSlice434 {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (P : G → Finset ℕ) (V : G → ℝ) (q : ℝ) (w wp : ℕ) : ℂ :=
  ∑ a ∈ Fintype.piFinset
      (fun i : (g : G) × parityRawSharedSlots434 J => P i.1),
    parityRawPhysicalSlice434 J P V q w wp (fun g i => a ⟨g,i⟩)

/-- Exact clean RAW slice factorization, obtained from the original full
physical pairing with K=1 and no freed first-J slots. The sole shared
harmonic inverse stays in the true shared probability. -/
theorem parity_raw_clean_slice_exact434
    {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (P : G → Finset ℕ) (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (s : ∀ g : G,parityRawSharedSlots434 J → ℕ)
    (hq : 0 < q) (hP : ∀ g p,p ∈ P g → p.Prime)
    (hs : ∀ g i,s g i ∈ P g) (hInj : ∀ g,Function.Injective (s g))
    (hAvoid : ∀ g i,¬s g i ∣ w) (hAvoid' : ∀ g i,¬s g i ∣ wp)
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h) :
    parityRawPhysicalSlice434 J P V q w wp s =
      (sourceB574SharedMass434 (J+1) (fun _ : G => parityRawSharedSlots434 J) V s : ℂ)*
        parityRawStrippedSlice434 P V q w wp := by
  let E := fun _ : G => parityRawSharedSlots434 J
  let d₀ := ∏ p ∈ Finset.univ.biUnion (fun g => sourceSharedPrimeSet434 (E g) (s g)),p
  have hd := source_shared_global_labelled_product434 P (J+1) E s hs hInj hDisj
  change d₀=sourceB574SharedDilation434 (J+1) E s at hd
  have h := source_original_clean_global_pairing434 P J 1 (fun _ => ∅) s w wp q V
    hq hP hs hInj hAvoid hAvoid' hDisj (fun _ _ => (1 : ℂ))
  dsimp only at h
  simp only [Finset.card_empty,Nat.add_zero] at h
  change (∏ g,((V g : ℂ)^(J+1))⁻¹)*(∏ g,((V g : ℂ)^1)⁻¹)*
      (d₀ : ℂ)⁻¹*(((sourcePhysicalGroupedHalf434 P (J+1) q (d₀*w))^2 : ℝ) : ℂ)*
      (((sourcePhysicalGroupedHalf434 P (J+1) q (d₀*wp))^2 : ℝ) : ℂ)*
      (∑ a ∈ sourceGlobalSharedCompletions434 P (J+1) E s w,
        ∑ b ∈ sourceGlobalSharedCompletions434 P (J+1) E s wp,(1 : ℂ)) =
    (∏ g,∏ i : E g,((V g : ℂ)*(s g i : ℂ))⁻¹)*
      bigMarkPrefactor P (fun _ => 1) q V w*bigMarkPrefactor P (fun _ => 1) q V wp*
      (∑ a ∈ bigMarkLists P (fun _ => 1) w,∑ b ∈ bigMarkLists P (fun _ => 1) wp,(1 : ℂ)) at h
  have hMass : (∏ g,∏ i : E g,((V g : ℂ)*(s g i : ℂ))⁻¹) =
      (sourceB574SharedMass434 (J+1) E V s : ℂ) := by
    unfold sourceB574SharedMass434 sourcePrimeSharedAtom434
    push_cast
    simp only [one_div,mul_comm]
  rw [hd,hMass] at h
  unfold parityRawPhysicalSlice434 parityRawStrippedSlice434
  dsimp only
  rw [source_B574_true_labelled_completions_exact434 _ _ _ _ w hs hDisj,
    source_B574_true_labelled_completions_exact434 _ _ _ _ wp hs hDisj]
  convert h using 1 <;> dsimp only [E] <;> ring

private theorem raw_finite_shared_error434
    {A : Type} [DecidableEq A] (F : Finset A) (mu : A → ℝ)
    (good : A → Prop) [DecidablePred good] (physical : A → ℂ)
    (stripped : ℂ) (B : ℝ)
    (htotal : ∑ a ∈ F,mu a=1)
    (hclean : ∀ a ∈ F,good a → physical a=(mu a : ℂ)*stripped)
    (herr : ∀ a ∈ F,‖physical a-(mu a : ℂ)*stripped‖ ≤ mu a*B) :
    ‖(∑ a ∈ F,physical a)-stripped‖ ≤
      B*(1-∑ a ∈ F,if good a then mu a else 0) := by
  have hsum : (∑ a ∈ F,physical a)-stripped =
      ∑ a ∈ F,(physical a-(mu a : ℂ)*stripped) := by
    rw [Finset.sum_sub_distrib,←Finset.sum_mul]
    have hc : (∑ a ∈ F,(mu a : ℂ))=1 := by exact_mod_cast htotal
    rw [hc,one_mul]
  calc
    _ = ‖∑ a ∈ F,(physical a-(mu a : ℂ)*stripped)‖ := congrArg norm hsum
    _ ≤ ∑ a ∈ F,‖physical a-(mu a : ℂ)*stripped‖ := norm_sum_le _ _
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
    _ = _ := by rw [Finset.sum_sub_distrib,htotal];ring

/-- Genuine quantitative K=1 shared restoration. Clean identities and the
dirty physical bound are proved for the complete original RAW carrier;
the lost shared probability is then estimated using both endpoint divisor
sets. There is no auxiliary forbidden set and no Q/xi cost. -/
theorem parity_raw_shared_restoration_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (J : ℕ) (P : G → Finset ℕ) (V : G → ℝ) (q : ℝ) (w wp : ℕ)
    (Pmin vmin : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (hw : 0 < w) (hwp : 0 < wp)
    (hPmin : 0 < Pmin) (hvmin : 0 < vmin)
    (hP : ∀ g p,p ∈ P g → p.Prime)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p : ℝ)) (hVmin : ∀ g,vmin ≤ V g)
    (hPrimeMin : ∀ g p,p ∈ P g → Pmin ≤ (p : ℝ))
    (hDisj : ∀ g h p,p ∈ P g → p ∈ P h → g=h) :
    let I := (g : G) × parityRawSharedSlots434 J
    ‖parityRawRestoredSlice434 J P V q w wp-parityRawStrippedSlice434 P V q w wp‖ ≤
      (q^(-2*((J+1)*Fintype.card G : ℝ))+1)*
        ‖actualBigMarkDecoration P (fun _ => 1) q V (fun _ => 1) w‖*
        ‖actualBigMarkDecoration P (fun _ => 1) q V (fun _ => 1) wp‖*
        (((Fintype.card I : ℝ)*((w.log2 : ℝ)+(wp.log2 : ℝ))+
          (Fintype.card I : ℝ)^2)/(Pmin*vmin)) := by
  dsimp only
  let I := (g : G) × parityRawSharedSlots434 J
  let E := fun _ : G => parityRawSharedSlots434 J
  let S : I → Finset ℕ := fun i => P i.1
  let mu : (I → ℕ) → ℝ := sourceSharedLaw434 (fun i => sourcePrimeSharedAtom434 (V i.1))
  let good : (I → ℕ) → Prop := fun a =>
    Function.Injective a ∧ ∀ i,¬a i ∣ w ∧ ¬a i ∣ wp ∧ a i ∉ (∅ : Finset ℕ)
  let physical : (I → ℕ) → ℂ := fun a => parityRawPhysicalSlice434 J P V q w wp (fun g i => a ⟨g,i⟩)
  let stripped := parityRawStrippedSlice434 P V q w wp
  let loss : ℝ := q^(-2*((J+1)*Fintype.card G : ℝ))
  let base : ℝ := ‖actualBigMarkDecoration P (fun _ => 1) q V (fun _ => 1) w‖*
    ‖actualBigMarkDecoration P (fun _ => 1) q V (fun _ => 1) wp‖
  let B : ℝ := (loss+1)*base
  have hV0 (g : G) : 0 ≤ V g := (hvmin.trans_le (hVmin g)).le
  have hBnonneg : 0 ≤ B := by dsimp [B,base,loss];positivity
  have hmassPoint (a : I → ℕ) :
      mu a=sourceB574SharedMass434 (J+1) E V (fun g i => a ⟨g,i⟩) := by
    change (∏ i : (g : G) × E g,sourcePrimeSharedAtom434 (V i.1) (a i)) =
      ∏ g,∏ i : E g,sourcePrimeSharedAtom434 (V g) (a ⟨g,i⟩)
    exact Fintype.prod_sigma _
  have hmu0 (a : I → ℕ) : 0 ≤ mu a := by
    rw [hmassPoint]
    exact source_B574_shared_mass_nonneg434 (J+1) E V (fun g i => a ⟨g,i⟩) hV0
  have htotal : ∑ a ∈ Fintype.piFinset S,mu a=1 :=
    source_shared_law_total434 S (fun i => sourcePrimeSharedAtom434 (V i.1))
      (fun i => source_prime_shared_atom_total434 (P i.1) (V i.1) (hV i.1)
        (hvmin.trans_le (hVmin i.1)).ne')
  have hs (a : I → ℕ) (ha : a ∈ Fintype.piFinset S) :
      ∀ g i,a ⟨g,i⟩ ∈ P g := fun g i => (Fintype.mem_piFinset.mp ha) ⟨g,i⟩
  have hclean (a : I → ℕ) (ha : a ∈ Fintype.piFinset S) (hg : good a) :
      physical a=(mu a : ℂ)*stripped := by
    have hi : ∀ g,Function.Injective (fun i : E g => a ⟨g,i⟩) := by
      intro g i j hij
      have he : (⟨g,i⟩ : I)=⟨g,j⟩ := hg.1 hij
      simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he
    rw [hmassPoint]
    exact parity_raw_clean_slice_exact434 J P V q w wp (fun g i => a ⟨g,i⟩)
      hq hP (hs a ha) hi (fun g i => (hg.2 ⟨g,i⟩).1)
      (fun g i => (hg.2 ⟨g,i⟩).2.1) hDisj
  have hstripped : ‖stripped‖=base := by
    simp only [stripped,base,parity_raw_stripped_slice_marked434,norm_mul,norm_star]
  have herr (a : I → ℕ) (ha : a ∈ Fintype.piFinset S) :
      ‖physical a-(mu a : ℂ)*stripped‖ ≤ mu a*B := by
    have hp := parity_raw_physical_slice_bound434 J P V q w wp (fun g i => a ⟨g,i⟩)
      hq hq1 hV0 hP (hs a ha) hDisj
    rw [←hmassPoint] at hp
    have hp' : ‖physical a‖ ≤ mu a*(loss*base) := hp.trans_eq (by dsimp [base];ring)
    have hk : ‖(mu a : ℂ)*stripped‖=mu a*base := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hmu0 a),hstripped]
    calc
      _ ≤ ‖physical a‖+‖(mu a : ℂ)*stripped‖ := norm_sub_le _ _
      _ ≤ mu a*(loss*base)+mu a*base := add_le_add hp' hk.le
      _ = _ := by dsimp [B];ring
  have he := raw_finite_shared_error434 (Fintype.piFinset S) mu good physical stripped B
    htotal hclean herr
  have hd := source_actual_shared_clean_defect434 S (fun i => V i.1)
    w wp ∅ Pmin vmin hw hwp hPmin hvmin
    (fun i p hp => hP i.1 p hp) (fun i => hV i.1) (fun i => hVmin i.1)
    (fun i p hp => hPrimeMin i.1 p hp)
  have hfin := he.trans (mul_le_mul_of_nonneg_left hd hBnonneg)
  change ‖(∑ a ∈ Fintype.piFinset S,physical a)-stripped‖ ≤ _
  convert hfin using 1 <;> dsimp only [B,base,loss] <;>
    simp only [Finset.card_empty,Nat.cast_zero,add_zero] <;> ring

/-- Exact RAW shared-label count: J labels in every complete original
group; the additional free endpoint mark is not counted as shared. -/
theorem parity_raw_shared_index_card434
    {G : Type} [Fintype G] [DecidableEq G] (J : ℕ) :
    Fintype.card ((g : G) × parityRawSharedSlots434 J)=J*Fintype.card G := by
  simp only [Fintype.card_sigma,Fintype.card_coe,parity_raw_shared_slot_card434,
    Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Nat.mul_comm]
  norm_cast

/-- Actual r20 specialization with true mass floor, prime lower cutoff and
full group disjointness derived before J or the endpoints. This is a
literal RAW physical-to-stripped estimate; no comparison probe or external
small-error hypothesis is used. -/
theorem parity_eventually_actual_raw_shared_restoration434 :
    ∀ᶠ L : ℝ in atTop,1 < L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (J w wp : ℕ),0 < w → 0 < wp →
        let P := b645ActualBand434 L hS
        let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
        let I := (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J
        ‖parityRawRestoredSlice434 J P V (1/2) w wp-parityRawStrippedSlice434 P V (1/2) w wp‖ ≤
          ((1/2 : ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS) : ℝ))+1)*
            ‖actualBigMarkDecoration P (fun _ => 1) (1/2) V (fun _ => 1) w‖*
            ‖actualBigMarkDecoration P (fun _ => 1) (1/2) V (fun _ => 1) wp‖*
            (((Fintype.card I : ℝ)*((w.log2 : ℝ)+(wp.log2 : ℝ))+(Fintype.card I : ℝ)^2)/
              (Real.exp (L^(1/10 : ℝ))*(Real.log (6/5 : ℝ)/2))) := by
  filter_upwards [parity_eventually_actual_full_mass_floor434] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro hS J w wp hw hwp
  exact parity_raw_shared_restoration_bound434 J (b645ActualBand434 L hS)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (1/2) w wp (Real.exp (L^(1/10 : ℝ))) (Real.log (6/5 : ℝ)/2)
    (by norm_num) (by norm_num) hw hwp (Real.exp_pos _)
    source_actual_P_uniform_mass_floor_positive
    (fun g p hp => (parity_actual_full_band_prime_floor434 L h.1.le hS g p hp).1)
    (parity_actual_full_mass_exact434 L hS) (fun g => (h.2.2 hS g).1)
    (fun g p hp => (parity_actual_full_band_prime_floor434 L h.1.le hS g p hp).2)
    (parity_actual_full_band_disjoint434 L h.1 hS)
end Green64Analytic.Parity

end

end

