module

public import Green64.Library.Weights.FullBanObservedDomination
public import Green64.Library.Weights.Part098

@[expose] public section

/-!
# Analysis / Estimates / FullBanHarmonicEnvelope

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## FullBanHarmonicEnvelope -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- The full-ban observed envelope retains both auxiliary-avoidance
filters after the complete hidden marked lists have been summed. -/
def b598RetainedObservedHarmonicMass434
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (D w wp : ℕ) : ℝ :=
  ∑ a∈bigMarkLists P (sourceOriginalProbeChosenGroupCount434 m nu.2) w,
    ∑ b∈bigMarkLists P (sourceOriginalProbeChosenGroupCount434 m nu.1) wp,
      b579SelectedHarmonicMass (sourceOriginalProbeChosenGroupCount434 m nu.2) V a *
      b579SelectedHarmonicMass (sourceOriginalProbeChosenGroupCount434 m nu.1) V b *
      ((∏g,∏i,a g i : ℕ):ℝ) * ((∏g,∏i,b g i : ℕ):ℝ) *
      b598RetainedObservedKnu434 m nu Q hA hB xi P V aux D a b

private theorem retained_density
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀g,0 < V g) (hP : ∀g p,p∈P g → 0 < p)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (D w wp : ℕ) :
    b598RetainedObservedHarmonicMass434 m nu Q hA hB xi P V aux D w wp =
      (∑ a∈bigMarkLists P (sourceOriginalProbeChosenGroupCount434 m nu.2) w,
        b598AvoidedNorm434 (sourceOriginalProbeChosenGroupCount434 m nu.2) D
          (b598OriginalSourceColumn434 m nu Q hB xi P V aux) a) *
      (∑ b∈bigMarkLists P (sourceOriginalProbeChosenGroupCount434 m nu.1) wp,
        b598AvoidedNorm434 (sourceOriginalProbeChosenGroupCount434 m nu.1) D
          (b598OriginalTargetColumn434 m nu Q hA xi P V aux) b) /
      ((∏g,(V g)^(sourceOriginalProbeChosenGroupCount434 m nu.2 g)) *
       (∏g,(V g)^(sourceOriginalProbeChosenGroupCount434 m nu.1 g))) := by
  let cB := sourceOriginalProbeChosenGroupCount434 m nu.2
  let cA := sourceOriginalProbeChosenGroupCount434 m nu.1
  let VB := ∏g,(V g)^(cB g)
  let VA := ∏g,(V g)^(cA g)
  let fB := b598AvoidedNorm434 cB D (b598OriginalSourceColumn434 m nu Q hB xi P V aux)
  let fA := b598AvoidedNorm434 cA D (b598OriginalTargetColumn434 m nu Q hA xi P V aux)
  have hpos {c : G → ℕ} {n : ℕ} {a : ∀g,Fin (c g) → ℕ}
      (ha : a∈bigMarkLists P c n) : ∀g i,0 < a g i := by
    intro g i
    exact hP g (a g i) ((b598_mem_raw_selected_group_lists434 P c a).mp
      (b598_actual_selected_lists_subset_raw434 P c n ha) g i)
  have hterm (a : ∀g,Fin (cB g) → ℕ) (ha : a∈bigMarkLists P cB w)
      (b : ∀g,Fin (cA g) → ℕ) (hb : b∈bigMarkLists P cA wp) :
      b579SelectedHarmonicMass cB V a * b579SelectedHarmonicMass cA V b *
        ((∏g,∏i,a g i : ℕ):ℝ) * ((∏g,∏i,b g i : ℕ):ℝ) *
        b598RetainedObservedKnu434 m nu Q hA hB xi P V aux D a b =
      (fB a*fA b)/(VB*VA) := by
    have hdB := b579_selected_harmonic_density cB V a hV (hpos ha)
    have hdA := b579_selected_harmonic_density cA V b hV (hpos hb)
    rw [b598_selected_nat_cast_product434,b598_selected_nat_cast_product434,
      b598_retained_observed_columns434]
    calc
      _ = (b579SelectedHarmonicMass cB V a*b579SelectedPrimeProduct cB a) *
          (b579SelectedHarmonicMass cA V b*b579SelectedPrimeProduct cA b) *
          (fB a*fA b) := by dsimp [fB,fA,cA,cB]; ring
      _ = (VB⁻¹*VA⁻¹)*(fB a*fA b) := by rw [hdB,hdA]
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  change (∑a∈bigMarkLists P cB w,∑b∈bigMarkLists P cA wp,_) = _
  calc
    _ = ∑a∈bigMarkLists P cB w,∑b∈bigMarkLists P cA wp,(fB a*fA b)/(VB*VA) :=
      Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => hterm a ha b hb))
    _ = _ := by
      simp_rw [←Finset.sum_div]
      congr 1
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a ha => by rw [Finset.mul_sum])

omit [DecidableEq G] in
private theorem norm_avoided (c : G → ℕ) (D : ℕ)
    (f : (∀g,Fin (c g) → ℕ) → ℂ) (a : ∀g,Fin (c g) → ℕ) :
    ‖(b598AvoidedNorm434 c D f a:ℂ)‖=b598AvoidedNorm434 c D f a := by
  have hh : 0 ≤ b598AvoidedNorm434 c D f a := by
    unfold b598AvoidedNorm434
    split_ifs <;> positivity
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh]

/-- Literal fixed-auxiliary full marked Knu envelope, on every physical
pair including dirty endpoints. It has no inverse xi or auxiliary square
root. The original full ban has already supplied the retained observed
coprimality gates, before the hidden-slot inequality is applied. -/
theorem b598_actual_full_ban_harmonic_envelope434
    (vmin : ℝ) (m : ℕ) (hv : 0 < vmin) :
    ∃ C : ℝ,1 ≤ C ∧
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (J : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
        (_hnu : Disjoint nu.1 nu.2)
        (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
        (_hPrime : ∀g p,p∈P g → p.Prime)
        (_hDisj : ∀g h p,p∈P g → p∈P h → g=h)
        (_hV : ∀g,vmin ≤ V g)
        (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
        (_haux : aux∈Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu P))
        (D : ℕ) (_hD : D=sourceOriginalProbeDA434 m nu aux * sourceOriginalProbeDB434 m nu aux)
        (w wp : ℕ),
      ‖sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi P V aux (1/2) w wp‖ ≤
        C^(2*Fintype.card G) *
          b598RetainedObservedHarmonicMass434 m nu Q hA hB xi P V aux D w wp := by
  obtain ⟨C,hC,hbound⟩ := b599_original_observed_marked_l1_uniform vmin (m+1) hv
  refine ⟨C,hC,?_⟩
  intro G _ _ J hmJ nu hnu Q hA hB xi P V hPrime hDisj hV aux haux D hD w wp
  let t := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
  let cB := sourceOriginalProbeChosenGroupCount434 m nu.2
  let cA := sourceOriginalProbeChosenGroupCount434 m nu.1
  let rB := fun g => 1+cA g
  let rA := fun g => 1+cB g
  let fB := b598AvoidedNorm434 cB D (b598OriginalSourceColumn434 m nu Q hB xi P V aux)
  let fA := b598AvoidedNorm434 cA D (b598OriginalTargetColumn434 m nu Q hA xi P V aux)
  have htB (g : G) : t g=cB g+rB g := by
    dsimp only [t]
    rw [b598_original_free_mark_count434 J 1 m hmJ nu hnu]
    dsimp [cA,cB,rB]
    omega
  have htA (g : G) : t g=cA g+rA g := by
    dsimp only [t]
    rw [b598_original_free_mark_count434 J 1 m hmJ nu hnu]
    dsimp [cA,cB,rA]
    omega
  have hrB (g : G) : 1 ≤ rB g ∧ rB g ≤ m+1 := by
    have hh := source_original_probe_chosen_group_count_le434 m nu.1 g
    dsimp [rB,cA]
    omega
  have hrA (g : G) : 1 ≤ rA g ∧ rA g ≤ m+1 := by
    have hh := source_original_probe_chosen_group_count_le434 m nu.2 g
    dsimp [rA,cB]
    omega
  have hs := hbound P t cB rB V w
    (b598OriginalObservedBSlot434 J 1 m hmJ nu)
    (b598_original_observed_B_slot_injective434 J 1 m hmJ nu) htB
    (fun a => (fB a:ℂ)) hrB hV
  have ht := hbound P t cA rA V wp
    (b598OriginalObservedASlot434 J 1 m hmJ nu)
    (b598_original_observed_A_slot_injective434 J 1 m hmJ nu) htA
    (fun b => (fA b:ℂ)) hrA hV
  have hsn : 0 ≤ C^(Fintype.card G)*(∑a∈bigMarkLists P cB w,‖(fB a:ℂ)‖)/(∏g,(V g)^(cB g)) :=
    le_trans (norm_nonneg _) hs
  have hb := b598_full_ban_coupled_observed_domination434 J 1 m hmJ nu Q hA hB xi
    P V hPrime hDisj aux haux D hD w wp
  apply hb.trans
  change ‖actualBigMarkDecoration P t (1/2) V
      (fun a => (fB (fun g i => a g (b598OriginalObservedBSlot434 J 1 m hmJ nu g i)):ℂ)) w‖ *
    ‖actualBigMarkDecoration P t (1/2) V
      (fun b => (fA (fun g i => b g (b598OriginalObservedASlot434 J 1 m hmJ nu g i)):ℂ)) wp‖ ≤ _
  calc
    _ ≤ (C^(Fintype.card G)*(∑a∈bigMarkLists P cB w,‖(fB a:ℂ)‖)/(∏g,(V g)^(cB g))) *
        (C^(Fintype.card G)*(∑b∈bigMarkLists P cA wp,‖(fA b:ℂ)‖)/(∏g,(V g)^(cA g))) :=
      mul_le_mul hs ht (norm_nonneg _) hsn
    _ = _ := by
      have hVp (g : G) : 0 < V g := hv.trans_le (hV g)
      rw [retained_density m nu Q hA hB xi P V hVp (fun g p hp => (hPrime g p hp).pos) aux D w wp]
      rw [show 2*Fintype.card G=Fintype.card G+Fintype.card G by omega,pow_add]
      simp only [fB,fA,norm_avoided]
      dsimp only [cA,cB]
      ring
end Green64Analytic.CorrelationSquare

end

end

