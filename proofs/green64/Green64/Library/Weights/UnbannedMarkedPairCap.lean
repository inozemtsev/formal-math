module

public import Green64.Library.Weights.Part098
public import Green64.Library.Weights.ObservedSlots
public import Green64.Library.Weights.Part054

@[expose] public section

/-!
# Weights / UnbannedMarkedPairCap

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## UnbannedMarkedPairCap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- The literal original stripped marked slice AFTER removing the free
auxiliary ban. Only the if-ban guard is absent; both complete marked
carriers, true active cells and the full canonical Knu are unchanged. -/
def b615OriginalUnbannedMarkedSlice434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ) : ℂ :=
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
    (∑ a∈bigMarkLists P t w,∑ b∈bigMarkLists P t wp,
      sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux a b)

private theorem zero_mark_lists_card
    (P : G → Finset ℕ) (n : ℕ) :
    (bigMarkLists P (fun _ => 0) n).card=1 := by
  let a0 : ∀_g : G,Fin 0 → ℕ := fun _ i => Fin.elim0 i
  have hm (a : ∀_g : G,Fin 0 → ℕ) : a∈bigMarkLists P (fun _ => 0) n := by
    apply Fintype.mem_piFinset.mpr
    intro g
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  have ha (a : ∀_g : G,Fin 0 → ℕ) : a=a0 := by
    funext g i
    exact Fin.elim0 i
  have hs : bigMarkLists P (fun _ => 0) n={a0} := by
    ext a
    simp only [Finset.mem_singleton]
    exact ⟨fun _ => ha a,fun _ => hm a⟩
  rw [hs]
  simp

omit [Fintype G] [DecidableEq G] in
private theorem complete_marked_constant_uniform
    (vmin : ℝ) (rmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ,1 ≤ C ∧
      ∀ {H : Type} [Fintype H] [DecidableEq H]
        (P : H → Finset ℕ) (t : H → ℕ) (V : H → ℝ) (n : ℕ),
      (∀g,1 ≤ t g ∧ t g ≤ rmax) → (∀g,vmin ≤ V g) →
      ‖actualBigMarkDecoration P t (1/2) V (fun _=>1) n‖ ≤ C^(Fintype.card H) := by
  obtain ⟨C,hC,hB⟩ := b599_original_observed_marked_l1_uniform vmin rmax hv
  refine ⟨C,hC,?_⟩
  intro H _ _ P t V n ht hV
  let c : H → ℕ := fun _=>0
  let s : ∀g,Fin (c g) → Fin (t g) := fun _ i=>Fin.elim0 i
  have hs : ∀g,Function.Injective (s g) := by
    intro g i
    exact Fin.elim0 i
  have h := hB P t c t V n s hs (by intro g; simp [c]) (fun _=>1) ht hV
  have hc := zero_mark_lists_card P n
  simpa only [c,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
    pow_zero,Finset.prod_const_one,hc,Nat.cast_one,div_one] using h

/-- Exact original no-ban Knu cap, with all actual marked lists retained.
The bound is proved from the canonical true-cell/all-conductor theorem;
there is no assumed kernel bound or replacement of either auxiliary law. -/
theorem b615_original_unbanned_slice_marked_bound434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (P : G → Finset ℕ) (V : G → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (q : ℝ) (w wp : ℕ)
    (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi) :
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
    ‖b615OriginalUnbannedMarkedSlice434 J ell m hmJ nu Q hA hB xi P V aux q w wp‖ ≤ 
      ((Q : ℝ)^4*(xi⁻¹)^2)*
        ‖actualBigMarkDecoration P t q V (fun _=>1) w‖*
        ‖actualBigMarkDecoration P t q V (fun _=>1) wp‖ := by
  dsimp only
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
  let K := sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi P V aux
  let cap : ℝ := (Q : ℝ)^4*(xi⁻¹)^2
  have hrow : ‖∑a∈bigMarkLists P t w,∑b∈bigMarkLists P t wp,K a b‖ ≤ 
      cap*(bigMarkLists P t w).card*(bigMarkLists P t wp).card := by
    calc
      _  ≤  ∑a∈bigMarkLists P t w,‖∑b∈bigMarkLists P t wp,K a b‖ := norm_sum_le _ _
      _  ≤  ∑a∈bigMarkLists P t w,∑b∈bigMarkLists P t wp,‖K a b‖ :=
        Finset.sum_le_sum (fun a _=>norm_sum_le _ _)
      _  ≤  ∑a∈bigMarkLists P t w,∑b∈bigMarkLists P t wp,cap :=
        Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun b _=>
          source_original_probe_canonical_Knu_true_uniform434
            J ell m hmJ nu Q hA hB xi hhA hhB hxi P V aux a b))
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul];ring
  have hOne (n : ℕ) : ‖actualBigMarkDecoration P t q V (fun _=>1) n‖=
      ‖bigMarkPrefactor P t q V n‖*(bigMarkLists P t n).card := by
    simp [actualBigMarkDecoration]
  change ‖bigMarkPrefactor P t q V w*bigMarkPrefactor P t q V wp*
    (∑a∈bigMarkLists P t w,∑b∈bigMarkLists P t wp,K a b)‖ ≤ _
  rw [norm_mul,norm_mul]
  calc
    _  ≤  ‖bigMarkPrefactor P t q V w‖*‖bigMarkPrefactor P t q V wp‖*
        (cap*(bigMarkLists P t w).card*(bigMarkLists P t wp).card) :=
      mul_le_mul_of_nonneg_left hrow (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by rw [hOne,hOne];dsimp only [cap];ring

omit [Fintype G] [DecidableEq G] in
/-- One fixed constant controls the COMPLETE original no-ban marked pair,
uniformly in every endpoint and every RAW auxiliary draw. Actual free
counts are used, so the exponent contains all groups and hidden marks.
This cap is only a cost factor in B615's squared-auxiliary local tail. -/
theorem b615_original_unbanned_full_pair_uniform434
    (vmin : ℝ) (m : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ,1 ≤ C ∧
      ∀ {H : Type} [Fintype H] [DecidableEq H]
        (J : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 H m),
      Disjoint nu.1 nu.2 →
      ∀ (Q : ℕ) (hA hB xi : ℝ),0<hA → 0<hB → 0<xi →
      ∀ (P : H → Finset ℕ) (V : H → ℝ), (∀g,vmin ≤ V g) →
      ∀ (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (w wp : ℕ),
      ‖b615OriginalUnbannedMarkedSlice434 J 1 m hmJ nu Q hA hB xi P V aux
          (1/2) w wp‖ ≤ ((Q : ℝ)^4*(xi⁻¹)^2)*C^(2*Fintype.card H) := by
  obtain ⟨C,hC,hBound⟩ := complete_marked_constant_uniform vmin (1+2*m) hv
  refine ⟨C,hC,?_⟩
  intro H _ _ J hmJ nu hnu Q hA hB xi hhA hhB hxi P V hV aux w wp
  let t := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
  have ht : ∀g,1 ≤ t g ∧ t g ≤ 1+2*m := by
    intro g
    have ha : sourceOriginalProbeChosenGroupCount434 m nu.1 g ≤  m := by
      simpa only [sourceOriginalProbeChosenGroupCount434,Fintype.card_fin] using
        Fintype.card_le_of_injective
          (fun z : {i : Fin m // (g,i)∈nu.1}=>z.val) Subtype.val_injective
    have hb : sourceOriginalProbeChosenGroupCount434 m nu.2 g ≤  m := by
      simpa only [sourceOriginalProbeChosenGroupCount434,Fintype.card_fin] using
        Fintype.card_le_of_injective
          (fun z : {i : Fin m // (g,i)∈nu.2}=>z.val) Subtype.val_injective
    have he := b598_original_free_mark_count434 J 1 m hmJ nu hnu g
    change 1 ≤ sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g ∧
      sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g ≤ 1+2*m
    omega
  have hw := hBound P t V w ht hV
  have hwp := hBound P t V wp ht hV
  have hcap := b615_original_unbanned_slice_marked_bound434 J 1 m hmJ nu
    Q hA hB xi P V aux (1/2) w wp hhA hhB hxi
  dsimp only at hcap
  apply hcap.trans
  have hCn : 0 ≤ C^(Fintype.card H) := pow_nonneg (by linarith) _
  calc
    _  ≤  ((Q : ℝ)^4*(xi⁻¹)^2)*C^(Fintype.card H)*C^(Fintype.card H) := by
      gcongr
    _ = _ := by rw [mul_assoc,←pow_add,←two_mul]
end Green64Analytic.CorrelationSquare

end

end

