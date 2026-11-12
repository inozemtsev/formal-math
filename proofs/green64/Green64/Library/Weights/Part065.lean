module

public import Green64.Library.Weights.ActualInitialBaseline

@[expose] public section

/-!
# Weights / Part065

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualInitialDistinctness -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- The original initial no-rebirth list implies numerical injectivity of
the complete active array, including across BIG groups. -/
theorem source_original_ACTUAL_initial_nodup_active_injective434
    (J ell : ℕ) (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup) :
    Function.Injective (fun x : Sigma (fun _ : BG => Fin (J+ell)) =>
      bm x.1 ((y.2 x.1).1 x.2)) := by
  let l : List (Sigma (fun _ : BG => Fin (J+ell))) :=
    (Finset.univ : Finset BG).toList.flatMap (fun g =>
      (Finset.univ : Finset (Fin (J+ell))).toList.map (fun j => ⟨g,j⟩))
  let f : Sigma (fun _ : BG => Fin (J+ell)) → ℕ :=
    fun x => bm x.1 ((y.2 x.1).1 x.2)
  have hall (x : Sigma (fun _ : BG => Fin (J+ell))) : x ∈ l := by
    apply List.mem_flatMap.mpr
    refine ⟨x.1,by simp,?_⟩
    exact List.mem_map.mpr ⟨x.2,by simp,rfl⟩
  have he : l.map f = physicalOutputInitialBirths SP sm BP bm J ell y := by
    simp [l,f,physicalOutputInitialBirths,List.map_flatMap,List.map_map,Function.comp_def]
  have hh : (l.map f).Nodup := by rw [he];exact hn
  intro x z hxz
  exact List.inj_on_of_nodup_map hh (hall x) (hall z) hxz

/-- Baseline cancellation applies to the literal original initial
distinctness filter, with no new distinctness premise. -/
theorem source_original_ACTUAL_initial_nodup_baseline_cancel434
    (J ell : ℕ) (q : ℝ) (N : ℕ) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (y : FullPhysicalOutput SP sm BP bm (J+ell))
    (hn : (physicalOutputInitialBirths SP sm BP bm J ell y).Nodup)
    (hb : ∀ g p,0 < physicalSourceBaseline BP bm q N g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q N g p ≤ 1) :
    ‖(physicalSourceBaselineProduct BP bm q N:ℂ)‖ *
      (∏ g,activeMass (J+ell) (physicalSourceMuTilde BP bm q N V g) (y.2 g).1) ≤
    ∏ g,activeMass (J+ell) (fun p => 1/(V g*(bm g p:ℝ))) (y.2 g).1 := by
  exact source_original_ACTUAL_distinct_active_baseline_cancel434 BP bm
    (J+ell) q N V hV (fun g => (y.2 g).1)
    (source_original_ACTUAL_initial_nodup_active_injective434 SP sm BP bm J ell y hn) hb hb1
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualInitialBIGMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exact untilted normalization for all original BIG active slots. -/
theorem source_original_ACTUAL_active_harmonic_mass_one434
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (M : ℕ) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g) :
    (∑ a : (g : BG) → Fin M → BP g,
      ∏ g,activeMass M (fun p => 1/(V g*(bm g p:ℝ))) (a g))=1 := by
  have hOne (g : BG) : (∑ p : BP g,1/(V g*(bm g p:ℝ)))=1 := by
    simp_rw [one_div,mul_inv_rev]
    rw [← Finset.sum_mul]
    simpa only [one_div] using congrArg (fun t => t*(V g)⁻¹) (hHarmonic g) |>.trans
      (mul_inv_cancel₀ (ne_of_gt (hV g)))
  have hLocal (g : BG) :
      (∑ a : Fin M → BP g,activeMass M (fun p => 1/(V g*(bm g p:ℝ))) a)=1 := by
    unfold activeMass
    calc
      _ = ∏ i : Fin M,∑ p : BP g,1/(V g*(bm g p:ℝ)) := by
        convert (Fintype.prod_sum (fun (_i : Fin M) (p : BP g) =>
          (1:ℝ)/(V g*(bm g p:ℝ)))).symm using 1
      _ = 1 := by simp only [hOne,Finset.prod_const_one]
  rw [←Fintype.prod_sum]
  simp only [hLocal,Finset.prod_const_one]

/-- The exact baseline-weighted, globally distinct initial BIG active
mass is at most one, uniformly in the number of groups and active slots.
The filter is numerical, and may be discharged from the original initial
list by source_original_ACTUAL_initial_nodup_active_injective434. -/
theorem source_original_ACTUAL_distinct_initial_BIG_mass_le_one434
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (M : ℕ) (q : ℝ) (N : ℕ) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (hHarmonic : ∀ g,∑ p : BP g,1/(bm g p:ℝ)=V g)
    (hb : ∀ g p,0 < physicalSourceBaseline BP bm q N g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q N g p ≤ 1) :
    ‖(physicalSourceBaselineProduct BP bm q N:ℂ)‖ *
      (∑ a : (g : BG) → Fin M → BP g,
        if Function.Injective (fun x : Sigma (fun _ : BG => Fin M) =>
          bm x.1 (a x.1 x.2))
        then ∏ g,activeMass M (physicalSourceMuTilde BP bm q N V g) (a g)
        else 0) ≤ 1 := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ a : (g : BG) → Fin M → BP g,
        ∏ g,activeMass M (fun p => 1/(V g*(bm g p:ℝ))) (a g) := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs with hn
      · exact source_original_ACTUAL_distinct_active_baseline_cancel434 BP bm M q N V hV a hn hb hb1
      · rw [mul_zero]
        apply Finset.prod_nonneg
        intro g hg
        exact activeMass_nonneg M _ (fun p =>
          div_nonneg zero_le_one (mul_nonneg (hV g).le (Nat.cast_nonneg _))) (a g)
    _ = 1 := source_original_ACTUAL_active_harmonic_mass_one434 BP bm M V hV hHarmonic
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualInitialSMALLMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- A direct bound for the actual marked SMALL state mass. Its Haar
torus cardinality cancels; the explicitly retained cost is (#P/V)^M.
No false unit normalization of marked states is used. -/
theorem source_original_ACTUAL_SMALL_initial_mass_bound434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
    (M : ℕ) (V : ℝ) (hV : 0 < V) :
    (∑ x : SmallState modulus M,stateMass modulus M V) ≤
      ((Fintype.card P:ℝ)/V)^M := by
  have hc : Fintype.card (SmallState modulus M) ≤
      Fintype.card (SmallTorus modulus × (Fin M → P)) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hcR : (Fintype.card (SmallState modulus M):ℝ) ≤
      (Fintype.card (SmallTorus modulus):ℝ)*(Fintype.card P:ℝ)^M := by
    exact_mod_cast (by simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] using hc)
  have ht : (Fintype.card (SmallTorus modulus):ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (⟨fun _ => 0⟩ : Nonempty (SmallTorus modulus))).ne'
  calc
    _ = (Fintype.card (SmallState modulus M):ℝ)*stateMass modulus M V := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ ((Fintype.card (SmallTorus modulus):ℝ)*(Fintype.card P:ℝ)^M)*
        stateMass modulus M V :=
      mul_le_mul_of_nonneg_right hcR (stateMass_positive modulus M V hV).le
    _ = _ := by
      unfold stateMass haarAtomMass
      rw [div_pow]
      field_simp

/-- Tensorization over the genuine SMALL physical state families.
All group and active-slot costs are explicit. -/
theorem source_original_ACTUAL_SMALL_GROUP_initial_mass_bound434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (M : ℕ) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) :
    (∑ s : GroupState SP sm M,groupStateMass SP sm M Vs) ≤
      ∏ g,((Fintype.card (SP g):ℝ)/Vs g)^M := by
  change (∑ s : (g : SG) → SmallState (sm g) M,
    ∏ g,stateMass (sm g) M (Vs g)) ≤ _
  have he : (∑ s : (g : SG) → SmallState (sm g) M,
      ∏ g,stateMass (sm g) M (Vs g)) =
      ∏ g,∑ s : SmallState (sm g) M,stateMass (sm g) M (Vs g) := by
    convert (Fintype.prod_sum (fun (g : SG) (_s : SmallState (sm g) M) =>
      stateMass (sm g) M (Vs g))).symm using 1
  rw [he]
  apply Finset.prod_le_prod₀
  · intro g hg
    exact Finset.sum_nonneg (fun _ _ => (stateMass_positive (sm g) M (Vs g) (hVs g)).le)
  · intro g hg
    exact source_original_ACTUAL_SMALL_initial_mass_bound434 (sm g) M (Vs g) (hVs g)
end Green64Analytic.CorrelationSquare

end

end

