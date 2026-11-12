module

public import Green64.Library.Correlation.ActualPositiveRootCost

@[expose] public section

/-!
# Weights / ActualInitialBaseline

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualInitialBaseline -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem distinct_baseline_product434
    {I P : Type} [Fintype I] [Fintype P] [DecidableEq P]
    (f : I → P) (hf : Function.Injective f)
    (b w : P → ℝ) (hb : ∀ p,0 < b p) (hb1 : ∀ p,b p ≤ 1)
    (hw : ∀ p,0 ≤ w p) :
    (∏ p,b p)*(∏ i,w (f i)/b (f i)) ≤ ∏ i,w (f i) := by
  have hprod : (∏ p,b p) ≤ ∏ i,b (f i) := by
    have hh := Finset.prod_le_prod_of_subset_of_le_one₀
      (Finset.subset_univ (Finset.univ.image f))
      (fun p (_ : p ∈ Finset.univ) => (hb p).le)
      (fun p (_ : p ∈ Finset.univ) _ => hb1 p)
    rw [Finset.prod_image (fun i _ j _ hij => hf hij)] at hh
    exact hh
  calc
    _ ≤ (∏ i,b (f i))*(∏ i,w (f i)/b (f i)) :=
      mul_le_mul_of_nonneg_right hprod
        (Finset.prod_nonneg (fun i _ => div_nonneg (hw _) (hb _).le))
    _ = _ := by
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      field_simp [ne_of_gt (hb (f i))]

/-- The ORIGINAL baseline cancels the tilt denominators of a globally
distinct initial active array. There is no loss exponential in the
number of active slots. Distinctness here is numerical across groups. -/
theorem source_original_ACTUAL_distinct_active_baseline_cancel434
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (M : ℕ) (q : ℝ) (N : ℕ) (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (a : (g : BG) → Fin M → BP g)
    (ha : Function.Injective (fun x : Sigma (fun _ : BG => Fin M) => bm x.1 (a x.1 x.2)))
    (hb : ∀ g p,0 < physicalSourceBaseline BP bm q N g p)
    (hb1 : ∀ g p,physicalSourceBaseline BP bm q N g p ≤ 1) :
    ‖(physicalSourceBaselineProduct BP bm q N:ℂ)‖ *
      (∏ g,activeMass M (physicalSourceMuTilde BP bm q N V g) (a g)) ≤
    ∏ g,activeMass M (fun p => 1/(V g*(bm g p:ℝ))) (a g) := by
  let f : Sigma (fun _ : BG => Fin M) → Sigma BP := fun x => ⟨x.1,a x.1 x.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply ha
    exact congrArg (fun x : Sigma BP => bm x.1 x.2) hij
  have hw (x : Sigma BP) : 0 ≤ 1/(V x.1*(bm x.1 x.2:ℝ)) := by
    exact div_nonneg zero_le_one (mul_nonneg (hV x.1).le (Nat.cast_nonneg _))
  have hh := distinct_baseline_product434 f hf
    (fun x : Sigma BP => physicalSourceBaseline BP bm q N x.1 x.2)
    (fun x : Sigma BP => 1/(V x.1*(bm x.1 x.2:ℝ)))
    (fun x => hb x.1 x.2) (fun x => hb1 x.1 x.2) hw
  have hp : 0 ≤ physicalSourceBaselineProduct BP bm q N := by
    exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun p _ => (hb g p).le))
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  simpa only [physicalSourceBaselineProduct,activeMass,Fintype.prod_sigma,
    physicalSourceMuTilde,div_div,f] using hh
end Green64Analytic.CorrelationSquare

end

end

