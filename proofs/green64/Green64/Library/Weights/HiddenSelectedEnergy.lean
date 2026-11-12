module

public import Green64.Library.Weights.ArbitraryObservedSlots
public import Green64.Library.Correlation.Part067

@[expose] public section

/-!
# Weights / HiddenSelectedEnergy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualHiddenSelectedEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000
variable {G : Type} [Fintype G] [DecidableEq G]

/-- Literal selected-coordinate harmonic energy AFTER all r_g hidden
base/opposite-block slots have been summed. The actual numeric selected
product and auxiliary normalization D are retained. -/
def b580ActualHiddenSelectedEnergy
    (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
    (q D : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ) : ℝ :=
  ∑ a∈bigMarkLists P c n,
    b579SelectedHarmonicMass c V a *
      (b579SelectedPrimeProduct c a)^2/D *
      ((b580HiddenAllFactor q c r (fun g => smallPrimeCount (P g) n) V)^2 *
        ‖f a‖^2)

private theorem b580_actual_mark_positive
    (P : G → Finset ℕ) (c : G → ℕ) (n : ℕ)
    (hP : ∀ g p,p∈P g → 0<p)
    (a : ∀ g,Fin (c g) → ℕ) (ha : a∈bigMarkLists P c n) :
    ∀ g i,0<a g i := by
  intro g i
  have hg := Fintype.mem_piFinset.mp ha g
  have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
  exact hP g _ (Finset.mem_filter.mp hi).1

theorem b580_hidden_selected_energy_count_factor
    (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
    (q : ℝ) (n : ℕ) :
    (b580HiddenAllFactor q c r (fun g => smallPrimeCount (P g) n) V)^2 *
      ((bigMarkLists P c n).card:ℝ)/(∏ g,(V g)^(c g)) =
      ∏ g,b580HiddenGroupEnergy q (c g) (r g) (smallPrimeCount (P g) n) (V g) := by
  rw [bigMarkLists_card]
  push_cast
  unfold b580HiddenAllFactor b580HiddenGroupEnergy
  rw [←Finset.prod_pow,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]

/-- Pointwise active-product estimate, on the EXISTING observed distinct
lists with all hidden counts retained. Auxiliary dependence may remain
arbitrary inside f. The only size premise is the actual active cell edge. -/
theorem b580_hidden_selected_active_energy_bound
    (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
    (q D R : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ)
    (hP : ∀ g p,p∈P g → 0<p)
    (hV : ∀ g,0<V g) (hD : 0<D) (hR : 0≤R)
    (hf : ∀ a∈bigMarkLists P c n,‖f a‖≤1)
    (hActive : ∀ a∈bigMarkLists P c n,
      f a≠0 → b579SelectedPrimeProduct c a≤R*D) :
    b580ActualHiddenSelectedEnergy P c r V q D n f ≤
      R*∏ g,b580HiddenGroupEnergy q (c g) (r g) (smallPrimeCount (P g) n) (V g) := by
  let B := b580HiddenAllFactor q c r (fun g => smallPrimeCount (P g) n) V
  let A := ∏ g,(V g)^(c g)
  have hA : 0<A := Finset.prod_pos (fun g _ => pow_pos (hV g) _)
  have hterm (a : ∀ g,Fin (c g) → ℕ) (ha : a∈bigMarkLists P c n) :
      b579SelectedHarmonicMass c V a*(b579SelectedPrimeProduct c a)^2/D*
        (B^2*‖f a‖^2) ≤ R*B^2/A := by
    have hmu : 0≤b579SelectedHarmonicMass c V a := by
      unfold b579SelectedHarmonicMass
      apply Finset.prod_nonneg
      intro g _
      apply Finset.prod_nonneg
      intro i _
      exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (hV g).le)
    by_cases hz : f a=0
    · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero]
      positivity
    have hX := hActive a ha hz
    have hden := b579_selected_harmonic_density c V a hV
      (b580_actual_mark_positive P c n hP a ha)
    have hf2 : ‖f a‖^2≤1 := by
      nlinarith [hf a ha,norm_nonneg (f a)]
    have hpre : 0≤b579SelectedHarmonicMass c V a*
        (b579SelectedPrimeProduct c a)^2/D := by positivity
    calc
      _ ≤ b579SelectedHarmonicMass c V a*
          (b579SelectedPrimeProduct c a)^2/D*B^2 := by
        have hh := mul_le_mul_of_nonneg_left hf2 (mul_nonneg hpre (sq_nonneg B))
        nlinarith only [hh]
      _ = (b579SelectedPrimeProduct c a/D)*B^2/A := by
        calc
          _ = (b579SelectedHarmonicMass c V a*b579SelectedPrimeProduct c a)*
              (b579SelectedPrimeProduct c a/D)*B^2 := by ring
          _ = _ := by rw [hden]; dsimp [A]; ring
      _ ≤ R*B^2/A := by
        have hh : b579SelectedPrimeProduct c a/D≤R := (div_le_iff₀ hD).mpr hX
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hh (sq_nonneg B)) hA.le
  unfold b580ActualHiddenSelectedEnergy
  calc
    _ ≤ ∑ _a∈bigMarkLists P c n,R*B^2/A :=
      Finset.sum_le_sum (fun a ha => hterm a ha)
    _ = R*(B^2*((bigMarkLists P c n).card:ℝ)/A) := by simp; ring
    _ = _ := by rw [b580_hidden_selected_energy_count_factor]

/-- Uniform actual endpoint energy with one constant per group and ALL
hidden slots. It requires no bound on N, the prime alphabet or D. -/
theorem b580_hidden_selected_active_energy_uniform
    (vmin : ℝ) (tmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧ ∀ {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
      (D R : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ),
      (∀ g p,p∈P g → 0<p) →
      (∀ g,c g+r g≤tmax) → (∀ g,vmin≤V g) → 0<D → 0≤R →
      (∀ a∈bigMarkLists P c n,‖f a‖≤1) →
      (∀ a∈bigMarkLists P c n,
        f a≠0 → b579SelectedPrimeProduct c a≤R*D) →
      b580ActualHiddenSelectedEnergy P c r V (1/2) D n f≤R*C^(Fintype.card G) := by
  obtain ⟨C,hC,hbound⟩ := b580_hidden_all_group_energy_uniform vmin tmax hv
  refine ⟨C,hC,?_⟩
  intro G _ _ P c r V D R n f hP ht hV hD hR hf hActive
  exact (b580_hidden_selected_active_energy_bound P c r V (1/2) D R n f
    hP (fun g => hv.trans_le (hV g)) hD hR hf hActive).trans
      (mul_le_mul_of_nonneg_left
        (hbound c r (fun g => smallPrimeCount (P g) n) V ht hV) hR)

theorem b580_hidden_selected_energy_scalar
    (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
    (q D : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ) (z : ℂ) :
    b580ActualHiddenSelectedEnergy P c r V q D n (fun a => z*f a) =
      ‖z‖^2*b580ActualHiddenSelectedEnergy P c r V q D n f := by
  unfold b580ActualHiddenSelectedEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [norm_mul,mul_pow]
  ring

/-- Finite native bound for a literal full primitive canonical column
with arbitrary hidden base/opposite probes. The actual conductor/cell
cap remains explicitly squared, and cell support is proved from Kν. -/
theorem b580_actual_canonical_hidden_energy_uniform
    (vmin : ℝ) (tmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧ ∀ {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) (c r : G → ℕ) (V : G → ℝ)
      (Q : ℕ) (active : Finset ℤ) (h xi : ℝ) (mass : ℤ → ℝ)
      (D n : ℕ),
      (∀ g p,p∈P g → 0<p) → (∀ g,c g+r g≤tmax) → (∀ g,vmin≤V g) →
      0<D → 0<h → 0<xi → (∀ j∈active,xi ≤ mass j) →
      b580ActualHiddenSelectedEnergy P c r V (1/2) (D:ℝ) n
        (fun a => sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D
          (∏ g,∏ i : Fin (c g),a g i)) ≤
      (max 1 ((Q:ℝ)^2*xi⁻¹))^2*Real.exp h*C^(Fintype.card G) := by
  obtain ⟨C,hC,hbound⟩ := b580_hidden_selected_active_energy_uniform vmin tmax hv
  refine ⟨C,hC,?_⟩
  intro G _ _ P c r V Q active h xi mass D n hP ht hV hD hh hxi hMass
  let K : (∀ g,Fin (c g) → ℕ) → ℂ := fun a =>
    sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D
      (∏ g,∏ i : Fin (c g),a g i)
  let S : ℝ := max 1 ((Q:ℝ)^2*xi⁻¹)
  let f := fun a => K a/(S:ℂ)
  have hS : 0<S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hSc : (S:ℂ)≠0 := by exact_mod_cast hS.ne'
  have hf (a : ∀ g,Fin (c g) → ℕ) : ‖f a‖≤1 := by
    dsimp [f]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
    apply (div_le_one hS).mpr
    exact (source_original_actual_primitive_global_bound434
      Q active h hh mass xi hxi hMass D _).trans (le_max_right _ _)
  have hAct (a : ∀ g,Fin (c g) → ℕ)
      (_ha : a∈bigMarkLists P c n) (hf0 : f a≠0) :
      b579SelectedPrimeProduct c a≤Real.exp h*(D:ℝ) := by
    have hK : K a≠0 := by
      intro hz
      apply hf0
      dsimp [f]
      rw [hz,zero_div]
    have hb := b579_actual_primitive_column_product_bound
      Q active h hh mass D _ hD hK
    simpa only [b579SelectedPrimeProduct,Nat.cast_prod] using hb
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have he := hbound P c r V (D:ℝ) (Real.exp h) n f
    hP ht hV hDr (Real.exp_pos h).le (fun a _ => hf a) hAct
  have hKrec : K=(fun a => (S:ℂ)*f a) := by
    funext a
    dsimp [f]
    field_simp
  change b580ActualHiddenSelectedEnergy P c r V (1/2) (D:ℝ) n K≤_
  rw [hKrec,b580_hidden_selected_energy_scalar,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg S)
  simpa only [S,mul_assoc] using hm
end Green64Analytic.CorrelationSquare

end

end

