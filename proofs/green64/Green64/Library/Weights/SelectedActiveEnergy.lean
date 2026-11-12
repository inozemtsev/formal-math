module

public import Green64.Library.Weights.SelectedGroupEnergy

@[expose] public section

/-!
# Weights / SelectedActiveEnergy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualSelectedActiveEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {G : Type} [Fintype G] [DecidableEq G]

/-- Numeric product of exactly the coordinates seen by one canonical
block column, with its original ordered labels. -/
def b579SelectedPrimeProduct (c : G → ℕ)
    (a : ∀ g,Fin (c g) → ℕ) : ℝ :=
  ∏ g, ∏ i : Fin (c g),(a g i:ℝ)

/-- Restriction of the unchanged independent reciprocal-prime law to
the selected coordinates; there is no conditional renormalization. -/
def b579SelectedHarmonicMass (c : G → ℕ) (V : G → ℝ)
    (a : ∀ g,Fin (c g) → ℕ) : ℝ :=
  ∏ g, ∏ i : Fin (c g),1/((a g i:ℝ)*V g)

/-- Coefficient left by exactly summing the unobserved base slot in
each group. Distinctness is retained in N-c. -/
def b579SelectedBaseFactor (q : ℝ) (c N : G → ℕ) (V : G → ℝ) : ℝ :=
  ∏ g,q^((N g:ℤ)-((c g+1:ℕ):ℤ))*((N g-c g:ℕ):ℝ)/V g

/-- The selected-coordinate lift with its actual numeric product,
normalized by the actual auxiliary block product D. -/
def b579ActualSelectedEnergy
    (P : G → Finset ℕ) (c : G → ℕ) (V : G → ℝ)
    (q D : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ) : ℝ :=
  ∑ a ∈ bigMarkLists P c n,
    b579SelectedHarmonicMass c V a *
      (b579SelectedPrimeProduct c a)^2/D *
      ((b579SelectedBaseFactor q c (fun g => smallPrimeCount (P g) n) V)^2 *
        ‖f a‖^2)

omit [DecidableEq G] in
theorem b579_selected_harmonic_density
    (c : G → ℕ) (V : G → ℝ) (a : ∀ g,Fin (c g) → ℕ)
    (hV : ∀ g,0<V g) (ha : ∀ g i,0<a g i) :
    b579SelectedHarmonicMass c V a * b579SelectedPrimeProduct c a =
      (∏ g,(V g)^(c g))⁻¹ := by
  unfold b579SelectedHarmonicMass b579SelectedPrimeProduct
  rw [←Finset.prod_mul_distrib]
  calc
    _ = ∏ g : G,((V g)^(c g))⁻¹ := by
      apply Finset.prod_congr rfl
      intro g _
      rw [←Finset.prod_mul_distrib]
      calc
        _ = ∏ _i : Fin (c g),(V g)⁻¹ := by
          apply Finset.prod_congr rfl
          intro i _
          have hp : (a g i:ℝ) ≠ 0 := by exact_mod_cast (ha g i).ne'
          have hv : V g ≠ 0 := (hV g).ne'
          field_simp
        _ = _ := by simp
    _ = _ := by rw [Finset.prod_inv_distrib]

private theorem b579_actual_mark_positive
    (P : G → Finset ℕ) (c : G → ℕ) (n : ℕ)
    (hP : ∀ g p,p ∈ P g → 0<p)
    (a : ∀ g,Fin (c g) → ℕ) (ha : a ∈ bigMarkLists P c n) :
    ∀ g i,0<a g i := by
  intro g i
  have hg := Fintype.mem_piFinset.mp ha g
  have hi := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hg).1 i
  exact hP g _ (Finset.mem_filter.mp hi).1

theorem b579_selected_energy_count_factor
    (P : G → Finset ℕ) (c : G → ℕ) (V : G → ℝ)
    (q : ℝ) (n : ℕ) :
    (b579SelectedBaseFactor q c (fun g => smallPrimeCount (P g) n) V)^2 *
      ((bigMarkLists P c n).card:ℝ)/(∏ g,(V g)^(c g)) =
      ∏ g,b579SelectedGroupEnergy q (c g) (smallPrimeCount (P g) n) (V g) := by
  rw [bigMarkLists_card]
  push_cast
  unfold b579SelectedBaseFactor b579SelectedGroupEnergy
  rw [←Finset.prod_pow,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]

/-- Genuine active-product energy estimate on the EXISTING ordered
distinct prime-divisor lists. The support condition is the upper edge
of the actual canonical log cell, X≤exp(h)D. No bound on the physical
energy or on the number of primes is assumed. -/
theorem b579_actual_selected_active_energy_bound
    (P : G → Finset ℕ) (c : G → ℕ) (V : G → ℝ)
    (q D R : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ)
    (hP : ∀ g p,p ∈ P g → 0<p)
    (hV : ∀ g,0<V g) (hD : 0<D) (hR : 0≤R)
    (hf : ∀ a ∈ bigMarkLists P c n,‖f a‖≤1)
    (hActive : ∀ a ∈ bigMarkLists P c n,
      f a ≠ 0 → b579SelectedPrimeProduct c a ≤ R*D) :
    b579ActualSelectedEnergy P c V q D n f ≤
      R*∏ g,b579SelectedGroupEnergy q (c g) (smallPrimeCount (P g) n) (V g) := by
  let B := b579SelectedBaseFactor q c (fun g => smallPrimeCount (P g) n) V
  let A := ∏ g,(V g)^(c g)
  have hA : 0<A := Finset.prod_pos (fun g _ => pow_pos (hV g) _)
  have hterm (a : ∀ g,Fin (c g) → ℕ) (ha : a ∈ bigMarkLists P c n) :
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
      (b579_actual_mark_positive P c n hP a ha)
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
  unfold b579ActualSelectedEnergy
  calc
    _ ≤ ∑ _a ∈ bigMarkLists P c n,R*B^2/A :=
      Finset.sum_le_sum (fun a ha => hterm a ha)
    _ = R*(B^2*((bigMarkLists P c n).card:ℝ)/A) := by simp; ring
    _ = _ := by rw [b579_selected_energy_count_factor]

/-- Uniform bound for the actual selected-coordinate endpoint at q=1/2.
The explicit active-cell factor R and one fixed constant per group remain. -/
theorem b579_actual_selected_active_energy_uniform
    (vmin : ℝ) (cmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧ ∀ {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) (c : G → ℕ) (V : G → ℝ)
      (D R : ℝ) (n : ℕ) (f : (∀ g,Fin (c g) → ℕ) → ℂ),
      (∀ g p,p ∈ P g → 0<p) →
      (∀ g,c g≤ cmax) → (∀ g,vmin≤V g) → 0<D → 0≤R →
      (∀ a ∈ bigMarkLists P c n,‖f a‖≤1) →
      (∀ a ∈ bigMarkLists P c n,
        f a≠0 → b579SelectedPrimeProduct c a≤R*D) →
      b579ActualSelectedEnergy P c V (1/2) D n f ≤ R*C^(Fintype.card G) := by
  obtain ⟨C,hC,hbound⟩ := b579_selected_all_group_energy_uniform vmin cmax hv
  refine ⟨C,hC,?_⟩
  intro G _ _ P c V D R n f hP hc hV hD hR hf hActive
  exact (b579_actual_selected_active_energy_bound P c V (1/2) D R n f
    hP (fun g => hv.trans_le (hV g)) hD hR hf hActive).trans
      (mul_le_mul_of_nonneg_left (hbound c (fun g => smallPrimeCount (P g) n) V hc hV) hR)
end Green64Analytic.CorrelationSquare

end

end

