module

public import Green64.Library.Weights.MarkedSquareDominatesW1

@[expose] public section

/-!
# Weights / SelectedGroupEnergy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SelectedGroupEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact count of two choices of the unobserved base mark, allowing
the two choices to agree but requiring each to avoid the selected list. -/
theorem b579_selected_base_square_count (N c : ℕ) :
    N.descFactorial c * (N-c)^2 =
      N.descFactorial (c+2) + N.descFactorial (c+1) := by
  by_cases hc : c < N
  · have hs : N-c = (N-(c+1))+1 := by omega
    have hstep : N.descFactorial (c+2) =
        (N-(c+1))*((N-c)*N.descFactorial c) := by
      rw [show c+2=(c+1)+1 by omega, Nat.descFactorial_succ,
        Nat.descFactorial_succ]
    rw [hstep, Nat.descFactorial_succ, hs]
    ring
  · have hNc : N ≤ c := by omega
    have h1 : N.descFactorial (c+1)=0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    have h2 : N.descFactorial (c+2)=0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [h1,h2,Nat.sub_eq_zero_of_le hNc]
    norm_num

/-- Exact scalar energy of the selected c coordinates after summing the
single unobserved base mark, with the ORIGINAL q damping and V powers. -/
def b579SelectedGroupEnergy (q : ℝ) (c N : ℕ) (V : ℝ) : ℝ :=
  (q^((N:ℤ)-((c+1:ℕ):ℤ)) * ((N-c:ℕ):ℝ) / V)^2 *
    (N.descFactorial c:ℝ) / V^c

private theorem b579_square_zpow (q : ℝ) (z : ℤ) :
    (q^z)^2 = (q^2)^z := by
  calc
    _ = q^(z*(2:ℤ)) := by norm_num [zpow_mul]
    _ = q^((2:ℤ)*z) := by congr 1; ring
    _ = _ := by norm_num [zpow_mul]

/-- The selected-coordinate energy is a sum of TWO original marked
weights at q squared. No prime-product cap or free-state normalization
is inserted into this identity. -/
theorem b579_selected_group_energy_exact
    (q V : ℝ) (c N : ℕ) (hq : 0<q) (hV : 0<V) :
    b579SelectedGroupEnergy q c N V =
      q^2*b575MarkedGroup (q^2) (c+2) N V +
        b575MarkedGroup (q^2) (c+1) N V / V := by
  have hcount : (N.descFactorial c:ℝ)*((N-c:ℕ):ℝ)^2 =
      (N.descFactorial (c+2):ℝ)+(N.descFactorial (c+1):ℝ) := by
    exact_mod_cast b579_selected_base_square_count N c
  have hz : (N:ℤ)-((c+1:ℕ):ℤ) =
      ((N:ℤ)-((c+2:ℕ):ℤ))+1 := by omega
  have hp : (q^2)^((N:ℤ)-((c+1:ℕ):ℤ)) =
      (q^2)^((N:ℤ)-((c+2:ℕ):ℤ))*q^2 := by
    conv_lhs => rw [hz]
    rw [zpow_add₀ (pow_ne_zero _ hq.ne'),zpow_one]
  unfold b579SelectedGroupEnergy b575MarkedGroup
  rw [div_pow,mul_pow,b579_square_zpow]
  have hV0 : V ≠ 0 := hV.ne'
  rw [show V^(c+2)=V^c*V^2 by rw [pow_add],
    show V^(c+1)=V^c*V by rw [pow_succ]]
  field_simp
  calc
    _ = (q^2)^((N:ℤ)-((c+1:ℕ):ℤ)) *
        ((N.descFactorial c:ℝ)*((N-c:ℕ):ℝ)^2) := by ring
    _ = _ := by rw [hcount,hp]; ring

theorem b579_selected_group_energy_nonneg
    (q V : ℝ) (c N : ℕ) (hV : 0≤V) :
    0 ≤ b579SelectedGroupEnergy q c N V := by
  unfold b579SelectedGroupEnergy
  positivity

/-- The collapsed, active-cell-normalized selected endpoint has a
constant energy per actual group. The constant is independent of the
endpoint distinct count, auxiliary product, and prime sizes. -/
theorem b579_selected_group_energy_uniform
    (vmin : ℝ) (cmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧ ∀ (c N : ℕ) (V : ℝ),
      c≤ cmax → vmin≤V →
      b579SelectedGroupEnergy (1/2) c N V ≤ C := by
  obtain ⟨K,hK,hbound⟩ := uniform_group_mark_bound
    (1/4:ℝ) vmin (cmax+2) (by norm_num) (by norm_num) hv
  let C : ℝ := K+K/vmin
  have hKn : 0≤K := by linarith
  have hC : 1≤C := by
    have hd0 : 0≤K/vmin := div_nonneg hKn hv.le
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro c N V hc hV
  have hVp : 0<V := hv.trans_le hV
  have h1 : b575MarkedGroup (1/4) (c+1) N V ≤ K :=
    (le_abs_self _).trans (hbound (c+1) N V (by omega) hV)
  have h2 : b575MarkedGroup (1/4) (c+2) N V ≤ K :=
    (le_abs_self _).trans (hbound (c+2) N V (by omega) hV)
  rw [b579_selected_group_energy_exact (1/2) V c N (by norm_num) hVp]
  norm_num only [show (1/2:ℝ)^2=(1/4:ℝ) by norm_num]
  have hd : b575MarkedGroup (1/4) (c+1) N V / V ≤ K/vmin := by
    calc
      _ ≤ K/V := div_le_div_of_nonneg_right h1 hVp.le
      _ ≤ K/vmin := div_le_div_of_nonneg_left hKn hv hV
  dsimp [C]
  nlinarith

/-- One fixed constant per retained group, without a cardinality cost
for its prime alphabet or for its injective mark lists. -/
theorem b579_selected_all_group_energy_uniform
    (vmin : ℝ) (cmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧
      ∀ {G : Type} [Fintype G] (c N : G → ℕ) (V : G → ℝ),
      (∀ g,c g≤ cmax) → (∀ g,vmin≤V g) →
      (∏ g,b579SelectedGroupEnergy (1/2) (c g) (N g) (V g)) ≤
        C^(Fintype.card G) := by
  obtain ⟨C,hC,hbound⟩ := b579_selected_group_energy_uniform vmin cmax hv
  refine ⟨C,hC,?_⟩
  intro G _ c N V hc hV
  calc
    _ ≤ ∏ _g : G,C := by
      apply Finset.prod_le_prod₀
      · intro g _; exact b579_selected_group_energy_nonneg _ _ _ _ (hv.trans_le (hV g)).le
      · intro g _; exact hbound (c g) (N g) (V g) (hc g) (hV g)
    _ = _ := by simp
end Green64Analytic.CorrelationSquare

end

end

