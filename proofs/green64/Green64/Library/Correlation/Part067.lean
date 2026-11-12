module

public import Green64.Library.Weights.BaseSlotMarginal
public import Green64.Library.Weights.Part052
public import Green64.Library.Weights.MarkedSquareDominatesW1

@[expose] public section

/-!
# Correlation / Part067

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualCanonicalSelectedEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Nonzero literal primitive kernel forces the actual output product
within exp(h) of its own positive auxiliary input product. -/
theorem b579_actual_primitive_column_product_bound
    (Q : ℕ) (active : Finset ℤ) (h : ℝ) (hh : 0<h)
    (mass : ℤ → ℝ) (D X : ℕ) (hD : 0<D)
    (hK : sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D X≠0) :
    (X:ℝ)≤Real.exp h*(D:ℝ) := by
  by_cases hz : X=0
  · simp only [hz,Nat.cast_zero]
    positivity
  have hX : 0<X := Nat.pos_of_ne_zero hz
  have he : sourceOriginalLiteralLogCellIndex434 h D=
      sourceOriginalLiteralLogCellIndex434 h X := by
    by_contra hoff
    exact hK (source_original_true_primitive_global_kernel_cell_mismatch_zero434
      Q active h hh mass D X hoff)
  let j := sourceOriginalLiteralLogCellIndex434 h D
  have hd : sourceOriginalLiteralLogCell434 h j D :=
    (source_original_literal_log_cell_iff_index434 h hh D j).mpr rfl
  have hx : sourceOriginalLiteralLogCell434 h j X :=
    (source_original_literal_log_cell_iff_index434 h hh X j).mpr he
  have hlog : Real.log (X:ℝ)≤h+Real.log (D:ℝ) := by
    dsimp [sourceOriginalLiteralLogCell434] at hd hx
    linarith [hd.1,hx.2]
  have hDr : 0<(D:ℝ) := by exact_mod_cast hD
  have hXr : 0<(X:ℝ) := by exact_mod_cast hX
  calc
    _ = Real.exp (Real.log (X:ℝ)) := (Real.exp_log hXr).symm
    _ ≤ Real.exp (h+Real.log (D:ℝ)) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [Real.exp_add,Real.exp_log hDr]

theorem b579_actual_selected_energy_scalar
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (c : G → ℕ) (V : G → ℝ)
    (q D : ℝ) (n : ℕ) (f : (∀g,Fin (c g) → ℕ) → ℂ) (z : ℂ) :
    b579ActualSelectedEnergy P c V q D n (fun a => z*f a) =
      ‖z‖^2*b579ActualSelectedEnergy P c V q D n f := by
  unfold b579ActualSelectedEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [norm_mul,mul_pow]
  ring

/-- The finite bound for an ACTUAL full primitive canonical block
column. Its original conductor/cell cap remains explicitly squared;
the product-size and active-cell conditions are derived from the
literal kernel rather than supplied as a desired energy hypothesis. -/
theorem b579_actual_canonical_selected_energy_uniform
    (vmin : ℝ) (cmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧ ∀ {G : Type} [Fintype G] [DecidableEq G]
      (P : G → Finset ℕ) (c : G → ℕ) (V : G → ℝ)
      (Q : ℕ) (active : Finset ℤ) (h xi : ℝ) (mass : ℤ → ℝ)
      (D n : ℕ),
      (∀g p,p∈P g → 0<p) → (∀g,c g≤ cmax) → (∀g,vmin≤V g) →
      0<D → 0<h → 0<xi → (∀j∈active,xi ≤ mass j) →
      b579ActualSelectedEnergy P c V (1/2) (D:ℝ) n
        (fun a => sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D
          (∏g,∏i : Fin (c g),a g i)) ≤
      (max 1 ((Q:ℝ)^2*xi⁻¹))^2*Real.exp h*C^(Fintype.card G) := by
  obtain ⟨C,hC,hbound⟩ := b579_actual_selected_active_energy_uniform vmin cmax hv
  refine ⟨C,hC,?_⟩
  intro G _ _ P c V Q active h xi mass D n hP hc hV hD hh hxi hMass
  let K : (∀g,Fin (c g) → ℕ) → ℂ := fun a =>
    sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D
      (∏g,∏i : Fin (c g),a g i)
  let S : ℝ := max 1 ((Q:ℝ)^2*xi⁻¹)
  let f := fun a => K a/(S:ℂ)
  have hS : 0<S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hSc : (S:ℂ)≠0 := by exact_mod_cast hS.ne'
  have hf (a : ∀g,Fin (c g) → ℕ) : ‖f a‖≤1 := by
    dsimp [f]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
    apply (div_le_one hS).mpr
    exact (source_original_actual_primitive_global_bound434
      Q active h hh mass xi hxi hMass D _).trans (le_max_right _ _)
  have hAct (a : ∀g,Fin (c g) → ℕ)
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
  have he := hbound P c V (D:ℝ) (Real.exp h) n f
    hP hc hV hDr (Real.exp_pos h).le (fun a _ => hf a) hAct
  have hKrec : K=(fun a => (S:ℂ)*f a) := by
    funext a
    dsimp [f]
    field_simp
  change b579ActualSelectedEnergy P c V (1/2) (D:ℝ) n K ≤ _
  rw [hKrec,b579_actual_selected_energy_scalar,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg S)
  simpa only [S,mul_assoc] using hm
end Green64Analytic.CorrelationSquare

end

end

/-! ## HiddenGroupEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Exact damping and hidden-completion factor after retaining c of the
original c+r ordered marks. The exponent is the original INTEGER exponent. -/
def b580HiddenGroupFactor (q : ℝ) (c r N : ℕ) (V : ℝ) : ℝ :=
  q^((N:ℤ)-((c+r:ℕ):ℤ)) * ((N-c).descFactorial r:ℝ) / V^r

/-- Selected-coordinate counting energy after summing ALL r hidden slots. -/
def b580HiddenGroupEnergy (q : ℝ) (c r N : ℕ) (V : ℝ) : ℝ :=
  (b580HiddenGroupFactor q c r N V)^2 * (N.descFactorial c:ℝ) / V^c

/-- With an occupied selected carrier, the exact hidden factor is itself
the original marked weight on the N-c remaining divisor primes. -/
theorem b580_hidden_factor_eq_marked_tail
    (q V : ℝ) (c r N : ℕ) (hc : c≤N) :
    b580HiddenGroupFactor q c r N V =
      b575MarkedGroup q r (N-c) V := by
  have he : (N:ℤ)-((c+r:ℕ):ℤ)=((N-c:ℕ):ℤ)-(r:ℤ) := by omega
  simp only [b580HiddenGroupFactor,b575MarkedGroup,he]

/-- Exact two-original-weight factorization. It keeps both the full
mark order c+r and the hidden mark order r, without replacing the
distinct divisor count by a valuation or a global prime-product cap. -/
theorem b580_hidden_group_energy_exact
    (q V : ℝ) (c r N : ℕ) (hc : c≤N) :
    b580HiddenGroupEnergy q c r N V =
      b575MarkedGroup q (c+r) N V *
        b575MarkedGroup q r (N-c) V := by
  have he : ((N-c:ℕ):ℤ)-(r:ℤ)=(N:ℤ)-((c+r:ℕ):ℤ) := by omega
  have hf : (N.descFactorial (c+r):ℝ) =
      (N.descFactorial c:ℝ)*((N-c).descFactorial r:ℝ) := by
    have hnat : N.descFactorial (c+r) =
        N.descFactorial c*(N-c).descFactorial r := by
      simpa [Nat.mul_comm] using
        (Nat.descFactorial_mul_descFactorial (n:=N) (k:=c) (m:=c+r) (by omega)).symm
    exact_mod_cast hnat
  unfold b580HiddenGroupEnergy b580HiddenGroupFactor b575MarkedGroup
  rw [he,hf,pow_add]
  simp only [div_eq_mul_inv,mul_inv_rev,mul_pow]
  ring

/-- An overfull selected carrier has EXACTLY zero energy. No division
by a vanishing factorial or presumed nonempty list is used. -/
theorem b580_hidden_group_energy_zero_of_overfull
    (q V : ℝ) (c r N : ℕ) (hc : N<c) :
    b580HiddenGroupEnergy q c r N V=0 := by
  simp only [b580HiddenGroupEnergy,
    Nat.descFactorial_eq_zero_iff_lt.mpr hc,Nat.cast_zero,mul_zero,zero_div]

theorem b580_hidden_group_energy_nonneg
    (q V : ℝ) (c r N : ℕ) (hV : 0≤V) :
    0≤b580HiddenGroupEnergy q c r N V := by
  unfold b580HiddenGroupEnergy
  positivity

/-- One fixed group constant bounds arbitrary bounded hidden and observed
mark counts. Both factors use the existing ORIGINAL uniform marked bound
at q=1/2; no independent auxiliary averaging is required. -/
theorem b580_hidden_group_energy_uniform
    (vmin : ℝ) (tmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧ ∀ (c r N : ℕ) (V : ℝ),
      c+r≤tmax → vmin≤V →
      b580HiddenGroupEnergy (1/2) c r N V≤C := by
  obtain ⟨K,hK,hbound⟩ := uniform_group_mark_bound
    (1/2:ℝ) vmin tmax (by norm_num) (by norm_num) hv
  have hK0 : 0≤K := by linarith
  refine ⟨K^2,by nlinarith,?_⟩
  intro c r N V ht hV
  have hVp : 0<V := hv.trans_le hV
  by_cases hc : c≤N
  · rw [b580_hidden_group_energy_exact (1/2) V c r N hc]
    have h1 : b575MarkedGroup (1/2) (c+r) N V≤K :=
      (le_abs_self _).trans (hbound (c+r) N V ht hV)
    have h2 : b575MarkedGroup (1/2) r (N-c) V≤K :=
      (le_abs_self _).trans (hbound r (N-c) V (by omega) hV)
    have h20 : 0≤b575MarkedGroup (1/2) r (N-c) V := by
      unfold b575MarkedGroup
      positivity
    calc
      _ ≤ K*K := mul_le_mul h1 h2 h20 hK0
      _ = _ := by ring
  · rw [b580_hidden_group_energy_zero_of_overfull (1/2) V c r N (by omega)]
    exact sq_nonneg K

/-- Exact all-group bound, with arbitrary distinct c_g and r_g. In the
original endpoint r_g is one base mark plus the opposite block's probes. -/
theorem b580_hidden_all_group_energy_uniform
    (vmin : ℝ) (tmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧
      ∀ {G : Type} [Fintype G] (c r N : G → ℕ) (V : G → ℝ),
      (∀ g,c g+r g≤tmax) → (∀ g,vmin≤V g) →
      (∏ g,b580HiddenGroupEnergy (1/2) (c g) (r g) (N g) (V g)) ≤
        C^(Fintype.card G) := by
  obtain ⟨C,hC,hbound⟩ := b580_hidden_group_energy_uniform vmin tmax hv
  refine ⟨C,hC,?_⟩
  intro G _ c r N V ht hV
  calc
    _ ≤ ∏ _g : G,C := by
      apply Finset.prod_le_prod₀
      · intro g _
        exact b580_hidden_group_energy_nonneg _ _ _ _ _
          (hv.trans_le (hV g)).le
      · intro g _
        exact hbound (c g) (r g) (N g) (V g) (ht g) (hV g)
    _ = _ := by simp
end Green64Analytic.CorrelationSquare

end

end

