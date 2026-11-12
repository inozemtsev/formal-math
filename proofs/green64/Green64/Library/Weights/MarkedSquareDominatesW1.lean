module

public import Green64.Library.Weights.Part044
public import Green64.Library.Analysis.Estimates.TrueCellPrimeFibre

@[expose] public section

/-!
# Weights / MarkedSquareDominatesW1

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## MarkedSquareDominatesW1 -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Literal positive distinct-count factor of the original marked weight. -/
def b575MarkedGroup (q : ℝ) (t N : ℕ) (V : ℝ) : ℝ :=
  q ^ ((N:ℤ)-(t:ℤ)) * (N.descFactorial t:ℝ) / V^t

private theorem b575_marked_group_nonneg
    (q V : ℝ) (t N : ℕ) (hq : 0<q) (hV : 0<V) :
    0 ≤ b575MarkedGroup q t N V := by
  dsimp [b575MarkedGroup]
  positivity


private theorem b575_marked_square_sqrt_identity
    (q V : ℝ) (t N : ℕ) (hq : 0≤q) (htN : t≤N) :
    (b575MarkedGroup q t N V)^2 =
      (b575MarkedGroup (Real.sqrt q) t N V)^2*q^(N-t) := by
  have hc : (N:ℤ)-(t:ℤ)=((N-t:ℕ):ℤ) := (Nat.cast_sub htN).symm
  have hs : (Real.sqrt q^(N-t))^2=q^(N-t) := by
    calc
      _ = (Real.sqrt q^2)^(N-t) := by
        rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ = _ := by rw [Real.sq_sqrt hq]
  simp only [b575MarkedGroup,hc,zpow_natCast,mul_pow,div_pow]
  rw [hs]
  ring

/-- The actual higher-mark factor is square dominated by the one-mark
factor, uniformly in the distinct count. This preserves zero factors. -/
theorem b575_original_marked_group_square_domination
    (vmin : ℝ) (tmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (t N : ℕ) (V : ℝ), 1 ≤ t → t ≤ tmax →
        vmin ≤ V → V ≤ 4 →
        (b575MarkedGroup (1/2) t N V)^2 ≤
          C*b575MarkedGroup (1/2) 1 N V := by
  have hq : 0 < Real.sqrt (1/2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hq1 : Real.sqrt (1/2:ℝ) < 1 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 1/2 by norm_num), Real.sqrt_nonneg (1/2:ℝ)]
  obtain ⟨K,hK,hbound⟩ := uniform_group_mark_bound
    (Real.sqrt (1/2:ℝ)) vmin tmax hq hq1 hv
  let C : ℝ := 4*(2:ℝ)^tmax*K^2
  have hpow : (1:ℝ) ≤ 2^tmax := one_le_pow₀ (by norm_num)
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (K-1)]
  refine ⟨C,hC,?_⟩
  intro t N V ht htmax hV hV4
  have hVp : 0<V := hv.trans_le hV
  by_cases hNt : N<t
  · have hf := Nat.descFactorial_eq_zero_iff_lt.mpr hNt
    simp only [b575MarkedGroup,hf,Nat.cast_zero,mul_zero,zero_div,zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (by linarith) (b575_marked_group_nonneg _ _ _ _ (by norm_num) hVp)
  have htN : t≤N := by omega
  have hN : 1≤N := ht.trans htN
  let a : ℕ := N-t
  have hcast : (N:ℤ)-(t:ℤ)=(a:ℤ) := by dsimp [a]; exact (Nat.cast_sub htN).symm
  have hcast1 : (N:ℤ)-(1:ℤ)=((N-1:ℕ):ℤ) := (Nat.cast_sub hN).symm
  have hsplit : N-1=a+(t-1) := by dsimp [a]; omega
  have hsquare : (b575MarkedGroup (1/2) t N V)^2 =
      (b575MarkedGroup (Real.sqrt (1/2)) t N V)^2 * (1/2:ℝ)^a := by
    exact b575_marked_square_sqrt_identity (1/2) V t N (by norm_num) htN
  have hb : b575MarkedGroup (Real.sqrt (1/2)) t N V ≤ K :=
    (le_abs_self _).trans (hbound t N V htmax hV)
  have hb0 := b575_marked_group_nonneg (Real.sqrt (1/2)) V t N hq hVp
  have hbsq : (b575MarkedGroup (Real.sqrt (1/2)) t N V)^2 ≤ K^2 :=
    (sq_le_sq₀ hb0 (by linarith)).mpr hb
  have hsmall : (1/2:ℝ)^tmax ≤ (1/2:ℝ)^(t-1) := by
    have hsum : (t-1)+(tmax-(t-1))=tmax := Nat.add_sub_of_le (by omega)
    have hp : (1/2:ℝ)^(tmax-(t-1)) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [←hsum,pow_add]
    exact mul_le_of_le_one_right (by positivity) hp
  have hNV : (1/4:ℝ) ≤ (N:ℝ)/V := by
    apply (le_div_iff₀ hVp).mpr
    have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hW1 : b575MarkedGroup (1/2) 1 N V =
      (1/2:ℝ)^a * (1/2:ℝ)^(t-1)*((N:ℝ)/V) := by
    unfold b575MarkedGroup
    norm_num only [Nat.cast_one,Nat.descFactorial_one,pow_one]
    rw [hcast1,zpow_natCast,hsplit,pow_add]
    ring
  have hlower : (1/2:ℝ)^a*(1/2:ℝ)^tmax/4 ≤ b575MarkedGroup (1/2) 1 N V := by
    rw [hW1]
    have hh := mul_le_mul hsmall hNV (by norm_num : (0:ℝ) ≤ 1/4) (by positivity : (0:ℝ) ≤ (1/2:ℝ)^(t-1))
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ (1/2:ℝ)^a)
    nlinarith only [hh']
  have hp_inv : (2:ℝ)^tmax*(1/2:ℝ)^tmax=1 := by
    rw [←mul_pow]; norm_num
  have hmass : (1/2:ℝ)^a ≤ (4*(2:ℝ)^tmax)*b575MarkedGroup (1/2) 1 N V := by
    have hh := mul_le_mul_of_nonneg_left hlower (by positivity : (0:ℝ) ≤ 4*(2:ℝ)^tmax)
    calc
      _ = (4*(2:ℝ)^tmax)*((1/2:ℝ)^a*(1/2:ℝ)^tmax/4) := by
        calc
          _ = (1/2:ℝ)^a*((2:ℝ)^tmax*(1/2:ℝ)^tmax) := by rw [hp_inv]; ring
          _ = _ := by ring
      _ ≤ _ := hh
  calc
    _ = (b575MarkedGroup (Real.sqrt (1/2)) t N V)^2*(1/2:ℝ)^a := hsquare
    _ ≤ K^2*(1/2:ℝ)^a := mul_le_mul_of_nonneg_right hbsq (by positivity)
    _ ≤ K^2*((4*(2:ℝ)^tmax)*b575MarkedGroup (1/2) 1 N V) :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ = _ := by dsimp [C]; ring

/-- All actual groups are retained; the constant grows only by one
fixed factor per group, and hence by a fixed power of L for the original family. -/
theorem b575_original_all_group_square_domination
    (vmin : ℝ) (tmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧
      ∀ {G : Type} [Fintype G] (t N : G → ℕ) (V : G → ℝ),
      (∀ g,1≤t g ∧ t g≤tmax) →
      (∀ g,vmin≤V g ∧ V g≤4) →
      (∏ g,b575MarkedGroup (1/2) (t g) (N g) (V g))^2 ≤
        C^(Fintype.card G)*∏ g,b575MarkedGroup (1/2) 1 (N g) (V g) := by
  obtain ⟨C,hC,hbound⟩ := b575_original_marked_group_square_domination vmin tmax hv
  refine ⟨C,hC,?_⟩
  intro G _ t N V ht hV
  rw [←Finset.prod_pow]
  calc
    _ ≤ ∏ g : G,C*b575MarkedGroup (1/2) 1 (N g) (V g) := by
      apply Finset.prod_le_prod₀
      · intro g _; exact sq_nonneg _
      · intro g _; exact hbound (t g) (N g) (V g) (ht g).1 (ht g).2 (hV g).1 (hV g).2
    _ = _ := by rw [Finset.prod_mul_distrib]; simp


/-- Literal original marked decorations, with the genuine group harmonic
masses, are square dominated by the SAME one-mark weight used by the
original P-gated native endpoint. No valuation count replaces distinct support. -/
theorem b575_actual_marked_decoration_square_le_original_W1
    (vmin : ℝ) (tmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (t : G → ℕ)
        (b : (∀ g, Fin (t g) → ℕ) → ℂ),
        (∀ g,1≤t g ∧ t g≤tmax) →
        (∀ g,vmin≤groupHarmonic (P g) ∧
          groupHarmonic (P g)≤4) →
        (∀ a,‖b a‖≤1) → ∀ n,
        ‖actualBigMarkDecoration P t (1/2)
          (fun g => groupHarmonic (P g)) b n‖^2 ≤
          C^(Fintype.card G)*
            Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight (1/2) 1 P n := by
  obtain ⟨C,hC,hbound⟩ := b575_original_all_group_square_domination vmin tmax hv
  refine ⟨C,hC,?_⟩
  intro G _ _ P t b ht hV hb n
  let V := fun g => groupHarmonic (P g)
  let N := fun g => smallPrimeCount (P g) n
  have hVp (g : G) : 0<V g := hv.trans_le (hV g).1
  have hp := sourceBigMarkDecoration_pointwise P t (1/2) V b n
    (by norm_num) hVp hb
  have hnon : 0 ≤ ∏ g,b575MarkedGroup (1/2) (t g) (N g) (V g) := by
    apply Finset.prod_nonneg
    intro g _
    exact b575_marked_group_nonneg _ _ _ _ (by norm_num) (hVp g)
  have hs : ‖actualBigMarkDecoration P t (1/2) V b n‖^2 ≤
      (∏ g,b575MarkedGroup (1/2) (t g) (N g) (V g))^2 := by
    apply (sq_le_sq₀ (norm_nonneg _) hnon).mpr
    exact hp
  have hdom := hbound t N V ht hV
  have hsingle : (∏ g,b575MarkedGroup (1/2) 1 (N g) (V g)) =
      Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight (1/2) 1 P n := by
    unfold Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight
    apply Finset.prod_congr rfl
    intro g _
    have hc : N g=Green64Analytic.SourceBlockSieve.shiftTwoGroupOmega (P g) n := rfl
    by_cases hzero : N g=0
    · simp [b575MarkedGroup,←hc,hzero]
    · have hN : 1≤N g := Nat.one_le_iff_ne_zero.mpr hzero
      have he : ((N g:ℤ)-(1:ℤ))=((N g-1:ℕ):ℤ) := (Nat.cast_sub hN).symm
      simp only [b575MarkedGroup,←hc,Nat.cast_one,he,zpow_natCast]
      rfl
  rw [hsingle] at hdom
  exact hs.trans hdom


/-- The full original W1 from the literal unsplit weight is exactly the
single-mark weight in the original native P-gated kernel. -/
theorem b575_original_W1_eq_native_single
    {G : Type} [Fintype G] (P : G → Finset ℕ) (n : ℕ) :
    sourceOriginalW1 P n=Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight (1/2) 1 P n := by
  unfold sourceOriginalW1 Green64Analytic.ShiftTwoTerminal.sourceMarkedWeight
  apply Finset.prod_congr rfl
  intro g _
  simp only [shiftTwoOriginalGroupFactor,Nat.descFactorial_one,pow_one]
  simp [groupHarmonic,one_div,mul_comm]

/-- Final actual higher-mark/W1 bridge for the EXISTING weighted Rankin
theorem, on the unchanged original distinct-list carrier and harmonic masses. -/
theorem b575_actual_marked_square_le_literal_original_W1
    (vmin : ℝ) (tmax : ℕ) (hv : 0<vmin) :
    ∃ C : ℝ, 1≤C ∧
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) (t : G → ℕ)
        (b : (∀ g, Fin (t g) → ℕ) → ℂ),
        (∀ g,1≤t g ∧ t g≤tmax) →
        (∀ g,vmin≤groupHarmonic (P g) ∧ groupHarmonic (P g)≤4) →
        (∀ a,‖b a‖≤1) → ∀ n,
        ‖actualBigMarkDecoration P t (1/2) (fun g => groupHarmonic (P g)) b n‖^2 ≤
          C^(Fintype.card G)*sourceOriginalW1 P n := by
  simpa only [b575_original_W1_eq_native_single] using
    b575_actual_marked_decoration_square_le_original_W1 vmin tmax hv
end Green64Analytic.CorrelationSquare

end

end

