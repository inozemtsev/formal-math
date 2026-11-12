module

public import Green64.Library.Analysis.Estimates.Part004
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Correlation.Part001
public import Mathlib
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Green64.Library.Weights.Part001
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Weights.Part011
public import Green64.Library.Sieve.Foundations.ArithmeticSieve
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Weights / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceLinearCollarPlancherel -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- Full real-line Plancherel for the actual finite linear collar.
L1, L2 and Fourier squared integrability are proved, not assumed. -/
theorem source_linear_collar_plancherel434
    (K : 𝓢(ℝ,ℂ)) (F : Finset ℕ) (a : ℕ → ℂ)
    (H : ℝ) (hH : 0 < H) :
    let Q : ℝ → ℂ := fun v => ∑ n ∈ F, a n * K (((n:ℝ)-v)/H)
    Integrable Q ∧ MemLp Q 2 volume ∧
    Integrable (fun s : ℝ => ‖(𝓕 Q) s‖^2) ∧
    (∫ s : ℝ, ‖(𝓕 Q) s‖^2) = ∫ v : ℝ, ‖Q v‖^2 := by
  obtain ⟨Q,hQ⟩ := source_linear_finite_schwartz_exists434 K F a H hH
  dsimp only
  rw [← hQ]
  refine ⟨Q.integrable, Q.memLp 2, ?_, ?_⟩
  · have hmem : MemLp (𝓕 (Q : ℝ → ℂ)) 2 volume := by
      simpa only [SchwartzMap.fourier_coe] using
        ((𝓕 Q : 𝓢(ℝ,ℂ)).memLp 2 (volume : Measure ℝ))
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  · simpa only [SchwartzMap.fourier_coe, hQ] using
      (SchwartzMap.integral_norm_sq_fourier Q)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralGroupLogBudget -/

section

namespace Green64Analytic.CorrelationSquare

/-- The uniform literal source weight K^(all groups + distinguished
small group) has FIXED log-power size when both other-small and
BIG group counts are ≤ C0 logL. No K may depend on L. -/
theorem source_literal_group_card_log_budget
    (K L C0 : ℝ) (hK : 1 ≤ K)
    (hL : 1 ≤ L) (hC0 : 0 ≤ C0)
    (nSmall nBig : ℕ)
    (hSmall : (nSmall:ℝ) ≤ C0*Real.log L)
    (hBig : (nBig:ℝ) ≤ C0*Real.log L) :
    K^(nSmall+nBig+1) ≤ K*L^(2*C0*Real.log K) := by
  have hKpos : 0 < K := by linarith
  have hLpos : 0 < L := by linarith
  have hCount : ((nSmall+nBig:ℕ):ℝ) ≤ (2*C0)*Real.log L := by
    push_cast
    linarith
  have hPower :
      K^(nSmall+nBig) ≤ K^((2*C0)*Real.log L) := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hK hCount)
  have hSwap : K^((2*C0)*Real.log L) =
      L^(2*C0*Real.log K) := by
    rw [Real.rpow_def_of_pos hKpos,Real.rpow_def_of_pos hLpos]
    congr 1
    ring
  calc
    K^(nSmall+nBig+1) = K*K^(nSmall+nBig) := by
      rw [pow_succ]
      ring
    _ ≤ K*K^((2*C0)*Real.log L) :=
      mul_le_mul_of_nonneg_left hPower (by linarith)
    _ = K*L^(2*C0*Real.log K) := by rw [hSwap]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceGrowingGroupBudget -/

section

namespace Green64Analytic.CorrelationSquare

/-- Original O(log L) small and big mark-group counts admit
a fixed integer log-power budget, uniform as L increases. -/
theorem source_literal_group_card_uniform_nat_log_budget
    (K C0 : ℝ) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) :
    ∃ g : ℕ, ∀ L : ℝ, max 3 K ≤ L →
      ∀ nSmall nBig : ℕ,
      (nSmall : ℝ) ≤ C0 * Real.log L →
      (nBig : ℝ) ≤ C0 * Real.log L →
      K^(nSmall+nBig+1) ≤ L^g := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2*C0*Real.log K)
  refine ⟨n+1, ?_⟩
  intro L hL nSmall nBig hSmall hBig
  have hL1 : 1 ≤ L :=
    (by linarith [le_max_left (3:ℝ) K])
  have hKL : K ≤ L := (le_max_right 3 K).trans hL
  have hPow :
      L^(2*C0*Real.log K) ≤ L^(n:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hn.le
  have hBase := source_literal_group_card_log_budget
    K L C0 hK hL1 hC0 nSmall nBig hSmall hBig
  calc
    K^(nSmall+nBig+1) ≤ K*L^(2*C0*Real.log K) := hBase
    _ ≤ K*L^n := by
      rw [← Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left hPow (by linarith)
    _ ≤ L*L^n := mul_le_mul_of_nonneg_right hKL (by positivity)
    _ = L^(n+1) := by rw [pow_succ]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLogPhaseDerivatives -/

section

/-! Exact real logarithmic phase derivatives used by the original
`pre:derivatives` estimate, with source-real (not integer) frequencies. -/

namespace Green64Analytic.CorrelationMellin

noncomputable def sourceLogPhase (Δ x : ℝ) : ℝ :=
  (Δ / (2 * Real.pi)) * Real.log x

theorem sourceLogPhase_hasDerivAt (Δ x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (sourceLogPhase Δ)
      ((Δ / (2 * Real.pi)) * x⁻¹) x := by
  change HasDerivAt (fun y => (Δ / (2 * Real.pi)) * Real.log y)
    ((Δ / (2 * Real.pi)) * x⁻¹) x
  exact (Real.hasDerivAt_log hx).const_mul (Δ / (2 * Real.pi))

theorem sourceLogPhase_deriv (Δ x : ℝ) (hx : x ≠ 0) :
    deriv (sourceLogPhase Δ) x = (Δ / (2 * Real.pi)) * x⁻¹ :=
  (sourceLogPhase_hasDerivAt Δ x hx).deriv

theorem sourceLogPhase_deriv_hasDerivAt (Δ x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (Δ / (2 * Real.pi)) * y⁻¹)
      ((Δ / (2 * Real.pi)) * (-(x^2)⁻¹)) x := by
  exact (hasDerivAt_inv hx).const_mul (Δ / (2 * Real.pi))

/-- On the full consecutive block [U,4U], the first derivative
is of size Δ/U, uniformly for positive real Δ. -/
theorem sourceLogPhase_first_window (Δ U x : ℝ)
    (hΔ : 0 ≤ Δ) (hU : 0 < U) (hlo : U ≤ x) (hhi : x ≤ 4 * U) :
    (Δ / (2 * Real.pi)) * (4 * U)⁻¹ ≤ deriv (sourceLogPhase Δ) x ∧
    deriv (sourceLogPhase Δ) x ≤ (Δ / (2 * Real.pi)) * U⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le hU hlo
  rw [sourceLogPhase_deriv Δ x (ne_of_gt hx)]
  have hc : 0 ≤ Δ / (2 * Real.pi) := by positivity
  exact ⟨mul_le_mul_of_nonneg_left (inv_anti₀ hx hhi) hc,
    mul_le_mul_of_nonneg_left (inv_anti₀ hU hlo) hc⟩

/-- The second derivative's exact model is Δ/(2π x²).
This bounds its magnitude throughout the entire [U,4U] block. -/
theorem sourceLogPhase_second_window (Δ U x : ℝ)
    (hΔ : 0 ≤ Δ) (hU : 0 < U) (hlo : U ≤ x) (hhi : x ≤ 4 * U) :
    (Δ / (2 * Real.pi)) * ((4 * U)⁻¹)^2 ≤
      (Δ / (2 * Real.pi)) * (x⁻¹)^2 ∧
    (Δ / (2 * Real.pi)) * (x⁻¹)^2 ≤
      (Δ / (2 * Real.pi)) * (U⁻¹)^2 := by
  have hx : 0 < x := lt_of_lt_of_le hU hlo
  have hc : 0 ≤ Δ / (2 * Real.pi) := by positivity
  have hleft : (4 * U)⁻¹ ≤ x⁻¹ := inv_anti₀ hx hhi
  have hright : x⁻¹ ≤ U⁻¹ := inv_anti₀ hU hlo
  have hleftSq : ((4 * U)⁻¹)^2 ≤ (x⁻¹)^2 := by gcongr
  have hrightSq : (x⁻¹)^2 ≤ (U⁻¹)^2 := by gcongr
  exact ⟨mul_le_mul_of_nonneg_left hleftSq hc,
    mul_le_mul_of_nonneg_left hrightSq hc⟩

/-- Monotonicity hypothesis of the complete-block first-derivative
exponential-sum test, for positive real frequency differences. -/
theorem sourceLogPhase_deriv_antitone_positive
    (δ x y : ℝ) (hδ : 0 ≤ δ) (hx : 0 < x)
    (hxy : x ≤ y) :
    deriv (sourceLogPhase δ) y ≤ deriv (sourceLogPhase δ) x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [sourceLogPhase_deriv δ x (ne_of_gt hx),
    sourceLogPhase_deriv δ y (ne_of_gt hy)]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hx hxy) (by positivity)

/-- Exact integer avoidance in the small-frequency regime:
for 0<δ<=U the derivative remains strictly between integers 0 and 1,
with quantitative λ=δ/(8πU). -/
theorem sourceLogPhase_deriv_integer_avoid_positive
    (δ U x : ℝ) (hδ : 0 < δ) (hU : 0 < U)
    (hδU : δ ≤ U) (hlo : U ≤ x) (hhi : x ≤ 4*U) :
    0 < δ/(8*Real.pi*U) ∧ δ/(8*Real.pi*U) ≤ 1/2 ∧
    δ/(8*Real.pi*U) ≤ deriv (sourceLogPhase δ) x ∧
    deriv (sourceLogPhase δ) x ≤ 1-δ/(8*Real.pi*U) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden : 0 < 8*Real.pi*U := by positivity
  have hwindow := sourceLogPhase_first_window δ U x hδ.le hU hlo hhi
  have hEqLow : (δ/(2*Real.pi)) * (4*U)⁻¹ =
      δ/(8*Real.pi*U) := by ring
  have hEqUp : (δ/(2*Real.pi)) * U⁻¹ =
      δ/(2*Real.pi*U) := by ring
  have hδbound : 5*δ ≤ 8*Real.pi*U := by
    calc
      _ ≤ 5*U := mul_le_mul_of_nonneg_left hδU (by norm_num)
      _ ≤ 8*Real.pi*U := by
        have hpi3 : 3 < Real.pi := Real.pi_gt_three
        nlinarith
  have hEps5 : 5*(δ/(8*Real.pi*U)) ≤ 1 := by
    have hEq : 5*(δ/(8*Real.pi*U)) = (5*δ)/(8*Real.pi*U) := by ring
    rw [hEq]
    exact (div_le_iff₀ hden).mpr (by simpa only [one_mul] using hδbound)
  have hEpshalf : δ/(8*Real.pi*U) ≤ 1/2 := by linarith
  have hEpsupper : δ/(2*Real.pi*U) ≤ 1-δ/(8*Real.pi*U) := by
    have heq : δ/(2*Real.pi*U) = 4*(δ/(8*Real.pi*U)) := by ring
    rw [heq]
    linarith
  change 0 < δ/(8*Real.pi*U) ∧
    δ/(8*Real.pi*U) ≤ 1/2 ∧
    δ/(8*Real.pi*U) ≤ deriv (sourceLogPhase δ) x ∧
    deriv (sourceLogPhase δ) x ≤ 1-δ/(8*Real.pi*U)
  exact ⟨div_pos hδ hden,hEpshalf,hEqLow ▸ hwindow.1,
    hwindow.2.trans (hEqUp ▸ hEpsupper)⟩

end Green64Analytic.CorrelationMellin

end

/-! ## SourceLogWindowCutoff -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- A genuine fixed smooth compact log cutoff equal to one on the
entire original physical interval; depends only on the fixed A. -/
theorem source_log_window_cutoff_exists434 (A : ℝ) (hA : 1 ≤ A) :
    ∃ (chi : 𝓢(ℝ,ℂ)) (B : ℝ), 0 < B ∧
      tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B ∧
      ∀ Y v : ℝ, 0 < Y → v ∈ Set.Icc (Y/(2*A)) (2*A*Y) →
        chi (Real.log (v/Y)) = 1 := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨2*A+1,2*A+2,by linarith,by linarith⟩
  let chi : 𝓢(ℝ,ℂ) :=
    (b.hasCompactSupport.comp_left (g := fun x : ℝ => (x:ℂ)) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  refine ⟨chi,2*A+2,by linarith,?_,?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro u hu
    have hb : b u ≠ 0 := by
      intro h
      apply hu
      change (b u:ℂ) = 0
      exact_mod_cast h
    have hm : u ∈ Metric.ball (0:ℝ) b.rOut := by
      rw [← b.support_eq]
      exact hb
    have huB : |u| < 2*A+2 := by
      simpa [Metric.mem_ball,Real.dist_eq,b] using hm
    exact abs_le.mp huB.le
  · intro Y v hY hvV
    have hAp : 0 < 2*A := by linarith
    have hv : 0 < v := (div_pos hY hAp).trans_le hvV.1
    have hLo : (2*A)⁻¹ ≤ v/Y := by
      apply (le_div_iff₀ hY).mpr
      simpa only [div_eq_mul_inv,mul_comm] using hvV.1
    have hHi : v/Y ≤ 2*A := (div_le_iff₀ hY).mpr hvV.2
    have hl := Real.log_le_log (inv_pos.mpr hAp) hLo
    have hu := Real.log_le_log (div_pos hv hY) hHi
    rw [Real.log_inv] at hl
    have hbound := Real.log_le_sub_one_of_pos hAp
    have hlog : |Real.log (v/Y)| ≤ 2*A+1 := by
      rw [abs_le]
      constructor <;> linarith
    have hb : b (Real.log (v/Y)) = 1 :=
      b.one_of_mem_closedBall (by
        simpa [Metric.mem_closedBall,Real.dist_eq,b] using hlog)
    change (b (Real.log (v/Y)):ℂ) = 1
    exact_mod_cast hb
end Green64Analytic.CorrelationSquare

end

/-! ## SourceMinorDenominatorBudget -/

section

namespace Green64SourceC6

/-- Explicit four-term saving behind the source's large-denominator
minor-arc claim. B is the desired log saving, A controls log(2r);
the rational approximation bound r≤U1U2/L^(A+B) keeps the final
term small. No generic "minor arc saving" premise occurs. -/
theorem source_large_denominator_four_term_save
    (L A B U1 U2 r : ℝ)
    (hL : 1 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hU1 : L^(A+B) ≤ U1)
    (hU2 : L^B ≤ U2)
    (hrlo : L^B ≤ r)
    (hrhi : r ≤ U1*U2/L^(A+B))
    (hlog0 : 0 ≤ Real.log (2*r))
    (hlog : Real.log (2*r) ≤ L^A) :
    1/U2+1/r+Real.log (2*r)/U1+
       r*Real.log (2*r)/(U1*U2) ≤ 4/(L^B) := by
  have hLp : 0 < L := by linarith
  let X : ℝ := L^A
  let Z : ℝ := L^B
  let W : ℝ := L^(A+B)
  have hXp : 0 < X := Real.rpow_pos_of_pos hLp A
  have hZp : 0 < Z := Real.rpow_pos_of_pos hLp B
  have hWp : 0 < W := Real.rpow_pos_of_pos hLp (A+B)
  have hW : W = X*Z := by
    dsimp [W, X, Z]
    rw [Real.rpow_add hLp]
  have hU1p : 0 < U1 := by linarith [hWp]
  have hU2p : 0 < U2 := by linarith [hZp]
  have hrp : 0 < r := by linarith [hZp]
  have hUZ : 0 < U1*U2 := mul_pos hU1p hU2p
  have hU2save : 1/U2 ≤ 1/Z :=
    one_div_le_one_div_of_le hZp hU2
  have hrsave : 1/r ≤ 1/Z :=
    one_div_le_one_div_of_le hZp hrlo
  have hXZ : X/W = 1/Z := by
    rw [hW]
    field_simp
  have hlogsave : Real.log (2*r)/U1 ≤ 1/Z := by
    calc
      Real.log (2*r)/U1 ≤ X/U1 := by
        exact (div_le_div_iff_of_pos_right hU1p).mpr hlog
      _ ≤ X/W :=
        div_le_div_of_nonneg_left hXp.le hWp hU1
      _ = 1/Z := hXZ
  have hprod : r*Real.log (2*r) ≤ (U1*U2/W)*X := by
    have hp0 : 0 ≤ U1*U2/W := by positivity
    exact mul_le_mul hrhi hlog hlog0 hp0
  have hfrac : ((U1*U2/W)*X)/(U1*U2) = 1/Z := by
    rw [hW]
    field_simp
  have hlast : r*Real.log (2*r)/(U1*U2) ≤ 1/Z := by
    calc
      r*Real.log (2*r)/(U1*U2) ≤
        ((U1*U2/W)*X)/(U1*U2) :=
          div_le_div_of_nonneg_right hprod hUZ.le
      _ = 1/Z := hfrac
  have hfour := add_le_add (add_le_add (add_le_add hU2save hrsave) hlogsave) hlast
  calc
    1/U2+1/r+Real.log (2*r)/U1+
        r*Real.log (2*r)/(U1*U2) ≤
       1/Z+1/Z+1/Z+1/Z := hfour
    _ = 4/(L^B) := by dsimp [Z]; ring
end Green64SourceC6

end

/-! ## SourceMinorSavingRoot -/

section

namespace Green64SourceC6

/-- Once the four terms are ≤ 4 L^{-B}, the exact squared
C6 bound with prefactor L^{2C7} saves the stated power of L.
The constant 16 absorbs sqrt(200). -/
theorem source_minor_bracket_to_power_saving
    (s L C7 B q : ℝ)
    (hs : 0 ≤ s) (hL : 1 ≤ L) (hq : 0 ≤ q)
    (hSq : s^2 ≤ 50*L^(2*C7)*q)
    (hsmall : q ≤ 4/L^B) :
    s ≤ 16*L^(C7-B/2) := by
  have hLp : 0 < L := by linarith
  have hPosB : 0 < L^B := Real.rpow_pos_of_pos hLp B
  have hScale : s^2 ≤ 50*L^(2*C7)*(4/L^B) := by
    exact hSq.trans (mul_le_mul_of_nonneg_left hsmall
      (by positivity : 0 ≤ 50*L^(2*C7)))
  have hExponents : 50*L^(2*C7)*(4/L^B) =
      200*L^(2*C7-B) := by
    rw [Real.rpow_sub hLp]
    field_simp
    ring
  have hhalf : (L^(C7-B/2))^2 = L^(2*C7-B) := by
    calc
      (L^(C7-B/2))^2 = (L^(C7-B/2))^(2:ℝ) :=
        (Real.rpow_natCast (L^(C7-B/2)) 2).symm
      _ = L^((C7-B/2)*2) :=
        (Real.rpow_mul hLp.le (C7-B/2) (2:ℝ)).symm
      _ = L^(2*C7-B) := by congr 1; ring
  have hRight : 0 ≤ 16*L^(C7-B/2) := by positivity
  have hRightSq : (16*L^(C7-B/2))^2 =
      256*L^(2*C7-B) := by
    rw [show (16*L^(C7-B/2))^2 =
      256*(L^(C7-B/2))^2 by ring, hhalf]
  have hBound : 200*L^(2*C7-B) ≤256*L^(2*C7-B) := by
    have hh : 0 ≤ L^(2*C7-B) := (Real.rpow_pos_of_pos hLp _).le
    nlinarith
  have hScale' : s^2 ≤ 200*L^(2*C7-B) := by
    rw [← hExponents]
    exact hScale
  apply (sq_le_sq₀ hs hRight).mp
  rw [hRightSq]
  exact hScale'.trans hBound
end Green64SourceC6

end

/-! ## SourceMultiplierCauchy -/

section

open MeasureTheory Filter
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- Bounded complex comparison multipliers preserve integrability of the
actual conjugated endpoint product. No relation between endpoint signs. -/
theorem source_multiplier_product_integrable434
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g m : α → ℂ) (C : ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hm : AEStronglyMeasurable m μ) (hBound : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    Integrable (fun x => m x*star (f x)*g x) μ := by
  have hProd : Integrable (fun x => ‖f x‖*‖g x‖) μ := hf.norm.integrable_mul hg.norm
  apply (hProd.const_mul C).mono'
    ((hm.mul hf.aestronglyMeasurable.star).mul hg.aestronglyMeasurable)
  filter_upwards [hBound] with x hx
  simpa only [Pi.mul_apply,Pi.star_apply,norm_mul,norm_star,mul_assoc] using
    mul_le_mul_of_nonneg_right hx (mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)))

/-- The major/minor-arc Cauchy estimate applies to independent complex
endpoint sequences, hence never relies on a shared parity switch. -/
theorem source_multiplier_cauchy434
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g m : α → ℂ) (C : ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hC : 0 ≤ C)
    (hm : AEStronglyMeasurable m μ) (hBound : ∀ᵐ x ∂μ, ‖m x‖ ≤ C) :
    ‖∫ x, m x*star (f x)*g x ∂μ‖ ≤
      C*Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  have hInt := source_multiplier_product_integrable434 μ f g m C hf hg hm hBound
  have hProd : Integrable (fun x => ‖f x‖*‖g x‖) μ := hf.norm.integrable_mul hg.norm
  have hHolder : (∫ x, ‖f x‖*‖g x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
    simpa only [Real.rpow_two,Real.sqrt_eq_rpow] using
      integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (by simpa using hf) (by simpa using hg)
  calc
    _ ≤ ∫ x, ‖m x*star (f x)*g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, C*(‖f x‖*‖g x‖) ∂μ := by
      apply integral_mono_ae hInt.norm (hProd.const_mul C)
      filter_upwards [hBound] with x hx
      simp only [norm_mul,norm_star]
      nlinarith [mul_le_mul_of_nonneg_right hx (mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x)))]
    _ = C*(∫ x, ‖f x‖*‖g x‖ ∂μ) := integral_const_mul _ _
    _ ≤ C*(Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hHolder hC
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceComparisonMajorMinor -/

section

open MeasureTheory Filter
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 2200000

/-- Full comparison multiplier split. Only the first endpoint needs small
major-arc energy; the second needs its ordinary global L2 bound. -/
theorem source_comparison_major_minor434
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g m : α → ℂ)
    (major : Set α) (δ : ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hm : AEStronglyMeasurable m μ) (hMajor : MeasurableSet major)
    (hδ : 0 ≤ δ) (hBound : ∀ x, ‖m x‖ ≤ 1)
    (hMinor : ∀ x ∉ major, ‖m x‖ ≤ δ) :
    ‖∫ x, m x*star (f x)*g x ∂μ‖ ≤
      Real.sqrt (∫ x in major, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) +
      δ*Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
  have hInt := source_multiplier_product_integrable434 μ f g m 1 hf hg hm
    (Eventually.of_forall hBound)
  have hFM : MemLp f 2 (μ.restrict major) := hf.mono_measure Measure.restrict_le_self
  have hGM : MemLp g 2 (μ.restrict major) := hg.mono_measure Measure.restrict_le_self
  have hFm : MemLp f 2 (μ.restrict majorᶜ) := hf.mono_measure Measure.restrict_le_self
  have hGm : MemLp g 2 (μ.restrict majorᶜ) := hg.mono_measure Measure.restrict_le_self
  have hBoundM := source_multiplier_cauchy434 (μ.restrict major) f g m 1 hFM hGM
    (by norm_num) (hm.mono_measure Measure.restrict_le_self) (Eventually.of_forall hBound)
  have hBoundm := source_multiplier_cauchy434 (μ.restrict majorᶜ) f g m δ hFm hGm hδ
    (hm.mono_measure Measure.restrict_le_self)
    ((ae_restrict_mem hMajor.compl).mono (fun x hx => hMinor x hx))
  have hGmajor : (∫ x in major, ‖g x‖^2 ∂μ) ≤ ∫ x, ‖g x‖^2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x => sq_nonneg ‖g x‖)) hg.norm.integrable_sq
  have hGminor : (∫ x in majorᶜ, ‖g x‖^2 ∂μ) ≤ ∫ x, ‖g x‖^2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x => sq_nonneg ‖g x‖)) hg.norm.integrable_sq
  have hFminor : (∫ x in majorᶜ, ‖f x‖^2 ∂μ) ≤ ∫ x, ‖f x‖^2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x => sq_nonneg ‖f x‖)) hf.norm.integrable_sq
  have hMfinal : ‖∫ x in major, m x*star (f x)*g x ∂μ‖ ≤
      Real.sqrt (∫ x in major, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
    simp only [one_mul] at hBoundM
    exact hBoundM.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hGmajor) (Real.sqrt_nonneg _))
  have hmfinal : ‖∫ x in majorᶜ, m x*star (f x)*g x ∂μ‖ ≤
      δ*Real.sqrt (∫ x, ‖f x‖^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
    refine hBoundm.trans ?_
    gcongr
  rw [← integral_add_compl hMajor hInt]
  exact (norm_add_le _ _).trans (add_le_add hMfinal hmfinal)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceNatArcEnergy -/

section

open MeasureTheory
open scoped BigOperators

noncomputable def sourceNatFourierPoly
    (S : Finset ℕ) (F : ℕ → ℂ) : C(AddCircle (1:ℝ), ℂ) :=
  sourceCircleFourierPoly (S.image (fun n : ℕ => (n : ℤ)))
    (fun z : ℤ => F z.toNat)

/-- Parseval on an arbitrary set of circle frequencies, with actual
integer coefficient positions, including any irregular source
physical square-exception support. -/
theorem source_nat_fourier_arc_energy
    (S : Finset ℕ) (F : ℕ → ℂ)
    (A : Set (AddCircle (1:ℝ))) :
    (∫ x in A, ‖sourceNatFourierPoly S F x‖^2
      ∂AddCircle.haarAddCircle) ≤
        ∑ n ∈ S, ‖F n‖^2 := by
  have h := source_circle_arc_energy_le_coeff_l2
    (S.image (fun n : ℕ => (n : ℤ)))
    (fun z : ℤ => F z.toNat) A
  have hsum : (∑ z ∈ S.image (fun n : ℕ => (n : ℤ)),
      ‖F z.toNat‖^2) = ∑ n ∈ S, ‖F n‖^2 := by
    rw [Finset.sum_image]
    · simp only [Int.toNat_natCast]
    · intro n hn m hm hEq
      change (n:ℤ) = (m:ℤ) at hEq
      exact_mod_cast hEq
  simpa only [sourceNatFourierPoly, hsum] using h

end

/-! ## SourceNatFourierLiteral -/

section

open MeasureTheory
open scoped BigOperators

/-- The normalized AddCircle Fourier polynomial is literally the
original finite additive exponential sum on integer coefficient
positions. No synthetic L² surrogate is being Fourier transformed. -/
theorem source_nat_fourier_literal (S : Finset ℕ) (F : ℕ → ℂ)
    (x : AddCircle (1:ℝ)) :
    sourceNatFourierPoly S F x =
      ∑ n ∈ S, F n * fourier (T := 1) (n:ℤ) x := by
  classical
  simp only [sourceNatFourierPoly, sourceCircleFourierPoly,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_image]
  · simp only [Int.toNat_natCast]
  · intro n hn m hm hEq
    change (n:ℤ) = (m:ℤ) at hEq
    exact_mod_cast hEq

/-- The Fourier convention is e(theta*n)=exp(2*pi*i*theta*n),
not an unnormalized kernel with a missing factor 2*pi. -/
theorem source_nat_fourier_real_phase (S : Finset ℕ) (F : ℕ → ℂ)
    (theta : ℝ) :
    sourceNatFourierPoly S F (theta : AddCircle (1:ℝ)) =
      ∑ n ∈ S,
        F n * Complex.exp
          ((2:ℂ)*Real.pi*Complex.I*(n:ℂ)*(theta:ℂ)) := by
  rw [source_nat_fourier_literal]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fourier_coe_apply]
  congr 1
  congr 1
  push_cast
  ring

end

/-! ## SourceShiftedFourierIdentity -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 2500000

/-- Normalized Haar character orthogonality, with the library's exact 2*pi phase. -/
theorem source_integral_fourier_character434 (n : ℤ) :
    (∫ θ : AddCircle (1:ℝ), fourier n θ ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T:=1))) 0 n
  rw [MeasureTheory.ContinuousMap.inner_toLp] at h
  simpa only [fourier_zero,map_one,mul_one,eq_comm] using h

/-- For star(Uhat)*Vhat the shifted correlation uses the NEGATIVE multiplier.
No 2*pi is suppressed or converted into a Mellin frequency. -/
theorem source_shifted_character_product434 (n m k : ℤ) (θ : AddCircle (1:ℝ)) :
    fourier (-k) θ*star (fourier m θ)*fourier n θ = fourier (n-m-k) θ := by
  rw [Complex.star_def,←fourier_neg,←fourier_add,←fourier_add]
  congr 1
  ring

/-- Exact finite shifted correlation. Both endpoints and the signed integer
shift remain independent; missing coefficients need not be filled in. -/
theorem source_shifted_fourier_finite_identity434
    (S T : Finset ℤ) (a b : ℤ → ℂ) (k : ℤ) :
    (∫ θ : AddCircle (1:ℝ), fourier (-k) θ*
      star (sourceCircleFourierPoly S a θ)*sourceCircleFourierPoly T b θ
      ∂AddCircle.haarAddCircle) =
      ∑ m ∈ S, ∑ n ∈ T, if n = m+k then star (a m)*b n else 0 := by
  classical
  let atom := fun m n : ℤ => fun θ : AddCircle (1:ℝ) =>
    (star (a m)*b n)*fourier (n-m-k) θ
  have hInt (m n : ℤ) : Integrable (atom m n) AddCircle.haarAddCircle := by
    have hc : Continuous (atom m n) := continuous_const.mul (fourier (n-m-k)).continuous
    simpa [IntegrableOn] using hc.continuousOn.integrableOn_compact
      (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hPoint (θ : AddCircle (1:ℝ)) :
      fourier (-k) θ*star (sourceCircleFourierPoly S a θ)*sourceCircleFourierPoly T b θ =
      ∑ m ∈ S, ∑ n ∈ T, atom m n θ := by
    simp only [sourceCircleFourierPoly,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
      smul_eq_mul,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [atom]
    rw [←source_shifted_character_product434]
    ring
  have hAtom (m n : ℤ) : (∫ θ, atom m n θ ∂AddCircle.haarAddCircle) =
      if n = m+k then star (a m)*b n else 0 := by
    dsimp only [atom]
    rw [integral_const_mul,source_integral_fourier_character434]
    have heq : n-m-k = 0 ↔ n = m+k := by omega
    simp only [heq]
    split_ifs <;> simp
  calc
    _ = ∫ θ : AddCircle (1:ℝ), ∑ m ∈ S, ∑ n ∈ T, atom m n θ
        ∂AddCircle.haarAddCircle := integral_congr_ae (Filter.Eventually.of_forall hPoint)
    _ = ∑ m ∈ S, ∑ n ∈ T, ∫ θ, atom m n θ ∂AddCircle.haarAddCircle := by
      rw [integral_finset_sum S (fun m hm => integrable_finset_sum T (fun n hn => hInt m n))]
      apply Finset.sum_congr rfl
      intro m hm
      exact integral_finset_sum T (fun n hn => hInt m n)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_congr rfl (fun n hn => hAtom m n)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceFiniteComparisonFourier -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 3000000

/-- Literal finite comparison multiplier for star(Uhat)*Vhat.
The minus sign is forced by the positive Fourier convention. -/
noncomputable def sourceFiniteShiftMultiplier434 {ι : Type*}
    (J : Finset ι) (c : ι → ℂ) (shift : ι → ℤ) : C(AddCircle (1:ℝ),ℂ) :=
  ∑ j ∈ J, c j • fourier (-shift j)

theorem source_finite_shift_multiplier_bound434 {ι : Type*}
    (J : Finset ι) (c : ι → ℂ) (shift : ι → ℤ) (θ : AddCircle (1:ℝ)) :
    ‖sourceFiniteShiftMultiplier434 J c shift θ‖ ≤ ∑ j ∈ J, ‖c j‖ := by
  simp only [sourceFiniteShiftMultiplier434,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    smul_eq_mul]
  calc
    _ ≤ ∑ j ∈ J, ‖c j * fourier (-shift j) θ‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul,show ‖fourier (-shift j) θ‖ = 1 from Circle.norm_coe _,mul_one]

/-- Two independent finite probability laws and bounded tuple tests give
the required unit bound before any collapse onto product values. -/
theorem source_product_probability_coefficient_mass434 {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (u : ι → ℝ) (v : κ → ℝ)
    (b : ι → ℂ) (d : κ → ℂ)
    (hu : ∀ i ∈ S, 0 ≤ u i) (hv : ∀ j ∈ T, 0 ≤ v j)
    (hSumU : (∑ i ∈ S, u i) ≤ 1) (hSumV : (∑ j ∈ T, v j) ≤ 1)
    (hb : ∀ i ∈ S, ‖b i‖ ≤ 1) (hd : ∀ j ∈ T, ‖d j‖ ≤ 1) :
    (∑ ij ∈ S.product T, ‖((u ij.1*v ij.2:ℝ):ℂ)*b ij.1*d ij.2‖) ≤ 1 := by
  classical
  rw [Finset.product_eq_sprod, Finset.sum_product]
  have hTerm (i : ι) (hi : i ∈ S) (j : κ) (hj : j ∈ T) :
      ‖((u i*v j:ℝ):ℂ)*b i*d j‖ ≤ u i*v j := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hu i hi) (hv j hj))]
    have hbd : ‖b i‖*‖d j‖ ≤ (1:ℝ) := by
      nlinarith [norm_nonneg (b i),norm_nonneg (d j),hb i hi,hd j hj]
    nlinarith [mul_le_mul_of_nonneg_left hbd (mul_nonneg (hu i hi) (hv j hj))]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ T, u i*v j :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hTerm i hi j hj))
    _ = (∑ i ∈ S, u i)*(∑ j ∈ T, v j) := by rw [Finset.sum_mul]; simp only [Finset.mul_sum]
    _ ≤ 1 := by
      have hV0 : 0 ≤ ∑ j ∈ T, v j := Finset.sum_nonneg hv
      nlinarith [mul_le_mul_of_nonneg_right hSumU hV0]

/-- Exact comparison convolution, with arbitrary independent endpoint
coefficients and signed integer shifts. All finite sums are inside the proof. -/
theorem source_finite_comparison_fourier_identity434 {ι : Type*}
    (J : Finset ι) (c : ι → ℂ) (shift : ι → ℤ)
    (S T : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ θ : AddCircle (1:ℝ), sourceFiniteShiftMultiplier434 J c shift θ *
      star (sourceCircleFourierPoly S a θ)*sourceCircleFourierPoly T b θ
      ∂AddCircle.haarAddCircle) =
    ∑ j ∈ J, c j*(∑ m ∈ S, ∑ n ∈ T,
      if n = m+shift j then star (a m)*b n else 0) := by
  let f := sourceCircleFourierPoly S a
  let g := sourceCircleFourierPoly T b
  let atom := fun j θ => c j*(fourier (-shift j) θ*star (f θ)*g θ)
  have hInt (j : ι) : Integrable (atom j) AddCircle.haarAddCircle := by
    have hc : Continuous (atom j) :=
      continuous_const.mul (((fourier (-shift j)).continuous.mul f.continuous.star).mul g.continuous)
    simpa [IntegrableOn] using hc.continuousOn.integrableOn_compact
      (μ:=AddCircle.haarAddCircle) isCompact_univ
  have hPoint (θ : AddCircle (1:ℝ)) :
      sourceFiniteShiftMultiplier434 J c shift θ * star (f θ) * g θ = ∑ j ∈ J, atom j θ := by
    simp only [sourceFiniteShiftMultiplier434,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul,Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by dsimp [atom]; ring)
  calc
    _ = ∫ θ : AddCircle (1:ℝ), ∑ j ∈ J, atom j θ ∂AddCircle.haarAddCircle :=
      integral_congr_ae (Filter.Eventually.of_forall hPoint)
    _ = ∑ j ∈ J, ∫ θ : AddCircle (1:ℝ), atom j θ ∂AddCircle.haarAddCircle :=
      integral_finset_sum J (fun j _ => hInt j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [atom,f,g]
      rw [integral_const_mul,source_shifted_fourier_finite_identity434]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceNatShiftedFourier -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 3000000

/-- Original positive endpoint indices, with a genuinely signed shift.
The target support and positivity are not suppressed by a toNat cast. -/
theorem source_nat_shifted_fourier_identity434
    (S T : Finset ℕ) (a b : ℕ → ℂ) (k : ℤ)
    (hT : ∀ n ∈ T, 0 < n) :
    (∫ θ : AddCircle (1:ℝ), fourier (-k) θ *
      star (sourceNatFourierPoly S a θ)*sourceNatFourierPoly T b θ
      ∂AddCircle.haarAddCircle) =
    ∑ m ∈ S, if 0 < (m:ℤ)+k ∧ ((m:ℤ)+k).toNat ∈ T then
      star (a m)*b ((m:ℤ)+k).toNat else 0 := by
  classical
  have hBase := source_shifted_fourier_finite_identity434
    (S.image (fun n : ℕ => (n:ℤ))) (T.image (fun n : ℕ => (n:ℤ)))
    (fun n => a n.toNat) (fun n => b n.toNat) k
  change (∫ θ : AddCircle (1:ℝ), fourier (-k) θ *
    star (sourceNatFourierPoly S a θ)*sourceNatFourierPoly T b θ
    ∂AddCircle.haarAddCircle) = _ at hBase
  rw [hBase,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro m hm
    have hmem : (m:ℤ)+k ∈ T.image (fun n : ℕ => (n:ℤ)) ↔
        0 < (m:ℤ)+k ∧ ((m:ℤ)+k).toNat ∈ T := by
      constructor
      · intro hh
        obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp hh
        rw [←heq]
        exact ⟨Int.natCast_pos.mpr (hT n hn),by simpa using hn⟩
      · rintro ⟨hpos,hmem⟩
        exact Finset.mem_image.mpr ⟨_,hmem,Int.toNat_of_nonneg hpos.le⟩
    simpa only [Int.toNat_natCast,Finset.sum_ite_eq',hmem]
  · intro n hn m hm heq
    change (n:ℤ) = (m:ℤ) at heq
    exact_mod_cast heq
end Green64Analytic.CorrelationSquare

end

/-! ## SourceProductShiftFourier -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6
set_option maxHeartbeats 4000000

/-- Match the source integer exponential to the positive circle convention. -/
theorem source_fourier_integer_phase434 (n : ℤ) (theta : ℝ) :
    fourier n (theta:AddCircle (1:ℝ)) = integerPhase theta n := by
  rw [fourier_coe_apply]
  unfold integerPhase
  congr 1
  push_cast
  ring

noncomputable def sourceProductShiftCoefficient434
    (M N : ℕ) (u v : ℕ → ℝ) (b d : ℕ → ℂ) (ij : ℕ × ℕ) : ℂ :=
  ((u (M+ij.1)*v (N+ij.2):ℝ):ℂ)*b (M+ij.1)*d (N+ij.2)

def sourceProductShift434 (M N : ℕ) (k : ℤ) (ij : ℕ × ℕ) : ℤ :=
  k*((M+ij.1:ℕ):ℤ)*((N+ij.2:ℕ):ℤ)

noncomputable def sourceProductMultiplier434
    (M N P Q : ℕ) (u v : ℕ → ℝ) (b d : ℕ → ℂ) (k : ℤ) :
    C(AddCircle (1:ℝ),ℂ) :=
  sourceFiniteShiftMultiplier434 ((Finset.range P).product (Finset.range Q))
    (sourceProductShiftCoefficient434 M N u v b d) (sourceProductShift434 M N k)

/-- Exact native C6 product multiplier. The sign is -k*theta because the
pairing is star(Uhat)*Vhat. Neither 2pi nor a product scale is suppressed. -/
theorem source_product_multiplier_integer434
    (M N P Q : ℕ) (u v : ℕ → ℝ) (b d : ℕ → ℂ) (k : ℤ) (theta : ℝ) :
    sourceProductMultiplier434 M N P Q u v b d k (theta:AddCircle (1:ℝ)) =
    ∑ i ∈ Finset.range P, ((u (M+i):ℝ):ℂ)*b (M+i)*
      (∑ j ∈ Finset.range Q, ((v (N+j):ℝ):ℂ)*d (N+j)*
        integerPhase ((-(k:ℝ)*theta)*((N+j:ℕ):ℝ)) ((M+i:ℕ):ℤ)) := by
  simp only [sourceProductMultiplier434,sourceFiniteShiftMultiplier434,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    Finset.product_eq_sprod,Finset.sum_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hPhase : fourier (-(sourceProductShift434 M N k (i,j)))
      (theta:AddCircle (1:ℝ)) =
      integerPhase ((-(k:ℝ)*theta)*((N+j:ℕ):ℝ)) ((M+i:ℕ):ℤ) := by
    rw [source_fourier_integer_phase434]
    unfold integerPhase sourceProductShift434
    congr 1
    push_cast
    ring
  rw [hPhase]
  dsimp only [sourceProductShiftCoefficient434]
  push_cast
  ring

/-- No coefficient growth is introduced by the rectangular product collapse. -/
theorem source_product_shift_coefficient_mass434
    (M N P Q : ℕ) (u v : ℕ → ℝ) (b d : ℕ → ℂ)
    (hu : ∀ i ∈ Finset.range P, 0 ≤ u (M+i))
    (hv : ∀ j ∈ Finset.range Q, 0 ≤ v (N+j))
    (hSumU : (∑ i ∈ Finset.range P, u (M+i)) ≤ 1)
    (hSumV : (∑ j ∈ Finset.range Q, v (N+j)) ≤ 1)
    (hb : ∀ i ∈ Finset.range P, ‖b (M+i)‖ ≤ 1)
    (hd : ∀ j ∈ Finset.range Q, ‖d (N+j)‖ ≤ 1) :
    (∑ ij ∈ (Finset.range P).product (Finset.range Q),
      ‖sourceProductShiftCoefficient434 M N u v b d ij‖) ≤ 1 := by
  exact source_product_probability_coefficient_mass434
    (Finset.range P) (Finset.range Q) (fun i => u (M+i)) (fun j => v (N+j))
    (fun i => b (M+i)) (fun j => d (N+j)) hu hv hSumU hSumV hb hd
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalLinearFourierLiteral -/

section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- The Fourier image of the actual linear physical collar is
EXACTLY the true original source nat Fourier polynomial evaluated at
the additive beta on AddCircle, with positive exponent +2*pi*i*n*beta.
The Fourier variable on the real physical v-line is NEGATIVE beta.
This simultaneously checks the H Jacobian and sign convention. -/
theorem source_linear_collar_fourier_literal434
    (K : ℝ → ℂ) (hK : Integrable K) (hKcont : Continuous K)
    (F : Finset ℕ) (a : ℕ → ℂ)
    (H : ℝ) (hH : 0 < H) (beta : ℝ) :
    (𝓕 (fun v : ℝ =>
        ∑ n ∈ F, a n * K (((n:ℝ)-v)/H))) (-beta) =
      ((H:ℂ) * (𝓕 K) (H*beta)) *
        sourceNatFourierPoly F a (beta : AddCircle (1:ℝ)) := by
  classical
  have hFT := source_linear_collar_finite_fourier434
    K hK hKcont F a H hH (-beta)
  have hfreq : -H*(-beta) = H*beta := by ring
  rw [hfreq] at hFT
  have hphase :
      (∑ n ∈ F, a n *
          Complex.exp ((((-2*Real.pi*((n:ℝ)*(-beta)):ℝ):ℂ)*Complex.I))) =
        sourceNatFourierPoly F a (beta : AddCircle (1:ℝ)) := by
    rw [source_nat_fourier_real_phase]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    congr 1
    push_cast
    ring
  rw [hphase] at hFT
  exact hFT
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalAdditiveFourierBand -/

section

open MeasureTheory FourierTransform
open scoped FourierTransform BigOperators RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 750000

/-- The true source additive polynomial is dominated POINTWISE on the
whole original beta arc by the real-line Fourier transform of the
ordinary linear physical collar, whenever the auxiliary kernel has a
positive Fourier lower bound on [-1,1]. This is a condition on the
chosen bump K, NEVER a hypothesis on source low/high energy. -/
theorem source_linear_collar_additive_beta_band434
    (K : ℝ → ℂ) (hK : Integrable K) (hKcont : Continuous K)
    (F : Finset ℕ) (a : ℕ → ℂ) (H c : ℝ)
    (hH : 0 < H) (hc : 0 < c)
    (hFourierLower : ∀ beta : ℝ, |beta| ≤ 1/H →
      c ≤ ‖(𝓕 K) (H*beta)‖)
    (beta : ℝ) (hbeta : |beta| ≤ 1/H) :
    (H^2*c^2) *
      ‖sourceNatFourierPoly F a (beta:AddCircle (1:ℝ))‖^2 ≤
    ‖(𝓕 (fun v : ℝ =>
      ∑ n ∈ F, a n*K (((n:ℝ)-v)/H))) (-beta)‖^2 := by
  let P : ℂ := sourceNatFourierPoly F a (beta:AddCircle (1:ℝ))
  have hKband : c ≤ ‖(𝓕 K) (H*beta)‖ :=
    hFourierLower beta hbeta
  have hSq : c^2 ≤ ‖(𝓕 K) (H*beta)‖^2 :=
    pow_le_pow_left₀ hc.le hKband 2
  have hTerm : (H^2*c^2)*‖P‖^2 ≤
      (H^2*‖(𝓕 K) (H*beta)‖^2)*‖P‖^2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSq (sq_nonneg H))
      (sq_nonneg _)
  have hFT := source_linear_collar_fourier_literal434
    K hK hKcont F a H hH beta
  rw [hFT]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  simpa only [P, mul_pow] using hTerm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLinearCollarArcEnergy -/

section

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- Genuine additive arc energy from the linear physical collar.
The proof supplies all integrability and uses full-line Plancherel. -/
theorem source_linear_collar_arc_energy434
    (K : 𝓢(ℝ,ℂ)) (F : Finset ℕ) (a : ℕ → ℂ)
    (H c : ℝ) (hH : 0 < H) (hc : 0 < c)
    (hLower : ∀ t : ℝ, |t| ≤ 1 → c ≤ ‖(𝓕 (K : ℝ → ℂ)) t‖) :
    (H^2*c^2) * (∫ beta in Set.Icc (-(1/H)) (1/H),
      ‖sourceNatFourierPoly F a (beta : AddCircle (1:ℝ))‖^2) ≤
    ∫ v : ℝ, ‖∑ n ∈ F, a n*K (((n:ℝ)-v)/H)‖^2 := by
  let Q : ℝ → ℂ := fun v => ∑ n ∈ F, a n*K (((n:ℝ)-v)/H)
  have hReg := source_linear_collar_plancherel434 K F a H hH
  have hE : Integrable (fun s : ℝ => ‖(𝓕 Q) (-s)‖^2) :=
    hReg.2.2.1.comp_neg
  have hP : Continuous (fun beta : ℝ =>
      ‖sourceNatFourierPoly F a (beta : AddCircle (1:ℝ))‖^2) := by
    simp_rw [source_nat_fourier_real_phase]
    fun_prop
  have hBand (beta : ℝ) (hb : |beta| ≤ 1/H) :
      c ≤ ‖(𝓕 (K : ℝ → ℂ)) (H*beta)‖ := by
    apply hLower
    rw [abs_mul, abs_of_pos hH]
    have hInv : H*(1/H) = 1 := by field_simp
    nlinarith [(mul_le_mul_of_nonneg_left hb hH.le)]
  calc
    _ = ∫ beta in Set.Icc (-(1/H)) (1/H),
        (H^2*c^2)*‖sourceNatFourierPoly F a
          (beta : AddCircle (1:ℝ))‖^2 := (integral_const_mul _ _).symm
    _ ≤ ∫ beta in Set.Icc (-(1/H)) (1/H), ‖(𝓕 Q) (-beta)‖^2 := by
      apply setIntegral_mono_on
        (hP.integrableOn_Icc.const_mul (H^2*c^2)) hE.integrableOn measurableSet_Icc
      intro beta hb
      exact source_linear_collar_additive_beta_band434 K K.integrable K.continuous
        F a H c hH hc hBand beta (abs_le.mpr hb)
    _ ≤ ∫ beta : ℝ, ‖(𝓕 Q) (-beta)‖^2 :=
      setIntegral_le_integral hE (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    _ = ∫ s : ℝ, ‖(𝓕 Q) s‖^2 := by
      simpa using (integral_neg_eq_self (fun s : ℝ => ‖(𝓕 Q) s‖^2)
        (volume : Measure ℝ))
    _ = _ := hReg.2.2.2
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLinearToLogArc -/

section

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 2000000

/-- Actual additive band energy bounded by the logarithmic collar and
its already proved replacement error. No arithmetic energy premise. -/
theorem source_linear_to_log_arc434
    (K : 𝓢(ℝ,ℂ)) (F : Finset ℕ) (a : ℕ → ℂ)
    (H Y A δ M c : ℝ) (hH : 1 ≤ H) (hY : 0 < Y)
    (hA : 1 ≤ A) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hc : 0 < c) (hHcap : H ≤ Y/(8*A))
    (hF : ∀ n ∈ F, 0 < n)
    (hCoef : ∀ n ∈ F, a n ≠ 0 → Y/A ≤ (n:ℝ) ∧ (n:ℝ) ≤ A*Y)
    (hSupport : ∀ z, K z ≠ 0 → |z| ≤ δ)
    (hLip : ∀ z z', ‖K z-K z'‖ ≤ M*|z-z'|)
    (hLower : ∀ t : ℝ, |t| ≤ 1 → c ≤ ‖(𝓕 (K : ℝ → ℂ)) t‖) :
    c^2 * (∫ beta in Set.Icc (-(1/H)) (1/H),
      ‖sourceNatFourierPoly F a (beta : AddCircle (1:ℝ))‖^2) ≤
    2*(H^2)⁻¹ * (∫ v in Set.Icc (Y/(2*A)) (2*A*Y),
      ‖∑ n ∈ F, a n*K (v*Real.log ((n:ℝ)/v)/H)‖^2) +
    2*(4*δ*(4*δ+1)*(16*A*δ^2*M)^2*(H/Y)^2 *
      ∑ n ∈ F, ‖a n‖^2) := by
  classical
  have hHp : 0 < H := by linarith
  have hAp : 0 < A := by linarith
  let V := Set.Icc (Y/(2*A)) (2*A*Y)
  let Q : ℝ → ℂ := fun v => ∑ n ∈ F, a n*K (((n:ℝ)-v)/H)
  let R : ℝ → ℂ := fun v => ∑ n ∈ F, a n*K (v*Real.log ((n:ℝ)/v)/H)
  let E : ℝ → ℂ := fun v => ∑ n ∈ F, a n*sourceCollarKernelDifference434 K H n v
  have hQ : Continuous Q := by dsimp [Q]; fun_prop
  have hR : ContinuousOn R V := by
    apply continuousOn_finset_sum
    intro n hn v hvV
    have hv : 0 < v := (div_pos hY (by positivity)).trans_le hvV.1
    have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr (hF n hn)
    have hr : ContinuousAt (fun v : ℝ => (n:ℝ)/v) v :=
      continuousAt_const.div continuousAt_id hv.ne'
    have hl := (Real.continuousAt_log (div_pos hnR hv).ne').comp hr
    exact (continuousAt_const.mul (K.continuous.continuousAt.comp
      ((continuousAt_id.mul hl).div_const H))).continuousWithinAt
  have hEeq : E = fun v => Q v-R v := by
    funext v
    simp only [E,Q,R,sourceCollarKernelDifference434,mul_sub,Finset.sum_sub_distrib]
  have hE : ContinuousOn E V := by rw [hEeq]; exact hQ.continuousOn.sub hR
  have hQI : IntegrableOn (fun v => ‖Q v‖^2) V := hQ.norm.pow 2 |>.integrableOn_Icc
  have hRI : IntegrableOn (fun v => ‖R v‖^2) V := hR.norm.pow 2 |>.integrableOn_Icc
  have hEI : IntegrableOn (fun v => ‖E v‖^2) V := hE.norm.pow 2 |>.integrableOn_Icc
  have hQzero (v : ℝ) (hv : v ∉ V) : Q v = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    by_cases ha : a n = 0
    · simp [ha]
    · have hb := hCoef n hn ha
      rw [source_linear_collar_true_window_support434 K (n:ℝ) v Y A H δ
        hA hY hHp hHcap hδ hδ1 hSupport hb.1 hb.2 hv, mul_zero]
  have hRestrict : (∫ v : ℝ, ‖Q v‖^2) = ∫ v in V, ‖Q v‖^2 := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v ∈ V
    · change v ∈ Set.Icc (Y/(2*A)) (2*A*Y) at hv
      simp only [Set.indicator_of_mem hv]
    · have hz := hQzero v hv
      change v ∉ Set.Icc (Y/(2*A)) (2*A*Y) at hv
      simp only [Set.indicator_of_notMem hv,hz,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  have hTriangle : (∫ v in V, ‖Q v‖^2) ≤
      2*(∫ v in V, ‖R v‖^2)+2*(∫ v in V, ‖E v‖^2) := by
    calc
      _ ≤ ∫ v in V, 2*‖R v‖^2+2*‖E v‖^2 := by
        apply setIntegral_mono_on hQI ((hRI.const_mul 2).add (hEI.const_mul 2))
          measurableSet_Icc
        intro v hv
        change ‖Q v‖^2 ≤ 2*‖R v‖^2+2*‖E v‖^2
        have he : Q v = R v + E v := by rw [hEeq]; simp
        have ht : ‖Q v‖ ≤ ‖R v‖+‖E v‖ := by rw [he]; exact norm_add_le _ _
        have ht2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
        nlinarith [sq_nonneg (‖R v‖-‖E v‖)]
      _ = _ := by rw [integral_add (hRI.const_mul 2) (hEI.const_mul 2),
        integral_const_mul,integral_const_mul]
  have hArc := source_linear_collar_arc_energy434 K F a H c hHp hc hLower
  have hRaw : (H^2*c^2)*(∫ beta in Set.Icc (-(1/H)) (1/H),
      ‖sourceNatFourierPoly F a (beta:AddCircle (1:ℝ))‖^2) ≤
      2*(∫ v in V, ‖R v‖^2)+2*(∫ v in V, ‖E v‖^2) :=
    (hArc.trans_eq hRestrict).trans hTriangle
  have hErr := source_physical_collar_replacement_error434
    F a K M δ H Y A hF K.continuous hM hδ hδ1 hH hY hAp hHcap hSupport hLip
  have hNorm := mul_le_mul_of_nonneg_left hRaw (by positivity : 0 ≤ (H^2)⁻¹)
  have hCancel : (H^2)⁻¹*(H^2*c^2) = c^2 := by field_simp
  rw [← mul_assoc,hCancel,mul_add] at hNorm
  calc
    _ ≤ (H^2)⁻¹*(2*(∫ v in V, ‖R v‖^2)) +
          (H^2)⁻¹*(2*(∫ v in V, ‖E v‖^2)) := hNorm
    _ = 2*(H^2)⁻¹*(∫ v in V, ‖R v‖^2) +
          2*((H^2)⁻¹*(∫ v in V, ‖E v‖^2)) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hErr (by norm_num : (0:ℝ) ≤ 2))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceNativeD61AlphaDefinitions -/

section

open Filter Topology
open scoped BigOperators Classical
set_option maxHeartbeats 0
set_option autoImplicit false

namespace Green64Analytic.SourceBlockSieve

noncomputable def sourceD19RoughTest (y : ℝ) (m : ℕ) : ℝ :=
  if 2 ≤ m ∧ y < (m.minFac:ℝ) then 1 else 0

noncomputable def sourceD36OriginalCofactorMask
    (b η δ L : ℝ) (f : ℕ → ℝ) (m : ℕ) : ℂ :=
  if Real.exp ((1-η)*L)≤(m:ℝ) ∧
      (m:ℝ)≤Real.exp ((1-b+δ)*L) then (f m:ℂ) else 0

noncomputable def sourceD36DyadicInterval (j : ℕ) : Finset ℕ :=
  Finset.Icc (2^j) (2^(j+1)-1)

noncomputable def sourceD34CoupledCutoff (h : ℕ) : ℝ :=
  1/(100*((h:ℝ)+1))

theorem sourceD34_coupled_cutoff_valid (h : ℕ) (hh : 2≤h) :
    0 < sourceD34CoupledCutoff h ∧
    sourceD34CoupledCutoff h ≤ 1/100 ∧
    sourceD34CoupledCutoff h < 1/2 ∧
    sourceD34CoupledCutoff h*(4*(h:ℝ)+2) ≤ 1/4 := by
  have hreal : 0≤(h:ℝ) := Nat.cast_nonneg _
  have hlow : (2:ℝ)≤(h:ℝ) := by exact_mod_cast hh
  have hden : 0<100*((h:ℝ)+1) := by positivity
  have hposit : 0<sourceD34CoupledCutoff h := by
    unfold sourceD34CoupledCutoff
    positivity
  have hsmall : sourceD34CoupledCutoff h ≤ 1/100 := by
    unfold sourceD34CoupledCutoff
    apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<100)).mpr
    nlinarith
  have hlevel : sourceD34CoupledCutoff h*(4*(h:ℝ)+2) ≤ 1/4 := by
    unfold sourceD34CoupledCutoff
    calc
      (1/(100*((h:ℝ)+1)))*(4*(h:ℝ)+2) =
        (4*(h:ℝ)+2)/(100*((h:ℝ)+1)) := by ring
      _ ≤ 1/4 := (div_le_iff₀ hden).mpr (by nlinarith [hreal])
  exact ⟨hposit,hsmall,hsmall.trans_lt (by norm_num),hlevel⟩

end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.ShiftTwoTerminal

noncomputable def roughCutoff (x : ℝ) : ℝ := Real.exp (Real.sqrt (Real.log x))

def rough (W : ℝ) (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → W < (p : ℝ)

noncomputable def restrictSequence (K : Finset ℕ) (alpha : ℕ → ℂ) : ℕ → ℂ :=
  fun m => if m ∈ K then alpha m else 0

end Green64Analytic.ShiftTwoTerminal

end

/-! ## SourceD20CellProxy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- The actual rough integer test, including repeated prime factors. -/
def sourceD20Rough (y : ℝ) (n : ℕ) : Prop := 2 ≤ n ∧ y < (n.minFac:ℝ)
noncomputable def sourceD20CellRatio (C : Finset ℕ) (W y : ℝ) : ℝ :=
  ((C.filter (sourceD20Rough y)).card:ℝ) /
    ((C.filter (sourceD20Rough W)).card:ℝ)
noncomputable def sourceD20CellProxy (C : Finset ℕ) (W y : ℝ) (n : ℕ) : ℝ :=
  if sourceD20Rough W n then sourceD20CellRatio C W y else 0
noncomputable def sourceD20CellDelta (C : Finset ℕ) (W y : ℝ) (n : ℕ) : ℝ :=
  sourceD19RoughTest y n - sourceD20CellProxy C W y n

lemma sourceD20_rough_mono {W y : ℝ} (h : W ≤ y) {n : ℕ}
    (hn : sourceD20Rough y n) : sourceD20Rough W n :=
  ⟨hn.1,h.trans_lt hn.2⟩
lemma sourceD20_selected_subset (C : Finset ℕ) {W y : ℝ} (h : W ≤ y) :
    C.filter (sourceD20Rough y) ⊆ C.filter (sourceD20Rough W) := by
  intro n hn
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,
    sourceD20_rough_mono h (Finset.mem_filter.mp hn).2⟩
lemma sourceD20_ratio_bounds (C : Finset ℕ) {W y : ℝ} (h : W ≤ y) :
    0 ≤ sourceD20CellRatio C W y ∧ sourceD20CellRatio C W y ≤ 1 := by
  have hcard : ((C.filter (sourceD20Rough y)).card:ℝ) ≤
      ((C.filter (sourceD20Rough W)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (sourceD20_selected_subset C h)
  constructor
  · unfold sourceD20CellRatio; positivity
  · unfold sourceD20CellRatio
    exact div_le_one_of_le₀ hcard (Nat.cast_nonneg _)
lemma sourceD20_proxy_bounds (C : Finset ℕ) {W y : ℝ} (h : W ≤ y) (n : ℕ) :
    0 ≤ sourceD20CellProxy C W y n ∧ sourceD20CellProxy C W y n ≤ 1 := by
  unfold sourceD20CellProxy
  split_ifs
  · exact sourceD20_ratio_bounds C h
  · norm_num
lemma sourceD20_delta_bound (C : Finset ℕ) {W y : ℝ} (h : W ≤ y) (n : ℕ) :
    |sourceD20CellDelta C W y n| ≤ 1 := by
  obtain ⟨hp,hp1⟩ := sourceD20_proxy_bounds C h n
  have ht : 0 ≤ sourceD19RoughTest y n ∧ sourceD19RoughTest y n ≤ 1 := by
    unfold sourceD19RoughTest; split_ifs <;> norm_num
  unfold sourceD20CellDelta
  exact abs_le.mpr ⟨by linarith,by linarith⟩
lemma sourceD20_delta_support (C : Finset ℕ) {W y : ℝ} (h : W ≤ y) (n : ℕ)
    (hn : ¬sourceD20Rough W n) : sourceD20CellDelta C W y n = 0 := by
  have hy : ¬sourceD20Rough y n := fun hh => hn (sourceD20_rough_mono h hh)
  simp only [sourceD20CellDelta,sourceD20CellProxy,if_neg hn]
  unfold sourceD19RoughTest
  rw [if_neg (show ¬(2 ≤ n ∧ y < (n.minFac:ℝ)) from hy)]
  ring
/-- Exact count matching also when the denominator is zero: both counts vanish. -/
theorem sourceD20_full_cell_mass (C : Finset ℕ) {W y : ℝ} (h : W ≤ y) :
    (∑ n ∈ C,sourceD20CellProxy C W y n) = ((C.filter (sourceD20Rough y)).card:ℝ) := by
  have hcard := Finset.card_le_card (sourceD20_selected_subset C h)
  by_cases hz : (C.filter (sourceD20Rough W)).card = 0
  · have hy : (C.filter (sourceD20Rough y)).card = 0 := by omega
    simp [sourceD20CellProxy,sourceD20CellRatio,hz,hy]
  · have hn : ((C.filter (sourceD20Rough W)).card:ℝ) ≠ 0 := by exact_mod_cast hz
    unfold sourceD20CellProxy
    rw [←Finset.sum_filter,Finset.sum_const, nsmul_eq_mul]
    unfold sourceD20CellRatio
    field_simp
/-- No shortened-cell renormalization is used in this identity. -/
theorem sourceD20_full_cell_zero (C : Finset ℕ) {W y : ℝ} (h : W ≤ y) :
    (∑ n ∈ C,sourceD20CellDelta C W y n)=0 := by
  unfold sourceD20CellDelta
  rw [Finset.sum_sub_distrib,sourceD20_full_cell_mass C h]
  have ht : (∑ n ∈ C,sourceD19RoughTest y n)=((C.filter (sourceD20Rough y)).card:ℝ) := by
    simp [sourceD19RoughTest,sourceD20Rough,Finset.sum_boole]
    congr 1
    ext n
    simp only [Finset.mem_filter, sourceD20Rough]
  rw [ht,sub_self]
/-- The full-cell total variation is at most twice the actual selected count. -/
theorem sourceD20_full_cell_variation (C : Finset ℕ) {W y : ℝ} (h : W ≤ y) :
    (∑ n ∈ C,|sourceD20CellDelta C W y n|) ≤
      2*((C.filter (sourceD20Rough y)).card:ℝ) := by
  have hb : ∀ n ∈ C, |sourceD20CellDelta C W y n| ≤
      sourceD19RoughTest y n+sourceD20CellProxy C W y n := by
    intro n hn
    have ht : 0 ≤ sourceD19RoughTest y n := by unfold sourceD19RoughTest; positivity
    exact (abs_sub _ _).trans_eq (by
      rw [abs_of_nonneg ht,abs_of_nonneg (sourceD20_proxy_bounds C h n).1])
  have hh := Finset.sum_le_sum hb
  rw [Finset.sum_add_distrib,sourceD20_full_cell_mass C h] at hh
  have ht : (∑ n ∈ C,sourceD19RoughTest y n)=((C.filter (sourceD20Rough y)).card:ℝ) := by
    simp [sourceD19RoughTest,sourceD20Rough,Finset.sum_boole]
    congr 1
    ext n
    simp only [Finset.mem_filter, sourceD20Rough]
  rw [ht] at hh
  simpa only [two_mul] using hh
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20LogCells -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
noncomputable def sourceD20LogCell (Δ : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Ioc ⌊Real.exp ((j:ℝ)*Δ)⌋₊ ⌊Real.exp (((j:ℝ)+1)*Δ)⌋₊
noncomputable def sourceD20CellIndex (Δ : ℝ) (n : ℕ) : ℕ :=
  ⌈Real.log (n:ℝ)/Δ⌉₊-1
lemma sourceD20_mem_cell (Δ : ℝ) (j n : ℕ) :
    n ∈ sourceD20LogCell Δ j ↔
      Real.exp ((j:ℝ)*Δ) < (n:ℝ) ∧ (n:ℝ) ≤ Real.exp (((j:ℝ)+1)*Δ) := by
  simp only [sourceD20LogCell,Finset.mem_Ioc,
    Nat.floor_lt (Real.exp_nonneg _),Nat.le_floor_iff (Real.exp_nonneg _)]
lemma sourceD20_cell_log_bounds {Δ : ℝ} (hΔ : 0 < Δ) {j n : ℕ}
    (hn : n ∈ sourceD20LogCell Δ j) :
    (j:ℝ) < Real.log (n:ℝ)/Δ ∧ Real.log (n:ℝ)/Δ ≤ (j:ℝ)+1 := by
  obtain ⟨hl,hu⟩ := (sourceD20_mem_cell Δ j n).mp hn
  have hn0 : (0:ℝ)<n := (Real.exp_pos _).trans hl
  have hlo := Real.log_lt_log (Real.exp_pos _) hl
  rw [Real.log_exp] at hlo
  have hhi := (Real.log_le_iff_le_exp hn0).mpr hu
  exact ⟨(lt_div_iff₀ hΔ).mpr hlo,(div_le_iff₀ hΔ).mpr hhi⟩
/-- Every integer >=2 belongs to exactly its full logarithmic cell. -/
theorem sourceD20_index_mem {Δ : ℝ} (hΔ : 0 < Δ) (n : ℕ) (hn : 2 ≤ n) :
    n ∈ sourceD20LogCell Δ (sourceD20CellIndex Δ n) := by
  let t := Real.log (n:ℝ)/Δ
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have ht : 0<t := div_pos (Real.log_pos hn1) hΔ
  have hc : 1 ≤ ⌈t⌉₊ := Nat.ceil_pos.mpr ht
  have hlo : ((⌈t⌉₊-1:ℕ):ℝ) < t :=
    (Nat.lt_ceil).mp (show ⌈t⌉₊-1<⌈t⌉₊ by omega)
  have hhi : t ≤ ((⌈t⌉₊-1:ℕ):ℝ)+1 := by
    have h := Nat.le_ceil t
    have he : (⌈t⌉₊-1)+1=⌈t⌉₊ := by omega
    exact h.trans_eq (by exact_mod_cast he.symm)
  apply (sourceD20_mem_cell Δ _ n).mpr
  have hn0 : (0:ℝ)<n := by linarith
  constructor
  · have he := Real.exp_lt_exp.mpr ((lt_div_iff₀ hΔ).mp hlo)
    simpa only [Real.exp_log hn0,t,sourceD20CellIndex] using he
  · exact (Real.log_le_iff_le_exp hn0).mp ((div_le_iff₀ hΔ).mp hhi)
lemma sourceD20_cell_unique {Δ : ℝ} (hΔ : 0 < Δ) {i j n : ℕ}
    (hi : n ∈ sourceD20LogCell Δ i) (hj : n ∈ sourceD20LogCell Δ j) : i=j := by
  obtain ⟨hli,hui⟩ := sourceD20_cell_log_bounds hΔ hi
  obtain ⟨hlj,huj⟩ := sourceD20_cell_log_bounds hΔ hj
  have h1 : (i:ℝ)<(j:ℝ)+1 := hli.trans_le huj
  have h2 : (j:ℝ)<(i:ℝ)+1 := hlj.trans_le hui
  have hh1 : i < j+1 := by exact_mod_cast h1
  have hh2 : j < i+1 := by exact_mod_cast h2
  omega
lemma sourceD20_cell_index_eq {Δ : ℝ} (hΔ : 0 < Δ) {j n : ℕ}
    (hn : n ∈ sourceD20LogCell Δ j) : sourceD20CellIndex Δ n=j := by
  have hl := (sourceD20_mem_cell Δ j n).mp hn
  have he : (1:ℝ) ≤ Real.exp ((j:ℝ)*Δ) := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hΔ.le)
  have hn2 : 2 ≤ n := by
    have ht : (1:ℝ) < n := he.trans_lt hl.1
    have htN : 1 < n := by exact_mod_cast ht
    omega
  exact sourceD20_cell_unique hΔ (sourceD20_index_mem hΔ n hn2) hn
noncomputable def sourceD20FullProxy (Δ W y : ℝ) (n : ℕ) : ℝ :=
  sourceD20CellProxy (sourceD20LogCell Δ (sourceD20CellIndex Δ n)) W y n
noncomputable def sourceD20FullDelta (Δ W y : ℝ) (n : ℕ) : ℝ :=
  sourceD19RoughTest y n-sourceD20FullProxy Δ W y n
lemma sourceD20_full_proxy_on_cell {Δ W y : ℝ} (hΔ : 0 < Δ) {j n : ℕ}
    (hn : n ∈ sourceD20LogCell Δ j) :
    sourceD20FullProxy Δ W y n=sourceD20CellProxy (sourceD20LogCell Δ j) W y n := by
  simp only [sourceD20FullProxy,sourceD20_cell_index_eq hΔ hn]
theorem sourceD20_full_delta_zero {Δ W y : ℝ} (hΔ : 0<Δ) (hWy : W≤y) (j : ℕ) :
    (∑ n ∈ sourceD20LogCell Δ j,sourceD20FullDelta Δ W y n)=0 := by
  have he : (∑ n ∈ sourceD20LogCell Δ j,sourceD20FullDelta Δ W y n) =
      ∑ n ∈ sourceD20LogCell Δ j,sourceD20CellDelta (sourceD20LogCell Δ j) W y n := by
    apply Finset.sum_congr rfl; intro n hn
    simp only [sourceD20FullDelta,sourceD20CellDelta,sourceD20_full_proxy_on_cell hΔ hn]
  rw [he]
  exact sourceD20_full_cell_zero _ hWy
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20IntervalCancellation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
lemma sourceD20_cell_ge_two {Δ : ℝ} (hΔ : 0 < Δ) {j n : ℕ}
    (hn : n ∈ sourceD20LogCell Δ j) : 2 ≤ n := by
  have he : (1:ℝ) ≤ Real.exp ((j:ℝ)*Δ) := Real.one_le_exp (by positivity)
  have ht : (1:ℝ)<n := he.trans_lt ((sourceD20_mem_cell Δ j n).mp hn).1
  have : 1 < n := by exact_mod_cast ht
  omega
lemma sourceD20_index_mono {Δ : ℝ} (hΔ : 0 < Δ) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) : sourceD20CellIndex Δ a ≤ sourceD20CellIndex Δ b := by
  have hlog := Real.log_le_log (show (0:ℝ)<a by exact_mod_cast (show 0<a by omega))
    (Nat.cast_le.mpr hab)
  exact Nat.sub_le_sub_right (Nat.ceil_le_ceil (div_le_div_of_nonneg_right hlog hΔ.le)) 1
/-- A cell meeting an interval is either an endpoint cell or is present in full. -/
theorem sourceD20_interior_cell_full {Δ : ℝ} (hΔ : 0 < Δ) (a b j : ℕ)
    (ha : 2 ≤ a) (hj : j ∈ (Finset.Icc a b).image (sourceD20CellIndex Δ))
    (hja : j ≠ sourceD20CellIndex Δ a) (hjb : j ≠ sourceD20CellIndex Δ b) :
    (Finset.Icc a b).filter (fun n => sourceD20CellIndex Δ n=j) = sourceD20LogCell Δ j := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hj
  have hma := (Finset.mem_Icc.mp hm).1
  have hmb := (Finset.mem_Icc.mp hm).2
  have hc1 := sourceD20_index_mono hΔ (by omega : 1 ≤ a) hma
  have hc2 := sourceD20_index_mono hΔ (by omega : 1 ≤ m) hmb
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hidx⟩ := Finset.mem_filter.mp hn
    rw [←hidx]
    exact sourceD20_index_mem hΔ n (ha.trans (Finset.mem_Icc.mp hn).1)
  · intro hn
    have hn2 := sourceD20_cell_ge_two hΔ hn
    have hnidx := sourceD20_cell_index_eq hΔ hn
    have han : a ≤ n := by
      by_contra hh
      have hc := sourceD20_index_mono hΔ (by omega : 1 ≤ n) (by omega : n ≤ a)
      rw [hnidx] at hc
      exact hja (le_antisymm hc hc1)
    have hnb : n ≤ b := by
      by_contra hh
      have hc := sourceD20_index_mono hΔ (by omega : 1 ≤ b) (by omega : b ≤ n)
      rw [hnidx] at hc
      exact hjb (le_antisymm hc2 hc)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨han,hnb⟩,hnidx⟩
/-- Only the two cut endpoint cells survive. There is no factor counting full cells. -/
theorem sourceD20_interval_sum_bound {Δ W y : ℝ} (hΔ : 0 < Δ) (hWy : W ≤ y)
    (a b : ℕ) (ha : 2 ≤ a) (H : ℝ) (hH : 0 ≤ H)
    (hcard : ∀ j ∈ (Finset.Icc a b).image (sourceD20CellIndex Δ),
      ((sourceD20LogCell Δ j).card:ℝ) ≤ H) :
    |∑ n ∈ Finset.Icc a b,sourceD20FullDelta Δ W y n| ≤ 2*H := by
  let I := Finset.Icc a b
  let J := I.image (sourceD20CellIndex Δ)
  let F := fun j => ∑ n ∈ I.filter (fun n => sourceD20CellIndex Δ n=j),
    sourceD20FullDelta Δ W y n
  have hfiber : (∑ j ∈ J,F j) = ∑ n ∈ I,sourceD20FullDelta Δ W y n :=
    Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem _ hn) _
  have hpoint : ∀ j ∈ J, |F j| ≤ H := by
    intro j hj
    have hsub : I.filter (fun n => sourceD20CellIndex Δ n=j) ⊆ sourceD20LogCell Δ j := by
      intro n hn
      obtain ⟨hn,he⟩ := Finset.mem_filter.mp hn
      rw [←he]
      exact sourceD20_index_mem hΔ n (ha.trans (Finset.mem_Icc.mp hn).1)
    calc
      |F j| ≤ ∑ n ∈ I.filter (fun n => sourceD20CellIndex Δ n=j),
          |sourceD20FullDelta Δ W y n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ I.filter (fun n => sourceD20CellIndex Δ n=j),(1:ℝ) := by
        apply Finset.sum_le_sum; intro n hn
        exact sourceD20_delta_bound _ hWy n
      _ = ((I.filter (fun n => sourceD20CellIndex Δ n=j)).card:ℝ) := by simp
      _ ≤ ((sourceD20LogCell Δ j).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ H := hcard j hj
  have hz : ∀ j ∈ J,j ≠ sourceD20CellIndex Δ a → j ≠ sourceD20CellIndex Δ b → F j=0 := by
    intro j hj hja hjb
    dsimp [F,I]
    rw [sourceD20_interior_cell_full hΔ a b j ha hj hja hjb]
    exact sourceD20_full_delta_zero hΔ hWy j
  let E : Finset ℕ := {sourceD20CellIndex Δ a,sourceD20CellIndex Δ b}
  have hc : (J.filter (fun j => j ∈ E)).card ≤ 2 := by
    have he : J.filter (fun j => j ∈ E) ⊆ E := fun j hj => (Finset.mem_filter.mp hj).2
    exact (Finset.card_le_card he).trans Finset.card_le_two
  rw [←hfiber]
  calc
    |∑ j ∈ J,F j| ≤ ∑ j ∈ J,|F j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ J,if j ∈ E then H else 0 := by
      apply Finset.sum_le_sum; intro j hj
      by_cases he : j ∈ E
      · rw [ite_eq_left he]; exact hpoint j hj
      · rw [ite_eq_right he]
        have ha' : j ≠ sourceD20CellIndex Δ a := by intro h; apply he; simp [E,h]
        have hb' : j ≠ sourceD20CellIndex Δ b := by intro h; apply he; simp [E,h]
        rw [hz j hj ha' hb',abs_zero]
    _ = ((J.filter (fun j => j ∈ E)).card:ℝ)*H := by rw [←Finset.sum_filter]; simp
    _ ≤ 2*H := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hH
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD20CellSize -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
lemma sourceD20_cell_card_bound {Δ : ℝ} (hΔ : 0<Δ) {j n : ℕ}
    (hn : n ∈ sourceD20LogCell Δ j) (B : ℝ) (hnB : (n:ℝ)≤B) :
    ((sourceD20LogCell Δ j).card:ℝ) ≤ (Real.exp Δ-1)*B+1 := by
  let A := Real.exp ((j:ℝ)*Δ)
  let Z := Real.exp (((j:ℝ)+1)*Δ)
  have hAZ : A ≤ Z := Real.exp_le_exp.mpr (by nlinarith)
  have hfloor : ⌊A⌋₊ ≤ ⌊Z⌋₊ := Nat.floor_le_floor hAZ
  have heq : Z=A*Real.exp Δ := by dsimp [Z,A]; rw [←Real.exp_add]; congr 1; ring
  have hA : A≤B := ((sourceD20_mem_cell Δ j n).mp hn).1.le.trans hnB
  have hcoef : 0≤Real.exp Δ-1 := sub_nonneg.mpr (Real.one_le_exp hΔ.le)
  have hf1 := Nat.floor_le (Real.exp_nonneg (((j:ℝ)+1)*Δ))
  have hf2 := Nat.lt_floor_add_one A
  simp only [sourceD20LogCell,Nat.card_Ioc]
  change ((⌊Z⌋₊-⌊A⌋₊:ℕ):ℝ) ≤ _
  rw [Nat.cast_sub hfloor]
  have hm := mul_le_mul_of_nonneg_left hA hcoef
  change (⌊Z⌋₊:ℝ)≤Z at hf1
  have hf1' : (⌊Z⌋₊:ℝ) ≤ A*Real.exp Δ := hf1.trans_eq heq
  nlinarith only [hf1',hf2,hm]
/-- Uniform genuine prefix bound for every truncation of the source test interval. -/
theorem sourceD20_interval_raw_bound {Δ W y : ℝ} (hΔ : 0<Δ) (hWy : W≤y)
    (a b : ℕ) (ha : 2≤a) :
    |∑ n ∈ Finset.Icc a b,sourceD20FullDelta Δ W y n| ≤
      2*((Real.exp Δ-1)*(b:ℝ)+1) := by
  apply sourceD20_interval_sum_bound hΔ hWy a b ha
  · have he : 0 ≤ Real.exp Δ-1 := sub_nonneg.mpr (Real.one_le_exp hΔ.le)
    positivity
  · intro j hj
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
    exact sourceD20_cell_card_bound hΔ (sourceD20_index_mem hΔ n (ha.trans (Finset.mem_Icc.mp hn).1))
      b (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2)
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD21CellIntervals -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Every truncated FULL cell remains an interval; its ratio is not recomputed. -/
theorem sourceD21_cell_slice (Δ : ℝ) (hΔ : 0<Δ) (a b j : ℕ) (ha : 2≤a) :
    (Finset.Icc a b).filter (fun n => sourceD20CellIndex Δ n=j)=
      Finset.Icc (max a (⌊Real.exp ((j:ℝ)*Δ)⌋₊+1))
        (min b ⌊Real.exp (((j:ℝ)+1)*Δ)⌋₊) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hidx⟩ := Finset.mem_filter.mp hn
    have hc := sourceD20_index_mem hΔ n (ha.trans (Finset.mem_Icc.mp hn).1)
    rw [hidx] at hc
    have hh := Finset.mem_Ioc.mp hc
    have hi := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨max_le hi.1 (by omega),le_min hi.2 hh.2⟩
  · intro hn
    have hi := Finset.mem_Icc.mp hn
    have hna := (le_max_left _ _).trans hi.1
    have hnb := hi.2.trans (min_le_left _ _)
    have hc : n∈sourceD20LogCell Δ j := Finset.mem_Ioc.mpr
      ⟨by have := (le_max_right _ _).trans hi.1; omega,hi.2.trans (min_le_right _ _)⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hna,hnb⟩,sourceD20_cell_index_eq hΔ hc⟩

/-- A polynomial number of actual cells; no replacement by the number of integers. -/
theorem sourceD21_cell_count (Δ : ℝ) (hΔ : 0<Δ) (a b : ℕ) (ha : 2≤a) (hab : a≤b) :
    (((Finset.Icc a b).image (sourceD20CellIndex Δ)).card:ℝ) ≤ Real.log (b:ℝ)/Δ+2 := by
  let N := ⌈Real.log (b:ℝ)/Δ⌉₊
  have hs : (Finset.Icc a b).image (sourceD20CellIndex Δ) ⊆ Finset.range (N+1) := by
    intro j hj
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
    have hi := sourceD20_index_mono hΔ
      (show 1≤n by have := Finset.mem_Icc.mp hn;omega) (Finset.mem_Icc.mp hn).2
    have hbN : sourceD20CellIndex Δ b≤N := Nat.sub_le _ _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hi.trans hbN))
  have hc : (((Finset.Icc a b).image (sourceD20CellIndex Δ)).card:ℝ)≤(N:ℝ)+1 := by
    have hh := Finset.card_le_card hs
    simpa only [Finset.card_range,Nat.cast_add,Nat.cast_one] using (Nat.cast_le (α:=ℝ)).mpr hh
  have hp : 0≤Real.log (b:ℝ)/Δ := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1≤b by omega))) hΔ.le
  have hceil : (N:ℝ)<Real.log (b:ℝ)/Δ+1 := Nat.ceil_lt_add_one hp
  linarith
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22CellCount -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

noncomputable def sourceD22Cell (Y Δ : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊Y⌋₊ ⌊Real.exp Δ*Y⌋₊
noncomputable def sourceD22Count (Y Δ z : ℝ) : ℝ :=
  (((sourceD22Cell Y Δ).filter (sourceD20Rough z)).card:ℝ)
noncomputable def sourceD22SieveConstant : ℝ :=
  let K := (Real.exp (Real.exp 1*4)/(1-Real.exp (-1)))/Real.exp (-4/(1/2:ℝ))
  K*Real.exp K

lemma sourceD22_rough_iff (z : ℝ) (hz : 0≤z) (n : ℕ) (hn : 2≤n) :
    sourceD20Rough z n ↔ ∀ p ∈ (Finset.range (⌊z⌋₊+1)).filter Nat.Prime, ¬p∣n := by
  constructor
  · intro h p hp hd
    obtain ⟨hpR,hpP⟩ := Finset.mem_filter.mp hp
    have hpz : (p:ℝ)≤z := (Nat.cast_le.mpr (by have := Finset.mem_range.mp hpR;omega)).trans (Nat.floor_le hz)
    have hm : (n.minFac:ℝ)≤p := Nat.cast_le.mpr (Nat.minFac_le_of_dvd hpP.two_le hd)
    linarith [h.2]
  · intro h
    refine ⟨hn,?_⟩
    by_contra hh
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hb : n.minFac≤⌊z⌋₊ := Nat.le_floor (le_of_not_gt hh)
    exact h n.minFac (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩) (Nat.minFac_dvd n)

/-- Exact original full-cell count, with prime 2 and natural floors retained. -/
theorem sourceD22_cell_count_error (h : ℕ) (z Y Δ : ℝ)
    (hz : 1<z) (hh : 2≤h) (hev : Even h) (hY : 1≤Y) (hΔ : 0≤Δ) :
    |sourceD22Count Y Δ z - (Real.exp Δ-1)*Y*sourceNaturalEuler ⌊z⌋₊| ≤
      (Real.exp Δ-1)*Y*sourceNaturalEuler ⌊z⌋₊ * sourceD22SieveConstant * Real.exp (-(h:ℝ)) +
      2*z^(4*(h:ℝ)+2) := by
  have hs := Green64Analytic.SieveContinuation.full_cell_rough_count h z Y Δ hz hh hev
    (by linarith) hΔ
  have he : (sourceD22Cell Y Δ).filter (sourceD20Rough z) =
      (sourceD22Cell Y Δ).filter (fun n => ∀ p ∈ (Finset.range (⌊z⌋₊+1)).filter Nat.Prime, ¬p∣n) := by
    ext n
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hn
    have hn2 : 2≤n := by
      have hN : 1≤⌊Y⌋₊ := Nat.le_floor (by simpa using hY)
      have ht := (Finset.mem_Ioc.mp hn).1
      omega
    simpa only [Finset.mem_filter] using sourceD22_rough_iff z (by linarith) n hn2
  unfold sourceD22Count
  rw [he]
  convert hs using 1 <;> norm_num [sourceD22Cell,sourceNaturalEuler,sourceD22SieveConstant,mul_assoc]

lemma sourceD22_log_cell_exact (Δ : ℝ) (j : ℕ) :
    sourceD20LogCell Δ j = sourceD22Cell (Real.exp ((j:ℝ)*Δ)) Δ := by
  unfold sourceD20LogCell sourceD22Cell
  rw [←Real.exp_add]
  congr 3
  ring

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22PrimeCellTheta -/

section

open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
noncomputable def sourceD22PrimeCount (Y Δ : ℝ) : ℝ :=
  (((sourceD22Cell Y Δ).filter Nat.Prime).card:ℝ)

lemma sourceD22_theta_cell_identity (Y Δ : ℝ) (hY : 0≤Y) (hΔ : 0≤Δ) :
    Chebyshev.theta (Real.exp Δ*Y)-Chebyshev.theta Y =
      ∑ p ∈ (sourceD22Cell Y Δ).filter Nat.Prime,Real.log (p:ℝ) := by
  have hYZ : Y≤Real.exp Δ*Y := le_mul_of_one_le_left hY (Real.one_le_exp hΔ)
  have hF := Nat.floor_le_floor hYZ
  let f : ℕ → ℝ := fun p => if p.Prime then Real.log (p:ℝ) else 0
  have hsub : Finset.Ioc 0 ⌊Y⌋₊ ⊆ Finset.Ioc 0 ⌊Real.exp Δ*Y⌋₊ := by
    intro p hp; exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hp).1,(Finset.mem_Ioc.mp hp).2.trans hF⟩
  have hdiff : Finset.Ioc 0 ⌊Real.exp Δ*Y⌋₊ \ Finset.Ioc 0 ⌊Y⌋₊ = sourceD22Cell Y Δ := by
    ext p; simp only [Finset.mem_sdiff,Finset.mem_Ioc,sourceD22Cell]; omega
  have hh := Finset.sum_sdiff (f:=f) hsub
  rw [hdiff] at hh
  simp only [f,←Finset.sum_filter] at hh
  change (∑ p ∈ (sourceD22Cell Y Δ).filter Nat.Prime,Real.log (p:ℝ))+
    Chebyshev.theta Y=Chebyshev.theta (Real.exp Δ*Y) at hh
  linarith

/-- Counting primes on a narrow cell through theta avoids a coarse pi(t)-t/log(t) error. -/
theorem sourceD22_prime_count_theta_upper (Y Δ : ℝ) (hY : 1<Y) (hΔ : 0≤Δ) :
    Real.log Y*sourceD22PrimeCount Y Δ ≤
      Chebyshev.theta (Real.exp Δ*Y)-Chebyshev.theta Y := by
  rw [sourceD22_theta_cell_identity Y Δ (by linarith) hΔ]
  have hh : (∑ _p ∈ (sourceD22Cell Y Δ).filter Nat.Prime,Real.log Y) ≤
      ∑ p ∈ (sourceD22Cell Y Δ).filter Nat.Prime,Real.log (p:ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpY : Y<(p:ℝ) := (Nat.floor_lt (by linarith : 0≤Y)).mp (Finset.mem_Ioc.mp hpI).1
    exact Real.log_le_log (by linarith) hpY.le
  simpa only [Finset.sum_const,nsmul_eq_mul,sourceD22PrimeCount,mul_comm] using hh


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22EulerLower -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- A weak elementary Euler floor suffices to absorb the full-cell remainder. -/
theorem sourceD22_euler_lower (z : ℝ) (hz : 1≤z) :
    z⁻¹ ≤ sourceNaturalEuler ⌊z⌋₊ := by
  have hN : 1≤⌊z⌋₊ := Nat.le_floor (by simpa using hz)
  have hNp : (0:ℝ)<⌊z⌋₊ := by exact_mod_cast (show 0<⌊z⌋₊ by omega)
  have hfloor : (⌊z⌋₊:ℝ)≤z := Nat.floor_le (by linarith)
  exact ((inv_le_inv₀ (by linarith) hNp).mpr hfloor).trans
    (source_natural_euler_lower ⌊z⌋₊ hN)

lemma sourceD22_sieve_constant_pos : 0<sourceD22SieveConstant := by
  have hden : 0<1-Real.exp (-1) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  unfold sourceD22SieveConstant
  positivity

lemma sourceD22_precise_depth (ε : ℝ) (hε : 0<ε) :
    ∃ h : ℕ,2≤h ∧ Even h ∧ sourceD22SieveConstant*Real.exp (-(h:ℝ)) ≤ ε := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  have hs : Tendsto (fun n : ℕ => sourceD22SieveConstant*Real.exp (-(n:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using he.const_mul sourceD22SieveConstant
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hs.eventually_lt_const hε)
  exact ⟨2*(N+1),by omega,⟨N+1,by omega⟩,(hN _ (by omega)).le⟩


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22CellRate -/

section

open Filter Topology
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Any fixed sieve depth and logarithmic mesh are negligible against the cell scale. -/
theorem sourceD22_subpower_rate (S c β ε : ℝ) (hβ : 0<β) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, 2*L^S*Real.exp (c*Real.sqrt L-β*L) ≤ ε := by
  have hrate := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero S (β/2) (by linarith)
  have hsmall := hrate.eventually_lt_const (show (0:ℝ)<ε/2 by linarith)
  have hroot := Real.tendsto_sqrt_atTop.eventually_ge_atTop (2*c/β)
  filter_upwards [hsmall,hroot,eventually_gt_atTop (0:ℝ)] with L hs hr hL
  have hm : 2*c≤Real.sqrt L*β := (div_le_iff₀ hβ).mp hr
  have hmul := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg L)
  have hsq := Real.sq_sqrt hL.le
  have heq : Real.sqrt L*β*Real.sqrt L=β*L := by
    calc
      _ = β*(Real.sqrt L)^2 := by ring
      _ = _ := by rw [hsq]
  rw [heq] at hmul
  have hgap : c*Real.sqrt L-β*L ≤ -(β/2)*L := by nlinarith only [hmul]
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgap)
    (show 0≤2*L^S by positivity)
  change L^S*Real.exp (-(β/2)*L)<ε/2 at hs
  linarith

lemma sourceD22_exp_sqrt_power (L c : ℝ) :
    (Real.exp (Real.sqrt L))^c=Real.exp (c*Real.sqrt L) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,mul_comm]

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22RemainderRelative -/

section

open Filter Topology
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Actual additive full-cell sieve error is relatively small UNIFORMLY in Y. -/
theorem sourceD22_cell_remainder_relative (S β ε : ℝ) (h : ℕ)
    (hβ : 0<β) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Real.exp (β*L)≤Y →
      2*(Real.exp (Real.sqrt L))^(4*(h:ℝ)+2) ≤
        ε*((Real.exp (L^(-S))-1)*Y*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  filter_upwards [sourceD22_subpower_rate S (4*(h:ℝ)+3) β ε hβ hε,
    eventually_gt_atTop (0:ℝ)] with L hrate hL
  intro Y hY
  let Δ := L^(-S)
  let V := sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊
  let Q := Δ*Real.exp (β*L-Real.sqrt L)
  have hΔ : 0<Δ := Real.rpow_pos_of_pos hL _
  have hYpos : 0<Y := (Real.exp_pos _).trans_le hY
  have hV : Real.exp (-Real.sqrt L)≤V := by
    simpa only [Real.exp_neg] using sourceD22_euler_lower
      (Real.exp (Real.sqrt L)) (Real.one_le_exp (Real.sqrt_nonneg L))
  have hVpos : 0<V := (Real.exp_pos _).trans_le hV
  have hmesh : Δ≤Real.exp Δ-1 := by linarith [Real.add_one_le_exp Δ]
  have hmain : Q≤(Real.exp Δ-1)*Y*V := by
    have he : Q=Δ*Real.exp (β*L)*Real.exp (-Real.sqrt L) := by
      dsimp [Q]; rw [sub_eq_add_neg,Real.exp_add]; ring
    rw [he]
    exact mul_le_mul (mul_le_mul hmesh hY (Real.exp_pos _).le (by linarith)) hV
      (Real.exp_pos _).le (mul_nonneg (hΔ.le.trans hmesh) hYpos.le)
  have hmul := mul_le_mul_of_nonneg_right hrate (show 0≤Q by dsimp [Q]; positivity)
  have hcancel : L^S*Δ=1 := by
    dsimp [Δ]
    rw [←Real.rpow_add hL]; simp
  have halg : (2*L^S*Real.exp ((4*(h:ℝ)+3)*Real.sqrt L-β*L))*Q =
      2*Real.exp ((4*(h:ℝ)+2)*Real.sqrt L) := by
    calc
      _ = 2*(L^S*Δ)*(Real.exp ((4*(h:ℝ)+3)*Real.sqrt L-β*L)*
          Real.exp (β*L-Real.sqrt L)) := by dsimp [Q]; ring
      _ = _ := by rw [hcancel,←Real.exp_add]; congr 2 <;> ring
  rw [halg] at hmul
  rw [sourceD22_exp_sqrt_power]
  exact hmul.trans (mul_le_mul_of_nonneg_left hmain hε.le)

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22Denominator -/

section

open Filter Topology
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

/-- Relative asymptotic for the ACTUAL full-cell denominator, uniformly over all Y>=x^beta. -/
theorem sourceD22_denominator_relative (S β ε : ℝ) (hβ : 0<β) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Real.exp (β*L)≤Y →
      let Δ := L^(-S)
      let W := Real.exp (Real.sqrt L)
      let main := (Real.exp Δ-1)*Y*sourceNaturalEuler ⌊W⌋₊
      |sourceD22Count Y Δ W-main|≤ε*main := by
  obtain ⟨h,hh,hev,hdepth⟩ := sourceD22_precise_depth (ε/2) (by linarith)
  filter_upwards [sourceD22_cell_remainder_relative S β (ε/2) h hβ (by linarith),
    eventually_gt_atTop (0:ℝ)] with L herr hL
  intro Y hY
  let Δ := L^(-S)
  let W := Real.exp (Real.sqrt L)
  let main := (Real.exp Δ-1)*Y*sourceNaturalEuler ⌊W⌋₊
  have hY1 : 1≤Y := (Real.one_le_exp (mul_nonneg hβ.le hL.le)).trans hY
  have hW : 1<W := Real.one_lt_exp_iff.mpr (Real.sqrt_pos.mpr hL)
  have hΔ : 0<Δ := Real.rpow_pos_of_pos hL _
  have hV : 0 ≤ sourceNaturalEuler ⌊W⌋₊ :=
    (inv_nonneg.mpr (by linarith : 0≤W)).trans (sourceD22_euler_lower W hW.le)
  have hmain : 0 ≤ main := by
    dsimp [main]; exact mul_nonneg (mul_nonneg (by linarith [Real.one_le_exp hΔ.le]) (by linarith)) hV
  have hb := sourceD22_cell_count_error h W Y Δ hW hh hev hY1 hΔ.le
  have he := herr Y hY
  have hd := mul_le_mul_of_nonneg_left hdepth hmain
  change |sourceD22Count Y Δ W-main|≤ε*main
  change |sourceD22Count Y Δ W-main| ≤ main*sourceD22SieveConstant*Real.exp (-(h:ℝ))+
    2*W^(4*(h:ℝ)+2) at hb
  change 2*W^(4*(h:ℝ)+2)≤(ε/2)*main at he
  nlinarith only [hb,he,hd]

/-- The real denominator is positive; neither an empty-cell convention nor an assumption. -/
theorem sourceD22_denominator_positive (S β : ℝ) (hβ : 0<β) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, Real.exp (β*L)≤Y →
      0<sourceD22Count Y (L^(-S)) (Real.exp (Real.sqrt L)) := by
  filter_upwards [sourceD22_denominator_relative S β (1/2) hβ (by norm_num),
    eventually_gt_atTop (0:ℝ)] with L hrel hL
  intro Y hY
  have hΔ : 0<L^(-S) := Real.rpow_pos_of_pos hL _
  have hYpos : 0<Y := (Real.exp_pos _).trans_le hY
  have hV : 0<sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
    (inv_pos.mpr (Real.exp_pos _)).trans_le (sourceD22_euler_lower _
      (Real.one_le_exp (Real.sqrt_nonneg L)))
  have hmain : 0<(Real.exp (L^(-S))-1)*Y*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
    mul_pos (mul_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hΔ)) hYpos) hV
  have hh := (abs_le.mp (hrel Y hY)).1
  linarith


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD22LogDenominator -/

section

open Filter Topology
open scoped Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0

lemma sourceD22_cell_lower (S β : ℝ) (hS : 0<S) (hβ : 0<β) :
    ∀ᶠ L : ℝ in atTop, ∀ j n : ℕ,
      n∈sourceD20LogCell (L^(-S)) j → Real.exp (β*L)≤(n:ℝ) →
      Real.exp ((β/2)*L)≤Real.exp ((j:ℝ)*L^(-S)) := by
  filter_upwards [eventually_ge_atTop (max 1 (2/β))] with L hL
  have hL1 : 1≤L := (le_max_left _ _).trans hL
  have hL2 : 2/β≤L := (le_max_right _ _).trans hL
  have hmesh : L^(-S)≤1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (show -S≤0 by linarith)
  have hB : 2≤L*β := (div_le_iff₀ hβ).mp hL2
  intro j n hn hsize
  have hh := hsize.trans ((sourceD20_mem_cell (L^(-S)) j n).mp hn).2
  have hex := Real.exp_le_exp.mp hh
  apply Real.exp_le_exp.mpr
  nlinarith only [hex,hmesh,hB]

/-- Exact full-cell denominator and its positive normalized asymptotic on every source cell. -/
theorem sourceD22_actual_log_denominator (S β ε : ℝ)
    (hS : 0<S) (hβ : 0<β) (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ j : ℕ,
      (∃ n∈sourceD20LogCell (L^(-S)) j, Real.exp (β*L)≤(n:ℝ)) →
      let Y := Real.exp ((j:ℝ)*L^(-S))
      let main := (Real.exp (L^(-S))-1)*Y*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊
      let den := (((sourceD20LogCell (L^(-S)) j).filter (sourceD20Rough (Real.exp (Real.sqrt L)))).card:ℝ)
      0<den ∧ |den/main-1|≤ε := by
  filter_upwards [sourceD22_cell_lower S β hS hβ,
    sourceD22_denominator_relative S (β/2) ε (by linarith) hε,
    sourceD22_denominator_positive S (β/2) (by linarith),eventually_gt_atTop (0:ℝ)]
    with L hlower hrel hpos hL
  intro j hj
  obtain ⟨n,hn,hsize⟩ := hj
  let Y := Real.exp ((j:ℝ)*L^(-S))
  let main := (Real.exp (L^(-S))-1)*Y*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊
  let den := sourceD22Count Y (L^(-S)) (Real.exp (Real.sqrt L))
  have hY : Real.exp ((β/2)*L)≤Y := hlower j n hn hsize
  have hp : 0<den := hpos Y hY
  have hr : |den-main|≤ε*main := hrel Y hY
  have hV : 0<sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
    (inv_pos.mpr (Real.exp_pos _)).trans_le (sourceD22_euler_lower _
      (Real.one_le_exp (Real.sqrt_nonneg L)))
  have hm : 0 < main := by
    dsimp [main]
    exact mul_pos (mul_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr
      (Real.rpow_pos_of_pos hL _))) (Real.exp_pos _)) hV
  have hratio : |den/main-1|≤ε := by
    have he : den/main-1=(den-main)/main := by field_simp
    rw [he,abs_div,abs_of_pos hm]
    exact (div_le_iff₀ hm).mpr hr
  rw [sourceD22_log_cell_exact]
  exact ⟨hp,hratio⟩

end Green64Analytic.SourceBlockSieve

end

