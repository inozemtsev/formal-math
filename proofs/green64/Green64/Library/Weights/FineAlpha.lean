module

public import Green64.Library.Analysis.Estimates.PrimeFineProxy
public import Green64.Library.Weights.Part045

@[expose] public section

/-!
# Weights / FineAlpha

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualFineAlpha -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- A literal full-cell prime or rough discrepancy, cut only AFTER its
full-cell normalization. Precision S is chosen after the required saving. -/
def b629ActualFineAlpha434 (prime : Bool) (L S gamma : ℝ) (l u n : ℕ) : ℂ :=
  if n ∈ Finset.Icc l u then
    if prime then (b627PrimeFullDelta434 (L^(-S)) (Real.exp (Real.sqrt L)) n : ℂ)
    else (sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L))
      ((Real.exp L)^gamma) n : ℂ)
  else 0

private theorem b629_mellin_phase434 (n : ℕ) (hn : 0 < n) (t : ℝ) :
    sourceD20Mellin t n = (n : ℂ)⁻¹ * sourcePhase n t := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold sourceD20Mellin sourcePhase
  rw [Complex.ofReal_natCast, Complex.cpow_add _ _ hn0,
    Complex.cpow_neg_one, Complex.cpow_def_of_ne_zero hn0,
    ← Complex.natCast_log]
  congr 2
  push_cast
  ring

private theorem b629_character_zero_modulus434
    (chi : DirichletCharacter ℂ 0) (n : ℕ) (hn : 2 ≤ n) : chi n = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  simpa only [Nat.coprime_zero_right] using (show n ≠ 1 by omega)

/-- The actual canonical fine alpha satisfies the ENTIRE original E
SourceAlphaDiscrepancy contract, including modulus zero. No discrepancy
or energy estimate is an input premise. -/
theorem b629_actual_fine_source_discrepancy434
    (B S beta gamma : ℝ) (hB : 0 < B) (hS : 2*B < S)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, ∀ (prime : Bool) (l u : ℕ),
      2 ≤ l → u ≤ 2*l → Real.exp (beta*L) ≤ (l:ℝ) →
      (u:ℝ) ≤ Real.exp (2*L) →
      SourceAlphaDiscrepancy L B (Real.exp L)
        (b629ActualFineAlpha434 prime L S gamma l u) := by
  filter_upwards [b627_actual_prime_restricted_all_character_saving434
      B S beta hB hS hbeta,
    sourceD21_restricted_all_character_saving B S beta gamma hB hS hbeta hgamma,
    eventually_gt_atTop (0:ℝ)] with L hprime hrough hL
  intro prime l u hl hu hsize hub q chi a b t hq ha hb ht
  by_cases hq0 : q = 0
  · subst q
    have hz : (∑ n ∈ Finset.Icc a b,
        b629ActualFineAlpha434 prime L S gamma l u n * chi n *
          (n:ℂ)⁻¹ * sourcePhase n t) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hc : n ∈ Finset.Icc l u
      · rw [b629_character_zero_modulus434 chi n
          (hl.trans (Finset.mem_Icc.mp hc).1)]
        simp
      · simp [b629ActualFineAlpha434, hc]
    rw [hz, norm_zero]
    exact Real.rpow_nonneg hL.le _
  · let : NeZero q := ⟨hq0⟩
    have he : (∑ n ∈ Finset.Icc a b,
        b629ActualFineAlpha434 prime L S gamma l u n * chi n *
          (n:ℂ)⁻¹ * sourcePhase n t) =
        ∑ n ∈ Finset.Icc a b,
          b629ActualFineAlpha434 prime L S gamma l u n * chi n *
            sourceD20Mellin t n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [b629_mellin_phase434 n (by have := (Finset.mem_Icc.mp hn).1; omega)]
      ring
    rw [he]
    cases prime with
    | false =>
      simpa only [b629ActualFineAlpha434, Bool.false_eq_true, ite_false] using
        hrough l u a b q chi hl hu hsize hub hq t ht
    | true =>
      simpa only [b629ActualFineAlpha434, ite_true] using
        hprime l u a b q chi t hl hu hsize hub hq ht

/-- Both literal fine coefficients have norm at most one, with original
rough support. These constants do not depend on the precision S. -/
theorem b629_actual_fine_coefficient_and_rough_support434
    (S beta gamma : ℝ) (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop, ∀ (prime : Bool) (l u : ℕ),
      Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ n : ℕ,
      ‖b629ActualFineAlpha434 prime L S gamma l u n‖ ≤ 1 ∧
      (b629ActualFineAlpha434 prime L S gamma l u n ≠ 0 →
        SourceRoughAbove n (Real.exp (Real.sqrt L))) := by
  have hW := Real.tendsto_exp_atTop.eventually
    (source_presieve_real_le_power gamma hgamma)
  filter_upwards [b627_actual_prime_fine_coefficient_bound434 S beta hS hbeta,
    hW] with L hprime hWy
  have hWy' : Real.exp (Real.sqrt L) ≤ (Real.exp L)^gamma := by
    simpa only [sourcePresieveReal, Real.log_exp] using hWy
  intro prime l u hsize n
  by_cases hc : n ∈ Finset.Icc l u
  · have hnsize : Real.exp (beta*L) ≤ (n:ℝ) :=
      hsize.trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hc).1)
    have hbound : ‖b629ActualFineAlpha434 prime L S gamma l u n‖ ≤ 1 := by
      cases prime with
      | false =>
        simpa only [b629ActualFineAlpha434, hc, ite_true, Bool.false_eq_true,
          ite_false, Complex.norm_real, Real.norm_eq_abs, sourceD20FullDelta,
          sourceD20FullProxy, sourceD20CellDelta] using
          sourceD20_delta_bound
            (sourceD20LogCell (L^(-S)) (sourceD20CellIndex (L^(-S)) n)) hWy' n
      | true =>
        simpa only [b629ActualFineAlpha434, hc, ite_true,
          Complex.norm_real, Real.norm_eq_abs] using (hprime n hnsize).1
    refine ⟨hbound, ?_⟩
    intro hn
    have hr : sourceD20Rough (Real.exp (Real.sqrt L)) n := by
      by_contra hnot
      apply hn
      cases prime with
      | false =>
        simp only [b629ActualFineAlpha434, hc, ite_true, Bool.false_eq_true, ite_false]
        have hz := sourceD20_delta_support
          (sourceD20LogCell (L^(-S)) (sourceD20CellIndex (L^(-S)) n)) hWy' n hnot
        have hzFull : sourceD20FullDelta (L^(-S)) (Real.exp (Real.sqrt L))
            ((Real.exp L)^gamma) n = 0 := by
          simpa only [sourceD20FullDelta, sourceD20FullProxy, sourceD20CellDelta] using hz
        simp only [hzFull, Complex.ofReal_zero]
      | true =>
        simp only [b629ActualFineAlpha434, hc, ite_true,
          (hprime n hnsize).2 hnot, Complex.ofReal_zero]
    intro p hp hpn
    exact hr.2.trans_le (Nat.cast_le.mpr (Nat.minFac_le_of_dvd hp.two_le hpn))
  · simp [b629ActualFineAlpha434, hc]
end Green64Analytic.CorrelationSquare

end

end

