module

public import Green64.Library.Weights.FineAlpha

@[expose] public section

/-!
# Weights / FineMarkedArc

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualFineMarkedArc -/

section

open MeasureTheory Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 10000000

private theorem b629_discrepancy_weaken434
    (L x B C : ℝ) (alpha : ℕ → ℂ) (hL : 1 ≤ L) (hBC : B ≤ C)
    (h : SourceAlphaDiscrepancy L C x alpha) :
    SourceAlphaDiscrepancy L B x alpha := by
  intro q chi a b t hq ha hb ht
  have hp := Real.rpow_le_rpow_of_exponent_le hL hBC
  exact (h q chi a b t (hq.trans hp) ha hb (ht.trans hp)).trans
    (Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hBC))

/-- Arbitrarily strong actual FULL marked additive-arc saving for the
literal prime or rough fine proxy. K is chosen before discrepancy B and
fine precision S. No hDisc, arc energy, tail saving or amplitude cap is
assumed. Geometry is the existing physical SourceComparisonData contract. -/
theorem b629_actual_fine_full_marked_signed_arc434
    (cfg : SourceComparisonFixed434) (target betaFine gammaFine : ℝ)
    (hbeta : 0 < betaFine) (hgamma : 0 < gammaFine) :
    ∃ Karc : ℝ, 0 < Karc ∧ ∃ B : ℕ, ∃ S : ℝ,
      2*((B:ℝ)+1)+3 < S ∧ ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (prime : Bool) (l u : ℕ),
      2 ≤ l → u ≤ 2*l → Real.exp (betaFine*L) ≤ (l:ℝ) →
      (u:ℝ) ≤ Real.exp (2*L) →
      ∀ Y Hprime : ℝ, ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      ∀ d : SourceComparisonData434 ι β cfg x L Y Hprime,
      d.alpha = b629ActualFineAlpha434 prime L S gammaFine l u →
      ∀ (eps : Bool) (den h : ℕ), 0 < den → (den:ℝ) ≤ L^cfg.cm →
      (∫ theta in {theta : ℝ | |theta| ≤ L^cfg.Carc/Hprime},
        ‖sourceCircleFourierPoly d.support
          (sourceSignedCoefficients434 d.Ptw eps d.endpoint)
          (((h:ℝ)/(den:ℝ)+theta:ℝ):AddCircle (1:ℝ))‖^2) ≤
        Karc*Y*L^(-target) := by
  obtain ⟨Karc,hKarc,B,X0,hX0,hArc⟩ :=
    eventually_source_data_signed_arc434 cfg target
  let S : ℝ := 2*((B:ℝ)+1)+4
  have hB : (0:ℝ) < (B:ℝ)+1 := by positivity
  have hS : 2*((B:ℝ)+1) < S := by dsimp [S]; linarith
  have hFine := b629_actual_fine_source_discrepancy434
    ((B:ℝ)+1) S betaFine gammaFine hB hS hbeta hgamma
  refine ⟨Karc,hKarc,B,S,by dsimp [S]; linarith,X0,hX0,?_⟩
  filter_upwards [hArc,hFine] with L hArcL hFineL
  intro x hx hLog hL prime l u hl hu hsize hub Y Hprime ι β _ _ _ _ d hAlpha
    eps den h hden hDenCap
  have hexp : Real.exp L = x := by
    rw [hLog, Real.exp_log (by linarith)]
  have hDiscStrong := hFineL prime l u hl hu hsize hub
  rw [hexp] at hDiscStrong
  have hDisc : SourceAlphaDiscrepancy L (B:ℝ) x d.alpha := by
    rw [hAlpha]
    exact b629_discrepancy_weaken434 L x (B:ℝ) ((B:ℝ)+1) _
      (by linarith) (by linarith) hDiscStrong
  exact hArcL x hx hLog hL Y Hprime d hDisc eps den h hden hDenCap
end Green64Analytic.CorrelationSquare

end

end

