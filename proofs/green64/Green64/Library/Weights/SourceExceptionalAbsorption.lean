module

public import Green64.Library.Correlation.Part004
public import Mathlib.Tactic

@[expose] public section

/-!
# Weights / SourceExceptionalAbsorption

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceExceptionalAbsorption -/

section

/-! Algebraic elimination of the self term in the *unconditional*
source exceptional-time estimate. The eventual source-scale absorption
is a separate quantitative theorem, not hidden in this statement. -/

namespace Green64Analytic.CorrelationMellin

private theorem absorb_self_term
    (N K Y R D M : ℝ)
    (hN : 0 ≤ N) (hD : 0 < D)
    (hEstimate : N*D ≤ 448*K*(Y*R+N*Real.sqrt Y)*M)
    (hAbsorb : 896*K*Real.sqrt Y*M ≤ D) :
    N ≤ (896*K*Y*R*M)/D := by
  have hMult := mul_le_mul_of_nonneg_right hAbsorb hN
  have hFin : N*D ≤ 896*K*Y*R*M := by
    nlinarith [hMult]
  exact (le_div_iff₀ hD).mpr (by nlinarith [hFin])

/-- Quantitative exceptional cardinality following actual unconditional
Gram-row and power-moment estimates, once the explicit numerical
absorption inequality is satisfied. The original prime polynomial
and its exact j₀ order are retained, not abstract exceptional sets. -/
theorem source_exceptional_count_absorbed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (times : ι → ℝ) (s : Finset ℕ) (P Y : ℕ) (C δ : ℝ)
    (hP : 1 ≤ P) (hY : 1 ≤ Y)
    (hprime : ∀ p ∈ s, Nat.Prime p)
    (hSupport : s ⊆ Finset.Icc P (2*P))
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (b : ℕ → ℂ) (hb : ∀ p ∈ s, ‖b p‖ ≤ C)
    (hRange : ∀ i, |times i| ≤ (Y:ℝ))
    (hSep : ∀ i j, i ≠ j → 1 ≤ |times i-times j|)
    (hlarge : ∀ i : ι,
      δ ≤ ‖∑ p : {p : ℕ // p ∈ s},
        (b p.val * ((p.val:ℂ)⁻¹)) * sourcePhase p.val (times i)‖)
    (hAbsorb :
      896*((Nat.log2 Y+1:ℕ):ℝ)*Real.sqrt (Y:ℝ) *
        ((Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
          (2*C^2/(P:ℝ))^(sourcePrimeMomentOrder P Y)) ≤
        δ^(2*sourcePrimeMomentOrder P Y)) :
    (Fintype.card ι : ℝ) ≤
      (896*((Nat.log2 Y+1:ℕ):ℝ)*(Y:ℝ)*
         (1+Real.log (2*(Y:ℝ))) *
         ((Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
           (2*C^2/(P:ℝ))^(sourcePrimeMomentOrder P Y))) /
        δ^(2*sourcePrimeMomentOrder P Y) := by
  have hEstimate := source_exceptional_log_count_unconditional_self_term
    times s P Y C δ hP hY hprime hSupport hC hδ.le b hb
      hRange hSep hlarge
  exact absorb_self_term _ _ _ _ _ _ (by positivity) (by positivity)
    (by convert hEstimate using 1 <;> ring)
    (by simpa only [mul_assoc] using hAbsorb)
end Green64Analytic.CorrelationMellin

end

