module

public import Green64.Library.Weights.Part037
public import Green64.Library.Weights.FineAlpha
public import Green64.Library.Weights.Part102

@[expose] public section

/-!
# Weights / ParityFineInputs

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ActualParityFineInputs -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

private theorem b647_minfac_support_of_actual_alpha434
    (prime : Bool) (L S b : ℝ) (l u n : ℕ) (hl : 2 ≤ l)
    (hR : SourceRoughAbove n (Real.exp (Real.sqrt L)))
    (hn : b629ActualFineAlpha434 prime L S b l u n ≠ 0) :
    sourceD20Rough (Real.exp (Real.sqrt L)) n := by
  have hc : n ∈ Finset.Icc l u := by
    by_contra hnot
    apply hn
    simp only [b629ActualFineAlpha434, hnot, ite_false]
  have hn2 : 2 ≤ n := hl.trans (Finset.mem_Icc.mp hc).1
  exact ⟨hn2, hR n.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)⟩

/-- The actual Parity cofactor coefficient has all original discrepancy and
literal minFac-support fields, together with genuine prime/rough full-cell
density. One density constant precedes the requested discrepancy precision
and every fine mesh S. No coefficient, density or discrepancy premise. -/
theorem b647_actual_parity_fine_alpha_inputs434
    (b A B ε : ℝ) (hb : 0 < b) (hsmall : b ≤ A/100)
    (hAB : A ≤ B) (hB : B < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D S : ℝ, 0 < D → 2*D < S →
      ∀ᶠ L : ℝ in atTop, ∀ (prime : Bool) (l u : ℕ),
        u ≤ 2*l → Real.exp (A*L) ≤ (l:ℝ) → (u:ℝ) ≤ Real.exp (B*L) →
        let alpha := b629ActualFineAlpha434 prime L S b l u
        SourceAlphaDiscrepancy L D (Real.exp L) alpha ∧
        (∀ n : ℕ, ‖alpha n‖ ≤ 1 ∧
          (alpha n ≠ 0 → sourceD20Rough (Real.exp (Real.sqrt L)) n)) ∧
        (∀ n ∈ Finset.Icc l u,
          0 ≤ b647ActualFineProxy434 prime L S b n ∧
          b647ActualFineProxy434 prime L S b n ≤
            C/(L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)) := by
  obtain ⟨C,hC,hDensity⟩ := b647_actual_prime_or_rough_proxy_density434
    b A B ε hb hsmall hAB hB hε
  refine ⟨C,hC,?_⟩
  intro D S hD hS
  have hSpos : 0 < S := by linarith
  have hA : 0 < A := by linarith
  filter_upwards [hDensity S hSpos,
    b629_actual_fine_source_discrepancy434 D S A b hD hS hA hb,
    b629_actual_fine_coefficient_and_rough_support434 S A b hSpos hA hb,
    eventually_gt_atTop (0:ℝ)] with L hdensity hdisc hcoeff hL
  intro prime l u hu hlow hhigh
  have hl1 : (1:ℝ) < l :=
    (Real.one_lt_exp_iff.mpr (mul_pos hA hL)).trans_le hlow
  have hl : 2 ≤ l := by
    have h : 1 < l := by exact_mod_cast hl1
    omega
  have hu2 : (u:ℝ) ≤ Real.exp (2*L) := hhigh.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith : B ≤ 2) hL.le))
  refine ⟨hdisc prime l u hl hu hlow hu2, ?_, ?_⟩
  · intro n
    have hn := hcoeff prime l u hlow n
    exact ⟨hn.1, fun hnonzero => b647_minfac_support_of_actual_alpha434
      prime L S b l u n hl (hn.2 hnonzero) hnonzero⟩
  · intro n hn
    exact hdensity prime n
      (hlow.trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1))
      ((Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans hhigh)

/-- Insert the actual canonical signed alpha into the complete Parity F/G
physical correlation. The old generic rough-support premise is discharged.
The same alpha, conjugations, both ordinary cofactors, both true prime-slot
remainders, P weights, common parity sign, shift 2k and exterior Z remain. -/
theorem b647_actual_fine_parity_physical_correlation434
    (S beta b : ℝ) (hS : 0 < S) (hbeta : 0 < beta) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, ∀ (prime : Bool) (l u : ℕ),
      Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (cfg : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
        (tw : Bool) (residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
        (lo hi : ℕ) (xi1 xi2 xi3 rho sigma Z bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ),
        Z ≠ 0 →
        (∀ j p, p ∈ P j → p.Prime) →
        (∀ j p, p ∈ P j → (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
        let alpha := b629ActualFineAlpha434 prime L S b l u
        b633ParitySeparatedCorrelation434 cfg g P tw alpha residual q chi lo hi
          xi1 xi2 xi3 rho sigma Z bPsi k psi =
        (Z:ℂ)*sourceCorrelationTwoTwists cfg g P
          (b633ParityEFirstCore434 alpha residual q chi lo hi xi2 rho sigma)
          (b633ParitySecondCore434 alpha residual q chi lo hi xi1 rho sigma)
          tw tw Z (rho+xi3) (-rho) bPsi (2*k) (fun t => (t:ℂ)*psi t) := by
  filter_upwards [b629_actual_fine_coefficient_and_rough_support434
      S beta b hS hbeta hb, eventually_gt_atTop (0:ℝ)] with L hcoeff hL
  intro prime l u hlow cfg g P tw residual q chi lo hi xi1 xi2 xi3 rho sigma Z bPsi k psi
    hZ hp hW
  have hl1 : (1:ℝ) < l :=
    (Real.one_lt_exp_iff.mpr (mul_pos hbeta hL)).trans_le hlow
  have hl : 2 ≤ l := by
    have h : 1 < l := by exact_mod_cast hl1
    omega
  apply b633_parity_actual_harmonic_correlation434 cfg g P (Real.exp (Real.sqrt L))
    tw (b629ActualFineAlpha434 prime L S b l u) residual q chi lo hi
    xi1 xi2 xi3 rho sigma Z bPsi k psi hZ hp hW
  intro n hn
  exact b647_minfac_support_of_actual_alpha434 prime L S b l u n hl
    ((hcoeff prime l u hlow n).2 hn) hn
end Green64Analytic.Parity

end

end

