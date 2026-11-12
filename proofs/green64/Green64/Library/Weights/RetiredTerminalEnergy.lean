module

public import Green64.Library.Analysis.Estimates.RetiredPrimeReturnHilbert
public import Green64.Library.Weights.Part060

@[expose] public section

/-!
# Weights / RetiredTerminalEnergy

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRetiredTerminalEnergy -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Polynomial Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false

private theorem return_sum {R A : Type} [Fintype R] [DecidableEq R] [AddCommMonoid A]
    (f : SourceOriginalGhostReturnState434 R → A) :
    (∑ s, f s) = f .unborn + f .retired + ∑ r : R, f (.pending r) := by
  change (∑ s ∈ insert .unborn
    (insert .retired (Finset.univ.image SourceOriginalGhostReturnState434.pending)), f s) = _
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_image (by intro a ha b hb h; exact SourceOriginalGhostReturnState434.pending.inj h)]
  ac_rfl

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
local notation "H" => SourceOriginalPrimeReturnProductState434 modulus

/-- No initial history penalty: all yet-unborn prime coordinates
have density exactly one, for the same finite physical carrier. -/
theorem source_original_RETIRED_unborn_density434
    (V tau : ℝ) (mu : P → ℝ) :
    sourceOriginalPrimeRetiredDensity434 modulus V tau mu (fun _ => .unborn) = 1 := by
  simp [source_original_RETIRED_prime_density_exact434,
    sourceOriginalRetiredAtomBase434, sourceOriginalRetiredAtomDegree434]

/-- Exact vacuum history mass, including every distinct retired
set. The finite factorial partition is kept before any estimate. -/
theorem source_original_RETIRED_vacuum_mass_exact434
    (V tau : ℝ) (mu : P → ℝ) :
    (∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
      ∏ p, sourceOriginalGhostReturnVacuum434 (s p)) =
    sourceOriginalRetiredMoment434
      (∏ p, ((1 : ℝ[X]) + Polynomial.C (tau*mu p)*Polynomial.X)) := by
  have hm (s : H) :
      sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
        (∏ p, sourceOriginalGhostReturnVacuum434 (s p)) =
      sourceOriginalRetiredMoment434
        ((∏ p, sourceOriginalRetiredAtomPolynomial434 V tau (mu p) (s p)) *
          Polynomial.C (∏ p, sourceOriginalGhostReturnVacuum434 (s p))) := by
    rw [mul_comm _ (Polynomial.C _), source_original_RETIRED_moment_C_mul434, mul_comm]
    rfl
  simp_rw [hm]
  rw [←map_sum]
  congr 1
  simp only [map_prod, ←Finset.prod_mul_distrib]
  have hsep := (Fintype.prod_sum (fun p
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) =>
      sourceOriginalRetiredAtomPolynomial434 V tau (mu p) s *
        Polynomial.C (sourceOriginalGhostReturnVacuum434 s))).symm
  rw [hsep]
  apply Finset.prod_congr rfl
  intro p hp
  rw [return_sum]
  simp [sourceOriginalRetiredAtomPolynomial434, sourceOriginalRetiredAtomBase434,
    sourceOriginalRetiredAtomDegree434, sourceOriginalGhostReturnVacuum434]

/-- True numerical terminal histories with arbitrary bounded joint
complex observation. No sum is replaced by independent samples. -/
theorem source_original_NUMERIC_RETIRED_terminal_energy434
    (V tau : ℝ) (mu : P → ℝ) (hV : 0 ≤ V) (ht : 0 < tau)
    (hm : ∀ p, 0 ≤ mu p) (hM : tau * (∑ p, mu p) < 1)
    (shift : ℤ) (external : Finset ℕ)
    (F : Finset ℕ → ℂ) (hF : ∀ seen, ‖F seen‖ ≤ 1) :
    (∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
      ‖if sourceOriginalPrimeProductPending434 modulus shift s = 0 then
        F (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus)
       else 0‖^2) ≤ 1 / (1-tau*(∑ p, mu p)) := by
  have hsq (s : H) :
      ‖if sourceOriginalPrimeProductPending434 modulus shift s = 0 then
        F (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus)
       else 0‖^2 ≤ ∏ p, sourceOriginalGhostReturnVacuum434 (s p) := by
    have hh := source_original_PRIME_PRODUCT_joint_vacuum_majorant434 modulus shift s
      (fun seen => F (external ∪ seen.image modulus))
      (fun seen => hF (external ∪ seen.image modulus))
    have hid : (∏ p, sourceOriginalGhostReturnVacuum434 (s p))^2 =
        ∏ p, sourceOriginalGhostReturnVacuum434 (s p) := by
      rw [pow_two, ←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      cases s p <;> norm_num [sourceOriginalGhostReturnVacuum434]
    have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
    rw [hid] at hs
    exact hs
  calc
    _ ≤ ∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
        ∏ p, sourceOriginalGhostReturnVacuum434 (s p) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hsq s)
        (source_original_RETIRED_prime_density_nonneg434 modulus V tau mu hV ht.le hm s)
    _ = _ := source_original_RETIRED_vacuum_mass_exact434 modulus V tau mu
    _ ≤ _ := by
      have h := source_original_RETIRED_partition_bound434 Finset.univ
        (fun p => tau*mu p) (fun p hp => mul_nonneg ht.le (hm p))
        (by simpa only [←Finset.mul_sum] using hM)
      simpa only [←Finset.mul_sum] using h

/-- The terminal physical G/vacuum vector, with the REAL numerical
no-rebirth gate, has the same finite geometric boundary budget. -/
theorem source_original_NUMERIC_RETIRED_terminal_G_energy434
    (eta V tau : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hV : 0 ≤ V) (ht : 0 < tau)
    (hm : ∀ p, 0 ≤ mu p) (hM : tau * (∑ p, mu p) < 1)
    (shift : ℤ) (hi : Function.Injective modulus)
    (external : Finset ℕ) (hext : ∀ p, modulus p ∉ external)
    (F : Finset ℕ → ℂ) (hF : ∀ seen, ‖F seen‖ ≤ 1) :
    (∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
      ‖sourceOriginalPhysicalNumericPrimePoolG434 modulus eta V mu
        (sourceOriginalPrimeProductPending434 modulus shift s)
        (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus)
        (fun out seen => if out=0 then F seen else 0)‖^2) ≤
    ((∏ p, (1+eta*(V*mu p))) * Real.exp (eta*V/tau)) /
      (1-tau*(∑ p, mu p)) := by
  have hK : 0 ≤ (∏ p, (1+eta*(V*mu p))) * Real.exp (eta*V/tau) := by
    apply mul_nonneg _ (Real.exp_pos _).le
    exact Finset.prod_nonneg (fun p hp =>
      add_nonneg zero_le_one (mul_nonneg he (mul_nonneg hV (hm p))))
  calc
    _ ≤ ((∏ p, (1+eta*(V*mu p))) * Real.exp (eta*V/tau)) *
        ∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
          ‖if sourceOriginalPrimeProductPending434 modulus shift s=0 then
            F (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus)
           else 0‖^2 :=
      source_original_NUMERIC_PRIME_POOL_G_retired_Hilbert434 modulus shift eta V tau mu
        he he1 hV ht hm hi external hext
        (fun (out : Multiset (Atom P modulus)) (seen : Finset ℕ) =>
          if out=0 then F seen else 0)
    _ ≤ ((∏ p, (1+eta*(V*mu p))) * Real.exp (eta*V/tau)) *
        (1/(1-tau*(∑ p, mu p))) :=
      mul_le_mul_of_nonneg_left
        (source_original_NUMERIC_RETIRED_terminal_energy434 modulus V tau mu
          hV ht hm hM shift external F hF) hK
    _ = _ := by ring

end Green64Analytic.CorrelationSquare

end

end

