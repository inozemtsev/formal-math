module

public import Green64.Library.Weights.RetiredFactorialMoment

@[expose] public section

/-!
# Analysis / Estimates / RetiredPrimeReturnHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRetiredPrimeReturnHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Polynomial
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

/-- Retired and unborn are different original seen states. Only the
retired state gets a new positive Hilbert weight. -/
def sourceOriginalRetiredAtomBase434 {R : Type} (V tau mu : ℝ) :
    SourceOriginalGhostReturnState434 R → ℝ
  | .unborn => 1
  | .pending _ => V*mu
  | .retired => tau*mu

def sourceOriginalRetiredAtomDegree434 {R : Type} :
    SourceOriginalGhostReturnState434 R → ℕ
  | .unborn => 0
  | .pending _ => 0
  | .retired => 1

def sourceOriginalRetiredAtomPolynomial434 {R : Type}
    (V tau mu : ℝ) (s : SourceOriginalGhostReturnState434 R) : ℝ[X] :=
  Polynomial.C (sourceOriginalRetiredAtomBase434 V tau mu s) *
    Polynomial.X ^ sourceOriginalRetiredAtomDegree434 s

private theorem return_sum {R A : Type} [Fintype R] [DecidableEq R] [AddCommMonoid A]
    (f : SourceOriginalGhostReturnState434 R → A) :
    (∑ s, f s) = f .unborn + f .retired + ∑ r : R, f (.pending r) := by
  change (∑ s ∈ insert .unborn
    (insert .retired (Finset.univ.image SourceOriginalGhostReturnState434.pending)), f s) = _
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_image (by intro a ha b hb h; exact SourceOriginalGhostReturnState434.pending.inj h)]
  ac_rfl

private def oneK {R : Type} [Fintype R] [DecidableEq R] (a : R) (eta lambda : ℝ)
    (s t : SourceOriginalGhostReturnState434 R) : ℂ :=
  sourceOriginalGhostReturnLiteralRow434 a eta lambda s
    (fun u => if u=t then 1 else 0)

private theorem one_norm {R : Type} [Fintype R] [DecidableEq R]
    (a : R) (eta lambda : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hl : 0 ≤ lambda) (s t : SourceOriginalGhostReturnState434 R) :
    ‖oneK a eta lambda s t‖ =
      match s with
      | .unborn => (if t=.unborn then 1 else 0) +
          (if t=.pending a then eta*lambda else 0)
      | .pending r => if r=a then
          (if t=.pending r then 1-eta else 0) +
          (if t=.retired then eta else 0)
          else (if t=.pending r then 1 else 0)
      | .retired => if t=.retired then 1 else 0 := by
  have hq : 0 ≤ 1-eta := sub_nonneg.mpr he1
  have hne : ‖(eta:ℂ)‖ = eta := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
  have hnl : ‖(lambda:ℂ)‖ = lambda := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hnq : ‖(1:ℂ)-(eta:ℂ)‖ = 1-eta := by
    rw [←Complex.ofReal_one, ←Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hq]
  cases s with
  | unborn =>
      cases t with
      | unborn => simp [oneK, source_original_GHOST_RETURN_literal_unborn434]
      | retired => simp [oneK, source_original_GHOST_RETURN_literal_unborn434]
      | pending r =>
          by_cases hr : r=a
          · subst r
            simp [oneK, source_original_GHOST_RETURN_literal_unborn434, norm_mul,
              hne, hnl, abs_of_nonneg he, abs_of_nonneg hl]
          · simp [oneK, source_original_GHOST_RETURN_literal_unborn434, hr, Ne.symm hr]
  | retired =>
      cases t <;> simp [oneK, source_original_GHOST_RETURN_literal_retired434]
  | pending r =>
      cases t with
      | unborn =>
          by_cases hr : r=a <;>
            simp [oneK, source_original_GHOST_RETURN_literal_pending434, hr]
      | retired =>
          by_cases hr : r=a <;>
            simp [oneK, source_original_GHOST_RETURN_literal_pending434, hr, hne, he]
      | pending t =>
          by_cases hr : r=a
          · subst r
            by_cases ht : t=a
            · subst t
              simp [oneK, source_original_GHOST_RETURN_literal_pending434, hnq]
            · simp [oneK, source_original_GHOST_RETURN_literal_pending434, ht, Ne.symm ht]
          · by_cases ht : r=t
            · subst t
              simp [oneK, source_original_GHOST_RETURN_literal_pending434, hr]
            · simp [oneK, source_original_GHOST_RETURN_literal_pending434, hr, ht, Ne.symm ht]

private theorem one_column_polynomial {R : Type} [Fintype R] [DecidableEq R]
    (a : R) (eta V tau mu : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hV : 0 ≤ V) (ht : 0 < tau) (hm : 0 ≤ mu)
    (t : SourceOriginalGhostReturnState434 R) :
    (∑ s, sourceOriginalRetiredAtomPolynomial434 V tau mu s *
      Polynomial.C ‖oneK a eta (V*mu) s t‖) =
      Polynomial.C (sourceOriginalRetiredAtomBase434 V tau mu t) *
        (Polynomial.C (eta*V/tau) + Polynomial.X)^sourceOriginalRetiredAtomDegree434 t := by
  rw [return_sum]
  simp_rw [one_norm a eta (V*mu) he he1 (mul_nonneg hV hm)]
  cases t with
  | unborn =>
      simp [sourceOriginalRetiredAtomPolynomial434, sourceOriginalRetiredAtomBase434,
        sourceOriginalRetiredAtomDegree434]
  | retired =>
      have hh : tau*mu*(eta*V/tau) = V*mu*eta := by
        field_simp <;> ring
      have hmif (j : R) :
          Polynomial.C (if j=a then eta else 0) =
            if j=a then Polynomial.C eta else (0 : ℝ[X]) := by
        by_cases hj : j=a <;> simp [hj]
      have hf : Polynomial.C (tau*mu)*Polynomial.X + Polynomial.C (V*mu*eta) =
          Polynomial.C (tau*mu)*(Polynomial.C (eta*V/tau)+Polynomial.X) := by
        rw [mul_add, ←Polynomial.C_mul, hh]
        ring
      simpa [sourceOriginalRetiredAtomPolynomial434, sourceOriginalRetiredAtomBase434,
        sourceOriginalRetiredAtomDegree434, hmif, mul_ite] using hf
  | pending r =>
      have hterm (j : R) :
          sourceOriginalRetiredAtomPolynomial434 V tau mu (.pending j) *
            Polynomial.C (if j=a then
              (if (SourceOriginalGhostReturnState434.pending r)=.pending j then 1-eta else 0) +
              (if (SourceOriginalGhostReturnState434.pending r)=.retired then eta else 0)
             else if (SourceOriginalGhostReturnState434.pending r)=.pending j then 1 else 0) =
          if j=r then Polynomial.C (V*mu*(if r=a then 1-eta else 1)) else 0 := by
        by_cases hj : j=r
        · subst j
          by_cases hr : r=a <;>
            simp [sourceOriginalRetiredAtomPolynomial434, sourceOriginalRetiredAtomBase434,
              sourceOriginalRetiredAtomDegree434, hr]
        · simp [sourceOriginalRetiredAtomPolynomial434, sourceOriginalRetiredAtomBase434,
            sourceOriginalRetiredAtomDegree434, hj, Ne.symm hj]
      simp_rw [hterm]
      by_cases hr : r=a
      · subst r
        simp [sourceOriginalRetiredAtomPolynomial434, sourceOriginalRetiredAtomBase434,
          sourceOriginalRetiredAtomDegree434]
        ring
      · simp [sourceOriginalRetiredAtomPolynomial434, sourceOriginalRetiredAtomBase434,
          sourceOriginalRetiredAtomDegree434, hr, Ne.symm hr]

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
local notation "H" => SourceOriginalPrimeReturnProductState434 modulus

/-- Factorial retired-register density on the ORIGINAL once-born
prime-return carrier. No histories are identified or discarded. -/
def sourceOriginalPrimeRetiredDensity434 (V tau : ℝ) (mu : P → ℝ) (s : H) : ℝ :=
  sourceOriginalRetiredMoment434
    (∏ p, sourceOriginalRetiredAtomPolynomial434 V tau (mu p) (s p))

theorem source_original_RETIRED_prime_density_exact434
    (V tau : ℝ) (mu : P → ℝ) (s : H) :
    sourceOriginalPrimeRetiredDensity434 modulus V tau mu s =
      (∏ p, sourceOriginalRetiredAtomBase434 V tau (mu p) (s p)) *
        ((∑ p, sourceOriginalRetiredAtomDegree434 (s p)).factorial : ℝ) := by
  unfold sourceOriginalPrimeRetiredDensity434 sourceOriginalRetiredAtomPolynomial434
  rw [Finset.prod_mul_distrib, ←map_prod, Finset.prod_pow_eq_pow_sum,
    source_original_RETIRED_moment_C_X_pow434]

theorem source_original_RETIRED_prime_density_nonneg434
    (V tau : ℝ) (mu : P → ℝ) (hV : 0 ≤ V) (ht : 0 ≤ tau)
    (hm : ∀ p, 0 ≤ mu p) (s : H) :
    0 ≤ sourceOriginalPrimeRetiredDensity434 modulus V tau mu s := by
  rw [source_original_RETIRED_prime_density_exact434]
  apply mul_nonneg _ (Nat.cast_nonneg _)
  apply Finset.prod_nonneg
  intro p hp
  cases s p <;> simp [sourceOriginalRetiredAtomBase434, mul_nonneg hV (hm p),
    mul_nonneg ht (hm p)]

/-- The exact weighted column of the real once-born G. Its
retired-history cost is exp(eta*V/tau), with no pool-size factor. -/
theorem source_original_RETIRED_prime_G_column434
    (shift : ℤ) (eta V tau : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hV : 0 ≤ V) (ht : 0 < tau)
    (hm : ∀ p, 0 ≤ mu p) (t : H) :
    (∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
      ‖∏ p, sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖) ≤
    Real.exp (eta*V/tau) * sourceOriginalPrimeRetiredDensity434 modulus V tau mu t := by
  let b := ∏ p, sourceOriginalRetiredAtomBase434 V tau (mu p) (t p)
  let r := ∑ p, sourceOriginalRetiredAtomDegree434 (t p)
  have hb : 0 ≤ b := by
    apply Finset.prod_nonneg
    intro p hp
    cases t p <;> simp [sourceOriginalRetiredAtomBase434, mul_nonneg hV (hm p),
      mul_nonneg ht.le (hm p)]
  have hpoly :
      (∑ s : H, (∏ p, sourceOriginalRetiredAtomPolynomial434 V tau (mu p) (s p)) *
        Polynomial.C ‖∏ p,
          sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖) =
      Polynomial.C b * (Polynomial.C (eta*V/tau) + Polynomial.X)^r := by
    simp only [norm_prod, map_prod, ←Finset.prod_mul_distrib]
    have hsep := (Fintype.prod_sum (fun p
      (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) =>
        sourceOriginalRetiredAtomPolynomial434 V tau (mu p) s *
          Polynomial.C ‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu s (t p)‖)).symm
    rw [hsep]
    have hh (p : P) :
        (∑ s : SourceOriginalGhostReturnState434 (ZMod (modulus p)),
          sourceOriginalRetiredAtomPolynomial434 V tau (mu p) s *
            Polynomial.C ‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu s (t p)‖) =
        Polynomial.C (sourceOriginalRetiredAtomBase434 V tau (mu p) (t p)) *
          (Polynomial.C (eta*V/tau)+Polynomial.X)^sourceOriginalRetiredAtomDegree434 (t p) :=
      one_column_polynomial _ eta V tau (mu p) he he1 hV ht (hm p) (t p)
    simp_rw [hh]
    rw [Finset.prod_mul_distrib, ←map_prod, Finset.prod_pow_eq_pow_sum]
  have hmom := congrArg sourceOriginalRetiredMoment434 hpoly
  simp only [map_sum] at hmom
  have hterm (s : H) :
      sourceOriginalRetiredMoment434
        ((∏ p, sourceOriginalRetiredAtomPolynomial434 V tau (mu p) (s p)) *
          Polynomial.C ‖∏ p,
            sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖) =
      sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
        ‖∏ p, sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖ := by
    rw [mul_comm, source_original_RETIRED_moment_C_mul434, mul_comm]
    rfl
  simp_rw [hterm] at hmom
  rw [hmom, source_original_RETIRED_moment_C_mul434,
    source_original_RETIRED_prime_density_exact434]
  have hh := mul_le_mul_of_nonneg_left
    (source_original_RETIRED_shifted_power_bound434 (eta*V/tau)
      (div_nonneg (mul_nonneg he hV) ht.le) r) hb
  simpa only [b, r, mul_assoc, mul_left_comm, mul_comm] using hh

/-- Arbitrary complex futures in the new, explicitly stated density.
This is proved from both actual Schur budgets, without transferring
a previous Hilbert estimate between different densities. -/
theorem source_original_RETIRED_prime_G_Hilbert434
    (shift : ℤ) (eta V tau : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hV : 0 ≤ V) (ht : 0 < tau)
    (hm : ∀ p, 0 ≤ mu p) (F : H → ℂ) :
    (∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
      ‖sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F‖^2) ≤
    ((∏ p, (1+eta*(V*mu p))) * Real.exp (eta*V/tau)) *
      ∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s * ‖F s‖^2 := by
  let D := sourceOriginalPrimeRetiredDensity434 modulus V tau mu
  let K := fun (s t : H) =>
    ∏ p, sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)
  let A := fun s t => D s * ‖K s t‖
  let M := ∏ p, (1+eta*(V*mu p))
  let C := Real.exp (eta*V/tau)
  have hD := source_original_RETIRED_prime_density_nonneg434 modulus V tau mu hV ht.le hm
  have hA (s t : H) : 0 ≤ A s t := mul_nonneg (hD s) (norm_nonneg _)
  have hM : 0 ≤ M := Finset.prod_nonneg (fun p hp =>
    add_nonneg zero_le_one (mul_nonneg he (mul_nonneg hV (hm p))))
  have hr (s : H) : (∑ t, A s t) ≤ M*D s := by
    dsimp only [A]
    rw [←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left
      (source_original_PRIME_RETURN_G_row434 modulus shift eta V mu he he1
        (fun p => mul_nonneg hV (hm p)) s) (hD s)).trans_eq (mul_comm _ _)
  have hc (t : H) : (∑ s, A s t) ≤ C*D t :=
    source_original_RETIRED_prime_G_column434 modulus shift eta V tau mu he he1 hV ht hm t
  have hf (s : H) :
      D s * ‖sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F‖ ≤
        ∑ t, A s t * ‖F t‖ := by
    change D s * ‖∑ t, K s t * F t‖ ≤ _
    calc
      _ ≤ D s * ∑ t, ‖K s t * F t‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hD s)
      _ = _ := by simp only [norm_mul, Finset.mul_sum, A, mul_assoc]
  exact source_original_finite_density_kernel_energy434 Finset.univ D hD A hA
    M C hM (fun s hs => hr s) (fun t ht => hc t) F
    (fun s => sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F)
    (fun s hs => hf s)

/-- Literal numeric physical G, with its full pending multiset and
seen register, in the factorial retired-history density. -/
theorem source_original_NUMERIC_PRIME_POOL_G_retired_Hilbert434
    (shift : ℤ) (eta V tau : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hV : 0 ≤ V) (ht : 0 < tau)
    (hm : ∀ p, 0 ≤ mu p) (hi : Function.Injective modulus)
    (external : Finset ℕ) (hext : ∀ p, modulus p ∉ external)
    (F : Multiset (Green64Fock.Atom P modulus) → Finset ℕ → ℂ) :
    (∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
      ‖sourceOriginalPhysicalNumericPrimePoolG434 modulus eta V mu
        (sourceOriginalPrimeProductPending434 modulus shift s)
        (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus) F‖^2) ≤
    ((∏ p, (1+eta*(V*mu p))) * Real.exp (eta*V/tau)) *
      ∑ s : H, sourceOriginalPrimeRetiredDensity434 modulus V tau mu s *
        ‖F (sourceOriginalPrimeProductPending434 modulus shift s)
          (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus)‖^2 := by
  simp_rw [source_original_NUMERIC_PRIME_POOL_G_return_matrix434
    modulus shift _ hi external hext]
  exact source_original_RETIRED_prime_G_Hilbert434 modulus shift eta V tau mu he he1 hV ht hm _

end Green64Analytic.CorrelationSquare

end

end

