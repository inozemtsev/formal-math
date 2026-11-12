module

public import Green64.Library.Weights.NumericRestrictedPool
public import Green64.Library.Weights.Part018

@[expose] public section

/-!
# Correlation / PrimeReturnHilbertSchur

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPrimeReturnHilbertSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The pending weight is V*mu, as in the existing physical OLD
sector density. Unborn and retired remain distinct seen states. -/
def sourceOriginalReturnPendingMass434 {R : Type} (lambda : ℝ) :
    SourceOriginalGhostReturnState434 R → ℝ
  | .unborn => 1
  | .pending _ => lambda
  | .retired => 1

private def singleK {R : Type} [Fintype R] [DecidableEq R]
    (a : R) (eta lambda : ℝ)
    (s t : SourceOriginalGhostReturnState434 R) : ℂ :=
  sourceOriginalGhostReturnLiteralRow434 a eta lambda s
    (fun u => if u=t then 1 else 0)

private theorem return_sum {R : Type} [Fintype R] [DecidableEq R]
    (f : SourceOriginalGhostReturnState434 R → ℝ) :
    (∑ s, f s) = f .unborn + f .retired + ∑ r : R, f (.pending r) := by
  change (∑ s ∈ insert .unborn
    (insert .retired (Finset.univ.image SourceOriginalGhostReturnState434.pending)),
      f s) = _
  rw [Finset.sum_insert (by simp),Finset.sum_insert (by simp),
    Finset.sum_image (by intro a ha b hb h; exact SourceOriginalGhostReturnState434.pending.inj h)]
  ring

private theorem single_norm {R : Type} [Fintype R] [DecidableEq R]
    (a : R) (eta lambda : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hl : 0 ≤ lambda) (s t : SourceOriginalGhostReturnState434 R) :
    ‖singleK a eta lambda s t‖ =
      match s with
      | .unborn => (if t=.unborn then 1 else 0) +
          (if t=.pending a then eta*lambda else 0)
      | .pending r => if r=a then
          (if t=.pending r then 1-eta else 0) +
          (if t=.retired then eta else 0)
          else (if t=.pending r then 1 else 0)
      | .retired => if t=.retired then 1 else 0 := by
  have hq : 0 ≤ 1-eta := sub_nonneg.mpr he1
  have hne : ‖(eta:ℂ)‖ = eta := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he]
  have hnl : ‖(lambda:ℂ)‖ = lambda := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl]
  have hnq : ‖(1:ℂ)-(eta:ℂ)‖ = 1-eta := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq]
  cases s with
  | unborn =>
      cases t with
      | unborn => simp [singleK,source_original_GHOST_RETURN_literal_unborn434]
      | retired => simp [singleK,source_original_GHOST_RETURN_literal_unborn434]
      | pending r =>
          by_cases hr : r=a
          · subst r
            simp [singleK,source_original_GHOST_RETURN_literal_unborn434,norm_mul,hne,hnl,
              abs_of_nonneg he,abs_of_nonneg hl]
          · simp [singleK,source_original_GHOST_RETURN_literal_unborn434,hr,Ne.symm hr]
  | retired =>
      cases t <;> simp [singleK,source_original_GHOST_RETURN_literal_retired434]
  | pending r =>
      cases t with
      | unborn =>
          by_cases hr : r=a <;>
            simp [singleK,source_original_GHOST_RETURN_literal_pending434,hr]
      | retired =>
          by_cases hr : r=a <;>
            simp [singleK,source_original_GHOST_RETURN_literal_pending434,hr,hne,he]
      | pending t =>
          by_cases hr : r=a
          · subst r
            by_cases ht : t=a
            · subst t
              simp [singleK,source_original_GHOST_RETURN_literal_pending434,hnq]
            · simp [singleK,source_original_GHOST_RETURN_literal_pending434,ht,Ne.symm ht]
          · by_cases ht : r=t
            · subst t
              simp [singleK,source_original_GHOST_RETURN_literal_pending434,hr]
            · simp [singleK,source_original_GHOST_RETURN_literal_pending434,hr,ht,Ne.symm ht]

/-- True literal once-born G: its absolute row cost has no residue
count or history count. The test can be an arbitrary joint future. -/
theorem source_original_RETURN_G_row434
    {R : Type} [Fintype R] [DecidableEq R]
    (a : R) (eta lambda : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hl : 0 ≤ lambda) (s : SourceOriginalGhostReturnState434 R) :
    (∑ t : SourceOriginalGhostReturnState434 R,
      ‖sourceOriginalGhostReturnLiteralRow434 a eta lambda s
        (fun u => if u=t then 1 else 0)‖) ≤ 1+eta*lambda := by
  change (∑ t, ‖singleK a eta lambda s t‖) ≤ _
  simp_rw [single_norm a eta lambda he he1 hl]
  cases s with
  | unborn => simp [Finset.sum_add_distrib]
  | retired => simp [mul_nonneg he hl]
  | pending r =>
      by_cases hr : r=a
      · simp [hr,Finset.sum_add_distrib,mul_nonneg he hl]
      · simp [hr,mul_nonneg he hl]

/-- Weighted column in the same pending mass lambda. In particular
the numerical seen register adds no column multiplicity factor. -/
theorem source_original_RETURN_G_column434
    {R : Type} [Fintype R] [DecidableEq R]
    (a : R) (eta lambda : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hl : 0 ≤ lambda) (t : SourceOriginalGhostReturnState434 R) :
    (∑ s : SourceOriginalGhostReturnState434 R,
      sourceOriginalReturnPendingMass434 lambda s *
      ‖sourceOriginalGhostReturnLiteralRow434 a eta lambda s
        (fun u => if u=t then 1 else 0)‖) ≤
    (1+eta*lambda)*sourceOriginalReturnPendingMass434 lambda t := by
  change (∑ s,sourceOriginalReturnPendingMass434 lambda s*
    ‖singleK a eta lambda s t‖) ≤ _
  rw [return_sum]
  simp_rw [single_norm a eta lambda he he1 hl]
  cases t with
  | unborn =>
      simp [sourceOriginalReturnPendingMass434,mul_nonneg he hl]
  | retired =>
      simp [sourceOriginalReturnPendingMass434,mul_ite,Finset.sum_ite_eq',
        mul_comm]
  | pending r =>
      have hterm (j : R) :
          sourceOriginalReturnPendingMass434 lambda (.pending j) *
            (if j=a then
              (if (SourceOriginalGhostReturnState434.pending r)=.pending j then 1-eta else 0) +
              (if (SourceOriginalGhostReturnState434.pending r)=.retired then eta else 0)
             else if (SourceOriginalGhostReturnState434.pending r)=.pending j then 1 else 0) =
          if j=r then lambda*(if r=a then 1-eta else 1) else 0 := by
        by_cases hj : j=r
        · subst j
          simp [sourceOriginalReturnPendingMass434]
        · simp [sourceOriginalReturnPendingMass434,hj,Ne.symm hj]
      simp_rw [hterm]
      have hprod : 0 ≤ eta*lambda^2 := mul_nonneg he (sq_nonneg lambda)
      by_cases hr : r=a
      · subst r
        simp [sourceOriginalReturnPendingMass434]
        nlinarith
      · simp [sourceOriginalReturnPendingMass434,hr,Ne.symm hr]
        nlinarith

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Product of the genuine pending masses; no normalization of seen
and no replacement by independently resampled histories. -/
def sourceOriginalPrimeReturnDensity434
    (V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalPrimeReturnProductState434 modulus) : ℝ :=
  ∏ p,sourceOriginalReturnPendingMass434 (V*mu p) (s p)

private theorem density_nonneg (V : ℝ) (mu : P → ℝ)
    (hl : ∀ p,0 ≤ V*mu p) (s : SourceOriginalPrimeReturnProductState434 modulus) :
    0 ≤ sourceOriginalPrimeReturnDensity434 modulus V mu s := by
  apply Finset.prod_nonneg
  intro p hp
  cases s p <;> simp [sourceOriginalReturnPendingMass434,hl p]

/-- Actual simultaneous prime-return matrix row, with all common
numeric history tests still allowed in the continuation. -/
theorem source_original_PRIME_RETURN_G_row434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hl : ∀ p,0 ≤ V*mu p)
    (s : SourceOriginalPrimeReturnProductState434 modulus) :
    (∑ t : SourceOriginalPrimeReturnProductState434 modulus,
      ‖∏ p,sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖) ≤
      ∏ p, (1+eta*(V*mu p)) := by
  simp_rw [norm_prod]
  have hs : (∑ t : SourceOriginalPrimeReturnProductState434 modulus,
      ∏ p,‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖) =
      ∏ p,∑ t : SourceOriginalGhostReturnState434 (ZMod (modulus p)),
        ‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) t‖ := by
    convert (Fintype.prod_sum (fun p (t : SourceOriginalGhostReturnState434 (ZMod (modulus p))) =>
      ‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) t‖)).symm using 1
  rw [hs]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact Finset.sum_nonneg (fun t ht => norm_nonneg _)
  · intro p hp
    exact source_original_RETURN_G_row434
      (-(shift : ZMod (modulus p))) eta (V*mu p) he he1 (hl p) (s p)

/-- Actual weighted column for the entire prime-return product. -/
theorem source_original_PRIME_RETURN_G_column434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hl : ∀ p,0 ≤ V*mu p)
    (t : SourceOriginalPrimeReturnProductState434 modulus) :
    (∑ s : SourceOriginalPrimeReturnProductState434 modulus,
      sourceOriginalPrimeReturnDensity434 modulus V mu s *
      ‖∏ p,sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖) ≤
      (∏ p, (1+eta*(V*mu p)))*
        sourceOriginalPrimeReturnDensity434 modulus V mu t := by
  simp only [sourceOriginalPrimeReturnDensity434,norm_prod,←Finset.prod_mul_distrib]
  have hs : (∑ s : SourceOriginalPrimeReturnProductState434 modulus,
      ∏ p,sourceOriginalReturnPendingMass434 (V*mu p) (s p) *
        ‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)‖) =
      ∏ p,∑ s : SourceOriginalGhostReturnState434 (ZMod (modulus p)),
        sourceOriginalReturnPendingMass434 (V*mu p) s *
          ‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu s (t p)‖ := by
    convert (Fintype.prod_sum (fun p (s : SourceOriginalGhostReturnState434 (ZMod (modulus p))) =>
      sourceOriginalReturnPendingMass434 (V*mu p) s *
        ‖sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu s (t p)‖)).symm using 1
  rw [hs]
  apply Finset.prod_le_prod₀
  · intro p hp
    apply Finset.sum_nonneg
    intro s hs
    apply mul_nonneg _ (norm_nonneg _)
    cases s <;> simp [sourceOriginalReturnPendingMass434,hl p]
  · intro p hp
    exact source_original_RETURN_G_column434
      (-(shift : ZMod (modulus p))) eta (V*mu p) he he1 (hl p) (t p)

/-- Hilbert bound for the exact numerical no-rebirth G matrix, for
EVERY complex future F, without a bounded-mask assumption. -/
theorem source_original_PRIME_RETURN_G_Hilbert434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hl : ∀ p,0 ≤ V*mu p)
    (F : SourceOriginalPrimeReturnProductState434 modulus → ℂ) :
    (∑ s : SourceOriginalPrimeReturnProductState434 modulus,
      sourceOriginalPrimeReturnDensity434 modulus V mu s *
      ‖sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F‖^2) ≤
    (∏ p,(1+eta*(V*mu p)))^2 *
      ∑ s : SourceOriginalPrimeReturnProductState434 modulus,
        sourceOriginalPrimeReturnDensity434 modulus V mu s * ‖F s‖^2 := by
  let D := sourceOriginalPrimeReturnDensity434 modulus V mu
  let K : SourceOriginalPrimeReturnProductState434 modulus →
      SourceOriginalPrimeReturnProductState434 modulus → ℂ :=
    fun s t => ∏ p,sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p)
  let A := fun s t => D s*‖K s t‖
  let M := ∏ p,(1+eta*(V*mu p))
  have hD := density_nonneg modulus V mu hl
  have hA (s t) : 0 ≤ A s t := mul_nonneg (hD s) (norm_nonneg _)
  have hM : 0 ≤ M := Finset.prod_nonneg
    (fun p hp => by nlinarith [mul_nonneg he (hl p)])
  have hr (s) : (∑ t,A s t) ≤ M*D s := by
    dsimp only [A]
    rw [←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left
      (source_original_PRIME_RETURN_G_row434 modulus shift eta V mu he he1 hl s)
      (hD s)).trans_eq (mul_comm _ _)
  have hc (t) : (∑ s,A s t) ≤ M*D t :=
    source_original_PRIME_RETURN_G_column434 modulus shift eta V mu he he1 hl t
  have ht (s) :
      D s*‖sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F‖ ≤
        ∑ t,A s t*‖F t‖ := by
    change D s*‖∑ t,K s t*F t‖ ≤ _
    calc
      _ ≤ D s*(∑ t,‖K s t*F t‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hD s)
      _ = _ := by
        simp only [norm_mul,Finset.mul_sum,A,mul_assoc]
  simpa only [pow_two,D,M] using
    (source_original_finite_density_kernel_energy434 Finset.univ D hD A hA
      M M hM (fun s hs => hr s) (fun t ht => hc t)
      F (fun s => sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu F)
      (fun s hs => ht s))

/-- This applies to the literal numerical physical pool G, with its
original pending multisets and numerical seen. F is unrestricted.
The measure is displayed as the exact return-coordinate product;
identifying the full active/orbit disintegration is a separate bridge. -/
theorem source_original_NUMERIC_PRIME_POOL_G_Hilbert434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (hl : ∀ p,0 ≤ V*mu p)
    (hi : Function.Injective modulus) (external : Finset ℕ)
    (hext : ∀ p,modulus p ∉ external)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    (∑ s : SourceOriginalPrimeReturnProductState434 modulus,
      sourceOriginalPrimeReturnDensity434 modulus V mu s *
      ‖sourceOriginalPhysicalNumericPrimePoolG434 modulus eta V mu
        (sourceOriginalPrimeProductPending434 modulus shift s)
        (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus) F‖^2) ≤
    (∏ p,(1+eta*(V*mu p)))^2 *
      ∑ s : SourceOriginalPrimeReturnProductState434 modulus,
        sourceOriginalPrimeReturnDensity434 modulus V mu s *
        ‖F (sourceOriginalPrimeProductPending434 modulus shift s)
          (external ∪ (sourceOriginalPrimeProductSeen434 modulus s).image modulus)‖^2 := by
  simp_rw [source_original_NUMERIC_PRIME_POOL_G_return_matrix434
    modulus shift _ hi external hext]
  exact source_original_PRIME_RETURN_G_Hilbert434 modulus shift eta V mu he he1 hl _

end Green64Analytic.CorrelationSquare

end

end

