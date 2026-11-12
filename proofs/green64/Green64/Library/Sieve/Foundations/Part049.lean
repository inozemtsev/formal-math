module

public import Green64.Library.Sieve.Foundations.Part048
public import Green64.Library.Sieve.Foundations.Part044
public import Green64.Library.Sieve.Foundations.Part045
public import Green64.Library.Sieve.Foundations.Part034
public import Green64.Library.Sieve.Foundations.Part036
public import Green64.Library.Sieve.Foundations.Part037
public import Green64.Library.Sieve.Foundations.Part008
public import Green64.Library.Sieve.Foundations.Part046

@[expose] public section

/-!
# Sieve / Foundations / Part049

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## QuarterFullCellGlobalAudit -/

section



end

/-! ## QuarterFullCellB629ActualSourceSum -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- Exact original §7.3 full-cell prime/rough proxy source over the
positive whole K interval equals the finite sum, over ACTUAL
quarter-product binary dyad cuts, of sources with the true b629
prime/rough fine coefficient on each literal nested Kcut.
This is an IDENTITY OF THE ORIGINAL COMPLETE FINITE TRIPLE, and
uses no abstract family bound, no per-cut analytic saving, no
recalculated full-cell proxy B_I and no assumption on beta.
No original Q/P/signed source weights are dropped. -/
theorem parity_original_actual_fullcell_triple_eq_quarter_b629_cut_sources434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c)
    (prime : Bool) (S gamma : ℝ) (beta : ℕ → ℂ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      (Finset.Icc a b) (Finset.Icc c e)
      (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
      beta Y =
    ∑ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434
          (Finset.Icc a b) (Finset.Icc c e) Y)).filter
          (parityOriginalTypeIIQuarterProductGate434 L),
      parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
        (b629ActualFineAlpha434 prime L S gamma
          (max a scale.1) (min b (2*scale.1-1)))
        beta Y := by
  classical
  rw [parity_original_TypeII_positive_Icc_triple_eq_quarter_nested_cuts434
    d L Psi hL hPsi a b c e Y ha hc
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
    beta]
  apply Finset.sum_congr rfl
  intro scale hs
  apply parity_original_TypeII_triple_alpha_congr_on_K434
  intro m hm
  have hLow : a ≤ max a scale.1 := le_max_left _ _
  have hUpper : min b (2*scale.1-1)≤b := min_le_left _ _
  have hProxy := parity_original_actual_fullcell_proxy_nested_interval_eq434
    prime L S gamma a b (max a scale.1) (min b (2*scale.1-1))
    m hLow hUpper
  have hB629 := parity_original_actual_full_dyad_proxy_eq_b629434
    prime L S gamma (max a scale.1) (min b (2*scale.1-1)) m
  have hh := hProxy.symm.trans hB629
  simpa only [restrictSequence,hm,ite_true] using hh
end Green64Analytic.Parity

end

end

/-! ## SignedFullCellB629CutSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Full original signed factorial/epsilon Mellin source is invariant
under alpha replacing only when the two actual coefficient functions
agree ON its genuine K support; no signed subsum bound, no assumption
about source Q/P or beta normalization. -/
theorem parity_original_signed_source_alpha_congr_on_K434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha alpha' beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ)
    (hAlpha : ∀m∈K,alpha m=alpha' m) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha beta signed rho Y =
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J alpha' beta signed rho Y := by
  classical
  unfold parityOriginalShiftTwoSignedBilinearMellinSource434
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  have hP := (Finset.mem_filter.mp hz).1
  have hm := (Finset.mem_product.mp hP).1
  rw [hAlpha z.1 hm]

/-- Native ORIGINAL Parity §7.3 whole full-cell prime/rough SIGNED
source (actual 20! factorial, ε sign, rho Mellin phase) is exactly
the sum over physically attained quarter dyad K/J nested Icc cuts
with the genuine native b629 fine alpha on each cut, retaining the
same original source full-cell B_I values and unchanged beta.
This closes the actual SIGNED carrier identity; it is stronger than
the earlier separately checked unsigned sourceOriginalA equality. -/
theorem parity_original_signed_fullcell_eq_quarter_b629_cut_sources434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (a b c e Y : ℕ) (ha : 0<a) (hc : 0<c)
    (prime : Bool) (S gamma : ℝ) (beta : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
      (Finset.Icc a b) (Finset.Icc c e)
      (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
      beta signed rho Y =
    ∑ scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
        (parityOriginalTypeIIPhysicalPairs434
          (Finset.Icc a b) (Finset.Icc c e) Y)).filter
          (parityOriginalTypeIIQuarterProductGate434 L),
      parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
        (restrictSequence
          (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
          (b629ActualFineAlpha434 prime L S gamma
            (max a scale.1) (min b (2*scale.1-1))))
        beta signed rho Y := by
  classical
  rw [parity_original_signed_positive_Icc_eq_quarter_nested_sources434
    d L Psi hL hPsi a b c e Y ha hc
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
    beta signed rho]
  apply Finset.sum_congr rfl
  intro scale hs
  apply parity_original_signed_source_alpha_congr_on_K434
  intro m hm
  -- The attained literal scale is a power of two; rewrite its
  -- original historical `Nat.log` to this same true source scale.
  have hAttained := (Finset.mem_filter.mp hs).1
  obtain ⟨z,hz,hScale⟩ := Finset.mem_image.mp hAttained
  have hScaleM : scale.1 = 2^(Nat.log 2 z.1) := by
    exact (congrArg Prod.fst hScale).symm
  have hPower : 2^(Nat.log 2 scale.1) = scale.1 := by
    rw [hScaleM]
    have hp := Nat.log_pow (by norm_num : 1<2) (Nat.log 2 z.1)
    simpa only [hp]
  have hh := parity_original_actual_quarter_fullcell_alpha_eq_b629_cut434
    prime L S gamma a b (Nat.log 2 scale.1) m
  simp only [pow_succ,hPower,mul_comm] at hh
  have hmAlt : m ∈ Finset.Icc (max a scale.1) (min b (scale.1*2-1)) := by
    simpa only [mul_comm (2:ℕ) scale.1] using hm
  have hEq :
      parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b m =
      b629ActualFineAlpha434 prime L S gamma
        (max a scale.1) (min b (2*scale.1-1)) m := by
    simpa only [restrictSequence,hmAlt,ite_true,
      mul_comm (2:ℕ) scale.1] using hh
  simpa only [restrictSequence,hm,ite_true] using hEq
end Green64Analytic.Parity

end

end

/-! ## TwoFactorReplacementNormBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- The second original nonsmooth factor replacement is paid
separately by its *own* legitimate source bound, rather than
assuming smoothness of the already replaced B1 or an invalid
signed-subsum inequality. This is an unconditional triangle
ledger conditional ONLY on the TWO explicit source estimates. -/
theorem parity_original_signed_two_factor_proxy_replacement_norm_ledger434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (sharpM proxyM sharpN proxyN : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ)
    (M1 M2 : ℝ)
    (hFirst : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J (fun m => sharpM m - proxyM m) sharpN
      signed rho Y‖ ≤ M1)
    (hSecond : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxyM (fun n => sharpN n - proxyN n)
      signed rho Y‖ ≤ M2) :
    ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J sharpM sharpN signed rho Y -
      parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxyM proxyN signed rho Y‖ ≤ M1+M2 := by
  rw [parity_original_signed_two_factor_proxy_telescoping434]
  exact (norm_add_le _ _).trans (add_le_add hFirst hSecond)

/-- The general original unsigned Parity(4.2) second-replacement
norm ledger is distinct from signed factorial source (above).
No claim the latter implies unrestricted arbitrary-alpha TypeII. -/
theorem parity_original_unsigned_two_factor_proxy_replacement_norm_ledger434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (sharpM proxyM sharpN proxyN : ℕ → ℂ)
    (Y : ℕ) (M1 M2 : ℝ)
    (hFirst : ‖parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J (fun m => sharpM m - proxyM m) sharpN Y‖ ≤ M1)
    (hSecond : ‖parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J proxyM (fun n => sharpN n - proxyN n) Y‖ ≤ M2) :
    ‖parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J sharpM sharpN Y -
      parityOriginalShiftTwoOriginalTypeIITripleSource434
      d L Psi K J proxyM proxyN Y‖ ≤ M1+M2 := by
  rw [parity_original_unsigned_two_factor_proxy_telescoping434]
  exact (norm_add_le _ _).trans (add_le_add hFirst hSecond)

/-- If both original first- and second-factor source discrepancies
carry the SAME arbitrary inverse-log precision, the total is at
most twice the same error. This holds without claiming either
individual premise has been discharged for the full §7.3 family. -/
theorem parity_original_signed_two_factor_proxy_two_error_paid434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (sharpM proxyM sharpN proxyN : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ)
    (C : ℝ) (hFirst : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J (fun m => sharpM m - proxyM m) sharpN
      signed rho Y‖ ≤ C)
    (hSecond : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxyM (fun n => sharpN n - proxyN n)
      signed rho Y‖ ≤ C) :
    ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J sharpM sharpN signed rho Y -
      parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxyM proxyN signed rho Y‖ ≤ 2*C := by
  have h := parity_original_signed_two_factor_proxy_replacement_norm_ledger434
    d L Psi K J sharpM proxyM sharpN proxyN signed rho Y C C
    hFirst hSecond
  nlinarith
end Green64Analytic.Parity

end

end

/-! ## SecondProxyOrientationPaid -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2300000

/-- Exact source algebra: the original signed second replacement
against an ALREADY nonsmooth first proxy B1 is TWICE the true
source with factors exchanged and B1/2 as bounded beta. All
original signed epsilon factorial Q/P/Mellin arithmetic intact. -/
theorem parity_original_signed_second_proxy_swapped_half_exact434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (proxyM deltaN : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxyM deltaN signed rho Y =
    2 * parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi J K deltaN (fun m => proxyM m/(2:ℂ)) signed rho Y := by
  rw [parity_original_signed_source_swap_factors434]
  unfold parityOriginalShiftTwoSignedBilinearMellinSource434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hPair :
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 J K u,
        deltaN z.1 * proxyM z.2) =
      2 * (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 J K u,
        deltaN z.1 * (proxyM z.2/(2:ℂ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hPair]
  ring

/-- Source-true second-replacement analytic orientation rule:
if the ORIGINAL signed b629 discrepancy on the switched second
factor has a uniform norm bound M when its beta coefficient is
B1/2, then the actual original second replacement is ≤2M.
The bound on the swapped source is an EXPLICIT premise, not an
unproved global arbitrary-alpha Parity(4.2) claim. -/
theorem parity_original_signed_second_proxy_swapped_half_norm_paid434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (proxyM deltaN : ℕ → ℂ)
    (signed : Bool) (rho : ℝ) (Y : ℕ)
    (M : ℝ)
    (hSwapped : ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi J K deltaN (fun m => proxyM m/(2:ℂ)) signed rho Y‖ ≤ M) :
    ‖parityOriginalShiftTwoSignedBilinearMellinSource434
      d L Psi K J proxyM deltaN signed rho Y‖ ≤ 2*M := by
  rw [parity_original_signed_second_proxy_swapped_half_exact434]
  rw [norm_mul]
  have hTwo : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
  rw [hTwo]
  exact mul_le_mul_of_nonneg_left hSwapped (by norm_num)
end Green64Analytic.Parity

end

end

/-! ## UnbalancedPhysicalFactorGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The true original Parity §7.3 UNBALANCED physical factor range:
if the real smooth source Ψ(u/exp L) is nonzero, h=-2 means
m*n=u+2, and the smaller factor n is in its actual source window
exp(b1 L)≤n≤exp((1/2−κ)L), then the larger factor m lies between
exp((1/2+κ)L) and 4 exp((1−b1)L). Unlike an abstract x-scale
intuition, the upper constant 4 pays the literal shifted +2 and
compact Ψ support [1,2]. No η, β, test proxy or source family
cardinality is assumed. -/
theorem parity_original_unbalanced_true_physical_factor_range434
    (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (m n u : ℕ)
    (hEq : m*n=u+2)
    (hNonzero : Psi ((u:ℝ)/Real.exp L)≠0)
    (hNlower : Real.exp (b1*L)≤(n:ℝ))
    (hNupper : (n:ℝ)≤Real.exp ((1/2-kappa)*L)) :
    Real.exp ((1/2+kappa)*L)≤(m:ℝ) ∧
      (m:ℝ)≤4*Real.exp ((1-b1)*L) := by
  have hePos : 0<Real.exp L := Real.exp_pos _
  have heOne : 1≤Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  have hPsiWindow : (u:ℝ)/Real.exp L∈Set.Icc 1 2 :=
    hPsi (by simpa only [Function.mem_support] using hNonzero)
  have huLower : Real.exp L≤(u:ℝ) :=
    by simpa only [one_mul] using (le_div_iff₀ hePos).mp (Set.mem_Icc.mp hPsiWindow).1
  have huUpper : (u:ℝ)≤2*Real.exp L :=
    (div_le_iff₀ hePos).mp (Set.mem_Icc.mp hPsiWindow).2
  have hProd : (m:ℝ)*(n:ℝ)=(u:ℝ)+2 := by
    exact_mod_cast hEq
  have hProdLower : Real.exp L≤(m:ℝ)*(n:ℝ) := by
    linarith
  have hProdUpper : (m:ℝ)*(n:ℝ)≤4*Real.exp L := by
    linarith
  have hNpos : 0<(n:ℝ) :=
    lt_of_lt_of_le (Real.exp_pos _) hNlower
  have hMp : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hLowFactor :
      Real.exp ((1/2+kappa)*L)*Real.exp ((1/2-kappa)*L)=Real.exp L := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hUpperFactor :
      Real.exp ((1-b1)*L)*Real.exp (b1*L)=Real.exp L := by
    rw [←Real.exp_add]
    congr 1
    ring
  constructor
  · by_contra h
    have hmSmall : (m:ℝ)<Real.exp ((1/2+kappa)*L) := lt_of_not_ge h
    have hnProd := mul_le_mul_of_nonneg_left hNupper hMp
    have hmProd := mul_lt_mul_of_pos_right hmSmall hNpos
    nlinarith [hnProd,hmProd,hLowFactor,hProdLower]
  · by_contra h
    have hmBig : 4*Real.exp ((1-b1)*L)<(m:ℝ) := lt_of_not_ge h
    have hnProd := mul_le_mul_of_nonneg_left hNlower hMp
    have hmProd := mul_lt_mul_of_pos_right hmBig (Real.exp_pos (b1*L))
    nlinarith [hnProd,hmProd,hUpperFactor,hProdUpper]
end Green64Analytic.Parity

end

end

/-! ## UnbalancedActivePhysicalCarrier -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Original unbalanced §7.3 SMALL factor interval, retaining its
real exp(b1 L) and exp((1/2−κ)L) endpoints exactly. -/
def parityOriginalUnbalancedSmallFactor434 (L b1 kappa : ℝ) (n : ℕ) : Prop :=
  Real.exp (b1*L) ≤ (n:ℝ) ∧
  (n:ℝ) ≤ Real.exp (((1/2:ℝ)-kappa)*L)

/-- Actual positive shifted unbalanced pair with a nonzero smooth
source value for at least one real supported u: the physical
carrier used by the original weighted TypeII, not all hypothetical
factor pairs satisfying interval exponents. -/
def parityOriginalUnbalancedActivePhysicalPairs434
    (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (Y : ℕ) : Finset (ℕ×ℕ) :=
  (parityOriginalTypeIIPhysicalPairs434 K
    (J.filter (parityOriginalUnbalancedSmallFactor434 L b1 kappa)) Y).filter
      (fun z => ∃ u ∈ Finset.Ioc 0 Y,
        z.1*z.2=u+2 ∧ Psi ((u:ℝ)/Real.exp L)≠0)

/-- Original complete unsigned TypeII source with n in its native
small-factor unbalanced band equals the exact signed/complex
source restricted to ACTUALLY Psi-active positive shifted pairs.
Inactive physical pairs have zero source terms separately. No
u=0, nonphysical m,n or surrogate smooth weights are inserted. -/
theorem parity_original_unbalanced_triple_eq_active_physical_pairs434
    (d : ℕ) (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      K (J.filter (parityOriginalUnbalancedSmallFactor434 L b1 kappa))
      alpha beta Y =
    ∑ z ∈ parityOriginalUnbalancedActivePhysicalPairs434
        L b1 kappa Psi K J Y,
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0 := by
  classical
  rw [parity_original_TypeII_triple_eq_physical_pair_restriction434]
  unfold parityOriginalUnbalancedActivePhysicalPairs434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hActive : ∃ u ∈ Finset.Ioc 0 Y,
      z.1*z.2=u+2 ∧ Psi ((u:ℝ)/Real.exp L)≠0
  · simp only [if_pos hActive]
  · simp only [if_neg hActive]
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hEq : 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2
    · have hZero : Psi ((u:ℝ)/Real.exp L)=0 := by
        by_contra hNonzero
        exact hActive ⟨u,hu,hEq.2.2,hNonzero⟩
      simp [hEq,hZero]
    · simp [hEq]

/-- EVERY source Psi-active original unbalanced factor pair lies
inside the large-factor range of pinned Parity §7.3, with the true
fixed +2 shift and upper containing factor four. -/
theorem parity_original_unbalanced_active_pairs_true_large_factor_range434
    (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (z : ℕ×ℕ)
    (hz : z ∈ parityOriginalUnbalancedActivePhysicalPairs434
      L b1 kappa Psi K J Y) :
    Real.exp (((1/2:ℝ)+kappa)*L) ≤ (z.1:ℝ) ∧
    (z.1:ℝ) ≤ 4*Real.exp ((1-b1)*L) := by
  classical
  unfold parityOriginalUnbalancedActivePhysicalPairs434 at hz
  simp only [Finset.mem_filter] at hz
  obtain ⟨hPair,⟨u,hu,hShift,hNonzero⟩⟩ := hz
  unfold parityOriginalTypeIIPhysicalPairs434 at hPair
  simp only [Finset.mem_filter] at hPair
  have hJN := (Finset.mem_product.mp hPair.1).2
  have hn := (Finset.mem_filter.mp hJN).2
  exact parity_original_unbalanced_true_physical_factor_range434
    L b1 kappa Psi hL hPsi z.1 z.2 u hShift hNonzero hn.1 hn.2
end Green64Analytic.Parity

end

end

/-! ## UniformFourierBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 32000

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_B633_full_fourier_fixed_chi_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs))
          (rho xi1 xi2 xi3 U : ℝ)
          (ζ : EuclideanSpace ℝ (Fin 3)),
          0 < U → |rho| ≤ L^Cfreq →
          |xi1+2*Real.pi*(ζ 0)| ≤ L^Cfreq →
          |xi2+2*Real.pi*(ζ 1)| ≤ L^Cfreq →
          |xi3+2*Real.pi*(ζ 2)| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
          L band slot delta freq (Finset.Icc a b)
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let original := parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N F.alpha F.residual
          (2*k.natAbs) chi F.lo F.hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨Kpsi,hKpsi,hPsiBudget⟩ :=
    parity_original_historical_fixed_smooth_dyadic_psi_log_budget434
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_actual_original_Parity417_physical_cofactor_saving_common_precision434
      jQ target Cfreq CZ Ck 0 Kpsi
      hTarget hCZ hCk (by norm_num) hKpsi
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hSave := hSave beta gamma hbeta hgamma
  filter_upwards [hSave,eventually_ge_atTop (1:ℝ)] with L hSaveL hL
  refine ⟨hSaveL.1,hSaveL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L
    band slot delta freq (Finset.Icc a b)
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let psi : ℝ → ℂ := parityOriginalHistoricalDyadicSmoothPsi434
  let original := parityOriginalHistoricalActualB633FullFourierCofactor434
    L rho xi1 xi2 xi3 U Z k N F.alpha F.residual
    (2*k.natAbs) chi F.lo F.hi signed psi ζ
  let shifted := parityOriginalEq417PhysicalCofactors434
    L rho (xi1+2*Real.pi*(ζ 0)) (xi2+2*Real.pi*(ζ 1))
      (xi3+2*Real.pi*(ζ 2)) 0 Z k N F.alpha F.residual
      (2*k.natAbs) chi F.lo F.hi signed psi
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL
  have hZpos : 0 < Z := by
    have h : 0 < Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos _)
    exact h.trans_le hZlo
  have hN : ∀ z∈N,0 < z := by
    intro z hz
    exact (Finset.mem_Icc.mp hz).1
  have h0 : |(0:ℝ)| ≤ L^Cfreq := by
    simpa only [abs_zero] using (Real.rpow_nonneg hLpos.le Cfreq)
  have hBound : ‖shifted‖ ≤ Z*L^(-target) :=
    hSaveL.2.2 hFamily Z hZlo hZhi band hband slot delta freq
      k hk hkBound chi rho
      (xi1+2*Real.pi*(ζ 0)) (xi2+2*Real.pi*(ζ 1))
      (xi3+2*Real.pi*(ζ 2)) 0 hrho hxi1 hxi2 hxi3 h0
      prime lFine uFine a b hFineLow hl hu hub signed psi
      parity_original_historical_dyadic_smooth_psi_contDiff434
      parity_original_historical_dyadic_psi_Parity417_support434
      (hPsiBudget L)
  have hExp : original =
      parityOriginalHistoricalB633ThreeFourierScale434 U Z ζ * shifted := by
    dsimp [original,shifted]
    rw [parity_original_historical_actual_B633_full_cofactor_fourier_shift434
      L rho xi1 xi2 xi3 U Z k N hN F.alpha F.residual
      (2*k.natAbs) chi F.lo F.hi signed psi ζ hU hZpos]
    congr 1
  change ‖original‖ ≤ Z*L^(-target)
  rw [hExp,norm_mul,parity_original_historical_B633_three_fourier_scale_norm_one434,one_mul]
  exact hBound

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_B633_full_chi_fourier_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (rho xi1 xi2 xi3 U : ℝ)
          (ζ : EuclideanSpace ℝ (Fin 3)),
          0 < U → |rho| ≤ L^Cfreq →
          |xi1+2*Real.pi*(ζ 0)| ≤ L^Cfreq →
          |xi2+2*Real.pi*(ζ 1)| ≤ L^Cfreq →
          |xi3+2*Real.pi*(ζ 2)| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let F : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq (Finset.Icc a b)
            (b629ActualFineAlpha434 prime L S gamma lFine uFine)
            (2*k.natAbs) chi 0 0
        let original := ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            parityOriginalHistoricalActualB633FullFourierCofactor434
              L rho xi1 xi2 xi3 U Z k N (F chi).alpha (F chi).residual
              (2*k.natAbs) chi (F chi).lo (F chi).hi signed
              parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hEachL⟩ :=
    parity_eventually_original_actual_B633_full_fourier_fixed_chi_saving_common_precision434
      jQ target Cfreq CZ Ck hTarget hCZ hCk
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hEachL := hEachL beta gamma hbeta hgamma
  filter_upwards [hEachL,eventually_ge_atTop (1:ℝ)] with L hEachL hL
  refine ⟨hEachL.1,hEachL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let F : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq (Finset.Icc a b)
      (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      (2*k.natAbs) chi 0 0
  let W : DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun chi =>
    parityOriginalHistoricalActualB633FullFourierCofactor434
      L rho xi1 xi2 xi3 U Z k N (F chi).alpha (F chi).residual
      (2*k.natAbs) chi (F chi).lo (F chi).hi signed
      parityOriginalHistoricalDyadicSmoothPsi434 ζ
  have hAll (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      ‖W chi‖ ≤ Z*L^(-target) := by
    exact hEachL.2.2 hFamily Z hZlo hZhi band hband slot delta freq
      k hk hkBound chi rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
      prime lFine uFine a b hFineLow hl hu hub signed
  have hZpos : 0 < Z := by
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL
    have h : 0 < Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos _)
    exact h.trans_le hZlo
  have hM : 0 ≤ Z*L^(-target) :=
    (mul_nonneg hZpos.le (Real.rpow_nonneg (le_trans (by norm_num : (0:ℝ)≤1) hL) _))
  change ‖∑ chi : DirichletCharacter ℂ (2*k.natAbs),
    parityShiftTwoMaskCoefficient434 k.natAbs chi * W chi‖ ≤ Z*L^(-target)
  calc
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        ‖parityShiftTwoMaskCoefficient434 k.natAbs chi * W chi‖ := norm_sum_le _ _
    _ ≤ ∑ chi : DirichletCharacter ℂ (2*k.natAbs),
        ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖ * (Z*L^(-target)) := by
          apply Finset.sum_le_sum
          intro chi hchi
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hAll chi) (norm_nonneg _)
    _ = (Z*L^(-target)) *
        (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs chi‖) := by
          rw [←Finset.sum_mul]
          ring
    _ ≤ (Z*L^(-target))*1 :=
      mul_le_mul_of_nonneg_left
        (parity_signed_shift_two_mask_coefficient_mass_le_one434 k hk) hM
    _ = _ := mul_one _

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_B509_source_core_full_chi_fourier_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (rho xi1 xi2 xi3 U : ℝ)
          (ζ : EuclideanSpace ℝ (Fin 3)),
          0 < U → |rho| ≤ L^Cfreq →
          |xi1+2*Real.pi*(ζ 0)| ≤ L^Cfreq →
          |xi2+2*Real.pi*(ζ 1)| ≤ L^Cfreq →
          |xi3+2*Real.pi*(ζ 2)| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq K alpha (2*k.natAbs) chi 0 0
        let original := ∑chi : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs chi *
            parityOriginalHistoricalActualB633FullFourierCofactor434
              L rho xi1 xi2 xi3 U Z k N alpha
              (sourceF chi).residual (2*k.natAbs) chi
              (sourceF chi).lo (sourceF chi).hi signed
              parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_original_actual_B633_full_chi_fourier_saving_common_precision434
      jQ target Cfreq CZ Ck hTarget hCZ hCk
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hSave := hSave beta gamma hbeta hgamma
  filter_upwards [hSave] with L hSaveL
  refine ⟨hSaveL.1,hSaveL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let K := Finset.Icc a b
  let raw := b629ActualFineAlpha434 prime L S gamma lFine uFine
  let alpha := restrictSequence K raw
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq K alpha (2*k.natAbs) chi 0 0
  let rawF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq K raw (2*k.natAbs) chi 0 0
  have hCore (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      sourceF chi=rawF chi :=
    parity_original_native_source_B509_core_double_fine_restrict_eq_raw434
      20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq K raw
      (2*k.natAbs) chi 0 0
  have hAlpha (chi : DirichletCharacter ℂ (2*k.natAbs)) :
      (rawF chi).alpha=alpha := rfl
  have hSourceRaw :
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          parityOriginalHistoricalActualB633FullFourierCofactor434
            L rho xi1 xi2 xi3 U Z k N alpha
            (sourceF chi).residual (2*k.natAbs) chi
            (sourceF chi).lo (sourceF chi).hi signed
            parityOriginalHistoricalDyadicSmoothPsi434 ζ) =
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
          parityOriginalHistoricalActualB633FullFourierCofactor434
            L rho xi1 xi2 xi3 U Z k N (rawF chi).alpha
            (rawF chi).residual (2*k.natAbs) chi
            (rawF chi).lo (rawF chi).hi signed
            parityOriginalHistoricalDyadicSmoothPsi434 ζ) := by
    apply Finset.sum_congr rfl
    intro chi hchi
    rw [hCore chi, hAlpha chi]
  have hRawSave := hSaveL.2.2 hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U ζ hU hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  change ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N alpha
          (sourceF chi).residual (2*k.natAbs) chi
          (sourceF chi).lo (sourceF chi).hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ‖ ≤ Z*L^(-target)
  rw [hSourceRaw]
  exact hRawSave

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_B509_source_core_full_chi_fourier_ball_saving_common_precision434
    (jQ : ℕ) (target Cfreq CZ Ck : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (rho xi1 xi2 xi3 U : ℝ) (T : ℝ)
          (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)),
          0 < U → |rho| ≤ L^Cfreq →
          (∀ ζ : EuclideanSpace ℝ (Fin 3), ‖ζ‖ ≤ T →
            |xi1+2*Real.pi*(ζ 0)| ≤ L^Cfreq ∧
            |xi2+2*Real.pi*(ζ 1)| ≤ L^Cfreq ∧
            |xi3+2*Real.pi*(ζ 2)| ≤ L^Cfreq) →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq K alpha (2*k.natAbs) chi 0 0
        let original : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
          ∑chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
              parityOriginalHistoricalActualB633FullFourierCofactor434
                L rho xi1 xi2 xi3 U Z k N alpha
                (sourceF chi).residual (2*k.natAbs) chi
                (sourceF chi).lo (sourceF chi).hi signed
                parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * original ζ‖ ≤
          (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f := by
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_original_actual_B509_source_core_full_chi_fourier_saving_common_precision434
      jQ target Cfreq CZ Ck hTarget hCZ hCk
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hSave := hSave beta gamma hbeta hgamma
  filter_upwards [hSave,eventually_ge_atTop (1:ℝ)] with L hSaveL hL
  refine ⟨hSaveL.1,hSaveL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U T f hU hrho hFrequencies
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
      L band slot delta freq K alpha (2*k.natAbs) chi 0 0
  let G : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
    ∑chi : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs chi *
        parityOriginalHistoricalActualB633FullFourierCofactor434
          L rho xi1 xi2 xi3 U Z k N alpha
          (sourceF chi).residual (2*k.natAbs) chi
          (sourceF chi).lo (sourceF chi).hi signed
          parityOriginalHistoricalDyadicSmoothPsi434 ζ
  have hCont : Continuous G := by
    dsimp only [G]
    apply continuous_finset_sum
    intro chi hchi
    exact continuous_const.mul
      (parity_original_actual_B633_full_fourier_cofactor_continuous434
        L rho xi1 xi2 xi3 U Z k N alpha (sourceF chi).residual
        (2*k.natAbs) chi (sourceF chi).lo (sourceF chi).hi
        signed parityOriginalHistoricalDyadicSmoothPsi434)
  have hZpos : 0 < Z := by
    have hLpos : 0 < L := by linarith
    have hh : 0 < Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos _)
    exact hh.trans_le hZlo
  have hM : 0 ≤ Z*L^(-target) :=
    mul_nonneg hZpos.le (Real.rpow_nonneg (by linarith : 0≤L) _)
  have hPoint (ζ : EuclideanSpace ℝ (Fin 3)) (hζ : ‖ζ‖≤T) :
      ‖G ζ‖≤Z*L^(-target) := by
    obtain ⟨h1,h2,h3⟩ := hFrequencies ζ hζ
    have hSaved := hSaveL.2.2 hFamily Z hZlo hZhi band hBand slot delta freq
      k hk hkBound rho xi1 xi2 xi3 U ζ hU hrho h1 h2 h3
      prime lFine uFine a b hFineLow hl hu hub signed
    exact hSaved
  change ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
    (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * G ζ‖ ≤
    (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f
  exact parity_original_signed_continuous_ball_source_moment434
    f G T (Z*L^(-target)) hM hCont hPoint

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_B509_full_chi_polynomial_ball_saving_common_precision434
    (jQ : ℕ) (target C0 Cf CZ Ck : ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (rho xi1 xi2 xi3 U T : ℝ)
          (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)),
          0 < U → T ≤ L^Cf →
          |rho| ≤ L^C0 → |xi1| ≤ L^C0 →
          |xi2| ≤ L^C0 → |xi3| ≤ L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine →
          (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (signed : Bool),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let N := Finset.Icc 1 ⌊64*Z⌋₊
        let sourceF : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
          sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L)
            L band slot delta freq K alpha (2*k.natAbs) chi 0 0
        let original : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
          ∑chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
              parityOriginalHistoricalActualB633FullFourierCofactor434
                L rho xi1 xi2 xi3 U Z k N alpha
                (sourceF chi).residual (2*k.natAbs) chi
                (sourceF chi).lo (sourceF chi).hi signed
                parityOriginalHistoricalDyadicSmoothPsi434 ζ
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖ ≤ T} : Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * original ζ‖ ≤
          (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f := by
  let Cfreq : ℝ := max C0 (Cf+1)+1
  obtain ⟨J,B,S,hSB,hSave⟩ :=
    parity_eventually_original_actual_B509_source_core_full_chi_fourier_ball_saving_common_precision434
      jQ target Cfreq CZ Ck hTarget hCZ hCk
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hSave := hSave beta gamma hbeta hgamma
  filter_upwards [hSave,eventually_ge_atTop (8:ℝ)] with L hSaveL hL
  refine ⟨hSaveL.1,hSaveL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U T f hU hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  dsimp only
  have hRho : |rho|≤L^Cfreq := by
    have he : C0 ≤ Cfreq := by dsimp [Cfreq]; linarith [le_max_left C0 (Cf+1)]
    exact hrho.trans (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤L) he)
  have hFrequencies (ζ : EuclideanSpace ℝ (Fin 3)) (hζ : ‖ζ‖≤T) :
      |xi1+2*Real.pi*(ζ 0)|≤L^Cfreq ∧
      |xi2+2*Real.pi*(ζ 1)|≤L^Cfreq ∧
      |xi3+2*Real.pi*(ζ 2)|≤L^Cfreq := by
    exact parity_original_real_3d_all_shifted_poly_ball434
      L C0 Cf xi1 xi2 xi3 T hL hT hxi1 hxi2 hxi3 ζ hζ
  exact hSaveL.2.2 hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U T f hU hRho hFrequencies
    prime lFine uFine a b hFineLow hl hu hub signed

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_Bprime_full_odd_lowfreq_le_integrated_417_plus_two_ghost_common_precision434
    (jQ : ℕ) (target C0 Cf CZ Ck : ℝ)
    (hTarget : 0 < target) (hCZ : 0≤CZ) (hCk : 0≤Ck) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 8≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → 0<T → T≤L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 →
          |xi2|≤L^C0 → |xi3|≤L^C0 →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (buf : ℝ → ℂ) (smoothLo smoothHi : ℝ)
          (hSmooth : ContDiff ℝ ∞ buf)
          (hBufSupport : ∀x:ℝ,buf x≠0 → smoothLo ≤ x ∧ x ≤ smoothHi)
          (H : ℕ),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf smoothLo smoothHi hSmooth hBufSupport
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                A (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
        (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f +
          2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  obtain ⟨J,B,S,hSB,hFourier⟩ :=
    parity_eventually_original_actual_B509_full_chi_polynomial_ball_saving_common_precision434
      jQ target C0 Cf CZ Ck hTarget hCZ hCk
  refine ⟨J,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hFourier := hFourier beta gamma hbeta hgamma
  have hS : 0<S := by
    have hb : 0≤(B:ℝ) := Nat.cast_nonneg B
    linarith
  have hSource :=
    parity_eventually_original_actual_Bprime_all_m_unmasked_ball_le_eq417_plus_two_ghost434
      S beta gamma Ck hS hbeta hgamma
  filter_upwards [hFourier,hSource,eventually_ge_atTop (8:ℝ)]
    with L hFourierL hSourceL hL
  refine ⟨hL,hFourierL.1,hFourierL.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hE hV hT hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
    buf smoothLo smoothHi hSmooth hBufSupport H
  classical
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let d := sourceOriginalLiteralDepth 20 L
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let A : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf smoothLo smoothHi hSmooth hBufSupport
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  have hZ : 0<Z := by
    have hLp : 0<L := by linarith
    have hh : 0<Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp _)
    exact hh.trans_le hZlo
  have hB := hSourceL.2 hLw prime lFine uFine hl hFineLow K k hk hkBound
    d band slot delta freq rho xi1 xi2 xi3 U E V Z signed
    hU hE hV hZ hDyad hkZ
    buf smoothLo smoothHi hSmooth hBufSupport H T hT
  have hSave := hFourierL.2.2 hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U T f hU hTCut hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu hub signed
  let Fχ : DirichletCharacter ℂ (2*k.natAbs) → PrimeSlotCore := fun chi =>
    sourceNativePrimeCore 20 d L band slot delta freq K alpha
      (2*k.natAbs) chi 0 0
  let Hχ : DirichletCharacter ℂ (2*k.natAbs) →
      EuclideanSpace ℝ (Fin 3) → ℂ := fun chi ζ =>
    parityOriginalHistoricalActualB633FullFourierCofactor434
      L rho xi1 xi2 xi3 U Z k N alpha (Fχ chi).residual
      (2*k.natAbs) chi (Fχ chi).lo (Fχ chi).hi signed
      parityOriginalHistoricalDyadicSmoothPsi434 ζ
  let c : DirichletCharacter ℂ (2*k.natAbs) → ℂ :=
    fun chi => parityShiftTwoMaskCoefficient434 k.natAbs chi
  have hCont (chi : DirichletCharacter ℂ (2*k.natAbs)) : Continuous (Hχ chi) :=
    parity_original_actual_B633_full_fourier_cofactor_continuous434
      L rho xi1 xi2 xi3 U Z k N alpha (Fχ chi).residual
      (2*k.natAbs) chi (Fχ chi).lo (Fχ chi).hi signed
      parityOriginalHistoricalDyadicSmoothPsi434
  have hSwap := parity_original_full_character_fourier_ball_fubini434
    f T c Hχ hCont
  -- Both inequalities are defined on precisely the same raw K,
  -- sorted source core and complete unrestricted 2|k| character family.
  -- In particular the ghosts are retained at exactly their old source mass.
  dsimp only at hB hSave hSwap ⊢
  calc
    _ ≤ ‖∑chi : DirichletCharacter ℂ (2*k.natAbs),
          c chi * (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * Hχ chi ζ)‖ +
        2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
            convert hB using 1
    _ = ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
            (∑chi : DirichletCharacter ℂ (2*k.natAbs),
              c chi * Hχ chi ζ)‖ +
        2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
            rw [hSwap]
    _ ≤ (Z*L^(-target))*parityOriginal3DSourceMomentFiniteBudget434 0 f +
        2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
            exact add_le_add_left hSave _

end Green64Analytic.Parity

end

end

/-! ## UniformQuarterBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 32000

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_Bprime_lowfreq_primary_normalized_two_ghost_quarter_common_precision434
    (jQ : ℕ) (D C0 Cf CZ Ck K0 Cbox A R : ℝ)
    (hD : 0<D) (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V →
          E=U*L^(-K0) → Z≤24*Cbox*Real.exp L*L^(K0+88) →
          0<T → T≤L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (H : ℕ),
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                At (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
        Cmoment*Z*L^(-D) +
          2*((L^(2*parityOriginalW1PolylogExponent434)*
            ((Nat.ceil (65*Z):ℕ):ℝ)*
            (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
          (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let p0 : ℝ := 5*(K0+90)*((P:ℝ)+1)
  have hp0 : 0≤p0 := by
    have hK : 0≤K0+90 := by linarith
    have hp : 0≤(P:ℝ) := Nat.cast_nonneg _
    dsimp [p0]
    positivity
  have hTarget : 0<D+p0 := by linarith
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_full_odd_lowfreq_le_integrated_417_plus_two_ghost_common_precision434
      jQ (D+p0) C0 Cf CZ Ck hTarget hCZ hCk
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hMain := hMain beta gamma hbeta hgamma
  let BE : ℝ := 2*A*(P.factorial:ℝ)
  let BN : ℝ := 32*A^2*(P.factorial:ℝ)*(2:ℝ)^P+(P.factorial:ℝ)*A
  filter_upwards [hMain,eventually_ge_atTop (32:ℝ),eventually_ge_atTop (6*Cbox),
    eventually_ge_atTop BE,eventually_ge_atTop BN]
    with L hMainL h32 hC hBE hBN
  refine ⟨h32,hC,hMainL.2.1,hMainL.2.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hE hZupper
    hT hTCut hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad H
  classical
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let d := sourceOriginalLiteralDepth 20 L
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  have hZ0 : 0≤Z := by
    have hh : 0<Real.exp L*L^(-CZ) :=
      mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos (by linarith : 0<L) _)
    exact (hh.trans_le hZlo).le
  have hMoment := parity_original_actual_capfree_Bprime_M0_uniform_polylog_quarter434
    L U E V Z K0 Cbox A hLw hK0 k hk hU hV hUV hE hZ0
    (by linarith : 0≤Cbox) hC hZupper hA buf hSmooth hSupport
    (by simpa only [Nat.zero_add] using hBE)
    (by simpa only [Nat.zero_add] using hBN) R hR hCube
  have hAbsorb := parity_original_actual_capfree_Bprime_primary_inverse_log_from_M0434
    L Z D K0 Cmoment (parityOriginal3DSourceMomentFiniteBudget434 0 f)
    hLw hZ0 hMoment
  have hOld := hMainL.2.2.2 hLw hFamily Z hZlo hZhi band hBand slot delta freq
    k hk hkBound rho xi1 xi2 xi3 U E V T signed hU hEpos hV hT hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
    buf (-Real.log A) (Real.log A) hSmooth hSupport H
  dsimp only at hOld hAbsorb ⊢
  exact hOld.trans (add_le_add_left hAbsorb _)

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_Bprime_full_odd_fixed_KZ_any_log_saving_quarter_common_precision434
    (jQ : ℕ) (D C0 Cf CZ Ck K0 Cbox A R : ℝ)
    (hD : 0<D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
        ∀ (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V →
          E=U*L^(-K0) → Z≤24*Cbox*Real.exp L*L^(K0+88) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
          |((2*k:ℤ):ℝ)|≤Z/128 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let d := sourceOriginalLiteralDepth 20 L
        let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
        let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
        let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
          (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
        let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
          L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
        let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
        let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
          parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
            d L E V band slot delta (Nat.ceil (6*U*V)) m K k
        let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
          parityOriginalHistoricalUngatedSourceToSigma434
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
            (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
              (∑m0∈K, ∑q∈sourceTerms m0,
                parityOriginalHistoricalDyadicSmoothPsi434
                  ((parityOriginalHistoricalCanonicalZ434 q.1 m0 q.2.1 q.2.2:ℝ)/Z) *
                alpha m0 * star (alpha q.2.1) *
                At (phi m0 q) *
                parityOriginal3DPhysicalLogFourierPhase434 ζ
                  (parityOriginalHistoricalRealLogTriple434 U Z
                    (phi m0 q).2.2 (phi m0 q).2.1 (phi m0 q).1))‖ ≤
        (Cmoment+132*Cmoment1)*Z*L^(-D) := by
  let P : ℕ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower
  let X : ℝ := (5*(K0+90))*(((1+P:ℕ):ℝ)+1)
  let Dghost : ℝ := D+2*parityOriginalW1PolylogExponent434+30
  have hCW : 0≤parityOriginalW1PolylogExponent434 :=
    parity_original_actual_W1_polylog_exponent_nonneg434
  have hDghost : 0≤Dghost := by dsimp [Dghost]; linarith
  have hCfX : Cf = X+Dghost := by simpa only [X,Dghost] using hCf
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_lowfreq_primary_normalized_two_ghost_quarter_common_precision434
      jQ D C0 Cf CZ Ck K0 Cbox A R
      hD hCZ hCk hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hMain := hMain beta gamma hbeta hgamma
  have hGhost := parity_eventually_original_Bprime_two_ghost_scaled_tail_quarter_canonical434
    CZ Ck hCZ
  let J1 : ℕ := 1+P
  let BE1 : ℝ := 2*A*(J1.factorial:ℝ)
  let BN1 : ℝ := 32*A^2*(J1.factorial:ℝ)*(2:ℝ)^J1+(J1.factorial:ℝ)*A
  filter_upwards [hMain,hGhost,eventually_ge_atTop BE1,
    eventually_ge_atTop BN1] with L hMainL hGhostL hBE1 hBN1
  refine ⟨hMainL.1,hMainL.2.1,hMainL.2.2.1,hMainL.2.2.2.1,?_⟩
  intro hLw hFamily Z hZlo hZhi band hBand slot delta freq k hk hkBound
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hE hZupper
    hTscale hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad
  classical
  let K := Finset.Icc a b
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let d := sourceOriginalLiteralDepth 20 L
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let N : Finset ℕ := Finset.Icc 1 ⌊64*Z⌋₊
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let At : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let sourceTerms : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta (Nat.ceil (6*U*V)) m K k
  let phi : ℕ → (ℕ × (ℕ × ℕ)) → I :=
    parityOriginalHistoricalUngatedSourceToSigma434
  have hLpos : 0<L := by linarith
  have hTpos : 0<T := by
    rw [hTscale]
    exact Real.rpow_pos_of_pos hLpos _
  have hTCut : T≤L^Cf := by rw [hTscale]
  have hTghost : T=L^(X+Dghost) := by rw [hTscale,hCfX]
  have hGhostBound := hGhostL.2 hLw Z hZlo hZhi k hk hkBound
    Dghost U E V K0 Cbox A hDghost hK0 hU hV hUV hE
    (by linarith : 0≤Cbox) hMainL.2.1 hZupper hA
    buf hSmooth hSupport
    (by simpa only [J1] using hBE1)
    (by simpa only [J1] using hBN1)
    R hR hCube
  let Err : ℝ :=
    (L^(2*parityOriginalW1PolylogExponent434)*
      ((Nat.ceil (65*Z):ℕ):ℝ)*
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15)*
      (parityOriginal3DSourceMomentFiniteBudget434 1 f/T)
  have hErr : Err≤66*Z*Cmoment1*
      L^(2*parityOriginalW1PolylogExponent434+30-Dghost) := by
    dsimp only [Err]
    rw [hTghost]
    convert hGhostBound using 1
  have hTwoGhost : 2*Err≤132*Z*Cmoment1*L^(-D) :=
    parity_original_actual_two_ghost_precision_algebra434
      L Z D Cmoment1 Err hLw (by simpa only [Dghost] using hErr)
  have hMainBound := hMainL.2.2.2.2 hLw hFamily Z hZlo hZhi band hBand
    slot delta freq k hk hkBound rho xi1 xi2 xi3 U E V T signed
    hU hEpos hV hUV hE hZupper hTpos hTCut
    hrho hxi1 hxi2 hxi3 hkZ
    prime lFine uFine a b hFineLow hl hu hub hDyad 1
  dsimp only at hMainBound hTwoGhost ⊢
  calc
    _ ≤ Cmoment*Z*L^(-D)+2*Err := by
      simpa only [Err,pow_one] using hMainBound
    _ ≤ Cmoment*Z*L^(-D)+132*Z*Cmoment1*L^(-D) :=
      add_le_add_right hTwoGhost _
    _ = (Cmoment+132*Cmoment1)*Z*L^(-D) := by ring

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_norm_quarter_common_precision434
    (jQ : ℕ) (D C0 Cf CZ Ck K0 Cbox A R : ℝ)
    (hD : 0<D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (KS : Finset ℤ) (N Y : ℕ) (ZS : Finset ℕ),
          (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^Ck) →
          (∀z∈ZS, 0<z ∧ z≤Y) →
          (∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            Real.exp L*L^(-CZ)≤(Z:ℝ) ∧
            (Z:ℝ)≤Real.exp L*L^CZ ∧
            (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) →
          (∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∑k∈KS,∑Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
          parityOriginalActualBprimeFineLowfreqSignal434
            d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
            rho xi1 xi2 xi3 T signed buf A hSmooth hSupport‖ ≤
          (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*
            (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D) := by
  obtain ⟨J,B,S,hBS,hLocal⟩ :=
    parity_eventually_original_actual_Bprime_full_odd_fixed_KZ_any_log_saving_quarter_common_precision434
      jQ D C0 Cf CZ Ck K0 Cbox A R
      hD hCf hCZ hCk hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hLocal := hLocal beta gamma hbeta hgamma
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC0 : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤Cmoment1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hC : 0≤Cmoment+132*Cmoment1 := by linarith
  filter_upwards [hLocal] with L hL
  refine ⟨hL.1,hL.2.1,hL.2.2.1,hL.2.2.2.1,?_⟩
  intro hLw hFamily band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hkZwindow
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let F : ℤ → ℕ → ℂ := fun k Z =>
    parityOriginalActualBprimeFineLowfreqSignal434
      d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
      rho xi1 xi2 xi3 T signed buf A hSmooth hSupport
  have hKBound : ∀k∈KS,k.natAbs≤N := by
    intro k hk
    exact (hKS k hk).2.1
  have hZBound : ∀z∈ZS,z≤Y := by
    intro z hz
    exact (hZS z hz).2
  have hZPositive : ∀z∈ZS,0<z := by
    intro z hz
    exact (hZS z hz).1
  have hPosL : 0<L := by linarith
  have hCell : ∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
      ‖F k Z‖≤(Cmoment+132*Cmoment1)*(Z:ℝ)*L^(-D) := by
    intro k hk Z hz
    have hkk := hKS k hk
    have hzz := hZwindow Z hz
    have hkz := hkZwindow k hk Z hz
    have hOne := hL.2.2.2.2 hLw hFamily (Z:ℝ) hzz.1 hzz.2.1
      band hBand slot delta freq k hkk.1 hkk.2.2
      rho xi1 xi2 xi3 U E V T signed
      hU hEpos hV hUV hEscale hzz.2.2 hT
      hrho hxi1 hxi2 hxi3 hkz
      prime lFine uFine a b hFineLow hl hu huExp hDyad
    dsimp only at hOne ⊢
    change ‖F k Z‖ ≤ (Cmoment+132*Cmoment1)*(Z:ℝ)*L^(-D)
    simpa only [F,parityOriginalActualBprimeFineLowfreqSignal434] using hOne
  have hSum :=
    parity_original_actual_signed_k_smooth_psi_neighbor_global_norm_bound434
      L D (Cmoment+132*Cmoment1) hPosL hC KS N hKBound ZS Y hZBound
      hZPositive F hCell
  simpa only [F,d,K,alpha,Cmoment,Cmoment1] using hSum

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_any_log_quarter_common_precision434
    (jQ : ℕ) (Agoal D C0 Cf CZ Ck K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+Ck+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (KS : Finset ℤ) (N Y : ℕ) (ZS : Finset ℕ),
          (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^Ck) →
          (∀z∈ZS, 0<z ∧ z≤Y) →
          (∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            Real.exp L*L^(-CZ)≤(Z:ℝ) ∧
            (Z:ℝ)≤Real.exp L*L^CZ ∧
            (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) →
          (∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) →
          N≤Nat.ceil (L^Ck) →
          (Y:ℝ)≤25*Cbox*Real.exp L*L^(K0+88) →
          1≤Y → Real.log (Y:ℝ)≤2*L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∑k∈KS,∑Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
          parityOriginalActualBprimeFineLowfreqSignal434
            d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
            rho xi1 xi2 xi3 T signed buf A hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hGlobal⟩ :=
    parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_norm_quarter_common_precision434
      jQ D C0 Cf CZ Ck K0 Cbox A R
      hD hCf hCZ hCk hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hGlobal := hGlobal beta gamma hbeta hgamma
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC0 : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤Cmoment1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hC : 0≤Cmoment+132*Cmoment1 := by linarith
  filter_upwards [hGlobal] with L hL
  refine ⟨hL.1,hL.2.1,hL.2.2.1,hL.2.2.2.1,?_⟩
  intro hLw hFamily band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hkZwindow hN hY hYpos hLogY
  have hBound := hL.2.2.2.2 hLw hFamily band hBand slot delta freq
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hEscale
    hT hrho hxi1 hxi2 hxi3 prime lFine uFine a b
    hFineLow hl hu huExp hDyad KS N Y ZS hKS hZS hZwindow hkZwindow
  have hNumeric := parity_original_actual_kZ_counted_loss_absorbed434
    L Agoal D (Cmoment+132*Cmoment1) Ck K0 Cbox N Y
    (by linarith : 1≤L) hC hCk hK0 hCbox hN hY hYpos hLogY hPrecision
  let Q : ℝ := (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ))*
     (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D)
  have hTwice :
      (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*
        (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D) = 2*Q := by
    dsimp [Q]; push_cast; ring
  have hTwiceBound :
      2*Q ≤ (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
        Real.exp L*L^(-Agoal) := by
    calc
      2*Q ≤ 2*((125*Cbox*(1+2/Real.log 2)*
          (Cmoment+132*Cmoment1))*Real.exp L*L^(-Agoal)) :=
        mul_le_mul_of_nonneg_left hNumeric (by norm_num)
      _ = _ := by ring
  dsimp only at hBound ⊢
  exact hBound.trans (hTwice ▸ hTwiceBound)

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_Bprime_true_physical_kZ_any_log_quarter_common_precision434
    (jQ : ℕ) (Agoal D C0 Cf K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+(K0+89)+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        U*V≤Cbox*Real.exp L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∑k∈KS,∑Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
          parityOriginalActualBprimeFineLowfreqSignal434
            d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
            rho xi1 xi2 xi3 T signed buf A hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_any_log_quarter_common_precision434
      jQ Agoal D C0 Cf (K0+90) (K0+89) K0 Cbox A R
      hD hPrecision hCf (by linarith) (by linarith)
      hK0 hCbox hA hR buf hSmooth hSupport hCube
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hMain := hMain beta gamma hbeta hgamma
  have hSource := parity_eventually_original_actual_full_odd_smooth_source_kZ_inputs_quarter434
    K0 Cbox hK0 hCbox
  filter_upwards [hMain,hSource] with L hMainL hSourceL
  rcases hMainL with ⟨hL8,hL6,hFamily,hReserved,hMainRest⟩
  rcases hSourceL with ⟨hL32,hLarge,hYpos,hYhi,hYlog,hSourceRest⟩
  refine ⟨hL32,hL6,hFamily,hReserved,?_⟩
  intro hLw hFamily0 band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
  let N := Nat.ceil (L^(K0+89))
  have hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U := by
    intro m hm
    obtain ⟨hl,hr⟩ := hDyadStrict m hm
    exact ⟨hl,hr.le⟩
  have hGeo := hSourceRest d band slot delta hLw U V E
    hU hV hUV hUVhi hEscale K hDyadStrict
  dsimp only at hGeo
  rcases hGeo with ⟨hKS,hZS,hZwindow,hShift⟩
  have hMainBound := hMainRest hLw hFamily0 band hBand slot delta freq
    rho xi1 xi2 xi3 U E V T signed
    hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hShift (le_refl N)
    hYhi hYpos hYlog
  dsimp only at hMainBound ⊢
  exact hMainBound

/-- The same original source expression, with common fine precision chosen first. -/
theorem parity_eventually_original_actual_true_full_psi_physical_ball_any_log_quarter_common_precision434
    (jQ : ℕ) (Agoal D C0 Cf K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+(K0+89)+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop, 128≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤4*U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        U*V≤Cbox*Real.exp L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖parityOriginalActualTruePsiGlobalPhysicalBall434
          d L U E V hLw band slot delta freq rho alpha signed Ybox K KS
          (parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS)
          buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_true_physical_kZ_any_log_quarter_common_precision434
      jQ Agoal D C0 Cf K0 Cbox A R
      hD hPrecision hCf hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  refine ⟨J,B,S,hBS,?_⟩
  intro beta gamma hbeta hgamma
  have hMain := hMain beta gamma hbeta hgamma
  have hSpos : 0<S := by linarith
  have hEq := parity_eventually_original_actual_fine_full_psi_global_ball_eq_Bprime434
    S beta gamma (K0+89) hSpos hbeta hgamma
  have hSource := parity_eventually_original_actual_full_odd_smooth_source_kZ_inputs_quarter434
    K0 Cbox hK0 hCbox
  filter_upwards [hMain,hEq,hSource] with L hMainL hEqL hSourceL
  rcases hMainL with ⟨hL32,hL6,hFamily,hReserved,hMainRest⟩
  rcases hSourceL with ⟨hLcap,hLarge,hYpos,hYhi,hYlog,hSourceRest⟩
  refine ⟨hLcap,hL6,hFamily,hReserved,?_⟩
  intro hLw hFamily0 band hBand slot delta freq rho U E V T signed
    hU hEpos hV hUV hEscale hT hrho
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hGeo := hSourceRest d band slot delta hLw U V E
    hU hV hUV hUVhi hEscale K hDyadStrict
  dsimp only at hGeo
  rcases hGeo with ⟨hKS,hZS,hZwin,hShift⟩
  have hKS0 : ∀k∈KS,k≠0 ∧ (k.natAbs:ℝ)≤L^(K0+89) := by
    intro k hk
    exact ⟨(hKS k hk).1,(hKS k hk).2.2⟩
  have hFull := hEqL.2 hLw prime lFine uFine hl hFineLow K KS hKS0 ZSmooth
    d band slot delta freq U E V T rho A signed buf hSmooth hSupport
  have hZero : |(0:ℝ)|≤L^C0 := by
    simp only [abs_zero]
    exact (Real.rpow_pos_of_pos (by linarith : 0<L) _).le
  have hOld := hMainRest hLw hFamily0 band hBand slot delta freq
    rho 0 0 0 U E V T signed hU hEpos hV hUV hEscale hT
    hrho hZero hZero hZero
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  dsimp only at hFull hOld ⊢
  rw [hFull]
  exact hOld

end Green64Analytic.Parity

end

end

