module

public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Green64.Library.PrimeNumberTheoremAnd.ResidueCalcOnRectangles
public import Batteries.Tactic.Lemma
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Complex.Hadamard
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

/-!
# Sieve / Foundation / Analysis / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Analysis.BlaschkeFactor -/

section

open Set Metric
open scoped ComplexConjugate

namespace Chen

noncomputable def blaschkeFactor (R : ℝ) (w z : ℂ) : ℂ :=
  (R : ℂ) * (z - w) / ((R : ℂ) ^ 2 - conj w * z)

theorem blaschkeFactor_eq_inv_canonicalFactor (R : ℝ) (w z : ℂ) :
    blaschkeFactor R w z = (Complex.canonicalFactor R w z)⁻¹ := by
  simp [blaschkeFactor, Complex.canonicalFactor, inv_div]
theorem blaschke_denominator_ne_zero {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) :
    (R : ℂ) ^ 2 - conj w * z ≠ 0 := by
  have hwR : ‖w‖ < R := by simpa using hw
  have hzR : ‖z‖ ≤ R := by simpa using hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg w) hwR
  have hp : ‖conj w * z‖ < R ^ 2 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [mul_le_mul_of_nonneg_left hzR (norm_nonneg w)]
  intro he
  have he' := congrArg norm (sub_eq_zero.mp he)
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at he'
  linarith
theorem analyticOnNhd_blaschkeFactor {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    AnalyticOnNhd ℂ (blaschkeFactor R w) (closedBall 0 R) := by
  intro z hz
  unfold blaschkeFactor
  fun_prop (disch := exact blaschke_denominator_ne_zero hw hz)

theorem norm_blaschkeFactor_on_sphere {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ sphere 0 R) : ‖blaschkeFactor R w z‖ = 1 := by
  rw [blaschkeFactor_eq_inv_canonicalFactor, norm_inv,
    Complex.norm_canonicalFactor_eval_circle_eq_one hw hz, inv_one]
/-- The maximum principle on a disk, with the closed-ball analyticity
interface used by finite zero factorizations. -/
theorem norm_le_of_analyticOnNhd_closedBall {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ closedBall c R) :
    ‖f z‖ ≤ M := by
  have hd : DiffContOnCl ℂ f (ball c R) := by
    apply DifferentiableOn.diffContOnCl
    simpa only [closure_ball _ hR.ne'] using hf.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
  · simpa only [frontier_ball _ hR.ne'] using hb
  · simpa only [closure_ball _ hR.ne'] using hz
theorem norm_blaschkeFactor_le_one {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) : ‖blaschkeFactor R w z‖ ≤ 1 := by
  apply norm_le_of_analyticOnNhd_closedBall (pos_of_mem_ball hw) (analyticOnNhd_blaschkeFactor hw)
    (fun u hu => (norm_blaschkeFactor_on_sphere hw hu).le) hz
theorem blaschkeFactor_ne_zero {R : ℝ} {w z : ℂ} (hw : w ∈ ball 0 R)
    (hz : z ∈ closedBall 0 R) (hzw : z ≠ w) : blaschkeFactor R w z ≠ 0 := by
  unfold blaschkeFactor
  exact div_ne_zero (mul_ne_zero (by exact_mod_cast (pos_of_mem_ball hw).ne')
    (sub_ne_zero.mpr hzw)) (blaschke_denominator_ne_zero hw hz)

end Chen

end

/-! ## ChenTheorem.Analysis.BlaschkeLogDerivative -/

section

open Set Metric
open scoped ComplexConjugate

namespace Chen
theorem logDeriv_blaschkeFactor {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) (hzw : z ≠ w) :
    logDeriv (blaschkeFactor R w) z =
      1 / (z - w) + conj w / ((R : ℂ) ^ 2 - conj w * z) := by
  have hR : (R : ℂ) ≠ 0 := by exact_mod_cast (pos_of_mem_ball hw).ne'
  have hn : (R : ℂ) * (z - w) ≠ 0 := mul_ne_zero hR (sub_ne_zero.mpr hzw)
  have hd := blaschke_denominator_ne_zero hw hz
  unfold blaschkeFactor
  change logDeriv ((fun x : ℂ => (R:ℂ)*(x-w)) /
    (fun x : ℂ => (R:ℂ)^2 - conj w*x)) z = _
  rw [logDeriv_div z hn hd (by fun_prop) (by fun_prop),
    logDeriv_const_mul z (R : ℂ) hR]
  simp only [logDeriv_apply, deriv_sub_const, deriv_id'', deriv_const_sub, deriv_const_mul_id]
  ring
/-- Each reflected-zero term in the Blaschke logarithmic derivative is
bounded by `4/R` on the three-quarter disk. -/
theorem norm_blaschke_logDeriv_correction_le {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : ‖z‖ ≤ 3 * R / 4) :
    ‖conj w / ((R : ℂ) ^ 2 - conj w * z)‖ ≤ 4 / R := by
  have hwR : ‖w‖ < R := by simpa using hw
  have hR : 0 < R := pos_of_mem_ball hw
  have hmul : ‖w‖ * ‖z‖ ≤ 3 * R ^ 2 / 4 := by
    have h := mul_le_mul hwR.le hz (norm_nonneg z) hR.le
    nlinarith
  have hden := norm_sub_norm_le ((R : ℂ) ^ 2) (conj w * z)
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    norm_mul, Complex.norm_conj] at hden
  have hdenlower : R ^ 2 / 4 ≤ ‖(R : ℂ) ^ 2 - conj w * z‖ := by linarith
  have hdenpos : 0 < ‖(R : ℂ) ^ 2 - conj w * z‖ := by nlinarith
  rw [norm_div, Complex.norm_conj]
  apply (div_le_div_iff₀ hdenpos hR).mpr
  nlinarith
end Chen

end

/-! ## ChenTheorem.Analysis.DiskBlaschkeProduct -/

section

open Set Metric Function MeromorphicOn
open scoped Classical

namespace Chen

/-- The finite Blaschke product of the zeros in the open disk, with their
analytic multiplicities. The support is finite when `f` is analytic on the closed disk. -/
noncomputable def diskBlaschkeProduct (f : ℂ → ℂ) (R : ℝ) : ℂ → ℂ :=
  ∏ᶠ w, (blaschkeFactor R w) ^ (divisor f (ball 0 R) w).toNat
theorem diskBlaschkeProduct_eq_prod (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) (z : ℂ) :
    diskBlaschkeProduct f R z = ∏ w ∈ hfin.toFinset,
      blaschkeFactor R w z ^ (divisor f (ball 0 R) w).toNat := by
  have hs : (fun w => (blaschkeFactor R w) ^ (divisor f (ball 0 R) w).toNat).mulSupport ⊆
      (divisor f (ball 0 R)).support := by
    intro w hw
    contrapose! hw
    simp only [mem_support, not_not] at hw
    simp [hw]
  rw [diskBlaschkeProduct, finprod_eq_prod_of_mulSupport_subset_of_finite _ hs hfin]
  simp
theorem analyticOnNhd_diskBlaschkeProduct (f : ℂ → ℂ) (R : ℝ) :
    AnalyticOnNhd ℂ (diskBlaschkeProduct f R) (closedBall 0 R) := by
  intro z hz
  apply analyticAt_finprod
  intro w
  by_cases hw : w ∈ ball 0 R
  · exact ((analyticOnNhd_blaschkeFactor hw) z hz).pow _
  · simp only [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw, Int.toNat_zero, pow_zero]
    exact analyticAt_const
theorem norm_diskBlaschkeProduct_le_one (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖diskBlaschkeProduct f R z‖ ≤ 1 := by
  rw [diskBlaschkeProduct_eq_prod f R hfin z, norm_prod]
  refine Finset.prod_le_one₀ (fun w hw => norm_nonneg _) ?_
  intro w hw
  rw [norm_pow]
  have hwR := (divisor f (ball 0 R)).supportWithinDomain (hfin.mem_toFinset.mp hw)
  exact pow_le_one₀ (norm_nonneg _) (norm_blaschkeFactor_le_one hwR hz)
theorem norm_diskBlaschkeProduct_on_sphere (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) {z : ℂ} (hz : z ∈ sphere 0 R) :
    ‖diskBlaschkeProduct f R z‖ = 1 := by
  rw [diskBlaschkeProduct_eq_prod f R hfin z, norm_prod]
  apply Finset.prod_eq_one
  intro w hw
  have hwR := (divisor f (ball 0 R)).supportWithinDomain (hfin.mem_toFinset.mp hw)
  rw [norm_pow, norm_blaschkeFactor_on_sphere hwR hz, one_pow]
theorem canonical_product_eq_diskBlaschkeProduct {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    (∏ᶠ w, (Complex.canonicalFactor R w) ^ (-divisor f (ball 0 R) w)) =
      diskBlaschkeProduct f R := by
  unfold diskBlaschkeProduct
  congr 1
  funext w z
  have hd : 0 ≤ divisor f (ball 0 R) w := (hf.mono ball_subset_closedBall).divisor_nonneg w
  have he : ((divisor f (ball 0 R) w).toNat : ℤ) = divisor f (ball 0 R) w :=
    Int.toNat_of_nonneg hd
  simp only [Pi.pow_apply]
  conv_lhs => rw [← he]
  rw [zpow_neg, zpow_natCast, blaschkeFactor_eq_inv_canonicalFactor, inv_pow]
end Chen

end

/-! ## ChenTheorem.Analysis.AnalyticZeroFactorization -/

section

open Set Metric Filter Topology MeromorphicOn

namespace Chen
/-- Continuity removes the exceptional discrete set from an identity on an open set. -/
theorem eqOn_of_continuousOn_codiscrete {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : f =ᶠ[codiscreteWithin U] g) : EqOn f g U := by
  intro z hz
  have hpunct : f =ᶠ[𝓝[≠] z] g := by
    have he' := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp he z hz
    have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ U :=
      eventually_nhdsWithin_of_eventually_nhds (hU.mem_nhds hz)
    filter_upwards [he', hmem] with w hw hwU
    exact hw.resolve_right (by simpa using hwU)
  have hnhds := ((hf.continuousAt (hU.mem_nhds hz)).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hg.continuousAt (hU.mem_nhds hz))).mp hpunct
  exact hnhds.eq_of_nhds
theorem analyticOnNhd_of_canonicalDecomp {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : Complex.CanonicalDecomp f g R) : AnalyticOnNhd ℂ g (closedBall 0 R) := by
  apply D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mp
  intro z
  change 0 ≤ divisor g (closedBall 0 R) z
  rw [D.divisor_eq_divisor hR]
  exact (hf.mono sphere_subset_closedBall).divisor_nonneg z
/-- The analytic Blaschke factorization is an exact identity even at zeros
and on the boundary, not merely a codiscrete identity. -/
theorem canonicalDecomp_eqOn_closedBall {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : Complex.CanonicalDecomp f g R) :
    EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R) := by
  have hg := analyticOnNhd_of_canonicalDecomp hR hf D
  have hp := analyticOnNhd_diskBlaschkeProduct f R
  have he := D.eventuallyEq
  rw [canonical_product_eq_diskBlaschkeProduct hf] at he
  change f =ᶠ[codiscreteWithin (closedBall 0 R)] (fun z => diskBlaschkeProduct f R z * g z) at he
  have hb := eqOn_of_continuousOn_codiscrete isOpen_ball
    (hf.continuousOn.mono ball_subset_closedBall)
    ((hp.mul hg).continuousOn.mono ball_subset_closedBall)
    (he.filter_mono (codiscreteWithin_mono ball_subset_closedBall))
  apply hb.of_subset_closure hf.continuousOn (hp.mul hg).continuousOn ball_subset_closedBall
  rw [closure_ball _ hR.ne']
/-- A nonzero center value gives an analytic zero-free factor on the disk;
all interior zeros and their multiplicities occur in the explicit finite product. -/
theorem exists_analytic_blaschke_factorization {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R) := by
  have hmem : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have horder : meromorphicOrderAt f 0 ≠ ⊤ := by
    rw [(hf 0 hmem).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
    simp
  have horders : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    exact hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected hmem u.property horder
  obtain ⟨g, D⟩ := hf.meromorphicOn.exists_canonicalDecomp horders
  exact ⟨g, analyticOnNhd_of_canonicalDecomp hR hf D, D.ne_zero,
    canonicalDecomp_eqOn_closedBall hR hf D⟩
end Chen

end

/-! ## ChenTheorem.Analysis.DiskZeroLogDerivative -/

section

open Set Metric Function MeromorphicOn
open scoped Classical ComplexConjugate

namespace Chen

noncomputable def diskZeroPoleSum (f : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∑ᶠ w, (divisor f (ball 0 R) w : ℂ) / (z - w)

noncomputable def diskZeroCount (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ w, (divisor f (ball 0 R) w : ℝ)
theorem diskZeroPoleSum_eq_sum (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) (z : ℂ) :
    diskZeroPoleSum f R z = ∑ w ∈ hfin.toFinset, (divisor f (ball 0 R) w : ℂ) / (z - w) := by
  apply finsum_eq_sum_of_support_subset_of_finite _ _ hfin
  intro w hw
  contrapose! hw
  simp only [mem_support, not_not] at hw
  simp [hw]
theorem diskZeroCount_eq_sum (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) :
    diskZeroCount f R = ∑ w ∈ hfin.toFinset, (divisor f (ball 0 R) w : ℝ) := by
  apply finsum_eq_sum_of_support_subset_of_finite _ _ hfin
  intro w hw
  contrapose! hw
  simp only [mem_support, not_not] at hw
  simp [hw]
theorem ne_zero_point_ne_divisor_support {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z w : ℂ}
    (hz : z ∈ closedBall 0 R) (hfz : f z ≠ 0)
    (hw : w ∈ (divisor f (ball 0 R)).support) : z ≠ w := by
  intro he
  subst w
  have hzR := (divisor f (ball 0 R)).supportWithinDomain hw
  have ho := (hf z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz
  have hd := mem_support.mp hw
  rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hzR, ho] at hd
  simp at hd
theorem logDeriv_diskBlaschkeProduct {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z : ℂ}
    (hz : z ∈ closedBall 0 R) (hfz : f z ≠ 0) :
    logDeriv (diskBlaschkeProduct f R) z =
      ∑ w ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        (divisor f (ball 0 R) w : ℂ) *
          (1 / (z - w) + conj w / ((R : ℂ) ^ 2 - conj w * z)) := by
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hwR (w : ℂ) (hw : w ∈ hfin.toFinset) : w ∈ ball 0 R :=
    (divisor f (ball 0 R)).supportWithinDomain (hfin.mem_toFinset.mp hw)
  have hzw (w : ℂ) (hw : w ∈ hfin.toFinset) : z ≠ w :=
    ne_zero_point_ne_divisor_support hf hz hfz (hfin.mem_toFinset.mp hw)
  have hprod : diskBlaschkeProduct f R = fun u => ∏ w ∈ hfin.toFinset,
      blaschkeFactor R w u ^ (divisor f (ball 0 R) w).toNat := by
    funext u
    exact diskBlaschkeProduct_eq_prod f R hfin u
  rw [hprod, logDeriv_fun_prod (s := hfin.toFinset)
    (f := fun w u => blaschkeFactor R w u ^ (divisor f (ball 0 R) w).toNat) (x := z)
    (fun w hw => pow_ne_zero _ (blaschkeFactor_ne_zero (hwR w hw) hz (hzw w hw)))
    (fun w hw => ((analyticOnNhd_blaschkeFactor (hwR w hw)) z hz).differentiableAt.pow _)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [logDeriv_fun_pow ((analyticOnNhd_blaschkeFactor (hwR w hw)) z hz).differentiableAt,
    logDeriv_blaschkeFactor (hwR w hw) hz (hzw w hw)]
  have hd := (hf.mono ball_subset_closedBall).divisor_nonneg w
  have hcast : ((divisor f (ball 0 R) w).toNat : ℂ) = (divisor f (ball 0 R) w : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hd
  rw [hcast]
/-- The logarithmic derivative of the finite zero product equals the sum
of the zero poles up to a term controlled by the number of zeros. -/
theorem norm_logDeriv_diskBlaschkeProduct_sub_poles_le {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z : ℂ}
    (hz : ‖z‖ ≤ 3 * R / 4) (hfz : f z ≠ 0) :
    ‖logDeriv (diskBlaschkeProduct f R) z - diskZeroPoleSum f R z‖ ≤
      (4 / R) * diskZeroCount f R := by
  have hzR : z ∈ closedBall 0 R := by simp only [mem_closedBall_zero_iff]; linarith
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  rw [logDeriv_diskBlaschkeProduct hf hzR hfz, diskZeroPoleSum_eq_sum f R hfin z,
    ← Finset.sum_sub_distrib, diskZeroCount_eq_sum f R hfin, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro w hw
  have hwR := (divisor f (ball 0 R)).supportWithinDomain (hfin.mem_toFinset.mp hw)
  have hd := (hf.mono ball_subset_closedBall).divisor_nonneg w
  rw [show (divisor f (ball 0 R) w : ℂ) *
      (1 / (z - w) + conj w / ((R : ℂ) ^ 2 - conj w * z)) -
      (divisor f (ball 0 R) w : ℂ) / (z - w) =
      (divisor f (ball 0 R) w : ℂ) * (conj w / ((R : ℂ) ^ 2 - conj w * z)) by ring,
    norm_mul, Complex.norm_int_of_nonneg hd]
  have h := mul_le_mul_of_nonneg_left (norm_blaschke_logDeriv_correction_le hwR hz)
    (show (0 : ℝ) ≤ (divisor f (ball 0 R) w : ℝ) by exact_mod_cast hd)
  simpa only [mul_comm] using h
end Chen

end

/-! ## ChenTheorem.Analysis.DiskZeroCount -/

section

open Set Metric Function MeromorphicOn

namespace Chen

theorem diskZeroCount_nonneg {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) : 0 ≤ diskZeroCount f R := by
  apply finsum_nonneg
  intro w
  exact_mod_cast (hf.mono ball_subset_closedBall).divisor_nonneg w
theorem diskZeroCount_le_closedBall {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    diskZeroCount f R ≤ ((∑ᶠ w, divisor f (closedBall 0 R) w : ℤ) : ℝ) := by
  have hfin := (divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
  have hmap : ((∑ᶠ w, divisor f (closedBall 0 R) w : ℤ) : ℝ) =
      ∑ᶠ w, (divisor f (closedBall 0 R) w : ℝ) := map_finsum (Int.castRingHom ℝ) hfin
  rw [hmap]
  apply finsum_le_finsum'
  · apply hf.meromorphicOn.divisor_ball_support_finite.subset
    intro w hw
    simpa only [mem_support, ne_eq, Int.cast_eq_zero] using hw
  · apply hfin.subset
    intro w hw
    simpa only [mem_support, ne_eq, Int.cast_eq_zero] using hw
  · intro w
    change (divisor f (ball 0 R) w : ℝ) ≤ (divisor f (closedBall 0 R) w : ℝ)
    by_cases hw : w ∈ ball 0 R
    · rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hw,
        hf.meromorphicOn.divisor_apply (ball_subset_closedBall hw)]
    · rw [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw, Int.cast_zero]
      exact_mod_cast hf.divisor_nonneg w
theorem diskZeroCount_le_of_outer_bound {f : ℂ → ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hb : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M) :
    diskZeroCount f r ≤ Real.log (M / ‖f 0‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hf' : AnalyticOnNhd ℂ f (closedBall 0 |R|) := by simpa only [abs_of_pos hR] using hf
  have hb' : ∀ z ∈ sphere 0 |R|, ‖f z‖ ≤ M := by simpa only [abs_of_pos hR] using hb
  have hj := hf'.sum_divisor_le (r := r) (R := R)
    (by simpa only [abs_of_pos hr] using hr)
    (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR) hM h0 hb'
  rw [abs_of_pos hr] at hj
  exact (diskZeroCount_le_closedBall (hf.mono (closedBall_subset_closedBall hrR.le))).trans hj
end Chen

end

/-! ## ChenTheorem.Analysis.GeometricTruncation -/

section

namespace Chen

theorem geometric_pow_le_exp_quarter {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 3 / 4) (k : ℕ) :
    r ^ k ≤ Real.exp ((k : ℝ) * (-1 / 4)) := by
  have hbase : r ≤ Real.exp (-1 / 4 : ℝ) := by
    have h := Real.add_one_le_exp (-1 / 4 : ℝ)
    linarith
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hr hbase k

/-- One common truncation index controls all geometric tails with ratio at most 3/4. -/
theorem exists_geometric_truncation {M : ℝ} (hM : 1 ≤ M) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 4 * Real.log (8 * M) + 2 ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 3 / 4 → M * r ^ k / (1 - r) ≤ 1 / 2 := by
  have hM0 : 0 < M := by linarith
  have hlog : 0 ≤ Real.log (8 * M) := Real.log_nonneg (by linarith)
  let k : ℕ := ⌈4 * Real.log (8 * M)⌉₊ + 1
  have hklo : 4 * Real.log (8 * M) ≤ (k : ℝ) := by
    have h := Nat.le_ceil (4 * Real.log (8 * M))
    dsimp [k]
    push_cast
    linarith
  have hkhi : (k : ℝ) ≤ 4 * Real.log (8 * M) + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 4 * Real.log (8 * M) by positivity)
    dsimp [k]
    push_cast
    linarith
  refine ⟨k, by dsimp [k]; omega, hkhi, ?_⟩
  intro r hr hr'
  have hpow : r ^ k ≤ 1 / (8 * M) := by
    calc
      r ^ k ≤ Real.exp ((k : ℝ) * (-1 / 4)) := geometric_pow_le_exp_quarter hr hr' k
      _ ≤ Real.exp (-Real.log (8 * M)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hprod : M * r ^ k ≤ 1 / 8 := by
    calc
      _ ≤ M * (1 / (8 * M)) := mul_le_mul_of_nonneg_left hpow hM0.le
      _ = _ := by field_simp
  apply (div_le_iff₀ (by linarith : 0 < 1 - r)).mpr
  linarith

theorem one_add_pow_le_exp_of_nat_le {x L : ℝ} (hx : 0 ≤ x) (k : ℕ) (hk : (k : ℝ) ≤ L) :
    (1 + x) ^ k ≤ Real.exp (L * x) := by
  have hbase : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  calc
    _ ≤ (Real.exp x) ^ k := pow_le_pow_left₀ (by linarith) hbase k
    _ = Real.exp ((k : ℝ) * x) := (Real.exp_nat_mul x k).symm
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk hx)

end Chen

end

/-! ## ChenTheorem.Analysis.PNT.Mathlib.Analysis.Asymptotics.Asymptotics -/

section

/-
Adapted from PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean
Upstream commit: c6c73610b406689c4b58325cbe1342ecca25d755
License: Apache-2.0; see LICENSE and NOTICE in this directory tree.
Blueprint annotations removed; imports localized. See SOURCES.json.
-/

open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics

end

/-! ## ChenTheorem.Analysis.PNT.Mathlib.Analysis.Asymptotics.Uniformly -/

section

/-
Adapted from PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Uniformly.lean
Upstream commit: c6c73610b406689c4b58325cbe1342ecca25d755
License: Apache-2.0; see LICENSE and NOTICE in this directory tree.
Blueprint annotations removed; imports localized. See SOURCES.json.
-/
/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/

/-!
# Uniform Asymptotics

For a family of functions `f : ι × α → E` and `g : α → E`, we can think of
`f =O[𝓟 s ×ˢ l] fun (i, x) ↦ g x` as expressing that `f i` is O(g) uniformly on `s`.

This file provides methods for constructing `=O[𝓟 s ×ˢ l]` relations (similarly `Θ`)
and deriving their consequences.
-/

open Filter

open Topology

namespace Asymptotics

variable {α ι E F : Type*} {s : Set ι}

section Basic

variable [Norm E] [Norm F] {f : ι × α → E} {g : α → F} {l : Filter α}

/- If f = O(g) uniformly on `s`, then f_i = O(g) for any i.` -/
theorem isBigO_of_isBigOUniformly (h : f =O[𝓟 s ×ˢ l] (g ∘ Prod.snd)) {i : ι}
    (hi : i ∈ s) : (fun x ↦ f (i, x)) =O[l] g := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C, Filter.eventually_iff_exists_mem.mpr ⟨v, hv, ?_⟩⟩
  exact fun y hy ↦ ht _ <| huv ⟨hu hi, hy⟩

/- If f = Ω(g) uniformly on `s`, then f_i = Ω(g) for any i.` -/
theorem isBigO_rev_of_isBigOUniformly_rev (h : (g ∘ Prod.snd) =O[𝓟 s ×ˢ l] f) {i : ι}
    (hi : i ∈ s) : g =O[l] fun x ↦ f (i, x) := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C, Filter.eventually_iff_exists_mem.mpr ⟨v, hv, ?_⟩⟩
  exact fun y hy ↦ ht (i, y) <| huv ⟨hu hi, hy⟩

/- If f = Θ(g) uniformly on `s`, then f_i = Θ(g) for any i.` -/
theorem isTheta_of_isThetaUniformly (h : f =Θ[𝓟 s ×ˢ l] (g ∘ Prod.snd)) {i : ι}
    (hi : i ∈ s) : (fun x ↦ f (i, x)) =Θ[l] g :=
  ⟨isBigO_of_isBigOUniformly h.1 hi, isBigO_rev_of_isBigOUniformly_rev h.2 hi⟩

end Basic

section Order

variable [NormedAddCommGroup α] [LinearOrder α] [ProperSpace α] [NormedAddCommGroup F]

theorem isLittleO_const_fst_atBot [NoMinOrder α] [ClosedIicTopology α] (c : F) (ly : Filter E) :
    (fun (_ : α × E) ↦ c) =o[atBot ×ˢ ly] Prod.fst := by
  refine ly.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  change ((fun _ ↦ c) ∘ Prod.fst) =o[atBot ×ˢ ly] (id ∘ Prod.fst)
  rewrite [← isLittleO_map, map_fst_prod]
  exact isLittleO_const_id_atBot2 c

theorem isLittleO_const_snd_atBot [NoMinOrder α] [ClosedIicTopology α] (c : F) (lx : Filter E) :
    (fun (_ : E × α) ↦ c) =o[lx ×ˢ atBot] Prod.snd := by
  refine lx.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  change ((fun _ ↦ c) ∘ Prod.snd) =o[lx ×ˢ atBot] (id ∘ Prod.snd)
  rewrite [← isLittleO_map, map_snd_prod]
  exact isLittleO_const_id_atBot2 c

theorem isLittleO_const_fst_atTop [NoMaxOrder α] [ClosedIciTopology α] (c : F) (ly : Filter E) :
    (fun (_ : α × E) ↦ c) =o[atTop ×ˢ ly] Prod.fst := by
  refine ly.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  change ((fun _ ↦ c) ∘ Prod.fst) =o[atTop ×ˢ ly] (id ∘ Prod.fst)
  rewrite [← isLittleO_map, map_fst_prod]
  exact isLittleO_const_id_atTop2 c

theorem isLittleO_const_snd_atTop [NoMaxOrder α] [ClosedIciTopology α] (c : F) (lx : Filter E) :
    (fun (_ : E × α) ↦ c) =o[lx ×ˢ atTop] Prod.snd := by
  refine lx.eq_or_neBot.casesOn (fun h ↦ by simp [h]) (fun _ ↦ ?_)
  change ((fun _ ↦ c) ∘ Prod.snd) =o[lx ×ˢ atTop] (id ∘ Prod.snd)
  rewrite [← isLittleO_map, map_snd_prod]
  exact isLittleO_const_id_atTop2 c

end Order

section ContinuousOn

variable [TopologicalSpace ι] {C : ι → E} {c : F}

section IsBigO

variable [SeminormedAddGroup E] [Norm F]

/- A family of constant functions `f (i, x) = C i` is uniformly bounded w.r.t. `s` by
`⨆ i ∈ s, ‖C i‖`, if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOWithUniformlyOn_isCompact
    (hf : ContinuousOn C s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (l : Filter α) :
    IsBigOWith (sSup (norm '' (C '' s)) / ‖c‖) (𝓟 s ×ˢ l)
    (fun (i, _x) ↦ C i) fun _ => c := by
  refine isBigOWith_iff.mpr <| eventually_of_mem ?_ (fun x hx ↦ ?_) (U := s ×ˢ Set.univ)
  · exact prod_mem_prod (mem_principal_self s) univ_mem
  · rw [div_mul_cancel₀ _ hc]
    replace hs := hs.image_of_continuousOn hf |>.image continuous_norm
    have h_sSup := hs.isLUB_sSup <| Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x.1, hx.1⟩
    exact h_sSup.1 <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx.1

/- A family of constant functions `f (i, x) = C i` is uniformly O(1) w.r.t. `s`,
if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOUniformlyOn_isCompact
    (hf : ContinuousOn C s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (l : Filter α) :
    (fun (i, _x) ↦ C i) =O[𝓟 s ×ˢ l] fun _ => c :=
  (hf.const_isBigOWithUniformlyOn_isCompact hs hc l).isBigO

end IsBigO

section IsTheta

variable [NormedAddGroup E] [SeminormedAddGroup F]

/- A family of constant functions `f (i, x) = C i` is uniformly bounded below w.r.t. `s` by
`⊓ i ∈ s, ‖C i‖`, if `s` is compact and `C` is continuous. -/
theorem _root_.ContinuousOn.const_isBigOWithUniformlyOn_isCompact_rev
    (hf : ContinuousOn C s) (hs : IsCompact s) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / sInf (norm '' (C '' s))) (𝓟 s ×ˢ l)
    (fun _ => c) fun (i, _x) ↦ C i := by
  refine isBigOWith_iff.mpr <| eventually_of_mem ?_ (fun x hx ↦ ?_) (U := s ×ˢ Set.univ)
  · exact prod_mem_prod (mem_principal_self s) univ_mem
  · rewrite [mul_comm_div]
    replace hs := hs.image_of_continuousOn hf |>.image continuous_norm
    have h_sInf := hs.isGLB_sInf <| Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x.1, hx.1⟩
    refine le_mul_of_one_le_right (norm_nonneg c) <| (one_le_div ?_).mpr <|
      h_sInf.1 <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx.1
    obtain ⟨_, ⟨x, hx, hCx⟩, hnormCx⟩ := hs.sInf_mem h_sInf.nonempty
    rewrite [← hnormCx, ← hCx]
    exact (norm_ne_zero_iff.mpr (hC x hx)).symm.lt_of_le (norm_nonneg _)

/- A family of constant functions `f (i, x) = C i` is uniformly Ω(1) w.r.t. `s`,
if `s` is compact and `C` is continuous with no zeros on `s`. -/
theorem _root_.ContinuousOn.const_isBigOUniformlyOn_isCompact_rev
    (hf : ContinuousOn C s) (hs : IsCompact s) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    (fun _ => c) =O[𝓟 s ×ˢ l] (fun (i, _x) ↦ C i) :=
  (hf.const_isBigOWithUniformlyOn_isCompact_rev hs hC l).isBigO

/- A family of constant functions `f (i, x) = C i` is uniformly Θ(1) w.r.t. `s`,
if `s` is compact and `C` is continuous with no zeros on `s`. -/
theorem _root_.ContinuousOn.const_isThetaUniformlyOn_isCompact (hf : ContinuousOn C s)
    (hs : IsCompact s) (hc : ‖c‖ ≠ 0) (hC : ∀ i ∈ s, C i ≠ 0) (l : Filter α) :
    (fun (i, _x) ↦ C i) =Θ[𝓟 s ×ˢ l] fun _ => c :=
  ⟨hf.const_isBigOUniformlyOn_isCompact hs hc l,
    hf.const_isBigOUniformlyOn_isCompact_rev hs hC l⟩

end IsTheta

end ContinuousOn
end Asymptotics

end

/-! ## ChenTheorem.Analysis.PNT.PerronFormula -/

section

/-
Adapted from PrimeNumberTheoremAnd/PerronFormula.lean
Upstream commit: c6c73610b406689c4b58325cbe1342ecca25d755
License: Apache-2.0; see LICENSE and NOTICE in this directory tree.
Blueprint annotations removed; imports localized. See SOURCES.json.
-/

set_option lang.lemmaCmd true

open Asymptotics Complex ComplexConjugate Topology Filter Real MeasureTheory Set

open scoped Interval

/-
In this section, we prove the Perron formula, which plays a key role in our proof of Mellin
inversion.
-/

/-
The following is preparatory material used in the proof of the Perron formula, see Lemma
\ref{formulaLtOne}.
-/

/- TODO: move to general section. -/

lemma zeroTendstoDiff (L₁ L₂ : ℂ) (f : ℝ → ℂ) (h : ∀ᶠ T in atTop, f T = 0)
    (h' : Tendsto f atTop (𝓝 (L₂ - L₁))) : L₁ = L₂ := by
  rw [← zero_add L₁, ← @eq_sub_iff_add_eq]
  exact tendsto_nhds_unique (EventuallyEq.tendsto h) h'

/- TODO: Move this to general section. -/

lemma RectangleIntegral_tendsTo_VerticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ - I * T) (σ' + I * T)) atTop
      (𝓝 (VerticalIntegral f σ' - VerticalIntegral f σ)) := by
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
    mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im, one_mul, zero_add, zero_sub,
    add_im]
  apply Tendsto.sub
  · rewrite [← zero_add (VerticalIntegral _ _), ← zero_sub_zero]
    apply Tendsto.add <| Tendsto.sub (hbot.comp tendsto_neg_atTop_atBot) htop
    exact (intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id).const_smul I
  · exact (intervalIntegral_tendsto_integral hleft tendsto_neg_atTop_atBot tendsto_id).const_smul I

lemma verticalIntegral_eq_verticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hf : HolomorphicOn f ([[σ, σ']] ×ℂ univ))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    VerticalIntegral f σ = VerticalIntegral f σ' := by
  refine zeroTendstoDiff _ _ _ (univ_mem' fun _ ↦ ?_)
    (RectangleIntegral_tendsTo_VerticalIntegral hbot htop hleft hright)
  exact integral_boundary_rect_eq_zero_of_differentiableOn f _ _
    (hf.mono fun z hrect ↦ ⟨by simpa using hrect.1, trivial⟩)

lemma verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    {σ σ' : ℝ} {f : ℂ → ℂ} {p : ℂ} (hσ : σ < p.re ∧ p.re < σ')
    (hf : HolomorphicOn f (Icc σ σ' ×ℂ univ \ {p}))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop :
      Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, VerticalIntegral f σ' - VerticalIntegral f σ =
    RectangleIntegral f (-c - c * I + p) (c + c * I + p) := by
  have : Icc σ σ' ×ℂ univ ∈ 𝓝 p := by
    rw [← mem_interior_iff_mem_nhds, Complex.interior_reProdIm, interior_Icc, interior_univ]
    refine ⟨⟨?_, ?_⟩, trivial⟩ <;> linarith
  obtain ⟨c', hc'0, hc'⟩ := ((nhds_hasBasis_square p).1 _).mp this
  filter_upwards [Ioo_mem_nhdsGT hc'0] with c ⟨hc0, hcc'⟩
  have hsub : Square p c ⊆ Icc σ σ' ×ℂ univ := (square_subset_square hc0 hcc'.le).trans hc'
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_VerticalIntegral hbot htop hleft hright)
  apply Filter.EventuallyEq.tendsto
  filter_upwards [Filter.Ioi_mem_atTop ((c - p.im) ⊔ (c + p.im))] with y hy
  have : c - p.im < y ∧ c + p.im < y := sup_lt_iff.mp hy
  have : c + σ ≤ p.re := by simpa using (hsub ⟨left_mem_uIcc, left_mem_uIcc⟩).1.1
  have : c + p.re ≤ σ' := by simpa using (hsub ⟨right_mem_uIcc, right_mem_uIcc⟩).1.2
  apply RectanglePullToNhdOfPole'
  · simpa using ⟨by linarith, by linarith, by linarith⟩
  · exact square_mem_nhds p (ne_of_gt hc0)
  · apply RectSubRect' <;> simpa using by linarith
  · refine hf.mono (Set.sdiff_subset_sdiff ?_ subset_rfl)
    simpa [Rectangle, uIcc_of_lt (hσ.1.trans hσ.2)] using! fun x ⟨hx, _⟩ ↦ ⟨hx, trivial⟩

/- Truncated contour shift through a simple pole. The left vertical side stays as the
symmetric truncation; only the right vertical side is required to be Bochner integrable. -/
theorem tendsto_truncated_vertical_shift_with_simple_pole
    {σ σ' : ℝ} {f : ℂ → ℂ} {p A : ℂ} (hσ : σ < p.re ∧ p.re < σ')
    (hf : HolomorphicOn f (Icc σ σ' ×ℂ univ \ {p}))
    (hpole : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * π * I) : ℂ) • VIntegral f σ (-T) T)
      atTop (𝓝 (VerticalIntegral' f σ' - A)) := by
  have hrect : ∀ᶠ T : ℝ in atTop,
      RectangleIntegral' f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) = A := by
    filter_upwards [eventually_gt_atTop (|p.im| + 1)] with T hT
    have hTabs : |p.im| < T := by linarith
    have hTpos : 0 < T := lt_of_le_of_lt (abs_nonneg p.im) hTabs
    refine ResidueTheoremOnRectangleWithSimplePole' ?_ ?_ ?_ ?_ hpole
    · simp [le_of_lt (hσ.1.trans hσ.2)]
    · simp only [sub_im, ofReal_im, mul_im, I_re, zero_mul, I_im, ofReal_re, one_mul,
        zero_add, zero_sub, add_im]
      linarith
    · rw [rectangle_mem_nhds_iff]
      simp only [mem_reProdIm, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
        mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im, one_mul, zero_add,
        zero_sub, add_im]
      constructor
      · rw [uIoo_of_lt (hσ.1.trans hσ.2)]
        exact ⟨hσ.1, hσ.2⟩
      · rw [uIoo_of_lt (by linarith)]
        exact abs_lt.mp hTabs
    · refine hf.mono (sdiff_subset_sdiff ?_ subset_rfl)
      intro z hz
      rw [Rectangle] at hz
      simp only [sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, sub_zero, add_re, add_zero, uIcc_of_le (le_of_lt (hσ.1.trans hσ.2)),
        mem_reProdIm] at hz
      exact ⟨hz.1, trivial⟩
  have hleft_eq : ∀ᶠ T : ℝ in atTop,
      (1 / (2 * π * I) : ℂ) • VIntegral f σ (-T) T =
        (1 / (2 * π * I) : ℂ) • HIntegral f σ σ' (-T) -
          (1 / (2 * π * I) : ℂ) • HIntegral f σ σ' T +
          (1 / (2 * π * I) : ℂ) • VIntegral f σ' (-T) T - A := by
    filter_upwards [hrect] with T hT
    have hT' : (1 / (2 * π * I) : ℂ) •
        RectangleIntegral f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) = A := by
      simpa [RectangleIntegral'] using hT
    calc
      (1 / (2 * π * I) : ℂ) • VIntegral f σ (-T) T
          = (1 / (2 * π * I) : ℂ) • HIntegral f σ σ' (-T) -
              (1 / (2 * π * I) : ℂ) • HIntegral f σ σ' T +
              (1 / (2 * π * I) : ℂ) • VIntegral f σ' (-T) T -
              (1 / (2 * π * I) : ℂ) •
                RectangleIntegral f ((σ : ℂ) - I * (T : ℂ)) ((σ' : ℂ) + I * (T : ℂ)) := by
            simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
              ofReal_im, mul_zero, sub_self, sub_zero, sub_im, mul_im, one_mul, zero_add,
              zero_sub, add_re, add_zero, add_im]
            module
      _ = (1 / (2 * π * I) : ℂ) • HIntegral f σ σ' (-T) -
              (1 / (2 * π * I) : ℂ) • HIntegral f σ σ' T +
              (1 / (2 * π * I) : ℂ) • VIntegral f σ' (-T) T - A := by
            rw [hT']
  have hbotT :
      Tendsto (fun T : ℝ ↦ (1 / (2 * π * I) : ℂ) • HIntegral f σ σ' (-T))
        atTop (𝓝 0) := by
    simpa [HIntegral] using
      (hbot.comp tendsto_neg_atTop_atBot).const_smul (1 / (2 * π * I) : ℂ)
  have htopT :
      Tendsto (fun T : ℝ ↦ (1 / (2 * π * I) : ℂ) • HIntegral f σ σ' T)
        atTop (𝓝 0) := by
    simpa [HIntegral] using htop.const_smul (1 / (2 * π * I) : ℂ)
  have hrightT :
      Tendsto (fun T : ℝ ↦ (1 / (2 * π * I) : ℂ) • VIntegral f σ' (-T) T)
        atTop (𝓝 (VerticalIntegral' f σ')) := by
    simpa [VIntegral, VerticalIntegral', VerticalIntegral] using
      ((intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id).const_smul
        I).const_smul (1 / (2 * π * I) : ℂ)
  have hA : Tendsto (fun _ : ℝ => A) atTop (𝓝 A) := tendsto_const_nhds
  have hsum := ((hbotT.sub htopT).add hrightT).sub hA
  have hleft_eq_symm := hleft_eq.mono (fun _ hT => hT.symm)
  simpa [sub_eq_add_neg, add_assoc] using (hsum.congr' hleft_eq_symm)

/- Set-integral form of `tendsto_truncated_vertical_shift_with_simple_pole`, normalized
as `(2π)⁻¹ ∫ f(σ + it) dt`. -/
theorem tendsto_truncated_vertical_shift_with_simple_pole_Ioo
    {σ σ' : ℝ} {f : ℂ → ℂ} {p A : ℂ} (hσ : σ < p.re ∧ p.re < σ')
    (hf : HolomorphicOn f (Icc σ σ' ×ℂ univ \ {p}))
    (hpole : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun T : ℝ ↦ (1 / (2 * π) : ℂ) * ∫ t in Set.Ioo (-T) T,
        f (σ + t * I)) atTop (𝓝 (VerticalIntegral' f σ' - A)) := by
  have hbase := tendsto_truncated_vertical_shift_with_simple_pole hσ hf hpole hbot htop hright
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [VIntegral]
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  simp only [smul_eq_mul]
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero]


lemma RectangleIntegral_tendsTo_UpperU {σ σ' T : ℝ} {f : ℂ → ℂ}
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ + I * T) (σ' + I * U)) atTop
      (𝓝 (UpperUIntegral f σ σ' T)) := by
  have h_re  (s : ℝ) (t : ℝ) : (s  + I * t).re = s  := by simp
  have h_im  (s : ℝ) (t : ℝ) : (s  + I * t).im = t  := by simp
  have hbot : Tendsto (fun (_ : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + T * I)) atTop
      (𝓝 <| ∫ (x : ℝ) in σ..σ', f (x + T * I)) := by exact tendsto_const_nhds
  have hvert (s : ℝ) (int : Integrable (fun (y : ℝ) ↦ f (s + y * I))) :
      Tendsto (fun (U : ℝ) ↦ I * ∫ (y : ℝ) in T..U, f (s + y * I)) atTop
        (𝓝 <| I * ∫ (y : ℝ) in Ioi T, f (s + y * I)) := by
    exact (intervalIntegral_tendsto_integral_Ioi T int.restrict tendsto_id).const_smul I
  have := ((hbot.sub htop).add (hvert σ' hright)).sub (hvert σ hleft)
  simpa only [RectangleIntegral, UpperUIntegral, h_re, h_im, sub_zero,
    ← integral_Ici_eq_integral_Ioi]


lemma RectangleIntegral_tendsTo_LowerU {σ σ' T : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ - I * U) (σ' - I * T)) atTop
      (𝓝 (- LowerUIntegral f σ σ' T)) := by
  have h_re  (s : ℝ) (t : ℝ) : (s  - I * t).re = s  := by simp
  have h_im  (s : ℝ) (t : ℝ) : (s  - I * t).im = -t  := by simp
  have hbot' :
      Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x - y * I)) atTop (𝓝 0) := by
    convert (hbot.comp tendsto_neg_atTop_atBot) using 1
    ext; simp only [Function.comp_apply, ofReal_neg, neg_mul]; rfl
  have htop : Tendsto (fun (_ : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x - T * I)) atTop
      (𝓝 <| ∫ (x : ℝ) in σ..σ', f (x - T * I)) := tendsto_const_nhds
  have hvert (s : ℝ) (int : Integrable (fun (y : ℝ) ↦ f (s + y * I))) :
      Tendsto (fun (U : ℝ) ↦ I * ∫ (y : ℝ) in -U..-T, f (s + y * I)) atTop
        (𝓝 <| I * ∫ (y : ℝ) in Iic (-T), f (s + y * I)) := by
    have := (intervalIntegral_tendsto_integral_Iic (-T) int.restrict tendsto_id).const_smul I
    convert! (this.comp tendsto_neg_atTop_atBot) using 1
  have := ((hbot'.sub htop).add (hvert σ' hright)).sub (hvert σ hleft)
  rw [zero_sub] at this
  simp_rw [RectangleIntegral, LowerUIntegral, HIntegral, VIntegral, h_re, h_im, ofReal_neg, neg_mul,
    neg_add_rev, neg_sub]
  have final :
      (((-∫ (x : ℝ) in σ..σ', f (↑x - ↑T * I)) +
          I * ∫ (y : ℝ) in Iic (-T), f (↑σ' + ↑y * I)) -
          I * ∫ (y : ℝ) in Iic (-T), f (↑σ + ↑y * I)) =
      (-(I * ∫ (y : ℝ) in Iic (-T), f (↑σ + ↑y * I)) +
        ((I * ∫ (y : ℝ) in Iic (-T), f (↑σ' + ↑y * I)) -
          ∫ (x : ℝ) in σ..σ', f (↑x - ↑T * I))) := by
    ring_nf
    congr
    ext
    ring_nf
  exact final ▸ this
--%\end{proof}

/-
TODO : Move to general section
-/

lemma limitOfConstant {a : ℝ → ℂ} {σ : ℝ} (σpos : 0 < σ)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : 0 < σ') (_ : 0 < σ''), a σ' = a σ'')
    (ha' : Tendsto a atTop (𝓝 0)) : a σ = 0 := by
  /-
  \begin{align*}
  \lim_{\sigma'\to\infty}a(\sigma) &= \lim_{\sigma'\to\infty}a(\sigma') \\
  &= 0
  \end{align*}
  -/
  have := eventuallyEq_of_mem (mem_atTop σ) fun σ' h ↦ ha σ' σ (σpos.trans_le h) σpos
  exact tendsto_const_nhds_iff.mp (ha'.congr' this)


lemma limitOfConstantLeft {a : ℝ → ℂ} {σ : ℝ} (σlt : σ ≤ -3 / 2)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : σ' ≤ -3 / 2) (_ : σ'' ≤ -3 / 2), a σ' = a σ'')
    (ha' : Tendsto a atBot (𝓝 0)) : a σ = 0 := by
  /-
  \begin{align*}
    \lim_{\sigma'\to-\infty}a(\sigma) &= \lim_{\sigma'\to-\infty}a(\sigma') \\
    &= 0
  \end{align*}
  -/
  have := eventuallyEq_of_mem (mem_atBot (-3/2)) fun σ' h ↦ ha σ' σ h σlt
  exact tendsto_const_nhds_iff.mp (ha'.congr' this)


lemma tendsto_rpow_atTop_nhds_zero_of_norm_lt_one {x : ℝ} (xpos : 0 < x) (x_lt_one : x < 1)
    (C : ℝ) :
    Tendsto (fun (σ : ℝ) ↦ x ^ σ * C) atTop (𝓝 0) := by
  have := Tendsto.mul_const C (tendsto_rpow_atTop_of_base_lt_one x (by linarith) x_lt_one)
  simpa only [rpow_eq_pow, zero_mul] using this


lemma tendsto_rpow_atTop_nhds_zero_of_norm_gt_one {x : ℝ} (x_gt_one : 1 < x) (C : ℝ) :
    Tendsto (fun (σ : ℝ) ↦ x ^ σ * C) atBot (𝓝 0) := by
  have := (zero_lt_one.trans x_gt_one)
  have h := tendsto_rpow_atTop_nhds_zero_of_norm_lt_one (inv_pos.mpr this)
    (inv_lt_one_of_one_lt₀ x_gt_one) C
  convert (h.comp tendsto_neg_atBot_atTop) using 1
  ext; simp only [this.le, inv_rpow, Function.comp_apply, rpow_neg, inv_inv]


-- -- TODO: move near `Complex.cpow_neg`?
-- lemma Complex.cpow_inv_ofReal_pos {a : ℝ} (ha : 0 ≤ a) (r : ℂ) :
--     ((a : ℂ) ^ r)⁻¹ = (a : ℂ)⁻¹ ^ r := by

lemma Complex.cpow_eq_exp_log_ofReal (x : ℝ) (hx : 0 < x) (y : ℂ) :
    (x : ℂ) ^ y = Complex.exp (Real.log x * y) := by
  simp [← Complex.cpow_eq_pow, Complex.cpow, hx.ne.symm, ← Complex.ofReal_log hx.le]

-- TODO: move near `Complex.mul_cpow_ofReal_nonneg`
lemma Complex.cpow_neg_eq_inv_pow_ofReal_pos {a : ℝ} (ha : 0 < a) (r : ℂ) :
    (a : ℂ) ^ (-r) = (a⁻¹ : ℂ) ^ r := by
  rw [cpow_neg, ← Complex.inv_cpow]
  exact slitPlane_arg_ne_pi (Or.inl ha)

namespace Perron

variable {x σ σ' σ'' T : ℝ}

noncomputable abbrev f (x : ℝ) := fun (s : ℂ) ↦ x ^ s / (s * (s + 1))


lemma f_mul_eq_f {x t : ℝ} (tpos : 0 < t) (xpos : 0 < x) (s : ℂ) :
    f t s * (x : ℂ) ^ (-s) = f (t / x) s := by
  by_cases s_eq_zero : s = 0
  · simp [f, s_eq_zero]
  by_cases s_eq_neg_one : s = -1
  · simp [f, s_eq_neg_one]
  field_simp [f, s_eq_zero,
    show s + 1 ≠ 0 from fun hs ↦ add_eq_zero_iff_eq_neg.mp hs |> s_eq_neg_one]
  convert (Complex.mul_cpow_ofReal_nonneg tpos.le (inv_pos.mpr xpos).le s).symm using 2
  · convert Complex.cpow_neg_eq_inv_pow_ofReal_pos xpos s
    exact ofReal_inv x
  · norm_cast


lemma isHolomorphicOn (xpos : 0 < x) : HolomorphicOn (f x) {0, -1}ᶜ := by
  /- Composition of differentiabilities. -/
  unfold f
  simp_rw [Complex.cpow_def_of_ne_zero <| ofReal_ne_zero.mpr <| ne_of_gt xpos]
  apply DifferentiableOn.div
    <| DifferentiableOn.cexp <| DifferentiableOn.const_mul differentiableOn_id _
  · exact DifferentiableOn.mul differentiableOn_id
      <| DifferentiableOn.add_const _ differentiableOn_id
  · intro x hx
    obtain ⟨h0, h1⟩ := not_or.mp hx
    exact mul_ne_zero h0 <| add_ne_add_left 1 |>.mpr h1 |>.trans_eq (neg_add_cancel 1)


lemma integral_one_div_const_add_sq_pos (c : ℝ) (hc : 0 < c) :
    0 < ∫ (t : ℝ), 1 / (c + t ^ 2) := by
  have hfun_eq (t : ℝ) : 1 / (c + t ^ 2) = c⁻¹ * (1 + (c.sqrt⁻¹ * t) ^ 2)⁻¹ := by
    field_simp [hc.ne.symm]
    simp [hc.le]
    ring
  simp_rw [hfun_eq, integral_const_mul,
    Measure.integral_comp_mul_left (fun t ↦ (1 + t ^ 2)⁻¹) (a:=c.sqrt⁻¹)]
  simp [abs_eq_self.mpr <| Real.sqrt_nonneg c,
    mul_pos (inv_pos.mpr hc) <| mul_pos (sqrt_pos.mpr hc) Real.pi_pos]

lemma Integrable.one_div_const_add_sq (c : ℝ) (hc : 0 < c) :
    Integrable fun (t : ℝ) ↦ 1 / (c + t ^ 2) :=
  .of_integral_ne_zero (integral_one_div_const_add_sq_pos c hc).ne'

lemma integralPosAux'_of_le (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (hle : c₁ ≤ c₂) :
    0 < ∫ (t : ℝ), 1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) := by
  have c₂_pos : 0 < c₂ := by linarith
  have hlower (t : ℝ) :
      1 / (c₂ + t ^ 2) ≤ 1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) := by
    gcongr
    calc
      _ ≤ (c₂ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt := by gcongr
      _ ≤ c₂ + t ^ 2 := by rw [← Real.sqrt_mul, sqrt_mul_self] <;> positivity
  have hupper (t : ℝ) :
      1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) ≤ 1 / (c₁ + t ^ 2) := by
      gcongr
      calc
        _ ≥ (c₁ + t ^ 2).sqrt * (c₁ + t ^ 2).sqrt := by gcongr
        _ ≥ c₁ + t ^ 2 := by rw [← Real.sqrt_mul, sqrt_mul_self] <;> positivity
  calc 0 < ∫ t, 1 / (c₂ + t^2) := integral_one_div_const_add_sq_pos c₂ c₂_pos
       _ ≤ ∫ t, 1 / (Real.sqrt (c₁ + t^2) * Real.sqrt (c₂ + t^2)) := ?_
  refine integral_mono (Integrable.one_div_const_add_sq c₂ c₂_pos) ?_ hlower
  apply MeasureTheory.Integrable.mono (g := fun t : ℝ ↦ 1 / (c₁ + t ^ 2))
    <| Integrable.one_div_const_add_sq c₁ c₁_pos
  · refine (measurable_const.div <| Measurable.mul ?_ ?_).aestronglyMeasurable <;>
      exact (measurable_const.add <| measurable_id'.pow_const 2).sqrt
  · refine ae_of_all _ (fun x ↦ ?_)
    repeat rewrite [norm_of_nonneg (by positivity)]
    exact hupper x


lemma integralPosAux' (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (c₂_pos : 0 < c₂) :
    0 < ∫ (t : ℝ), 1 / ((c₁ + t^2).sqrt * (c₂ + t^2).sqrt) := by
  by_cases hc : c₁ ≤ c₂
  · exact integralPosAux'_of_le c₁ c₂ c₁_pos hc
  · convert integralPosAux'_of_le c₂ c₁ c₂_pos (by linarith) using 4; rw [mul_comm]


lemma integralPosAux : 0 < ∫ (t : ℝ), 1 / ((1 + t^2).sqrt * (2 + t^2).sqrt) := by
  /- This integral is between $\frac{1}{2}$ and $1$ of the integral of $\frac{1}{1+t^2}$,
  which is $\pi$. -/
  apply integralPosAux' <;> norm_num


lemma vertIntBound (xpos : 0 < x) (σ_gt_one : 1 < σ) :
    ‖VerticalIntegral (f x) σ‖ ≤
      x ^ σ * ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt) := by
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (‖σ + t * I‖ * ‖σ + t * I + 1‖) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt) :=
        mul_le_mul_of_nonneg_left ?_ (rpow_nonneg xpos.le _)
  · simp [VerticalIntegral]
  · simp [Complex.norm_cpow_eq_rpow_re_of_pos xpos]
  · simp [integral_const_mul, div_eq_mul_inv]
  · by_cases hint : Integrable fun (a : ℝ) ↦ 1 / (‖σ + a * I‖ * ‖σ + a * I + 1‖)
    swap
    · rw [integral_undef hint]; exact integral_nonneg <| fun t ↦ by positivity
    conv => rhs; rhs; intro a; rhs
    apply integral_mono hint
    · have := integralPosAux
      contrapose! this
      simp_rw [integral_undef this, le_rfl]
    rw [Pi.le_def]
    intro t
    gcongr <;> rw [Complex.norm_def] <;> apply Real.sqrt_le_sqrt
    · simp_rw [normSq_add_mul_I, add_le_add_iff_right, one_le_pow₀ σ_gt_one.le]
    · rw [add_right_comm, ← ofReal_one, ← ofReal_add, normSq_add_mul_I, add_le_add_iff_right]
      nlinarith
  rfl


lemma vertIntBoundLeft (xpos : 0 < x) :
    ∃ C, ∀ (σ : ℝ) (_ : σ < -3 / 2), ‖VerticalIntegral' (f x) σ‖ ≤ C * x ^ σ := by

  /- This proof is adapted from `vertIntBound` -/
  use 1 / (2 * π) *
    ‖(∫ (t : ℝ), 1 / ((4⁻¹ + t ^ 2).sqrt * (4⁻¹ + t ^ 2).sqrt : ℂ))‖
  intro σ hσ
  simp only [VerticalIntegral', smul_eq_mul, norm_mul]
  rw [(by simp [pi_nonneg] : ‖1 / (2 * ↑π * I)‖ = 1 / (2 * π)), mul_assoc]
  apply (mul_le_mul_iff_right₀ (by simp [pi_pos])).mpr
  calc
    _ = ‖∫ (t : ℝ), x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ ≤ ∫ (t : ℝ), ‖x ^ (σ + t * I) / ((σ + t * I) * (σ + t * I + 1))‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ (t : ℝ), x ^ σ / ‖((σ + t * I) * (σ + t * I + 1))‖ := ?_
    _ = x ^ σ * ∫ (t : ℝ), 1 / (‖σ + t * I‖ * ‖σ + t * I + 1‖) := ?_
    _ ≤ x ^ σ * ∫ (t : ℝ), 1 / ((4⁻¹ + t ^ 2).sqrt * (4⁻¹ + t ^ 2).sqrt) := ?_
    _ ≤ _ := ?_
  · simp [VerticalIntegral]
  · congr with t
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos xpos, add_re, ofReal_re,
      re_ofReal_mul, I_re, mul_zero, add_zero]
  · simp_rw [div_eq_mul_inv, integral_const_mul, one_mul, norm_mul]
  · gcongr x ^ σ * ?_
    by_cases hint : Integrable fun (a : ℝ) ↦ 1 / (‖σ + ↑a * I‖ * ‖σ + ↑a * I + 1‖)
    swap
    · rw [integral_undef hint]
      exact integral_nonneg <| fun t ↦ by simp only [Pi.zero_apply]; positivity
    apply integral_mono hint
    · have := integralPosAux' (4⁻¹) (4⁻¹) (by norm_num) (by norm_num)
      contrapose! this
      simp_rw [integral_undef this, le_rfl]
    rw [Pi.le_def]
    intro t
    gcongr <;> rw [Complex.norm_def] <;> apply Real.sqrt_le_sqrt
    · rw [normSq_add_mul_I, add_le_add_iff_right]; ring_nf; nlinarith
    · rw [(by push_cast; ring : σ + t * I + 1 = ofReal (σ + 1) + t * I),
        normSq_add_mul_I, add_le_add_iff_right]; ring_nf; nlinarith
  · rw [mul_comm]
    gcongr
    · have : 0 ≤ ∫ (t : ℝ), 1 / (Real.sqrt (4⁻¹ + t ^ 2) * Real.sqrt (4⁻¹ + t ^ 2)) :=
        by positivity
      rw [← norm_of_nonneg this, ← Complex.norm_real]
      apply le_of_eq; congr; norm_cast


lemma map_conj (hx : 0 ≤ x) (s : ℂ) : f x (conj s) = conj (f x s) := by
  simp only [f, map_div₀, map_mul, map_add, map_one]
  congr
  rw [cpow_conj, Complex.conj_ofReal]
  rw [Complex.arg_ofReal_of_nonneg hx]
  exact pi_ne_zero.symm

theorem isTheta_uniformlyOn_uIcc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 [[σ', σ'']] ×ˢ (atBot ⊔ atTop)]
    ((fun y ↦ 1 / y^2) ∘ Prod.snd) := by
  set l := 𝓟 [[σ', σ'']] ×ˢ (atBot ⊔ atTop : Filter ℝ) with hl
  refine IsTheta.div (isTheta_norm_left.mp ?_) ?_
  · suffices (fun (σ, _y) ↦ |x| ^ σ) =Θ[l] fun _ ↦ (1 : ℝ) by
      simpa [Complex.norm_cpow_of_ne_zero <| ofReal_ne_zero.mpr (ne_of_gt xpos),
        arg_ofReal_of_nonneg xpos.le] using this
    exact (continuousOn_const.rpow continuousOn_id fun _ _ ↦
        Or.inl <| ne_of_gt (abs_pos_of_pos xpos))
      |>.const_isThetaUniformlyOn_isCompact isCompact_uIcc (by norm_num)
      (fun i _ ↦ ne_of_gt <| rpow_pos_of_pos (abs_pos_of_pos xpos) _) _
  · have h_c {c : ℂ} : (fun (_ : ℝ × ℝ) ↦ c) =o[l] Prod.snd := by
      rewrite [hl, Filter.prod_sup, isLittleO_sup]
      exact ⟨isLittleO_const_snd_atBot c _, isLittleO_const_snd_atTop c _⟩
    have h_yI : (fun ((_σ, y) : ℝ × ℝ) ↦ y * I) =Θ[l] Prod.snd :=
      IsTheta.of_norm_eventuallyEq_norm (by simp)
    have h_σ_yI : (fun (σy : ℝ × ℝ) ↦ σy.1 + σy.2 * I) =Θ[l] Prod.snd := by
      refine IsLittleO.add_isTheta ?_ h_yI
      exact continuous_ofReal.continuousOn.const_isBigOUniformlyOn_isCompact isCompact_uIcc
        (by norm_num : ‖(1 : ℂ)‖ ≠ 0) _ |>.trans_isLittleO h_c
    simp_rw [sq]; exact h_σ_yI.mul (h_σ_yI.add_isLittleO h_c)

theorem isTheta_uniformlyOn_uIoc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 (uIoc σ' σ'') ×ˢ (atBot ⊔ atTop)]
    fun (_, y) ↦ 1 / y^2 := by
  refine (𝓟 (uIoc σ' σ'')).eq_or_neBot.casesOn (fun hbot ↦ by simp [hbot]) (fun _ ↦ ?_)
  haveI : NeBot (atBot (α := ℝ) ⊔ atTop) := sup_neBot.mpr (Or.inl atBot_neBot)
  exact (isTheta_uniformlyOn_uIcc xpos σ' σ'').mono (by simpa using! Ioc_subset_Icc_self)

lemma isTheta (xpos : 0 < x) :
    ((fun (y : ℝ) ↦ f x (σ + y * I)) =Θ[atBot] fun (y : ℝ) ↦ 1 / y^2) ∧
    (fun (y : ℝ) ↦ f x (σ + y * I)) =Θ[atTop] fun (y : ℝ) ↦ 1 / y^2 :=
  isTheta_sup.mp <| isTheta_of_isThetaUniformly (isTheta_uniformlyOn_uIcc xpos σ σ) left_mem_uIcc


lemma isIntegrable (xpos : 0 < x) (σ_ne_zero : σ ≠ 0) (σ_ne_neg_one : σ ≠ -1) :
    Integrable fun (t : ℝ) ↦ f x (σ + t * I) := by
  /- By \ref{isHolomorphicOn}, $f$ is continuous, so it is integrable on any interval. -/
  have : Continuous (fun (y : ℝ) ↦ f x (σ + y * I)) := by
    refine (isHolomorphicOn xpos).continuousOn.comp_continuous (by continuity) fun x ↦
      not_or.mpr ?_
    simp [Complex.ext_iff, σ_ne_zero, σ_ne_neg_one]
  /- Also, $|f(x)| = \Theta(x^{-2})$ as $x\to\infty$, -/
  refine this.locallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (univ_mem' fun y ↦ ?_) (isTheta xpos).2.isBigO ⟨Ioi 1, Ioi_mem_atTop 1, ?_⟩
  · /- and $|f(-x)| = \Theta(x^{-2})$ as $x\to\infty$. -/
    change ‖f x (↑σ + ↑y * I)‖ = ‖f x (↑σ + ↑(-y) * I)‖
    have : (↑σ + ↑(-y) * I) = conj (↑σ + ↑y * I) := Complex.ext (by simp) (by simp)
    simp_rw [this, map_conj xpos.le, norm_conj]
  · /- Since $g(x) = x^{-2}$ is integrable on $[a,\infty)$ for any $a>0$, we conclude. -/
    refine integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num)
      (show (0 : ℝ) < 1 by norm_num) |>.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := (show (0 : ℝ) < 1 by norm_num).trans hy
    change (y : ℝ) ^ (-2 : ℝ) = 1 / y ^ 2
    rw [eq_div_iff (pow_ne_zero 2 hy0.ne'), ← rpow_natCast y 2, ← rpow_add hy0]
    norm_num

theorem horizontal_integral_isBigO {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] :
    (fun (y : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + y * I) ∂μ) =O[atBot ⊔ atTop]
      fun y ↦ 1 / y^2 := by
  let g := fun ((σ, y) : ℝ × ℝ) ↦ f x (σ + y * I)
  calc
    _ =Θ[atBot ⊔ atTop] fun (y : ℝ) ↦ ∫ (σ : ℝ) in uIoc σ' σ'', g (σ, y) ∂μ :=
        IsTheta.of_norm_eventuallyEq_norm <| univ_mem'
          fun _ ↦ intervalIntegral.norm_intervalIntegral_eq _ _ _ _
    _ =O[atBot ⊔ atTop] fun y ↦ 1 / y^2 :=
      (isTheta_uniformlyOn_uIoc xpos σ' σ'').isBigO.set_integral_isBigO
        (g := fun x => 1 / (x ^ 2))
        measure_Ioc_lt_top


lemma tendsto_zero_Lower (xpos : 0 < x) (σ' σ'' : ℝ) :
    Tendsto (fun (t : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atBot (𝓝 0) := by

  have hcast : (fun (y : ℝ) ↦ 1 / y ^ 2) =ᶠ[atBot] fun y ↦ (-y) ^ (-2 : ℝ) := by
    filter_upwards [Iic_mem_atBot 0] with y hy using
      by rw [rpow_neg (neg_nonneg.mpr hy), inv_eq_one_div, rpow_two, neg_sq]
  exact isBigO_sup.mp (horizontal_integral_isBigO xpos σ' σ'' volume)
    |>.1.trans_eventuallyEq hcast |>.trans_tendsto
    <| tendsto_rpow_neg_atTop (by norm_num) |>.comp tendsto_neg_atBot_atTop


lemma tendsto_zero_Upper (xpos : 0 < x) (σ' σ'' : ℝ) :
    Tendsto (fun (t : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atTop (𝓝 0) := by

  have hcast : (fun (y : ℝ) ↦ 1 / y ^ 2) =ᶠ[atTop] fun y ↦ y ^ (-2 : ℝ) := by
    filter_upwards [Ici_mem_atTop 0] with y hy using by rw [rpow_neg hy, inv_eq_one_div, rpow_two]
  refine isBigO_sup.mp (horizontal_integral_isBigO xpos σ' σ'' volume)
    |>.2.trans_eventuallyEq hcast |>.trans_tendsto <| tendsto_rpow_neg_atTop (by norm_num)

lemma contourPull {σ' σ'' : ℝ} (xpos : 0 < x) (hσ0 : 0 ∉ [[σ', σ'']])
    (hσ1 : -1 ∉ [[σ', σ'']]) :
    VerticalIntegral (f x) σ' = VerticalIntegral (f x) σ'' := by
  refine verticalIntegral_eq_verticalIntegral ((isHolomorphicOn xpos).mono ?_)
    (tendsto_zero_Lower xpos σ' σ'') (tendsto_zero_Upper xpos σ' σ'')
    (isIntegrable xpos (fun h ↦ hσ0 (h ▸ left_mem_uIcc))
      (fun h ↦ hσ1 (h ▸ left_mem_uIcc)))
    (isIntegrable xpos (fun h ↦ hσ0 (h ▸ right_mem_uIcc))
      (fun h ↦ hσ1 (h ▸ right_mem_uIcc)))
  rintro ⟨x, y⟩ ⟨hx, hy⟩ ⟨hc | hc⟩ <;> simp_all [Complex.ext_iff]

/-
We are ready for the first case of the Perron formula, namely when $x<1$:
-/

lemma formulaLtOne (xpos : 0 < x) (x_lt_one : x < 1) (σ_pos : 0 < σ)
    : VerticalIntegral (f x) σ = 0 := by
  /-
  Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on the half-plane
  $\{s\in\mathbb{C}:\Re(s)>0\}$. The rectangle integral of $f$ with corners $\sigma-iT$ and
  $\sigma+iT$ is zero. The limit of this rectangle integral as $T\to\infty$ is
  $\int_{(\sigma')}-\int_{(\sigma)}$. Therefore, $\int_{(\sigma')}=\int_{(\sigma)}$.
  -/
  have h_contourPull (σ' σ'' : ℝ) (σ'pos : 0 < σ') (σ''pos : 0 < σ'') :
      VerticalIntegral (f x) σ' = VerticalIntegral (f x) σ'' :=
    contourPull xpos (notMem_uIcc_of_lt σ'pos σ''pos)
      (notMem_uIcc_of_lt (by linarith) (by linarith))
  /-
  But we also have the bound $\int_{(\sigma')} \leq x^{\sigma'} * C$, where
  $C=\int_\R\frac{1}{|(1+t)(1+t+1)|}dt$.
  -/
  have VertIntBound : ∃ C > 0, ∀ σ' > 1, ‖VerticalIntegral (f x) σ'‖ ≤ x^σ' * C := by
    let C := ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt)
    exact ⟨C, integralPosAux, fun _ ↦ vertIntBound xpos⟩
  /- Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$. -/
  have AbsVertIntTendsto :
      Tendsto ((‖·‖ : ℂ → ℝ) ∘ (VerticalIntegral (f x))) atTop (𝓝 0) := by
    obtain ⟨C, _, hC⟩ := VertIntBound
    have := tendsto_rpow_atTop_nhds_zero_of_norm_lt_one xpos x_lt_one C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    · filter_upwards; exact fun _ ↦ norm_nonneg _
    · filter_upwards [eventually_gt_atTop 1]; exact hC
  have VertIntTendsto : Tendsto (VerticalIntegral (f x)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr AbsVertIntTendsto
  /- So pulling contours gives $\int_{(\sigma)}=0$. -/
  exact limitOfConstant σ_pos h_contourPull VertIntTendsto

/-
The second case is when $x>1$.
Here are some auxiliary lemmata for the second case.
TODO: Move to more general section
-/

theorem HolomorphicOn.upperUIntegral_eq_zero {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ T ≤ z.im})
    (htop : Tendsto (fun y : ℝ ↦ ∫ (x : ℝ) in σ..σ', f (↑x + ↑y * I)) atTop (𝓝 0))
    (hleft : Integrable fun y : ℝ ↦ f (↑σ + ↑y * I))
    (hright : Integrable fun y : ℝ ↦ f (↑σ' + ↑y * I)) :
    UpperUIntegral f σ σ' T = 0 := by
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_UpperU htop hleft hright)
  apply EventuallyEq.tendsto
  filter_upwards [eventually_ge_atTop T]
  refine fun _ hTU ↦ hf.vanishesOnRectangle fun _ ↦ ?_
  rw [mem_Rect (by simp [hσ]) (by simp [hTU])]
  simpa using by tauto

theorem HolomorphicOn.lowerUIntegral_eq_zero {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ z.im ≤ -T})
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : Integrable fun y : ℝ ↦ f (↑σ + ↑y * I))
    (hright : Integrable fun y : ℝ ↦ f (↑σ' + ↑y * I)) :
    LowerUIntegral f σ σ' T = 0 := by
  suffices h : - LowerUIntegral f σ σ' T = 0 by exact neg_eq_zero.mp h
  apply tendsto_nhds_unique (RectangleIntegral_tendsTo_LowerU hbot hleft hright)
  apply EventuallyEq.tendsto
  filter_upwards [eventually_ge_atTop T]
  refine fun _ hTU ↦ hf.vanishesOnRectangle fun _ ↦ ?_
  rw [mem_Rect (by simp [hσ]) (by simp [hTU])]
  simpa using by tauto

lemma sPlusOneNeZero {s : ℂ} (s_ne_neg_one : s ≠ -1) : s + 1 ≠ 0 :=
  fun h ↦ s_ne_neg_one (add_eq_zero_iff_eq_neg.mp h)


lemma keyIdentity (x : ℝ) {s : ℂ} (s_ne_zero : s ≠ 0) (s_ne_neg_one : s ≠ -1) :
    (x : ℂ) ^ s / (s * (s + 1))
      = (x : ℂ) ^ s / s - (x : ℂ) ^ s / (s + 1) := by
    field_simp [sPlusOneNeZero, mul_ne_zero]; ring_nf


variable {α β : Type*} [LinearOrder β] [NoMaxOrder β] [TopologicalSpace β]
  [ClosedIciTopology β] {y : β} {l : Filter α}

lemma _root_.Filter.Tendsto.eventually_bddAbove {f : α → β} (hf : Tendsto f l (𝓝 y)) :
    ∀ᶠ s in l.smallSets, BddAbove (f '' s) := by
  obtain ⟨y', hy'⟩ := exists_gt y
  obtain ⟨s, hsl, hs⟩ := (Tendsto.eventually_le_const hy' hf).exists_mem
  simp_rw [Filter.eventually_smallSets, bddAbove_def]
  refine ⟨s, hsl, fun t ht ↦ ⟨y', fun y hy ↦ ?_⟩⟩
  obtain ⟨x, hxt, hxy⟩ := hy
  exact hxy ▸ hs x (ht hxt)

lemma bddAbove_square_of_tendsto {f : ℂ → β} {x : ℂ}
    (hf : Tendsto f (𝓝[≠] x) (𝓝 y)) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, BddAbove (f '' (Square x c \ {x})) := by
  obtain ⟨t, htf, ht⟩ := eventually_smallSets.mp hf.eventually_bddAbove
  obtain ⟨ε, hε0, hε⟩ := nhdsWithin_hasBasis (nhds_hasBasis_square x) {x}ᶜ |>.1 t |>.mp htf
  filter_upwards [Ioo_mem_nhdsGT hε0] with ε' ⟨hε'0, hε'⟩
  exact ht _ <| (Set.sdiff_subset_sdiff (square_subset_square hε'0 hε'.le) subset_rfl).trans hε


lemma diffBddAtZero {x : ℝ} (xpos : 0 < x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0,
      BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - 1 / s)) ''
        (Square 0 c \ {0})) := by

  apply bddAbove_square_of_tendsto
  suffices
      Tendsto
        (norm ∘ (fun (s : ℂ) ↦ ↑x ^ s / s - ↑x ^ (0 : ℂ) / s - ↑x ^ s / (1 + s)))
        (𝓝[≠] 0)
        (𝓝 (‖(deriv (fun (s : ℂ) ↦ (x : ℂ) ^ s) 0) -
          x ^ (0 : ℂ) / (1 + 0)‖))
    by
    apply this.congr'
    filter_upwards
      [sdiff_mem_nhdsWithin_compl (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr (by norm_num : (0 : ℂ) ≠ -1))) {0}]
    with s hs
    rw [Function.comp_apply, Function.comp_apply, keyIdentity _ hs.2 hs.1, cpow_zero]; ring_nf
  have hx0 : (x : ℂ) ≠ 0 := slitPlane_ne_zero (.inl xpos)
  refine (Tendsto.sub ?_ (tendsto_nhdsWithin_of_tendsto_nhds ?_)).norm
  · convert hasDerivAt_iff_tendsto_slope.mp
      (differentiableAt_fun_id.const_cpow (.inl hx0)).hasDerivAt using 2
    rw [slope_def_field]; ring
  · exact (continuous_id.const_cpow (.inl hx0)).tendsto 0
      |>.div (tendsto_const_nhds.add tendsto_id) (by norm_num)


lemma diffBddAtNegOne {x : ℝ} (xpos : 0 < x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0,
      BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) -
          (-x⁻¹) / (s + 1))) '' (Square (-1) c \ {-1})) := by

  apply bddAbove_square_of_tendsto
  suffices
      Tendsto (norm ∘ (fun (s : ℂ) ↦ ↑x ^ s / s - (↑x ^ s / (s + 1) - x⁻¹ / (s + 1))))
        (𝓝[≠] (-1))
        (𝓝 (‖x ^ (-1 : ℂ) / -1 - (deriv (fun (s : ℂ) ↦ (x : ℂ) ^ s) (-1))‖))
    by
    apply this.congr'
    filter_upwards
      [sdiff_mem_nhdsWithin_compl (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr (by norm_num : (-1 : ℂ) ≠ 0))) {-1}]
    with s hs
    rw [Function.comp_apply, Function.comp_apply, keyIdentity _ hs.1 hs.2]
    ring_nf
  have hx0 : (x : ℂ) ≠ 0 := slitPlane_ne_zero (.inl xpos)
  refine (Tendsto.sub (tendsto_nhdsWithin_of_tendsto_nhds ?_) ?_).norm
  · exact ((continuous_id.const_cpow (.inl hx0)).tendsto _).div tendsto_id (by norm_num)
  · convert hasDerivAt_iff_tendsto_slope.mp
      (differentiableAt_fun_id.const_cpow (.inl hx0)).hasDerivAt using 2
    rw [slope_def_field, cpow_neg_one, ofReal_inv]; ring


lemma residueAtZero (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (f x) (-c - c * I) (c + c * I) = 1 := by
  /- For $c>0$ sufficiently small, -/
  filter_upwards
    [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1 / 2), diffBddAtZero xpos]
  intro c hc bddAbove
  obtain ⟨cpos, _⟩ := hc
  have RectSub : Square 0 c \ {0} ⊆ {0, -1}ᶜ := by
    refine fun s ⟨hs, hs0⟩ ↦ not_or.mpr ⟨hs0, ?_⟩
    rw [Square, mem_Rect (by simpa using by linarith) (by simp [cpos.le])] at hs
    replace hs : -c ≤ s.re ∧ s.re ≤ c ∧ -c ≤ s.im ∧ s.im ≤ c := by simpa using hs
    simpa [Complex.ext_iff] using fun h ↦ by linarith
  have fHolo : HolomorphicOn (f x) (Square 0 c \ {0}) := (isHolomorphicOn xpos).mono RectSub
  have f1Holo : HolomorphicOn ((f x) - (fun (s : ℂ) ↦ 1 / s)) (Square 0 c \ {0}) :=
    fHolo.sub (by simpa using differentiableOn_inv.mono fun s hs ↦ hs.2)

  have RectMemNhds : Square 0 c ∈ 𝓝 0 := square_mem_nhds 0 (ne_of_gt cpos)
  /-
  $x^s/(s(s+1))$ is equal to $1/s$ plus a function, $g$, say,
  holomorphic in the whole rectangle (by Lemma \ref{diffBddAtZero}).
  -/
  obtain ⟨g, gHolo, g_eq_fDiff⟩ :=
    existsDifferentiableOn_of_bddAbove RectMemNhds f1Holo bddAbove
  simp_rw [Square, add_zero] at fHolo gHolo RectMemNhds
  /- Now apply Lemma \ref{ResidueTheoremOnRectangleWithSimplePole}. -/
  refine ResidueTheoremOnRectangleWithSimplePole ?_ ?_ RectMemNhds gHolo ?_
  any_goals simpa using cpos.le
  convert g_eq_fDiff using 3 <;> simp [Square]


lemma residueAtNegOne (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (f x) (-c - c * I - 1) (c + c * I - 1) = -x⁻¹ := by
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1 / 2), diffBddAtNegOne xpos]
  intro c hc bddAbove
  obtain ⟨cpos, _⟩ := hc
  have h_mem {s : ℂ} (hs : s ∈ Square (-1) c) :
      -c ≤ s.re + 1 ∧ s.re + 1 ≤ c ∧ -c ≤ s.im ∧ s.im ≤ c := by
    rw [Square, mem_Rect (by simpa using by linarith) (by simp [cpos.le])] at hs
    simpa using hs
  have RectSub : Square (-1) c \ {-1} ⊆ {0, -1}ᶜ := by
    refine fun s ⟨hs, hs1⟩ ↦ not_or.mpr ⟨?_, hs1⟩
    simpa [Complex.ext_iff] using fun _ _ ↦ by linarith [h_mem hs]
  have fHolo : HolomorphicOn (f x) (Square (-1) c \ {-1}) := (isHolomorphicOn xpos).mono RectSub
  have f1Holo :
      HolomorphicOn ((f x) - (fun (s : ℂ) ↦ -x⁻¹ / (s + 1))) (Square (-1) c \ {-1}) := by
    refine fHolo.sub <| (differentiableOn_const _).neg.div ?_
      fun x hx ↦ sPlusOneNeZero hx.2
    exact differentiableOn_id.add (differentiableOn_const 1)
  have RectMemNhds : Square (-1) c ∈ 𝓝 (-1) := square_mem_nhds (-1) (ne_of_gt cpos)
  obtain ⟨g, gHolo, g_eq_fDiff⟩ :=
    existsDifferentiableOn_of_bddAbove RectMemNhds f1Holo bddAbove
  simp_rw [Square] at fHolo gHolo RectMemNhds
  refine ResidueTheoremOnRectangleWithSimplePole ?_ ?_ RectMemNhds gHolo ?_
  · simpa using cpos.le
  · simpa using cpos.le
  · convert! g_eq_fDiff using 3; simp


lemma residuePull1 (x_gt_one : 1 < x) (σ_pos : 0 < σ) :
    VerticalIntegral' (f x) σ = 1 + VerticalIntegral' (f x) (-1 / 2) := by

  apply eq_add_of_sub_eq
  have xpos : 0 < x := zero_lt_one.trans x_gt_one
  have hf : HolomorphicOn (f x) (Icc (-1 / 2) σ ×ℂ univ \ {0}) :=
    (isHolomorphicOn xpos).mono fun s ⟨⟨⟨_, _⟩, _⟩, hs0⟩ hc ↦ hc.casesOn
      (fun hc ↦ hs0 hc) (fun hc ↦ by linarith [show s.re = -1 from congrArg _ hc])
  have := (residueAtZero xpos).and <| verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    (by simpa using ⟨by linarith, by linarith⟩) hf
    (tendsto_zero_Lower xpos _ _) (tendsto_zero_Upper xpos _ _)
    (isIntegrable xpos (by norm_num) (by norm_num))
    (isIntegrable xpos (by linarith) (by linarith))
  obtain ⟨c, hcf, hc⟩ := this.exists_mem
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhdsWithin_iff.mp hcf
  obtain hε := hc (ε/2)
    (hεc ⟨mem_ball_iff_norm.mpr (by simp [abs_of_pos hε, hε]), half_pos hε⟩)
  rw [VerticalIntegral', ← smul_sub, hε.2, ← RectangleIntegral', add_zero, add_zero, hε.1]


lemma residuePull2 (x_gt_one : 1 < x) :
    VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) (-1 / 2)
    = -1 / x + VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) (-3 / 2) := by
  apply eq_add_of_sub_eq
  have xpos : 0 < x := zero_lt_one.trans x_gt_one
  have hf : HolomorphicOn (f x) (Icc (-3 / 2) (-1 / 2) ×ℂ univ \ {-1}) :=
    (isHolomorphicOn xpos).mono fun s ⟨⟨⟨_, _⟩, _⟩, hs1⟩ hc ↦ hc.casesOn
      (fun hc ↦ by linarith [show s.re = 0 from congrArg _ hc]) (fun hc ↦ hs1 hc)
  have := (residueAtNegOne xpos).and <| verticalIntegral_sub_verticalIntegral_eq_squareIntegral
    (by simpa using ⟨by linarith, by linarith⟩) hf
    (tendsto_zero_Lower xpos _ _) (tendsto_zero_Upper xpos _ _)
    (isIntegrable xpos (by norm_num) (by norm_num))
    (isIntegrable xpos (by norm_num) (by norm_num))
  obtain ⟨c, hcf, hc⟩ := this.exists_mem
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhdsWithin_iff.mp hcf
  replace hε := hc (ε/2)
    (hεc ⟨mem_ball_iff_norm.mpr (by simp [abs_of_pos, hε]), half_pos hε⟩)
  rw [VerticalIntegral', ← smul_sub, hε.2, ← RectangleIntegral', neg_div, one_div,
    ← ofReal_inv]
  exact hε.1


lemma contourPull3 (x_gt_one : 1 < x) (σ'le : σ' ≤ -3 / 2) (σ''le : σ'' ≤ -3 / 2) :
    VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) σ' =
      VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) σ'' := by

  unfold VerticalIntegral'
  congr 1
  exact contourPull (by linarith) (notMem_uIcc_of_gt (by linarith) (by linarith))
    (notMem_uIcc_of_gt (by linarith) (by linarith))


lemma formulaGtOne (x_gt_one : 1 < x) (σ_pos : 0 < σ) :
    VerticalIntegral' (fun s ↦ x^s / (s * (s + 1))) σ = 1 - 1 / x := by
  /- Let $f(s) = x^s/(s(s+1))$. Then $f$ is holomorphic on $\C \setminus {0,-1}$. -/
  set f : ℂ → ℂ := (fun s ↦ x^s / (s * (s + 1)))
  /- First pull the contour from $(\sigma)$ to $(-1/2)$, picking up a residue $1$ at $s=0$. -/
  rw [residuePull1 x_gt_one σ_pos]
  /- Next pull the contour from $(-1/2)$ to $(-3/2)$, picking up a residue $-1/x$ at
  $s=-1$. -/
  rw [residuePull2 x_gt_one]
  /- Then pull the contour all the way to $(\sigma')$ with $\sigma'<-3/2$. -/
  have contourPull₃ (σ' σ'' : ℝ) (hσ' : σ' ≤ -3/2) (hσ'' : σ'' ≤ -3/2) :
      VerticalIntegral' f σ' = VerticalIntegral' f σ'' :=
    contourPull3 x_gt_one hσ' hσ''
  /- For $\sigma' < -3/2$, the integral is bounded by
  $x^{\sigma'}\int_\R\frac{1}{|(1+t ^ 2)(2+t ^ 2)|^{1/2}}dt$. -/
  have VertIntBound : ∃ C, ∀ σ' < -3/2, ‖VerticalIntegral' f σ'‖ ≤ C * x ^ σ' :=
    vertIntBoundLeft (by linarith : 0 < x)
  /- Therefore $\int_{(\sigma')}\to 0$ as $\sigma'\to\infty$. -/
  have AbsVertIntTendsto :
      Tendsto ((‖·‖ : ℂ → ℝ) ∘ (VerticalIntegral' f)) atBot (𝓝 0) := by
    obtain ⟨C, hC⟩ := VertIntBound
    have := tendsto_rpow_atTop_nhds_zero_of_norm_gt_one x_gt_one C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
    · filter_upwards using fun _ ↦ norm_nonneg _
    · filter_upwards [eventually_lt_atBot (-3/2)]
      (conv at hC => intro σ hσ; rw [mul_comm]); exact fun _ ↦ hC _
  /- So pulling contours gives $\int_{(-3/2)}=0$. -/
  rw [limitOfConstantLeft (σ := -3/2) (Eq.le rfl) contourPull₃ ?_]
  · ring
  · exact tendsto_zero_iff_norm_tendsto_zero.mpr AbsVertIntTendsto


/-
The two together give the Perron formula. (Which doesn't need to be a separate lemma.)

For $x>0$ and $\sigma>0$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds = \begin{cases}
1-\frac1x & \text{ if }x>1\\
0 & \text{ if } x<1
\end{cases}.
$$
-/

end Perron

end

/-! ## ChenTheorem.Analysis.SiegelTaylorInequality -/

section

namespace Chen

theorem norm_tsum_nat_add_le_geometric {a : ℕ → ℂ} {M r : ℝ}
    (hr : 0 ≤ r) (hr' : r < 1) (ha : ∀ n, ‖a n‖ ≤ M * r ^ n) (k : ℕ) :
    ‖∑' n : ℕ, a (n + k)‖ ≤ M * r ^ k / (1 - r) := by
  have hg := (hasSum_geometric_of_lt_one hr hr').mul_left (M * r ^ k)
  have hb (n : ℕ) : ‖a (n + k)‖ ≤ M * r ^ k * r ^ n := by
    calc
      ‖a (n + k)‖ ≤ M * r ^ (n + k) := ha _
      _ = M * r ^ k * r ^ n := by rw [pow_add]; ring
  simpa only [div_eq_mul_inv] using tsum_of_norm_bounded hg hb

theorem powerSeries_tail_norm_le {a : ℕ → ℂ} {M r x : ℝ}
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hrx : r * x < 1)
    (ha : ∀ n, ‖a n‖ ≤ M * r ^ n) (k : ℕ) :
    ‖∑' n : ℕ, a (n + k) * (x : ℂ) ^ (n + k)‖ ≤
      M * (r * x) ^ k / (1 - r * x) := by
  refine norm_tsum_nat_add_le_geometric (a := fun n => a n * (x : ℂ) ^ n)
    (mul_nonneg hr hx) hrx ?_ k
  intro n
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg hx]
  calc
    ‖a n‖ * x ^ n ≤ (M * r ^ n) * x ^ n :=
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hx n)
    _ = M * (r * x) ^ n := by rw [mul_pow]; ring

theorem powerSeries_summable_of_geometric_bound {a : ℕ → ℂ} {M r x : ℝ}
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hrx : r * x < 1)
    (ha : ∀ n, ‖a n‖ ≤ M * r ^ n) :
    Summable (fun n : ℕ => a n * (x : ℂ) ^ n) := by
  apply ((summable_geometric_of_lt_one (mul_nonneg hr hx) hrx).mul_left M).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg hx]
  calc
    ‖a n‖ * x ^ n ≤ (M * r ^ n) * x ^ n :=
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hx n)
    _ = M * (r * x) ^ n := by rw [mul_pow]; ring

/-- Truncating a Taylor series with nonnegative uncorrected coefficients.
The coefficients `b n - ρ` are those of a function after removing its simple pole. -/
theorem siegelTaylor_lower_bound {b : ℕ → ℂ} {F : ℂ} {ρ M r x : ℝ}
    (hb : ∀ n, 0 ≤ (b n).re) (hb0 : 1 ≤ (b 0).re)
    (hx : 1 < x) (hr : 0 ≤ r) (hrx : r * x < 1)
    (hbound : ∀ n, ‖b n - (ρ : ℂ)‖ ≤ M * r ^ n)
    (hsum : HasSum (fun n : ℕ => (b n - (ρ : ℂ)) * (x : ℂ) ^ n)
      (F + ((ρ / (x - 1) : ℝ) : ℂ)))
    (k : ℕ) (hk : 1 ≤ k) :
    1 - ρ * x ^ k / (x - 1) - M * (r * x) ^ k / (1 - r * x) ≤ F.re := by
  have hx0 : 0 ≤ x := by linarith
  have hpartial : 1 ≤ ∑ n ∈ Finset.range k, (b n).re * x ^ n := by
    calc
      1 ≤ (b 0).re * x ^ 0 := by simpa using hb0
      _ ≤ ∑ n ∈ Finset.range k, (b n).re * x ^ n :=
        Finset.single_le_sum (fun n _ => mul_nonneg (hb n) (pow_nonneg hx0 n))
          (Finset.mem_range.mpr (by omega))
  have htail := powerSeries_tail_norm_le hr hx0 hrx hbound k
  have htailre := (Complex.abs_re_le_norm
    (∑' n : ℕ, (b (n + k) - (ρ : ℂ)) * (x : ℂ) ^ (n + k))).trans htail
  have he := hsum.summable.sum_add_tsum_nat_add k
  rw [hsum.tsum_eq] at he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_sum, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_im, mul_zero, sub_zero] at hre
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    geom_sum_eq (ne_of_gt hx)] at hre
  have ht := (abs_le.mp htailre).1
  simp only [← Complex.ofReal_pow, sub_mul] at ht
  have hid : ρ * (x ^ k - 1) / (x - 1) + ρ / (x - 1) = ρ * x ^ k / (x - 1) := by ring
  simp only [mul_div_assoc] at hid ht ⊢
  linarith

end Chen

end

/-! ## ChenTheorem.Analysis.SignedTaylorSeries -/

section

namespace Chen

/-- Taylor coefficients in powers of `c - s` rather than `s - c`. -/
noncomputable def backwardTaylorCoeff (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * (n.factorial : ℂ)⁻¹ * iteratedDeriv n f c

theorem norm_backwardTaylorCoeff_le {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖backwardTaylorCoeff f c n‖ ≤ M * (R⁻¹) ^ n := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hM
  have h := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hn.le)
  simp only [backwardTaylorCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    norm_inv, Complex.norm_natCast, one_mul]
  calc
    (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f c‖ ≤
        (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ) * M / R ^ n) := h
    _ = M * (R⁻¹) ^ n := by rw [inv_pow]; field_simp

theorem hasSum_backwardTaylorCoeff {f : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (hz : ‖z‖ < R) :
    HasSum (fun n : ℕ => backwardTaylorCoeff f c n * z ^ n) (f (c - z)) := by
  have hcz : c - z ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm, show c - z - c = -z by ring, norm_neg]
    exact hz
  have he : (fun n : ℕ => backwardTaylorCoeff f c n * z ^ n) =
      (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (c - z - c) ^ n • iteratedDeriv n f c) := by
    funext n
    have hpow : (-z) ^ n = (-1 : ℂ) ^ n * z ^ n := by rw [neg_eq_neg_one_mul, mul_pow]
    simp only [backwardTaylorCoeff, smul_eq_mul, show c - z - c = -z by ring, hpow]
    ring
  rw [he]
  exact Complex.hasSum_taylorSeries_on_ball hf hcz

open scoped ComplexOrder in
theorem backwardTaylorCoeff_nonneg_of_alternating {f : ℂ → ℂ} {c : ℂ}
    (h : ∀ n : ℕ, 0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n f c) (n : ℕ) :
    0 ≤ backwardTaylorCoeff f c n := by
  have hn : 0 ≤ (n.factorial : ℂ)⁻¹ := by positivity
  convert mul_nonneg hn (h n) using 1
  unfold backwardTaylorCoeff
  ring

end Chen

end

/-! ## ChenTheorem.Analysis.PoleTaylorCoefficients -/

section

namespace Chen

theorem backwardTaylorCoeff_inv_sub_one (n : ℕ) :
    backwardTaylorCoeff (fun s : ℂ => (s - 1)⁻¹) 2 n = 1 := by
  unfold backwardTaylorCoeff
  rw [iteratedDeriv_comp_sub_const]
  change (-1 : ℂ) ^ n * (n.factorial : ℂ)⁻¹ *
    iteratedDeriv n (Inv.inv : ℂ → ℂ) (2 - 1) = 1
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
  norm_num only [show (2 : ℂ) - 1 = 1 by norm_num, one_zpow, mul_one]
  have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℂ) ^ n * (-1) ^ n) *
        ((n.factorial : ℂ)⁻¹ * n.factorial) := by ring
    _ = 1 := by rw [hs, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), mul_one]

theorem backwardTaylorCoeff_const_mul (f : ℂ → ℂ) (c a : ℂ) (n : ℕ) :
    backwardTaylorCoeff (fun s => a * f s) c n = a * backwardTaylorCoeff f c n := by
  unfold backwardTaylorCoeff
  rw [iteratedDeriv_const_mul_field]
  ring

theorem backwardTaylorCoeff_pole (a : ℂ) (n : ℕ) :
    backwardTaylorCoeff (fun s : ℂ => a / (s - 1)) 2 n = a := by
  simp only [div_eq_mul_inv]
  rw [backwardTaylorCoeff_const_mul, backwardTaylorCoeff_inv_sub_one, mul_one]

theorem backwardTaylorCoeff_sub {f g : ℂ → ℂ} {c : ℂ} (n : ℕ)
    (hf : ContDiffAt ℂ n f c) (hg : ContDiffAt ℂ n g c) :
    backwardTaylorCoeff (fun s => f s - g s) c n =
      backwardTaylorCoeff f c n - backwardTaylorCoeff g c n := by
  unfold backwardTaylorCoeff
  rw [iteratedDeriv_fun_sub hf hg]
  ring

end Chen

end

/-! ## ChenTheorem.Analysis.SmallPowerDiskGeometry -/

section

namespace Chen

theorem exists_small_power_disk_radius {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ 3 * r ≤ 1 / 4 ∧ r < 1 / 4 ∧
      3 * Real.log 3 ≤ ε * (Real.log (1 / 4 : ℝ) - Real.log r) := by
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let M : ℝ := 3 * Real.log 3 / ε + Real.log 3 + 1
  have hM : Real.log (3 : ℝ) < M := by
    have h := div_nonneg (show 0 ≤ 3 * Real.log (3 : ℝ) by positivity) hε.le
    dsimp [M]
    linarith
  have hM0 : 0 < M := hlog.trans hM
  let r : ℝ := Real.exp (Real.log (1 / 4 : ℝ) - M)
  have hr : 0 < r := Real.exp_pos _
  have hlogr : Real.log r = Real.log (1 / 4 : ℝ) - M := Real.log_exp _
  have hrsmall : r ≤ 1 / 12 := by
    calc
      r ≤ Real.exp (Real.log (1 / 4 : ℝ) - Real.log 3) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]; norm_num
  refine ⟨r, hr, by linarith, by linarith, ?_⟩
  rw [hlogr]
  have hratio : 3 * Real.log (3 : ℝ) / ε ≤ M := by dsimp [M]; linarith
  have h := (div_le_iff₀ hε).mp hratio
  nlinarith

end Chen

end

/-! ## ChenTheorem.Analysis.ThreeCircleBound -/

section

open Complex.HadamardThreeLines

namespace Chen
/-- The three-circle estimate, obtained from mathlib's three-lines theorem by
composing an entire function with the complex exponential. -/
theorem norm_le_three_circle {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c z : ℂ} {r R A B : ℝ} (hr : 0 < r) (hrR : r < R)
    (hA : ∀ w, ‖w - c‖ ≤ r → ‖f w‖ ≤ A)
    (hB : ∀ w, ‖w - c‖ ≤ R → ‖f w‖ ≤ B)
    (hzr : r ≤ ‖z - c‖) (hzR : ‖z - c‖ ≤ R) :
    ‖f z‖ ≤ A ^ (1 - (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) *
      B ^ ((Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) := by
  have hR : 0 < R := hr.trans hrR
  have hz0 : z - c ≠ 0 := norm_pos_iff.mp (hr.trans_le hzr)
  have hlr : Real.log r < Real.log R := Real.log_lt_log hr hrR
  let F : ℂ → ℂ := fun w => f (c + Complex.exp w)
  have hF : Differentiable ℂ F := hf.comp (Complex.differentiable_exp.const_add c)
  have he (w : ℂ) : ‖c + Complex.exp w - c‖ = Real.exp w.re := by
    rw [add_sub_cancel_left, Complex.norm_exp]
  have hFR (w : ℂ) (hw : w ∈ verticalClosedStrip (Real.log r) (Real.log R)) : ‖F w‖ ≤ B := by
    apply hB
    rw [he]
    exact (Real.exp_le_exp.mpr hw.2).trans_eq (Real.exp_log hR)
  have hbounded : BddAbove ((norm ∘ F) '' verticalClosedStrip (Real.log r) (Real.log R)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hFR w hw
  have hleft : ∀ w ∈ Complex.re ⁻¹' {Real.log r}, ‖F w‖ ≤ A := by
    intro w hw
    apply hA
    rw [he, show w.re = Real.log r from hw, Real.exp_log hr]
  have hright : ∀ w ∈ Complex.re ⁻¹' {Real.log R}, ‖F w‖ ≤ B := by
    intro w hw
    apply hB
    rw [he, show w.re = Real.log R from hw, Real.exp_log hR]
  have hz : Complex.log (z - c) ∈ verticalClosedStrip (Real.log r) (Real.log R) := by
    change Real.log r ≤ (Complex.log (z - c)).re ∧ (Complex.log (z - c)).re ≤ Real.log R
    rw [Complex.log_re]
    exact ⟨Real.log_le_log hr hzr, Real.log_le_log (hr.trans_le hzr) hzR⟩
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlr hz hF.diffContOnCl hbounded hleft hright
  simpa only [F, Complex.exp_log hz0, add_sub_cancel, Complex.log_re] using h
end Chen

end

/-! ## ChenTheorem.Analysis.TwoDiskInterpolation -/

section

namespace Chen
/-- An inner bound independent of `q` and an outer cubic bound yield an arbitrarily
small power of `q` when the logarithmic separation of the circles is large enough. -/
theorem norm_le_small_power_of_two_disks {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c z : ℂ} {r R A C q ε : ℝ} (hr : 0 < r) (hrR : r < R)
    (hA : 1 ≤ A) (hC : 1 ≤ C) (hq : 1 ≤ q) (hε : 0 ≤ ε)
    (hscale : 3 * Real.log 3 ≤ ε * (Real.log R - Real.log r))
    (hinner : ∀ w, ‖w - c‖ ≤ r → ‖f w‖ ≤ A)
    (houter : ∀ w, ‖w - c‖ ≤ R → ‖f w‖ ≤ C * q ^ 3)
    (hz : ‖z - c‖ ≤ 3 * r) (hzR : ‖z - c‖ ≤ R) :
    ‖f z‖ ≤ A * C * q ^ ε := by
  have hq0 : 0 ≤ q := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hC0 : 0 ≤ C := by linarith
  by_cases hzr : ‖z - c‖ ≤ r
  · apply (hinner z hzr).trans
    have hpow : 1 ≤ q ^ ε := Real.one_le_rpow hq hε
    have h1 := mul_le_mul_of_nonneg_left hC hA0
    have h2 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hA0 hC0)
    nlinarith
  have hzr' : r ≤ ‖z - c‖ := le_of_lt (lt_of_not_ge hzr)
  have hgap : 0 < Real.log R - Real.log r := sub_pos.mpr (Real.log_lt_log hr hrR)
  let θ := (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr (Real.log_le_log hr hzr')) hgap.le
  have hθ1 : θ ≤ 1 := by
    apply (div_le_iff₀ hgap).mpr
    have h := Real.log_le_log (hr.trans_le hzr') hzR
    linarith
  have hlog : Real.log ‖z - c‖ - Real.log r ≤ Real.log 3 := by
    have h := Real.log_le_log (hr.trans_le hzr') hz
    rw [Real.log_mul (by norm_num) hr.ne'] at h
    linarith
  have hθε : 3 * θ ≤ ε := by
    dsimp [θ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hgap).mpr
    linarith
  have hApow : A ^ (1 - θ) ≤ A := by
    simpa using Real.rpow_le_rpow_of_exponent_le hA (show 1 - θ ≤ 1 by linarith)
  have hCpow : C ^ θ ≤ C := by
    simpa using Real.rpow_le_rpow_of_exponent_le hC hθ1
  have hqpow : q ^ (3 * θ) ≤ q ^ ε := Real.rpow_le_rpow_of_exponent_le hq hθε
  have hBpow : (C * q ^ (3 : ℕ)) ^ θ ≤ C * q ^ ε := by
    rw [Real.mul_rpow hC0 (pow_nonneg hq0 _), ← Real.rpow_natCast_mul hq0 3 θ]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul hCpow hqpow (Real.rpow_nonneg hq0 _) hC0
  have h := norm_le_three_circle hf hr hrR hinner houter hzr' hzR
  change ‖f z‖ ≤ A ^ (1 - θ) * (C * q ^ (3 : ℕ)) ^ θ at h
  calc
    ‖f z‖ ≤ _ := h
    _ ≤ A * (C * q ^ ε) := mul_le_mul hApow hBpow
      (Real.rpow_nonneg (mul_nonneg hC0 (pow_nonneg hq0 _)) _) hA0
    _ = _ := by ring
end Chen

end

/-! ## ChenTheorem.Analysis.ZeroFreeLogDerivative -/

section

open Set Metric

namespace Chen
/-- A normalized holomorphic logarithm with real part at most `M` has norm
at most `14 M` on the disk with seven eighths of the original radius. -/
theorem norm_analyticLog_le_on_inner_ball (g : ℂ → ℂ) (c : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball c R))
    (hc : g c = 0) (hbound : ∀ z ∈ ball c R, (g z).re ≤ M)
    (z : ℂ) (hz : dist z c < 7 * R / 8) : ‖g z‖ ≤ 14 * M := by
  let G : ℂ → ℂ := fun w => g (c + w)
  have hmem (w : ℂ) (hw : w ∈ ball (0 : ℂ) R) : c + w ∈ ball c R := by
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
  have hG : DifferentiableOn ℂ G (ball 0 R) :=
    hg.comp (by fun_prop : DifferentiableOn ℂ (fun w => c + w) (ball 0 R)) hmem
  have hGc : G 0 = 0 := by simp [G, hc]
  have hzb : z - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    linarith
  have hb := Complex.borelCaratheodory_zero hM hG (fun w hw => hbound _ (hmem w hw)) hR hzb hGc
  have hnorm : ‖z - c‖ < 7 * R / 8 := by simpa only [dist_eq_norm] using hz
  have hden : 0 < R - ‖z - c‖ := by linarith
  have hratio : 2 * M * ‖z - c‖ / (R - ‖z - c‖) ≤ 14 * M := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  simpa only [G, add_sub_cancel] using hb.trans hratio
/-- Growth relative to a nonzero center value controls the logarithmic
derivative on the three-quarter disk, provided that the whole disk is zero-free.
The constants are absolute and no arithmetic assumptions are used. -/
theorem norm_logDeriv_le_of_nonvanishing_ball (f : ℂ → ℂ) (c : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball c R))
    (hne : ∀ z ∈ ball c R, f z ≠ 0)
    (hbound : ∀ z ∈ ball c R, ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (z : ℂ) (hz : dist z c ≤ 3 * R / 4) : ‖deriv f z / f z‖ ≤ 224 * M / R := by
  obtain ⟨g, hg, hgc, hge⟩ := exists_normalized_analyticLog_on_ball f c R hR hf hne
  have hc : f c ≠ 0 := hne c (mem_ball_self hR)
  have hreal : ∀ w ∈ ball c R, (g w).re ≤ M := by
    intro w hw
    apply Real.exp_le_exp.mp
    rw [← Complex.norm_exp, hge w hw, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hc)).mpr (hbound w hw)
  have hinner : ∀ w, dist w c < 7 * R / 8 → ‖g w‖ ≤ 14 * M :=
    norm_analyticLog_le_on_inner_ball g c R M hR hM hg hgc hreal
  have hzinner : dist z c < 7 * R / 8 := by linarith
  have hsub : ball z (R / 8) ⊆ ball c R := by
    intro w hw
    have hdist := dist_triangle w z c
    change dist w z < R / 8 at hw
    change dist w c < R
    linarith
  have hmapping : MapsTo g (ball z (R / 8)) (closedBall (g z) (28 * M)) := by
    intro w hw
    have hwinner : dist w c < 7 * R / 8 := by
      have hdist := dist_triangle w z c
      change dist w z < R / 8 at hw
      linarith
    change dist (g w) (g z) ≤ 28 * M
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hinner w hwinner, hinner z hzinner])
  have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hg.mono hsub) hmapping (by positivity : 0 < R / 8)
  rw [deriv_analyticLog_eq_logDeriv isOpen_ball hf hg c hc hge z (by
    change dist z c < R
    linarith)] at hd
  convert hd using 1
  ring
end Chen

end

/-! ## ChenTheorem.Analysis.ZeroFreeFactorBounds -/

section

open Set Metric MeromorphicOn

namespace Chen
/-- Removing the interior zeros preserves the boundary norm and increases
the modulus at the center. The analytic remainder inherits the original bound. -/
theorem exists_bounded_analytic_zeroFree_factor {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hb : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R) ∧
      (∀ z ∈ closedBall 0 R, ‖g z‖ ≤ M) ∧ ‖f 0‖ ≤ ‖g 0‖ := by
  obtain ⟨g, hg, hne, he⟩ := exists_analytic_blaschke_factorization hR hf h0
  have hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hboundary : ∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖ := by
    intro z hz
    rw [he (sphere_subset_closedBall hz), norm_mul,
      norm_diskBlaschkeProduct_on_sphere f R hfin hz, one_mul]
  refine ⟨g, hg, hne, he, ?_, ?_⟩
  · intro z hz
    exact norm_le_of_analyticOnNhd_closedBall hR hg
      (fun w hw => (hboundary w hw).trans_le (hb w hw)) hz
  · have hmem : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
    rw [he hmem, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (norm_diskBlaschkeProduct_le_one f R hfin hmem)
/-- A boundary growth estimate gives a quantitative logarithmic-derivative
bound for the analytic zero-free remainder of the finite Blaschke factorization. -/
theorem exists_analytic_factor_with_logDeriv_bound {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h0 : f 0 ≠ 0) (hb : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ Real.exp B * ‖f 0‖) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R) ∧
      ∀ z : ℂ, ‖z‖ ≤ 3 * R / 4 → ‖deriv g z / g z‖ ≤ 224 * B / R := by
  obtain ⟨g, hg, hne, he, hbound, hanchor⟩ := exists_bounded_analytic_zeroFree_factor hR hf h0 hb
  refine ⟨g, hg, hne, he, ?_⟩
  intro z hz
  apply norm_logDeriv_le_of_nonvanishing_ball g 0 R B hR hB
    (hg.differentiableOn.mono ball_subset_closedBall) hne
  · intro w hw
    exact (hbound w (ball_subset_closedBall hw)).trans
      (mul_le_mul_of_nonneg_left hanchor (Real.exp_pos B).le)
  · simpa only [dist_zero_right] using hz
end Chen

end

/-! ## ChenTheorem.Analysis.LocalZeroLogDerivative -/

section

open Set Metric Filter Topology

namespace Chen
theorem logDeriv_eq_blaschke_add_factor {f g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (he : EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R))
    {z : ℂ} (hz : z ∈ ball 0 R) (hfz : f z ≠ 0) (hgz : g z ≠ 0) :
    logDeriv f z = logDeriv (diskBlaschkeProduct f R) z + logDeriv g z := by
  have hzR := ball_subset_closedBall hz
  have hn : closedBall (0 : ℂ) R ∈ 𝓝 z :=
    mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
  have he' := he.eventuallyEq_of_mem hn
  have hpz : diskBlaschkeProduct f R z ≠ 0 := by
    intro hp
    apply hfz
    calc
      f z = diskBlaschkeProduct f R z * g z := he hzR
      _ = 0 := by rw [hp, zero_mul]
  have hp := (analyticOnNhd_diskBlaschkeProduct f R z hzR).differentiableAt
  calc
    logDeriv f z = logDeriv (fun u => diskBlaschkeProduct f R u * g u) z := by
      rw [logDeriv_apply, logDeriv_apply, he'.deriv_eq, he hzR]
    _ = _ := logDeriv_mul z hpz hgz hp (hg z hzR).differentiableAt
/-- Local zero isolation: subtracting the poles of the zeros in the disk
leaves an error bounded by boundary growth and the number of zeros. -/
theorem norm_logDeriv_sub_diskZeroPoleSum_le {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h0 : f 0 ≠ 0) (hb : ∀ w ∈ sphere 0 R, ‖f w‖ ≤ Real.exp B * ‖f 0‖)
    {z : ℂ} (hz : ‖z‖ ≤ 3 * R / 4) (hfz : f z ≠ 0) :
    ‖deriv f z / f z - diskZeroPoleSum f R z‖ ≤ (224 * B + 4 * diskZeroCount f R) / R := by
  obtain ⟨g, hg, hne, he, hgbound⟩ := exists_analytic_factor_with_logDeriv_bound hR hB hf h0 hb
  have hzR : z ∈ ball 0 R := by simp only [mem_ball_zero_iff]; linarith
  have hlog := logDeriv_eq_blaschke_add_factor hg he hzR hfz (hne z hzR)
  have hpb := norm_logDeriv_diskBlaschkeProduct_sub_poles_le hR hf hz hfz
  have hgb := hgbound z hz
  change ‖logDeriv f z - diskZeroPoleSum f R z‖ ≤ _
  rw [hlog, show logDeriv (diskBlaschkeProduct f R) z + logDeriv g z - diskZeroPoleSum f R z =
    (logDeriv (diskBlaschkeProduct f R) z - diskZeroPoleSum f R z) + logDeriv g z by ring]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ (4 / R) * diskZeroCount f R + 224 * B / R := add_le_add hpb hgb
    _ = _ := by ring
end Chen

end

/-! ## ChenTheorem.Analysis.LocalZeroLogDerivativeBound -/

section

open Set Metric

namespace Chen
/-- A fully quantitative local logarithmic-derivative expansion. Analyticity
and a bound on a slightly larger disk suffice; there is no nonvanishing
assumption on the disks, only at their center and at the evaluation point. -/
theorem norm_logDeriv_sub_zero_poles_le_of_outer_bound {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (4 * R / 3))) (h0 : f 0 ≠ 0)
    (hb : ∀ w ∈ sphere 0 (4 * R / 3), ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 3 * R / 4) (hfz : f z ≠ 0) :
    ‖deriv f z / f z - diskZeroPoleSum f R z‖ ≤
      240 * (Real.log (M / ‖f 0‖) + 1) / R := by
  let B := Real.log (M / ‖f 0‖) + 1
  have houter : 0 < 4 * R / 3 := by positivity
  have hsub : R ≤ 4 * R / 3 := by linarith
  have hnorm0 : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hcenter : ‖f 0‖ ≤ M := norm_le_of_analyticOnNhd_closedBall houter hf hb
    (mem_closedBall_self houter.le)
  have hratio : 1 ≤ M / ‖f 0‖ := (one_le_div hnorm0).mpr hcenter
  have hlog : 0 ≤ Real.log (M / ‖f 0‖) := Real.log_nonneg hratio
  have hB : 0 < B := by dsimp [B]; linarith
  have hgrowth : M ≤ Real.exp B * ‖f 0‖ := by
    calc
      M = Real.exp (Real.log (M / ‖f 0‖)) * ‖f 0‖ := by
        rw [Real.exp_log (by positivity)]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by dsimp [B]; linarith)) hnorm0.le
  have hbinner : ∀ w ∈ sphere 0 R, ‖f w‖ ≤ Real.exp B * ‖f 0‖ := by
    intro w hw
    exact (norm_le_of_analyticOnNhd_closedBall houter hf hb
      (closedBall_subset_closedBall hsub (sphere_subset_closedBall hw))).trans hgrowth
  have hcount := diskZeroCount_le_of_outer_bound hR (by linarith : R < 4 * R / 3) hM hf h0 hb
  rw [show (4 * R / 3) / R = (4 / 3 : ℝ) by field_simp] at hcount
  have hden : (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at h
    exact h
  have hcountB : diskZeroCount f R ≤ 4 * B := by
    apply hcount.trans
    apply (div_le_iff₀ (by linarith : 0 < Real.log (4 / 3 : ℝ))).mpr
    dsimp [B]
    nlinarith
  have hlocal := norm_logDeriv_sub_diskZeroPoleSum_le hR hB
    (hf.mono (closedBall_subset_closedBall hsub)) h0 hbinner hz hfz
  apply hlocal.trans
  apply div_le_div_of_nonneg_right _ hR.le
  change 224 * B + 4 * diskZeroCount f R ≤ 240 * B
  linarith
end Chen

end

/-! ## ChenTheorem.Analysis.ZeroPoleRealPart -/

section

open Set Metric Function MeromorphicOn
open scoped Classical

namespace Chen

theorem zero_of_mem_disk_divisor_support {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {w : ℂ}
    (hw : w ∈ (divisor f (ball 0 R)).support) : f w = 0 := by
  by_contra hne
  have hwR := (divisor f (ball 0 R)).supportWithinDomain hw
  exact ne_zero_point_ne_divisor_support hf (ball_subset_closedBall hwR) hne hw rfl
theorem one_le_disk_divisor_of_zero {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    {w : ℂ} (hw : w ∈ ball 0 R) (hfw : f w = 0) : 1 ≤ divisor f (ball 0 R) w := by
  have hm : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have horder0 : meromorphicOrderAt f 0 ≠ ⊤ := by
    rw [(hf 0 hm).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
    simp
  have horder := hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall (0 : ℂ) R).isPreconnected hm (ball_subset_closedBall hw) horder0
  have ho : meromorphicOrderAt f w ≠ 0 := by
    intro he
    exact ((hf w (ball_subset_closedBall hw)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp he) hfw
  have hd := (hf.mono ball_subset_closedBall).divisor_nonneg w
  change (0 : ℤ) ≤ divisor f (ball 0 R) w at hd
  have hdne : divisor f (ball 0 R) w ≠ 0 := by
    rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hw]
    intro he
    exact (WithTop.untop₀_eq_zero.mp he).elim ho horder
  omega
theorem re_int_zero_pole_nonneg (m : ℤ) (hm : 0 ≤ m) {z w : ℂ}
    (hzw : w.re ≤ z.re) : 0 ≤ ((m : ℂ) / (z - w)).re := by
  simp only [Complex.div_re, Complex.intCast_re, Complex.intCast_im, Complex.sub_re,
    zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (by exact_mod_cast hm) (sub_nonneg.mpr hzw))
    (Complex.normSq_nonneg _)
theorem diskZeroPoleSum_re_nonneg {f : ℂ → ℂ} {R κ : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hright : ∀ w ∈ ball 0 R, κ < w.re → f w ≠ 0)
    {z : ℂ} (hz : κ ≤ z.re) : 0 ≤ (diskZeroPoleSum f R z).re := by
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  rw [diskZeroPoleSum_eq_sum f R hfin z, Complex.re_sum]
  apply Finset.sum_nonneg
  intro w hw
  have hws := hfin.mem_toFinset.mp hw
  have hwR := (divisor f (ball 0 R)).supportWithinDomain hws
  have hfw := zero_of_mem_disk_divisor_support hf hws
  have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w hwR h hfw)
  exact re_int_zero_pole_nonneg _ ((hf.mono ball_subset_closedBall).divisor_nonneg w) (hwκ.trans hz)
theorem one_div_re_gap_le_re_zero_pole (m : ℤ) (hm : 1 ≤ m) {z w : ℂ}
    (hre : w.re < z.re) (him : w.im = z.im) :
    1 / (z.re - w.re) ≤ ((m : ℂ) / (z - w)).re := by
  have he : z - w = ((z.re - w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [he, ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hm) (sub_nonneg.mpr hre.le)
/-- A zero at the same height as the evaluation point contributes at least
one reciprocal horizontal gap; the other zero contributions are nonnegative. -/
theorem one_div_re_gap_le_diskZeroPoleSum_re {f : ℂ → ℂ} {R κ : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hright : ∀ u ∈ ball 0 R, κ < u.re → f u ≠ 0)
    {z w : ℂ} (hz : κ < z.re) (hw : w ∈ ball 0 R) (hfw : f w = 0)
    (him : w.im = z.im) : 1 / (z.re - w.re) ≤ (diskZeroPoleSum f R z).re := by
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hmult := one_le_disk_divisor_of_zero hR hf h0 hw hfw
  have hws : w ∈ (divisor f (ball 0 R)).support := by
    apply mem_support.mpr
    omega
  have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w hw h hfw)
  rw [diskZeroPoleSum_eq_sum f R hfin z, Complex.re_sum]
  apply (one_div_re_gap_le_re_zero_pole _ hmult (hwκ.trans_lt hz) him).trans
  apply Finset.single_le_sum _ (hfin.mem_toFinset.mpr hws)
  intro u hu
  have hus := hfin.mem_toFinset.mp hu
  have huR := (divisor f (ball 0 R)).supportWithinDomain hus
  have hfu := zero_of_mem_disk_divisor_support hf hus
  have huκ : u.re ≤ κ := le_of_not_gt (fun h => hright u huR h hfu)
  exact re_int_zero_pole_nonneg _ ((hf.mono ball_subset_closedBall).divisor_nonneg u) (huκ.trans hz.le)
end Chen

end

/-! ## ChenTheorem.Analysis.MultipleZeroPoleRealPart -/

section

open Set Metric Function MeromorphicOn
open scoped Classical

namespace Chen
theorem two_le_disk_divisor_of_zero_deriv {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    {w : ℂ} (hw : w ∈ ball 0 R) (hfw : f w = 0) (hdfw : deriv f w = 0) :
    2 ≤ divisor f (ball 0 R) w := by
  have hd := one_le_disk_divisor_of_zero hR hf h0 hw hfw
  by_contra! hh
  have hd1 : divisor f (ball 0 R) w = 1 := by omega
  rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hw] at hd1
  have ho : meromorphicOrderAt f w = ((1 : ℤ) : WithTop ℤ) := by
    cases he : meromorphicOrderAt f w with
    | top => simp [he] at hd1
    | coe n => simpa [he] using hd1
  have hdo := meromorphicOrderAt_deriv_eq_sub_one (f := f) (x := w) (n := (1 : ℤ)) (by norm_num) ho
  norm_num at hdo
  have hdne := ((hf w (ball_subset_closedBall hw)).deriv.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mp hdo
  exact hdne hdfw
theorem two_div_re_gap_le_diskZeroPoleSum_re_of_zero_deriv {f : ℂ → ℂ} {R κ : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hright : ∀ u ∈ ball 0 R, κ < u.re → f u ≠ 0)
    {z w : ℂ} (hz : κ < z.re) (hw : w ∈ ball 0 R) (hfw : f w = 0)
    (hdfw : deriv f w = 0) (him : w.im = z.im) :
    2 / (z.re - w.re) ≤ (diskZeroPoleSum f R z).re := by
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hm := two_le_disk_divisor_of_zero_deriv hR hf h0 hw hfw hdfw
  have hws : w ∈ (divisor f (ball 0 R)).support := by apply mem_support.mpr; omega
  have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w hw h hfw)
  have he : z - w = ((z.re - w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hp : 2 / (z.re - w.re) ≤ (((divisor f (ball 0 R) w : ℤ) : ℂ) / (z - w)).re := by
    rw [he, ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) (by linarith)
  rw [diskZeroPoleSum_eq_sum f R hfin z, Complex.re_sum]
  apply hp.trans
  apply Finset.single_le_sum _ (hfin.mem_toFinset.mpr hws)
  intro u hu
  have hus := hfin.mem_toFinset.mp hu
  have huR := (divisor f (ball 0 R)).supportWithinDomain hus
  have hfu := zero_of_mem_disk_divisor_support hf hus
  have huκ : u.re ≤ κ := le_of_not_gt (fun h => hright u huR h hfu)
  exact re_int_zero_pole_nonneg _ ((hf.mono ball_subset_closedBall).divisor_nonneg u) (huκ.trans hz.le)
end Chen

end

/-! ## ChenTheorem.Analysis.ZeroPoleSubsetRealPart -/

section

open Set Metric MeromorphicOn Function

namespace Chen
theorem re_one_zero_pole_le_int_zero_pole (m : ℤ) (hm : 1 ≤ m) {z w : ℂ}
    (hre : w.re ≤ z.re) : (1 / (z - w)).re ≤ ((m : ℂ) / (z - w)).re := by
  simp only [Complex.div_re, Complex.one_re, Complex.one_im, Complex.intCast_re,
    Complex.intCast_im, Complex.sub_re, zero_mul, zero_div, add_zero, one_mul]
  apply div_le_div_of_nonneg_right _ (Complex.normSq_nonneg _)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith
/-- Any finite set of distinct zeros gives a lower bound for the real part
of the full pole sum. Multiplicities in the full sum are at least one. -/
theorem sum_re_zero_poles_le_diskZeroPoleSum_re {f : ℂ → ℂ} {R κ : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hright : ∀ u ∈ ball 0 R, κ < u.re → f u ≠ 0)
    {z : ℂ} (hz : κ ≤ z.re) (T : Finset ℂ)
    (hT : ∀ w ∈ T, w ∈ ball 0 R ∧ f w = 0) :
    ∑ w ∈ T, (1 / (z - w)).re ≤ (diskZeroPoleSum f R z).re := by
  classical
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hsub : T ⊆ hfin.toFinset := by
    intro w hw
    apply hfin.mem_toFinset.mpr
    apply mem_support.mpr
    have hm := one_le_disk_divisor_of_zero hR hf h0 (hT w hw).1 (hT w hw).2
    omega
  have hnonneg : ∀ w ∈ hfin.toFinset,
      0 ≤ (((divisor f (ball 0 R) w : ℤ) : ℂ) / (z - w)).re := by
    intro w hw
    have hws := hfin.mem_toFinset.mp hw
    have hwR := (divisor f (ball 0 R)).supportWithinDomain hws
    have hfw := zero_of_mem_disk_divisor_support hf hws
    have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w hwR h hfw)
    exact re_int_zero_pole_nonneg _ ((hf.mono ball_subset_closedBall).divisor_nonneg w)
      (hwκ.trans hz)
  rw [diskZeroPoleSum_eq_sum f R hfin z, Complex.re_sum]
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w hw _ => hnonneg w hw))
  apply Finset.sum_le_sum
  intro w hw
  have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w (hT w hw).1 h (hT w hw).2)
  exact re_one_zero_pole_le_int_zero_pole _
    (one_le_disk_divisor_of_zero hR hf h0 (hT w hw).1 (hT w hw).2) (hwκ.trans hz)
theorem pair_re_zero_poles_le_diskZeroPoleSum_re {f : ℂ → ℂ} {R κ : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hright : ∀ u ∈ ball 0 R, κ < u.re → f u ≠ 0)
    {z w₁ w₂ : ℂ} (hz : κ ≤ z.re) (hw₁ : w₁ ∈ ball 0 R) (hw₂ : w₂ ∈ ball 0 R)
    (hf₁ : f w₁ = 0) (hf₂ : f w₂ = 0) (hne : w₁ ≠ w₂) :
    (1 / (z - w₁)).re + (1 / (z - w₂)).re ≤ (diskZeroPoleSum f R z).re := by
  classical
  have h := sum_re_zero_poles_le_diskZeroPoleSum_re hR hf h0 hright hz {w₁, w₂}
    (by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw₁, hf₁⟩
        · exact ⟨hw₂, hf₂⟩)
  simpa [hne] using h
end Chen

end

/-! ## ChenTheorem.Analysis.ZetaRegularPart -/

section

open scoped Topology

namespace Chen

/-- The entire extension of `(s - 1) * ζ(s)`, using mathlib's pole removal. -/
noncomputable abbrev zetaPoleFactor : ℂ → ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1

theorem zetaPoleFactor_one : zetaPoleFactor 1 = 1 := by
  simp [zetaPoleFactor, DirichletCharacter.LFunctionTrivChar₁]
theorem zetaPoleFactor_eq {s : ℂ} (hs : s ≠ 1) :
    zetaPoleFactor s = (s - 1) * riemannZeta s := by
  rw [zetaPoleFactor, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs]
  simp

theorem differentiable_zetaPoleFactor : Differentiable ℂ zetaPoleFactor :=
  DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
/-- The regular part of `ζ(s) * g(s)` after subtracting its residue at one.
The value at one is given by the derivative of the numerator. -/
noncomputable def regularizedZetaMul (g : ℂ → ℂ) : ℂ → ℂ :=
  dslope (fun s => zetaPoleFactor s * g s) 1
theorem differentiable_regularizedZetaMul {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (regularizedZetaMul g) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (c := (1 : ℂ)) Filter.univ_mem).mpr
    (differentiable_zetaPoleFactor.mul hg).differentiableOn
theorem regularizedZetaMul_eq {g : ℂ → ℂ} {s : ℂ} (hs : s ≠ 1) :
    regularizedZetaMul g s = riemannZeta s * g s - g 1 / (s - 1) := by
  rw [regularizedZetaMul, dslope_of_ne _ hs]
  simp only [slope, vsub_eq_sub, smul_eq_mul, zetaPoleFactor_one, one_mul, zetaPoleFactor_eq hs]
  field_simp

end Chen

end

/-! ## ChenTheorem.Analysis.RegularizedTaylorSeries -/

section

open scoped Topology

namespace Chen

theorem backwardTaylorCoeff_regularizedZetaMul {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (n : ℕ) :
    backwardTaylorCoeff (regularizedZetaMul g) 2 n =
      backwardTaylorCoeff (fun s => riemannZeta s * g s) 2 n - g 1 := by
  have he : regularizedZetaMul g =ᶠ[𝓝 (2 : ℂ)]
      (fun s => riemannZeta s * g s - g 1 / (s - 1)) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (2 : ℂ) ≠ 1)] with s hs
    exact regularizedZetaMul_eq hs
  have hF : AnalyticAt ℂ (fun s => riemannZeta s * g s) 2 :=
    (analyticOn_riemannZeta 2 (by norm_num)).mul (hg.analyticAt 2)
  have hP : AnalyticAt ℂ (fun s : ℂ => g 1 / (s - 1)) 2 :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  have hc : backwardTaylorCoeff (regularizedZetaMul g) 2 n =
      backwardTaylorCoeff (fun s => riemannZeta s * g s - g 1 / (s - 1)) 2 n := by
    unfold backwardTaylorCoeff
    rw [he.iteratedDeriv_eq]
  rw [hc, backwardTaylorCoeff_sub n hF.contDiffAt hP.contDiffAt, backwardTaylorCoeff_pole]

theorem hasSum_regularizedZetaMul_backwardTaylor {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (z : ℂ) :
    HasSum (fun n : ℕ => (backwardTaylorCoeff (fun s => riemannZeta s * g s) 2 n - g 1) * z ^ n)
      (regularizedZetaMul g (2 - z)) := by
  have h := hasSum_backwardTaylorCoeff
    (differentiable_regularizedZetaMul hg).differentiableOn
    (c := (2 : ℂ)) (R := ‖z‖ + 1) (by linarith : ‖z‖ < ‖z‖ + 1)
  simpa only [backwardTaylorCoeff_regularizedZetaMul hg] using h

end Chen

end

