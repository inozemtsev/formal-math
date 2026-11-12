module

public import Green64.Library.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
public import Green64.Library.OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / GaussSum / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace ActualEisensteinCubic

theorem canonical_finite_prime_gauss_transform
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i,
      (∏ i, (canonicalSextic (P i) (hgood i) ^ j i)
        (IdealGaussCRT.quotientProdEquivPi P hc x i)) * ψ (h * x)) =
      ∏ i, if IdealGaussCRT.quotientProdEquivPi P hc h i = 0 then 0 else
        ((canonicalSextic (P i) (hgood i) ^ j i)
          (IdealGaussCRT.quotientProdEquivPi P hc h i))⁻¹ *
          gaussSum (canonicalSextic (P i) (hgood i) ^ j i)
            (IdealGaussCRT.coordinateAddChar (fun i => O ⧸ P i)
              (IdealGaussCRT.quotientProdEquivPi P hc) ψ i) := by
  exact IdealGaussCRT.gauss_transform_finite_ideal_crt P hc
    (fun i => canonicalSextic (P i) (hgood i) ^ j i) ψ
    (fun i => canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)) h

noncomputable def finiteSexticQuotientRow
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (x : O ⧸ ∏ i, P i) : ℂ :=
  ∏ i, (canonicalSextic (P i) (hgood i) ^ j i)
    (IdealGaussCRT.quotientProdEquivPi P hc x i)

theorem finiteSexticQuotientRow_one_mk
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (a : O) :
    finiteSexticQuotientRow P hc hgood (fun _ => 1)
      (Ideal.Quotient.mk (∏ i, P i) a) =
      finiteSquarefreeRow P hgood Finset.univ a := by
  simp only [finiteSexticQuotientRow, IdealGaussCRT.quotientProdEquivPi_mk, pow_one]
  rfl

theorem finiteSexticQuotientRow_mk_eq_zero_iff
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticQuotientRow P hc hgood j
      (Ideal.Quotient.mk (∏ i, P i) a) = 0 ↔ ∃ i, a ∈ P i := by
  classical
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  simp only [finiteSexticQuotientRow, IdealGaussCRT.quotientProdEquivPi_mk,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    MulChar.apply_eq_zero_iff, isUnit_iff_ne_zero, not_not,
    Ideal.Quotient.eq_zero_iff_mem]

theorem canonical_finite_prime_gauss_transform_scalar
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => canonicalSextic (P i) (hgood i) ^ j i) ψ
    (fun i => canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)) h

theorem finiteSexticQuotientRow_inv_eq_star
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (h : O ⧸ ∏ i, P i) :
    (finiteSexticQuotientRow P hc hgood j h)⁻¹ =
      star (finiteSexticQuotientRow P hc hgood j h) := by
  classical
  simp only [finiteSexticQuotientRow, star_prod]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']

theorem canonical_finite_prime_gauss_transform_conj
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar P hc hgood hchar j hj0 hj6 ψ,
    finiteSexticQuotientRow_inv_eq_star]

theorem canonical_finite_prime_gauss_transform_vanishes
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (a : O)
    (ha : ∃ i, a ∈ P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x *
      ψ (Ideal.Quotient.mk (∏ i, P i) a * x)) = 0 := by
  rw [canonical_finite_prime_gauss_transform_scalar P hc hgood hchar j hj0 hj6 ψ,
    (finiteSexticQuotientRow_mk_eq_zero_iff P hc hgood j a).2 ha,
    inv_zero, zero_mul]

theorem finiteSexticQuotientRow_disjoint_pair_mk
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSexticQuotientRow P hc hgood (fun i => if i ∈ S then 1 else 5)
      (Ideal.Quotient.mk (∏ i, P i) a) =
      finiteSquarefreeRow P hgood S a *
        star (finiteSquarefreeRow P hgood (Finset.univ \ S) a) := by
  classical
  have hpow5 (i : ι) :
      (canonicalSextic (P i) (hgood i) ^ 5) (Ideal.Quotient.mk (P i) a) =
        star (canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) a)) := by
    rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0)]
    rw [canonicalSextic_conj_as_row_label]
    ring
  have hterm (i : ι) :
      (canonicalSextic (P i) (hgood i) ^ (if i ∈ S then 1 else 5))
          (Ideal.Quotient.mk (P i) a) =
        if i ∈ S then canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) a)
        else star (canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) a)) := by
    split_ifs <;> simp only [pow_one, hpow5]
  simp only [finiteSexticQuotientRow, IdealGaussCRT.quotientProdEquivPi_mk]
  simp_rw [hterm]
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.sdiff_eq_filter]
  simp only [finiteSquarefreeRow, star_prod]

theorem canonical_disjoint_pair_gauss_transform
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S : Finset ι) (ψ : AddChar (O ⧸ ∏ i, P i) ℂ)
    (h : O ⧸ ∏ i, P i) :
    let row := finiteSexticQuotientRow P hc hgood (fun i => if i ∈ S then 1 else 5)
    (∑ x : O ⧸ ∏ i, P i, row x * ψ (h * x)) =
      (row h)⁻¹ * ∑ x : O ⧸ ∏ i, P i, row x * ψ x := by
  classical
  exact canonical_finite_prime_gauss_transform_scalar P hc hgood hchar
    (fun i => if i ∈ S then 1 else 5)
    (fun i => by split_ifs <;> decide)
    (fun i => by split_ifs <;> decide) ψ h

end ActualEisensteinCubic

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

def paperE (z : ℂ) : ℂ := ShortDraftTrace.breveE (z / eisLam)

def paperFrequency (u : ℂ) : ℂ :=
  (2 * Complex.I / (Real.sqrt 3 : ℂ)) * (starRingEnd ℂ u)

theorem paperE_eq_exp (z : ℂ) :
    paperE z = Complex.exp (4 * Real.pi * Complex.I * (z.im / Real.sqrt 3)) := by
  exact ShortDraftTrace.breveE_div_lam_eq_e z

theorem inner_paperFrequency (z u : ℂ) :
    inner ℝ z (paperFrequency u) = 2 * (z * u).im / Real.sqrt 3 := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [Complex.inner]
  simp only [paperFrequency, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.normSq_ofReal]
  norm_num
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

theorem fourierChar_paperFrequency (z u : ℂ) :
    (Real.fourierChar (inner ℝ z (paperFrequency u)) : ℂ) = paperE (z * u) := by
  rw [inner_paperFrequency, paperE_eq_exp, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem dualFrequencyEquiv_coordinates (p : ℤ × ℤ) :
    eisEmbedding (dualFrequencyEquiv p) =
      complexPoint ((p.1 : ℝ) / 2 + (p.2 : ℝ))
        (Real.sqrt 3 * (p.1 : ℝ) / 2) := by
  change eisEmbedding (ActualEisensteinCoordinates.eval (p.1 + p.2) p.1) = _
  rw [eisEmbedding_eval]
  apply Complex.ext <;> norm_num [complexPoint, omega3] <;> ring

theorem explicitDualFrequency_eq_paperFrequency (c : ℂ) (p : ℤ × ℤ) :
    explicitDualFrequency c p = paperFrequency (eisEmbedding (dualFrequencyEquiv p) / c) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hnum : complexPoint (p.1 : ℝ)
      (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) =
      (2 * Complex.I / (Real.sqrt 3 : ℂ)) *
        starRingEnd ℂ (eisEmbedding (dualFrequencyEquiv p)) := by
    rw [dualFrequencyEquiv_coordinates]
    apply Complex.ext <;>
      norm_num [complexPoint, Complex.div_re, Complex.div_im] <;>
      field_simp <;>
      simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  unfold explicitDualFrequency paperFrequency
  rw [map_div₀, hnum]
  ring

theorem explicitDualFrequency_phase (r c : ℂ) (p : ℤ × ℤ) :
    (Real.fourierChar (inner ℝ r (explicitDualFrequency c p)) : ℂ) =
      paperE (r * eisEmbedding (dualFrequencyEquiv p) / c) := by
  rw [explicitDualFrequency_eq_paperFrequency, fourierChar_paperFrequency]
  congr 1
  ring

theorem paperFrequency_norm_sq (u : ℂ) :
    ‖paperFrequency u‖ ^ 2 = (4 / 3 : ℝ) * ‖u‖ ^ 2 := by
  have hnorm : ‖(2 * Complex.I / (Real.sqrt 3 : ℂ))‖ ^ 2 = (4 / 3 : ℝ) := by
    rw [norm_div, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3),
      div_pow, Real.sq_sqrt]
  rw [paperFrequency, norm_mul, mul_pow, Complex.norm_conj, hnorm]

theorem explicitDualFrequency_norm_sq (c : ℂ) (p : ℤ × ℤ) :
    ‖explicitDualFrequency c p‖ ^ 2 =
      (4 / 3 : ℝ) * ‖eisEmbedding (dualFrequencyEquiv p)‖ ^ 2 / ‖c‖ ^ 2 := by
  rw [explicitDualFrequency_eq_paperFrequency, paperFrequency_norm_sq, norm_div, div_pow]
  ring

def paperFourier (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  (2 / Real.sqrt 3 : ℝ) • ∫ z : ℂ, paperE (-(z * u)) * f z

theorem paperFourier_eq_standard (f : ℂ → ℂ) (u : ℂ) :
    paperFourier f u = (2 / Real.sqrt 3 : ℝ) • 𝓕 f (paperFrequency u) := by
  unfold paperFourier
  congr 1
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Circle.smul_def, smul_eq_mul]
  have hp : (Real.fourierChar (-inner ℝ z (paperFrequency u)) : ℂ) =
      paperE (-(z * u)) := by
    simpa only [inner_neg_left, neg_mul] using fourierChar_paperFrequency (-z) u
  rw [hp]

theorem eisTraceModChar_eq_paperE (c : O) (hc : c ≠ 0) (z : O) :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
      (Ideal.Quotient.mk (Ideal.span {c}) z) =
      paperE (eisEmbedding z / eisEmbedding c) := by
  rw [eisTraceModChar, IdealGaussCRT.traceModChar_mk]
  unfold paperE
  congr 1
  ring

theorem eisTraceModChar_frequency (c : O) (hc : c ≠ 0)
    (h : O) (r : O ⧸ Ideal.span {c}) :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
      (Ideal.Quotient.mk (Ideal.span {c}) h * r) =
      paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
        eisEmbedding h / eisEmbedding c) := by
  conv_lhs => rw [← GaussianShiftedPartition.representative_spec c r, ← map_mul]
  rw [eisTraceModChar_eq_paperE, map_mul]
  congr 1
  ring

theorem actual_eisenstein_paper_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
            eisEmbedding h / eisEmbedding c)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
      eisEmbedding h / eisEmbedding c)
  have ht : (∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)) =
      (2 / Real.sqrt 3 : ℝ) • ∑' p : ℤ × ℤ,
        A (dualFrequencyEquiv p) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
    calc
      _ = ∑' p : ℤ × ℤ, A (dualFrequencyEquiv p) *
          paperFourier f (eisEmbedding (dualFrequencyEquiv p) / eisEmbedding c) :=
        (dualFrequencyEquiv.tsum_eq _).symm
      _ = ∑' p : ℤ × ℤ, (2 / Real.sqrt 3 : ℝ) •
          (A (dualFrequencyEquiv p) *
            (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) := by
        apply tsum_congr
        intro p
        rw [paperFourier_eq_standard, ← explicitDualFrequency_eq_paperFrequency]
        change A (dualFrequencyEquiv p) *
          ((2 / Real.sqrt 3 : ℝ) • (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) = _
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
    rfl
  have hp := actual_eisenstein_poisson_explicit f c hc P
  simp_rw [explicitDualFrequency_phase] at hp
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) •
    ∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)
  rw [ht, smul_smul]
  convert hp using 1
  congr 1
  ring

theorem actual_eisenstein_paper_poisson_trace (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  simpa only [eisTraceModChar_frequency] using actual_eisenstein_paper_poisson f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem paperFourier_comp_mul (f : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0) (u : ℂ) :
    paperFourier (fun z => f (a * z)) u =
      (1 / ‖a‖ ^ 2 : ℝ) • paperFourier f (u / a) := by
  have hd : dualMap (complexMulEquiv a ha) (paperFrequency u) =
      paperFrequency (u / a) := by
    rw [dual_mul_apply]
    unfold paperFrequency
    rw [map_div₀]
    ring
  have hj : inverseJacobian (complexMulEquiv a ha) = 1 / ‖a‖ ^ 2 := by
    rw [inverseJacobian, complexMulEquiv_det, abs_inv,
      abs_of_nonneg (Complex.normSq_nonneg a), Complex.sq_norm]
    ring
  rw [paperFourier_eq_standard, paperFourier_eq_standard]
  have hF := fourier_comp_linearEquiv (complexMulEquiv a ha) f (paperFrequency u)
  simp only [Function.comp_def, complexMulEquiv_apply] at hF
  rw [hF, hd, hj, smul_smul, smul_smul]
  congr 1
  ring

def paperRadialFourier (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  paperFourier (fun z => W (‖z‖ ^ 2)) (Real.sqrt t : ℂ)

theorem paperFourier_radial (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2)) u =
      paperRadialFourier W (‖u‖ ^ 2) := by
  unfold paperRadialFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let a : ℂ := u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hnC
  have hna : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, hn]
  have hq : u / a = (‖u‖ : ℂ) := by
    dsimp [a]
    field_simp
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) = fun z : ℂ => W (‖z‖ ^ 2) := by
    funext z
    rw [norm_mul, hna, one_mul]
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, hq] at hF
  simpa using hF

theorem inverseSqrt_ne_zero (K : ℝ) (hK : 0 < K) :
    (Real.sqrt K : ℂ)⁻¹ ≠ 0 :=
  inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hK)))

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

theorem paperFourier_radial_scaled (W : ℝ → ℂ) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2 / K)) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  let a : ℂ := (Real.sqrt K : ℂ)⁻¹
  have ha : a ≠ 0 := inverseSqrt_ne_zero K hK
  have hna : ‖a‖ ^ 2 = 1 / K := inverseSqrt_norm_sq K hK
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) =
      fun z : ℂ => W (‖z‖ ^ 2 / K) := by
    funext z
    rw [norm_mul, mul_pow, hna]
    congr 1
    ring
  have hnorm : ‖u / a‖ ^ 2 = K * ‖u‖ ^ 2 := by
    rw [norm_div, div_pow, hna]
    field_simp
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, one_div_one_div, paperFourier_radial, hnorm] at hF
  exact hF

def scaledRadialTest (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) : 𝓢(ℂ, ℂ) :=
  affinePullback (radialTest W)
    (complexMulEquiv ((Real.sqrt K : ℂ)⁻¹) (inverseSqrt_ne_zero K hK)) 0

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

theorem paperFourier_scaledRadialTest (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (scaledRadialTest W K hK) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  change paperFourier (fun z => scaledRadialTest W K hK z) u = _
  simp only [scaledRadialTest_apply]
  exact paperFourier_radial_scaled W K hK u

theorem actual_radial_paper_poisson_trace (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      (K / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)
  have ht : (∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c)) =
      K • ∑' h : O, A h *
        paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    calc
      _ = ∑' h : O, K • (A h *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) := by
        apply tsum_congr
        intro h
        rw [paperFourier_scaledRadialTest, norm_div, div_pow]
        have hr : K * (‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) =
            K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 := by ring
        rw [hr]
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
  have hp := actual_eisenstein_paper_poisson_trace (scaledRadialTest W K hK) c hc P
  change (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
    scaledRadialTest W K hK (eisEmbedding z)) =
    (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c) at hp
  rw [ht, smul_smul] at hp
  simpa only [scaledRadialTest_apply, one_div_mul_eq_div] using hp

theorem actual_compact_radial_paper_poisson_trace (W : ℝ → ℂ)
    (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W) (K : ℝ) (hK : 0 < K)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      (K / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  exact actual_radial_paper_poisson_trace (hWc.toSchwartzMap hWs) K hK c hc P

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson

def finiteSexticRow {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) : ℂ :=
  ∏ i, (canonicalSextic (P i) (hgood i) ^ j i) (Ideal.Quotient.mk (P i) a)

theorem finiteSexticRow_mul {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a b : O) :
    finiteSexticRow P hgood j (a * b) =
      finiteSexticRow P hgood j a * finiteSexticRow P hgood j b := by
  simp only [finiteSexticRow, map_mul, Finset.prod_mul_distrib]

theorem finite_prime_product_ne_bot {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] :
    (∏ i, P i) ≠ ⊥ := by
  change (∏ i, P i) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact NeZero.ne (P i)

def finitePrimeModulus {ι : Type*} [Fintype ι] (P : ι → Ideal O) : O :=
  ConcretePrimeRowBridge.idealGenerator (∏ i, P i)

theorem span_finitePrimeModulus {ι : Type*} [Fintype ι] (P : ι → Ideal O) :
    Ideal.span {finitePrimeModulus P} = ∏ i, P i :=
  ConcretePrimeRowBridge.span_idealGenerator _

theorem finitePrimeModulus_ne_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] :
    finitePrimeModulus P ≠ 0 := by
  intro hz
  have hspan := span_finitePrimeModulus P
  rw [hz] at hspan
  exact finite_prime_product_ne_bot P (by simpa using hspan.symm)

theorem eisEmbedding_norm_sq_eq_absNorm_span (a : O) :
    ‖eisEmbedding a‖ ^ 2 = (Ideal.absNorm (Ideal.span {a}) : ℝ) := by
  open ActualEisensteinCoordinates ShortDraftLatticeCount in
    have hnorm : ‖eisEmbedding a‖ ^ 2 = (q (coords a) : ℝ) := by
      simpa only [eval_coords, q, pow_two] using
        eisEmbedding_eval_norm_sq (coords a).1 (coords a).2
    have hNat : (qNat a : ℤ) = q (coords a) := Int.toNat_of_nonneg (qO_nonneg a)
    have hNatR := congrArg (fun n : ℤ => (n : ℝ)) hNat
    simp only [Int.cast_natCast] at hNatR
    rw [← qNat_eq_absNorm_span, hNatR]
    exact hnorm

theorem finitePrimeModulus_norm_sq {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) :
    ‖eisEmbedding (finitePrimeModulus P)‖ ^ 2 = (Ideal.absNorm (∏ i, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, span_finitePrimeModulus]

def principalSexticRow {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    (r : O ⧸ Ideal.span {c}) : ℂ :=
  finiteSexticQuotientRow P hcop hgood j (Ideal.quotEquivOfEq hc r)

@[simp] theorem principalSexticRow_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (a : O) :
    principalSexticRow P hcop hgood j c hc (Ideal.Quotient.mk (Ideal.span {c}) a) =
      finiteSexticRow P hgood j a := by
  simp only [principalSexticRow, finiteSexticQuotientRow,
    Ideal.quotEquivOfEq_mk, IdealGaussCRT.quotientProdEquivPi_mk, finiteSexticRow]

theorem canonical_principal_gauss_transform {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj P hcop hgood hchar j hj0 hj6 φ (e h)

theorem canonical_radial_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let hc0 := finitePrimeModulus_ne_zero P
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r) := by
    rw [canonical_principal_gauss_transform P hcop hgood hchar j hj0 hj6 c
      (span_finitePrimeModulus P) ψ, principalSexticRow_mk]
  have hp := actual_radial_paper_poisson_trace W scale hscale c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  simpa only [row, principalSexticRow_mk] using hp

def canonicalGaussSum {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) : ℂ := by
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  exact ∑ r, row r * ψ r

def canonicalNormalizedGauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) : ℂ :=
  canonicalGaussSum P hcop hgood j / (‖eisEmbedding (finitePrimeModulus P)‖ : ℂ)

theorem canonical_radial_poisson_normalized {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow P hgood j h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  let G := canonicalGaussSum P hcop hgood j
  let F : O → ℂ := fun h => star (finiteSexticRow P hgood j h) *
    paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)
  have hp := canonical_radial_poisson P hcop hgood hchar j hj0 hj6 W scale hscale
  change (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
    (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
      (star (finiteSexticRow P hgood j h) * G) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  have hsum : (∑' h : O, (star (finiteSexticRow P hgood j h) * G) *
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, F h := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    dsimp [F]
    ring
  rw [hsum] at hp
  rw [hp]
  change ((scale / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * ∑' h : O, F h) =
    ((scale : ℂ) * (G / (‖eisEmbedding c‖ : ℂ)) / (‖eisEmbedding c‖ : ℂ)) *
      ∑' h : O, F h
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  push_cast
  field_simp

theorem canonical_compact_radial_poisson_normalized {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow P hgood j h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  exact canonical_radial_poisson_normalized P hcop hgood hchar j hj0 hj6
    (hWc.toSchwartzMap hWs) scale hscale

theorem finiteSexticRow_eq_zero_iff {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    finiteSexticRow P hgood j a = 0 ↔ ∃ i, a ∈ P i := by
  classical
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  simp only [finiteSexticRow, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    MulChar.apply_eq_zero_iff, isUnit_iff_ne_zero, not_not, Ideal.Quotient.eq_zero_iff_mem]

theorem finiteSexticRow_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) :
    finiteSexticRow P hgood j 0 = 0 := by
  rw [finiteSexticRow_eq_zero_iff]
  exact ⟨Classical.arbitrary ι, Ideal.zero_mem _⟩

theorem finiteSexticRow_radial_summable {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    Summable (fun z : O => finiteSexticRow P hgood j z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) := by
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W scale hscale)
    (Ideal.Quotient.mk (Ideal.span {c}))
    (principalSexticRow P hcop hgood j c (span_finitePrimeModulus P))
  simpa only [principalSexticRow_mk, scaledRadialTest_apply] using hs

theorem finiteSexticRow_disjoint_pair {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSexticRow P hgood (fun i => if i ∈ S then 1 else 5) a =
      finiteSquarefreeRow P hgood S a *
        star (finiteSquarefreeRow P hgood (Finset.univ \ S) a) := by
  simpa only [finiteSexticQuotientRow, IdealGaussCRT.quotientProdEquivPi_mk,
    finiteSexticRow] using finiteSexticQuotientRow_disjoint_pair_mk P hcop hgood S a

theorem canonical_disjoint_pair_radial_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let row := fun a => finiteSquarefreeRow P hgood S a *
      star (finiteSquarefreeRow P hgood (Finset.univ \ S) a)
    (∑' z : O, row z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood
        (fun i => if i ∈ S then 1 else 5) / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (row h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  have hp := canonical_radial_poisson_normalized P hcop hgood hchar
    (fun i => if i ∈ S then 1 else 5)
    (fun i => by split_ifs <;> decide) (fun i => by split_ifs <;> decide)
    W scale hscale
  simpa only [finiteSexticRow_disjoint_pair P hcop hgood S] using hp

end ActualEisensteinCubic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Poisson.RadialFourier -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

def radialTestCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℝ (Function.hasTemperateGrowth_norm_sq ℂ)
    ⟨1, 1, fun z => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      nlinarith [sq_nonneg (‖z‖ - 1)]⟩

@[simp] theorem radialTestCLM_apply (W : 𝓢(ℝ, ℂ)) : radialTestCLM W = radialTest W := by
  ext z
  rfl

def radialFourierCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  (FourierTransform.fourierCLM ℝ 𝓢(ℂ, ℂ)).comp radialTestCLM

@[simp] theorem radialFourierCLM_apply (W : 𝓢(ℝ, ℂ)) :
    radialFourierCLM W = 𝓕 (radialTest W) := by
  simp [radialFourierCLM]

theorem paperRadialFourier_eq_plane (W : 𝓢(ℝ, ℂ)) (t : ℝ) :
    paperRadialFourier W t =
      (2 / Real.sqrt 3 : ℝ) • radialFourierCLM W (paperFrequency (Real.sqrt t : ℂ)) := by
  rw [paperRadialFourier, paperFourier_eq_standard, radialFourierCLM_apply]
  rfl

theorem paperFrequency_sqrt_norm_sq (t : ℝ) (ht : 0 ≤ t) :
    ‖paperFrequency (Real.sqrt t : ℂ)‖ ^ 2 = (4 / 3 : ℝ) * t := by
  rw [paperFrequency_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht]

theorem paperRadialFourier_weighted_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ A * ‖paperRadialFourier W t‖ ≤
      (2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A) *
        (Finset.Iic (2 * A, 0)).sup (schwartzSeminormFamily ℝ ℂ ℂ)
          (radialFourierCLM W) := by
  let ξ : ℂ := paperFrequency (Real.sqrt t : ℂ)
  have hn : ‖ξ‖ ^ 2 = (4 / 3 : ℝ) * t := paperFrequency_sqrt_norm_sq t ht
  have hscale : 0 ≤ (2 / Real.sqrt 3 : ℝ) := by positivity
  have hpow : (1 + t) ^ A ≤ (1 + ‖ξ‖) ^ (2 * A) := by
    have hbase : 1 + t ≤ (1 + ‖ξ‖) ^ 2 := by
      nlinarith [norm_nonneg ξ]
    calc
      (1 + t) ^ A ≤ ((1 + ‖ξ‖) ^ 2) ^ A := pow_le_pow_left₀ (by positivity) hbase A
      _ = _ := by rw [← pow_mul]
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2 * A, 0)) (k := 2 * A) (n := 0) le_rfl le_rfl (radialFourierCLM W) ξ
  simp only [norm_iteratedFDeriv_zero] at hb
  rw [paperRadialFourier_eq_plane, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  change (1 + t) ^ A * ((2 / Real.sqrt 3) * ‖radialFourierCLM W ξ‖) ≤ _
  calc
    _ = (2 / Real.sqrt 3) * ((1 + t) ^ A * ‖radialFourierCLM W ξ‖) := by ring
    _ ≤ (2 / Real.sqrt 3) * ((1 + ‖ξ‖) ^ (2 * A) * ‖radialFourierCLM W ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hscale
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hb hscale using 1
      ring_nf
      rfl

theorem schwartzCLM_finite_seminorm_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(E, ℂ)) (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      S.sup (schwartzSeminormFamily ℝ E ℂ) (T W) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) :=
    (S.sup (schwartzSeminormFamily ℝ E ℂ)).comp T.toLinearMap
  have hq : Continuous q :=
    (((schwartz_withSeminorms ℝ E ℂ).finset_sups).continuous_seminorm S).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

theorem paperRadialFourier_source_weighted_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (t : ℝ), 0 ≤ t →
        (1 + t) ^ A * ‖paperRadialFourier W t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hbound⟩ :=
    schwartzCLM_finite_seminorm_control radialFourierCLM (Finset.Iic (2 * A, 0))
  refine ⟨s, (2 / Real.sqrt 3) * 2 ^ (2 * A) * C, by positivity, ?_⟩
  intro W t ht
  apply (paperRadialFourier_weighted_bound W A t ht).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound W)
      (show 0 ≤ (2 / Real.sqrt 3) * 2 ^ (2 * A) by positivity)

theorem paperRadialFourier_source_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (t : ℝ), 0 ≤ t →
        ‖paperRadialFourier W t‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + t) ^ A := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_source_weighted_bound A
  refine ⟨s, C, hC, ?_⟩
  intro W t ht
  apply (le_div_iff₀ (by positivity : 0 < (1 + t) ^ A)).mpr
  simpa only [mul_comm] using hbound W t ht

end

section
open MeasureTheory
open scoped SchwartzMap ContDiff

def halfEulerCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((x / 2 : ℝ) : ℂ))).comp
    (SchwartzMap.derivCLM ℂ ℂ)

@[simp] theorem halfEulerCLM_apply (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    halfEulerCLM g s = (s / 2 : ℝ) • deriv g s := by
  have hg : (fun x : ℝ => ((x / 2 : ℝ) : ℂ)).HasTemperateGrowth := by
    simp only [div_eq_mul_inv]
    fun_prop
  simp only [halfEulerCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.derivCLM_apply]
  rfl

theorem hasDerivAt_halfFlow (g : 𝓢(ℝ, ℂ)) (a t : ℝ) :
    HasDerivAt (fun y : ℝ => g (a * Real.exp (y / 2)))
      (halfEulerCLM g (a * Real.exp (t / 2))) t := by
  have hf : HasDerivAt (fun y : ℝ => a * Real.exp (y / 2))
      ((a * Real.exp (t / 2)) / 2) t := by
    convert (((hasDerivAt_id t).div_const 2).exp.const_mul a) using 1 <;> simp only [id_eq] ; ring
  simpa only [halfEulerCLM_apply, Function.comp_def] using
    (g.hasDerivAt (a * Real.exp (t / 2))).scomp t hf

theorem iteratedDeriv_halfFlow (g : 𝓢(ℝ, ℂ)) (a : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun y : ℝ => g (a * Real.exp (y / 2))) t =
      ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) (a * Real.exp (t / 2)) := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y : ℝ => g (a * Real.exp (y / 2))) =
        fun y : ℝ => halfEulerCLM g (a * Real.exp (y / 2)) :=
      funext (fun y => (hasDerivAt_halfFlow g a y).deriv)
    rw [hd, ih (halfEulerCLM g),
      Function.iterate_succ_apply]

 theorem sqrt_exp_half (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  rw [Real.sqrt_eq_iff_eq_sq (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

 theorem eulerDeriv_sqrt_profile (g : 𝓢(ℝ, ℂ)) (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    LocalLogFourier.eulerDeriv (fun s => g (Real.sqrt s)) j x =
      ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) (Real.sqrt x) := by
  unfold LocalLogFourier.eulerDeriv
  have hflow : (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) =
      fun t : ℝ => g (Real.sqrt x * Real.exp (t / 2)) := by
    funext t
    rw [Real.sqrt_mul hx, sqrt_exp_half]
  rw [hflow, iteratedDeriv_halfFlow]
  simp

theorem contDiffOn_sqrt_profile (g : 𝓢(ℝ, ℂ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ => g (Real.sqrt x)) (Set.Ioi 0) := by
  intro x hx
  exact ((g.smooth ⊤).contDiffAt.comp x
    (Real.contDiffAt_sqrt (ne_of_gt hx))).contDiffWithinAt

theorem contDiff_sqrt_profile_log (g : 𝓢(ℝ, ℂ)) (x : ℝ) (hx : 0 ≤ x) :
    ContDiff ℝ ∞ (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) := by
  have heq : (fun t : ℝ => g (Real.sqrt (x * Real.exp t))) =
      fun t : ℝ => g (Real.sqrt x * Real.exp (t / 2)) := by
    funext t
    rw [Real.sqrt_mul hx, sqrt_exp_half]
  rw [heq]
  exact (g.smooth ⊤).comp (by fun_prop)

theorem sqrt_profile_rapid_bound (g : 𝓢(ℝ, ℂ)) (A : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖g (Real.sqrt x)‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0 g +
        SchwartzMap.seminorm ℝ (2 * A) 0 g) := by
  have hsmall := SchwartzMap.norm_le_seminorm ℝ g (Real.sqrt x)
  have hlarge := SchwartzMap.norm_pow_mul_le_seminorm ℝ g (2 * A) (Real.sqrt x)
  have hsqrt : ‖Real.sqrt x‖ ^ (2 * A) = x ^ A := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
      pow_mul, Real.sq_sqrt hx]
  rw [hsqrt] at hlarge
  have hs0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 g := by positivity
  have hsA : 0 ≤ SchwartzMap.seminorm ℝ (2 * A) 0 g := by positivity
  by_cases hx1 : x ≤ 1
  · have hp : (1 + x) ^ A ≤ (2 : ℝ) ^ A := by gcongr; linarith
    calc
      _ ≤ 2 ^ A * ‖g (Real.sqrt x)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ A * SchwartzMap.seminorm ℝ 0 0 g := by gcongr
      _ ≤ _ := by gcongr; linarith
  · have hp : (1 + x) ^ A ≤ (2 * x) ^ A := by gcongr; linarith
    calc
      _ ≤ (2 * x) ^ A * ‖g (Real.sqrt x)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 2 ^ A * (x ^ A * ‖g (Real.sqrt x)‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ A * SchwartzMap.seminorm ℝ (2 * A) 0 g := by gcongr
      _ ≤ _ := by gcongr; linarith

theorem eulerDeriv_sqrt_profile_rapid_bound (g : 𝓢(ℝ, ℂ)) (A j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (fun s => g (Real.sqrt s)) j x‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0
          ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) +
        SchwartzMap.seminorm ℝ (2 * A) 0
          ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g)) := by
  rw [eulerDeriv_sqrt_profile g j x hx]
  exact sqrt_profile_rapid_bound _ A x hx

theorem paperFrequency_real_temperate :
    (fun s : ℝ => paperFrequency (s : ℂ)).HasTemperateGrowth := by
  have heq : (fun s : ℝ => paperFrequency (s : ℂ)) =
      fun s : ℝ => (2 * Complex.I / (Real.sqrt 3 : ℂ)) * (s : ℂ) := by
    funext s
    simp [paperFrequency]
  rw [heq]
  fun_prop

theorem paperFrequency_real_growth (s : ℝ) :
    ‖s‖ ≤ 1 + ‖paperFrequency (s : ℂ)‖ := by
  have hn := paperFrequency_norm_sq (s : ℂ)
  have heq : ‖(s : ℂ)‖ = ‖s‖ := by simp
  rw [heq] at hn
  have hns := norm_nonneg s
  have hnf := norm_nonneg (paperFrequency (s : ℂ))
  nlinarith [sq_nonneg (‖s‖ - ‖paperFrequency (s : ℂ)‖)]

def paperRealRayCLM : 𝓢(ℂ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ paperFrequency_real_temperate
    ⟨1, 1, by simpa using paperFrequency_real_growth⟩

@[simp] theorem paperRealRayCLM_apply (g : 𝓢(ℂ, ℂ)) (s : ℝ) :
    paperRealRayCLM g s = g (paperFrequency (s : ℂ)) := rfl

def halfEulerIterateCLM : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)
  | 0 => ContinuousLinearMap.id ℝ _
  | j + 1 => (halfEulerCLM.restrictScalars ℝ).comp (halfEulerIterateCLM j)

@[simp] theorem halfEulerIterateCLM_apply (j : ℕ) (g : 𝓢(ℝ, ℂ)) :
    halfEulerIterateCLM j g = (halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [halfEulerIterateCLM, ContinuousLinearMap.comp_apply,
      ih, Function.iterate_succ_apply']
    rfl

def paperFourierRayCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) • (paperRealRayCLM.comp radialFourierCLM)

@[simp] theorem paperFourierRayCLM_apply (W : 𝓢(ℝ, ℂ)) (s : ℝ) :
    paperFourierRayCLM W s =
      (2 / Real.sqrt 3 : ℝ) • radialFourierCLM W (paperFrequency (s : ℂ)) := by
  simp [paperFourierRayCLM]

theorem paperRadialFourier_eq_ray (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier W = fun x : ℝ => paperFourierRayCLM W (Real.sqrt x) := by
  funext x
  rw [paperRadialFourier_eq_plane, paperFourierRayCLM_apply]

def paperEulerCLM (j : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (halfEulerIterateCLM j).comp paperFourierRayCLM

theorem paperRadialFourier_eulerDeriv (W : 𝓢(ℝ, ℂ)) (j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    LocalLogFourier.eulerDeriv (paperRadialFourier W) j x =
      paperEulerCLM j W (Real.sqrt x) := by
  rw [paperRadialFourier_eq_ray, eulerDeriv_sqrt_profile _ j x hx]
  simp only [paperEulerCLM, ContinuousLinearMap.comp_apply, halfEulerIterateCLM_apply]

theorem paperRadialFourier_contDiffOn (W : 𝓢(ℝ, ℂ)) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) := by
  rw [paperRadialFourier_eq_ray]
  exact contDiffOn_sqrt_profile _

theorem paperRadialFourier_log_contDiff (W : 𝓢(ℝ, ℂ)) (x : ℝ) (hx : 0 ≤ x) :
    ContDiff ℝ ∞ (fun t : ℝ => paperRadialFourier W (x * Real.exp t)) := by
  rw [paperRadialFourier_eq_ray]
  exact contDiff_sqrt_profile_log _ x hx

theorem paperRadialFourier_euler_weighted_bound (W : 𝓢(ℝ, ℂ)) (A j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0 (paperEulerCLM j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (paperEulerCLM j W)) := by
  rw [paperRadialFourier_eulerDeriv W j x hx]
  exact sqrt_profile_rapid_bound _ A x hx

theorem schwartzCLM_family_finite_seminorm_control
    (T : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K →
        SchwartzMap.seminorm ℝ 0 0 (T j W) +
          SchwartzMap.seminorm ℝ (2 * A) 0 (T j W) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let qj : ℕ → Seminorm ℝ 𝓢(ℝ, ℂ) := fun j =>
    (SchwartzMap.seminorm ℝ 0 0 + SchwartzMap.seminorm ℝ (2 * A) 0).comp
      (T j).toLinearMap
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) := ∑ j ∈ Finset.range (K + 1), qj j
  have hqfun : (q : 𝓢(ℝ, ℂ) → ℝ) = fun W => ∑ j ∈ Finset.range (K + 1),
      (SchwartzMap.seminorm ℝ 0 0 (T j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T j W)) := by
    funext W
    simp [q, qj]
  have hq : Continuous q := by
    rw [hqfun]
    apply continuous_finsetSum
    intro j hj
    exact (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp
        (T j).continuous).add
      (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2 * A, 0)).comp
        (T j).continuous)
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W j hj
    apply le_trans ?_ (Seminorm.le_def.mp hbound W)
    rw [hqfun]
    exact Finset.single_le_sum (f := fun i =>
      SchwartzMap.seminorm ℝ 0 0 (T i W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T i W))
      (by intro i hi; positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem paperRadialFourier_euler_source_weighted_bound (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K → ∀ (x : ℝ), 0 ≤ x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hbound⟩ :=
    schwartzCLM_family_finite_seminorm_control paperEulerCLM A K
  refine ⟨s, 2 ^ A * C, by positivity, ?_⟩
  intro W j hj x hx
  apply (paperRadialFourier_euler_weighted_bound W A j x hx).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound W j hj) (show 0 ≤ (2 : ℝ) ^ A by positivity)

theorem paperRadialFourier_euler_source_decay (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K → ∀ (x : ℝ), 0 ≤ x →
        ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + x) ^ A := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  refine ⟨s, C, hC, ?_⟩
  intro W j hj x hx
  apply (le_div_iff₀ (by positivity : 0 < (1 + x) ^ A)).mpr
  simpa only [mul_comm] using hbound W j hj x hx

theorem paperRadialFourier_euler_bound (W : 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro j hj x hx
  exact hbound W j hj x hx.le

theorem compact_paperRadialFourier_regular
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (A K : ℕ) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) ∧
      ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  exact ⟨paperRadialFourier_contDiffOn (hWc.toSchwartzMap hWs),
    paperRadialFourier_euler_bound (hWc.toSchwartzMap hWs) A K⟩

theorem paperRadialFourier_log_separation
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : ℝ → ℂ,
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_uniform V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem inverse_square_le_cauchy_product (a b q : ℝ) (hq : 0 ≤ q)
    (hQ : (a ^ 2 + b ^ 2) / 2 ≤ q) :
    ((1 + q) ^ 2)⁻¹ ≤
      4 * ((1 + a ^ 2)⁻¹ * (1 + b ^ 2)⁻¹) := by
  have hsum : 1 + a ^ 2 + b ^ 2 ≤ 2 * (1 + q) := by linarith
  have hsquare : (1 + a ^ 2 + b ^ 2) ^ 2 ≤ (2 * (1 + q)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hsum
  have hden : (1 + a ^ 2) * (1 + b ^ 2) ≤ 4 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  calc
    _ = 1 / (1 + q) ^ 2 := by simp only [one_div]
    _ ≤ 4 / ((1 + a ^ 2) * (1 + b ^ 2)) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hden)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem eisenstein_cauchy_summable :
    Summable (fun h : O => ((1 + ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by
  apply (latticeCoordEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => inv_nonneg.mpr (sq_nonneg _)) _
    (summable_int_cauchy_product.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (p.1 : ℝ) (p.2 : ℝ)
    (‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) (sq_nonneg _)
  change ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / 2 ≤
    ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
  rw [eisEmbedding_eval_norm_sq]
  push_cast
  nlinarith [sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ))]

def eisensteinCauchyMass : ℝ :=
  ∑' h : O, ((1 + ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹

theorem eisensteinCauchyMass_nonneg : 0 ≤ eisensteinCauchyMass :=
  tsum_nonneg (fun _ => by positivity)

theorem eisensteinCauchyMass_subtype (S : Set O) :
    (∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) ≤ eisensteinCauchyMass := by
  exact (eisenstein_cauchy_summable.subtype S).tsum_le_tsum_of_inj
    Subtype.val Subtype.val_injective (fun _ _ => by positivity) (fun _ => le_rfl)
    eisenstein_cauchy_summable

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

theorem paperRadialFourier_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
        (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound (A + 2)
  refine ⟨s, C * (eisensteinCauchyMass + 1), by
    have := eisensteinCauchyMass_nonneg
    positivity, ?_⟩
  intro W K T hK hT
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + T) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hD : 0 < D := by dsimp [D]; positivity
  let S := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hp (h : S) :
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    exact polynomial_tail_majorant A K T _ B _ hK hT (sq_nonneg _)
      (norm_nonneg _) h.property (hb W _ (by positivity))
  have hmajor : Summable (fun h : S => (B / D) *
      ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
    (eisenstein_cauchy_summable.subtype S).mul_left (B / D)
  have hs : Summable (fun h : S =>
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : S, (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / D) * ∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / D) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype S) (div_nonneg hB hD.le)
    _ ≤ (B / D) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, D]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_injective_on_squarefree
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J)
    (h : idealSupport F I = idealSupport F J) : I = J := by
  have hfac : UniqueFactorizationMonoid.normalizedFactors I =
      UniqueFactorizationMonoid.normalizedFactors J := by
    rw [Multiset.Nodup.ext
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsI.ne_zero).mp hsI)
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsJ.ne_zero).mp hsJ)]
    intro P
    constructor
    · intro hP
      let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨I, hI, hP⟩⟩
      have hp : p ∈ idealSupport F I := (mem_idealSupport_iff F I p).mpr hP
      rw [h] at hp
      exact (mem_idealSupport_iff F J p).mp hp
    · intro hP
      let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨J, hJ, hP⟩⟩
      have hp : p ∈ idealSupport F J := (mem_idealSupport_iff F J p).mpr hP
      rw [← h] at hp
      exact (mem_idealSupport_iff F I p).mp hp
  rw [← Ideal.prod_normalizedFactors_eq_self hsI.ne_zero,
    ← Ideal.prod_normalizedFactors_eq_self hsJ.ne_zero, hfac]

theorem baseChangeWeight_eq_zero_of_not_squarefree
    {q : ℕ} (χ : DirichletCharacter ℂ q) {I : Ideal O} (hI : ¬ Squarefree I) :
    baseChangeWeight χ I = 0 := by
  simp only [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hI,
    Int.cast_zero, zero_mul]

end ConcretePrimeRowBridge

end

end OAI

end

