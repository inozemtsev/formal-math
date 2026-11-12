module

public import Mathlib
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Data.Nat.Totient
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Data.List.Prime
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Green64.Library.Analysis.Compactness.Part002

@[expose] public section

/-!
# Analysis / Estimates / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceFourierLpParseval -/

section

open MeasureTheory

/-- Finite normalized circle Fourier Parseval, with signed integer
frequencies and arbitrary complex coefficients. No arithmetic
independence or cancellation is required. -/
theorem source_fourierLp_finite_parseval (s : Finset ℤ) (a : ℤ → ℂ) :
    ‖∑ n ∈ s, a n • (fourierLp (T := 1) 2 n)‖ ^ 2 =
      ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have hinner := (orthonormal_fourier (T := 1)).inner_sum a a s
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [hinner]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_comm, Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  norm_cast

end

/-! ## SourceL1FourierPairing -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 800000

/-- L¹ Fourier self-adjoint pairing with a Schwartz test.
This is the generic missing bridge from classical L¹ Fourier to L². -/
theorem source_L1_fourier_pairing434 (f : ℝ → ℂ)
    (hf : Integrable f) (psi : 𝓢(ℝ,ℂ)) :
    (∫ s : ℝ, (𝓕 f) s * psi s) =
      ∫ u : ℝ, f u * (𝓕 (psi : ℝ → ℂ)) u := by
  have hpair := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf psi.integrable
  have hv (g : ℝ → ℂ) (s : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar
        (volume : Measure ℝ) (innerₗ ℝ) g s = (𝓕 g) s := by
    rw [Real.fourier_eq]
    rfl
  have hsym : (innerₗ ℝ).flip = innerₗ ℝ := by
    ext x y
    simp only [LinearMap.flip_apply]
  rw [hsym] at hpair
  simp_rw [hv, smul_eq_mul] at hpair
  exact hpair
end Green64Analytic.CorrelationSquare

end

/-! ## SourceL1L2FourierTest -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- On every genuine Schwartz test, the classical L¹ Fourier transform
and the L²-Fourier transform have the same distributional pairing.
Source independent, no energy hypotheses other than L¹∩L² membership. -/
theorem source_L1L2_fourier_test_pair434
    (f : ℝ → ℂ) (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hF2 : MemLp (𝓕 f) 2 (volume : Measure ℝ))
    (psi : 𝓢(ℝ,ℂ)) :
    (∫ s : ℝ, psi s *
      ((MemLp.toLp (𝓕 f) hF2 : Lp ℂ 2 (volume : Measure ℝ)) s)) =
      (∫ u : ℝ, (𝓕 psi) u *
      ((MemLp.toLp f hf2 : Lp ℂ 2 (volume : Measure ℝ)) u)) := by
  have hFa := hF2.coeFn_toLp
  have hPa := hf2.coeFn_toLp
  calc
    _ = ∫ s : ℝ, psi s * (𝓕 f) s := by
      apply integral_congr_ae
      filter_upwards [hFa] with s hs
      rw [hs]
    _ = ∫ s : ℝ, (𝓕 f) s * psi s := by
      apply integral_congr_ae
      filter_upwards with s
      ring
    _ = ∫ u : ℝ, f u * (𝓕 (psi : ℝ → ℂ)) u :=
      source_L1_fourier_pairing434 f hf1 psi
    _ = ∫ u : ℝ, (𝓕 psi) u * f u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [← congrFun (SchwartzMap.fourier_coe psi) u]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hPa] with u hu
      rw [hu]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceL1L2FourierDistribution -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1100000

/-- Genuine identification of the L¹ classical Fourier transform with
the L² isometric Fourier transform, via equality of tempered
distributions and their injective canonical L² embedding. -/
theorem source_L1L2_fourier_compat434
    (f : ℝ → ℂ) (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ))
    (hF2 : MemLp (𝓕 f) 2 (volume : Measure ℝ)) :
    (MemLp.toLp (𝓕 f) hF2 : Lp ℂ 2 (volume : Measure ℝ)) =
      𝓕 (MemLp.toLp f hf2 : Lp ℂ 2 (volume : Measure ℝ)) := by
  let F2 : Lp ℂ 2 (volume : Measure ℝ) := MemLp.toLp f hf2
  let G2 : Lp ℂ 2 (volume : Measure ℝ) := MemLp.toLp (𝓕 f) hF2
  have hDist : (G2 : 𝓢'(ℝ,ℂ)) = ((𝓕 F2 : Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ,ℂ)) := by
    rw [← Lp.fourier_toTemperedDistribution_eq F2]
    apply DFunLike.ext
    intro psi
    rw [TemperedDistribution.fourier_apply]
    simp only [Lp.toTemperedDistribution_apply, smul_eq_mul]
    change (∫ x : ℝ, psi x * G2 x) =
      (∫ x : ℝ, (𝓕 psi) x * F2 x)
    exact source_L1L2_fourier_test_pair434 f hf1 hf2 hF2 psi
  have hinj : Function.Injective
      (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2) :=
    LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot
        (F:=ℂ) (μ:=(volume : Measure ℝ)) (p:=2))
  exact hinj hDist
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteCharacterKernelReproduction -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Exact character reproduction expansion for a finite,
physically weighted conditional character-frame kernel. The
kernel is evaluated as K(D,X), retaining the input character
at D and output character at X. This orientation is essential
for the original major-arc comparison statement. -/
theorem source_original_finite_character_kernel_reproduction434
    {X C : Type} [Fintype X] [Fintype C]
    (w : X → ℝ) (chi : X → C → ℂ)
    (gate : X → Prop) (nu : ℝ)
    (p : X) (hp : gate p) (e : C) :
    (∑ q : X, (w q:ℂ) *
      (if gate q ∧ gate p then (nu:ℂ)⁻¹ *
        (∑ c : C, star (chi q c) * chi p c)
       else 0) * chi q e) =
    ∑ c : C,
      ((∑ q : X, (w q:ℂ) *
        (if gate q then star (chi q c) * chi q e else 0)) /
          (nu:ℂ)) * chi p c := by
  classical
  let T : X → C → ℂ := fun q c =>
    (w q:ℂ) * (if gate q then star (chi q c) * chi q e else 0)
  have hrow (q : X) :
      (w q:ℂ) *
        (if gate q ∧ gate p then (nu:ℂ)⁻¹ *
          (∑ c : C, star (chi q c) * chi p c)
         else 0) * chi q e =
      ∑ c : C, ((nu:ℂ)⁻¹ * (T q c)) * chi p c := by
    by_cases hq : gate q
    · simp only [hq, hp, and_self, and_true, if_pos, T]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      ring
    · simp only [hq, false_and, if_neg, mul_zero, zero_mul, T]
      simp [hq]
  calc
    _ = ∑ q : X, ∑ c : C,
          ((nu:ℂ)⁻¹ * T q c) * chi p c := by
          apply Finset.sum_congr rfl
          intro q hq
          exact hrow q
    _ = ∑ c : C, ∑ q : X,
          ((nu:ℂ)⁻¹ * T q c) * chi p c := Finset.sum_comm
    _ = ∑ c : C,
          ((∑ q : X, T q c)/(nu:ℂ)) * chi p c := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          rw [div_eq_mul_inv]
          ring
    _ = _ := by rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteTwoGlobalCharacterMode -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exact independent prime-tuple Fubini and quantitative
reproduction error for ONE character mode in each ORIGINAL
GLOBAL block. The two character modes may have distinct
conductors. No test-function independence is presumed; here
the explicit product structure comes from the rational
character mode itself. -/
theorem source_original_finite_two_global_character_mode434
    {X Y : Type} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ)
    (KX : X → X → ℂ) (KY : Y → Y → ℂ)
    (chiX : X → ℂ) (chiY : Y → ℂ)
    (pX : X) (pY : Y)
    (epsX epsY : ℝ) (hepsX : 0 ≤ epsX) (hepsY : 0 ≤ epsY)
    (hChiX : ‖chiX pX‖ ≤ 1) (hChiY : ‖chiY pY‖ ≤ 1)
    (hRepX :
      ‖(∑ qX : X, (wX qX:ℂ)*KX qX pX*chiX qX) -
         chiX pX‖ ≤ epsX)
    (hRepY :
      ‖(∑ qY : Y, (wY qY:ℂ)*KY qY pY*chiY qY) -
         chiY pY‖ ≤ epsY) :
    ‖(∑ q : X × Y,
        ((wX q.1:ℂ)*(wY q.2:ℂ))*
          (KX q.1 pX*KY q.2 pY)*
          (chiX q.1*chiY q.2)) -
       (chiX pX*chiY pY)‖ ≤
      epsX+epsY+epsX*epsY := by
  classical
  let RX : ℂ := ∑ qX : X, (wX qX:ℂ)*KX qX pX*chiX qX
  let RY : ℂ := ∑ qY : Y, (wY qY:ℂ)*KY qY pY*chiY qY
  let x : ℂ := chiX pX
  let y : ℂ := chiY pY
  have hfactor :
    (∑ q : X × Y,
      ((wX q.1:ℂ)*(wY q.2:ℂ))*
        (KX q.1 pX*KY q.2 pY)*
        (chiX q.1*chiY q.2)) = RX*RY := by
    calc
      _ = ∑ qX : X, ∑ qY : Y,
        ((wX qX:ℂ)*KX qX pX*chiX qX)*
        ((wY qY:ℂ)*KY qY pY*chiY qY) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro qX hqX
        apply Finset.sum_congr rfl
        intro qY hqY
        ring
      _ = ∑ qX : X,
        ((wX qX:ℂ)*KX qX pX*chiX qX)*
          (∑ qY : Y, (wY qY:ℂ)*KY qY pY*chiY qY) := by
        apply Finset.sum_congr rfl
        intro qX hqX
        rw [Finset.mul_sum]
      _ = RX*RY := by
        dsimp [RX,RY]
        rw [Finset.sum_mul]
  have hMul12 : ‖(RX-x)*(RY-y)‖ ≤ epsX*epsY := by
    rw [norm_mul]
    exact mul_le_mul hRepX hRepY (norm_nonneg _) hepsX
  have hMulY : ‖(RX-x)*y‖ ≤ epsX := by
    rw [norm_mul]
    exact (mul_le_mul hRepX hChiY (norm_nonneg _) hepsX).trans_eq
      (mul_one epsX)
  have hMulX : ‖x*(RY-y)‖ ≤ epsY := by
    rw [norm_mul]
    exact (mul_le_mul hChiX hRepY (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul epsY)
  have halg :
      RX*RY - x*y =
        ((RX-x)*(RY-y)+(RX-x)*y)+x*(RY-y) := by ring
  rw [hfactor, halg]
  calc
    _ ≤ ‖(RX-x)*(RY-y)+(RX-x)*y‖ + ‖x*(RY-y)‖ :=
      norm_add_le _ _
    _ ≤ (‖(RX-x)*(RY-y)‖ + ‖(RX-x)*y‖) +
          ‖x*(RY-y)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (epsX*epsY+epsX)+epsY :=
      add_le_add (add_le_add hMul12 hMulY) hMulX
    _ = epsX+epsY+epsX*epsY := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFiniteTwoGlobalFourierSpan -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Finite rational-Fourier character span over BOTH original
GLOBAL primitive blocks. Each Fourier basis mode separates
multiplicatively between the two products (a fact special to
Dirichlet characters), but neither the kernel nor its coefficient
sum is replaced by independent test assumptions. An arbitrary
finite complex coefficient vector is allowed, and the precise
l1 coefficient norm is retained. The only analytical inputs
are the actual per-character physical frame reproduction bounds. -/
theorem source_original_finite_two_global_fourier_span434
    {X Y C : Type} [Fintype X] [Fintype Y] [Fintype C]
    (wX : X → ℝ) (wY : Y → ℝ)
    (KX : X → X → ℂ) (KY : Y → Y → ℂ)
    (chiX : X → C → ℂ) (chiY : Y → C → ℂ)
    (pX : X) (pY : Y)
    (epsX epsY : ℝ) (hepsX : 0 ≤ epsX) (hepsY : 0 ≤ epsY)
    (hChiX : ∀ e, ‖chiX pX e‖ ≤ 1)
    (hChiY : ∀ e, ‖chiY pY e‖ ≤ 1)
    (hRepX : ∀ e : C,
      ‖(∑ qX : X, (wX qX:ℂ)*KX qX pX*chiX qX e) -
        chiX pX e‖ ≤ epsX)
    (hRepY : ∀ e : C,
      ‖(∑ qY : Y, (wY qY:ℂ)*KY qY pY*chiY qY e) -
        chiY pY e‖ ≤ epsY)
    (a : C → ℂ) :
    ‖(∑ q : X × Y,
      ((wX q.1:ℂ)*(wY q.2:ℂ))*
        (KX q.1 pX*KY q.2 pY)*
        (∑ e : C, a e*(chiX q.1 e*chiY q.2 e))) -
      (∑ e : C, a e*(chiX pX e*chiY pY e))‖ ≤
    (epsX+epsY+epsX*epsY) * (∑ e : C, ‖a e‖) := by
  classical
  let delta : ℝ := epsX+epsY+epsX*epsY
  let F : X × Y → ℂ := fun q =>
    ((wX q.1:ℂ)*(wY q.2:ℂ)) * (KX q.1 pX*KY q.2 pY)
  let mode : C → ℂ := fun e =>
    ∑ q : X × Y, F q*(chiX q.1 e*chiY q.2 e)
  let target : C → ℂ := fun e => chiX pX e*chiY pY e
  have hmode (e : C) : ‖mode e - target e‖ ≤ delta := by
    exact source_original_finite_two_global_character_mode434
      wX wY KX KY (fun q => chiX q e) (fun q => chiY q e)
      pX pY epsX epsY hepsX hepsY
      (hChiX e) (hChiY e) (hRepX e) (hRepY e)
  have hswap :
      (∑ q : X × Y, F q *
        (∑ e : C, a e*(chiX q.1 e*chiY q.2 e))) =
      ∑ e : C, a e*mode e := by
    calc
      _ = ∑ q : X × Y, ∑ e : C,
          a e*(F q*(chiX q.1 e*chiY q.2 e)) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        ring
      _ = ∑ e : C, ∑ q : X × Y,
          a e*(F q*(chiX q.1 e*chiY q.2 e)) := Finset.sum_comm
      _ = ∑ e : C, a e*mode e := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.mul_sum]
  have hRewrite :
      (∑ e : C, a e*mode e) - (∑ e : C, a e*target e) =
      ∑ e : C, a e*(mode e-target e) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  change ‖(∑ q : X × Y, F q *
     (∑ e : C, a e*(chiX q.1 e*chiY q.2 e))) -
    (∑ e : C, a e*target e)‖ ≤
    delta * (∑ e : C, ‖a e‖)
  rw [hswap,hRewrite]
  have hterm (e : C) :
      ‖a e*(mode e-target e)‖ ≤ ‖a e‖*delta := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hmode e) (norm_nonneg _)
  calc
    _ ≤ ∑ e : C, ‖a e*(mode e-target e)‖ := norm_sum_le _ _
    _ ≤ ∑ e : C, ‖a e‖*delta :=
      Finset.sum_le_sum (fun e he => hterm e)
    _ = delta*(∑ e : C, ‖a e‖) := by
      rw [← Finset.sum_mul]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGcdCharacterBudget -/

section

open scoped BigOperators
open MeasureTheory
namespace Green64Analytic.CorrelationMellin
/-- The exact original all-gcd/all-character family has den terms:
principal, imprimitive and modulus-one characters are all counted. -/
theorem source_original_gcd_character_count (den : ℕ) (hden : 0 < den) :
    (∑ d ∈ den.divisors, Nat.card (DirichletCharacter ℂ (den/d))) = den := by
  classical
  have hcomp (d : ℕ) (hd : d ∈ den.divisors) :
      den/d ∈ den.divisors := by
    have hdvd := (Nat.mem_divisors.mp hd).1
    apply Nat.mem_divisors.mpr
    refine ⟨?_, Nat.ne_of_gt hden⟩
    exact ⟨d, (Nat.div_mul_cancel hdvd).symm⟩
  have htot : (∑ d ∈ den.divisors, (den/d).totient) =
      ∑ d ∈ den.divisors, d.totient := by
    apply Finset.sum_bij (fun d _ => den/d)
    · intro d hd; exact hcomp d hd
    · intro d hd e he hEq
      have hh := congrArg (fun u => den/u) hEq
      simpa only [Nat.div_div_self (Nat.mem_divisors.mp hd).1 (Nat.ne_of_gt hden),
        Nat.div_div_self (Nat.mem_divisors.mp he).1 (Nat.ne_of_gt hden)] using hh
    · intro e he
      refine ⟨den/e, hcomp e he, ?_⟩
      exact Nat.div_div_self (Nat.mem_divisors.mp he).1 (Nat.ne_of_gt hden)
    · intro d hd; rfl
  calc
    _ = ∑ d ∈ den.divisors, (den/d).totient := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd := (Nat.mem_divisors.mp hd).1
      have hdpos := Nat.pos_of_dvd_of_pos hdvd hden
      have hqpos : 0 < den/d := Nat.div_pos (Nat.le_of_dvd hden hdvd) hdpos
      letI : NeZero (den/d) := ⟨Nat.ne_of_gt hqpos⟩
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (den/d)
    _ = ∑ d ∈ den.divisors, d.totient := htot
    _ = den := Nat.sum_totient den

/-- Direct finite coefficient-energy summation used for the original
character/gcd and four-dyadic-box family. It retains every summand
with multiplicity and charges exactly the square of the family size. -/
theorem source_original_finite_family_energy
    {κ : Type} [Fintype κ] (F : κ → ℝ → ℂ) (coef : κ → ℂ)
    (lo hi E : ℝ) (hcoef : ∀ k, ‖coef k‖ ≤ 1)
    (hF : ∀ k, Continuous (F k))
    (hEnergy : ∀ k, (∫ t in Set.Icc lo hi, ‖F k t‖^2) ≤ E) :
    (∫ t in Set.Icc lo hi, ‖∑ k, coef k * F k t‖^2) ≤
      (Fintype.card κ : ℝ)^2 * E := by
  classical
  have hInt (k : κ) : IntegrableOn (fun t => ‖F k t‖^2) (Set.Icc lo hi) :=
    ((hF k).norm.pow 2).integrableOn_Icc
  have hPoint (t : ℝ) : ‖∑ k, coef k * F k t‖^2 ≤
      (Fintype.card κ : ℝ) * ∑ k, ‖F k t‖^2 := by
    calc
      _ ≤ (∑ k, ‖F k t‖)^2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        calc
          _ ≤ ∑ k, ‖coef k * F k t‖ := norm_sum_le _ _
          _ ≤ ∑ k, ‖F k t‖ := by
            apply Finset.sum_le_sum
            intro k _
            rw [norm_mul]
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcoef k) (norm_nonneg _)
      _ ≤ _ := by simpa only [Finset.card_univ] using
        (sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun k => ‖F k t‖))
  have hLeft : Continuous (fun t => ‖∑ k, coef k * F k t‖^2) :=
    ((continuous_finset_sum _ (fun k _ => continuous_const.mul (hF k))).norm.pow 2)
  have hRight : Continuous (fun t => (Fintype.card κ : ℝ) * ∑ k, ‖F k t‖^2) := by
    exact continuous_const.mul (continuous_finset_sum _ (fun k _ => (hF k).norm.pow 2))
  calc
    _ ≤ ∫ t in Set.Icc lo hi, (Fintype.card κ : ℝ) * ∑ k, ‖F k t‖^2 :=
      setIntegral_mono_on hLeft.integrableOn_Icc hRight.integrableOn_Icc measurableSet_Icc
        (fun t _ => hPoint t)
    _ = (Fintype.card κ : ℝ) * ∑ k, (∫ t in Set.Icc lo hi, ‖F k t‖^2) := by
      rw [integral_const_mul, integral_finset_sum _ (fun k _ => hInt k)]
    _ ≤ (Fintype.card κ : ℝ) * ∑ _k : κ, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hEnergy k)) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two, mul_assoc]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceOriginalHarmonicBudget -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Every actual source prime group has a sufficient harmonic cap 3L.
No dyadic interval or constant harmonic-mass assumption is imposed. -/
theorem source_original_group_harmonic_budget434
    (S : Finset ℕ) (N : ℕ) (x L : ℝ)
    (hN : 0 < N) (hx : 0 < x) (hL : 1 ≤ L)
    (hLog : L = Real.log x) (hCap : (N:ℝ) ≤ x^2)
    (hS : ∀ p ∈ S, 1 ≤ p ∧ p ≤ N) :
    (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ 3*L := by
  have hSub : S ⊆ Finset.Icc 1 N := fun p hp => Finset.mem_Icc.mpr (hS p hp)
  have hLogN : Real.log (N:ℝ) ≤ 2*L := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr hN) hCap
    simpa only [Real.log_pow,←hLog,Nat.cast_ofNat] using hh
  calc
    _ ≤ ∑ p ∈ Finset.Icc 1 N, (1:ℝ)/(p:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub (fun p _ _ => by positivity)
    _ ≤ 1+Real.log (N:ℝ) := by
      simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,
        Rat.cast_natCast,one_div] using harmonic_le_one_add_log N
    _ ≤ _ := by linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalOrderedPrimeFibreFactorial -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- A genuine ordered k-tuple of ACTUAL primes with product n
is a permutation of the unique prime factor list of n.
Numerical repeats are handled correctly: the output is a
list with multiplicities and no artificial squarefree
assumption. -/
theorem source_original_ordered_prime_product_perm434
    (S : Finset ℕ) (k n : ℕ)
    (hp : ∀ p ∈ S, Nat.Prime p)
    (a : Fin k → {p : ℕ // p ∈ S})
    (ha : (∏ i : Fin k, (a i).val)=n) :
    List.Perm
      (List.ofFn (fun i : Fin k => (a i).val))
      (Nat.primeFactorsList n) := by
  apply Nat.primeFactorsList_unique
  · simpa only [List.prod_ofFn] using ha
  · intro p h
    obtain ⟨i,hi⟩ :=
      (List.mem_ofFn' (fun i : Fin k => (a i).val) p).mp h
    rw [←hi]
    exact hp (a i).val (a i).property

/-- Quantitative number-theoretic fibre bound for the actual
ordered prime-label source law:
at fixed integer product n, at most k! different ordered
k-tuples of genuine primes occur.
This is TRUE even with numerical repeated prime labels.
The proof uses uniqueness of prime factorization AND
permutation-list counting, rather than assuming an abstract
atom-multiplicity inequality. -/
theorem source_original_ordered_prime_fibre_card_le_factorial434
    (S : Finset ℕ) (k n : ℕ)
    (hp : ∀ p ∈ S, Nat.Prime p) :
    ((Finset.univ : Finset (Fin k → {p : ℕ // p ∈ S})).filter
       (fun a => (∏ i : Fin k, (a i).val)=n)).card ≤
       Nat.factorial k := by
  classical
  let D := {p : ℕ // p ∈ S}
  let X := Fin k → D
  let T : Finset X := Finset.univ.filter
    (fun a => (∏ i : Fin k, (a i).val)=n)
  let encode : X → List ℕ :=
    fun a => List.ofFn (fun i : Fin k => (a i).val)
  have hEncode : Function.Injective encode := by
    intro a b hab
    have hEq : (fun i : Fin k => (a i).val) =
                 (fun i : Fin k => (b i).val) :=
      List.ofFn_injective hab
    funext i
    exact Subtype.ext (congrFun hEq i)
  have hImage :
      T.image encode ⊆ (n.primeFactorsList.permutations.toFinset) := by
    intro l hl
    obtain ⟨a,ha,hlEq⟩ := Finset.mem_image.mp hl
    subst l
    have htuple : (∏ i : Fin k, (a i).val)=n :=
      (Finset.mem_filter.mp ha).2
    have hperm := source_original_ordered_prime_product_perm434
      S k n hp a htuple
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr hperm)
  by_cases hT : T.Nonempty
  · obtain ⟨a,ha⟩ := hT
    have hLen : n.primeFactorsList.length = k := by
      have hh := (source_original_ordered_prime_product_perm434
        S k n hp a (Finset.mem_filter.mp ha).2).length_eq
      simpa only [List.length_ofFn] using hh.symm
    calc
      _ = T.card := rfl
      _ = (T.image encode).card :=
        (Finset.card_image_of_injective T hEncode).symm
      _ ≤ n.primeFactorsList.permutations.toFinset.card :=
        Finset.card_le_card hImage
      _ ≤ n.primeFactorsList.permutations.length :=
        List.toFinset_card_le _
      _ = (n.primeFactorsList.length).factorial :=
        List.length_permutations _
      _ = k.factorial := by rw [hLen]
  · have hEmpty : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ k.factorial
    rw [hEmpty]
    exact Nat.zero_le _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPureMellinProductTwist -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The exact Mellin phase in the source03 physical Fourier
residual, not a logarithmic phase surrogate. This is
unit-modulus even at n=0 (where Real.log 0=0). -/
noncomputable def sourceOriginalPureMellinPhase434
    (ζ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((ζ*Real.log (n:ℝ)):ℂ))

theorem source_original_pure_mellin_phase_norm_one434
    (ζ : ℝ) (n : ℕ) :
    ‖sourceOriginalPureMellinPhase434 ζ n‖ = 1 := by
  unfold sourceOriginalPureMellinPhase434
  simpa only [Complex.ofReal_mul] using
    (Complex.norm_exp_I_mul_ofReal (ζ*Real.log (n:ℝ)))

/-- Mellin phase separates EXACTLY across the two genuine
positive integer products D_A and D_B (or X_A and X_B).
The positivity assumption is essential for Real.log_mul. -/
theorem source_original_pure_mellin_product_factor434
    (ζ : ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    sourceOriginalPureMellinPhase434 ζ (a*b) =
      sourceOriginalPureMellinPhase434 ζ a *
      sourceOriginalPureMellinPhase434 ζ b := by
  have haR : (a:ℝ) ≠ 0 := by
    exact_mod_cast ha.ne'
  have hbR : (b:ℝ) ≠ 0 := by
    exact_mod_cast hb.ne'
  unfold sourceOriginalPureMellinPhase434
  rw [Nat.cast_mul, Real.log_mul haR hbR]
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The EXACT original weighted L2 test energy is invariant
under multiplication by the unit-modulus Mellin phase,
for ARBITRARY complex mark-sensitive endpoint tests and
ARBITRARY original real harmonic weights (no unit bound). -/
theorem source_original_pure_mellin_weighted_energy_eq434
    {X : Type} [Fintype X]
    (mu : X → ℝ) (product : X → ℕ)
    (ζ : ℝ) (f : X → ℂ) :
    (∑ x : X, mu x *
      ‖sourceOriginalPureMellinPhase434 ζ (product x)*f x‖^2) =
    (∑ x : X, mu x*‖f x‖^2) := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  rw [norm_mul, source_original_pure_mellin_phase_norm_one434]
  simp only [one_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalFourierPushforward -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Push a finite Fourier expansion from arbitrary original modes
onto a (possibly NONINJECTIVE) finite family of target modes.
Distinct imprimitive characters can share a primitive conductor:
the push-forward collects their coefficients EXACTLY. -/
noncomputable def sourceOriginalFiniteFourierPushforward434
    {C D : Type} [Fintype C] [Fintype D]
    (φ : C → D) (a : C → ℂ) (d : D) : ℂ :=
  ∑ c : C, if φ c = d then a c else 0

theorem source_original_finite_fourier_pushforward_exact434
    {C D : Type} [Fintype C] [Fintype D]
    (φ : C → D) (a : C → ℂ) (b : D → ℂ) :
    (∑ d : D, sourceOriginalFiniteFourierPushforward434 φ a d * b d) =
      ∑ c : C, a c * b (φ c) := by
  classical
  unfold sourceOriginalFiniteFourierPushforward434
  calc
    _ = ∑ d : D, ∑ c : C,
        (if φ c = d then a c else 0) * b d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_mul]
    _ = ∑ c : C, ∑ d : D,
        (if φ c = d then a c else 0) * b d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      simp

/-- Grouping characters by their actual primitive conductor
cannot increase Fourier l1 mass, even when the full-to-primitive
index map is MANY-TO-ONE. -/
theorem source_original_finite_fourier_pushforward_l1434
    {C D : Type} [Fintype C] [Fintype D]
    (φ : C → D) (a : C → ℂ) :
    (∑ d : D, ‖sourceOriginalFiniteFourierPushforward434 φ a d‖) ≤
    ∑ c : C, ‖a c‖ := by
  classical
  unfold sourceOriginalFiniteFourierPushforward434
  calc
    _ ≤ ∑ d : D, ∑ c : C,
        ‖if φ c = d then a c else 0‖ :=
      Finset.sum_le_sum (fun d hd => norm_sum_le _ _)
    _ = ∑ c : C, ∑ d : D,
        ‖if φ c = d then a c else 0‖ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      calc
        _ = ∑ d : D, (if φ c = d then ‖a c‖ else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          split_ifs <;> simp
        _ = ‖a c‖ := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePrimeBlockReciprocal -/

section

set_option maxHeartbeats 6000000
open scoped BigOperators
namespace Green64Analytic.SourceBlockSieve

/-!
Source-adapted exact prime reciprocal block bound from the verified
ArithmeticSieve.lean of task-1657e7da76e0, lines ~1484-1564.
No hidden analytical PNT assumption.
-/

theorem source_quadratic_prime_reciprocal_le_four : ∀ (w : ℝ) (s : Finset ℕ), 1 < w →
  (∀ p ∈ s, Nat.Prime p ∧ w < (p:ℝ) ∧ (p:ℝ) ≤ w^2) →
  (∑ p ∈ s, (p:ℝ)⁻¹) ≤ 4 := by
  have logsum : ∀ (N : ℕ) (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
(∑ p ∈ s, ((N/p:ℕ):ℝ)*Real.log p) ≤ (N:ℝ)*Real.log N := by
    intro N s hp
    have hlocal : ∀ n ∈ Finset.Ioc 0 N, (∑ p ∈ s.filter (fun p => p ∣ n), Real.log (p:ℝ)) ≤ Real.log N := by
      intro n hn
      have hn0 := (Finset.mem_Ioc.mp hn).1
      let t := s.filter (fun p => p ∣ n)
      have ht : ∀ p ∈ t, Nat.Prime p := fun p hpt => hp p (Finset.mem_filter.mp hpt).1
      have hd : (∏ p ∈ t, p) ∣ n := by
        apply Finset.prod_dvd_of_isRelPrime
        · intro p hpt q hqt hpq
          exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (ht p hpt) (ht q hqt)).mpr hpq)
        · intro p hpt
          exact (Finset.mem_filter.mp hpt).2
      have hprodpos : (0:ℝ) < ∏ p ∈ t, (p:ℝ) := Finset.prod_pos (fun p hpt => by exact_mod_cast (ht p hpt).pos)
      have hprodle : (∏ p ∈ t, (p:ℝ)) ≤ N := by
        rw [← Nat.cast_prod]
        exact_mod_cast (Nat.le_of_dvd hn0 hd).trans (Finset.mem_Ioc.mp hn).2
      calc
        _ = Real.log (∏ p ∈ t, (p:ℝ)) := (Real.log_prod (fun p hpt => by exact_mod_cast (ht p hpt).ne_zero)).symm
        _ ≤ Real.log N := Real.log_le_log hprodpos hprodle
    have hswap : (∑ p ∈ s, ((N/p:ℕ):ℝ)*Real.log p) =
        ∑ n ∈ Finset.Ioc 0 N, ∑ p ∈ s.filter (fun p => p ∣ n), Real.log (p:ℝ) := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hps
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    rw [hswap]
    calc
      _ ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log (N:ℝ) := Finset.sum_le_sum hlocal
      _ = _ := by simp
  intro w s hw hp
  by_cases hs : s = ∅
  · simp [hs]
  have hw0 : 0 < w := by linarith
  have hlw : 0 < Real.log w := Real.log_pos hw
  let N := ⌊w^2⌋₊
  have hpN : ∀ p ∈ s, p ≤ N := by
    intro p hps
    by_contra hh
    have hn : N+1 ≤ p := by omega
    have hnR : (N:ℝ)+1 ≤ p := by exact_mod_cast hn
    have hh := Nat.lt_floor_add_one (w^2)
    have hpu := (hp p hps).2.2
    change w^2 < (N:ℝ)+1 at hh
    linarith
  obtain ⟨p0,hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  have hN : 0 < N := lt_of_lt_of_le (hp p0 hp0).1.pos (hpN p0 hp0)
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hNlog : Real.log (N:ℝ) ≤ 2*Real.log w := by
    have hnle : (N:ℝ) ≤ w^2 := Nat.floor_le (sq_nonneg w)
    have he := Real.log_le_log hNR hnle
    simpa [Real.log_pow] using he
  have hweight : ∀ p ∈ s, (N:ℝ)*Real.log w*(p:ℝ)⁻¹ ≤ 2*((N/p:ℕ):ℝ)*Real.log p := by
    intro p hps
    have hpp := (hp p hps).1
    have hpR : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hq : 1 ≤ N/p := Nat.div_pos (hpN p hps) hpp.pos
    have hmod := Nat.mod_lt N hpp.pos
    have hdecomp := Nat.mod_add_div N p
    have hpn : p ≤ p*(N/p) := by simpa using Nat.mul_le_mul_left p hq
    have hNbound : N ≤ 2*(N/p)*p := by nlinarith
    have hNboundR : (N:ℝ) ≤ 2*((N/p:ℕ):ℝ)*(p:ℝ) := by exact_mod_cast hNbound
    have hdiv : (N:ℝ)/(p:ℝ) ≤ 2*((N/p:ℕ):ℝ) := (div_le_iff₀ hpR).mpr hNboundR
    have hlp : Real.log w ≤ Real.log (p:ℝ) := Real.log_le_log hw0 (hp p hps).2.1.le
    calc
      _ = ((N:ℝ)/(p:ℝ))*Real.log w := by ring
      _ ≤ ((N:ℝ)/(p:ℝ))*Real.log (p:ℝ) := mul_le_mul_of_nonneg_left hlp (div_nonneg hNR.le hpR.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right hdiv (hlw.le.trans hlp)
  have hsum := Finset.sum_le_sum hweight
  simp only [← Finset.mul_sum, mul_assoc] at hsum
  have hlog := logsum N s (fun p hps => (hp p hps).1)
  have hfin : (N:ℝ)*Real.log w*(∑ p ∈ s, (p:ℝ)⁻¹) ≤ (N:ℝ)*Real.log w*4 := by
    have hh := mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ) ≤ 2)
    have hh2 := mul_le_mul_of_nonneg_left hNlog (by positivity : (0:ℝ) ≤ 2*(N:ℝ))
    nlinarith
  exact le_of_mul_le_mul_left hfin (mul_pos hNR hlw)

end Green64Analytic.SourceBlockSieve

end

/-! ## SourcePrimeLogBandDefinition -/

section

namespace Green64Analytic.SourceBlockSieve

/-- True natural-prime source cell, in the source logarithmic coordinates. -/
noncomputable def sourcePrimeLogBand (L u v : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp (u*L)⌋₊ ⌊Real.exp (v*L)⌋₊).filter Nat.Prime

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceQSkipPrimeFibre -/

section

open scoped BigOperators
namespace Green64Analytic.QSkipFactorial

/-- A fixed-product fibre of labelled prime slots in one prime band.
    Entries may repeat. -/
noncomputable def primeProductFibre (n : ℕ) (Q : Finset ℕ) (v : ℕ) :
    Finset (Fin n → {p : ℕ // p ∈ Q}) :=
  Finset.univ.filter (fun a => (∏ i, (a i).val) = v)

/-- Unique factorization bounds the number of labelled assignments to a
    fixed prime product by n!, even with repeated prime values. -/
theorem primeProductFibre_card_le_factorial (n : ℕ) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (v : ℕ) :
    (primeProductFibre n Q v).card ≤ n.factorial := by
  classical
  by_cases he : (primeProductFibre n Q v).Nonempty
  · obtain ⟨a₀, ha₀⟩ := he
    let S := primeProductFibre n Q v
    let tr : (Fin n → {p : ℕ // p ∈ Q}) → List ℕ :=
      fun a => List.ofFn (fun i => (a i).val)
    have hpr (a : Fin n → {p : ℕ // p ∈ Q}) :
        ∀ p ∈ tr a, Prime p := by
      intro p hp
      have hx : p ∈ List.ofFn (fun i : Fin n => (a i).val) := hp
      rcases (List.mem_ofFn.mp hx) with ⟨i, rfl⟩
      exact Nat.prime_iff.mp (hQ (a i).val (a i).property)
    have hmem : ∀ a ∈ S, tr a ∈ (tr a₀).permutations.toFinset := by
      intro a ha
      have haP : (∏ i, (a i).val) = v := (Finset.mem_filter.mp ha).2
      have h0P : (∏ i, (a₀ i).val) = v := (Finset.mem_filter.mp ha₀).2
      have hprod : (tr a).prod = (tr a₀).prod := by
        simp only [tr, List.prod_ofFn]
        exact haP.trans h0P.symm
      rw [List.mem_toFinset, List.mem_permutations]
      exact perm_of_prod_eq_prod hprod (hpr a) (hpr a₀)
    have hinj : Set.InjOn tr (↑S : Set _) := by
      intro a ha b hb hEq
      have heq : (fun i : Fin n => (a i).val) = (fun i : Fin n => (b i).val) :=
        (List.ofFn_inj).mp hEq
      funext i
      exact Subtype.ext (congrFun heq i)
    have hsubset : S.image tr ⊆ (tr a₀).permutations.toFinset := by
      intro t ht
      rcases Finset.mem_image.mp ht with ⟨a, ha, rfl⟩
      exact hmem a ha
    have hcard : S.card = (S.image tr).card :=
      (Finset.card_image_iff.mpr hinj).symm
    calc
      S.card = (S.image tr).card := hcard
      _ ≤ (tr a₀).permutations.toFinset.card := Finset.card_le_card hsubset
      _ ≤ (tr a₀).permutations.length := List.toFinset_card_le _
      _ = n.factorial := by simp [tr, List.length_permutations]
  · have hE : primeProductFibre n Q v = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp he
    simp [hE]

/-- Separate factors of an equal global product when opposite allocations
    are coprime across different bands. This keeps multiplicities. -/
theorem components_eq_of_cross_coprime {m : ℕ} (u v : Fin m → ℕ)
    (heq : (∏ g, u g) = ∏ g, v g)
    (hcop : ∀ g h, g ≠ h → Nat.Coprime (u g) (v h)) :
    ∀ g, u g = v g := by
  classical
  intro g
  have hmem : g ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
  have hcopU : Nat.Coprime (u g) (∏ h ∈ (Finset.univ : Finset (Fin m)).erase g, v h) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro h hh
    exact hcop g h (Ne.symm (Finset.ne_of_mem_erase hh))
  have hcopV : Nat.Coprime (v g) (∏ h ∈ (Finset.univ : Finset (Fin m)).erase g, u h) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro h hh
    exact (hcop h g (Finset.ne_of_mem_erase hh)).symm
  have hdU : u g ∣ ∏ h, v h := heq ▸ (Finset.dvd_prod_of_mem u hmem)
  have hdV : v g ∣ ∏ h, u h := heq.symm ▸ (Finset.dvd_prod_of_mem v hmem)
  have hsV := (Finset.prod_erase_mul (Finset.univ : Finset (Fin m)) v hmem).symm
  have hsU := (Finset.prod_erase_mul (Finset.univ : Finset (Fin m)) u hmem).symm
  exact Nat.dvd_antisymm
    (hcopU.dvd_of_dvd_mul_left (hsV ▸ hdU))
    (hcopV.dvd_of_dvd_mul_left (hsU ▸ hdV))
end Green64Analytic.QSkipFactorial

end

/-! ## SourceRealFrequencyPhases -/

section

/-!
Exact real-frequency phases used in the source Dirichlet polynomials.
We keep the logarithm, real frequency, conjugation and integer argument.
The exceptional n=0 is not used in source dyadic prime/rough intervals.
-/

namespace Green64Analytic.CorrelationMellin

noncomputable def sourcePhase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ))

theorem sourcePhase_conj_mul (n : ℕ) (t u : ℝ) :
    sourcePhase n t * star (sourcePhase n u) = sourcePhase n (t - u) := by
  unfold sourcePhase
  change Complex.exp (Complex.I * (↑(t * Real.log (n : ℝ)) : ℂ)) *
    (starRingEnd ℂ) (Complex.exp (Complex.I * (↑(u * Real.log (n : ℝ)) : ℂ))) =
      Complex.exp (Complex.I * (↑((t-u) * Real.log (n : ℝ)) : ℂ))
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem sourcePhase_norm (n : ℕ) (t : ℝ) : ‖sourcePhase n t‖ = 1 := by
  unfold sourcePhase
  rw [Complex.norm_exp]
  have him : (Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re]
    simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_self]
  rw [him, Real.exp_zero]

theorem sourcePhase_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    sourcePhase (m * n) t = sourcePhase m t * sourcePhase n t := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold sourcePhase
  rw [show (↑(m*n) : ℝ) = (m : ℝ) * (n : ℝ) by norm_cast,
    Real.log_mul hm0 hn0, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sourcePhase_add (n : ℕ) (u t : ℝ) :
    sourcePhase n (u+t) = sourcePhase n u * sourcePhase n t := by
  unfold sourcePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sourcePhase_neg (n : ℕ) (t : ℝ) :
    sourcePhase n (-t) = star (sourcePhase n t) := by
  unfold sourcePhase
  change Complex.exp (Complex.I * (↑((-t)*Real.log (n : ℝ)) : ℂ)) =
    (starRingEnd ℂ) (Complex.exp (Complex.I * (↑(t*Real.log (n : ℝ)) : ℂ)))
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

end Green64Analytic.CorrelationMellin

end

/-! ## SourceOriginalHarmonicSeparation -/

section

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 6500000

/-- Literal free-product and first-endpoint phases after Fourier separation
of psi(w/(Z*D1*D2)). The sign on D1,D2 and the factor 2*pi are explicit. -/
noncomputable def sourceComparisonLogFourierPhase434 (Z : ℝ) (w da db : ℕ)
    (a1 a2 t : ℝ) : ℂ :=
  Complex.exp (Complex.I*(((-2*Real.pi*t)*Real.log Z:ℝ):ℂ)) *
    sourcePhase da (-(a1+a2+2*Real.pi*t)) *
    sourcePhase db (-(a1+a2+2*Real.pi*t)) * sourcePhase w (a1+2*Real.pi*t)

theorem source_original_comparison_log_phase434 (Z : ℝ) (w da db : ℕ)
    (a1 a2 t : ℝ) (hZ : 0 < Z) (hw : 0 < w) (ha : 0 < da) (hb : 0 < db) :
    Complex.exp (((2*Real.pi*t*Real.log ((w:ℝ)/(Z*(da:ℝ)*(db:ℝ)))):ℂ)*Complex.I) *
      sourcePhase w a1 * sourcePhase (da*db) (-(a1+a2)) =
      sourceComparisonLogFourierPhase434 Z w da db a1 a2 t := by
  have hwa : (w:ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have haa : (da:ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbb : (db:ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hLog : Real.log ((w:ℝ)/(Z*(da:ℝ)*(db:ℝ))) =
      Real.log (w:ℝ)-Real.log Z-Real.log (da:ℝ)-Real.log (db:ℝ) := by
    rw [Real.log_div hwa (by positivity),Real.log_mul (by positivity) hbb,
      Real.log_mul hZ.ne' haa]
    ring
  rw [sourcePhase_mul da db ha hb]
  unfold sourceComparisonLogFourierPhase434 sourcePhase
  rw [hLog]
  simp only [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem source_original_schwartz_log_inversion434 (phi : SchwartzMap ℝ ℂ) (r : ℝ) :
    phi r = ∫ t : ℝ,
      Complex.exp (((2*Real.pi*t*r:ℝ):ℂ)*Complex.I) * (𝓕 phi) t := by
  calc
    phi r = (𝓕⁻ (𝓕 phi)) r := by rw [FourierTransform.fourierInv_fourier_eq]
    _ = _ := by
      rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq']
      simp only [Real.inner_apply,smul_eq_mul,mul_assoc]

/-- Literal harmonic weight Fourier separation. The factor 1/Y is kept
outside and Y/w inside the endpoint: no physical-scale factor is lost.
Here phi is the Schwartz logarithmic cutoff, i.e. psi(exp r) = phi r. -/
theorem source_original_harmonic_fourier_identity434
    (phi : SchwartzMap ℝ ℂ) (Z Y : ℝ) (w wp da db : ℕ) (a1 a2 : ℝ)
    (hZ : 0 < Z) (hY : 0 < Y) (hw : 0 < w) (ha : 0 < da) (hb : 0 < db) :
    phi (Real.log ((w:ℝ)/(Z*(da:ℝ)*(db:ℝ)))) * (w:ℂ)⁻¹ *
      sourcePhase w a1 * sourcePhase wp a2 * sourcePhase (da*db) (-(a1+a2)) =
    (Y:ℂ)⁻¹ * ∫ t : ℝ, (𝓕 phi) t *
      sourceComparisonLogFourierPhase434 Z w da db a1 a2 t *
        ((Y:ℂ)/(w:ℂ)) * sourcePhase wp a2 := by
  have hYn : (Y:ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hwn : (w:ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  rw [source_original_schwartz_log_inversion434 phi]
  simp_rw [←integral_mul_const]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [←source_original_comparison_log_phase434 Z w da db a1 a2 t hZ hw ha hb]
  push_cast
  field_simp [hYn,hwn] <;> ring_nf

theorem source_original_log_fourier_phase_norm434 (Z : ℝ) (w da db : ℕ) (a1 a2 t : ℝ) :
    ‖sourceComparisonLogFourierPhase434 Z w da db a1 a2 t‖ = 1 := by
  simp only [sourceComparisonLogFourierPhase434,norm_mul,sourcePhase_norm,mul_one,
    Complex.norm_exp,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,sub_self,Real.exp_zero]

/-- The actual harmonic Fourier integrand is integrable; no integrability
premise has been introduced to justify changing the order of summation. -/
theorem source_original_harmonic_fourier_integrable434
    (phi : SchwartzMap ℝ ℂ) (Z Y : ℝ) (w wp da db : ℕ) (a1 a2 : ℝ) :
    Integrable (fun t : ℝ => (𝓕 phi) t *
      sourceComparisonLogFourierPhase434 Z w da db a1 a2 t *
        ((Y:ℂ)/(w:ℂ))*sourcePhase wp a2) := by
  have hCont : Continuous (sourceComparisonLogFourierPhase434 Z w da db a1 a2) := by
    unfold sourceComparisonLogFourierPhase434 sourcePhase
    fun_prop
  have hBound : ∀ᵐ t : ℝ ∂volume,
      ‖sourceComparisonLogFourierPhase434 Z w da db a1 a2 t‖ ≤ (1:ℝ) := by
    filter_upwards with t
    exact (source_original_log_fourier_phase_norm434 Z w da db a1 a2 t).le
  exact (((𝓕 phi).integrable.mul_bdd hCont.aestronglyMeasurable hBound).mul_const
    ((Y:ℂ)/(w:ℂ))).mul_const (sourcePhase wp a2)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSeparatedHarmonic -/

section

/-! Reciprocal-gap harmonic estimate on arbitrary 1-separated real points,
not only an integer time grid. The injective floor map is the key. -/
namespace Green64Analytic.CorrelationMellin

theorem source_separated_positive_reciprocal
    (S : Finset ℝ) (B : ℝ)
    (hB : 1 ≤ B)
    (hPos : ∀ x ∈ S, 1 ≤ x)
    (hBound : ∀ x ∈ S, x ≤ B)
    (hSep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) :
    (∑ x ∈ S, x⁻¹) ≤ 1 + Real.log B := by
  classical
  let N : ℕ := ⌊B⌋₊
  have hN : 1 ≤ N :=
    (Nat.le_floor_iff' (by decide : (1:ℕ) ≠ 0)).2 (by exact_mod_cast hB)
  have hFloors (x : ℝ) (hx : x ∈ S) :
      1 ≤ (⌊x⌋₊:ℕ) ∧ ⌊x⌋₊ ≤ N := by
    exact ⟨(Nat.le_floor_iff' (by decide : (1:ℕ) ≠ 0)).2 (by exact_mod_cast hPos x hx),
      Nat.floor_mono (hBound x hx)⟩
  have hInj : Set.InjOn (fun x : ℝ => ⌊x⌋₊) S := by
    intro x hx y hy hEq
    by_contra hne
    have hGap := hSep x hx y hy hne
    have hxlow := Nat.floor_le (by linarith [hPos x hx] : (0:ℝ) ≤ x)
    have hylow := Nat.floor_le (by linarith [hPos y hy] : (0:ℝ) ≤ y)
    have hxhigh := Nat.lt_floor_add_one x
    have hyhigh := Nat.lt_floor_add_one y
    change ⌊x⌋₊ = ⌊y⌋₊ at hEq
    rw [hEq] at hxlow hxhigh
    have hNear : |x-y| < 1 :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    exact (not_lt_of_ge hGap) hNear
  have hSub : S.image (fun x : ℝ => ⌊x⌋₊) ⊆
      Finset.Icc 1 N := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr (hFloors x hx)
  have hWeight (x : ℝ) (hx : x ∈ S) :
      x⁻¹ ≤ (((⌊x⌋₊:ℕ):ℝ))⁻¹ := by
    have hFlo := (hFloors x hx).1
    have hfp : (0:ℝ) < (⌊x⌋₊:ℕ) := by exact_mod_cast hFlo
    exact inv_anti₀ hfp (Nat.floor_le (by linarith [hPos x hx]))
  have hNonneg : ∀ k ∈ Finset.Icc 1 N,
      k ∉ S.image (fun x : ℝ => ⌊x⌋₊) →
      (0:ℝ) ≤ (k:ℝ)⁻¹ := by
    intro k _ _
    positivity
  have hNHarmonic : ∑ k ∈ Finset.Icc 1 N, ((k:ℝ))⁻¹ ≤
      1 + Real.log B := by
    have hcast : ∑ k ∈ Finset.Icc 1 N, ((k:ℝ))⁻¹ =
        ((harmonic N : ℚ) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum,
        Rat.cast_inv, Rat.cast_natCast]
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    have hNle : (N:ℝ) ≤ B :=
      Nat.floor_le (by linarith [hB])
    have hlog := Real.log_le_log hNpos hNle
    rw [hcast]
    exact (harmonic_le_one_add_log N).trans (by linarith)
  calc
    ∑ x ∈ S, x⁻¹ ≤
        ∑ x ∈ S, (((⌊x⌋₊:ℕ):ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      exact hWeight
    _ = ∑ k ∈ S.image (fun x : ℝ => ⌊x⌋₊), (k:ℝ)⁻¹ := by
      rw [Finset.sum_image hInj]
    _ ≤ ∑ k ∈ Finset.Icc 1 N, (k:ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub hNonneg
    _ ≤ 1 + Real.log B := hNHarmonic
end Green64Analytic.CorrelationMellin

end

/-! ## SourceTau6PrimePowerBinomial -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 850000

/-- The exact local prime-power numerical inequality behind
τ(p^e)^6 ≤ d₆₄(p^e). This is a universal arithmetic statement:
(e+1)^6 ≤ C(e+63,63), including e=0. -/
theorem source_tau6_prime_power_binomial434 (e : ℕ) :
    (e+1)^6 ≤ Nat.choose (e+63) 63 := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    have hPolyEq :
        (e+64)*(e+1)^5 = (e+2)^6 +
          (57*e^5+270*e^4+490*e^3+405*e^2+129*e) := by ring
    have hPoly : (e+2)^6 ≤ (e+64)*(e+1)^5 := by
      rw [hPolyEq]
      exact Nat.le_add_right _ _
    have hChoose : Nat.choose (e+63) 63 * (e+64) =
        Nat.choose (e+64) 63 * (e+1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_mul_succ_eq (e+63) 63)
    have hStep : (e+2)^6*(e+1) ≤
        Nat.choose (e+64) 63 * (e+1) := by
      calc
        _ ≤ ((e+64)*(e+1)^5)*(e+1) :=
          Nat.mul_le_mul_right (e+1) hPoly
        _ = (e+64)*(e+1)^6 := by ring
        _ ≤ (e+64)*Nat.choose (e+63) 63 :=
          Nat.mul_le_mul_left _ ih
        _ = Nat.choose (e+64) 63 * (e+1) := by
          rw [mul_comm, hChoose]
    have hCancel : (e+2)^6 ≤ Nat.choose (e+64) 63 :=
      Nat.le_of_mul_le_mul_right hStep (by omega)
    convert hCancel using 1 <;> omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceTau6PrimePowerActual -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- The ACTUAL Mathlib divisor count sigma₀ at p^e obeys
tau(p^e)^6 ≤ binomial(e+63,63), with no squarefreeness assumption.
Only local prime powers: the multiplicative passage to d64(n)
requires a separate checked convolution-of-64 factors bridge. -/
theorem source_tau6_actual_divisor_prime_power434
    (p e : ℕ) (hp : Nat.Prime p) :
    (ArithmeticFunction.sigma 0 (p^e))^6 ≤
      Nat.choose (e+63) 63 := by
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  exact source_tau6_prime_power_binomial434 e
end Green64Analytic.CorrelationSquare

end

/-! ## SourceUniformFourierTail -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap BigOperators
set_option maxHeartbeats 4000000
namespace Green64Analytic.CorrelationMellin

/-- Native integration-by-parts decay, with all constants controlled by the
first N derivative L1 norms. The cutoff is NOT fixed before the scale. -/
theorem source_uniform_fourier_decay (f : 𝓢(ℝ,ℂ)) (N : ℕ) (xi : ℝ) :
    |xi|^N * ‖(𝓕 f) xi‖ ≤
      2^N * ∑ j ∈ Finset.range (N+1),
        ∫ u : ℝ, ‖iteratedFDeriv ℝ j (f : ℝ → ℂ) u‖ := by
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K := (0 : ℕ∞)) (N := (N : ℕ∞)) (f.smooth N)
    (fun k n hk hn => f.integrable_pow_mul_iteratedFDeriv volume k n)
    (k := 0) (n := N) (by simp) (by simp) xi
  simpa only [SchwartzMap.fourier_coe, Real.norm_eq_abs,
    norm_iteratedFDeriv_zero, pow_zero, Nat.cast_zero, zero_mul,
    zero_add, mul_zero, zero_add, one_mul, Finset.range_one, Finset.sum_product,
    Finset.sum_singleton] using h

/-- Integrating the native decay on each half-line gives an explicit,
uniform family bound. B is a derivative budget, not a tail assumption. -/
theorem source_uniform_fourier_tail_from_decay
    (f : 𝓢(ℝ,ℂ)) (N : ℕ) (R B : ℝ) (hN : 2 ≤ N)
    (hR : 0 < R) (hB : 0 ≤ B)
    (hDecay : ∀ xi : ℝ, |xi|^N * ‖(𝓕 f) xi‖ ≤ B) :
    (∫ xi in {xi : ℝ | R ≤ |xi|}, ‖(𝓕 f) xi‖) ≤
      2 * B * R^(-(N:ℝ)+1) / ((N:ℝ)-1) := by
  have hExp : -(N:ℝ) < -1 := by
    have hn : (1:ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    linarith
  have hG : Integrable (fun xi : ℝ => ‖(𝓕 f) xi‖) := (𝓕 f).integrable.norm
  have hWeight := integrableOn_Ioi_rpow_of_lt hExp hR
  have hPoint (xi : ℝ) (hxi : xi ∈ Set.Ioi R) (sgn : ℝ)
      (hsgn : |sgn| = 1) :
      ‖(𝓕 f) (sgn*xi)‖ ≤ B * xi^(-(N:ℝ)) := by
    have hx : 0 < xi := hR.trans hxi
    have h := hDecay (sgn*xi)
    rw [abs_mul, hsgn, one_mul, abs_of_pos hx] at h
    rw [Real.rpow_neg hx.le, Real.rpow_natCast]
    exact (le_div_iff₀ (pow_pos hx N)).mpr (by simpa [mul_comm,div_eq_mul_inv] using h)
  have hPlus : (∫ xi in Set.Ioi R, ‖(𝓕 f) xi‖) ≤
      B * (-(R^(-(N:ℝ)+1)) / (-(N:ℝ)+1)) := by
    calc
      _ ≤ ∫ xi in Set.Ioi R, B * xi^(-(N:ℝ)) :=
        setIntegral_mono_on hG.integrableOn (hWeight.const_mul B)
          measurableSet_Ioi (fun xi hxi => by simpa using hPoint xi hxi 1 (by norm_num))
      _ = _ := by rw [integral_const_mul, integral_Ioi_rpow_of_lt hExp hR]
  have hMinus : (∫ xi in Set.Iic (-R), ‖(𝓕 f) xi‖) ≤
      B * (-(R^(-(N:ℝ)+1)) / (-(N:ℝ)+1)) := by
    have hNeg := integral_comp_neg_Ioi (E := ℝ) R (fun xi : ℝ => ‖(𝓕 f) xi‖)
    rw [← hNeg]
    calc
      _ ≤ ∫ xi in Set.Ioi R, B * xi^(-(N:ℝ)) :=
        setIntegral_mono_on hG.comp_neg.integrableOn (hWeight.const_mul B)
          measurableSet_Ioi (fun xi hxi => by simpa using hPoint xi hxi (-1) (by norm_num))
      _ = _ := by rw [integral_const_mul, integral_Ioi_rpow_of_lt hExp hR]
  have hSet : {xi : ℝ | R ≤ |xi|} = Set.Iic (-R) ∪ Set.Ici R := by
    ext xi
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  rw [hSet, setIntegral_union (by
    apply Set.disjoint_left.mpr
    intro xi hx hy
    simp only [Set.mem_Iic,Set.mem_Ici] at hx hy
    linarith) measurableSet_Ici hG.integrableOn hG.integrableOn,
    integral_Ici_eq_integral_Ioi]
  calc
    _ ≤ B * (-(R^(-(N:ℝ)+1)) / (-(N:ℝ)+1)) +
        B * (-(R^(-(N:ℝ)+1)) / (-(N:ℝ)+1)) := add_le_add hMinus hPlus
    _ = _ := by
      rw [show -(N:ℝ)+1 = -((N:ℝ)-1) by ring, neg_div_neg_eq]
      ring
end Green64Analytic.CorrelationMellin

end

/-! ## TruncatedPrimeGeometry -/

section

set_option maxHeartbeats 1400000
namespace Green64Analytic.LastPrimeErrors

/-- A FIXED gap δ from the moving prime-product boundary guarantees
the last prime is in a PNT2 range. Source scale x=exp L, z=exp(b L).
No squarefree or distinct-prime restriction appears. -/
theorem truncated_prefix_last_prime_room
    (b δ L q : ℝ)
    (hb : 0 ≤ b) (hδ : 0 < δ) (hL : 0 < L) (hq : 0 < q)
    (hcap : q ≤ Real.exp ((1-b-δ)*L)) :
    (b+δ)*L ≤ Real.log (Real.exp L/q) ∧
      Real.exp (b*L) ≤ Real.exp L/q := by
  have _ := hb
  have hexp :
      Real.exp ((1-b-δ)*L)*Real.exp ((b+δ)*L) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlast : Real.exp ((b+δ)*L) ≤ Real.exp L/q := by
    apply (le_div_iff₀ hq).2
    calc
      Real.exp ((b+δ)*L)*q = q*Real.exp ((b+δ)*L) := by ring
      _ ≤ Real.exp ((1-b-δ)*L)*Real.exp ((b+δ)*L) :=
        mul_le_mul_of_nonneg_right hcap (Real.exp_pos _).le
      _ = Real.exp L := hexp
  have hlg : (b+δ)*L ≤ Real.log (Real.exp L/q) := by
    have hh := Real.log_le_log (Real.exp_pos _) hlast
    simpa only [Real.log_exp] using hh
  have hbδ : b*L ≤ (b+δ)*L := by nlinarith
  have hbroom : Real.exp (b*L) ≤ Real.exp L/q :=
    (Real.exp_le_exp.mpr hbδ).trans hlast
  exact ⟨hlg,hbroom⟩

/-- Canonical elementary positive-scale predicates; all derived
from fixed b,δ and L, before any choice of large x. -/
theorem truncated_prefix_error_inputs
    (b δ L : ℝ)
    (hb : 0 ≤ b) (hδ : 0 < δ) (hL : 0 < L) :
    0 < (b+δ)*L ∧ 0 ≤ Real.exp ((1-b-δ)*L) ∧
      0 ≤ Real.exp (b*L)+1 := by
  constructor
  · have hbd : 0 < b+δ := by linarith
    exact mul_pos hbd hL
  constructor
  · exact (Real.exp_pos _).le
  · have he := Real.exp_pos (b*L)
    linarith

end Green64Analytic.LastPrimeErrors

end

/-! ## code.PrimeSupportLog -/

section

set_option maxHeartbeats 0
namespace Green64Analytic.CorrelationSquare
open scoped BigOperators

/-- Distinct prime divisor count uses an actual product of prime powers,
    rather than a loose bound by the integer n. -/
theorem two_pow_primeFactors_card_le (n : ℕ) (hn : 0 < n) :
    2^(n.primeFactors.card) ≤ n := by
  have h2 : 2^(n.primeFactors.card) ≤
      ∏ p ∈ n.primeFactors, p := by
    calc
      _ = ∏ p ∈ n.primeFactors, (2:ℕ) := by simp
      _ ≤ ∏ p ∈ n.primeFactors, p := by
        apply Finset.prod_le_prod
        intro p hp
        exact (Nat.mem_primeFactors.mp hp).1.two_le
  have hmult : (∏ p ∈ n.primeFactors, p) ≤ n := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors, p^(n.factorization p) := by
        apply Finset.prod_le_prod
        intro p hp
        have h := Nat.mem_primeFactors.mp hp
        have hm : 1 ≤ n.factorization p :=
          Nat.Prime.factorization_pos_of_dvd h.1 hn.ne' h.2.1
        have hpow := Nat.pow_le_pow_right h.1.pos hm
        simpa using hpow
      _ = n := (Nat.prod_primeFactors_pow_factorization hn.ne').symm
  exact h2.trans hmult



/-- Every distinct prime divisor costs at least log(2) of the integer size. -/
theorem smallPrimeSupport_card_log_le (S : Finset ℕ) (n : ℕ)
    (hn : 0 < n) (hS : ∀ p ∈ S, p.Prime) :
    ((S.filter (fun p => p ∣ n)).card : ℝ) * Real.log 2 ≤
      Real.log (n:ℝ) := by
  have hsub : S.filter (fun p => p ∣ n) ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hpS,hpn⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hS p hpS,hpn,hn.ne'⟩
  have hc := Finset.card_le_card hsub
  have hp : 2^((S.filter (fun p => p ∣ n)).card) ≤ n :=
    (Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hc).trans
       (two_pow_primeFactors_card_le n hn)
  have hpR : (2:ℝ)^((S.filter (fun p => p ∣ n)).card) ≤ (n:ℝ) :=
    by exact_mod_cast hp
  have hlog := Real.log_le_log
    (by positivity : 0 < (2:ℝ)^((S.filter (fun p => p ∣ n)).card)) hpR
  rw [Real.log_pow] at hlog
  exact hlog
end Green64Analytic.CorrelationSquare

end

