module

public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part002

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / GaussSum / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets -/

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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar

section
variable {F : Type*} [Field F] [Fintype F]

theorem bracket_eq_zero_iff (χ : MulChar F ℂ) (j : ℕ) (hj4 : j ≠ 4) (x : F) :
    bracket χ j x = 0 ↔ x = 0 := by
  have hr : (rootCard F : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos))
  by_cases hj0 : j = 0
  · simp only [bracket, ite_eq_right hj4, ite_eq_left hj0, mul_eq_zero, hr, false_or,
      MulChar.apply_eq_zero_iff, isUnit_iff_ne_zero, not_not]
  · simp only [bracket, ite_eq_right hj4, ite_eq_right hj0, MulChar.apply_eq_zero_iff,
      isUnit_iff_ne_zero, not_not]

theorem norm_bracket_nonexceptional_le_one (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) : ‖bracket χ j x‖ ≤ 1 := by
  rw [norm_bracket_nonexceptional χ j hj4 hj0]
  split_ifs <;> norm_num

theorem norm_bracket_zero_le (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ ≤ (rootCard F)⁻¹ := by
  rw [norm_bracket_zero]
  split_ifs <;> simp only [mul_zero, mul_one, le_refl]
  exact inv_nonneg.mpr rootCard_pos.le

open ActualEisensteinCubic
noncomputable local instance quotientFieldBounds (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeBounds (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_A5_norm_cases (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    ‖activeRow (canonicalSextic P hgood) ψ j σ ε x‖ =
      if j = 4 then
        (if x = 0 then ((Fintype.card (O ⧸ P) : ℝ) - 1) / rootCard (O ⧸ P)
         else (rootCard (O ⧸ P))⁻¹)
      else if j = 0 then (rootCard (O ⧸ P))⁻¹ * (if x = 0 then 0 else 1)
      else if x = 0 then 0 else 1 := by
  rw [canonical_A5_norm_eq_bracket P hgood hchar ψ hψ j hj6 σ ε x]
  by_cases hj4 : j = 4
  · subst j
    simp only [↓reduceIte]
    by_cases hx : x = 0
    · subst x
      simp only [↓reduceIte]
      exact norm_bracket_four_zero _
    · rw [ite_eq_right hx]
      exact norm_bracket_four_nonzero _ x hx
  · rw [ite_eq_right hj4]
    by_cases hj0 : j = 0
    · subst j
      simp only [↓reduceIte]
      exact norm_bracket_zero _ x
    · rw [ite_eq_right hj0]
      exact norm_bracket_nonexceptional _ j hj4 hj0 x

theorem actual_trace_A5_normalized (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ Ideal.span {p})ˣ) (x : O ⧸ Ideal.span {p}) :
    let χ := canonicalSextic (Ideal.span {p}) hgood
    let ψ := ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    activeRow χ ψ j σ ε x = ((χ⁻¹) ^ 2) σ * phase χ ψ j ε * bracket χ j x := by
  exact canonical_A5_normalized (Ideal.span {p}) hgood hchar _
    (PrimitiveTrace.eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp) j hj6 σ ε x

theorem actual_bracket_four_divisibility_split (p : O) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (n b : O) :
    bracket (canonicalSextic (Ideal.span {p}) hgood) 4 (Ideal.Quotient.mk (Ideal.span {p}) (n * b ^ 3)) =
      -(rootCard (O ⧸ Ideal.span {p}) : ℂ)⁻¹ +
      (rootCard (O ⧸ Ideal.span {p}) : ℂ) * (if p ∣ n then 1 else 0) +
      (rootCard (O ⧸ Ideal.span {p}) : ℂ) * (if ¬p ∣ n ∧ p ∣ b then 1 else 0) := by
  simpa only [Ideal.mem_span_singleton] using canonical_bracket_four_cube_split (Ideal.span {p}) hgood n b

theorem actual_bracket_zero_iff (p : O) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (j : ℕ) (hj4 : j ≠ 4) (n : O) :
    bracket (canonicalSextic (Ideal.span {p}) hgood) j (Ideal.Quotient.mk (Ideal.span {p}) n) = 0 ↔ p ∣ n := by
  rw [bracket_eq_zero_iff _ j hj4, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem rootCard_span (p : O) [(Ideal.span {p}).IsMaximal] :
    rootCard (O ⧸ Ideal.span {p}) = ‖ConcreteTraceCRT.eisEmbedding p‖ := by
  rw [rootCard, ← Nat.card_eq_fintype_card]
  change Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) = _
  rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

end

variable {F : Type*} [Field F] [Fintype F]

def zeroFourierCoefficient (χ : MulChar F ℂ) (j : ℕ) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ t : F, (χ ^ j) t

theorem zeroFourierCoefficient_zero (χ : MulChar F ℂ) :
    zeroFourierCoefficient χ 0 = 1 - (Fintype.card F : ℂ)⁻¹ := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  have hq0 : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  rw [zeroFourierCoefficient, pow_zero, MulChar.sum_one_eq_card_units, Fintype.card_units,
    Nat.cast_sub hq, Nat.cast_one]
  field_simp

theorem zeroFourierCoefficient_nontrivial (χ : MulChar F ℂ) (j : ℕ) (hj : χ ^ j ≠ 1) :
    zeroFourierCoefficient χ j = 0 := by
  rw [zeroFourierCoefficient, MulChar.sum_eq_zero_of_ne_one hj, mul_zero]

theorem zeroFourierCoefficient_zero_norm_le_one (χ : MulChar F ℂ) :
    ‖zeroFourierCoefficient χ 0‖ ≤ 1 := by
  rw [zeroFourierCoefficient_zero]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hqpos : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le zero_lt_one hq
  have hinv : (Fintype.card F : ℝ)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ hqpos).mpr
    exact hq
  have hnonneg : 0 ≤ 1 - (Fintype.card F : ℝ)⁻¹ := sub_nonneg.mpr hinv
  have heq : (1 : ℂ) - (Fintype.card F : ℂ)⁻¹ = ((1 - (Fintype.card F : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [heq, Complex.norm_real, Real.norm_of_nonneg hnonneg]
  exact sub_le_self _ (inv_nonneg.mpr hqpos.le)

open ActualEisensteinCubic
noncomputable local instance quotientFieldInactive (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeInactive (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_zeroFourierCoefficient (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) (j : ℕ) (hj6 : j < 6) :
    zeroFourierCoefficient (canonicalSextic P hgood) j =
      if j = 0 then 1 - (Fintype.card (O ⧸ P) : ℂ)⁻¹ else 0 := by
  by_cases hj : j = 0
  · subst j
    simpa using zeroFourierCoefficient_zero (canonicalSextic P hgood)
  · rw [ite_eq_right hj]
    exact zeroFourierCoefficient_nontrivial _ j (canonicalSextic_pow_ne_one P hgood hchar hj hj6)

theorem finite_active_scalar_norm_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (ψ : ∀ i, AddChar (O ⧸ P i) ℂ) (hψ : ∀ i, (ψ i).IsPrimitive)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ ε : ∀ i, (O ⧸ P i)ˣ) :
    ‖∏ i, (((canonicalSextic (P i) (hgood i))⁻¹) ^ 2) (σ i) *
      phase (canonicalSextic (P i) (hgood i)) (ψ i) (j i) (ε i)‖ = 1 := by
  rw [norm_prod]
  have hlocal (i : ι) :
      ‖(((canonicalSextic (P i) (hgood i))⁻¹) ^ 2) (σ i) *
        phase (canonicalSextic (P i) (hgood i)) (ψ i) (j i) (ε i)‖ = 1 := by
    rw [norm_mul, FiniteRayExpansion.norm_char_unit,
      canonical_phase_norm (P i) (hgood i) (hchar i) (ψ i) (hψ i) (j i) (hj6 i) (ε i), one_mul]
  simp only [hlocal, Finset.prod_const_one]

end LocalReflectionBrackets

namespace EisensteinSchwartzPoisson
open MeasureTheory MeasureTheory.Measure Set Real
open scoped SchwartzMap FourierTransform

theorem complex_radial_norm_sq_integral (F : ℝ → ℂ) :
    (∫ z : ℂ, F (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by
  have hsub : (∫ r : ℝ in Ioi 0, (2 * r) • F (r ^ 2)) = ∫ t : ℝ in Ioi 0, F t := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
      using (integral_comp_rpow_Ioi_of_pos (g := F) (by norm_num : (0 : ℝ) < 2))
  have hsub' : (2 : ℂ) * (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) =
      ∫ t : ℝ in Ioi 0, F t := by
    simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat,
      mul_assoc, integral_const_mul] using hsub
  calc
    _ = ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 : ℂ) * F (p.1 ^ 2) := by
      rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
      simp only [Complex.norm_polarCoord_symm, sq_abs, Complex.real_smul]
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) *
        ∫ _θ : ℝ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
      rw [← setIntegral_prod_mul, volume_eq_prod]
      simp only [mul_one]
    _ = (∫ r : ℝ in Ioi 0, (r : ℂ) * F (r ^ 2)) * (2 * Real.pi : ℂ) := by
      congr 1
      simp only [integral_const, measureReal_restrict_apply MeasurableSet.univ,
        Set.univ_inter, volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]),
        sub_neg_eq_add, Complex.real_smul, mul_one]
      push_cast
      ring
    _ = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, F t := by rw [← hsub']; ring

theorem paperRadialFourier_zero_eq_halfline (F : ℝ → ℂ) :
    paperRadialFourier F 0 = (2 * Real.pi / Real.sqrt 3 : ℂ) *
      ∫ t : ℝ in Ioi 0, F t := by
  have he : paperE 0 = 1 := by simp [paperE_eq_exp]
  simp only [paperRadialFourier, paperFourier, Real.sqrt_zero, Complex.ofReal_zero,
    mul_zero, neg_zero, he, one_mul]
  rw [complex_radial_norm_sq_integral]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

theorem quadratic_principal_zero_modes_equal (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier (fun t : ℝ => paperRadialFourier W (t ^ 2)) 0 =
      paperRadialFourier (fun t : ℝ => W (t ^ 2)) 0 := by
  rw [paperRadialFourier_zero_eq_halfline, paperRadialFourier_zero_eq_halfline,
    paperRadialFourier_halfline_integral]

def quadraticSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  horizontalSlice (radialTest W) 0

@[simp] theorem quadraticSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticSquareProfile W x = W (x ^ 2) := by
  simp [quadraticSquareProfile, horizontalSlice_apply, complexPoint_eq,
    radialTest_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def quadraticTransformedSquareProfile (W : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 / Real.sqrt 3) (by positivity)))
      (horizontalSlice (𝓕 (radialTest W)) 0)

@[simp] theorem quadraticTransformedSquareProfile_apply (W : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticTransformedSquareProfile W x = paperRadialFourier W (x ^ 2) := by
  simp only [quadraticTransformedSquareProfile, _root_.smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, horizontalSlice_apply]
  rw [paperRadialFourier_square]
  simp only [complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero,
    SchwartzMap.fourier_coe, mul_comm x (2 / Real.sqrt 3)]
  rfl

theorem quadraticSquareProfile_principal_equal (W : 𝓢(ℝ, ℂ)) :
    paperRadialFourier (quadraticTransformedSquareProfile W) 0 =
      paperRadialFourier (quadraticSquareProfile W) 0 := by
  have h1 : (quadraticTransformedSquareProfile W : ℝ → ℂ) =
      fun x => paperRadialFourier W (x ^ 2) := by funext x; exact quadraticTransformedSquareProfile_apply W x
  have h2 : (quadraticSquareProfile W : ℝ → ℂ) = fun x => W (x ^ 2) := by
    funext x; exact quadraticSquareProfile_apply W x
  rw [h1, h2, quadratic_principal_zero_modes_equal]

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap
namespace ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson

theorem primeSubsetGenerator_norm_sq {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 = (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (span_idealGenerator _)

theorem masked_principal_radial_poisson {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * ∑ E ∈ S.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
          (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
        ∑' h : O, paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
  let Q : Empty → Ideal O := Empty.elim
  let : ∀ i, (Q i).IsMaximal := fun i => nomatch i
  have hcop : Pairwise (Function.onFun IsCoprime Q) := by intro i; cases i
  have hg : ∀ i, lambda ∉ Q i := fun i => nomatch i
  have hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2 := fun i => nomatch i
  have hj0 : ∀ i : Empty, (1 : ℕ) ≠ 0 := fun i => nomatch i
  have hj6 : ∀ i : Empty, (1 : ℕ) < 6 := fun i => nomatch i
  have hp := canonical_masked_radial_poisson_collected P hinj S Q hcop hg hc
    (fun _ => 1) hj0 hj6 V M hM
  simpa only [finiteSexticRow_of_isEmpty, canonicalNormalizedGauss_of_isEmpty,
    finitePrimeModulus_norm_of_isEmpty, Complex.ofReal_one, mul_one, div_one,
    star_one, one_mul, one_pow, primeSubsetGenerator_norm_sq, Complex.ofReal_natCast] using hp

def maskedPrincipalRemainder {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (V : ℝ → ℂ) (M : ℝ) : ℂ :=
  (M : ℂ) * ∑ E ∈ S.powerset,
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier V
      (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))

theorem masked_principal_radial_poisson_zero_split {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (V : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z * V (‖eisEmbedding z‖ ^ 2 / M)) =
      (M : ℂ) * paperRadialFourier V 0 *
        (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) +
        maskedPrincipalRemainder P S V M := by
  have hp (E : Finset ι) : 0 < (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hs (E : Finset ι) :
      (∑' h : O, paperRadialFourier V
        (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ))) =
      paperRadialFourier V 0 +
        ∑' h : O, if h = 0 then 0 else paperRadialFourier V
          (M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) := by
    have hsum := (paperRadialFourier_lattice_summable_norm V
      (M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)) (div_pos hM (hp E))).of_norm
    have heq (h : O) : M / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) * ‖eisEmbedding h‖ ^ 2 =
        M * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by ring
    simp_rw [heq] at hsum
    simpa only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
      using hsum.tsum_eq_add_tsum_ite 0
  have hprime : ∀ i, Prime (P i) := fun i => Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  rw [masked_principal_radial_poisson P hinj S V M hM]
  simp_rw [hs, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, mul_add]
  rw [primeSubset_moebius_norm_sum P hprime hinj S]
  unfold maskedPrincipalRemainder
  ring

theorem quadratic_square_poisson_main_cancel {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask P S z *
      paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
    (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) =
      maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M -
      maskedPrincipalRemainder P S (quadraticSquareProfile W) M := by
  have h1 := masked_principal_radial_poisson_zero_split P hinj S
    (quadraticTransformedSquareProfile W) M hM
  have h2 := masked_principal_radial_poisson_zero_split P hinj S (quadraticSquareProfile W) M hM
  simp only [quadraticTransformedSquareProfile_apply] at h1
  simp only [quadraticSquareProfile_apply] at h2
  rw [h1, h2, quadraticSquareProfile_principal_equal]
  ring

end ActualEisensteinCubic

open scoped BigOperators Classical
namespace PrimaryIdealUnitReindex
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

abbrev GoodIdeal := {I : Ideal O // primaryGenerator I ≠ 0}
abbrev GoodElement := {z : O // primaryGenerator (Ideal.span {z}) ≠ 0}

theorem finite_units : Finite Oˣ := by
  let f : Oˣ → {z : O // z ∈ rowNormDisk 1} := fun u => ⟨u.val, by
    rw [mem_rowNormDisk]
    rw [Ideal.span_singleton_eq_top.mpr u.isUnit]
    norm_num⟩
  exact Finite.of_injective f (fun u v h => Units.ext (congrArg Subtype.val h))

theorem span_unit_primary (u : Oˣ) (I : GoodIdeal) :
    Ideal.span {(u : O) * primaryGenerator I.val} = I.val := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  exact (primaryGenerator_spec I.val I.property).1

def unitIdealToElement (p : Oˣ × GoodIdeal) : GoodElement :=
  ⟨p.1.val * primaryGenerator p.2.val, by rw [span_unit_primary]; exact p.2.property⟩

theorem unitIdealToElement_injective : Function.Injective unitIdealToElement := by
  intro p q hpq
  have he : p.1.val * primaryGenerator p.2.val = q.1.val * primaryGenerator q.2.val :=
    congrArg Subtype.val hpq
  have hI : p.2 = q.2 := by
    apply Subtype.ext
    simpa only [span_unit_primary] using congrArg (fun z : O => Ideal.span {z}) he
  have hu : p.1 = q.1 := by
    apply Units.ext
    rw [hI] at he
    exact mul_right_cancel₀ q.2.property he
  exact Prod.ext hu hI

theorem unitIdealToElement_surjective : Function.Surjective unitIdealToElement := by
  intro z
  let I : GoodIdeal := ⟨Ideal.span {z.val}, z.property⟩
  have ha : Associated (primaryGenerator I.val) z.val :=
    Ideal.span_singleton_eq_span_singleton.mp (primaryGenerator_spec I.val I.property).1
  obtain ⟨u, hu⟩ := ha
  refine ⟨(u, I), Subtype.ext ?_⟩
  change u.val * primaryGenerator I.val = z.val
  simpa only [mul_comm] using hu

def unitIdealEquiv : Oˣ × GoodIdeal ≃ GoodElement :=
  Equiv.ofBijective unitIdealToElement ⟨unitIdealToElement_injective, unitIdealToElement_surjective⟩

theorem tsum_good_elements_product (f : O → ℂ) :
    (∑' z : GoodElement, f z.val) =
      ∑' p : Oˣ × GoodIdeal, f (p.1.val * primaryGenerator p.2.val) := by
  exact (unitIdealEquiv.tsum_eq (fun z : GoodElement => f z.val)).symm

theorem tsum_good_elements_unit_invariant (f : O → ℂ)
    (hf : Summable (fun z : GoodElement => f z.val))
    (hu : ∀ (u : Oˣ) (I : GoodIdeal), f (u.val * primaryGenerator I.val) = f (primaryGenerator I.val)) :
    (∑' z : GoodElement, f z.val) =
      (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal, f (primaryGenerator I.val) := by
  let : Finite Oˣ := finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  have hp : Summable (fun p : Oˣ × GoodIdeal => f (p.1.val * primaryGenerator p.2.val)) :=
    unitIdealEquiv.summable_iff.mpr hf
  rw [tsum_good_elements_product, hp.tsum_prod]
  simp only [hu, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]

theorem lambda_prime_actual : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K).zeta_sub_one_prime'

theorem primaryGenerator_ne_zero_of_good_factors (I : Ideal O) (hI : I ≠ 0)
    (hg : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, lambda ∉ P) :
    primaryGenerator I ≠ 0 := by
  rw [primaryGenerator, ite_eq_right hI]
  apply Multiset.prod_ne_zero
  intro hz
  obtain ⟨P, hP, hzero⟩ := Multiset.mem_map.mp hz
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  exact primaryPrime_ne_zero P (hg P hP) hzero

theorem primaryGenerator_span_ne_zero_iff (z : O) :
    primaryGenerator (Ideal.span {z}) ≠ 0 ↔ ¬ lambda ∣ z := by
  constructor
  · intro hg hdiv
    have hs := primaryGenerator_spec (Ideal.span {z}) hg
    have hzgen : z ∣ primaryGenerator (Ideal.span {z}) := by
      apply Ideal.mem_span_singleton.mp
      exact hs.1.le (Ideal.subset_span (by simp))
    have hgen := hdiv.trans hzgen
    have hminus : lambda ∣ primaryGenerator (Ideal.span {z}) - 1 :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans hs.2
    have hone : lambda ∣ (1 : O) := by
      convert dvd_sub hgen hminus using 1 ; ring
    exact lambda_prime_actual.not_isUnit (isUnit_of_dvd_one hone)
  · intro hdiv
    have hz : z ≠ 0 := by intro h; subst z; exact hdiv (dvd_zero _)
    have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
    apply primaryGenerator_ne_zero_of_good_factors _ hI
    intro P hP hlam
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hzin : z ∈ P := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
      (Ideal.subset_span (by simp))
    have hcop : IsCoprime lambda z := lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hdiv
    obtain ⟨a, b, hab⟩ := hcop
    have hone : (1 : O) ∈ P := by
      rw [← hab]
      exact P.add_mem (P.mul_mem_left a hlam) (P.mul_mem_left b hzin)
    exact (inferInstance : P.IsMaximal).ne_top ((Ideal.eq_top_iff_one P).mpr hone)

theorem tsum_ramified_mask (f : O → ℂ) :
    (∑' z : O, if lambda ∣ z then 0 else f z) = ∑' z : GoodElement, f z.val := by
  calc
    _ = ∑' z : O, ({z : O | primaryGenerator (Ideal.span {z}) ≠ 0} : Set O).indicator f z := by
      apply tsum_congr
      intro z
      simp only [Set.indicator, Set.mem_ofPred_eq, primaryGenerator_span_ne_zero_iff]
      split_ifs <;> rfl
    _ = _ := (tsum_subtype ({z : O | primaryGenerator (Ideal.span {z}) ≠ 0} : Set O) f).symm

theorem tsum_ramified_mask_unit_invariant (f : O → ℂ) (hf : Summable f)
    (hu : ∀ (u : Oˣ) (I : GoodIdeal), f (u.val * primaryGenerator I.val) = f (primaryGenerator I.val)) :
    (∑' z : O, if lambda ∣ z then 0 else f z) =
      (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal, f (primaryGenerator I.val) := by
  rw [tsum_ramified_mask]
  exact tsum_good_elements_unit_invariant f (hf.subtype _) hu

end PrimaryIdealUnitReindex

open scoped BigOperators Classical
namespace QuadraticUnitInvariance
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay

theorem principalNormalizedGauss_three_eq_quadraticGamma
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) :
    principalNormalizedGauss P hcop hg (fun _ => 3) c hc hc0 = quadraticGammaO c hc0 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let e := (Ideal.quotEquivOfEq hc).trans (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (P i) (hg i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ P i) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0) hchar

theorem principalNormalizedGauss_three_eq_rayValue
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) :
    principalNormalizedGauss P hcop hg (fun _ => 3) c hc hc0 = quadraticRayValue (residue c) := by
  rw [principalNormalizedGauss_three_eq_quadraticGamma P hcop hg hchar c hc hc0,
    quadraticGammaO_eq_rayValue]

theorem quadratic_unit_phase
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (u : Oˣ) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) u.val *
      quadraticRayValue (residue (∏ i, p i)) =
        quadraticRayValue (residue (u.val * ∏ i, p i)) := by
  have hn0 : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hn : Ideal.span {∏ i, p i} = ∏ i, Ideal.span {p i} := span_finset_prod _ _
  have hc : Ideal.span {u.val * ∏ i, p i} = ∏ i, Ideal.span {p i} := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, hn]
  have h := principalNormalizedGauss_unit_change (fun i => Ideal.span {p i}) hcop hg (fun _ => 3)
    (u.val * ∏ i, p i) (∏ i, p i) hc hn (mul_ne_zero u.ne_zero hn0) hn0 u rfl
  rw [principalNormalizedGauss_three_eq_rayValue _ hcop hg hchar,
    principalNormalizedGauss_three_eq_rayValue _ hcop hg hchar] at h
  exact h.symm

theorem finiteSexticRow_three_star
    {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (z : O) :
    star (finiteSexticRow P hg (fun _ => 3) z) = finiteSexticRow P hg (fun _ => 3) z := by
  simp only [finiteSexticRow, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [canonicalSextic_pow_three_quadratic]
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom, star_intCast]

theorem quadratic_unit_value_eq_of_same_ray
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i)) (u : Oˣ) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) u.val =
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val := by
  have hne : quadraticRayValue (residue (∏ i, p i)) ≠ 0 := by
    rw [← canonicalProductGauss_three_eq_rayValue p hp hcop hg hchar]
    exact norm_ne_zero_iff.mp (by rw [norm_canonicalProductGauss p hp hcop hg hchar
      (fun _ => 3) (fun _ => by decide) (fun _ => by decide)]; norm_num)
  apply mul_right_cancel₀ hne
  rw [quadratic_unit_phase p hp hcop hg hchar, hray,
    quadratic_unit_phase q hq hcopq hgq hcharq, residue_mul, residue_mul, hray]

theorem quadratic_pair_unit_invariant
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i)) (u : Oˣ) (z : O) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (u.val * z) *
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (u.val * z) =
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
      finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z := by
  have hu := quadratic_unit_value_eq_of_same_ray p hp hcop hg hchar q hq hcopq hgq hcharq hray u
  have hs := finiteSexticRow_unit_mul_star (fun i => Ideal.span {q i}) hgq (fun _ => 3) u
  rw [finiteSexticRow_three_star] at hs
  rw [finiteSexticRow_mul, finiteSexticRow_mul, hu]
  calc
    _ = (finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) u.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z) := by ring
    _ = _ := by rw [hs, one_mul]

end QuadraticUnitInvariance

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound -/

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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical
namespace CoprimeBilinearSieve
open FiniteSieveOperator CoprimeSieveOperator CoprimeMobiusExtension

theorem disjoint_bilinear_expansion {ι n p : Type*} [DecidableEq ι]
    [Fintype n] [Fintype p]
    (B : Finset ι) (left : n → Finset ι) (right : p → Finset ι)
    (hl : ∀ j, left j ⊆ B) (hr : ∀ k, right k ⊆ B)
    (z : n → ℂ) (v : p → ℂ) :
    (∑ j, ∑ k, if Disjoint (left j) (right k) then star (z j) * v k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (star (∑ j, if D ⊆ left j then z j else 0) *
          (∑ k, if D ⊆ right k then v k else 0)) := by
  have hp (j : n) (k : p) :
      (if Disjoint (left j) (right k) then star (z j) * v k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) := by
    calc
      _ = (if Disjoint (left j) (right k) then (1 : ℂ) else 0) *
          (star (z j) * v k) := by split_ifs <;> simp
      _ = _ := by
        rw [disjoint_indicator_expansion B _ _ (hl j) (hr k), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ j, ∑ D ∈ B.powerset, ∑ k, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ D ∈ B.powerset, ∑ j, ∑ k, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      simp only [star_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : D ⊆ left j <;> by_cases hk : D ⊆ right k <;> simp [hj, hk]

theorem coprime_bilinear_operator_bound {ι m n p : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (B : Finset ι) (left : n → Finset ι) (right : p → Finset ι)
    (hl : ∀ j, left j ⊆ B) (hr : ∀ k, right k ⊆ B)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2) := by
  let X (D : Finset ι) (i : m) : ℂ := ∑ j, A i j * (if D ⊆ left j then a j else 0)
  let Y (D : Finset ι) (i : m) : ℂ := ∑ k, C i k * (if D ⊆ right k then b k else 0)
  have heq (i : m) :
      (∑ j, ∑ k, if Disjoint (left j) (right k) then
        star (A i j * a j) * (C i k * b k) else 0) =
        ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card * (star (X D i) * Y D i) := by
    simpa only [X, Y, mul_ite, mul_zero] using
      disjoint_bilinear_expansion B left right hl hr (fun j => A i j * a j)
        (fun k => C i k * b k)
  have hnorm :
      (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
        star (A i j * a j) * (C i k * b k) else 0‖) ≤
        ∑ D ∈ B.powerset, ∑ i, ‖X D i‖ * ‖Y D i‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D _
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_star]
    exact le_rfl
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (B.powerset ×ˢ (Finset.univ : Finset m))
    (fun di => ‖X di.1 di.2‖) (fun di => ‖Y di.1 di.2‖)
  simp only [Finset.sum_product] at hCS
  have hX : (∑ D ∈ B.powerset, ∑ i, ‖X D i‖ ^ 2) ≤
      ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ B.powerset, ‖operator A‖ ^ 2 *
          ∑ j, ‖if D ⊆ left j then a j else 0‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact energy_bound A _
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy B left hl a]
  have hY : (∑ D ∈ B.powerset, ∑ i, ‖Y D i‖ ^ 2) ≤
      ‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ B.powerset, ‖operator C‖ ^ 2 *
          ∑ k, ‖if D ⊆ right k then b k else 0‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact energy_bound C _
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy B right hr b]
  exact (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnorm 2).trans
    (hCS.trans (mul_le_mul hX hY (by positivity) (by positivity)))

end CoprimeBilinearSieve

namespace IdealCoprimeBilinearSieve
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum IdealCoprimeSieveOperator FiniteSieveOperator

theorem support_weighted_energy_bound {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ j, (2 : ℝ) ^ (primeSupport (column j)).card * ‖a j‖ ^ 2) ≤
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (support_card_bound ε hε (column j) (hcol j)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le)
      (supportConstant_pos ε hε).le)

theorem ideal_coprime_bilinear_operator_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε)
    (left : n → Ideal O) (right : p → Ideal O)
    (hl0 : ∀ j, left j ≠ 0) (hr0 : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (_hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * (supportConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * (supportConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by
  let B : Finset (Ideal O) :=
    (Finset.univ.biUnion (fun j => primeSupport (left j))) ∪
      (Finset.univ.biUnion (fun k => primeSupport (right k)))
  have hl (j : n) : primeSupport (left j) ⊆ B := by
    intro P hP
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hP⟩))
  have hr (k : p) : primeSupport (right k) ⊆ B := by
    intro P hP
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hP⟩))
  have h := CoprimeBilinearSieve.coprime_bilinear_operator_bound B
    (fun j => primeSupport (left j)) (fun k => primeSupport (right k)) hl hr A C a b
  simp_rw [primeSupport_disjoint_iff (hl0 _) (hr0 _)] at h
  apply h.trans
  apply mul_le_mul
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (support_weighted_energy_bound ε hε left hl0 N₁ hlN a) (sq_nonneg ‖operator A‖)
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (support_weighted_energy_bound ε hε right hr0 N₂ hrN b) (sq_nonneg ‖operator C‖)
  · positivity
  · have hpos := (supportConstant_pos ε hε).le
    positivity

end IdealCoprimeBilinearSieve

namespace DivisorBlockCauchy
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum FiniteSieveOperator IdealCoprimeSieveOperator

theorem divisor_mask_energy {n : Type*} [Fintype n]
    (S : Finset (Ideal O)) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      ∑ j, ((idealDivisors (column j)).card : ℝ) * ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  have hsub : S.filter (fun D => D ∣ column j) ⊆ idealDivisors (column j) := by
    intro D hD
    exact (mem_idealDivisors (hcol j)).mpr (Finset.mem_filter.mp hD).2
  have hite (D : Ideal O) : ‖if D ∣ column j then a j else 0‖ ^ 2 =
      if D ∣ column j then ‖a j‖ ^ 2 else 0 := by split_ifs <;> simp
  simp_rw [hite]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)

def divisorConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose

theorem divisorConstant_pos (ε : ℝ) (hε : 0 < ε) : 0 < divisorConstant ε hε :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.1

theorem divisor_mask_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O))
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  apply (divisor_mask_energy S column hcol a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2
    (column j) (hcol j)).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le) (divisorConstant_pos ε hε).le

theorem rectangular_cauchy {α β : Type*} (S : Finset α) (T : Finset β)
    (H : α → β → ℝ) (E : α → ℝ) (F : β → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hH : ∀ d ∈ S, ∀ e ∈ T, (H d e) ^ 2 ≤ C * E d * F e) :
    (∑ d ∈ S, ∑ e ∈ T, H d e) ^ 2 ≤
      (S.card : ℝ) * T.card * C * (∑ d ∈ S, E d) * (∑ e ∈ T, F e) := by
  classical
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ T)
    (fun _ => (1 : ℝ)) (fun x => H x.1 x.2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_product, Nat.cast_mul, Finset.sum_product] at hCS
  have hsum : (∑ d ∈ S, ∑ e ∈ T, (H d e) ^ 2) ≤
      C * (∑ d ∈ S, E d) * (∑ e ∈ T, F e) := by
    calc
      _ ≤ ∑ d ∈ S, ∑ e ∈ T, C * E d * F e := by
        apply Finset.sum_le_sum
        intro d hd
        exact Finset.sum_le_sum (fun e he => hH d hd e he)
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]
  apply hCS.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ (S.card : ℝ) * T.card by positivity)

end DivisorBlockCauchy

namespace IdealDivisorBilinearBlocks
abbrev O := ActualEisensteinCubic.O
open FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

def blockValue {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  ∑ i, ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
    star (A D i j * (if D ∣ left j then a j else 0)) *
      (B E i k * (if E ∣ right k then b k else 0)) else 0‖

theorem blockValue_nonneg {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) :
    0 ≤ blockValue left right A B a b D E :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (left : n → Ideal O) (right : p → Ideal O)
    (hl0 : ∀ j, left j ≠ 0) (hr0 : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hA : ∀ D ∈ S, ‖operator (A D)‖ ^ 2 ≤ UA)
    (hB : ∀ E ∈ T, ‖operator (B E)‖ ^ 2 ≤ UB) :
    (∑ D ∈ S, ∑ E ∈ T, blockValue left right A B a b D E) ^ 2 ≤
      (S.card : ℝ) * T.card *
        (UA * UB * (supportConstant ε hε * N₁ ^ ε) *
          (supportConstant ε hε * N₂ ^ ε)) *
        ((divisorConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by
  let EL (D : Ideal O) : ℝ := ∑ j, ‖if D ∣ left j then a j else 0‖ ^ 2
  let ER (E : Ideal O) : ℝ := ∑ k, ‖if E ∣ right k then b k else 0‖ ^ 2
  let C : ℝ := UA * UB * (supportConstant ε hε * N₁ ^ ε) *
    (supportConstant ε hε * N₂ ^ ε)
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hEL (D) : 0 ≤ EL D := by dsimp [EL]; positivity
  have hER (E) : 0 ≤ ER E := by dsimp [ER]; positivity
  have hp (D : Ideal O) (hD : D ∈ S) (E : Ideal O) (hE : E ∈ T) :
      (blockValue left right A B a b D E) ^ 2 ≤ C * EL D * ER E := by
    have hh := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound
      ε hε left right hl0 hr0 N₁ N₂ hN₁ hN₂ hlN hrN (A D) (B E)
      (fun j => if D ∣ left j then a j else 0)
      (fun k => if E ∣ right k then b k else 0)
    change (blockValue left right A B a b D E) ^ 2 ≤
      (‖operator (A D)‖ ^ 2 * (supportConstant ε hε * N₁ ^ ε) * EL D) *
      (‖operator (B E)‖ ^ 2 * (supportConstant ε hε * N₂ ^ ε) * ER E) at hh
    apply hh.trans
    calc
      _ ≤ (UA * (supportConstant ε hε * N₁ ^ ε) * EL D) *
          (UB * (supportConstant ε hε * N₂ ^ ε) * ER E) := by
        gcongr
        · exact hA D hD
        · exact hB E hE
      _ = _ := by dsimp [C]; ring
  have hc := rectangular_cauchy S T (blockValue left right A B a b) EL ER C hC hp
  have he1 := divisor_mask_energy_small_power ε hε S left hl0 N₁ hlN a
  have he2 := divisor_mask_energy_small_power ε hε T right hr0 N₂ hrN b
  apply hc.trans
  change (S.card : ℝ) * T.card * C * (∑ D ∈ S, EL D) * (∑ E ∈ T, ER E) ≤ _
  change (∑ D ∈ S, EL D) ≤ _ at he1
  change (∑ E ∈ T, ER E) ≤ _ at he2
  dsimp only [C]
  gcongr

end IdealDivisorBilinearBlocks

namespace FiniteSieveRestriction
open FiniteSieveOperator

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

def extendByZero (S : Finset n) (f : n → p) (u : n → ℂ) (k : p) : ℂ :=
  ∑ j ∈ S, if f j = k then u j else 0

omit [Fintype n] [Fintype p] [DecidableEq n] in
theorem extendByZero_apply_image (S : Finset n) (f : n → p) (u : n → ℂ)
    (hf : Set.InjOn f S) (j : n) (hj : j ∈ S) : extendByZero S f u (f j) = u j := by
  unfold extendByZero
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp only [ite_eq_right (fun h => hkj (hf hk hj h))]
  · exact fun h => (h hj).elim

omit [Fintype n] [Fintype p] [DecidableEq n] in
theorem extendByZero_zero (S : Finset n) (f : n → p) (u : n → ℂ)
    (k : p) (hk : k ∉ S.image f) : extendByZero S f u k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact ite_eq_right (fun h => hk (Finset.mem_image.mpr ⟨j, hj, h⟩))

omit [Fintype n] [DecidableEq n] in
theorem extendByZero_energy (S : Finset n) (f : n → p) (u : n → ℂ)
    (hf : Set.InjOn f S) :
    (∑ k, ‖extendByZero S f u k‖ ^ 2) = ∑ j ∈ S, ‖u j‖ ^ 2 := by
  calc
    _ = ∑ k ∈ S.image f, ‖extendByZero S f u k‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp [extendByZero_zero S f u k hk]
    _ = ∑ j ∈ S, ‖extendByZero S f u (f j)‖ ^ 2 := by
      rw [Finset.sum_image]
      exact fun j hj k hk h => hf hj hk h
    _ = _ := Finset.sum_congr rfl (fun j hj => by rw [extendByZero_apply_image S f u hf j hj])

omit [Fintype n] [DecidableEq n] in
theorem extendByZero_matrix {m : Type*} (S : Finset n) (f : n → p)
    (u : n → ℂ) (A : Matrix m p ℂ) (i : m) :
    (∑ k, A i k * extendByZero S f u k) = ∑ j ∈ S, A i (f j) * u j := by
  simp only [extendByZero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (f j)]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

theorem masked_column_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (S : Finset n) (f : n → p) (hf : Set.InjOn f S) (A : Matrix m p ℂ) :
    ‖operator (fun i j => if j ∈ S then A i (f j) else 0)‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  let v : EuclideanSpace ℂ p := WithLp.toLp 2 (extendByZero S f u)
  have hv : ‖v‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖extendByZero S f u k‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2
    rw [extendByZero_energy S f u hf]
    exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖u j‖)
  have heq : operator (fun i j => if j ∈ S then A i (f j) else 0) u = operator A v := by
    ext i
    change (∑ j, (if j ∈ S then A i (f j) else 0) * u j) =
      ∑ k, A i k * extendByZero S f u k
    rw [extendByZero_matrix]
    simp only [ite_mul, zero_mul, ← Finset.sum_filter]
    simp
  rw [heq]
  exact ((operator A).le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))

theorem column_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix m p ℂ) :
    ‖operator (fun i j => A i (f j))‖ ≤ ‖operator A‖ := by
  simpa only [Finset.mem_univ, ite_true] using
    masked_column_restriction_norm_le Finset.univ f hf.injOn A

theorem row_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix p m ℂ) :
    ‖operator (fun i j => A (f i) j)‖ ≤ ‖operator A‖ := by
  let B : Matrix n m ℂ := fun i j => A (f i) j
  have h := column_restriction_norm_le f hf A.conjTranspose
  change ‖operator B.conjTranspose‖ ≤ ‖operator A.conjTranspose‖ at h
  rw [operator_conjTranspose_norm B, operator_conjTranspose_norm A] at h
  exact h

theorem submatrix_norm_le {m q : Type*} [Fintype m] [Fintype q]
    [DecidableEq m] [DecidableEq q]
    (r : m → q) (hr : Function.Injective r) (c : n → p) (hc : Function.Injective c)
    (A : Matrix q p ℂ) :
    ‖operator (fun i j => A (r i) (c j))‖ ≤ ‖operator A‖ :=
  (row_restriction_norm_le r hr (fun i j => A i (c j))).trans
    (column_restriction_norm_le c hc A)

end FiniteSieveRestriction

open scoped BigOperators
namespace FiniteSieveOperator

theorem squared_norm_le_of_energy {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a : n → ℂ, (∑ i, ‖∑ j, A i j * a j‖ ^ 2) ≤ C * ∑ j, ‖a j‖ ^ 2) :
    ‖operator A‖ ^ 2 ≤ C := by
  have hop : ‖operator A‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C)
    intro a
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg a))).mp
    simpa only [mul_pow, Real.sq_sqrt hC, EuclideanSpace.norm_sq_eq, operator_apply] using h a
  simpa only [Real.sq_sqrt hC] using pow_le_pow_left₀ (norm_nonneg _) hop 2

end FiniteSieveOperator

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
abbrev O := ActualEisensteinCubic.O
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss

theorem idealSexticRow_ambient
    (F G : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥) (hGp : ∀ I ∈ G, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hGg : ∀ I ∈ G, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hIF : I ∈ F) (hIG : I ∈ G) (z : O) :
    idealSexticRow F hFp hFg I z = idealSexticRow G hGp hGg I z := by
  let idx (i : primePool F) (hi : i ∈ idealSupport F I) : primePool G :=
    ⟨i.val, mem_primePool_iff.mpr ⟨I, hIG, (mem_idealSupport_iff F I i).mp hi⟩⟩
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_bij idx
  · intro i hi
    exact (mem_idealSupport_iff G I (idx i hi)).mpr ((mem_idealSupport_iff F I i).mp hi)
  · intro i hi j hj hij
    exact Subtype.ext (congrArg (fun k : primePool G => k.val) hij)
  · intro j hj
    let i : primePool F := ⟨j.val, mem_primePool_iff.mpr
      ⟨I, hIF, (mem_idealSupport_iff G I j).mp hj⟩⟩
    have hi : i ∈ idealSupport F I :=
      (mem_idealSupport_iff F I i).mpr ((mem_idealSupport_iff G I j).mp hj)
    exact ⟨i, hi, Subtype.ext rfl⟩
  · intro i hi
    rfl

def Admissible (I : Ideal O) : Prop :=
  I ≠ 0 ∧ Squarefree I ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2

theorem singletonPositive (I : Ideal O) (h : Admissible I) : ∀ J ∈ ({I} : Finset (Ideal O)), J ≠ ⊥ := by
  intro J hJ
  rcases Finset.mem_singleton.mp hJ with rfl
  exact h.1

theorem singletonGood (I : Ideal O) (h : Admissible I) :
    ∀ J ∈ ({I} : Finset (Ideal O)), ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors J,
      goodLambda ∉ P := by
  intro J hJ P hP
  rcases Finset.mem_singleton.mp hJ with rfl
  exact (h.2.2 P hP).1

def quadraticRow (I : Ideal O) (z : O) : ℂ :=
  if h : Admissible I then
    (idealSexticRow {I} (singletonPositive I h) (singletonGood I h) I z) ^ 3
  else 0

theorem quadraticRow_eq (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hI : I ∈ F) (z : O) :
    quadraticRow I z =
      (idealSexticRow F (fun J hJ => (hF J hJ).1)
        (fun J hJ P hP => (hF J hJ).2.2 P hP |>.1) I z) ^ 3 := by
  rw [quadraticRow, dite_eq_left (hF I hI)]
  congr 1
  exact idealSexticRow_ambient {I} F (singletonPositive I (hF I hI))
    (fun J hJ => (hF J hJ).1) (singletonGood I (hF I hI))
    (fun J hJ P hP => (hF J hJ).2.2 P hP |>.1) I (Finset.mem_singleton_self I) hI z

def idealRange (X : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊X⌋₊).filter Admissible

theorem mem_idealRange {X : ℝ} {I : Ideal O} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha.1 (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, ha⟩

theorem idealRange_mono {X Y : ℝ} (h : X ≤ Y) : idealRange X ⊆ idealRange Y := by
  intro I hI
  rcases mem_idealRange.mp hI with ⟨ha, hN⟩
  exact mem_idealRange.mpr ⟨ha, hN.trans h⟩

def matrix (M N : ℝ) : Matrix (idealRange M) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)

def sieveNorm (M N : ℝ) : ℝ := ‖FiniteSieveOperator.operator (matrix M N)‖ ^ 2

theorem sieveNorm_nonneg (M N : ℝ) : 0 ≤ sieveNorm M N := sq_nonneg _

def rangeInclusion {X Y : ℝ} (h : X ≤ Y) (I : idealRange X) : idealRange Y :=
  ⟨I.val, idealRange_mono h I.property⟩

theorem rangeInclusion_injective {X Y : ℝ} (h : X ≤ Y) :
    Function.Injective (rangeInclusion h) := by
  intro I J heq
  exact Subtype.ext (congrArg (fun x : idealRange Y => x.val) heq)

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  have h := FiniteSieveRestriction.submatrix_norm_le
    (rangeInclusion hM) (rangeInclusion_injective hM)
    (rangeInclusion hN) (rangeInclusion_injective hN) (matrix M' N')
  change ‖FiniteSieveOperator.operator (matrix M N)‖ ≤
    ‖FiniteSieveOperator.operator (matrix M' N')‖ at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j => quadraticRow (cols j) (primaryGenerator (rows i)))‖ ^ 2 ≤
      sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (matrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem energy_bound (M N : ℝ) (a : idealRange N → ℂ) :
    (∑ I : idealRange M, ‖∑ J : idealRange N,
      quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      sieveNorm M N * ∑ J, ‖a J‖ ^ 2 :=
  FiniteSieveOperator.energy_bound (matrix M N) a

end CanonicalQuadraticSieve

end

end OAI

end

