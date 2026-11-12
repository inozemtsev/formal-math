module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.UnitRows
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part021
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.Euler

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.FixedRay -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open RayFourExpansion CenteredMomentPrimary HeckeFamily HeckeRowClosure
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_coprime_four (a : O) (ha : Supported (Ideal.span {a})) :
    IsCoprime (4 : O) a := by
  have hn := (supported_span_iff a).mp ha |>.2
  have hneg : IsCoprime (-2 : O) a :=
    CanonicalRowCompletion.negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
      (by simpa only [neg_dvd] using hn)
  have h2 : IsCoprime (2 : O) a := hneg.of_isCoprime_of_dvd_left ⟨-1, by ring⟩
  have h4 : IsCoprime ((2 : O)^2) a := h2.pow_left
  simpa only [show (2 : O)^2 = 4 by norm_num] using h4

theorem supported_coprime_twelve (a : O) (ha : Supported (Ideal.span {a})) :
    IsCoprime (12 : O) a := by
  have h9 := ShortDraftCRT.nine_coprime_of_not_lambda_dvd a ((supported_span_iff a).mp ha).1
  have h36 : IsCoprime (36 : O) a := by
    convert (supported_coprime_four a ha).mul_left h9 using 1 ; norm_num
  exact h36.of_isCoprime_of_dvd_left ⟨3, by norm_num⟩

theorem supported_rayMask (a : O) (ha : Supported (Ideal.span {a})) : rayMask a = 1 := by
  rw [rayMask, ite_eq_left (CenteredMomentCommonSupport.isUnit_residue_of_coprime
    4 a (supported_coprime_four a ha))]

def phaseTable (D E : O) (r s : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour r) (ActualEisensteinCoordinates.residue E) : ℂ) *
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour s) (ActualEisensteinCoordinates.residue D) : ℂ) *
  (QuadraticAllOddCRT.quadraticRaySign
    (QuadraticGaussRay.residueQuotientFour r) (QuadraticGaussRay.residueQuotientFour s) : ℂ)

theorem phaseTable_mk (D E a b : O) :
    phaseTable D E (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) =
      sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b := by
  simp only [phaseTable, QuadraticGaussRay.residueQuotientFour_mk,
    sexticReciprocityPhase, star_intCast]

theorem phaseTable_norm (D E : O) (r s : RayRing) : ‖phaseTable D E r s‖ ≤ 1 := by
  unfold phaseTable QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> norm_num

theorem phaseTable_expansion (D E a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ * rayCharacter χ a * rayCharacter ξ b := by
  have h := pair_phase_expansion (phaseTable D E) a b
  simpa only [supported_rayMask a ha, supported_rayMask b hb, one_mul,
    phaseTable_mk] using h

theorem phaseTable_mass (D E : O) :
    (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ‖) ≤ 256 := by
  simpa only [mul_one] using pairCoeff_sum_norm_le (phaseTable D E) 1
    (fun u v => phaseTable_norm D E u v)

def primaryRayHom (χ : RayCharacter) : O →* ℂ where
  toFun n := primaryIdealCharacter 4 χ (Ideal.span {n})
  map_one' := by simp [← Ideal.one_eq_top]
  map_mul' x y := by rw [← Ideal.span_singleton_mul_span_singleton, map_mul]

theorem primaryRayHom_primary (χ : RayCharacter) (a : O) (hp : λ₀^2 ∣ a - 1) :
    primaryRayHom χ a = rayCharacter χ a := by
  change χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {a}))) = _
  rw [CompletedGauss.primaryGenerator_span a (CubicJacobiGlobal.primary_ne_zero a hp) hp]
  rfl

theorem primaryRayHom_unit_mul (χ : RayCharacter) (u : Oˣ) (a : O) :
    primaryRayHom χ ((u : O) * a) = primaryRayHom χ a := by
  change primaryIdealCharacter 4 χ (Ideal.span {(u : O) * a}) = _
  rw [Ideal.span_singleton_mul_left_unit u.isUnit]
  rfl

theorem primaryRayHom_periodic (χ : RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(12 : O)}) (primaryRayHom χ) := by
  let F : O →* ℂ := χ.toMonoidHom.comp (Ideal.Quotient.mk (Ideal.span {(4 : O)})).toMonoidHom
  refine periodic_of_primary _ ?_ _ F ?_ (primaryRayHom_unit_mul χ) ?_ ?_
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ActualEisensteinCubic.lambda_sq_dvd_three.trans ⟨4, by norm_num⟩
  · intro x y hxy
    apply congrArg χ
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact (show (4 : O) ∣ 12 from ⟨3, by norm_num⟩).trans (Ideal.mem_span_singleton.mp hxy)
  · intro x hx
    have hz : CompletedGauss.primaryGenerator (Ideal.span {x}) = 0 := by
      by_contra hn
      exact (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff x).mp hn hx
    change χ (Ideal.Quotient.mk _ (CompletedGauss.primaryGenerator (Ideal.span {x}))) = 0
    let : Nontrivial RayRing := Fintype.one_lt_card_iff_nontrivial.mp (by rw [rayRing_card]; norm_num)
    rw [hz, map_zero, MulChar.map_zero]
  · exact primaryRayHom_primary χ

def primaryRayCharacter (χ : RayCharacter) : Character :=
  rowCharacter (Ideal.span {(12 : O)}) (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
    (primaryRayHom χ) (primaryRayHom_periodic χ) (by
      intro u
      simpa using primaryRayHom_unit_mul χ u 1)

@[simp] theorem primaryRayCharacter_modulus (χ : RayCharacter) :
    (primaryRayCharacter χ).modulus = Ideal.span {(12 : O)} := rfl

theorem primaryRayCharacter_primary (χ : RayCharacter) (a : O)
    (ha : Supported (Ideal.span {a})) (hp : λ₀^2 ∣ a - 1) :
    elementCoeff (primaryRayCharacter χ) a = rayCharacter χ a := by
  rw [primaryRayCharacter, elementCoeff_rowCharacter,
    ite_eq_left (CenteredMomentCommonSupport.isUnit_residue_of_coprime
      12 a (supported_coprime_twelve a ha)), primaryRayHom_primary χ a hp]

theorem completeSupportExtension_separated (D E h a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    completeSupportExtension D E hD hE h a b =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            (rayCharacter χ a * idealRowHom h (Ideal.span {a})) *
            (rayCharacter ξ b * star (idealRowHom (-h) (Ideal.span {b}))) := by
  rw [completeSupportExtension]
  have he := phaseTable_expansion D E a b ha hb
  calc
    _ = actualCorrelation D E hD hE h *
        (sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
          sexticReciprocityPhase a b) *
        idealRowHom h (Ideal.span {a}) * star (idealRowHom (-h) (Ideal.span {b})) := by ring
    _ = _ := by
      rw [he]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring

end SevenEighths.CenteredMomentFixedRay

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ChildRows -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildRows
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily HeckeRowClosure
open CenteredMomentFixedRay RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def childCharacter (η : Character) (χ : RayCharacter) : Character :=
  η.product (primaryRayCharacter χ)

@[simp] theorem childCharacter_modulus (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus = η.modulus ⊓ Ideal.span {(12 : O)} := rfl

theorem childCharacter_primary (η : Character) (χ : RayCharacter) (n : O)
    (hn : Supported (Ideal.span {n})) (hp : λ₀^2 ∣ n - 1) :
    elementCoeff (childCharacter η χ) n = elementCoeff η n * rayCharacter χ n := by
  rw [childCharacter, elementCoeff_product, primaryRayCharacter_primary χ n hn hp]

theorem child_row_primary (η : Character) (χ : RayCharacter) (m A h n : O)
    (hn : Supported (Ideal.span {n})) (hp : λ₀^2 ∣ n - 1) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n =
      (elementCoeff η n * rayCharacter χ n) * coprimalityMask m n *
        idealRowHom (A*h) (Ideal.span {n}) := by
  rw [rowTwist_extract_sixth_mask _ m 1 (A*h) n hn]
  change elementCoeff (childCharacter η χ) n * _ * _ = _
  rw [childCharacter_primary η χ n hn hp]
  simp only [one_pow, one_mul]

theorem child_row_extract (η : Character) (χ : RayCharacter) (m A h e n : O) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) (e*n) =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) e *
        rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n := map_mul _ _ _

theorem exists_child_row_character (η : Character) (χ : RayCharacter) (m A h : O)
    (hm : m ≠ 0) (hA : A ≠ 0) (hh : h ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ ρ : Character, ∀ n, elementCoeff ρ n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n :=
  exists_row_character (childCharacter η χ) m 1 (A*h) hm one_ne_zero (mul_ne_zero hA hh) hmLam hm2

theorem old_coefficient_nonzero_coprime (η : Character) (e : O)
    (he : elementCoeff η e ≠ 0) : IsCoprime (Ideal.span {e}) η.modulus :=
  (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp he)

theorem old_coefficient_prime_coprime (η : Character) (e : O)
    (he : elementCoeff η e ≠ 0) (P : Ideal O) (hP : P ∣ Ideal.span {e}) :
    IsCoprime η.modulus P :=
  (old_coefficient_nonzero_coprime η e he).symm.of_isCoprime_of_dvd_right hP

theorem childCharacter_coprime (η : Character) (χ : RayCharacter) (Q P : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) (hQP : IsCoprime Q P)
    (hηP : IsCoprime η.modulus P) : IsCoprime (childCharacter η χ).modulus P := by
  have h12 : IsCoprime (Ideal.span {(12 : O)}) P :=
    hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr (hQ.trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6, by norm_num⟩)))
  rw [childCharacter_modulus]
  exact (hηP.mul_left h12).of_isCoprime_of_dvd_left
    (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)

theorem separated_exceptional_count (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A e : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (he : elementCoeff η e ≠ 0) (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors D,
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P ∧ P ∣ Ideal.span {e} ∧
        CenteredExceptionalCount.valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  apply CenteredExceptionalProfile.fixed_support_exceptional_count
    (childCharacter η χ) Q hQ0 hQ hQ72 m A hm hA hmLam hm2 T hT hex D hD
      ?_ Z C M F hZ hC hDnorm hN
  intro P hP
  obtain ⟨hg,h2,hQP,hPe,hval⟩ := hgood P hP
  exact ⟨hg,h2,hQP,childCharacter_coprime η χ Q P hQ72 hQP
    (old_coefficient_prime_coprime η e he P hPe),hval⟩

end SevenEighths.CenteredMomentChildRows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ExceptionalPair -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentExceptionalPair
open HeckeFamily CenteredExceptionalProfile CenteredMomentChildRows CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem idealCoeff_ne_zero_iff (χ : Character) (I : Ideal O) :
    idealCoeff χ I ≠ 0 ↔ I ≠ ⊥ ∧ IsCoprime I χ.modulus := by
  change (if I = ⊥ then 0 else χ.residue
    (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I))) ≠ 0 ↔ _
  by_cases hI : I = ⊥
  · simp only [hI,ite_true,ne_eq,not_true_eq_false,false_and]
  · rw [ite_eq_right hI]
    have he : χ.residue (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I)) ≠ 0 ↔
        IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator I)) := MulChar.apply_ne_zero_iff
    rw [IdealCharacter.isUnit_mk_iff_isCoprime,Ideal.span_singleton_generator] at he
    exact he.trans (and_iff_right hI).symm

theorem fixed_primitive_product (χ ψ τ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hψ : Q ≤ ψ.modulus) (hτ : Q ≤ τ.modulus) :
    ∃ ρ : Character, FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      Q ≤ ρ.modulus ∧ InducedBy (χ.product τ) ρ := by
  obtain ⟨ρ,hmod,hprim,hnorm,hmask⟩ := exists_primitive_product_character ψ τ
  refine ⟨ρ,hprim,(le_inf hψ hτ).trans hmod,?_⟩
  intro I
  by_cases hI : I = 0
  · simp only [hI,idealCoeff_zero,ite_self]
  by_cases hc : IsCoprime I (χ.product τ).modulus
  · have hn := (idealCoeff_ne_zero_iff (χ.product τ) I).mpr ⟨hI,hc⟩
    rw [idealCoeff_product] at hn
    have hχ := (idealCoeff_ne_zero_iff χ I).mp (left_ne_zero_of_mul hn) |>.2
    have he : idealCoeff χ I = idealCoeff ψ I := by rw [h I,ite_eq_left hχ]
    have hnψ : idealCoeff (ψ.product τ) I ≠ 0 := by
      rw [idealCoeff_product,← he]
      exact hn
    have hcψ := (idealCoeff_ne_zero_iff (ψ.product τ) I).mp hnψ |>.2
    change IsCoprime I (ψ.modulus ⊓ τ.modulus) at hcψ
    rw [ite_eq_left hc,idealCoeff_product,he,hmask I,ite_eq_left hcψ]
  · have hz : idealCoeff (χ.product τ) I = 0 := by
      by_contra hn
      exact hc ((idealCoeff_ne_zero_iff (χ.product τ) I).mp hn).2
    rw [hz,ite_eq_right hc]

theorem fixedInducingRow_of_product (η₁ η₂ τ : Character) (Q : Ideal O)
    (m A z₁ z₂ : O) (hτ : Q ≤ τ.modulus)
    (he : ∀ n, rowTwist (HeckeRowClosure.elementHom η₂) m 1 (A*z₂) n =
      rowTwist (HeckeRowClosure.elementHom η₁) m 1 (A*z₁) n * elementCoeff τ n)
    (hx : FixedInducingRow η₁ Q m A z₁) : FixedInducingRow η₂ Q m A z₂ := by
  obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hx
  obtain ⟨ρ,hρ,hQρ,hindρ⟩ := fixed_primitive_product χ ψ τ hind Q hQ hτ
  refine ⟨χ.product τ,ρ,hρ,hindρ,hQρ,?_⟩
  intro n
  rw [elementCoeff_product,hrow n,he n]

def rayRatio (χ ξ : RayCharacter) : Character :=
  (primaryRayCharacter χ).inverse.product (primaryRayCharacter ξ)

theorem childCharacter_ratio (η : Character) (χ ξ : RayCharacter) (n : O) :
    elementCoeff (childCharacter η ξ) n =
      elementCoeff (childCharacter η χ) n * elementCoeff (rayRatio χ ξ) n := by
  simp only [childCharacter,rayRatio,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsUnit (Ideal.Quotient.mk (Ideal.span {(12 : O)}) n)
  · have hχ : elementCoeff (primaryRayCharacter χ) n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr hn
    field_simp
  · have hz (ψ : RayCharacter) : elementCoeff (primaryRayCharacter ψ) n = 0 :=
      MulChar.map_nonunit _ hn
    rw [hz χ,hz ξ]
    ring

def reflectionRatio (χ ξ : RayCharacter) : Character :=
  (rayRatio χ ξ).product (HeckeUnitRows.character (-1 : Oˣ))

theorem reflectionRatio_modulus (χ ξ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) : Q ≤ (reflectionRatio χ ξ).modulus := by
  change Q ≤ ((Ideal.span {(12 : O)}) ⊓ (Ideal.span {(12 : O)})) ⊓ Ideal.span {(36 : O)}
  refine le_inf (le_inf ?_ ?_) ?_
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨6,by norm_num⟩)
  · exact hQ.trans (Ideal.span_singleton_le_span_singleton.mpr ⟨2,by norm_num⟩)

end SevenEighths.CenteredMomentExceptionalPair

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ExceptionalReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentExceptionalReflection
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CenteredMomentChildRows
open CenteredMomentFixedRay CenteredMomentExceptionalPair RayFourExpansion
open CanonicalRowCompletion CanonicalQuadraticSieve CanonicalUnitEuler
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem child_rows_zero_off_support (η : Character) (χ ξ : RayCharacter)
    (m A z n : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : ¬Supported (Ideal.span {n})) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n = 0 ∧
      rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n = 0 := by
  exact ⟨rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
    rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn⟩

theorem child_row_reflection (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) (n : O) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) n *
        elementCoeff (reflectionRatio χ ξ) n := by
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 (A*(-z)) n hn,
      rowTwist_extract_sixth_mask _ m 1 (A*z) n hn]
    simp only [one_pow, one_mul]
    change elementCoeff (childCharacter η ξ) n * coprimalityMask m n *
        idealRowHom (A*(-z)) (Ideal.span {n}) =
      (elementCoeff (childCharacter η χ) n * coprimalityMask m n *
        idealRowHom (A*z) (Ideal.span {n})) * elementCoeff (reflectionRatio χ ξ) n
    rw [childCharacter_ratio, reflectionRatio, elementCoeff_product,
      HeckeUnitRows.elementCoeff_character]
    have hu : unitSupplement (-1 : Oˣ) n = idealRowHom (-1) (Ideal.span {n}) := by
      change (if Supported (Ideal.span {n}) then
        idealRowHom ((-1 : Oˣ) : O) (Ideal.span {n}) else 0) = _
      rw [ite_eq_left hn]
      rfl
    rw [hu, show A*(-z) = (-1)*(A*z) by ring, idealRowHom_argument_mul]
    ring
  · obtain ⟨hleft, hright⟩ := child_rows_zero_off_support η χ ξ m A z n hmLam hm2 hn
    rw [hleft, hright, zero_mul]

theorem child_row_reflection_hom (η : Character) (χ ξ : RayCharacter)
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    rowTwist (elementHom (childCharacter η ξ)) m 1 (A*(-z)) =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*z) *
        elementHom (reflectionRatio χ ξ) := by
  ext n
  exact child_row_reflection η χ ξ m A z hmLam hm2 n

theorem fixedInducingRow_reflected (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hex : FixedInducingRow (childCharacter η χ) Q m A z) :
    FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  exact fixedInducingRow_of_product (childCharacter η χ) (childCharacter η ξ)
    (reflectionRatio χ ξ) Q m A z (-z) (reflectionRatio_modulus χ ξ Q hQ)
    (child_row_reflection η χ ξ m A z hmLam hm2) hex

theorem fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    FixedInducingRow (childCharacter η χ) Q m A z ↔
      FixedInducingRow (childCharacter η ξ) Q m A (-z) := by
  constructor
  · exact fixedInducingRow_reflected η χ ξ Q hQ m A z hmLam hm2
  · intro hex
    simpa only [neg_neg] using
      fixedInducingRow_reflected η ξ χ Q hQ m A (-z) hmLam hm2 hex

theorem not_fixedInducingRow_reflection_iff (η : Character) (χ ξ : RayCharacter)
    (Q : Ideal O) (hQ : Q ≤ Ideal.span {(72 : O)})
    (m A z : O) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    (¬FixedInducingRow (childCharacter η χ) Q m A z) ↔
      ¬FixedInducingRow (childCharacter η ξ) Q m A (-z) :=
  not_congr (fixedInducingRow_reflection_iff η χ ξ Q hQ m A z hmLam hm2)

end SevenEighths.CenteredMomentExceptionalReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Fourier -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

def frequencyReduction (d m : O) (h : d ∣ m) : Residue m →+* Residue d :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr h)

@[simp] theorem frequencyReduction_mk (d m : O) (h : d ∣ m) (x : O) :
    frequencyReduction d m h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem quotientTrace_scaled (d a m : O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    (h : Residue m) (x : Residue d) :
    quotientTrace m hm0 (h * scaledResidue d a m hm x) =
      quotientTrace d hd (frequencyReduction d m (hm ▸ dvd_mul_right d a) h * x) := by
  subst m
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht := quotientTrace_conductor_scale d a h hd ha (Ideal.Quotient.mk _ x)
  simp only [scaledResidue_mk, frequencyReduction_mk, ← map_mul]
  simpa only [← map_mul, conductorReduction, Ideal.Quotient.factor_mk, mul_assoc,
    mul_left_comm, mul_comm] using ht

def residueGauss (d : O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  ∑' x : Residue d, χ x * quotientTrace d hd (h * x)

theorem residueGauss_supported_mk (d : O)
    (hd : CanonicalQuadraticSieve.Supported (Ideal.span {d})) (h : O) :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

theorem fourierSum_scaled (d a m : O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    [Fintype (Residue d)] (χ : MulChar (Residue d) ℂ) (h : Residue m) :
    fourierSum (quotientTrace m hm0) (scaledResidue d a m hm) χ h =
      residueGauss d hd χ (frequencyReduction d m (hm ▸ dvd_mul_right d a) h) := by
  simp only [fourierSum, residueGauss, tsum_fintype, quotientTrace_scaled d a m hm hd ha hm0]

theorem actual_gauss_correlation (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    (∑ h : Residue (u * v),
      residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j))) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv j := by
  have h := fullModulusCorrelation_fourier u v χu χv j
    (quotientTrace (u * v) (mul_ne_zero hu hv))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive _ _)
  simp_rw [fourierSum_scaled u v (u * v) rfl hu hv (mul_ne_zero hu hv),
    fourierSum_scaled v u (u * v) (mul_comm u v) hv hu (mul_ne_zero hu hv)] at h
  exact h

def normalizedResidueGauss (d : O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  residueGauss d hd χ h / (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)

theorem normalized_gauss_correlation (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    fullModulusCorrelation u v χu χv j =
      ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))⁻¹ *
      ∑ h : Residue (u * v),
        normalizedResidueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
          star (normalizedResidueGauss v hv χv
            (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j)) := by
  let ru : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)
  let rv : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ)
  have hqu : (0 : ℝ) < Ideal.absNorm (Ideal.span {u}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hu))
  have hqv : (0 : ℝ) < Ideal.absNorm (Ideal.span {v}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hv))
  have hru : ru ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqu).ne'
  have hrv : rv ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqv).ne'
  have hsqu : ru ^ 2 = (Ideal.absNorm (Ideal.span {u}) : ℂ) := by
    dsimp only [ru]
    exact_mod_cast Real.sq_sqrt hqu.le
  have hsqv : rv ^ 2 = (Ideal.absNorm (Ideal.span {v}) : ℂ) := by
    dsimp only [rv]
    exact_mod_cast Real.sq_sqrt hqv.le
  have hcard : (Fintype.card (Residue (u * v)) : ℂ) = (ru * rv) ^ 2 := by
    have hc : Fintype.card (Residue (u * v)) = Ideal.absNorm (Ideal.span {u * v}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [hc, ← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul,
      ← hsqu, ← hsqv, mul_pow]
  have hterm (h : Residue (u * v)) :
      normalizedResidueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (normalizedResidueGauss v hv χv
          (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
        quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j)) =
      (residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
        quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j))) / (ru * rv) := by
    simp only [normalizedResidueGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
    dsimp only [ru, rv]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, actual_gauss_correlation u v hu hv χu χv j, hcard]
  change _ = (ru * rv)⁻¹ * ((ru * rv) ^ 2 * _ / (ru * rv))
  field_simp

end SevenEighths.CenteredMomentFourier
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.HeckeVolume -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentHeckeVolume
open HeckeFamily CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentPrimary CanonicalQuadraticSieve QuadraticInitialBound
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
open PrimaryIdealUnitReindex (GoodIdeal)
open CubicEisenstein (PrimaryLower primaryLowerIdealEquiv)
local notation "O" => ActualEisensteinCubic.O

def primaryCoefficient (ψ : Character) : Ideal O →* ℂ where
  toFun I := if primaryGenerator I=0 then 0 else idealCoeff ψ I
  map_one' := by simp only [primaryGenerator_one,one_ne_zero,ite_false,map_one]
  map_mul' := by
    intro I J
    simp only [primaryGenerator_mul,map_mul]
    by_cases hI : primaryGenerator I=0 <;> by_cases hJ : primaryGenerator J=0 <;>
      simp only [hI,hJ,mul_eq_zero,or_false,ite_true,ite_false,zero_mul,mul_zero]

theorem primaryCoefficient_good (ψ : Character) (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    primaryCoefficient ψ I = elementCoeff ψ (primaryGenerator I) := by
  change (if primaryGenerator I=0 then 0 else idealCoeff ψ I)=_
  rw [ite_eq_right hI]
  conv_lhs => rw [← (primaryGenerator_spec I hI).1,idealCoeff_span ψ hI]

theorem primaryCoefficient_norm (ψ : Character) (I : Ideal O) : ‖primaryCoefficient ψ I‖ ≤ 1 := by
  change ‖if primaryGenerator I=0 then 0 else idealCoeff ψ I‖ ≤ 1
  split_ifs
  · simp only [norm_zero,zero_le_one]
  · exact idealCoeff_norm_le_one ψ I

def periodicValue (c : O) (ψ : Character) (r : O ⧸ Ideal.span {c}) : ℂ :=
  if (3:O) ∣ Quotient.out r-1 then elementCoeff ψ (Quotient.out r) else 0

theorem periodicValue_mk (c : O) (h3 : (3:O) ∣ c) (ψ : Character)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus) (x : O) :
    periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) x) =
      if (3:O) ∣ x-1 then elementCoeff ψ x else 0 := by
  have hc : c ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-x :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk _ x)))
  have hd := h3.trans hc
  have hprimary : (3:O) ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)-1 ↔ (3:O) ∣ x-1 := by
    constructor
    · intro h; convert dvd_sub h hd using 1 ; ring
    · intro h; convert dvd_add hd h using 1 ; ring
  have hres : Ideal.Quotient.mk ψ.modulus (Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) x)) =
      Ideal.Quotient.mk ψ.modulus x :=
    Ideal.Quotient.eq.mpr (hmod (Ideal.mem_span_singleton.mpr hc))
  simp only [periodicValue,hprimary,elementCoeff,hres]

theorem periodicValue_norm (c : O) (ψ : Character) (r : O ⧸ Ideal.span {c}) :
    ‖periodicValue c ψ r‖ ≤ 1 := by
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  let : Fintype (O ⧸ ψ.modulus) := Fintype.ofFinite _
  unfold periodicValue
  split_ifs
  · exact norm_finite_character_le_one ψ.residue _
  · simp only [norm_zero,zero_le_one]

theorem lattice_eq_ideal_sum (c : O) (h3 : (3:O) ∣ c) (ψ : Character)
    (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus) (W : ℝ → ℂ) (X : ℝ) :
    (∑' z : O, periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X)) =
      ∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
  let f : O → ℂ := fun z => elementCoeff ψ z*W (‖eisEmbedding z‖^2/X)
  have hleft : (∑' z : O, periodicValue c ψ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X)) =
      ∑' z : PrimaryLower, f z.val := by
    calc
      _ = ∑' z : O, ({z : O | (3:O) ∣ z-1} : Set O).indicator f z := by
        apply tsum_congr
        intro z
        rw [periodicValue_mk c h3 ψ hmod z]
        simp only [Set.indicator_apply,Set.mem_ofPred_eq,f]
        split_ifs <;> simp only [zero_mul]
      _ = _ := (tsum_subtype {z : O | (3:O) ∣ z-1} f).symm
  have hideal : (∑' I : GoodIdeal, primaryCoefficient ψ I.val*W ((Ideal.absNorm I.val:ℝ)/X)) =
      ∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X) := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryGenerator I ≠ 0})
      (f := fun I : Ideal O => primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X))
    intro I hI
    change primaryGenerator I ≠ 0
    intro hz
    apply hI
    simp only [primaryCoefficient,MonoidHom.coe_mk,OneHom.coe_mk,hz,ite_true,zero_mul]
  rw [hleft,← hideal,← primaryLowerIdealEquiv.symm.tsum_eq]
  apply tsum_congr
  intro I
  change elementCoeff ψ (primaryGenerator I.val)*W (‖eisEmbedding (primaryGenerator I.val)‖^2/X)=_
  rw [primaryGenerator_norm_sq I.val I.property,primaryCoefficient_good ψ I.val I.property]

theorem fixed_period_volume (c : O) (hc : c ≠ 0) (h3 : (3:O) ∣ c)
    (ψ : Character) (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0 < X) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' I : Ideal O, primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X/‖eisEmbedding c‖^2:ℝ) • ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r)*paperRadialFourier W 0)‖ ≤
      (Fintype.card (O ⧸ Ideal.span {c}):ℝ)*pvControl W := by
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [← lattice_eq_ideal_sum c h3 ψ hmod W X]
  have h := CenteredMomentLattice.periodic_lattice_volume_error W X hX c hc (periodicValue c ψ)
  exact h.trans (mul_le_mul_of_nonneg_right (by
    calc
      _ ≤ ∑ _r : O ⧸ Ideal.span {c}, (1:ℝ) := Finset.sum_le_sum (fun r hr => periodicValue_norm c ψ r)
      _ = _ := by simp) (pvControl_nonneg W))

theorem masked_hecke_volume
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    (ψ : Character) (hmod : (Ideal.span {c} : Ideal O) ≤ ψ.modulus)
    (R : Ideal O) (hR : R ≠ 0) (W : 𝓢(ℝ, ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W : ℝ → ℂ) ⊆ Set.Iic b) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let Ψ := primaryCoefficient ψ
    let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
      ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperRadialFourier W 0)
    ‖(∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
      (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v‖ ≤
      ((idealDivisors R).card : ℝ) *
        ((Fintype.card (O ⧸ Ideal.span {c}) : ℝ) * pvControl W) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let Ψ := primaryCoefficient ψ
  let v := (1 / (‖eisEmbedding c‖ ^ 2 : ℂ)) *
    ((∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r) * paperRadialFourier W 0)
  let B := (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) * pvControl W
  let L : ℝ → ℂ := fun Y => ∑' I : Ideal O, Ψ I * W ((Ideal.absNorm I : ℝ) / Y)
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (pvControl_nonneg W)
  have hnD (D : Ideal O) (hD : D ∈ idealDivisors R) : 0 < (Ideal.absNorm D : ℝ) := by
    have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsingle (D : Ideal O) (hD : D ∈ idealDivisors R) :
      ‖L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v‖ ≤ B := by
    have h := fixed_period_volume c hc h3 ψ hmod W
      (X / Ideal.absNorm D) (div_pos hX (hnD D hD))
    convert h using 1
    congr 1
    dsimp only [v]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    ring
  have hcoef (D : Ideal O) : ‖(moebius D : ℂ) * Ψ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (primaryCoefficient_norm ψ D) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have heq :
      (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (Ψ I * W ((Ideal.absNorm I : ℝ) / X))) -
        (X : ℂ) * (∑ D ∈ idealDivisors R, (moebius D : ℂ) * Ψ D / (Ideal.absNorm D : ℂ)) * v =
      ∑ D ∈ idealDivisors R, ((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v) := by
    rw [masked_plain_ideal_sum R hR Ψ W b X hX hs]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro D _
    simp only [L, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  change ‖_ - (X : ℂ) * _ * v‖ ≤ ((idealDivisors R).card : ℝ) * B
  rw [heq]
  calc
    _ ≤ ∑ D ∈ idealDivisors R, ‖((moebius D : ℂ) * Ψ D) *
        (L (X / Ideal.absNorm D) - ((X / Ideal.absNorm D : ℝ) : ℂ) * v)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ idealDivisors R, B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul (hcoef D) (hsingle D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

def fixedPeriod (Q : Ideal O) : O := 3*ConcretePrimeRowBridge.idealGenerator Q

theorem fixedPeriod_ne_zero (Q : Ideal O) (hQ : Q ≠ 0) : fixedPeriod Q ≠ 0 :=
  mul_ne_zero (by norm_num) (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)

theorem fixedPeriod_three (Q : Ideal O) : (3:O) ∣ fixedPeriod Q := dvd_mul_right _ _

theorem span_fixedPeriod_le (Q : Ideal O) : (Ideal.span {fixedPeriod Q} : Ideal O) ≤ Q := by
  conv_rhs => rw [← ConcretePrimeRowBridge.span_idealGenerator Q]
  exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

theorem inducedBy_of_elementCoeff_eq (χ χ' ψ : Character)
    (heq : ∀ n, elementCoeff χ' n=elementCoeff χ n)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) :
    CenteredExceptionalProfile.InducedBy χ' ψ := by
  have hideal (I : Ideal O) : idealCoeff χ' I=idealCoeff χ I := by
    by_cases hI : I=0
    · simp only [hI,map_zero]
    · conv_lhs => rw [← ConcretePrimeRowBridge.span_idealGenerator I,
        idealCoeff_span χ' (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),heq]
      rw [← idealCoeff_span χ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
        ConcretePrimeRowBridge.span_idealGenerator]
  intro I
  by_cases hI : I=0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    rw [hideal I] at hn
    have hc' := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc,hideal I,hind I,ite_eq_left hc']
  · have hz : idealCoeff χ' I=0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    rw [ite_eq_right hc,hz]

theorem fixedInducingRow_controlled (η : Character) (Q : Ideal O) (m A₀ z : O)
    (hm : m ≠ 0) (hA : A₀ ≠ 0) (hz : z ≠ 0)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hex : CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z) :
    ∃ χ ψ : Character,
      χ.modulus.absNorm ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      CenteredExceptionalProfile.InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
      ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A₀*z) n := by
  obtain ⟨χ₀,ψ,hprim,hind,hQ,hrow₀⟩ := hex
  obtain ⟨χ,hbound,hrow⟩ := HeckeRowClosure.exists_row_character_with_conductor
    η m 1 (A₀*z) hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2
  refine ⟨χ,ψ,hbound,hprim,?_,hQ,hrow⟩
  exact inducedBy_of_elementCoeff_eq χ₀ χ ψ (fun n => (hrow n).trans (hrow₀ n).symm) hind

theorem induced_primaryCoefficient (χ ψ : Character)
    (hind : CenteredExceptionalProfile.InducedBy χ ψ) (I : Ideal O) :
    primaryCoefficient χ I =
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I := by
  change (if primaryGenerator I=0 then 0 else idealCoeff χ I)=
    (if IsCoprime I χ.modulus then (1:ℂ) else 0)*(if primaryGenerator I=0 then 0 else idealCoeff ψ I)
  rw [hind I]
  split_ifs <;> simp only [one_mul,zero_mul]

theorem primaryCoefficient_actual_row (η χ : Character) (m A₀ z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (I : Ideal O) :
    primaryCoefficient χ I=idealCoeff χ I := by
  change (if primaryGenerator I=0 then 0 else idealCoeff χ I)=_
  by_cases hI : I=0
  · simp only [hI,primaryGenerator_zero,map_zero,ite_self]
  by_cases hg : primaryGenerator I=0
  · rw [ite_eq_left hg]
    let n := ConcretePrimeRowBridge.idealGenerator I
    have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
    have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
    have hbad : ¬Supported (Ideal.span {n}) := by
      intro h
      have hp : primaryGenerator (Ideal.span {n}) ≠ 0 :=
        PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff n |>.mpr ((CanonicalQuadraticSieve.supported_span_iff n).mp h).1
      exact hp (hs ▸ hg)
    rw [← hs,idealCoeff_span χ hn,hrow,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hbad]
  · rw [ite_eq_right hg]

def density (c : O) (hc : c ≠ 0) (ψ : Character) (R : Ideal O) : ℂ :=
  letI := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  (∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)) *
    (1/(‖eisEmbedding c‖^2:ℂ))*(∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r)

theorem density_norm_le (c : O) (hc : c ≠ 0) (ψ : Character) (R : Ideal O) (hR : R ≠ 0) :
    ‖density c hc ψ R‖ ≤
      ((idealDivisors R).card:ℝ)*(Nat.card (O ⧸ Ideal.span {c}):ℝ)/‖eisEmbedding c‖^2 := by
  let := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hdiv : ‖∑ D ∈ idealDivisors R, (moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)‖ ≤
      ((idealDivisors R).card:ℝ) := by
    calc
      _ ≤ ∑ D ∈ idealDivisors R, ‖(moebius D:ℂ)*primaryCoefficient ψ D/(Ideal.absNorm D:ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _D ∈ idealDivisors R, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
        have hN : (1:ℝ) ≤ Ideal.absNorm D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD0)
        rw [norm_div,norm_mul,Complex.norm_natCast]
        apply (div_le_one (by linarith : 0 < (Ideal.absNorm D:ℝ))).mpr
        exact ((mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one D)).trans
          (primaryCoefficient_norm ψ D)).trans hN
      _ = _ := by simp
  have hres : ‖∑ r : O ⧸ Ideal.span {c}, periodicValue c ψ r‖ ≤
      (Nat.card (O ⧸ Ideal.span {c}):ℝ) := by
    calc
      _ ≤ ∑ r : O ⧸ Ideal.span {c}, ‖periodicValue c ψ r‖ := norm_sum_le _ _
      _ ≤ ∑ _r : O ⧸ Ideal.span {c}, (1:ℝ) := Finset.sum_le_sum (fun r hr => periodicValue_norm c ψ r)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  unfold density
  rw [norm_mul,norm_mul,norm_div,norm_one,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ (((idealDivisors R).card:ℝ)*(1/‖eisEmbedding c‖^2))*(Nat.card (O ⧸ Ideal.span {c}):ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hdiv (by positivity)) hres (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_induced_volume (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : 𝓢(ℝ,ℂ)) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Iic b) :
    ‖(∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)) -
      (X:ℂ)*(density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W 0)‖ ≤
      ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W := by
  let := finite_quotient_span (fixedPeriod_ne_zero Q hQ)
  let : Fintype (O ⧸ Ideal.span {fixedPeriod Q}) := Fintype.ofFinite _
  have h := masked_hecke_volume (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ)
    (fixedPeriod_three Q) ψ ((span_fixedPeriod_le Q).trans hQψ)
    χ.modulus χ.modulus_ne_bot W b X hX hs
  have he (I : Ideal O) :
      (if IsCoprime I χ.modulus then (1:ℂ) else 0)*primaryCoefficient ψ I=idealCoeff χ I := by
    rw [← induced_primaryCoefficient χ ψ hind I,primaryCoefficient_actual_row η χ m A₀ z hmLam hm2 hrow I]
  simp_rw [show ∀ I : Ideal O, (if IsCoprime I χ.modulus then (1:ℂ) else 0)*
      (primaryCoefficient ψ I*W ((Ideal.absNorm I:ℝ)/X)) =
        idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X) by intro I; rw [← mul_assoc,he]] at h
  convert h using 1
  · congr 1
    unfold density
    ring
  · rw [Nat.card_eq_fintype_card]
    ring

end SevenEighths.CenteredMomentHeckeVolume

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.MaskDescent -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.HeckeMaskDescent
open HeckeFamily CenteredExceptionalProfile CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem exists_coprime_shift (a c r : O) (hac : IsCoprime a c) (hr : r ≠ 0) :
    ∃ t : O, IsCoprime (a+t*c) r := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := (normalizedFactors r).filter (fun p => ¬p ∣ a)
  refine ⟨s.prod, IsCoprime.symm ?_⟩
  apply isCoprime_of_prime_dvd (by rintro ⟨h,-⟩; exact hr h)
  intro p hp hpr hpnew
  by_cases hpa : p ∣ a
  · have hpc : ¬p ∣ c := fun h => hp.not_isUnit (hac.isUnit_of_dvd' hpa h)
    have hps : ¬p ∣ s.prod := by
      intro h
      obtain ⟨q,hq,hpq⟩ := hp.exists_mem_multiset_dvd h
      obtain ⟨hqr,hqa⟩ := Multiset.mem_filter.mp hq
      exact hqa ((hp.associated_of_dvd (prime_of_normalized_factor q hqr) hpq).dvd'.trans hpa)
    have ht : p ∣ s.prod*c := by convert dvd_sub hpnew hpa using 1 ; ring
    exact (hp.dvd_or_dvd ht).elim hps hpc
  · obtain ⟨q,hq,hpq⟩ := exists_mem_normalizedFactors_of_dvd hr hp.irreducible hpr
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,fun h => hpa (hpq.dvd.trans h)⟩
    have ht : p ∣ s.prod*c := dvd_mul_of_dvd_left (hpq.dvd.trans (Multiset.dvd_prod hqs)) c
    exact hpa (by convert dvd_sub hpnew ht using 1 ; ring)

theorem exists_primitive_above (χ : Character) (Q : Ideal O)
    (hdesc : FiniteConductor.FactorsThroughIdeal χ.residue
      (Q.map (Ideal.Quotient.mk χ.modulus))) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨K,φ,hMK,hQK,hK,hprim,hnorm,hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation_above_quotient
      χ.modulus χ.residue (Q.map (Ideal.Quotient.mk χ.modulus)) hdesc
  have hu : IdealCharacter.UnitInvariant K φ := by
    intro u
    have h := hmask (u : O)
    simpa only [χ.unit_trivial u,u.isUnit.map (Ideal.Quotient.mk χ.modulus),ite_true] using h.symm
  refine ⟨Character.ofResidue K hK φ hu,hprim,?_,?_⟩
  · exact (Ideal.le_comap_map).trans hQK
  · exact IdealCharacter.ofResidue_source_mask χ.modulus K χ.residue φ χ.unit_trivial hu hmask

theorem descent_of_mask (χ χ' ψ : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ' ψ) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (ψ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a : O := 1+q
  have ha : Ideal.Quotient.mk χ.modulus a = (u : O ⧸ χ.modulus) := by
    dsimp [a];rw [map_add,map_one,hqu];ring
  have hψa : Ideal.Quotient.mk ψ.modulus a = 1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  let c := idealGenerator (χ.modulus*ψ.modulus)
  have hc : IsCoprime a c := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [show Ideal.span {c}=χ.modulus*ψ.modulus from span_idealGenerator _]
    apply IsCoprime.mul_right
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
    · exact (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hψa ▸ isUnit_one)
  obtain ⟨t,htall⟩ := exists_coprime_shift a c (r*goodLambda) hc
    (mul_ne_zero hr goodLambda_prime.ne_zero)
  have ht := htall.of_mul_right_left
  let n := a+t*c
  have hmem : c ∈ χ.modulus*ψ.modulus := by
    rw [← span_idealGenerator (χ.modulus*ψ.modulus)]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hnχ : Ideal.Quotient.mk χ.modulus n = (u : O ⧸ χ.modulus) := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_left hmem),mul_zero,add_zero,ha]
  have hnψ : Ideal.Quotient.mk ψ.modulus n = 1 := by
    dsimp [n];rw [map_add,map_mul,Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_right hmem),mul_zero,add_zero,hψa]
  have hnχ' : elementCoeff χ' n ≠ 0 := by
    rw [he n,ite_eq_left ht]
    exact MulChar.apply_ne_zero_iff.mpr (hnχ ▸ u.isUnit)
  have hn0 : n ≠ 0 := by
    intro hz
    have hunit : IsUnit goodLambda := (htall.of_mul_right_right).isUnit_of_dvd'
      (by change goodLambda ∣ n; rw [hz]; exact dvd_zero _) (dvd_refl _)
    exact goodLambda_prime.not_isUnit hunit
  have hcop : IsCoprime (Ideal.span {n}) χ'.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hnχ')
  have heq := elementCoeff_eq_of_inducedBy χ' ψ hind n hn0 hcop
  rw [he n,ite_eq_left ht] at heq
  change χ.residue (Ideal.Quotient.mk χ.modulus n) = ψ.residue (Ideal.Quotient.mk ψ.modulus n) at heq
  simpa only [hnχ,hnψ,map_one] using heq

theorem inducedBy_mask (χ χ' ψ : Character) (r : O)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0)
    (hind : InducedBy χ ψ) : InducedBy χ' ψ := by
  intro I
  by_cases hI : I = 0
  · simp only [hI,map_zero,ite_self]
  by_cases hc : IsCoprime I χ'.modulus
  · have hn' := CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I |>.mpr ⟨hI,hc⟩
    let n := idealGenerator I
    have hn0 : n ≠ 0 := idealGenerator_ne_zero I hI
    have hspan : Ideal.span {n} = I := span_idealGenerator I
    have hval' : elementCoeff χ' n = idealCoeff χ' I := by
      rw [← idealCoeff_span χ' hn0,hspan]
    have hval : elementCoeff χ n = idealCoeff χ I := by
      rw [← idealCoeff_span χ hn0,hspan]
    have hm := he n
    have hcr : IsCoprime n r := by
      by_contra hr
      rw [ite_eq_right hr,hval'] at hm
      exact hn' hm
    rw [ite_eq_left hcr,hval',hval] at hm
    have hn := hm ▸ hn'
    have hcχ := (CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn |>.2
    rw [ite_eq_left hc,hm,hind I,ite_eq_left hcχ]
  · have hz : idealCoeff χ' I = 0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ' I).mp hn).2
    rw [ite_eq_right hc,hz]

theorem fixed_inducing_mask_iff (χ χ' : Character) (r : O) (hr : r ≠ 0)
    (he : ∀ n, elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0) (Q : Ideal O) :
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ' ψ) ↔
    (∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      Q ≤ ψ.modulus ∧ InducedBy χ ψ) := by
  constructor
  · rintro ⟨ψ,hprim,hQ,hind⟩
    obtain ⟨ρ,hρ,hmod,hindρ⟩ := exists_primitive_above χ ψ.modulus
      (descent_of_mask χ χ' ψ r hr he hind)
    exact ⟨ρ,hρ,hQ.trans hmod,hindρ⟩
  · rintro ⟨ψ,hprim,hQ,hind⟩
    exact ⟨ψ,hprim,hQ,inducedBy_mask χ χ' ψ r he hind⟩
end SevenEighths.HeckeMaskDescent

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FixedRowMask -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRowMask
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem row_mask_mul (η : Character) (m r A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom η) (m*r) 1 (A*z) n =
      if IsCoprime n r then rowTwist (elementHom η) m 1 (A*z) n else 0 := by
  by_cases hs : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ _ _ _ _ hs,
      rowTwist_extract_sixth_mask _ _ _ _ _ hs]
    change elementHom η n * (if IsCoprime (m*r) n then (1:ℂ) else 0) * _ = _
    rw [IsCoprime.mul_left_iff]
    by_cases hm : IsCoprime m n <;> by_cases hr : IsCoprime n r <;>
      simp [coprimalityMask,hm,hr,show IsCoprime r n ↔ IsCoprime n r from isCoprime_comm]
  · rw [rowTwist_zero_of_not_supported _ _ _ _ _
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) hs,
      rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hs]
    split_ifs <;> rfl

theorem fixedInducingRow_mul_mask_iff (η : Character) (Q : Ideal O)
    (m r A z : O) (hm : m ≠ 0) (hr : r ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow η Q (m*r) A z ↔ FixedInducingRow η Q m A z := by
  obtain ⟨χ,hχ⟩ := exists_row_character η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  obtain ⟨χ',hχ'⟩ := exists_row_character η (m*r) 1 (A*z) (mul_ne_zero hm hr)
    one_ne_zero (mul_ne_zero hA hz) (hmLam.trans (dvd_mul_right _ _))
      (hm2.trans (dvd_mul_right _ _))
  have hmask (n : O) : elementCoeff χ' n =
      if IsCoprime n r then elementCoeff χ n else 0 := by
    rw [hχ' n,hχ n,row_mask_mul η m r A z n hmLam hm2]
  have transport (ρ : Character) (mask : O)
      (hρ : ∀ n,elementCoeff ρ n=rowTwist (elementHom η) mask 1 (A*z) n) :
      FixedInducingRow η Q mask A z ↔
        ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
          Q ≤ ψ.modulus ∧ InducedBy ρ ψ := by
    constructor
    · rintro ⟨ρ₀,ψ,hprim,hind,hQ,hρ₀⟩
      exact ⟨ψ,hprim,hQ,CenteredMomentHeckeVolume.inducedBy_of_elementCoeff_eq
        ρ₀ ρ ψ (fun n => (hρ n).trans (hρ₀ n).symm) hind⟩
    · rintro ⟨ψ,hprim,hQ,hind⟩
      exact ⟨ρ,ψ,hprim,hind,hQ,hρ⟩
  rw [transport χ' (m*r) hχ',transport χ m hχ]
  exact HeckeMaskDescent.fixed_inducing_mask_iff χ χ' r hr hmask Q
end SevenEighths.CenteredMomentFixedRowMask

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FixedRayInducingTransport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedRayInducingTransport
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile
open CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentExceptionalPair CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O

theorem modulus_generator_ne_zero (ν : Character) :
    idealGenerator ν.modulus ≠ 0 :=
  idealGenerator_ne_zero ν.modulus ν.modulus_ne_bot

theorem modulus_unit_iff (ν : Character) (n : O) :
    IsUnit (Ideal.Quotient.mk ν.modulus n) ↔
      IsCoprime n (idealGenerator ν.modulus) := by
  rw [IdealCharacter.isUnit_mk_iff_isCoprime]
  conv_lhs => rw [←span_idealGenerator ν.modulus]
  rw [Ideal.isCoprime_span_singleton_iff]

theorem elementCoeff_product_inverse_mask (η ν : Character) (n : O) :
    elementCoeff ((η.product ν).product ν.inverse) n =
      if IsCoprime n (idealGenerator ν.modulus) then elementCoeff η n else 0 := by
  rw [elementCoeff_product,elementCoeff_product,elementCoeff_inverse]
  by_cases hn : IsCoprime n (idealGenerator ν.modulus)
  · have hv : elementCoeff ν n ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr ((modulus_unit_iff ν n).mpr hn)
    simp only [hn,ite_true,mul_assoc,mul_inv_cancel₀ hv,mul_one]
  · have hv : elementCoeff ν n = 0 :=
      MulChar.map_nonunit ν.residue (fun hu=>hn ((modulus_unit_iff ν n).mp hu))
    simp only [hn,ite_false,hv,mul_zero,zero_mul]

theorem rowTwist_product (η ν : Character) (m f z n : O) :
    rowTwist (elementHom (η.product ν)) m f z n =
      rowTwist (elementHom η) m f z n * elementCoeff ν n := by
  change elementCoeff (η.product ν) n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) * elementCoeff ν n
  rw [elementCoeff_product]
  ring

theorem rowTwist_product_inverse_mask (η ν : Character) (m A z n : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    rowTwist (elementHom ((η.product ν).product ν.inverse)) m 1 (A*z) n =
      rowTwist (elementHom η) (m*idealGenerator ν.modulus) 1 (A*z) n := by
  rw [row_mask_mul η m (idealGenerator ν.modulus) A z n hmLam hm2]
  change elementCoeff ((η.product ν).product ν.inverse) n *
    idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n}) = _
  rw [elementCoeff_product_inverse_mask]
  split_ifs
  · rfl
  · exact zero_mul _

theorem fixedInducingRow_product_of (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (h : FixedInducingRow η Q m A z) :
    FixedInducingRow (η.product ν) Q m A z :=
  fixedInducingRow_of_product η (η.product ν) ν Q m A z z hν
    (fun n=>rowTwist_product η ν m 1 (A*z) n) h

theorem fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν) Q m A z ↔ FixedInducingRow η Q m A z := by
  constructor
  · intro h
    have hi := fixedInducingRow_product_of (η.product ν) ν.inverse Q m A z hν h
    obtain ⟨χ,ψ,hprim,hind,hQ,hrow⟩ := hi
    apply (fixedInducingRow_mul_mask_iff η Q m (idealGenerator ν.modulus) A z
      hm (modulus_generator_ne_zero ν) hA hz hmLam hm2).mp
    exact ⟨χ,ψ,hprim,hind,hQ,fun n=>(hrow n).trans
      (rowTwist_product_inverse_mask η ν m A z n hmLam hm2)⟩
  · exact fixedInducingRow_product_of η ν Q m A z hν

theorem not_fixedInducingRow_product_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_iff η ν Q m A z hν hm hA hz hmLam hm2)

theorem fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    FixedInducingRow (η.product ν.inverse) Q m A z ↔ FixedInducingRow η Q m A z :=
  fixedInducingRow_product_iff η ν.inverse Q m A z hν hm hA hz hmLam hm2

theorem not_fixedInducingRow_product_inverse_iff (η ν : Character) (Q : Ideal O)
    (m A z : O) (hν : Q ≤ ν.modulus)
    (hm : m≠0) (hA : A≠0) (hz : z≠0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) :
    (¬FixedInducingRow (η.product ν.inverse) Q m A z) ↔ ¬FixedInducingRow η Q m A z :=
  not_congr (fixedInducingRow_product_inverse_iff η ν Q m A z hν hm hA hz hmLam hm2)

end SevenEighths.CenteredMomentFixedRayInducingTransport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.HeckeCancellation -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentHeckeCancellation
open HeckeFamily CenteredMomentHeckeVolume ConcreteTraceCRT EisensteinSchwartzPoisson
open IdealMobiusDivisorSum QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

def idealSum (χ : Character) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X)

def volumeControl (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)*pvControl W

def densityControl (Q : Ideal O) (χ : Character) : ℝ :=
  ((idealDivisors χ.modulus).card:ℝ)*(Nat.card (O ⧸ Ideal.span {fixedPeriod Q}):ℝ)/‖eisEmbedding (fixedPeriod Q)‖^2

lemma volumeControl_nonneg (Q : Ideal O) (χ : Character) (W : 𝓢(ℝ,ℂ)) : 0 ≤ volumeControl Q χ W :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pvControl_nonneg W)

lemma densityControl_nonneg (Q : Ideal O) (χ : Character) : 0 ≤ densityControl Q χ := by
  unfold densityControl
  positivity

theorem actual_rectangle_saving (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b₁ b₂ : ℝ)
    (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Iic b₁)
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Iic b₂)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 1 ≤ L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁*X₂=T) (hprodY : Y₁*Y₂=T) :
    let E := volumeControl Q χ W₁+volumeControl Q χ W₂
    let C := densityControl Q χ*(‖paperRadialFourier W₁ 0‖+‖paperRadialFourier W₂ 0‖)+E
    ‖idealSum χ W₁ X₁*idealSum χ W₂ X₂-idealSum χ W₁ Y₁*idealSum χ W₂ Y₂‖ ≤
      4*E*C*(T/L) := by
  let E := volumeControl Q χ W₁+volumeControl Q χ W₂
  let D := densityControl Q χ
  let C := D*(‖paperRadialFourier W₁ 0‖+‖paperRadialFourier W₂ 0‖)+E
  let v₁ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W₁ 0
  let v₂ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus*paperRadialFourier W₂ 0
  have hE₁ := volumeControl_nonneg Q χ W₁
  have hE₂ := volumeControl_nonneg Q χ W₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hD : 0 ≤ D := densityControl_nonneg Q χ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hL0 : 0 < L := by linarith
  have hden : ‖density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus‖ ≤ D :=
    density_norm_le _ _ ψ χ.modulus χ.modulus_ne_bot
  have hvol₁ : ‖v₁‖ ≤ D*‖paperRadialFourier W₁ 0‖ := by
    dsimp only [v₁]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have hvol₂ : ‖v₂‖ ≤ D*‖paperRadialFourier W₂ 0‖ := by
    dsimp only [v₂]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hden (norm_nonneg _)
  have ha₁ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₁ X-(X:ℂ)*v₁‖ ≤ E :=
    (actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ b₁ X
      (lt_of_lt_of_le hL0 hX) hs₁).trans (le_add_of_nonneg_right hE₂)
  have ha₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₂ X-(X:ℂ)*v₂‖ ≤ E :=
    (actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₂ b₂ X
      (lt_of_lt_of_le hL0 hX) hs₂).trans (le_add_of_nonneg_left hE₁)
  have hv₁ (X : ℝ) (hX : L ≤ X) : ‖(X:ℂ)*v₁‖ ≤ C*X := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_trans hL0.le hX)]
    have hv : ‖v₁‖ ≤ C := by
      dsimp only [C]
      nlinarith [mul_nonneg hD (norm_nonneg (paperRadialFourier W₂ 0))]
    nlinarith [mul_le_mul_of_nonneg_right hv (le_trans hL0.le hX)]
  have hv₂ (X : ℝ) (hX : L ≤ X) : ‖idealSum χ W₂ X‖ ≤ C*X := by
    have hb := norm_le_norm_sub_add (idealSum χ W₂ X) ((X:ℂ)*v₂)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_trans hL0.le hX)] at hb
    have hEX : E ≤ E*X := by nlinarith [mul_le_mul_of_nonneg_left (le_trans hL hX) hE]
    have hbound := ha₂ X hX
    have hv := mul_le_mul_of_nonneg_left hvol₂ (le_trans hL0.le hX)
    dsimp only [C]
    nlinarith [mul_nonneg (mul_nonneg hD (norm_nonneg (paperRadialFourier W₁ 0))) (le_trans hL0.le hX)]
  have hmain : ((X₁:ℂ)*v₁)*((X₂:ℂ)*v₂)=((Y₁:ℂ)*v₁)*((Y₂:ℂ)*v₂) := by
    have hp : (X₁:ℂ)*X₂=(Y₁:ℂ)*Y₂ := by exact_mod_cast hprodX.trans hprodY.symm
    calc
      _ = ((X₁:ℂ)*X₂)*(v₁*v₂) := by ring
      _ = ((Y₁:ℂ)*Y₂)*(v₁*v₂) := by rw [hp]
      _ = _ := by ring
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (ha₁ X₁ hX₁) (ha₂ X₂ hX₂)
    (ha₁ Y₁ hY₁) (ha₂ Y₂ hY₂) (hv₂ X₂ hX₂) (hv₁ X₁ hX₁)
    (hv₂ Y₂ hY₂) (hv₁ Y₁ hY₁) hL0 hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentHeckeCancellation

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.HeckeTwist -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeTwist
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentLattice CenteredMomentCounting CenteredMomentTwist
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem idealSum_absolute (χ : Character) (W : ℝ → ℂ) (b M X : ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hX : 0 < X)
    (hW : ∀ y, ‖W y‖ ≤ M) (hs : Function.support W ⊆ Set.Iic b) :
    ‖idealSum χ W X‖ ≤ (128*b*M)*X := by
  have h := norm_tsum_ideal_ball (fun I => idealCoeff χ I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) M (mul_nonneg hb hX.le) hM (by change idealCoeff χ (0:Ideal O)*_ = 0; rw [map_zero,zero_mul])
    (by intro I; rw [norm_mul]; exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
    (by intro I hI; apply (div_le_iff₀ hX).mp; apply hs; intro hz; exact hI (by rw [hz,mul_zero]))
  change ‖idealSum χ W X‖ ≤ _ at h
  convert h using 1 ; ring

theorem twistedIdealSum_scale (χ : Character) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    twistedIdealSum χ W t X = (X : ℂ) ^ (Complex.I * t) *
      idealSum χ (normPowerProfile W a b ha hs hW t) X := by
  unfold twistedIdealSum idealSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [normPowerProfile_apply]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  rw [hphase]
  ring

theorem twistedIdealSum_volume (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖twistedIdealSum χ W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus *
        paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      volumeControl Q χ (normPowerProfile W a b ha hs hW t) := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus *
      paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
    (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) *
      (density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow _ b X hX
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twistedIdealSum_absolute (χ : Character) (W : ℝ → ℂ) (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t X : ℝ) (hX : 0 < X) :
    ‖twistedIdealSum χ W t X‖ ≤ (128 * b * M) * X := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,
    norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact idealSum_absolute χ _ b M X hb hM hX
    (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y))
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twisted_actual_volumeCoefficient_norm_le (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W : ℝ → ℂ) (a b M : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t : ℝ) :
    ‖density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      128 * b * M := by
  let V := normPowerProfile W a b ha hs hW t
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Iic b :=
    (normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2)
  exact norm_linear_coefficient_le (fun X => idealSum χ V X)
    _ (128 * b * M) (volumeControl Q χ V) (volumeControl_nonneg Q χ V)
    (fun X hX => actual_induced_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow V b X hX hV)
    (fun X hX => idealSum_absolute χ V b M X hb hM hX
      (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y)) hV)

theorem actual_twisted_rectangle_saving
    (η χ ψ : Character) (Q : Ideal O) (hQ : Q ≠ 0)
    (hQψ : Q ≤ ψ.modulus) (hind : CenteredExceptionalProfile.InducedBy χ ψ)
    (m A₀ z : O) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
      volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
    ‖twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
      twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂‖ ≤
      4 * E * (128 * (b₁ * M₁ + b₂ * M₂)) * (T / L) := by
  let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t
  let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t
  let E := volumeControl Q χ V₁ + volumeControl Q χ V₂
  let C := 128 * (b₁ * M₁ + b₂ * M₂)
  let v₁ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier V₁ 0
  let v₂ := density (fixedPeriod Q) (fixedPeriod_ne_zero Q hQ) ψ χ.modulus * paperRadialFourier V₂ 0
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hE₁ := volumeControl_nonneg Q χ V₁
  have hE₂ := volumeControl_nonneg Q χ V₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  have hC₁ : 128 * b₁ * M₁ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₂ hM₂]
  have hC₂ : 128 * b₂ * M₂ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₁ hM₁]
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₁ t X - m₁ X‖ ≤ E := by
    have h := twistedIdealSum_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ a₁ b₁ ha₁ hs₁ hW₁ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₁‖ ≤ E
    simpa only [v₁, mul_assoc] using h.trans (le_add_of_nonneg_right hE₂)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₂ t X - m₂ X‖ ≤ E := by
    have h := twistedIdealSum_volume η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₂ a₂ b₂ ha₂ hs₂ hW₂ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₂‖ ≤ E
    simpa only [v₂, mul_assoc] using h.trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (twisted_actual_volumeCoefficient_norm_le η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ a₁ b₁ M₁
      ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hL hX)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (le_trans hL.le hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedIdealSum χ W₂ t X‖ ≤ C * X :=
    (twistedIdealSum_absolute χ W₂ a₂ b₂ M₂ ha₂ hb₂ hM₂ hs₂ hW₂ hbound₂ t X
      (lt_of_lt_of_le hL hX)).trans (mul_le_mul_of_nonneg_right hC₂ (le_trans hL.le hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hpow := CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (le_trans hL.le hX₁) (le_trans hL.le hX₂)
      (le_trans hL.le hY₁) (le_trans hL.le hY₂) (hprodX.trans hprodY.symm)
    simpa only [CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hpow
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (he₁ X₁ hX₁) (he₂ X₂ hX₂)
    (he₁ Y₁ hY₁) (he₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentHeckeTwist

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.HeckeHeight -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeHeight
open HeckeFamily CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentHeckeTwist
open CenteredMomentLattice CenteredMomentMask CenteredMomentTwist CenteredMomentHeight
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem volumeControl_polynomial_height (Q : Ideal O) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ χ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      ∀ t : ℝ, volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨n, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hprofile⟩ := hn W hs hW
  let mass : ℝ := Nat.card (O ⧸ Ideal.span {fixedPeriod Q})
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  let A := D * mass * pvConstant * C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hC.le
  refine ⟨1 + A, by linarith, ?_⟩
  intro Z hZ χ hnorm t
  have hheight : (1 + ‖t / (2 * Real.pi)‖) ^ n ≤ (1 + ‖t‖) ^ n := by
    gcongr
    exact normalized_height_le t
  have hseminorm := (hprofile t).trans (mul_le_mul_of_nonneg_left hheight hC.le)
  have herr : volumeControl Q χ (normPowerProfile W a b ha hs hW t) ≤
      (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := by
    unfold volumeControl pvControl
    rw [mul_assoc]
    apply mul_le_mul (hdiv Z hZ χ.modulus χ.modulus_ne_bot hnorm)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseminorm pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := herr
    _ = A * Z ^ ε * (1 + ‖t‖) ^ n := by dsimp only [A]; ring
    _ ≤ (1 + A) * Z ^ ε * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A)
          (Real.rpow_nonneg (le_trans zero_le_one hZ) ε)) (by positivity)

theorem normalized_actual_rectangle_estimate
    (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ η χ ψ : Character, (Ideal.absNorm χ.modulus : ℝ) ≤ Z ^ B →
      (Q ≤ ψ.modulus) → CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A₀ z : O, (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) m 1 (A₀*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedIdealSum χ W₁ t X₁ * twistedIdealSum χ W₂ t X₂ -
          twistedIdealSum χ W₁ t Y₁ * twistedIdealSum χ W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨n₁, hn₁⟩ := volumeControl_polynomial_height Q a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := volumeControl_polynomial_height Q a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128 * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (D₁ + D₂) * V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ η χ ψ hnorm hQψ hind m A₀ z hmLam hm2 hrow t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := volumeControl Q χ (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    volumeControl Q χ (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ χ hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A₀ z hmLam hm2 hrow W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := CenteredMoment.normalized_centered_saving _ T L V E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * V * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * V *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (D₁ + D₂) * V) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

def rowTwistedSum (η : Character) (m A₀ z : O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A₀*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

theorem rowTwistedSum_eq (η χ : Character) (m A₀ z : O)
    (hrow : ∀ n, elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A₀*z) n)
    (W : ℝ → ℂ) (t X : ℝ) :
    rowTwistedSum η m A₀ z W t X=twistedIdealSum χ W t X := by
  apply tsum_congr
  intro I
  have he := HeckeRowClosure.idealCoeff_eq_row η χ m 1 (A₀*z) hrow I
  simp only [one_pow,mul_one] at he
  rw [he]

theorem exceptional_rectangle_estimate (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A₀ z : O),
      m ≠ 0 → A₀ ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A₀*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A₀ z →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A₀ z W₁ t X₁*rowTwistedSum η m A₀ z W₂ t X₂-
         rowTwistedSum η m A₀ z W₁ t Y₁*rowTwistedSum η m A₀ z W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,hJ⟩ := normalized_actual_rectangle_estimate Q hQ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A₀ z hm hA hz hmLam hm2 hcond hex t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  obtain ⟨χ,ψ,hχ,hprim,hind,hQψ,hrow⟩ := fixedInducingRow_controlled η Q m A₀ z hm hA hz hmLam hm2 hex
  have hχnorm : (Ideal.absNorm χ.modulus:ℝ) ≤ Z^B :=
    (show (Ideal.absNorm χ.modulus:ℝ) ≤ HeckeRowClosure.rowConductorBound η m 1 (A₀*z) by exact_mod_cast hχ).trans hcond
  simp_rw [rowTwistedSum_eq η χ m A₀ z hrow]
  exact hbound Z hZ η χ ψ hχnorm hQψ hind m A₀ z hmLam hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentHeckeHeight

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.HeckeSlots -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeSlots
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentCounting CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def rowSlot (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑ P ∈ S, β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
    (Ideal.absNorm P:ℂ)^(Complex.I*t)

theorem row_twisted_coefficient_norm (η : Character) (m A z : O) (t : ℝ)
    (P : Ideal O) (hP : P ≠ 0) :
    ‖(idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t)‖ ≤ 1 := by
  have hn : 0 < (Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  rw [norm_mul, norm_mul, show (Ideal.absNorm P:ℂ)=((Ideal.absNorm P:ℝ):ℂ) by simp,
    norm_real_imaginary_power _ t hn, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η P)).trans
    (CanonicalRowCompletion.idealRowHom_norm _ _)

theorem rowSlot_bound (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hβ : ∀ P ∈ S, ‖β P‖ ≤ M)
    (hN : ∀ P ∈ S, β P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H) :
    ‖rowSlot η m A z S β t‖ ≤ 128*M*H := by
  let f : Ideal O → ℂ := fun P => if P ∈ S then
    β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
      (Ideal.absNorm P:ℂ)^(Complex.I*t) else 0
  have hf0 : f 0=0 := by simp only [f, map_zero, zero_mul, mul_zero, ite_self]
  have hf : ∀ P, ‖f P‖ ≤ M := by
    intro P
    by_cases hP : P ∈ S
    · by_cases hP0 : P=0
      · rw [hP0,hf0,norm_zero]; exact hM
      · dsimp only [f]; rw [ite_eq_left hP, mul_assoc, norm_mul]
        exact (mul_le_mul (hβ P hP) (row_twisted_coefficient_norm η m A z t P hP0)
          (norm_nonneg _) hM).trans_eq (mul_one M)
    · simp only [f,ite_eq_right hP,norm_zero]; exact hM
  have hsup : ∀ P, f P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ H := by
    intro P hP
    have hm : P ∈ S := by by_contra hn; exact hP (by simp only [f,ite_eq_right hn])
    exact hN P hm (by intro hz; exact hP (by simp only [f,ite_eq_left hm,hz,zero_mul]))
  have he : (∑' P, f P)=rowSlot η m A z S β t := by
    rw [tsum_eq_sum (s := S) (fun P hP => by simp only [f,ite_eq_right hP])]
    unfold rowSlot
    exact Finset.sum_congr rfl (fun P hP => by simp only [f,ite_eq_left hP])
  rw [← he]
  exact norm_tsum_ideal_ball f H M hH hM hf0 hf hsup

variable {ι : Type*} [Fintype ι]

theorem whole_product_normalization (R : ℂ) (q : ι → ℂ) (k p : ι → ℝ)
    (D T L : ℝ) (hD : 0 ≤ D) (hT : 0 < T) (hL : 0 < L)
    (_hk : ∀ i, 0 ≤ k i) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, ‖q i‖ ≤ k i*p i)
    (hR : ‖(Real.sqrt T:ℂ)⁻¹*R‖ ≤ D*(Real.sqrt T/L)) :
    ‖(Real.sqrt (T*∏ i,p i):ℂ)⁻¹*(R*∏ i,q i)‖ ≤
      D*(∏ i,k i)*(Real.sqrt (T*∏ i,p i)/L) := by
  have hP : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => hp i)
  have hTP : 0 < T*∏ i,p i := mul_pos hT hP
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsTP : 0 < Real.sqrt (T*∏ i,p i) := Real.sqrt_pos.2 hTP
  have hQ : ‖∏ i,q i‖ ≤ (∏ i,k i)*(∏ i,p i) := by
    rw [norm_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hq i)
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsT.le] at hR
  have hR' : ‖R‖ ≤ D*T/L := by
    have h := mul_le_mul_of_nonneg_left hR hsT.le
    rw [← mul_assoc,mul_inv_cancel₀ hsT.ne',one_mul] at h
    have hs := Real.sq_sqrt hT.le
    convert h using 1
    calc
      D*T/L = D*(Real.sqrt T)^2/L := by rw [hs]
      _ = _ := by ring
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsTP.le,norm_mul]
  calc
    _ ≤ (Real.sqrt (T*∏ i,p i))⁻¹*((D*T/L)*((∏ i,k i)*(∏ i,p i))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hR' hQ (norm_nonneg _) (by positivity)) (inv_nonneg.mpr hsTP.le)
    _ = _ := by
      have hs := Real.sq_sqrt hTP.le
      field_simp
      rw [hs]

def centeredSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (p : ι → ℝ) (t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt (T*∏ i,p i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
      rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

theorem exceptional_slots_estimate (Q : Ideal O) (hQ : Q ≠ 0)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (η : Character) (m A z : O),
      m ≠ 0 → A ≠ 0 → z ≠ 0 →
      (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ) ≤ Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀ (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (p b M : ι → ℝ),
      (∀ i, 0 < p i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ P ∈ S i, ‖β i P‖ ≤ M i) →
      (∀ i, ∀ P ∈ S i, β i P ≠ 0 → (Ideal.absNorm P:ℝ) ≤ b i*p i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β p t X₁ X₂ Y₁ Y₂ T‖ ≤
        C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*M i)*(Real.sqrt (T*∏ i,p i)/L) := by
  obtain ⟨J,hJ⟩ := exceptional_rectangle_estimate Q hQ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ η m A z hm hA hz hmLam hm2 hcond hex S β p b M hp hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖ ≤ (128*b i*M i)*p i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*p i) (M i)
      (mul_nonneg (hb i) (hp i).le) (hM i) (hβ i) (hN i) using 1 ; ring
  exact whole_product_normalization _ (fun i => rowSlot η m A z (S i) (β i) t)
    (fun i => 128*b i*M i) p (C*Z^ε*(1+‖t‖)^J) T L
    (by positivity) hT hL (fun i => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hp hslots
    (hbound Z hZ η m A z hm hA hz hmLam hm2 hcond hex
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

end SevenEighths.CenteredMomentHeckeSlots

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.HeckeExpansion -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

def rowWeight (η : Character) (m A z : O) (t : ℝ) : Ideal O →*₀ ℂ where
  toFun I := (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)
  map_one' := by simp only [map_one,Nat.cast_one,Complex.one_cpow,one_mul]
  map_zero' := by simp only [map_zero,zero_mul,mul_zero]
  map_mul' I J := by
    have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t) =
        (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm I) : (0:ℝ) ≤ Ideal.absNorm I)
        (Nat.cast_nonneg (Ideal.absNorm J) : (0:ℝ) ≤ Ideal.absNorm J) (Complex.I*t)
    simp only [map_mul,Nat.cast_mul,hpow]
    ring

theorem rowTwistedSum_eq_weight (η : Character) (m A z : O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    rowTwistedSum η m A z W t X =
      ∑' I : Ideal O, rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := rfl

theorem rowSlot_eq_weight (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) :
    rowSlot η m A z S β t = ∑ P ∈ S, β P*rowWeight η m A z t P := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro P hP
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
  ring

theorem actual_hecke_rectangle_sum
    (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      rowTwistedSum η m A z W₁ t X₁ * rowTwistedSum η m A z W₂ t X₂ -
        rowTwistedSum η m A z W₁ t Y₁ * rowTwistedSum η m A z W₂ t Y₂ := by
  let w := rowWeight η m A z t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [map_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [rowTwistedSum_eq_weight]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem live_slot_product (η : Character) (m A z : O) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (t : ℝ) :
    (∏ i,rowSlot η m A z (S i) (β i) t) =
      ∑ v : (i : ι) → S i, (∏ i,β i (v i))*rowWeight η m A z t (∏ i,(v i:Ideal O)) := by
  have hs (i : ι) : rowSlot η m A z (S i) (β i) t =
      ∑ P : S i, β i P*rowWeight η m A z t P := by
    rw [rowSlot_eq_weight]
    exact (Finset.sum_coe_sort (S i) (fun P => β i P*rowWeight η m A z t P)).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_prod,← Finset.prod_mul_distrib]

theorem actual_slot_rectangle_sum (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
       ∏ i,rowSlot η m A z (S i) (β i) t := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        rowWeight η m A z t (∏ i,(v i:Ideal O))*
          (rowWeight η m A z t (I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
    simp only [map_mul]; ring
  simp_rw [ht,tsum_mul_left]
  rw [actual_hecke_rectangle_sum η m A z t W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂,
    live_slot_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem common_extracted_slot_rectangle (η : Character) (m A z : O)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal O, ∑' J : Ideal O,
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)) =
      rowWeight η m A z t (B₁*B₂)*
        ∑ v : (i : ι) → S i, (∏ i,β i (v i))*
          ∑' I : Ideal O, ∑' J : Ideal O,
            rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
              idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
                (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J := by
  have ht (v : (i : ι) → S i) (I J : Ideal O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) =
      rowWeight η m A z t (B₁*B₂)*
        (rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
            (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J) := by
    rw [CenteredMomentExtraction.idealRectangle_extract]
    simp only [map_mul]
    ring
  simp_rw [ht,tsum_mul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DivisorAllocation -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorAllocation
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def nonemptySelections (s : Finset ι) : Finset (Finset ι) := s.powerset.erase ∅

omit [DecidableEq ι] in
theorem prime_complement (P : Ideal O) (hP : Prime P) (s : Finset ι) (v : ι → Ideal O) :
    (∏ i ∈ s, (1-(if P ∣ v i then (1:ℂ) else 0))) =
      if P ∣ ∏ i ∈ s,v i then 0 else 1 := by
  by_cases h : P ∣ ∏ i ∈ s,v i
  · rw [ite_eq_left h]
    obtain ⟨i,hi,hd⟩ := (hP.dvd_finsetProd_iff v).mp h
    exact Finset.prod_eq_zero hi (by simp only [ite_eq_left hd,sub_self])
  · rw [ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    have hd : ¬P∣v i := fun hh => h ((hP.dvd_finsetProd_iff v).mpr ⟨i,hi,hh⟩)
    simp only [ite_eq_right hd,sub_zero]

theorem prime_factor_allocation (P : Ideal O) (hP : Prime P)
    (s : Finset ι) (v : ι → Ideal O) :
    (if P ∣ ∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
        ∏ i ∈ J, if P ∣ v i then (1:ℂ) else 0 := by
  let f := fun J : Finset ι => (-1:ℂ)^J.card*∏ i ∈ J,if P∣v i then (1:ℂ) else 0
  have he : (∑ J ∈ nonemptySelections s,f J)+1 =
      if P ∣ ∏ i ∈ s,v i then (0:ℂ) else 1 := by
    have hr := Finset.sum_erase_add s.powerset f (Finset.mem_powerset.mpr (Finset.empty_subset s))
    have hh := Finset.prod_sub (fun _i : ι => (1:ℂ))
      (fun i => if P∣v i then (1:ℂ) else 0) s
    simp only [Finset.prod_const_one,mul_one] at hh
    rw [prime_complement P hP s v] at hh
    simpa only [nonemptySelections,f,Finset.card_empty,pow_zero,Finset.prod_empty,one_mul] using hr.trans hh.symm
  have hn : (∑ J ∈ nonemptySelections s, (-1:ℂ)^(J.card+1)*
      ∏ i ∈ J,if P∣v i then (1:ℂ) else 0) = -(∑ J ∈ nonemptySelections s,f J) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f]
    rw [pow_succ]
    ring
  rw [hn]
  by_cases h : P∣∏ i ∈ s,v i <;> simp only [h,ite_true,ite_false] at he ⊢ <;>
    linear_combination he

theorem squarefree_dvd_iff (D I : Ideal O) (hD : Squarefree D) :
    D∣I ↔ ∀ P ∈ primeSupport D,P∣I := by
  constructor
  · intro hd P hP
    exact (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)).trans hd
  · intro h
    rw [← squarefree_support_product_self hD]
    apply Finset.prod_dvd_of_coprime ?_ h
    intro P hP Q hQ hne
    let : P.IsMaximal := (Ideal.isPrime_of_prime (support_prime hP)).isMaximal (support_prime hP).ne_zero
    let : Q.IsMaximal := (Ideal.isPrime_of_prime (support_prime hQ)).isMaximal (support_prime hQ).ne_zero
    exact Ideal.isCoprime_of_isMaximal hne

abbrev Allocation (D : Ideal O) (s : Finset ι) :=
  (P : primeSupport D) → nonemptySelections s

def allocationTerm (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)*
    ∏ i ∈ (a P).val, if (P:Ideal O)∣v i then (1:ℂ) else 0

theorem squarefree_mask_allocation (D : Ideal O) (hD : Squarefree D)
    (s : Finset ι) (v : ι → Ideal O) :
    (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ a : Allocation D s, allocationTerm D s v a := by
  have hprod : (if D∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∏ P : primeSupport D, if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0 := by
    by_cases hd : D∣∏ i ∈ s,v i
    · rw [ite_eq_left hd]
      symm
      apply Finset.prod_eq_one
      intro P hP
      rw [ite_eq_left ((squarefree_dvd_iff _ _ hD).mp hd P P.property)]
    · rw [ite_eq_right hd]
      obtain ⟨P,hP,hnd⟩ := not_forall.mp (fun h => hd ((squarefree_dvd_iff _ _ hD).mpr h))
        |> fun h => by simpa only [not_forall,not_imp] using h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨P,hP⟩ : primeSupport D)) (by simp only [ite_eq_right hnd])
  rw [hprod]
  have hl (P : primeSupport D) :
      (if (P:Ideal O)∣∏ i ∈ s,v i then (1:ℂ) else 0) =
      ∑ J : nonemptySelections s, (-1:ℂ)^(J.val.card+1)*
        ∏ i ∈ J.val, if (P:Ideal O)∣v i then (1:ℂ) else 0 := by
    rw [prime_factor_allocation P (support_prime P.property) s v]
    exact (Finset.sum_coe_sort (nonemptySelections s) (fun J =>
      (-1:ℂ)^(J.card+1)*∏ i ∈ J,if (P:Ideal O)∣v i then (1:ℂ) else 0)).symm
  simp_rw [hl]
  exact Fintype.prod_sum _

theorem allocationTerm_norm_le_one (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ‖allocationTerm D s v a‖ ≤ 1 := by
  unfold allocationTerm
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro P hP
  rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i hi
  split_ifs <;> norm_num

theorem allocation_card_bound (D : Ideal O) (s : Finset ι) :
    Fintype.card (Allocation D s) ≤ (2^(primeSupport D).card)^s.card := by
  have hc : (nonemptySelections s).card ≤ 2^s.card := by
    simpa only [nonemptySelections,Finset.card_powerset] using
      (Finset.card_erase_le (s := s.powerset) (a := (∅:Finset ι)))
  change Fintype.card (primeSupport D → nonemptySelections s) ≤ _
  simp only [Fintype.card_fun,Fintype.card_coe]
  calc
    _ ≤ (2^s.card)^(primeSupport D).card := Nat.pow_le_pow_left hc _
    _ = _ := by simp only [← pow_mul,Nat.mul_comm]

theorem allocation_mass_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      ∀ v : ι → Ideal O, (∑ a : Allocation D s, ‖allocationTerm D s v a‖) ≤
        C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C^N,pow_pos hC _,?_⟩
  intro D hD s hs v
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ∑ _a : Allocation D s,(1:ℝ) := Finset.sum_le_sum (fun a _ => allocationTerm_norm_le_one D s v a)
    _ = (Fintype.card (Allocation D s):ℝ) := by simp
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

end SevenEighths.CenteredMomentDivisorAllocation

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DivisorExtraction -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def selectedPrimes (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    Finset (primeSupport D) := Finset.univ.filter (fun P => i ∈ (a P).val)

def selectedDivisor (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) : Ideal O :=
  ∏ P ∈ selectedPrimes D s a i, (P:Ideal O)

theorem selected_divides_factor (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) : (P:Ideal O)∣v i := by
  have hP := (Finset.prod_ne_zero_iff.mp hn) P (Finset.mem_univ P)
  have hprod := (mul_ne_zero_iff.mp hP).2
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) i hi
  by_contra h
  exact hfactor (by simp only [ite_eq_right h])

theorem selectedDivisor_ne_zero (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    selectedDivisor D s a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => (support_prime P.property).ne_zero)

theorem selectedDivisor_dvd (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) (i : ι) :
    selectedDivisor D s a i ∣ v i := by
  apply Finset.prod_dvd_of_coprime ?_ ?_
  · intro P hP Q hQ hne
    let : (P:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime P.property)).isMaximal
      (support_prime P.property).ne_zero
    let : (Q:Ideal O).IsMaximal := (Ideal.isPrime_of_prime (support_prime Q.property)).isMaximal
      (support_prime Q.property).ne_zero
    exact Ideal.isCoprime_of_isMaximal (fun he => hne (Subtype.ext he))
  · intro P hP
    exact selected_divides_factor D s v a hn P i (Finset.mem_filter.mp hP).2

theorem exists_factor_quotients (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0) :
    ∃ q : ι → Ideal O, ∀ i, v i=selectedDivisor D s a i*q i := by
  choose q hq using (fun i => selectedDivisor_dvd D s v a hn i)
  exact ⟨q,hq⟩

theorem selected_prime_slot (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (hn : allocationTerm D s v a ≠ 0)
    (P : primeSupport D) (i : ι) (hi : i ∈ (a P).val) (hv : Prime (v i)) :
    v i=(P:Ideal O) :=
  ((prime_dvd_prime_iff_eq (support_prime P.property) hv).mp
    (selected_divides_factor D s v a hn P i hi)).symm

theorem double_selected_prime_slot_zero (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) (P Q : primeSupport D) (hPQ : P ≠ Q)
    (i : ι) (hPi : i ∈ (a P).val) (hQi : i ∈ (a Q).val) (hv : Prime (v i)) :
    allocationTerm D s v a=0 := by
  by_contra hn
  apply hPQ
  apply Subtype.ext
  exact (selected_prime_slot D s v a hn P i hPi hv).symm.trans
    (selected_prime_slot D s v a hn Q i hQi hv)

end SevenEighths.CenteredMomentDivisorExtraction

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DivisorEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorEnergy
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι α ρ : Type*} [DecidableEq ι]

def allocatedPolynomial (D : Ideal O) (s : Finset ι) (T : Finset α)
    (v : α → ι → Ideal O) (F : ρ → α → ℂ) (a : Allocation D s) (h : ρ) : ℂ :=
  ∑ j ∈ T, allocationTerm D s (v j) a*F h j

theorem finite_mask_regroup (D : Ideal O) (hD : Squarefree D) (s : Finset ι)
    (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (h : ρ) :
    (∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocatedPolynomial D s T v F a h := by
  have ht (j : α) : (if D∣∏ i ∈ s,v j i then F h j else 0) =
      ∑ a : Allocation D s, allocationTerm D s (v j) a*F h j := by
    have he := congrArg (fun w : ℂ => w*F h j) (squarefree_mask_allocation D hD s (v j))
    simpa only [ite_mul,one_mul,zero_mul,Finset.sum_mul] using he
  simp_rw [ht]
  rw [Finset.sum_comm]
  rfl

theorem allocation_card_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), D ≠ 0 → ∀ s : Finset ι, s.card ≤ N →
      (Fintype.card (Allocation D s):ℝ) ≤ C*(Ideal.absNorm D:ℝ)^ε := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/N) (div_pos hε hNr)
  refine ⟨C^N,pow_pos hC _,?_⟩
  intro D hD s hs
  have hn : 0 ≤ (Ideal.absNorm D:ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ ((2:ℝ)^(primeSupport D).card)^s.card := by exact_mod_cast allocation_card_bound D s
    _ ≤ ((2:ℝ)^(primeSupport D).card)^N := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hs
    _ ≤ (C*(Ideal.absNorm D:ℝ)^(ε/N))^N := pow_le_pow_left₀ (by positivity) (hb D hD) N
    _ = C^N*(Ideal.absNorm D:ℝ)^ε := by
      rw [mul_pow,← Real.rpow_mul_natCast hn]
      congr 2
      field_simp

theorem allocated_energy_small_power (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Ideal O), Squarefree D → ∀ s : Finset ι, s.card ≤ N →
      ∀ (T : Finset α) (v : α → ι → Ideal O) (F : ρ → α → ℂ) (rows : Finset ρ),
      (∑ h ∈ rows, ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
  obtain ⟨C,hC,hcard⟩ := allocation_card_small_power (ι := ι) N hN ε hε
  refine ⟨C,hC,?_⟩
  intro D hD s hs T v F rows
  have hrow (h : ρ) : ‖∑ j ∈ T, if D∣∏ i ∈ s,v j i then F h j else 0‖^2 ≤
      (Fintype.card (Allocation D s):ℝ)*∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 := by
    rw [finite_mask_regroup D hD s T v F h]
    calc
      _ ≤ (∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _a : Allocation D s => (1:ℝ))
          (fun a => ‖allocatedPolynomial D s T v F a h‖))
  calc
    _ ≤ ∑ h ∈ rows, (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ‖allocatedPolynomial D s T v F a h‖^2 :=
      Finset.sum_le_sum (fun h _ => hrow h)
    _ = (Fintype.card (Allocation D s):ℝ)*
        ∑ a : Allocation D s, ∑ h ∈ rows, ‖allocatedPolynomial D s T v F a h‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard D hD.ne_zero s hs)
      (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end SevenEighths.CenteredMomentDivisorEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DivisorTensor -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorTensor
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentMask HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def allocationSign (D : Ideal O) (s : Finset ι) (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)

theorem allocationSign_norm (D : Ideal O) (s : Finset ι) (a : Allocation D s) :
    ‖allocationSign D s a‖=1 := by
  simp only [allocationSign,norm_prod,norm_pow,norm_neg,norm_one,one_pow,Finset.prod_const_one]

theorem allocationTerm_eq_ite (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a =
      if ∀ i ∈ s, selectedDivisor D s a i∣v i then allocationSign D s a else 0 := by
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [ite_eq_left hh]
    unfold allocationTerm allocationSign
    apply Finset.prod_congr rfl
    intro P hP
    have he : (∏ i ∈ (a P).val,if (P:Ideal O)∣v i then (1:ℂ) else 0)=1 := by
      apply Finset.prod_eq_one
      intro i hi
      have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a P).property)) hi
      have hPi : (P:Ideal O)∣selectedDivisor D s a i :=
        Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ P,hi⟩)
      rw [ite_eq_left (hPi.trans (hh i his))]
    rw [he,mul_one]
  · rw [ite_eq_right hh]
    by_contra hn
    exact hh (fun i _ => selectedDivisor_dvd D s v a hn i)

theorem allocationTerm_eq_product (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) :
    allocationTerm D s v a = allocationSign D s a*
      ∏ i ∈ s, if selectedDivisor D s a i∣v i then (1:ℂ) else 0 := by
  rw [allocationTerm_eq_ite]
  by_cases hh : ∀ i ∈ s, selectedDivisor D s a i∣v i
  · rw [ite_eq_left hh,Finset.prod_eq_one (fun i hi => by rw [ite_eq_left (hh i hi)]),mul_one]
  · rw [ite_eq_right hh]
    push Not at hh
    obtain ⟨i,hi,hnd⟩ := hh
    rw [Finset.prod_eq_zero hi (by simp only [ite_eq_right hnd]),mul_zero]

theorem selected_plain_sum (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (hD : D ≠ 0) (W : ℝ → ℂ) (X : ℝ) :
    (∑' I : Ideal O, if D∣I then rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) else 0) =
      rowWeight η m A z t D*rowTwistedSum η m A z W t (X/Ideal.absNorm D) := by
  rw [tsum_ideal_divisible D hD, rowTwistedSum_eq_weight,← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [map_mul]
  have he : (Ideal.absNorm (D*I):ℝ)/X = (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm D:ℝ)) := by
    simp only [map_mul,Nat.cast_mul,div_div_eq_mul_div]
    ring
  rw [he]
  ring

theorem selected_plain_scales (D₁ D₂ : Ideal O) (X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/Ideal.absNorm D₁)*(X₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) ∧
    (Y₁/Ideal.absNorm D₁)*(Y₂/Ideal.absNorm D₂)=T/(Ideal.absNorm D₁*Ideal.absNorm D₂:ℝ) :=
  CenteredMomentExtraction.extracted_product_scale X₁ X₂ Y₁ Y₂ T D₁ D₂ hX hY

end SevenEighths.CenteredMomentDivisorTensor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DivisorSlots -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorSlots
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem selected_slot_exact (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I) (β : Ideal O → ℂ) :
    rowSlot η m A z S (fun I => if D∣I then β I else 0) t =
      if P ∈ S ∧ D∣P then β P*rowWeight η m A z t P else 0 := by
  rw [rowSlot_eq_weight]
  have hz (I : Ideal O) (hI : I ∈ S) (hne : I ≠ P) :
      (if D∣I then β I else 0)*rowWeight η m A z t I=0 := by
    have hnd : ¬D∣I := fun hd => hne ((prime_dvd_prime_iff_eq hP (hS I hI)).mp (hPD.trans hd)).symm
    simp only [ite_eq_right hnd,zero_mul]
  by_cases hmem : P ∈ S
  · rw [Finset.sum_eq_single P (fun I hI hne => hz I hI hne) (fun h => (h hmem).elim)]
    by_cases hd : D∣P <;> simp only [hmem,hd,and_self,true_and,ite_true,ite_false,zero_mul]
  · rw [Finset.sum_eq_zero (fun I hI => hz I hI (fun he => hmem (he ▸ hI)))]
    simp only [hmem,false_and,ite_false]

theorem selected_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D P : Ideal O) (hP : Prime P) (hPD : P∣D)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M : ℝ) (hM : 0 ≤ M) (hβ : ∀ I ∈ S, ‖β I‖ ≤ M) :
    ‖rowSlot η m A z S (fun I => if D∣I then β I else 0) t‖ ≤ M := by
  rw [selected_slot_exact η m A z t D P hP hPD S hS β]
  split_ifs with h
  · rw [norm_mul]
    exact (mul_le_mul (hβ P h.1) (row_twisted_coefficient_norm η m A z t P hP.ne_zero)
      (norm_nonneg _) hM).trans_eq (mul_one M)
  · simpa only [norm_zero] using hM

theorem selectedDivisor_empty (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (he : selectedPrimes D s a i=∅) : selectedDivisor D s a i=1 := by
  simp only [selectedDivisor,he,Finset.prod_empty]

theorem allocated_slot_bound (η : Character) (m A z : O) (t : ℝ)
    (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι)
    (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Prime I)
    (β : Ideal O → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hβ : ∀ I ∈ S, ‖β I‖ ≤ M)
    (hN : ∀ I ∈ S, β I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ H) :
    ‖rowSlot η m A z S (fun I => if selectedDivisor D s a i∣I then β I else 0) t‖ ≤
      if (selectedPrimes D s a i).Nonempty then M else 128*M*H := by
  by_cases hn : (selectedPrimes D s a i).Nonempty
  · rw [ite_eq_left hn]
    obtain ⟨P,hP⟩ := hn
    exact selected_slot_bound η m A z t (selectedDivisor D s a i) P (support_prime P.property)
      (Finset.dvd_prod_of_mem _ hP) S hS β M hM hβ
  · rw [ite_eq_right hn]
    have he := selectedDivisor_empty D s a i (Finset.not_nonempty_iff_eq_empty.mp hn)
    simp only [he,one_dvd,ite_true]
    exact rowSlot_bound η m A z S β t H M hH hM hβ hN

end SevenEighths.CenteredMomentDivisorSlots

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DivisorBoundary -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorBoundary
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def frozenSlots (D : Ideal O) (s slots : Finset ι) (a : Allocation D s) : Finset ι :=
  slots.filter (fun i => (selectedPrimes D s a i).Nonempty)

def extractedProduct (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) : Ideal O :=
  (∏ i ∈ plain,selectedDivisor D s a i)*(∏ i ∈ frozenSlots D s slots a,v i)

theorem divisor_dvd_extractedProduct (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0) :
    D∣extractedProduct D s plain slots a v := by
  apply (squarefree_dvd_iff _ _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  have hne : (a PP).val.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    (Finset.mem_erase.mp (a PP).property).1
  obtain ⟨i,hi⟩ := hne
  have his : i ∈ s := (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (a PP).property)) hi
  have hip : PP ∈ selectedPrimes D s a i := Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  rcases Finset.mem_union.mp (hs his) with hp | hslot
  · apply dvd_mul_of_dvd_left
    exact (Finset.dvd_prod_of_mem (fun Q : primeSupport D => (Q:Ideal O)) hip).trans
      (Finset.dvd_prod_of_mem (fun i => selectedDivisor D s a i) hp)
  · apply dvd_mul_of_dvd_right
    exact (selected_divides_factor D s v a hn PP i hi).trans
      (Finset.dvd_prod_of_mem v (Finset.mem_filter.mpr ⟨hslot,⟨PP,hip⟩⟩))

theorem extractedProduct_ne_zero (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0) :
    extractedProduct D s plain slots a v ≠ 0 :=
  mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => selectedDivisor_ne_zero D s a i))
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hv i (Finset.mem_filter.mp hi).1))

theorem actual_divisor_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) :
    Ideal.absNorm D ≤ (∏ i ∈ plain,Ideal.absNorm (selectedDivisor D s a i))*
      (∏ i ∈ frozenSlots D s slots a,Ideal.absNorm (v i)) := by
  have hd := divisor_dvd_extractedProduct D hD s plain slots hs a v hn
  have hnorm := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (extractedProduct_ne_zero D s plain slots a v hv))) (map_dvd Ideal.absNorm hd)
  simpa only [extractedProduct,map_mul,map_prod] using hnorm

theorem actual_divisor_log_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  have hnorm : (Ideal.absNorm D:ℝ) ≤
      (∏ i ∈ plain,(Ideal.absNorm (selectedDivisor D s a i):ℝ))*
      (∏ i ∈ frozenSlots D s slots a,(Ideal.absNorm (v i):ℝ)) := by
    exact_mod_cast actual_divisor_norm_boundary D hD s plain slots hs a v hn hv
  have hp (i : ι) : (Ideal.absNorm (selectedDivisor D s a i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D s a i))
  have hq (i : ι) (hi : i ∈ frozenSlots D s slots a) : (Ideal.absNorm (v i):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i (Finset.mem_filter.mp hi).1))
  have hh := Real.logb_le_logb_of_le hZ (show (0:ℝ)<Ideal.absNorm D by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)) hnorm
  rw [Real.logb_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (Finset.prod_ne_zero_iff.mpr hq), Real.logb_prod _ _ (fun i _ => hp i),
    Real.logb_prod _ _ hq] at hh
  exact hh

def formalReduction (D : Ideal O) (s plain slots : Finset ι) (a : Allocation D s)
    (P : ι → ℝ) (Z : ℝ) : ℝ :=
  (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
    ∑ i ∈ frozenSlots D s slots a,Real.logb Z (P i)

def frozenRatio (D : Ideal O) (s slots : Finset ι) (a : Allocation D s)
    (v : ι → Ideal O) (P : ι → ℝ) (Z : ℝ) : ℝ :=
  ∑ i ∈ frozenSlots D s slots a,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)

theorem formal_reduction_add_ratio (D : Ideal O) (s plain slots : Finset ι)
    (a : Allocation D s) (v : ι → Ideal O) (hv : ∀ i ∈ slots,v i ≠ 0)
    (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i) (Z : ℝ) :
    formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z =
      (∑ i ∈ plain,Real.logb Z (Ideal.absNorm (selectedDivisor D s a i):ℝ))+
      (∑ i ∈ frozenSlots D s slots a,Real.logb Z (Ideal.absNorm (v i):ℝ)) := by
  unfold formalReduction frozenRatio
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have his := (Finset.mem_filter.mp hi).1
  rw [Real.logb_div (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i his))) (hP i his).ne']
  ring

theorem actual_formal_boundary (D : Ideal O) (hD : Squarefree D)
    (s plain slots : Finset ι) (hs : s ⊆ plain ∪ slots)
    (a : Allocation D s) (v : ι → Ideal O) (hn : allocationTerm D s v a ≠ 0)
    (hv : ∀ i ∈ slots,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i ∈ slots,0 < P i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤
      formalReduction D s plain slots a P Z+frozenRatio D s slots a v P Z := by
  rw [formal_reduction_add_ratio D s plain slots a v hv P hP Z]
  exact actual_divisor_log_boundary D hD s plain slots hs a v hn hv Z hZ

theorem divisor_dyad_card (Ds : Finset (Ideal O)) (T : ℝ) (hT : 1 ≤ T)
    (hD : ∀ D ∈ Ds,D ≠ 0) (hN : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T) :
    (Ds.card:ℝ) ≤ 256*T := by
  have h := DescentFiberCost.finite_ideal_count_real Ds (2*T) (by linarith) hD
    (fun D hD => (hN D hD).le)
  linarith

theorem paired_raw_divisor_bound (Ds : Finset (Ideal O)) (T Z θ : ℝ)
    (hT : 1 ≤ T) (hZ : 1 < Z) (r₁ r₂ w₁ w₂ : Ideal O → ℝ)
    (hD : ∀ D ∈ Ds,D ≠ 0)
    (hlo : ∀ D ∈ Ds,T ≤ (Ideal.absNorm D:ℝ))
    (hhi : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T)
    (hleft : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₁ D+w₁ D)
    (hright : ∀ D ∈ Ds,Real.logb Z (Ideal.absNorm D:ℝ) ≤ r₂ D+w₂ D)
    (hw : ∀ D ∈ Ds,w₁ D+w₂ D ≤ 2*θ) :
    (∑ D ∈ Ds,Z^(-(r₁ D+r₂ D)/2)) ≤ 256*Z^θ := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have he (D : Ideal O) (hmem : D ∈ Ds) : Z^(-(r₁ D+r₂ D)/2) ≤ Z^θ/T := by
    have hn := Real.logb_le_logb_of_le hZ hT0 (hlo D hmem)
    have h₁ := hleft D hmem
    have h₂ := hright D hmem
    have hω := hw D hmem
    have hh : -(r₁ D+r₂ D)/2 ≤ θ-Real.logb Z T := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hh
    rw [Real.rpow_sub hZ0,Real.rpow_logb hZ0 hZ.ne' hT0] at hpow
    exact hpow
  calc
    _ ≤ ∑ _D ∈ Ds,Z^θ/T := Finset.sum_le_sum (fun D hD => he D hD)
    _ = (Ds.card:ℝ)*(Z^θ/T) := by simp
    _ ≤ (256*T)*(Z^θ/T) := mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT hD hhi) (by positivity)
    _ = _ := by field_simp

end SevenEighths.CenteredMomentDivisorBoundary

end

end OAI

end

