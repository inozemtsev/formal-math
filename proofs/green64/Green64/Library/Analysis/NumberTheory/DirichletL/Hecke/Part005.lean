module

public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.IdealOperations
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.Euler
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part021
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Hecke / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Hecke.Conjugation -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex
namespace SevenEighths.HeckeFamily

theorem idealCoeff_inverse_conj (χ : Character) (J : Ideal O) :
    idealCoeff χ.inverse J=conj (idealCoeff χ J) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  by_cases hJ : J=0
  · subst J
    rw [map_zero,map_zero,map_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,
    idealCoeff_span χ.inverse hg,idealCoeff_span χ hg]
  exact (MulChar.star_apply' χ.residue _).symm

theorem idealTerm_inverse_conj (χ : Character) (s : ℂ) (J : Ideal O) :
    idealTerm χ.inverse s J=conj (idealTerm χ (conj s) J) := by
  by_cases hJ : J=0
  · subst J
    simp only [idealTerm,map_zero,zero_div]
  have hN : (0 : ℝ)<J.absNorm := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hpow := Complex.cpow_conj ((J.absNorm : ℝ) : ℂ) (conj s)
    (by rw [Complex.arg_ofReal_of_nonneg hN.le]; exact Real.pi_ne_zero.symm)
  simp only [conj_ofReal, conj_conj] at hpow
  unfold idealTerm
  rw [idealCoeff_inverse_conj,map_div₀]
  congr 1

theorem LFunction_inverse_conj (χ : Character) (hχ : χ.residue≠1) (s : ℂ) :
    LFunction χ.inverse s=conj (LFunction χ (conj s)) := by
  have hi : χ.inverse.residue≠1 := by
    change χ.residue⁻¹≠1
    simpa only [ne_eq,inv_eq_one] using hχ
  have hA := LFunction_entire_nonprincipal χ.inverse hi
  have hB : Differentiable ℂ (fun z => conj (LFunction χ (conj z))) := by
    intro z
    simpa only [Function.comp_def,conj_conj] using
      (LFunction_entire_nonprincipal χ hχ (conj z)).conj_conj
  have he : LFunction χ.inverse=(fun z => conj (LFunction χ (conj z))) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hA).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hB) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    rw [LFunction_eq_ideal_tsum χ.inverse hz,LFunction_eq_ideal_tsum χ (by simpa using hz),conj_tsum]
    exact tsum_congr (idealTerm_inverse_conj χ z)
  exact congr_fun he s

end SevenEighths.HeckeFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.HeckeDetectorFamilyInclusion
open HeckeFamily HeckeDetectorZeros Complex

theorem maximum_le_of_inclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ)
    (hinclude : ∀ i,∃ j, ∀ s : ℂ, LFunction (χ i) s=LFunction (ψ j) s) :
    zeroMaximum χ hχ T≤zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
    obtain ⟨j,hj⟩ := hinclude i
    rw [←hs]
    apply zero_re_le_maximum ψ hψ T j
    · rw [hs]
      exact hm.le
    · exact ht
    · rw [←hj s]
      exact hz
  · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

theorem maximum_sum_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum χ hχ T≤zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inl i,fun _ => rfl⟩

theorem maximum_sum_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum ψ hψ T≤zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inr i,fun _ => rfl⟩

theorem inverse_nonprincipal (χ : Character) (hχ : χ.residue≠1) : χ.inverse.residue≠1 := by
  change χ.residue⁻¹≠1
  simpa only [ne_eq,inv_eq_one] using hχ

theorem maximum_inverse {ι : Type*} [Fintype ι] (χ : ι→Character)
    (hχ : ∀ i,(χ i).residue≠1) (T : ℝ) :
    zeroMaximum (fun i => (χ i).inverse) (fun i => inverse_nonprincipal (χ i) (hχ i)) T=
      zeroMaximum χ hχ T := by
  let ψ := fun i => (χ i).inverse
  have hψ := fun i => inverse_nonprincipal (χ i) (hχ i)
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum ψ hψ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained ψ hψ T hm
      rw [LFunction_inverse_conj (χ i) (hχ i),map_eq_zero] at hz
      have hh := zero_re_le_maximum χ hχ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds χ hχ T).1
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
      have hz' : LFunction (ψ i) (conj s)=0 := by
        rw [LFunction_inverse_conj (χ i) (hχ i),conj_conj,hz,map_zero]
      have hh := zero_re_le_maximum ψ hψ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz'
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

end SevenEighths.HeckeDetectorFamilyInclusion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.RowClosure -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeRowClosure
open HeckeFamily
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem periodic_of_primary (M : Ideal O)
    (hM : M ≤ Ideal.span {λ₀ ^ 2}) (G F : O →* ℂ)
    (hF : CanonicalCoefficientClass.FactorsModulo M F)
    (hu : ∀ (u : Oˣ) x, G ((u : O) * x) = G x)
    (hz : ∀ x, λ₀ ∣ x → G x = 0)
    (hagree : ∀ x, λ₀ ^ 2 ∣ x - 1 → G x = F x) :
    CanonicalCoefficientClass.FactorsModulo M G := by
  intro x y hxy
  have hdiff : λ₀ ^ 2 ∣ x - y := Ideal.mem_span_singleton.mp (hM hxy)
  have hdiff' : λ₀ ∣ x - y := (dvd_pow_self λ₀ (by decide : 2 ≠ 0)).trans hdiff
  by_cases hx : λ₀ ∣ x
  · have hy : λ₀ ∣ y := by
      convert dvd_sub hx hdiff' using 1 ; ring
    rw [hz x hx, hz y hy]
  · have hg := PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff x |>.mpr hx
    have hspec := CompletedGauss.primaryGenerator_spec (Ideal.span {x}) hg
    obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
    have hp : λ₀ ^ 2 ∣ (u : O) * x - 1 := by
      have hp' : λ₀ ^ 2 ∣ CompletedGauss.primaryGenerator (Ideal.span {x}) - 1 := hspec.2
      rwa [mul_comm, hu']
    have hq : λ₀ ^ 2 ∣ (u : O) * y - 1 := by
      have hd := hdiff.trans (dvd_mul_left (x-y) (u : O))
      convert dvd_sub hp hd using 1 ; ring
    rw [← hu u x, ← hu u y, hagree _ hp, hagree _ hq]
    apply hF
    simpa only [mul_sub] using M.mul_mem_left (u : O) hxy

def quotientRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : (O ⧸ M) →* ℂ where
  toFun x := Quotient.liftOn' x G (fun a b hab => hG a b (M.quotientRel_def.mp hab))
  map_one' := G.map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    exact G.map_mul

@[simp] theorem quotientRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    quotientRow M G hG (Ideal.Quotient.mk M z) = G z := rfl

def residueRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : MulChar (O ⧸ M) ℂ :=
  MulChar.ofUnitHom (Units.map (quotientRow M G hG))

theorem residueRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    residueRow M G hG (Ideal.Quotient.mk M z) =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := by
  by_cases hz : IsUnit (Ideal.Quotient.mk M z)
  · obtain ⟨u, hu⟩ := hz
    rw [ite_eq_left (hu ▸ u.isUnit), ← hu]
    change MulChar.ofUnitHom (Units.map (quotientRow M G hG)) (u : O ⧸ M) = G z
    rw [MulChar.ofUnitHom_coe]
    change quotientRow M G hG (u : O ⧸ M) = G z
    rw [hu, quotientRow_mk]
  · rw [ite_eq_right hz]
    exact MulChar.map_nonunit _ hz

def rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) : Character :=
  Character.ofResidue M hM (residueRow M G hG) (by
    intro u
    rw [residueRow_mk, ite_eq_left (u.isUnit.map (Ideal.Quotient.mk M)), hu])

theorem elementCoeff_rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) (z : O) :
    elementCoeff (rowCharacter M hM G hG hu) z =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := residueRow_mk M G hG z

def elementHom (η : Character) : O →* ℂ where
  toFun := elementCoeff η
  map_one' := elementCoeff_one η
  map_mul' := elementCoeff_mul η

theorem elementHom_periodic (η : Character) :
    CanonicalCoefficientClass.FactorsModulo η.modulus (elementHom η) := by
  intro x y hxy
  apply congrArg η.residue
  exact Ideal.Quotient.eq.mpr hxy

theorem elementHom_norm (η : Character) (x : O) : ‖elementHom η x‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem rowTwist_unit_mul (η : Character) (m f z : O) (u : Oˣ) (n : O) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z ((u : O)*n) =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  change elementCoeff η ((u : O)*n) * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {(u : O)*n}) = elementCoeff η n * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem rowTwist_unit (η : Character) (m f z : O) (u : Oˣ) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z (u : O) = 1 := by
  simpa using rowTwist_unit_mul η m f z u 1

theorem rowTwist_periodic (η : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r})
      (CanonicalRowCompletion.rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _
    (CanonicalRowCompletion.actualPeriodicRow (elementHom η) m u a b r hr)
    (CanonicalRowCompletion.actualPeriodicRow_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1 hn
  · exact CanonicalRowCompletion.rowTwist_eq_actualPeriodicRow_primary
      _ _ _ _ hmLam hm2 u a b r hr hpr hx

theorem rowTwist_nonzero_coprime (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    CanonicalQuadraticSieve.Supported (Ideal.span {n}) ∧ IsCoprime n (m^6*f^4*z) := by
  have hs : CanonicalQuadraticSieve.Supported (Ideal.span {n}) := by
    by_contra h
    exact hn (CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 h)
  refine ⟨hs, ?_⟩
  have hrow : CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n}) ≠ 0 :=
    right_ne_zero_of_mul hn
  have hp := pow_ne_zero 6 hrow
  rw [← CanonicalRowCompletion.idealRowHom_argument_pow _ _ _ hs,
    CanonicalRowCompletion.idealRowHom_sixth_mask _ _ hs] at hp
  by_cases hc : IsCoprime (Ideal.span {n}) (Ideal.span {m^6*f^4*z})
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mp hc
  · simp [hc] at hp

theorem rowTwist_nonzero_unit (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}) n) := by
  obtain ⟨hs, hc⟩ := rowTwist_nonzero_coprime η m f z n hmLam hm2 hn
  have hm : IsCoprime n m := hc.of_isCoprime_of_dvd_right ⟨m^5*f^4*z, by ring⟩
  have hr : IsCoprime n r := hc.of_isCoprime_of_dvd_right
    ⟨m^6*((u : O)*λ₀^a*(2 : O)^b), by
      rw [show m^6*f^4*z = m^6*(f^4*z) by ring, hx]; ring⟩
  have h2 := hm.of_isCoprime_of_dvd_right hm2
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n
    ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1).symm
  have h72 : IsCoprime n (72 : O) := by
    convert (h2.pow_right : IsCoprime n ((2 : O)^3)).mul_right h9 using 1 ; norm_num
  have he : elementCoeff η n ≠ 0 := left_ne_zero_of_mul hn
  have hη : IsCoprime (Ideal.span {n}) η.modulus := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
    exact MulChar.apply_ne_zero_iff.mp he
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff,
    IsCoprime.mul_right_iff, IsCoprime.mul_right_iff]
  exact ⟨⟨⟨hη, (Ideal.isCoprime_span_singleton_iff _ _).mpr hm⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h72⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hr⟩

theorem exists_row_character (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z), ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))

def rowConductorBound (η : Character) (m f z : O) : ℕ :=
  η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm *
    ((Ideal.span {f}).absNorm ^ 4 * (Ideal.span {z}).absNorm)

theorem row_modulus_norm_le (η : Character) (m f z : O)
    (hf : f ≠ 0) (hz : z ≠ 0) (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}).absNorm ≤
      rowConductorBound η m f z := by
  have hprod : (Ideal.span {f^4*z} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz)
  let : Finite (O ⧸ Ideal.span {f^4*z}) := Ring.HasFiniteQuotients.finiteQuotient hprod
  have hle : (Ideal.span {f^4*z} : Ideal O) ≤ Ideal.span {r} := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨(u : O)*λ₀^a*(2 : O)^b, by rw [hx]; ring⟩
  have hn := FiniteConductor.absNorm_le_of_le hle
  have heq : (Ideal.span {f^4*z} : Ideal O) = (Ideal.span {f})^4 * Ideal.span {z} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  rw [heq, map_mul, map_pow] at hn
  simpa only [rowConductorBound, map_mul] using
    Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn

theorem exists_row_character_with_conductor (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, χ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      ∀ n : O, elementCoeff χ n =
        CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z),
    row_modulus_norm_le η m f z hf hz u a b r hx, ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))

theorem idealCoeff_eq_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I = idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero, zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
  rw [← hs, idealCoeff_span χ hn, heq]
  change elementCoeff η n * _ = idealCoeff η (Ideal.span {n}) * _
  rw [idealCoeff_span η hn]
  rfl

theorem exists_primitive_row (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      (∀ I : Ideal O, idealCoeff χ I =
        idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I) ∧
      (∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0) := by
  obtain ⟨χ, hnorm, heq⟩ := exists_row_character_with_conductor η m f z hm hf hz hmLam hm2
  obtain ⟨ψ, _, hp, hn, hmask⟩ := exists_primitive_character χ
  exact ⟨χ, ψ, hp, hn.trans hnorm, idealCoeff_eq_row η χ m f z heq, hmask⟩

end SevenEighths.HeckeRowClosure

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.ExceptionalRows -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeExceptionalRows
open HeckeFamily UniqueFactorizationMonoid

def rows (S : Finset (Ideal O)) : Set O :=
  {u | u ≠ 0 ∧ ∀ P ∈ normalizedFactors (Ideal.span {u}),
    P ∈ S ∧ (normalizedFactors (Ideal.span {u})).count P < 6}

def bound (S : Finset (Ideal O)) : ℕ := ((∏ P ∈ S, P)^5).absNorm

theorem row_ideal_dvd (S : Finset (Ideal O)) {u : O} (hu : u ∈ rows S) :
    (Ideal.span {u} : Ideal O) ∣ (∏ P ∈ S, P)^5 := by
  have hI : (Ideal.span {u} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hu.1
  have hle : normalizedFactors (Ideal.span {u}) ≤ 5 • S.val := by
    apply Multiset.le_iff_count.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors (Ideal.span {u})
    · have hp := hu.2 P hP
      have hc : S.val.count P = 1 := Multiset.count_eq_one_of_mem S.nodup hp.1
      rw [Multiset.count_nsmul, hc]
      omega
    · simp only [Multiset.count_eq_zero.mpr hP]
      exact Nat.zero_le _
  have hd := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self hI, Multiset.prod_nsmul] at hd
  change (Ideal.span {u} : Ideal O) ∣ (S.prod id)^5
  simpa only [Finset.prod_val] using hd

theorem row_norm_bound (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    {u : O} (hu : u ∈ rows S) : (Ideal.span {u}).absNorm ≤ bound S := by
  have hd := map_dvd Ideal.absNorm (row_ideal_dvd S hu)
  apply Nat.le_of_dvd _ hd
  apply Nat.pos_of_ne_zero
  rw [ne_eq, Ideal.absNorm_eq_zero_iff]
  exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero))

theorem rows_subset_normDisk (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    rows S ⊆ (ConcretePrimeRowBridge.rowNormDisk (bound S) : Set O) := by
  intro u hu
  apply ConcretePrimeRowBridge.mem_rowNormDisk.mpr
  refine ⟨?_, row_norm_bound S hS hu⟩
  apply Nat.pos_of_ne_zero
  simpa only [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] using hu.1

theorem rows_finite (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) : (rows S).Finite :=
  (ConcretePrimeRowBridge.rowNormDisk (bound S)).finite_toSet.subset (rows_subset_normDisk S hS)

end SevenEighths.HeckeExceptionalRows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.RowNonprincipal -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRowNonprincipal
open HeckeFamily CanonicalRowCompletion CenteredMomentCanonical
open ConcretePrimeRowBridge hiding O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem nonprincipal_of_local_factor (χ : Character)
    (Q J P : Ideal O) [P.IsMaximal]
    (hQ : Q ≤ Ideal.span {λ₀ ^ 2})
    (φ : O →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ)
    (hJ : CanonicalQuadraticSieve.Supported J)
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : ¬ 6 ∣ c)
    (hcop : IsCoprime (Q * J) (P ^ c))
    (hrow : ∀ n : O, λ₀ ^ 2 ∣ n - 1 →
      elementCoeff χ n = φ n * idealRowHom n (P ^ c * J)) :
    χ.residue ≠ 1 := by
  let ψ := canonicalPrimePowerCharacter P hg hc
  have hψ : ψ ≠ 1 := fun h => hc6 ((HeckeLocalRamification.canonicalPrimePowerCharacter_eq_one_iff P hg hchar hc).mp h)
  obtain ⟨u, hu⟩ : ∃ u : (O ⧸ P ^ c)ˣ, ψ (u : O ⧸ P ^ c) ≠ 1 := by
    by_contra! h
    apply hψ
    apply MulChar.ext
    intro u
    rw [MulChar.one_apply u.isUnit]
    exact h u
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) (P ^ c) hcop
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P ^ c))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk (P ^ c) n) = (1, (u : O ⧸ P ^ c)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnQ : n - 1 ∈ Q := Ideal.mul_le_left hn
  have hnJ : n - 1 ∈ J := Ideal.mul_le_right hn
  have hnprimary : λ₀ ^ 2 ∣ n - 1 := Ideal.mem_span_singleton.mp (hQ hnQ)
  have hv : elementCoeff χ n = ψ (u : O ⧸ P ^ c) := by
    rw [hrow n hnprimary, map_mul, hφ n 1 hnQ, map_one, one_mul,
      idealRowHom_congr_mod J n 1 hnJ, idealRowHom_one_supported J hJ, mul_one]
    rw [← canonicalPrimePowerCharacter_mk P hg hc n, hnP]
  have hv0 : elementCoeff χ n ≠ 0 := hv ▸ (MulChar.apply_ne_zero_iff.mpr u.isUnit)
  intro hχ
  have hunit : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hv0
  have hv1 : elementCoeff χ n = 1 := by
    change χ.residue _ = 1
    rw [hχ, MulChar.one_apply hunit]
  exact hu (hv.symm.trans hv1)

theorem actual_row_nonprincipal (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P J : Ideal O) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hJ : CanonicalQuadraticSieve.Supported J)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : ¬ 6 ∣ c)
    (hsplit : Ideal.span {r} = P ^ c * J)
    (hcop : IsCoprime ((η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) * J) (P ^ c))
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n) :
    χ.residue ≠ 1 := by
  let φ := HeckeRowClosure.elementHom η * coprimalityMask m * numeratorBadTwist u a b r hr
  refine nonprincipal_of_local_factor χ (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) J P
      ?_ φ ?_ hJ hg hchar hc hc6 hcop ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact Ideal.mul_le_right.trans ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr hd72))
  · intro x y hxy
    change ((HeckeRowClosure.elementHom η x * coprimalityMask m x) * numeratorBadTwist u a b r hr x) =
      ((HeckeRowClosure.elementHom η y * coprimalityMask m y) * numeratorBadTwist u a b r hr y)
    rw [HeckeRowClosure.elementHom_periodic η x y (Ideal.mul_le_left (Ideal.mul_le_left hxy)),
      coprimalityMask_periodic m x y (Ideal.mul_le_right (Ideal.mul_le_left hxy)),
      numeratorBadTwist_periodic u a b r hr x y (Ideal.mul_le_right hxy)]
  · intro n hn
    rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hn]
    change φ n * idealRowHom n (Ideal.span {r}) = φ n * idealRowHom n (P ^ c * J)
    rw [hsplit]

open UniqueFactorizationMonoid in

theorem extract_prime_power (I : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (P : Ideal O) (hP : P ∈ normalizedFactors I) :
    ∃ J : Ideal O, I = P ^ (normalizedFactors I).count P * J ∧
      CanonicalQuadraticSieve.Supported J ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ (normalizedFactors I).count Q
  have hPS : P ∈ S := Multiset.mem_toFinset.mpr hP
  have hsplit : I = P ^ (normalizedFactors I).count P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI.1).symm
      _ = ∏ Q ∈ S, Q ^ (normalizedFactors I).count Q := Finset.prod_multiset_count _
      _ = P ^ (normalizedFactors I).count P * J :=
        (Finset.mul_prod_erase S (fun Q => Q ^ (normalizedFactors I).count Q) hPS).symm
  have hgood := supported_factors_good I hI P hP
  let : P.IsMaximal := hgood.1
  refine ⟨J, hsplit, ?_, ?_⟩
  · exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplit ▸ hI) |>.2
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hgoodQ := supported_factors_good I hI Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := hgoodQ.1
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

open UniqueFactorizationMonoid in

theorem principal_row_multiplicity (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (hprincipal : χ.residue = 1)
    (P : Ideal O) (hP : P ∈ normalizedFactors (Ideal.span {r}))
    (hcop : IsCoprime (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) P) :
    6 ∣ (normalizedFactors (Ideal.span {r})).count P := by
  by_contra hc6
  have hgood := supported_factors_good (Ideal.span {r}) hr P hP
  let : P.IsMaximal := hgood.1
  obtain ⟨J, hsplit, hJ, hJP⟩ := extract_prime_power _ hr P hP
  have hc : 1 ≤ (normalizedFactors (Ideal.span {r})).count P := Multiset.count_pos.mpr hP
  exact actual_row_nonprincipal η χ m f z hmLam hm2 u a b r hr hpr hx P J
    hgood.2.1 hgood.2.2 hJ hc hc6 hsplit ((hcop.mul_left hJP).pow_right) hχ hprincipal

open UniqueFactorizationMonoid in

theorem principal_row_fixed_support (η χ : Character) (m f z : O)
    (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (hprincipal : χ.residue = 1)
    (hfree : ∀ P ∈ normalizedFactors (Ideal.span {r}),
      (normalizedFactors (Ideal.span {r})).count P < 6) :
    r ∈ HeckeExceptionalRows.rows
      (normalizedFactors (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)})).toFinset := by
  let Q := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}
  have hQ : Q ≠ ⊥ := mul_ne_zero
    (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  refine ⟨Ideal.span_singleton_eq_bot.not.mp hr.1, ?_⟩
  intro P hP
  refine ⟨?_, hfree P hP⟩
  apply Multiset.mem_toFinset.mpr
  have hgood := supported_factors_good (Ideal.span {r}) hr P hP
  let : P.IsMaximal := hgood.1
  apply (Ideal.mem_normalizedFactors_iff hQ).mpr
  refine ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor P hP), ?_⟩
  by_contra hQP
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := hgood.1.eq_of_le hJ.ne_top hPJ
    exact hQP (hPJ' ▸ hQJ)
  have hd := principal_row_multiplicity η χ m f z hmLam hm2 u a b r hr hpr hx hχ hprincipal P hP hcop
  exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) (hfree P hP) hd

end SevenEighths.HeckeRowNonprincipal

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CenteredExceptionalProfile -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredExceptionalProfile
open UniqueFactorizationMonoid HeckeFamily CanonicalRowCompletion
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O
open CenteredExceptionalCount CenteredMomentCanonical
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem split_at_prime (I P : Ideal O) (hI : I ≠ 0) [P.IsMaximal] :
    ∃ J : Ideal O, I = P ^ valuation I P * J ∧ J ≠ 0 ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ valuation I Q
  have hsplit : I = P ^ valuation I P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI).symm
      _ = ∏ Q ∈ S, Q ^ valuation I Q := Finset.prod_multiset_count _
      _ = P ^ valuation I P * J := by
        by_cases hP : P ∈ S
        · exact (Finset.mul_prod_erase S (fun Q => Q ^ valuation I Q) hP).symm
        · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
            (fun h => hP (Multiset.mem_toFinset.mpr h))
          simp only [J, Finset.erase_eq_of_notMem hP, hz, pow_zero, one_mul]
  refine ⟨J, hsplit, ?_, ?_⟩
  · intro hz
    apply hI
    rw [hsplit, hz, mul_zero]
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hp := prime_of_normalized_factor Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

theorem exists_unit_probe (Q K P : Ideal O) (hK : K ≠ 0) [P.IsMaximal]
    (hQP : IsCoprime Q P) (u : (O ⧸ P)ˣ) :
    ∃ n : O, n - 1 ∈ Q ∧ IsCoprime (Ideal.span {n}) K ∧
      Ideal.Quotient.mk P n = (u : O ⧸ P) := by
  obtain ⟨J, hsplit, hJ, hJP⟩ := split_at_prime K P hK
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) P (hQP.mul_left hJP)
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk P n) = (1, (u : O ⧸ P)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnJ : Ideal.Quotient.mk J n = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn)
  have hcJ : IsCoprime (Ideal.span {n}) J :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnJ ▸ isUnit_one)
  have hcP : IsCoprime (Ideal.span {n}) P :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hnP ▸ u.isUnit)
  refine ⟨n, Ideal.mul_le_left hn, ?_, hnP⟩
  rw [hsplit]
  exact hcP.pow_right.mul_right hcJ

theorem valuation_mod_six_of_unit_agreement (Q K I J P : Ideal O)
    (hK : K ≠ 0) (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (heq : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      idealRowHom n I = idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  obtain ⟨I₀, hsplitI, hI₀, hcI⟩ := split_at_prime I P hI.1
  obtain ⟨J₀, hsplitJ, hJ₀, hcJ⟩ := split_at_prime J P hJ.1
  have hsI : CanonicalQuadraticSieve.Supported I₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitI ▸ hI)).2
  have hsJ : CanonicalQuadraticSieve.Supported J₀ :=
    ((CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplitJ ▸ hJ)).2
  have hpows : actualSextic P hg ^ valuation I P = actualSextic P hg ^ valuation J P := by
    apply MulChar.ext
    intro u
    obtain ⟨n, hn, hcK, hnP⟩ := exists_unit_probe (Q * I₀ * J₀) K P hK
      ((hQP.mul_left hcI).mul_left hcJ) u
    have hval := heq n (Ideal.mul_le_left (Ideal.mul_le_left hn)) hcK
    have hIn : n - 1 ∈ I₀ := Ideal.mul_le_right (Ideal.mul_le_left hn)
    have hJn : n - 1 ∈ J₀ := Ideal.mul_le_right hn
    rw [hsplitI, hsplitJ, map_mul, map_mul, map_pow, map_pow,
      idealRowHom_congr_mod I₀ n 1 hIn, idealRowHom_congr_mod J₀ n 1 hJn,
      idealRowHom_one_supported I₀ hsI, idealRowHom_one_supported J₀ hsJ,
      mul_one, mul_one, idealRowHom_prime n P hg, hnP] at hval
    simpa only [MulChar.pow_apply_coe] using hval
  have hm := (pow_eq_pow_iff_modEq.mp hpows)
  rw [actualSextic_order_six P hg hchar] at hm
  exact hm

def InducedBy (χ ψ : Character) : Prop :=
  ∀ I : Ideal O, idealCoeff χ I =
    if IsCoprime I χ.modulus then idealCoeff ψ I else 0

theorem exists_primitive_inducedBy (χ : Character) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      χ.modulus ≤ ψ.modulus ∧ InducedBy χ ψ := by
  obtain ⟨ψ, hmod, hprim, _, hmask⟩ := exists_primitive_character χ
  exact ⟨ψ, hprim, hmod, hmask⟩

theorem elementCoeff_eq_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (n : O) (hn : n ≠ 0) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = elementCoeff ψ n := by
  have he := h (Ideal.span {n})
  simp only [hc, ite_true, idealCoeff_span χ hn, idealCoeff_span ψ hn] at he
  exact he

theorem elementCoeff_eq_one_of_inducedBy (χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hψ : Q ≤ ψ.modulus)
    (n : O) (hn : n - 1 ∈ Q) (hc : IsCoprime (Ideal.span {n}) χ.modulus) :
    elementCoeff χ n = 1 := by
  have hn0 : n ≠ 0 := by
    intro hz
    have h1 : (1 : O) ∈ Q := by simpa [hz] using Q.neg_mem hn
    exact hQ ((Ideal.eq_top_iff_one Q).mpr h1)
  rw [elementCoeff_eq_of_inducedBy χ ψ h n hn0 hc]
  change ψ.residue (Ideal.Quotient.mk ψ.modulus n) = 1
  rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (hψ hn), map_one]

theorem local_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q K I J P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (hI : CanonicalQuadraticSieve.Supported I)
    (hJ : CanonicalQuadraticSieve.Supported J) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P)
    (hrow₁ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ₁ n = elementCoeff η n * idealRowHom n I)
    (hrow₂ : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ₂ n = elementCoeff η n * idealRowHom n J) :
    valuation I P % 6 = valuation J P % 6 := by
  let L := ((K * η.modulus) * χ₁.modulus) * χ₂.modulus
  have hL : L ≠ 0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero hK η.modulus_ne_bot) χ₁.modulus_ne_bot) χ₂.modulus_ne_bot
  apply valuation_mod_six_of_unit_agreement Q L I J P hL hI hJ hg hchar hQP
  intro n hn hc
  obtain ⟨⟨⟨hcK, hcη⟩, hc₁⟩, hc₂⟩ :=
    (show ((IsCoprime (Ideal.span {n}) K ∧ IsCoprime (Ideal.span {n}) η.modulus) ∧
      IsCoprime (Ideal.span {n}) χ₁.modulus) ∧ IsCoprime (Ideal.span {n}) χ₂.modulus from by
        simpa only [L, IsCoprime.mul_right_iff] using hc)
  have he₁ := elementCoeff_eq_one_of_inducedBy χ₁ ψ₁ h₁ Q hQ hψ₁ n hn hc₁
  have he₂ := elementCoeff_eq_one_of_inducedBy χ₂ ψ₂ h₂ Q hQ hψ₂ n hn hc₂
  rw [hrow₁ n hn hcK] at he₁
  rw [hrow₂ n hn hcK] at he₂
  have hη : elementCoeff η n ≠ 0 := MulChar.apply_ne_zero_iff.mpr
    ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcη)
  exact mul_left_cancel₀ hη (he₁.trans he₂.symm)

theorem actual_row_on_fixed_units (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1)
    (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (n : O) (hn : n - 1 ∈ Ideal.span {(72 : O)})
    (hc : IsCoprime (Ideal.span {n}) (Ideal.span {m})) :
    elementCoeff χ n = elementCoeff η n * idealRowHom n (Ideal.span {r}) := by
  have hd72 : λ₀ ^ 2 ∣ (72 : O) := ActualEisensteinCubic.lambda_sq_dvd_three.trans
    (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩)
  have hp : λ₀ ^ 2 ∣ n - 1 := hd72.trans (Ideal.mem_span_singleton.mp hn)
  rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hp]
  change ((elementCoeff η n * coprimalityMask m n) * numeratorBadTwist u a b r hr n) *
    idealRowHom n (Ideal.span {r}) = _
  have hm : coprimalityMask m n = 1 := by
    change (if IsCoprime m n then (1 : ℂ) else 0) = 1
    simp only [((Ideal.isCoprime_span_singleton_iff _ _).mp hc).symm, ite_true]
  rw [hm, numeratorBadTwist_periodic u a b r hr n 1 hn, map_one, mul_one, mul_one]

theorem actual_rows_good_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u₁ u₂ : Oˣ) (a₁ b₁ a₂ b₂ : ℕ) (r₁ r₂ : O)
    (hr₁ : CanonicalQuadraticSieve.Supported (Ideal.span {r₁}))
    (hr₂ : CanonicalQuadraticSieve.Supported (Ideal.span {r₂}))
    (hpr₁ : λ₀ ^ 2 ∣ r₁ - 1) (hpr₂ : λ₀ ^ 2 ∣ r₂ - 1)
    (hx₁ : f ^ 4 * z₁ = (u₁ : O) * λ₀ ^ a₁ * (2 : O) ^ b₁ * r₁)
    (hx₂ : f ^ 4 * z₂ = (u₂ : O) * λ₀ ^ a₂ * (2 : O) ^ b₂ * r₂)
    (hχ₁ : ∀ n, elementCoeff χ₁ n = rowTwist (HeckeRowClosure.elementHom η) m f z₁ n)
    (hχ₂ : ∀ n, elementCoeff χ₂ n = rowTwist (HeckeRowClosure.elementHom η) m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P)
    (hchar : ringChar (O ⧸ P) ≠ 2) (hQP : IsCoprime Q P) :
    valuation (Ideal.span {r₁}) P % 6 = valuation (Ideal.span {r₂}) P % 6 := by
  apply local_rows_profile η χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ Q (Ideal.span {m})
    (Ideal.span {r₁}) (Ideal.span {r₂}) P hQ (Ideal.span_singleton_eq_bot.not.mpr hm)
    hψ₁ hψ₂ hr₁ hr₂ hg hchar hQP
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₁ m f z₁ hmLam hm2 u₁ a₁ b₁ r₁ hr₁ hpr₁ hx₁ hχ₁ n (hQ72 hn) hc
  · intro n hn hc
    exact actual_row_on_fixed_units η χ₂ m f z₂ hmLam hm2 u₂ a₂ b₂ r₂ hr₂ hpr₂ hx₂ hχ₂ n (hQ72 hn) hc

theorem valuation_span_eq_zero_of_not_mem (x : O) (P : Ideal O) (hx : x ∉ P) :
    valuation (Ideal.span {x}) P = 0 := by
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ P.zero_mem)
  apply Multiset.count_eq_zero.mpr
  intro hP
  have hle := ((Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr hx0)).mp hP).2
  exact hx (hle (Ideal.subset_span (by simp)))

theorem valuation_supported_numerator (x : O) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : r ≠ 0) (hx : x = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P : Ideal O) (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P) :
    valuation (Ideal.span {x}) P = valuation (Ideal.span {r}) P := by
  have hu : Ideal.span {(u : O)} = (1 : Ideal O) := by
    simpa only [Ideal.one_eq_top] using (Ideal.span_singleton_eq_top.mpr u.isUnit)
  have hl0 : Ideal.span {λ₀} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have h20 : Ideal.span {(2 : O)} ≠ (0 : Ideal O) :=
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hr0 : Ideal.span {r} ≠ (0 : Ideal O) := Ideal.span_singleton_eq_bot.not.mpr hr
  rw [hx]
  simp only [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hu, one_mul]
  rw [valuation_mul _ _ _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ h20)) hr0,
    valuation_mul _ _ _ (pow_ne_zero _ hl0) (pow_ne_zero _ h20), valuation_pow, valuation_pow,
    valuation_span_eq_zero_of_not_mem λ₀ P hg, valuation_span_eq_zero_of_not_mem (2 : O) P h2]
  omega

theorem valuation_mod_six_cancel_frozen (A I J P : Ideal O)
    (hA : A ≠ 0) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : valuation (A * I) P % 6 = valuation (A * J) P % 6) :
    valuation I P % 6 = valuation J P % 6 := by
  rw [valuation_mul A I P hA hI, valuation_mul A J P hA hJ] at h
  exact Nat.ModEq.add_left_cancel' (valuation A P) h

theorem actual_rows_profile (η χ₁ χ₂ ψ₁ ψ₂ : Character)
    (h₁ : InducedBy χ₁ ψ₁) (h₂ : InducedBy χ₂ ψ₂)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hψ₁ : Q ≤ ψ₁.modulus) (hψ₂ : Q ≤ ψ₂.modulus)
    (m f z₁ z₂ : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ₁ : ∀ n, elementCoeff χ₁ n = rowTwist (HeckeRowClosure.elementHom η) m f z₁ n)
    (hχ₂ : ∀ n, elementCoeff χ₂ n = rowTwist (HeckeRowClosure.elementHom η) m f z₂ n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨u₁, a₁, b₁, r₁, hr₁, hpr₁, hx₁⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₁) (mul_ne_zero (pow_ne_zero _ hf) hz₁)
  obtain ⟨u₂, a₂, b₂, r₂, hr₂, hpr₂, hx₂⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z₂) (mul_ne_zero (pow_ne_zero _ hf) hz₂)
  have hr₁0 := Ideal.span_singleton_eq_bot.not.mp hr₁.1
  have hr₂0 := Ideal.span_singleton_eq_bot.not.mp hr₂.1
  have h := actual_rows_good_profile η χ₁ χ₂ ψ₁ ψ₂ h₁ h₂ Q hQ hQ72 hψ₁ hψ₂
    m f z₁ z₂ hm hmLam hm2 u₁ u₂ a₁ b₁ a₂ b₂ r₁ r₂ hr₁ hr₂ hpr₁ hpr₂ hx₁ hx₂
    hχ₁ hχ₂ P hg (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP
  rw [← valuation_supported_numerator _ u₁ a₁ b₁ r₁ hr₁0 hx₁ P hg h2,
    ← valuation_supported_numerator _ u₂ a₂ b₂ r₂ hr₂0 hx₂ P hg h2,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at h
  exact valuation_mod_six_cancel_frozen _ _ _ P
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ hf))
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) h

theorem local_row_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q K I P : Ideal O) (hQ : Q ≠ ⊤) (hK : K ≠ 0)
    (hψ : Q ≤ ψ.modulus) (hI : CanonicalQuadraticSieve.Supported I)
    [P.IsMaximal] (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hrow : ∀ n : O, n - 1 ∈ Q → IsCoprime (Ideal.span {n}) K →
      elementCoeff χ n = elementCoeff η n * idealRowHom n I) :
    valuation I P % 6 = 0 := by
  have hzero : valuation (1 : Ideal O) P % 6 = 0 := by
    simp only [valuation, normalizedFactors_one, Multiset.count_zero, Nat.zero_mod]
  rw [← hzero]
  apply valuation_mod_six_of_unit_agreement (Q * η.modulus) (K * χ.modulus) I 1 P
    (mul_ne_zero hK χ.modulus_ne_bot) hI
    (by constructor; exact one_ne_zero; simp only [normalizedFactors_one, Multiset.notMem_zero, false_implies, implies_true]) hg hchar
    (hQP.mul_left hηP)
  intro n hn hc
  obtain ⟨hcK, hcχ⟩ := IsCoprime.mul_right_iff.mp hc
  have hnQ := Ideal.mul_le_left hn
  have hη : elementCoeff η n = 1 := by
    change η.residue (Ideal.Quotient.mk η.modulus n) = 1
    rw [(Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mul_le_right hn), map_one]
  have he := elementCoeff_eq_one_of_inducedBy χ ψ h Q hQ hψ n hnQ hcχ
  rw [hrow n hnQ hcK, hη, one_mul] at he
  simpa only [map_one] using he

theorem actual_row_numerator_valuation_zero (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m f z : O) (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P) :
    valuation (Ideal.span {f ^ 4 * z}) P % 6 = 0 := by
  obtain ⟨u, a, b, r, hr, hpr, hx⟩ :=
    exists_supported_numerator_factorization (f ^ 4 * z) (mul_ne_zero (pow_ne_zero _ hf) hz)
  rw [valuation_supported_numerator _ u a b r (Ideal.span_singleton_eq_bot.not.mp hr.1) hx P hg h2]
  apply local_row_valuation_zero η χ ψ h Q (Ideal.span {m}) (Ideal.span {r}) P hQ
    (Ideal.span_singleton_eq_bot.not.mpr hm) hψ hr hg
    (ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem P h2) hQP hηP
  intro n hn hc
  exact actual_row_on_fixed_units η χ m f z hmLam hm2 u a b r hr hpr hx hχ n (hQ72 hn) hc

theorem actual_row_forced_residue_four (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η.modulus P)
    (hA2 : valuation (Ideal.span {A}) P % 6 = 2) :
    valuation (Ideal.span {z}) P % 6 = 4 := by
  have he := actual_row_numerator_valuation_zero η χ ψ h Q hQ hQ72 hψ m 1 (A * z)
    hm one_ne_zero (mul_ne_zero hA hz) hmLam hm2 hχ P hg h2 hQP hηP
  simp only [one_pow, one_mul] at he
  rw [← Ideal.span_singleton_mul_span_singleton, valuation_mul _ _ _
    (Ideal.span_singleton_eq_bot.not.mpr hA) (Ideal.span_singleton_eq_bot.not.mpr hz),
    Nat.add_mod, hA2] at he
  omega

theorem actual_forced_fourth_power (η χ ψ : Character) (h : InducedBy χ ψ)
    (Q : Ideal O) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hψ : Q ≤ ψ.modulus)
    (m A z : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2) :
    D ^ 4 ∣ sixthRemainder (Ideal.span {z}) ∧
      (Ideal.absNorm D : ℝ) ^ 4 ≤ Ideal.absNorm (sixthRemainder (Ideal.span {z})) := by
  have hf : ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4 := by
    intro P hP
    have hp := prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    obtain ⟨hg, h2, hQP, hηP, hA2⟩ := hgood P hP
    exact actual_row_forced_residue_four η χ ψ h Q hQ hQ72 hψ m A z hm hA hz hmLam hm2 hχ
      P hg h2 hQP hηP hA2
  exact ⟨forced_fourth_power_dvd _ D hD hf, forced_fourth_power_norm_le _ D hD hf⟩

def FixedInducingRow (η : Character) (Q : Ideal O) (m A z : O) : Prop :=
  ∃ χ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
    InducedBy χ ψ ∧ Q ≤ ψ.modulus ∧
    ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m 1 (A * z) n

theorem fixed_inducing_rows_profile (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (P : Ideal O) [P.IsMaximal] (hg : λ₀ ∉ P) (h2 : (2 : O) ∉ P)
    (hQP : IsCoprime Q P) :
    valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6 := by
  obtain ⟨χ₁, ψ₁, _, hi₁, hψ₁, hχ₁⟩ := h₁
  obtain ⟨χ₂, ψ₂, _, hi₂, hψ₂, hχ₂⟩ := h₂
  have he := actual_rows_profile η χ₁ χ₂ ψ₁ ψ₂ hi₁ hi₂ Q hQ hQ72 hψ₁ hψ₂
    m 1 (A * z₁) (A * z₂) hm one_ne_zero (mul_ne_zero hA hz₁) (mul_ne_zero hA hz₂)
    hmLam hm2 hχ₁ hχ₂ P hg h2 hQP
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at he
  exact valuation_mod_six_cancel_frozen _ _ _ P (Ideal.span_singleton_eq_bot.not.mpr hA)
    (Ideal.span_singleton_eq_bot.not.mpr hz₁) (Ideal.span_singleton_eq_bot.not.mpr hz₂) he

theorem fixed_inducing_rows_same_remainder (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A z₁ z₂ : O) (hm : m ≠ 0) (hA : A ≠ 0) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (h₁ : FixedInducingRow η Q m A z₁) (h₂ : FixedInducingRow η Q m A z₂)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (hsector : ∀ P ∈ S, valuation (Ideal.span {z₁}) P % 6 = valuation (Ideal.span {z₂}) P % 6) :
    sixthRemainder (Ideal.span {z₁}) = sixthRemainder (Ideal.span {z₂}) := by
  apply sixthRemainder_eq_of_prime_profile (sixthRemainder_ne_zero _)
  intro P hP
  rw [sixthRemainder_valuation]
  by_cases hPS : P ∈ S
  · exact hsector P hPS
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    obtain ⟨hg, h2, hQP⟩ := houtside P hP hPS
    exact fixed_inducing_rows_profile η Q hQ hQ72 m A z₁ z₂ hm hA hz₁ hz₂ hmLam hm2
      h₁ h₂ P hg h2 hQP

theorem fixed_inducing_remainder_card (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z) :
    (T.image (fun z => sixthRemainder (Ideal.span {z}))).card ≤ 6 ^ S.card := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  let code : Ideal O → (S → Fin 6) :=
    fun R P => ⟨valuation R P.val % 6, Nat.mod_lt _ (by decide)⟩
  have hinj : (Rs : Set (Ideal O)).InjOn code := by
    intro R hR R' hR' he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hR'
    apply fixed_inducing_rows_same_remainder η Q hQ hQ72 m A z z' hm hA (hT z hz) (hT z' hz')
      hmLam hm2 (hex z hz) (hex z' hz') S houtside
    intro P hP
    have hh := congrArg (fun f : S → Fin 6 => (f ⟨P, hP⟩).val) he
    simpa only [code, sixthRemainder_valuation, Nat.mod_mod] using hh
  have hc := Finset.card_le_card_of_injOn code (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Rs] using hc

theorem fixed_inducing_row_count (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (S : Finset (Ideal O))
    (houtside : ∀ P : Ideal O, Prime P → P ∉ S →
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ S.card * C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  let Rs := T.image (fun z => sixthRemainder (Ideal.span {z}))
  have hRs : ∀ R ∈ Rs, R ≠ 0 := by
    intro R hR
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hR
    exact sixthRemainder_ne_zero _
  have hRnorm : ∀ R ∈ Rs, Z ^ (2 * F) ≤ (Ideal.absNorm R : ℝ) := by
    intro R hR
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hR
    obtain ⟨χ, ψ, _, hi, hψ, hχ⟩ := hex z hz
    have hf := (actual_forced_fourth_power η χ ψ hi Q hQ hQ72 hψ m A z hm hA
      (hT z hz) hmLam hm2 hχ D hD hgood).2
    calc
      Z ^ (2 * F) = (Z ^ (F / 2)) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
        congr 1
        norm_num
        ring
      _ ≤ (Ideal.absNorm D : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) hDnorm _
      _ ≤ _ := hf
  have hcount := element_count_power_scale_family T Rs hRs Z C M (2 * F) hZ hC hRnorm hT
    (fun z hz => Finset.mem_image.mpr ⟨z, hz, rfl⟩) hN
  have hcard : (Rs.card : ℝ) ≤ (6 : ℝ) ^ S.card := by
    exact_mod_cast fixed_inducing_remainder_card η Q hQ hQ72 m A hm hA hmLam hm2 S houtside T hT hex
  apply hcount.trans
  gcongr

theorem outside_fixed_support (Q : Ideal O) (hQ : Q ≠ 0)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (P : Ideal O) (hP : Prime P)
    (hPS : P ∉ (normalizedFactors Q).toFinset) :
    λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := (inferInstance : P.IsMaximal).eq_of_le hJ.ne_top hPJ
    apply hPS
    apply Multiset.mem_toFinset.mpr
    apply (Ideal.mem_normalizedFactors_iff hQ).mpr
    exact ⟨Ideal.isPrime_of_prime hP, hPJ' ▸ hQJ⟩
  have h72 : (72 : O) ∉ P := by
    intro hh
    have hle : Q ≤ P := hQ72.trans ((Ideal.span_singleton_le_iff_mem _).mpr hh)
    have he := Ideal.isCoprime_iff_sup_eq.mp hcop
    rw [sup_eq_right.mpr hle] at he
    exact hP.ne_one (by simpa only [Ideal.one_eq_top] using he)
  have hl : λ₀ ∣ (72 : O) :=
    (dvd_pow_self λ₀ (by decide : (2 : ℕ) ≠ 0)).trans
      (ActualEisensteinCubic.lambda_sq_dvd_three.trans (show (3 : O) ∣ 72 from ⟨24, by norm_num⟩))
  have h2 : (2 : O) ∣ 72 := ⟨36, by norm_num⟩
  refine ⟨?_, ?_, hcop⟩
  · intro hh
    obtain ⟨v, hv⟩ := hl
    exact h72 (hv ▸ P.mul_mem_right v hh)
  · intro hh
    obtain ⟨v, hv⟩ := h2
    exact h72 (hv ▸ P.mul_mem_right v hh)

theorem fixed_support_exceptional_count (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) :=
  fixed_inducing_row_count η Q hQ hQ72 m A hm hA hmLam hm2
    (normalizedFactors Q).toFinset (outside_fixed_support Q hQ0 hQ72) T hT hex
    D hD hgood Z C M F hZ hC hDnorm hN

theorem fixed_support_exceptional_count_weaker (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - F) / 6) := by
  apply (fixed_support_exceptional_count η Q hQ0 hQ hQ72 m A hm hA hmLam hm2 T hT hex
    D hD hgood Z C M F (zero_lt_one.trans_le hZ) hC hDnorm hN).trans
  gcongr
  linarith

theorem fixed_inducing_rows_empty (η : Character) (Q : Ideal O)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, FixedInducingRow η Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ normalizedFactors D, λ₀ ∉ P ∧ (2 : O) ∉ P ∧
      IsCoprime Q P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P % 6 = 2)
    (H : ℝ) (hH : H < (Ideal.absNorm D : ℝ) ^ 4)
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) : T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨χ, ψ, _, hi, hψ, hχ⟩ := hex z hz
  have hf := (actual_forced_fourth_power η χ ψ hi Q hQ hQ72 hψ m A z hm hA
    (hT z hz) hmLam hm2 hχ D hD hgood).2
  have hr := sixthRemainder_norm_le (Ideal.span {z}) (Ideal.span_singleton_eq_bot.not.mpr (hT z hz))
  exact (not_le_of_gt hH) (hf.trans (hr.trans (hN z hz)))

end SevenEighths.CenteredExceptionalProfile

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

def zeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
    (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ s.re = x}

def zeroSetWithSentinel : Set ℝ := insert (1 / 2) zeroRealParts

def beta : ℝ := sSup zeroSetWithSentinel

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zero_re_le_beta (χ : Character) {s : ℂ} (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (χ : Character) {s : ℂ}
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := lt_trans (by linarith [half_le_beta]) hs
  exact (not_lt_of_ge (zero_re_le_beta χ hpos hpole hz)) hs

theorem exists_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hεsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), 0 < s.re ∧
      (s ≠ 1 ∨ χ.residue ≠ 1) ∧ LFunction χ s = 0 ∧ beta - ε < s.re := by
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    zeroSet_bddAbove hε hεsmall
  obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hpos, hpole, hz, hlt⟩

theorem beta_le_seven_eighths_of_uniform_margin
    (hbound : 7 / 8 < beta →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < beta - 7 / 8 ∧ 0 < σ ∧
        ∀ (χ : Character) (s : ℂ), 0 < s.re →
          (s ≠ 1 ∨ χ.residue ≠ 1) → LFunction χ s = 0 →
            s.re ≤ beta - Supremum.continuationMargin beta ω σ) :
    beta ≤ 7 / 8 := by
  apply Supremum.seven_eighths_of_uniform_margin_with_sentinel zeroSet_bddAbove
  intro hbeta
  obtain ⟨ω, σ, hω, hωb, hσ, hzeros⟩ := hbound hbeta
  refine ⟨ω, σ, hω, hωb, hσ, ?_⟩
  rintro x ⟨χ, s, hpos, hpole, hz, rfl⟩
  exact hzeros χ s hpos hpole hz

end SevenEighths.HeckeZeroSupremum

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.Reciprocal -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem coefficients_sum_ne_zero_of_principal (χ : Character) (hχ : χ.residue = 1) :
    (∑ a, coefficients χ a) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  have heq : (∑ a, coefficients χ a) =
      (Nat.card (coordinateQuotientHom χ).ker : ℂ) *
        (Fintype.card (O ⧸ χ.modulus)ˣ : ℂ) := by
    calc
      _ = ∑ a, χ.residue (coordinateQuotientHom χ (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact coefficients_eq_quotient_character χ a
      _ = ∑ a : ZMod χ.period × ZMod χ.period,
          χ.residue (coordinateQuotientHom χ a) :=
        e.bijective.sum_comp (fun a => χ.residue (coordinateQuotientHom χ a))
      _ = _ := by
        rw [sum_comp_additiveHom _ (coordinateQuotientHom_surjective χ), hχ,
          MulChar.sum_one_eq_card_units]
  rw [heq]
  apply mul_ne_zero
  · exact_mod_cast (Nat.card_pos (α := (coordinateQuotientHom χ).ker)).ne'
  · exact_mod_cast (Fintype.card_pos (α := (O ⧸ χ.modulus)ˣ)).ne'

theorem dualScalar_ne_zero (N : ℕ) [NeZero N] : HeckeTheta.dualScalar N ≠ 0 := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  unfold HeckeTheta.dualScalar
  apply mul_ne_zero <;> apply Complex.ofReal_ne_zero.mpr
  · exact (Real.rpow_pos_of_pos (sq_pos_of_pos hN) _).ne'
  · exact (Real.rpow_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hN)) _).ne'

theorem principal_dual_constant_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    (HeckeTheta.pair (coefficients χ)).g₀ ≠ 0 := by
  rw [HeckeTheta.pair_g₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (dualScalar_ne_zero χ.period))
    (coefficients_sum_ne_zero_of_principal χ hχ)

def regularizedL (χ : Character) (s : ℂ) : ℂ :=
  HeckeTheta.regularizedLatticeL (coefficients χ) s / 6

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem regularizedL_at_one (χ : Character) :
    regularizedL χ 1 = (Real.pi : ℂ) * (HeckeTheta.pair (coefficients χ)).g₀ / 6 := by
  simp [regularizedL, HeckeTheta.regularizedLatticeL, HeckeTheta.regularizedCompleted]

theorem regularizedL_ne_zero_at_one (χ : Character) (hχ : χ.residue = 1) :
    regularizedL χ 1 ≠ 0 := by
  rw [regularizedL_at_one]
  exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (principal_dual_constant_ne_zero χ hχ)) (by norm_num)

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

theorem regularizedL_ne_zero (χ : Character) (hχ : χ.residue = 1) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regularizedL χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact regularizedL_ne_zero_at_one χ hχ
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  rw [regularizedL_eq χ h0 h1]
  exact mul_ne_zero (sub_ne_zero.mpr h1)
    (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inl h1))

def reciprocal (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then (s - 1) / regularizedL χ s else (LFunction χ s)⁻¹

theorem reciprocal_eq_inv (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    reciprocal χ s = (LFunction χ s)⁻¹ := by
  unfold reciprocal
  split_ifs
  · rw [regularizedL_eq χ h0 h1, div_mul_eq_div_div,
      div_self (sub_ne_zero.mpr h1), one_div]
  · rfl

theorem reciprocal_principal_one (χ : Character) (hχ : χ.residue = 1) :
    reciprocal χ 1 = 0 := by simp [reciprocal, hχ]

theorem reciprocal_differentiableAt (χ : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : DifferentiableAt ℂ (reciprocal χ) s := by
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  by_cases hχ : χ.residue = 1
  · have heq : reciprocal χ = fun z => (z - 1) / regularizedL χ z := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (differentiableAt_id.sub_const 1).div
      (regularizedL_differentiableAt χ h0) (regularizedL_ne_zero χ hχ hs)
  · have heq : reciprocal χ = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv
      (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inr hχ))

end SevenEighths.HeckeReciprocal

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

def factors (M : Ideal O) (ψ : Character) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => idealCoeff ψ P.val)

theorem factors_eq (M : Ideal O) (ψ : Character) (s : ℂ) :
    factors M ψ s = ∏ P ∈ SmoothMobiusCorrection.primeSet M,
      (1 - IdealEuler.weighted (idealCoeff ψ) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (M : Ideal O) (ψ : Character) :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem factors_ne_zero (M : Ideal O) (ψ : Character) {s : ℂ} (hs : 0 < s.re) :
    factors M ψ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val

theorem LFunction_eq_of_mask_right (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rw [LFunction_eq_series χ hs, LFunction_eq_series ψ hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (idealCoeff_norm_le_one ψ) hmask s hs

theorem regularizedL_analytic (χ : Character) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
  intro s hs
  exact (regularizedL_differentiableAt χ (by intro h; simp [h] at hs)).differentiableWithinAt

theorem regularizedL_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    regularizedL χ s = regularizedL ψ s * factors χ.modulus ψ s := by
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (regularizedL ψ) (factors χ.modulus ψ) (regularizedL χ)
    (regularizedL_analytic ψ) hf (regularizedL_analytic χ) _ hs
  intro z hz
  have hz' : 1 < z.re := by simpa using hz
  have h0 : z ≠ 0 := by intro h; norm_num [h] at hz'
  have h1 : z ≠ 1 := by intro h; norm_num [h] at hz'
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1,
    LFunction_eq_of_mask_right χ ψ hmask hz']
  ring

theorem LFunction_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h := regularizedL_eq_of_mask χ ψ hmask hs
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1, mul_assoc] at h
  exact mul_left_cancel₀ (sub_ne_zero.mpr h1) h

theorem regularizedL_one_ne_zero_iff (χ : Character) :
    regularizedL χ 1 ≠ 0 ↔ χ.residue = 1 := by
  constructor
  · intro h
    by_contra hχ
    rw [regularizedL_at_one,
      HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ),
      mul_zero, zero_div] at h
    exact h rfl
  · exact regularizedL_ne_zero_at_one χ

theorem principal_iff_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    χ.residue = 1 ↔ ψ.residue = 1 := by
  rw [← regularizedL_one_ne_zero_iff χ, ← regularizedL_one_ne_zero_iff ψ,
    regularizedL_eq_of_mask χ ψ hmask (by norm_num : 0 < (1 : ℂ).re),
    mul_ne_zero_iff, and_iff_left (factors_ne_zero χ.modulus ψ (by norm_num))]

theorem LFunction_eq_of_mask_nonprincipal (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha (η : Character) (hη : η.residue ≠ 1) :
      AnalyticOnNhd ℂ (LFunction η) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (LFunction_differentiableAt η (by intro h; simp [h] at hz)
      (Or.inr hη)).differentiableWithinAt
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (LFunction ψ) (factors χ.modulus ψ) (LFunction χ) (ha ψ hψ) hf (ha χ hχ) _ hs
  intro z hz
  exact (LFunction_eq_of_mask_right χ ψ hmask (by simpa using hz)).symm

theorem LFunction_eq_of_mask_nonpole (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rcases hpole with h1 | hχ
  · exact LFunction_eq_of_mask χ ψ hmask hs h1
  · exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

theorem exists_primitive_same_zeros (χ : Character) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ s : ℂ, 0 < s.re → s ≠ 1 →
        (LFunction χ s = 0 ↔ LFunction ψ s = 0) := by
  obtain ⟨ψ, hmod, hp, hnorm, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hmod, hp, hnorm, ?_⟩
  intro s hs h1
  rw [LFunction_eq_of_mask χ ψ hmask hs h1, mul_eq_zero]
  exact or_iff_left (factors_ne_zero χ.modulus ψ hs)

theorem exists_primitive_zero (χ : Character) {s : ℂ}
    (hs : 0 < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (s ≠ 1 ∨ ψ.residue ≠ 1) ∧ LFunction ψ s = 0 := by
  obtain ⟨ψ, _, hp, _, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, ?_, ?_⟩
  · rcases hpole with h1 | hχ
    · exact Or.inl h1
    · exact Or.inr (fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h))
  · rw [LFunction_eq_of_mask_nonpole χ ψ hmask hs hpole, mul_eq_zero] at hz
    exact hz.resolve_right (factors_ne_zero χ.modulus ψ hs)

end SevenEighths.HeckeFiniteDeletion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DeletionBounds -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionBounds
open HeckeFamily

theorem constant_pow_primeSupport_bound (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Ideal O, M ≠ ⊥ →
      K^(IdealMobiusDivisorSum.primeSupport M).card ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max K 1)
  have hn0 : 0 < (n : ℝ) := by linarith [le_max_right K 1]
  have hKpow : K ≤ (2 : ℝ)^n := by
    have hn2 : (n : ℝ) ≤ (2 : ℝ)^n := by exact_mod_cast (show n < 2^n from Nat.lt_two_pow_self).le
    linarith [le_max_left K 1]
  obtain ⟨C, hC, hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound
    (ε/(n : ℝ)) (div_pos hε hn0)
  refine ⟨C^n, by positivity, ?_⟩
  intro M hM
  calc
    _ ≤ ((2 : ℝ)^n)^(IdealMobiusDivisorSum.primeSupport M).card :=
      pow_le_pow_left₀ hK hKpow _
    _ = ((2 : ℝ)^(IdealMobiusDivisorSum.primeSupport M).card)^n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (C*(M.absNorm : ℝ)^(ε/(n : ℝ)))^n :=
      pow_le_pow_left₀ (by positivity) (hbound M hM) n
    _ = C^n*(M.absNorm : ℝ)^ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), div_mul_cancel₀ _ hn0.ne']

def localBound (σ : ℝ) : ℝ := (1-(2 : ℝ)^(-σ))⁻¹

theorem localBound_pos {σ : ℝ} (hσ : 0 < σ) : 0 < localBound σ := by
  unfold localBound
  exact inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

theorem term_bound {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖a*(N : ℂ)^(-s)‖ ≤ (2 : ℝ)^(-σ) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha).trans
  apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ N) (by linarith : -s.re ≤ -σ)).trans
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)

theorem factor_bounds {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖EulerFactors.factor N a s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor N a s)⁻¹‖ ≤ localBound σ := by
  have hδ : (2 : ℝ)^(-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hδ0 : 0 ≤ (2 : ℝ)^(-σ) := Real.rpow_nonneg (by norm_num) _
  have ht := term_bound hσ hN ha hs
  have hl : 1-(2 : ℝ)^(-σ) ≤ ‖EulerFactors.factor N a s‖ := by
    have hh := norm_sub_le (1-a*(N : ℂ)^(-s)) (-a*(N : ℂ)^(-s))
    have he : (1-a*(N : ℂ)^(-s))-(-a*(N : ℂ)^(-s)) = 1 := by ring
    rw [he, norm_one, neg_mul, norm_neg] at hh
    change 1-(2 : ℝ)^(-σ) ≤ ‖1-a*(N : ℂ)^(-s)‖
    linarith
  constructor
  · apply (norm_sub_le _ _).trans
    rw [norm_one]
    apply (add_le_add (le_refl 1) ht).trans
    unfold localBound
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr
    nlinarith [sq_nonneg ((2 : ℝ)^(-σ))]
  · rw [norm_inv]
    exact (inv_le_inv₀ (by linarith : 0 < ‖EulerFactors.factor N a s‖)
      (by linarith : 0 < 1-(2 : ℝ)^(-σ))).mpr hl

theorem factors_bound_pow (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card ∧
    ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
  have hfactor (P : SmoothMobiusCorrection.PrimeIdeal) :
      ‖EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s‖ ≤ localBound σ ∧
      ‖(EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val) s)⁻¹‖ ≤ localBound σ :=
    factor_bounds hσ (by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
      (idealCoeff_norm_le_one ψ P.val) hs
  have he : (∏ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ) =
      (localBound σ)^(IdealMobiusDivisorSum.primeSupport M).card := by
    rw [SmoothMobiusCorrection.prod_primeSet M (fun _ => localBound σ)]
    simp
  constructor
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).1)
  · unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
    rw [← Finset.prod_inv_distrib, norm_prod, ← he]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun P _ => (hfactor P).2)

theorem factors_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O), M ≠ ⊥ → ∀ (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*(M.absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := constant_pow_primeSupport_bound (localBound σ) ε
    (localBound_pos hσ).le hε
  refine ⟨2*C, by positivity, ?_⟩
  intro M hM ψ s hs
  obtain ⟨h1, h2⟩ := factors_bound_pow σ hσ M ψ hs
  have h := hb M hM
  nlinarith

def radical (M : Ideal O) : Ideal O :=
  SmoothMobiusCorrection.primeProduct (SmoothMobiusCorrection.primeSet M)

theorem radical_ne_zero (M : Ideal O) : radical M ≠ 0 :=
  SmoothMobiusCorrection.primeProduct_ne_zero _

theorem factors_radical (M : Ideal O) (ψ : Character) (s : ℂ) :
    HeckeFiniteDeletion.factors (radical M) ψ s = HeckeFiniteDeletion.factors M ψ s := by
  unfold HeckeFiniteDeletion.factors radical
  rw [SmoothMobiusCorrection.primeSet_primeProduct]

theorem factors_radical_subpower_bound (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      σ ≤ s.re → ‖HeckeFiniteDeletion.factors M ψ s‖ +
        ‖(HeckeFiniteDeletion.factors M ψ s)⁻¹‖ ≤ C*((radical M).absNorm : ℝ)^ε := by
  obtain ⟨C, hC, hb⟩ := factors_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s hs
  simpa only [factors_radical] using hb (radical M) (radical_ne_zero M) ψ s hs

theorem factor_bound_any_re {N : ℝ} (hN : 2 ≤ N) {a s : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖EulerFactors.factor N a s‖ ≤ 2*N^(max (-s.re) 0) := by
  have hn : 1 ≤ N := by linarith
  have ht : ‖a*(N : ℂ)^(-s)‖ ≤ N^(-s.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N), Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _) ha
  have hpow : N^(-s.re) ≤ N^(max (-s.re) 0) :=
    Real.rpow_le_rpow_of_exponent_le hn (le_max_left _ _)
  have h1 : 1 ≤ N^(max (-s.re) 0) := Real.one_le_rpow hn (le_max_right _ _)
  have hb := norm_sub_le (1 : ℂ) (a*(N : ℂ)^(-s))
  rw [norm_one] at hb
  change ‖1-a*(N : ℂ)^(-s)‖ ≤ _
  linarith

theorem factors_bound_any_re (M : Ideal O) (ψ : Character) (s : ℂ) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card *
        ((radical M).absNorm : ℝ)^(max (-s.re) 0) := by
  unfold HeckeFiniteDeletion.factors EulerFactors.deletedProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ P ∈ SmoothMobiusCorrection.primeSet M,
        2*(P.val.absNorm : ℝ)^(max (-s.re) 0) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      exact factor_bound_any_re (show (2 : ℝ) ≤ (P.val.absNorm : ℝ) by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
        (idealCoeff_norm_le_one ψ P.val)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

theorem primeSet_card (M : Ideal O) :
    (SmoothMobiusCorrection.primeSet M).card =
      (IdealMobiusDivisorSum.primeSupport M).card := by
  unfold SmoothMobiusCorrection.primeSet
  rw [Finset.card_image_iff.mpr ?_, Finset.card_attach]
  intro P hP Q hQ h
  exact Subtype.ext (congrArg (fun R : SmoothMobiusCorrection.PrimeIdeal => R.val) h)

theorem factors_any_re_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Ideal O) (ψ : Character) (s : ℂ),
      ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
        C*((radical M).absNorm : ℝ)^(max (-s.re) 0 + ε) := by
  obtain ⟨C, hC, hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M ψ s
  have hR : 0 < ((radical M).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))
  have hc : (2 : ℝ)^(SmoothMobiusCorrection.primeSet M).card ≤ C*((radical M).absNorm : ℝ)^ε := by
    have h := hb (radical M) (radical_ne_zero M)
    rw [← primeSet_card, radical, SmoothMobiusCorrection.primeSet_primeProduct] at h
    exact h
  apply (factors_bound_any_re M ψ s).trans
  calc
    _ ≤ (C*((radical M).absNorm : ℝ)^ε)*((radical M).absNorm : ℝ)^(max (-s.re) 0) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [Real.rpow_add hR]; ring

end SevenEighths.HeckeDeletionBounds

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DeletionDerivative -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionDerivative
open HeckeFamily HeckeDeletionBounds

theorem factor_deriv {N : ℝ} (hN : 0 < N) (a s : ℂ) :
    deriv (EulerFactors.factor N a) s = a*(N : ℂ)^(-s)*Complex.log (N : ℂ) := by
  have h := (hasDerivAt_const s (1 : ℂ)).sub
    (((hasDerivAt_id s).neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))).const_mul a)
  have h' : HasDerivAt (EulerFactors.factor N a)
      (a*(N : ℂ)^(-s)*Complex.log (N : ℂ)) s := by
    convert h using 1
    · funext z
      rfl
    · dsimp
      ring
  exact h'.deriv

theorem factor_logDeriv_norm {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖logDeriv (EulerFactors.factor N a) s‖ ≤ localBound σ * Real.log N := by
  have hn0 : 0 < N := by linarith
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have ht := term_bound hσ hN ha hs
  have hδ : (2 : ℝ)^(-σ) ≤ 1 :=
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  have hf := (factor_bounds hσ hN ha hs).2
  rw [logDeriv_apply, factor_deriv hn0, div_eq_mul_inv, norm_mul, norm_mul,
    ← Complex.ofReal_log hn0.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hterm : ‖a*(N : ℂ)^(-s)‖ ≤ 1 := ht.trans hδ
  calc
    _ ≤ (1*Real.log N)*localBound σ := by gcongr
    _ = _ := by ring

theorem factors_logDeriv_norm (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖logDeriv (HeckeFiniteDeletion.factors M ψ) s‖ ≤
      localBound σ * Real.log ((radical M).absNorm : ℝ) := by
  have hp0 (P : SmoothMobiusCorrection.PrimeIdeal) : 0 < (P.val.absNorm : ℝ) := by
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 0 < P.val.absNorm)
  have hp2 (P : SmoothMobiusCorrection.PrimeIdeal) : 2 ≤ (P.val.absNorm : ℝ) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have he : logDeriv (HeckeFiniteDeletion.factors M ψ) s =
      ∑ P ∈ SmoothMobiusCorrection.primeSet M,
        logDeriv (EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val)) s := by
    apply logDeriv_fun_prod
    · intro P _
      exact EulerFactors.factor_ne_zero (by linarith [hp2 P]) (idealCoeff_norm_le_one ψ P.val)
        (hσ.trans_le hs)
    · intro P _
      exact EulerFactors.differentiable_factor (hp0 P) _ s
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ*Real.log (P.val.absNorm : ℝ) := by
      apply Finset.sum_le_sum
      intro P _
      exact factor_logDeriv_norm hσ (hp2 P) (idealCoeff_norm_le_one ψ P.val) hs
    _ = localBound σ * Real.log ((radical M).absNorm : ℝ) := by
      rw [← Finset.mul_sum, ← Real.log_prod (fun P _ => (hp0 P).ne')]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

end SevenEighths.HeckeDeletionDerivative

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DeletionReciprocal -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDeletionReciprocal
open HeckeFamily HeckeFiniteDeletion HeckeReciprocal HeckeDeletionBounds

theorem reciprocal_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    reciprocal χ s = reciprocal ψ s * (factors χ.modulus ψ s)⁻¹ := by
  by_cases hχ : χ.residue = 1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [reciprocal, ite_eq_left hχ, ite_eq_left hψ]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    simp only [reciprocal, ite_eq_right hχ, ite_eq_right hψ]
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs, mul_inv]

theorem exists_primitive_reciprocal_reduction (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : Character,
      ∃ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
        (∀ I : Ideal O, idealCoeff χ I =
          if IsCoprime I χ.modulus then idealCoeff ψ I else 0) ∧
        ∀ s : ℂ, σ ≤ s.re →
          ‖reciprocal χ s‖ ≤ C*((radical χ.modulus).absNorm : ℝ)^ε * ‖reciprocal ψ s‖ := by
  obtain ⟨C, hC, hb⟩ := factors_radical_subpower_bound σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro χ
  obtain ⟨ψ, _, hp, hn, hm⟩ := exists_primitive_character χ
  refine ⟨ψ, hp, hn, hm, ?_⟩
  intro s hs
  rw [reciprocal_eq_of_mask χ ψ hm (hσ.trans_le hs), norm_mul]
  have hf := hb χ.modulus ψ s hs
  have hfb : ‖(factors χ.modulus ψ s)⁻¹‖ ≤ C*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ s)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hfb (norm_nonneg (reciprocal ψ s))

end SevenEighths.HeckeDeletionReciprocal

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFamily
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def Character.refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) : Character :=
  Character.ofResidue M hM (ResidueCharacter.inflate hle η.residue)
    (ResidueCharacter.inflate_global_units hle η.residue η.unit_trivial)

theorem elementCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (n : O) :
    elementCoeff (η.refineModulus M hM hle) n =
      if IsUnit (Ideal.Quotient.mk M n) then elementCoeff η n else 0 :=
  ResidueCharacter.inflate_mk hle η.residue n

theorem idealCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (I : Ideal O) :
    idealCoeff (η.refineModulus M hM hle) I =
      if IsCoprime I M then idealCoeff η I else 0 :=
  IdealCharacter.ofResidue_source_mask M η.modulus _ _ _ _
    (ResidueCharacter.inflate_mk hle η.residue) I

theorem idealCoeff_source_mask (η : Character) (I : Ideal O) :
    idealCoeff η I = if IsCoprime I η.modulus then idealCoeff η I else 0 := by
  apply IdealCharacter.ofResidue_source_mask η.modulus η.modulus η.residue η.residue
    η.unit_trivial η.unit_trivial _ I
  intro n
  split_ifs with hn
  · rfl
  · exact MulChar.map_nonunit _ hn

def Character.excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : Character :=
  η.refineModulus (η.modulus * ∏ P ∈ S, P)
    (mul_ne_zero η.modulus_ne_bot (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))
    Ideal.mul_le_left

theorem idealCoeff_excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    idealCoeff (η.excludePrimes S hS) I =
      if ∀ P ∈ S, IsCoprime I P then idealCoeff η I else 0 := by
  rw [Character.excludePrimes, idealCoeff_refineModulus, IsCoprime.mul_right_iff,
    IsCoprime.prod_right_iff]
  by_cases hη : IsCoprime I η.modulus
  · simp only [hη, true_and]
  · have hz : idealCoeff η I = 0 := by simpa only [hη, ite_false] using idealCoeff_source_mask η I
    simp [hη, hz]

theorem excludePrimes_mask (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    idealCoeff (η.excludePrimes S hS) I =
      if IsCoprime I (η.excludePrimes S hS).modulus then idealCoeff η I else 0 :=
  idealCoeff_refineModulus η _ _ _ I

end SevenEighths.HeckeFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.Origin -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeOrigin
open HeckeFamily HeckeTheta

def poleRemoved (χ : Character) (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^s * (Complex.Gamma (s+1))⁻¹ *
    HeckeMellinIdentity.regularized (pair (coefficients χ)) s / 6

theorem poleRemoved_entire (χ : Character) : Differentiable ℂ (poleRemoved χ) := by
  have hGamma : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s+1))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul hGamma).mul
      (HeckeMellinIdentity.regularized_entire _)).div_const 6

theorem poleRemoved_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    poleRemoved χ s = (s-1) * LFunction χ s := by
  unfold poleRemoved LFunction continuedLattice latticeL completed
  rw [HeckeMellinIdentity.regularized_eq _ (pair_k _) h0 h1,
    Complex.Gamma_add_one s h0, mul_inv_rev]
  field_simp

theorem poleRemoved_zero (χ : Character) :
    poleRemoved χ 0 = coefficients χ (0,0) / 6 := by
  simp [poleRemoved, HeckeMellinIdentity.regularized, pair_f₀]

theorem poleRemoved_one (χ : Character) :
    poleRemoved χ 1 = HeckeReciprocal.regularizedL χ 1 := by
  rw [HeckeReciprocal.regularizedL_at_one]
  simp [poleRemoved, HeckeMellinIdentity.regularized,
    Complex.Gamma_add_one 1 one_ne_zero,
    show (pair (coefficients χ)).ε = 1 from rfl]

theorem poleRemoved_one_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    poleRemoved χ 1 ≠ 0 := by
  rw [poleRemoved_one]
  exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ

def continued (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then poleRemoved χ s / (s-1) else LFunction χ s

theorem continued_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    continued χ s = LFunction χ s := by
  unfold continued
  split_ifs
  · rw [poleRemoved_eq χ h0 h1, mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)]
  · rfl

theorem continued_differentiableAt (χ : Character) {s : ℂ}
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : DifferentiableAt ℂ (continued χ) s := by
  by_cases hχ : χ.residue = 1
  · have heq : continued χ = fun z => poleRemoved χ z / (z-1) := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact (poleRemoved_entire χ s).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr (hpole.resolve_right (not_not.mpr hχ)))
  · have heq : continued χ = LFunction χ := by
      funext z
      simp [continued, hχ]
    rw [heq]
    exact ((HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6) s

theorem continued_zero (χ : Character) : continued χ 0 = -coefficients χ (0,0) / 6 := by
  by_cases hχ : χ.residue = 1
  · simp [continued, hχ, poleRemoved_zero]
    ring
  · rw [HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal χ hχ]
    simp [continued, hχ, LFunction, continuedLattice, latticeL, Complex.Gamma_zero]

end SevenEighths.HeckeOrigin

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimitiveSupremum
open HeckeFamily HeckeZeroSupremum

def primitiveZeroRealParts : Set ℝ :=
  {x | ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
    (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
    LFunction χ s = 0 ∧ s.re = x}

def primitiveSetWithSentinel : Set ℝ := insert (1 / 2) primitiveZeroRealParts

theorem primitiveSet_subset : primitiveSetWithSentinel ⊆ zeroSetWithSentinel := by
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact Set.mem_insert _ _
  · obtain ⟨χ, s, _, hhalf, _, hpole, hz, rfl⟩ := hx
    exact Set.mem_insert_of_mem _ ⟨χ, s, by linarith, hpole, hz, rfl⟩

theorem primitiveSet_bddAbove : BddAbove primitiveSetWithSentinel :=
  zeroSet_bddAbove.mono primitiveSet_subset

theorem primitiveSet_nonempty : primitiveSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem beta_eq_primitive_supremum : beta = sSup primitiveSetWithSentinel := by
  apply le_antisymm
  · apply csSup_le zeroSet_nonempty
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact le_csSup primitiveSet_bddAbove (Set.mem_insert _ _)
    · by_cases hhalf : (1 / 2 : ℝ) ≤ x
      · obtain ⟨χ, s, hpos, hpole, hz, rfl⟩ := hx
        obtain ⟨ψ, hp, hpoleψ, hzψ⟩ :=
          HeckeFiniteDeletion.exists_primitive_zero χ hpos hpole hz
        apply le_csSup primitiveSet_bddAbove
        exact Set.mem_insert_of_mem _ ⟨ψ, s, hp, hhalf,
          zeroRealParts_le_one ⟨χ, s, hpos, hpole, hz, rfl⟩, hpoleψ, hzψ, rfl⟩
      · exact (le_of_not_ge hhalf).trans
          (le_csSup primitiveSet_bddAbove (Set.mem_insert _ _))
  · exact csSup_le_csSup zeroSet_bddAbove primitiveSet_nonempty primitiveSet_subset

theorem exists_primitive_zero_near_beta {ε : ℝ} (hε : 0 < ε)
    (hsmall : (1 / 2 : ℝ) ≤ beta - ε) :
    ∃ (χ : Character) (s : ℂ), FiniteFourier.IsPrimitiveOnIdeals χ.residue ∧
      (1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ (s ≠ 1 ∨ χ.residue ≠ 1) ∧
      LFunction χ s = 0 ∧ beta - ε < s.re := by
  rw [beta_eq_primitive_supremum] at hsmall ⊢
  obtain ⟨x, hx, hlt⟩ := Supremum.exists_gt_supremum_sub_of_insert
    primitiveSet_bddAbove hε hsmall
  obtain ⟨χ, s, hp, hhalf, hone, hpole, hz, rfl⟩ := hx
  exact ⟨χ, s, hp, hhalf, hone, hpole, hz, hlt⟩

end SevenEighths.HeckePrimitiveSupremum

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.ReciprocalBound -/

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

def bound (σ : ℝ) : ℝ :=
  ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖CubicEisenstein.fullIdealWeight s I‖ ≤
      ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖ := by
  by_cases hI : I = 0
  · simp [hI, CubicEisenstein.fullIdealWeight]
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [CubicEisenstein.fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

theorem reciprocal_norm_le (χ : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖HeckeReciprocal.reciprocal χ s‖ ≤ bound σ := by
  have hs1 : 1 < s.re := hσ.trans_le hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have hsp : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeReciprocal.reciprocal_eq_inv χ hs0 hsp, LFunction_eq_series χ hs1,
    ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs1]
  have hsum := IdealEuler.inverse_summable_norm (idealCoeff χ)
    (idealCoeff_norm_le_one χ) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖(UniqueFactorizationMonoid.moebius I : ℂ) *
    (idealCoeff χ I * CubicEisenstein.fullIdealWeight s I)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖CubicEisenstein.fullIdealWeight s I‖ := by
      apply (mul_le_of_le_one_left (by positivity)
        (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)
    _ ≤ _ := normWeight_le_of_re_ge hs I

end SevenEighths.HeckeReciprocalBound

end

end OAI

end

