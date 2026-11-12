module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part021
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.PrincipalEulerIdentity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma evenRatio_eq_coordR (Q : ℝ) (hQ : 0<Q) (a x z : ℂ) :
    evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z) = coordR Q (a^2) x z := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold evenRatio coordR coordV
  calc
    _ = a^2 * ((Q:ℂ)^4 * ((Q:ℂ)^(-x))^6 * (Q:ℂ)^(-6*z)) := by ring
    _ = a^2 * ((Q:ℂ)^(4:ℂ) * (Q:ℂ)^((6:ℂ)*(-x)) * (Q:ℂ)^(-6*z)) := by
      rw [Complex.cpow_ofNat]
      have h6 : (Q:ℂ)^((6:ℂ)*(-x)) = ((Q:ℂ)^(-x))^6 := by
        simpa using Complex.cpow_nat_mul (Q:ℂ) 6 (-x)
      rw [h6]
    _ = a^2 * (Q:ℂ)^((4:ℂ)+6*(-x)+(-6*z)) := by
      rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
    _ = _ := by congr 2; ring

lemma coordK_eq_geometric (Q : ℝ) (hQ : 0<Q) (eta x w : ℂ) :
    coordK Q eta x w = eta*((Q:ℂ)-1)*((Q:ℂ)^(-x))*((Q:ℂ)^(-w)) := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold coordK
  rw [show -x-w = -x+(-w) by ring, Complex.cpow_add _ _ hn]
  ring

lemma one_sub_ne_zero_of_norm_lt_one (a : ℂ) (ha : ‖a‖<1) : 1-a ≠ 0 := by
  intro h
  have he : a=1 := by linear_combination -h
  rw [he, norm_one] at ha
  exact lt_irrefl _ ha

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalFullSeries (eta a X W V : ℂ) : ℂ :=
  1/(1-V)+W/(1-W)+principalMarkedSeries p hp hg eta a X W V

include hc

theorem principalFullSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  dsimp only
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simp only [Complex.ofReal_natCast]
  have hratio := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hratio
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hratio]
    exact hR
  rw [principalFullSeries, principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV hr,
    hratio]
  unfold unramifiedClosed
  dsimp only
  rw [coordK_eq_geometric _ hQ]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [coordW, coordD, star_one, mul_one, one_mul, Complex.ofReal_natCast] at hD hw ⊢
  unfold ProbeLocal.continuedCorrection
  field_simp [hD, hv, hw]
  ring

omit hc

def actualACube (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p)^3 * HeckeFamily.elementCoeff eta p^3

lemma actualACube_sq (eta : HeckeFamily.Character) (p : O) :
    actualACube eta p ^ 2 = actualAPhase eta p := by
  unfold actualACube actualAPhase
  ring

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PrincipalProduct -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection
local notation "O" => ActualEisensteinCubic.O

def primeDefectBound (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ (-(363/200:ℝ))

def principalLocal (eta : HeckeFamily.Character) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase eta (primaryGenerator P.val))
    (HeckeFamily.elementCoeff eta (primaryGenerator P.val)) 1 s 1 (1/6)

def principalCorrection (eta : HeckeFamily.Character) (S : Finset (Ideal O)) (s : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val ∉ S}, principalLocal eta P.val s

lemma primeDefectBound_nonneg (P : PrimeIdeal) : 0 ≤ primeDefectBound P := by
  unfold primeDefectBound
  positivity

lemma primeDefectBound_summable : Summable primeDefectBound := by
  have h : Summable (fun P : PrimeIdeal => ‖CubicEisenstein.fullIdealWeight ((363/200:ℝ):ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm ((363/200:ℝ):ℂ) (by norm_num)).comp_injective
      Subtype.val_injective
  apply (h.mul_left 240).congr
  intro P
  unfold primeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero, ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

lemma principalLocal_bound (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (s : ℂ) (hs : 7/8 < s.re) :
    ‖principalLocal eta P s-1‖ ≤ primeDefectBound P := by
  apply unramifiedClosed_second_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _
  · simp
  · exact hs.le
  · norm_num
  · norm_num

lemma principalLocal_analytic (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (principalLocal eta P) {s : ℂ | 7/8 < s.re} := by
  apply principalClosed_analytic
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _

theorem exists_uniform_principal_cutoff :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ (S : Finset (Ideal O)),
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | 7/8 < s.re} ∧
        ∀ s : ℂ, 7/8 < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero primeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F, hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro S hS eta
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    apply P.property
    apply hS P.val
    exact (Finset.le_sup (f := fun Q : PrimeIdeal => Ideal.absNorm Q.val) hm).trans (le_max_right _ _)
  let inc : T → {P : PrimeIdeal // P ∉ F} := fun P => ⟨P.val, hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun t : {P : PrimeIdeal // P ∉ F} => t.val) h
  have hnorm (P : T) : 4 ≤ Ideal.absNorm P.val.val := by
    have hh : ¬ Ideal.absNorm P.val.val ≤ N := fun h => P.property (hS P.val h)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T => primeDefectBound P.val) :=
    primeDefectBound_summable.subtype _
  have hsmall : (∑' P : T, primeDefectBound P.val) ≤ 1/6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => primeDefectBound_nonneg P.val) (fun _ => le_rfl)
      hsum (primeDefectBound_summable.subtype _)
  have hhalf (P : T) : primeDefectBound P.val ≤ 1/2 := by
    have hterm := Summable.le_tsum hsum P (fun Q _ => primeDefectBound_nonneg Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun P : T => principalLocal eta P.val)
      (fun P : T => primeDefectBound P.val) _ (Complex.isOpen_re_gt _) hsum
      (fun P => principalLocal_analytic eta P.val (hnorm P))
      (fun P s hs => principalLocal_bound eta P.val (hnorm P) s hs) hhalf
  · intro s hs
    exact product_defect_le (fun P : T => principalLocal eta P.val s)
      (fun P : T => primeDefectBound P.val) hsum
      (fun P => principalLocal_bound eta P.val (hnorm P) s hs) hhalf hsmall

def smallPrimeSet (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le N).toFinset.filter Prime

lemma mem_smallPrimeSet (N : ℕ) (P : PrimeIdeal) :
    P.val ∈ smallPrimeSet N ↔ Ideal.absNorm P.val ≤ N := by
  simp [smallPrimeSet, P.property]

theorem exists_principal_correction (S₀ : Finset (Ideal O)) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ ∀ eta : HeckeFamily.Character,
      AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | 7/8 < s.re} ∧
      ∀ s : ℂ, 7/8 < s.re → ‖principalCorrection eta S s-1‖ ≤ 1/2 := by
  obtain ⟨N, hN, hcut⟩ := exists_uniform_principal_cutoff
  refine ⟨S₀ ∪ smallPrimeSet N, Finset.subset_union_left, ?_⟩
  apply hcut
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RowAnalytic -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem fullIdealWeight_norm_eq_of_re (s t : ℂ) (h : s.re = t.re) (I : Ideal O) :
    ‖fullIdealWeight s I‖ = ‖fullIdealWeight t I‖ := by
  by_cases hI : I = 0
  · simp [hI, fullIdealWeight]
  · exact (norm_fullIdealWeight s ⟨I, hI⟩).trans
      ((by rw [h] : _ = _).trans (norm_fullIdealWeight t ⟨I, hI⟩).symm)

theorem fullIdealWeight_continuous (I : Ideal O) : Continuous (fun t => fullIdealWeight t I) := by
  by_cases hI : I = 0
  · simp only [hI, fullIdealWeight]
    exact continuous_const
  · have hn : (Ideal.absNorm I : ℂ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_ne_zero_iff I).mpr
        (Ring.HasFiniteQuotients.finiteQuotient hI)
    simp only [fullIdealWeight, ite_eq_right hI]
    exact continuous_id.neg.const_cpow (Or.inl hn)

def rowMajorant (σ : ℝ) (p : Ideal O × Ideal O) : ℝ :=
  2 * (‖fullIdealWeight (σ : ℂ) p.1‖ * ‖fullIdealWeight (3 * (σ : ℂ)) p.2‖)

theorem rowMajorant_summable (σ : ℝ) (hσ : 1 < σ) : Summable (rowMajorant σ) := by
  have h3 : 1 < (3 * (σ : ℂ)).re := by norm_num; linarith
  exact ((fullIdealWeight_summable_norm (σ : ℂ) hσ).mul_of_nonneg
    (fullIdealWeight_summable_norm (3 * (σ : ℂ)) h3)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2

theorem spectralSummand_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ y : ℝ) (p : Ideal O × Ideal O) :
    ‖spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2‖ ≤ rowMajorant σ p := by
  have h1 : ((σ : ℂ) + y * Complex.I).re = (σ : ℂ).re := by simp
  have h3 : (3 * ((σ : ℂ) + y * Complex.I)).re = (3 * (σ : ℂ)).re := by simp
  simpa only [rowMajorant, fullIdealWeight_norm_eq_of_re _ _ h1,
    fullIdealWeight_norm_eq_of_re _ _ h3] using
    spectralSummand_norm_le S D Ψ hΨ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem spectralRow_continuous_vertical (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) :
    Continuous (fun y : ℝ => spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  apply continuous_tsum _ (rowMajorant_summable σ hσ)
    (fun p y => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
  intro p
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  exact continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
    ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))

theorem spectralRow_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ) (y : ℝ) :
    ‖spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)‖ ≤ ∑' p, rowMajorant σ p := by
  have hs := spectralRow_summable S D Ψ hΨ ((σ : ℂ) + y * Complex.I) (by simpa using hσ)
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum (fun p => spectralSummand_vertical_bound S D Ψ hΨ σ y p)
      (rowMajorant_summable σ hσ))

theorem verticalKernel_norm (Z : ℝ) (hZ : 0 < Z) (σ y : ℝ) :
    ‖(Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2)‖ =
      Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : (((σ : ℂ) + y * Complex.I) ^ 2).re = σ ^ 2 + (-1 * y ^ 2) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [hre, Real.exp_add]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

theorem spectralRow_vertical_integrable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) := by
  let B : ℝ := ∑' p, rowMajorant σ p
  have hg := (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * B)
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply hg.mono' (hk.mul (spectralRow_continuous_vertical S D Ψ hΨ σ hσ)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [Pi.mul_apply, Pi.pow_apply]
  rw [norm_mul, verticalKernel_norm Z hZ σ y]
  calc
    _ ≤ (Z ^ σ * Real.exp (σ ^ 2) * Real.exp (-1 * y ^ 2)) * B :=
      mul_le_mul_of_nonneg_left (spectralRow_vertical_bound S D Ψ hΨ σ hσ y)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le) (Real.exp_pos _).le)
    _ = _ := by ring

end SevenEighths.ProbeRow
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem CalibrationData.residueMonoid_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

theorem CalibrationData.Xi_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.Xi a‖ ≤ 1 := by
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans
    (idealRowHom_norm _ _)

theorem CalibrationData.Xi_norm_one (C : CalibrationData) (a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    ‖C.Xi a‖ = 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hu := (CubicEisenstein.isUnit_quotient_span_iff C.generator a).mpr hcop
  have hξ : ‖C.residueMonoid a‖ = 1 := by
    exact (FiniteRayExpansion.norm_char_unit C.residue hu.unit)
  have hc : IsCoprime (Ideal.span {a} : Ideal O) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff a C.generator).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask C.generator (Ideal.span {a}) ha
  rw [idealRowHom_argument_pow _ _ _ ha, ite_eq_left hc] at h6
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ = 1
  rw [norm_mul, hξ, Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0), mul_one]

theorem calibrated_rowCoefficient_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    rowCoefficient η C.Xi s hs m a = HeckeFamily.elementCoeff η a * (C.Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  rowCoefficient_apply_unit η C.Xi s hs m a (C.Xi_norm_one a ha hcop)

theorem physicalRow_integrable (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s})) (m : O)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((4 : ℂ) + y * Complex.I) *
      Complex.exp (((4 : ℂ) + y * Complex.I) ^ 2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) ((4 : ℂ) + y * Complex.I)) := by
  exact spectralRow_vertical_integrable C.excluded D (rowCoefficient η C.Xi s hs m)
    (fun a => rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m a)
    4 (by norm_num) Z hZ

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CalibrationSupport -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

theorem calibrationForSet_coprime_of_excluded (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (a : O)
    (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    IsCoprime (calibrationForSet S hS).generator a := by
  apply (calibrationForSet_coprime_iff S hS a).mpr
  intro P hP ha
  apply hmask P hP
  exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

theorem source_rowCoefficient_apply (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    rowCoefficient η (calibrationForSet S hS).Xi s hs m a =
      HeckeFamily.elementCoeff η a * ((calibrationForSet S hS).Xi a)⁻¹ *
        sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  calibrated_rowCoefficient_apply η (calibrationForSet S hS) s hs m a ha
    (calibrationForSet_coprime_of_excluded S hS a hmask)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowPeriod -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def calibrationRowModulus (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : Id :=
  1*Ideal.span {B}*Ideal.span {(72:O)}*Ideal.span {D.numeratorGood}

def periodicCalibrationXi (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact D.numeratorSupported.1

lemma periodicCalibrationXi_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (a : O) : ‖periodicCalibrationXi C B D a‖≤1 := by
  rw [periodicCalibrationXi,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported a)

lemma periodicCalibrationXi_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (periodicCalibrationXi C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change C.residueMonoid x*_ = C.residueMonoid y*_
  congr 1
  · apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)

lemma periodicCalibrationXi_eq_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    periodicCalibrationXi C B D n=C.Xi n := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hmask : coprimalityMask B n=(1:ℂ) := by
    change (if IsCoprime B n then (1:ℂ) else 0)=1
    rw [ite_eq_left hc]
  simp only [MonoidHom.one_apply,hmask,one_mul,one_pow] at he
  change C.residueMonoid n*_ = C.residueMonoid n*idealRowHom C.generator (Ideal.span {n})
  rw [←he]

def lowPeriodicBase (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) : O→*ℂ :=
  rayMonoid χ*targetMonoid η*conjugateMonoid (periodicCalibrationXi C B D)*reciprocityPhaseMonoid s hs

def lowBaseModulus (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) : Id :=
  η.modulus*(Ideal.span {C.generator}*calibrationRowModulus C B D)*Ideal.span {(4:O)}

lemma lowBaseModulus_ne_zero (η : HeckeFamily.Character) (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : lowBaseModulus η C B D≠0 := by
  unfold lowBaseModulus
  apply mul_ne_zero
  · exact mul_ne_zero η.modulus_ne_bot (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
      (calibrationRowModulus_ne_zero C B hB D))
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowPeriodicBase_periodic (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) :
    FactorsModulo (lowBaseModulus η C B D) (lowPeriodicBase η C B D s hs χ) := by
  intro x y hxy
  have h4 : (4:O)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy)
  have hη : targetMonoid η x=targetMonoid η y := by
    apply congrArg η.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hc := periodicCalibrationXi_periodic C B D x y (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  change ((rayMonoid χ x*targetMonoid η x)*star (periodicCalibrationXi C B D x))*
      sexticReciprocityPhase s x=
    ((rayMonoid χ y*targetMonoid η y)*star (periodicCalibrationXi C B D y))*sexticReciprocityPhase s y
  rw [hη,hc,sexticReciprocityPhase_congr_right s x y h4]
  have hr : rayMonoid χ x=rayMonoid χ y := rayCharacter_eq_of_mod_four χ x y h4
  rw [hr]

lemma lowPeriodicBase_norm (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (a : O) : ‖lowPeriodicBase η C B D s hs χ a‖≤1 := by
  have hr : ‖rayMonoid χ a‖≤1 := FiniteRayExpansion.norm_char_le_one χ _
  change ‖((rayMonoid χ a*targetMonoid η a)*star (periodicCalibrationXi C B D a))*sexticReciprocityPhase s a‖≤1
  simp only [norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) hr).trans (targetMonoid_norm_le_one η a))).trans (periodicCalibrationXi_norm C B D a))).trans (sexticReciprocityPhase_norm s a)

lemma lowPeriodicBase_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    lowPeriodicBase η C B D s hs χ n=(rayMonoid χ*physicalRowBase η C.Xi s hs) n := by
  change ((rayMonoid χ n*targetMonoid η n)*star (periodicCalibrationXi C B D n))*sexticReciprocityPhase s n=
    rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)
  rw [periodicCalibrationXi_eq_primary C B D hBL hB2 n hn hpn hc]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowPuncture -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_generator_dvd (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (a : O) (ha : Ideal.span {a}∈S) : a∣(calibrationForSet S hS).generator := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
  rw [calibrationForSet_span]
  exact Finset.dvd_prod_of_mem (fun P : Id=>P) ha

lemma calibration_generator_bad (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    λ₀∣(calibrationForSet S hS).generator ∧ (2:O)∣(calibrationForSet S hS).generator := by
  constructor
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl rfl
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr trivial

lemma supported_of_coprime_bad (B n : O) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (hc : IsCoprime B n) : Supported (Ideal.span {n}) := by
  apply supported_span_iff n |>.mpr
  constructor
  · exact PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp
      (hc.of_isCoprime_of_dvd_left hBL)
  · have h2 : IsCoprime (-2:O) n := (hc.of_isCoprime_of_dvd_left hB2).neg_left
    have hn := negative_two_prime.irreducible.coprime_iff_not_dvd.mp h2
    simpa only [neg_dvd] using hn

lemma lowPeriodicBase_zero_of_not_coprime (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (n : O) (hc : ¬IsCoprime B n) : lowPeriodicBase η C B D s hs χ n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
  change ((rayMonoid χ n*targetMonoid η n)*star (C.residueMonoid n*
      ((((1:O→*ℂ) n*coprimalityMask B n)*
        numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
        movingNumeratorRow D.numeratorGood D.numeratorSupported n)))*sexticReciprocityPhase s n=0
  rw [hm]
  simp only [mul_zero,zero_mul,star_zero]

lemma lowPeriodicRow_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) (z n : O) (hpn : λ₀^2∣n-1) :
    rowTwist (lowPeriodicBase η C B D s hs χ) B 1 z n=
      (coprimalityMask B*(rayMonoid χ*rowCoefficient η C.Xi s hs z)) n := by
  by_cases hc : IsCoprime B n
  · have hn := supported_of_coprime_bad B n hBL hB2 hc
    have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [ite_eq_left hc]
    rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn,lowPeriodicBase_eq_primary η C B D hBL hB2 s hs χ n hn hpn hc]
    simp only [MonoidHom.mul_apply,hm,mul_one,one_pow,one_mul]
    change (rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n))*
      idealRowHom z (Ideal.span {n})=rayMonoid χ n*
        (((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)*idealRowHom z (Ideal.span {n}))
    ring
  · have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
    change lowPeriodicBase η C B D s hs χ n*idealRowHom (B^6*1^4*z) (Ideal.span {n})=
      coprimalityMask B n*(rayMonoid χ n*rowCoefficient η C.Xi s hs z n)
    rw [lowPeriodicBase_zero_of_not_coprime η C B D s hs χ n hc,hm,zero_mul,zero_mul]

lemma calibration_coprime_iff_excluded_span (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (a : O) :
    IsCoprime (calibrationForSet S hS).generator a ↔ ∀P∈S,¬P∣Ideal.span {a} := by
  rw [calibrationForSet_coprime_iff]
  constructor
  · intro h P hP hd
    exact h P hP (Ideal.dvd_iff_le.mp hd (Ideal.subset_span (by simp)))
  · intro h P hP ha
    apply h P hP
    exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowCompletion -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma summand_zero_completedIndex (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id)
    (h : completedIndex I J=0) : summand Ψ W X I J=0 := by
  have hprod : primaryGenerator I*primaryGenerator J^3=0 := h
  rcases mul_eq_zero.mp hprod with hI|hJ
  · simp only [summand,columnWeight,squarefreeGaussCoefficient,hI,ne_eq,not_true_eq_false,
      and_false,dite_false,zero_mul,zero_div]
  · have hj : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        Ψ (primaryGenerator J)^3/(Ideal.absNorm J:ℂ)=0
      simp only [hj,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
        div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
    simp only [summand,hc,mul_zero,zero_mul]

lemma markedSummand_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id) :
    markedSummand S D Ψ W X I J=
      summand (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X I J*
        (if D∣I*J^3 then (1:ℂ) else 0) := by
  rw [summand_mul_fixed_twist]
  change completedMask S D I J*summand Ψ W X I J=
    coprimalityMask (calibrationForSet S hS).generator (completedIndex I J)*summand Ψ W X I J*
      (if D∣I*J^3 then (1:ℂ) else 0)
  by_cases hA : completedIndex I J=0
  · rw [summand_zero_completedIndex Ψ W X I J hA]
    simp only [mul_zero,zero_mul]
  · have he := calibration_coprime_iff_excluded_span S hS (completedIndex I J)
    rw [completedIndex_eq_primaryGenerator] at he hA
    rw [(primaryGenerator_spec (I*J^3) hA).1] at he
    change _=(if IsCoprime (calibrationForSet S hS).generator (completedIndex I J) then (1:ℂ) else 0)*_ * _
    rw [completedIndex_eq_primaryGenerator,he]
    unfold completedMask
    by_cases hd : D∣I*J^3 <;> by_cases hx : ∀P∈S,¬P∣I*J^3 <;>
      simp only [hd,hx,and_self,and_false,true_and,false_and,ite_true,ite_false,mul_one,mul_zero,zero_mul] ; simp_all

lemma markedCompletedT_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X
        (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [InverseMoment.markedCompletedT_eq_tsum _ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  exact markedSummand_eq_punctured S hS D Ψ W X p.1 p.2

lemma inverseMarkedCompletedT_congr_primary (Ψ Φ : O→*ℂ)
    (h : ∀n : O,ConcretePrimeRowBridge.goodLambda^2∣n-1→Ψ n=Φ n)
    (W : ℝ→ℂ) (X : ℝ) (d : Id→ℂ) :
    InverseMoment.markedCompletedT Ψ W X d=InverseMoment.markedCompletedT Φ W X d := by
  unfold InverseMoment.markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

def calibrationLowData (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) :
    GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator :=
  goodMaskRowData _ 1 _ (calibrationForSet S hS).generator_ne_zero one_ne_zero
    (calibrationForSet S hS).generator_ne_zero

theorem correctedPhysicalRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X)
    (E : GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) W X=
      ∑χ : RayCharacter,correctionCoeff χ*InverseMoment.markedCompletedT
        (rowTwist (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator E s hs χ)
          (calibrationForSet S hS).generator 1 z) W X (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_punctured S hS D _ W hW X hX]
  congr 1
  apply inverseMarkedCompletedT_congr_primary
  intro n hn
  exact (lowPeriodicRow_eq_primary η (calibrationForSet S hS) (calibrationForSet S hS).generator E
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2 s hs χ z n hn).symm

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RowInterchange -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem spectralSummand_norm_eq_of_re (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (s t : ℂ) (h : s.re = t.re) (I J : Ideal O) :
    ‖spectralSummand S D Ψ s I J‖ = ‖spectralSummand S D Ψ t I J‖ := by
  have h3 : (3 * s).re = (3 * t).re := by simp [Complex.mul_re, h]
  simp only [spectralSummand, norm_mul, fullIdealWeight_norm_eq_of_re _ _ h,
    fullIdealWeight_norm_eq_of_re _ _ h3]

def mellinSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (p : Ideal O × Ideal O) (y : ℝ) : ℂ :=
  (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) * Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
    spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem mellinSummand_norm (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) (y : ℝ) :
    ‖mellinSummand S D Ψ σ Z p y‖ =
      (Z ^ σ * Real.exp (σ ^ 2) * ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖) *
        Real.exp (-1 * y ^ 2) := by
  unfold mellinSummand
  rw [norm_mul, verticalKernel_norm Z hZ σ y,
    spectralSummand_norm_eq_of_re S D Ψ _ (σ : ℂ) (by simp)]
  ring

theorem mellinSummand_integrable (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) :
    Integrable (mellinSummand S D Ψ σ Z p) := by
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have ht : Continuous (fun y : ℝ => spectralSummand S D Ψ
      ((σ : ℂ) + y * Complex.I) p.1 p.2) :=
    continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
      ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply ((integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖)).mono'
    (hk.mul ht).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => (mellinSummand_norm S D Ψ σ Z hZ p y).le)

theorem mellinSummand_integral_norm (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) :
    (∫ y : ℝ, ‖mellinSummand S D Ψ σ Z p y‖) =
      ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖ *
        (Z ^ σ * Real.exp (σ ^ 2) * ∫ y : ℝ, Real.exp (-1 * y ^ 2)) := by
  simp only [mellinSummand_norm S D Ψ σ Z hZ, integral_const_mul]
  ring

theorem spectralRow_integral_eq_tsum (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    (∫ y : ℝ, (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) =
      ∑' p, ∫ y : ℝ, mellinSummand S D Ψ σ Z p y := by
  let : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hs : Summable (fun p => ∫ y : ℝ, ‖mellinSummand S D Ψ σ Z p y‖) := by
    simp only [mellinSummand_integral_norm S D Ψ σ Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (σ : ℂ) hσ).norm.mul_right _
  rw [integral_tsum_of_summable_integral_norm
    (fun p => mellinSummand_integrable S D Ψ σ Z hZ p) hs]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [mellinSummand, tsum_mul_left, spectralRow]

end SevenEighths.ProbeRow
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianMellin -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianMellinProfile (y : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-(Complex.log (y:ℂ))^2/4)

lemma gaussianMellin_integral (y : ℝ) (hy : 0<y) (σ : ℝ) :
    (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      (Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log (y:ℂ))^2/4) := by
  have hi (v : ℝ) :
      (y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2)=
      Complex.exp ((-1:ℂ)*(v:ℂ)^2+
        (Complex.I*(2*(σ:ℂ)-Complex.log (y:ℂ)))*(v:ℂ)+
        ((σ:ℂ)^2-Complex.log (y:ℂ)*(σ:ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),←Complex.exp_add]
    congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring
  simp_rw [hi]
  rw [integral_cexp_quadratic (by norm_num : (-1:ℂ).re<0)]
  congr 1
  · norm_num
  · congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma gaussianMellin_inversion (y : ℝ) (hy : 0<y) (σ : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)*
      (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      gaussianMellinProfile y := by
  rw [gaussianMellin_integral y hy σ]
  exact mul_assoc _ _ _ |>.symm

lemma gaussian_completed_norm_power (a b Z : ℝ) (ha : 0<a) (hb : 0<b) (hZ : 0<Z) (t : ℂ) :
    (Z:ℂ)^t*((a:ℂ)^(-t)*(b:ℂ)^(-(3*t)))=((a*b^3/Z:ℝ):ℂ)^(-t) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos ha (pow_pos hb 3)).le hZ.le]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le (pow_pos hb 3).le]
  have hp : ((b^3:ℝ):ℂ)^(-t)=(b:ℂ)^((3:ℂ)*(-t)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hb.le (3:ℝ) (-t)).symm
  rw [hp,Complex.cpow_neg (Z:ℂ),div_inv_eq_mul]
  rw [show (3:ℂ)*(-t)= -(3*t) by ring]
  ring

lemma gaussianMellinProfile_norm (y : ℝ) (hy : 0<y) :
    ‖gaussianMellinProfile y‖=
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (-(Real.log y)^2/4) := by
  unfold gaussianMellinProfile
  rw [norm_mul,Complex.norm_exp,←Complex.ofReal_log hy.le]
  congr 2
  simp [←Complex.ofReal_pow]

lemma gaussianMellinProfile_power_bound (y : ℝ) (hy : 0<y) (a : ℝ) :
    ‖gaussianMellinProfile y‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (a^2)*y^(-a) := by
  rw [gaussianMellinProfile_norm y hy,Real.rpow_def_of_pos hy]
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log y/2-a)]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianCompletion -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianCompletedProfile (y : ℝ) : ℂ := gaussianMellinProfile y/(Real.sqrt y:ℂ)

lemma gaussianCompleted_Vstar (y : ℝ) (hy : 0<y) :
    Vstar gaussianCompletedProfile y=gaussianMellinProfile y := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianCompletedProfile]
  field_simp

lemma gaussian_mellinSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (σ Z : ℝ) (hZ : 0<Z) (I J : Id) :
    ((1/(2*Real.pi):ℝ):ℂ)*(∫v : ℝ,mellinSummand S D Ψ σ Z (I,J) v)=
      correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hq : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z :=
    div_pos (mul_pos hi (pow_pos hj 3)) hZ
  have hp (v : ℝ) : mellinSummand S D Ψ σ Z (I,J) v=
      (((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z:ℝ):ℂ)^(-((σ:ℂ)+v*Complex.I))*
      Complex.exp (((σ:ℂ)+v*Complex.I)^2)*
      (completedMask S D I J*completedCorrection I J*
        (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J) := by
    unfold mellinSummand spectralSummand fullIdealWeight
    simp only [ite_eq_right hI,ite_eq_right hJ]
    rw [←gaussian_completed_norm_power _ _ Z hi hj hZ]
    push_cast
    ring
  simp_rw [hp]
  rw [integral_mul_const,←mul_assoc,gaussianMellin_inversion _ hq σ]
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianCompleted_Vstar _ hq]
  ring

lemma gaussian_correctedSummand_summable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    Summable (fun p : Id×Id=>correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2) := by
  have hs : Summable (fun p : Id×Id=>∫v : ℝ,‖mellinSummand S D Ψ 2 Z p v‖) := by
    simp only [mellinSummand_integral_norm S D Ψ 2 Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (2:ℂ) (by norm_num)).norm.mul_right _
  have hi : Summable (fun p : Id×Id=>∫v : ℝ,mellinSummand S D Ψ 2 Z p v) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun p=>norm_integral_le_integral_norm _) hs
  have hh := hi.mul_left (((1/(2*Real.pi):ℝ):ℂ))
  simpa only [gaussian_mellinSummand S D Ψ 2 Z hZ] using hh

theorem spectralRow_eq_gaussianCompleted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (σ : ℝ) (hσ : 1<σ) (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral σ (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow S D Ψ t)=
      correctedCompletedT S D Ψ gaussianCompletedProfile Z := by
  rw [verticalIntegral,spectralRow_integral_eq_tsum S D Ψ hΨ σ hσ Z hZ,←tsum_mul_left]
  unfold correctedCompletedT
  apply tsum_congr
  intro p
  exact gaussian_mellinSummand S D Ψ σ Z hZ p.1 p.2

theorem markedPhysicalProbe_eq_gaussian (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (X Y Z : ℝ) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      (Y:ℂ)⁻¹*∑'s : {I : Id // CanonicalQuadraticSieve.Supported I},
        if ∀P∈C.excluded,¬P∣s.val then
          let a := primaryGenerator s.val
          let ha := CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero s.val s.property
          let has := (CanonicalQuadraticSieve.supported_span_primaryGenerator_iff s.val).mpr s.property
          let q : ℝ := Ideal.absNorm s.val
          W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val/
            (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
          ∑'m : O,C.residueMonoid m*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)*
            W0 (elementNorm m/(elementNorm C.generator*q*X))*
            correctedCompletedT C.excluded D (rowCoefficient η C.Xi a has m)
              gaussianCompletedProfile Z
        else 0 := by
  unfold markedPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    apply tsum_congr
    intro m
    rw [spectralRow_eq_gaussianCompleted _ _ _
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m) 4 (by norm_num) Z hZ]
  · rfl

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianPartition -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

def gaussianCutoff (y : ℝ) : ℂ := (Real.smoothTransition (2-y):ℂ)
def gaussianAnnulus (y : ℝ) : ℂ := annularCutoff gaussianCutoff y

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy
lemma gaussianAnnulus_contDiff : ContDiff ℝ ∞ gaussianAnnulus := by
  unfold gaussianAnnulus annularCutoff gaussianCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).sub
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))
lemma gaussianAnnulus_compact : HasCompactSupport gaussianAnnulus := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianAnnulus y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianAnnulus_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianAnnulus_large y (le_of_lt (lt_of_not_ge h)))

lemma gaussianAnnulus_nonneg (y : ℝ) : 0≤(gaussianAnnulus y).re := by
  by_cases hy : y≤1/2
  · rw [gaussianAnnulus_small y hy]; simp
  · change 0≤Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)
    exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
lemma gaussianAnnulus_norm (y : ℝ) : ‖gaussianAnnulus y‖=(gaussianAnnulus y).re := by
  have h : gaussianAnnulus y=((gaussianAnnulus y).re:ℂ) := by
    simp [gaussianAnnulus,annularCutoff,gaussianCutoff]
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gaussianAnnulus_nonneg y)]
  rfl

lemma gaussianAnnulus_support_scales (x : ℝ) (K : ℕ)
    (hlo : (2:ℝ)^K≤x) (hhi : x<(2:ℝ)^(K+1)) (j : ℕ) (hj : j∉({K,K+1}:Finset ℕ)) :
    gaussianAnnulus (x/(2:ℝ)^j)=0 := by
  have hp : (0:ℝ)<2^j := by positivity
  have hj' : j≠K ∧ j≠K+1 := by simpa using hj
  by_cases hlt : j<K
  · apply gaussianAnnulus_large
    apply (le_div_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show j+1≤K by omega)
    rw [pow_succ] at h
    linarith
  · apply gaussianAnnulus_small
    apply (div_le_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show K+2≤j by omega)
    have he : (2:ℝ)^(K+2)=2*((2:ℝ)^(K+1)) := by rw [pow_succ]; ring
    rw [he] at h
    linarith

lemma gaussianAnnulus_partition (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j)) 1 := by
  obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have h : HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j))
      (∑j∈({K,K+1}:Finset ℕ),gaussianAnnulus (x/(2:ℝ)^j)) :=
    hasSum_sum_of_ne_finset_zero (gaussianAnnulus_support_scales x K hlo hhi)
  convert h using 1
  rw [Finset.sum_pair (by omega : K≠K+1)]
  unfold gaussianAnnulus annularCutoff
  have he : 2*(x/(2:ℝ)^(K+1))=x/(2:ℝ)^K := by rw [pow_succ]; field_simp
  have hh : 2≤2*(x/(2:ℝ)^K) := by
    have hq : 1≤x/(2:ℝ)^K := (one_le_div (by positivity)).mpr hlo
    linarith
  rw [he,gaussianCutoff_small _ ((div_le_one (by positivity)).mpr hhi.le),
    gaussianCutoff_large _ hh]
  ring

lemma gaussianAnnulus_partition_norm (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>‖gaussianAnnulus (x/(2:ℝ)^j)‖) 1 := by
  simpa only [gaussianAnnulus_norm,Complex.one_re] using
    Complex.hasSum_re (gaussianAnnulus_partition x hx)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianWindows -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open CompletedGauss

lemma gaussianMellinProfile_real (y : ℝ) (hy : 0<y) :
    gaussianMellinProfile y=
      ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
        (Real.exp (-(Real.log y)^2/4):ℂ) := by
  unfold gaussianMellinProfile
  rw [←Complex.ofReal_log hy.le]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def gaussianDyadicProfile (Z : ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z)/(Real.sqrt y:ℂ)

lemma gaussianDyadicProfile_small (Z : ℝ) (j : ℕ) (y : ℝ) (hy : y≤1/2) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_small y hy,zero_mul,zero_div]
lemma gaussianDyadicProfile_large (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 2≤y) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_large y hy,zero_mul,zero_div]

lemma gaussianDyadicProfile_compact (Z : ℝ) (j : ℕ) : HasCompactSupport (gaussianDyadicProfile Z j) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianDyadicProfile Z j y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianDyadicProfile_small Z j y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianDyadicProfile_large Z j y (le_of_lt (lt_of_not_ge h)))

lemma gaussianDyadicProfile_contDiff (Z : ℝ) (hZ : 0<Z) (j : ℕ) :
    ContDiff ℝ ∞ (gaussianDyadicProfile Z j) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have he : gaussianDyadicProfile Z j =ᶠ[𝓝 y]
        (fun x : ℝ=>gaussianAnnulus x*
          (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
            (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))/(Real.sqrt x:ℂ)) := by
      filter_upwards [eventually_gt_nhds hy] with x hx
      rw [gaussianDyadicProfile,gaussianMellinProfile_real _ (div_pos (mul_pos (by positivity) hx) hZ)]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hq : (2:ℝ)^j*y/Z≠0 := ne_of_gt (div_pos (mul_pos (by positivity) hy) hZ)
    have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have ha := gaussianAnnulus_contDiff.contDiffAt (x:=y)
    have hl : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.log ((2:ℝ)^j*x/Z)) y :=
      (show ContDiffAt ℝ ∞ (fun x : ℝ=>(2:ℝ)^j*x/Z) y by fun_prop).log hq
    have hg : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4)) y :=
      ((hl.pow 2).neg.div_const 4).exp
    have hgC := Complex.ofRealCLM.contDiff.contDiffAt.comp y hg
    have hsR : ContDiffAt ℝ ∞ Real.sqrt y := Real.contDiffAt_sqrt hy.ne'
    have ht : ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianAnnulus x*
        (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
          (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))) y :=
      ha.mul (contDiffAt_const.mul hgC)
    have hsc : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y hsR
    simpa only [div_eq_mul_inv] using ht.mul (hsc.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianDyadicProfile_small Z j x hx.le

lemma gaussianDyadicProfile_Vstar (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 0<y) :
    Vstar (gaussianDyadicProfile Z j) y=
      gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z) := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianDyadicProfile]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianDecomposition -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma annular_reassembly_summable {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤N p) :
    Summable (fun q : α×ℕ=>gaussianAnnulus (N q.1/(2:ℝ)^q.2)*a q.1) := by
  have hs (p : α) : HasSum (fun j : ℕ=>‖gaussianAnnulus (N p/(2:ℝ)^j)*a p‖) ‖a p‖ := by
    by_cases hp : a p=0
    · simp only [hp,mul_zero,norm_zero]
      exact hasSum_zero
    · simpa only [norm_mul,one_mul] using (gaussianAnnulus_partition_norm (N p) (hN p hp)).mul_right ‖a p‖
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  exact ⟨fun p=>(hs p).summable,by simpa only [fun p=>(hs p).tsum_eq] using ha.norm⟩

lemma annular_reassembly {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤N p) :
    (∑'j : ℕ,∑'p : α,gaussianAnnulus (N p/(2:ℝ)^j)*a p)=∑'p,a p := by
  rw [Summable.tsum_comm (f:=fun p : α=>fun j : ℕ=>gaussianAnnulus (N p/(2:ℝ)^j)*a p)
    (annular_reassembly_summable a N ha hN)]
  apply tsum_congr
  intro p
  by_cases hp : a p=0
  · simp [hp]
  · simpa only [one_mul] using ((gaussianAnnulus_partition (N p) (hN p hp)).mul_right (a p)).tsum_eq

lemma gaussian_dyadic_correctedSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (hZ : 0<Z) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN := mul_pos hi (pow_pos hj 3)
  unfold correctedSummand markedSummand summand
  rw [gaussianDyadicProfile_Vstar _ _ _ (div_pos hN (by positivity)),
    gaussianCompleted_Vstar _ (div_pos hN hZ)]
  have he : (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/Z=
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z := by
    field_simp
  rw [he]
  ring

lemma gaussian_correctedSummand_norm_ge_one (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (I J : Id)
    (h : correctedSummand S D Ψ gaussianCompletedProfile Z I J≠0) :
    1≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hI : I≠0 := by intro he; subst I; simp [correctedSummand,markedSummand,summand] at h
  have hJ : J≠0 := by intro he; subst J; simp [correctedSummand,markedSummand,summand] at h
  have hi : 1≤Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : 1≤Ideal.absNorm J := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  exact_mod_cast one_le_mul_of_one_le_of_one_le hi (one_le_pow₀ hj)

theorem correctedGaussian_eq_tsum_dyadic (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    correctedCompletedT S D Ψ gaussianCompletedProfile Z=
      ∑'j : ℕ,correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) := by
  unfold correctedCompletedT
  simp_rw [gaussian_dyadic_correctedSummand S D Ψ Z hZ]
  exact (annular_reassembly _ _ (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=>gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).symm

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianLow -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianDyadicSchwartz (Z : ℝ) (hZ : 0<Z) (j : ℕ) : SchwartzMap ℝ ℂ :=
  (gaussianDyadicProfile_compact Z j).toSchwartzMap (gaussianDyadicProfile_contDiff Z hZ j)

theorem physicalSpectralRow_eq_dyadic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*
      spectralRow S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) t)=
      ∑'j : ℕ,∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (gaussianDyadicSchwartz Z hZ j) ((2:ℝ)^j)
          (fun A=>if D∣A then (1:ℂ) else 0) := by
  have hΨ := rowCoefficient_norm_le_one η (calibrationForSet S hS).Xi
    (calibrationForSet S hS).Xi_norm_le_one s hs z
  rw [spectralRow_eq_gaussianCompleted _ _ _ hΨ 4 (by norm_num) Z hZ,
    correctedGaussian_eq_tsum_dyadic _ _ _ hΨ Z hZ]
  apply tsum_congr
  intro j
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D
    (gaussianDyadicProfile Z j) (gaussianDyadicProfile_compact Z j) ((2:ℝ)^j)
    (by positivity) (calibrationLowData S hS)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianDerivative -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianLog (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log z)^2/4)

lemma gaussianLog_ofReal (y : ℝ) : gaussianLog (y:ℂ)=gaussianMellinProfile y := rfl

lemma gaussianLog_power_bound (z : ℂ) (hz : z≠0) (a : ℝ) :
    ‖gaussianLog z‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (Real.pi^2/4+a^2)*‖z‖^(-a) := by
  have hre : (-(Complex.log z)^2/4).re=
      ((Complex.log z).im^2-(Real.log ‖z‖)^2)/4 := by
    simp [pow_two,Complex.mul_re,Complex.log_re]
  have hp : (Complex.log z).im^2≤Real.pi^2 := by
    have h1 := Complex.log_im_le_pi z
    have h2 := Complex.neg_pi_lt_log_im z
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0≤Real.pi+(Complex.log z).im by linarith)]
  unfold gaussianLog
  rw [norm_mul,Complex.norm_exp,hre,Real.rpow_def_of_pos (norm_pos_iff.mpr hz),
    mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log ‖z‖/2-a)]

lemma iteratedDeriv_restrict_positive (f : ℂ→ℂ)
    (hf : ∀x : ℝ,0<x→AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) (hx : 0<x) :
    iteratedDeriv n (fun y : ℝ=>f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : Set.EqOn (deriv (fun y : ℝ=>f (y:ℂ))) (fun y : ℝ=>deriv f (y:ℂ)) (Set.Ioi 0) := by
      intro y hy
      exact (hf y hy).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he.iteratedDeriv_of_isOpen isOpen_Ioi n hx]
    exact ih (deriv f) (fun y hy=>(hf y hy).deriv)

lemma gaussianLog_analytic (z : ℂ) (hz : 0<z.re) : AnalyticAt ℂ gaussianLog z := by
  have hl := analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  unfold gaussianLog
  exact analyticAt_const.mul (((hl.pow 2).neg.div_const (c:=4)).cexp)

lemma gaussianLog_scaled_analytic (r : ℝ) (hr : 0< r) (z : ℂ) (hz : 0<z.re) :
    AnalyticAt ℂ (fun w : ℂ=>gaussianLog ((r:ℂ)*w)) z := by
  have h : 0<((r:ℂ)*z).re := by simpa using mul_pos hr hz
  exact (gaussianLog_analytic _ h).comp (analyticAt_const.mul analyticAt_id)

lemma gaussianLog_scaled_disk_bound (a : ℝ) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0< r→∀y∈Set.Icc (1/2:ℝ) 2,
      ∀z∈Metric.closedBall (y:ℂ) (1/4),‖gaussianLog ((r:ℂ)*z)‖≤C*r^(-a) := by
  have hc : ContinuousOn (fun t : ℝ=>t^(-a)) (Set.Icc (1/4:ℝ) (9/4)) := by
    intro t ht
    exact (continuousAt_id.rpow_const (Or.inl (show t≠0 by linarith [ht.1]))).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hBpos : 0<B := by
    have hh := hB 1 (by norm_num : (1:ℝ)∈Set.Icc (1/4:ℝ) (9/4))
    norm_num at hh
    linarith
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (Real.pi^2/4+a^2)
  have hcn : 0≤ c := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro r hr y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hyr : ‖(y:ℂ)‖=y := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [hy.1])]
  have hu := norm_sub_norm_le z (y:ℂ)
  have hl := norm_sub_norm_le (y:ℂ) z
  rw [hyr] at hu hl
  rw [norm_sub_rev] at hl
  have hzn : ‖z‖∈Set.Icc (1/4:ℝ) (9/4) := ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hz0 : z≠0 := norm_pos_iff.mp (by linarith [hzn.1])
  have hrz : (r:ℂ)*z≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz0
  have hb : ‖z‖^(-a)≤B := (le_abs_self _).trans (hB ‖z‖ hzn)
  have hh := gaussianLog_power_bound ((r:ℂ)*z) hrz a
  have hnorm : ‖(r:ℂ)*z‖=r*‖z‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  rw [hnorm,Real.mul_rpow hr.le (norm_nonneg _)] at hh
  calc
    _ ≤ c*(r^(-a)*‖z‖^(-a)) := hh
    _ ≤ c*(r^(-a)*B) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hcn
    _ ≤ (c+1)*B*r^(-a) := by nlinarith [mul_nonneg hBpos.le (Real.rpow_pos_of_pos hr (-a)).le]

lemma gaussianLog_scaled_derivative_bound (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0< r→∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (fun x : ℝ=>gaussianMellinProfile (r*x)) y‖≤C*r^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLog_scaled_disk_bound a
  refine ⟨(n.factorial:ℝ)*B/(1/4:ℝ)^n,by positivity,?_⟩
  intro r hr y hy
  have hf : ∀x : ℝ,0<x→AnalyticAt ℂ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (x:ℂ) :=
    fun x hx=>gaussianLog_scaled_analytic r hr (x:ℂ) hx
  have he : (fun x : ℝ=>gaussianMellinProfile (r*x))=
      (fun x : ℝ=>gaussianLog ((r:ℂ)*(x:ℂ))) := by
    funext x
    rw [←Complex.ofReal_mul,gaussianLog_ofReal]
  rw [he,iteratedDeriv_restrict_positive _ hf n y (by linarith [hy.1])]
  have hd : DiffContOnCl ℂ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (Metric.ball (y:ℂ) (1/4)) := by
    apply DifferentiableOn.diffContOnCl_ball (U:={z : ℂ|0<z.re})
      (fun z hz=>(gaussianLog_scaled_analytic r hr z hz).differentiableAt.differentiableWithinAt)
    intro z hz
    have hn : ‖z-(y:ℂ)‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have ha := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hn
    simp only [Complex.sub_re,Complex.ofReal_re,abs_le] at ha
    change 0<z.re
    linarith [hy.1]
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1/4) hd
    (fun z hz=>hbound r hr y hy z (Metric.sphere_subset_closedBall hz))
  exact hh.trans_eq (by ring)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianSeminorm -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open Filter Set
namespace SevenEighths.ProbePhysical

def gaussianFixedWindow (y : ℝ) : ℂ := gaussianAnnulus y/(Real.sqrt y:ℂ)
lemma gaussianFixedWindow_small (y : ℝ) (hy : y≤1/2) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_small y hy,zero_div]
lemma gaussianFixedWindow_large (y : ℝ) (hy : 2≤y) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_large y hy,zero_div]
lemma gaussianFixedWindow_compact : HasCompactSupport gaussianFixedWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianFixedWindow y≠0 at hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))
lemma gaussianFixedWindow_contDiff : ContDiff ℝ ∞ gaussianFixedWindow := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have hf : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_sqrt hy.ne')
    unfold gaussianFixedWindow
    simp only [div_eq_mul_inv]
    exact gaussianAnnulus_contDiff.contDiffAt.mul (hf.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianFixedWindow_small x hx.le

def gaussianFixedSchwartz : SchwartzMap ℝ ℂ := gaussianFixedWindow_compact.toSchwartzMap gaussianFixedWindow_contDiff

lemma gaussianProfile_scaled_smooth (r : ℝ) (hr : 0< r) (y : ℝ) (hy : 0<y) :
    ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianMellinProfile (r*x)) y := by
  have hf : ContDiffAt ℂ ∞ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (y:ℂ) :=
    (gaussianLog_scaled_analytic r hr (y:ℂ) hy).contDiffAt
  have hh := (hf.restrict_scalars ℝ).comp y Complex.ofRealCLM.contDiff.contDiffAt
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,←Complex.ofReal_mul,gaussianLog_ofReal] using hh

lemma gaussianDyadicProfile_factor (Z : ℝ) (j : ℕ) :
    gaussianDyadicProfile Z j=(fun y : ℝ=>gaussianFixedWindow y*
      gaussianMellinProfile (((2:ℝ)^j/Z)*y)) := by
  funext y
  unfold gaussianDyadicProfile gaussianFixedWindow
  rw [show (2:ℝ)^j*y/Z=((2:ℝ)^j/Z)*y by ring]
  ring

lemma gaussianDyadicProfile_derivative_outside (Z : ℝ) (j n : ℕ) (y : ℝ)
    (hy : y∉Set.Icc (1/2:ℝ) 2) : iteratedDeriv n (gaussianDyadicProfile Z j) y=0 := by
  have he : gaussianDyadicProfile Z j=ᶠ[𝓝 y](fun _=>0) := by
    simp only [Set.mem_Icc,not_and_or,not_le] at hy
    rcases hy with hy|hy
    · filter_upwards [eventually_lt_nhds hy] with x hx
      exact gaussianDyadicProfile_small Z j x hx.le
    · filter_upwards [eventually_gt_nhds hy] with x hx
      exact gaussianDyadicProfile_large Z j x hx.le
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianDyadicProfile_derivative_uniform (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→∀j : ℕ,∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤C*(((2:ℝ)^j/Z)^(-a)) := by
  choose B hB hbound using fun i : ℕ=>gaussianLog_scaled_derivative_bound a i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i gaussianFixedSchwartz
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := by exact apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro Z hZ j y hy
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  have hy0 : 0<y := by linarith [hy.1]
  rw [gaussianDyadicProfile_factor,iteratedDeriv_fun_mul
    (gaussianFixedWindow_contDiff.contDiffAt.of_le (by simp))
    ((gaussianProfile_scaled_smooth _ hr y hy0).of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i gaussianFixedWindow y*
        iteratedDeriv (n-i) (fun x : ℝ=>gaussianMellinProfile (((2:ℝ)^j/Z)*x)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*(((2:ℝ)^j/Z)^(-a))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hfixed : ‖iteratedDeriv i gaussianFixedWindow y‖≤A i := by
        have hh := SchwartzMap.le_seminorm' ℝ 0 i gaussianFixedSchwartz y
        simp only [pow_zero,one_mul] at hh
        exact hh
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfixed (Nat.cast_nonneg _))
        (hbound _ _ hr y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*(((2:ℝ)^j/Z)^(-a)) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*(((2:ℝ)^j/Z)^(-a)) := by nlinarith [Real.rpow_pos_of_pos hr (-a)]

theorem gaussianDyadicSchwartz_seminorm (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      SchwartzMap.seminorm ℝ k n (gaussianDyadicSchwartz Z hZ j)≤C*(((2:ℝ)^j/Z)^(-a)) := by
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicProfile_derivative_uniform a n
  refine ⟨(2:ℝ)^k*B,by positivity,?_⟩
  intro Z hZ j
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  change |y|^k*‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤_
  by_cases hy : y∈Set.Icc (1/2:ℝ) 2
  · have habs : |y|≤2 := by rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.2
    calc
      _ ≤ (2:ℝ)^k*(B*(((2:ℝ)^j/Z)^(-a))) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) habs k) (hbound Z hZ j y hy)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [gaussianDyadicProfile_derivative_outside Z j n y hy,norm_zero,mul_zero]
    positivity

theorem gaussianDyadicSchwartz_finite_seminorm (a : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*(((2:ℝ)^j/Z)^(-a)) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1,by norm_num,?_⟩
    intro Z hZ j
    simp only [Finset.sup_empty,one_mul]
    change 0≤(((2:ℝ)^j/Z)^(-a))
    exact Real.rpow_nonneg (by positivity) _
  | @insert p S hp ih =>
    obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_seminorm a p.1 p.2
    obtain ⟨C,hC,hrest⟩ := ih
    refine ⟨B+C,by positivity,?_⟩
    intro Z hZ j
    rw [Finset.sup_insert,Seminorm.sup_apply]
    apply max_le
    · exact (hbound Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])
    · exact (hrest Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])

theorem gaussianDyadicSchwartz_two_sided (A : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*min (((2:ℝ)^j/Z)^A) (((2:ℝ)^j/Z)^(-A)) := by
  obtain ⟨B,hB,hlo⟩ := gaussianDyadicSchwartz_finite_seminorm (-A) S
  obtain ⟨C,hC,hhi⟩ := gaussianDyadicSchwartz_finite_seminorm A S
  refine ⟨B+C,by positivity,?_⟩
  intro Z hZ j
  rw [mul_min_of_nonneg _ _ (by positivity : 0≤B+C)]
  apply le_min
  · have hh := hlo Z hZ j
    rw [neg_neg] at hh
    exact hh.trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) A])
  · exact (hhi Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-A)])

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianSummation -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical

lemma gaussianDyadicSchwartz_polynomial_decay (N : ℕ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C/(1+(2:ℝ)^j/Z)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianDyadicSchwartz_finite_seminorm 0 S
  obtain ⟨C,hC,hdecay⟩ := gaussianDyadicSchwartz_finite_seminorm (N:ℝ) S
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro Z hZ j
  let r := (2:ℝ)^j/Z
  have hr : 0< r := div_pos (by positivity) hZ
  have hden : 0<(1+r)^N := pow_pos (by linarith) _
  change _≤(B+C)*(2:ℝ)^N/(1+r)^N
  by_cases hr1 : r≤1
  · have hh := hzero Z hZ j
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+r)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay Z hZ j
    change _≤C*r^(-(N:ℝ)) at hh
    rw [Real.rpow_neg hr.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+r)^N≤(2*r)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hi : 0≤C*(r^N)⁻¹ := by positivity
    have hm := mul_le_mul_of_nonneg_left hp hi
    rw [mul_pow] at hm
    have hn : r^N≠0 := ne_of_gt (pow_pos hr _)
    have he : (C*(r^N)⁻¹)*((2:ℝ)^N*r^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianDyadicSchwartz_summed (s : ℝ) (hs : 0<s) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_polynomial_decay N S
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound Z hZ j) (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j) := by positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianFlow -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianFlow (R : ℝ) (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-((Real.log R:ℂ)+z)^2/4)
lemma gaussianFlow_analytic (R : ℝ) (z : ℂ) : AnalyticAt ℂ (gaussianFlow R) z := by
  unfold gaussianFlow
  fun_prop
lemma gaussianFlow_real (R : ℝ) (hR : 0<R) (s : ℝ) :
    gaussianFlow R (s:ℂ)=gaussianMellinProfile (R*Real.exp s) := by
  unfold gaussianFlow gaussianMellinProfile
  rw [←Complex.ofReal_log (mul_pos hR (Real.exp_pos _)).le,Real.log_mul hR.ne' (Real.exp_pos _).ne',Real.log_exp,
    Complex.ofReal_add]

lemma iteratedDeriv_restrict_real (f : ℂ→ℂ)
    (hf : ∀x : ℝ,AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ=>f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : deriv (fun y : ℝ=>f (y:ℂ))=(fun y : ℝ=>deriv f (y:ℂ)) := by
      funext y
      exact (hf y).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he]
    exact ih (deriv f) (fun y=>(hf y).deriv)

lemma gaussianFlow_disk_bound (a L : ℝ) (_hL : 0≤L) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ∀z∈Metric.closedBall (y:ℂ) 1,‖gaussianFlow R z‖≤C*R^(-a) := by
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖
  let B := Real.exp (a^2+1/4+|a| *(L+1))
  have hc : 0≤ c := norm_nonneg _
  have hB : 0<B := Real.exp_pos _
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro R hR y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hzr := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hd
  have hzi := (Complex.abs_im_le_norm (z-(y:ℂ))).trans hd
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hzr hzi
  have hre : |z.re|≤L+1 := by
    have h := abs_add_le (z.re-y) y
    have he : z.re-y+y=z.re := by ring
    rw [he] at h
    linarith
  have hsq : z.im^2≤1 := by nlinarith [(abs_le.mp hzi).1,(abs_le.mp hzi).2]
  have hmul : -(a*z.re)≤|a| *(L+1) := by
    calc
      _ ≤ |a*z.re| := neg_le_abs _
      _ = |a| *|z.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (abs_nonneg _)
  have he : (-((Real.log R:ℂ)+z)^2/4).re=(z.im^2-(Real.log R+z.re)^2)/4 := by
    simp [pow_two,Complex.mul_re]
  unfold gaussianFlow
  rw [norm_mul,Complex.norm_exp,he]
  have hb : Real.exp ((z.im^2-(Real.log R+z.re)^2)/4)≤B*R^(-a) := by
    rw [Real.rpow_def_of_pos hR,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((Real.log R+z.re)/2-a)]
  calc
    _ ≤ c*(B*R^(-a)) := mul_le_mul_of_nonneg_left hb hc
    _ ≤ (c+1)*B*R^(-a) := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]

lemma gaussianFlow_derivative_bound (a L : ℝ) (hL : 0≤L) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianFlow_disk_bound a L hL
  refine ⟨(n.factorial:ℝ)*B,by positivity,?_⟩
  intro R hR y hy
  rw [iteratedDeriv_restrict_real _ (fun x=>gaussianFlow_analytic R (x:ℂ)) n y]
  have hf : Differentiable ℂ (gaussianFlow R) := fun z=>(gaussianFlow_analytic R z).differentiableAt
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl
    (fun z hz=>hbound R hR y hy z (Metric.sphere_subset_closedBall hz))
  simpa only [one_pow,div_one,mul_assoc] using h

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianLogWindow -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open Filter Set MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianFlow_real_smooth (R : ℝ) : ContDiff ℝ ∞ (fun s : ℝ=>gaussianFlow R (s:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  have hf : ContDiffAt ℂ ∞ (gaussianFlow R) (s:ℂ) := (gaussianFlow_analytic R _).contDiffAt
  exact (hf.restrict_scalars ℝ).comp s Complex.ofRealCLM.contDiff.contDiffAt

def gaussianLogWindow (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  (hV.mul_right (f':=fun s : ℝ=>gaussianFlow R (s:ℂ))).toSchwartzMap
    (V.smooth'.mul (gaussianFlow_real_smooth R))
@[simp] lemma gaussianLogWindow_apply (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R s : ℝ) : gaussianLogWindow V hV R s=V s*gaussianFlow R (s:ℂ) := rfl

lemma gaussianLogWindow_derivative_outside (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hbox : ∀s,V s≠0→|s|≤L) (R y : ℝ) (hy : L < |y|) (n : ℕ) :
    iteratedDeriv n (gaussianLogWindow V hV R) y=0 := by
  have he : (gaussianLogWindow V hV R:ℝ→ℂ)=ᶠ[𝓝 y](fun _=>0) := by
    have hu : {x : ℝ | L < |x|}∈𝓝 y := (isOpen_lt continuous_const continuous_abs).mem_nhds hy
    filter_upwards [hu] with x hx
    have hv : V x=0 := by by_contra h; exact (not_lt_of_ge (hbox x h)) hx
    simp only [gaussianLogWindow_apply,hv,zero_mul]
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianLogWindow_derivative_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (gaussianLogWindow V hV R) y‖≤C*R^(-a) := by
  choose B hB hbound using fun i : ℕ=>gaussianFlow_derivative_bound a L hL i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i V
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro R hR y hy
  change ‖iteratedDeriv n (fun s : ℝ=>V s*gaussianFlow R (s:ℂ)) y‖≤_
  rw [iteratedDeriv_fun_mul (f:=(V:ℝ→ℂ)) (g:=fun s : ℝ=>gaussianFlow R (s:ℂ))
    (V.smooth'.contDiffAt.of_le (by simp))
    ((gaussianFlow_real_smooth R).contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i V y*
        iteratedDeriv (n-i) (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*R^(-a)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hv : ‖iteratedDeriv i V y‖≤A i := by
        simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℝ 0 i V y
      exact mul_le_mul (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
        (hbound _ R hR y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*R^(-a) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*R^(-a) := by nlinarith [Real.rpow_pos_of_pos hR (-a)]

theorem gaussianLogWindow_seminorm (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      SchwartzMap.seminorm ℝ k n (gaussianLogWindow V hV R)≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLogWindow_derivative_bound V hV L hL a n
  refine ⟨(1+L^k)*B,by positivity,?_⟩
  intro R hR
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  by_cases hy : |y|≤L
  · calc
      _ ≤ L^k*(B*R^(-a)) := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy k)
        (hbound R hR y hy) (norm_nonneg _) (pow_nonneg hL _)
      _ ≤ _ := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]
  · rw [gaussianLogWindow_derivative_outside V hV L hbox R y (lt_of_not_ge hy) n,norm_zero,mul_zero]
    positivity

theorem gaussianLogWindow_fourier_moment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      (∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤C*R^(-a) := by
  let p := (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower
  let K := J+p
  choose B hB hb using fun q : ℕ×ℕ=>gaussianLogWindow_seminorm V hV L hL hbox a q.1 q.2
  let C := (∑i∈Finset.range (K+1),(B (0,i)+B (p,i)))+1
  have hC : 0<C := by
    have hh : 0≤∑i∈Finset.range (K+1),(B (0,i)+B (p,i)) :=
      Finset.sum_nonneg (fun i _=>add_nonneg (hB _).le (hB _).le)
    dsimp only [C]; linarith
  let D := (2:ℝ)^J*(FourierBridge.coefficientMomentBound 0 C+FourierBridge.coefficientMomentBound J C)
  have hD : 0≤D := mul_nonneg (by positivity)
    (add_nonneg (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le)
      (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le))
  refine ⟨D+1,by positivity,?_⟩
  intro R hR
  have hcancel : R^a*R^(-a)=1 := by rw [←Real.rpow_add hR]; simp
  have hsource (i : ℕ) (hi : i≤J+(MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower) :
      R^a*(SchwartzMap.seminorm ℝ 0 i (gaussianLogWindow V hV R)+
        SchwartzMap.seminorm ℝ p i (gaussianLogWindow V hV R))≤C := by
    have hbi : B (0,i)+B (p,i)≤C := by
      have hh := Finset.single_le_sum (s:=Finset.range (K+1)) (a:=i)
        (f:=fun i=>B (0,i)+B (p,i))
        (fun i _=>add_nonneg (hB _).le (hB _).le) (Finset.mem_range.mpr (by dsimp only [K,p]; omega))
      dsimp only [C]; linarith
    calc
      _ ≤ R^a*(B (0,i)*R^(-a)+B (p,i)*R^(-a)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hb (0,i) R hR) (hb (p,i) R hR)) (by positivity)
      _ = B (0,i)+B (p,i) := by rw [←add_mul]; calc
        _=(B (0,i)+B (p,i))*(R^a*R^(-a)) := by ring
        _=_ := by rw [hcancel,mul_one]
      _ ≤ C := hbi
  have hh := FourierBridge.uniform_fourier_one_plus_moment (gaussianLogWindow V hV R) J
    (R^a) C (by positivity) hC.le hsource
  change R^a*(∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤D at hh
  have hp := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hR (-a)).le
  have hc' : R^(-a)*R^a=1 := by rw [mul_comm,hcancel]
  rw [←mul_assoc,hc',one_mul] at hp
  exact hp.trans (by nlinarith [Real.rpow_pos_of_pos hR (-a)])

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianCoupled -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge LocalLogFourier
namespace SevenEighths.ProbePhysical

def gaussianJointDensity (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕 (gaussianLogWindow V hV R)

lemma gaussianProfile_positive_smooth : ContDiffOn ℝ ∞ gaussianMellinProfile (Set.Ioi 0) := by
  intro y hy
  have hh := (gaussianProfile_scaled_smooth 1 (by norm_num) y hy).contDiffWithinAt (s:=Set.Ioi 0)
  simpa only [one_mul] using hh

lemma gaussianLogWindow_eq_positive (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R : ℝ) (hR : 0<R) : gaussianLogWindow V hV R=
      positiveLogProfile V gaussianMellinProfile R hV V.smooth' gaussianProfile_positive_smooth hR := by
  ext s
  simp only [gaussianLogWindow_apply,positiveLogProfile_apply,gaussianFlow_real R hR]

theorem gaussian_coupled_separation {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a y : ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) (hR : 0<R)
    (hactive : (∏i,W i (y i))≠0→V (∑i,a i*y i)=1) :
    (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
      ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t := by
  have hh := coupled_positive_log_separation W gaussianMellinProfile V R a y hV V.smooth'
    gaussianProfile_positive_smooth hR hactive
  rw [←gaussianLogWindow_eq_positive V hV R hR] at hh
  exact hh

theorem gaussian_coupled_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i y≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀y : ι→ℝ,
        (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
          ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let T := ∑i,|a i| *M i
  have hT : 0≤T := Finset.sum_nonneg (fun i _=>mul_nonneg (abs_nonneg _) (hM i))
  obtain ⟨φ,hφc,hφs,hφone,hφsupp,_⟩ := FourierBridge.exists_complex_smooth_cutoff T hT
  let V : SchwartzMap ℝ ℂ := hφc.toSchwartzMap hφs
  have hV : HasCompactSupport (V:ℝ→ℂ) := hφc
  have hbox : ∀s,V s≠0→|s|≤T+1 := by
    intro s hs
    have hh := hφsupp (subset_tsupport φ hs)
    exact abs_le.mpr hh
  refine ⟨V,hV,?_,?_⟩
  · intro R hR y
    apply gaussian_coupled_separation W a y V hV R hR
    exact FourierBridge.coupled_cutoff_active W φ a y M hwindow (by simpa only [T] using hφone)
  · intro A J
    obtain ⟨C,hC,hbound⟩ := gaussianLogWindow_fourier_moment V hV (T+1) (by linarith) hbox A J
    refine ⟨C,hC,?_⟩
    intro R hR
    exact ⟨JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV R) J,hbound R hR⟩

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianSlots -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical

def gaussianSlotWindow {ι : Type*} (W : ι→ℝ→ℂ) : Option ι→ℝ→ℂ
  | none => fun y=>gaussianAnnulus (Real.exp y)
  | some i => fun y=>W i (Real.exp y)
def gaussianSlotSlope {ι : Type*} : Option ι→ℝ
  | none => 1
  | some _ => -1
def gaussianSlotPoint {ι : Type*} (x : ℝ) (q : ι→ℝ) : Option ι→ℝ
  | none => Real.log x
  | some i => Real.log (q i)

lemma gaussianSlot_argument {ι : Type*} [Fintype ι] (x : ℝ) (hx : 0<x) (q : ι→ℝ) (hq : ∀i,0<q i) :
    Real.exp (∑i : Option ι,gaussianSlotSlope i*gaussianSlotPoint x q i)=x/(∏i,q i) := by
  simp only [Fintype.sum_option,gaussianSlotSlope,gaussianSlotPoint,one_mul,neg_one_mul]
  rw [Real.exp_add,Real.exp_sum,Real.exp_log hx]
  simp_rw [Real.exp_neg,Real.exp_log (hq _)]
  rw [Finset.prod_inv_distrib]
  rfl

lemma logPhase_neg_argument (t y : ℝ) : logPhase t (-y)=logPhase (-t) y := by
  unfold logPhase
  congr 1
  push_cast
  ring

lemma gaussianSlot_product {ι : Type*} [Fintype ι] (W : ι→ℝ→ℂ)
    (x : ℝ) (hx : 0<x) (q : ι→ℝ) (hq : ∀i,0<q i) (t : ℝ) :
    (∏i : Option ι,gaussianSlotWindow W i (gaussianSlotPoint x q i)*
      logPhase t (gaussianSlotSlope i*gaussianSlotPoint x q i))=
      gaussianAnnulus x*logPhase t (Real.log x)*
        ∏i,W i (q i)*logPhase (-t) (Real.log (q i)) := by
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,gaussianSlotSlope,
    one_mul,neg_one_mul,Real.exp_log hx,logPhase_neg_argument]
  simp_rw [Real.exp_log (hq _)]

lemma gaussianFixedWindow_Vstar_twist (t x : ℝ) (hx : 0<x) :
    Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x=
      gaussianAnnulus x*logPhase t (Real.log x) := by
  have hs : (Real.sqrt x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  unfold Vstar CompletedHeight.normTwistedSource gaussianFixedWindow
  field_simp

lemma gaussianAnnulus_log_support (y : ℝ) (hy : gaussianAnnulus (Real.exp y)≠0) :
    |y|≤|Real.log (1/2)|+|Real.log 2|+1 := by
  have hlo : (1/2:ℝ)<Real.exp y := by
    by_contra h; exact hy (gaussianAnnulus_small _ (le_of_not_gt h))
  have hhi : Real.exp y<2 := by
    by_contra h; exact hy (gaussianAnnulus_large _ (le_of_not_gt h))
  have hl : Real.log (1/2)≤y := by simpa using Real.log_le_log (by norm_num : (0:ℝ)<1/2) hlo.le
  have hh : y≤Real.log 2 := by simpa using Real.log_le_log (Real.exp_pos y) hhi.le
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log (1/2)); have := abs_nonneg (Real.log 2); linarith
  · have := le_abs_self (Real.log 2); have := abs_nonneg (Real.log (1/2)); linarith

theorem gaussian_selected_slot_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
        gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
          ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
            (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let M' : Option ι→ℝ := fun o=>match o with
    | none => |Real.log (1/2)|+|Real.log 2|+1
    | some i => M i
  have hM' : ∀o,0≤M' o := by intro o; cases o with
    | none => dsimp [M']; positivity
    | some i => exact hM i
  have hW : ∀o y,gaussianSlotWindow W o y≠0→|y|≤M' o := by
    intro o y
    cases o with
    | none => exact gaussianAnnulus_log_support y
    | some i => exact hwindow i y
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_coupled_family (gaussianSlotWindow W) gaussianSlotSlope M' hM' hW
  refine ⟨V,hV,?_,hbound⟩
  intro R hR x hx q hq
  have hh := hsep R hR (gaussianSlotPoint x q)
  rw [gaussianSlot_argument x hx q hq] at hh
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,Real.exp_log hx] at hh
  simp_rw [Real.exp_log (hq _)] at hh
  rw [show R*(x/∏i,q i)=R*x/(∏i,q i) by ring] at hh
  rw [hh]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [gaussianFixedWindow_Vstar_twist t x hx]
  simp only [gaussianSlotSlope,one_mul,neg_one_mul,logPhase_neg_argument]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianCompletedSlots -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma correctedSummand_normTwisted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (T t : ℝ) (I J : Id) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource W t) T I J=
      logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T))*
        correctedSummand S D Ψ W T I J := by
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
    CompletedHeight.normTwistedSource
  ring

lemma correctedSummand_fixed_finite (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T : ℝ) (hT : 0<T) :
    (Function.support (fun p : Id×Id=>correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2)).Finite := by
  apply (completedT_finite_support Ψ gaussianFixedWindow gaussianFixedWindow_compact T hT).subset
  intro p hp hz
  exact hp (by simp only [correctedSummand,markedSummand,hz,mul_zero])

lemma gaussian_slot_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ) (x : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ=>logPhase t x*c*
      (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*b t) := by
  have hh : Integrable (fun t : ℝ=>b t*(logPhase t x*c*
      ∏i,W i (q i)*logPhase (-t) (Real.log (q i)))) := by
    apply b.integrable.mul_bdd (c:=‖c‖*∏i,‖W i (q i)‖)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul ((logPhase_continuous_left x).mul_const c)
      apply continuous_finsetProd
      intro i hi
      exact ((logPhase_continuous_left (Real.log (q i))).comp continuous_neg).const_mul _
    · apply Filter.Eventually.of_forall
      intro t
      simp only [norm_mul,norm_prod,logPhase_norm,mul_one,one_mul,le_refl]
  simpa only [mul_comm (b _) _] using hh

lemma gaussian_selected_summand {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (Z : ℝ) (hZ : 0<Z) (j : ℕ)
    (q : ι→ℝ) (hq : ∀i,0<q i) (I J : Id) :
    (∏i,W i (q i))*correctedSummand S D Ψ
      (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j) I J=
      ∫t : ℝ,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) I J*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hT : (0:ℝ)<2^j := by positivity
  have hN := div_pos (mul_pos hi (pow_pos hj 3)) hT
  have hprod : 0<∏i,q i := Finset.prod_pos (fun i _=>hq i)
  have hh := hsep ((2:ℝ)^j/Z) (div_pos hT hZ) _ hN q hq
  have he : (2:ℝ)^j/Z*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(∏i,q i)=
      (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(Z*∏i,q i) := by ring
  rw [he] at hh
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianDyadicProfile_Vstar _ _ _ hN]
  let c : ℂ := completedCorrection I J*completedMask S D I J*
    (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J
  calc
    _ = c*(gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
      (∏i,W i (q i))*gaussianMellinProfile
        ((2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(Z*∏i,q i))) := by dsimp [c]; ring
    _ = c*∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t)
      ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by rw [hh]
    _ = _ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp [c]
      ring

lemma correctedSummand_gaussian_factor (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianMellinProfile (((2:ℝ)^j/Z)*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j))*
        correctedSummand S D Ψ gaussianFixedWindow ((2:ℝ)^j) I J := by
  rw [gaussianDyadicProfile_factor]
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
  ring

lemma gaussian_selected_completed_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (T : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ=>correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*b t) := by
  let hf := correctedSummand_fixed_finite S D Ψ T hT
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  simp_rw [hr,Finset.sum_mul]
  apply integrable_finsetSum
  intro p hp
  simp_rw [correctedSummand_normTwisted]
  exact gaussian_slot_integrable W q b _ _

theorem gaussian_selected_completed {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (Z : ℝ) (hZ : 0<Z) (j : ℕ)
    (q : ι→ℝ) (hq : ∀i,0<q i) :
    (∏i,W i (q i))*correctedCompletedT S D Ψ
      (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j)=
      ∫t : ℝ,correctedCompletedT S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  let hf := correctedSummand_fixed_finite S D Ψ ((2:ℝ)^j) (by positivity)
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow ((2:ℝ)^j) p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hl : correctedCompletedT S D Ψ (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j)=
      ∑p∈hf.toFinset,correctedSummand S D Ψ (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j) p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_gaussian_factor,hz p hp,mul_zero])
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  have hi (p : Id×Id) : Integrable (fun t : ℝ=>
      correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) p.1 p.2*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
    simp_rw [correctedSummand_normTwisted]
    exact gaussian_slot_integrable W q _ _ _
  rw [hl,Finset.mul_sum]
  simp_rw [hr,Finset.sum_mul]
  rw [integral_finsetSum _ (fun p _=>hi p)]
  apply Finset.sum_congr rfl
  intro p hp
  exact gaussian_selected_summand W V hV hsep S D Ψ Z hZ j q hq p.1 p.2

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianTuple -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussian_selected_tuple_sum {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (Z : ℝ) (hZ : 0<Z) (j : ℕ) (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j))=
      ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  have hi (k : α) : Integrable (fun t : ℝ=>a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
    simpa only [mul_assoc] using (gaussian_selected_completed_integrable W (q k) _ S (D k) (Ψ k) _ (by positivity)).const_mul _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _=>hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hh := gaussian_selected_completed W V hV hsep S (D k) (Ψ k) Z hZ j (q k) (hq k hk)
  calc
    _ = a k*((∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j)) := by ring
    _ = a k*∫t : ℝ,correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
      (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))*
        gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by rw [hh]
    _ = _ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t=>by dsimp only; ring)

lemma gaussian_selected_scale {ι : Type*} [Fintype ι]
    (Z : ℝ) (P Q : ι→ℝ) (hP : ∀i,0<P i) :
    (Z*∏i,P i)*(∏i,Q i/P i)=Z*∏i,Q i := by
  rw [Finset.prod_div_distrib]
  have hp : (∏i,P i)≠0 := ne_of_gt (Finset.prod_pos (fun i _=>hP i))
  field_simp

theorem gaussian_selected_tuple_family {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) ∧
      (∀F : Finset α,∀a : α→ℂ,∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
        ∀Z : ℝ,0<Z→∀j : ℕ,∀q : α→ι→ℝ,(∀k∈F,∀i,0<q k i)→
        (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
          (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j))=
          ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
            (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
              gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_selected_slot_family W M hM hwindow
  exact ⟨V,hV,hbound,fun F a S D Ψ Z hZ j q hq=>
    gaussian_selected_tuple_sum W V hV hsep F a S D Ψ Z hZ j q hq⟩

lemma gaussianFixedWindow_twist_compact (t : ℝ) :
    HasCompactSupport (CompletedHeight.normTwistedSource gaussianFixedWindow t) := by
  exact gaussianFixedWindow_compact.mul_left

theorem gaussian_twisted_physical_row_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id) (j : ℕ) (t : ℝ) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)
          (fun A=>if D∣A then (1:ℂ) else 0) := by
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D _
    (gaussianFixedWindow_twist_compact t) _ (by positivity) (calibrationLowData S hS)

lemma correctedGaussian_dyadic_summable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    Summable (fun j : ℕ=>correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j)) := by
  have hh := (annular_reassembly_summable
    (fun p : Id×Id=>correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2)
    (fun p : Id×Id=>(Ideal.absNorm p.1:ℝ)*(Ideal.absNorm p.2:ℝ)^3)
    (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=>gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).prod_symm.prod
  simpa only [correctedCompletedT,gaussian_dyadic_correctedSummand S D Ψ Z hZ,Prod.swap] using hh

theorem gaussian_selected_tuple_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (hΨ : ∀k∈F,∀n,‖Ψ k n‖≤1) (Z : ℝ) (hZ : 0<Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      gaussianCompletedProfile (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  have hp (k : α) (hk : k∈F) : 0<Z*∏i,q k i :=
    mul_pos hZ (Finset.prod_pos (fun i _=>hq k hk i))
  have hd (k : α) (hk : k∈F) : Summable (fun j : ℕ=>a k*(∏i,W i (q k i))*
      correctedCompletedT S (D k) (Ψ k) (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j)) :=
    (correctedGaussian_dyadic_summable S (D k) (Ψ k) (hΨ k hk) _ (hp k hk)).mul_left _
  calc
    _ = ∑k∈F,∑'j : ℕ,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [correctedGaussian_eq_tsum_dyadic S (D k) (Ψ k) (hΨ k hk) _ (hp k hk),tsum_mul_left]
    _ = ∑'j : ℕ,∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j) := (Summable.tsum_finsetSum hd).symm
    _ = _ := by
      apply tsum_congr
      intro j
      exact gaussian_selected_tuple_sum W V hV hsep F a S D Ψ Z hZ j q hq

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianCrude -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CubicEisenstein FourierBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussianAnnulus_norm_le_one (y : ℝ) : ‖gaussianAnnulus y‖≤1 := by
  rw [gaussianAnnulus_norm]
  change Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)≤1
  linarith [Real.smoothTransition.le_one (2-y),Real.smoothTransition.nonneg (2-2*y)]

lemma gaussianAnnulus_scaled_square (N T : ℝ) (hN : 0<N) (hT : 0<T) :
    N^2*‖gaussianAnnulus (N/T)‖≤4*T^2 := by
  by_cases hz : gaussianAnnulus (N/T)=0
  · rw [hz,norm_zero,mul_zero]
    positivity
  have hn : N/T<2 := by
    by_contra hh
    exact hz (gaussianAnnulus_large _ (le_of_not_gt hh))
  have hn' : N<2*T := (div_lt_iff₀ hT).mp hn
  calc
    _ ≤ N^2 := mul_le_of_le_one_right (sq_nonneg _) (gaussianAnnulus_norm_le_one _)
    _ ≤ _ := by nlinarith

lemma gaussianFixedWindow_spectral_identity (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T t : ℝ) (hT : 0<T) (I J : Id) (hI : I≠0) (hJ : J≠0) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J=
      spectralSummand S D Ψ 2 I J*
        ((((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3:ℝ):ℂ)^2*
          (gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)*
            logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)))) := by
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hic : (Ideal.absNorm I:ℂ)≠0 := by exact_mod_cast hi.ne'
  have hjc : (Ideal.absNorm J:ℂ)≠0 := by exact_mod_cast hj.ne'
  unfold correctedSummand markedSummand CompletedGauss.summand spectralSummand fullIdealWeight
  rw [gaussianFixedWindow_Vstar_twist t _ (div_pos (mul_pos hi (pow_pos hj 3)) hT)]
  simp only [ite_eq_right hI,ite_eq_right hJ]
  norm_num only [show (3:ℂ)*2=6 by norm_num,Complex.cpow_neg,Complex.cpow_ofNat]
  push_cast
  field_simp

lemma gaussianFixedWindow_summand_crude (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (T t : ℝ) (hT : 0<T) (I J : Id) :
    ‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J‖≤
      4*T^2*rowMajorant 2 (I,J) := by
  by_cases hI : I=0
  · subst I
    simp only [correctedSummand,markedSummand,summand_zero_left,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  by_cases hJ : J=0
  · subst J
    simp only [correctedSummand,markedSummand,summand_zero_right,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := mul_pos hi (pow_pos hj 3)
  rw [gaussianFixedWindow_spectral_identity S D Ψ T t hT I J hI hJ,
    norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,
    norm_mul,logPhase_norm,mul_one]
  have hs : ‖spectralSummand S D Ψ 2 I J‖≤ rowMajorant 2 (I,J) := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_zero,zero_mul,add_zero] using
      spectralSummand_vertical_bound S D Ψ hΨ 2 0 (I,J)
  have hn := gaussianAnnulus_scaled_square _ T hN hT
  exact (mul_le_mul hs hn (by positivity) (by unfold rowMajorant;positivity)).trans_eq (by ring)

theorem gaussianFixedWindow_completed_crude :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀D : Id,∀Ψ : O→*ℂ,
      (∀n,‖Ψ n‖≤1)→∀T t : ℝ,0<T→
      ‖correctedCompletedT S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T‖≤C*T^2 := by
  let M : ℝ := ∑'p : Id×Id,rowMajorant 2 p
  have hM : 0≤M := tsum_nonneg (fun p=>by unfold rowMajorant;positivity)
  refine ⟨4*M+1,by positivity,?_⟩
  intro S D Ψ hΨ T t hT
  have hs := correctedSummand_summable S D Ψ _ (gaussianFixedWindow_twist_compact t) T hT
  change ‖∑'p : Id×Id,correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖≤_
  calc
    _ ≤ ∑'p : Id×Id,‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑'p : Id×Id,4*T^2*rowMajorant 2 p := hs.norm.tsum_le_tsum
      (fun p=>gaussianFixedWindow_summand_crude S D Ψ hΨ T t hT p.1 p.2)
      ((rowMajorant_summable 2 (by norm_num)).mul_left (4*T^2))
    _ = (4*M)*T^2 := by rw [tsum_mul_left];dsimp only [M];ring
    _ ≤ _ := by nlinarith [sq_nonneg T]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GaussianDensityBudget -/

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianJointMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : ℝ :=
  ∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖

lemma gaussianJointMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : 0≤gaussianJointMoment V hV J R := by
  apply integral_nonneg
  intro t
  positivity

lemma gaussianJointMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianJointMoment V hV J R≤C*R^(-A) := by
  obtain ⟨L,hL,hbox⟩ := hV.isBounded.exists_pos_norm_le
  have hb : ∀s,V s≠0→|s|≤L := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbox s (subset_tsupport V hs)
  exact gaussianLogWindow_fourier_moment V hV L hL.le hb A J

lemma gaussianJointMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianJointMoment V hV J R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianJointMoment_power_bound V hV J 0
  obtain ⟨C,hC,hdecay⟩ := gaussianJointMoment_power_bound V hV J (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianJointMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianJointMoment_polynomial_decay V hV J N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianJointMoment_nonneg V hV J _)
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end SevenEighths.ProbePhysical
end

end OAI

end

