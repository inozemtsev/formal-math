module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part016
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.Analysis.Normed.Group.Tannery
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part001
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.IdealBridge
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part021
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.Euler

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.SixthFrequency -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss ConcreteTraceCRT GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma finite_fourier_invariant_unit {R : Type*} [CommRing R] [Fintype R]
    (F : R→ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (hF : ∀ x,F ((u:R)*x)=F x) (H : R) :
    (∑ x,F x*ψ (((u:R)*H)*x)) = ∑ x,F x*ψ (H*x) := by
  symm
  rw [← Equiv.sum_comp u.mulLeft (fun x=>F x*ψ (H*x))]
  simp only [Units.mulLeft_apply,hF]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  congr 1
  ring

lemma supported_sixth_value (A v : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime A v) : idealRowHom (v^6) (Ideal.span {A})=1 := by
  rw [idealRowHom_sixth_mask _ _ hA, ite_eq_left ((Ideal.isCoprime_span_singleton_iff A v).mpr hcop)]

theorem barePhysicalFourier_sixth_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    barePhysicalFourier A s (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) (v^6*H) =
      barePhysicalFourier A s (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs)
  let := finite_quotient_span hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) (v^6) hcop.pow_left.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (supportedElement_ne_zero s hs) ((u:Residue (A*s))*x) =
        movingQuotient A s (supportedElement_ne_zero s hs) x := by
    rw [show (u:Residue (A*s))=Ideal.Quotient.mk _ (v^6) by rfl,
      movingQuotient_unit_scale A s hs (v^6) hcop.of_mul_right_right.pow_left,
      supported_sixth_value A v hA hcop.of_mul_right_left.symm,
      supported_sixth_value s v hs hcop.of_mul_right_right.symm,inv_one,one_mul,one_mul]
  have he := finite_fourier_invariant_unit (movingQuotient A s (supportedElement_ne_zero s hs))
    (quotientTrace (A*s) hAs) u hF (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x,movingQuotient A s (supportedElement_ne_zero s hs) x *
    quotientTrace (A*s) hAs (Ideal.Quotient.mk _ (v^6*H)*x)) =
    ∑ x,movingQuotient A s (supportedElement_ne_zero s hs) x *
      quotientTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u,residueUnit_coe,map_mul] using he

theorem bareCongruenceCoefficient_sixth_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  have he := barePhysicalFourier_sixth_frequency A s hA hs v H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  exact mul_left_cancel₀ hn he

theorem bareSourceCoefficient_sixth_frequency (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_sixth_frequency A s hA hs v H hcop]

theorem bareSourceCoefficient_product_frequency (η : HeckeFamily.Character) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryGenerator J*m^3)*r)) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) ((a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (a^6) * bareSourceCoefficient η J hJ.2 B r hB (b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop ((a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (b^6) hab
  rw [show b^6*a^6=(a*b)^6 by ring] at hi
  rw [show a^6*b^6=(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LocalUnitFrequency -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss ConcreteTraceCRT GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation ConcretePrimeRowBridge ProbePrimePower ProbeLocal ProbeEuler
local notation "O" => ActualEisensteinCubic.O

lemma finite_fourier_unit_scale {R : Type*} [CommRing R] [Fintype R]
    (F : R → ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (c : ℂ) (hc : c ≠ 0)
    (hF : ∀ x, F ((u : R) * x) = c * F x) (H : R) :
    (∑ x, F x * ψ (((u : R) * H) * x)) = c⁻¹ * ∑ x, F x * ψ (H*x) := by
  have he : (∑ x, F x * ψ (H*x)) = c * ∑ x, F x * ψ (((u : R)*H)*x) := by
    rw [← Equiv.sum_comp u.mulLeft (fun x => F x * ψ (H*x))]
    simp only [Units.mulLeft_apply, hF, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show H*((u : R)*x) = ((u : R)*H)*x by ring]
    ring
  rw [he, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem barePhysicalFourier_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    barePhysicalFourier A s (supportedElement_ne_zero A hA)
        (supportedElement_ne_zero s hs) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        barePhysicalFourier A s (supportedElement_ne_zero A hA)
          (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs)
  let := finite_quotient_span hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) b hcop.symm
  have hcA := idealRowHom_ne_zero_of_coprime A b hA hcop.of_mul_right_left.symm
  have hcs := idealRowHom_ne_zero_of_coprime s b hs hcop.of_mul_right_right.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (supportedElement_ne_zero s hs) ((u : Residue (A*s))*x) =
        (idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹) *
          movingQuotient A s (supportedElement_ne_zero s hs) x := by
    exact movingQuotient_unit_scale A s hs b hcop.of_mul_right_right x
  have he := finite_fourier_unit_scale (movingQuotient A s (supportedElement_ne_zero s hs))
    (quotientTrace (A*s) hAs) u _ (mul_ne_zero hcA (inv_ne_zero hcs)) hF
    (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x, movingQuotient A s (supportedElement_ne_zero s hs) x *
    quotientTrace (A*s) hAs (Ideal.Quotient.mk _ (b*H)*x)) =
      _ * ∑ x, movingQuotient A s (supportedElement_ne_zero s hs) x *
        quotientTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u, residueUnit_coe, map_mul, mul_inv_rev, inv_inv, mul_comm] using he

theorem bareCongruenceCoefficient_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  have he := barePhysicalFourier_unit_frequency A s hA hs b H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

lemma idealRowHom_norm_one_of_coprime (s b : O)
    (hs : Supported (Ideal.span {s})) (hcop : IsCoprime b s) :
    ‖idealRowHom b (Ideal.span {s})‖ = 1 := by
  have h6 := idealRowHom_sixth_mask b (Ideal.span {s}) hs
  rw [idealRowHom_argument_pow _ _ _ hs,
    ite_eq_left ((Ideal.isCoprime_span_singleton_iff s b).mpr hcop.symm)] at h6
  exact Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0)

theorem bareCongruenceCoefficient_unit_frequency_norm (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H)‖ =
      ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop,
    norm_mul, norm_mul, norm_inv,
    idealRowHom_norm_one_of_coprime A b hA hcop.of_mul_right_left,
    idealRowHom_norm_one_of_coprime s b hs hcop.of_mul_right_right,
    inv_one, one_mul, one_mul]

theorem bareCongruenceCoefficient_unit_frequency_eq_zero_iff (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H) = 0 ↔
      bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H = 0 := by
  rw [← norm_eq_zero, bareCongruenceCoefficient_unit_frequency_norm A s hA hs b H hcop,
    norm_eq_zero]

lemma supported_element_power (p : O) (hs : Supported (Ideal.span {p})) (n : ℕ) :
    Supported (Ideal.span {p^n}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hs n

lemma idealRowHom_prime_power_value (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (n : ℕ) :
    idealRowHom b (Ideal.span {p^n}) =
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^n := by
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg]

lemma actualSextic_unit_power_ne_zero (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hcop : IsCoprime b p) (t : ℕ) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t ≠ 0 := by
  apply pow_ne_zero
  exact (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff p b).mpr hcop.symm)

theorem bareCongruenceCoefficient_prime_power_unit_frequency (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) := by
  have he := bareCongruenceCoefficient_unit_frequency (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  simpa only [idealRowHom_prime_power_value p b hg, div_eq_mul_inv, mul_comm] using he

theorem bareCongruenceCoefficient_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          sourceScalar p hp hg t k j := by
  rw [bareCongruenceCoefficient_prime_power_unit_frequency p hp hs hg b hcop t k j,
    bareCongruenceCoefficient_all_prime_powers p hp hg t k j]

theorem barePhysicalFourier_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    barePhysicalFourier (p^t) (p^k) (pow_ne_zero _ hp.ne_zero)
        (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      (Ideal.absNorm (Ideal.span {p^k}) : ℂ) *
        (((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
          (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
            sourceScalar p hp hg t k j) := by
  rw [barePhysicalFourier_eq,
    bareCongruenceCoefficient_all_prime_powers_unit p hp hs hg b hcop t k j]

theorem bareCongruenceCoefficient_all_prime_powers_unit_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    ‖bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j)‖ =
      ‖sourceScalar p hp hg t k j‖ := by
  have he := bareCongruenceCoefficient_unit_frequency_norm (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  rw [bareCongruenceCoefficient_all_prime_powers p hp hg t k j] at he
  exact he

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SourceBounds -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbePhase ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareCongruenceCoefficient_norm_le (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    ‖bareCongruenceCoefficient A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  apply congruenceCoefficient_norm_le A s hA hs
  · intro m
    exact idealRowHom_norm _ _
  · intro m
    exact idealRowHom_norm _ _

theorem bareSourceCoefficient_norm_le (η : HeckeFamily.Character)
    (I : Ideal O) (hI : CubicSieve.Admissible I) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) (H : O) :
    ‖bareSourceCoefficient η I hI.2 A s (supportedElement_ne_zero A hA) H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  have hR : ‖reciprocitySign A s‖≤1 := sexticReciprocityPhase_norm A s
  have ht := targetMonoid_norm_le_one η A
  have hfac : ‖targetMonoid η A‖*‖reciprocitySign A s‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) ht).trans hR
  calc
    _ = (‖targetMonoid η A‖*‖reciprocitySign A s‖)*
        ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
      simp only [bareSourceCoefficient, correctedFiniteCoefficient, reciprocityCoefficient,
        norm_mul,norm_star,CubicSieve.gaussTwo_norm_one I hI,
        FiniteGaussPhase.norm_angularFactor A (supportedElement_ne_zero A hA),
        G_norm_one_of_odd A (supported_residue_odd A hA),one_mul,mul_one]
      ring
    _ ≤ ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hfac
    _ ≤ _ := bareCongruenceCoefficient_norm_le A s (supportedElement_ne_zero A hA)
      (supportedElement_ne_zero s hs) H

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighSeries -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def bareIdealHighCoefficient (η : HeckeFamily.Character) (u : O) (I J K L : Id) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L then
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
      (primaryGenerator I * primaryGenerator J^3) (primaryGenerator K)
      (mul_ne_zero (supported_primaryGenerator_ne_zero I h.2.1)
        (pow_ne_zero _ (supported_primaryGenerator_ne_zero J h.2.2.1)))
      (u*primaryGenerator L^6)
  else 0

theorem bareIdealHighCoefficient_norm_le (η : HeckeFamily.Character) (u : O) (I J K L : Id) :
    ‖bareIdealHighCoefficient η u I J K L‖ ≤ (K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3 := by
  unfold bareIdealHighCoefficient
  split_ifs with h
  · have hi := (supported_span_primaryGenerator_iff I).mpr h.2.1
    have hj := (supported_span_primaryGenerator_iff J).mpr h.2.2.1
    have hk := (supported_span_primaryGenerator_iff K).mpr h.2.2.2.1
    have hb := bareSourceCoefficient_norm_le η I ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      (primaryGenerator I*primaryGenerator J^3) (primaryGenerator K)
      (supported_completed _ _ hi hj) hk (u*primaryGenerator L^6)
    rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).1,
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).1,
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).1,
      map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] at hb
    convert hb using 1 ; ring
  · simp only [norm_zero]
    positivity

def bareIdealHighSummand (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  bareIdealHighCoefficient η u I J K L * fullIdealWeight (x+1/2) I *
    fullIdealWeight (1+3*x) J * fullIdealWeight w K * fullIdealWeight (6*z) L

lemma fullIdealWeight_nat_scale (s : ℂ) (I : Id) (hI : I≠0) (k : ℕ) :
    (I.absNorm:ℝ)^k * ‖fullIdealWeight s I‖ = ‖fullIdealWeight (s-k) I‖ := by
  have hN : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [fullIdealWeight,ite_eq_right hI]
  simp only [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re]
  rw [← Real.rpow_natCast,← Real.rpow_add hN]
  congr 1
  ring

theorem bareIdealHighSummand_norm_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖bareIdealHighSummand η u x w z I J K L‖ ≤
      ‖fullIdealWeight (x-1/2) I‖ * ‖fullIdealWeight (3*x-2) J‖ *
      ‖fullIdealWeight (w-1) K‖ * ‖fullIdealWeight (6*z) L‖ := by
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L
  · have hb := bareIdealHighCoefficient_norm_le η u I J K L
    calc
      _ ≤ ((K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3) *
          ‖fullIdealWeight (x+1/2) I‖ * ‖fullIdealWeight (1+3*x) J‖ *
          ‖fullIdealWeight w K‖ * ‖fullIdealWeight (6*z) L‖ := by
        simp only [bareIdealHighSummand,norm_mul]
        gcongr
      _ = ((I.absNorm:ℝ)^1*‖fullIdealWeight (x+1/2) I‖) *
          ((J.absNorm:ℝ)^3*‖fullIdealWeight (1+3*x) J‖) *
          ((K.absNorm:ℝ)^1*‖fullIdealWeight w K‖) * ‖fullIdealWeight (6*z) L‖ := by ring
      _ = _ := by
        rw [fullIdealWeight_nat_scale _ I h.2.1.1 1,
          fullIdealWeight_nat_scale _ J h.2.2.1.1 3,
          fullIdealWeight_nat_scale _ K h.2.2.2.1.1 1]
        norm_num only [Nat.cast_one, Nat.cast_ofNat]
        rw [show x+(1/2:ℂ)-1=x-1/2 by ring,show (1:ℂ)+3*x-3=3*x-2 by ring]
  · simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right h,zero_mul,norm_zero]
    positivity

theorem bareIdealHighSummand_summable (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by
    simp only [Complex.sub_re,Complex.div_re,Complex.one_re,Complex.one_im,
      show (2:ℂ).re=2 by rfl,show (2:ℂ).im=0 by rfl]
    norm_num
    linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by
    norm_num [Complex.sub_re,Complex.mul_re]
    linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by
    simp only [Complex.sub_re,Complex.one_re]
    linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by
    norm_num [Complex.mul_re]
    linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hall
  intro p
  simpa only [mul_assoc] using bareIdealHighSummand_norm_le η u x w z p.1.1 p.1.2 p.2.1 p.2.2

def bareIdealHighSeries (η : HeckeFamily.Character) (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighDeletion -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highIdealMask (S : Finset Id) (D I J K L : Id) : ℂ :=
  completedMask S D I J *
    (if ∀ P∈S,¬P∣K then 1 else 0) * (if ∀ P∈S,¬P∣L then 1 else 0)

lemma highIdealMask_norm_le_one (S : Finset Id) (D I J K L : Id) :
    ‖highIdealMask S D I J K L‖≤1 := by
  unfold highIdealMask
  split_ifs <;> simp only [mul_one,mul_zero,norm_zero]
  · exact completedMask_norm_le_one S D I J
  all_goals norm_num

def markedIdealHighSummand (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  highIdealMask S D I J K L * bareIdealHighSummand η u x w z I J K L

lemma markedIdealHighSummand_norm_le (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖markedIdealHighSummand S D η u x w z I J K L‖≤‖bareIdealHighSummand η u x w z I J K L‖ := by
  rw [markedIdealHighSummand,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (highIdealMask_norm_le_one S D I J K L)

theorem markedIdealHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (fun p=>markedIdealHighSummand_norm_le S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (bareIdealHighSummand_summable η u x w z hx hw hz).norm

def markedIdealHighSeries (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighAbsolute -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
abbrev NonzeroFrequency := {u : O // u≠0}

def frequencyWeight (z : ℂ) (u : NonzeroFrequency) : ℂ := (elementNorm u.val:ℂ)^(-z)

lemma frequencyWeight_norm (z : ℂ) (u : NonzeroFrequency) :
    ‖frequencyWeight z u‖=‖eisEmbedding u.val‖^(-2*z.re) := by
  have hn : 0<‖eisEmbedding u.val‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero u.property)
  unfold frequencyWeight elementNorm
  have hN : (Ideal.absNorm (Ideal.span {u.val}):ℝ)=‖eisEmbedding u.val‖^2 :=
    (eisEmbedding_norm_sq_eq_absNorm_span u.val).symm
  rw [hN,
    Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn), Complex.neg_re,
    ← Real.rpow_natCast_mul hn.le 2]
  congr 1
  ring

theorem frequencyWeight_summable_norm (z : ℂ) (hz : 1<z.re) :
    Summable (fun u : NonzeroFrequency => ‖frequencyWeight z u‖) := by
  simp only [frequencyWeight_norm]
  exact (summable_embedding_rpow (-2*z.re) (by linarith)).subtype _

def highAbsoluteMajorant (x w z : ℂ) (p : (Id×Id)×(Id×Id)) : ℝ :=
  ‖fullIdealWeight (x-1/2) p.1.1‖ * ‖fullIdealWeight (3*x-2) p.1.2‖ *
  ‖fullIdealWeight (w-1) p.2.1‖ * ‖fullIdealWeight (6*z) p.2.2‖

lemma highAbsoluteMajorant_nonneg (x w z : ℂ) (p : (Id×Id)×(Id×Id)) :
    0≤highAbsoluteMajorant x w z p := by unfold highAbsoluteMajorant; positivity

lemma highAbsoluteMajorant_summable (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) : Summable (highAbsoluteMajorant x w z) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by norm_num [Complex.sub_re,Complex.div_re]; linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by norm_num [Complex.sub_re,Complex.mul_re]; linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by norm_num [Complex.mul_re]; linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  unfold highAbsoluteMajorant
  simpa only [mul_assoc] using hall

theorem fullHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re)
    (mask : NonzeroFrequency→ℂ) (hmask : ∀u,‖mask u‖≤1) :
    Summable (fun p : NonzeroFrequency×((Id×Id)×(Id×Id)) =>
      mask p.1 * frequencyWeight z p.1 *
        markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) := by
  have hm := (frequencyWeight_summable_norm z hz).mul_of_nonneg
    (highAbsoluteMajorant_summable x w z hx hw (by linarith))
    (fun _=>norm_nonneg _) (highAbsoluteMajorant_nonneg x w z)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hm
  intro p
  rw [norm_mul,norm_mul]
  have hcoeff := (markedIdealHighSummand_norm_le S D η p.1.val x w z
    p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  change _≤‖frequencyWeight z p.1‖*highAbsoluteMajorant x w z p.2
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hmask p.1) (norm_nonneg _)
      · exact hcoeff
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [one_mul]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.IdealMultiplicative -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highSupport (I J K L : Id) : Prop :=
  Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L

lemma highSupport_mul (I J K L I' J' K' L' : Id) (hcop : IsCoprime I I') :
    highSupport (I*I') (J*J') (K*K') (L*L') ↔
      highSupport I J K L ∧ highSupport I' J' K' L' := by
  simp only [highSupport, squarefree_mul_iff, supported_mul_iff]
  have hc := hcop.isRelPrime
  tauto

lemma span_primaryGenerator_of_supported (I : Id) (hI : Supported I) :
    Ideal.span {primaryGenerator I}=I :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1

lemma primaryGenerator_coprime (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) : IsCoprime (primaryGenerator I) (primaryGenerator J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rwa [span_primaryGenerator_of_supported I hI,span_primaryGenerator_of_supported J hJ]

lemma completed_block_dvd_cube (I J K L : Id) : I*J^3*K ∣ (I*J*K*L)^3 := by
  refine ⟨I ^2*K^2*L^3,?_⟩
  ring

lemma first_block_dvd (I J K L : Id) : I ∣ I*J*K*L := by
  refine ⟨J*K*L,?_⟩
  ring

lemma last_block_dvd (I J K L : Id) : L ∣ I*J*K*L := by
  refine ⟨I*J*K,?_⟩
  ring

theorem bareIdealHighCoefficient_mul (η : HeckeFamily.Character)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η 1 (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η 1 I J K L * bareIdealHighCoefficient η 1 I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryGenerator_mul,primaryGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_frequency η I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul,one_mul]
    dsimp only at he
    convert he using 1 ; ring_nf
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dite_eq_right hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=>h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dite_eq_right hj,mul_zero]
    · unfold highSupport at hi
      rw [dite_eq_right hi,zero_mul]

lemma fullIdealWeight_mul (s : ℂ) (I J : Id) :
    fullIdealWeight s (I*J)=fullIdealWeight s I*fullIdealWeight s J :=
  (IdealEuler.normWeight s).map_mul I J

theorem bareIdealHighSummand_mul (η : HeckeFamily.Character) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η 1 x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η 1 x w z I J K L * bareIdealHighSummand η 1 x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_mul η I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.IdealFactorization -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PrimeIdeal := {P : Id // Prime P}

def primeValuations (I : Id) : PrimeIdeal →₀ ℕ :=
  (factorization I).subtypeDomain Prime

def idealFromValuations (v : PrimeIdeal →₀ ℕ) : Id :=
  v.prod (fun P n=>P.val^n)

lemma idealFromValuations_ne_zero (v : PrimeIdeal →₀ ℕ) : idealFromValuations v≠0 := by
  unfold idealFromValuations Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>pow_ne_zero _ P.property.ne_zero)

@[simp] lemma primeValuations_apply (I : Id) (P : PrimeIdeal) :
    primeValuations I P=(normalizedFactors I).count P.val := by
  simp only [primeValuations,Finsupp.subtypeDomain_apply,factorization_eq_count]

@[simp] lemma primeValuations_one : primeValuations 1=0 := by
  simp only [primeValuations,factorization_one,Finsupp.subtypeDomain_zero]

lemma primeValuations_mul (I J : Id) (hI : I≠0) (hJ : J≠0) :
    primeValuations (I*J)=primeValuations I+primeValuations J := by
  simp only [primeValuations,factorization_mul hI hJ,Finsupp.subtypeDomain_add]

@[simp] lemma primeValuations_prime (P : PrimeIdeal) :
    primeValuations P.val=Finsupp.single P 1 := by
  ext Q
  simp only [primeValuations_apply,normalizedFactors_irreducible P.property.irreducible,
    normalize_eq,Multiset.count_singleton,Finsupp.single_apply]
  by_cases h : Q=P
  · subst Q
    simp
  · have hv : Q.val≠P.val := fun hh=>h (Subtype.ext hh)
    simp [Ne.symm h,hv]

lemma primeValuations_pow (I : Id) (n : ℕ) :
    primeValuations (I ^n)=n • primeValuations I := by
  ext P
  simp only [primeValuations_apply,normalizedFactors_pow,Multiset.count_nsmul,
    Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

@[simp] lemma idealFromValuations_zero : idealFromValuations 0=1 := by
  simp [idealFromValuations]

lemma idealFromValuations_add (v w : PrimeIdeal →₀ ℕ) :
    idealFromValuations (v+w)=idealFromValuations v*idealFromValuations w := by
  exact Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)

@[simp] lemma idealFromValuations_single (P : PrimeIdeal) (n : ℕ) :
    idealFromValuations (Finsupp.single P n)=P.val^n := by
  simp [idealFromValuations]

@[simp] theorem primeValuations_idealFromValuations (v : PrimeIdeal →₀ ℕ) :
    primeValuations (idealFromValuations v)=v := by
  induction v using Finsupp.induction with
  | zero => simp only [idealFromValuations_zero,primeValuations_one]
  | @single_add P n v hP hn ih =>
    rw [idealFromValuations_add,primeValuations_mul _ _
      (idealFromValuations_ne_zero _) (idealFromValuations_ne_zero _),ih]
    simp only [idealFromValuations_single,primeValuations_pow,primeValuations_prime,
      Finsupp.smul_single,smul_eq_mul,mul_one]

@[simp] theorem idealFromValuations_primeValuations (I : Id) (hI : I≠0) :
    idealFromValuations (primeValuations I)=I := by
  have hs : ∀ P∈(factorization I).support,Prime P := by
    intro P hP
    exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp (by simpa using hP))
  unfold idealFromValuations primeValuations
  rw [Finsupp.prod_subtypeDomain_index hs]
  simp only [Finsupp.prod,support_factorization,factorization_eq_count]
  rw [← Finset.prod_multiset_count_of_subset _ _ (Finset.Subset.refl _)]
  exact Ideal.prod_normalizedFactors_eq_self hI

def nonzeroIdealValuationEquiv : {I : Id // I≠0} ≃ (PrimeIdeal →₀ ℕ) where
  toFun I := primeValuations I.val
  invFun v := ⟨idealFromValuations v,idealFromValuations_ne_zero v⟩
  left_inv I := Subtype.ext (idealFromValuations_primeValuations I.val I.property)
  right_inv := primeValuations_idealFromValuations

lemma primeIdeal_coprime (P Q : PrimeIdeal) (h : P≠Q) : IsCoprime P.val Q.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : Q.val.IsPrime := Ideal.isPrime_of_prime Q.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  let : Q.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance Q.property.ne_zero
  exact Ideal.isCoprime_of_isMaximal (fun hh=>h (Subtype.ext hh))

lemma prime_coprime_idealFromValuations (P : PrimeIdeal) (v : PrimeIdeal →₀ ℕ)
    (hP : v P=0) : IsCoprime P.val (idealFromValuations v) := by
  apply IsCoprime.prod_right
  intro Q hQ
  apply IsCoprime.pow_right
  apply primeIdeal_coprime
  intro hh
  subst Q
  exact Finsupp.mem_support_iff.mp hQ hP

def finsuppPairEquiv {α β γ : Type*} [Zero β] [Zero γ] :
    ((α→₀β)×(α→₀γ)) ≃ (α→₀(β×γ)) where
  toFun v := Finsupp.zipWith Prod.mk rfl v.1 v.2
  invFun v := (v.mapRange Prod.fst rfl,v.mapRange Prod.snd rfl)
  left_inv v := by
    apply Prod.ext <;> ext a <;> rfl
  right_inv v := by
    apply Finsupp.ext
    intro a
    exact Prod.eta (v a)

abbrev HighValuation := (ℕ×ℕ)×(ℕ×ℕ)
abbrev NonzeroIdeal := {I : Id // I≠0}

def highValuationEquiv : ((NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) ≃
    (PrimeIdeal→₀HighValuation) :=
  (Equiv.prodCongr
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)).trans
      ((Equiv.prodCongr finsuppPairEquiv finsuppPairEquiv).trans finsuppPairEquiv)

@[simp] lemma highValuationEquiv_apply
    (a : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) (P : PrimeIdeal) :
    highValuationEquiv a P =
      ((primeValuations a.1.1.val P,primeValuations a.1.2.val P),
        (primeValuations a.2.1.val P,primeValuations a.2.2.val P)) := rfl

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.EulerFinsupp -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp

lemma finitePi_fin {β : Type*} (n : ℕ) (f : Fin n→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : Fin n→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : Fin n→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  induction n with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp
  | succ n ih =>
    have ht := ih (fun i=>f i.succ) (fun i=>hf i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n+1)=>β)
    have he (v : β×(Fin n→β)) :
        (∏ i,f i (e v i))=f 0 v.1*(∏ i,f i.succ (v.2 i)) := by
      rw [Fin.prod_univ_succ]
      rfl
    constructor
    · rw [←e.summable_iff]
      simp only [Function.comp_def,he]
      have hm : Summable (fun v : β×(Fin n→β)=>‖f 0 v.1‖ * ‖∏ i : Fin n,f i.succ (v.2 i)‖) :=
        (hf 0).mul_of_nonneg ht.1 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
      simpa only [norm_mul] using hm
    · rw [←e.tsum_eq (fun v=>∏ i,f i (v i))]
      simp only [he]
      rw [←tsum_mul_tsum_of_summable_norm (f:=f 0)
        (g:=fun v : Fin n→β=>∏ i : Fin n,f i.succ (v i)) (hf 0) ht.1,ht.2,Fin.prod_univ_succ]

lemma finitePi {α β : Type*} [Fintype α] (f : α→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : α→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : α→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  let e := Fintype.equivFin α
  let d := Equiv.arrowCongr e.symm (Equiv.refl β)
  have h := finitePi_fin (Fintype.card α) (fun i=>f (e.symm i)) (fun i=>hf (e.symm i))
  have hd (v : Fin (Fintype.card α)→β) :
      (∏ i,f i (d v i))=∏ j,f (e.symm j) (v j) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [d,Equiv.arrowCongr_apply,Equiv.symm_symm,Equiv.refl_apply,e.symm_apply_apply,Function.comp_apply]
  constructor
  · rw [←d.summable_iff]
    simpa only [Function.comp_def,hd] using h.1
  · rw [←d.tsum_eq (fun v=>∏ i,f i (v i))]
    simp only [hd]
    rw [h.2]
    exact e.symm.prod_comp (fun i=>∑' b,f i b)

variable {α β : Type*} [AddCommMonoid β]

lemma finiteEuler (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hf : ∀a,Summable (fun b=>‖f a b‖)) (S : Finset α) :
    (∑' v : {v : α→₀β // (v.support:Set α)⊆S},v.val.prod f)=
      ∏ a∈S,∑' b,f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      v.val.prod f=∏ a:S,f a.val (e v a) := by
    rw [←Finsupp.prod_subtypeDomain_index (p:=fun a=>a∈S) (fun a ha=>v.property ha)]
    exact Finsupp.prod_fintype _ _ (fun a=>h0 a.val)
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏ a:S,f a.val (v a))]
  rw [(finitePi (fun a:S=>f a.val) (fun a=>hf a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑' b,f a b)

theorem hasProd_of_summable (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖)) :
    HasProd (fun a=>∑' b,f a b) (∑' v : α→₀β,v.prod f) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑' v : α→₀β,
      if v.support⊆S then v.prod f else 0) atTop (𝓝 (∑' v : α→₀β,v.prod f)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [ite_eq_left hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  have he (S : Finset α) : (∑' v : α→₀β,if v.support⊆S then v.prod f else 0)=
      ∏a∈S,∑' b,f a b := by
    rw [←finiteEuler f h0 hf S]
    trans ∑' v : α→₀β, {v : α→₀β | (v.support:Set α)⊆S}.indicator (fun v=>v.prod f) v
    · apply tsum_congr
      intro v
      simp only [Set.indicator,Set.mem_ofPred_eq,Finset.coe_subset]
    · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (fun v=>v.prod f)).symm
  change Tendsto (fun S : Finset α=>∏a∈S,∑' b,f a b) atTop _
  simpa only [he] using ht

end SevenEighths.ProbeEulerFinsupp
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.EulerMarked -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp
variable {α β : Type*} [AddCommMonoid β]

def markedArray (T : Finset α) (m f : α→β→ℂ) (v : α→₀β) : ℂ :=
  (∏a∈T,m a (v a))*v.prod f

def markedLocal (T : Finset α) (m f : α→β→ℂ) (a : α) (b : β) : ℂ :=
  (if a∈T then m a b else 1)*f a b

lemma markedArray_finite (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (v : α→₀β) (hv : v.support⊆S) :
    markedArray T m f v=∏a∈S,markedLocal T m f a (v a) := by
  simp only [markedArray,markedLocal,Finset.prod_mul_distrib]
  congr 1
  · symm
    rw [←Finset.prod_subset hTS]
    · apply Finset.prod_congr rfl
      intro a ha
      simp only [ite_eq_left ha]
    · intro a ha hna
      simp only [ite_eq_right hna]
  · exact Finsupp.prod_of_support_subset v hv _ (fun a _=>h0 a)

lemma markedArray_norm_le (T : Finset α) (m f : α→β→ℂ)
    (hm : ∀a∈T,∀b,‖m a b‖≤1) (v : α→₀β) :
    ‖markedArray T m f v‖≤‖v.prod f‖ := by
  rw [markedArray,norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun a ha=>hm a ha _)

lemma marked_finiteEuler (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (hf : ∀a,Summable (fun b=>‖f a b‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    (∑'v : {v : α→₀β // (v.support:Set α)⊆S},markedArray T m f v.val)=
      ∏a∈S,∑'b,markedLocal T m f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      markedArray T m f v.val=∏a:S,markedLocal T m f a.val (e v a) := by
    rw [markedArray_finite T S hTS m f h0 v.val v.property]
    exact (Finset.prod_coe_sort S _).symm
  have hg (a : α) : Summable (fun b=>‖markedLocal T m f a b‖) := by
    apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (hf a)
    intro b
    rw [markedLocal,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    split_ifs with ha
    · exact hm a ha b
    · simp
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏a:S,markedLocal T m f a.val (v a))]
  rw [(finitePi (fun a:S=>markedLocal T m f a.val) (fun a=>hg a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑'b,markedLocal T m f a b)

theorem marked_hasProd (T : Finset α) (m f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    HasProd (fun a=>∑'b,markedLocal T m f a b) (∑'v : α→₀β,markedArray T m f v) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑'v : α→₀β,
      if v.support⊆S then markedArray T m f v else 0) atTop
      (𝓝 (∑'v : α→₀β,markedArray T m f v)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [ite_eq_left hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact markedArray_norm_le T m f hm v
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  change Tendsto (fun S : Finset α=>∏a∈S,∑'b,markedLocal T m f a b) atTop _
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with S hTS
  rw [←marked_finiteEuler T S hTS m f h0 hf hm]
  trans ∑'v : α→₀β,{v : α→₀β | (v.support:Set α)⊆S}.indicator (markedArray T m f) v
  · apply tsum_congr
    intro v
    simp only [Set.indicator,Set.mem_ofPred_eq,Finset.coe_subset]
  · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (markedArray T m f)).symm

end SevenEighths.ProbeEulerFinsupp
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RadialExchange -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma radialFourier_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hσ : 0<σ) (hr : 0< r) :
    paperRadialFourier W r=verticalIntegral σ (fun z=>(r:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  have he := ProbeRadialMellin.radial_mellin_inversion W a b ha hW σ r hσ hr
  simpa only [mellinInv,verticalIntegral,Complex.real_smul,smul_eq_mul] using he.symm

lemma radial_sum_exchange {ι : Type*} [Countable ι] (W : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (σ : ℝ) (hσ : 0<σ) (c : ι→ℂ) (r : ι→ℝ) (hr : ∀i,0< r i)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    (∑'i,c i*paperRadialFourier W (r i))=
      verticalIntegral σ (fun z=>∑'i,c i*(r i:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  let F := fun i (t : ℝ)=>c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*
    mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)
  have hF (i) : Integrable (F i) := by
    simpa only [F,mul_assoc] using
      (ProbeRadialMellin.radial_mellin_inverse_integrable W a b ha hW σ (r i) hσ (hr i)).const_mul (c i)
  have hn (i) (t : ℝ) : ‖F i t‖=(‖c i‖*(r i)^(-σ))*
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hr i)]
    simp
  have hsum : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp only [hn,integral_const_mul]
    exact hc.mul_right _
  have he := integral_tsum_of_summable_integral_norm hF hsum
  simp_rw [radialFourier_vertical_inverse W a b ha hW σ _ hσ (hr _)]
  unfold verticalIntegral
  have hi (i) : c i*(↑(1/(2*Real.pi))*(∫t : ℝ,
      (r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)))=
      (↑(1/(2*Real.pi)):ℂ)*(∫t : ℝ,F i t) := by
    simp only [F,mul_assoc,integral_const_mul]
    ring
  simp_rw [hi]
  rw [tsum_mul_left,he]

lemma frequency_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>(elementNorm H.val)^(-σ)) := by
  have he (H : NonzeroFrequency) : ‖frequencyWeight (σ:ℂ) H‖=(elementNorm H.val)^(-σ) := by
    have hH : 0<elementNorm H.val := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr H.property))
    rw [frequencyWeight,Complex.norm_cpow_eq_rpow_re_of_pos hH]
    simp
  simpa only [he,Complex.ofReal_re] using frequencyWeight_summable_norm (σ:ℂ) hσ

theorem actualFrequency_moment_summable (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>‖actualCongruenceCoefficient C A s hA H.val‖*
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)) := by
  have hd : 0<elementNorm ((C.generator*A)*s) := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
  have hr (H : NonzeroFrequency) :
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)=
        (K/elementNorm ((C.generator*A)*s))^(-σ)*(elementNorm H.val)^(-σ) := by
    rw [show K*elementNorm H.val/elementNorm ((C.generator*A)*s)=
      (K/elementNorm ((C.generator*A)*s))*elementNorm H.val by ring]
    apply Real.mul_rpow (div_pos hK hd).le
    unfold elementNorm
    positivity
  simp only [hr]
  have hb := (frequency_rpow_summable σ hσ).mul_left
    (((Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {C.generator*A}):ℝ))*
      (K/elementNorm ((C.generator*A)*s))^(-σ))
  apply Summable.of_nonneg_of_le (fun H=>mul_nonneg (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (div_pos hK hd).le _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _))) _ hb
  intro H
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (actualCongruenceCoefficient_norm_le C A s hA hs H.val)
      (Real.rpow_nonneg (div_pos hK hd).le _)) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RadialIdentity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma elementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

lemma actualCongruenceCoefficient_zero_frequency (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA 0=0 := by
  apply actualCongruenceCoefficient_zero_off_calibration S hS A s hA hs hcop
  intro hc
  have hz := (calibrationForSet_coprime_iff S hS 0).mp hc
  obtain ⟨P,hP⟩ := hSne
  exact hz P hP P.zero_mem

theorem actualFrequency_mellin_nonzero (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    (∑'H : NonzeroFrequency,actualCongruenceCoefficient C A s hA H.val*
      paperRadialFourier W (K*elementNorm H.val/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  let : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  have he := radial_sum_exchange W a b ha hW σ (by linarith)
    (fun H : NonzeroFrequency=>actualCongruenceCoefficient C A s hA H.val)
    (fun H=>K*elementNorm H.val/elementNorm ((C.generator*A)*s)) (by
      intro H
      exact div_pos (mul_pos hK (elementNorm_pos H.val H.property))
        (elementNorm_pos _ (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
    (actualFrequency_moment_summable C A s hA hs K hK σ hσ)
  simpa only [Complex.ofReal_mul,Complex.ofReal_div] using he

theorem actualFrequency_mellin (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s))
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    let C := calibrationForSet S hS
    (∑'H : O,actualCongruenceCoefficient C A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  dsimp only
  rw [←actualFrequency_mellin_nonzero (calibrationForSet S hS) A s hA hs W a b ha hW K hK σ hσ]
  symm
  apply (Subtype.val_injective : Function.Injective (fun H : NonzeroFrequency=>H.val)).tsum_eq
    (f:=fun H : O=>actualCongruenceCoefficient (calibrationForSet S hS) A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm (((calibrationForSet S hS).generator*A)*s)))
  intro H hH
  have hn : H≠0 := by
    intro hz
    subst H
    exact hH (by dsimp only; rw [actualCongruenceCoefficient_zero_frequency S hS hSne A s hA hs hcop,zero_mul])
  exact ⟨⟨H,hn⟩,rfl⟩

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RadialSpectral -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma spectralSummand_mask_nonzero (S : Finset Id) (D I J : Id) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) : completedMask S D I J≠0 := by
  intro hz
  exact h (by simp only [spectralSummand,hz,zero_mul])

lemma spectralSummand_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Id) (Ψ : O→*ℂ) (t : ℂ) (h : spectralSummand S D Ψ t I J≠0) :
    IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hA : completedIndex I J≠0 := by
    intro hz
    exact h (spectralSummand_zero_completedIndex S D I J Ψ t hz)
  have hout : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  apply calibrationForSet_coprime_of_excluded S hS
  rw [completedIndex_eq_primaryGenerator] at hA ⊢
  rw [(primaryGenerator_spec (I*J^3) hA).1]
  exact hout

def radialMellinSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset Id) (D : Id) (s : O) (hs : Supported (Ideal.span {s}))
    (W : SchwartzMap ℝ ℂ) (K σ : ℝ) (t : ℂ) (I J : Id) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C (completedIndex I J) s hA H.val*
          ((K*elementNorm H.val/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)*
            mellin (paperRadialFourier W) z)
  else 0

theorem transformedSpectralTerm_radial_mellin (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (D : Id)
    (s : O) (hs : Supported (Ideal.span {s})) (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (K σ : ℝ) (hK : 0<K) (hσ : 1<σ) (t : ℂ) (I J : Id) :
    transformedSpectralTerm η (calibrationForSet S hS) S D s hs W K t I J=
      radialMellinSpectralTerm η (calibrationForSet S hS) S D s hs W K σ t I J := by
  unfold transformedSpectralTerm radialMellinSpectralTerm
  split_ifs with hA
  · by_cases hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0
    · simp only [hz,zero_mul]
    · rw [actualFrequency_mellin S hS hSne (completedIndex I J) s hA (supportedElement_ne_zero s hs)
        ((spectralSummand_calibration_coprime S hS D I J _ t hz).mul_right hcs)
        W a b ha hW K hK σ hσ]
  · rfl

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalRadial -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def radialMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ) (X Y Z σ : ℝ) : ℂ :=
  (Y:ℂ)⁻¹*∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      W1 (qs/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ))*
      verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
        ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
          (elementNorm C.generator*qs*X) σ t p.1 p.2)
    else 0

theorem markedPhysicalProbe_eq_radial_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Set.Icc a b)
    (X Y Z σ : ℝ) (hX : 0<X) (hZ : 0<Z) (hσ : 1<σ) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      radialMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z σ := by
  have hWc : HasCompactSupport (W0 : ℝ→ℂ) := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW
  rw [markedPhysicalProbe_eq_poisson η (calibrationForSet S hS) D W0 W1 hWc (W0.smooth (⊤:ℕ∞)) X Y Z hX hZ]
  unfold poissonPhysicalProbe radialMellinPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    congr 1
    unfold verticalIntegral
    congr 1
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    congr 1
    apply tsum_congr
    intro p
    have hcs : IsCoprime (calibrationForSet S hS).generator (primaryGenerator s.val) := by
      apply calibrationForSet_coprime_of_excluded S hS
      rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1]
      simpa only [calibrationForSet_excluded] using hs
    have hK : 0<elementNorm (calibrationForSet S hS).generator*(Ideal.absNorm s.val:ℝ)*X :=
      mul_pos (mul_pos (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero)
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1))) hX
    simpa only [calibrationForSet_excluded] using transformedSpectralTerm_radial_mellin η S hS hSne D
      (primaryGenerator s.val) ((supported_span_primaryGenerator_iff s.val).mpr s.property) hcs
      W0 a b ha hW _ σ hK hσ _ p.1 p.2
  · rfl

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SixthDecomposition -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ActualEisensteinCubic HeckeInverseAmplification CenteredExceptionalCount ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sixthRow_surjective (H : NonzeroFrequency) :
    ∃p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,rowMap p=H.val := by
  let I : Id := Ideal.span {H.val}
  have hI : I≠0 := Ideal.span_singleton_eq_bot.not.mpr H.property
  let J : Id := sixthQuotient I
  have hJ : J≠0 := sixthQuotient_ne_zero I
  let a := idealGenerator J
  have ha : a≠0 := idealGenerator_ne_zero J hJ
  have hspan : Ideal.span {a}=J := span_idealGenerator J
  have hd : a^6∣H.val := by
    apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
    rw [←Ideal.span_singleton_pow,hspan]
    change J^6∣I
    rw [←sixth_normal_form I hI]
    exact dvd_mul_left _ _
  obtain ⟨u,hu⟩ := hd
  have hu0 : u≠0 := by
    intro hz
    rw [hz,mul_zero] at hu
    exact H.property hu
  have hsu : Ideal.span {u}=sixthRemainder I := by
    have hi : Ideal.span {u}*J^6=I := by
      rw [←hspan,Ideal.span_singleton_pow,Ideal.span_singleton_mul_span_singleton]
      exact congrArg (fun b : O=>Ideal.span {b}) (by simpa only [mul_comm] using hu.symm)
    apply mul_right_cancel₀ (pow_ne_zero 6 hJ)
    exact hi.trans (sixth_normal_form I hI).symm
  have hf : SixthFree (Ideal.span {u}) := by
    rw [hsu]
    intro P
    exact sixthRemainder_valuation_lt I P
  refine ⟨(⟨u,hu0,hf⟩,⟨J,hJ⟩),?_⟩
  change u*a^6=H.val
  simpa only [mul_comm] using hu.symm

def sixthFrequencyEquiv : FreeRow×HeckeInverseAmplification.NonzeroIdeal ≃ NonzeroFrequency :=
  Equiv.ofBijective (fun p=>⟨rowMap p,rowMap_ne_zero p⟩) ⟨
    fun p q h=>rowMap_injective (congrArg Subtype.val h),
    fun H=>by obtain ⟨p,hp⟩ := sixthRow_surjective H;exact ⟨p,Subtype.ext hp⟩⟩

lemma sixthFrequencyEquiv_apply (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) :
    (sixthFrequencyEquiv p).val=p.1.val*(idealGenerator p.2.val)^6 := rfl

theorem tsum_sixth_decomposition (f : NonzeroFrequency→ℂ) :
    (∑'H : NonzeroFrequency,f H)=
      ∑'p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,f (sixthFrequencyEquiv p) :=
  (sixthFrequencyEquiv.tsum_eq f).symm

lemma idealGenerator_sixth_eq_primary (I : Id) (hI : CanonicalQuadraticSieve.Supported I) :
    (idealGenerator I)^6=(CompletedGauss.primaryGenerator I)^6 := by
  have he : Ideal.span {idealGenerator I}=Ideal.span {CompletedGauss.primaryGenerator I} :=
    (span_idealGenerator I).trans
      (CompletedGauss.primaryGenerator_spec I
        (supported_primaryGenerator_ne_zero I hI)).1.symm
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he
  have hh := congrArg (fun a : O=>a^6) hu
  simpa only [mul_pow,CanonicalUnitEuler.unit_pow_six,mul_one] using hh

lemma sixthFrequencyEquiv_primary (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal)
    (hP : CanonicalQuadraticSieve.Supported p.2.val) :
    (sixthFrequencyEquiv p).val=p.1.val*(CompletedGauss.primaryGenerator p.2.val)^6 := by
  rw [sixthFrequencyEquiv_apply,idealGenerator_sixth_eq_primary p.2.val hP]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SourcePrime -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
open ProbePhase ProbeEuler ProbePrimePower FiniteGaussPhase QuadraticGaussRay
local notation "O" => ActualEisensteinCubic.O

theorem gaussTwo_prime_localGamma (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (hI : primaryGenerator (Ideal.span {p})≠0) :
    gaussTwo (Ideal.span {p}) hI=localGamma p hp.ne_zero hg 2 := by
  let pp : Unit→O := fun _=>p
  have hpp : ∀i,pp i≠0 := fun _=>hp.ne_zero
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hi : primaryGenerator (Ideal.span {∏i,pp i})≠0 := by simpa [pp] using hI
  have he := gaussTwo_eq_canonicalProductGauss pp hpp hcop (fun _=>hg) (fun _=>hprimary) hi
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 2)] at he
  simpa [pp,localGamma,ConcreteBreveE.normalizedTraceGauss] using he

theorem G_prime_localG (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    G p=MixedGaussConversion.localG p hp hg := by
  let pp : Unit→O := fun _=>p
  have hpp : ∀i,pp i≠0 := fun _=>hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductG_eq_fixedGValue pp hpp hcop (fun _=>hg)
    (fun _=>hchar) (fun _=>hprimary)
  unfold canonicalProductG at he
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 3)] at he
  simpa [pp,G,fixedGQuotientValue,MixedGaussConversion.localG,breveLocalG,breveGamma3,
    ConcreteBreveE.normalizedTraceGauss] using he.symm

theorem localGamma_one_two_full_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * G p := by
  rw [G_prime_localG p hp hg hchar hprimary]
  exact localGamma_one_two_signal p hp hg hchar hprimary

lemma angularFactor_pow (p : O) (n : ℕ) : angularFactor (p^n)=angularFactor p^n := by
  simp only [angularFactor,map_pow,norm_pow,Complex.ofReal_pow,div_pow]

lemma gaussTwo_one : gaussTwo (1:Ideal O) (by rw [primaryGenerator_one]; exact one_ne_zero)=1 := by
  have hI : CubicSieve.Admissible (1:Ideal O) := ⟨squarefree_one,by rw [primaryGenerator_one]; exact one_ne_zero⟩
  rw [gaussTwo_eq_elementFourier (1:Ideal O) hI]
  simp only [primaryGenerator_one,map_one,norm_one,Complex.ofReal_one,div_one]
  have hrow (a : O) : CubicSieve.cubicRow (1:Ideal O) a=1 := by
    rw [CubicSieve.cubicRow,←idealRowHom_square,map_one,one_pow]
  rw [show CubicSieve.cubicRow (1:Ideal O)=(fun _=>1) from funext hrow]
  have he : elementFourier 1 one_ne_zero (fun _=>1) 1=sexticGauss 1 one_ne_zero 1 := by
    unfold elementFourier sexticGauss
    apply tsum_congr
    intro x
    simp only [Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_mul]
  rw [he,sexticGauss_one]

lemma gaussTwo_prime_power_small (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (e : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    gaussTwo (Ideal.span {p^e}) hI=localGamma p hp.ne_zero hg 2^e := by
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero,Ideal.span_singleton_one,←Ideal.one_eq_top] using gaussTwo_one
  · have hi : primaryGenerator (Ideal.span {p})≠0 := by simpa only [pow_one] using hI
    simpa only [pow_one] using gaussTwo_prime_localGamma p hp hg hprimary hi

lemma corrected_prime_cubic_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) :
    localGamma p hp hg 2 * star (angularFactor p) * star (G p) = -(localGamma p hp hg 1)⁻¹ := by
  have hsig := localGamma_one_two_full_signal p hp hg hchar hprimary
  have hn := localGamma_norm_one p hp hg hchar 1 (by decide) (by decide)
  have hne : localGamma p hp hg 1≠0 := by intro h; rw [h,norm_zero] at hn; norm_num at hn
  have hG : G p*star (G p)=1 := by
    rw [mul_comm]
    exact G_conjugate_cancel p (supported_residue_odd p hs)
      (cubicTwo_isUnit_of_odd p (supported_residue_odd p hs))
  apply mul_left_cancel₀ hne
  calc
    _ = (localGamma p hp hg 1*localGamma p hp hg 2)*star (angularFactor p)*star (G p) := by ring
    _ = -1 := by
      rw [hsig]
      calc
        _ = -(angularFactor p*star (angularFactor p))*(G p*star (G p)) := by ring
        _ = _ := by rw [angularFactor_mul_star p hp,hG]; ring
    _ = _ := by rw [mul_neg,mul_inv_cancel₀ hne]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.IdealUnit -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero,?_⟩
  intro P hP
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP

lemma G_one : G (1:O)=1 := by
  have hs : Supported (Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top]
    exact supported_one_ideal
  have ho := supported_residue_odd (1:O) hs
  have hn : G (1:O)≠0 := by
    intro hz
    have hh := G_norm_one_of_odd (1:O) ho
    rw [hz,norm_zero] at hh
    norm_num at hh
  have he := G_mul (1:O) 1 ho ho
  rw [one_mul,reciprocitySign_one_left (1:O) ho,mul_one] at he
  exact mul_left_cancel₀ hn (by simpa only [mul_one] using he.symm)

lemma angularFactor_one : FiniteGaussPhase.angularFactor (1:O)=1 := by
  simp only [FiniteGaussPhase.angularFactor,map_one,norm_one,Complex.ofReal_one,div_one]

@[simp] theorem bareIdealHighCoefficient_one (η : HeckeFamily.Character) :
    bareIdealHighCoefficient η 1 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,one_mul]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_one (η : HeckeFamily.Character) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_one,hw,one_mul]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighValuations -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev HighIdeal := (Id×Id)×(Id×Id)

def highIdeals (v : PrimeIdeal→₀HighValuation) : HighIdeal :=
  ((idealFromValuations (v.mapRange (fun b=>b.1.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.1.2) rfl)),
   (idealFromValuations (v.mapRange (fun b=>b.2.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.2.2) rfl)))

lemma highIdeals_eq_equiv (v : PrimeIdeal→₀HighValuation) :
    highIdeals v =
      (((highValuationEquiv.symm v).1.1.val,(highValuationEquiv.symm v).1.2.val),
       ((highValuationEquiv.symm v).2.1.val,(highValuationEquiv.symm v).2.2.val)) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    apply congrArg idealFromValuations
    ext P
    rfl

lemma highIdeals_injective : Function.Injective highIdeals := by
  intro v w h
  apply highValuationEquiv.symm.injective
  rw [highIdeals_eq_equiv,highIdeals_eq_equiv] at h
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.1.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.1.2) h)
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.2.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.2.2) h)

lemma highIdeals_zero : highIdeals 0=1 := by
  simp only [highIdeals,Finsupp.mapRange_zero,idealFromValuations_zero]
  rfl

lemma highIdeals_single (P : PrimeIdeal) (b : HighValuation) :
    highIdeals (Finsupp.single P b)=((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2)) := by
  simp only [highIdeals,Finsupp.mapRange_single,idealFromValuations_single]

lemma highIdeals_add (v w : PrimeIdeal→₀HighValuation) :
    highIdeals (v+w)=highIdeals v*highIdeals w := by
  have hproj (f : HighValuation→ℕ) (hf0 : f 0=0) (hf : ∀a b,f (a+b)=f a+f b) :
      (v+w).mapRange f hf0=v.mapRange f hf0+w.mapRange f hf0 := by
    ext P
    simp only [Finsupp.mapRange_apply,Finsupp.add_apply,hf]
  simp only [highIdeals,hproj (fun b=>b.1.1) rfl (fun _ _=>rfl),
    hproj (fun b=>b.1.2) rfl (fun _ _=>rfl),hproj (fun b=>b.2.1) rfl (fun _ _=>rfl),
    hproj (fun b=>b.2.2) rfl (fun _ _=>rfl),idealFromValuations_add]
  rfl

lemma prime_coprime_highIdeals (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation)
    (hv : v P=0) : IsCoprime P.val
      ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) := by
  have hc (f : HighValuation→ℕ) (hf0 : f 0=0) :
      IsCoprime P.val (idealFromValuations (v.mapRange f hf0)) := by
    apply prime_coprime_idealFromValuations
    simp only [Finsupp.mapRange_apply,hv,hf0]
  exact ((hc _ rfl).mul_right (hc _ rfl)).mul_right (hc _ rfl) |>.mul_right (hc _ rfl)

def highValuationTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (highIdeals v).1.1 (highIdeals v).1.2
    (highIdeals v).2.1 (highIdeals v).2.2

def highPrimeTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

lemma highPrimeTerm_zero (η : HeckeFamily.Character) (x w z : ℂ) (P : PrimeIdeal) :
    highPrimeTerm η x w z P 0=1 := by
  simp only [highPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one]

theorem highValuationTerm_eq_prod (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) :
    highValuationTerm η x w z v=v.prod (highPrimeTerm η x w z) := by
  induction v using Finsupp.induction with
  | zero =>
    simp only [highValuationTerm,highIdeals_zero,Prod.fst_one,Prod.snd_one,
      bareIdealHighSummand_one,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hv : v P=0 := Finsupp.notMem_support_iff.mp hP
    have hc := prime_coprime_highIdeals P v hv
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (highPrimeTerm_zero η x w z P),←ih]
    unfold highValuationTerm
    rw [highIdeals_add,highIdeals_single]
    exact bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hpow

theorem highValuationTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun v : PrimeIdeal→₀HighValuation=>‖highValuationTerm η x w z v‖) :=
  (bareIdealHighSummand_summable η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SourcePrimeFactor -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareSourceCoefficient_prime_formula (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k j : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^j) =
    (-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
  have ho := supported_residue_odd p hs
  have hself := reciprocitySign_self_eq_sextic_neg_one p hp.ne_zero hg hchar ho
  have hstar : star (actualSextic (Ideal.span {p}) hg (-1))=
      actualSextic (Ideal.span {p}) hg (-1) := by
    rw [←hself,reciprocitySign_star]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_prime_power_small p hp hg hprimary e he hI,
    bareCongruenceCoefficient_all_prime_powers p hp hg,
    angularFactor_pow,map_pow,
    G_completed_prime_power p ho e l he,
    G_cube_eq_normalizedTraceGauss p hp.ne_zero hg hchar ho,
    reciprocitySign_pow_left p _ (odd_residue_pow p ho k),reciprocitySign_pow_right p p ho,
    hself]
  change _ = _
  simp only [star_mul,star_pow,hstar]
  change (targetMonoid η p)^(e+3*l) * star (FiniteGaussPhase.angularFactor p)^(e+3*l) *
    (localGamma p hp.ne_zero hg 2^e *
      ((actualSextic (Ideal.span {p}) hg (-1))^(e*l+l.choose 2) *
        (star (localGamma p hp.ne_zero hg 3)^l * star (G p)^e)) *
      (((actualSextic (Ideal.span {p}) hg (-1))^k)^(e+3*l) *
        sourceScalar p hp hg (e+3*l) k j)) = _
  calc
    _ = (localGamma p hp.ne_zero hg 2 * star (FiniteGaussPhase.angularFactor p) * star (G p))^e *
      (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
        simp only [pow_add,pow_mul,mul_pow]
        ring
    _ = _ := by
      rw [corrected_prime_cubic_signal p hp.ne_zero hg hchar hprimary hs]
      rw [neg_eq_neg_one_mul ((localGamma p hp.ne_zero hg 1)⁻¹),mul_pow]

theorem bareSourceCoefficient_weighted_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^(6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  rw [bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k (6*m) he hI]
  unfold sourcePrincipalTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) (actualSextic_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  calc
    _ = ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
      ((star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
        (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2)) *
      sourceScalar p hp hg (e+3*l) k (6*m) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by ring
    _ = _ := by rw [←hpdiag]; ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.IdealLocalEuler -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

lemma primaryGenerator_prime_power (p : O) (hp : p≠0) (hprimary : goodLambda^2∣p-1) (e : ℕ) :
    primaryGenerator ((Ideal.span {p})^e)=p^e := by
  rw [primaryGenerator_pow,primaryGenerator_span p hp hprimary]

lemma prime_power_small_squarefree (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (e : ℕ) (he : e≤1) :
    Squarefree ((Ideal.span {p})^e) := by
  have hP : Prime (Ideal.span {p}:Ideal O) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero) inferInstance
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero] using (squarefree_one : Squarefree (1:Ideal O))
  · simpa only [pow_one] using hP.squarefree

theorem bareIdealHighCoefficient_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η 1 ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary,one_mul]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

lemma fullIdealWeight_power (s : ℂ) (I : Ideal O) (n : ℕ) :
    fullIdealWeight s (I ^n)=fullIdealWeight s I ^n := (IdealEuler.normWeight s).map_pow I n

lemma prime_spectral_weights (p : O) (hp : p≠0) (e l k m : ℕ) (x w z : ℂ) :
    fullIdealWeight (x+1/2) ((Ideal.span {p})^e) *
      fullIdealWeight (1+3*x) ((Ideal.span {p})^l) *
      fullIdealWeight w ((Ideal.span {p})^k) * fullIdealWeight (6*z) ((Ideal.span {p})^m) =
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by
  have hI : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
  simp only [fullIdealWeight_power]
  simp only [fullIdealWeight,ite_eq_right hI]
  rw [←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,
    ←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ]
  congr 1
  ring

theorem bareIdealHighSummand_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_at_prime η p hp hprimary hs e l k m he]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_weighted_prime η p hp hg hchar hprimary hs e l k m he _ x w z

def idealHighLocalFactor (η : HeckeFamily.Character) (P : Ideal O) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    bareIdealHighSummand η 1 x w z (P^e.val) (P^l) (P^k) (P^m)

theorem idealHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ) :
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z := by
  unfold idealHighLocalFactor sourcePrincipalSeries
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_at_prime η p hp hg hchar hprimary hs e.val l k m (by omega) x w z

theorem idealHighLocalFactor_euler_identity (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      (1-coordD Q (targetMonoid η p) 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q ((actualACube η p)^2) (targetMonoid η p) 1 x w z := by
  rw [idealHighLocalFactor_eq_source η p hp hg hchar hprimary hs]
  exact sourcePrincipalSeries_euler_identity p hp hg hchar _ _ x w z hV hR hW hD

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighEuler -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma bareIdealHighSummand_support (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L : Id) (h : bareIdealHighSummand η u x w z I J K L≠0) :
    highSupport I J K L := by
  by_contra hn
  apply h
  unfold highSupport at hn
  simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right hn,zero_mul]

theorem highValuationTerm_tsum_eq (η : HeckeFamily.Character) (x w z : ℂ) :
    (∑'v : PrimeIdeal→₀HighValuation,highValuationTerm η x w z v)=
      bareIdealHighSeries η 1 x w z := by
  unfold highValuationTerm bareIdealHighSeries
  apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
    bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  intro a ha
  have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
  let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
    ((⟨a.1.1,hs.2.1.1⟩,⟨a.1.2,hs.2.2.1.1⟩),
      (⟨a.2.1,hs.2.2.2.1.1⟩,⟨a.2.2,hs.2.2.2.2.1⟩))
  refine ⟨highValuationEquiv b,?_⟩
  rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]

theorem bareIdealHighSeries_hasProd (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,highPrimeTerm η x w z P b)
      (bareIdealHighSeries η 1 x w z) := by
  have hs := highValuationTerm_summable_norm η x w z hx hw hz
  simp only [highValuationTerm_eq_prod] at hs
  have he := ProbeEulerFinsupp.hasProd_of_summable (highPrimeTerm η x w z)
    (highPrimeTerm_zero η x w z) hs
  simpa only [←highValuationTerm_eq_prod,highValuationTerm_tsum_eq] using he

theorem bareIdealHighSeries_eq_tprod (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    bareIdealHighSeries η 1 x w z =
      ∏' P : PrimeIdeal,∑' b : HighValuation,highPrimeTerm η x w z P b :=
  (bareIdealHighSeries_hasProd η x w z hx hw hz).tprod_eq.symm

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighEulerGeneral -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highArray_val_prod (F : HighIdeal→ℂ) (h1 : F 1=1)
    (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
    (v : PrimeIdeal→₀HighValuation) :
    F (highIdeals v)=v.prod (fun P b=>F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) := by
  have hzero (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    simp only [pow_zero]
    change F (1 : HighIdeal)=1
    exact h1
  induction v using Finsupp.induction with
  | zero => simp only [highIdeals_zero,h1,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hc := prime_coprime_highIdeals P v (Finsupp.notMem_support_iff.mp hP)
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (hzero P),←ih,
      highIdeals_add,highIdeals_single]
    exact hmul _ _ hpow

theorem highArray_hasProd (F : HighIdeal→ℂ) (h1 : F 1=1)
    (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
    (hzero : ∀ a : HighIdeal,F a≠0 → a.1.1≠0 ∧ a.1.2≠0 ∧ a.2.1≠0 ∧ a.2.2≠0)
    (hs : Summable (fun a=>‖F a‖)) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) (∑' a,F a) := by
  have hv := hs.comp_injective highIdeals_injective
  have hp := highArray_val_prod F h1 hmul
  simp only [Function.comp_def,hp] at hv
  have hlocal (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    simp only [pow_zero]
    change F (1 : HighIdeal)=1
    exact h1
  have he := ProbeEulerFinsupp.hasProd_of_summable
    (fun (P : PrimeIdeal) (b : HighValuation)=>F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) hlocal hv
  have hsum : (∑' v : PrimeIdeal→₀HighValuation,F (highIdeals v))=∑' a,F a := by
    apply highIdeals_injective.tsum_eq
    intro a ha
    have hn := hzero a ha
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hn.1⟩,⟨a.1.2,hn.2.1⟩),(⟨a.2.1,hn.2.2.1⟩,⟨a.2.2,hn.2.2.2⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [←hp,hsum] using he

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighEulerLocal -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highPrimeTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖highPrimeTerm η x w z P b‖) := by
  have hs := (highValuationTerm_summable_norm η x w z hx hw hz).comp_injective
    (Finsupp.single_injective P)
  simpa only [Function.comp_def,highValuationTerm_eq_prod,
    Finsupp.prod_single_index (highPrimeTerm_zero η x w z P)] using hs

lemma highPrimeTerm_zero_of_two_le (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤e) :
    highPrimeTerm η x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η 1 x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_isUnit
  omega

theorem highPrimeTerm_tsum_eq_localFactor (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,highPrimeTerm η x w z P b)=
      idealHighLocalFactor η P.val x w z := by
  have hs := (highPrimeTerm_summable_norm η x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, highPrimeTerm η x w z P ((e,l),b))=
        ∑' k,∑' m,highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [highPrimeTerm_zero_of_two_le η x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_hasProd_localFactor (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>idealHighLocalFactor η P.val x w z)
      (bareIdealHighSeries η 1 x w z) := by
  have h := bareIdealHighSeries_hasProd η x w z hx hw hz
  simpa only [highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz] using h

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighEulerRational -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma supported_primeGenerator_prime (P : PrimeIdeal) (hs : Supported P.val) :
    Prime (primaryGenerator P.val) := by
  apply (Ideal.span_singleton_prime (supported_primaryGenerator_ne_zero P.val hs)).mp
  rw [span_primaryGenerator_of_supported P.val hs]
  exact Ideal.isPrime_of_prime P.property

lemma targetMonoid_primaryGenerator (η : HeckeFamily.Character) (I : Ideal O) (hs : Supported I) :
    targetMonoid η (primaryGenerator I)=HeckeFamily.idealCoeff η I := by
  calc
    _ = HeckeFamily.idealCoeff η (Ideal.span {primaryGenerator I}) :=
      (HeckeFamily.idealCoeff_span η (supported_primaryGenerator_ne_zero I hs)).symm
    _ = _ := by rw [span_primaryGenerator_of_supported I hs]

def idealClosedCorrection (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
    (HeckeFamily.idealCoeff η P.val) 1 x w z

theorem idealHighLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z =
      (1-HeckeFamily.idealCoeff η P.val*(Q:ℂ)^(-x)) /
        ((1-(Q:ℂ)^(-6*z))*(1-(Q:ℂ)^(-w))) * idealClosedCorrection η P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1 := by
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hDnorm : ‖coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x‖<1 := by
    apply (coordD_norm_le _ hQ0 _ 1 x (targetMonoid_norm_le_one η p) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0 := by
    intro he
    have hh : coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x=1 := (sub_eq_zero.mp he).symm
    rw [hh,norm_one] at hDnorm
    exact lt_irrefl _ hDnorm
  have he := idealHighLocalFactor_euler_identity η p hp hg.1 hg.2 hprimary hsp x w z hV hR hW hD
  dsimp only at he ⊢
  rw [hspan,actualACube_sq,targetMonoid_primaryGenerator η P.val hs] at he
  simpa only [coordD,coordV,coordW,star_one,mul_one,one_mul,idealClosedCorrection,p] using he

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.GlobalCorrection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def globalPrimeDefectBound (P : PrimeIdeal) : ℝ :=
  240*(Ideal.absNorm P.val:ℝ)^(-(17/10:ℝ))

def globalClosedCorrection (η : HeckeFamily.Character) (S : Finset Id) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},idealClosedCorrection η P.val x w z

lemma globalPrimeDefectBound_nonneg (P : PrimeIdeal) : 0≤globalPrimeDefectBound P := by
  unfold globalPrimeDefectBound
  positivity

lemma globalPrimeDefectBound_summable : Summable globalPrimeDefectBound := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((17/10:ℝ):ℂ) (by norm_num)).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight ((17/10:ℝ):ℂ) P.val‖=globalPrimeDefectBound P
  unfold globalPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

structure CorrectionTail (S : Finset Id) : Prop where
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤Ideal.absNorm P.val
  small : (∑' P : {P : PrimeIdeal // P.val∉S},globalPrimeDefectBound P.val)≤1/6

lemma CorrectionTail.summable {S : Finset Id} (_h : CorrectionTail S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val) :=
  globalPrimeDefectBound_summable.subtype _

lemma CorrectionTail.half {S : Finset Id} (h : CorrectionTail S)
    (P : {P : PrimeIdeal // P.val∉S}) : globalPrimeDefectBound P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>globalPrimeDefectBound_nonneg Q.val)
  linarith [h.small]

lemma idealClosedCorrection_bound (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤globalPrimeDefectBound P := by
  apply unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|7/8<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 7/8≤x.re) (hw : 9/10≤w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

theorem globalClosedCorrection_principal (η : HeckeFamily.Character) (S : Finset Id)
    (hs : ∀P : PrimeIdeal,P.val∉S → CanonicalQuadraticSieve.Supported P.val) (x : ℂ) :
    globalClosedCorrection η S x 1 (1/6)=principalCorrection η S x := by
  apply tprod_congr
  intro P
  unfold idealClosedCorrection principalLocal
  rw [←targetMonoid_primaryGenerator η P.val.val (hs P.val P.property)]
  rfl

theorem exists_uniform_global_cutoff :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N → P.val∈S) → CorrectionTail S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero globalPrimeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>Ideal.absNorm P.val) hm).trans (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  constructor
  · intro P hP
    have hn : ¬Ideal.absNorm P.val≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>globalPrimeDefectBound_nonneg P.val) (fun _=>le_rfl)
      (globalPrimeDefectBound_summable.subtype _) (globalPrimeDefectBound_summable.subtype _)

theorem exists_global_correction (S₀ : Finset Id) :
    ∃S : Finset Id,S₀⊆S ∧ CorrectionTail S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,hcut _ ?_⟩
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighExcludedEuler -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_mul (S : Finset Id) (hS : ∀P∈S,Prime P) (A B : Id) :
    (∀P∈S,¬P∣A*B) ↔ (∀P∈S,¬P∣A) ∧ (∀P∈S,¬P∣B) := by
  constructor
  · intro h
    constructor
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inl hd))
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inr hd))
  · rintro ⟨hA,hB⟩ P hP hd
    exact ((hS P hP).dvd_mul.mp hd).elim (hA P hP) (hB P hP)

lemma outside_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    (∀P∈S,¬P∣A^3) ↔ ∀P∈S,¬P∣A := by
  constructor
  · intro h P hP hd
    exact h P hP (dvd_trans hd (dvd_pow_self A (by decide : (3:ℕ)≠0)))
  · intro h P hP hd
    exact h P hP ((hS P hP).dvd_of_dvd_pow hd)

def highExclusion (S : Finset Id) (hS : ∀P∈S,Prime P) : Id→*ℂ where
  toFun A := if ∀P∈S,¬P∣A then 1 else 0
  map_one' := by
    rw [ite_eq_left]
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  map_mul' A B := by
    simp only [outside_mul S hS A B]
    split_ifs <;> simp_all

lemma highExclusion_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    highExclusion S hS (A^3)=highExclusion S hS A := by
  change (if ∀P∈S,¬P∣A^3 then (1:ℂ) else 0)=_
  simp only [outside_cube S hS]
  rfl

theorem highIdealMask_unmarked (S : Finset Id) (hS : ∀P∈S,Prime P) (I J K L : Id) :
    highIdealMask S 1 I J K L =
      highExclusion S hS I*highExclusion S hS J*highExclusion S hS K*highExclusion S hS L := by
  have he : completedMask S 1 I J=highExclusion S hS (I*J^3) := by
    simp only [completedMask,one_dvd,true_and]
    rfl
  unfold highIdealMask
  rw [he,map_mul,highExclusion_cube]
  rfl

lemma highIdealMask_unmarked_one (S : Finset Id) (hS : ∀P∈S,Prime P) :
    highIdealMask S 1 1 1 1 1=1 := by
  rw [highIdealMask_unmarked S hS]
  simp only [map_one,one_mul]

lemma highIdealMask_unmarked_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (a b : HighIdeal) :
    highIdealMask S 1 (a.1.1*b.1.1) (a.1.2*b.1.2) (a.2.1*b.2.1) (a.2.2*b.2.2)=
      highIdealMask S 1 a.1.1 a.1.2 a.2.1 a.2.2 * highIdealMask S 1 b.1.1 b.1.2 b.2.1 b.2.2 := by
  simp only [highIdealMask_unmarked S hS,map_mul]
  ring

theorem excludedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η 1 x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighExcludedLocal -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highExclusion_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    highExclusion S hS P.val=if P.val∈S then 0 else 1 := by
  change (if ∀Q∈S,¬Q∣P.val then (1:ℂ) else 0)=_
  by_cases hP : P.val∈S
  · rw [ite_eq_right (fun h=>h P.val hP (dvd_refl _)),ite_eq_left hP]
  · have houtside : ∀Q∈S,¬Q∣P.val := by
      intro Q hQ hd
      have hn : (⟨Q,hS Q hQ⟩ : PrimeIdeal)≠P := by
        intro hh
        exact hP ((congrArg Subtype.val hh) ▸ hQ)
      exact (hS Q hQ).not_isUnit ((primeIdeal_coprime ⟨Q,hS Q hQ⟩ P hn).isUnit_of_dvd hd)
    rw [ite_eq_left houtside,ite_eq_right hP]

lemma highIdealMask_prime_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∉S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=1 := by
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,
    ite_eq_right hP,one_pow,one_mul]

lemma highIdealMask_prime_inside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∈S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=
      if b=0 then 1 else 0 := by
  rcases b with ⟨⟨e,l⟩,k,m⟩
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,ite_eq_left hP]
  by_cases he : e=0 <;> by_cases hl : l=0 <;> by_cases hk : k=0 <;> by_cases hm : m=0 <;>
    simp [he,hl,hk,hm,Prod.mk_eq_zero]

theorem excludedHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η 1 x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealHighLocalFactor η P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η 1 x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one,mul_one]
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

theorem excludedIdealHighSeries_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (markedIdealHighSeries S 1 η 1 x w z) := by
  have h := excludedIdealHighSeries_hasProd S hS η x w z hx hw hz
  simp only [excludedHighLocalFactor S hS η x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealHighLocalFactor η P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsMultiplicative -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem bareSourceCoefficient_product_row_frequency (η : HeckeFamily.Character) (u : O) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryGenerator J*m^3)*r)) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) (u*(a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (u*a^6) * bareSourceCoefficient η J hJ.2 B r hB (u*b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop (u*(a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (u*a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (u*b^6) hab
  rw [show b^6*(u*a^6)=u*(a*b)^6 by ring] at hi
  rw [show a^6*(u*b^6)=u*(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

theorem bareIdealHighCoefficient_row_mul (η : HeckeFamily.Character) (u : O)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η u (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η u I J K L * bareIdealHighCoefficient η u I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryGenerator_mul,primaryGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_row_frequency η u I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul]
    dsimp only at he
    convert he using 1 ; ring_nf
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dite_eq_right hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=>h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dite_eq_right hj,mul_zero]
    · unfold highSupport at hi
      rw [dite_eq_right hi,zero_mul]

theorem bareIdealHighSummand_row_mul (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η u x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η u x w z I J K L * bareIdealHighSummand η u x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_mul η u I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsEuler -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

@[simp] theorem bareIdealHighCoefficient_row_one (η : HeckeFamily.Character) (u : O) :
    bareIdealHighCoefficient η u 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,mul_one]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_row_one (η : HeckeFamily.Character) (u : O) (x w z : ℂ) :
    bareIdealHighSummand η u x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_row_one,hw,one_mul]

theorem bareIdealHighSeries_row_hasProd (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (bareIdealHighSeries η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · exact bareIdealHighSummand_row_one η u x w z
  · intro a b hc
    exact bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc
  · intro a ha
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (bareIdealHighSummand_summable η u x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI

end

