module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part001
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.Canonical
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Mathlib.Analysis.Normed.Ring.Finite

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.GramLocalExtension -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge CenteredMomentCorrelation CenteredMomentCanonical
local notation "O" => ActualEisensteinCubic.O

lemma finiteField_local_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (u v k : F) (huv : u≠0 ∨ v≠0) :
    ‖localCorrelation χ u v k‖≤(Fintype.card F:ℝ) := by
  rcases huv with hu|hv
  · exact fullCorrelation_bezout_norm u v u⁻¹ 0 k (by simp [hu]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)
  · exact fullCorrelation_bezout_norm u v 0 v⁻¹ k (by simp [hv]) χ χ
      (FiniteRayExpansion.norm_char_le_one χ) (FiniteRayExpansion.norm_char_le_one χ)

def localExtension (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ k : O) : ℂ := by
  letI : Fintype (O⧸P) := Fintype.ofFinite _
  letI : Field (O⧸P) := Ideal.Quotient.field P
  exact if n₁∈P ∧ n₂∈P then 0 else (Ideal.absNorm P:ℂ)^(c-1)*
    localCorrelation (actualSextic P hg^c) (Ideal.Quotient.mk P n₁)
      (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k)

lemma localExtension_both_zero (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ k : O) (h₁ : n₁∈P) (h₂ : n₂∈P) :
    localExtension P hg c n₁ n₂ k=0 := by simp [localExtension,h₁,h₂]

theorem localExtension_periodic (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (n₁ n₂ m₁ m₂ k l : O)
    (h₁ : n₁-m₁∈P) (h₂ : n₂-m₂∈P) (hk : k-l∈P) :
    localExtension P hg c n₁ n₂ k=localExtension P hg c m₁ m₂ l := by
  have he₁ := Ideal.Quotient.eq.mpr h₁
  have he₂ := Ideal.Quotient.eq.mpr h₂
  have hek := Ideal.Quotient.eq.mpr hk
  have hm₁ : n₁∈P↔m₁∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₁,Ideal.Quotient.eq_zero_iff_mem]
  have hm₂ : n₂∈P↔m₂∈P := by
    rw [←Ideal.Quotient.eq_zero_iff_mem,he₂,Ideal.Quotient.eq_zero_iff_mem]
  simp only [localExtension,hm₁,hm₂,he₁,he₂,hek]

theorem localExtension_norm (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (hc : 1≤ c) (n₁ n₂ k : O) :
    ‖localExtension P hg c n₁ n₂ k‖≤(Ideal.absNorm P:ℝ)^c := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  unfold localExtension
  split_ifs with hn
  · simp only [norm_zero]
    positivity
  have huv : Ideal.Quotient.mk P n₁≠0 ∨ Ideal.Quotient.mk P n₂≠0 := by
    by_contra hh
    push Not at hh
    exact hn ⟨Ideal.Quotient.eq_zero_iff_mem.mp hh.1,Ideal.Quotient.eq_zero_iff_mem.mp hh.2⟩
  have hh := finiteField_local_norm (actualSextic P hg^c) (Ideal.Quotient.mk P n₁)
    (Ideal.Quotient.mk P n₂) (Ideal.Quotient.mk P k) huv
  rw [norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm P:ℝ)^(c-1)*(Ideal.absNorm P:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hh
    _ = _ := by rw [←pow_succ,Nat.sub_add_cancel hc]

theorem primePower_common_extension (P : Ideal O) [P.IsMaximal] (hg : goodLambda∉P)
    (c : ℕ) (hc : 1≤ c) [Fintype (O⧸P^c)] (n₁ n₂ k : O)
    (hn : n₁∉P ∨ n₂∉P) :
    fullCorrelation (fun x : O⧸P^c=>Ideal.Quotient.mk _ n₂*x)
      (fun y : O⧸P^c=>Ideal.Quotient.mk _ n₁*y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) (Ideal.Quotient.mk _ k)=
      localExtension P hg c n₁ n₂ k := by
  let : Fintype (O⧸P) := Fintype.ofFinite _
  let : Field (O⧸P) := Ideal.Quotient.field P
  have hn' : ¬(n₁∈P ∧ n₂∈P) := by tauto
  rw [localExtension,ite_eq_right hn']
  rcases hn with h₁|h₂
  · have hu : IsUnit (Ideal.Quotient.mk (P^c) n₁) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=>h₁ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨u,hu⟩ := hu
    rw [←hu]
    unfold primePowerRow
    rw [primePower_localCorrelation]
    simp only [primePowerReduction,Ideal.Quotient.factor_mk,hu]
  · have hv : IsUnit (Ideal.Quotient.mk (P^c) n₂) :=
      (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
        (isUnit_iff_ne_zero.mpr (fun hz=>h₂ (Ideal.Quotient.eq_zero_iff_mem.mp hz)))
    obtain ⟨v,hv⟩ := hv
    rw [←hv]
    unfold primePowerRow
    rw [fullCorrelation_reduction_unit_left _ (primePowerReduction_surjective P hc),
      primePowerReduction_multiplicity,Nat.cast_pow]
    change (Ideal.absNorm P:ℂ)^(c-1)*localCorrelation (actualSextic P hg^c)
      (primePowerReduction P hc (Ideal.Quotient.mk _ n₁)) (primePowerReduction P hc v)
      (primePowerReduction P hc (Ideal.Quotient.mk _ k))=_
    simp only [hv,primePowerReduction,Ideal.Quotient.factor_mk]

end SevenEighths.ProbeGramCommon
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.Sextic -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_pow_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (n : ℕ) :
    actualSextic P hg ^ n = 1 ↔ 6 ∣ n := by
  rw [← orderOf_dvd_iff_pow_eq_one, CenteredMomentCanonical.actualSextic_order_six P hg hc]

theorem actualSextic_primePowerGauss_at_pow (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r n j : ℕ) :
    primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) n (p ^ j) =
      if 6 ∣ r then
        (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
        (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0)
      else if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) 1 else 0 := by
  by_cases hr : 6 ∣ r
  · rw [ite_eq_left hr, (actualSextic_pow_eq_one_iff _ hg hc r).mpr hr]
    apply primePowerGauss_at_pow_principal p hp
    have hprim : (quotientTrace p hp.ne_zero).IsPrimitive :=
      GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero
    simpa using hprim (a := 1) one_ne_zero
  · rw [ite_eq_right hr]
    exact primePowerGauss_at_pow_nonprincipal p hp _
      (fun h => hr ((actualSextic_pow_eq_one_iff _ hg hc r).mp h)) n j

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CongruenceScalar -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

def exactQuotient (a b : O) (h : b ∣ a) : O := Classical.choose h

lemma exactQuotient_spec (a b : O) (h : b ∣ a) : a = b * exactQuotient a b h :=
  Classical.choose_spec h

lemma exactQuotient_eq (a b c : O) (h : b ∣ a) (hb : b ≠ 0) (he : a = b*c) :
    exactQuotient a b h = c := by
  apply mul_left_cancel₀ hb
  exact (exactQuotient_spec a b h).symm.trans he

def positiveScalar (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) : ℂ :=
  if k = 0 then primePowerGauss p hp (χ^(n+1)) n (p^j)
  else ∑' d : O ⧸ Ideal.span {p^k},
    if h : p^k ∣ p^j-p^(n+1)*representative (p^k) d then
      (χ^k) (Ideal.Quotient.mk (Ideal.span {p}) (representative (p^k) d)) *
        primePowerGauss p hp (χ^(n+1)) n
          (exactQuotient (p^j-p^(n+1)*representative (p^k) d) (p^k) h)
    else 0

@[simp] theorem positiveScalar_kzero (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 0 j = primePowerGauss p hp (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, ite_true]

theorem positiveScalar_kone_jzero (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) :
    positiveScalar p hp.ne_zero χ n 1 0 = 0 := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false]
  rw [pow_one]
  simp only [pow_zero, pow_one]
  refine (tsum_congr (g := fun _ => (0:ℂ)) ?_).trans tsum_zero
  intro d
  rw [dite_eq_right]
  intro hd
  have hd2 : p ∣ p^(n+1)*representative p d :=
    (dvd_pow_self p (by omega : n+1 ≠ 0)).mul_right _
  have hunit : p ∣ (1:O) := by
    have := dvd_add hd hd2
    simpa only [sub_add_cancel] using this
  exact hp.not_isUnit (isUnit_iff_dvd_one.mpr hunit)

theorem positiveScalar_kone_convolution (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) = scalarKOne p hp χ (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false, scalarKOne]
  rw [pow_one]
  simp only [pow_one]
  apply tsum_congr
  intro d
  have he : p^(j+1)-p^(n+1)*representative p d = p*(p^j-p^n*representative p d) := by
    simp only [pow_succ]
    ring
  have hd : p ∣ p^(j+1)-p^(n+1)*representative p d := ⟨_,he⟩
  rw [dite_eq_left hd, exactQuotient_eq _ _ _ hd hp he, representative_spec]

theorem positiveScalar_kone (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (χ^n) n (p^j) := by
  rw [positiveScalar_kone_convolution, scalarKOne_eq]
  have he : χ^(n+1)*χ⁻¹ = χ^n := by rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  rw [he]

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LiftedFourier -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_lift_add (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    primePowerGauss p hp.ne_zero χ (n+k) (p^k*h) =
      (Ideal.absNorm (Ideal.span {p}):ℂ)^k * primePowerGauss p hp.ne_zero χ n h := by
  by_cases hd : p^n ∣ h
  · obtain ⟨a, rfl⟩ := hd
    have he : p^k*(p^n*a) = p^(n+k)*a := by rw [pow_add]; ring
    rw [he, primePowerGauss_lift, primePowerGauss_lift, pow_add]
    ring
  · have hbig : ¬p^(n+k) ∣ p^k*h := by
      rw [pow_add, mul_comm (p^n) (p^k), mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
      exact hd
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hbig,
      primePowerGauss_zero_off_support _ _ _ _ _ hd, mul_zero]

theorem primePowerGauss_add_period (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h a : O) :
    primePowerGauss p hp χ n (h+p^(n+1)*a) = primePowerGauss p hp χ n h := by
  unfold primePowerGauss conductorFourier
  apply tsum_congr
  intro x
  have hz : Ideal.Quotient.mk (Ideal.span {p*p^n}) (p^(n+1)*a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    rw [pow_succ']
  simp only [map_add, hz, add_zero]

theorem gauss_exactQuotient_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    (if hd : p^k ∣ h then primePowerGauss p hp.ne_zero χ n (exactQuotient h (p^k) hd) else 0) =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ * primePowerGauss p hp.ne_zero χ (n+k) h := by
  have hq : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  by_cases hd : p^k ∣ h
  · rw [dite_eq_left hd]
    conv_rhs => rw [exactQuotient_spec h (p^k) hd]
    rw [primePowerGauss_lift_add p hp, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  · rw [dite_eq_right hd]
    have hnd : ¬p^(n+k) ∣ h := by
      intro he
      exact hd ((show p^k ∣ p^(n+k) from ⟨p^n, by rw [pow_add]; ring⟩).trans he)
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hnd, mul_zero]

theorem positiveScalar_full_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) (hk : k ≠ 0) :
    positiveScalar p hp.ne_zero χ n k j =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ *
        ∑' d : O ⧸ Ideal.span {p^k},
          (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) *
            primePowerGauss p hp.ne_zero (χ^(n+1)) (n+k)
              (p^j-p^(n+1)*representative (p^k) d) := by
  rw [positiveScalar, ite_eq_right hk, ← tsum_mul_left]
  apply tsum_congr
  intro d
  have he := gauss_exactQuotient_lift p hp (χ^(n+1)) n k
    (p^j-p^(n+1)*representative (p^k) d)
  by_cases hd : p^k ∣ p^j-p^(n+1)*representative (p^k) d
  · rw [dite_eq_left hd] at he ⊢
    rw [he]
    ring
  · rw [dite_eq_right hd] at he ⊢
    linear_combination (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) * he

lemma quotientTrace_split_frequency (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (H d v : O) :
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ ((H-b*d)*v)) =
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (H*v)) *
        quotientTrace a ha (Ideal.Quotient.mk _ ((-v)*d)) := by
  have hs := quotientTrace_conductor_scale a b ((-v)*d) ha hb 1
  simp only [mul_one, map_one] at hs
  rw [show (H-b*d)*v = H*v+b*((-v)*d) by ring, map_add, AddChar.map_add_eq_mul, hs]

def quotientFourier (p c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {c}, χ (Ideal.Quotient.mk _ (representative c d)) *
    quotientTrace c hc (Ideal.Quotient.mk _ (H*representative c d))

lemma quotientFourier_congr (p a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H : O) (he : a=b) :
    quotientFourier p a ha χ H = quotientFourier p b hb χ H := by
  subst b
  rfl

lemma primePowerGauss_eq_quotientFourier (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (H : O) :
    primePowerGauss p hp χ n H =
      quotientFourier p (p*p^n) (mul_ne_zero hp (pow_ne_zero _ hp)) χ H := by
  unfold primePowerGauss conductorFourier quotientFourier
  apply tsum_congr
  intro d
  have hr : conductorReduction p (p^n) d =
      Ideal.Quotient.mk (Ideal.span {p}) (representative (p*p^n) d) := by
    conv_lhs => rw [← representative_spec (p*p^n) d]
    rfl
  have hm : Ideal.Quotient.mk (Ideal.span {p*p^n}) (H*representative (p*p^n) d) =
      Ideal.Quotient.mk _ H*d := by rw [map_mul, representative_spec]
  rw [hr, hm]

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PrimePhase -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge QuadraticGaussRay FiniteGaussPhase CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem normalizedTraceGauss_eq_normalizedGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) :
    letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
    letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
    ConcreteBreveE.normalizedTraceGauss p hp χ =
      ProbeGauss.normalizedGauss χ (quotientTrace p hp) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn : Real.sqrt (Nat.card (O ⧸ Ideal.span {p}) : ℝ) = ‖eisEmbedding p‖ := by
    change Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) = _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]
  simp only [ConcreteBreveE.normalizedTraceGauss, ProbeGauss.normalizedGauss,
    quotientTrace, ← Nat.card_eq_fintype_card, hn]

theorem quadraticRayValue_eq_normalizedTraceGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    quadraticRayValue (residue p) =
      ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) := by
  let pp : Unit → O := fun _ => p
  have hpp : ∀ i, pp i ≠ 0 := fun _ => hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductGauss_three_eq_rayValue pp hpp hcop (fun _ => hg) (fun _ => hc)
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 3)] at he
  simpa [pp] using he.symm

theorem G_cube_eq_normalizedTraceGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ho : EisensteinEPrimaryPhase.odd (residue p)) :
    G (p ^ 3) =
      ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) := by
  rw [G_cube p ho (cubicTwo_isUnit_of_odd p ho)]
  exact quadraticRayValue_eq_normalizedTraceGauss p hp hg hc

theorem normalizedTraceGauss_three_sq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) ^ 2 =
      actualSextic (Ideal.span {p}) hg (-1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let χ := actualSextic (Ideal.span {p}) hg
  have h6 : χ ^ 6 = 1 := (ProbePrimePower.actualSextic_pow_eq_one_iff _ hg hc 6).mpr (by decide)
  have h3 : χ ^ 3 ≠ 1 := fun h => (by decide : ¬6 ∣ 3)
    ((ProbePrimePower.actualSextic_pow_eq_one_iff _ hg hc 3).mp h)
  have hi : (χ ^ 3)⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    exact h6
  have hψ : (quotientTrace p hp).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
  have he := ProbeGauss.normalizedGauss_inverse_pair (χ ^ 3) (quotientTrace p hp) h3 hψ
  rw [hi, ← pow_two] at he
  rw [normalizedTraceGauss_eq_normalizedGauss]
  rw [he]
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), ← map_pow]
  norm_num
  rfl

theorem reciprocitySign_self_eq_sextic_neg_one (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ho : EisensteinEPrimaryPhase.odd (residue p)) :
    reciprocitySign p p = actualSextic (Ideal.span {p}) hg (-1) := by
  have hq := QuadraticAllOddCRT.quadraticRayValue_mul (residue p) (residue p) ho ho
  rw [quadraticRayValue_square _ ho] at hq
  have hprod : reciprocitySign p p * quadraticRayValue (residue p) ^ 2 = 1 := by
    simpa only [reciprocitySign, pow_two, mul_assoc] using hq.symm
  have he := normalizedTraceGauss_three_sq p hp hg hc
  rw [← quadraticRayValue_eq_normalizedTraceGauss p hp hg hc] at he
  rw [he] at hprod
  calc
    reciprocitySign p p = reciprocitySign p p * 1 := (mul_one _).symm
    _ = reciprocitySign p p * (reciprocitySign p p * actualSextic (Ideal.span {p}) hg (-1)) := by rw [hprod]
    _ = reciprocitySign p p ^ 2 * actualSextic (Ideal.span {p}) hg (-1) := by ring
    _ = _ := by rw [reciprocitySign_sq p p ho ho, one_mul]

end SevenEighths.ProbePhase
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhasePowers -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

lemma residue_one_mod_four : residue (1 : O) = (1, 0) := by
  have he : (1 : O) = eval 1 0 := by simp [eval]
  rw [he, residue_eval]
  norm_num

lemma odd_residue_one : EisensteinEPrimaryPhase.odd (residue (1 : O)) := by
  rw [residue_one_mod_four]
  decide

lemma odd_residue_pow (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    EisensteinEPrimaryPhase.odd (residue (a ^ n)) := by
  induction n with
  | zero => simpa only [pow_zero] using odd_residue_one
  | succ n ih =>
    rw [pow_succ, residue_mul]
    exact odd_mul _ _ ih ha

lemma reciprocitySign_symm (a b : O) : reciprocitySign a b = reciprocitySign b a := by
  simp only [reciprocitySign, quadraticRaySign_symm]

lemma reciprocitySign_one_left (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    reciprocitySign 1 a = 1 := by
  have ht : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRaySign (1, 0) r = 1 := by decide
  unfold reciprocitySign
  rw [residue_one_mod_four]
  exact_mod_cast ht (residue a) ha

lemma reciprocitySign_mul_left (a b c : O) :
    reciprocitySign (a * b) c = reciprocitySign a c * reciprocitySign b c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_left, Int.cast_mul]

lemma reciprocitySign_pow_left (a b : O)
    (hb : EisensteinEPrimaryPhase.odd (residue b)) (n : ℕ) :
    reciprocitySign (a ^ n) b = reciprocitySign a b ^ n := by
  induction n with
  | zero => simp only [pow_zero, reciprocitySign_one_left b hb]
  | succ n ih => rw [pow_succ, reciprocitySign_mul_left, ih, pow_succ]

lemma reciprocitySign_pow_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    reciprocitySign a (b ^ n) = reciprocitySign a b ^ n := by
  rw [reciprocitySign_symm, reciprocitySign_pow_left b a ha n, reciprocitySign_symm b a]

lemma G_one : G (1 : O) = 1 := by
  have hq : quadraticRayValue (residue (1 : O)) = 1 := by
    rw [residue_one_mod_four]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num
  have he := G_cube (1 : O) odd_residue_one (cubicTwo_isUnit_of_odd 1 odd_residue_one)
  simpa only [one_pow, hq] using he

theorem G_pow (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (n : ℕ) :
    G (a ^ n) = G a ^ n * reciprocitySign a a ^ (n.choose 2) := by
  induction n with
  | zero => simp [G_one]
  | succ n ih =>
    rw [pow_succ, G_mul (a ^ n) a (odd_residue_pow a ha n) ha, ih,
      reciprocitySign_pow_left a a ha n, Nat.choose_succ_succ, Nat.choose_one_right,
      pow_add, pow_succ]
    ring

theorem reciprocitySign_cube_self (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    reciprocitySign (a ^ 3) (a ^ 3) = reciprocitySign a a := by
  rw [reciprocitySign_cube_right (a ^ 3) a (odd_residue_pow a ha 3) ha,
    reciprocitySign_symm, reciprocitySign_cube_right a a ha ha]

theorem G_cube_power (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a)) (l : ℕ) :
    G (a ^ (3 * l)) = G (a ^ 3) ^ l * reciprocitySign a a ^ (l.choose 2) := by
  rw [pow_mul, G_pow (a ^ 3) (odd_residue_pow a ha 3), reciprocitySign_cube_self a ha]

theorem G_completed_prime_power (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (e l : ℕ) (he : e ≤ 1) :
    G (a ^ (e + 3 * l)) =
      G a ^ e * G (a ^ 3) ^ l * reciprocitySign a a ^ (e * l + l.choose 2) := by
  have hc : e = 0 ∨ e = 1 := by omega
  rcases hc with rfl | rfl
  · simpa only [zero_add, zero_mul, pow_zero, one_mul] using G_cube_power a ha l
  · rw [pow_add, pow_one, G_mul a (a ^ (3 * l)) ha (odd_residue_pow a ha _),
      G_cube_power a ha l, pow_mul, reciprocitySign_pow_right a (a ^ 3) ha l,
      reciprocitySign_cube_right a a ha ha]
    simp only [pow_one, one_mul, pow_add]
    ring

end SevenEighths.ProbePhase
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PairPhase -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def sexticPair (p q : O) : ℂ :=
  idealRowHom q (Ideal.span {p}) * idealRowHom p (Ideal.span {q})

theorem sexticPair_cube (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda ^ 2 ∣ p - 1) (hprimaryQ : goodLambda ^ 2 ∣ q - 1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q})) :
    sexticPair p q ^ 3 = reciprocitySign p q := by
  have hr : idealRowHom q (Ideal.span {p}) =
      reciprocitySign p q * idealRowHom p (Ideal.span {q}) :=
    idealRowHom_prime_reciprocity p q hp hq hprimaryP hprimaryQ hsP hsQ
  have h6 := idealRowHom_sixth_mask p (Ideal.span {q}) hsQ
  rw [idealRowHom_argument_pow _ _ _ hsQ, ite_eq_left hcop.symm] at h6
  have h2 := reciprocitySign_sq p q (supported_residue_odd p hsP) (supported_residue_odd q hsQ)
  calc
    sexticPair p q ^ 3 = reciprocitySign p q ^ 3 * idealRowHom p (Ideal.span {q}) ^ 6 := by
      unfold sexticPair
      rw [hr]
      ring
    _ = reciprocitySign p q := by rw [h6, mul_one, pow_succ, h2, one_mul]

theorem completed_pair_phase (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda ^ 2 ∣ p - 1) (hprimaryQ : goodLambda ^ 2 ∣ q - 1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q})) (e f l k : ℕ) :
    sexticPair p q ^ ((e + 3 * l) * (f + 3 * k)) / sexticPair p q ^ (e * f) =
      reciprocitySign p q ^ (e * k + f * l + l * k) := by
  have h3 := sexticPair_cube p q hp hq hprimaryP hprimaryQ hsP hsQ hcop
  have h2 := reciprocitySign_sq p q (supported_residue_odd p hsP) (supported_residue_odd q hsQ)
  have hr : reciprocitySign p q ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at h2; norm_num at h2
  have hz : sexticPair p q ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at h3; exact hr h3.symm
  have hexp : (e + 3 * l) * (f + 3 * k) = e * f + 3 * (e * k + f * l + 3 * l * k) := by ring
  rw [hexp, pow_add, pow_mul (sexticPair p q) 3 (e * k + f * l + 3 * l * k),
    h3, mul_div_cancel_left₀ _ (pow_ne_zero _ hz)]
  have htail : e * k + f * l + 3 * l * k = (e * k + f * l + l * k) + 2 * (l * k) := by ring
  rw [htail, pow_add, pow_mul (reciprocitySign p q) 2 (l * k), h2, one_pow, mul_one]

end SevenEighths.ProbePhase
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CompletedCRTPhase -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CubicEisenstein
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma reciprocitySign_star (a b : O) : star (reciprocitySign a b)=reciprocitySign a b := by
  simp only [reciprocitySign, star_intCast]

theorem completed_cubic_pair_cancel (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : goodLambda^2∣p-1) (hprimaryQ : goodLambda^2∣q-1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q}))
    (e f l k : ℕ) :
    sexticPair p q ^ ((e+3*l)*(f+3*k)) * sexticPair p q ^ (2*e*f) *
      star (reciprocitySign (p^(e+3*l)) (q^(f+3*k))) = 1 := by
  have hpodd := supported_residue_odd p hsP
  have hqodd := supported_residue_odd q hsQ
  have h3 := sexticPair_cube p q hp hq hprimaryP hprimaryQ hsP hsQ hcop
  have h2 := reciprocitySign_sq p q hpodd hqodd
  rw [reciprocitySign_star, reciprocitySign_pow_left p _ (odd_residue_pow q hqodd _) _,
    reciprocitySign_pow_right p q hpodd, ← pow_mul, ← pow_add]
  have hexp : (e+3*l)*(f+3*k)+2*e*f = 3*(e*f+e*k+f*l+3*l*k) := by ring
  rw [hexp, pow_mul, h3, ← pow_add]
  have hsum : e*f+e*k+f*l+3*l*k+(f+3*k)*(e+3*l) =
      2*(e*f+2*e*k+2*f*l+6*l*k) := by ring
  rw [hsum, pow_mul, h2, one_pow]

lemma sexticPair_mul_left (a b c : O) :
    sexticPair (a*b) c = sexticPair a c * sexticPair b c := by
  simp only [sexticPair, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    idealRowHom_argument_mul]
  ring

lemma sexticPair_mul_right (a b c : O) :
    sexticPair a (b*c) = sexticPair a b * sexticPair a c := by
  simp only [sexticPair, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    idealRowHom_argument_mul]
  ring

lemma sexticPair_cube_left (a b : O) : sexticPair (a^3) b=sexticPair a b^3 := by
  rw [show a^3=a*a*a by ring, sexticPair_mul_left, sexticPair_mul_left]
  ring

lemma sexticPair_cube_right (a b : O) : sexticPair a (b^3)=sexticPair a b^3 := by
  rw [show b^3=b*b*b by ring, sexticPair_mul_right, sexticPair_mul_right]
  ring

theorem sexticPair_cube_supported (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : goodLambda^2∣a-1) (hpb : goodLambda^2∣b-1) (hcop : IsCoprime a b) :
    sexticPair a b^3 = reciprocitySign a b := by
  have hr : idealRowHom b (Ideal.span {a}) =
      reciprocitySign a b * idealRowHom a (Ideal.span {b}) :=
    idealRowHom_primary_reciprocity a b hpa hpb ha hb
  have hc : IsCoprime (Ideal.span {b}:Ideal O) (Ideal.span {a}) := by
    exact (Ideal.isCoprime_span_singleton_iff b a).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask a (Ideal.span {b}) hb
  rw [idealRowHom_argument_pow _ _ _ hb, ite_eq_left hc] at h6
  have h2 := reciprocitySign_sq a b (supported_residue_odd a ha) (supported_residue_odd b hb)
  calc
    _ = reciprocitySign a b^3 * idealRowHom a (Ideal.span {b})^6 := by
      unfold sexticPair
      rw [hr]
      ring
    _ = _ := by rw [h6,mul_one,pow_succ,h2,one_mul]

theorem completed_cubic_cross_cancel (c n d m : O)
    (hc : Supported (Ideal.span {c})) (hn : Supported (Ideal.span {n}))
    (hd : Supported (Ideal.span {d})) (hm : Supported (Ideal.span {m}))
    (hpc : goodLambda^2∣c-1) (hpn : goodLambda^2∣n-1)
    (hpd : goodLambda^2∣d-1) (hpm : goodLambda^2∣m-1)
    (hcd : IsCoprime c d) (hcm : IsCoprime c m)
    (hnd : IsCoprime n d) (hnm : IsCoprime n m) :
    sexticPair (c*n^3) (d*m^3) * sexticPair c d^2 *
      star (reciprocitySign (c*n^3) (d*m^3)) = 1 := by
  have hcd3 := sexticPair_cube_supported c d hc hd hpc hpd hcd
  have hcm3 := sexticPair_cube_supported c m hc hm hpc hpm hcm
  have hnd3 := sexticPair_cube_supported n d hn hd hpn hpd hnd
  have hnm3 := sexticPair_cube_supported n m hn hm hpn hpm hnm
  have hRnm := reciprocitySign_sq n m (supported_residue_odd n hn) (supported_residue_odd m hm)
  have he : sexticPair (c*n^3) (d*m^3)*sexticPair c d^2 =
      reciprocitySign (c*n^3) (d*m^3) := by
    calc
      _ = sexticPair c d^3 * sexticPair c m^3 * sexticPair n d^3 *
          (sexticPair n m^3)^3 := by
        rw [sexticPair_mul_left, sexticPair_mul_right, sexticPair_mul_right,
          sexticPair_cube_left, sexticPair_cube_left, sexticPair_cube_right,
          sexticPair_cube_right]
        ring
      _ = reciprocitySign c d * reciprocitySign c m * reciprocitySign n d * reciprocitySign n m := by
        rw [hcd3,hcm3,hnd3,hnm3,pow_succ,hRnm,one_mul]
      _ = _ := by
        rw [reciprocitySign_mul_left, reciprocitySign_mul_right, reciprocitySign_mul_right,
          reciprocitySign_cube_right c m (supported_residue_odd c hc) (supported_residue_odd m hm),
          reciprocitySign_symm (n^3) d,
          reciprocitySign_cube_right d n (supported_residue_odd d hd) (supported_residue_odd n hn),
          reciprocitySign_symm d n,
          reciprocitySign_cube_right (n^3) m (odd_residue_pow n (supported_residue_odd n hn) 3)
            (supported_residue_odd m hm), reciprocitySign_symm (n^3) m,
          reciprocitySign_cube_right m n (supported_residue_odd m hm) (supported_residue_odd n hn),
          reciprocitySign_symm m n]
        ring
  rw [he,reciprocitySign_star,←pow_two]
  exact reciprocitySign_sq _ _
    (by simpa only [ActualEisensteinCoordinates.residue_mul] using
      (EisensteinEPrimaryPhase.odd_mul _ _ (supported_residue_odd c hc)
        (odd_residue_pow n (supported_residue_odd n hn) 3)))
    (by simpa only [ActualEisensteinCoordinates.residue_mul] using
      (EisensteinEPrimaryPhase.odd_mul _ _ (supported_residue_odd d hd)
        (odd_residue_pow m (supported_residue_odd m hm) 3)))

end SevenEighths.ProbePhase
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PrimeConstants -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def localGamma (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (r : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ r)

lemma localGamma_norm_one (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) : ‖localGamma p hp hg r‖ = 1 :=
  MixedGaussConversion.norm_localGauss p hp hg hc r hr hr6

lemma actualSextic_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) : actualSextic P hg ^ 6 = 1 :=
  (actualSextic_pow_eq_one_iff P hg hc 6).mpr (by decide)

lemma actualSextic_neg_one_sq (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) : actualSextic P hg (-1)^2 = 1 := by
  rw [← map_pow]
  norm_num

theorem localGamma_inverse_pair (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) :
    localGamma p hp hg r * localGamma p hp hg (6-r) =
      actualSextic (Ideal.span {p}) hg (-1)^r := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let χ := actualSextic (Ideal.span {p}) hg
  have hχ : χ^r ≠ 1 := by
    intro he
    have hd := (actualSextic_pow_eq_one_iff _ hg hc r).mp he
    exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hr) hr6) hd
  have hinv : (χ^r)⁻¹ = χ^(6-r) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.add_sub_of_le hr6.le]
    exact actualSextic_six _ hg hc
  have hψ : (quotientTrace p hp).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
  have he := ProbeGauss.normalizedGauss_inverse_pair (χ^r) (quotientTrace p hp) hχ hψ
  rw [hinv] at he
  simp only [localGamma, ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simpa only [MulChar.pow_apply' _ hr] using he

lemma localGamma_two_four (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    localGamma p hp hg 2 * localGamma p hp hg 4 = 1 := by
  have he := localGamma_inverse_pair p hp hg hc 2 (by decide) (by decide)
  simpa only [show 6-2=4 from rfl, actualSextic_neg_one_sq] using he

theorem localGamma_one_two_signal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hprimary : goodLambda^2 ∣ p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * MixedGaussConversion.localG p hp hg := by
  have he := breveGamma1_gamma2_eq_neg_alpha_G (Ideal.span {p}) hg hc p rfl hp hprimary
  simpa only [localGamma, ConcreteBreveE.normalizedTraceGauss, pow_one,
    breveGamma1, breveGamma2, MixedGaussConversion.localG, FiniteGaussPhase.angularFactor,
    neg_div] using he

lemma actualSextic_pow_six_mul_add (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (r j : ℕ) :
    actualSextic P hg ^ (6*r+j) = actualSextic P hg ^ j := by
  rw [pow_add, pow_mul, actualSextic_six P hg hc, one_pow, one_mul]

lemma actualSextic_fifth_inverse (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) :
    actualSextic P hg ^ 5 = (actualSextic P hg)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact actualSextic_six P hg hc

lemma primeGauss_inverse_pair (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) :
    primeGauss p hp χ 1 * primeGauss p hp χ⁻¹ 1 =
      χ (-1) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have ht := ProbeGauss.gauss_inverse_pair χ (quotientTrace p hp) hχ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp)
  have hcard : Nat.card (O ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := rfl
  simpa only [primeGauss, tsum_fintype, map_one, one_mul, gaussSum,
    ← Nat.card_eq_fintype_card, hcard] using ht

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LocalWeights -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma even_diagonal_exponent (r : ℕ) : r + (2*r).choose 2 = 2*r*r := by
  rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  cases r with
  | zero => simp
  | succ r =>
    rw [show 2*(r+1)-1 = 2*r+1 by omega]
    ring

def localCubePhase (C omega : ℂ) (e l k : ℕ) : ℂ :=
  C^l * omega^((e+3*l)*k+e*l+l.choose 2)

theorem localCubePhase_even (C omega : ℂ) (hC : C^2=omega) (ho : omega^2=1)
    (e r k : ℕ) : localCubePhase C omega e (2*r) k = omega^(e*k) := by
  unfold localCubePhase
  rw [pow_mul C 2 r, hC, ← pow_add]
  have he : r+((e+3*(2*r))*k+e*(2*r)+(2*r).choose 2) =
      e*k+2*(3*r*k+e*r+r*r) := by
    have hd := even_diagonal_exponent r
    nlinarith
  rw [he, pow_add, pow_mul omega 2, ho, one_pow, mul_one]

def weightedScalar (Q eta a G1 C omega X W V scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (-eta*X/G1)^e * (a*X^3/Q)^l * localCubePhase C omega e l k * scalar * W^k * V^m

lemma weightedScalar_zero (Q eta a G1 C omega X W V : ℂ) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V 0 e l k m = 0 := by
  simp [weightedScalar]

def evenRatio (Q a X V : ℂ) : ℂ := a^2*Q^4*X^6*V

lemma weighted_squarefree_boundary (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r)*G1) 1 (2*r) 0 r =
      evenRatio Q a X V ^ r * (-eta*X) := by
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [mul_zero, pow_zero, pow_one, mul_one]
  unfold evenRatio
  rw [mul_pow, mul_pow, mul_pow, div_pow, mul_pow, pow_mul, pow_mul, pow_mul, pow_mul]
  field_simp
  ring

lemma weighted_even_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+5)*(Q-1))
      0 (2*r+2) 0 (r+1+d) =
      evenRatio Q a X V ^ r * (evenRatio Q a X V*(1-Q⁻¹)*V^d) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [zero_mul, pow_zero, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_even_kone (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+6))
      0 (2*r+2) 1 (r+1) = evenRatio Q a X V ^ r * (W*evenRatio Q a X V) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [pow_zero, pow_one, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_squarefree_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V
      ((omega⁻¹*G1)*(Q^(6*r)*(Q-1))) 1 (2*r) 1 (r+1+d) =
      evenRatio Q a X V ^ r * (-eta*(Q-1)*X*W*V^(d+1)) := by
  have hω : omega ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at ho; norm_num at ho
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [one_mul, pow_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsWeights -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma localCubePhase_step_two (C omega : ℂ) (hC : C^2=omega) (ho : omega^2=1)
    (e l k : ℕ) : localCubePhase C omega e (l+2) k=localCubePhase C omega e l k := by
  have hchoose : (l+2).choose 2=l.choose 2+2*l+1 := by
    rw [show l+2=(l+1)+1 by omega,Nat.choose_succ_succ,Nat.choose_one_right,
      Nat.choose_succ_succ,Nat.choose_one_right]
    change l+1+(l+l.choose 2)=l.choose 2+2*l+1
    omega
  unfold localCubePhase
  rw [pow_add C l 2,hC,hchoose]
  have he : (e+3*(l+2))*k+e*(l+2)+(l.choose 2+2*l+1)=
      ((e+3*l)*k+e*l+l.choose 2)+(2*(3*k+e+l)+1) := by ring
  have ht : omega^(2*(3*k+e+l)+1)=omega := by
    rw [pow_add,pow_mul omega 2,ho,one_pow,pow_one,one_mul]
  rw [he,pow_add omega _ (2*(3*k+e+l)+1),ht]
  calc
    _ = C^l*omega^((e+3*l)*k+e*l+l.choose 2)*omega^2 := by ring
    _ = _ := by rw [ho,mul_one]

theorem weightedScalar_step_two (Q eta a G1 C omega X W V scalar : ℂ)
    (hQ : Q≠0) (hC : C^2=omega) (ho : omega^2=1) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*weightedScalar Q eta a G1 C omega X W V scalar e l k m := by
  unfold weightedScalar evenRatio
  rw [localCubePhase_step_two C omega hC ho]
  rw [pow_add (a*X^3/Q) l 2,pow_succ V m]
  have hbase : (a*X^3/Q)^2*Q^6=a^2*Q^4*X^6 := by
    field_simp
  linear_combination (-eta*X/G1)^e*(a*X^3/Q)^l*localCubePhase C omega e l k*scalar*W^k*V^m*V*hbase

def rowWeightedScalar (Q eta a G1 C omega X W V rho scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (rho^k/rho^(e+3*l))*weightedScalar Q eta a G1 C omega X W V scalar e l k m

lemma rowWeightedScalar_zero (Q eta a G1 C omega X W V rho : ℂ) (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho 0 e l k m=0 := by
  rw [rowWeightedScalar,weightedScalar_zero,mul_zero]

theorem rowWeightedScalar_parameters (Q eta a G1 C omega X W V rho scalar : ℂ)
    (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m=
      weightedScalar Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar e l k m := by
  unfold rowWeightedScalar weightedScalar
  simp only [pow_add,pow_mul,mul_pow,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

theorem evenRatio_unit (Q a X V rho : ℂ) (hρ : rho^6=1) :
    evenRatio Q (a/rho^3) X V=evenRatio Q a X V := by
  unfold evenRatio
  rw [div_pow,←pow_mul,show 3*2=6 by decide,hρ,div_one]

theorem rowWeightedScalar_step_two (Q eta a G1 C omega X W V rho scalar : ℂ)
    (hQ : Q≠0) (hC : C^2=omega) (ho : omega^2=1) (hρ : rho^6=1) (e l k m : ℕ) :
    rowWeightedScalar Q eta a G1 C omega X W V rho (Q^6*scalar) e (l+2) k (m+1)=
      evenRatio Q a X V*rowWeightedScalar Q eta a G1 C omega X W V rho scalar e l k m := by
  rw [rowWeightedScalar_parameters,rowWeightedScalar_parameters,
    weightedScalar_step_two Q (eta/rho) (a/rho^3) G1 C omega X (rho*W) V scalar hQ hC ho,
    evenRatio_unit Q a X V rho hρ]

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.ScalarVanishing -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

theorem higher_convolution_zero (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n m : ℕ) (H : O) :
    (∑' d : O ⧸ Ideal.span {p^(m+2)},
      χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
        primePowerGauss p hp.ne_zero ξ (n+(m+2))
          (H-p^(n+1)*representative (p^(m+2)) d)) = 0 := by
  let : Finite (O ⧸ Ideal.span {p^(m+2)}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero _ hp.ne_zero)
  let : Fintype (O ⧸ Ideal.span {p^(m+2)}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {p*p^(n+(m+2))}) :=
    ConcreteTraceCRT.finite_quotient_span (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
  let : Fintype (O ⧸ Ideal.span {p*p^(n+(m+2))}) := Fintype.ofFinite _
  have hmod : p*p^(n+(m+2)) = p^(m+2)*p^(n+1) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hinner (V : O) : (∑' d : O ⧸ Ideal.span {p^(m+2)},
      χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
        quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
          (Ideal.Quotient.mk _ ((-V)*representative (p^(m+2)) d))) =
      primePowerGauss p hp.ne_zero χ (m+1) (-V) := by
    change quotientFourier p (p^(m+2)) (pow_ne_zero _ hp.ne_zero) χ (-V) = _
    rw [primePowerGauss_eq_quotientFourier]
    apply quotientFourier_congr
    rw [← pow_succ']
  unfold primePowerGauss conductorFourier
  simp_rw [tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  change (∑ d : O ⧸ Ideal.span {p^(m+2)},
    χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
      (ξ (Ideal.Quotient.mk _ v) *
        quotientTrace (p*p^(n+(m+2))) _
          (Ideal.Quotient.mk _ (H-p^(n+1)*representative (p^(m+2)) d)*Ideal.Quotient.mk _ v))) = 0
  have ht (d : O ⧸ Ideal.span {p^(m+2)}) :
      quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ ((H-p^(n+1)*representative (p^(m+2)) d)*v)) =
      quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ (H*v)) *
      quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
        (Ideal.Quotient.mk _ ((-v)*representative (p^(m+2)) d)) := by
    have ht := quotientTrace_split_frequency (p^(m+2)) (p^(n+1))
      (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero) H
      (representative (p^(m+2)) d) v
    simp only [quotientTrace_mk] at ht ⊢
    simpa only [← hmod] using ht
  simp_rw [← map_mul, ht]
  calc
    _ = ξ (Ideal.Quotient.mk _ v) *
        quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
          (Ideal.Quotient.mk _ (H*v)) *
        ∑ d : O ⧸ Ideal.span {p^(m+2)},
          χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
            quotientTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
              (Ideal.Quotient.mk _ ((-v)*representative (p^(m+2)) d)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = quotientTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
          (Ideal.Quotient.mk _ (H*v)) *
        (ξ (Ideal.Quotient.mk _ v) * primePowerGauss p hp.ne_zero χ (m+1) (-v)) := by
      have hi := hinner v
      rw [tsum_fintype] at hi
      rw [hi]
      ring
    _ = 0 := by rw [higher_outer_lift_annihilated p hp.ne_zero χ ξ (by omega : 0 < m+1) v, mul_zero]

theorem positiveScalar_kge_two (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n m j : ℕ) :
    positiveScalar p hp.ne_zero χ n (m+2) j = 0 := by
  rw [positiveScalar_full_lift p hp χ n (m+2) j (by omega),
    higher_convolution_zero p hp (χ^(m+2)) (χ^(n+1)) n m (p^j), mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.ScalarTable -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def gaussValuationTable (Q G : ℂ) (r n j : ℕ) : ℂ :=
  if 6 ∣ r then (if n+1 ≤ j then Q^(n+1) else 0) - (if n ≤ j then Q^n else 0)
  else if j=n then Q^n*G else 0

theorem actualSextic_gaussValuationTable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r n j : ℕ) :
    primePowerGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) n (p^j) =
      gaussValuationTable (Ideal.absNorm (Ideal.span {p}))
        (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg ^ r) 1) r n j :=
  actualSextic_primePowerGauss_at_pow p hp hg hc r n j

theorem positiveScalar_actual_table (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    let χ := actualSextic (Ideal.span {p}) hg
    let Q : ℂ := Ideal.absNorm (Ideal.span {p})
    positiveScalar p hp.ne_zero χ n k j =
      if k=0 then gaussValuationTable Q (primeGauss p hp.ne_zero (χ^(n+1)) 1) (n+1) n j
      else if k=1 ∧ 1 ≤ j then
        (χ (-1))⁻¹ * primeGauss p hp.ne_zero χ 1 *
          gaussValuationTable Q (primeGauss p hp.ne_zero (χ^n) 1) n n (j-1)
      else 0 := by
  dsimp only
  rcases k with _ | k
  · rw [ite_eq_left rfl, positiveScalar_kzero, actualSextic_gaussValuationTable p hp hg hc]
  rcases k with _ | k
  · rcases j with _ | j
    · simp only [ zero_add, Nat.one_ne_zero, ite_false,
          show ¬(1:ℕ) ≤ 0 by omega, and_false]
      exact positiveScalar_kone_jzero p hp _ n
    · rw [ite_eq_right (by omega : (1:ℕ) ≠ 0), ite_eq_left ⟨rfl, by omega⟩,
        positiveScalar_kone p hp.ne_zero, MulChar.inv_apply_eq_inv',
        actualSextic_gaussValuationTable p hp hg hc]
      simp
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), positiveScalar_kge_two p hp]

theorem zero_index_scalar (p : O) (_hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (k j : ℕ) (_hk : k ≠ 0) :
    (χ^k) (Ideal.Quotient.mk _ (p^j)) = if j=0 then 1 else 0 := by
  by_cases hj : j=0
  · simp [hj]
  · rw [ite_eq_right hj]
    have hz : Ideal.Quotient.mk (Ideal.span {p}) (p^j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_pow_self p hj))
    rw [hz, MulChar.map_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.UnramifiedScalar -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem unramified_even_kzero (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 0 (6*m) =
      if r+1 ≤ m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) * ((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else 0 := by
  rw [positiveScalar_kzero, actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_left (by omega : 6 ∣ 6*r+5+1)]
  by_cases hm : r+1 ≤ m
  · rw [ite_eq_left hm, ite_eq_left (by omega), ite_eq_left (by omega), pow_succ]
    ring
  · rw [ite_eq_right hm, ite_eq_right (by omega), ite_eq_right (by omega), sub_self]

theorem unramified_squarefree_kzero (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 0 (6*m) =
      if m=r then (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [positiveScalar_kzero, actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega : ¬6 ∣ 6*r+1), actualSextic_pow_six_mul_add _ hg hc, pow_one]
  by_cases hm : m=r
  · rw [ite_eq_left hm, ite_eq_left (by omega)]
  · rw [ite_eq_right hm, ite_eq_right (by omega)]

theorem unramified_squarefree_kone (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 1 (6*m) =
      if r< m then
        ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) * ((Ideal.absNorm (Ideal.span {p}):ℂ)-1))
      else 0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  rw [ite_eq_right (by decide : (1:ℕ) ≠ 0)]
  by_cases hm : r< m
  · rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left hm, gaussValuationTable,
      ite_eq_left (by omega : 6 ∣ 6*r), ite_eq_left (by omega), ite_eq_left (by omega), pow_succ]
    ring
  · rw [ite_eq_right hm]
    by_cases hm0 : m=0
    · subst m
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_left ⟨rfl, by omega⟩, gaussValuationTable,
        ite_eq_left (by omega : 6 ∣ 6*r), ite_eq_right (by omega), ite_eq_right (by omega), sub_self, mul_zero]

theorem unramified_odd_zero (r m k : ℕ) (d : ℕ) (hd : d=2 ∨ d=3) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) k (6*m) = 0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  split_ifs with hk hk1
  · rw [gaussValuationTable, ite_eq_right (by rcases hd with rfl | rfl <;> omega),
      ite_eq_right (by rcases hd with rfl | rfl <;> omega)]
  · rw [gaussValuationTable, ite_eq_right (by rcases hd with rfl | rfl <;> omega),
      ite_eq_right (by rcases hd with rfl | rfl <;> omega), mul_zero]
  · rfl

theorem unramified_even_kone (r m : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 1 (6*m) =
      if m=r+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+6) else 0 := by
  rw [positiveScalar_actual_table p hp hg hc, ite_eq_right (by decide : (1:ℕ) ≠ 0)]
  by_cases hm : m=r+1
  · subst m
    rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left rfl, gaussValuationTable,
      ite_eq_right (by omega : ¬6 ∣ 6*r+5), ite_eq_left (by omega),
      actualSextic_pow_six_mul_add _ hg hc, actualSextic_fifth_inverse _ hg hc]
    have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
      intro h
      have hpow : actualSextic (Ideal.span {p}) hg ^ 1 = 1 := by simpa using h
      have hdiv := (actualSextic_pow_eq_one_iff _ hg hc 1).mp hpow
      norm_num at hdiv
    have hi := primeGauss_inverse_pair p hp.ne_zero (actualSextic (Ideal.span {p}) hg) hχ
    have hω : actualSextic (Ideal.span {p}) hg (-1) ≠ 0 :=
      (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr (isUnit_one.neg : IsUnit (-1 : O ⧸ Ideal.span {p}))
    calc
      _ = (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) *
          ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
            (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 *
              primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg)⁻¹ 1)) := by ring
      _ = (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
        rw [hi]
        field_simp
      _ = _ := (pow_succ _ (6*r+5)).symm
  · rw [ite_eq_right hm]
    by_cases hm0 : m=0
    · subst m
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_left ⟨rfl, by omega⟩, gaussValuationTable,
        ite_eq_right (by omega : ¬6 ∣ 6*r+5), ite_eq_right (by omega), mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsScalar -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem row_even_kzero (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+5) 0 (j+6*m) =
      if r+1≤ m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=5 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) else 0 := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_left (by omega : 6∣6*r+5+1)]
  by_cases hm : r+1≤ m
  · rw [ite_eq_left hm,ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
    ring
  · rw [ite_eq_right hm,ite_eq_right (by omega)]
    by_cases hb : j=5 ∧ m=r
    · rw [ite_eq_left hb,ite_eq_left (by omega),zero_sub]
    · rw [ite_eq_right hb,ite_eq_right (by omega),sub_self]

theorem row_nonprincipal_kzero (r m j d : ℕ) (hj : j<6) (hd : d<5) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) 0 (j+6*m) =
      if j=d ∧ m=r then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+d)*
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^(d+1)) 1
      else 0 := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega : ¬6∣6*r+d+1)]
  rw [show 6*r+d+1=6*r+(d+1) by omega,actualSextic_pow_six_mul_add _ hg hc]
  have he : j+6*m=6*r+d ↔ j=d ∧ m=r := by omega
  simp only [he]

theorem row_squarefree_kone (r m j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r) 1 (j+6*m) =
      ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
        (if 6*r+1<j+6*m then
          (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r)*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
        else if j=1 ∧ m=r then -(Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) else 0) := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤j+6*m
  · rw [ite_eq_left ⟨rfl,hpos⟩,gaussValuationTable,ite_eq_left (by omega : 6∣6*r)]
    congr 1
    by_cases hb : 6*r+1<j+6*m
    · rw [ite_eq_left hb,ite_eq_left (by omega),ite_eq_left (by omega),pow_succ]
      ring
    · rw [ite_eq_right hb,ite_eq_right (by omega)]
      by_cases he : j=1 ∧ m=r
      · rw [ite_eq_left he,ite_eq_left (by omega),zero_sub]
      · rw [ite_eq_right he,ite_eq_right (by omega),sub_self]
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),mul_zero]

theorem row_nonprincipal_kone (r m j d : ℕ) (hj : j<6) (hd0 : 0<d) (hd : d<5) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (6*r+d) 1 (j+6*m) =
      if j=d+1 ∧ m=r then
        ((actualSextic (Ideal.span {p}) hg (-1))⁻¹ *
          primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1) *
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+d)*
            primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^d) 1)
      else 0 := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hpos : 1≤j+6*m
  · rw [ite_eq_left ⟨rfl,hpos⟩,gaussValuationTable,ite_eq_right (by omega : ¬6∣6*r+d),
      actualSextic_pow_six_mul_add _ hg hc]
    by_cases he : j=d+1 ∧ m=r
    · rw [ite_eq_left he,ite_eq_left (by omega)]
    · rw [ite_eq_right he,ite_eq_right (by omega),mul_zero]
  · rw [ite_eq_right (by omega),ite_eq_right (by omega)]

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsRecurrence -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma gaussValuationTable_step_six (Q G : ℂ) (r n j : ℕ) :
    gaussValuationTable Q G (r+6) (n+6) (j+6)=Q^6*gaussValuationTable Q G r n j := by
  have hd : 6∣r+6 ↔ 6∣r := by omega
  have hle : n+6+1≤j+6 ↔ n+1≤j := by omega
  have hle' : n+6≤j+6 ↔ n≤j := by omega
  have he : j+6=n+6 ↔ j=n := by omega
  simp only [gaussValuationTable,hd,hle,hle',he]
  split_ifs <;> simp [pow_add] <;> ring

theorem positiveScalar_step_six (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (n+6) k (j+6)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^6*
        positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j := by
  rw [positiveScalar_actual_table p hp hg hc,positiveScalar_actual_table p hp hg hc]
  have hp6 (a : ℕ) : actualSextic (Ideal.span {p}) hg^(a+6)=
      actualSextic (Ideal.span {p}) hg^a := by
    rw [pow_add,actualSextic_six _ hg hc,mul_one]
  by_cases hk : k=0
  · simp only [hk,ite_true]
    rw [show n+6+1=(n+1)+6 by omega,hp6,gaussValuationTable_step_six]
  · simp only [ite_eq_right hk]
    by_cases hk1 : k=1
    · subst k
      by_cases hj : 1≤j
      · rw [ite_eq_left ⟨rfl,by omega⟩,ite_eq_left ⟨rfl,hj⟩,hp6,
          show j+6-1=(j-1)+6 by omega,gaussValuationTable_step_six]
        ring
      · have hz : j=0 := by omega
        subst j
        simp only [show (1:ℕ)≤0+6 by omega,show ¬(1:ℕ)≤0 by omega,
          and_true,and_false,ite_true,ite_false,mul_zero]
        simp only [gaussValuationTable]
        split_ifs <;> simp_all ; omega
    · rw [ite_eq_right (by omega),ite_eq_right (by omega),mul_zero]

theorem positiveScalar_zero_below (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) (hj : j<n) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j=0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  split_ifs with hk hk1
  · simp only [gaussValuationTable]
    split_ifs <;> simp_all <;> omega
  · have hbelow : j-1<n := by omega
    have hz : gaussValuationTable (Ideal.absNorm (Ideal.span {p}))
        (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^n) 1) n n (j-1)=0 := by
      simp only [gaussValuationTable]
      split_ifs <;> simp_all <;> omega
    rw [hz,mul_zero]
  · rfl

end SevenEighths.ProbePrimePower
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LocalSeries -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalMarkedTerm (eta a X W V : ℂ) (e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1)) X W V
      (positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (e+3*l-1) k (6*m)) e l k m

include hc in
lemma localGamma_conjugate_three_sq :
    (star (localGamma p hp.ne_zero hg 3))^2 = actualSextic (Ideal.span {p}) hg (-1) := by
  have hg3 : localGamma p hp.ne_zero hg 3 ^ 2 = actualSextic (Ideal.span {p}) hg (-1) :=
    ProbePhase.normalizedTraceGauss_three_sq p hp.ne_zero hg hc
  rw [← star_pow, hg3]
  have hω := actualSextic_neg_one_sq (Ideal.span {p}) hg
  rcases (sq_eq_one_iff).mp hω with h | h
  · simp [h]
  · simp [h]

include hc in
lemma firstGauss_ne_zero : primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 ≠ 0 := by
  have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
    intro h
    have he : actualSextic (Ideal.span {p}) hg ^ 1 = 1 := by simpa using h
    have hd := (actualSextic_pow_eq_one_iff _ hg hc 1).mp he
    norm_num at hd
  have he := primeGauss_inverse_pair p hp.ne_zero (actualSextic (Ideal.span {p}) hg) hχ
  have hω : actualSextic (Ideal.span {p}) hg (-1) ≠ 0 :=
    (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr isUnit_one.neg
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  intro hz
  rw [hz, zero_mul] at he
  exact (mul_ne_zero hω hQ) he.symm

omit [(Ideal.span {p}).IsMaximal] in
include hp in
lemma primeNorm_ne_zero : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
  exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)

include hc

omit hc in
@[simp] theorem markedTerm_zero_index (eta a X W V : ℂ) (k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 0 k m = 0 := by
  simp only [principalMarkedTerm, mul_zero, add_zero, ite_true]

omit hc in
lemma markedTerm_higher_outer (eta a X W V : ℂ) (e l k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V e l (k+2) m = 0 := by
  unfold principalMarkedTerm
  split_ifs
  · rfl
  · rw [positiveScalar_kge_two p hp, weightedScalar_zero]

lemma markedTerm_odd (eta a X W V : ℂ) (e r k m : ℕ) (he : e ≤ 1) :
    principalMarkedTerm p hp hg eta a X W V e (2*r+1) k m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega)]
  have hn : e+3*(2*r+1)-1 = 6*r+(e+2) := by omega
  rw [hn, unramified_odd_zero p hp hg hc r m k (e+2) (by omega), weightedScalar_zero]

lemma markedTerm_squarefree_boundary (eta a X W V : ℂ) (r : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 r =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r * (-eta*X) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kzero p hp hg hc, ite_eq_left rfl]
  exact weighted_squarefree_boundary _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (firstGauss_ne_zero p hp hg hc) (localGamma_conjugate_three_sq p hp hg hc)
    (actualSextic_neg_one_sq _ hg) r

lemma markedTerm_squarefree_boundary_off (eta a X W V : ℂ) (r m : ℕ) (hm : m ≠ r) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kzero p hp hg hc, ite_eq_right hm, weightedScalar_zero]

lemma markedTerm_even_bulk (eta a X W V : ℂ) (r d : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 (r+1+d) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*V^d) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kzero p hp hg hc, ite_eq_left (by omega)]
  exact weighted_even_bulk _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) r d

lemma markedTerm_even_bulk_off (eta a X W V : ℂ) (r m : ℕ) (hm : m < r+1) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kzero p hp hg hc, ite_eq_right (by omega), weightedScalar_zero]

lemma markedTerm_even_kone (eta a X W V : ℂ) (r : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 (r+1) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kone p hp hg hc, ite_eq_left rfl]
  exact weighted_even_kone _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) r

lemma markedTerm_even_kone_off (eta a X W V : ℂ) (r m : ℕ) (hm : m ≠ r+1) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kone p hp hg hc, ite_eq_right hm, weightedScalar_zero]

lemma markedTerm_squarefree_bulk (eta a X W V : ℂ) (r d : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 (r+1+d) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V^(d+1)) := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kone p hp hg hc, ite_eq_left (by omega)]
  exact weighted_squarefree_bulk _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (firstGauss_ne_zero p hp hg hc) (localGamma_conjugate_three_sq p hp hg hc)
    (actualSextic_neg_one_sq _ hg) r d

lemma markedTerm_squarefree_bulk_off (eta a X W V : ℂ) (r m : ℕ) (hm : m < r+1) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 m = 0 := by
  unfold principalMarkedTerm
  rw [ite_eq_right (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kone p hp hg hc, ite_eq_right (by omega), weightedScalar_zero]

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsSeries -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def rowMarkedTerm (eta a X W V rho : ℂ) (j e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    rowWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1)) X W V rho
      (positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (e+3*l-1) k (j+6*m)) e l k m

include hc in
theorem rowMarkedTerm_step (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0<e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k (m+1)=
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
        rowMarkedTerm p hp hg eta a X W V rho j e l k m := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),ite_eq_right (by omega),
    show e+3*(l+2)-1=(e+3*l-1)+6 by omega,
    show j+6*(m+1)=(j+6*m)+6 by omega,
    positiveScalar_step_six p hp hg hc]
  exact rowWeightedScalar_step_two _ _ _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) hρ e l k m

theorem rowMarkedTerm_higher_outer (eta a X W V rho : ℂ) (j e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho j e l (k+2) m=0 := by
  unfold rowMarkedTerm
  split_ifs
  · rfl
  · rw [positiveScalar_kge_two p hp,rowWeightedScalar_zero]

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LocalSummation -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma hasSum_geometric_tail (f : ℕ → ℂ) (a : ℕ) (B V : ℂ) (hV : ‖V‖<1)
    (hz : ∀ m, m<a → f m=0) (hf : ∀ n, f (n+a)=B*V^n) :
    HasSum f (B/(1-V)) := by
  have ht : HasSum (fun n => f (n+a)) (B/(1-V)) := by
    simpa only [hf, div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hV).mul_left B
  have hs : (∑ i ∈ Finset.range a, f i) = 0 :=
    Finset.sum_eq_zero (fun i hi => hz i (Finset.mem_range.mp hi))
  simpa only [hs, zero_add] using ht.sum_range_add

lemma tsum_two_of_rest_zero (f : ℕ → ℂ) (hf : ∀ k, f (k+2)=0) :
    (∑' k, f k) = f 0+f 1 := by
  rw [tsum_eq_sum (s := {0,1})]
  · simp
  · intro k hk
    have hk2 : 2 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hk2
    simpa only [Nat.add_comm] using hf k

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalInner (eta a X W V : ℂ) (e l : ℕ) : ℂ :=
  ∑' k : ℕ, ∑' m : ℕ, principalMarkedTerm p hp hg eta a X W V e l k m

include hc

lemma squarefree_boundary_hasSum (eta a X W V : ℂ) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r * (-eta*X)) := by
  apply (hasSum_ite_eq r _).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hmS
  dsimp only
  by_cases hm : m=r
  · subst m
    rw [ite_eq_left rfl, markedTerm_squarefree_boundary p hp hg hc]
  · rw [ite_eq_right hm, markedTerm_squarefree_boundary_off p hp hg hc _ _ _ _ _ _ _ hm]

lemma even_kone_hasSum (eta a X W V : ℂ) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  apply (hasSum_ite_eq (r+1) _).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hmS
  dsimp only
  by_cases hm : m=r+1
  · subst m
    rw [ite_eq_left rfl, markedTerm_even_kone p hp hg hc]
  · rw [ite_eq_right hm, markedTerm_even_kone_off p hp hg hc _ _ _ _ _ _ _ hm]

lemma even_bulk_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)) / (1-V)) := by
  apply hasSum_geometric_tail _ (r+1) _ V hV
  · exact markedTerm_even_bulk_off p hp hg hc eta a X W V r
  · intro n
    rw [Nat.add_comm n (r+1), markedTerm_even_bulk p hp hg hc]
    ring

lemma squarefree_bulk_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V) / (1-V)) := by
  apply hasSum_geometric_tail _ (r+1) _ V hV
  · exact markedTerm_squarefree_bulk_off p hp hg hc eta a X W V r
  · intro n
    rw [Nat.add_comm n (r+1), markedTerm_squarefree_bulk p hp hg hc, pow_succ]
    ring

omit hc in
lemma principalInner_two (eta a X W V : ℂ) (e l : ℕ) :
    principalInner p hp hg eta a X W V e l =
      (∑' m, principalMarkedTerm p hp hg eta a X W V e l 0 m) +
      (∑' m, principalMarkedTerm p hp hg eta a X W V e l 1 m) := by
  apply tsum_two_of_rest_zero
  intro k
  simp only [markedTerm_higher_outer p hp hg, tsum_zero]

lemma principalInner_squarefree (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    principalInner p hp hg eta a X W V 1 (2*r) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*X - eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)) := by
  rw [principalInner_two p hp hg, (squarefree_boundary_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq,
    (squarefree_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq]
  ring

lemma principalInner_even (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    principalInner p hp hg eta a X W V 0 (2*r+2) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  rw [principalInner_two p hp hg, (even_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq,
    (even_kone_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq]
  ring

lemma principalInner_odd (eta a X W V : ℂ) (e r : ℕ) (he : e≤1) :
    principalInner p hp hg eta a X W V e (2*r+1) = 0 := by
  simp only [principalInner, markedTerm_odd p hp hg hc _ _ _ _ _ e r _ _ he, tsum_zero]

omit hc in
@[simp] lemma principalInner_zero (eta a X W V : ℂ) :
    principalInner p hp hg eta a X W V 0 0 = 0 := by
  simp only [principalInner, markedTerm_zero_index p hp hg, tsum_zero]

lemma principalInner_squarefree_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 1 l)
      ((-eta*X-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  let B := -eta*X-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)
  have he : HasSum (fun r => principalInner p hp hg eta a X W V 1 (2*r))
      ((1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)⁻¹ * B) := by
    simpa only [principalInner_squarefree p hp hg hc eta a X W V hV, B] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right B
  have ho : HasSum (fun r => principalInner p hp hg eta a X W V 1 (2*r+1)) 0 := by
    simp only [principalInner_odd p hp hg hc eta a X W V 1 _ (by omega)]
    exact hasSum_zero
  convert he.even_add_odd ho using 1
  simp only [add_zero, div_eq_mul_inv, B]
  ring

lemma principalInner_even_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 0 l)
      ((evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  let B := evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V
  have he : HasSum (fun r => principalInner p hp hg eta a X W V 0 (2*r))
      (B/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    apply hasSum_geometric_tail _ 1 B _ hR
    · intro m hm
      have hm0 : m=0 := by omega
      simp [hm0, principalInner_zero p hp hg]
    · intro r
      rw [show 2*(r+1)=2*r+2 by ring, principalInner_even p hp hg hc _ _ _ _ _ hV]
      ring
  have ho : HasSum (fun r => principalInner p hp hg eta a X W V 0 (2*r+1)) 0 := by
    simp only [principalInner_odd p hp hg hc eta a X W V 0 _ (by omega)]
    exact hasSum_zero
  simpa only [add_zero, B] using he.even_add_odd ho

def principalMarkedSeries (eta a X W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, principalInner p hp hg eta a X W V e.val l

theorem principalMarkedSeries_eq (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    principalMarkedSeries p hp hg eta a X W V =
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-eta*X+W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  unfold principalMarkedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [(principalInner_even_hasSum p hp hg hc eta a X W V hV hR).tsum_eq,
    (principalInner_squarefree_hasSum p hp hg hc eta a X W V hV hR).tsum_eq]
  unfold markedFactor
  simp only [pow_one]
  ring

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsDiagonal -/

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeEuler

theorem diagonal_recurrence_eq (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0) :
    ∀ r m,f r m=if r≤ m then R^r*f 0 (m-r) else 0 := by
  intro r
  induction r with
  | zero => intro m; simp
  | succ r ih =>
    intro m
    cases m with
    | zero => simp [hz]
    | succ m =>
      rw [hstep,ih]
      by_cases h : r≤ m
      · simp only [h,ite_true,Nat.succ_le_succ_iff,Nat.succ_sub_succ_eq_sub,pow_succ]
        ring
      · simp only [h,ite_false,Nat.succ_le_succ_iff,mul_zero]

theorem diagonal_recurrence_inner_hasSum (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0)
    (hs : Summable (f 0)) (r : ℕ) : HasSum (f r) (R^r*∑' m,f 0 m) := by
  have he := diagonal_recurrence_eq f R hstep hz
  have htail : HasSum (fun m=>f r (m+r)) (R^r*∑' m,f 0 m) := by
    convert hs.hasSum.mul_left (R^r) using 1
    funext m
    rw [he,ite_eq_left (Nat.le_add_left r m),Nat.add_sub_cancel]
  have hzero : (∑ m∈Finset.range r,f r m)=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [he,ite_eq_right (by have := Finset.mem_range.mp hm; omega)]
  simpa only [hzero,zero_add] using htail.sum_range_add

theorem diagonal_recurrence_hasSum (f : ℕ→ℕ→ℂ) (R : ℂ)
    (hstep : ∀ r m,f (r+1) (m+1)=R*f r m) (hz : ∀ r,f (r+1) 0=0)
    (hs : Summable (f 0)) (hR : ‖R‖<1) :
    HasSum (fun r=>∑' m,f r m) ((∑' m,f 0 m)/(1-R)) := by
  have he (r : ℕ) := (diagonal_recurrence_inner_hasSum f R hstep hz hs r).tsum_eq
  have hg : HasSum (fun r=>R^r*(∑' m,f 0 m)) ((∑' m,f 0 m)/(1-R)) := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right (∑' m,f 0 m)
  convert hg using 1
  funext r
  exact he r

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsSummability -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma geometric_indicator_summable (V A : ℂ) (hV : ‖V‖<1) (p : ℕ→Prop) :
    Summable (fun m=>(if p m then A else 0)*V^m) := by
  convert (((hasSum_geometric_of_norm_lt_one hV).summable.mul_left A).indicator {m | p m}) using 1
  funext m
  by_cases hm : p m <;> simp [hm]

lemma gaussValuationTable_geometric_summable (Q G V : ℂ) (hV : ‖V‖<1)
    (r n : ℕ) (j : ℕ→ℕ) :
    Summable (fun m=>gaussValuationTable Q G r n (j m)*V^m) := by
  by_cases hr : 6∣r
  · have ha := geometric_indicator_summable V (Q^(n+1)) hV (fun m=>n+1≤j m)
    have hb := geometric_indicator_summable V (Q^n) hV (fun m=>n≤j m)
    convert ha.sub hb using 1
    funext m
    simp only [gaussValuationTable,ite_eq_left hr,sub_mul]
    split_ifs <;> rfl
  · convert geometric_indicator_summable V (Q^n*G) hV (fun m=>j m=n) using 1
    funext m
    simp only [gaussValuationTable,ite_eq_right hr]
    split_ifs <;> rfl

theorem positiveScalar_geometric_summable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k : ℕ) (j : ℕ→ℕ) (V : ℂ) (hV : ‖V‖<1) :
    Summable (fun m=>positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k (j m)*V^m) := by
  simp only [positiveScalar_actual_table p hp hg hc]
  by_cases hk : k=0
  · simp only [ite_eq_left hk]
    exact gaussValuationTable_geometric_summable _ _ V hV (n+1) n j
  · simp only [ite_eq_right hk]
    have hs := (gaussValuationTable_geometric_summable (Ideal.absNorm (Ideal.span {p}))
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^n) 1) V hV n n (fun m=>j m-1)).mul_left
      (((actualSextic (Ideal.span {p}) hg (-1))⁻¹)*primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
    convert hs.indicator {m | k=1 ∧ 1≤j m} using 1
    funext m
    by_cases hm : k=1 ∧ 1≤j m <;> simp [hm,mul_assoc]

end SevenEighths.ProbePrimePower
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem rowMarkedTerm_frequency_summable (eta a X W V rho : ℂ) (hV : ‖V‖<1)
    (j e l k : ℕ) : Summable (fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k m) := by
  by_cases ht : e+3*l=0
  · simp only [rowMarkedTerm,ite_eq_left ht,summable_zero]
  · simp only [rowMarkedTerm,ite_eq_right ht,rowWeightedScalar,weightedScalar]
    have hs := SevenEighths.ProbePrimePower.positiveScalar_geometric_summable p hp hg hc (e+3*l-1) k (fun m=>j+6*m) V hV
    convert hs.mul_left ((rho^k/rho^(e+3*l)) *
      ((-eta*X/primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)^e *
        (a*X^3/(Ideal.absNorm (Ideal.span {p}):ℂ))^l *
        localCubePhase (star (localGamma p hp.ne_zero hg 3))
          (actualSextic (Ideal.span {p}) hg (-1)) e l k) *W^k) using 1
    funext m
    ring

theorem rowMarkedTerm_zero_lower_edge (eta a X W V rho : ℂ)
    (j e l k : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k 0=0 := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),positiveScalar_zero_below p hp hg hc _ _ _ (by omega),
    rowWeightedScalar_zero]

theorem rowMarkedFamily_hasSum (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j e l k : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    HasSum (fun r=>∑' m,rowMarkedTerm p hp hg eta a X W V rho j e (l+2*r) k m)
      ((∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m)/
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  apply diagonal_recurrence_hasSum
  · intro r m
    rw [show l+2*(r+1)=(l+2*r)+2 by omega]
    exact rowMarkedTerm_step p hp hg hc eta a X W V rho hρ j e (l+2*r) k m (by omega)
  · intro r
    rw [show l+2*(r+1)=(l+2*r)+2 by omega]
    exact rowMarkedTerm_zero_lower_edge p hp hg hc eta a X W V rho j e (l+2*r) k hj (by omega)
  · simpa only [mul_zero,add_zero] using rowMarkedTerm_frequency_summable p hp hg hc eta a X W V rho hV j e l k
  · exact hR

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsFamilies -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowInner (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑' k, ∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m

def rowMarkedSeries (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2, ∑' l,rowInner p hp hg eta a X W V rho j e.val l

lemma rowInner_two (eta a X W V rho : ℂ) (j e l : ℕ) :
    rowInner p hp hg eta a X W V rho j e l=
      (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l 0 m)+
      (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l 1 m) := by
  apply tsum_two_of_rest_zero
  intro k
  simp only [rowMarkedTerm_higher_outer,tsum_zero]

@[simp] lemma rowInner_zero (eta a X W V rho : ℂ) (j : ℕ) :
    rowInner p hp hg eta a X W V rho j 0 0=0 := by
  simp only [rowInner,rowMarkedTerm,mul_zero,add_zero,ite_true,tsum_zero]

include hc in
theorem rowInner_family_hasSum (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j e l : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    HasSum (fun r=>rowInner p hp hg eta a X W V rho j e (l+2*r))
      (rowInner p hp hg eta a X W V rho j e l/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  have h0 := rowMarkedFamily_hasSum p hp hg hc eta a X W V rho hρ hV hR j e l 0 hj ht
  have h1 := rowMarkedFamily_hasSum p hp hg hc eta a X W V rho hρ hV hR j e l 1 hj ht
  convert h0.add h1 using 1
  · funext r
    exact rowInner_two p hp hg eta a X W V rho j e (l+2*r)
  · rw [rowInner_two,add_div]

include hc in

theorem rowMarkedSeries_four_families (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=
      (rowInner p hp hg eta a X W V rho j 0 2+
       rowInner p hp hg eta a X W V rho j 1 0+
       rowInner p hp hg eta a X W V rho j 0 1+
       rowInner p hp hg eta a X W V rho j 1 1)/
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  have h02 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 2 hj (by omega)
  have h10 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 1 0 hj (by omega)
  have h01 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 1 hj (by omega)
  have h11 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 1 1 hj (by omega)
  have he0 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r))
      (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    have hshift : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*(r+1)))
        (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
      convert h02 using 1
      funext r
      congr 1
      omega
    have h := hshift.sum_range_add (f:=fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r)) (k:=1)
    simpa only [Finset.sum_range_one,mul_zero,rowInner_zero,zero_add] using h
  have he1 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 1 (2*r))
      (rowInner p hp hg eta a X W V rho j 1 0/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [zero_add] using h10
  have ho0 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 0 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h01
  have ho1 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 1 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 1 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h11
  unfold rowMarkedSeries
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]
  rw [(he0.even_add_odd ho0).tsum_eq,(he1.even_add_odd ho1).tsum_eq]
  ring

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighRowsTail -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma gaussValuationTable_above (Q G : ℂ) (r n j : ℕ) (hj : n+1≤j) :
    gaussValuationTable Q G r n j=if 6∣r then Q^(n+1)-Q^n else 0 := by
  unfold gaussValuationTable
  by_cases hd : 6∣r
  · rw [ite_eq_left hd,ite_eq_left hd,ite_eq_left hj,ite_eq_left (by omega)]
  · rw [ite_eq_right hd,ite_eq_right hd,ite_eq_right (by omega)]

theorem positiveScalar_stable_large (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (n k j j' : ℕ)
    (hj : n+1<j) (hj' : n+1<j') :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j' := by
  simp only [positiveScalar_actual_table p hp hg hc,
    show 1≤j by omega,show 1≤j' by omega,and_true,
    gaussValuationTable_above _ _ _ n j (by omega),
    gaussValuationTable_above _ _ _ n j' (by omega),
    gaussValuationTable_above _ _ _ n (j-1) (by omega),
    gaussValuationTable_above _ _ _ n (j'-1) (by omega)]

end SevenEighths.ProbePrimePower
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc

theorem rowMarkedTerm_base_tail (eta a X W V rho : ℂ)
    (j e l k m : ℕ) (ht : 0<e+3*l) (ht6 : e+3*l≤6) :
    rowMarkedTerm p hp hg eta a X W V rho j e l k (m+2)=
      rowMarkedTerm p hp hg eta a X W V rho j e l k 2*V^m := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),ite_eq_right (by omega),
    SevenEighths.ProbePrimePower.positiveScalar_stable_large p hp hg hc (e+3*l-1) k (j+6*(m+2)) (j+6*2) (by omega) (by omega)]
  unfold rowWeightedScalar weightedScalar
  rw [pow_add V m 2]
  ring

theorem rowInner_base_rational (eta a X W V rho : ℂ) (hV : ‖V‖<1)
    (j e l : ℕ) (ht : 0<e+3*l) (ht6 : e+3*l≤6) :
    rowInner p hp hg eta a X W V rho j e l=
      ∑ k : Fin 2,
        (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
         rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
         rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V)) := by
  have hsum (k : ℕ) : (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m)=
      rowMarkedTerm p hp hg eta a X W V rho j e l k 0+
      rowMarkedTerm p hp hg eta a X W V rho j e l k 1+
      rowMarkedTerm p hp hg eta a X W V rho j e l k 2/(1-V) := by
    have ht' : HasSum (fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k (m+2))
        (rowMarkedTerm p hp hg eta a X W V rho j e l k 2/(1-V)) := by
      have hgeo := (hasSum_geometric_of_norm_lt_one hV).mul_left (rowMarkedTerm p hp hg eta a X W V rho j e l k 2)
      rw [←div_eq_mul_inv] at hgeo
      convert hgeo using 1
      funext m
      exact rowMarkedTerm_base_tail p hp hg hc eta a X W V rho j e l k m ht ht6
    have h := ht'.sum_range_add (f:=fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k m) (k:=2)
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] using h.tsum_eq
  rw [rowInner_two,hsum 0,hsum 1]
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]

end SevenEighths.ProbeEuler
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.LocalRamification -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeLocalRamification
open CenteredMomentCorrelation CenteredMomentCanonical
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O

theorem crtCharacter_eq_one_iff {S ι : Type*} [CommRing S] [Fintype ι]
    {R : ι → Type*} [∀ i, CommRing (R i)]
    (e : S ≃+* ∀ i, R i) (χ : ∀ i, MulChar (R i) ℂ) :
    crtCharacter e χ = 1 ↔ ∀ i, χ i = 1 := by
  constructor
  · intro h i
    apply MulChar.ext
    intro u
    let v : ∀ j, R j := Function.update (fun _ => 1) i (u : R i)
    have hv : IsUnit v := by
      rw [Pi.isUnit_iff]
      intro j
      by_cases hj : j = i
      · subst j
        simp [v]
      · simp [v, hj]
    have hx : IsUnit (e.symm v) := hv.map e.symm.toMonoidHom
    have heq := congrArg (fun f : MulChar S ℂ => f (e.symm v)) h
    rw [crtCharacter_apply, e.apply_symm_apply, MulChar.one_apply hx] at heq
    have hprod : (∏ j, χ j (v j)) = χ i (u : R i) := by
      rw [Finset.prod_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [v, hj]
      · simp
    rw [hprod] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · intro h
    apply MulChar.ext
    intro u
    rw [crtCharacter_apply, MulChar.one_apply u.isUnit]
    apply Finset.prod_eq_one
    intro i _
    rw [h i, MulChar.one_apply]
    exact (u.isUnit.map e.toMonoidHom).map (Pi.evalMonoidHom _ i)

theorem primePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    {c : ℕ} (hc : 1 ≤ c) (χ : MulChar (O ⧸ P) ℂ) :
    primePowerCharacter P hc χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro u
    obtain ⟨x,hx⟩ := primePowerReduction_surjective P hc (u : O ⧸ P)
    have hux : IsUnit x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
      change Ideal.Quotient.mk P a = (u : O ⧸ P) at hx
      rw [hx]
      exact u.isUnit
    have heq := congrArg (fun f : MulChar (O ⧸ P^c) ℂ => f x) h
    rw [primePowerCharacter_apply, hx, MulChar.one_apply hux] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · rintro rfl
    apply MulChar.ext
    intro u
    rw [primePowerCharacter_apply, MulChar.one_apply u.isUnit,
      MulChar.one_apply (u.isUnit.map (primePowerReduction P hc))]

theorem canonicalPrimePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) : canonicalPrimePowerCharacter P hg hc = 1 ↔ 6 ∣ c := by
  rw [canonicalPrimePowerCharacter, primePowerCharacter_eq_one_iff,
    ← orderOf_dvd_iff_pow_eq_one, actualSextic_order_six P hg hchar]

theorem canonicalCRTCharacter_eq_one_iff {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    canonicalCRTCharacter P hg c hc hcop = 1 ↔ ∀ i, 6 ∣ c i := by
  rw [canonicalCRTCharacter, crtCharacter_eq_one_iff]
  exact forall_congr' (fun i => canonicalPrimePowerCharacter_eq_one_iff (P i) (hg i) (hchar i) (hc i))

theorem product_nonprincipal_of_coprime {A : Type*} [CommRing A]
    (I J : Ideal A) (hIJ : IsCoprime I J)
    (φ : MulChar (A ⧸ I) ℂ) (ψ : MulChar (A ⧸ J) ℂ) (hψ : ψ ≠ 1) :
    ResidueCharacter.product I J φ ψ ≠ 1 := by
  intro h
  apply hψ
  apply MulChar.ext
  intro u
  let e := Ideal.quotientInfEquivQuotientProd I J hIJ
  obtain ⟨x,hx⟩ := e.surjective ((1 : A ⧸ I), (u : A ⧸ J))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk I a, Ideal.Quotient.mk J a) = (1, (u : A ⧸ J)) at hx
  have hI := congrArg Prod.fst hx
  have hJ := congrArg Prod.snd hx
  dsimp only at hI hJ
  have hu : IsUnit (Ideal.Quotient.mk (I ⊓ J) a) := by
    apply (ResidueCharacter.isUnit_mk_inf_iff I J a).mpr
    constructor
    · rw [hI]
      exact isUnit_one
    · rw [hJ]
      exact u.isUnit
  have heq := congrArg (fun χ : MulChar (A ⧸ I ⊓ J) ℂ =>
    χ (Ideal.Quotient.mk (I ⊓ J) a)) h
  rw [ResidueCharacter.product_mk, hI, hJ, map_one, one_mul, MulChar.one_apply hu] at heq
  simpa only [MulChar.one_apply u.isUnit] using heq

theorem nonprincipal_fixed_times_local (Q P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : c < 6)
    (hcop : IsCoprime Q (P^c)) (φ : MulChar (O ⧸ Q) ℂ) :
    ResidueCharacter.product Q (P^c) φ (canonicalPrimePowerCharacter P hg hc) ≠ 1 := by
  apply product_nonprincipal_of_coprime _ _ hcop
  intro h
  exact Nat.not_dvd_of_pos_of_lt (by omega) hc6
    ((canonicalPrimePowerCharacter_eq_one_iff P hg hchar hc).mp h)

end SevenEighths.HeckeLocalRamification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonSupport -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonSupport
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

abbrev Residue (d : A) := A ⧸ Ideal.span {d}

def principalCRT (d a : A) (h : IsCoprime d a) :
    Residue (d * a) ≃+* Residue d × Residue a :=
  (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton d a).symm).trans
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {d}) (Ideal.span {a})
      ((Ideal.isCoprime_span_singleton_iff d a).mpr h))

@[simp] theorem principalCRT_mk (d a : A) (h : IsCoprime d a) (x : A) :
    principalCRT d a h (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
  ext <;> simp [principalCRT, Ideal.quotEquivOfEq_mk]

lemma coprime_mul_dvd_iff (d a n : A) (h : IsCoprime d a) :
    d * a ∣ n ↔ d ∣ n ∧ a ∣ n := by
  constructor
  · intro hn
    exact ⟨(dvd_mul_right d a).trans hn, (dvd_mul_left a d).trans hn⟩
  · rintro ⟨hd, ha⟩
    exact h.mul_dvd hd ha

theorem full_product_congruence (D E a b n : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ n ↔ D * E ∣ n ∧ a ∣ n ∧ b ∣ n := by
  have heq : (D * a) * (E * b) = (D * E) * (a * b) := by ring
  rw [heq, coprime_mul_dvd_iff _ _ _ (ha.mul_right hb), coprime_mul_dvd_iff _ _ _ hab]

theorem isUnit_residue_of_coprime (d a : A) (h : IsCoprime d a) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {d}) a) := by
  obtain ⟨u, v, huv⟩ := h
  apply IsUnit.of_mul_eq_one (Ideal.Quotient.mk (Ideal.span {d}) v)
  have hd : Ideal.Quotient.mk (Ideal.span {d}) d = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton d))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {d})) huv
  simpa only [map_add, map_mul, map_one, hd, mul_zero, zero_mul, zero_add, mul_comm] using hm

lemma residue_eq_zero_iff_dvd (d n : A) :
    Ideal.Quotient.mk (Ideal.span {d}) n = 0 ↔ d ∣ n := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem full_congruence_split (D E a b x y j : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ (E * b) * x - (D * a) * y - j ↔
      (D * E ∣ E * (b * x) - D * (a * y) - j) ∧
      Ideal.Quotient.mk (Ideal.span {a}) (E * b * x) = Ideal.Quotient.mk _ j ∧
      Ideal.Quotient.mk (Ideal.span {b}) (D * a * y) = Ideal.Quotient.mk _ (-j) := by
  rw [full_product_congruence D E a b _ ha hb hab]
  have hzeroa : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  have hzerob : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  have heq : (E * b) * x - (D * a) * y - j = E * (b * x) - D * (a * y) - j := by ring
  refine and_congr (by rw [heq]) (and_congr ?_ ?_)
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzeroa, mul_zero, zero_mul, sub_zero]
    exact sub_eq_zero
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzerob, mul_zero, zero_mul, zero_sub, map_neg]
    constructor <;> intro h <;> linear_combination -h

theorem sum_residual_constraints
    {X Y S T : Type*} [Fintype X] [Fintype Y] [CommRing S] [CommRing T]
    [Fintype S] [Fintype T]
    (p : X → Y → Prop) [∀ x y, Decidable (p x y)]
    (f : X → ℂ) (g : Y → ℂ) (α : S → ℂ) (β : T → ℂ)
    (a : Sˣ) (b : Tˣ) (j : S) (k : T) :
    (∑ x : X × S, ∑ y : Y × T,
      if p x.1 y.1 ∧ (a : S) * x.2 = j ∧ (b : T) * y.2 = k
      then (f x.1 * α x.2) * star (g y.1 * β y.2) else 0) =
    (∑ x : X, ∑ y : Y, if p x y then f x * star (g y) else 0) *
      α ((↑a⁻¹ : S) * j) * star (β ((↑b⁻¹ : T) * k)) := by
  have ha (x : S) : (a : S) * x = j ↔ x = (↑a⁻¹ : S) * j := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  have hb (y : T) : (b : T) * y = k ↔ y = (↑b⁻¹ : T) * k := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  simp only [Fintype.sum_prod_type, ha, hb]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p x y
  · simp only [h, true_and, star_mul]
    simp [ite_and, Finset.sum_ite_eq', mul_assoc, mul_left_comm, mul_comm]
  · simp [h]

theorem fullCorrelation_unit_change
    {X Y R : Type*} [CommRing X] [CommRing Y] [CommRing R]
    [Fintype X] [Fintype Y]
    (left : X → R) (right : Y → R) (χ : MulChar X ℂ) (ψ : MulChar Y ℂ)
    (u : Xˣ) (v : Yˣ) (j : R) :
    fullCorrelation (fun x => left ((u : X) * x)) (fun y => right ((v : Y) * y)) χ ψ j =
      χ (↑u⁻¹ : X) * star (ψ (↑v⁻¹ : Y)) * fullCorrelation left right χ ψ j := by
  have hχ (x : X) : χ x = χ (↑u⁻¹ : X) * χ ((u : X) * x) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hψ (y : Y) : ψ y = ψ (↑v⁻¹ : Y) * ψ ((v : Y) * y) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  unfold fullCorrelation
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv u.mulLeft
  intro x
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv v.mulLeft
  intro y
  simp only [Units.mulLeft_apply]
  by_cases h : left ((u : X) * x) - right ((v : Y) * y) = j
  · simp only [h, ite_true]
    rw [hχ x, hψ y, star_mul]
    ring
  · simp only [h, ite_false, mul_zero]

lemma character_unit_inverse {X : Type*} [CommRing X] [Fintype X]
    (χ : MulChar X ℂ) (u : Xˣ) : χ (↑u⁻¹ : X) = star (χ (u : X)) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

def residueUnit (d a : A) (h : IsCoprime d a) : (Residue d)ˣ :=
  (isUnit_residue_of_coprime d a h).unit

@[simp] theorem residueUnit_coe (d a : A) (h : IsCoprime d a) :
    (residueUnit d a h : Residue d) = Ideal.Quotient.mk _ a :=
  (isUnit_residue_of_coprime d a h).unit_spec

def scaledCommonCorrelation (D E a b : A)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) : ℂ :=
  fullCorrelation
    (fun x => scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x))
    (fun y => scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y))
    χD χE (Ideal.Quotient.mk _ j)

theorem scaledCommonCorrelation_eq (D E a b : A)
    (hDb : IsCoprime D b) (hEa : IsCoprime E a)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) :
    scaledCommonCorrelation D E a b χD χE j =
      star (χD (Ideal.Quotient.mk _ b)) * χE (Ideal.Quotient.mk _ a) *
        fullModulusCorrelation D E χD χE j := by
  have h := fullCorrelation_unit_change
    (scaledResidue D E (D * E) rfl) (scaledResidue E D (D * E) (mul_comm _ _))
    χD χE (residueUnit D b hDb) (residueUnit E a hEa) (Ideal.Quotient.mk _ j)
  simpa only [residueUnit_coe, character_unit_inverse, star_star,
    scaledCommonCorrelation, fullModulusCorrelation] using h

theorem fullModulusCorrelation_extract (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
    let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      scaledCommonCorrelation D E a b χD χE j *
        χa ((↑α⁻¹ : Residue a) * Ideal.Quotient.mk _ j) *
        star (χb ((↑β⁻¹ : Residue b) * Ideal.Quotient.mk _ (-j))) := by
  dsimp only
  let e₁ := principalCRT D a (IsCoprime.mul_left_iff.mp ha).1
  let e₂ := principalCRT E b (IsCoprime.mul_left_iff.mp hb).2
  let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
  let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
  let p := fun x : Residue D => fun y : Residue E =>
    scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x) -
      scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y) =
        Ideal.Quotient.mk _ j
  have hextract : fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      ∑ x : Residue D × Residue a, ∑ y : Residue E × Residue b,
        if p x.1 y.1 ∧ (α : Residue a) * x.2 = Ideal.Quotient.mk _ j ∧
          (β : Residue b) * y.2 = Ideal.Quotient.mk _ (-j)
        then (χD x.1 * χa x.2) * star (χE y.1 * χb y.2) else 0 := by
    unfold fullModulusCorrelation fullCorrelation
    apply Fintype.sum_equiv e₁.toEquiv
    intro x
    apply Fintype.sum_equiv e₂.toEquiv
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [e₁, e₂, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, principalCRT_mk,
      hχDa, hχEb, p, α, β, residueUnit_coe, ← map_mul]
    rw [scaledResidue_congruence, scaledResidue_congruence,
      full_congruence_split D E a b x y j ha hb hab]
    split_ifs <;> rfl
  rw [hextract, sum_residual_constraints]
  rfl

theorem fullModulusCorrelation_complete_support (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      fullModulusCorrelation D E χD χE j *
        (χE (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ E))) *
        (χb (Ideal.Quotient.mk _ D) * star (χD (Ideal.Quotient.mk _ b))) *
        (χb (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ b))) *
        χa (Ideal.Quotient.mk _ j) * star (χb (Ideal.Quotient.mk _ (-j))) := by
  rw [fullModulusCorrelation_extract D E a b ha hb hab χD χE χa χb χDa χEb hχDa hχEb j]
  rw [scaledCommonCorrelation_eq D E a b (IsCoprime.mul_left_iff.mp hb).1
    (IsCoprime.mul_left_iff.mp ha).2 χD χE j]
  simp only [map_mul, character_unit_inverse, residueUnit_coe, star_mul, star_star]
  ring

end SevenEighths.CenteredMomentCommonSupport
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Lattice -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentLattice
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open QuadraticInitialBound

theorem radial_zero_mode_error (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t)
    (A : O → ℂ) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ h, ‖A h‖ ≤ B) :
    ‖t • (∑' h : O, A h * paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) -
      t • (A 0 * paperRadialFourier W 0)‖ ≤ B * pvControl W := by
  let F : O → ℂ := fun h => A h * paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hF (h : O) : ‖F h‖ ≤ B * ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA h) (norm_nonneg _)
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF (hs.mul_left B)
  have hsplit := hFs.of_norm.tsum_eq_add_tsum_ite 0
  have hzero : F 0 = A 0 * paperRadialFourier W 0 := by simp only [F, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have htail : (∑' h : O, if h = 0 then 0 else F h) =
      ∑' h : {h : O // h ≠ 0}, F h := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [ite_eq_right h.property]
  have heq : (∑' h : O, F h) - F 0 = ∑' h : {h : O // h ≠ 0}, F h := by
    rw [hsplit, htail]
    ring
  have hn : ‖∑' h : {h : O // h ≠ 0}, F h‖ ≤
      B * (∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) := by
    calc
      _ ≤ ∑' h : {h : O // h ≠ 0}, ‖F h‖ := norm_tsum_le_tsum_norm (hFs.subtype _)
      _ ≤ ∑' h : {h : O // h ≠ 0}, B *
          ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ :=
        (hFs.subtype _).tsum_le_tsum (fun h => hF h) ((hs.subtype _).mul_left B)
      _ = _ := tsum_mul_left
  change ‖t • (∑' h : O, F h) - t • (A 0 * paperRadialFourier W 0)‖ ≤ _
  rw [← hzero, ← smul_sub, heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ t * (B * ∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) :=
      mul_le_mul_of_nonneg_left hn ht.le
    _ = B * (t * ∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) := by ring
    _ ≤ B * pvControl W := mul_le_mul_of_nonneg_left (pv_lattice_bound W t ht) hB

theorem periodic_lattice_volume_error (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
        W (‖eisEmbedding z‖ ^ 2 / X)) -
      (X / ‖eisEmbedding c‖ ^ 2 : ℝ) •
        ((∑ r : O ⧸ Ideal.span {c}, P r) * paperRadialFourier W 0)‖ ≤
      (∑ r : O ⧸ Ideal.span {c}, ‖P r‖) * pvControl W := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c},
    P r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)
  let B : ℝ := ∑ r : O ⧸ Ideal.span {c}, ‖P r‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hA (h : O) : ‖A h‖ ≤ B := by
    apply (norm_sum_le _ _).trans
    dsimp only [B]
    apply Finset.sum_le_sum
    intro r _
    rw [norm_mul, ψ.norm_apply, mul_one]
  have hA0 : A 0 = ∑ r : O ⧸ Ideal.span {c}, P r := by
    simp only [A, map_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
  have hnorm : 0 < ‖eisEmbedding c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
  have h := radial_zero_mode_error W (X / ‖eisEmbedding c‖ ^ 2)
    (div_pos hX hnorm) A B hB hA
  rw [actual_radial_paper_poisson_trace W X hX c hc P]
  rw [hA0] at h
  simpa only [A, B, ψ, div_mul_eq_mul_div] using h

theorem logPhase_eq_normPower (t x : ℝ) (hx : 0 < x) :
    FourierBridge.logPhase (t / (2 * Real.pi)) (Real.log x) =
      (x : ℂ) ^ (Complex.I * t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
  unfold FourierBridge.logPhase
  rw [← Complex.ofReal_log hx.le]
  congr 1
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  push_cast
  field_simp

def normPowerProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) : 𝓢(ℝ, ℂ) :=
  CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (t / (2 * Real.pi))

theorem normPowerProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t x : ℝ) :
    normPowerProfile W a b ha hs hW t x = (x : ℂ) ^ (Complex.I * t) * W x := by
  rw [normPowerProfile, CompletedHeight.uniformTwistedSchwartz_apply]
  unfold CompletedHeight.normTwistedSource
  by_cases hx : W x = 0
  · simp only [hx, mul_zero]
  · rw [logPhase_eq_normPower t x (lt_of_lt_of_le ha (hs hx).1)]

theorem normPowerProfile_zero_mode (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
      (2 * Real.pi / Real.sqrt 3 : ℂ) *
        ∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (Complex.I * t) * W y := by
  rw [paperRadialFourier_zero_eq_halfline]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro y _
  exact normPowerProfile_apply W a b ha hs hW t y

theorem normPowerProfile_uniform_degree (a b : ℝ) (ha : 0 < a)
    (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) ≤
        C * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
  obtain ⟨n, hn⟩ := CompletedHeight.normTwistedSource_uniform_degree a b ha S
  refine ⟨n, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hn W hs hW
  exact ⟨C, hC, fun t => hbound (t / (2 * Real.pi))⟩

theorem periodic_twisted_lattice_volume_error (a b : ℝ) (ha : 0 < a) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∀ c : O, ∀ hc : c ≠ 0,
      ∀ P : O ⧸ Ideal.span {c} → ℂ,
      letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
      letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
      ∃ C : ℝ, 0 < C ∧ ∀ t X : ℝ, 0 < X →
        ‖(∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
            (((‖eisEmbedding z‖ ^ 2 / X : ℝ) : ℂ) ^ (Complex.I * t) *
              W (‖eisEmbedding z‖ ^ 2 / X))) -
          (X / ‖eisEmbedding c‖ ^ 2 : ℝ) •
            ((∑ r : O ⧸ Ideal.span {c}, P r) *
              paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)‖ ≤
          C * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  refine ⟨n, ?_⟩
  intro W hs hW c hc P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  obtain ⟨D, hD, hbound⟩ := hn W hs hW
  let B : ℝ := ∑ r : O ⧸ Ideal.span {c}, ‖P r‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨(1 + B) * pvConstant * D, mul_pos (mul_pos (by linarith) pvConstant_pos) hD, ?_⟩
  intro t X hX
  have h := periodic_lattice_volume_error (normPowerProfile W a b ha hs hW t) X hX c hc P
  simp only [normPowerProfile_apply] at h
  apply h.trans
  change B * (pvConstant * _) ≤ _
  calc
    _ ≤ B * (pvConstant * (D * (1 + ‖t / (2 * Real.pi)‖) ^ n)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hbound t) pvConstant_pos.le) hB
    _ ≤ (1 + B) * pvConstant * D * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
      nlinarith [mul_nonneg pvConstant_pos.le hD.le,
        mul_nonneg (mul_nonneg pvConstant_pos.le hD.le)
          (show 0 ≤ (1 + ‖t / (2 * Real.pi)‖) ^ n by positivity)]

end SevenEighths.CenteredMomentLattice
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.Mask -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem ideal_coprime_mobius (I R : Ideal O) (hR : R ≠ 0) :
    (if IsCoprime I R then (1 : ℂ) else 0) =
      ∑ D ∈ idealDivisors R, if D ∣ I then (moebius D : ℂ) else 0 := by
  let G : Ideal O := R ⊔ I
  have hG : G ≠ 0 := by
    intro hz
    apply hR
    apply le_antisymm _ bot_le
    exact le_sup_left.trans_eq hz
  have hdiv : (idealDivisors R).filter (fun D => D ∣ I) = idealDivisors G := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hR, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G, sup_comm]

theorem tsum_ideal_divisible (D : Ideal O) (hD : D ≠ 0) (f : Ideal O → ℂ) :
    (∑' I : Ideal O, if D ∣ I then f I else 0) =
      ∑' J : Ideal O, f (D * J) := by
  let F : Ideal O → ℂ := fun I => if D ∣ I then f I else 0
  have hrange : Function.support F ⊆ Set.range (fun J : Ideal O => D * J) := by
    intro I hI
    have hd : D ∣ I := by
      by_contra hn
      exact hI (by simp only [F, ite_eq_right hn])
    obtain ⟨J, hJ⟩ := hd
    exact ⟨J, hJ.symm⟩
  have ht := (mul_right_injective₀ hD).tsum_eq hrange
  calc
    _ = ∑' J : Ideal O, F (D * J) := ht.symm
    _ = _ := by
      apply tsum_congr
      intro J
      simp only [F, dvd_mul_right, ite_true]

theorem masked_ideal_sum_eq (R : Ideal O) (hR : R ≠ 0)
    (f : Ideal O → ℂ) (hf : Summable f) :
    (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) * f I) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * ∑' J : Ideal O, f (D * J) := by
  have hterm (I : Ideal O) : (if IsCoprime I R then (1 : ℂ) else 0) * f I =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * (if D ∣ I then f I else 0) := by
    rw [ideal_coprime_mobius I R hR, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro D _
    by_cases h : D ∣ I <;> simp only [h, ite_true, ite_false, zero_mul, mul_zero]
  have hsum (D : Ideal O) :
      Summable (fun I : Ideal O => (moebius D : ℂ) * (if D ∣ I then f I else 0)) := by
    have h := (hf.indicator {I : Ideal O | D ∣ I}).mul_left (moebius D : ℂ)
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun D _ => hsum D)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [tsum_mul_left, tsum_ideal_divisible D (ne_zero_of_dvd_ne_zero hR
    ((mem_idealDivisors hR).mp hD))]

theorem annular_ideal_sum_summable (χ : Ideal O → ℂ) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    Summable (fun I : Ideal O => χ I * W ((Ideal.absNorm I : ℝ) / X)) := by
  apply summable_of_hasFiniteSupport
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b * X))).subset
  intro I hI
  have hw : W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
    intro hz
    exact hI (by simp only [hz, mul_zero])
  have hn : (Ideal.absNorm I : ℝ) ≤ b * X := (div_le_iff₀ hX).mp (hs hw)
  exact_mod_cast hn.trans (Nat.le_ceil (b * X))

theorem masked_plain_ideal_sum (R : Ideal O) (hR : R ≠ 0)
    (χ : Ideal O →* ℂ) (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
        (χ I * W ((Ideal.absNorm I : ℝ) / X))) =
      ∑ D ∈ idealDivisors R, (moebius D : ℂ) * χ D *
        ∑' J : Ideal O, χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D)) := by
  rw [masked_ideal_sum_eq R hR _ (annular_ideal_sum_summable χ W b X hX hs)]
  apply Finset.sum_congr rfl
  intro D hD
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
  have hnD : (Ideal.absNorm D : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm D ≠ 0 by
      intro hz
      exact hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hterms (J : Ideal O) :
      χ (D * J) * W ((Ideal.absNorm (D * J) : ℝ) / X) =
        χ D * (χ J * W ((Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D))) := by
    rw [map_mul, map_mul, Nat.cast_mul]
    have harg : (Ideal.absNorm D : ℝ) * Ideal.absNorm J / X =
        (Ideal.absNorm J : ℝ) / (X / Ideal.absNorm D) := by field_simp
    rw [harg]
    ring
  simp_rw [hterms]
  rw [tsum_mul_left]
  ring

theorem polynomial_mask_divisor_bound (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal O, R ≠ 0 →
      (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ((idealDivisors R).card : ℝ) ≤ C * Z ^ ε := by
  let δ := ε / (B + 1)
  have hden : 0 < B + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C, hC, hcount⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm
  have hexp : B * δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    _ ≤ C * (Ideal.absNorm R : ℝ) ^ δ := hcount R hR
    _ ≤ C * (Z ^ B) ^ δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hnorm hδ.le) hC.le
    _ = C * Z ^ (B * δ) := by rw [← Real.rpow_mul (by linarith : 0 ≤ Z)]
    _ ≤ C * Z ^ ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hexp) hC.le

end SevenEighths.CenteredMomentMask
end

end OAI

end

