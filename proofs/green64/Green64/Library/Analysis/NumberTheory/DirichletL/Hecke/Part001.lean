module

public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part007

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Hecke / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection -/

section

namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

abbrev PrimeIdeal := {P : Ideal ActualEisensteinCubic.O // Prime P}

def primeProduct (s : Finset PrimeIdeal) : Ideal ActualEisensteinCubic.O := ∏ P ∈ s, P.val

def primeSet (I : Ideal ActualEisensteinCubic.O) : Finset PrimeIdeal :=
  (primeSupport I).attach.image (fun P => ⟨P.val, support_prime P.property⟩)

@[simp] theorem mem_primeSet (I : Ideal ActualEisensteinCubic.O) (P : PrimeIdeal) :
    P ∈ primeSet I ↔ P.val ∈ primeSupport I := by
  simp only [primeSet, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨Q,hQ⟩
    have hv := congrArg Subtype.val hQ
    simpa only [←hv] using Q.property
  · intro h
    exact ⟨⟨P.val,h⟩,rfl⟩

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.property)
  simpa only [primeProduct, Finset.prod_eq_multiset_prod] using h

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨Q,hQ,he⟩
    have : Q=P := Subtype.ext he
    simpa [this] using hQ
  · intro h
    exact ⟨P,h,rfl⟩

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal ActualEisensteinCubic.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal ActualEisensteinCubic.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

def mobiusPrimeCoeff (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  (moebius I : ℂ) * primeValueHom w I

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal ActualEisensteinCubic.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal ActualEisensteinCubic.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

end

section
open ActualEisensteinCubic
open Filter

lemma prime_norm_two_le (P : PrimeIdeal) : 2 ≤ Ideal.absNorm P.val := by
  have h0 : Ideal.absNorm P.val ≠ 0 := fun h => P.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.val ≠ 1 := by
    intro h
    apply P.property.not_isUnit
    rw [Ideal.absNorm_eq_one_iff.mp h]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal ActualEisensteinCubic.O) from isUnit_one)
  omega

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

def primeNormPower (P : PrimeIdeal) (s : ℂ) : ℂ := (Ideal.absNorm P.val : ℂ)^(-s)

def primeCharacterTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  χ (Ideal.absNorm P.val) * primeNormPower P s

def primeDensity (P : PrimeIdeal) : ℂ := 1-(1:ℂ)/(Ideal.absNorm P.val:ℂ)

lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)

lemma primeDensity_norm_le_one (P : PrimeIdeal) : ‖primeDensity P‖≤1 := by
  have hn := prime_norm_pos P
  have hn1 : (1:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast (by have:=prime_norm_two_le P;omega)
  have he : primeDensity P = ((1-(1:ℝ)/(Ideal.absNorm P.val:ℝ):ℝ):ℂ) := by
    simp [primeDensity]
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
  · have : (0:ℝ)≤1/(Ideal.absNorm P.val:ℝ) := by positivity
    linarith
  · exact sub_nonneg.mpr ((div_le_one hn).mpr hn1)

lemma primeCharacterTerm_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (σ : ℝ) (hs : σ≤ s.re) :
    ‖primeCharacterTerm χ P s‖≤(Ideal.absNorm P.val:ℝ)^(-σ) := by
  rw [primeCharacterTerm,norm_mul,norm_primeNormPower]
  have hn1 : (1:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast (by have:=prime_norm_two_le P;omega)
  calc
    _ ≤ 1*(Ideal.absNorm P.val:ℝ)^(-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
    _ ≤ _ := by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hs)

lemma primeCharacterTerm_norm_lt_one {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (hs : 0<s.re) : ‖primeCharacterTerm χ P s‖<1 := by
  apply (primeCharacterTerm_norm_le χ P s s.re le_rfl).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg (by have:=prime_norm_two_le P;exact_mod_cast (by omega:1<Ideal.absNorm P.val)) (by linarith)

lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he : x=1 := (sub_eq_zero.mp h).symm
  simp [he] at hx

lemma correctionDenominator_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (hs : 0<s.re) : 1-primeDensity P*primeCharacterTerm χ P s≠0 := by
  apply one_sub_ne_zero
  rw [norm_mul]
  calc
    _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
      mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
    _ < 1 := by rw [one_mul];exact primeCharacterTerm_norm_lt_one χ P s hs

def correctionTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) : ℂ :=
  if P.val∈S then 0 else
    -((1:ℂ)/(Ideal.absNorm P.val:ℂ))*primeCharacterTerm χ P s /
      (1-primeDensity P*primeCharacterTerm χ P s)

def eulerCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) : ℂ :=
  ∏' P : PrimeIdeal, (1+correctionTerm χ S P s)

lemma correctionTerm_factor {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) :
    1+correctionTerm χ S P s =
      if P.val∈S then 1 else (1-primeCharacterTerm χ P s)/(1-primeDensity P*primeCharacterTerm χ P s) := by
  by_cases hP : P.val∈S
  · simp [correctionTerm,hP]
  · simp only [correctionTerm,ite_eq_right hP]
    have hd := correctionDenominator_ne_zero χ P s hs
    apply (eq_div_iff hd).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hd]
    dsimp [primeDensity]
    ring

lemma correctionFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) : 1+correctionTerm χ S P s≠0 := by
  rw [correctionTerm_factor χ S P s hs]
  split_ifs
  · exact one_ne_zero
  · exact div_ne_zero (one_sub_ne_zero (primeCharacterTerm_norm_lt_one χ P s hs))
      (correctionDenominator_ne_zero χ P s hs)

lemma correctionTerm_uniform_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) (P : PrimeIdeal) (s : ℂ) (hs : σ≤ s.re) :
    ‖correctionTerm χ S P s‖ ≤
      (1-(2:ℝ)^(-σ))⁻¹*(Ideal.absNorm P.val:ℝ)^(-(1+σ)) := by
  have hn := prime_norm_pos P
  have hn2 : (2:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast prime_norm_two_le P
  have hr : (2:ℝ)^(-σ)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr0 : 0<1-(2:ℝ)^(-σ) := sub_pos.mpr hr
  have hx := primeCharacterTerm_norm_le χ P s σ hs
  have hx2 : ‖primeCharacterTerm χ P s‖≤(2:ℝ)^(-σ) := hx.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith))
  have hd : 1-(2:ℝ)^(-σ)≤‖1-primeDensity P*primeCharacterTerm χ P s‖ := by
    have hb : ‖primeDensity P*primeCharacterTerm χ P s‖≤(2:ℝ)^(-σ) := by
      rw [norm_mul]
      calc
        _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
          mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
        _ ≤ _ := by simpa using hx2
    have hh := norm_sub_norm_le (1:ℂ) (primeDensity P*primeCharacterTerm χ P s)
    simpa only [norm_one] using (show 1-(2:ℝ)^(-σ) ≤ ‖(1:ℂ)‖-‖primeDensity P*primeCharacterTerm χ P s‖ from by simpa using sub_le_sub_left hb 1) |>.trans hh
  by_cases hP : P.val∈S
  · simp only [correctionTerm,ite_eq_left hP,norm_zero]
    positivity
  · rw [correctionTerm,ite_eq_right hP,norm_div,norm_mul,norm_neg,norm_div,norm_one,Complex.norm_natCast]
    calc
      _ ≤ ((1:ℝ)/(Ideal.absNorm P.val:ℝ)*(Ideal.absNorm P.val:ℝ)^(-σ))/(1-(2:ℝ)^(-σ)) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hx (by positivity)) hr0 hd
      _ = _ := by
        rw [show -(1+σ)=(-1)+(-σ) by ring,Real.rpow_add hn,Real.rpow_neg_one]
        ring

lemma prime_norm_series_summable (σ : ℝ) (hσ : 0<σ) :
    Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val:ℝ)^(-(1+σ))) := by
  have ht := (CubicEisenstein.fullIdealWeight_summable_norm (1+(σ:ℂ)) (by simp;linarith)).comp_injective
    (i := fun P : PrimeIdeal => P.val) Subtype.val_injective
  apply ht.congr
  intro P
  simp only [Function.comp_def,CubicEisenstein.fullIdealWeight,ite_eq_right P.property.ne_zero]
  simpa only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-(1+(σ:ℂ))))

lemma correctionTerm_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 0<s.re) : Summable (fun P : PrimeIdeal => ‖correctionTerm χ S P s‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => correctionTerm_uniform_bound χ S s.re hs P s le_rfl)
  exact (prime_norm_series_summable s.re hs).mul_left _

theorem eulerCorrection_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 0<s.re) : eulerCorrection χ S s≠0 :=
  tprod_one_add_ne_zero_of_summable (fun P => correctionFactor_ne_zero χ S P s hs)
    (correctionTerm_summable χ S s hs)

lemma primeCharacterTerm_differentiable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : PrimeIdeal) : Differentiable ℂ (primeCharacterTerm χ P) := by
  have hn : (Ideal.absNorm P.val:ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (prime_norm_pos P))
  exact ((differentiable_id.neg).const_cpow (Or.inl hn)).const_mul _

lemma correctionTerm_differentiableOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (P : PrimeIdeal) (σ : ℝ) (hσ : 0≤σ) :
    DifferentiableOn ℂ (correctionTerm χ S P) {s:ℂ | σ<s.re} := by
  unfold correctionTerm
  by_cases hP : P.val∈S
  · simpa only [ite_eq_left hP] using (differentiableOn_const (𝕜 := ℂ) (s := {s:ℂ | σ<s.re}) (c := (0:ℂ)))
  · simp only [ite_eq_right hP]
    intro s hs
    have hx := primeCharacterTerm_differentiable χ P s
    convert ((hx.const_mul (-((1:ℂ)/(Ideal.absNorm P.val:ℂ)))).div
      ((differentiableAt_const (1:ℂ)).sub (hx.const_mul (primeDensity P)))
      (correctionDenominator_ne_zero χ P s (lt_of_le_of_lt hσ hs))).differentiableWithinAt using 1

lemma eulerCorrection_locally_uniform {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    HasProdLocallyUniformlyOn (fun P s => 1+correctionTerm χ S P s)
      (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  have hu := (prime_norm_series_summable σ hσ).mul_left ((1-(2:ℝ)^(-σ))⁻¹)
  exact hu.hasProdLocallyUniformlyOn_one_add
    (isOpen_lt continuous_const Complex.continuous_re)
    (Filter.Eventually.of_forall (fun P s hs => correctionTerm_uniform_bound χ S σ hσ P s hs.le))
    (fun P => (correctionTerm_differentiableOn χ S P σ hσ.le).continuousOn)

theorem eulerCorrection_differentiableOn_halfplane {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (σ : ℝ) (hσ : 0<σ) :
    DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | σ<s.re} := by
  apply (eulerCorrection_locally_uniform χ S σ hσ).differentiableOn
  · apply Filter.Eventually.of_forall
    intro t
    change DifferentiableOn ℂ (fun z => ∏ P ∈ t, (1+correctionTerm χ S P z)) _
    apply DifferentiableOn.fun_finsetProd
    intro P hP
    exact (differentiableOn_const (𝕜 := ℂ) (c := (1:ℂ))).add
      (correctionTerm_differentiableOn χ S P σ hσ.le)
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem eulerCorrection_differentiableOn {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : DifferentiableOn ℂ (eulerCorrection χ S) {s:ℂ | 0<s.re} := by
  intro s hs
  have hh := eulerCorrection_differentiableOn_halfplane χ S (s.re/2) (by dsimp at hs;linarith)
  exact (hh.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show s∈{z:ℂ | s.re/2<z.re} by dsimp at *;linarith))).differentiableWithinAt

end

section
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

lemma prod_primeSet {M : Type*} [CommMonoid M] (I : Ideal ActualEisensteinCubic.O) (f : Ideal ActualEisensteinCubic.O→M) :
    (∏P∈primeSet I,f P.val)=∏P∈primeSupport I,f P := by
  unfold primeSet
  rw [Finset.prod_image]
  · exact Finset.prod_attach (primeSupport I) f
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

lemma primeValueHom_squarefree (w : Ideal ActualEisensteinCubic.O→ℂ) (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeValueHom w I=∏P∈primeSet I,w P.val := by
  calc
    _ = primeValueHom w (primeProduct (primeSet I)) :=
      congrArg (primeValueHom w) (primeProduct_primeSet I hI).symm
    _ = _ := by simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]

lemma outside_primeProduct_iff (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P)
    (t : Finset PrimeIdeal) :
    (∀P∈S,¬P∣primeProduct t) ↔ ∀Q∈t,Q.val∉S := by
  constructor
  · intro h Q hQ hQS
    apply h Q.val hQS
    exact Finset.dvd_prod_of_mem (fun P : PrimeIdeal => P.val) hQ
  · intro h P hP hd
    obtain ⟨Q,hQ,hPQ⟩ := ((hS P hP).dvd_finsetProd_iff (fun Q : PrimeIdeal => Q.val)).mp hd
    have he : P=Q.val := associated_iff_eq.mp (((hS P hP).dvd_prime_iff_associated Q.property).mp hPQ)
    exact h Q hQ (he ▸ hP)

def outsideMask (S : Finset (Ideal ActualEisensteinCubic.O)) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if ∀P∈S,¬P∣I then 1 else 0

lemma prod_cut_primes (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P)
    (t : Finset PrimeIdeal) (f : Ideal ActualEisensteinCubic.O→ℂ) :
    (∏Q∈t,if Q.val∈S then 0 else f Q.val)=outsideMask S (primeProduct t)*(∏Q∈t,f Q.val) := by
  by_cases ho : ∀P∈S,¬P∣primeProduct t
  · rw [outsideMask,ite_eq_left ho,one_mul]
    apply Finset.prod_congr rfl
    intro Q hQ
    exact ite_eq_right ((outside_primeProduct_iff S hS t).mp ho Q hQ)
  · rw [outsideMask,ite_eq_right ho,zero_mul]
    have hh : ¬∀Q∈t,Q.val∉S := fun h => ho ((outside_primeProduct_iff S hS t).mpr h)
    push Not at hh
    obtain ⟨Q,hQ,hQS⟩ := hh
    exact Finset.prod_eq_zero hQ (ite_eq_left hQS)

lemma nat_cpow_prod {ι : Type*} (t : Finset ι) (N : ι→ℕ) (s : ℂ) :
    ((∏i∈t,N i : ℕ):ℂ)^s=∏i∈t,(N i:ℂ)^s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Nat.cast_mul,Complex.natCast_mul_natCast_cpow,ih]

lemma primeNormTerm_prod {q : ℕ} (χ : DirichletCharacter ℂ q) (t : Finset PrimeIdeal) (s : ℂ) :
    (∏P∈t,χ (Ideal.absNorm P.val)*(Ideal.absNorm P.val:ℂ)^(-s))=
      χ (Ideal.absNorm (primeProduct t))*(Ideal.absNorm (primeProduct t):ℂ)^(-s) := by
  rw [Finset.prod_mul_distrib]
  simp only [primeProduct,map_prod,Nat.cast_prod]
  congr 1
  simpa only [Nat.cast_prod] using (nat_cpow_prod t (fun P=>Ideal.absNorm P.val) (-s)).symm

def ordinaryPrimeValue {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else χ (Ideal.absNorm I)*(Ideal.absNorm I:ℂ)^(-s)

def dampedPrimeValue {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  if I∈S then 0 else (1-(1:ℂ)/(Ideal.absNorm I:ℂ))*(χ (Ideal.absNorm I)*(Ideal.absNorm I:ℂ)^(-s))

def ordinarySeriesTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  outsideMask S I * baseChangeWeight χ I * CubicEisenstein.fullIdealWeight s I

def dampedSeriesTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ordinarySeriesTerm χ S s I * SixthPowerAverage.totientDensity I

lemma ordinarySeriesTerm_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (I : Ideal ActualEisensteinCubic.O) :
    ordinarySeriesTerm χ S s I = mobiusPrimeCoeff (ordinaryPrimeValue χ S s) I := by
  by_cases hI : Squarefree I
  · rw [mobiusPrimeCoeff,primeValueHom_squarefree _ I hI]
    simp only [ordinaryPrimeValue]
    rw [prod_cut_primes S hS (primeSet I) (fun P => χ (Ideal.absNorm P)*(Ideal.absNorm P:ℂ)^(-s)),
      primeNormTerm_prod,primeProduct_primeSet I hI]
    simp only [ordinarySeriesTerm,baseChangeWeight,CubicEisenstein.fullIdealWeight,ite_eq_right hI.ne_zero]
    ring
  · simp [ordinarySeriesTerm,baseChangeWeight,mobiusPrimeCoeff_nonsquarefree _ I hI,
      moebius_of_not_squarefree hI]

lemma dampedSeriesTerm_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (I : Ideal ActualEisensteinCubic.O) :
    dampedSeriesTerm χ S s I = mobiusPrimeCoeff (dampedPrimeValue χ S s) I := by
  by_cases hI : Squarefree I
  · rw [mobiusPrimeCoeff,primeValueHom_squarefree _ I hI]
    simp only [dampedPrimeValue]
    rw [prod_cut_primes S hS (primeSet I) (fun P => (1-(1:ℂ)/(Ideal.absNorm P:ℂ))*(χ (Ideal.absNorm P)*(Ideal.absNorm P:ℂ)^(-s))),
      Finset.prod_mul_distrib,primeNormTerm_prod,
      prod_primeSet I (fun P => (1-(1:ℂ)/(Ideal.absNorm P:ℂ))),
      primeProduct_primeSet I hI]
    simp only [dampedSeriesTerm,ordinarySeriesTerm,baseChangeWeight,SixthPowerAverage.totientDensity,
      CubicEisenstein.fullIdealWeight,ite_eq_right hI.ne_zero]
    ring
  · simp [dampedSeriesTerm,ordinarySeriesTerm,baseChangeWeight,mobiusPrimeCoeff_nonsquarefree _ I hI,
      moebius_of_not_squarefree hI]

end

open ActualEisensteinCubic

lemma ordinaryPrimeValue_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) :
    ‖ordinaryPrimeValue χ S s P.val‖≤(Ideal.absNorm P.val:ℝ)^(-s.re) := by
  by_cases hP : P.val∈S
  · simp only [ordinaryPrimeValue,ite_eq_left hP,norm_zero]
    positivity
  · simpa only [ordinaryPrimeValue,ite_eq_right hP,primeCharacterTerm,primeNormPower] using
      primeCharacterTerm_norm_le χ P s s.re le_rfl

lemma dampedPrimeValue_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) :
    ‖dampedPrimeValue χ S s P.val‖≤(Ideal.absNorm P.val:ℝ)^(-s.re) := by
  by_cases hP : P.val∈S
  · simp only [dampedPrimeValue,ite_eq_left hP,norm_zero]
    positivity
  · change ‖if P.val∈S then 0 else primeDensity P*primeCharacterTerm χ P s‖≤_
    rw [ite_eq_right hP,norm_mul]
    exact (mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)).trans
      (by simpa using primeCharacterTerm_norm_le χ P s s.re le_rfl)

lemma prime_reciprocal_series_summable (s : ℂ) (hs : 1<s.re) :
    Summable (fun P : PrimeIdeal => (Ideal.absNorm P.val:ℝ)^(-s.re)) := by
  have hh := prime_norm_series_summable (s.re-1) (by linarith)
  simpa only [show 1+(s.re-1)=s.re by ring] using hh

lemma ordinaryPrimeValue_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : Summable (fun P : PrimeIdeal => ‖ordinaryPrimeValue χ S s P.val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => ordinaryPrimeValue_norm_le χ S P s) (prime_reciprocal_series_summable s hs)

lemma dampedPrimeValue_summable {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : Summable (fun P : PrimeIdeal => ‖dampedPrimeValue χ S s P.val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => dampedPrimeValue_norm_le χ S P s) (prime_reciprocal_series_summable s hs)

lemma ordinarySeries_euler {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      ∏'P : PrimeIdeal,(1-ordinaryPrimeValue χ S s P.val) := by
  simp_rw [ordinarySeriesTerm_eq χ S hS]
  exact mobiusPrimeCoeff_euler _ (ordinaryPrimeValue_summable χ S s hs)

lemma dampedSeries_euler {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I)=
      ∏'P : PrimeIdeal,(1-dampedPrimeValue χ S s P.val) := by
  simp_rw [dampedSeriesTerm_eq χ S hS]
  exact mobiusPrimeCoeff_euler _ (dampedPrimeValue_summable χ S s hs)

lemma local_correction_identity {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (P : PrimeIdeal) (s : ℂ) (hs : 0<s.re) :
    (1-dampedPrimeValue χ S s P.val)*(1+correctionTerm χ S P s)=
      1-ordinaryPrimeValue χ S s P.val := by
  rw [correctionTerm_factor χ S P s hs]
  by_cases hP : P.val∈S
  · simp [dampedPrimeValue,ordinaryPrimeValue,hP]
  · simp only [dampedPrimeValue,ordinaryPrimeValue,ite_eq_right hP]
    change (1-primeDensity P*primeCharacterTerm χ P s)*
      ((1-primeCharacterTerm χ P s)/(1-primeDensity P*primeCharacterTerm χ P s))=
      1-primeCharacterTerm χ P s
    exact mul_div_cancel₀ _ (correctionDenominator_ne_zero χ P s hs)

theorem actual_dirichlet_correction {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      eulerCorrection χ S s*(∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I) := by
  rw [ordinarySeries_euler χ S hS s hs,dampedSeries_euler χ S hS s hs,mul_comm]
  have hd : Multipliable (fun P : PrimeIdeal => 1-dampedPrimeValue χ S s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-dampedPrimeValue χ S s P.val‖) by
        simpa only [norm_neg] using dampedPrimeValue_summable χ S s hs)
  have hc := multipliable_one_add_of_summable (correctionTerm_summable χ S s (by linarith))
  change _ = (∏' P : PrimeIdeal, (1-dampedPrimeValue χ S s P.val))*(∏' P : PrimeIdeal, (1+correctionTerm χ S P s))
  rw [←hd.tprod_mul hc]
  apply tprod_congr
  intro P
  exact (local_correction_identity χ S P s (by linarith)).symm

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

lemma normFiber_tsum (a : Ideal ActualEisensteinCubic.O→ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val)=normFiberCoeff a n := by
  let : Fintype {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := ActualEisensteinCubic.O) n).fintype
  rw [tsum_fintype]
  symm
  change (∑I∈FiniteSFactor.fiber n,a I)=_
  apply Finset.sum_bij (fun I hI => (⟨I,FiniteSFactor.mem_fiber.mp hI⟩ : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}))
  · intro I hI
    exact Finset.mem_univ _
  · intro I hI J hJ he
    exact congrArg Subtype.val he
  · intro I hI
    exact ⟨I.val,FiniteSFactor.mem_fiber.mpr I.property,rfl⟩
  · intro I hI
    rfl

lemma idealDirichlet_fiber (a : Ideal ActualEisensteinCubic.O→ℂ) (s : ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val*CubicEisenstein.fullIdealWeight s I.val)=
      LSeries.term (normFiberCoeff a) s n := by
  by_cases hn : n=0
  · subst n
    have hz (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=0}) : CubicEisenstein.fullIdealWeight s I.val=0 := by
      have hI : I.val=0 := Ideal.absNorm_eq_zero_iff.mp I.property
      simp [CubicEisenstein.fullIdealWeight,hI]
    simp only [hz,mul_zero,tsum_zero,LSeries.term_zero]
  · have ht (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}) :
        CubicEisenstein.fullIdealWeight s I.val=(n:ℂ)^(-s) := by
      have hI : I.val≠0 := fun h => hn (by rw [←I.property,h,map_zero])
      rw [CubicEisenstein.fullIdealWeight,ite_eq_right hI,I.property]
    simp_rw [ht]
    rw [tsum_mul_right,normFiber_tsum,LSeries.term_of_ne_zero hn,Complex.cpow_neg,div_eq_mul_inv]

lemma idealDirichlet_summable (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1) (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal ActualEisensteinCubic.O => a I*CubicEisenstein.fullIdealWeight s I) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun I => ?_) (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem idealDirichlet_eq_LSeries (a : Ideal ActualEisensteinCubic.O→ℂ) (ha : ∀I,‖a I‖≤1)
    (s : ℂ) (hs : 1<s.re) :
    (∑'I : Ideal ActualEisensteinCubic.O,a I*CubicEisenstein.fullIdealWeight s I)=LSeries (normFiberCoeff a) s := by
  have hh := (idealDirichlet_summable a ha s hs).hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},
    a I.val*CubicEisenstein.fullIdealWeight s I.val) _ at hh
  simp_rw [idealDirichlet_fiber] at hh
  exact hh.tsum_eq.symm

lemma ordinarySeriesTerm_outside {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : ordinarySeriesTerm χ S s I=
      FiniteSFactor.outsideWeight S (baseChangeWeight χ) I*CubicEisenstein.fullIdealWeight s I := by
  unfold ordinarySeriesTerm outsideMask FiniteSFactor.outsideWeight
  split_ifs <;> simp

lemma dampedSeriesTerm_outside {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (I : Ideal ActualEisensteinCubic.O) : dampedSeriesTerm χ S s I=
      SixthPowerAverage.outsideWeight χ S I*CubicEisenstein.fullIdealWeight s I := by
  unfold dampedSeriesTerm ordinarySeriesTerm outsideMask SixthPowerAverage.outsideWeight
    FiniteSFactor.outsideWeight SixthPowerAverage.weightedMoebius
  split_ifs <;> ring

lemma ordinarySeries_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : (∑'I : Ideal ActualEisensteinCubic.O,ordinarySeriesTerm χ S s I)=
      LSeries (FiniteSFactor.outsideCoeff S (baseChangeWeight χ)) s := by
  simp_rw [ordinarySeriesTerm_outside]
  apply idealDirichlet_eq_LSeries
  intro I
  unfold FiniteSFactor.outsideWeight
  split_ifs
  · exact ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ I
  · simp
  exact hs

lemma dampedSeries_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (s : ℂ) (hs : 1<s.re) : (∑'I : Ideal ActualEisensteinCubic.O,dampedSeriesTerm χ S s I)=
      LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  simp_rw [dampedSeriesTerm_outside]
  exact idealDirichlet_eq_LSeries _ (SixthPowerAverage.outsideWeight_norm_le_one χ S) s hs

theorem actual_LSeries_correction {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 1<s.re) :
    LSeries (FiniteSFactor.outsideCoeff S (baseChangeWeight χ)) s=
      eulerCorrection χ S s*LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  rw [←ordinarySeries_eq_LSeries χ S s hs,←dampedSeries_eq_LSeries χ S s hs]
  exact actual_dirichlet_correction χ S hS s hs

theorem full_LSeries_correction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀P∈S,Prime P) (s : ℂ) (hs : 2<s.re) :
    LSeries (normFiberCoeff (baseChangeWeight χ)) s=
      (CompactMellinBridge.finiteEulerFactor χ S s*eulerCorrection χ S s)*
        LSeries (SixthPowerAverage.weightedCoeff χ S) s := by
  rw [FiniteSFactor.normFiberLSeries_finiteEuler_baseChange χ S hS s hs,
    actual_LSeries_correction χ S hS s (by linarith)]
  exact (mul_assoc _ _ _).symm

theorem eulerCorrection_analytic {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O)) :
    AnalyticOnNhd ℂ (eulerCorrection χ S) {s : ℂ | 0<s.re} :=
  (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).mpr
    (eulerCorrection_differentiableOn χ S)

end SmoothMobiusCorrection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.RowCompletion.ThetaNonvanishing -/

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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical ContDiff Topology
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SixthPowerAverage CompactMellinBridge InitialMeanSquare

theorem corrected_weighted_mellin_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0) (s : ℂ) (hRe : 2<s.re) :
    (χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))=
      mellin W s := by
  rw [weightedCompactMellin_eq_series χ S W hW hs s hRe]
  have hc:=SmoothMobiusCorrection.full_LSeries_correction χ S hS s hRe
  have hp:=normFiber_LSeries_eq_pair_inverse χ (baseChangeChar χ) (baseChangeWeight χ)
    (normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s
  have he:=pair_inverse_euler_identity χ (baseChangeChar χ) s (by linarith : 1<s.re)
  rw [←hp,hc] at he
  calc
    _=((χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        LSeries (weightedCoeff χ S) s))*mellin W s := by ring
    _=mellin W s := by rw [he,one_mul]

theorem dirichlet_open_strip_of_theta_models {q₀ : ℕ} [NeZero q₀]
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (z : ℂ) (hz : (23:ℝ)/24<z.re) (hz1 : z.re<1) : χ.LFunction z≠0 := by
  let W : ℝ→ℂ:=ConcreteCompactWeight.weight z
  have hW : ContDiff ℝ ∞ W:=ConcreteCompactWeight.weight_smooth z
  have hWs : ∀x,x≤1 ∨ 2≤x→W x=0:=ConcreteCompactWeight.weight_support z
  have hM:=weightedCompactMellin_analytic χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels W hW hWs
  have hE:=finiteEulerFactor_analytic χ S hSp ((23:ℝ)/24)
  have hH : AnalyticOnNhd ℂ (SmoothMobiusCorrection.eulerCorrection χ S)
      {s : ℂ | (23:ℝ)/24<s.re} :=
    (SmoothMobiusCorrection.eulerCorrection_analytic χ S).mono (by intro s hs;change 0<s.re;change (23:ℝ)/24<s.re at hs;linarith)
  have hWanalytic:=compact_weight_mellin_analytic W hW hWs ((23:ℝ)/24)
  have hnotboth : χ≠1 ∨ baseChangeChar χ≠1 := by
    by_cases hc : χ=1
    · exact Or.inr (baseChangeChar_ne_one_of_one χ hc)
    · exact Or.inl hc
  have hzneq : z≠1 := by intro he;subst z;norm_num at hz1
  exact (pair_zero_free_of_identity_gt_two χ (baseChangeChar χ) hnotboth
    ((23:ℝ)/24) (by norm_num)
    (fun s=>(finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
      mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
    (mellin W) ((hE.mul hH).mul hM) hWanalytic
    (corrected_weighted_mellin_identity χ S hSp W hW hWs)
    z hz hzneq (ConcreteCompactWeight.weight_mellin_ne_zero z)).1

theorem dirichlet_nonvanishing_of_theta_models {q₀ : ℕ} [NeZero q₀]
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (z : ℂ) (hz : (23:ℝ)/24<z.re) (hpole : ¬(χ=1 ∧ z=1)) : χ.LFunction z≠0 := by
  by_cases hz1 : z.re<1
  · exact dirichlet_open_strip_of_theta_models χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels z hz hz1
  · exact ShortDraft.dirichlet_target_of_one_le_re q₀ χ z (le_of_not_gt hz1) hpole

theorem dirichletTarget_of_theta_models
    (hmodels : ∀(q₀ : ℕ) [NeZero q₀] (χ : DirichletCharacter ℂ q₀),
      ∃S : Finset (Ideal ActualEisensteinCubic.O),fixedBadPrimes⊆S ∧ (∀P∈S,Prime P) ∧
      ∃ρ q levelBound : ℝ,0<ρ ∧ 1<q ∧ 1≤levelBound ∧
        HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound) :
    ShortDraft.DirichletTarget := by
  intro q₀ _ χ z hz hpole
  obtain ⟨S,hbad,hSp,ρ,q,level,hρ,hq,hl,hm⟩:=hmodels q₀ χ
  exact dirichlet_nonvanishing_of_theta_models χ S hbad hSp ρ q level hρ hq hl hm z hz hpole

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace QuadraticAllOddCRT

section
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open CanonicalQuadraticSieve hiding O

local instance : (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O).IsMaximal:=lambdaIdeal_maximal

lemma lambda_odd : ringChar (ActualEisensteinCubic.O⧸Ideal.span {lambda})≠2:=
  ActualEisensteinSieve.lambda_residue_odd

lemma lambda_residue : residue lambda=((3:ZMod 4),(1:ZMod 4)) := by
  have h : lambda=eval (-1) 1 := by
    change (ActualEisensteinCubic.omega-1:ActualEisensteinCubic.O)=((-1:ℤ):ActualEisensteinCubic.O)+((1:ℤ):ActualEisensteinCubic.O)*ActualEisensteinCubic.omega
    push_cast
    ring
  rw [h,residue_eval]
  decide

lemma lambda_quadratic_ray_ne_zero : quadraticRayValue (residue lambda)≠0 := by
  apply quadraticRayValue_ne_zero_of_odd
  rw [lambda_residue]
  decide

lemma character_lambda_primary (p : ActualEisensteinCubic.O) (hp : lambda^2∣p-1) :
    character (Ideal.span {lambda}) (Ideal.Quotient.mk (Ideal.span {lambda}) p)=1 := by
  have hm : Ideal.Quotient.mk (Ideal.span {lambda}) p=Ideal.Quotient.mk (Ideal.span {lambda}) (1:ActualEisensteinCubic.O) :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hp))
  rw [hm,map_one,map_one]

def lambdaQuadraticRay (r : EisensteinEPrimaryPhase.Coord) : ℂ:=
  quadraticRayValue (EisensteinEPrimaryPhase.mul (residue lambda) r)/
    (quadraticRayValue (residue lambda)*quadraticRayValue r)

theorem character_lambda_eq_ray (p : ActualEisensteinCubic.O) (hp : p≠0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2)
    (hprimary : lambda^2∣p-1) :
    character (Ideal.span {p}) (Ideal.Quotient.mk (Ideal.span {p}) lambda)=
      lambdaQuadraticRay (residue p) := by
  have hcop : IsCoprime (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O) (Ideal.span {p}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro he
    apply hg
    rw [←he]
    exact Ideal.subset_span (by simp)
  have h:=quadratic_ray_cross lambda p PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero hp hcop lambda_odd hc
  rw [character_lambda_primary p hprimary,one_mul] at h
  have hodd : EisensteinEPrimaryPhase.odd (residue p) := by
    have hn : ‖quadraticRayValue (residue p)‖=1 := by
      let pp : Unit→ActualEisensteinCubic.O:=fun _=>p
      have hpp : ∀i,pp i≠0:=fun _=>hp
      have hcp : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})):=by
        intro i j hij
        exact False.elim (hij (Subsingleton.elim _ _))
      have hh:=FiniteGaussPhase.norm_canonicalProductGauss pp hpp hcp (fun _=>hg) (fun _=>hc)
        (fun _=>3) (by intro i;decide) (by intro i;decide)
      rw [QuadraticGaussRay.canonicalProductGauss_three_eq_rayValue pp hpp hcp (fun _=>hg) (fun _=>hc)] at hh
      simpa [pp] using hh
    exact QuadraticUnitInvariance.odd_of_quadraticRayValue_norm_eq_one _ hn
  unfold lambdaQuadraticRay
  rw [←residue_mul]
  apply (eq_div_iff (mul_ne_zero lambda_quadratic_ray_ne_zero (quadraticRayValue_ne_zero_of_odd _ hodd))).mpr
  simpa only [mul_assoc] using h.symm

end

open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega

def lambdaQuadraticTable (r : EisensteinEPrimaryPhase.Coord) : ℤ :=
  if ¬EisensteinEPrimaryPhase.odd r then 0
  else if r∈({(0,1),(1,0),(1,2),(1,3),(2,3),(3,3)} : Finset EisensteinEPrimaryPhase.Coord)
    then 1 else -1

lemma lambdaQuadraticTable_mul (r s : EisensteinEPrimaryPhase.Coord) :
    lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
      lambdaQuadraticTable r*lambdaQuadraticTable s := by
  have h : ∀r s : EisensteinEPrimaryPhase.Coord,
      lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
        lambdaQuadraticTable r*lambdaQuadraticTable s := by decide
  exact h r s

lemma lambdaQuadraticTable_eq_ray (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    (lambdaQuadraticTable r:ℂ)=lambdaQuadraticRay r := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hn3 : (-3 : ZMod 4) = 1 := by decide
  rcases r with ⟨a,b⟩
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [lambdaQuadraticTable,lambdaQuadraticRay,lambda_residue,EisensteinEPrimaryPhase.mul,
      EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      Prod.mk.injEq,hcmp,hn3,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      ZMod.val_neg_one,ZMod.val_mul,ZMod.val_add,ZMod.val_sub,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_three]
  all_goals
    field_simp [Complex.I_ne_zero]
    change (-2 : ℂ) = Complex.I * (Complex.I ^ (1 : ℤ) + Complex.I ^ (2 - 1 : ℤ))
    norm_num [Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]

def lambdaQuadraticCharacter : ActualEisensteinCubic.O→*ℂ where
  toFun n:=(lambdaQuadraticTable (residue n):ℂ)
  map_one' := by
    have h : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0):=by
      have h1 : (1:ActualEisensteinCubic.O)=eval 1 0:=by simp [eval]
      rw [h1,residue_eval]
      norm_num
    rw [h]
    exact_mod_cast (show lambdaQuadraticTable ((1:ZMod 4),0)=1 from by decide)
  map_mul' x y := by
    rw [residue_mul,lambdaQuadraticTable_mul]
    push_cast
    rfl

lemma lambdaQuadraticCharacter_periodic (x y : ActualEisensteinCubic.O) (h : (4:ActualEisensteinCubic.O)∣x-y) :
    lambdaQuadraticCharacter x=lambdaQuadraticCharacter y := by
  change (lambdaQuadraticTable (residue x):ℂ)=(lambdaQuadraticTable (residue y):ℂ)
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y h]

end QuadraticAllOddCRT

open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open CubicJacobiGlobal hiding O
open QuadraticAllOddCRT
open CanonicalQuadraticSieve hiding O
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma localRowValue_square (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue x P^2=eisEmbedding (primeValue P x) := by
  unfold localRowValue primeValue
  split_ifs with h
  · let : P.IsMaximal:=h.1
    change (actualSextic P h.2 (Ideal.Quotient.mk P x))^2=_
    rw [←MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),canonicalSextic_pow_two]
    rfl
  · simp

theorem idealRowHom_square (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom x I ^2=eisEmbedding (idealSymbol I x) := by
  have hm (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue x)).prod^2=eisEmbedding ((s.map (fun P=>primeValue P x)).prod) := by
    induction s using Multiset.induction_on with
    | empty=>simp
    | @cons P s ih=>
      simp only [Multiset.map_cons,Multiset.prod_cons,mul_pow,map_mul,localRowValue_square,ih]
  by_cases hI : I=0
  · subst I
    simp only [map_zero,idealSymbol_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · change (if I=0 then 0 else _)^2=eisEmbedding (if I=0 then 0 else _)
    simp only [ite_eq_right hI]
    exact hm _

lemma actualSextic_cube_quadratic (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    actualSextic P hg^3=character P := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ,hχ3⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧
      χ^3=(quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ActualEisensteinCubic.O) :=
    ⟨_,rfl,(sexticChar_powers P hg).2.1⟩
  rw [hχ,MulChar.ringHomComp_pow,hχ3]
  ext x
  change eisEmbedding ((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ActualEisensteinCubic.O)=((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ℂ)
  simp

lemma idealRowHom_lambda_prime_cube (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : lambda^2∣p-1) (hs : Supported (Ideal.span {p})) :
    idealRowHom lambda (Ideal.span {p})^3=lambdaQuadraticCharacter p := by
  let : (Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmem : Ideal.span {p}∈normalizedFactors (Ideal.span {p}) :=
    (Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩
  obtain ⟨hg,hc⟩:=hs.2 _ hmem
  rw [idealRowHom_prime lambda _ hg]
  change (actualSextic _ hg (Ideal.Quotient.mk _ lambda))^3=_
  rw [←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
  have he:=character_lambda_eq_ray p hp.ne_zero hg hc hprimary
  have ho:=ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p
  have hs' := (supported_span_iff p).mp hs
  change character _ (Ideal.Quotient.mk _ lambda)=_
  rw [he]
  exact (lambdaQuadraticTable_eq_ray _ (ho.mpr hs'.2)).symm

theorem idealRowHom_lambda_cube (y : ActualEisensteinCubic.O) (hy : lambda^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lambda (Ideal.span {y})^3=lambdaQuadraticCharacter y := by
  have hy0 : y≠0:=by
    intro he
    apply hs.1
    simp [he]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization y hy0 hy
  rw [←hprod] at hs ⊢
  clear hprod hy hy0 y
  induction s using Multiset.induction_on with
  | empty=>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_pow]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀q∈s,Prime q ∧ lambda^2∣q-1:=
      fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,mul_pow,
      idealRowHom_lambda_prime_cube p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

theorem idealRowHom_lambda_formula (y : ActualEisensteinCubic.O) (hy : lambda^2∣y-1)
    (hs : Supported (Ideal.span {y})) :
    idealRowHom lambda (Ideal.span {y})=
      eisEmbedding (CubicRamified.linearRay 1 0 y)^2*lambdaQuadraticCharacter y := by
  have htwo:=idealRowHom_square lambda (Ideal.span {y})
  change idealRowHom lambda (Ideal.span {y})^2=eisEmbedding (symbol lambda y) at htwo
  rw [CubicRamified.symbol_lambda_eq_linearRay y hy] at htwo
  have hthree:=idealRowHom_lambda_cube y hy hs
  have hq : lambdaQuadraticCharacter y^2=1 := by
    change (lambdaQuadraticTable (ActualEisensteinCoordinates.residue y):ℂ)^2=1
    have ho := ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd y |>.mpr ((supported_span_iff y).mp hs).2
    unfold lambdaQuadraticTable
    rw [ite_eq_right (not_not.mpr ho)]
    split_ifs <;> norm_num
  have hsix : idealRowHom lambda (Ideal.span {y})^6=1 := by
    calc
      _ = (idealRowHom lambda (Ideal.span {y})^3)^2:=by ring
      _ = 1:=by rw [hthree,hq]
  calc
    _ = (idealRowHom lambda (Ideal.span {y})^2)^2*(idealRowHom lambda (Ideal.span {y})^3):=by
      calc
        _ = idealRowHom lambda (Ideal.span {y})*idealRowHom lambda (Ideal.span {y})^6:=by rw [hsix,mul_one]
        _ = _:=by ring
    _ = _:=by rw [htwo,hthree]

theorem idealRowHom_lambda_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hx : lambda^2∣x-1) (hy : lambda^2∣y-1)
    (hsx : Supported (Ideal.span {x})) (hsy : Supported (Ideal.span {y}))
    (hxy : (36:ActualEisensteinCubic.O)∣x-y) :
    idealRowHom lambda (Ideal.span {x})=idealRowHom lambda (Ideal.span {y}) := by
  rw [idealRowHom_lambda_formula x hx hsx,idealRowHom_lambda_formula y hy hsy,
    CubicRamified.linearRay_congr_mod_nine 1 0 x y hx hy ((show (9:ActualEisensteinCubic.O)∣36 from ⟨4,by norm_num⟩).trans hxy),
    lambdaQuadraticCharacter_periodic x y ((show (4:ActualEisensteinCubic.O)∣36 from ⟨9,by norm_num⟩).trans hxy)]

end CanonicalRowCompletion

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma cuspRemainder_absolute_chart (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (hz : ‖z‖≤1)
    (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖)≤eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℝ := fun r => ‖cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,R r≤G (f r) := by
    intro r
    simpa only [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul] using
      translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0 r
  have hr : Summable R := (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  refine ⟨hr,?_⟩
  have hsum : (∑'r,R r)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem cuspRemainder_absolute_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => ‖cuspRemainderProfile a b s (cosetHeight r w)‖) ∧
    (∑'r : CuspCosets,‖cuspRemainderProfile a b s (cosetHeight r w)‖)≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact cuspRemainder_absolute_chart a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainder_aux_norm (b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) (hvb : v≤b) :
    ‖cuspRemainderProfile (b+1) (b+2) s v‖=v^s.re := by
  rw [cuspRemainderProfile,cuspSeedProfile_zero (b+1) (b+2) s v (by linarith) (by linarith),
    sub_zero,positiveHeightPower_eq_cpow s v hv,Complex.norm_cpow_eq_rpow_re_of_pos hv]

lemma cuspRemainder_row_scaled_deriv_aux_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (fun q => cuspRemainderProfile a b s (rowHeight u q)) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight u p)‖ := by
  have hh := rowHeight_pos u hu p hp
  by_cases hb : rowHeight u p≤b
  · rw [cuspRemainder_aux_norm b s _ hh hb]
    exact cuspRemainder_row_scaled_deriv_bound a b s C hC u hu p hp j
  · have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
      (cuspRemainderProfile_contDiffAt a b s) u hu p hp j).1
    rw [hd.deriv,cuspRemainderProfile_deriv_zero a b s _ hab hh (lt_of_not_ge hb)]
    simp only [zero_mul,mul_zero,norm_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg s) hC0) (norm_nonneg _)

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def weightedHeightProfile (F : ℝ→ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma weightedHeightProfile_axis_differentiable (F : ℝ→ℂ)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (weightedHeightProfile F r) p j) (p j) :=
  ((rowProfile_axis_derivatives F hF (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1.const_mul _).differentiableAt

lemma heightPoincare_axis_termwise (F : ℝ→ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) ∧
    HasDerivAt (axisSlice (heightPoincareField F) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) (p j) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [ContinuousAt,Function.update_eq_self] using
      ((continuous_axis_update p j).continuousAt (x := p j))
  have hn : ∀ᶠt in 𝓝 (p j),Function.update p j t∈U := ht (hU.mem_nhds hpU)
  have hz (r : CuspCosets) (hr : r∉S) :
      deriv (axisSlice (weightedHeightProfile F r) p j) (p j)=0 := by
    have he : axisSlice (weightedHeightProfile F r) p j=ᶠ[𝓝 (p j)] (fun _ => 0) := by
      filter_upwards [hn] with t ht
      change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
      rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]
    exact he.deriv_eq.trans (deriv_const _ _)
  refine ⟨summable_of_ne_finset_zero hz,?_⟩
  rw [tsum_eq_sum hz]
  have hd := HasDerivAt.sum (u := S) (fun r hr =>
    (weightedHeightProfile_axis_differentiable F hF r p hp j).hasDerivAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  simp only [Finset.sum_apply]
  change (∑'r,weightedHeightProfile F r (Function.update p j t))=
    ∑r∈S,weightedHeightProfile F r (Function.update p j t)
  apply tsum_eq_sum
  intro r hr
  change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
  rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]

lemma weightedRemainder_axis_deriv (a b : ℝ) (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      deriv (axisSlice (smoothSummand s r) p j) (p j)-
        deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  have he : axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j=ᶠ[𝓝 (p j)]
      (fun t => axisSlice (smoothSummand s r) p j t-
        axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j t) := by
    filter_upwards [hn] with t ht
    simp only [axisSlice,weightedHeightProfile,cuspRemainderProfile,smoothSummand]
    rw [rowSmoothPower_eq_height s _ (embeddedRow_ne_zero r) _ ht,
      positiveHeightPower_eq_cpow s _ (rowHeight_pos _ (embeddedRow_ne_zero r) _ ht)]
    ring
  rw [he.deriv_eq]
  exact deriv_sub (smooth_axis_differentiable s r p hp j)
    (weightedHeightProfile_axis_differentiable _ (cuspSeedProfile_contDiffAt a b s) r p hp j)

def eisensteinRemainderField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  smoothEisenstein s p-smoothCuspSeedField a b s p

theorem eisensteinRemainder_axis_termwise (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) ∧
    HasDerivAt (axisSlice (eisensteinRemainderField a b s) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)) (p j) := by
  have hE := eisenstein_axis_termwise s hs p hp j
  have hS := heightPoincare_axis_termwise (cuspSeedProfile a b s)
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp j
  have hcoeff : (∑'r,deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))=
      (∑'r,deriv (axisSlice (smoothSummand s r) p j) (p j))-
        ∑'r,deriv (axisSlice (weightedHeightProfile (cuspSeedProfile a b s) r) p j) (p j) := by
    simp_rw [weightedRemainder_axis_deriv a b s _ p hp j]
    exact hE.1.tsum_sub hS.1
  refine ⟨(hE.1.sub hS.1).congr (fun r => (weightedRemainder_axis_deriv a b s r p hp j).symm),?_⟩
  rw [hcoeff]
  apply (hE.2.2.1.sub hS.2).congr_of_eventuallyEq
  have hn : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    simpa only [Function.comp_apply,Function.update_eq_self] using hp
  filter_upwards [hn] with t ht
  change smoothEisenstein s _-smoothCuspSeedField a b s _=
    smoothEisenstein s _-heightPoincareField (cuspSeedProfile a b s) _
  rw [smoothCuspSeedField_eq a b s ha hab _ ht]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

namespace CubicEisenstein

lemma weightedRemainder_scaled_deriv_bound (a b : ℝ) (hab : a<b) (s : ℂ)
    (C : ℝ) (hC0 : 0≤C) (hC : ∀v,|v*deriv (cuspTransition a b) v|≤C)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)‖≤
      (‖s‖+C)*‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖ := by
  let g : SpatialCoordinates→ℂ:=fun q => cuspRemainderProfile a b s (rowHeight (embeddedRow r) q)
  have hd := (rowProfile_axis_derivatives (cuspRemainderProfile a b s)
    (cuspRemainderProfile_contDiffAt a b s) (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1
  have hw := hd.const_mul (cosetCharacter r)⁻¹
  have he : deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j)=
      (cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j) := by
    change deriv (fun t => (cosetCharacter r)⁻¹*axisSlice g p j t) (p j)=_
    rw [hw.deriv,hd.deriv]
  rw [he]
  calc
    ‖(p 2:ℂ)*((cosetCharacter r)⁻¹*deriv (axisSlice g p j) (p j))‖
      = ‖(cosetCharacter r)⁻¹*((p 2:ℂ)*deriv (axisSlice g p j) (p j))‖ := by congr 1; ring
    _ = ‖(p 2:ℂ)*deriv (axisSlice g p j) (p j)‖ := by
      rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul]
    _ ≤ _ := cuspRemainder_row_scaled_deriv_aux_bound a b hab s C hC0 hC _ (embeddedRow_ne_zero r) p hp j

theorem eisensteinRemainder_scaled_axis_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (eisensteinRemainderField a b s) p j) (p j)‖≤B := by
  obtain ⟨C,hC0,hC⟩ := cuspTransition_euler_bounded a b hab
  refine ⟨(‖s‖+C)*eisensteinRemainderBound (b+2) s,
    mul_nonneg (add_nonneg (norm_nonneg s) hC0) (eisensteinRemainderBound_nonneg _ _),?_⟩
  intro p hp j
  have hA : Summable (fun r : CuspCosets =>
      ‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖) ∧
      (∑'r : CuspCosets,‖cuspRemainderProfile (b+1) (b+2) s (rowHeight (embeddedRow r) p)‖)≤
        eisensteinRemainderBound (b+2) s := by
    simpa only [cosetHeight_upperPoint_rowHeight] using
      cuspRemainder_absolute_bound (b+1) (b+2) (by linarith) (by linarith) s hs
        (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)
  have hB := hA.1.mul_left (‖s‖+C)
  have hb (r : CuspCosets) := weightedRemainder_scaled_deriv_bound a b hab s C hC0 hC r p hp j
  have hnorm := hB.of_nonneg_of_le (fun r => norm_nonneg
    ((p 2:ℂ)*deriv (axisSlice (weightedHeightProfile (cuspRemainderProfile a b s) r) p j) (p j))) hb
  have ht := eisensteinRemainder_axis_termwise a b ha hab s (by linarith) p hp j
  rw [ht.2.deriv,←tsum_mul_left]
  apply (norm_tsum_le_tsum_norm hnorm).trans
  apply (Summable.tsum_le_tsum hb hnorm hB).trans
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hA.2 (add_nonneg (norm_nonneg s) hC0)

def kernelEisensteinRemainder (a b : ℝ) (s : ℂ) (hs : 2<s.re) : KernelQuotient→ℂ :=
  fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q

lemma kernelEisensteinRemainder_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelEisensteinRemainder a b s hs) :=
  (kernelQuotientEisenstein_contMDiff s hs).sub (kernelQuotientSeed_contMDiff a b s ha hab)

lemma kernelEisensteinRemainder_euclidean_smooth (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun q => kernelEisensteinRemainder a b s hs (kernelEuclideanProjection q)) p :=
  ((((kernelEisensteinRemainder_smooth a b ha hab s hs).comp kernelProjection_contMDiff)
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

lemma kernelEisensteinRemainder_euclidean_eq (a b : ℝ) (s : ℂ) (hs : 2<s.re)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p)=eisensteinRemainderField a b s p.ofLp := by
  unfold kernelEisensteinRemainder kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp,kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint]
  unfold eisensteinRemainderField
  rw [smoothEisenstein_eq_actual s p.ofLp hp,smoothCuspSeedField,dite_eq_left hp]
  simp only [mul_comm Complex.I]
  rfl

theorem kernelEisensteinRemainder_scaled_fderiv_bound (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃B : ℝ,0≤B ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => kernelEisensteinRemainder a b s (by linarith)
        (kernelEuclideanProjection q)) p (euclideanCoordinateVector j)‖≤B := by
  obtain ⟨B,hB,hbound⟩ := eisensteinRemainder_scaled_axis_bound a b ha hab s hs
  refine ⟨B,hB,?_⟩
  intro p hp j
  let f : EuclideanSpatial→ℂ:=fun q => kernelEisensteinRemainder a b s (by linarith) (kernelEuclideanProjection q)
  have hf : ∀q,0<q 2→ ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s (by linarith)
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s (by linarith) (WithLp.toLp 2 q) hq
  have heq := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤B
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,heq.deriv_eq]
  exact hbound p.ofLp hp j

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ConjugateLevelAction -/

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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

lemma globalKubotaKernel_conjugate_mem (M : levelThree) (N : globalKubotaKernel) :
    (M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel := by
  obtain ⟨n,hn,hnval⟩ := N.property
  change (n:SL(2,ActualEisensteinCubic.O))=(N:SL(2,ActualEisensteinCubic.O)) at hnval
  refine ⟨M*n*M⁻¹,?_,?_⟩
  · change finiteCubicMultiplier (M*n*M⁻¹)=1
    change finiteCubicMultiplier n=1 at hn
    simp only [map_mul,map_inv,hn,mul_one,mul_inv_cancel]
  · change (M:SL(2,ActualEisensteinCubic.O))*(n:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹=_
    rw [hnval]

def kernelConjugate (M : levelThree) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹,globalKubotaKernel_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelThree)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelThree)⁻¹,globalKubotaKernel_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]

lemma kernelConjugate_coe (M : levelThree) (N : globalKubotaKernel) :
    (kernelConjugate M N : SL(2,ActualEisensteinCubic.O))=(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹ := rfl

lemma level_action_respects_kernel (M : levelThree) (u v : HyperbolicSpace)
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (complexMatrix M • u) (complexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹) •
    (complexMatrix M • u)=complexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  change complexMatrix M • (integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) •
    ((complexMatrix M)⁻¹ • (complexMatrix M • u)))=_
  rw [inv_smul_smul,hN]

def kernelLevelAction (M : levelThree) : KernelQuotient→KernelQuotient :=
  Quotient.map' (fun w => complexMatrix M • w) (level_action_respects_kernel M)

lemma kernelLevelAction_mk (M : levelThree) (w : HyperbolicSpace) :
    kernelLevelAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • w) := rfl

lemma kernelLevelAction_one (q : KernelQuotient) : kernelLevelAction 1 q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (complexMatrix 1 • w)=integralOrbitProjection globalKubotaKernel w
    rw [map_one,one_smul]

lemma kernelLevelAction_mul (M N : levelThree) (q : KernelQuotient) :
    kernelLevelAction (M*N) q=kernelLevelAction M (kernelLevelAction N q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (complexMatrix (M*N) • w)=
      integralOrbitProjection globalKubotaKernel (complexMatrix M • (complexMatrix N • w))
    rw [map_mul,mul_smul]

lemma kernelLevelAction_continuous (M : levelThree) : Continuous (kernelLevelAction M) :=
  (continuous_hyperbolic_action (complexMatrix M)).quotient_map' (level_action_respects_kernel M)

def kernelLevelHomeomorph (M : levelThree) : KernelQuotient ≃ₜ KernelQuotient where
  toFun := kernelLevelAction M
  invFun := kernelLevelAction M⁻¹
  left_inv q := by rw [←kernelLevelAction_mul,inv_mul_cancel,kernelLevelAction_one]
  right_inv q := by rw [←kernelLevelAction_mul,mul_inv_cancel,kernelLevelAction_one]
  continuous_toFun := kernelLevelAction_continuous M
  continuous_invFun := kernelLevelAction_continuous M⁻¹

lemma kernelLevelAction_eisenstein (M : levelThree) (s : ℂ) (hs : 2<s.re)
    (q : KernelQuotient) :
    kernelQuotientEisenstein s hs (kernelLevelAction M q)=
      complexCharacter M*kernelQuotientEisenstein s hs q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact hyperbolicEisenstein_automorphy M s hs w

lemma kernelLevelAction_seed (M : levelThree) (a b : ℝ) (s : ℂ) (q : KernelQuotient) :
    kernelQuotientSeed a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeed_automorphy a b s M w

lemma kernelLevelAction_defect (M : levelThree) (a b : ℝ) (s : ℂ) (q : KernelQuotient) :
    kernelQuotientDefect a b s (kernelLevelAction M q)=complexCharacter M*kernelQuotientDefect a b s q := by
  induction q using Quotient.inductionOn with
  | _ w => exact smoothCuspSeedDefect_automorphy a b s M w

lemma kernelLevelAction_fundamentalDomain (M : levelThree) :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => complexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree).image_of_equiv (MulAction.toPerm (complexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (complexMatrix M)).symm hyperbolicVolume hyperbolicVolume from by
      exact (measurePreserving_smul (complexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelConjugate M⁻¹).toEquiv
  intro N w
  change complexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelThree)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelThree)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) • (complexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change complexMatrix M • (((complexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O))*
    ((complexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]

lemma kernelLevelAction_measurePreserving (M : levelThree) :
    MeasurePreserving (kernelLevelAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelLevelAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => complexMatrix M • w
  have hmap := (measurePreserving_smul (complexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (complexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelLevelAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelLevelAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelLevelAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelLevelAction_fundamentalDomain M)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota

def kernelLevelPullback (M : levelThree) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelLevelAction M) (kernelLevelAction_measurePreserving M)

lemma kernelLevelPullback_ae_eq (M : levelThree) (F : KernelQuotientL2) :
    kernelLevelPullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelLevelAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelLevelAction_measurePreserving M)

lemma kernelLevelPullback_one (F : KernelQuotientL2) : kernelLevelPullback 1 F=F := by
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq 1 F] with q hq
  simpa only [kernelLevelAction_one] using hq

lemma kernelLevelPullback_comp (M N : levelThree) (F : KernelQuotientL2) :
    kernelLevelPullback M (kernelLevelPullback N F)=kernelLevelPullback (N*M) F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelLevelPullback_ae_eq N F)
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M (kernelLevelPullback N F),hcomp,
    kernelLevelPullback_ae_eq (N*M) F] with q hp hn hnm
  rw [hp,hnm]
  exact hn.trans (congrArg F (kernelLevelAction_mul N M q).symm)

lemma kernelLevelPullback_surjective (M : levelThree) : Function.Surjective (kernelLevelPullback M) := by
  intro F
  refine ⟨kernelLevelPullback M⁻¹ F,?_⟩
  rw [kernelLevelPullback_comp,inv_mul_cancel,kernelLevelPullback_one]

def kernelLevelUnitary (M : levelThree) : KernelQuotientL2 ≃ₗᵢ[ℂ] KernelQuotientL2 :=
  LinearIsometryEquiv.ofSurjective (kernelLevelPullback M) (kernelLevelPullback_surjective M)

lemma kernelLevelUnitary_apply (M : levelThree) (F : KernelQuotientL2) :
    kernelLevelUnitary M F=kernelLevelPullback M F := rfl

lemma kernelLevelPullback_defect (M : levelThree) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelLevelPullback M (kernelL2Defect a b ha hab s)=
      complexCharacter M • kernelL2Defect a b ha hab s := by
  have hdef := kernelL2Defect_ae_eq a b ha hab s
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hdef
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M (kernelL2Defect a b ha hab s),hcomp,hdef,
    Lp.coeFn_smul (complexCharacter M) (kernelL2Defect a b ha hab s)] with q hp hc hd hs
  change _=complexCharacter M * kernelL2Defect a b ha hab s q at hs
  rw [hp,hs,hd]
  exact hc.trans (kernelLevelAction_defect M a b s q)

lemma kernelLevelPullback_of_remainder_ae (M : levelThree) (a b : ℝ) (s : ℂ)
    (hs : 2<s.re) (F : KernelQuotientL2)
    (hF : F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M F=complexCharacter M • F := by
  have hcomp := (kernelLevelAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hF
  apply Lp.ext
  filter_upwards [kernelLevelPullback_ae_eq M F,hcomp,hF,Lp.coeFn_smul (complexCharacter M) F]
    with q hp hc hf hsmul
  change _=complexCharacter M*F q at hsmul
  rw [hp,hsmul,hf]
  dsimp only [Function.comp_def] at hc
  rw [hc,kernelLevelAction_eisenstein,kernelLevelAction_seed,mul_sub]

lemma kernelCorrection_character_of_initial_overlap (M : levelThree) (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    ∀s∈cuspUpperParameterRegion,
      kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s)=
        complexCharacter M • kernelEisensteinL2Correction a b ha hab s := by
  have hc : AnalyticOnNhd ℂ (kernelEisensteinL2Correction a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hl : AnalyticOnNhd ℂ (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      cuspUpperParameterRegion := by
    intro s hs
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelLevelPullback M).toContinuousLinearMap _).comp_of_eq (hc s hs) rfl
  have hr : AnalyticOnNhd ℂ (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s)
      cuspUpperParameterRegion := by
    intro s hs
    exact (hc s hs).const_smul (c := complexCharacter M)
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelLevelPullback M (kernelEisensteinL2Correction a b ha hab s))
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s => complexCharacter M • kernelEisensteinL2Correction a b ha hab s) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLevelPullback_of_remainder_ae M a b s (by linarith [hs.1]) _ (hoverlap s hs.1 hs.2)
  exact hl.eqOn_of_preconnected_of_eventuallyEq hr cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) hevent

lemma thetaApproach_tendsto_complex_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hh : Continuous (fun t : ℝ => (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I) := by fun_prop
    have ht := (hh.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using ht
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    change (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I≠(4/3:ℂ)
    intro he
    have him := congrArg Complex.im he
    simp at him
    linarith

lemma kernelEisensteinResidueVector_character_of_initial_overlap (M : levelThree) (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
      complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  have hlim := (kernelEisensteinResidueVector_limit a b ha hab).comp thetaApproach_tendsto_complex_punctured
  have hl := (kernelLevelPullback M).continuous.continuousAt.tendsto.comp hlim
  have hr := hlim.const_smul (complexCharacter M)
  have hevent :
      (fun t : ℝ => kernelLevelPullback M
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)]
      (fun t : ℝ => complexCharacter M •
        (((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
          kernelEisensteinL2Correction a b ha hab ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I∈cuspUpperParameterRegion := by
      simp only [cuspUpperParameterRegion,Set.mem_ofPred_eq,Complex.add_re,Complex.add_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
        Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
      norm_num
      exact ht
    rw [map_smul,kernelCorrection_character_of_initial_overlap M a b ha hab hoverlap _ hs]
    exact smul_comm _ _ _
  exact tendsto_nhds_unique_of_eventuallyEq hl hr hevent

lemma kernelCuspAverageFamily_eq_of_initial_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspAverageFamily a b ha hab s=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hrestr := ae_restrict_of_ae hcorrected (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  rw [kernelCuspAverageFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact hw.trans (kernelQuotientEisenstein_mk s hs w)

lemma kernelEisensteinResidueVector_nonzero_character_of_initial_overlap (a b : ℝ)
    (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ, ∀hs : 4<s.re, 0<s.im →
      kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q) :
    kernelEisensteinResidueVector a b ha hab≠0 ∧
      ∀M : levelThree,kernelLevelPullback M (kernelEisensteinResidueVector a b ha hab)=
        complexCharacter M • kernelEisensteinResidueVector a b ha hab := by
  constructor
  · apply kernelEisensteinResidueVector_ne_zero_of_overlap a b ha hab
    intro s hs hi
    exact kernelCuspAverageFamily_eq_of_initial_overlap a b ha hab s (by linarith) (hoverlap s hs hi)
  · intro M
    exact kernelEisensteinResidueVector_character_of_initial_overlap M a b ha hab hoverlap

end CubicEisenstein

open scoped BigOperators
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open EisensteinEPrimaryPhase (Coord odd)

def quadraticRayExponent (r : Coord) : ZMod 4 :=
  if r∈({(0,1),(0,3),(1,0),(1,1),(3,0),(3,3)} : Finset Coord) then 0
  else if r∈({(1,2),(1,3),(2,3)} : Finset Coord) then 1 else 3

def fourthRoot (a : ZMod 4) : ℂ := Complex.I ^(a.val:ℤ)

lemma fourthRoot_add (a b : ZMod 4) : fourthRoot (a+b)=fourthRoot a*fourthRoot b := by
  unfold fourthRoot
  rw [←zpow_add₀ Complex.I_ne_zero]
  apply I_zpow_eq_of_mod_four
  push_cast
  simp

lemma quadraticRayValue_eq_fourthRoot (r : Coord) (hr : odd r) :
    quadraticRayValue r=fourthRoot (quadraticRayExponent r) := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases r with ⟨a,b⟩
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [quadraticRayExponent,fourthRoot,EisensteinEPrimaryPhase.odd,
      quadraticRayValue,breveGaussianFourTerms_formula,Prod.mk.injEq,hcmp,
      ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf

def quadraticRaySign (r s : Coord) : ℤ :=
  if odd r ∧ odd s then
    if quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s then 1 else -1
  else 0

lemma quadraticRaySign_mul_left (r s t : Coord) :
    quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
      quadraticRaySign r t*quadraticRaySign s t := by
  have h : ∀r s t : Coord,
      quadraticRaySign (EisensteinEPrimaryPhase.mul r s) t=
        quadraticRaySign r t*quadraticRaySign s t := by decide
  exact h r s t

lemma quadraticRaySign_mul_right (r s t : Coord) :
    quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
      quadraticRaySign r s*quadraticRaySign r t := by
  have h : ∀r s t : Coord,
      quadraticRaySign r (EisensteinEPrimaryPhase.mul s t)=
        quadraticRaySign r s*quadraticRaySign r t := by decide
  exact h r s t

lemma quadraticRaySign_symm (r s : Coord) : quadraticRaySign r s=quadraticRaySign s r := by
  have h : ∀r s : Coord,quadraticRaySign r s=quadraticRaySign s r := by decide
  exact h r s

lemma quadraticRaySign_sq (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRaySign r s^2=1 := by
  unfold quadraticRaySign
  rw [ite_eq_left ⟨hr,hs⟩]
  split_ifs <;> norm_num

lemma quadraticRaySign_exponent (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by
  have h : ∀r s : Coord,odd r → odd s →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
        (if quadraticRaySign r s=1 then 0 else 2)+quadraticRayExponent r+quadraticRayExponent s := by decide
  exact h r s hr hs

lemma quadraticRaySign_root (r s : Coord) (hr : odd r) (hs : odd s) :
    fourthRoot (if quadraticRaySign r s=1 then 0 else 2)=(quadraticRaySign r s:ℂ) := by
  by_cases he : quadraticRayExponent (EisensteinEPrimaryPhase.mul r s)=
      quadraticRayExponent r+quadraticRayExponent s
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]
  · norm_num [quadraticRaySign,hr,hs,he,fourthRoot,ZMod.val_zero,ZMod.val_ofNat,Complex.I_sq]

lemma odd_mul (r s : Coord) (hr : odd r) (hs : odd s) : odd (EisensteinEPrimaryPhase.mul r s) := by
  have h : ∀r s : Coord,odd r → odd s → odd (EisensteinEPrimaryPhase.mul r s) := by decide
  exact h r s hr hs

theorem quadraticRayValue_mul (r s : Coord) (hr : odd r) (hs : odd s) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul r s)=
      (quadraticRaySign r s:ℂ)*quadraticRayValue r*quadraticRayValue s := by
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul r s hr hs),quadraticRaySign_exponent r s hr hs,
    fourthRoot_add,fourthRoot_add,quadraticRaySign_root r s hr hs,
    quadraticRayValue_eq_fourthRoot r hr,quadraticRayValue_eq_fourthRoot s hs]

lemma quadraticRayPair_eq_sign (r s : Coord) (hr : odd r) (hs : odd s) :
    MixedCrossSeparation.quadraticRayPair r s=(quadraticRaySign r s:ℂ) := by
  unfold MixedCrossSeparation.quadraticRayPair
  rw [quadraticRayValue_mul r s hr hs]
  apply (div_eq_iff (mul_ne_zero (quadraticRayValue_ne_zero_of_odd r hr)
    (quadraticRayValue_ne_zero_of_odd s hs))).mpr
  ring

end QuadraticAllOddCRT

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CubicJacobiGlobal hiding O
open QuadraticGaussRay hiding O
open QuadraticAllOddCRT
open ActualEisensteinCoordinates hiding O omega
open UniqueFactorizationMonoid

lemma supported_factors_good (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2 := by
  intro P hP
  have hp := prime_of_normalized_factor P hP
  exact ⟨(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero,hI.2 P hP⟩

lemma idealRowHom_one_supported (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) : idealRowHom 1 I=1 := by
  have h := CanonicalUnitEuler.idealRowHom_unit_norm (1:ActualEisensteinCubic.Oˣ) I hI.1 (supported_factors_good I hI)
  simpa using h

lemma supported_prime_data (p : ActualEisensteinCubic.O) (hp : Prime p) (hs : Supported (Ideal.span {p})) :
    lambda∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) ∧ ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2 := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  exact hs.2 _ ((Ideal.mem_normalizedFactors_iff hs.1).mpr ⟨inferInstance,le_rfl⟩)

lemma supported_residue_odd (p : ActualEisensteinCubic.O) (hs : Supported (Ideal.span {p})) : EisensteinEPrimaryPhase.odd (residue p) :=
  (ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd p).mpr ((supported_span_iff p).mp hs).2

theorem idealRowHom_prime_reciprocity (p q : ActualEisensteinCubic.O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : lambda^2∣p-1) (hprimaryQ : lambda^2∣q-1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q})) :
    idealRowHom q (Ideal.span {p})=
      (quadraticRaySign (residue p) (residue q):ℂ)*idealRowHom p (Ideal.span {q}) := by
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let : (Ideal.span {q}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hq.irreducible
  obtain ⟨hgP,hcP⟩ := supported_prime_data p hp hsP
  obtain ⟨hgQ,hcQ⟩ := supported_prime_data q hq hsQ
  by_cases he : (Ideal.span {p}:Ideal ActualEisensteinCubic.O)=Ideal.span {q}
  · have hqp : q∈(Ideal.span {p}:Ideal ActualEisensteinCubic.O) := by rw [he];exact Ideal.subset_span (by simp)
    have hpq : p∈(Ideal.span {q}:Ideal ActualEisensteinCubic.O) := by rw [←he];exact Ideal.subset_span (by simp)
    rw [idealRowHom_prime q _ hgP,idealRowHom_prime p _ hgQ,
      Ideal.Quotient.eq_zero_iff_mem.mpr hqp,Ideal.Quotient.eq_zero_iff_mem.mpr hpq]
    simp only [MulChar.map_zero,mul_zero]
  · have hcop : IsCoprime (Ideal.span {p}:Ideal ActualEisensteinCubic.O) (Ideal.span {q}) := Ideal.isCoprime_of_isMaximal he
    have hqp : q∉(Ideal.span {p}:Ideal ActualEisensteinCubic.O) := by
      intro h
      apply he
      exact ((inferInstance : (Ideal.span {q}:Ideal ActualEisensteinCubic.O).IsMaximal).eq_of_le
        (Ideal.IsMaximal.ne_top inferInstance)
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h))).symm
    have h2 : idealRowHom q (Ideal.span {p})^2=idealRowHom p (Ideal.span {q})^2 := by
      rw [idealRowHom_square,idealRowHom_square]
      exact congrArg ConcreteTraceCRT.eisEmbedding (symbol_reciprocity q p hq.ne_zero hp.ne_zero hprimaryQ hprimaryP)
    have h6 : idealRowHom q (Ideal.span {p})^6=1 := by
      rw [idealRowHom_prime q _ hgP]
      have h := canonicalSextic_sixth_power_mask (Ideal.span {p}) hgP q
      change actualSextic _ hgP (Ideal.Quotient.mk _ (q^6))=_ at h
      simpa only [map_pow,ite_eq_right hqp] using h
    have hcross := quadratic_ray_cross p q hp.ne_zero hq.ne_zero hcop hcP hcQ
    rw [residue_mul,quadraticRayValue_mul _ _ (supported_residue_odd p hsP) (supported_residue_odd q hsQ)] at hcross
    have h3 (x y : ActualEisensteinCubic.O) (hg : lambda∉(Ideal.span {x}:Ideal ActualEisensteinCubic.O)) [(Ideal.span {x}).IsMaximal] :
        idealRowHom y (Ideal.span {x})^3=
          character (Ideal.span {x}) (Ideal.Quotient.mk (Ideal.span {x}) y) := by
      rw [idealRowHom_prime y _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    have hc : idealRowHom q (Ideal.span {p})^3*idealRowHom p (Ideal.span {q})^3=
        (quadraticRaySign (residue p) (residue q):ℂ) := by
      rw [h3 p q hgP,h3 q p hgQ]
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ (supported_residue_odd p hsP))
      apply mul_right_cancel₀ (quadraticRayValue_ne_zero_of_odd _ (supported_residue_odd q hsQ))
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hcross.symm
    calc
      _ = idealRowHom q (Ideal.span {p})*idealRowHom q (Ideal.span {p})^6 := by rw [h6,mul_one]
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom q (Ideal.span {p})^2)^2 := by ring
      _ = idealRowHom q (Ideal.span {p})^3*(idealRowHom p (Ideal.span {q})^2)^2 := by rw [h2]
      _ = (idealRowHom q (Ideal.span {p})^3*idealRowHom p (Ideal.span {q})^3)*idealRowHom p (Ideal.span {q}) := by ring
      _ = _ := by rw [hc]

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CubicJacobiGlobal hiding O
open QuadraticAllOddCRT
open ActualEisensteinCoordinates hiding O omega

def sexticReciprocityPhase (a b : ActualEisensteinCubic.O) : ℂ :=
  (quadraticRaySign (residue a) (residue b):ℂ)

lemma sexticReciprocityPhase_mul_left (a b c : ActualEisensteinCubic.O) :
    sexticReciprocityPhase (a*b) c=sexticReciprocityPhase a c*sexticReciprocityPhase b c := by
  simp only [sexticReciprocityPhase,residue_mul,quadraticRaySign_mul_left,Int.cast_mul]

lemma sexticReciprocityPhase_mul_right (a b c : ActualEisensteinCubic.O) :
    sexticReciprocityPhase a (b*c)=sexticReciprocityPhase a b*sexticReciprocityPhase a c := by
  simp only [sexticReciprocityPhase,residue_mul,quadraticRaySign_mul_right,Int.cast_mul]

lemma sexticReciprocityPhase_one_right (a : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a})) :
    sexticReciprocityPhase a 1=1 := by
  have h1 : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0) := by
    have h : (1:ActualEisensteinCubic.O)=eval 1 0 := by simp [eval]
    rw [h,residue_eval]
    norm_num
  have ht : ∀r : EisensteinEPrimaryPhase.Coord,EisensteinEPrimaryPhase.odd r →
      quadraticRaySign r ((1:ZMod 4),0)=1 := by decide
  simp only [sexticReciprocityPhase,h1,ht _ (supported_residue_odd a ha),Int.cast_one]

lemma sexticReciprocityPhase_one_left (a : ActualEisensteinCubic.O) (ha : Supported (Ideal.span {a})) :
    sexticReciprocityPhase 1 a=1 := by
  have he : sexticReciprocityPhase 1 a=sexticReciprocityPhase a 1 := by
    simp only [sexticReciprocityPhase,quadraticRaySign_symm]
  rw [he,sexticReciprocityPhase_one_right a ha]

lemma idealRowHom_prime_primary_reciprocity (p b : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimaryP : lambda^2∣p-1) (hprimaryB : lambda^2∣b-1)
    (hsP : Supported (Ideal.span {p})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {p})=sexticReciprocityPhase p b*idealRowHom p (Ideal.span {b}) := by
  have hb0 : b≠0 := by
    intro h
    apply hsB.1
    simp [h]
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization b hb0 hprimaryB
  rw [←hprod] at hsB ⊢
  clear hprod hb0 hprimaryB b
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_supported _ hsP,sexticReciprocityPhase_one_right p hsP,mul_one]
  | @cons q s ih =>
    have hq := hfactors q (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : Supported (Ideal.span {q}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hsB
    rw [Multiset.prod_cons,idealRowHom_argument_mul,←Ideal.span_singleton_mul_span_singleton,
      map_mul,sexticReciprocityPhase_mul_right,
      idealRowHom_prime_reciprocity p q hp hq.1 hprimaryP hq.2 hsP hsplit.1,
      ih hsplit.2 htail]
    simp only [sexticReciprocityPhase]
    ring

theorem idealRowHom_primary_reciprocity (a b : ActualEisensteinCubic.O)
    (hprimaryA : lambda^2∣a-1) (hprimaryB : lambda^2∣b-1)
    (hsA : Supported (Ideal.span {a})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a})=sexticReciprocityPhase a b*idealRowHom a (Ideal.span {b}) := by
  have ha0 : a≠0 := by
    intro h
    apply hsA.1
    simp [h]
  obtain ⟨s,hprod,hfactors⟩ := exists_primary_prime_factorization a ha0 hprimaryA
  rw [←hprod] at hsA ⊢
  clear hprod ha0 hprimaryA a
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,
      idealRowHom_one_supported _ hsB,sexticReciprocityPhase_one_left b hsB,one_mul]
  | @cons p s ih =>
    have hp := hfactors p (Multiset.mem_cons_self _ _)
    have htail : ∀r∈s,Prime r ∧ lambda^2∣r-1 := fun r hr => hfactors r (Multiset.mem_cons_of_mem hr)
    have hsplit : Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}) := by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hsA
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_argument_mul,sexticReciprocityPhase_mul_left,
      idealRowHom_prime_primary_reciprocity p b hp.1 hp.2 hprimaryB hsplit.1 hsB,
      ih hsplit.2 htail]
    ring

theorem idealRowHom_primary_reciprocity_ray (a b : ActualEisensteinCubic.O)
    (hprimaryA : lambda^2∣a-1) (hprimaryB : lambda^2∣b-1)
    (hsA : Supported (Ideal.span {a})) (hsB : Supported (Ideal.span {b})) :
    idealRowHom b (Ideal.span {a})=
      MixedCrossSeparation.quadraticRayPair (residue a) (residue b)*idealRowHom a (Ideal.span {b}) := by
  rw [quadraticRayPair_eq_sign _ _ (supported_residue_odd a hsA) (supported_residue_odd b hsB)]
  exact idealRowHom_primary_reciprocity a b hprimaryA hprimaryB hsA hsB

theorem idealRowHom_ideal_reciprocity (I J : Ideal ActualEisensteinCubic.O) (hI : Supported I) (hJ : Supported J) :
    idealRowHom (primaryGenerator J) I=
      sexticReciprocityPhase (primaryGenerator I) (primaryGenerator J)*idealRowHom (primaryGenerator I) J := by
  have hpI := primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)
  have hpJ := primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)
  have h := idealRowHom_primary_reciprocity (primaryGenerator I) (primaryGenerator J)
    hpI.2 hpJ.2 (by rwa [hpI.1]) (by rwa [hpJ.1])
  simpa only [hpI.1,hpJ.1] using h

end CanonicalRowCompletion

end

end OAI

end

