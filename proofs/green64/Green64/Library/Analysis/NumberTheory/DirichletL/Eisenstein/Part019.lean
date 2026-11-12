module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part018
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part014

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part019

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion -/

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma source_period_of_three_supported
    (hs:∀h:Eis,¬(3:Eis)∣h→sourceResidualFourierCoefficient h=0)
    (a:Eis) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubicSourceResidualFunction (upperPoint (z+eisEmbedding a) v hv)=
      cubicSourceResidualFunction (upperPoint z v hv) := by
  rw [cubicSourceResidualFunction_bessel,cubicSourceResidualFunction_bessel]
  apply congrArg (fun t:ℂ=>(3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+t)
  apply tsum_congr
  intro h
  by_cases hd:(3:Eis)∣h
  · obtain ⟨b,rfl⟩:=hd
    have hp:ShortDraftTrace.breveE (cuspFrequency (3*b)*eisEmbedding a)=1:=by
      have he:cuspFrequency (3*b)*eisEmbedding a=cuspFrequency b*(3*eisEmbedding a):=by
        unfold cuspFrequency
        rw [map_mul,map_ofNat]
        ring
      rw [he,cuspFrequency_period]
    rw [mul_add,AddChar.map_add_eq_mul,hp,mul_one]
  · rw [hs h hd]
    by_cases hh:h=0 <;> simp [hh]

theorem exists_source_coefficient_not_three :
    ∃h:Eis,¬(3:Eis)∣h ∧ sourceResidualFourierCoefficient h≠0 := by
  by_contra hn
  have hs:∀h:Eis,¬(3:Eis)∣h→sourceResidualFourierCoefficient h=0:=by
    intro h hh
    by_contra hne
    exact hn ⟨h,hh,hne⟩
  apply cubicSource_not_eisenstein_periodic
  intro a w
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [complexTranslation_action]
  exact source_period_of_three_supported hs a z v hv

theorem exists_sourceArithmeticResidue_not_three :
    ∃h:Eis,¬(3:Eis)∣h ∧ sourceArithmeticResidue h≠0 := by
  obtain ⟨h,hh,ht⟩:=exists_source_coefficient_not_three
  refine ⟨h,hh,?_⟩
  intro hz
  apply ht
  simp only [sourceResidualFourierCoefficient,hz,mul_zero]

end CubicEisenstein

namespace CompletedGauss

section
open Filter MeasureTheory
open scoped Classical BigOperators Topology FourierTransform SchwartzMap ContDiff

lemma compactMellin_vertical_integrable (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V) σ := by
  have hc : HasCompactSupport (CubicReflectionKernel.mellinLogFamily V σ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (CubicReflectionKernel.mellinLogFamily_support V a b ha hsupp σ)
  have hd : ContDiff ℝ ∞ (CubicReflectionKernel.mellinLogFamily V σ) :=
    (CubicReflectionKernel.mellinLogFamily_smooth V hV).comp (contDiff_const.prodMk contDiff_id)
  let f : 𝓢(ℝ,ℂ) := hc.toSchwartzMap hd
  have hf : Integrable (fun t : ℝ=>(𝓕 f) (t/(2*Real.pi))) := by
    simpa only [div_eq_mul_inv] using
      (𝓕 f).integrable.comp_mul_right' (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  change Integrable (fun t : ℝ=>mellin V ((σ:ℂ)+t*Complex.I))
  have hfcoe : (f:ℝ→ℂ)=CubicReflectionKernel.mellinLogFamily V σ := rfl
  simpa only [CubicReflectionKernel.mellin_eq_logFamily_fourier,
    SchwartzMap.fourier_coe,hfcoe] using hf

theorem compactMellin_inversion (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ x : ℝ) (hx : 0<x) :
    V x=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin V ((σ:ℂ)+t*Complex.I) := by
  have hm := mellinInv_mellin_eq σ V hx
    (CubicReflectionKernel.compact_source_mellin_convergent V a b ha hsupp hV σ)
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) hV.continuous.continuousAt
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using hm.symm

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma positive_cpow_vertical_norm (r σ t : ℝ) (hr : 0< r) :
    ‖(r:ℂ)^((σ:ℂ)+t*Complex.I)‖=r^σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_negative_vertical_norm (r σ t : ℝ) (hr : 0< r) :
    ‖(r:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=r^(-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_vertical_continuous (r σ : ℝ) (hr : 0< r) :
    Continuous (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma positive_cpow_negative_vertical_continuous (r σ : ℝ) (hr : 0< r) :
    Continuous (fun t : ℝ=>(r:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma vertical_power_mul_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0< r) :
    Integrable (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)*M t) := by
  apply (hM.norm.const_mul (r^σ)).mono'
    ((positive_cpow_vertical_continuous r σ hr).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by simp only [Pi.mul_apply,norm_mul,positive_cpow_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0< r) (c : ℂ) :
    Integrable (fun t : ℝ=>c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t) := by
  apply (hM.norm.const_mul (‖c‖*r^(-σ))).mono'
    ((continuous_const.mul (positive_cpow_negative_vertical_continuous r σ hr)).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [Pi.mul_apply,norm_mul,positive_cpow_negative_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integral_norm (M : ℝ→ℂ) (r σ : ℝ) (hr : 0< r) (c : ℂ) :
    (∫t : ℝ,‖c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖)=
      (‖c‖*r^(-σ))*(∫t : ℝ,‖M t‖) := by
  simp only [norm_mul,positive_cpow_negative_vertical_norm r σ _ hr,integral_const_mul]

theorem weighted_vertical_sum_integral {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (M : ℝ→ℂ) (hM : Integrable M) :
    (∑' i,∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t)=
      ∫t : ℝ,(∑' i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I)))*M t := by
  have hi (i : α) := weighted_vertical_power_integrable M hM (r i) σ (hr i) (c i)
  have hs : Summable (fun i=>∫t : ℝ,‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖) := by
    simp only [weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact hc.mul_right _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>tsum_mul_right)

lemma positive_quotient_cpow_neg (r X : ℝ) (hr : 0< r) (hX : 0<X) (s : ℂ) :
    ((r/X:ℝ):ℂ)^(-s)=(r:ℂ)^(-s)*(X:ℂ)^s := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hr.le hX.le,
    Complex.cpow_neg,Complex.cpow_neg,div_inv_eq_mul]

theorem weightedMellin_inversion {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    (∑'i,c i*V (r i/X))=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin V ((σ:ℂ)+t*Complex.I)*(X:ℂ)^((σ:ℂ)+t*Complex.I)*
        (∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let M : ℝ→ℂ := fun t=>(X:ℂ)^((σ:ℂ)+t*Complex.I)*mellin V ((σ:ℂ)+t*Complex.I)
  have hM : Integrable M := vertical_power_mul_integrable _
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) X σ hX
  have hi (i : α) : c i*V (r i/X)=(1/(2*Real.pi):ℂ)*
      ∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t := by
    rw [compactMellin_inversion V a b ha hsupp hV σ _ (div_pos (hr i) hX)]
    rw [←mul_assoc,mul_comm (c i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>by
      dsimp only
      rw [positive_quotient_cpow_neg _ _ (hr i) hX]
      dsimp only [M]
      ring)
  simp_rw [hi]
  rw [tsum_mul_left,weighted_vertical_sum_integral r hr c σ hc M hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>by dsimp only [M];ring)

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma angularFactor_norm_le_one (a : ActualEisensteinCubic.O) : ‖FiniteGaussPhase.angularFactor a‖≤1 := by
  by_cases ha : a=0
  · subst a; simp [FiniteGaussPhase.angularFactor]
  · exact (FiniteGaussPhase.norm_angularFactor a ha).le

lemma cubicRow_norm_le_one (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) (x : ActualEisensteinCubic.O⧸I) :
    ‖cubicRow I hI x‖≤1 := by
  unfold cubicRow
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi; exact norm_nonneg _
  · intro i hi
    exact FiniteRayExpansion.norm_char_le_one _ _

lemma gaussTwo_norm_le_sqrt (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) :
    ‖gaussTwo I hI‖≤Real.sqrt (Ideal.absNorm I:ℝ) := by
  let n := primaryGenerator I
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {n}) := finite_quotient_span hI
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : ‖eisEmbedding n‖=Real.sqrt (Ideal.absNorm I:ℝ) := primaryGenerator_norm I hI
  have hsum : ‖∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x‖≤(Ideal.absNorm I:ℝ) := by
    calc
      _≤∑x : ActualEisensteinCubic.O⧸Ideal.span {n},‖cubicRow I hI (e x)*ψ x‖ := norm_sum_le _ _
      _≤∑_x : ActualEisensteinCubic.O⧸Ideal.span {n},(1:ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul,AddChar.norm_apply,mul_one]
        exact cubicRow_norm_le_one I hI (e x)
      _=(Ideal.absNorm I:ℝ) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
        congr 1
        rw [←Nat.card_eq_fintype_card,←Submodule.cardQuot_apply,←Ideal.absNorm_apply,
          (primaryGenerator_spec I hI).1]
  change ‖(∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x)/(‖eisEmbedding n‖:ℂ)‖≤_
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hn]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hN)).mpr
  simpa only [Real.mul_self_sqrt hN.le] using hsum

lemma columnWeight_div_sqrt_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ)‖≤1 := by
  by_cases hI : Squarefree I ∧ primaryGenerator I≠0
  · have hN : 0<(Ideal.absNorm I:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI.2 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [columnWeight_eq Ψ I hI.1 hI.2,norm_div,norm_mul,norm_mul,norm_star,
      FiniteGaussPhase.norm_angularFactor _ hI.2,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_one (Real.sqrt_pos.mpr hN)).mpr
    exact (mul_le_of_le_one_right (norm_nonneg _) (hΨ _)).trans (gaussTwo_norm_le_sqrt I hI.2)
  · simp only [columnWeight,squarefreeGaussCoefficient,dite_eq_right hI,zero_mul,zero_div,norm_zero,zero_le_one]

lemma cubeWeight_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ I‖≤1 := by
  by_cases hI : I=0
  · subst I; simp
  have hN : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one hN
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
    Ψ (primaryGenerator I)^3/(Ideal.absNorm I:ℂ)‖≤1
  rw [norm_div,norm_mul,norm_pow,norm_star,norm_pow,Complex.norm_natCast]
  apply (div_le_one hn).mpr
  apply le_trans _ hN
  calc
    _≤(1:ℝ)*1 := mul_le_mul
      (pow_le_one₀ (norm_nonneg _) (angularFactor_norm_le_one _))
      (pow_le_one₀ (norm_nonneg _) (hΨ _)) (pow_nonneg (norm_nonneg _) _) zero_le_one
    _=1 := one_mul _

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

abbrev CompletedMellinIndex := NonzeroIdeal×NonzeroIdeal

def completedMellinLength (p : CompletedMellinIndex) : ℝ :=
  (Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3

def completedMellinCoefficient (Ψ : ActualEisensteinCubic.O→*ℂ) (p : CompletedMellinIndex) : ℂ :=
  columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*cubeWeight Ψ p.2.1

lemma nonzeroIdeal_norm_pos (I : NonzeroIdeal) : 0<(Ideal.absNorm I.1:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>I.2 (Ideal.absNorm_eq_zero_iff.mp h))

lemma completedMellinLength_pos (p : CompletedMellinIndex) : 0<completedMellinLength p :=
  mul_pos (nonzeroIdeal_norm_pos p.1) (pow_pos (nonzeroIdeal_norm_pos p.2) 3)

lemma completedMellinCoefficient_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (p : CompletedMellinIndex) : ‖completedMellinCoefficient Ψ p‖≤1 := by
  rw [completedMellinCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_right (columnWeight_div_sqrt_norm_le_one Ψ hΨ p.1.1)
    (norm_nonneg _)).trans (by simpa only [one_mul] using cubeWeight_norm_le_one Ψ hΨ p.2.1)

lemma nonzeroIdeal_norm_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun I : NonzeroIdeal=>(Ideal.absNorm I.1:ℝ)^(-σ)) := by
  have h := (fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ)).subtype (fun I=>I≠0)
  apply h.congr
  intro I
  change ‖fullIdealWeight (σ:ℂ) I.1‖=(Ideal.absNorm I.1:ℝ)^(-σ)
  rw [fullIdealWeight,ite_eq_right I.2]
  simpa only [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (nonzeroIdeal_norm_pos I) (-(σ:ℂ)))

lemma completedMellinLength_rpow (p : CompletedMellinIndex) (σ : ℝ) :
    (completedMellinLength p)^(-σ)=
      (Ideal.absNorm p.1.1:ℝ)^(-σ)*(Ideal.absNorm p.2.1:ℝ)^(-(3*σ)) := by
  rw [completedMellinLength,Real.mul_rpow (nonzeroIdeal_norm_pos p.1).le
    (pow_nonneg (nonzeroIdeal_norm_pos p.2).le _),←Real.rpow_natCast_mul (nonzeroIdeal_norm_pos p.2).le]
  congr 1
  congr 1
  ring

theorem completedMellinCoefficient_summable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (σ : ℝ) (hσ : 1<σ) :
    Summable (fun p=>‖completedMellinCoefficient Ψ p‖*(completedMellinLength p)^(-σ)) := by
  have hI := nonzeroIdeal_norm_rpow_summable σ hσ
  have hJ := nonzeroIdeal_norm_rpow_summable (3*σ) (by linarith)
  have hp := hI.mul_of_nonneg hJ (fun I=>Real.rpow_nonneg (nonzeroIdeal_norm_pos I).le _)
    (fun J=>Real.rpow_nonneg (nonzeroIdeal_norm_pos J).le _)
  apply hp.of_nonneg_of_le
  · intro p; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (completedMellinLength_pos p).le _)
  · intro p
    rw [←completedMellinLength_rpow]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (completedMellinLength_pos p).le _)
      (completedMellinCoefficient_norm_le_one Ψ hΨ p)

def completedDirichletSeries (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) : ℂ :=
  ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
    (completedMellinLength p:ℂ)^(1/2-s)

theorem completedT_eq_mellin_index (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=∑'p : CompletedMellinIndex,
      completedMellinCoefficient Ψ p*Vstar W (completedMellinLength p/X) := by
  have hfull := completedT_summable Ψ W hW X hX
  have hinj : Function.Injective (fun p : CompletedMellinIndex=>(p.1.1,p.2.1)) := by
    intro p q h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hsub := hfull.comp_injective hinj
  calc
    completedT Ψ W X=∑'I : NonzeroIdeal,∑'J : Ideal ActualEisensteinCubic.O,summand Ψ W X I.1 J := by
      symm
      unfold completedT
      apply tsum_subtype_eq_of_support_subset
        (s:={I:Ideal ActualEisensteinCubic.O|I≠0}) (f:=fun I:Ideal ActualEisensteinCubic.O=>∑'J:Ideal ActualEisensteinCubic.O,summand Ψ W X I J)
      intro I hI hz
      subst I
      exact hI (by simp only [summand_zero_left,tsum_zero])
    _=∑'I : NonzeroIdeal,∑'J : NonzeroIdeal,summand Ψ W X I.1 J.1 := by
      apply tsum_congr
      intro I
      symm
      apply tsum_subtype_eq_of_support_subset
        (s:={J:Ideal ActualEisensteinCubic.O|J≠0}) (f:=fun J:Ideal ActualEisensteinCubic.O=>summand Ψ W X I.1 J)
      intro J hJ hz
      subst J
      exact hJ (summand_zero_right Ψ W X I.1)
    _=∑'p : CompletedMellinIndex,summand Ψ W X p.1.1 p.2.1 := hsub.tsum_prod.symm
    _=_ := rfl

theorem completedT_initial_mellin (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hWc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  rw [completedT_eq_mellin_index Ψ W hWc X hX]
  have h := weightedMellin_inversion completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2)
    (completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num))
    (Vstar W) a b ha (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW) X hX
  have hd (t : ℝ) : completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
    unfold completedDirichletSeries
    apply tsum_congr
    intro p
    congr 2
    ring
  simpa only [hd,Complex.ofReal_div,Complex.ofReal_ofNat] using h

end

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma nat_sqrt_cpow_half (a : ℕ) :
    (Real.sqrt (a:ℝ):ℂ)=(a:ℂ)^(1/2:ℂ) := by
  simpa only [Real.sqrt_eq_rpow,Complex.ofReal_natCast,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat] using
    (Complex.ofReal_cpow (Nat.cast_nonneg a) (1/2:ℝ))

lemma nat_half_shift_product (a b : ℕ) (ha : a≠0) (hb : b≠0) (C D s : ℂ) :
    (C/(Real.sqrt (a:ℝ):ℂ)*(D/(b:ℂ)))*((a:ℂ)*(b:ℂ)^3)^(1/2-s)=
      C*D*(b:ℂ)^(1/2-3*s)*(a:ℂ)^(-s) := by
  have ha0 : (a:ℂ)≠0 := Nat.cast_ne_zero.mpr ha
  have hb0 : (b:ℂ)≠0 := Nat.cast_ne_zero.mpr hb
  have hhalf : (a:ℂ)^(1/2:ℂ)≠0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl ha0)
  rw [nat_sqrt_cpow_half]
  have hmul : ((a:ℂ)*(b:ℂ)^3)^(1/2-s)=
      (a:ℂ)^(1/2-s)*(b:ℂ)^(3*(1/2-s)) := by
    rw [←Nat.cast_pow,Complex.natCast_mul_natCast_cpow,Nat.cast_pow,
      ←Complex.natCast_cpow_natCast_mul]
    norm_num
  rw [hmul]
  have hA : (a:ℂ)^(1/2-s)=(a:ℂ)^(1/2:ℂ)*(a:ℂ)^(-s) := by
    rw [sub_eq_add_neg,Complex.cpow_add _ _ ha0]
  have hB : (b:ℂ)^(3*(1/2-s))=(b:ℂ)*(b:ℂ)^(1/2-3*s) := by
    rw [show (3:ℂ)*(1/2-s)=1+(1/2-3*s) by ring,
      Complex.cpow_add _ _ hb0,Complex.cpow_one]
  rw [hA,hB]
  field_simp

lemma completedDirichletTerm_expanded (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) (p : CompletedMellinIndex) :
    completedMellinCoefficient Ψ p*(completedMellinLength p:ℂ)^(1/2-s)=
      columnWeight Ψ p.1.1*star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3*(Ideal.absNorm p.2.1:ℂ)^(1/2-3*s)*
      (Ideal.absNorm p.1.1:ℂ)^(-s) := by
  have ha : Ideal.absNorm p.1.1≠0 := fun h=>p.1.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hb : Ideal.absNorm p.2.1≠0 := fun h=>p.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  unfold completedMellinCoefficient completedMellinLength
  change (columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*
    (star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3/(Ideal.absNorm p.2.1:ℂ)))*
    (((Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3:ℝ):ℂ)^(1/2-s)=_
  rw [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_natCast]
  rw [nat_half_shift_product _ _ ha hb]
  ring

theorem completedDirichletSeries_expanded (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) :
    completedDirichletSeries Ψ s=∑'p : CompletedMellinIndex,
      columnWeight Ψ p.1.1*star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3*(Ideal.absNorm p.2.1:ℂ)^(1/2-3*s)*
      (Ideal.absNorm p.1.1:ℂ)^(-s) := by
  unfold completedDirichletSeries
  exact tsum_congr (completedDirichletTerm_expanded Ψ s)

end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma weighted_vertical_series_continuous {α : Type*}
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    Continuous (fun t : ℝ=>∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  apply continuous_tsum
    (fun i=>continuous_const.mul (positive_cpow_negative_vertical_continuous (r i) σ (hr i))) hc
  intro i t
  change ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤‖c i‖*(r i)^(-σ)
  rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]

lemma weighted_vertical_series_norm {α : Type*}
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) (t : ℝ) :
    ‖∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤∑'i,‖c i‖*(r i)^(-σ) := by
  have he (i : α) : ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=‖c i‖*(r i)^(-σ) := by
    rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]
  simpa only [he] using norm_tsum_le_tsum_norm (hc.congr (fun i=>(he i).symm))

lemma completedDirichletSeries_initial (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) :
    completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
  unfold completedDirichletSeries
  apply tsum_congr
  intro p
  congr 2
  ring

theorem completedT_initial_mellin_integrable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*
      (X:ℂ)^((3/2:ℂ)+t*Complex.I)*completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)) := by
  have hsum := completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num)
  have hc := weighted_vertical_series_continuous completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hb := weighted_vertical_series_norm completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hmi : Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_div,Complex.ofReal_ofNat] using
      (compactMellin_vertical_integrable (Vstar W) a b ha (Vstar_support W a b hsupp)
        (Vstar_contDiff W a b ha hsupp hW) (3/2))
  have hbase := vertical_power_mul_integrable _ hmi X (3/2) hX
  have hi := hbase.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,completedDirichletSeries_initial,
    mul_comm (mellin (Vstar W) _)] using hi

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def dualIdealDyad (j : ℕ) : Finset (Ideal Eis) :=
  (ConcretePrimeRowBridge.idealsUpTo (2^j)).filter
    (fun I => Nat.clog 2 (Ideal.absNorm I)=j)

lemma mem_dualIdealDyad (I : Ideal Eis) (j : ℕ) :
    I∈dualIdealDyad j ↔ I≠0 ∧ Nat.clog 2 (Ideal.absNorm I)=j := by
  simp only [dualIdealDyad,Finset.mem_filter,ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hI,_⟩,hj⟩
    exact ⟨fun h => by simp [h] at hI, hj⟩
  · rintro ⟨hI,hj⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩,hj⟩
    simpa only [hj] using Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)

lemma dualIdealDyad_bounds (j : ℕ) (I : Ideal Eis) (hI : I∈dualIdealDyad j) :
    I≠0 ∧ (2:ℝ)^j/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^j := by
  obtain ⟨hn,hj⟩:= (mem_dualIdealDyad I j).mp hI
  have hu:=Nat.le_pow_clog (by norm_num : 1<2) (Ideal.absNorm I)
  have hl:=two_pow_clog_le_double (Ideal.absNorm I)
    (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn))
  rw [hj] at hu hl
  refine ⟨hn,?_,by exact_mod_cast hu⟩
  have he : (2:ℝ)^j≤2*(Ideal.absNorm I:ℝ):=by exact_mod_cast hl
  linarith

abbrev NonzeroDualIdeal := {I : Ideal Eis // I≠0}

def dualDyadicIndexEquiv :
    (ℕ×NonzeroDualIdeal×NonzeroDualIdeal) ≃
      (Σ i : ℕ×ℕ×ℕ, (dualIdealDyad i.2.2)×(dualIdealDyad i.2.1)) where
  toFun x := ⟨(x.1,Nat.clog 2 (Ideal.absNorm x.2.2.val),Nat.clog 2 (Ideal.absNorm x.2.1.val)),
    ⟨⟨x.2.1.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.1.property,rfl⟩⟩,
      ⟨x.2.2.val,(mem_dualIdealDyad _ _).mpr ⟨x.2.2.property,rfl⟩⟩⟩⟩
  invFun x := ⟨x.1.1,⟨x.2.1.val,((mem_dualIdealDyad _ _).mp x.2.1.property).1⟩,
    ⟨x.2.2.val,((mem_dualIdealDyad _ _).mp x.2.2.property).1⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    rcases x with ⟨⟨m,j,k⟩,⟨⟨I,hI⟩,⟨J,hJ⟩⟩⟩
    have hi:=((mem_dualIdealDyad I k).mp hI).2
    have hj:=((mem_dualIdealDyad J j).mp hJ).2
    dsimp only
    subst k
    subst j
    rfl

theorem tsum_dualIdealDyads
    (f : ℕ×NonzeroDualIdeal×NonzeroDualIdeal → ℂ) (hf : Summable f) :
    (∑'x, f x) = ∑'i : ℕ×ℕ×ℕ,
      ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
        f (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  let g := f ∘ dualDyadicIndexEquiv.symm
  have hg : Summable g := dualDyadicIndexEquiv.symm.summable_iff.mpr hf
  calc
    _ = ∑'x,g x := (dualDyadicIndexEquiv.symm.tsum_eq f).symm
    _ = ∑'i,∑'x,g ⟨i,x⟩ := Summable.tsum_sigma' (fun _=>hasSum_fintype _ |>.summable) hg
    _ = _ := by
      apply tsum_congr
      intro i
      rw [tsum_fintype,Fintype.sum_prod_type]
      rfl

end CompletedGauss

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.BesselReflection -/

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

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology

section
open CubicEisenstein

def completedBesselProfile (Ψ : ActualEisensteinCubic.O→*ℂ) (q : ℝ) : ℝ→ℂ :=
  radialBesselProfile completedMellinLength (completedMellinCoefficient Ψ) q

def besselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
    ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)

def inverseBesselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*(2:ℂ)^(1-2*s)*
    (Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹

theorem completedBesselProfile_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    mellin (completedBesselProfile Ψ q) (2*s)=
      besselMellinFactor q s*completedDirichletSeries Ψ s := by
  let : Countable ActualEisensteinCubic.O :=
    ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) :=
    ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hsum := completedMellinCoefficient_summable Ψ hΨ (s.re-1/2) (by linarith)
  have he : -(s.re-1/2)=1/2-s.re := by ring
  simp only [he] at hsum
  exact radialBesselProfile_mellin completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) q hq s (by linarith) hsum

lemma inverseBesselMellinFactor_mul (q : ℝ) (hq : 0<q) (s : ℂ)
    (hs : -(1/3)<s.re) :
    inverseBesselMellinFactor q s*besselMellinFactor q s=1 := by
  have hq0 : (((4*Real.pi*q:ℝ):ℂ)^(2*s+1))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have h1 : Complex.Gamma (s+1/3)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
  have h2 : Complex.Gamma (s+2/3)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
  have hp : (2:ℂ)^(1-2*s)*(2:ℂ)^(2*s-1)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    simp
  unfold inverseBesselMellinFactor besselMellinFactor
  calc
    _=((((4*Real.pi*q:ℝ):ℂ)^(2*s+1))/(((4*Real.pi*q:ℝ):ℂ)^(2*s+1)))*
        ((2:ℂ)^(1-2*s)*(2:ℂ)^(2*s-1))*
        ((Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹*
          (Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))) := by ring
    _=1 := by rw [div_self hq0,hp,inv_mul_cancel₀ (mul_ne_zero h1 h2)];ring

theorem completedDirichletSeries_eq_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    completedDirichletSeries Ψ s=
      inverseBesselMellinFactor q s*mellin (completedBesselProfile Ψ q) (2*s) := by
  rw [completedBesselProfile_mellin Ψ hΨ q hq s hs,←mul_assoc,
    inverseBesselMellinFactor_mul q hq s (by linarith),one_mul]

end

theorem inverseBesselMellinFactor_differentiable (q : ℝ) (hq : 0<q) :
    Differentiable ℂ (inverseBesselMellinFactor q) := by
  have hq0 : ((4*Real.pi*q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : Differentiable ℂ (fun s : ℂ=>((4*Real.pi*q:ℝ):ℂ)^(2*s+1)) :=
    (show Differentiable ℂ (fun s : ℂ=>2*s+1) from by fun_prop).const_cpow (Or.inl hq0)
  have h2 : Differentiable ℂ (fun s : ℂ=>(2:ℂ)^(1-2*s)) :=
    (show Differentiable ℂ (fun s : ℂ=>1-2*s) from by fun_prop).const_cpow
      (Or.inl (by norm_num : (2:ℂ)≠0))
  have h3 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+1/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have h4 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+2/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  convert (h1.mul h2).mul (h4.mul h3) using 1
  ext s
  simp only [inverseBesselMellinFactor,Pi.mul_apply,mul_inv_rev]

theorem inverseBesselMellinFactor_strip_bound (q : ℝ) (hq : 0<q) (a b : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖inverseBesselMellinFactor q s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cg,hCg,hg⟩ := CubicGammaExponential.inverse_cubic_Gamma_pair_strip_bound a b
  let Ca := (4*Real.pi*q)^(2*a+1)+(4*Real.pi*q)^(2*b+1)
  let Cb := (2:ℝ)^(1-2*b)+(2:ℝ)^(1-2*a)
  have hqpos : 0<4*Real.pi*q := by positivity
  have hCa : 0≤Ca := by dsimp [Ca];positivity
  have hCb : 0≤Cb := by dsimp [Cb];positivity
  refine ⟨Ca*Cb*Cg,by positivity,?_⟩
  intro s hs
  have hp1 : ‖((4*Real.pi*q:ℝ):ℂ)^(2*s+1)‖≤Ca := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    have hr : (2*s+1).re=2*s.re+1 := by simp
    rw [hr]
    exact VerticalContourShift.rpow_between_endpoints _ _ _ _ hqpos
      (by linarith [hs.1]) (by linarith [hs.2])
  have hp2 : ‖(2:ℂ)^(1-2*s)‖≤Cb := by
    change ‖((2:ℝ):ℂ)^(1-2*s)‖≤Cb
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ))]
    have hr : (1-2*s).re=1-2*s.re := by simp
    rw [hr]
    exact VerticalContourShift.rpow_between_endpoints _ _ _ _ (by norm_num)
      (by linarith [hs.2]) (by linarith [hs.1])
  simp only [inverseBesselMellinFactor,norm_mul]
  calc
    _≤(Ca*Cb)*(Cg*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hp1 hp2 (norm_nonneg _) hCa) (hg s hs)
        (norm_nonneg _) (mul_nonneg hCa hCb)
    _=_ := by ring

def continuedBesselDirichlet (F : ℝ→ℂ) (q : ℝ) (s : ℂ) : ℂ :=
  inverseBesselMellinFactor q s*mellin F (2*s)

theorem continuedBesselDirichlet_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) :
    Differentiable ℂ (continuedBesselDirichlet F q) :=
  (inverseBesselMellinFactor_differentiable q hq).mul (hF.comp (by fun_prop))

theorem continuedBesselDirichlet_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (a b : ℝ) (ha : MellinConvergent F ((2*a:ℝ):ℂ))
    (hb : MellinConvergent F ((2*b:ℝ):ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖continuedBesselDirichlet F q s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Ci,hCi,hi⟩ := inverseBesselMellinFactor_strip_bound q hq a b
  obtain ⟨Cm,hCm,hm⟩ := VerticalContourShift.mellin_uniform_strip_bound F (2*a) (2*b) ha hb
  refine ⟨Ci*Cm,mul_nonneg hCi hCm,?_⟩
  intro s hs
  have hms : ‖mellin F (2*s)‖≤Cm := hm (2*s)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  rw [continuedBesselDirichlet,norm_mul]
  calc
    _≤(Ci*Real.exp (2*Real.pi*|s.im|))*Cm :=
      mul_le_mul (hi s hs) hms (norm_nonneg _) (mul_nonneg hCi (Real.exp_pos _).le)
    _=_ := by ring

theorem continuedBesselDirichlet_eq_initial (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    continuedBesselDirichlet (completedBesselProfile Ψ q) q s=
      completedDirichletSeries Ψ s :=
  (completedDirichletSeries_eq_mellin Ψ hΨ q hq s hs).symm

end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSource_horizontal_hasDerivAt (side:Bool) (v:ℝ) (hv:0<v)
    (z direction:ℂ) (t:ℝ) :
    HasDerivAt (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3)
        (z/3+(t:ℂ)*(direction/3)) (direction/3)) t := by
  have he : (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv)) =
      (fun x:ℝ => (ramifiedBesselCoefficients side).series
        (v/3,z/3+(x:ℂ)*(direction/3))) := by
    funext x
    rw [ramifiedSource_eq_series]
    congr 2
    ring
  rw [he]
  exact (ramifiedBesselCoefficients side).series_horizontal_hasDerivAt
    (v/3) (by positivity) (z/3) (direction/3) t

lemma ramifiedSource_wirtingerBar_cusp_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C ∧ ∀(v:ℝ)(hv:0<v)(z:ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
        (upperPoint w v hv)) z‖ ≤ C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C1,hC1,h1b⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (1/3)
  obtain ⟨CI,hCI,hIb⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (Complex.I/3)
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (ramifiedSource_horizontal_hasDerivAt side v hv z 1 0).deriv
  have hI := (ramifiedSource_horizontal_hasDerivAt side v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  have he : -residualCuspDecayRate*(v/3)=-(residualCuspDecayRate/3)*v := by ring
  have hb1 := h1b (v/3) (z/3) (by linarith)
  have hbI := hIb (v/3) (z/3) (by linarith)
  rw [he] at hb1 hbI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖Complex.I*(∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3)‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-(residualCuspDecayRate/3)*v)+
      CI*Real.exp (-(residualCuspDecayRate/3)*v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hbI) (by norm_num)
    _ = _ := by ring

lemma ramifiedSource_wirtingerZ_cusp_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C ∧ ∀(v:ℝ)(hv:0<v)(z:ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
        (upperPoint w v hv)) z‖ ≤ C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C1,hC1,h1b⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (1/3)
  obtain ⟨CI,hCI,hIb⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (Complex.I/3)
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (ramifiedSource_horizontal_hasDerivAt side v hv z 1 0).deriv
  have hI := (ramifiedSource_horizontal_hasDerivAt side v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  have he : -residualCuspDecayRate*(v/3)=-(residualCuspDecayRate/3)*v := by ring
  have hb1 := h1b (v/3) (z/3) (by linarith)
  have hbI := hIb (v/3) (z/3) (by linarith)
  rw [he] at hb1 hbI
  rw [horizontalWirtingerZ,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖Complex.I*(∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3))‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3)‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-(residualCuspDecayRate/3)*v)+
      CI*Real.exp (-(residualCuspDecayRate/3)*v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hbI) (by norm_num)
    _ = _ := by ring

lemma ramifiedConjugate_barProfile_isBigO (side:Bool) (z:ℂ) :
    cuspBarProfile (fun w => cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w)) z
      =O[atTop] (fun v:ℝ => Real.exp (-(residualCuspDecayRate/3)*v)) := by
  obtain ⟨C,hC,hb⟩ := ramifiedSource_wirtingerZ_cusp_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp:0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspBarProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖horizontalWirtingerBar (fun w => star (ramifiedSourceFunction
    (ramifiedCuspRoot side:Eis) (upperPoint w v hvp))) z‖ ≤ _
  rw [horizontalWirtingerBar_star,norm_star]
  exact hb v hvp z hv

lemma ramifiedConjugate_zProfile_isBigO (side:Bool) (z:ℂ) :
    cuspZProfile (fun w => cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w)) z
      =O[atTop] (fun v:ℝ => Real.exp (-(residualCuspDecayRate/3)*v)) := by
  obtain ⟨C,hC,hb⟩ := ramifiedSource_wirtingerBar_cusp_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp:0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖horizontalWirtingerZ (fun w => star (ramifiedSourceFunction
    (ramifiedCuspRoot side:Eis) (upperPoint w v hvp))) z‖ ≤ _
  rw [horizontalWirtingerZ_star,norm_star]
  exact hb v hvp z hv

end

local notation "Eis" => ActualEisensteinCubic.O

lemma reflectedCuspProfile_eq_inv_square (A:ℂ) (Q:ℝ) (g:ℝ→ℂ) (v:ℝ) :
    reflectedCuspProfile A Q g v=A/(v:ℂ)^2*g ((Q*v)⁻¹) := by
  unfold reflectedCuspProfile
  rw [Complex.cpow_neg,Complex.cpow_ofNat]
  ring

lemma reflectedCuspProfile_reverse (A:ℂ) (hA:A≠0) (Q:ℝ) (hQ:0<Q)
    (f g:ℝ→ℂ) (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v)
    (v:ℝ) (hv:0<v) :
    g v=reflectedCuspProfile (A⁻¹/(Q:ℂ)^2) Q f v := by
  have he:=hfg (Q*v)⁻¹ (by positivity)
  have harg:(Q*(Q*v)⁻¹)⁻¹=v := by field_simp
  rw [reflectedCuspProfile_eq_inv_square,harg] at he
  rw [reflectedCuspProfile_eq_inv_square,he,Complex.ofReal_inv,Complex.ofReal_mul]
  have hcQ:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hcv:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

theorem cusp_mellin_entire_both (f g:ℝ→ℂ) (A:ℂ) (hA:A≠0)
    (Q decayF decayG:ℝ) (hQ:0<Q) (hdecayF:0<decayF) (hdecayG:0<decayG)
    (hf:ContinuousOn f (Set.Ioi 0)) (hg:ContinuousOn g (Set.Ioi 0))
    (hfbound:f =O[atTop] (fun v:ℝ=>Real.exp (-decayF*v)))
    (hgbound:g =O[atTop] (fun v:ℝ=>Real.exp (-decayG*v)))
    (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    ((∀s:ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f)) ∧
    ((∀s:ℂ,MellinConvergent g s) ∧ Differentiable ℂ (mellin g)) := by
  constructor
  · exact cusp_mellin_entire f g A Q decayF decayG hQ hdecayF hdecayG
      hf hg hfbound hgbound hfg
  · exact cusp_mellin_entire g f (A⁻¹/(Q:ℂ)^2) Q decayG decayF hQ hdecayG hdecayF
      hg hf hgbound hfbound (reflectedCuspProfile_reverse A hA Q hQ f g hfg)

theorem conjugateSource_ramified_cusp_mellin_entire (side:Bool)
    (G:CubicKubota.levelThree) (g:SL(2,ℂ))
    (hfactor:g=complexMatrix G*integralComplexMatrix
      (lowerCuspMatrix (ramifiedCuspRoot side:Eis))) (hc:g 1 0≠0) :
    ((∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)))) ∧
    ((∀s:ℂ,MellinConvergent
      (cuspZProfile (fun w=>cubicSourceConjugateFunction
        (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
        (-g 1 1/g 1 0)) s) ∧
      Differentiable ℂ (mellin
        (cuspZProfile (fun w=>cubicSourceConjugateFunction
          (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
          (-g 1 1/g 1 0)))) := by
  have hchar:CubicKubota.complexCharacter G≠0 := by
    intro hz
    have hn:=CubicKubota.norm_complexCharacter G
    rw [hz,norm_zero] at hn
    norm_num at hn
  have hscalar : -star (CubicKubota.complexCharacter G)/(g 1 0)^2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  exact cusp_mellin_entire_both
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
      (-g 1 1/g 1 0))
    (-star (CubicKubota.complexCharacter G)/(g 1 0)^2) hscalar (‖g 1 0‖^2)
    residualCuspDecayRate (residualCuspDecayRate/3)
    (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualCuspDecayRate_pos
    (div_pos residualCuspDecayRate_pos (by norm_num))
    (cuspBarProfile_conjugate_continuousOn _)
    (cuspZProfile_conjugate_translate_continuousOn _ _)
    (cuspBarProfile_conjugate_isBigO _)
    (ramifiedConjugate_zProfile_isBigO side _)
    (fun v hv=>cuspBarProfile_conjugate_reflection G g _ hfactor hc v hv)

end CubicEisenstein

open scoped BigOperators Classical

namespace CompletedGauss

section
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem squarefree_cube_decomposition_unique {I J I' J':Ideal Eis}
    (hJ:J≠0) (hJ':J'≠0) (hI:Squarefree I) (hI':Squarefree I')
    (h:I*J^3=I'*J'^3) : I=I' ∧ J=J' := by
  have hf:=congrArg normalizedFactors h
  rw [normalizedFactors_mul hI.ne_zero (pow_ne_zero _ hJ),
    normalizedFactors_mul hI'.ne_zero (pow_ne_zero _ hJ'),
    normalizedFactors_pow,normalizedFactors_pow] at hf
  have hi:=(squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  have hi':=(squarefree_iff_nodup_normalizedFactors hI'.ne_zero).mp hI'
  have hc (P:Ideal Eis) :
      (normalizedFactors I).count P=(normalizedFactors I').count P ∧
      (normalizedFactors J).count P=(normalizedFactors J').count P := by
    have he:=congrArg (Multiset.count P) hf
    simp only [Multiset.count_add,Multiset.count_nsmul] at he
    have h1:=Multiset.nodup_iff_count_le_one.mp hi P
    have h2:=Multiset.nodup_iff_count_le_one.mp hi' P
    omega
  constructor
  · calc
      I=(normalizedFactors I).prod:=(Ideal.prod_normalizedFactors_eq_self hI.ne_zero).symm
      _=(normalizedFactors I').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).1))
      _=I':=Ideal.prod_normalizedFactors_eq_self hI'.ne_zero
  · calc
      J=(normalizedFactors J).prod:=(Ideal.prod_normalizedFactors_eq_self hJ).symm
      _=(normalizedFactors J').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).2))
      _=J':=Ideal.prod_normalizedFactors_eq_self hJ'

theorem primary_squarefree_cube_eq_iff {I J I' J':Ideal Eis}
    (hI:Squarefree I) (hI':Squarefree I')
    (hgI:primaryGenerator I≠0) (hgJ:primaryGenerator J≠0)
    (hgI':primaryGenerator I'≠0) (hgJ':primaryGenerator J'≠0) :
    primaryGenerator I*(primaryGenerator J)^3=
      primaryGenerator I'*(primaryGenerator J')^3 ↔ I=I' ∧ J=J' := by
  constructor
  · intro h
    have hleft:primaryGenerator (I*J^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI (pow_ne_zero _ hgJ)
    have hright:primaryGenerator (I'*J'^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI' (pow_ne_zero _ hgJ')
    have he:I*J^3=I'*J'^3:=by
      calc
        I*J^3=Ideal.span {primaryGenerator (I*J^3)}:=(primaryGenerator_spec _ hleft).1.symm
        _=Ideal.span {primaryGenerator (I'*J'^3)}:=by
          apply congrArg (fun z:Eis => (Ideal.span {z}:Ideal Eis))
          simpa only [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow] using h
        _=I'*J'^3:=(primaryGenerator_spec _ hright).1
    exact squarefree_cube_decomposition_unique
      (primaryGenerator_ne_zero_ideal J hgJ) (primaryGenerator_ne_zero_ideal J' hgJ') hI hI' he
  · rintro ⟨rfl,rfl⟩
    rfl

theorem primary_squarefree_cube_injective :
    Function.Injective (fun x:
      {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0} =>
        primaryGenerator x.1.val*(primaryGenerator x.2.val)^3) := by
  intro x y he
  have h:= (primary_squarefree_cube_eq_iff x.1.property.1 y.1.property.1
    x.1.property.2 x.2.property y.1.property.2 y.2.property).mp he
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

def besselSmoothingIntegrand (F : ℝ→ℂ) (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin V (s-1/2)*(X:ℂ)^(s-1/2)*continuedBesselDirichlet F q s

lemma besselSmoothingIntegrand_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) : Differentiable ℂ (besselSmoothingIntegrand F q V X) := by
  have hm := (CubicReflectionKernel.compact_source_mellin_differentiable V a b ha hVs hV).comp
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop)
  have hp : Differentiable ℂ (fun s : ℂ=>(X:ℂ)^(s-1/2)) :=
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (hm.mul hp).mul (continuedBesselDirichlet_differentiable F q hq hF)

lemma besselSmoothingIntegrand_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (lo hi : ℝ) (hF : ∀s : ℂ,MellinConvergent F s)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc lo hi →
      ‖besselSmoothingIntegrand F q V X s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cd,hCd,hd⟩ := continuedBesselDirichlet_strip_bound F q hq lo hi (hF _) (hF _)
  have hVc (s : ℂ) := CubicReflectionKernel.compact_source_mellin_convergent V a b ha hVs hV s
  obtain ⟨Cv,hCv,hv⟩ := VerticalContourShift.mellin_uniform_strip_bound V (lo-1/2) (hi-1/2)
    (hVc _) (hVc _)
  let Cx : ℝ := X^(lo-1/2)+X^(hi-1/2)
  have hCx : 0≤Cx := by dsimp [Cx];positivity
  refine ⟨Cv*Cx*Cd,mul_nonneg (mul_nonneg hCv hCx) hCd,?_⟩
  intro s hs
  have hvb : ‖mellin V (s-1/2)‖≤Cv := hv (s-1/2)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  have hxb : ‖(X:ℂ)^(s-1/2)‖≤Cx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have he : (s-1/2).re=s.re-1/2 := by simp
    rw [he]
    exact VerticalContourShift.rpow_between_endpoints X (lo-1/2) (hi-1/2) (s.re-1/2) hX
      (by linarith [hs.1]) (by linarith [hs.2])
  rw [besselSmoothingIntegrand,norm_mul,norm_mul]
  calc
    _≤(Cv*Cx)*(Cd*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hvb hxb (norm_nonneg _) hCv) (hd s hs)
        (norm_nonneg _) (mul_nonneg hCv hCx)
    _=_ := by ring

theorem besselSmoothingIntegrand_contour_eq (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent F s) (hFe : Differentiable ℂ (mellin F))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) (lo hi : ℝ) (hlh : lo≤hi)
    (hl : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I)))
    (hh : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I))) :
    (∫t : ℝ,besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I))=
      ∫t : ℝ,besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I) := by
  obtain ⟨C,hC,hb⟩ := besselSmoothingIntegrand_strip_bound F q hq lo hi hF V a b ha hVs hV X hX
  apply VerticalContourShift.integral_eq_of_exponential_strip_growth
    (besselSmoothingIntegrand F q V X) lo hi (2*Real.pi) C hlh (by positivity) hC
  · intro z hz1 hz2
    exact (besselSmoothingIntegrand_differentiable F q hq hFe V a b ha hVs hV X hX) z
  · exact hl
  · exact hh
  · intro σ hσ t
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,mul_one,zero_add] using
      hb ((σ:ℂ)+t*Complex.I) (by simpa using hσ)

theorem completedT_mellin_shift (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent (completedBesselProfile Ψ q) s)
    (hFe : Differentiable ℂ (mellin (completedBesselProfile Ψ q)))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) (lo : ℝ) (hl : lo≤2)
    (hleft : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I))) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I) := by
  have hid (t : ℝ) :
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)=
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
    rw [besselSmoothingIntegrand,continuedBesselDirichlet_eq_initial Ψ hΨ q hq _ (by norm_num)]
    rw [show (2:ℂ)+t*Complex.I-1/2=3/2+t*Complex.I by ring]
  have hr : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)) := by
    simp only [hid]
    exact completedT_initial_mellin_integrable Ψ hΨ W a b ha hWs hW X hX
  have he := besselSmoothingIntegrand_contour_eq (completedBesselProfile Ψ q) q hq hF hFe
    (Vstar W) a b ha (Vstar_support W a b hWs) (Vstar_contDiff W a b ha hWs hW)
    X hX lo 2 hl hleft hr
  rw [he]
  simpa only [Complex.ofReal_ofNat,hid] using
    completedT_initial_mellin Ψ hΨ W a b ha hWs hW X hX

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss
open CubicEisenstein

def besselReflectionFactor (q d : ℝ) (s : ℂ) : ℂ :=
  ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*(2:ℂ)^(2-4*s)/
    ((4*Real.pi*d:ℝ):ℂ)^(3-2*s)

lemma besselMellinFactor_reflection (q d : ℝ) (s : ℂ) :
    inverseBesselMellinFactor q s*besselMellinFactor d (1-s)=
      besselReflectionFactor q d s*CubicReflectionKernel.gammaMultiplier (1/2-s) := by
  have hp : (2:ℂ)^(1-2*s)*(2:ℂ)^(1-2*s)=(2:ℂ)^(2-4*s) := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  unfold inverseBesselMellinFactor besselMellinFactor besselReflectionFactor
    CubicReflectionKernel.gammaMultiplier
  rw [show (2:ℂ)*(1-s)-1=1-2*s by ring,
    show (2:ℂ)*(1-s)+1=3-2*s by ring,
    show (1:ℂ)-s+1/3=4/3-s by ring,
    show (1:ℂ)-s+2/3=5/3-s by ring,
    show (7/6:ℂ)+(1/2-s)=5/3-s by ring,
    show (5/6:ℂ)+(1/2-s)=4/3-s by ring,
    show (7/6:ℂ)-(1/2-s)=s+2/3 by ring,
    show (5/6:ℂ)-(1/2-s)=s+1/3 by ring]
  have he := congrArg (fun z : ℂ=>
    (((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*
      (Complex.Gamma (s+1/3))⁻¹*(Complex.Gamma (s+2/3))⁻¹*
      Complex.Gamma (4/3-s)*Complex.Gamma (5/3-s)*
      (((4*Real.pi*d:ℝ):ℂ)^(3-2*s))⁻¹)*z) hp
  simp only [div_eq_mul_inv,mul_inv_rev] at he ⊢
  linear_combination he

lemma besselReflectionFactor_norm (q d : ℝ) (hq : 0<q) (hd : 0<d) (s : ℂ) :
    ‖besselReflectionFactor q d s‖=
      (4*Real.pi*q)^(2*s.re+1)*(2:ℝ)^(2-4*s.re)/
        (4*Real.pi*d)^(3-2*s.re) := by
  unfold besselReflectionFactor
  have h2 : ‖(2:ℂ)^(2-4*s)‖=(2:ℝ)^(2-4*s.re) := by
    simpa only [Complex.ofReal_ofNat,show (2-4*s).re=2-4*s.re by simp] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ)) (2-4*s)
  rw [norm_div,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<4*Real.pi*q),
    h2,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<4*Real.pi*d)]
  norm_num

theorem continuedBesselDirichlet_reflection {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0< r i) (a : α→ℂ)
    (q d Q : ℝ) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (s : ℂ) (hs : s.re<4/3)
    (ha : Summable (fun i=>‖a i‖*(r i)^(s.re-1/2))) :
    continuedBesselDirichlet F q s=
      (A*(Q:ℂ)^(2-2*s)*besselReflectionFactor q d s)*
        CubicReflectionKernel.gammaMultiplier (1/2-s)*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by
  have hs' : -(1/3)<(1-s).re := by simp;linarith
  have ha' : Summable (fun i=>‖a i‖*(r i)^(1/2-(1-s).re)) := by
    convert ha using 1
    funext i
    congr 2
    simp
    ring
  have hm := radialBesselProfile_mellin r hr a d hd (1-s) hs' ha'
  have hc := cusp_mellin_reflection_of_identity F (radialBesselProfile r a d) A s Q hQ hreflect
  have hm' : mellin (radialBesselProfile r a d) (2-2*s)=
      besselMellinFactor d (1-s)*(∑'i,a i*(r i:ℂ)^(s-1/2)) := by
    calc
      _=mellin (radialBesselProfile r a d) (2*(1-s)) := by congr 1;ring
      _=_ := by simpa only [besselMellinFactor,show (1/2:ℂ)-(1-s)=s-1/2 by ring] using hm
  rw [hm'] at hc
  rw [continuedBesselDirichlet,hc]
  calc
    _=A*(Q:ℂ)^(2-2*s)*(inverseBesselMellinFactor q s*besselMellinFactor d (1-s))*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by ring
    _=_ := by rw [besselMellinFactor_reflection];ring

end CompletedGauss

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.DualKernelSummability -/

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

namespace CompletedGauss
open scoped BigOperators Classical ContDiff
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzeroDualIdeal_norm_pos (I : NonzeroDualIdeal) :
    0<(Ideal.absNorm I.val:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

lemma nonzeroDualIdeal_inv_pow_summable (n : ℕ) (hn : 1<n) :
    Summable (fun I : NonzeroDualIdeal => ((Ideal.absNorm I.val:ℝ)^n)⁻¹) := by
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (n:ℂ)
    (by exact_mod_cast hn)).subtype (fun I : Ideal Eis => I≠0)
  apply hs.congr
  intro I
  simp only [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property,
    Complex.cpow_neg,Complex.cpow_natCast,norm_inv,norm_pow,Complex.norm_natCast]

def rawDualKernelTerm (V : ℝ→ℂ) (scale ρ q : ℝ)
    (β : ℕ→Ideal Eis→Ideal Eis→ℂ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  β x.1 x.2.1.val x.2.2.val * CubicReflectionKernel.paperKernel V
    (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)

lemma rawDualKernel_inverse_square (scale ρ q : ℝ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ =
      (scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹) := by
  simp only [mul_pow,mul_inv_rev,←pow_mul,←inv_pow]
  ring

theorem rawDualKernelTerm_summable_norm
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (scale ρ q B : ℝ) (hscale : 0<scale) (hρ : 0<ρ) (hq : 1<q)
    (hB : 0≤B) (β : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hβ : ∀m,∀I J : NonzeroDualIdeal,‖β m I.val J.val‖≤B) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm V scale ρ q β x‖) := by
  obtain ⟨C,hC,hdec⟩:=CubicReflectionKernel.paperKernel_euler_power_decay
    V a b ha hsupp hV 2 0
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hij := hi.mul_of_nonneg hj (fun I=>by positivity) (fun J=>by positivity)
  have hs := hg.mul_of_nonneg hij (fun m=>by positivity) (fun IJ=>by positivity)
  have hmajor := hs.mul_left (B*C*(scale^2*ρ^6)⁻¹)
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  have hn:=nonzeroDualIdeal_norm_pos x.2.1
  have hb:=nonzeroDualIdeal_norm_pos x.2.2
  have hx : 0<scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3 := by positivity
  have hk := (hdec _ hx).2
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
  norm_num only [Nat.cast_ofNat] at hk
  have hr : (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^(-(2:ℝ))=
      ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
  rw [hr,rawDualKernel_inverse_square] at hk
  calc
    _ = ‖β x.1 x.2.1.val x.2.2.val‖*
        ‖CubicReflectionKernel.paperKernel V
          (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)‖ := by
        rw [rawDualKernelTerm,norm_mul]
    _ ≤ B*(C*((scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹))) :=
      mul_le_mul (hβ x.1 x.2.1 x.2.2) hk (norm_nonneg _) hB
    _ = _ := by ring

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

lemma canonical_dual_kernel_argument (K Y ρ q : ℝ) (i : ℕ×ℕ×ℕ)
    (k n b : Ideal Eis) (hK : 0<K) (hk : k≠0) (hn : n≠0) (hb : b≠0) :
    (Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
      Real.exp (-2*Real.log ((Ideal.absNorm k:ℝ)/K)+
        Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
        3*Real.log ((Ideal.absNorm b:ℝ)/(2:ℝ)^i.2.1)) =
    (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2)*(ρ*q^i.1)^3*
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 := by
  rw [positive_log_scale_identity _ _ _ _ _ _ _
    (nonzeroDualIdeal_norm_pos ⟨k,hk⟩) (nonzeroDualIdeal_norm_pos ⟨n,hn⟩)
    (nonzeroDualIdeal_norm_pos ⟨b,hb⟩) hK (by positivity) (by positivity)]
  unfold ramifiedScale
  field_simp

def canonicalRawBranchCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (ρ q : ℝ)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ) (k : Ideal Eis)
    (m : ℕ) (n b : Ideal Eis) : ℂ :=
  σ m*quadraticRow k (primaryGenerator (n*b))*
    reflectedDyadicCoefficient P hg j e (η m) (ramifiedScale ρ q m) n b

lemma canonicalRawBranchCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (ρ q : ℝ) (hρ : 0<ρ) (hq : 1≤q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal Eis) (m : ℕ) (n b : NonzeroDualIdeal) :
    ‖canonicalRawBranchCoefficient P hg j e ρ q η σ k m n.val b.val‖≤1/ρ := by
  have hn:=norm_at_least_one n.val n.property
  have hb:=norm_at_least_one b.val b.property
  have hr:=ramifiedScale_pos ρ q hρ (lt_of_lt_of_le zero_lt_one hq) m
  have hc:=reflectedDyadicCoefficient_norm P hg j e (η m) (ramifiedScale ρ q m) 1 1
    hr (by norm_num) (by norm_num) n.val b.val n.property b.property (hη m n b)
    (by linarith) (by linarith)
  have hdiv (v : Fin 3) : 1≤(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) :=
    norm_at_least_one _ (reflectionExtractedDivisor_ne_zero P (fun i=>NeZero.ne (P i)) j e v)
  have hroot : 1≤Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [hdiv 0,hdiv 2]
  have hrho : ρ≤ ramifiedScale ρ q m := by
    exact le_mul_of_one_le_right hρ.le (one_le_pow₀ hq)
  have hden := hrho.trans (le_mul_of_one_le_right hr.le hroot)
  simp only [Real.sqrt_one,one_mul] at hc
  have hcoeff:=hc.trans (div_le_div_of_nonneg_left (by norm_num) hρ hden)
  rw [canonicalRawBranchCoefficient,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (hσ m)).trans (quadraticRow_norm_le_one _ _))).trans hcoeff

theorem reflectedBranchBlock_canonical {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→idealRange K→ℂ)
    (i : ℕ×ℕ×ℕ) (k : idealRange K) (hK : 0<K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    reflectedBranchBlock P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k =
    ∑n : dualIdealDyad i.2.2, ∑b : dualIdealDyad i.2.1,
      rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val)
        (i.1,⟨n.val,((mem_dualIdealDyad _ _).mp n.property).1⟩,
          ⟨b.val,((mem_dualIdealDyad _ _).mp b.property).1⟩) := by
  have hkm:=mem_idealRange.mp k.property
  have hwk:=completedShellWindow_log (Ideal.absNorm k.val:ℝ) K
    (nonzeroDualIdeal_norm_pos ⟨k.val,hkm.1.1⟩) hK hk hkm.2
  simp only [reflectedBranchBlock,completedSmoothDyadicBlock,Finset.mul_sum]
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.2)]
  apply Finset.sum_congr rfl
  intro n _
  rw [←Finset.sum_coe_sort (dualIdealDyad i.2.1)]
  apply Finset.sum_congr rfl
  intro b _
  have hn:=dualIdealDyad_bounds _ n.val n.property
  have hb:=dualIdealDyad_bounds _ b.val b.property
  have hwn:=completedShellWindow_log (Ideal.absNorm n.val:ℝ) ((2:ℝ)^i.2.2)
    (nonzeroDualIdeal_norm_pos ⟨n.val,hn.1⟩) (by positivity) hn.2.1 hn.2.2
  have hwb:=completedShellWindow_log (Ideal.absNorm b.val:ℝ) ((2:ℝ)^i.2.1)
    (nonzeroDualIdeal_norm_pos ⟨b.val,hb.1⟩) (by positivity) hb.2.1 hb.2.2
  rw [hwk,hwn,hwb,canonical_dual_kernel_argument K Y ρ q i k.val n.val b.val hK hkm.1.1 hn.1 hb.1]
  simp only [rawDualKernelTerm,canonicalRawBranchCoefficient]
  ring

theorem canonicalRawBranch_summable_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m,‖σ m‖≤1) (k : Ideal Eis) (hk : k≠0) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η σ k) x‖) := by
  have hkn:=nonzeroDualIdeal_norm_pos ⟨k,hk⟩
  exact rawDualKernelTerm_summable_norm (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) _ ρ q (1/ρ) (by positivity) hρ hq (by positivity)
    _ (fun m n b=>canonicalRawBranchCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ k m n b)

theorem canonical_reflected_series {ι : Type*} [Fintype ι]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (K Y ρ q : ℝ) (hK : 0<K) (hY : 0<Y) (hρ : 0<ρ) (hq : 1<q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ) (σ : ℕ→idealRange K→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (hσ : ∀m k,‖σ m k‖≤1) (k : idealRange K)
    (hk : K/2≤(Ideal.absNorm k.val:ℝ)) :
    (∑'i : ℕ×ℕ×ℕ, reflectedBranchBlock P hg j e W K Y ρ q
      (fun l=>dualIdealDyad l.2.2) (fun l=>dualIdealDyad l.2.1)
      (fun l=>η l.1) (fun l=>σ l.1) i k) =
    ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
      rawDualKernelTerm (Vstar W) (Y⁻¹*(K/(Ideal.absNorm k.val:ℝ))^2) ρ q
        (canonicalRawBranchCoefficient P hg j e ρ q η (fun m=>σ m k) k.val) x := by
  have hs:=canonicalRawBranch_summable_norm P hg j e W a b ha hsupp hW K Y ρ q
    hK hY hρ hq η (fun m=>σ m k) hη (fun m=>hσ m k) k.val
    (mem_idealRange.mp k.property).1.1
  rw [tsum_dualIdealDyads _ hs.of_norm]
  apply tsum_congr
  intro i
  exact reflectedBranchBlock_canonical P hg j e W K Y ρ q η σ i k hK hk

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

namespace ReflectedBranchData

def withCanonicalCuspArray {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1) : ReflectedBranchData levelBound K I F Q :=
  { d with
    nColumns := fun i=>dualIdealDyad i.2.2
    bColumns := fun i=>dualIdealDyad i.2.1
    nBounds := fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
    bBounds := fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
    amplitude := fun i=>η i.1
    amplitude_bound := fun i n hn b hb=>hη i.1
      ⟨n,((mem_dualIdealDyad _ _).mp hn).1⟩ ⟨b,((mem_dualIdealDyad _ _).mp hb).1⟩
    rowPhase := fun i=>σ i.1
    rowPhase_bound := fun i k=>hσ i.1 k }

def rawValue {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  exact ∑'x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    rawDualKernelTerm (Vstar W)
      ((completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)⁻¹*
        (completedResidualScale K I Q/(Ideal.absNorm k.val:ℝ))^2) ρ q
      (canonicalRawBranchCoefficient (fun p : d.primes=>p.val) d.good
        (fun p=>completedLocalExponent I F p.val) d.label ρ q η (fun m=>σ m k) k.val) x

theorem withCanonicalCuspArray_value {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (η : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hη : ∀m,∀n b : NonzeroDualIdeal,‖η m n.val b.val‖≤1)
    (σ : ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hσ : ∀m k,‖σ m k‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X ρ q : ℝ) (hX : 0<X) (hρ : 0<ρ) (hq : 1<q)
    (hK : 0<completedResidualScale K I Q)
    (k : idealRange (completedResidualScale K I Q))
    (hk : completedResidualScale K I Q/2≤(Ideal.absNorm k.val:ℝ)) :
    (d.withCanonicalCuspArray η hη σ hσ).value W X ρ q k =
      d.rawValue η σ W X ρ q k := by
  let : ∀p : d.primes,p.val.IsMaximal:=d.maximal
  have hn (J : Ideal Eis) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) :=
    nonzeroDualIdeal_norm_pos ⟨J,hJ⟩
  have hprod:=hn (∏p : d.primes,p.val)
    (Finset.prod_ne_zero_iff.mpr (fun p _=>NeZero.ne p.val))
  have hd:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 1)
  have he:=hn _ (reflectionExtractedDivisor_ne_zero (fun p : d.primes=>p.val)
    (fun p=>NeZero.ne p.val) (fun p=>completedLocalExponent I F p.val) d.label 2)
  have hy : 0<completedBranchScale K (X/d.levelScale) I F Q
      (fun p : d.primes=>p.val) d.label := by
    unfold completedBranchScale
    have hl:=d.levelScale_pos
    positivity
  exact canonical_reflected_series (fun p : d.primes=>p.val) d.good
    (fun p=>completedLocalExponent I F p.val) d.label W a b ha hsupp hW
    (completedResidualScale K I Q)
    (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes=>p.val) d.label)
    ρ q hK hy hρ hq η σ hη hσ k hk

def restrictRows {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→Prop) :
    ReflectedBranchData levelBound K I F Q :=
  { d with
    rowPhase := fun i k=>if sector k then d.rowPhase i k else 0
    rowPhase_bound := by
      intro i k
      split_ifs
      · exact d.rowPhase_bound i k
      · simp }

theorem restrictRows_value {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→Prop)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    (d.restrictRows sector).value W X ρ q k =
      if sector k then d.value W X ρ q k else 0 := by
  by_cases hk:sector k
  · simp only [value,restrictRows,reflectedBranchBlock,ite_eq_left hk]
    rfl
  · simp only [value,restrictRows,reflectedBranchBlock,ite_eq_right hk,zero_mul,tsum_zero]

theorem sum_restrictRows_selected {ι : Type*} [Fintype ι] [DecidableEq ι]
    {levelBound K : ℝ} {I F Q : Ideal Eis}
    (d : ι→ReflectedBranchData levelBound K I F Q)
    (sector : idealRange (completedResidualScale K I Q)→ι)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) :
    (∑s : ι,((d s).restrictRows (fun k=>sector k=s)).value W X ρ q k)=
      (d (sector k)).value W X ρ q k := by
  calc
    _ = ((d (sector k)).restrictRows (fun k'=>sector k'=sector k)).value W X ρ q k := by
      apply Finset.sum_eq_single (sector k)
      · intro s _ hs
        rw [restrictRows_value,ite_eq_right (Ne.symm hs)]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = _ := by rw [restrictRows_value,ite_eq_left rfl]

end ReflectedBranchData

end CompletedGauss

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedFrequencyUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma ramifiedFrequencyChar_neg_unit (k:Eis) (u:Eisˣ) (n:ℕ) :
    ramifiedFrequencyChar k (-u) n=ramifiedFrequencyChar k u n := by
  ext x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hp:lambda^2∣(1+3*d)-1:=by
    rw [add_sub_cancel_left]
    exact dvd_mul_of_dvd_left lambda_sq_dvd_three d
  rw [ramifiedFrequencyChar_mk,ramifiedFrequencyChar_mk,Units.val_neg,neg_mul,
    symbol_neg_numerator _ _ hp]

lemma arithmeticResidueSum_neg_unit (h:Eis) (u:Eisˣ) (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum (-h) (u.val*lambda^n)=
      arithmeticResidueSum h ((-u).val*lambda^n) := by
  by_cases hd:u.val*lambda^n∣3*(-h)
  · obtain ⟨k,hk⟩:=hd
    have hk':3*h=((-u).val*lambda^n)*k:=by
      simp only [Units.val_neg]
      linear_combination -hk
    rw [ramified_arithmetic_character_test (-h) k u n hn hk,
      ramified_arithmetic_character_test h k (-u) n hn hk',ramifiedFrequencyChar_neg_unit]
  · have hl:arithmeticResidueSum (-h) (u.val*lambda^n)=0:=by
      by_contra he
      exact hd (ramified_arithmetic_support (-h) u n hn he)
    have hr:arithmeticResidueSum h ((-u).val*lambda^n)=0:=by
      by_contra he
      obtain ⟨k,hk⟩:=ramified_arithmetic_support h (-u) n hn he
      apply hd
      refine ⟨k,?_⟩
      simp only [Units.val_neg] at hk
      linear_combination -hk
    rw [hl,hr]

lemma principalResidueTerm_neg (h:Eis) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (-h) u n=principalResidueTerm h (-u) n := by
  unfold principalResidueTerm
  rw [arithmeticResidueSum_neg_unit h u (n+2) (by omega)]
  congr 2
  simp only [Units.val_neg]
  ring

lemma principalArithmeticResidue_neg (h:Eis) :
    principalArithmeticResidue (-h)=principalArithmeticResidue h := by
  by_cases hh:h=0
  · rw [hh,neg_zero]
  let N:=max (ramifiedFrequencyBound (-h)+1) (ramifiedFrequencyBound h+1)
  rw [principalArithmeticResidue_eq_sum (-h) (neg_ne_zero.mpr hh) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum h hh N (le_max_right _ _)]
  apply congrArg (fun z:ℂ=>z/((9*Real.sqrt 3/2:ℝ):ℂ))
  simp_rw [principalResidueTerm_neg]
  exact Fintype.sum_equiv (Equiv.neg Eisˣ)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h (-u) n)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h u n) (fun _=>rfl)

theorem sourceArithmeticResidue_neg (h:Eis) :
    sourceArithmeticResidue (-h)=sourceArithmeticResidue h := by
  have hU:unramifiedGaussResidue (-(9*h))=unramifiedGaussResidue (9*h):=by
    have he:=unramifiedGaussResidue_of_initial_relation (-(9*h)) (9*h) 0
      (fun _=>1) (fun _=>0) (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
      continuousAt_const continuousAt_const
      (fun s hs hi=>by simpa only [one_mul,zero_mul,add_zero] using unramifiedCubicGaussSeries_neg s (9*h))
    simpa only [one_mul,zero_mul,add_zero] using he
  simp only [sourceArithmeticResidue,cuspFrequency_neg,
    AddChar.map_neg_eq_inv,inv_eq_one,principalArithmeticResidue_neg,
    mul_neg,hU]

lemma cubicBesselNormalizer_neg (h:Eis) : cubicBesselNormalizer (-h)=cubicBesselNormalizer h := by
  simp only [cubicBesselNormalizer,cuspFrequency_neg,norm_neg]

theorem sourceResidualFourierCoefficient_neg (h:Eis) :
    sourceResidualFourierCoefficient (-h)=sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,sourceResidualFourierCoefficient,
    cubicBesselNormalizer_neg,sourceArithmeticResidue_neg]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_eq_one_iff_coordinate (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)=1 ↔
      (3:ℤ)∣(ActualEisensteinCoordinates.coords h).2 := by
  have he:ShortDraftTrace.breveE (cuspFrequency h)=
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ h):=by
    rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
    unfold cuspFrequency
    simp only [map_ofNat]
  rw [he,trace_third_coordinate]
  simpa only [pow_zero,one_mul,Nat.cast_zero,zero_add] using
    omega3_pow_exp_eq_one_iff 0 (ActualEisensteinCoordinates.coords h).2

lemma primary_or_negative_primary_of_source_mask (h:Eis) (h3:¬(3:Eis)∣h)
    (hphase:ShortDraftTrace.breveE (cuspFrequency h)=1) :
    lambda^2∣h-1 ∨ lambda^2∣(-h)-1 := by
  let a:ℤ:=(ActualEisensteinCoordinates.coords h).1
  let b:ℤ:=(ActualEisensteinCoordinates.coords h).2
  have heval:h=(a:Eis)+(b:Eis)*omega:=
    (ActualEisensteinCoordinates.eval_coords h).symm
  obtain ⟨B,hB⟩:=(sourceRayPhase_eq_one_iff_coordinate h).mp hphase
  have hBc:(b:Eis)=3*(B:Eis):=by exact_mod_cast hB
  have ha:¬(3:ℤ)∣a:=by
    rintro ⟨A,hA⟩
    apply h3
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hAc,hBc]
    ring
  have hcases:(3:ℤ)∣a-1 ∨ (3:ℤ)∣a+1:=by omega
  rcases hcases with ⟨A,hA⟩|⟨A,hA⟩
  · left
    apply lambda_sq_dvd_three.trans
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)-1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination hAc
  · right
    apply lambda_sq_dvd_three.trans
    refine ⟨-((A:Eis)+(B:Eis)*omega),?_⟩
    have hAc:(a:Eis)+1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination -hAc

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceFourier_supported_three_of_base_zero (hC:infinityCoefficientScalar=0)
    (h:Eis) (h3:¬(3:Eis)∣h) : sourceResidualFourierCoefficient h=0 := by
  by_cases hm:ShortDraftTrace.breveE (cuspFrequency h)=1
  · rcases primary_or_negative_primary_of_source_mask h h3 hm with hh|hh
    · exact sourceFourier_primary_zero_of_base_zero hC h hh
    · rw [←sourceResidualFourierCoefficient_neg h]
      exact sourceFourier_primary_zero_of_base_zero hC (-h) hh
  · simp only [sourceResidualFourierCoefficient,sourceArithmeticResidue,ite_eq_right hm,mul_zero]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem infinityCoefficientScalar_ne_zero : infinityCoefficientScalar≠0 := by
  intro hC
  obtain ⟨h,h3,hn⟩:=exists_source_coefficient_not_three
  exact hn (sourceFourier_supported_three_of_base_zero hC h h3)

lemma sourceResidualFourierCoefficient_one_ne_zero : sourceResidualFourierCoefficient 1≠0 := by
  intro h
  exact infinityCoefficientScalar_ne_zero (by simp only [infinityCoefficientScalar,h,star_zero])

lemma sourceArithmeticResidue_one_ne_zero : sourceArithmeticResidue 1≠0 := by
  intro h
  exact sourceResidualFourierCoefficient_one_ne_zero (by rw [sourceResidualFourierCoefficient,h,mul_zero])

theorem normalized_infinityCoefficient_squarefree_cube (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    infinityCoefficientScalar⁻¹*
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [infinityCoefficient_squarefree_cube I J hI hJ hsq]
  simp only [←mul_assoc,inv_mul_cancel₀ infinityCoefficientScalar_ne_zero,one_mul]

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations -/

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

namespace CompletedGauss
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

open CubicEisenstein

lemma positive_cpow_comp_continuous (r : ℝ) (hr : 0< r)
    (f : ℝ→ℂ) (hf : Continuous f) : Continuous (fun t=>(r:ℂ)^(f t)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp hf

theorem besselSmoothingIntegrand_reflected_integrable {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0< r i) (a : α→ℂ)
    (q d Q : ℝ) (hq : 0<q) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has : Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V : ℝ→ℂ) (v0 v1 : ℝ) (hv0 : 0<v0)
    (hVs : Function.support V⊆Set.Icc v0 v1) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) := by
  let P : ℝ→ℂ := fun t=>
    A*(Q:ℂ)^(2-2*((-1:ℂ)+t*Complex.I))*
      besselReflectionFactor q d ((-1:ℂ)+t*Complex.I)*
        (X:ℂ)^(((-1:ℂ)+t*Complex.I)-1/2)
  let D : ℝ→ℂ := fun t=>∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+(-t)*Complex.I))
  let K : ℝ→ℂ := fun t=>CubicReflectionKernel.mellinEulerData V 0 ((3/2:ℂ)+(-t)*Complex.I)
  have hK : Integrable K := by
    have hh := CubicReflectionKernel.mellinEulerData_vertical_integrable V v0 v1 hv0 hVs hV
      2 0 (3/2) (by norm_num)
    simpa only [K,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh.comp_neg
  have hD : Continuous D := by
    have hh := (weighted_vertical_series_continuous r hr a (3/2) has).comp continuous_neg
    simpa only [D,Function.comp_def,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh
  have hDb (t : ℝ) : ‖D t‖≤∑'i,‖a i‖*(r i)^(-(3/2:ℝ)) := by
    simpa only [D,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      weighted_vertical_series_norm r hr a (3/2) has (-t)
  have hP : Continuous P := by
    have h1 := positive_cpow_comp_continuous Q hQ
      (fun t : ℝ=>2-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h2 := positive_cpow_comp_continuous (4*Real.pi*q) (by positivity)
      (fun t : ℝ=>2*((-1:ℂ)+t*Complex.I)+1) (by fun_prop)
    have h3 := positive_cpow_comp_continuous 2 (by norm_num)
      (fun t : ℝ=>2-4*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h4 := positive_cpow_comp_continuous (4*Real.pi*d) (by positivity)
      (fun t : ℝ=>3-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h5 := positive_cpow_comp_continuous X hX
      (fun t : ℝ=>((-1:ℂ)+t*Complex.I)-1/2) (by fun_prop)
    have hn (t : ℝ) : (((4*Real.pi*d:ℝ):ℂ)^(3-2*((-1:ℂ)+t*Complex.I)))≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
    convert (((continuous_const (y:=A)).mul h1).mul ((h2.mul h3).div h4 hn)).mul h5 using 1 ;
      (ext t; simp only [P,besselReflectionFactor,Pi.mul_apply,Pi.div_apply,Complex.ofReal_ofNat])
  have hPn (t : ℝ) : ‖P t‖=‖P 0‖ := by
    simp only [P,norm_mul,besselReflectionFactor_norm q d hq hd,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ,Complex.norm_cpow_eq_rpow_re_of_pos hX]
    norm_num
  have hi := (hK.mul_bdd hP.aestronglyMeasurable
    (Eventually.of_forall (fun t=>(hPn t).le))).mul_bdd hD.aestronglyMeasurable
      (Eventually.of_forall hDb)
  apply hi.congr
  filter_upwards with t
  have he : ((-1:ℂ)+t*Complex.I).re-1/2=-(3/2:ℝ) := by norm_num
  have hsum : Summable (fun i=>‖a i‖*(r i)^(((-1:ℂ)+t*Complex.I).re-1/2)) := by
    simpa only [he] using has
  have href := continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect
    ((-1:ℂ)+t*Complex.I) (by norm_num) hsum
  change K t*P t*D t=besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)
  rw [besselSmoothingIntegrand,href]
  dsimp only [K,P,D]
  unfold CubicReflectionKernel.mellinEulerData CubicReflectionKernel.mellinData
  simp only [pow_zero,one_mul]
  have he1 : (1/2:ℂ)-((-1:ℂ)+t*Complex.I)=(3/2:ℂ)+(-t)*Complex.I := by ring
  have he2 : ((-1:ℂ)+t*Complex.I)-1/2=-((3/2:ℂ)+(-t)*Complex.I) := by ring
  rw [he1,he2]
  ring

end CompletedGauss

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteTranslationMultiplier {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) : ℂ :=
  ∑i,weight i*ShortDraftTrace.breveE (cuspFrequency h*shift i)

lemma finiteTranslationMultiplier_norm {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) :
    ‖finiteTranslationMultiplier shift weight h‖≤∑i,‖weight i‖ := by
  unfold finiteTranslationMultiplier
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,breveE_norm,mul_one]

namespace SubexponentialBesselCoefficients

def finiteTranslate {ι : Type*} [Fintype ι] (coeff : SubexponentialBesselCoefficients)
    (shift weight : ι→ℂ) : SubexponentialBesselCoefficients where
  value h := finiteTranslationMultiplier shift weight h*coeff.value h
  growth epsilon he := by
    obtain ⟨C,hC,hbound⟩:=coeff.growth epsilon he
    refine ⟨(∑i,‖weight i‖)*C,by positivity,?_⟩
    intro h hh
    rw [norm_mul]
    calc
      _ ≤ (∑i,‖weight i‖)*(C*Real.exp (epsilon*‖cuspFrequency h‖)) :=
        mul_le_mul (finiteTranslationMultiplier_norm shift weight h) (hbound h hh)
          (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by ring

lemma term_horizontal_translate (coeff : SubexponentialBesselCoefficients)
    (h : Eis) (v : ℝ) (z a : ℂ) :
    coeff.term h (v,z+a)=ShortDraftTrace.breveE (cuspFrequency h*a)*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [term,ite_eq_left hh,mul_zero]
  · simp only [term,ite_eq_right hh,mul_add,AddChar.map_add_eq_mul]
    ring

lemma finiteTranslate_term {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      ∑i,weight i*coeff.term h (v,z+shift i) := by
  simp_rw [term_horizontal_translate]
  rw [show (∑i,weight i*(ShortDraftTrace.breveE (cuspFrequency h*shift i)*coeff.term h (v,z)))=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) by
    simp only [finiteTranslationMultiplier,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  by_cases hh:h=0
  · simp only [term,ite_eq_left hh,mul_zero]
  · simp only [term,ite_eq_right hh,finiteTranslate]
    ring

theorem finiteTranslate_series {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    (coeff.finiteTranslate shift weight).series (v,z)=
      ∑i,weight i*coeff.series (v,z+shift i) := by
  simp only [series,finiteTranslate_term]
  rw [Summable.tsum_finsetSum (fun i hi=>(coeff.summable (v,z+shift i) hv).mul_left (weight i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact tsum_mul_left

theorem finiteTranslate_fullFunction {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ) (constant : ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    (coeff.finiteTranslate shift weight).fullFunction ((∑i,weight i)*constant) (upperPoint z v hv)=
      ∑i,weight i*coeff.fullFunction constant (upperPoint (z+shift i) v hv) := by
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    finiteTranslate_series coeff shift weight v hv,Finset.sum_mul,mul_add,
    Finset.sum_add_distrib]
  have hconst : (∑i,weight i*constant*(v:ℂ)^(2/3:ℂ))=
      ∑i,constant*(v:ℂ)^(2/3:ℂ)*weight i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hconst]
  ring_nf

end SubexponentialBesselCoefficients

theorem cubicSource_finite_translation {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    (∑i,weight i*cubicSourceResidualFunction (upperPoint (z+shift i) v hv))=
      (sourceBesselCoefficients.finiteTranslate shift weight).fullFunction
        ((∑i,weight i)*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv) := by
  simp only [cubicSourceResidualFunction_eq_bessel,sourceBesselFunction]
  exact (sourceBesselCoefficients.finiteTranslate_fullFunction shift weight _ v hv z).symm

end

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteAdditiveFourierCoeff {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (h : R) : ℂ :=
  (∑x,φ x*ψ (-h*x))/(Fintype.card R:ℂ)

lemma finiteAdditiveFourier_inversion {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (φ : R→ℂ) (x : R) :
    (∑h,finiteAdditiveFourierCoeff ψ φ h*ψ (h*x))=φ x := by
  have hN : (Fintype.card R:ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (∑h,∑y,φ y*ψ (-h*y)*ψ (h*x))/(Fintype.card R:ℂ) := by
      simp only [finiteAdditiveFourierCoeff,div_mul_eq_mul_div,Finset.sum_mul,Finset.sum_div]
    _ = (∑y,φ y*∑h,ψ (h*(x-y)))/(Fintype.card R:ℂ) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [mul_assoc,←AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))/(Fintype.card R:ℂ) := by
      simp only [AddChar.sum_mulShift _ hψ,apply_ite,Nat.cast_zero]
    _ = φ x := by
      have he : (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))=
          φ x*(Fintype.card R:ℂ) := by
        simp [sub_eq_zero]
      rw [he,mul_div_cancel_right₀ _ hN]

lemma finiteAdditiveFourierCoeff_norm {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (hφ : ∀x,‖φ x‖≤1) (h : R) :
    ‖finiteAdditiveFourierCoeff ψ φ h‖≤1 := by
  have hN : (0:ℝ)<Fintype.card R:=by exact_mod_cast Fintype.card_pos
  rw [finiteAdditiveFourierCoeff,norm_div,Complex.norm_natCast]
  apply (div_le_one hN).mpr
  calc
    _ ≤ ∑x,‖φ x*ψ (-h*x)‖ := norm_sum_le _ _
    _ ≤ ∑_x : R,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [norm_mul,AddChar.norm_apply,mul_one] using hφ x
    _ = _ := by simp

def thetaFourierTranslation (c : Eis) (h : Eis⧸Ideal.span {c}) : ℂ :=
  ConcreteTraceCRT.eisLam^2*ConcreteTraceCRT.eisEmbedding (Quotient.out h)/
    ConcreteTraceCRT.eisEmbedding c

lemma thetaFourierTranslation_phase (c : Eis) (hc : c≠0)
    (h : Eis⧸Ideal.span {c}) (x : Eis) :
    ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h)=
      quotientTrace c hc (h*Ideal.Quotient.mk _ x) := by
  have hm : h*Ideal.Quotient.mk _ x=Ideal.Quotient.mk _ (Quotient.out h*x) := by
    rw [map_mul,Ideal.Quotient.mk_out]
  rw [hm]
  simp only [quotientTrace,ConcreteTraceCRT.eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency thetaFourierTranslation
  rw [map_mul]
  have hc0:=ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hl:=ConcreteTraceCRT.eisLam_ne_zero
  field_simp
  linear_combination -(ConcreteTraceCRT.eisEmbedding x*
    ConcreteTraceCRT.eisEmbedding (Quotient.out h))*TraceLambdaPhase.eisLam_sq

lemma thetaFourierTranslation_inversion (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ) (x : Eis) :
    (∑h,finiteAdditiveFourierCoeff (quotientTrace c hc) φ h*
      ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h))=
      φ (Ideal.Quotient.mk _ x) := by
  simp only [thetaFourierTranslation_phase c hc]
  exact finiteAdditiveFourier_inversion (quotientTrace c hc)
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) φ _

end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma breveE_star (z : ℂ) : star (ShortDraftTrace.breveE z)=ShortDraftTrace.breveE (-z) := by
  change (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(z+starRingEnd ℂ z)))=
    Complex.exp (2*Real.pi*Complex.I*((-z)+starRingEnd ℂ (-z)))
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,map_add,map_neg,map_ofNat,Complex.conj_ofReal,Complex.conj_I,
    starRingEnd_self_apply]
  ring

lemma finiteTranslationMultiplier_star {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) :
    star (finiteTranslationMultiplier shift (fun i=>star (weight i)) h)=
      ∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i) := by
  simp only [finiteTranslationMultiplier,star_sum,star_mul,star_star,breveE_star,neg_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma finiteTranslate_term_multiplier {ι : Type*} [Fintype ι]
    (coeff : SubexponentialBesselCoefficients) (shift weight : ι→ℂ)
    (h : Eis) (v : ℝ) (z : ℂ) :
    (coeff.finiteTranslate shift weight).term h (v,z)=
      finiteTranslationMultiplier shift weight h*coeff.term h (v,z) := by
  by_cases hh:h=0
  · simp only [SubexponentialBesselCoefficients.term,ite_eq_left hh,mul_zero]
  · simp only [SubexponentialBesselCoefficients.term,ite_eq_right hh,
      SubexponentialBesselCoefficients.finiteTranslate]
    ring

def finiteConjugateSource {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  ∑i,weight i*cubicSourceConjugateFunction (upperPoint (z+shift i) v hv)

lemma finiteConjugateSource_eq_bessel {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    finiteConjugateSource shift weight v hv z=
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) := by
  rw [sourceBesselCoefficients.finiteTranslate_fullFunction]
  simp only [star_sum,star_mul,star_star,finiteConjugateSource,cubicSourceConjugateFunction,
    cubicSourceResidualFunction_eq_bessel,sourceBesselFunction]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteConjugateSource_wirtingerBar {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (finiteConjugateSource shift weight v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        (∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i))*
          star (sourceBesselCoefficients.term h (v,z)) := by
  have hf : finiteConjugateSource shift weight v hv = fun z=>
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) :=
    funext (finiteConjugateSource_eq_bessel shift weight v hv)
  rw [hf,horizontalWirtingerBar_star,
    SubexponentialBesselCoefficients.fullFunction_wirtingerZ,tsum_star]
  apply tsum_congr
  intro h
  rw [finiteTranslate_term_multiplier,star_mul,star_mul,finiteTranslationMultiplier_star]
  have hphase : star (2*Real.pi*Complex.I*cuspFrequency h)=
      -2*Real.pi*Complex.I*star (cuspFrequency h) := by
    simp only [star_mul,Complex.star_def,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
    ring
  rw [hphase]
  ring

def traceTwistedConjugateSource (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  finiteConjugateSource (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) φ) v hv z

theorem traceTwistedConjugateSource_wirtingerBar (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        φ (Ideal.Quotient.mk _ h)*star (sourceBesselCoefficients.term h (v,z)) := by
  change horizontalWirtingerBar (finiteConjugateSource (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) φ) v hv) z = _
  rw [finiteConjugateSource_wirtingerBar]
  simp only [thetaFourierTranslation_inversion c hc]

theorem traceTwistedConjugateSource_wirtingerBar_zero (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (traceTwistedConjugateSource c hc φ v hv) 0=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        φ (Ideal.Quotient.mk _ h)*star (sourceResidualFourierCoefficient h)*
          (v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  rw [traceTwistedConjugateSource_wirtingerBar]
  apply tsum_congr
  intro h
  by_cases hh:h=0
  · subst h
    simp [cuspFrequency]
  · rw [sourceBesselCoefficients.term_bessel h hh v hv]
    have hx : 0<4*Real.pi*‖cuspFrequency h‖*v :=
      mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))) hv
    rw [schlafliBesselK_cubic_real _ hx]
    have he0 : ShortDraftTrace.breveE (0:ℂ)=1 := by
      simp [ShortDraftTrace.breveE]
    simp only [mul_zero,he0,mul_one,star_mul,
      Complex.star_def,Complex.conj_ofReal,sourceBesselCoefficients]
    ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def fixedThetaTwist (Ψ : Eis→*ℂ) (x : Eis) : ℂ :=
  if lambda^2∣x-1 then eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x else 0

lemma fixedThetaTwist_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : lambda^2∣x-1) :
    fixedThetaTwist Ψ x=eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x := by
  simp only [fixedThetaTwist,ite_eq_left hx]

lemma fixedThetaTwist_not_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : ¬lambda^2∣x-1) :
    fixedThetaTwist Ψ x=0 := by
  simp only [fixedThetaTwist,ite_eq_right hx]

lemma paperLambda_symbol_cube (x : Eis) (hx : lambda^2∣x-1) :
    (eisEmbedding (symbol ramifiedTraceLambda x))^3=1 := by
  rw [←map_pow,symbol_cube_of_isCoprime _ _ hx
    (ramified_character_coprime 0 1 _ x (Or.inl (by simp)) hx),map_one]

lemma paperLambda_symbol_norm (x : Eis) (hx : lambda^2∣x-1) :
    ‖eisEmbedding (symbol ramifiedTraceLambda x)‖=1 := by
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one,one_pow] using congrArg norm (paperLambda_symbol_cube x hx)

lemma fixedThetaTwist_norm_le_one (Ψ : Eis→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1) (x : Eis) :
    ‖fixedThetaTwist Ψ x‖≤1 := by
  by_cases hx : lambda^2∣x-1
  · rw [fixedThetaTwist_primary Ψ x hx,norm_mul,paperLambda_symbol_norm x hx,one_mul]
    exact hΨ x
  · rw [fixedThetaTwist_not_primary Ψ x hx,norm_zero]
    norm_num

theorem fixedThetaTwist_periodic (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (x y : Eis)
    (hxy : x-y∈Ideal.span {(9:Eis)}*Q) : fixedThetaTwist Ψ x=fixedThetaTwist Ψ y := by
  have h9 : (9:Eis)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)
  have hd : lambda^2∣x-y := lambda_sq_dvd_three.trans ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9)
  have hp : lambda^2∣x-1 ↔ lambda^2∣y-1 := by
    constructor
    · intro hx
      convert dvd_sub hx hd using 1 ; ring
    · intro hy
      convert dvd_add hd hy using 1 ; ring
  by_cases hx : lambda^2∣x-1
  · have hy := hp.mp hx
    rw [fixedThetaTwist_primary Ψ x hx,fixedThetaTwist_primary Ψ y hy,
      hΨ x y (Ideal.mul_le_right hxy)]
    congr 2
    exact CubicRamified.symbol_traceLambda_congr_mod_nine x y hx hy h9
  · rw [fixedThetaTwist_not_primary Ψ x hx,
      fixedThetaTwist_not_primary Ψ y (fun hy=>hx (hp.mpr hy))]

def fixedThetaQuotient (Ψ : Eis→*ℂ) (c : Eis) (x : Eis⧸Ideal.span {c}) : ℂ :=
  fixedThetaTwist Ψ (Quotient.out x)

lemma fixedThetaQuotient_mk (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (c : Eis)
    (hc : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (x : Eis) :
    fixedThetaQuotient Ψ c (Ideal.Quotient.mk _ x)=fixedThetaTwist Ψ x := by
  apply fixedThetaTwist_periodic Ψ Q hΨ
  exact hc (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) x)))

lemma fixedThetaQuotient_norm_le_one (Ψ : Eis→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1)
    (c : Eis) (x : Eis⧸Ideal.span {c}) : ‖fixedThetaQuotient Ψ c x‖≤1 :=
  fixedThetaTwist_norm_le_one Ψ hΨ _

lemma paperLambda_symbol_squarefree_cube (n b : Eis) (hb : lambda^2∣b-1) :
    eisEmbedding (symbol ramifiedTraceLambda (n*b^3))=
      eisEmbedding (symbol ramifiedTraceLambda n) := by
  rw [symbol_mul_denominator,cubicSymbol_pow_denominator,map_mul,map_pow,
    paperLambda_symbol_cube b hb,mul_one]

theorem fixedThetaTwist_infinity_coefficient (Ψ : Eis→*ℂ) (I J : Ideal Eis)
    (hI : primaryGenerator I≠0) (hJ : primaryGenerator J≠0) (hsq : Squarefree I) :
    infinityCoefficientScalar⁻¹ *
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))*
        fixedThetaTwist Ψ (primaryGenerator I*(primaryGenerator J)^3)=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*gaussTwo I hI*
        Ψ (primaryGenerator I)*(Ψ (primaryGenerator J))^3 := by
  have hn := (primaryGenerator_spec I hI).2
  have hb := (primaryGenerator_spec J hJ).2
  have hnb : lambda^2∣primaryGenerator I*(primaryGenerator J)^3-1 :=
    CubicJacobiGlobal.primary_mul _ _ hn (primary_pow_congruence _ hb 3)
  rw [normalized_infinityCoefficient_squarefree_cube I J hI hJ hsq,
    fixedThetaTwist_primary Ψ _ hnb,paperLambda_symbol_squarefree_cube _ _ hb,map_mul,map_pow]
  have hunit : star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
      eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I))=1 := by
    simpa only [Complex.star_def,paperLambda_symbol_norm _ hn,one_pow,
      Complex.ofReal_one] using Complex.conj_mul' (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))
  calc
    _ = (star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
        eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*
        ((‖eisEmbedding (primaryGenerator J)‖:ℂ)*gaussTwo I hI*
          Ψ (primaryGenerator I)*(Ψ (primaryGenerator J))^3) := by ring
    _ = _ := by rw [hunit,one_mul]

end

open ActualEisensteinCubic CompletedGauss CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFourier_primary_squarefree_cube_preimage (x:Eis)
    (hx:lambda^2∣x-1) (hT:sourceResidualFourierCoefficient x≠0) :
    ∃p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0}),
      primaryGenerator p.1.val*(primaryGenerator p.2.val)^3=x := by
  have hx0:x≠0:=primary_ne_zero x hx
  have hgen:primaryGenerator (Ideal.span {x})=x:=primaryGenerator_span x hx0 hx
  have hg:primaryGenerator (Ideal.span {x})≠0:=by rwa [hgen]
  have ht:sourceResidualFourierCoefficient (primaryGenerator (Ideal.span {x}))≠0:=by
    rwa [hgen]
  obtain ⟨I,J,hI,hgI,hgJ,hIJ⟩:=sourceFourier_squarefree_cube_support (Ideal.span {x}) hg ht
  refine ⟨(⟨I,hI,hgI⟩,⟨J,hgJ⟩),?_⟩
  have he:=congrArg primaryGenerator hIJ
  simpa only [primaryGenerator_mul,primaryGenerator_pow,hgen] using he

theorem sourceFourier_tsum_primary_pairs (w:Eis→ℂ)
    (hw:∀x:Eis,w x≠0→lambda^2∣x-1) :
    (∑'x:Eis,w x*star (sourceResidualFourierCoefficient x))=
      ∑'p:({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
        {J:Ideal Eis // primaryGenerator J≠0}),
        w (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)*
          star (sourceResidualFourierCoefficient
            (primaryGenerator p.1.val*(primaryGenerator p.2.val)^3)) := by
  let P:=({I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
    {J:Ideal Eis // primaryGenerator J≠0})
  let phi:P→Eis:=fun p=>primaryGenerator p.1.val*(primaryGenerator p.2.val)^3
  let f:Eis→ℂ:=fun x=>w x*star (sourceResidualFourierCoefficient x)
  change (∑'x:Eis,f x)=∑'p:P,f (phi p)
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun p:Function.support (fun p:P=>f (phi p))=>phi p.val)
  · exact primary_squarefree_cube_injective.comp Subtype.val_injective
  · intro x hx
    have hwx:w x≠0:=by
      intro hz
      exact hx (by simp only [f,hz,zero_mul])
    have hTx:sourceResidualFourierCoefficient x≠0:=by
      intro hz
      exact hx (by simp only [f,hz,star_zero,mul_zero])
    obtain ⟨p,hp⟩:=sourceFourier_primary_squarefree_cube_preimage x (hw x hwx) hTx
    have hphi:phi p=x:=hp
    have hfp:f (phi p)≠0:=by rwa [hphi]
    exact ⟨⟨p,hfp⟩,hphi⟩
  · intro p
    rfl

end CubicEisenstein

end

end OAI

end

