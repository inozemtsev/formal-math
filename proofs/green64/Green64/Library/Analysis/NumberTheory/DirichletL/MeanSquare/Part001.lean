module

public import Green64.Library.OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
public import Green64.Library.OAI.NumberTheory.DirichletL.GaussSum.PowerfulParts

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / MeanSquare / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.LogarithmicBins -/

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

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FourierBridge (logPhase)

def initialOuterWeight {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (q : Frequency) (x : SecondExpansionData ι) : ℂ :=
  w x * outerWindow V (z x) (ud x) (ue x) (uv x) (kap x) *
    logPhase (q.1 + q.2.1) (z x) * logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)

lemma initialOuterWeight_continuous {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (x : SecondExpansionData ι) :
    Continuous (fun q => initialOuterWeight V w z ud ue uv kap q x) := by
  have h₁ : Continuous (fun q : Frequency => logPhase (q.1 + q.2.1) (z x)) :=
    (FourierBridge.logPhase_continuous_left (z x)).comp
    (continuous_fst.add continuous_snd.fst)
  have h₂ : Continuous (fun q : Frequency => logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)) :=
    (FourierBridge.logPhase_continuous_left (kap x - ud x - 2 * ue x - 2 * uv x)).comp
    continuous_snd.snd
  unfold initialOuterWeight
  fun_prop

lemma initialOuterWeight_norm {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (q : Frequency) (x : SecondExpansionData ι) :
    ‖initialOuterWeight V w z ud ue uv kap q x‖ =
      ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ := by
  simp only [initialOuterWeight, norm_mul, FourierBridge.logPhase_norm, mul_one]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def initialSourceSum (s : Finset (SecondExpansionData ι)) (w : SecondExpansionData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : SecondExpansionData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2
    (sourceObservation p x).1 (-(sourceObservation p x).1) A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem initialSource_eq_integrated
    (s : Finset (SecondExpansionData ι)) (w : SecondExpansionData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W b : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : SecondExpansionData ι → ℝ) (X₁ X₂ R : ℝ)
    (hsep : ∀ x ∈ s,
      postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R =
      separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
        A₁ A₂ b V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂) :
    initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      integratedSourceMode p hp hcop hg (𝓕 A₁) (𝓕 A₂) b s
        (initialOuterWeight V w z ud ue uv kap) F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ := by
  let Q : SecondExpansionData ι → Frequency → ℂ := fun x q =>
    initialOuterWeight V w z ud ue uv kap q x *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ q.1 q.2.2 true) (sourceObservation p x).2 (sourceObservation p x).1) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ q.2.1 q.2.2 false) (sourceObservation p x).2 (-(sourceObservation p x).1)
  let M : SecondExpansionData ι → ℝ := fun x =>
    (‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖) *
      rowMagnitude p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true *
      rowMagnitude p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
  have hc (x : SecondExpansionData ι) : Continuous (Q x) := by
    have hw := initialOuterWeight_continuous V w z ud ue uv kap x
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hw.mul h₁.star).mul h₂
  have hbound (x : SecondExpansionData ι) (q : Frequency) : ‖Q x q‖ ≤ M x := by
    dsimp only [Q, M]
    rw [norm_mul, norm_mul, norm_star, initialOuterWeight_norm]
    have h₁ := fixedRow_norm_le p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ q.1 q.2.2 true
    have h₂ := fixedRow_norm_le p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ q.2.1 q.2.2 false
    have hn₁ := rowMagnitude_nonneg p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true
    have hn₂ := rowMagnitude_nonneg p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
    gcongr
  calc
    _ = ∑ x ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * Q x (t₁,t₂,t₃) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsep x hx]
      unfold separatedPostCommon
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      dsimp [tripleCoefficient, Q, initialOuterWeight]
      ring
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * (∑ x ∈ s, Q x (t₁,t₂,t₃)) :=
      finite_triple_bounded_integral s (𝓕 A₁) (𝓕 A₂) b Q (fun x _ => hc x) M (fun x _ => hbound x)
    _ = _ := rfl

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

theorem initial_source_uniform_transfer (ε : ℝ) (hε : 0<ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (M : Fin 7→ℝ)
    (hM : ∀j,0≤M j) (hV : ∀j x,V j x≠0→|x|≤M j) (N J : ℕ) :
    ∃ Cₐ : ℝ,0<Cₐ ∧ ∃ Cₛ : ℝ,0≤Cₛ ∧ ∀R:ℝ,0<R→∃b:𝓢(ℝ,ℂ),
      (∀t₁ t₂ t₃:ℝ,(1+R)^N*‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖≤
        Cₛ*FirstPassCubeLabels.firstLogDensity J t₁*FirstPassCubeLabels.firstLogDensity J t₂*
          FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
        (w : SecondExpansionData ι→ℂ) (A K : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O)
        (z ud ue uv kap : SecondExpansionData ι→ℝ) (X₁ X₂ : ℝ),
        0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
        (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
        (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
        (∀x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖≤A) →
        ‖initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖≤
          A*Cₐ*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖*
            sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ,hCₐ,htrans⟩ := integrated_source_transfer ε hε
  obtain ⟨Cₛ,hCₛ,hsep⟩ := full_uniform_postCommonSmoothPair_fixed_tests A₁ A₂ W V M hM hV N J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR
  obtain ⟨b,hpoint,hid⟩ := hsep R hR
  refine ⟨b,hpoint,?_⟩
  intro ι _ p hp _ hcop hg hinj r s T w A K F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hA hK hs hmap hT hnorm hw
  have hsource := initialSource_eq_integrated p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid p hp hcop hg F Ψ₁ Ψ₂ m
      (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans p hp hcop hg hinj r s T (initialOuterWeight V w z ud ue uv kap) A K
    F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b hA hK hs hmap hT hnorm
  · intro q x hx
    rw [initialOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact initialOuterWeight_continuous V w z ud ue uv kap x

end

section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def initialLogIndex (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor),normLogBin (primeProductNorm p x.overlap),
    normLogBin (elementNorm (sourceObservation p x).1))

def initialLogColumn (Z B : ℝ) (j : SecondLogIndex) : ℝ :=
  Z/(secondLogE j*secondLogV j*B)

def initialLogLabel (j : SecondLogIndex) : ℝ := secondLogE j*secondLogV j*Real.exp 2

omit [DecidableEq ι] in
lemma sourceRow_nonzero (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    (sourceObservation p x).1≠0 := mul_ne_zero (primeSubsetGenerator_ne_zero _ _) hk

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceLabel_span (x : SecondExpansionData ι) :
    Ideal.span {(sourceObservation p x).2}=
      (∏i∈x.divisor,Ideal.span {p i})*(∏i∈x.overlap,Ideal.span {p i}) := by
  simp only [sourceObservation,←Ideal.span_singleton_mul_span_singleton,
    primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,FiniteGaussPhase.span_finset_prod]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceLabel_norm (x : SecondExpansionData ι) :
    elementNorm (sourceObservation p x).2=primeProductNorm p x.divisor*primeProductNorm p x.overlap := by
  simp only [elementNorm,sourceObservation,map_mul,norm_mul,mul_pow,
    primeSubsetGenerator_norm_eq_productNorm,primeProductNorm]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceQuotient_nonzero (x : SecondExpansionData ι) (hE : x.divisor⊆x.sourceCommon) :
    secondExpansionQuotient p x≠0 := by
  rw [secondExpansionQuotient_of_subset p x hE]
  intro he
  have hh := secondMaskQuotient_spec p x.divisor x.sourceCommon hE
  rw [he,mul_zero] at hh
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hh

include hp in

theorem initial_log_coordinates (Z : ℝ) (hZ : 0<Z) (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hk : x.frequency≠0) :
    let j := initialLogIndex p x
    let B := elementNorm (secondExpansionQuotient p x)
    let X₀ := initialLogColumn Z B j
    |Real.log (primeProductNorm p x.overlap*X₀/residualScale p Z x)|≤2 ∧
    |Real.log (primeProductNorm p x.divisor/secondLogE j)|≤2 ∧
    |Real.log (primeProductNorm p x.overlap/secondLogV j)|≤2 ∧
    |Real.log (elementNorm (sourceObservation p x).1/secondLogK j)|≤2 := by
  dsimp only
  have he := normLogBin_error (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)
  have hv := normLogBin_error (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)
  have hn : 1≤elementNorm (sourceObservation p x).1 := element_norm_ge_one _ (sourceRow_nonzero p x hk)
  have hrow := normLogBin_error (elementNorm (sourceObservation p x).1) hn
  have hE0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor).ne'
  have hV0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.overlap).ne'
  have hB0 := (SecondPassIntegration.elementNorm_pos _ (sourceQuotient_nonzero p hp x hE)).ne'
  have hE1 := (normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hV1 := (normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hratio : primeProductNorm p x.overlap*initialLogColumn Z
      (elementNorm (secondExpansionQuotient p x)) (initialLogIndex p x)/residualScale p Z x=
      (primeProductNorm p x.divisor/normLogScale (normLogBin (primeProductNorm p x.divisor)))*
      (primeProductNorm p x.overlap/normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [initialLogColumn,residualScale,initialLogIndex,secondLogE,secondLogV,
      elementNorm,primeSubsetGenerator_norm_eq_productNorm]
    have hZ0 := hZ.ne'
    dsimp [elementNorm] at hB0
    have hBn : ‖eisEmbedding (secondExpansionQuotient p x)‖≠0 := by
      intro hz
      apply hB0
      rw [hz]
      norm_num
    field_simp [hBn]

  refine ⟨?_,?_,?_,?_⟩
  · rw [hratio,Real.log_mul (div_ne_zero hE0 hE1) (div_ne_zero hV0 hV1),
      abs_of_nonneg (add_nonneg he.1 hv.1)]
    linarith [he.2,hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg he.1]
    linarith [he.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hv.1]
    linarith [hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hrow.1]
    linarith [hrow.2]

include hp in

omit [DecidableEq ι] in
theorem initial_log_target_bounds (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    elementNorm (sourceObservation p x).2 ≤ initialLogLabel (initialLogIndex p x) ∧
    elementNorm (sourceObservation p x).1≤ secondLogK (initialLogIndex p x)*Real.exp 1 := by
  have he := (normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.divisor)).2
  have hv := (normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.overlap)).2
  have hk' := (normLogBin_scale_bounds _ (element_norm_ge_one _ (sourceRow_nonzero p x hk))).2
  refine ⟨?_,hk'⟩
  rw [sourceLabel_norm]
  have hh := mul_le_mul he hv (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (mul_nonneg (normLogScale_pos _).le (Real.exp_pos _).le)
  simpa only [initialLogLabel,initialLogIndex,secondLogE,secondLogV,
    show (2:ℝ)=1+1 by norm_num,Real.exp_add,mul_assoc,mul_left_comm,mul_comm] using hh

theorem initial_log_mass (Z B : ℝ) (hB : B≠0) (j : SecondLogIndex) :
    initialLogColumn Z B j*initialLogLabel j=Z/B*Real.exp 2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn initialLogLabel secondLogE secondLogV
  field_simp

theorem initial_log_radial (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) (j : SecondLogIndex) :
    H*secondLogK j/(secondLogE j^2*secondLogV j^2*initialLogColumn Z B j^2)=
      H*secondLogK j*B^2/Z^2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn secondLogE secondLogV
  field_simp

end

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

include hcop in
theorem sourceLabel_squarefree (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hV : Disjoint x.sourceCommon x.overlap) :
    Squarefree (Ideal.span {(sourceObservation p x).2}) := by
  have hd : Disjoint x.divisor x.overlap := hV.mono_left hE
  rw [sourceLabel_span,←Finset.prod_union hd]
  exact primeSpanProduct_squarefree p hcop _

include hcop in
theorem sourceMask_coprime (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hV : Disjoint x.sourceCommon x.overlap) :
    IsCoprime (Ideal.span {secondExpansionQuotient p x})
      (Ideal.span {(sourceObservation p x).2}) := by
  rw [secondExpansionQuotient_of_subset p x hE,secondMaskQuotient_span,sourceLabel_span]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.mul_right
  · apply IsCoprime.prod_right
    intro j hj
    exact hcop (fun he => (Finset.mem_sdiff.mp hi).2 (he.symm ▸ hj))
  · apply IsCoprime.prod_right
    intro j hj
    exact hcop (fun he => Finset.disjoint_left.mp hV (Finset.mem_sdiff.mp hi).1 (he.symm ▸ hj))

include hp in
theorem initialLogIndex_mem_box (Z M K : ℝ) (x : SecondExpansionData ι)
    (hs : SecondSourceSupport p Z M x) (hE : x.divisor⊆x.sourceCommon)
    (hk : x.frequency≠0) (hK : elementNorm (sourceObservation p x).1≤K) :
    initialLogIndex p x∈secondLogBinBox (Z*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩ := secondSourceSupport_bounds p hp Z M x hs hE
  simp only [initialLogIndex,secondLogBinBox,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hE',
    normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hV,
    normLogBin_mono (SecondPassIntegration.elementNorm_pos _ (sourceRow_nonzero p x hk)) hK⟩

end

theorem initial_log_box_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ U V K : ℝ,1≤U → 0<V → 0<K → V≤U → K≤U →
      ((secondLogBinBox V K).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hpow⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro U V K hU hV hK hVU hKU
  have hv := normLogBin_le_log_upper V U hV hVU hU
  have hk := normLogBin_le_log_upper K U hK hKU hU
  have hlog := Real.log_nonneg hU
  let B := 1+Real.log 27+22*Real.log U
  have h27 : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hB : 1≤B := by dsimp [B]; linarith
  have hvB : (normLogBin V:ℝ)+1≤B := by dsimp [B]; linarith
  have hkB : (normLogBin K:ℝ)+1≤B := by dsimp [B]; linarith
  have hh : ((secondLogBinBox V K).card:ℝ)≤B^3 := by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B := mul_le_mul (pow_le_pow_left₀ (by positivity) hvB 2) hkB
        (by positivity) (sq_nonneg B)
      _ = B^3 := by ring
  exact hh.trans ((pow_le_pow_right₀ hB (by decide : 3≤10)).trans (hpow U hU))

end InitialMeanSquare

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (bit conductorExponent dilationExponent retained parity evenDouble
  primeProduct primeProductNorm aLabel dilationLabel jLabel j2Label squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

theorem local_first_conductor_balance (parityBit e₁ e₂ : Bool) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      2*bit (!parityBit && e₁ && e₂)=bit e₁+bit e₂+bit parityBit := by
  cases parityBit <;> cases e₁ <;> cases e₂ <;> decide

theorem local_first_conductor_bound (parityBit e₁ e₂ : Bool) (n : ℕ) (hn : 0<n) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2*n := by
  have h : (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2 := by
    cases parityBit <;> cases e₁ <;> cases e₂ <;> decide
  omega

variable {ι : Type*} [DecidableEq ι] (p : ι → O)

omit [DecidableEq ι] in
theorem firstActiveProduct_as_primeProduct (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)=
      primeProduct p S (fun i => if conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 then 0 else 1) := by
  unfold cubeActiveSupport primeProduct
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 <;> simp [h]

omit [DecidableEq ι] in
theorem first_conductor_product_balance (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)*dilationLabel p S v ε₁ ε₂*j2Label p S v ε₁ ε₂^2 =
      aLabel p S ε₁*aLabel p S ε₂*squarefreeLabel p S v := by
  rw [firstActiveProduct_as_primeProduct]
  simp only [dilationLabel,j2Label,aLabel,squarefreeLabel,primeProduct,← Finset.prod_pow,
    ← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  simpa only [evenDouble,mul_comm] using local_first_conductor_balance (parity (v i)) (ε₁ i) (ε₂ i)

variable [∀ i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_product_dvd (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) :
    (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)*
      dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂*jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣
      aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2 := by
  rw [firstActiveProduct_as_primeProduct,← primeProduct_add]
  simp only [dilationLabel,jLabel,aLabel,primeProduct,← Finset.prod_pow,← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  simpa only [mul_comm] using local_first_conductor_bound (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i) (v₁ i+v₂ i) (hv i hi)

variable (hp : ∀ i,p i≠0)
include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_norm_bound (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) (B : ℝ) (hB : 0≤B)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B) :
    ‖eisEmbedding (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2*
      ‖eisEmbedding (dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2*
      ‖eisEmbedding (jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤
    ‖eisEmbedding (aLabel p S ε₁)‖^2*‖eisEmbedding (aLabel p S ε₂)‖^2*B^4 := by
  have hn : aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2≠0 := by
    apply mul_ne_zero (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
    exact pow_ne_zero _ (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
  have h := element_norm_le_of_dvd hn (first_conductor_product_dvd p S v₁ v₂ ε₁ ε₂ hv)
  simp only [map_mul,map_pow,norm_mul,norm_pow,mul_pow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hm := mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hs := pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hm 2
  convert hs using 1 <;> ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel jLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

lemma first_row_numeric_bound (an en jn a1 a2 cn dn hn fn ell K B F : ℝ)
    (ha : 0≤an) (he : 0≤en) (hj : 0<jn) (h1 : 0<a1) (h2 : 0<a2) (hc : 0<cn)
    (hd : 0≤dn) (_hh : 0≤hn) (hf : 0≤fn) (hell : 0<ell) (hK : 0<K) (_hB : 0<B) (hF : 0<F)
    (hcon : an*en*jn≤a1*a2*B^4) (hfreq : hn≤ell^2*an*dn/(K*a1*a2*cn^2)) (hlabel : fn≤F) :
    hn*fn^2*en≤ell^2*B^4*F^2*dn/(K*cn^2*jn) := by
  have hratio : an*en/(a1*a2)≤B^4/jn := by
    apply (div_le_div_iff₀ (mul_pos h1 h2) hj).mpr
    nlinarith [hcon]
  calc
    hn*fn^2*en ≤ (ell^2*an*dn/(K*a1*a2*cn^2))*F^2*en := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul hfreq (pow_le_pow_left₀ hf hlabel 2) (sq_nonneg _) (by positivity)
    _ = (ell^2*dn*F^2/(K*cn^2))*(an*en/(a1*a2)) := by
      field_simp

    _ ≤ (ell^2*dn*F^2/(K*cn^2))*(B^4/jn) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstRowScale_le_pooled (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (b : GlobalCubeBlock ι) :
    globalFirstRowScale p K ell B F ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).2
  have hc := (hbds 1).1
  have hJ := (hbds 4).1
  change primeProductNorm p b.firstDivisor≤globalLogRep j 5*Real.exp 1 at hd
  change globalLogRep j 1≤primeProductNorm p b.common at hc
  change globalLogRep j 4≤globalCubeJNorm p x at hJ
  change ell^2*B^4*F^2*primeProductNorm p b.firstDivisor/
      (K*(primeProductNorm p b.common)^2*globalCubeJNorm p x) ≤
    Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  have hdpos := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
  have h5 := (globalLogRep_pos j 5).le
  apply div_le_div₀ (by positivity)
  · calc
      _ ≤ ell^2*B^4*F^2*(globalLogRep j 5*Real.exp 1) := by gcongr
      _ = _ := by ring
  · exact mul_pos (mul_pos hK (sq_pos_of_pos (globalLogRep_pos j 1))) (globalLogRep_pos j 4)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (globalLogRep_pos j 1).le hc 2) hK.le)
      hJ (globalLogRep_pos j 4).le (by positivity)

include hp in

theorem first_row_enlargement (b : GlobalCubeBlock ι) (x : Ideal O × O)
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : (Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ‖eisEmbedding x.2‖^2 ≤
      ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
      primeProductNorm p b.firstDivisor/
      (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
        ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x)‖^2 ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let active := cubeActiveSupport b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let e := dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let j := jLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let a1 := aLabel p b.cube.support b.cube.leftBit
  let a2 := aLabel p b.cube.support b.cube.rightBit
  have hpos (v : ι → ℕ) : 0<‖eisEmbedding (primeProduct p b.cube.support v)‖^2 :=
    zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))
  have hcon := first_conductor_norm_bound p hp b.cube.support b.cube.leftExponent b.cube.rightExponent
    b.cube.leftBit b.cube.rightBit b.cube.support_pos B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖eisEmbedding e‖^2) (‖eisEmbedding j‖^2)
    (‖eisEmbedding a1‖^2) (‖eisEmbedding a2‖^2) (primeProductNorm p b.common) (primeProductNorm p b.firstDivisor)
    (‖eisEmbedding x.2‖^2) (Ideal.absNorm x.1) ell K B F
    (FirstPassCubeLabels.primeProductNorm_pos p hp active).le (sq_nonneg _) (hpos _) (hpos _) (hpos _)
    (FirstPassCubeLabels.primeProductNorm_pos p hp b.common) (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
    (sq_nonneg _) (Nat.cast_nonneg _) hell hK hB hF hcon hh hf
  have hgen : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator x.1)‖^2=(Ideal.absNorm x.1 : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hrow : ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap e x)‖^2 =
      ‖eisEmbedding x.2‖^2*(Ideal.absNorm x.1 : ℝ)^2*‖eisEmbedding e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [show (‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator x.1)‖^2)^2 =
        (Ideal.absNorm x.1 : ℝ)^2 by rw [hgen]]
  rw [hrow]
  exact hnum.trans (globalFirstRowScale_le_pooled p hp K ell B F hK hell hB hF b)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstFrequencyScale (K ell : ℝ) (b : GlobalCubeBlock ι) : ℝ :=
  ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
    primeProductNorm p b.firstDivisor/
    (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
      ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)

def globalCubeFirstTargets (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O)) : Finset O :=
  s.image (DescentWeightedCauchy.firstElementRowMap
    (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
      b.cube.leftBit b.cube.rightBit))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_mem (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (x : Ideal O × O) (hx : x∈s) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x∈globalCubeFirstTargets p b s :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_ne_zero (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (hsf : ∀ x∈s,Squarefree x.1) (hs0 : ∀ x∈s,x.2≠0)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) : z≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  apply mul_ne_zero
  · apply mul_ne_zero (hs0 x hx)
    exact pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero _ (by simpa using (hsf x hx).ne_zero))
  · exact primeProduct_ne_zero p hp _ _

include hp in
theorem globalCubeFirstTargets_norm_bound (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : ∀ x∈s,(Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ∀ x∈s,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) :
    (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  rw [← eisEmbedding_norm_sq_eq_absNorm_span]
  exact first_row_enlargement p hp b x K ell B F hK hell hB hF hb₁ hb₂ (hf x hx) (hh x hx)

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.RowCaps -/

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

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

def globalFirstRowCap (K ell B F : ℝ) : ℝ :=
  (Real.exp 1)^2*ell^2*B^6*F^2/K

theorem globalFirstRowCap_pos (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) :
    0<globalFirstRowCap K ell B F := by
  unfold globalFirstRowCap
  positivity

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstPooledRow_le_cap (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (b : GlobalCubeBlock ι) (hadm : GlobalCubeAdmissible b)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤globalFirstRowCap K ell B F := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).1
  have hc := (hbds 1).2
  change globalLogRep j 5≤primeProductNorm p b.firstDivisor at hd
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  have hrad := globalCube_radical_bound p hp B hB.le x hb₁ hb₂
  have h1p := globalLogRep_pos j 1
  have hd' : globalLogRep j 5≤globalLogRep j 1*Real.exp 1*B^2 := by
    calc
      _ ≤ primeProductNorm p b.firstDivisor := hd
      _ ≤ primeProductNorm p (b.common∪b.cube.support) := primeProductNorm_mono p hp hadm.2.2
      _ = primeProductNorm p b.common*primeProductNorm p b.cube.support :=
        FirstPassCubeLabels.primeProductNorm_union p _ _ hadm.2.1
      _ ≤ (globalLogRep j 1*Real.exp 1)*B^2 :=
        mul_le_mul hc hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity)
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h4p := globalLogRep_pos j 4
  have hm : globalLogRep j 1≤(globalLogRep j 1)^2*globalLogRep j 4 := by
    calc
      globalLogRep j 1 = globalLogRep j 1*1*1 := by ring
      _ ≤ globalLogRep j 1*globalLogRep j 1*globalLogRep j 4 := by gcongr
      _ = _ := by ring
  have hr : globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)≤Real.exp 1*B^2 := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos h1p) h4p)).mpr
    calc
      _ ≤ globalLogRep j 1*Real.exp 1*B^2 := hd'
      _ ≤ ((globalLogRep j 1)^2*globalLogRep j 4)*Real.exp 1*B^2 := by gcongr
      _ = _ := by ring
  change Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)≤_
  calc
    _ = (Real.exp 1*ell^2*B^4*F^2/K)*(globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)) := by ring
    _ ≤ (Real.exp 1*ell^2*B^4*F^2/K)*(Real.exp 1*B^2) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = globalFirstRowCap K ell B F := by unfold globalFirstRowCap; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem globalTwoPassage_original_ranges
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Ct₁ C₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H : ℝ),
      0≤Γ → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₁ m₁ g₁ V₁ windows₁ C₁ Ct₁ Γ ε K ell B F M₁ H A J N true) *
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₂ m₂ g₂ V₂ windows₂ C₂ Ct₂ Γ ε K ell B F M₂ H A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,htransfer⟩ :=
    globalTwoPassage_transfer W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H
    hΓ hK hell hB hF hH hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  exact htransfer p hp hinj hcop hg hc hpr pool blocks s a w
    (fun b => globalCubeFirstTargets p b (s b)) Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H (globalFirstRowCap K ell B F)
    hΓ hK hell hB hF hH (globalFirstRowCap_pos K ell B F hK hell hB hF).le hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0
    (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx)
    (fun b hb z hz => globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz)
    (fun b hb z hz => globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz)

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

noncomputable abbrev actualSextic := ActualEisensteinCubic.canonicalSextic

def exceptionalPiece (P : Ideal O) [P.IsMaximal] (e : Fin 3) (n b : O) : ℂ :=
  if e=0 then -(rootCard (O ⧸ P) : ℂ)⁻¹
  else if e=1 then (rootCard (O ⧸ P) : ℂ)*(if n∈P then 1 else 0)
  else (rootCard (O ⧸ P) : ℂ)*(if n∉P ∧ b∈P then 1 else 0)

theorem bracket_four_eq_sum_exceptionalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (n b : O) :
    bracket (actualSextic P hg) 4 (Ideal.Quotient.mk P (n*b^3)) =
      ∑e : Fin 3, exceptionalPiece P e n b := by
  rw [canonical_bracket_four_cube_split]
  simp [Fin.sum_univ_succ,exceptionalPiece]
  ring

def exceptionalBranch {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O) : ℂ :=
  ∏i, exceptionalPiece (P i) (e i) n b

theorem prod_bracket_four_eq_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) 4 (Ideal.Quotient.mk (P i) (n*b^3))) =
      ∑e : ι→Fin 3, exceptionalBranch P e n b := by
  simp_rw [bracket_four_eq_sum_exceptionalPiece]
  simpa only [Fintype.piFinset_univ,exceptionalBranch] using
    Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (Fin 3)))
      (fun i e => exceptionalPiece (P i) e n b)

def exceptionalDivisor {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    (e : ι→Fin 3) (v : Fin 3) : Ideal O := ∏i, if e i=v then P i else 1

theorem exceptionalBranch_support {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O)
    (hne : exceptionalBranch P e n b≠0) :
    (∀i,e i=1 → n∈P i) ∧ (∀i,e i=2 → n∉P i ∧ b∈P i) := by
  have hn i : exceptionalPiece (P i) (e i) n b≠0 :=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  constructor
  · intro i hi
    by_contra h
    exact hn i (by simp [exceptionalPiece,hi,h])
  · intro i hi
    by_contra h
    exact hn i (by simp [exceptionalPiece,hi,h])

theorem exceptionalBranch_divisibility {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (e : ι→Fin 3) (n b : O) (hne : exceptionalBranch P e n b≠0) :
    exceptionalDivisor P e 1 ∣ Ideal.span {n} ∧
    exceptionalDivisor P e 2 ∣ Ideal.span {b} ∧
    (∀i,e i=2 → n∉P i) := by
  have hs := exceptionalBranch_support P e n b hne
  have hprod (v : Fin 3) (z : O) (hz : ∀i,e i=v → z∈P i) :
      exceptionalDivisor P e v ∣ Ideal.span {z} := by
    rw [exceptionalDivisor]
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      change IsCoprime (if e i=v then P i else 1) (if e j=v then P j else 1)
      by_cases hi : e i=v
      · rw [ite_eq_left hi]
        by_cases hj : e j=v
        · rw [ite_eq_left hj]
          exact hcop hij
        · rw [ite_eq_right hj]
          exact isCoprime_one_right
      · rw [ite_eq_right hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  exact ⟨hprod 1 n hs.1,hprod 2 b (fun i hi => (hs.2 i hi).2),fun i hi => (hs.2 i hi).1⟩

theorem rootCard_eq_sqrt_absNorm (P : Ideal O) [P.IsMaximal] :
    rootCard (O ⧸ P)=Real.sqrt (Ideal.absNorm P:ℝ) := by
  rw [rootCard,←Nat.card_eq_fintype_card]
  rfl

def exceptionalSize {ι : Type*} [Fintype ι] (P : ι→Ideal O)
    [∀i,(P i).IsMaximal] (e : ι→Fin 3) : ℝ :=
  ∏i, if e i=0 then (rootCard (O ⧸ P i))⁻¹ else rootCard (O ⧸ P i)

theorem exceptionalPiece_norm_le (P : Ideal O) [P.IsMaximal]
    (e : Fin 3) (n b : O) :
    ‖exceptionalPiece P e n b‖≤(if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P)) := by
  have hr : 0≤ rootCard (O ⧸ P) := rootCard_pos.le
  fin_cases e <;> simp only [exceptionalPiece,Fin.isValue,Fin.zero_eta,↓reduceIte]
  · simp [abs_of_nonneg hr]
  · by_cases hn : n∈P <;> simp [hn,abs_of_nonneg hr,hr]
  · by_cases hn : n∉P ∧ b∈P <;> simp [hn,abs_of_nonneg hr,hr]

theorem exceptionalBranch_norm_le {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (n b : O) :
    ‖exceptionalBranch P e n b‖≤exceptionalSize P e := by
  rw [exceptionalBranch,norm_prod,exceptionalSize]
  exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => exceptionalPiece_norm_le _ _ _ _)

theorem exceptionalDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hp : ∀i,P i≠0) (e : ι→Fin 3) (v : Fin 3) :
    exceptionalDivisor P e v≠0 := by
  rw [exceptionalDivisor]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs
  · exact hp i
  · exact one_ne_zero

theorem sqrt_norm_exceptionalDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) (v : Fin 3) :
    Real.sqrt (Ideal.absNorm (exceptionalDivisor P e v):ℝ)=
      ∏i,if e i=v then rootCard (O ⧸ P i) else 1 := by
  rw [exceptionalDivisor,map_prod,Nat.cast_prod,Real.sqrt_prod]
  · apply Finset.prod_congr rfl
    intro i _
    split_ifs with hi
    · rw [rootCard_eq_sqrt_absNorm]
    · simp
  · intro i _
    exact Nat.cast_nonneg _

theorem exceptionalSize_eq {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (e : ι→Fin 3) :
    exceptionalSize P e=
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (exceptionalDivisor P e 0):ℝ) := by
  rw [sqrt_norm_exceptionalDivisor,sqrt_norm_exceptionalDivisor,sqrt_norm_exceptionalDivisor,
    ←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  generalize e i=x
  fin_cases x <;> simp

theorem exceptional_normalized_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hp : ∀i,P i≠0)
    (e : ι→Fin 3) (n b : O) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖exceptionalBranch P e n b‖ /
      (Real.sqrt ((Ideal.absNorm (exceptionalDivisor P e 1):ℝ)*U)*
        ((Ideal.absNorm (exceptionalDivisor P e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (exceptionalDivisor P e 0):ℝ)*
        (Ideal.absNorm (exceptionalDivisor P e 2):ℝ))) := by
  have hn (v : Fin 3) : 0<(Ideal.absNorm (exceptionalDivisor P e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => exceptionalDivisor_ne_zero P hp e v (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs (v : Fin 3) : 0<Real.sqrt (Ideal.absNorm (exceptionalDivisor P e v):ℝ) := Real.sqrt_pos.mpr (hn v)
  have hsu : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  apply (div_le_div_of_nonneg_right (exceptionalBranch_norm_le P e n b) (by positivity)).trans
  rw [exceptionalSize_eq,Real.sqrt_mul (hn 1).le,Real.sqrt_mul (hn 0).le]
  have he := Real.sq_sqrt (hn 2).le
  apply le_of_eq
  field_simp [(hs 0).ne', (hs 1).ne', (hs 2).ne', (hn 2).ne', hsu.ne', hB.ne']
  nlinarith

end CompletedGauss

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss

theorem product_quadratic_norm_scaled (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀b∈T,‖β n b‖≤lengthScale) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,
        quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_all ε hε
  refine ⟨C,hC,?_⟩
  intro K U B lengthScale hK hU hB hL S T hS hT β hβ
  by_cases hL0 : lengthScale=0
  · have hz n hn b hb : β n b=0 := norm_eq_zero.mp (le_antisymm (by simpa [hL0] using hβ n hn b hb) (norm_nonneg _))
    simp only [hL0,pow_two,mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k _
    have hh : (∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b)=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      apply Finset.sum_eq_zero
      intro b hb
      rw [hz n hn b hb,mul_zero]
    rw [hh,norm_zero,zero_mul]
  have hLp : 0<lengthScale := lt_of_le_of_ne hL (Ne.symm hL0)
  have hLc : (lengthScale:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL0
  let γ : Ideal O→Ideal O→ℂ := fun n b => β n b/(lengthScale:ℂ)
  have hγ (n : Ideal O) (hn : n∈S) (b : Ideal O) (hb : b∈T) : ‖γ n b‖≤1 := by
    dsimp [γ]
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hL]
    exact (div_le_one hLp).mpr (hβ n hn b hb)
  have hb := hbound K U B hK hU hB S T hS hT γ hγ
  have he (k : idealRange K) :
      (∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b)=
      (lengthScale:ℂ)*(∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*γ n b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [γ]
    field_simp
  simp_rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hL,mul_pow]
  rw [←Finset.mul_sum]
  calc
    _ ≤ lengthScale^2*(C*(K*(U*B))^ε*(K+U*B)*(U*B)) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

theorem completed_quadratic_dyad (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B r S₀ E : ℝ,
      1≤K → 1≤U → 1≤B → 0< r → 0<S₀ → 0<E →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,
      (∀n∈S,∀b∈T,‖β n b‖≤1/(Real.sqrt U*B*r*Real.sqrt (S₀*E))) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,
        quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)/(B*r^2*S₀*E) := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_scaled ε hε
  refine ⟨C,hC,?_⟩
  intro K U B r S₀ E hK hU hB hr hS₀ hE S T hS hT β hβ
  apply (hbound K U B _ hK hU hB (by positivity) S T hS hT β hβ).trans
  apply le_of_eq
  have hU0 : U≠0 := by linarith
  have hB0 : B≠0 := by linarith
  have hr0 := ne_of_gt hr
  have hS0 := ne_of_gt hS₀
  have hE0 := ne_of_gt hE
  simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt (show 0≤U by linarith),
    Real.sq_sqrt (show 0≤S₀*E by positivity)]
  field_simp

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff

namespace CubicEisenstein

def spatialHorizontal (p : SpatialCoordinates) : ℂ := (p 0:ℂ)+(p 1:ℂ)*Complex.I

def mobiusSpatialDenominator (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℝ :=
  Complex.normSq (g 1 0*spatialHorizontal p+g 1 1)+Complex.normSq (g 1 0)*(p 2)^2

def mobiusSpatialHorizontal (g : SL(2,ℂ)) (p : SpatialCoordinates) : ℂ :=
  ((g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
    g 0 0*star (g 1 0)*(p 2:ℂ)^2)/(mobiusSpatialDenominator g p:ℂ)

def mobiusSpatial (g : SL(2,ℂ)) (p : SpatialCoordinates) : SpatialCoordinates :=
  ![(mobiusSpatialHorizontal g p).re,(mobiusSpatialHorizontal g p).im,
    p 2/mobiusSpatialDenominator g p]

lemma mobiusSpatialDenominator_pos (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0< mobiusSpatialDenominator g p := by
  simpa only [mobiusSpatialDenominator,Complex.normSq_eq_norm_sq] using
    mobius_denominator_pos g (spatialHorizontal p) (p 2) hp

lemma mobiusSpatial_positive (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0< mobiusSpatial g p 2 := div_pos hp (mobiusSpatialDenominator_pos g p hp)

lemma mobiusSpatial_coordinates (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    hyperbolicSpatialCoordinates (g • upperPoint (spatialHorizontal p) (p 2) hp)=mobiusSpatial g p := by
  rw [mobius_upperPoint]
  simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,
    mobiusSpatial,mobiusSpatialHorizontal,mobiusSpatialDenominator,Complex.normSq_eq_norm_sq]

lemma spatialHorizontal_contDiff : ContDiff ℝ ∞ spatialHorizontal := by
  unfold spatialHorizontal
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 0)).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).mul contDiff_const)

lemma mobiusSpatialDenominator_contDiff (g : SL(2,ℂ)) : ContDiff ℝ ∞ (mobiusSpatialDenominator g) := by
  unfold mobiusSpatialDenominator
  have hz : ContDiff ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) :=
    (contDiff_const.mul spatialHorizontal_contDiff).add contDiff_const
  have hre := Complex.reCLM.contDiff.comp hz
  have him := Complex.imCLM.contDiff.comp hz
  change ContDiff ℝ ∞ (fun p =>
    (g 1 0*spatialHorizontal p+g 1 1).re*(g 1 0*spatialHorizontal p+g 1 1).re+
    (g 1 0*spatialHorizontal p+g 1 1).im*(g 1 0*spatialHorizontal p+g 1 1).im+
    Complex.normSq (g 1 0)*(p 2)^2)
  exact ((hre.mul hre).add (him.mul him)).add (contDiff_const.mul ((contDiff_apply ℝ ℝ 2).pow 2))

lemma mobiusSpatial_contDiffAt (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (mobiusSpatial g) p := by
  have hD := (mobiusSpatialDenominator_contDiff g).contDiffAt (x := p)
  have hDc : ContDiffAt ℝ ∞ (fun p => (mobiusSpatialDenominator g p:ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p hD
  have hnum : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates =>
      (g 0 0*spatialHorizontal p+g 0 1)*star (g 1 0*spatialHorizontal p+g 1 1)+
        g 0 0*star (g 1 0)*(p 2:ℂ)^2) p := by
    have hz := spatialHorizontal_contDiff.contDiffAt (x := p)
    have hcz : ContDiffAt ℝ ∞ (fun p => g 1 0*spatialHorizontal p+g 1 1) p :=
      (contDiffAt_const.mul hz).add contDiffAt_const
    have hc := Complex.conjCLE.contDiff.contDiffAt.comp p hcz
    have hv : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => (p 2:ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_apply ℝ ℝ 2).contDiffAt
    exact (((contDiffAt_const.mul hz).add contDiffAt_const).mul hc).add
      (contDiffAt_const.mul (hv.pow 2))
  have hh : ContDiffAt ℝ ∞ (mobiusSpatialHorizontal g) p :=
    by
      unfold mobiusSpatialHorizontal
      simp only [div_eq_mul_inv]
      exact hnum.mul (hDc.inv (Complex.ofReal_ne_zero.mpr (mobiusSpatialDenominator_pos g p hp).ne'))
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact Complex.reCLM.contDiff.contDiffAt.comp p hh
  · exact Complex.imCLM.contDiff.contDiffAt.comp p hh
  · exact (by fun_prop : ContDiffAt ℝ ∞ (fun p : SpatialCoordinates => p 2) p).div hD
      (mobiusSpatialDenominator_pos g p hp).ne'

abbrev PositiveSpatial := {p : SpatialCoordinates // 0<p 2}

def positiveSpatialToUpper (p : PositiveSpatial) : UpperCoordinates :=
  ⟨(spatialHorizontal p.1,p.1 2),p.2⟩
def upperToPositiveSpatial (p : UpperCoordinates) : PositiveSpatial :=
  ⟨![p.1.1.re,p.1.1.im,p.1.2],p.2⟩

lemma positiveSpatialToUpper_continuous : Continuous positiveSpatialToUpper := by
  apply Continuous.subtype_mk
  exact (spatialHorizontal_contDiff.continuous.comp continuous_subtype_val).prodMk
    ((continuous_apply 2).comp continuous_subtype_val)
lemma upperToPositiveSpatial_continuous : Continuous upperToPositiveSpatial := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j <;> fun_prop

def positiveSpatialUpperHomeomorph : PositiveSpatial ≃ₜ UpperCoordinates where
  toFun := positiveSpatialToUpper
  invFun := upperToPositiveSpatial
  left_inv p := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [upperToPositiveSpatial,positiveSpatialToUpper,spatialHorizontal]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact Complex.re_add_im _
    · rfl
  continuous_toFun := positiveSpatialToUpper_continuous
  continuous_invFun := upperToPositiveSpatial_continuous

def positiveSpatialHomeomorph : PositiveSpatial ≃ₜ HyperbolicSpace :=
  positiveSpatialUpperHomeomorph.trans upperCoordinatesHomeomorph

lemma hyperbolicSpatial_isOpenEmbedding : Topology.IsOpenEmbedding hyperbolicSpatialCoordinates := by
  have ho : IsOpen {p : SpatialCoordinates | 0<p 2} := isOpen_lt continuous_const (by fun_prop)
  have he := ho.isOpenEmbedding_subtypeVal.comp positiveSpatialHomeomorph.symm.isOpenEmbedding
  exact he

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

namespace CubicEisenstein

abbrev KernelQuotient := IntegralOrbitQuotient globalKubotaKernel

def hyperbolicSpatialChart : OpenPartialHomeomorph HyperbolicSpace SpatialCoordinates :=
  hyperbolicSpatial_isOpenEmbedding.toOpenPartialHomeomorph hyperbolicSpatialCoordinates

@[simp] lemma hyperbolicSpatialChart_apply (w : HyperbolicSpace) :
    hyperbolicSpatialChart w=hyperbolicSpatialCoordinates w := rfl

@[simp] lemma hyperbolicSpatialChart_source : hyperbolicSpatialChart.source=Set.univ := rfl

lemma hyperbolicSpatialChart_target_positive {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) : 0<p 2 := by
  have he := hyperbolicSpatialChart.right_inv hp
  have hh := hyperbolicSpatialCoordinates_positive (hyperbolicSpatialChart.symm p)
  rwa [← hyperbolicSpatialChart_apply,he] at hh

def kernelLocalLift (w : HyperbolicSpace) : OpenPartialHomeomorph KernelQuotient HyperbolicSpace :=
  kernelQuotient_localHomeomorph.localInverseAt w

@[simp] lemma kernelLocalLift_symm (w : HyperbolicSpace) :
    (kernelLocalLift w).symm=integralOrbitProjection globalKubotaKernel :=
  kernelQuotient_localHomeomorph.localInverseAt_symm w

lemma kernelLocalLift_project {w : HyperbolicSpace} {q : KernelQuotient}
    (hq : q∈(kernelLocalLift w).source) :
    integralOrbitProjection globalKubotaKernel (kernelLocalLift w q)=q :=
  kernelQuotient_localHomeomorph.apply_localInverseAt_of_mem hq

lemma kernel_lifts_eventually_eq {X : Type*} [TopologicalSpace X]
    {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hfg : f x=g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) : f=ᶠ[𝓝 x]g := by
  obtain ⟨U,hU,hx,hUinj⟩ := kernelQuotient_localHomeomorph.isLocallyInjective (f x)
  have hfn : ∀ᶠ y in 𝓝 x,f y∈U := hf (hU.mem_nhds hx)
  have hgn : ∀ᶠ y in 𝓝 x,g y∈U := hg (hU.mem_nhds (hfg ▸ hx))
  filter_upwards [hfn,hgn,hproj] with y hyf hyg hye
  exact hUinj hyf hyg hye

lemma kernel_lifts_eventually_deck {X : Type*} [TopologicalSpace X]
    {f g : X→HyperbolicSpace} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hproj : (fun y => integralOrbitProjection globalKubotaKernel (f y))=ᶠ[𝓝 x]
      (fun y => integralOrbitProjection globalKubotaKernel (g y))) :
    ∃M : globalKubotaKernel, f=ᶠ[𝓝 x](fun y => integralComplexMatrix M • g y) := by
  have he := (integralOrbitProjection_eq_iff globalKubotaKernel (f x) (g x)).mp
    hproj.self_of_nhds
  obtain ⟨M,hM⟩ := MulAction.mem_orbit_iff.mp he
  refine ⟨M,kernel_lifts_eventually_eq hf
    ((continuous_hyperbolic_action (integralComplexMatrix M)).continuousAt.comp hg) hM.symm ?_⟩
  filter_upwards [hproj] with y hy
  simpa only [integralOrbitProjection_eq] using hy

lemma mobiusSpatial_coordinates_global (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicSpatialCoordinates (g•w)=mobiusSpatial g (hyperbolicSpatialCoordinates w) := by
  have hp := hyperbolicSpatialCoordinates_positive w
  have hr := hyperbolicSpatialCoordinates_reconstruct w
  nth_rw 1 [← hr]
  exact mobiusSpatial_coordinates g (hyperbolicSpatialCoordinates w) hp

def kernelCoordinateTransition (w : HyperbolicSpace) (p : SpatialCoordinates) : SpatialCoordinates :=
  hyperbolicSpatialCoordinates (kernelLocalLift w
    (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)))

lemma kernelCoordinateTransition_eventually (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) :
    ∃M : globalKubotaKernel,kernelCoordinateTransition w=ᶠ[𝓝 p]
      mobiusSpatial (integralComplexMatrix M) := by
  have hc : ContinuousAt hyperbolicSpatialChart.symm p :=
    hyperbolicSpatialChart.symm.continuousAt hp
  have hπ : ContinuousAt (fun y => integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)) p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp hc
  have hl : ContinuousAt (fun y => kernelLocalLift w (integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y))) p :=
    ((kernelLocalLift w).continuousAt hq).comp
      (f := fun y : SpatialCoordinates => integralOrbitProjection globalKubotaKernel
        (hyperbolicSpatialChart.symm y)) hπ
  have hqn : ∀ᶠ y in 𝓝 p,integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm y)∈(kernelLocalLift w).source :=
    hπ ((kernelLocalLift w).open_source.mem_nhds hq)
  have hproj : (fun y => integralOrbitProjection globalKubotaKernel (kernelLocalLift w
      (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y))))=ᶠ[𝓝 p]
      (fun y => integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm y)) := by
    filter_upwards [hqn] with y hy
    exact kernelLocalLift_project hy
  obtain ⟨M,hM⟩ := kernel_lifts_eventually_deck hl hc hproj
  refine ⟨M,?_⟩
  filter_upwards [hM,hyperbolicSpatialChart.open_target.mem_nhds hp] with y hy hyt
  change hyperbolicSpatialCoordinates _=mobiusSpatial _ y
  rw [hy,mobiusSpatial_coordinates_global]
  exact congrArg _ (hyperbolicSpatialChart.right_inv hyt)

lemma kernelCoordinateTransition_contDiffAt (w : HyperbolicSpace) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target)
    (hq : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift w).source) : ContDiffAt ℝ ∞ (kernelCoordinateTransition w) p := by
  obtain ⟨M,hM⟩ := kernelCoordinateTransition_eventually w p hp hq
  exact (mobiusSpatial_contDiffAt _ p (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq hM

def kernelQuotientChart (q : KernelQuotient) : OpenPartialHomeomorph KernelQuotient SpatialCoordinates :=
  (kernelLocalLift q.out).trans hyperbolicSpatialChart

@[simp] lemma kernelQuotientChart_symm (q : KernelQuotient) (p : SpatialCoordinates) :
    (kernelQuotientChart q).symm p=
      integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p) := by
  change (kernelLocalLift q.out).symm (hyperbolicSpatialChart.symm p)=_
  rw [kernelLocalLift_symm]

lemma kernelQuotientChart_contDiffOn (q r : KernelQuotient) :
    ContDiffOn ℝ ∞ ((kernelQuotientChart q).symm.trans (kernelQuotientChart r))
      ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)).source := by
  intro p hp
  have hp' : p∈hyperbolicSpatialChart.target := hp.1.1
  have hq' : integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p)∈
      (kernelLocalLift r.out).source := by
    rw [← kernelQuotientChart_symm q p]
    exact hp.2.1
  have he : (fun p => ((kernelQuotientChart q).symm.trans (kernelQuotientChart r)) p)=
      kernelCoordinateTransition r.out := by
    funext y
    change hyperbolicSpatialChart (kernelLocalLift r.out ((kernelQuotientChart q).symm y))=_
    rw [kernelQuotientChart_symm]
    rfl
  change ((kernelQuotientChart q).symm.trans (kernelQuotientChart r) : SpatialCoordinates→SpatialCoordinates)=_ at he
  rw [he]
  exact (kernelCoordinateTransition_contDiffAt r.out p hp' hq').contDiffWithinAt

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.SmoothTests -/

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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

instance hyperbolicSpatialChartedSpace : ChartedSpace SpatialCoordinates HyperbolicSpace :=
  hyperbolicSpatialChart.singletonChartedSpace hyperbolicSpatialChart_source

instance hyperbolicSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ HyperbolicSpace :=
  hyperbolicSpatialChart.isManifold_singleton hyperbolicSpatialChart_source

lemma kernelLocalLift_source_out (q : KernelQuotient) : q∈(kernelLocalLift q.out).source := by
  have h := kernelQuotient_localHomeomorph.apply_self_mem_localInverseAt_source (x := q.out)
  change integralOrbitProjection globalKubotaKernel q.out∈(kernelLocalLift q.out).source at h
  rwa [show integralOrbitProjection globalKubotaKernel q.out=q from Quotient.out_eq q] at h

instance kernelSpatialChartedSpace : ChartedSpace SpatialCoordinates KernelQuotient where
  atlas := Set.range kernelQuotientChart
  chartAt := kernelQuotientChart
  mem_chart_source q := ⟨kernelLocalLift_source_out q,Set.mem_univ _⟩
  chart_mem_atlas q := ⟨q,rfl⟩

instance kernelSpatialIsManifold : IsManifold 𝓘(ℝ,SpatialCoordinates) ∞ KernelQuotient := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨q,rfl⟩ ⟨r,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id_eq,Set.range_id,Set.inter_univ,id_eq] using
    kernelQuotientChart_contDiffOn q r

@[simp] lemma hyperbolicSpatial_chartAt (w : HyperbolicSpace) :
    chartAt SpatialCoordinates w=hyperbolicSpatialChart := rfl

@[simp] lemma kernelSpatial_chartAt (q : KernelQuotient) :
    chartAt SpatialCoordinates q=kernelQuotientChart q := rfl

lemma kernelProjection_contMDiff : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
    (integralOrbitProjection globalKubotaKernel) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨(continuous_integralOrbitProjection globalKubotaKernel).continuousAt,?_⟩
  have hp : hyperbolicSpatialCoordinates w∈hyperbolicSpatialChart.target :=
    hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have hq : integralOrbitProjection globalKubotaKernel
      (hyperbolicSpatialChart.symm (hyperbolicSpatialCoordinates w))∈
      (kernelLocalLift (integralOrbitProjection globalKubotaKernel w).out).source := by
    have hleft := hyperbolicSpatialChart.left_inv (Set.mem_univ w)
    change hyperbolicSpatialChart.symm (hyperbolicSpatialCoordinates w)=w at hleft
    rw [hleft]
    exact kernelLocalLift_source_out _
  have h : ContDiffWithinAt ℝ ∞
      (kernelCoordinateTransition (integralOrbitProjection globalKubotaKernel w).out) Set.univ
      (hyperbolicSpatialCoordinates w) :=
    (kernelCoordinateTransition_contDiffAt _ _ hp hq).contDiffWithinAt
  unfold kernelCoordinateTransition at h
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    kernelSpatial_chartAt,hyperbolicSpatial_chartAt,kernelCoordinateTransition,
    kernelQuotientChart,OpenPartialHomeomorph.trans_apply,Function.comp_def,
    hyperbolicSpatialChart_apply,id_eq] using h

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal NNReal

def kernelSmoothTests : Submodule ℂ (KernelQuotient→ℂ) where
  carrier f := ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f ∧ HasCompactSupport f
  zero_mem' := ⟨contMDiff_const,HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
  smul_mem' c f hf := by
    have hc : ContDiff ℝ ∞ (fun z : ℂ => c*z) := contDiff_const.mul contDiff_id
    exact ⟨hc.contMDiff.comp hf.1,hf.2.smul_left⟩

lemma kernelSmoothTests_memLp (f : kernelSmoothTests) :
    MemLp f.1 2 (integralQuotientVolume globalKubotaKernel) :=
  f.2.1.continuous.memLp_of_hasCompactSupport f.2.2

def kernelSmoothTestsToL2 : kernelSmoothTests→ₗ[ℂ]KernelQuotientL2 where
  toFun f := (kernelSmoothTests_memLp f).toLp f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma kernelSmoothTestsToL2_injective : Function.Injective kernelSmoothTestsToL2 := by
  intro f g hfg
  apply Subtype.ext
  apply kernel_continuous_eq_of_ae_eq _ _ f.2.1.continuous g.2.1.continuous
  exact ((kernelSmoothTests_memLp f).toLp_eq_toLp_iff (kernelSmoothTests_memLp g)).mp hfg

lemma kernelL2_smooth_compact_approx (f : KernelQuotientL2) (ε : ℝ) (hε : 0<ε) :
    ∃g : kernelSmoothTests,
      eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)≤
        ENNReal.ofReal ε := by
  obtain ⟨g,hgK,hfg,hgc,hgLp⟩ := kernelL2_continuous_compact_approx f
    (ENNReal.ofReal (ε/2)) (by positivity)
  let mass : ℝ≥0∞ := (integralQuotientVolume globalKubotaKernel Set.univ)^((2:ℝ≥0∞).toReal⁻¹)
  have hm : mass≠(∞:ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  let deltaLoss : ℝ := ε/(2*(mass.toReal+1))
  have hδ : 0<deltaLoss := div_pos hε (by positivity)
  obtain ⟨k,hkg,hksupp⟩ := hgc.exists_contMDiff_approx 𝓘(ℝ,SpatialCoordinates) ⊤
    (ε := fun _ => deltaLoss) continuous_const (fun _ => hδ)
  have hkK : HasCompactSupport (k : KernelQuotient→ℂ) :=
    HasCompactSupport.of_support_subset_isCompact hgK (hksupp.trans (subset_tsupport g))
  let kt : kernelSmoothTests := ⟨k,k.contMDiff,hkK⟩
  have hkgLp : eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel)≤
      ENNReal.ofReal (ε/2) := by
    have hb : ∀ᵐ q ∂integralQuotientVolume globalKubotaKernel,‖g q-k q‖≤deltaLoss :=
      Filter.Eventually.of_forall fun q => by
        simpa only [dist_eq_norm,norm_sub_rev] using (hkg q).le
    have hmul : mass.toReal*deltaLoss≤ε/2 := by
      have he : deltaLoss*(2*(mass.toReal+1))=ε := div_mul_cancel₀ _ (by positivity)
      have hp := ENNReal.toReal_nonneg (a := mass)
      nlinarith [mul_nonneg hp hδ.le]
    calc
      _ ≤ mass*ENNReal.ofReal deltaLoss := eLpNorm_le_of_ae_bound (hgc.sub k.contMDiff.continuous).aestronglyMeasurable hb
      _ = ENNReal.ofReal (mass.toReal*deltaLoss) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hm]
      _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal hmul
  refine ⟨kt,?_⟩
  have he : (f : KernelQuotient→ℂ)-kt.1=((f : KernelQuotient→ℂ)-g)+(g-(k : KernelQuotient→ℂ)) := by
    funext q
    change f q-k q=(f q-g q)+(g q-k q)
    ring
  rw [he]
  calc
    _ ≤ eLpNorm ((f : KernelQuotient→ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)+
        eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel) :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add hfg hkgLp
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

lemma kernelSmoothTestsToL2_dense : DenseRange kernelSmoothTestsToL2 := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨g,hg⟩ := kernelL2_smooth_compact_approx f (ε/2) (by positivity)
  refine ⟨g,?_⟩
  have he : ‖f-kernelSmoothTestsToL2 g‖=
      (eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)).toReal := by
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    exact (Lp.coeFn_sub _ _).trans ((Filter.EventuallyEq.refl _ _).sub
      (kernelSmoothTests_memLp g).coeFn_toLp)
  rw [dist_eq_norm,he]
  exact lt_of_le_of_lt ((ENNReal.toReal_mono (by simp) hg).trans_eq (ENNReal.toReal_ofReal (by positivity)))
    (by linarith)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal

lemma hyperbolicSpatialChart_symm_eq {p : SpatialCoordinates}
    (hp : p∈hyperbolicSpatialChart.target) :
    hyperbolicSpatialChart.symm p=upperPoint (spatialHorizontal p) (p 2)
      (hyperbolicSpatialChart_target_positive hp) := by
  have h := hyperbolicSpatialCoordinates_reconstruct (hyperbolicSpatialChart.symm p)
  have he : hyperbolicSpatialCoordinates (hyperbolicSpatialChart.symm p)=p :=
    hyperbolicSpatialChart.right_inv hp
  simpa only [he,spatialHorizontal] using h.symm

lemma kernelQuotientDefect_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    {p : SpatialCoordinates} (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientDefect a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedDefectField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeedDefect a b s _=smoothCuspSeedDefectField a b s p
  rw [smoothCuspSeedDefectField,dite_eq_left (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientDefect_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientDefect a b s) := by
  intro q
  rw [contMDiffAt_iff]
  refine ⟨(kernelQuotientDefect_continuous a b s ha hab).continuousAt,?_⟩
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hF := actual_smoothCuspSeedDefect_contDiffAt a b s ha hab _
    (hyperbolicSpatialChart_target_positive hp)
  have he : (fun p => kernelQuotientDefect a b s ((kernelQuotientChart q).symm p))=ᶠ[𝓝 (kernelQuotientChart q q)]
      smoothCuspSeedDefectField a b s := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hp
    exact kernelQuotientDefect_coordinate a b s q hp
  have hh := hF.congr_of_eventuallyEq he
  have hh' := hh.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

def kernelDefectSmoothTest (a b : ℝ) (ha : 1<a) (hab : a<b) (s : ℂ) : kernelSmoothTests :=
  ⟨kernelQuotientDefect a b s,kernelQuotientDefect_contMDiff a b s ha hab,
    kernelQuotientDefect_hasCompactSupport a b (by linarith) hab s⟩

lemma kernelDefectSmoothTest_toL2 (a b : ℝ) (ha : 1<a) (hab : a<b) (s : ℂ) :
    kernelSmoothTestsToL2 (kernelDefectSmoothTest a b ha hab s)=
      kernelL2Defect a b (by linarith) hab s := rfl

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace InitialMeanSquare

section
open ActualEisensteinCubic SecondPassArithmetic
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma quotient_span_fixed (r : O) (x : SecondExpansionData ι) (hx : InSecondQuotientSector p r x) :
    Ideal.span {secondExpansionQuotient p x}=Ideal.span {r} := by
  obtain ⟨hE,hr⟩ := hx
  rwa [secondExpansionQuotient_of_subset p x hE]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma quotient_norm_fixed (r : O) (x : SecondExpansionData ι) (hx : InSecondQuotientSector p r x) :
    elementNorm (secondExpansionQuotient p x)=elementNorm r := by
  simp only [elementNorm,eisEmbedding_norm_sq_eq_absNorm_span,quotient_span_fixed p r x hx]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma residualScale_fixed (Z : ℝ) (r : O) (x : SecondExpansionData ι)
    (hx : InSecondQuotientSector p r x) :
    residualScale p Z x=Z/(elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)*elementNorm r) := by
  rw [residualScale,quotient_norm_fixed p r x hx]

variable (hp : ∀i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem postCommonSmoothPair_fixed_mask (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m r f y₁ y₂ : O)
    (x : SecondExpansionData ι) (hx : InSecondQuotientSector p r x)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (z ud ue uv kap X₁ X₂ R : ℝ) :
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*secondExpansionQuotient p x) f y₁ y₂
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R=
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r) f y₁ y₂
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R := by
  have hm : Ideal.span {m*secondExpansionQuotient p x}=Ideal.span {m*r} := by
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      quotient_span_fixed p r x hx]
  simp only [postCommonSmoothPair,secondChildColumn,rowCoprimeMask_congr_span p _ hm]

theorem sourceWeight_norm_fixed
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex) (Z H : ℝ) (x : SecondExpansionData ι)
    (hx : InSecondQuotientSector p r x) (hZ : 0<Z) (hH : 0≤H)
    (hΨG : ‖Ψ (∏i∈x.sourceCommon,p i)‖≤1) (hΨV : ‖Ψ (∏i∈x.overlap,p i)‖≤1) :
    ‖sourceWeight p hp hcop hg Ψ m ray Z H x‖≤H*elementNorm r/Z^2*‖secondRayCoefficient ray‖ := by
  simpa only [quotient_norm_fixed p r x hx] using
    sourceWeight_norm_le p hp hcop hg hinj hc Ψ m ray Z H x hZ hH hΨG hΨV

end

lemma normCharacter_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (a : O) :
    ‖normCharacter χ a‖≤1 := χ.norm_le_one _

lemma conjugateMonoid_norm_le_one (Ψ : O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (a : O) :
    ‖conjugateMonoid Ψ a‖≤1 := by
  simpa only [conjugateMonoid,MonoidHom.coe_mk,OneHom.coe_mk,norm_star] using hΨ a

end
section

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
def sourceLogZ (Z X : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap*X/residualScale p Z x)
def sourceLogE (E : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)/E)
def sourceLogV (V : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap/V)
def sourceLogK (K : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Real.log (elementNorm (sourceObservation p x).1/K)
end

theorem initial_sector_fixed_profiles
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU₁ : ∀t,g₁ t≠0→U t=1) (hU₂ : ∀t,g₂ t≠0→U t=1)
    (hg₁ : ∀t,g₁ t≠0→|t|≤A) (hg₂ : ∀t,g₂ t≠0→|t|≤A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<E → 0<V → 0<X → 0<K →
        (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
          (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
          (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H =
        initialSourceSum p hp hcop hg s (sourceWeight p hp hcop hg Ψ m ray Z H)
          F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r) A₁ A₂ W windows
          (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K)
          X X (H*K/(E^2*V^2*X^2)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_source_fixed_profiles
    U hUc hUs g₁ g₂ W A 2 hA (by norm_num) hU₁ hU₂ hg₁ hg₂
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap
  calc
    _ = ∑x∈s,secondExpansionSource p hp hcop hg F Ψ m 1 1 ray {x}
        (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
        (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H := by
          simp only [secondExpansionSource,Finset.sum_singleton]
    _ = _ := by
      unfold initialSourceSum
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨hsubset,_⟩ := hs x hx
      have hh := hid p hp hcop hg hinj hpr F Ψ m ray x Z H E V X K
        hsubset (hk x hx) hZ hE hV hX hK (hz x hx) (he x hx) (hv x hx) (hkap x hx)
      rw [hh]
      rw [postCommonSmoothPair_fixed_mask p hp hcop hg F (secondRayMinus Ψ ray)
        (secondRayPlus Ψ ray) m r _ _ _ x (hs x hx)]
      rfl

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (normalizedColumn columnLog firstLogDensity)

theorem initial_sector_transfer
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU : ∀t,g t≠0→U t=1) (hgA : ∀t,g t≠0→|t|≤A)
    (ε : ℝ) (hε : 0<ε) (N J : ℕ) :
    ∃ (windows : Fin 7→ℝ→ℂ) (C Cₛ : ℝ),0≤C ∧ 0≤Cₛ ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<H → 0<E → 0<V → 0<X → 0<K →
        (∀a,‖Ψ a‖≤1) → (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        ∃ B : Frequency→ℝ,
          (∀q,0≤B q) ∧
          (∀q,(1+H*K/(E^2*V^2*X^2))^N*B q≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S)
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S) W H‖≤
          (C*H*elementNorm r/Z^2*‖secondRayCoefficient ray‖*(K*Real.exp 2)^ε)*
            (∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_sector_fixed_profiles
    U hUc hUs g g W A hA hU hU hgA hgA
  obtain ⟨Cw,hCw,hwbound⟩ := outerWindow_global_bound windows hwc (fun i => (hws i).continuous)
  have hM : 0≤A+2+1 := by linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := initial_source_uniform_transfer ε hε A₁ A₂ W windows
    (fun _ => A+2+1) (fun _ => hM) hwb N J
  refine ⟨windows,Cw*Cₐ,Cₛ,mul_nonneg hCw hCₐ.le,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m r ray s Z H E V X K hZ hH hE hV hX hK hΨ hs hk hz he hv hkap
  let R := H*K/(E^2*V^2*X^2)
  have hR : 0<R := by dsimp [R]; positivity
  obtain ⟨b,hpoint,hbound⟩ := htrans R hR
  let B : Frequency→ℝ := fun q => ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b q‖
  refine ⟨B,fun q => norm_nonneg _,?_,?_⟩
  · intro q
    simpa only [B,R,tripleCoefficient,mul_assoc] using hpoint q.1 q.2.1 q.2.2
  · let T := s.image (sourceObservation p)
    have hT0 : ∀y∈T,y.1≠0 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact sourceRow_nonzero p x (hk x hx)
    have hTK : ∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K*Real.exp 2 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hpos := elementNorm_pos _ (sourceRow_nonzero p x (hk x hx))
      have hl : Real.log (elementNorm (sourceObservation p x).1/K)≤2 :=
        (le_abs_self _).trans (hkap x hx)
      have hh := Real.exp_le_exp.mpr hl
      rw [Real.exp_log (div_pos hpos hK)] at hh
      have hh' := (div_le_iff₀ hK).mp hh
      simpa only [elementNorm,eisEmbedding_norm_sq_eq_absNorm_span,mul_comm] using hh'
    let D := H*elementNorm r/Z^2*‖secondRayCoefficient ray‖
    have hD : 0≤D := by dsimp [D,elementNorm]; positivity
    have hweights : ∀x∈s,‖sourceWeight p hp hcop hg Ψ m ray Z H x‖*
        ‖outerWindow windows (sourceLogZ p Z X x) 0 (sourceLogE p E x) (sourceLogV p V x) (sourceLogK p K x)‖≤D*Cw := by
      intro x hx
      exact mul_le_mul (sourceWeight_norm_fixed p hp hcop hg hinj hc Ψ m r ray Z H x
        (hs x hx) hZ hH.le (hΨ _) (hΨ _)) (hwbound _ _ _ _ _) (norm_nonneg _) hD
    have hh := hbound p hp hcop hg hinj r s T (sourceWeight p hp hcop hg Ψ m ray Z H) (D*Cw)
      (K*Real.exp 2) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r)
      (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K) X X
      (mul_nonneg hD hCw) (by positivity) hs (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) hT0 hTK hweights
    rw [hid p hp hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap]
    convert hh using 1 ; dsimp [D,B,R,T] ; ring

end InitialMeanSquare

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

theorem descent_ideal_inverse_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀ I∈S,(Ideal.absNorm I : ℝ)≤H) :
    (∑ I∈S,1/(Ideal.absNorm I : ℝ))≤128*Real.exp 1*(normLogBin H+1 : ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  let T := Finset.range (normLogBin H+1)
  let bin (j : ℕ) := S.filter (fun I => normLogBin (Ideal.absNorm I)=j)
  have hmap : ∀ I∈S,normLogBin (Ideal.absNorm I : ℝ)∈T := by
    intro I hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (normLogBin_mono (by linarith [hpos I hI]) (hH I hI)))
  have hbin (j : ℕ) : (∑ I∈bin j,1/(Ideal.absNorm I : ℝ))≤128*Real.exp 1 := by
    have hp := normLogScale_pos j
    have hone := normLogScale_ge_one j
    have he := Real.one_le_exp (show (0 : ℝ)≤1 by norm_num)
    have hc : ((bin j).card : ℝ)≤128*(normLogScale j*Real.exp 1) := by
      apply DescentFiberCost.finite_ideal_count_real _ _ (by nlinarith)
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        simpa only [hj] using (normLogBin_scale_bounds (Ideal.absNorm I : ℝ) (hpos I hIS)).2
    have ht (I : Ideal O) (hI : I∈bin j) : 1/(Ideal.absNorm I : ℝ)≤1/normLogScale j := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (normLogBin_scale_bounds (Ideal.absNorm I : ℝ) (hpos I hIS)).1
      rw [hj] at hb
      exact one_div_le_one_div_of_le hp hb
    calc
      _ ≤ ∑ _I∈bin j,1/normLogScale j := Finset.sum_le_sum ht
      _ = ((bin j).card : ℝ)/normLogScale j := by simp [div_eq_mul_inv]
      _ ≤ (128*(normLogScale j*Real.exp 1))/normLogScale j := div_le_div_of_nonneg_right hc hp.le
      _ = _ := by field_simp
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ _j∈T,128*Real.exp 1 := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp [T]; ring

theorem descent_normLogBin_small_power (ε : ℝ) (hε : 0<ε) (H : ℝ) (hH : 1≤H) :
    (normLogBin H+1 : ℝ)≤(1+1/ε)*H^ε := by
  have hH0 : 0<H := by linarith
  have hb : (normLogBin H : ℝ)≤Real.log H := Nat.floor_le (Real.log_nonneg hH)
  have hl := Real.log_le_rpow_div hH0.le hε
  have hp := Real.one_le_rpow hH hε.le
  calc
    _ ≤ H^ε/ε+1 := by linarith
    _ ≤ H^ε/ε+H^ε := add_le_add le_rfl hp
    _ = _ := by ring

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel b0Label j2Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]

def cubeProductIdeal (x : CubeCoordinates ι) : Ideal O :=
  Ideal.span {primeProduct p x.support x.leftExponent}*
    Ideal.span {primeProduct p x.support x.rightExponent}

def cubeParityKey (x : CubeCoordinates ι) : Ideal O × Ideal O :=
  (Ideal.span {squarefreeLabel p x.support (fun i => x.leftExponent i+x.rightExponent i)},
   Ideal.span {(b0Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit*
     j2Label p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit)})

def cubeDivisorKey (x : CubeCoordinates ι) : Fin 3 → Ideal O :=
  ![Ideal.span {primeProduct p x.support x.leftExponent},
    Ideal.span {aLabel p x.support x.leftBit},Ideal.span {aLabel p x.support x.rightBit}]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_product (x : CubeCoordinates ι) :
    cubeProductIdeal p x=(cubeParityKey p x).2^2*(cubeParityKey p x).1 := by
  have h := FirstPassCubeLabels.cube_pair_product_decomposition p x.support
    x.leftExponent x.rightExponent x.leftBit x.rightBit x.support_pos
  have h' := congrArg (fun z : O => (Ideal.span {z} : Ideal O)) h
  simp only [cubeProductIdeal,cubeParityKey,pow_two,←Ideal.span_singleton_mul_span_singleton] at h' ⊢
  convert h' using 1 ; congr 1 ; ring

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeDivisorKey_dvd (x : CubeCoordinates ι) (i : Fin 3) :
    cubeDivisorKey p x i ∣ cubeProductIdeal p x := by
  have hA1 := span_dvd_of_element_dvd
    (aLabel_dvd_primeProduct p x.support (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.support_pos)
  have hA2 := span_dvd_of_element_dvd
    (aLabel_dvd_primeProduct p x.support (fun i => x.leftExponent i+x.rightExponent i) x.rightBit x.support_pos)
  rw [primeProduct_add,←Ideal.span_singleton_mul_span_singleton] at hA1 hA2
  fin_cases i
  · exact dvd_mul_right _ _
  · exact hA1
  · exact hA2

variable (hp : ∀ i,p i≠0)
include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeParityKey_ne_zero (x : CubeCoordinates ι) :
    (cubeParityKey p x).1≠0 ∧ (cubeParityKey p x).2≠0 := by
  constructor
  · exact (Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp _ _)
  · exact (Ideal.span_singleton_eq_bot.not).mpr
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeProductIdeal_ne_zero (x : CubeCoordinates ι) : cubeProductIdeal p x≠0 := by
  rw [cubeParityKey_product]
  exact mul_ne_zero (pow_ne_zero _ (cubeParityKey_ne_zero p hp x).2) (cubeParityKey_ne_zero p hp x).1

variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem cubeDivisorKey_injective_on_product {x y : CubeCoordinates ι}
    (hx : x.Admissible) (hy : y.Admissible)
    (hprod : cubeProductIdeal p x=cubeProductIdeal p y)
    (hk : cubeDivisorKey p x=cubeDivisorKey p y) : x=y := by
  have h1 := congrFun hk 0
  have hA1 := congrFun hk 1
  have hA2 := congrFun hk 2
  change Ideal.span {primeProduct p x.support x.leftExponent}=
    Ideal.span {primeProduct p y.support y.leftExponent} at h1
  have h2 : Ideal.span {primeProduct p x.support x.rightExponent}=
    Ideal.span {primeProduct p y.support y.rightExponent} := by
    apply mul_left_cancel₀ ((Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp x.support x.leftExponent))
    simpa only [cubeProductIdeal,h1] using hprod
  have hv1 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.leftExponent y.leftExponent x.left_off y.left_off h1
  have hv2 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.rightExponent y.rightExponent x.right_off y.right_off h2
  change Ideal.span {aLabel p x.support x.leftBit}=Ideal.span {aLabel p y.support y.leftBit} at hA1
  change Ideal.span {aLabel p x.support x.rightBit}=Ideal.span {aLabel p y.support y.rightBit} at hA2
  rw [CubeCoordinates.aLabel_left p x hx,CubeCoordinates.aLabel_left p y hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA1
  rw [CubeCoordinates.aLabel_right p x hx,CubeCoordinates.aLabel_right p y hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA2
  exact CubeCoordinates.ext (Finsupp.ext (congrFun hv1)) (Finsupp.ext (congrFun hv2))
    (FirstCauchyArithmetic.family_product_injective _ hinj hA1)
    (FirstCauchyArithmetic.family_product_injective _ hinj hA2)

theorem cubeParityKey_fiber_card (s : Finset (CubeCoordinates ι)) (q : Ideal O × Ideal O)
    (hq1 : q.1≠0) (hq2 : q.2≠0) (hs : ∀ x∈s,x.Admissible)
    (hk : ∀ x∈s,cubeParityKey p x=q) :
    s.card≤(idealDivisors (q.2^2*q.1)).card^3 := by
  let D := idealDivisors (q.2^2*q.1)
  have hprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq2) hq1
  let encode (x : s) : Fin 3 → D := fun i => ⟨cubeDivisorKey p x.val i,by
    apply (mem_idealDivisors hprod0).mpr
    have h := cubeDivisorKey_dvd p x.val i
    simpa only [cubeParityKey_product,hk x.val x.property] using h⟩
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply cubeDivisorKey_injective_on_product p hp hinj (hs _ x.property) (hs _ y.property)
    · simp only [cubeParityKey_product,hk _ x.property,hk _ y.property]
    · funext i
      exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin,D] using Fintype.card_le_of_injective encode hi

end SecondPassArithmetic

end

end OAI

end

