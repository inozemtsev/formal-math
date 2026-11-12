module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part003

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / GaussSum / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.GaussSum.GlobalScales -/

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

namespace CompletedGauss
open ActualEisensteinCubic

theorem largeCubeCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (H₀ : ℝ) (B : Ideal O),B≠⊥ →
      ‖largeCubeCoefficient H₀ B‖ ≤ C*(Ideal.absNorm B : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  exact ⟨C,hC,fun H₀ B hB => (largeCubeCoefficient_norm_le H₀ B).trans (hbound B hB)⟩

end CompletedGauss

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def globalRowScaleFloor (K ell B F M : ℝ) : ℝ :=
  ell^2*B^2*F^2/(K*(ell*Real.exp M)^2)

theorem globalRowScaleFloor_pos (K ell B F M : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) : 0 < globalRowScaleFloor K ell B F M := by
  unfold globalRowScaleFloor
  positivity

theorem globalNormCaps_antitone_row (ell B Y₀ Y₁ M H : ℝ) (hY₀ : 0 < Y₀)
    (hY : Y₀ ≤ Y₁) (hH : 0 ≤ H) :
    ∀ i,globalNormCaps ell B Y₁ M H i ≤ globalNormCaps ell B Y₀ M H i := by
  have hc : ⌈H*(ell*Real.exp M)^2/Y₁⌉₊ ≤ ⌈H*(ell*Real.exp M)^2/Y₀⌉₊ :=
    Nat.ceil_mono (div_le_div_of_nonneg_left (by positivity) hY₀ hY)
  have hc' : (⌈H*(ell*Real.exp M)^2/Y₁⌉₊ : ℝ) ≤ ⌈H*(ell*Real.exp M)^2/Y₀⌉₊ := by exact_mod_cast hc
  intro i
  fin_cases i <;> simp [globalNormCaps]
  gcongr

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalRowScaleFloor_le_pooled (K ell B F M : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (side : Bool) (x : GlobalSecondData ι)
    (hx : GlobalSecondAdmissible x) (hk : x.source.frequency ≠ 0)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalRowScaleFloor K ell B F M ≤ globalPooledRowScale K ell B F (globalScaleIndex p side x) := by
  let j := globalScaleIndex p side x
  have hC : globalLogRep j 1 ≤ ell*Real.exp M :=
    (globalScaleIndex_bounds p hp side x hk 1).1.trans (globalSupported_small_norms p hp ell M hell side x hx hs).2.1
  have hJ := globalPooled_J_bound p hp B hB side x hk hb₁ hb₂
  have hcpos := globalLogRep_pos j 1
  have hjpos := globalLogRep_pos j 4
  have hd := globalLogRep_ge_one j 5
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  unfold globalRowScaleFloor globalPooledRowScale
  calc
    ell^2*B^2*F^2/(K*(ell*Real.exp M)^2) = ell^2*B^4*F^2/(K*(ell*Real.exp M)^2*B^2) := by field_simp
    _ ≤ Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4) := by
      apply div_le_div₀ (by positivity)
      · calc
          ell^2*B^4*F^2 = 1*ell^2*B^4*F^2*1 := by ring
          _ ≤ _ := by gcongr
      · positivity
      · gcongr

include hp in

theorem globalScaleIndex_mem_uniform_box (K ell B F M H : ℝ)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) (hH : 0 ≤ H)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk0 : x.source.frequency ≠ 0)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      (globalPooledRowScale K ell B F (globalScaleIndex p side x)) M H x.source.sourceCommon x.source.divisor) :
    globalScaleIndex p side x ∈
      globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) := by
  have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalScaleIndex p side x)
  have hfloor := globalRowScaleFloor_pos K ell B F M hK hell hB hF
  have hlower := globalRowScaleFloor_le_pooled p hp K ell B F M hK hell hB hF side x hx hk0 hs hb₁ hb₂
  have hcaps := globalScaleVector_le_caps p hp ell B _ M H hell hB.le hY hH side x hx hs hb₁ hb₂ hk
  apply globalScaleIndex_mem_box p hp side x hk0
  intro i
  exact (hcaps i).trans (globalNormCaps_antitone_row ell B _ _ M H hfloor hlower hH i)

end

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def weightedGlobalArithmeticBinSource (γ : GlobalSecondData ι → ℂ) (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) : ℂ :=
  globalSecondRawSource p hp hcop hg (globalArithmeticBin p s side q j)
    (fun x => γ x*globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x)
    F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j)

theorem weightedGlobalArithmeticBinSource_squarefree (γ : GlobalSecondData ι → ℂ) (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hs : ∀ x∈s,GlobalSecondAdmissible x)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) :
    weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j F Ψ m ray A₁ A₂ W V ell Y =
    globalSecondRawSource p hp hcop hg (globalSquarefreeBin p s side q j)
      (fun x => γ x*globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x)
      F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
      (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
      (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  unfold weightedGlobalArithmeticBinSource globalSecondRawSource globalSquarefreeBin
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hsf : Squarefree (newLabel (globalSecondTuple p x))
  · rw [ite_eq_left hsf]
  · rw [ite_eq_right hsf]
    have hz : globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x=0 := by
      by_contra hn
      exact hsf (globalSecondOuterWeight_squarefree p hp hcop hg Ψ m ray ell Y side x
        (hs x (Finset.mem_filter.mp hx).1) hn)
    simp only [hz,mul_zero,zero_mul]

end

theorem full_uniform_weightedGlobalArithmeticBin_transfer
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2), ∀ (θ₁ θ₂ : ℝ), ∀ (s : Finset (GlobalSecondData ι)) (side : Bool)
      (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (ell Y : ℝ)
      (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < ell → 0 < Y → q.1 ≠ ⊥ → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      ‖weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j F Ψ m ray (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V ell Y‖ ≤
      (Γ*C)*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalPooledOuterBound ray ell Y j*
        (globalPooledLabelScale j*Ideal.absNorm q.1)^ε/(1+globalBinRadial ell Y j)^A *
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := full_uniform_globalSecondRawSource_twisted_transfer ε hε A₁ A₂ W V M hM hV A J
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound V hVc hVs
  refine ⟨Cₐ*Cₛ*Cw,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc
  have htrans := htrans p hp hcop hg hinj
  intro θ₁ θ₂ s side q j F Ψ m ray ell Y γ Γ hell hY hq hΓ hγ hΨ hs hk
  rw [weightedGlobalArithmeticBinSource_squarefree p hp hcop hg γ s side q j hs]
  let t := globalSquarefreeBin p s side q j
  let T := globalArithmeticTargets p s side q j
  have ht (x : GlobalSecondData ι) (hx : x∈t) : x∈s ∧ globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hbound := globalArithmeticTargets_bounds p hp s side q j hk
  have hB : 0 ≤ globalPooledOuterBound ray ell Y j := by
    have h0 := (globalLogRep_pos j 0).le
    have h1 := (globalLogRep_pos j 1).le
    have h2 := (globalLogRep_pos j 2).le
    have h3 := (globalLogRep_pos j 3).le
    unfold globalPooledOuterBound
    positivity
  have hw : ∀ x∈t,‖γ x*globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x‖*
      ‖JointLogSeparation.outerWindow V (globalBinZ p ell side j x) (globalBinUd p j x)
        (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)‖ ≤ Γ*globalPooledOuterBound ray ell Y j*Cw := by
    intro x hx
    have hh := globalSecondOuterWeight_bin_bound p hp hcop hg hinj hc Ψ hΨ m ray ell Y hell hY.le side x (hk x (ht x hx).1)
    rw [(ht x hx).2.2] at hh
    rw [norm_mul]
    exact mul_le_mul (mul_le_mul (hγ x (ht x hx).1) hh (norm_nonneg _) hΓ)
      (hwglobal _ _ _ _ _) (norm_nonneg _) (mul_nonneg hΓ hB)
  have hh := htrans (globalBinRadial ell Y j) (globalBinRadial_pos ell Y hell hY j) θ₁ θ₂ t T q
    (fun x => γ x*globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x) (Γ*globalPooledOuterBound ray ell Y j*Cw)
    (globalPooledLabelScale j) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) hq (mul_nonneg (mul_nonneg hΓ hB) hCw)
    (zero_le_one.trans (globalPooledLabelScale_ge_one j))
    (fun x hx => hs x (ht x hx).1) (fun x hx => (ht x hx).2.1)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun a ha => (hbound a ha).1) (fun a ha => (hbound a ha).2.1) hw
  convert hh using 1 ; ring

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)

theorem weightedGlobalPositiveBin_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < K → 0 < ell → 0 < B → 0 < F → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight (Γ*C) ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨C,hC,htrans⟩ := full_uniform_weightedGlobalArithmeticBin_transfer ε hε A₁ A₂ W V M hM hV hVc hVs A J
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj hc θ₁ θ₂ K ell B F s side j pool Ψ m γ Γ hK hell hB hF hΓ hγ hΨ hs hk
  have hy := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hmass : globalPooledColumnScale ell j*globalPooledLabelScale j ≠ 0 :=
    (mul_pos (globalPooledColumnScale_pos ell hell j) (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))).ne'
  calc
    _ ≤ globalBinFirstCoefficient K ell B F j *
        ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        ‖weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ := by
      apply mul_le_mul_of_nonneg_left _ hfirst
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ray hray
      exact norm_sum_le _ _
    _ = ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalBinFirstCoefficient K ell B F j *
        ‖weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ := by simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
      have hq0 : q.1 ≠ ⊥ := by
        rw [← hqx]
        exact (globalSecondFixedTriple_nonzero p hp x).1
      have ht := htrans p hp hcop hg hinj hc θ₁ θ₂ s side q j pool Ψ m ray ell
        (globalPooledRowScale K ell B F j) γ Γ hell hy hq0 hΓ hγ hΨ hs hk
      have ht' := mul_le_mul_of_nonneg_left ht hfirst
      apply ht'.trans_eq
      have hc0 := (globalPooledColumnScale_pos ell hell j).ne'
      have hl0 := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).ne'
      unfold globalDescentWeight
      field_simp

end SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem fixedSecondTest_subunit (V : ℝ → ℂ) (X A : ℝ) (hX : 0 < X)
    (hV : ∀ s,V s ≠ 0 → |s| ≤ A) (hsmall : X*Real.exp A < 1)
    (a b : ℝ) (negative : Bool) (S : Finset ι) : fixedSecondTest p V X a b negative S=0 := by
  have hz : V (columnLog p X S)=0 := by
    by_contra hn
    have hh := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have h1 := primeProductNorm_ge_one p hp S
    linarith
  cases negative <;> simp [fixedSecondTest,JointLogSeparation.fixedColumnTest,hz]

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem childEnergy_subunit (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X A : ℝ) (hX : 0 < X)
    (hV : ∀ s,V s ≠ 0 → |s| ≤ A) (hsmall : X*Real.exp A < 1)
    (a b : ℝ) (negative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X negative rowNegative a b=0 := by
  have hrow (f y : O) : fixedChildRow p hp hcop hg pool Ψ m (fixedSecondTest p V X a b negative) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,fixedSecondTest_subunit p hp V X A hX hV hsmall a b negative S,mul_zero]
  simp [childEnergy,idealChildRow,hrow]

theorem densityChildEnergy_subunit (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ A : ℝ) (J : ℕ) (hX : 0 < X₁)
    (hV : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hsmall : X₁*Real.exp A < 1) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J=0 := by
  unfold densityChildEnergy childGeometricMean
  simp only [childEnergy_subunit p hp hcop hg pool Ψ₁ m T V₁ X₁ A hX hV hsmall,
    Real.sqrt_zero,zero_mul,mul_zero,integral_zero]

theorem childDensity_elementary_all_scales
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      (6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3)*K*X := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · exact childDensity_elementary_supported p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X F K A M J hX hF hK hA hM hscale hV₁ hV₂ hVs₁ hVs₂ hT
  · rw [densityChildEnergy_subunit p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X A (2*J) hX hVs₁ (lt_of_not_ge hscale),zero_div]
    have hI : 0 ≤ ∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t :=
      integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
    positivity

end SecondPassIntegration
end

namespace SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)

def globalTerminalConstant (A M : ℝ) : ℝ :=
  6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3

def globalRayTripleConstant : ℝ := 128^3*(Real.exp 1)^18*(512*32^2)

theorem globalTerminalConstant_nonneg (A M : ℝ) : 0 ≤ globalTerminalConstant A M := by
  have hI : 0 ≤ ∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  unfold globalTerminalConstant
  positivity

theorem radial_decay_step (R : ℝ) (hR : 0 ≤ R) (N : ℕ) :
    R/(1+R)^(N+1) ≤ 1/(1+R)^N := by
  have h1 : 0 < 1+R := by linarith
  have hr : R/(1+R) ≤ 1 := (div_le_iff₀ h1).mpr (by linarith)
  calc
    R/(1+R)^(N+1) = (R/(1+R))/(1+R)^N := by rw [pow_succ];field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hr (pow_nonneg h1.le _)

theorem globalPooledRow_radial_bound (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 1 ≤ B) (hF : 1 ≤ F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2) :
    globalLogRep j 8*Real.exp 1 ≤ globalBinRadial ell (globalPooledRowScale K ell B F j) j*K := by
  have hB0 := zero_lt_one.trans_le hB
  have hF0 := zero_lt_one.trans_le hF
  have hD := globalPooledDelta_pos B F hB0 hF0 j
  have hD1 : 1 ≤ globalPooledDelta B F j :=
    (one_le_mul_of_one_le_of_one_le hB hF).trans (globalPooledDelta_ge B F hB0.le hF0.le j)
  have hN := globalPooledNaturalRow_pos K B F hK hB0 hF0 j
  have hR := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell
    (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
  have he : globalLogRep j 8*Real.exp 1 =
      globalBinRadial ell (globalPooledRowScale K ell B F j) j*globalPooledNaturalRow K B F j := by
    rw [globalBinRadial,globalPooled_radial_ratio K ell B F hK hell hB0 hF0]
    field_simp
  calc
    _ = _ := he
    _ ≤ globalBinRadial ell (globalPooledRowScale K ell B F j) j*(K/(globalPooledDelta B F j)^2) :=
      mul_le_mul_of_nonneg_left (globalPooledNaturalRow_bound K B F hK hB0 hF0 j hJ) hR.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_self hK.le (one_le_pow₀ hD1)) hR.le

theorem globalRadialBin_terminal_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (V₁ V₂ : ℝ → ℂ) (C ε θ₁ θ₂ K ell B F A₀ M : ℝ) (N J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hA₀ : 0 ≤ A₀) (hM : 0 ≤ M)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ M) (hV₂ : ∀ t,‖V₂ t‖ ≤ M)
    (hVs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A₀) (hVs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A₀)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hJ : globalLogRep j 4 ≤ B^2) :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
    (C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (globalTerminalConstant A₀ M*globalRayTripleConstant)*K*((ell*B^3)*F)) /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by
  let X := globalPooledColumnScale ell j
  let lengthScale := globalPooledLabelScale j
  let R := globalBinRadial ell (globalPooledRowScale K ell B F j) j
  let K' := globalLogRep j 8*Real.exp 1
  let Ct := globalTerminalConstant A₀ M
  let Q := C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (Ct*globalRayTripleConstant)*K*((ell*B^3)*F)
  have hB0 := zero_lt_one.trans_le hB
  have hF0 := zero_lt_one.trans_le hF
  have hX := globalPooledColumnScale_pos ell hell j
  have hL := globalPooledLabelScale_ge_one j
  have hR : 0 < R := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
  have hK' : 1 ≤ K' := one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hCt : 0 ≤ Ct := globalTerminalConstant_nonneg A₀ M
  have hrow : K' ≤ R*K := globalPooledRow_radial_bound K ell B F hK hell hB hF j hJ
  have hQ : 0 ≤ Q := by
    have hn : 0 ≤ globalBinLossScale B j := by
      have hh := (globalLogRep_pos j 4).le
      unfold globalBinLossScale;positivity
    unfold Q globalRayTripleConstant
    positivity
  have hterm (ray : SecondRayIndex) (q : Ideal O × Ideal O × Ideal O) :
      densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂ X X (2*J)/(X*lengthScale) ≤ Ct*K'*(X*lengthScale) := by
    have h := SecondPassIntegration.childDensity_elementary_all_scales p hp hcop hg hc hinj pool
      (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (fun a => (secondRayMinus_norm_le Ψ ray a).trans (hΨ a))
      (fun a => (secondRayPlus_norm_le Ψ ray a).trans (hΨ a))
      (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂ X lengthScale K' A₀ M J
      hX hL hK' hA₀ hM hV₁ hV₂ hVs₁ hVs₂ (globalArithmeticTargets_bounds p hp s side q j hk)
    apply h.trans
    apply mul_le_mul_of_nonneg_left
    · exact le_mul_of_one_le_right hX.le hL
    · exact mul_nonneg hCt (zero_le_one.trans hK')
  have hmass := globalDescentWeight_mass p hp C ε θ₁ θ₂ K ell B F (N+1) (2*J)
    hC hε hK hell hB0 hF0 side s j hk hb₁ hb₂
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q*(Ct*K'*(X*lengthScale)) := by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hterm ray q)
        (globalDescentWeight_nonneg C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q hC hK hell hB0 hF0)
    _ = Ct*K'*(∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q*(X*lengthScale)) := by
      simp only [Finset.mul_sum]
      congr 1
      funext ray
      congr 1
      funext q
      ring
    _ ≤ Ct*(R*K)*((C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε /
        (1+R)^(N+1))*globalRayTripleConstant*((ell*B^3)*F)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hrow hCt
      · exact hmass
      · apply Finset.sum_nonneg
        intro ray hray
        apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg (globalDescentWeight_nonneg C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q hC hK hell hB0 hF0)
          (mul_nonneg hX.le (zero_le_one.trans hL))
      · exact mul_nonneg hCt (mul_nonneg hR.le hK.le)
    _ = Q*(R/(1+R)^(N+1)) := by dsimp only [Q];ring
    _ ≤ Q*(1/(1+R)^N) := mul_le_mul_of_nonneg_left (radial_decay_step R hR.le N) hQ
    _ = _ := by dsimp only [Q,R,Ct];ring

theorem globalRadialBin_terminal_bound_all_bins {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (V₁ V₂ : ℝ → ℂ) (C ε θ₁ θ₂ K ell B F A₀ M : ℝ) (N J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hA₀ : 0 ≤ A₀) (hM : 0 ≤ M)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ M) (hV₂ : ∀ t,‖V₂ t‖ ≤ M)
    (hVs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A₀) (hVs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A₀)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
    (C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (globalTerminalConstant A₀ M*globalRayTripleConstant)*K*((ell*B^3)*F)) /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by
  by_cases hs : (globalLogSector p s side j).Nonempty
  · obtain ⟨x,hx⟩ := hs
    obtain ⟨hxs,hj⟩ := Finset.mem_filter.mp hx
    have hJ := globalPooled_J_bound p hp B (zero_lt_one.trans_le hB) side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
    rw [hj] at hJ
    exact globalRadialBin_terminal_bound p hp hcop hg hc hinj pool Ψ hΨ m V₁ V₂ C ε θ₁ θ₂ K ell B F A₀ M N J
      hC hε hK hell hB hF hA₀ hM hV₁ hV₂ hVs₁ hVs₂ s side j hk hb₁ hb₂ hJ
  · have he : globalBinTriples p s side j=∅ := by
      simp only [globalBinTriples,Finset.not_nonempty_iff_eq_empty.mp hs,Finset.image_empty]
    rw [he]
    simp only [Finset.sum_empty,Finset.sum_const_zero]
    have hB0 := zero_lt_one.trans_le hB
    have hF0 := zero_lt_one.trans_le hF
    have hR := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
    have hct := globalTerminalConstant_nonneg A₀ M
    have hl := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
    have h4 := globalLogRep_pos j 4
    have hh : 0 ≤ globalBinLossScale B j := by unfold globalBinLossScale;positivity
    unfold globalRayTripleConstant
    positivity

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum CompletedGauss
open QuadraticSquarefreeKernel

def liftingPrimeElement : O := ActualEisensteinCoordinates.eval 1 3
def liftingPrime : Ideal O := Ideal.span {liftingPrimeElement}

theorem liftingPrimeElement_norm : ShortDraftLatticeCount.qNat liftingPrimeElement=7 := by
  unfold ShortDraftLatticeCount.qNat liftingPrimeElement
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem liftingPrime_norm : Ideal.absNorm liftingPrime=7 := by
  rw [liftingPrime,←qNat_eq_absNorm_span,liftingPrimeElement_norm]

theorem liftingPrime_prime : Prime liftingPrime := by
  apply Ideal.prime_of_isPrime
  · intro h
    have hh := Ideal.absNorm_eq_zero_iff.mpr h
    rw [liftingPrime_norm] at hh
    norm_num at hh
  · exact Ideal.isPrime_of_irreducible_absNorm (by
      rw [liftingPrime_norm,Nat.irreducible_iff_nat_prime]
      exact (by decide : Nat.Prime 7))

theorem liftingPrime_supported : Supported liftingPrime := by
  apply (supported_span_iff liftingPrimeElement).mpr
  have hlam : ShortDraftLatticeCount.qNat lambda=3 := by
    have he : lambda=ActualEisensteinCoordinates.eval (-1) 1 := theta_counter_lambda_eq
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q]
  have htwo : ShortDraftLatticeCount.qNat (2:O)=4 := by
    have he : (2:O)=ActualEisensteinCoordinates.eval 2 0 := by simp [ActualEisensteinCoordinates.eval]
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q]
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,hlam] at h
    omega
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,htwo] at h
    omega

theorem liftingPrime_admissible : Admissible liftingPrime :=
  ⟨liftingPrime_prime.ne_zero,liftingPrime_prime.squarefree,liftingPrime_supported.2⟩

theorem supported_pow {I : Ideal O} (hI : Supported I) (k : ℕ) : Supported (I^k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    change P∈UniqueFactorizationMonoid.normalizedFactors (1:Ideal O) at hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | succ k hk =>
    rw [pow_succ]
    exact (supported_mul_iff _ _).mpr ⟨hk,hI⟩

theorem exists_lifting_exponent (M : ℝ) (I : Ideal O) (hI : I≠0)
    (hIM : (Ideal.absNorm I:ℝ)≤M) :
    ∃k : ℕ, M<(49:ℝ)^k*(Ideal.absNorm I:ℝ) ∧
      (49:ℝ)^k*(Ideal.absNorm I:ℝ)≤49*M := by
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ hN).mpr (by simpa using hIM))
    (by norm_num : (1:ℝ)<49)
  refine ⟨k+1,?_,?_⟩
  · exact (div_lt_iff₀ hN).mp hhi
  · have h := (le_div_iff₀ hN).mp hlo
    rw [pow_succ]
    nlinarith

def liftingExponent (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : ℕ :=
  (exists_lifting_exponent M I hI hIM).choose

def liftedRow (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : Ideal O :=
  (liftingPrime^liftingExponent M I hI hIM)^2*I

theorem liftedRow_norm (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    (Ideal.absNorm (liftedRow M I hI hIM):ℝ)=(49:ℝ)^liftingExponent M I hI hIM*(Ideal.absNorm I:ℝ) := by
  simp only [liftedRow,map_mul,map_pow,liftingPrime_norm,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [←pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem liftedRow_bounds (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    M<(Ideal.absNorm (liftedRow M I hI hIM):ℝ) ∧
      (Ideal.absNorm (liftedRow M I hI hIM):ℝ)≤49*M := by
  rw [liftedRow_norm]
  exact (exists_lifting_exponent M I hI hIM).choose_spec

theorem liftedRow_squarefreePart (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : squarefreePart (liftedRow M I hI.1 hIM)=I :=
  (squarePart_mul_squarefree (pow_ne_zero _ liftingPrime_prime.ne_zero) hI.2.1).2

theorem liftedRow_supported (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : Supported (liftedRow M I hI.1 hIM) := by
  exact (supported_mul_iff _ _).mpr
    ⟨supported_pow (supported_pow liftingPrime_supported _) _,admissible_supported hI⟩

theorem liftedRow_character (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) (J : Ideal O) (hJ : Admissible J)
    (hPJ : IsCoprime liftingPrime J) :
    quadraticRow J (primaryGenerator (liftedRow M I hI.1 hIM)) =
      quadraticRow J (primaryGenerator I) := by
  rw [liftedRow,canonical_quadraticRow_primary_squarefree J hJ,
    idealZeroMask_primary_eq_indicator J _ hJ.1 (supported_pow liftingPrime_supported _),
    ite_eq_left hPJ.pow_left,one_mul]

theorem liftedRow_injective (M : ℝ) :
    Function.Injective (fun I : idealRange M =>
      liftedRow M I.val (mem_idealRange.mp I.property).1.1 (mem_idealRange.mp I.property).2) := by
  intro I J h
  apply Subtype.ext
  have he := congrArg squarefreePart h
  simpa only [liftedRow_squarefreePart M I.val (mem_idealRange.mp I.property).1,
    liftedRow_squarefreePart M J.val (mem_idealRange.mp J.property).1] using he

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularLifting -/

section

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss QuadraticSquarefreeKernel

def squarefreeHighRange (M K : ℝ) : Finset (Ideal O) :=
  (idealRange M).filter (fun I => K<(Ideal.absNorm I:ℝ))

def annularLift (M K : ℝ) (I : squarefreeHighRange M K) : Ideal O :=
  liftedRow M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1.1
    (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).2

theorem annularLift_injective (M K : ℝ) : Function.Injective (annularLift M K) := by
  intro I J h
  have he := congrArg squarefreePart h
  apply Subtype.ext
  simpa only [annularLift,
    liftedRow_squarefreePart M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1,
    liftedRow_squarefreePart M J.val (mem_idealRange.mp (Finset.mem_filter.mp J.property).1).1] using he

theorem annularLift_properties (M K : ℝ) (I : squarefreeHighRange M K) :
    Supported (annularLift M K I) ∧ K<(Ideal.absNorm (squarefreePart (annularLift M K I)):ℝ) ∧
      M<(Ideal.absNorm (annularLift M K I):ℝ) ∧ (Ideal.absNorm (annularLift M K I):ℝ)≤49*M := by
  have hi := mem_idealRange.mp (Finset.mem_filter.mp I.property).1
  have hn := liftedRow_bounds M I.val hi.1.1 hi.2
  refine ⟨liftedRow_supported M I.val hi.1 hi.2,?_,hn⟩
  simpa only [annularLift,liftedRow_squarefreePart M I.val hi.1] using (Finset.mem_filter.mp I.property).2

theorem annularLift_row_sum (M N K : ℝ) (I : squarefreeHighRange M K)
    (a : idealRange N → ℂ)
    (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑J : idealRange N, quadraticRow J.val (primaryGenerator (annularLift M K I))*a J) =
      ∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J := by
  apply Finset.sum_congr rfl
  intro J _
  by_cases hz : a J=0
  · simp only [hz,mul_zero]
  · rw [annularLift,liftedRow_character M I.val
      (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1 _ J.val
      (mem_idealRange.mp J.property).1 (hcop J hz)]

lemma exists_lifted_annular_scale (M x : ℝ) (hM : 0<M) (hx : M<x) (hupper : x≤49*M) :
    ∃j : Fin 7, ((2:ℝ)^j.val*M)/2≤x ∧ x≤(2:ℝ)^j.val*M := by
  have hratio : 1≤x/M := (le_div_iff₀ hM).mpr (by linarith)
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
  have hratioU : x/M≤49 := (div_le_iff₀ hM).mpr hupper
  have hk : k<6 := by
    by_contra hn
    have h6 : 6≤k := by omega
    have hp : (2:ℝ)^6≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) h6
    norm_num at hp
    linarith
  refine ⟨⟨k+1,by omega⟩,?_,?_⟩
  · have hl := (le_div_iff₀ hM).mp hlo
    simpa only [pow_succ,mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using hl
  · exact ((div_lt_iff₀ hM).mp hhi).le

lemma sum_injective_mask_le {ι : Type*} [Fintype ι]
    (f : ι → Ideal O) (hf : Function.Injective f) (S : Finset (Ideal O))
    (v : Ideal O → ℝ) (hv : ∀I, 0≤v I) :
    (∑i, if f i∈S then v (f i) else 0)≤∑I∈S,v I := by
  classical
  rw [←Finset.sum_filter]
  rw [←Finset.sum_image (f := v) (g := f) (by intro i hi j hj he; exact hf he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact (Finset.mem_filter.mp hi).2
  · intro I hI hnot
    exact hv I

theorem squarefreeHigh_energy_le_annuli (M N K : ℝ) (hM : 0<M)
    (a : idealRange N → ℂ) (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K a := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hE (I : Ideal O) : 0≤E I := sq_nonneg _
  have hlift :
      (∑I : squarefreeHighRange M K, E I.val) = ∑I : squarefreeHighRange M K, E (annularLift M K I) := by
    apply Finset.sum_congr rfl
    intro I _
    dsimp only [E]
    rw [annularLift_row_sum M N K I a hcop]
  change (∑I : squarefreeHighRange M K, E I.val)≤_
  rw [hlift]
  have hpoint (I : squarefreeHighRange M K) : E (annularLift M K I) ≤
      ∑j : Fin 7, if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := by
    have hp := annularLift_properties M K I
    obtain ⟨j,hjlo,hjhi⟩ := exists_lifted_annular_scale M _ hM hp.2.2.1 hp.2.2.2
    have hMj : 0<(2:ℝ)^j.val*M := by positivity
    have hm : annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K :=
      mem_highKernelRange.mpr ⟨hp.1,by linarith,hp.2.1⟩
    have hw : annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)=1 := by
      apply QuadraticInitialBound.annularSieveBump_eq_one
      · exact (le_div_iff₀ hMj).mpr (by linarith)
      · exact (div_le_one hMj).mpr hjhi
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 7)))
      (f := fun j => if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0)
      (fun j _ => by split_ifs; exact mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE _); exact le_rfl)
      (Finset.mem_univ j)
    simpa only [hm,ite_true,hw,one_mul] using hh
  calc
    _ ≤ ∑I : squarefreeHighRange M K, ∑j : Fin 7,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = ∑j : Fin 7, ∑I : squarefreeHighRange M K,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [annularHighEnergy,Finset.sum_coe_sort (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)]
      exact sum_injective_mask_le (annularLift M K) (annularLift_injective M K)
        (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)
        (fun I => mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE I))

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open FiniteSieveRestriction

def liftingDivisibleColumns (N : ℝ) : Finset (idealRange N) :=
  Finset.univ.filter (fun J => liftingPrime∣J.val)

def liftingQuotientColumn (N : ℝ) (J : liftingDivisibleColumns N) : idealRange N :=
  ⟨idealQuotient liftingPrime J.val.val, by
    have hd := (Finset.mem_filter.mp J.property).2
    have hj := mem_idealRange.mp J.val.property
    refine mem_idealRange.mpr ⟨admissible_idealQuotient hj.1 hd,?_⟩
    have hn := idealQuotient_norm_le liftingPrime_prime.ne_zero hd N hj.2
    rw [liftingPrime_norm] at hn
    have hN : 0≤N := (Nat.cast_nonneg _).trans hj.2
    exact hn.trans (by norm_num; linarith)⟩

theorem liftingQuotientColumn_injective (N : ℝ) : Function.Injective (liftingQuotientColumn N) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  exact idealQuotient_injective_on liftingPrime
    (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2 (congrArg Subtype.val h)

def liftingFreeCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  fun J => if liftingPrime∣J.val then 0 else a J

def liftingDividedCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  extendByZero Finset.univ (liftingQuotientColumn N) (fun J : liftingDivisibleColumns N => a J.val)

theorem liftingFreeCoefficient_coprime (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingFreeCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  apply ideals_coprime_of_relprime
  apply liftingPrime_prime.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hJ (by simp only [liftingFreeCoefficient,hd,ite_true])

theorem liftingDividedCoefficient_coprime (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingDividedCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  classical
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have hdiv := (Finset.mem_filter.mp I.property).2
  have hsf : Squarefree (liftingPrime*idealQuotient liftingPrime I.val.val) := by
    rw [idealQuotient_mul hdiv]
    exact (mem_idealRange.mp I.val.property).1.2.1
  exact ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hsf).1

theorem liftingDividedCoefficient_row_sum (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    (∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J) =
      ∑J : liftingDivisibleColumns N, quadraticRow (idealQuotient liftingPrime J.val.val) z*a J.val := by
  simpa only [liftingDividedCoefficient,liftingQuotientColumn] using
    extendByZero_matrix Finset.univ (liftingQuotientColumn N)
      (fun J : liftingDivisibleColumns N => a J.val) (fun (_ : Unit) J => quadraticRow J.val z) ()

theorem liftingCoefficient_row_split (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    (∑J : idealRange N, quadraticRow J.val z*a J) =
      (∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J) +
      quadraticRow liftingPrime z*(∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J) := by
  rw [liftingDividedCoefficient_row_sum,Finset.mul_sum,
    Finset.sum_coe_sort (liftingDivisibleColumns N)
      (fun J => quadraticRow liftingPrime z*(quadraticRow (idealQuotient liftingPrime J.val) z*a J))]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val
  · simp only [hd,ite_true,liftingFreeCoefficient,mul_zero,zero_add]
    rw [quadraticRow_divisor_factor J.val liftingPrime (mem_idealRange.mp J.property).1 hd z]
    ring
  · simp only [hd,ite_false,liftingFreeCoefficient,add_zero]

theorem liftingCoefficient_energy (N : ℝ) (a : idealRange N → ℂ) :
    (∑J : idealRange N, ‖liftingFreeCoefficient N a J‖^2) +
      (∑J : idealRange N, ‖liftingDividedCoefficient N a J‖^2) = ∑J, ‖a J‖^2 := by
  have he := extendByZero_energy Finset.univ (liftingQuotientColumn N)
    (fun J : liftingDivisibleColumns N => a J.val) (liftingQuotientColumn_injective N).injOn
  change (∑J : idealRange N, ‖liftingDividedCoefficient N a J‖^2)=
    ∑J : liftingDivisibleColumns N, ‖a J.val‖^2 at he
  rw [he,Finset.sum_coe_sort (liftingDivisibleColumns N) (fun J => ‖a J‖^2)]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val <;>
    simp only [liftingFreeCoefficient,hd,ite_true,ite_false,norm_zero,zero_pow (by decide : 2≠0),zero_add,add_zero]

theorem liftingCoefficient_row_energy (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    ‖∑J : idealRange N, quadraticRow J.val z*a J‖^2 ≤
      2*(‖∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J‖^2 +
        ‖∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J‖^2) := by
  rw [liftingCoefficient_row_split]
  let u := ∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J
  let v := ∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J
  change ‖u+quadraticRow liftingPrime z*v‖^2≤2*(‖u‖^2+‖v‖^2)
  have hp : ‖quadraticRow liftingPrime z*v‖≤‖v‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
  have hn : ‖u+quadraticRow liftingPrime z*v‖≤‖u‖+‖v‖ := by
    linarith [norm_add_le u (quadraticRow liftingPrime z*v)]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

theorem liftingFreeCoefficient_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N X (liftingFreeCoefficient N a) := by
  intro J hJ
  have hj : a J≠0 := by
    intro hz
    exact hJ (by simp only [liftingFreeCoefficient,hz,ite_self])
  exact ha J hj

theorem liftingDividedCoefficient_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N (X/7) (liftingDividedCoefficient N a) := by
  classical
  intro J hJ
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have he : liftingDividedCoefficient N a (liftingQuotientColumn N I)=a I.val :=
    extendByZero_apply_image _ _ _ (liftingQuotientColumn_injective N).injOn I (Finset.mem_univ I)
  have hn : a I.val≠0 := by rwa [he] at hJ
  have hs := ha I.val hn
  change (X/7)/2<(Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ) ∧
    (Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ)≤X/7
  rw [idealQuotient_norm_eq liftingPrime I.val.val liftingPrime_prime.ne_zero
    (Finset.mem_filter.mp I.property).2,liftingPrime_norm]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith

theorem coefficientOnShell_zero_or_scale (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : (∀J, a J=0) ∨ 1≤X := by
  classical
  by_cases h : ∀J, a J=0
  · exact Or.inl h
  · push Not at h
    obtain ⟨J,hJ⟩ := h
    have hnorm : 1≤(Ideal.absNorm J.val:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => (mem_idealRange.mp J.property).1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact Or.inr (hnorm.trans (ha J hJ).2)

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator

def ballQuadraticEnergy (M N : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑I : idealRange M, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2

theorem ballQuadraticEnergy_low_high (M N K : ℝ) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      ∑I : squarefreeHighRange M K, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2 := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hs : (idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K) ⊆ idealRange K := by
    intro I hI
    exact mem_idealRange.mpr ⟨(mem_idealRange.mp (Finset.mem_filter.mp hI).1).1,(Finset.mem_filter.mp hI).2⟩
  have hlo : (∑I∈(idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K), E I) ≤
      sieveNorm K N*(∑J, ‖a J‖^2) := by
    calc
      _ ≤ ∑I∈idealRange K,E I := Finset.sum_le_sum_of_subset_of_nonneg hs (fun I hI hnot => sq_nonneg _)
      _ = ballQuadraticEnergy K N a := (Finset.sum_coe_sort (idealRange K) E).symm
      _ ≤ _ := FiniteSieveOperator.energy_bound (matrix K N) a
  change (∑I : idealRange M,E I.val)≤_+(∑I : squarefreeHighRange M K,E I.val)
  rw [Finset.sum_coe_sort (idealRange M) E,
    ←Finset.sum_filter_add_sum_filter_not (idealRange M) (fun I => (Ideal.absNorm I:ℝ)≤K) E]
  rw [Finset.sum_coe_sort (squarefreeHighRange M K) E]
  simp only [not_le,squarefreeHighRange]
  linarith

theorem ballQuadraticEnergy_lifted_annuli (M N K : ℝ) (hM : 0<M) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      2*((∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingFreeCoefficient N a)) +
        ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingDividedCoefficient N a)) := by
  have hlo := ballQuadraticEnergy_low_high M N K a
  have hs : (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      2*((∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2) +
        ∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) := by
    calc
      _ ≤ ∑I : squarefreeHighRange M K, 2*(
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2 +
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) :=
        Finset.sum_le_sum (fun I _ => liftingCoefficient_row_energy N a (primaryGenerator I.val))
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
  have hfree := squarefreeHigh_energy_le_annuli M N K hM (liftingFreeCoefficient N a)
    (liftingFreeCoefficient_coprime N a)
  have hdiv := squarefreeHigh_energy_le_annuli M N K hM (liftingDividedCoefficient N a)
    (liftingDividedCoefficient_coprime N a)
  linarith

end

open ActualEisensteinCubic CompletedGauss

theorem ballQuadraticEnergy_mono {M M' N : ℝ} (hM : M≤M') (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a≤ballQuadraticEnergy M' N a := by
  unfold ballQuadraticEnergy
  rw [Finset.sum_coe_sort (idealRange M)
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2),
    Finset.sum_coe_sort (idealRange M')
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (idealRange_mono hM) (fun I hI hnot => sq_nonneg _)

theorem ballQuadraticEnergy_coefficientAtScale (M N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀J, a J≠0 → (Ideal.absNorm J.val:ℝ)≤X) :
    ballQuadraticEnergy M N a=ballQuadraticEnergy M X (coefficientAtScale N X a) := by
  unfold ballQuadraticEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

theorem ballQuadraticEnergy_column_shells (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M N (dyadicColumnCoefficient N lengthScale hNL j a) := by
  simpa only [one_mul,ballQuadraticEnergy] using
    weighted_energy_column_shells N lengthScale hNL
      (fun I : idealRange M => fun J : idealRange N => quadraticRow J.val (primaryGenerator I.val))
      (fun _ => (1:ℝ)) (fun _ => by norm_num) a

theorem ballQuadraticEnergy_column_shells_at_scale (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M ((2:ℝ)^j.val)
        (coefficientAtScale N ((2:ℝ)^j.val) (dyadicColumnCoefficient N lengthScale hNL j a)) := by
  apply (ballQuadraticEnergy_column_shells M N lengthScale hNL a).trans_eq
  apply congrArg (fun x : ℝ => (lengthScale + 1 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro j _
  exact ballQuadraticEnergy_coefficientAtScale M N _ _
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)

theorem columnDyadicLength_scale_upper (N : ℝ) (hN : 1≤N) :
    (2:ℝ)^columnDyadicLength N≤2*N := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0≤Real.log N/Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  calc
    _ = (2:ℝ)^((columnDyadicLength N:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2:ℝ)^(Real.log N/Real.log 2+1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil.le
    _ = 2*N := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
      have he : (2:ℝ)^(Real.log N/Real.log 2)=N :=
        Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
      rw [he,mul_comm]

theorem columnDyadicScale_bounds (N : ℝ) (hN : 1≤N) (j : Fin (columnDyadicLength N+1)) :
    1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤2*N := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  exact (pow_le_pow_right₀ (by norm_num) (by omega : j.val≤ columnDyadicLength N)).trans
    (columnDyadicLength_scale_upper N hN)

end

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy

theorem gcdPool_admissible {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀j, Admissible (cols j)) (D : Ideal O) (hD : D∈gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩,_,rfl⟩ := Finset.mem_image.mp hD
  exact admissible_of_dvd (hcols j) (GCDMonoid.gcd_dvd_left _ _)

theorem annularHighEnergy_gcd_reduction (M N K H : ℝ) (hN : 1≤N) (hH : 0<H)
    (ε : ℝ) (hε : 0<ε) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ 16*((∑c : EisensteinEPrimaryPhase.Coord,
      ∑D∈(gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H),
        ‖annularRayGcdBlock M N K D c a‖) +
      highKernelNorm (2*M) (N/H) K*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
  have h := highKernel_weighted_energy_ray_gcd_reduction ε hε H hH
    (fun I : highKernelRange (2*M) K => I.val) (fun J : idealRange N => J.val)
    Subtype.val_injective Subtype.val_injective (2*M) N K hN (fun I => I.property)
    (fun J => mem_idealRange.mp J.property) (fun I => annularHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨QuadraticInitialBound.annularSieveBump.nonneg,QuadraticInitialBound.annularSieveBump.le_one⟩) a
  simpa only [annularHighEnergy,annularRayGcdBlock,one_mul] using h

theorem HasSieveExponent.annular_energy_from_scalar_cost {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP CH : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧ 0<CH ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N K T H C : ℝ),
      1≤M → 1≤N → 1≤K → 4≤T → 0<H → H≤N/2 → 0≤C →
      (∀D∈gcdPool (fun J : idealRange N => J.val), (Ideal.absNorm D:ℝ)≤H →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
          (commonMaskIdeal D) K (N/(Ideal.absNorm D:ℝ)) M T
          (fun _ : Unit => (1:ℂ)) QuadraticInitialBound.annularSieveCutoff≤C) →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N K a ≤
        16*((C/6)*(divisorConstant ε hε*N^ε) +
          (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
            (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑J,‖a J‖^2 := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hsmall⟩ :=
    hexp.annular_small_gcd_complete hα deltaLoss hδ l A
  obtain ⟨CH,hCH,hhigh⟩ := hexp.high_kernel deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,?_⟩
  intro ε hε M N K T H C hM hN hK hT hH hHN hC hcost a ha
  classical
  let S := (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H)
  have hb (D : Ideal O) (hD : D∈S) (c : EisensteinEPrimaryPhase.Coord) :
      ‖annularRayGcdBlock M N K D c a‖ ≤
        (C/6)*∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 := by
    have hd := Finset.mem_filter.mp hD
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hd.1
    have hh := hsmall ε hε M N N K T hM hK hT a ha D hadm.1 (hd.2.trans hHN) c
    rw [poissonComparisonMajorant_energy_factor] at hh
    have hbound := mul_le_mul_of_nonneg_right (hcost D hd.1 hd.2)
      (show 0≤∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 by positivity)
    change _ ≤ C*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hbound
    have hn : ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖=6*‖annularRayGcdBlock M N K D c a‖ := by
      rw [norm_mul]
      norm_num
    rw [hn] at hh
    change _≤_*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hh
    nlinarith
  have hs := gcdRaySupport_weighted_sum_bound ε hε S (fun J : idealRange N => J.val)
    (fun J => (mem_idealRange.mp J.property).1.1) a N (C/6) (by positivity)
    (fun J hJ => (mem_idealRange.mp J.property).2)
    (fun D c => ‖annularRayGcdBlock M N K D c a‖) hb
  have hNH : 1≤N/H := (le_div_iff₀ hH).mpr (by linarith)
  have hh := hhigh (2*M) (N/H) K (by linarith) hNH hK
  have hred := annularHighEnergy_gcd_reduction M N K H hN hH ε hε a
  apply hred.trans
  have hsupp := (supportConstant_pos ε hε).le
  have hdiv := (divisorConstant_pos ε hε).le
  calc
    _ ≤ 16*((C/6)*(divisorConstant ε hε*N^ε)*∑J,‖a J‖^2 +
      (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
        (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
      gcongr
    _ = _ := by ring

end

section

def cutoffRescaleCoefficient (C η r q : ℝ) : ℝ := C*r*q^2/(r/q)^η

theorem cutoffRescaleCoefficient_eq (C η r q : ℝ) (hr : 0< r) (hq : 0<q) :
    cutoffRescaleCoefficient C η r q=C*r^(1-η)*q^(2+η) := by
  rw [cutoffRescaleCoefficient,Real.div_rpow hr.le hq.le,
    Real.rpow_sub hr,Real.rpow_one,Real.rpow_add hq,Real.rpow_two]
  have hrp : r^η≠0 := (Real.rpow_pos_of_pos hr η).ne'
  have hqp : q^η≠0 := (Real.rpow_pos_of_pos hq η).ne'
  field_simp

theorem cutoffRescaleCoefficient_bounds (C η r q : ℝ)
    (hC : 0≤C) (hη : 0≤η) (hη1 : η≤1) (hr : 1≤ r) (hr64 : r≤64) (hq : 1≤q) (hq7 : q≤7) :
    C≤ cutoffRescaleCoefficient C η r q ∧ cutoffRescaleCoefficient C η r q≤21952*C := by
  rw [cutoffRescaleCoefficient_eq C η r q (by linarith) (by linarith)]
  have hrlo : 1≤ r^(1-η) := Real.one_le_rpow hr (by linarith)
  have hqlo : 1≤q^(2+η) := Real.one_le_rpow hq (by linarith)
  have hrup : r^(1-η)≤ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr (show 1-η≤1 by linarith)
  have hqup : q^(2+η)≤q^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hq (show 2+η≤(3:ℝ) by linarith)
  constructor
  · calc
      C = C*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ C*r*q^3 := by gcongr
      _ ≤ C*64*7^3 := by gcongr
      _ = _ := by ring

theorem selectedPoissonK_rescale (C M X η r q : ℝ)
    (hM : 0<M) (hX : 0<X) (hr : 0< r) (hq : 0<q) :
    selectedPoissonK (cutoffRescaleCoefficient C η r q) (r*M) (X/q) η =
      selectedPoissonK C M X η := by
  unfold selectedPoissonK selectedPoissonT cutoffRescaleCoefficient
  have he : (r*M)*(X/q)=(r/q)*(M*X) := by ring
  rw [he,Real.mul_rpow (by positivity : 0≤ r/q) (by positivity : 0≤M*X)]
  have hp : (r/q)^η≠0 := (Real.rpow_pos_of_pos (by positivity) η).ne'
  field_simp

end

open scoped BigOperators Classical

def largeGcdThreshold (α N : ℝ) : ℝ := N^(1-1/α)

theorem largeGcdThreshold_quotient_power (α N : ℝ) (hα : α≠0) (hN : 0<N) :
    (N/largeGcdThreshold α N)^α=N := by
  have he : N/largeGcdThreshold α N=N^(1/α) := by
    rw [show 1/α=1-(1-1/α) by ring,Real.rpow_sub hN,Real.rpow_one]
    rfl
  rw [he,←Real.rpow_mul hN.le]
  field_simp
  rw [Real.rpow_one]

theorem largeGcdThreshold_bounds (α N : ℝ) (hα1 : 1≤α) (hα2 : α≤2) (hN : 4≤N) :
    1≤largeGcdThreshold α N ∧ largeGcdThreshold α N≤N/2 := by
  have hα : 0<α := by linarith
  have hN0 : 0<N := by linarith
  have ha : 0≤1-1/α := by
    have hi : 1/α≤1 := (div_le_one hα).mpr hα1
    linarith
  have hb : 1-1/α≤(1/2:ℝ) := by
    have hi : (1/2:ℝ)≤1/α := (le_div_iff₀ hα).mpr (by linarith)
    linarith
  refine ⟨Real.one_le_rpow (by linarith) ha,?_⟩
  calc
    largeGcdThreshold α N ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
    _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
    _ ≤ N/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩

theorem high_kernel_chosen_scale (M N K : ℝ) (hM : 0<M) (_hN : 0<N) (hK : 0<K)
    (hcut : N^2/M≤K) : Real.sqrt ((2*M)/K)*N≤2*M := by
  have hNK : N^2≤M*K := by
    have h := (div_le_iff₀ hM).mp hcut
    nlinarith
  let s := Real.sqrt ((2*M)/K)
  have hs0 : 0≤ s := Real.sqrt_nonneg _
  have hs : s^2*K=2*M := by
    dsimp only [s]
    rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ hK.ne']
  have hb : s^2*N^2≤2*M^2 := by
    calc
      _ ≤ s^2*(M*K) := mul_le_mul_of_nonneg_left hNK (sq_nonneg s)
      _ = (s^2*K)*M := by ring
      _ = _ := by rw [hs]; ring
  change s*N≤2*M
  nlinarith [sq_nonneg (s*N)]

theorem chosen_large_gcd_main (α M N K : ℝ) (hα : α≠0)
    (hM : 0<M) (hN : 0<N) (hK : 0<K) (hcut : N^2/M≤K) :
    2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α≤4*M := by
  rw [largeGcdThreshold_quotient_power α N hα hN]
  linarith [high_kernel_chosen_scale M N K hM hN hK hcut]

theorem chosen_large_gcd_full (α deltaLoss C M N K : ℝ) (hα1 : 1≤α) (hα2 : α≤2)
    (hδ : 0≤deltaLoss) (hC : 0≤C) (hM : 0<M) (hN : 4≤N) (hK : 0<K)
    (hcut : N^2/M≤K) :
    C*((2*M)*(N/largeGcdThreshold α N))^deltaLoss*
      (2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α) ≤
        (4*C*2^deltaLoss)*(M*N)^deltaLoss*M := by
  have hh := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hH : 0<largeGcdThreshold α N := by linarith
  have hN0 : 0<N := by linarith
  have hp : ((2*M)*(N/largeGcdThreshold α N))^deltaLoss≤(2*(M*N))^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ
    have hn := div_le_self hN0.le hh.1
    nlinarith
  have hm := chosen_large_gcd_main α M N K (by linarith) hM hN0 hK hcut
  calc
    _ ≤ C*(2*(M*N))^deltaLoss*(4*M) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]; ring

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonConstants -/

section

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

theorem list_exists_positive_bound (xs : List ℝ) :
    ∃ H : ℝ, 1≤H ∧ ∀x∈xs, x≤H := by
  induction xs with
  | nil => exact ⟨1,le_rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨H,hH,hxs⟩ := ih
    refine ⟨max H x, hH.trans (le_max_left _ _), ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact le_max_right _ _
    · exact (hxs y hy).trans (le_max_left _ _)

def poissonPrimitiveConstants
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [divisorConstant η hη, 2+1/(η*Real.log 2), 256,
   supportConstant η hη, divisorExponentConstant hexp η hη,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant, CD, CS, CT, CP,
   sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W),
   sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W),
   sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, D^η]

theorem poissonPrimitiveConstants_nonneg
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (hD : 0≤D) (W : 𝓢(ℝ,ℂ)) :
    ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, 0≤x := by
  intro x hx
  simp only [poissonPrimitiveConstants,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (divisorConstant_pos η hη).le
  · have : 0<Real.log 2 := Real.log_pos (by norm_num); positivity
  · norm_num
  · exact (supportConstant_pos η hη).le
  · exact (divisorExponentConstant_pos hexp η hη).le
  · positivity
  · positivity
  · exact dualMiddleDecayConstant_nonneg _
  · positivity
  · exact originalMiddleDecayConstant_nonneg _
  · exact nonzeroLatticeEnvelopeConstant_nonneg
  · exact hCD
  · exact hCS
  · exact hCT
  · exact hCP
  · positivity
  · positivity
  · positivity
  · exact Real.rpow_nonneg hD _

theorem poissonUnitBudget_power_envelope
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (G : Ideal O) (hG : G≠0) (K N P D H : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 1≤K) (hN : 1≤N) (hP : 1≤P) (hD : 1≤D) (hH : 1≤H)
    (hconst : ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, x≤H)
    (hscales : ∀x∈([(Ideal.absNorm G:ℝ), K,N,(2*K)*N,N*N,
      (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ), 0≤x ∧ x≤D*P^4) :
    ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp η hη η hη G K N W,
      0≤x ∧ x≤(H*P^(4*η))^8 := by
  let V := H*P^(4*η)
  have hP0 : 0<P := by linarith
  have hR : 1≤P^(4*η) := Real.one_le_rpow hP (by positivity)
  have hV : 1≤V := by dsimp [V]; nlinarith
  have hCV (x : ℝ)
      (hx : x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W) :
      0≤x ∧ x≤V := by
    refine ⟨poissonPrimitiveConstants_nonneg sD sS sT CD CS CT CP hCD hCS hCT hCP
      hexp η hη D (by linarith) W x hx, ?_⟩
    have hh := hconst x hx
    dsimp [V]
    nlinarith
  have hpow (x : ℝ)
      (hx : x∈([(Ideal.absNorm G:ℝ),K,N,(2*K)*N,N*N,
        (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ)) : 0≤x^η ∧ x^η≤V := by
    have hx0 := (hscales x hx).1
    refine ⟨Real.rpow_nonneg hx0 _, ?_⟩
    have hDpow : D^η≤H := hconst _ (by simp [poissonPrimitiveConstants])
    calc
      _ ≤ (D*P^4)^η := Real.rpow_le_rpow hx0 (hscales x hx).2 hη.le
      _ = D^η*P^(4*η) := by
        rw [Real.mul_rpow (by linarith : 0≤D) (by positivity : 0≤P^4)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
      _ ≤ V := mul_le_mul_of_nonneg_right hDpow (by positivity)
  let prims := poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W ++
    [(Ideal.absNorm G:ℝ)^η,K^η,N^η,((2*K)*N)^η,(N*N)^η,
      ((Ideal.absNorm G:ℝ)*(N*N))^η,(K*N)^η]
  have hprims : ∀x∈prims, 0≤x ∧ x≤V := by
    intro x hx
    simp only [prims,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hCV x hx
    all_goals exact hpow _ (by simp)
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈prims) (hn : xs.length≤8) : xs.prod≤V^8 :=
    list_prod_budget xs prims V hV hprims hx hn
  have hp1 (x : ℝ) (hx : x∈prims) : x≤V^8 := by
    simpa using hp [x] (by simpa using hx) (by simp)
  intro x hx
  simp only [poissonUnitBudget,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨by positivity, ?_⟩
    apply ((IdealDivisorBound.ideal_divisor_small_power η hη).choose_spec.2 G hG).trans
    have hh := hp [divisorConstant η hη,(Ideal.absNorm G:ℝ)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength K+1:ℕ) ≤ (2+1/(η*Real.log 2))*K^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη K hK).trans
    have hh := hp [2+1/(η*Real.log 2),K^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength N+1:ℕ) ≤ (2+1/(η*Real.log 2))*N^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη N hN).trans
    have hh := hp [2+1/(η*Real.log 2),N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [256,supportConstant η hη,divisorConstant η hη,N^η,N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [divisorExponentConstant hexp η hη,((2*K)*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖quadraticTransformedSquareProfile W 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨dualMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [dualMiddleDecayConstant (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨originalMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [originalMiddleDecayConstant (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨nonzeroLatticeEnvelopeConstant_nonneg, ?_⟩
    have hh := hp [nonzeroLatticeEnvelopeConstant] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,(N*N)^η,CD,sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,((Ideal.absNorm G:ℝ)*(N*N))^η,CS,sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [CT,sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,N^η,CP,(K*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh

end

section

theorem selectedPoisson_upper (C C1 M X η : ℝ)
    (hC : 4≤C) (hCC : C≤C1) (hM : 1≤M) (hX : 1≤X)
    (hη : 0≤η) (hη1 : η≤1) :
    4≤ selectedPoissonT C M X η ∧
    (M*X)^η≤ selectedPoissonT C M X η ∧
    selectedPoissonK C M X η≤C1*(M*X)^3 := by
  have hC10 : 0≤C1 := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hP0 : 0<M*X := by positivity
  have hR : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 4≤ selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  refine ⟨hT,by dsimp [selectedPoissonT]; nlinarith,?_⟩
  have hXP : X≤M*X := by nlinarith
  have hfrac : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg _) hM).trans (pow_le_pow_left₀ hX0.le hXP 2)
  have hrpow : (M*X)^η≤M*X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hη1
  calc
    selectedPoissonK C M X η = C*(M*X)^η*(X^2/M) := by
      unfold selectedPoissonK selectedPoissonT
      ring
    _ ≤ C1*(M*X)*(M*X)^2 := by gcongr
    _ = C1*(M*X)^3 := by ring

theorem poisson_seven_scale_bounds (g K N P B C1 : ℝ)
    (hP : 1≤P) (hB : 1≤B) (hC1 : 1≤C1)
    (hg0 : 0≤g) (hK0 : 0≤K) (hN0 : 0≤N)
    (hg : g≤B*P) (hK : K≤C1*P^3) (hN : N≤P) :
    ∀x∈([g,K,N,(2*K)*N,N*N,g*(N*N),K*N] : List ℝ),
      0≤x ∧ x≤(2*C1+B)*P^4 := by
  have hP0 : 0≤P := by linarith
  have hD : 1≤2*C1+B := by linarith
  have hp14 : P≤P^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (show 1≤4 by omega)
  have hp24 : P^2≤P^4 := pow_le_pow_right₀ hP (by omega)
  have hp34 : P^3≤P^4 := pow_le_pow_right₀ hP (by omega)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨hg0, hg.trans ?_⟩
    calc
      B*P ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hK0,hK.trans ?_⟩
    calc
      C1*P^3 ≤ C1*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hN0,hN.trans (hp14.trans ?_)⟩
    nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      2*K*N ≤ 2*(C1*P^3)*P := by gcongr
      _ = (2*C1)*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      N*N ≤ P*P := by gcongr
      _ = P^2 := by ring
      _ ≤ P^4 := hp24
      _ ≤ (2*C1+B)*P^4 := by nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      g*(N*N) ≤ (B*P)*(P*P) := by gcongr
      _ = B*P^3 := by ring
      _ ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      K*N ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith

theorem power_cutoff_dominates (P T η : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l) :
    P^4≤T^l := by
  have hp0 : 0<P := by linarith
  calc
    P^4 = P^(4:ℝ) := by rw [Real.rpow_ofNat]
    _ ≤ P^(η*l) := Real.rpow_le_rpow_of_exponent_le hP hpow
    _ = (P^η)^l := by rw [Real.rpow_mul hp0.le,Real.rpow_natCast]
    _ ≤ T^l := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hT l

theorem poisson_truncation_small (P T η K M N C1 : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l)
    (_hK : 0≤K) (hM : 0≤M) (hN : 0≤N) (hC1 : 0≤C1)
    (hKP : K≤C1*P^3) (hMP : M≤P) (hNP : N≤P) :
    K*M/T^l≤C1 ∧ K*N/T^l≤C1 := by
  have hp0 : 0<P := by linarith
  have htpos : 0<T := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hT
  have hcut := power_cutoff_dominates P T η l hP hT hpow
  have hb (Y : ℝ) (hY : 0≤Y) (hYP : Y≤P) : K*Y/T^l≤C1 := by
    apply (div_le_iff₀ (pow_pos htpos _)).mpr
    calc
      K*Y ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ C1*T^l := by gcongr
  exact ⟨hb M hM hMP,hb N hN hNP⟩

theorem poisson_tail_abstract (B P t K η M : ℝ) (A : ℕ)
    (hB : 1≤B) (hP : 1≤P) (hM : 0≤M)
    (ht : 1/(B*P^2)≤t) (hu : P^η≤1+t*K) (hA : 4≤η*A) :
    M/((min 1 t)^2*(1+t*K)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hP0 : 0<P := by linarith
  have hBP : 1≤B*P^2 := by nlinarith [sq_nonneg (P-1)]
  have hinv : 1/(B*P^2)≤1 := (div_le_one (by positivity)).mpr hBP
  have htlo : 1/(B*P^2)≤ min 1 t := le_min hinv ht
  have htpos : 0< min 1 t := lt_of_lt_of_le (by positivity) htlo
  have hup : 0<1+t*K := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hu
  have hpow := power_cutoff_dominates P (1+t*K) η A hP hu hA
  have hprod : 1/B^2≤(min 1 t)^2*(1+t*K)^A := by
    calc
      1/B^2 = (1/(B*P^2))^2*P^4 := by field_simp
      _ ≤ (min 1 t)^2*(1+t*K)^A := by gcongr
  apply (div_le_iff₀ (by positivity : 0<(min 1 t)^2*(1+t*K)^A)).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (show 0≤B^2*M by positivity)
  have he : (B^2*M)*(1/B^2)=M := by field_simp
  rw [he] at hh
  exact hh

theorem selectedPoisson_tail_shape (C B M X q η : ℝ) (A : ℕ)
    (hC : B≤C) (hB : 1≤B) (hM : 1≤M) (hX : 1≤X)
    (hq : 1≤q) (_hη : 0≤η) (hA : 4≤η*A) :
    M/((min 1 (M/((B*q)*(X/q)*(X/q))))^2*
      (1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hq0 : 0<q := by linarith
  have hC0 : 0<C := by linarith
  have hP : 1≤M*X := by nlinarith
  have hXP : X≤M*X := by nlinarith
  have hMQ : 1≤M*q := by nlinarith
  have hEq : M/((B*q)*(X/q)*(X/q))=M*q/(B*X^2) := by field_simp
  have ht : 1/(B*(M*X)^2)≤M/((B*q)*(X/q)*(X/q)) := by
    rw [hEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      1*(B*X^2) ≤ B*(M*X)^2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0.le hXP 2) hB0.le
      _ ≤ (M*q)*(B*(M*X)^2) := by nlinarith [show 0≤B*(M*X)^2 by positivity]
  have hu : (M*X)^η≤1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η := by
    rw [selectedPoisson_radial_identity C B M X q η hM0 hX0 hq0 hB0]
    have hp : 0≤(M*X)^η := Real.rpow_nonneg (by positivity) _
    have hb : (M*X)^η≤ selectedPoissonT C M X η*q/B := by
      apply (le_div_iff₀ hB0).mpr
      dsimp [selectedPoissonT]
      calc
        (M*X)^η*B = B*(M*X)^η := by ring
        _ ≤ C*(M*X)^η := mul_le_mul_of_nonneg_right hC hp
        _ ≤ C*(M*X)^η*q := le_mul_of_one_le_right (by positivity) hq
    linarith
  exact poisson_tail_abstract B (M*X) _ _ η M A hB hP hM0.le ht hu hA

theorem selectedPoisson_principal_shape (C M X N η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hN : 0≤N) (hNX : N≤X)
    (hη : 0≤η) (hα : 1/2≤α) :
    Real.sqrt (M/selectedPoissonK C M X η)*N+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
    M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 1≤ selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have hfrac : M/selectedPoissonK C M X η≤(M/X)^2 := by
    apply (div_le_iff₀ hK0).mpr
    have he : (M/X)^2*selectedPoissonK C M X η=M*selectedPoissonT C M X η := by
      unfold selectedPoissonK
      field_simp
    rw [he]
    nlinarith
  have hsqrt : Real.sqrt (M/selectedPoissonK C M X η)≤M/X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,hfrac⟩
  have hfirst : Real.sqrt (M/selectedPoissonK C M X η)*N≤M := by
    calc
      _ ≤ (M/X)*X := by gcongr
      _ = M := by field_simp
  have hsecond : Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
      selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
    calc
      _ ≤ Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
        gcongr ; linarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hT
          (show 0≤Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) by positivity)
        nlinarith
  exact add_le_add hfirst hsecond

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonShape (M X α : ℝ) : ℝ := M+X+X^(2*α-1)*M^(1-α)
def poissonShapeConstant (B C1 : ℝ) : ℝ := 2+4*C1^3+B^2+C1

theorem poisson_envelope_identity (H C P η Z : ℝ) (hP : 0<P) :
    262144*((H*P^(4*η))^8)^8*(C*P^(3*η)*Z) =
      (262144*H^64*C)*P^(259*η)*Z := by
  have hp : (P^(4*η))^64*P^(3*η)=P^(259*η) := by
    calc
      _ = P^((4*η)*64)*P^(3*η) := by rw [Real.rpow_mul hP.le (4*η) 64,Real.rpow_ofNat]
      _ = P^((4*η)*64+3*η) := (Real.rpow_add hP _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (262144*H^64*C)*((P^(4*η))^64*P^(3*η))*Z := by ring
    _ = _ := by rw [hp]

theorem poissonComparisonMajorant_selected_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (η : ℝ) (hη : 0<η) (hη1 : η≤1) (l A : ℕ)
    (hl : 4≤η*l) (hA : 4≤η*A)
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    (B C1 : ℝ) (hB : 1≤B) (hC1 : 1≤C1) (W : 𝓢(ℝ,ℂ)) :
    ∃ Cfinal : ℝ, 0<Cfinal ∧
      ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
        1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
        1≤ selectedPoissonK C M X η →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
        (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
        (fun _ : Unit => (1:ℂ)) W ≤
        Cfinal*(M*X)^(259*η)*poissonShape M X α := by
  let D := 2*C1+B
  have hD : 1≤D := by dsimp [D]; linarith only [hC1,hB]
  obtain ⟨H,hH,hconst⟩ := list_exists_positive_bound
    (poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W)
  let Cshape := poissonShapeConstant B C1
  have hC10 : 0≤C1 := le_trans zero_le_one hC1
  have hCs : 1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3,sq_nonneg B]
  have hCsC : C1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [pow_nonneg hC10 3,sq_nonneg B]
  have hCsB : B^2≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3]
  have hCsMid : 1+4*C1^3≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,sq_nonneg B]
  refine ⟨262144*H^64*Cshape,by positivity,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  have hM0 : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hP : 1≤M*X := by nlinarith only [hM,hX]
  have hP0 : 0<M*X := by positivity
  have hMP : M≤M*X := by nlinarith only [hM,hX]
  have hXP : X≤M*X := by nlinarith only [hM,hX]
  have hN : 1≤X/q := (le_div_iff₀ hq0).mpr (by simpa using hqX)
  have hNX : X/q≤X := div_le_self hX0.le hq
  have hNP : X/q≤M*X := hNX.trans hXP
  obtain ⟨hT,hTP,hKP⟩ := selectedPoisson_upper C C1 M X η hC hCC hM hX hη.le hη1
  have hKg : 0≤ selectedPoissonK C M X η := le_trans zero_le_one hK
  have hg : (Ideal.absNorm G:ℝ)≤B*(M*X) := by rw [hGN]; gcongr; exact hqX.trans hXP
  have hb := poissonUnitBudget_power_envelope sD sS sT CD CS CT CP hCD hCS hCT hCP
    hexp η hη G hG (selectedPoissonK C M X η) (X/q) (M*X) D H W
    hK hN hP hD hH hconst
    (poisson_seven_scale_bounds (Ideal.absNorm G:ℝ) (selectedPoissonK C M X η) (X/q)
      (M*X) B C1 hP hB hC1 (Nat.cast_nonneg _) hKg (by positivity) hg hKP hNP)
  let R := (M*X)^(3*η)
  have hR : 1≤R := Real.one_le_rpow hP (by positivity)
  let Z := X^(2*α-1)*M^(1-α)
  have hZ : 0≤Z := by dsimp [Z]; positivity
  let S := Cshape*R*poissonShape M X α
  have hshape : 1≤poissonShape M X α := by
    change 1≤M+X+Z
    linarith only [hM,hX,hZ]
  have hshape0 : 0≤poissonShape M X α := le_trans zero_le_one hshape
  have hMshape : M≤poissonShape M X α := by
    change M≤M+X+Z
    linarith only [hX,hZ]
  have hXshape : X≤poissonShape M X α := by
    change X≤M+X+Z
    linarith only [hM,hZ]
  have hZshape : Z≤poissonShape M X α := by
    change Z≤M+X+Z
    linarith only [hM,hX]
  have hRshape : 1≤R*poissonShape M X α := by nlinarith only [hR,hshape]
  have hshapeS : poissonShape M X α≤S := by
    calc
      poissonShape M X α ≤ R*poissonShape M X α := le_mul_of_one_le_left hshape0 hR
      _ ≤ Cshape*(R*poissonShape M X α) :=
        le_mul_of_one_le_left (mul_nonneg (by linarith only [hR]) hshape0) hCs
      _ = S := by dsimp [S]; ring
  have hMS : M≤S := hMshape.trans hshapeS
  have hNS : X/q≤S := hNX.trans (hXshape.trans hshapeS)
  have hMiddle : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C1^3*R*poissonShape M X α := by
    apply (selectedPoisson_middle_bound C M X η α hC hM hX hη.le hα2).trans
    change 4*C^3*R*Z≤4*C1^3*R*poissonShape M X α
    gcongr
  have hmidS : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)≤S :=
    hMiddle.trans (by dsimp [S]; gcongr; linarith only [hCsMid])
  have hprS : Real.sqrt (M/selectedPoissonK C M X η)*(X/q)+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)≤S := by
    apply (selectedPoisson_principal_shape C M X (X/q) η α hC hM hX (by positivity) hNX hη.le hα).trans
    calc
      M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)
          ≤ poissonShape M X α+4*C1^3*R*poissonShape M X α := add_le_add hMshape hMiddle
      _ ≤ R*poissonShape M X α+4*C1^3*R*poissonShape M X α :=
        add_le_add (le_mul_of_one_le_left hshape0 hR) (le_refl _)
      _ = (1+4*C1^3)*R*poissonShape M X α := by ring
      _ ≤ S := by dsimp [S]; gcongr
  obtain ⟨hED,hES⟩ := poisson_truncation_small (M*X) (selectedPoissonT C M X η) η
    (selectedPoissonK C M X η) M (X/q) C1 l hP hTP hl hKg hM0.le (by positivity) hC10 hKP hMP hNP
  have hC1S : C1≤S := by
    calc
      C1 ≤ Cshape := hCsC
      _ ≤ Cshape*(R*poissonShape M X α) := le_mul_of_one_le_right (by positivity) hRshape
      _ = S := by dsimp [S]; ring
  have htailS : M/((min 1 (M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q))))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤S := by
    rw [hGN]
    apply (selectedPoisson_tail_shape C B M X q η A hBC hB hM hX hq hη.le hA).trans
    calc
      B^2*M ≤ B^2*(R*poissonShape M X α) := by
        gcongr
        exact hMshape.trans (le_mul_of_one_le_left hshape0 hR)
      _ ≤ Cshape*(R*poissonShape M X α) := by gcongr
      _ = S := by dsimp [S]; ring
  have hV : 1≤H*(M*X)^(4*η) := by
    have hh := Real.one_le_rpow hP (show 0≤4*η by positivity)
    nlinarith only [hH,hh]
  have hU : 1≤(H*(M*X)^(4*η))^8 := one_le_pow₀ hV
  apply (poissonComparisonMajorant_unit_box sD sS sT CD CS CT CP l A hexp η hη η hη G
    (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
    ((H*(M*X)^(4*η))^8) S W hKg (by positivity) hM0.le (by linarith only [hT]) hU (by dsimp [S]; positivity)
    hb hMS hNS hmidS hprS (hED.trans hC1S) (hES.trans hC1S) htailS).trans_eq
  exact poisson_envelope_identity H Cshape (M*X) η (poissonShape M X α) hP0

end CanonicalQuadraticSieve

end

end OAI

end

