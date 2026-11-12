module

public import Green64.Library.Analysis.NumberTheory.DirichletL.QuadraticSieve.Part008

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.PooledRows -/

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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

def GlobalFirstAdmissible (b : GlobalFirstData ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor ⊆ b.common∪b.cube.support

variable (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstIndex (side : Bool) (b : GlobalFirstData ι) : GlobalLogIndex :=
  globalScaleIndex p side (b.append ⟨∅,∅,∅,1⟩)

def globalFirstPooledRow (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalPooledRowScale K ell B F (globalFirstIndex p side b)

def globalFirstCoefficient (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalBinFirstCoefficient K ell B F (globalFirstIndex p side b)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalPooledRowScale_first (K ell B F : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    globalPooledRowScale K ell B F (globalScaleIndex p side x)=
      globalFirstPooledRow p K ell B F side x.first := by
  have hc (i : Fin 10) (hi : i=1 ∨ i=4 ∨ i=5 ∨ i=9) :
      globalLogRep (globalScaleIndex p side x) i=globalLogRep (globalFirstIndex p side x.first) i := by
    rcases hi with rfl|rfl|rfl|rfl <;>
      simp [globalLogRep,globalFirstIndex,globalScaleIndex,globalScaleVector,GlobalFirstData.append,GlobalSecondData.first,globalCubeJNorm,globalCubeActiveRoot]
  unfold globalFirstPooledRow globalPooledRowScale
  rw [hc 1 (by simp),hc 4 (by simp),hc 5 (by simp)]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalBinFirstCoefficient_first (K ell B F : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    globalBinFirstCoefficient K ell B F (globalScaleIndex p side x)=
      globalFirstCoefficient p K ell B F side x.first := by
  have hc (i : Fin 10) (hi : i=5 ∨ i=9) :
      globalLogRep (globalScaleIndex p side x) i=globalLogRep (globalFirstIndex p side x.first) i := by
    rcases hi with rfl|rfl <;>
      simp [globalLogRep,globalFirstIndex,globalScaleIndex,globalScaleVector,GlobalFirstData.append,GlobalSecondData.first,globalCubeJNorm,globalCubeActiveRoot]
  unfold globalFirstCoefficient globalBinFirstCoefficient
  rw [hc 5 (by simp),hc 9 (by simp)]

def globalFirstConcreteCutoff (K ell B F M H : ℝ) (side : Bool) (b : GlobalFirstData ι) :
    Finset ι → Finset ι → Finset O :=
  firstCoreSecondCutoff p b.firstCommon (globalFirstBlockColumnScale p ell side b)
    (globalFirstPooledRow p K ell B F side b) M H

def globalFirstSupportedPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) : Finset (GlobalSecondData ι) :=
  (globalFirstExpansionPool pool s cutoff).filter (fun x =>
    SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstSupportedPool_admissible (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s cutoff ell M side) : GlobalSecondAdmissible x := by
  have hm := (mem_globalFirstExpansionPool pool s cutoff x).mp (Finset.mem_filter.mp hx).1
  have hb := hs x.first hm.1
  have hE := ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.1
  exact ⟨hb.1,hE,hb.2.1,hb.2.2⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstSupportedPool_frequency_ne_zero (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side) :
    x.source.frequency ≠ 0 := by
  have hm := (mem_globalFirstExpansionPool pool s _ x).mp (Finset.mem_filter.mp hx).1
  exact (Finset.mem_erase.mp ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.2.2).1

include hp in

theorem globalFirstSupportedPool_index_mem_box
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (K ell B F M H : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H)
    (side : Bool)
    (hb₁ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s
      (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side) :
    globalScaleIndex p side x ∈ globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) := by
  have hm := (mem_globalFirstExpansionPool pool s _ x).mp (Finset.mem_filter.mp hx).1
  have hk := (Finset.mem_erase.mp ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.2.2)
  apply globalScaleIndex_mem_uniform_box p hp K ell B F M H hK hell hB hF hH side x
    (globalFirstSupportedPool_admissible p pool s hs _ ell M side x hx)
    (Finset.mem_filter.mp hx).2 (hb₁ x.first hm.1) (hb₂ x.first hm.1) hk.1
  simpa only [globalFirstConcreteCutoff,globalPooledRowScale_first,globalFirstBlockColumnScale,
    globalFirstColumnScale,GlobalSecondData.first] using hk.2

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem globalSecondLiteralTerm_zero_of_not_support
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (g W : 𝓢(ℝ,ℂ)) (ell Y M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hell : 0<ell) (hgM : ∀ t,g t ≠ 0 → |t|≤M) (hE : x.source.divisor⊆x.source.sourceCommon)
    (hs : ¬SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source) :
    globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell Y side x=0 := by
  have hX := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon)
  have hz := secondExpansionSource_singleton_zero_of_not_support p hp hcop hg hinj
    (globalSecondRawPool pool x) Ψ (m*globalFirstBlockBadLabel p x.first)
    (globalFirstBlockLabel p x.first) (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    ray g W (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) Y M hX hgM x.source hE hs
  unfold globalSecondLiteralTerm
  dsimp only
  simp only [globalFirstBlockBadLabel,globalFirstBlockLabel,GlobalSecondData.first] at hz
  rw [hz,mul_zero]

theorem globalFirstTruncatedSource_eq_supported
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell M : ℝ) (hell : 0<ell)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      ∑ ray : SecondRayIndex,∑ x∈globalFirstSupportedPool p pool s cutoff ell M side,
        w x.first*globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell (Y x.first) side x := by
  rw [globalFirstTruncatedSource_eq_literal p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro ray hray
  unfold globalFirstSupportedPool
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs,globalSecondLiteralTerm_zero_of_not_support p hp hcop hg hinj pool Ψ m ray g W ell (Y x.first) M side x hell hgM]
    · ring
    · exact ((mem_secondExpansionPool _ _ _).mp ((mem_globalFirstExpansionPool pool s cutoff x).mp hx).2).2.1
    · exact hs

theorem globalFirstTruncatedSource_eq_bins
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (K ell B F M H : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool)
    (hb₁ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    globalFirstTruncatedSource p hp hg hinj pool s
      (fun b => w b*globalFirstCoefficient p K ell B F side b) cutoff Ψ m g W ell side
      (globalFirstPooledRow p K ell B F side) =
      ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinFirstCoefficient K ell B F j : ℂ)*
          globalSecondLiteralBinSource p hp hcop hg (fun x => w x.first) source side j pool Ψ m
            g g W ell (globalPooledRowScale K ell B F j) := by
  dsimp only
  rw [globalFirstTruncatedSource_eq_supported p hp hcop hg hinj hc hpr]
  · let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    have hmap : ∀ x∈source,globalScaleIndex p side x∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) :=
      fun x hx => globalFirstSupportedPool_index_mem_box p hp pool s hs K ell B F M H hK hell hB hF hH side hb₁ hb₂ x hx
    change (∑ ray : SecondRayIndex,∑ x∈source,
      (w x.first*globalFirstCoefficient p K ell B F side x.first)*
        globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell
          (globalFirstPooledRow p K ell B F side x.first) side x) = _
    simp only [globalSecondLiteralBinSource,Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ray hray
    have hsplit := Finset.sum_fiberwise_of_maps_to hmap
      (fun x => (w x.first*globalFirstCoefficient p K ell B F side x.first)*
        globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell
          (globalFirstPooledRow p K ell B F side x.first) side x)
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro x hx
    have hxj := (Finset.mem_filter.mp hx).2
    have hy := globalPooledRowScale_first p K ell B F side x
    have hc' := globalBinFirstCoefficient_first p K ell B F side x
    rw [hxj] at hy hc'
    rw [← hy,← hc']
    ring
  · exact hell
  · exact hgM

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (frequencyTwist)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalChildBudget (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε θ₁ θ₂ K ell B F M H : ℝ) (A J : ℕ) (side : Bool) : ℝ :=
  ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
    ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p source side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))

end

theorem globalFirstTruncatedSource_actual_transfer
    (ε : ℝ) (hε : 0<ε) (g W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0≤C ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℂ) (Γ θ K ell B F H : ℝ) (side : Bool)
      (Ψ : O →* ℂ) (m : O),
      0≤Γ → (∀ b∈s,‖w b‖≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
      let source := globalFirstSupportedPool p pool s cutoff ell M side
      ‖globalFirstTruncatedSource p hp hg hinj pool s
        (fun b => w b*globalFirstCoefficient p K ell B F side b) cutoff Ψ m
        (frequencyTwist g θ) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
      globalChildBudget p hp hcop hg pool source Ψ m windows (Γ*C) ε θ θ K ell B F M H A J side := by
  obtain ⟨windows,C,hC,hwc,hws,hwb,htrans⟩ := globalSecondLiteralBinSource_transfer ε hε g g W M hM hgM hgM A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ θ K ell B F H side Ψ m hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂
  dsimp only
  let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
  let source := globalFirstSupportedPool p pool s cutoff ell M side
  have htw : ∀ t,frequencyTwist g θ t ≠ 0 → |t|≤M := by
    intro t ht
    apply hgM t
    intro hz
    exact ht (by simp [JointLogSeparation.frequencyTwist_apply,hz])
  rw [globalFirstTruncatedSource_eq_bins p hp hcop hg hinj hc hpr pool s hs w Ψ m
    (frequencyTwist g θ) W K ell B F M H hK hell hB hF hH htw side hb₁ hb₂]
  apply (norm_sum_le _ _).trans
  unfold globalChildBudget
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j)]
  apply htrans p hp hcop hg hinj hc hpr θ θ K ell B F source side j pool Ψ m
    (fun x => w x.first) Γ hK hell hB hF hΓ
  · intro x hx
    exact hw x.first ((mem_globalFirstExpansionPool pool s cutoff x).mp (Finset.mem_filter.mp hx).1).1
  · exact hΨ
  · exact fun x hx => globalFirstSupportedPool_admissible p pool s hs cutoff ell M side x hx
  · exact fun x hx => globalFirstSupportedPool_frequency_ne_zero p pool s
      (globalFirstConcreteCutoff p K ell B F M H side) ell M side x hx

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstCoreRows_actual_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0≤C ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let cutoff := globalFirstConcreteCutoff p K ell B F M H side
      let source := globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      let profile := firstCoreModeProfile g V side t
      (∑ b∈s,weight b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
        globalFirstCoreCorrection p g V ell side t b)) ≤
      globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side +
      ‖globalFirstSourceZero p hg pool s (fun b => weight b) cutoff Ψmode m profile rowMajorant ell side
        (globalFirstPooledRow p K ell B F side)‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => weight b) cutoff Ψmode m profile rowMajorant ell side
        (globalFirstPooledRow p K ell B F side)‖ := by
  have hbase : ∀ x,firstCoreBaseProfile g V side x≠0 → |x|≤M := by
    intro x hx
    apply hgM x
    intro hz
    exact hx (by rw [firstCoreBaseProfile_apply,hz,zero_mul])
  obtain ⟨windows,C,hC,hwc,hws,hwb,htrans⟩ := globalFirstTruncatedSource_actual_transfer
    ε hε (firstCoreBaseProfile g V side) rowMajorant M hM hbase A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ K ell B F H Ψ m χ r t T hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
  dsimp only
  let cutoff := globalFirstConcreteCutoff p K ell B F M H side
  let source := globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  let Ψmode := firstCoreTwist side χ Ψ r
  have hweight : ∀ b∈s,0≤weight b := by
    intro b hb
    exact mul_nonneg (hw b hb).1 (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hY : ∀ b∈s,0<globalFirstPooledRow p K ell B F side b := by
    intro b hb
    exact globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hsource := htrans p hp hcop hg hinj hc hpr pool s (fun b => (w b : ℂ)) Γ
    (firstCoreModeHeight side t) K ell B F H side Ψmode m hΓ
    (fun b hb => by rw [Complex.norm_real,Real.norm_of_nonneg (hw b hb).1]; exact (hw b hb).2)
    hK hell hB hF hH hs (fun a => (firstCoreTwist_norm_le side χ Ψ r a).trans (hΨ a)) hb₁ hb₂
  have hfinite := globalFirstCoreRows_finite_le_sources p hp hg hinj hc pool s weight hweight cutoff Ψ m g V ell hell
    side χ r t (globalFirstPooledRow p K ell B F side) hY T hT hT0
  have hheight : ‖firstCoreModeHeight side t‖=‖t‖ := by cases side <;> simp [firstCoreModeHeight]
  have hbudget : globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε
      (firstCoreModeHeight side t) (firstCoreModeHeight side t) K ell B F M H A J side =
      globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side := by
    simp only [globalChildBudget,globalDescentWeight,hheight]
  dsimp only at hsource
  change _ ≤ globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε
    (firstCoreModeHeight side t) (firstCoreModeHeight side t) K ell B F M H A J side at hsource
  rw [hbudget] at hsource
  apply hfinite.trans
  apply add_le_add
  · apply add_le_add
    · simpa only [weight,firstCoreModeProfile,Complex.ofReal_mul] using hsource
    · exact le_rfl
  · exact le_rfl

end SecondPassArithmetic

open scoped BigOperators Classical
namespace InitialMeanSquare

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

structure Datum where
  divisor : Ideal O
  shared : Ideal O
  frequency : O
  deriving DecidableEq

def newRow (x : Datum) : O := idealGenerator x.divisor*x.frequency
def newLabel (x : Datum) : Ideal O := x.divisor*x.shared
def oldCommon (b : Ideal O) (x : Datum) : Ideal O := b*x.divisor
def observation (x : Datum) : O × Ideal O := (newRow x,newLabel x)

theorem span_newRow (x : Datum) :
    Ideal.span {newRow x}=x.divisor*Ideal.span {x.frequency} := by
  rw [newRow,←Ideal.span_singleton_mul_span_singleton,span_idealGenerator]

theorem divisor_dvd_row (x : Datum) : x.divisor∣Ideal.span {newRow x} := by
  rw [span_newRow]
  exact dvd_mul_right _ _

theorem divisor_dvd_label (x : Datum) : x.divisor∣newLabel x := dvd_mul_right _ _

theorem divisor_ne_zero_of_row (x : Datum) (hx : newRow x≠0) : x.divisor≠0 := by
  intro hd
  have hs : Ideal.span {newRow x}=(0 : Ideal O) := by rw [span_newRow,hd,zero_mul]
  exact hx (Ideal.span_singleton_eq_bot.mp hs)

theorem divisor_injective_on_fiber (y : O) (f : Ideal O) (hy : y≠0) :
    Set.InjOn Datum.divisor {x : Datum | observation x=(y,f)} := by
  intro x hx z hz hd
  have hxrow : newRow x=y := congrArg Prod.fst hx
  have hzrow : newRow z=y := congrArg Prod.fst hz
  have hxlabel : newLabel x=f := congrArg Prod.snd hx
  have hzlabel : newLabel z=f := congrArg Prod.snd hz
  have hdx := divisor_ne_zero_of_row x (by rwa [hxrow])
  have hshared : x.shared=z.shared := by
    apply mul_left_cancel₀ hdx
    calc
      x.divisor*x.shared = f := hxlabel
      _ = z.divisor*z.shared := hzlabel.symm
      _ = x.divisor*z.shared := by rw [hd]
  have hfreq : x.frequency=z.frequency := by
    apply mul_left_cancel₀ (idealGenerator_ne_zero x.divisor hdx)
    calc
      idealGenerator x.divisor*x.frequency = y := hxrow
      _ = idealGenerator z.divisor*z.frequency := hzrow.symm
      _ = idealGenerator x.divisor*z.frequency := by rw [hd]
  cases x
  cases z
  simp_all

theorem fiber_card_le (s : Finset Datum) (y : O) (f : Ideal O) (hy : y≠0) :
    (s.filter (fun x => observation x=(y,f))).card≤(idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  apply Finset.card_le_card_of_injOn Datum.divisor
  · intro x hx
    change x.divisor∈idealDivisors (Ideal.span {y})
    rw [mem_idealDivisors hyI]
    have he : newRow x=y := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    rw [←he]
    exact divisor_dvd_row x
  · intro x hx z hz he
    exact divisor_injective_on_fiber y f hy (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2 he

theorem fiber_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (y : O) (f : Ideal O), y≠0 →
      ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
        C*(Ideal.absNorm (Ideal.span {y}):ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s y f hy
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  exact (show ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
    (idealDivisors (Ideal.span {y})).card by exact_mod_cast fiber_card_le s y f hy).trans (hdiv _ hyI)

theorem weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (t : Finset (O×Ideal O))
      (w : Datum→ℂ) (P : O×Ideal O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,observation x∈t) →
      (∀y∈t,y.1≠0) → (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (observation x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hfiber⟩ := fiber_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s t w P A K hA hK hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t observation w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hc := (hfiber s y.1 y.2 (ht y hy)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hA) (sq_nonneg ‖P y‖)
  simpa only [Prod.eta,mul_assoc] using hh

theorem norm_newRow (x : Datum) :
    Ideal.absNorm (Ideal.span {newRow x})=Ideal.absNorm x.divisor*Ideal.absNorm (Ideal.span {x.frequency}) := by
  rw [span_newRow,map_mul]

theorem norm_newLabel (x : Datum) :
    Ideal.absNorm (newLabel x)=Ideal.absNorm x.divisor*Ideal.absNorm x.shared := by
  rw [newLabel,map_mul]

theorem norm_oldCommon (b : Ideal O) (x : Datum) :
    Ideal.absNorm (oldCommon b x)=Ideal.absNorm b*Ideal.absNorm x.divisor := by
  rw [oldCommon,map_mul]

end

theorem label_and_mask (b : Ideal O) (x : Datum)
    (hC : Squarefree (oldCommon b x)) (hs : Squarefree x.shared)
    (hcop : IsCoprime (oldCommon b x) x.shared) :
    Squarefree (newLabel x) ∧ IsCoprime b (newLabel x) := by
  have hC' : Squarefree (b*x.divisor) := hC
  have hcop' : IsCoprime (b*x.divisor) x.shared := hcop
  have hds : IsCoprime x.divisor x.shared :=
    hcop'.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
  have hbs : IsCoprime b x.shared :=
    hcop'.of_isCoprime_of_dvd_left (dvd_mul_right _ _)
  have hbd : IsCoprime b x.divisor := by
    apply Ideal.isCoprime_iff_gcd.mpr
    have hh := (IsRelPrime.of_squarefree_mul hC')
      (GCDMonoid.gcd_dvd_left b x.divisor) (GCDMonoid.gcd_dvd_right b x.divisor)
    simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp hh
  exact ⟨squarefree_mul_iff.mpr ⟨hds.isRelPrime,hC'.of_mul_right,hs⟩,hbd.mul_right hbs⟩

def columnScale (Z B F : ℝ) : ℝ := Z/(B*F)
def rowScale (Z H B : ℝ) : ℝ := Z^2/(H*B^2)

theorem initial_prefactor (Z H b d : ℝ) (hd : d≠0) :
    H*(b*d)/(Z^2*d)=H*b/Z^2 := by field_simp

theorem initial_column_scale (Z b d s : ℝ) :
    Z/((b*d)*s)=columnScale Z b (d*s) := by unfold columnScale; ring

theorem initial_row_bound (Z H b d h : ℝ) (hH : 0<H) (hb : 0<b) (hd : 0<d)
    (hh : h≤Z^2*d/(H*(b*d)^2)) : d*h≤ rowScale Z H b := by
  have h := mul_le_mul_of_nonneg_left hh hd.le
  have he : d*(Z^2*d/(H*(b*d)^2))=rowScale Z H b := by
    unfold rowScale
    field_simp

  exact h.trans_eq he

theorem initial_mass (Z B F : ℝ) (hF : F≠0) : columnScale Z B F*F=Z/B := by
  unfold columnScale
  field_simp

theorem initial_invariant_identity (Z H B F R : ℝ)
    (hZ : Z≠0) (hB : B≠0) (hF : F≠0) :
    rowScale Z H B*R/(columnScale Z B F*F)=(Z/H)*(R/B) := by
  unfold rowScale columnScale
  field_simp

theorem initial_invariant_bound (Z H B F R c : ℝ)
    (hZ : 0<Z) (hH : 0<H) (hB : 0<B) (hF : 0<F) (hR : R≤ c*B) :
    rowScale Z H B*R/(columnScale Z B F*F)≤ c*(Z/H) := by
  rw [initial_invariant_identity Z H B F R hZ.ne' hB.ne' hF.ne']
  have hh : R/B≤ c := (div_le_iff₀ hB).mpr hR
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (div_nonneg hZ.le hH.le)

theorem initial_invariant_power_general (Z B F R c σ : ℝ)
    (hZ : 0<Z) (hB : 0<B) (hF : 0<F) (hR : R≤ c*B) :
    rowScale Z (Z^(1+σ)) B*R/(columnScale Z B F*F)≤ c*Z^(-σ) := by
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    calc
      _ = Z^((1:ℝ)-(1+σ)) := by rw [Real.rpow_sub hZ,Real.rpow_one]
      _ = _ := by congr 1; ring
  simpa only [he] using initial_invariant_bound Z (Z^(1+σ)) B F R c
    hZ (Real.rpow_pos_of_pos hZ _) hB hF hR

theorem initial_invariant_power (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤ c*B) :
    rowScale Z (Z^((11:ℝ)/10)) B*R/(columnScale Z B F*F)≤ c*Z^(-(1:ℝ)/10) := by
  have hZ0 : 0<Z := by linarith
  have he : Z/(Z^((11:ℝ)/10))=Z^(-(1:ℝ)/10) := by
    calc
      _ = Z^((1:ℝ)-(11:ℝ)/10) := by rw [Real.rpow_sub hZ0,Real.rpow_one]
      _ = _ := by norm_num
  simpa only [he] using initial_invariant_bound Z (Z^((11:ℝ)/10)) B F R c
    hZ0 (Real.rpow_pos_of_pos hZ0 _) hB hF hR

theorem initial_invariant_reserved_margin (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤ c*B) (hc : c≤Z^((1:ℝ)/20)) :
    rowScale Z (Z^((11:ℝ)/10)) B*R≤
      columnScale Z B F*F*Z^(-(1:ℝ)/20) := by
  have hZ0 : 0<Z := by linarith
  have hmass : 0<columnScale Z B F*F := by unfold columnScale; positivity
  rw [mul_comm (columnScale Z B F*F)]
  apply (div_le_iff₀ hmass).mp
  apply (initial_invariant_power Z B F R c hZ hB hF hR).trans
  calc
    c*Z^(-(1:ℝ)/10) ≤ Z^((1:ℝ)/20)*Z^(-(1:ℝ)/10) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hZ0.le _)
    _ = Z^(-(1:ℝ)/20) := by rw [←Real.rpow_add hZ0]; norm_num

theorem initial_budget_identity (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) :
    (H*B/Z^2)*B*(Z/B)*(Z/B)=H := by field_simp

end InitialMeanSquare

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss -/

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
namespace CanonicalQuadraticSieve

theorem lifting_annular_scale_bounds (j : Fin 7) : 1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤64 := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  have hj : j.val≤6 := by omega
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj
  norm_num at hh
  exact hh

theorem HasSieveExponent.lifted_annular_selected {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤ selectedPoissonK fixedCutoffBase M N η →
      ∀ (j : Fin 7) (q : ℝ), 1≤q → q≤7 →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N (N/q) a →
      annularHighEnergy ((2:ℝ)^j.val*M) N (selectedPoissonK fixedCutoffBase M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hc0 : 0<fixedCutoffBase := lt_of_lt_of_le (by norm_num) fixedCutoffBase_bounds.1
  obtain ⟨C,hC,hann⟩ := hexp.annular_selected_bound hα1 hα2 η hη hη1 l A hl hA
    (21952*fixedCutoffBase) (by linarith [fixedCutoffBase_bounds.1])
  refine ⟨C*64^(260*η)*64,by positivity,?_⟩
  intro M N hM hN hthreshold hK j q hq hq7 a ha
  let r : ℝ := (2:ℝ)^j.val
  have hr := lifting_annular_scale_bounds j
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hq0 : 0<q := by linarith
  have hr0 : 0< r := by dsimp [r]; positivity
  have hNq : 4≤N/q := (le_div_iff₀ hq0).mpr (by nlinarith)
  have hNqN : N/q≤N := div_le_self hN0.le hq
  have hβ : 0≤2-1/α := by
    have hfrac : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα1
    linarith
  have hth : (N/q)^(2-1/α)≤ r*M := by
    calc
      _ ≤ N^(2-1/α) := Real.rpow_le_rpow (by positivity) hNqN hβ
      _ ≤ M := hthreshold
      _ ≤ r*M := by nlinarith [hr.1]
  let c := cutoffRescaleCoefficient fixedCutoffBase η r q
  have hc := cutoffRescaleCoefficient_bounds fixedCutoffBase η r q hc0.le hη.le hη1 hr.1 hr.2 hq hq7
  have hk := selectedPoissonK_rescale fixedCutoffBase M N η r q hM0 hN0 hr0 hq0
  have hh := hann c (r*M) (N/q) hc.1 hc.2 (by nlinarith [hr.1]) hNq hth
    (by simpa only [c,hk] using hK) (coefficientAtScale N (N/q) a)
    (coefficientAtScale_shell N (N/q) a ha)
  dsimp only [c] at hh
  rw [hk,←annularHighEnergy_coefficientAtScale (r*M) N (N/q)
    (selectedPoissonK fixedCutoffBase M N η) a (fun J hJ => (ha J hJ).2),
    ←coefficientAtScale_energy N (N/q) a (fun J hJ => (ha J hJ).2)] at hh
  have hp : ((r*M)*(N/q))^(260*η)≤64^(260*η)*(M*N)^(260*η) := by
    calc
      _ ≤ (64*(M*N))^(260*η) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        calc
          (r*M)*(N/q) ≤ (64*M)*N := by gcongr; exact hr.2
          _ = _ := by ring
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  change annularHighEnergy (r*M) N _ a≤_
  apply hh.trans
  calc
    _ ≤ C*(64^(260*η)*(M*N)^(260*η))*(64*M)*∑J,‖a J‖^2 := by
      gcongr
      exact hr.2
    _ = _ := by ring

theorem HasSieveExponent.ball_selected_high {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤ selectedPoissonK fixedCutoffBase M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      ballQuadraticEnergy M N a ≤
        (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+
          C*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
  obtain ⟨C,hC,hann⟩ := hexp.lifted_annular_selected hα1 hα2 η hη hη1 l A hl hA
  refine ⟨14*C,by positivity,?_⟩
  intro M N hM hN hthreshold hK a ha
  have hf (j : Fin 7) := hann M N hM hN hthreshold hK j 1 (by norm_num) (by norm_num)
    (liftingFreeCoefficient N a) (by simpa only [div_one] using liftingFreeCoefficient_shell N N a ha)
  have hd (j : Fin 7) := hann M N hM hN hthreshold hK j 7 (by norm_num) (by norm_num)
    (liftingDividedCoefficient N a) (liftingDividedCoefficient_shell N N a ha)
  have hsf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hf j)
  have hsd := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hd j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsf hsd
  have he := liftingCoefficient_energy N a
  have hb := ballQuadraticEnergy_lifted_annuli M N (selectedPoissonK fixedCutoffBase M N η)
    (by linarith) a
  calc
    _ ≤ sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
      2*(7*(C*(M*N)^(260*η)*M*∑J,‖liftingFreeCoefficient N a J‖^2)+
        7*(C*(M*N)^(260*η)*M*∑J,‖liftingDividedCoefficient N a J‖^2)) := by linarith
    _ = _ := by
      calc
        _ = sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
          (14*C)*(M*N)^(260*η)*M*((∑J,‖liftingFreeCoefficient N a J‖^2)+
            (∑J,‖liftingDividedCoefficient N a J‖^2)) := by ring
        _ = _ := by rw [he]; ring

theorem HasSieveExponent.low_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (c : ℝ) (hc : 4≤ c) :
    ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N → N^(2-1/α)≤M → M≤N^2 →
      sieveNorm (selectedPoissonK c M N η) N≤C*(M*N)^(6*η)*M := by
  obtain ⟨C,hC,hrev⟩ := hexp.reverse η hη
  have hc0 : 0<c := by linarith
  refine ⟨C*c^η*(1+c^α),by positivity,?_⟩
  intro M N hM hN hthreshold hupper
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hNM := improved_threshold_ge_column α N M hα hN hthreshold
  have hNP : N≤M*N := by nlinarith
  have hK := (selectedPoisson_bounds c M N η hc hM hN hupper hη.le).2.1
  have hKP := (selectedPoisson_upper c c M N η hc le_rfl hM hN hη.le hη1).2.2
  have hprod : selectedPoissonK c M N η*N≤ c*(M*N)^4 := by
    calc
      _ ≤ (c*(M*N)^3)*(M*N) := by gcongr
      _ = _ := by ring
  have hsmall : (selectedPoissonK c M N η*N)^η≤ c^η*(M*N)^(4*η) := by
    calc
      _ ≤ (c*(M*N)^4)^η := Real.rpow_le_rpow (by positivity) hprod hη.le
      _ = _ := by
        rw [Real.mul_rpow hc0.le (by positivity)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
  have hmain : (selectedPoissonK c M N η)^α≤ c^α*(M*N)^(2*η)*M := by
    apply (improved_threshold_low α c η N M (by linarith) hc0 hN0 hM0 hthreshold).trans
    have hp : (M*N)^(η*α)≤(M*N)^(2*η) := Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hc0.le _))
      hNM hN0.le (by positivity)
  have hR : 1≤(M*N)^(2*η) := Real.one_le_rpow hP (by positivity)
  have hsum : N+(selectedPoissonK c M N η)^α≤(1+c^α)*(M*N)^(2*η)*M := by
    calc
      _ ≤ M+c^α*(M*N)^(2*η)*M := add_le_add hNM hmain
      _ ≤ (M*N)^(2*η)*M+c^α*(M*N)^(2*η)*M := by
        exact add_le_add (le_mul_of_one_le_left hM0.le hR) le_rfl
      _ = _ := by ring
  have hpowers : (M*N)^(4*η)*(M*N)^(2*η)=(M*N)^(6*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  calc
    _ ≤ C*(selectedPoissonK c M N η*N)^η*(N+(selectedPoissonK c M N η)^α) := hrev _ _ hK hN
    _ ≤ C*(c^η*(M*N)^(4*η))*((1+c^α)*(M*N)^(2*η)*M) := by gcongr
    _ = C*c^η*(1+c^α)*((M*N)^(4*η)*(M*N)^(2*η))*M := by ring
    _ = _ := by rw [hpowers]

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

theorem globalCutoffRatio_le (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M≤U^8 := by
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hden : 1≤B^2*F^2 := by nlinarith [sq_nonneg (B-1),sq_nonneg (F-1)]
  have he : H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M =
      (H*K*ell^2*(Real.exp M)^4)/(B^2*F^2) := by
    unfold globalRowScaleFloor
    field_simp

  rw [he]
  calc
    _ ≤ H*K*ell^2*(Real.exp M)^4 := div_le_self (by positivity) hden
    _ ≤ U*U*U^2*U^4 := by gcongr
    _ = U^8 := by ring

theorem globalNormCaps_polynomial (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ∀i, 0<globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i ∧
      globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i≤27*U^22 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hratio := globalCutoffRatio_le K ell B F M H U hU hK hell hB hF hH hKU hellU hHU heU
  have hY := globalRowScaleFloor_pos K ell B F M hK hell hB0 hF0
  have hratio0 : 0≤H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M := by positivity
  have hceil : (⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1≤U^8+2 := by
    have hh := Nat.ceil_lt_add_one hratio0
    linarith
  have hpow8 : 1≤U^8 := one_le_pow₀ hU
  have hceil' : (⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1≤3*U^8 := by linarith
  have hrow : 3*(ell*Real.exp M)^2*B^2*
      ((⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1)^2≤27*U^22 := by
    calc
      _ ≤ 3*(U^2)^2*U^2*(3*U^8)^2 := by gcongr
      _ = 27*U^22 := by ring
  have hpow2 : U^2≤27*U^22 := by
    calc
      U^2 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hpow4 : U^4≤27*U^22 := by
    calc
      U^4 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hB2 : B^2≤27*U^22 := (pow_le_pow_left₀ hB0.le hBU 2).trans hpow2
  have hLB : (ell*Real.exp M)*B^2≤27*U^22 := by
    calc
      _ ≤ U^2*U^2 := by gcongr
      _ = U^4 := by ring
      _ ≤ _ := hpow4
  intro i
  fin_cases i <;> dsimp [globalNormCaps]
  all_goals constructor
  all_goals first | positivity | exact hL.trans hpow2 | exact hB2 | exact hLB | exact hrow

theorem normLogBin_le_log_upper (x Y : ℝ) (hx : 0<x) (hxy : x≤Y) (hY : 1≤Y) :
    (normLogBin x:ℝ)≤Real.log Y := by
  have hh : (normLogBin x:ℝ)≤normLogBin Y := by exact_mod_cast normLogBin_mono hx hxy
  exact hh.trans (Nat.floor_le (Real.log_nonneg hY))

theorem globalLogBox_card_le_log (caps : Fin 10 → ℝ) (Y : ℝ) (hY : 1≤Y)
    (hcaps : ∀i,0<caps i ∧ caps i≤Y) :
    ((globalLogBox caps).card:ℝ)≤(1+Real.log Y)^10 := by
  calc
    ((globalLogBox caps).card:ℝ) = ∏i : Fin 10,((normLogBin (caps i):ℝ)+1) := by
      rw [globalLogBox_card]
      push_cast
      rfl
    _ ≤ ∏_i : Fin 10,(1+Real.log Y) := by
      apply Finset.prod_le_prod₀ (by intro i _; positivity)
      intro i _
      linarith [normLogBin_le_log_upper (caps i) Y (hcaps i).1 (hcaps i).2 hY]
    _ = (1+Real.log Y)^10 := by simp

theorem globalLogBox_card_polynomial_log (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤
      (1+Real.log 27+22*Real.log U)^10 := by
  have hU0 : 0<U := by linarith
  have hY : 1≤27*U^22 := by nlinarith [one_le_pow₀ hU (n:=22)]
  have hh := globalLogBox_card_le_log _ (27*U^22) hY
    (globalNormCaps_polynomial K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU)
  have he : 1+Real.log (27*U^22)=1+Real.log 27+22*Real.log U := by
    rw [Real.log_mul (by norm_num : (27:ℝ)≠0) (pow_ne_zero 22 hU0.ne'),Real.log_pow]
    norm_num
    ring
  rwa [he] at hh

theorem globalLogRep_le_upper (caps : Fin 10 → ℝ) (j : GlobalLogIndex)
    (hj : j∈globalLogBox caps) (i : Fin 10) (Y : ℝ)
    (hc : 0<caps i) (hcap : caps i≤Y) (hY : 1≤Y) : globalLogRep j i≤Y := by
  have hji : j i≤normLogBin (caps i) := by
    have hh := Fintype.mem_piFinset.mp hj i
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hjY := hji.trans (normLogBin_mono hc hcap)
  have hr : globalLogRep j i≤normLogScale (normLogBin Y) := by
    unfold globalLogRep normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast hjY
  exact hr.trans (normLogBin_scale_bounds Y hY).1

theorem globalBinLossScale_cancel (B : ℝ) (j : GlobalLogIndex) :
    globalBinLossScale B j = Real.exp 5*globalLogRep j 1*globalLogRep j 6*
      globalLogRep j 7*B*Real.sqrt (globalLogRep j 9) := by
  have hj := (globalLogRep_pos j 4).ne'
  have he : Real.exp 5=Real.exp 4*Real.exp 1 := by rw [←Real.exp_add]; norm_num
  rw [he]
  unfold globalBinLossScale globalPooledLabelScale
  field_simp

theorem globalBinLossScale_polynomial (ell B Y M H U : ℝ)
    (hU : 1≤U) (hell : 0<ell) (hB : 1≤B)
    (hellU : ell≤U) (hBU : B≤U) (heU : Real.exp M≤U)
    (j : GlobalLogIndex) (hj : j∈globalLogBox (globalNormCaps ell B Y M H)) :
    globalBinLossScale B j≤Real.exp 5*U^8 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hL0 : 0<ell*Real.exp M := by positivity
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hpow2 : 1≤U^2 := one_le_pow₀ hU
  have h1 : globalLogRep j 1≤U^2 := globalLogRep_le_upper _ j hj 1 (U^2) hL0 hL hpow2
  have h6 : globalLogRep j 6≤U^2 := globalLogRep_le_upper _ j hj 6 (U^2) hL0 hL hpow2
  have h7 : globalLogRep j 7≤U^2 := globalLogRep_le_upper _ j hj 7 (U^2) hL0 hL hpow2
  have h9 : globalLogRep j 9≤U^2 := globalLogRep_le_upper _ j hj 9 (U^2) (by simp [globalNormCaps]; positivity)
    (by simpa [globalNormCaps] using pow_le_pow_left₀ hB0.le hBU 2) hpow2
  have hsqrt : Real.sqrt (globalLogRep j 9)≤U := Real.sqrt_le_iff.mpr ⟨hU0.le,h9⟩
  rw [globalBinLossScale_cancel]
  calc
    _ ≤ Real.exp 5*U^2*U^2*U^2*U*U := by
      gcongr
      all_goals exact (globalLogRep_pos j _).le
    _ = Real.exp 5*U^8 := by ring

end SecondPassArithmetic

namespace CanonicalQuadraticSieve

theorem sieveNorm_small_columns (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hN28 : N≤28) :
    sieveNorm M N≤785*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤28 := by
    exact_mod_cast (Nat.ceil_le.mpr hN28 : ⌈N⌉₊≤28)
  have hs : (⌈N⌉₊:ℝ)^2≤784 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) ⌈N⌉₊]
  have hc := QuadraticInitialBound.initialSieveConstant_pos
  have hb := sieveNorm_initial M N hM hN
  have ht : M+(⌈N⌉₊:ℝ)^2≤785*M := by linarith
  calc
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M+(⌈N⌉₊:ℝ)^2) := hb
    _ ≤ QuadraticInitialBound.initialSieveConstant*(785*M) := mul_le_mul_of_nonneg_left ht hc.le
    _ = _ := by ring

theorem HasSieveExponent.shell_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) :
    ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^(2-1/α)≤M →
      ∀a : idealRange N → ℂ, CoefficientOnShell N N a →
      ballQuadraticEnergy M N a≤C*(M*N)^ρ*M*∑J,‖a J‖^2 := by
  intro ρ hρ
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : η≤ρ/600 := min_le_right _ _
  have h6 : 6*η≤ρ := by linarith only [hηρ,hη]
  have h260 : 260*η≤ρ := by linarith only [hηρ,hη]
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith only [hh]
  obtain ⟨CH,hCH,hhigh⟩ := hexp.ball_selected_high hα1 hα2 η hη hη1 l l horder horder
  obtain ⟨CL,hCL,hlow⟩ := hexp.low_threshold hα1 hα2 η hη hη1 fixedCutoffBase fixedCutoffBase_bounds.1
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  let C := 790*I+CL+CH
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M N hM hN hthreshold a ha
  have hP : 1≤M*N := by nlinarith only [hM,hN]
  have hPρ : 1≤(M*N)^ρ := Real.one_le_rpow hP hρ.le
  have hE : 0≤∑J,‖a J‖^2 := by positivity
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hscale {x y : ℝ} (hxy : x≤y) :
      x*M*∑J,‖a J‖^2 ≤ y*M*∑J,‖a J‖^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxy hM0) hE
  have hmatrix : ballQuadraticEnergy M N a≤ sieveNorm M N*∑J,‖a J‖^2 :=
    FiniteSieveOperator.energy_bound (matrix M N) a
  by_cases hlarge : N^2≤M
  · have hb := sieveNorm_large_rows M N hM hN hlarge
    calc
      _ ≤ (5*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (5*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 5*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  by_cases hsmall : N≤28
  · have hb := sieveNorm_small_columns M N hM hN hsmall
    calc
      _ ≤ (785*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (785*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 785*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  have hupper : M≤N^2 := le_of_not_ge hlarge
  have hK := (selectedPoisson_bounds fixedCutoffBase M N η fixedCutoffBase_bounds.1 hM hN hupper hη.le).2.1
  have hb := hhigh M N hM (by linarith only [hsmall]) hthreshold hK a ha
  have hlb := hlow M N hM hN hthreshold hupper
  have hp6 : (M*N)^(6*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h6
  have hp260 : (M*N)^(260*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h260
  calc
    _ ≤ (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := hb
    _ ≤ (CL*(M*N)^(6*η)*M+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add hlb le_rfl) hE
    _ ≤ (CL*(M*N)^ρ*M+CH*(M*N)^ρ*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 hCL.le) hM0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp260 hCH.le) hM0)) hE
    _ = (CL+CH)*(M*N)^ρ*M*∑J,‖a J‖^2 := by ring
    _ ≤ _ := hscale (mul_le_mul_of_nonneg_right
      (show CL+CH≤C by dsimp [C]; linarith only [hI])
      (Real.rpow_nonneg (by positivity) _))

theorem HasSieveExponent.improve {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) : HasSieveExponent (2-1/α) := by
  have hα : 0<α := by linarith
  have hfrac : 1/α≤1 := (div_le_one hα).mpr hα1
  have hpos : 0≤1/α := by positivity
  apply hasSieveExponent_of_shell_threshold (2-1/α) (by linarith) (by linarith)
  exact hexp.shell_threshold hα1 hα2

open ActualEisensteinCubic CompletedGauss

theorem hasSieveExponent_one : HasSieveExponent 1 :=
  hasSieveExponent_one_of_improvement (fun _α hα hα2 h => h.improve hα.le hα2)

theorem sieveNorm_sharp :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N →
      sieveNorm M N≤C*(M*N)^ε*(M+N) := by
  simpa only [HasSieveExponent,Real.rpow_one] using hasSieveExponent_one

theorem finite_family_quadratic_large_sieve :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ (M N : ℝ), 1≤M → 1≤N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → Ideal O) (cols : n → Ideal O),
      Function.Injective rows → Function.Injective cols →
      (∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i):ℝ)≤M) →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i))*a j‖^2) ≤
        C*(M*N)^ε*(M+N)*∑j,‖a j‖^2 := by
  intro ε hε
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  classical
  have he := FiniteSieveOperator.energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) a
  have hn := family_squared_norm_le rows cols hr hc M N hrows hcols
  have hE : 0≤∑j,‖a j‖^2 := by positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hn hE).trans
    (mul_le_mul_of_nonneg_right (hsharp M N hM hN) hE))

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

theorem globalLogFactor_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ U : ℝ, 1≤U →
      (1+Real.log 27+22*Real.log U)^10≤C*U^ε := by
  let deltaLoss := ε/10
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let C0 := 1+Real.log 27+22/deltaLoss
  have hlog : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hC0 : 0<C0 := by dsimp [C0]; positivity
  refine ⟨C0^10,by positivity,?_⟩
  intro U hU
  have hU0 : 0<U := by linarith
  have hR : 1≤U^deltaLoss := Real.one_le_rpow hU hδ.le
  have hb : Real.log U≤U^deltaLoss/deltaLoss := Real.log_le_rpow_div hU0.le hδ
  have hs : 1+Real.log 27+22*Real.log U≤C0*U^deltaLoss := by
    calc
      _ ≤ (1+Real.log 27)*U^deltaLoss+22*(U^deltaLoss/deltaLoss) := add_le_add
        (le_mul_of_one_le_right (by linarith) hR)
        (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = C0*U^deltaLoss := by dsimp [C0]; ring
  have hs0 : 0≤1+Real.log 27+22*Real.log U := by
    have hu := Real.log_nonneg hU
    positivity
  calc
    _ ≤ (C0*U^deltaLoss)^10 := pow_le_pow_left₀ hs0 hs 10
    _ = C0^10*U^ε := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
      dsimp [deltaLoss]
      congr 1
      ring

theorem globalLogBox_card_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  exact (globalLogBox_card_polynomial_log K ell B F M H U hU hK hell hB hF hH
    hKU hellU hBU hHU heU).trans (hbound U hU)

theorem globalLogBox_total_loss (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      (∑j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinLossScale B j)^η)≤C*U^(ε+8*η) := by
  obtain ⟨C,hC,hcard⟩ := globalLogBox_card_small_power ε hε
  refine ⟨C*(Real.exp 5)^η,by positivity,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  have hU0 : 0<U := by linarith
  let S := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  have hbound (j : GlobalLogIndex) (hj : j∈S) :
      (globalBinLossScale B j)^η≤(Real.exp 5)^η*U^(8*η) := by
    have hb := globalBinLossScale_polynomial ell B (globalRowScaleFloor K ell B F M) M H U
      hU hell hB hellU hBU heU j hj
    have hnonneg : 0≤globalBinLossScale B j := by
      rw [globalBinLossScale_cancel]
      have h1 := (globalLogRep_pos j 1).le
      have h6 := (globalLogRep_pos j 6).le
      have h7 := (globalLogRep_pos j 7).le
      positivity
    apply (Real.rpow_le_rpow hnonneg hb hη).trans_eq
    rw [Real.mul_rpow (Real.exp_pos _).le (by positivity)]
    congr 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
    norm_num
  calc
    _ ≤ ∑_j∈S,((Real.exp 5)^η*U^(8*η)) := Finset.sum_le_sum hbound
    _ = (S.card:ℝ)*((Real.exp 5)^η*U^(8*η)) := by simp
    _ ≤ (C*U^ε)*((Real.exp 5)^η*U^(8*η)) :=
      mul_le_mul_of_nonneg_right (hcard K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) (by positivity)
    _ = (C*(Real.exp 5)^η)*U^(ε+8*η) := by rw [Real.rpow_add hU0]; ring

theorem globalBinLossScale_nonneg (B : ℝ) (hB : 0≤B) (j : GlobalLogIndex) :
    0≤globalBinLossScale B j := by
  rw [globalBinLossScale_cancel]
  have h1 := (globalLogRep_pos j 1).le
  have h6 := (globalLogRep_pos j 6).le
  have h7 := (globalLogRep_pos j 7).le
  positivity

theorem globalLogBox_radial_decay (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U Z θ : ℝ, ∀ N : ℕ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        (globalBinLossScale B j)^η/
          (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) ≤
        C*U^(ε+8*η)/Z^(θ*N) := by
  obtain ⟨C,hC,hall⟩ := globalLogBox_total_loss ε hε η hη
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U Z θ N hU hK hell hB hF hH hKU hellU hBU hHU heU hZ
  let box := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let radial := fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j
  have hbase : 0<Z^θ := Real.rpow_pos_of_pos hZ _
  have hden : 0<Z^(θ*N) := Real.rpow_pos_of_pos hZ _
  have hnum (j : GlobalLogIndex) : 0≤(globalBinLossScale B j)^η :=
    Real.rpow_nonneg (globalBinLossScale_nonneg B (by linarith) j) _
  have hp (j : GlobalLogIndex) (hj : Z^θ≤ radial j) :
      Z^(θ*N)≤(1+radial j)^N := by
    rw [Real.rpow_mul hZ.le,Real.rpow_natCast]
    exact pow_le_pow_left₀ hbase.le (by linarith) N
  calc
    _ ≤ ∑j∈box.filter (fun j => Z^θ≤ radial j), (globalBinLossScale B j)^η/Z^(θ*N) := by
      apply Finset.sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_left (hnum j) hden (hp j (Finset.mem_filter.mp hj).2)
    _ = (∑j∈box.filter (fun j => Z^θ≤ radial j),(globalBinLossScale B j)^η)/Z^(θ*N) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (∑j∈box,(globalBinLossScale B j)^η)/Z^(θ*N) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hnum j)
    _ ≤ C*U^(ε+8*η)/Z^(θ*N) := div_le_div_of_nonneg_right
      (hall K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hden.le

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns -/

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
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open MixedCrossSeparation (columnCoefficient)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def inputColumn (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*H S

def transformedColumn (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S*Ψ (∏i∈S,p i)*
    rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d)*
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h*H S

omit [DecidableEq ι] in
lemma inputColumn_eq (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) :
    inputColumn p Ψ b d H S=secondInputCoefficient p hg Ψ (b*d) 1 1 H S := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simp only [inputColumn,secondInputCoefficient,hr,one_pow,mul_one]

lemma transformedColumn_eq (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    transformedColumn p hp hcop hg Ψ b d h H S=
      secondPreColumn p hp hcop hg Ψ (b*d) 1 1 d h H S := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simp only [transformedColumn,secondPreColumn,hr,one_pow,mul_one]

theorem transformedColumn_union (hpr : ∀i,lambda^2∣p i-1)
    (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    transformedColumn p hp hcop hg Ψ b d h H (V∪N)=
      transformedColumn p hp hcop hg Ψ b d h (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
        (fun U => H (V∪U)) N := by
  simp_rw [transformedColumn_eq p hp hcop hg]
  simpa only [mul_one,one_mul] using secondPreColumn_union p hp hcop hg hpr
    Ψ b 1 1 1 d h H V N hVN

def initialPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) : ℂ :=
  ∑S∈F.powerset,∑T∈F.powerset,if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S*inputColumn p Ψ₁ b d H₁ S)*
      (supportMobius (fun i => Ideal.span {p i}) T*inputColumn p Ψ₂ b d H₂ T)*
      activeGaussRowFactor p hp hinj hg T S d h else 0

lemma initialPair_eq (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      secondActualPair p hp hg hinj F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂ := by
  simp only [initialPair,secondActualPair,inputColumn_eq p hg,mul_one]

def childSum (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) : ℂ :=
  ∑N∈F.powerset,secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
    (fun U => H (V∪U)) N

lemma childSum_eq (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) :
    childSum p hp hcop hg F V Ψ b d h H=
      secondChildSum p hp hcop hg F V Ψ b 1 1 1 d h H := by
  rw [secondChildSum_fixed_pool]
  simp only [childSum,mul_one,one_mul]

theorem initialPair_eq_children (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      ∑z : SecondRayIndex,∑V∈F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ b 1 1 1 d h (z,V)*
        star (childSum p hp hcop hg F V (secondRayMinus Ψ₁ z) b d h H₁)*
        childSum p hp hcop hg F V (secondRayPlus Ψ₂ z) b d (-h) H₂ := by
  simp_rw [initialPair_eq p hp hg,childSum_eq p hp hcop hg]
  exact secondActualPair_eq_children p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂

end InitialMeanSquare

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

instance fullSLContinuousAction : ContinuousConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨continuous_hyperbolic_action⟩

instance hyperbolicVolume_fullSupport : Measure.IsOpenPosMeasure hyperbolicVolume where
  open_pos U hU hne := by
    obtain ⟨u,hu⟩ := hne
    have hcover : (Set.univ : Set HyperbolicSpace) ⊆ ⋃g:SL(2,ℂ),g • U := by
      intro w hw
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,ℂ)) u w
      exact Set.mem_iUnion.mpr ⟨g,u,hu,hg⟩
    obtain ⟨seq,hseq⟩ := isLindelof_univ.indexed_countable_subcover
      (fun g : SL(2,ℂ) => g • U) (fun g => isOpenMap_smul g U hU) hcover
    intro hzero
    have hz : hyperbolicVolume (⋃n:ℕ,seq n • U)=0 := by
      apply measure_iUnion_null
      intro n
      rw [measure_smul,hzero]
    have htotal : hyperbolicVolume Set.univ=0 := measure_mono_null hseq hz
    exact hyperbolicVolume_ne_zero (Measure.measure_univ_eq_zero.mp htotal)

instance kernelQuotientVolume_fullSupport :
    Measure.IsOpenPosMeasure (integralQuotientVolume globalKubotaKernel) where
  open_pos U hU hne := by
    let quotientProjection := integralOrbitProjection globalKubotaKernel
    have hp : Measurable quotientProjection := measurable_integralOrbitProjection _
    have hpre : IsOpen (quotientProjection ⁻¹' U) := hU.preimage (continuous_integralOrbitProjection _)
    have hpren : (quotientProjection ⁻¹' U).Nonempty := by
      obtain ⟨q,hq⟩ := hne
      obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
      exact ⟨w,hq⟩
    intro hzero
    have hd : hyperbolicVolume ((quotientProjection ⁻¹' U)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
      simpa only [integralQuotientVolume,quotientProjection,Measure.map_apply (measurable_integralOrbitProjection _) hU.measurableSet,
        Measure.restrict_apply ((measurable_integralOrbitProjection _) hU.measurableSet)] using hzero
    have hinv : ∀M:globalKubotaKernel,M • (quotientProjection ⁻¹' U)=quotientProjection ⁻¹' U := by
      intro M
      ext w
      constructor
      · rintro ⟨u,hu,rfl⟩
        change quotientProjection (M • u)∈U
        change quotientProjection u∈U at hu
        rwa [show quotientProjection (M • u)=quotientProjection u from integralOrbitProjection_eq _ M u]
      · intro hw
        refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
        change quotientProjection (M⁻¹ • w)∈U
        rwa [show quotientProjection (M⁻¹ • w)=quotientProjection w from integralOrbitProjection_eq _ M⁻¹ w]
    have hz := globalKubotaKernel_isFundamentalDomain.measure_zero_of_invariant (quotientProjection ⁻¹' U) hinv hd
    exact hpre.measure_ne_zero _ hpren hz

lemma kernel_continuous_eq_of_ae_eq (f g : IntegralOrbitQuotient globalKubotaKernel → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (he : f =ᵐ[integralQuotientVolume globalKubotaKernel] g) : f=g :=
  (MeasureTheory.Measure.eq_of_ae_eq he hf hg)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_height (M : SL(2,O)) (hc : M 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix M • upperPoint z v hv)=v := by
  have hdet : M 0 0*M 1 1=1 := by
    have h := M.property
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using h
  let u : Oˣ := ⟨M 1 1,M 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (M 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hyperbolicHeight_action_upperPoint]
  simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
    hn,one_pow,]
  norm_num

lemma smoothCuspSeedDefect_high_zero (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ)
    (M : SL(2,O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hvlarge : max b a⁻¹<v) :
    smoothCuspSeedDefect a b s (integralComplexMatrix M • upperPoint z v hv)=0 := by
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  have hz : (fun r : CuspCosets => cuspCutoffTerm 1 (cuspSeedDefectProfile a b s) r
      (integralComplexMatrix M • upperPoint z v hv))=(fun _ => (0:ℂ)) := by
    funext r
    have hout : cosetHeight r (integralComplexMatrix M • upperPoint z v hv)<a ∨
        b<cosetHeight r (integralComplexMatrix M • upperPoint z v hv) := by
      induction r using Quotient.inductionOn with
      | _ N =>
        change cosetHeight (cosetOf N) _<a ∨ b<cosetHeight (cosetOf N) _
        rw [cosetHeight_cosetOf]
        change hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
          (integralComplexMatrix M • upperPoint z v hv))<a ∨
          b<hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
            (integralComplexMatrix M • upperPoint z v hv))
        simp only [←mul_smul,←map_mul]
        by_cases hc : ((N:SL(2,O))*M) 1 0=0
        · right
          rw [integral_upper_triangular_height _ hc]
          exact (le_max_left _ _).trans_lt hvlarge
        · left
          have hh := integral_hyperbolicHeight_mul_le_one ((N:SL(2,O))*M) hc (upperPoint z v hv)
          rw [hyperbolicHeight_upperPoint] at hh
          have hav : 1<a*v := by
            have hlt : a⁻¹<v := (le_max_right _ _).trans_lt hvlarge
            have hm := mul_lt_mul_of_pos_left hlt ha
            simpa only [mul_inv_cancel₀ ha.ne'] using hm
          nlinarith
    simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
  rw [hz,tsum_zero]

theorem kernelQuotientDefect_hasCompactSupport (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    HasCompactSupport (kernelQuotientDefect a b s) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max b a⁻¹)
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max b a⁻¹) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max b a⁻¹) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (smoothCuspSeedDefect_high_zero a b ha hab s r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)

def hyperbolicSpatialCoordinates (w : HyperbolicSpace) : SpatialCoordinates :=
  ![(hyperbolicHorizontal w).re,(hyperbolicHorizontal w).im,hyperbolicHeight w]

lemma hyperbolicSpatialCoordinates_continuous : Continuous hyperbolicSpatialCoordinates := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hyperbolicHorizontal_continuous
  · exact Complex.continuous_im.comp hyperbolicHorizontal_continuous
  · exact hyperbolicHeight_continuous

lemma hyperbolicSpatialCoordinates_positive (w : HyperbolicSpace) :
    0<hyperbolicSpatialCoordinates w 2 := hyperbolicHeight_pos w

lemma hyperbolicSpatialCoordinates_reconstruct (w : HyperbolicSpace) :
    upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+(hyperbolicSpatialCoordinates w 1:ℂ)*Complex.I)
      (hyperbolicSpatialCoordinates w 2) (hyperbolicSpatialCoordinates_positive w)=w := by
  change upperPoint (((hyperbolicHorizontal w).re:ℂ)+((hyperbolicHorizontal w).im:ℂ)*Complex.I)
    (hyperbolicHeight w) (hyperbolicHeight_pos w)=w
  rw [Complex.re_add_im]
  exact upperCoordinates_right_inverse w

lemma smoothCuspSeedDefect_continuous (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (smoothCuspSeedDefect a b s) := by
  have heq : smoothCuspSeedDefect a b s=
      fun w => heightPoincareField (cuspSeedDefectProfile a b s) (hyperbolicSpatialCoordinates w) := by
    funext w
    nth_rw 1 [←hyperbolicSpatialCoordinates_reconstruct w]
    exact smoothCuspSeedDefect_coordinate a b s ha hab _ (hyperbolicSpatialCoordinates_positive w)
  rw [heq,continuous_iff_continuousAt]
  intro w
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab _
    (hyperbolicSpatialCoordinates_positive w)).continuousAt.comp
      hyperbolicSpatialCoordinates_continuous.continuousAt

lemma kernelQuotientDefect_continuous (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelQuotientDefect a b s) :=
  (smoothCuspSeedDefect_continuous a b s ha hab).quotient_lift _

lemma actual_smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (smoothCuspSeedDefectField a b s) p := by
  have heq : smoothCuspSeedDefectField a b s =ᶠ[𝓝 p]
      heightPoincareField (cuspSeedDefectProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedDefectField_eq a b s ha hab q hq
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

end CubicEisenstein

namespace SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem globalChildBudget_height (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
      ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*
        globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp only [globalChildBudget,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro q hq
  simp only [globalDescentWeight,norm_zero,add_zero,one_pow,mul_one]
  ring

theorem globalChildBudget_density (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
    firstLogDensity 0 t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  rw [globalChildBudget_height,← mul_assoc,FirstPassCubeLabels.firstLogDensity_pair_moment]

theorem globalChildBudget_integral (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side) =
    (∫ t : ℝ,firstLogDensity 0 t)*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp_rw [globalChildBudget_density]
  exact integral_mul_const _ _

def globalFirstFiniteEnergy (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (t : ℝ) : ℝ :=
  ∑ b∈s,w b*∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2

theorem globalFirstFiniteEnergy_integrable (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (J : ℕ) :
    Integrable (fun t => firstLogDensity J t*globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t) := by
  simp only [globalFirstFiniteEnergy,Finset.mul_sum]
  apply integrable_finsetSum
  intro b hb
  apply integrable_finsetSum
  intro z hz
  have hi := firstCoreInputRow_integrable p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (FirstPassCubeLabels.normalizedColumn p
      (fun A => g (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r z
    (FirstPassCubeLabels.firstLogDensity_integrable J)
  simpa only [globalFirstCoreRow,mul_left_comm] using hi.const_mul (w b)

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤256*(columnDyadicLength H+1:ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑I∈divisorDyadicBin S H j,1/(Ideal.absNorm I:ℝ))≤256 := by
    have hp : 0<(2:ℝ)^j.val := by positivity
    have hone : 1≤(2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card:ℝ)≤128*(2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I∈divisorDyadicBin S H j) :
        1/(Ideal.absNorm I:ℝ)≤2/(2:ℝ)^j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith
    calc
      _ ≤ ∑_I∈divisorDyadicBin S H j,2/(2:ℝ)^j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card:ℝ)*(2/(2:ℝ)^j.val) := by simp
      _ ≤ (128*(2:ℝ)^j.val)*(2/(2:ℝ)^j.val) := by gcongr
      _ = _ := by field_simp; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑j : Fin (columnDyadicLength H+1),(256:ℝ) := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring

theorem ideal_reciprocal_cauchy (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (v : Ideal O → ℂ) :
    ‖∑I∈S,v I‖^2≤(∑I∈S,1/(Ideal.absNorm I:ℝ))*
      (∑I∈S,(Ideal.absNorm I:ℝ)*‖v I‖^2) := by
  have hpos (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun I hI => by positivity) (fun I hI => by positivity)
  intro I hI
  exact le_of_eq (by field_simp [(hpos I hI).ne'])

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

def columnSquareFiber (S : Finset (Ideal O)) (A : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => squarePart I=A)

theorem columnSquareFiber_injective (S : Finset (Ideal O)) (A : Ideal O) :
    Function.Injective (fun I : columnSquareFiber S A => squarefreePart I.val) := by
  intro I J he
  change squarefreePart I.val=squarefreePart J.val at he
  apply Subtype.ext
  have hi := (Finset.mem_filter.mp I.property).2
  have hj := (Finset.mem_filter.mp J.property).2
  calc
    I.val = A^2*squarefreePart I.val := by simpa only [hi] using (squarePart_sq_mul_squarefreePart I.val).symm
    _ = A^2*squarefreePart J.val := by rw [he]
    _ = J.val := by simpa only [hj] using squarePart_sq_mul_squarefreePart J.val

theorem columnSquareFiber_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (I : columnSquareFiber S A) :
    Admissible (squarefreePart I.val) ∧
      (Ideal.absNorm (squarefreePart I.val):ℝ)≤X/(Ideal.absNorm A:ℝ)^2 := by
  have hi := hS I.val (Finset.mem_filter.mp I.property).1
  have hp := (supported_square_parts I.val).mp hi.1
  have ha := (Finset.mem_filter.mp I.property).2
  have hAz : A≠0 := by rw [←ha]; exact hp.1.1
  have hAn : 0<(Ideal.absNorm A:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨hp.2,(le_div_iff₀ (sq_pos_of_pos hAn)).mpr ?_⟩
  have hn : (Ideal.absNorm A:ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
    have hh : (Ideal.absNorm (squarePart I.val):ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
      exact_mod_cast norm_decomposition I.val
    simpa only [ha] using hh
  nlinarith

theorem columnSquareFiber_card (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hscale : 1≤X/(Ideal.absNorm A:ℝ)^2) :
    ((columnSquareFiber S A).card:ℝ)≤128*(X/(Ideal.absNorm A:ℝ)^2) := by
  let T := (columnSquareFiber S A).image squarefreePart
  have hcard : T.card=(columnSquareFiber S A).card := Finset.card_image_iff.mpr (by
    intro I hI J hJ he
    have hh : (⟨I,hI⟩:columnSquareFiber S A)=(⟨J,hJ⟩:columnSquareFiber S A) :=
      columnSquareFiber_injective S A he
    exact congrArg Subtype.val hh)
  rw [←hcard]
  apply DescentFiberCost.finite_ideal_count_real T _ hscale
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).1.1
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).2

theorem columnSquareFiber_energy (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑k : idealRange K, ‖∑I∈columnSquareFiber S A,
      quadraticRow k.val (primaryGenerator I)*a I‖^2) ≤
      sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K *
        ∑I∈columnSquareFiber S A,‖a I‖^2 := by
  let T := columnSquareFiber S A
  let B : Matrix T (idealRange K) ℂ := fun I k => quadraticRow k.val (primaryGenerator (squarefreePart I.val))
  have hB : ‖FiniteSieveOperator.operator B‖^2≤ sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K := by
    apply family_squared_norm_le (fun I : T => squarefreePart I.val) (fun k : idealRange K => k.val)
      (columnSquareFiber_injective S A) Subtype.val_injective
    · intro I
      exact columnSquareFiber_bounds S X hS A I
    · intro k
      exact mem_idealRange.mp k.property
  have hBT : B.conjTranspose=(fun k I => quadraticRow k.val (primaryGenerator (squarefreePart I.val))) := by
    ext k I
    exact canonical_quadraticRow_star k.val (mem_idealRange.mp k.property).1 _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun I : T => a I.val)
  rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
  have hm (k : idealRange K) :
      ‖∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val‖^2 ≤
        ‖∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val‖^2 := by
    have hrow : (∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val)=
        idealZeroMask k.val (primaryGenerator A)*
        ∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      have hi := (Finset.mem_filter.mp I.property).2
      have hq : quadraticRow k.val (primaryGenerator I.val)=
          idealZeroMask k.val (primaryGenerator A)*quadraticRow k.val (primaryGenerator (squarefreePart I.val)) := by
        have hh := canonical_quadraticRow_primary_squarefree k.val (mem_idealRange.mp k.property).1
          (squarePart I.val) (squarefreePart I.val)
        rw [squarePart_sq_mul_squarefreePart,hi] at hh
        exact hh
      rw [hq]
      ring
    rw [hrow,norm_mul,mul_pow]
    have hmask : ‖idealZeroMask k.val (primaryGenerator A)‖^2≤1 := by
      unfold idealZeroMask
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hmask
  have hr (k : idealRange K) :
      (∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val :=
    (Finset.sum_coe_sort T _).symm
  simp_rw [hr]
  rw [←Finset.sum_coe_sort T (fun I => ‖a I‖^2)]
  exact (Finset.sum_le_sum (fun k _ => hm k)).trans
    (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

theorem columnSquareParts_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hA : A∈S.image squarePart) :
    A≠0 ∧ 1≤(Ideal.absNorm A:ℝ) ∧ (Ideal.absNorm A:ℝ)≤X ∧ 1≤X/(Ideal.absNorm A:ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hp := (supported_square_parts I).mp hi.1
  have ha : 1≤(Ideal.absNorm (squarePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hp.1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hp.2.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (Ideal.absNorm (squarePart I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)=(Ideal.absNorm I:ℝ) := by
    exact_mod_cast norm_decomposition I
  refine ⟨hp.1.1,ha,by nlinarith,?_⟩
  apply (le_div_iff₀ (by positivity : 0<(Ideal.absNorm (squarePart I):ℝ)^2)).mpr
  nlinarith

theorem bounded_supported_quadratic_norm :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K X lengthScale : ℝ,
      1≤K → 1≤X → 0≤lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖≤lengthScale) →
      (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤
        C*(K*X)^ε*(K+X)*X*lengthScale^2 := by
  intro ε hε
  let deltaLoss := ε/3
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := 256*(2+1/(deltaLoss*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨128*C*D^2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image squarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0<K := by linarith
  have hX0 : 0<X := by linarith
  have hP0 : 0<K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0≤R := by dsimp [R]; positivity
  have hRL : R≤D*X^deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    nlinarith
  let F : ℝ := 128*C*(K*X)^deltaLoss*(K+X)*X*lengthScale^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : idealRange K,‖∑I∈columnSquareFiber S A,
        quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0<(Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ)^2
    have hY : 1≤Y := hp.2.2.2
    have hYX : Y≤X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K≤C*(K*X)^deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K≤K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0≤Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖^2)≤128*Y*lengthScale^2 := by
      calc
        _ ≤ ∑_I∈columnSquareFiber S A,lengthScale^2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (columnSquareFiber_card S X hS A hY) (sq_nonneg _)
    have he := columnSquareFiber_energy S X K hS A a
    calc
      _ ≤ (Ideal.absNorm A:ℝ)*(sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖^2)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ ≤ (Ideal.absNorm A:ℝ)*((C*(K*X)^deltaLoss*(K+X))*(128*Y*lengthScale^2)) := by
        gcongr
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne']
  have hsplit (k : idealRange K) :
      (∑I∈S,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarePart hI) _).symm
  have hcauchy (k : idealRange K) :
      ‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2≤
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F*R^2 := by
    calc
      _ ≤ ∑k : idealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : idealRange K,‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _ ≤ R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R^2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X)^deltaLoss*(X^deltaLoss)^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^deltaLoss*((K*X)^deltaLoss)^2 := by gcongr
      _ = (K*X)^ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _ ≤ F*(D*X^deltaLoss)^2 := by gcongr
    _ = (128*C*D^2)*((K*X)^deltaLoss*(X^deltaLoss)^2)*(K+X)*X*lengthScale^2 := by dsimp [F]; ring
    _ ≤ _ := by gcongr

end CanonicalQuadraticSieve

end

end OAI

end

