module

public import Green64.Library.Analysis.Compactness.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part012
public import Green64.Library.OAI.NumberTheory.DirichletL.CubicSieve.DyadicKernel

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part013

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.RadialWindows -/

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
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma columnLog_three_split (A C S:Finset ι) (hAC:Disjoint A C)
    (hAS:Disjoint A S) (hCS:Disjoint C S) (ell:ℝ) (hell:0<ell) :
    columnLog p ell ((A∪C)∪S)=columnLog p (ell/(primeProductNorm p A*primeProductNorm p C)) S := by
  unfold columnLog
  rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hAS,hCS⟩),
    primeProductNorm_union p A C hAC]
  congr 1
  have hA := (primeProductNorm_pos p hp A).ne'
  have hC := (primeProductNorm_pos p hp C).ne'
  field_simp

include hp in
lemma canonicalCubeResidual_log
    (b:CubeCoordinates ι) (hb:b.Admissible) (C S:Finset ι)
    (hCB:Disjoint C b.support) (hSC:Disjoint S C) (hSB:Disjoint S b.support)
    (negative:Bool) (Ψ:O→*ℂ) (m f:O) (g:𝓢(ℝ,ℂ)) (ell:ℝ) (hell:0<ell) :
    canonicalCubeResidual p hg b C negative Ψ m f (fun U=>g (columnLog p ell U)) S =
      originalLabelColumn p hg b.support b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m (fun U=>g (columnLog p
          (ell/(primeProductNorm p (b.sideDivisor (!negative))*primeProductNorm p C)) U)))
        (∏i∈C,p i) f S := by
  have hA : b.sideDivisor (!negative)⊆b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  have hlog:=columnLog_three_split p hp (b.sideDivisor (!negative)) C S
    (hCB.symm.mono_left hA) (hSB.symm.mono_left hA) hSC.symm ell hell
  unfold canonicalCubeResidual originalLabelColumn multiplicativeCoreColumn
  have hside : (if negative then b.rightDivisor else b.leftDivisor)=b.sideDivisor (!negative) := by cases negative <;> rfl
  rw [hside]
  dsimp only
  rw [hlog]

lemma actualFirstKernel_insert_windows
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (Ψ₁ Ψ₂:O→*ℂ)
    (m₁ m₂ c f:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (X₁ X₂ K:ℝ) (d h:O)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W (fun _=>1) (fun _=>1) X₁ X₂ K d h =
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W V₁ V₂ X₁ X₂ K d h := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP:Disjoint N P
  · simp only [hNP,ite_true,one_mul]
    by_cases h₁:g₁ (columnLog p X₁ N)=0
    · simp only [threeGaussRowFactor,originalLabelColumn,multiplicativeCoreColumn,h₁,mul_zero,zero_mul,star_zero]
    by_cases h₂:g₂ (columnLog p X₂ P)=0
    · simp only [threeGaussRowFactor,originalLabelColumn,multiplicativeCoreColumn,h₂,mul_zero,zero_mul]
    rw [hV₁ _ h₁,hV₂ _ h₂,one_mul,one_mul]
  · simp only [hNP,ite_false]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic

lemma conductor_zero_swap (parityBit a b:Bool) :
    conductorExponent parityBit a b=0 ↔ conductorExponent parityBit b a=0 := by
  cases parityBit <;> cases a <;> cases b <;> decide

lemma conductor_parity_swap (parityBit a b:Bool) :
    (conductorExponent parityBit a b).val%2=(conductorExponent parityBit b a).val%2 := by
  cases parityBit <;> cases a <;> cases b <;> decide

lemma dilationExponent_swap (parityBit a b:Bool) :
    dilationExponent parityBit a b=dilationExponent parityBit b a := by
  cases parityBit <;> cases a <;> cases b <;> rfl

lemma retained_swap (parityBit a b:Bool) : retained parityBit a b=retained parityBit b a := by
  cases parityBit <;> cases a <;> cases b <;> rfl

lemma b0Exponent_swap (m:ℕ) (a b:Bool) : b0Exponent m a b=b0Exponent m b a := by
  cases a <;> cases b <;> simp [b0Exponent,evenDouble]

variable {ι:Type*} (p:ι→O) (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)

lemma cubeActiveSupport_swap : cubeActiveSupport B v ε₁ ε₂=cubeActiveSupport B v ε₂ ε₁ := by
  ext i
  simp only [cubeActiveSupport,Finset.mem_filter]
  constructor
  · rintro ⟨hi,he⟩
    exact ⟨hi,fun hx=>he ((conductor_zero_swap (parity (v i)) (ε₁ i) (ε₂ i)).mpr hx)⟩
  · rintro ⟨hi,he⟩
    exact ⟨hi,fun hx=>he ((conductor_zero_swap (parity (v i)) (ε₁ i) (ε₂ i)).mp hx)⟩

lemma cubeOddSupport_swap : cubeOddSupport B v ε₁ ε₂=cubeOddSupport B v ε₂ ε₁ := by
  ext i
  simp only [cubeOddSupport,Finset.mem_filter,conductor_parity_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma dilationLabel_swap : dilationLabel p B v ε₁ ε₂=dilationLabel p B v ε₂ ε₁ := by
  unfold dilationLabel primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [dilationExponent_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma jLabel_swap : jLabel p B v ε₁ ε₂=jLabel p B v ε₂ ε₁ := by
  unfold jLabel primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [retained_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma b0Label_swap : b0Label p B v ε₁ ε₂=b0Label p B v ε₂ ε₁ := by
  unfold b0Label primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [b0Exponent_swap (v i) (ε₁ i) (ε₂ i)]
end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels

theorem firstInputFamilyEnergy_swap {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hg:∀i,lambda∉Ideal.span {p i})
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (negative:Bool)
    (Ψ:O→*ℂ) (m:O) (H:Finset ι→ℂ) (V:ℝ→ℂ) (X:ℝ) (c d:O) (J:ℕ) (T:Finset O) :
    firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T =
    firstInputFamilyEnergy p hg F B v ε₂ ε₁ negative Ψ m H V X c d J T := by
  simp only [firstInputFamilyEnergy,firstCoreOuter,firstCoreInputRow,
    cubeOddSupport_swap B v ε₁ ε₂,b0Label_swap p B v ε₁ ε₂,jLabel_swap p B v ε₁ ε₂]

namespace CubeCoordinates
variable {ι:Type*}
def swap (b:CubeCoordinates ι) : CubeCoordinates ι :=
  ⟨b.rightExponent,b.leftExponent,b.rightDivisor,b.leftDivisor⟩
@[simp] lemma swap_swap (b:CubeCoordinates ι) : b.swap.swap=b := by cases b;rfl
end CubeCoordinates
end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def orientedCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ K d x.2

end

theorem orientedCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤C*Ymax^deltaLoss := mul_nonneg hC (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hswapD := FirstPassCubeLabels.dilationLabel_swap p b.cube.support
      (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ K hK (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (by simpa only [hswapD] using hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    rw [firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit true,
      firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit false,
      FirstPassCubeLabels.cubeActiveSupport_swap b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit] at hh
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [orientedCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ globalCubeCoefficient p K ell B F true b*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,(C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = (C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = (C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ (C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem orientedTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
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
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := orientedCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F
    (globalFirstRowCap K ell B F) hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT hT0
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc hT0
  have hprefix : 0≤Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg hCfirst (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance : BorelSpace EuclideanSpatial := ⟨rfl⟩

def euclideanC1cToH1 (f : C1c (E := EuclideanSpatial)) :
    h1 (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial)) := by
  let gr := graph (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial))
  refine ⟨gr f,?_⟩
  exact (LinearMap.range gr).le_topologicalClosure ⟨f,rfl⟩

lemma euclideanC1cToH1_norm (f : C1c (E := EuclideanSpatial)) :
    ‖euclideanC1cToH1 f‖=max ‖toL2 («μ» := volume) f‖ ‖toL2Grad («μ» := volume) f‖ := rfl

lemma euclideanC1c_supported_range (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    toL2 («μ» := volume) f∈LinearMap.range
      (Lp.extendByZeroₗᵢ («μ» := (volume : Measure EuclideanSpatial)) (p := (2:ℝ≥0∞)) hK).toLinearMap := by
  have hmem := memLp_of_mem_C1c («μ» := (volume : Measure EuclideanSpatial)) f.2
  have hres : MemLp f.1 2 (volume.restrict K) := hmem.mono_measure Measure.restrict_le_self
  refine ⟨hres.toLp f.1,?_⟩
  apply Lp.ext
  have hext := Lp.extendByZeroₗᵢ_ae_eq («μ» := (volume : Measure EuclideanSpatial)) hK (hres.toLp f.1)
  have hr : ∀ᵐx ∂(volume : Measure EuclideanSpatial),x∈K→hres.toLp f.1 x=f.1 x :=
    (ae_restrict_iff' hK).mp hres.coeFn_toLp
  have hg : (toL2 («μ» := volume) f : EuclideanSpatial→ℝ)=ᵐ[volume]f.1 := hmem.coeFn_toLp
  filter_upwards [hext,hr,hg] with x hx hrx hgx
  simp only [LinearIsometry.coe_toLinearMap]
  rw [hx,hgx]
  by_cases hxm : x∈K
  · simpa only [Set.indicator_of_mem hxm] using hrx hxm
  · rw [Set.indicator_of_notMem hxm]
    symm
    by_contra hne
    exact hxm (hf hne)

def euclideanC1cToSupportedH1 (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    h1On (E := EuclideanSpatial) K hK :=
  ⟨euclideanC1cToH1 f,euclideanC1c_supported_range K hK f hf⟩

lemma compact_clm_closedBall {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W] (T : V →L[ℝ] W)
    (hT : IsCompactOperator T) (R : ℝ) : IsCompact (closure (T '' Metric.closedBall 0 R)) :=
  IsCompactOperator.isCompact_closure_image_closedBall (f := T.toLinearMap) hT R

theorem euclidean_C1c_family_precompact (K : Set EuclideanSpatial) (hK : IsCompact K)
    (family : Set (C1c (E := EuclideanSpatial))) (R : ℝ)
    (hsupp : ∀f∈family,Function.support f.1⊆K)
    (hmass : ∀f∈family,‖toL2 («μ» := volume) f‖≤R)
    (hgrad : ∀f∈family,‖toL2Grad («μ» := volume) f‖≤R) :
    IsCompact (closure (toL2 («μ» := (volume : Measure EuclideanSpatial)) '' family)) := by
  let hKm := hK.measurableSet
  have hc := compact_clm_closedBall
    (V := h1On (E := EuclideanSpatial) K hKm)
    (W := Lp ℝ 2 (volume : Measure EuclideanSpatial))
    (h1OnToL2 (E := EuclideanSpatial) K hKm)
    (isCompactOperator_h1OnToL2 (E := EuclideanSpatial) hK hKm) R
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨euclideanC1cToSupportedH1 K hKm f (hsupp f hf),?_,rfl⟩
  have hn : ‖euclideanC1cToSupportedH1 K hKm f (hsupp f hf)‖≤R :=
    max_le (hmass f hf) (hgrad f hf)
  simpa only [Metric.mem_closedBall,dist_zero_right (euclideanC1cToSupportedH1 K hKm f (hsupp f hf))] using hn

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal InnerProductSpace

namespace CubicEisenstein

abbrev KernelFundamentalVolume : Measure HyperbolicSpace :=
  hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)

abbrev KernelGradientL2 := Lp (EuclideanSpace ℂ (Fin 3)) 2 KernelFundamentalVolume

lemma kernelTestPartial_continuous (f : kernelSmoothTests) (j : Fin 3) :
    Continuous (fun w => kernelTestPartial f w j) := by
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp
      hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma kernelGradientAt_continuous (f : kernelSmoothTests) :
    Continuous (fun w => kernelGradientAt w f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
    (kernelTestPartial_continuous f j)

lemma kernelGradientAt_memLp (f : kernelSmoothTests) :
    MemLp (fun w => kernelGradientAt w f) 2 KernelFundamentalVolume := by
  apply (memLp_two_iff_integrable_sq_norm
    (kernelGradientAt_continuous f).aestronglyMeasurable).mpr
  have hh := (quotient_projection_measurePreserving globalKubotaKernel).integrable_comp_of_integrable
    (kernelQuotientEnergyDensity_integrable f)
  have he : (fun w => kernelQuotientEnergyDensity f (integralOrbitProjection globalKubotaKernel w))=
      kernelTestEnergyDensity f := rfl
  dsimp only [Function.comp_def] at hh
  rw [he] at hh
  simpa only [kernelGradientAt_norm_sq] using hh

def kernelGradientToL2 (f : kernelSmoothTests) : KernelGradientL2 :=
  (kernelGradientAt_memLp f).toLp (fun w => kernelGradientAt w f)

lemma kernelGradientToL2_coe (f : kernelSmoothTests) :
    (kernelGradientToL2 f : HyperbolicSpace → EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelGradientAt w f := (kernelGradientAt_memLp f).coeFn_toLp

lemma kernelGradientToL2_inner (f g : kernelSmoothTests) :
    inner ℂ (kernelGradientToL2 f) (kernelGradientToL2 g)=kernelDirichletForm f g := by
  rw [L2.inner_def,kernelDirichletForm,integralQuotientVolume_integral _ _
    (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f,kernelGradientToL2_coe g] with w hf hg
  rw [hf,hg,kernelDirichletPairDensity_coordinate]

lemma kernelGradientToL2_norm_sq (f : kernelSmoothTests) :
    ‖kernelGradientToL2 f‖^2=kernelDirichletEnergy f := by
  have hh := kernelGradientToL2_inner f f
  rw [inner_self_eq_norm_sq_to_K,kernelDirichletForm_self] at hh
  rw [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow] at hh
  exact Complex.ofReal_injective hh

def kernelGradientLinear : kernelSmoothTests →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelGradientToL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (f+g),kernelGradientToL2_coe f,
      kernelGradientToL2_coe g,Lp.coeFn_add (kernelGradientToL2 f) (kernelGradientToL2 g)]
      with w hfg hf hg hadd
    simp only [hfg,hadd,Pi.add_apply,hf,hg,map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (c•f),kernelGradientToL2_coe f,
      Lp.coeFn_smul c (kernelGradientToL2 f)] with w hcf hf hsmul
    simp only [RingHom.id_apply,hcf,hsmul,Pi.smul_apply,hf,map_smul]

def kernelInitialGradientGraph : Submodule ℂ (KernelQuotientL2 × KernelGradientL2) :=
  LinearMap.range (kernelSmoothTestsToL2.prod kernelGradientLinear)

lemma kernelInitialGradientGraph_unique (x : KernelQuotientL2 × KernelGradientL2)
    (hx : x∈kernelInitialGradientGraph) (hz : x.1=0) : x.2=0 := by
  obtain ⟨f,hf⟩ := hx
  have hf1 : kernelSmoothTestsToL2 f=x.1 := congrArg Prod.fst hf
  have hf2 : kernelGradientLinear f=x.2 := congrArg Prod.snd hf
  have hzero : f=0 := kernelSmoothTestsToL2_injective (by
    simpa only [map_zero] using hf1.trans hz)
  rw [hzero,map_zero] at hf2
  exact hf2.symm

def kernelInitialGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 :=
  kernelInitialGradientGraph.toLinearPMap

lemma kernelInitialGradient_graph :
    kernelInitialGradient.graph=kernelInitialGradientGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelInitialGradientGraph_unique

lemma kernelInitialGradient_dense_domain :
    Dense (kernelInitialGradient.domain : Set KernelQuotientL2) := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [kernelInitialGradient_graph]
  exact ⟨f,rfl⟩

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.ReflectedDyadicSeries -/

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

namespace InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

lemma star_normalizedColumn {ι : Type*} (p : ι → O) (g : 𝓢(ℝ,ℂ))
    (Z : ℝ) (S : Finset ι) :
    star (normalizedColumn p (fun T => g (columnLog p Z T)) S) =
      normalizedColumn p (fun T => conjugateProfile g (columnLog p Z T)) S := by
  simp only [normalizedColumn, conjugateProfile_apply]
  simp

lemma conjugateProfile_support_bound (g : 𝓢(ℝ,ℂ)) (A : ℝ)
    (hg : ∀ t, g t ≠ 0 → |t| ≤ A) :
    ∀ t, conjugateProfile g t ≠ 0 → |t| ≤ A := by
  intro t ht
  apply hg t
  intro hz
  apply ht
  simp only [conjugateProfile_apply, hz, star_zero]

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem initial_nonzero_source_eq_bins
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z)
    (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      elementNorm (sourceObservation p x).1 ≤ Kmax) :
    let G := fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S
    truncatedSecondSource p hp hg hinj F Ψ m 1 1 G W H (fun C E => (K C E).erase 0) =
      ∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
          secondExpansionSource p hp hcop hg F Ψ m 1 1 ray
            (secondLogSector p ∅ F K R Z M j) G G W H := by
  dsimp only
  have hrow : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      ‖eisEmbedding (actualSecondRow p ∅ x.divisor x.frequency)‖^2 ≤ Kmax := by
    intro R hR x hx
    simpa only [initial_actual_row_norm] using hK R hR x hx
  have hfull := truncatedSecondSource_eq_binned p hp hcop hg hinj hc hpr ∅ F Ψ m 1 1
    g W Z H M Kmax hZ hgM K hrow
  have hsplit := truncatedSecondSource_eq_nonzero_add_zero p hp hg hinj F Ψ m 1 1
    (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S) W H K
  dsimp only at hfull
  rw [hsplit] at hfull
  exact add_left_cancel (by simpa only [add_comm] using hfull)

theorem initial_nonzero_source_norm_le_bins
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z)
    (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      elementNorm (sourceObservation p x).1 ≤ Kmax) :
    let G := fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1 G W H (fun C E => (K C E).erase 0)‖ ≤
      ∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray
            (secondLogSector p ∅ F K R Z M j) G G W H‖ := by
  dsimp only
  rw [initial_nonzero_source_eq_bins p hp hcop hg hinj hc hpr F Ψ m g W Z H M Kmax hZ hgM K hK]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ray hray
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro R hR
  exact norm_sum_le _ _

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

def initialBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let s := secondLogSector p ∅ F K R Z M j
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃))

theorem initial_nonzero_source_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O)
        (K : Finset ι → Finset ι → Finset O) (Z H Kmax : ℝ),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z A,
          elementNorm (sourceObservation p x).1 ≤ Kmax) →
        ∃ B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ,
          (∀ ray R j q, 0 ≤ B ray R j q) ∧
          (∀ ray R j q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B ray R j q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            W H (fun C E => (K C E).erase 0)‖ ≤
            C*(∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp A),
              ∑ j ∈ secondLogBinBox (Z*Real.exp A) Kmax,
                initialBinCost p hp hcop hg F R Ψ m ray K Z H A ε j windows (B ray R j)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_bin_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m K Z H Kmax hZ hH hΨ hK
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j hZ hH hΨ)
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j hZ hH hΨ)
  refine ⟨B,fun ray R j => (hB ray R j).1,fun ray R j => (hB ray R j).2.1,?_⟩
  apply (initial_nonzero_source_norm_le_bins p hp hcop hg hinj hc hpr F Ψ m
    g W Z H A Kmax hZ hgA K hK).trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro R hR
  apply Finset.sum_le_sum
  intro j hj
  convert (hB ray R j).2.2 using 1 ; dsimp only [initialBinCost, B] ; ring

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

theorem completed_smooth_series_rowPhase
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)
        ≤C*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨Cq,hCq,hquad⟩ := completed_smooth_quadratic V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n W a b ha hsupp hW A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨2*Cq*Cs^2,by positivity,?_⟩
  intro K Y H hK hY hH S T hS hT β hβ σ hσ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0< r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)≤_ at h
    have hphase : (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)≤
        ∑k : idealRange K,‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ i k)
    apply (hphase.trans h).trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (fun i k => σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by ring

end

open ActualEisensteinCubic

theorem completed_fiber_scalar_cost (deltaLoss K X a t Q c D S E : ℝ)
    (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X) (ha : 1≤a) (ht : 1≤t) (hQ : 1≤Q)
    (hc0 : 0<c) (hc : c≤K*Q) (hD : 1≤D) (hS : 1≤S) (hE : 1≤E)
    (hcost : c^2/(D*S*E^4)≤a*t^2*Q) :
    let k := K/(a*t)
    let y := k^2*c^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤(K*Q)^(10*deltaLoss)*(K+K^2*Q/X)/a := by
  dsimp only
  let k : ℝ := K/(a*t)
  let y : ℝ := k^2*c^2/(X*D*E^3)
  change (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤_
  have ha0 : 0<a := by linarith
  have ht0 : 0<t := by linarith
  have hX0 : 0<X := by linarith
  have hD0 : 0<D := by linarith
  have hS0 : 0<S := by linarith
  have hE0 : 0<E := by linarith
  have hK0 : 0<K := by linarith
  have hQ0 : 0<Q := by linarith
  have hk0 : 0<k := by dsimp [k]; positivity
  have hy0 : 0<y := by dsimp [y]; positivity
  have hat : 1≤a*t := one_le_mul_of_one_le_of_one_le ha ht
  have hk : k≤K := (div_le_self hK0.le hat)
  have hden : 1≤X*D*E^3 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX hD) (one_le_pow₀ hE)
  have hy : y≤K^2*(K*Q)^2 := by
    calc
      y ≤ k^2*c^2 := div_le_self (by positivity) hden
      _ ≤ K^2*(K*Q)^2 := mul_le_mul
        (pow_le_pow_left₀ hk0.le hk 2) (pow_le_pow_left₀ hc0.le hc 2) (by positivity) (by positivity)
  have hky : k*y≤(K*Q)^5 := by
    have hQ3 : 1≤Q^3 := one_le_pow₀ hQ
    calc
      k*y ≤ K*(K^2*(K*Q)^2) := mul_le_mul hk hy hy0.le hK0.le
      _ ≤ (K*(K^2*(K*Q)^2))*Q^3 := le_mul_of_one_le_right (by positivity) hQ3
      _ = (K*Q)^5 := by ring
  have hp : (k*y)^(2*deltaLoss)≤(K*Q)^(10*deltaLoss) := by
    have hh := Real.rpow_le_rpow (mul_pos hk0 hy0).le hky (by positivity : 0≤2*deltaLoss)
    convert hh using 1
    rw [←Real.rpow_natCast_mul (mul_pos hK0 hQ0).le]
    congr 1
    ring
  have hfirst : k/(S*E)≤K/a := by
    have hse : 1≤t*(S*E) := one_le_mul_of_one_le_of_one_le ht (one_le_mul_of_one_le_of_one_le hS hE)
    calc
      k/(S*E) = (K/a)/(t*(S*E)) := by dsimp [k]; field_simp
      _ ≤ K/a := div_le_self (by positivity) hse
  have hsecond : y/(S*E)≤K^2*Q/(a*X) := by
    calc
      y/(S*E) = (k^2/X)*(c^2/(D*S*E^4)) := by dsimp [y]; field_simp
      _ ≤ (k^2/X)*(a*t^2*Q) := mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = K^2*Q/(a*X) := by dsimp [k]; field_simp
  have hshape : (k+y)/(S*E)≤(K+K^2*Q/X)/a := by
    rw [add_div]
    have hh := add_le_add hfirst hsecond
    convert hh using 1
    field_simp
  calc
    _ = (k*y)^(2*deltaLoss)*((k+y)/(S*E)) := by ring
    _ ≤ (K*Q)^(10*deltaLoss)*((K+K^2*Q/X)/a) :=
      mul_le_mul hp hshape (by positivity) (by positivity)
    _ = _ := by ring

theorem completed_conductor_norm_bound {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) :
    (Ideal.absNorm (∏i,P i):ℝ)≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := by
  have hd : (∏i,P i)∣I*Q := Fintype.prod_dvd_of_coprime hcop hpool
  have hn : 0<Ideal.absNorm (I*Q) := Nat.pos_of_ne_zero (fun hz =>
    mul_ne_zero hI hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hh := Nat.le_of_dvd hn (map_dvd Ideal.absNorm hd)
  exact_mod_cast (by simpa only [map_mul] using hh)

theorem completed_actual_fiber_cost {ι : Type*} [Fintype ι]
    (deltaLoss K X : ℝ) (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X)
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0) (hIK : (Ideal.absNorm I:ℝ)≤K)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    let j := fun i => completedLocalExponent I F (P i)
    let k := K/((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ))
    let D := (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)
    let S := (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
    let E := (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)
    let y := k^2*(Ideal.absNorm (∏i,P i):ℝ)^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤
      (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  have hn (J : Ideal O) (hJ : J≠0) : 1≤(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hprod : (∏i,P i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))
  have hc := (completed_conductor_norm_bound I Q hI hQ P hcop hpool).trans
    (mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _))
  have hh := completed_fiber_scalar_cost deltaLoss K X
    (Ideal.absNorm (rowPowerfulPart I):ℝ) (Ideal.absNorm (rowMaskPart I Q):ℝ)
    (Ideal.absNorm Q:ℝ) (Ideal.absNorm (∏i,P i):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 1):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2):ℝ)
    hδ hK hX (hn _ (rowPowerfulPart_ne_zero I))
    (hn _ (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) (hn _ hQ)
    (lt_of_lt_of_le (by norm_num) (hn _ hprod)) hc
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 1))
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
  exact hh

def completedShellWindow (x : ℝ) : ℂ :=
  if -Real.log 2≤x ∧ x≤0 then 1 else 0

theorem completedShellWindow_support (x : ℝ) (h : completedShellWindow x≠0) :
    |x|≤Real.log 2 := by
  have hx : -Real.log 2≤x ∧ x≤0 := by
    by_contra hn
    exact h (by simp [completedShellWindow,hn])
  apply abs_le.mpr
  exact ⟨hx.1,hx.2.trans (Real.log_nonneg (by norm_num))⟩

theorem completedShellWindow_norm (x : ℝ) : ‖completedShellWindow x‖≤1 := by
  unfold completedShellWindow
  split_ifs <;> simp

theorem completedShellWindow_log (x U : ℝ) (hx : 0<x) (hU : 0<U)
    (hlo : U/2≤x) (hhi : x≤U) : completedShellWindow (Real.log (x/U))=1 := by
  apply ite_eq_left
  constructor
  · have hhalf : (1/2:ℝ)≤x/U := (le_div_iff₀ hU).mpr (by linarith)
    have hh := Real.strictMonoOn_log.monotoneOn (by norm_num : (1/2:ℝ)∈Set.Ioi 0)
      (show x/U∈Set.Ioi 0 from div_pos hx hU) hhalf
    simpa only [one_div,Real.log_inv] using hh
  · exact Real.log_nonpos (div_nonneg hx.le hU.le) ((div_le_one hU).mpr hhi)

theorem dyadic_root_product_bound (u v U B : ℝ) (hu : 0<u) (_hv : 0<v)
    (hU : 0<U) (hB : 0<B) (huU : U/2≤u) (hvB : B/2≤v) :
    Real.sqrt U*B≤4*(Real.sqrt u*v) := by
  have hs : Real.sqrt U≤2*Real.sqrt u := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hU.le,Real.sq_sqrt hu.le]
    nlinarith
  calc
    _ ≤ (2*Real.sqrt u)*(2*v) := mul_le_mul hs (by linarith) hB.le (by positivity)
    _ = _ := by ring

def reflectedDyadicCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r : ℝ)
    (n v : Ideal O) : ℂ :=
  η n v*reflectedBranch P hg j e
    (primaryGenerator (reflectionExtractedDivisor P j e 1*n))
    (primaryGenerator (reflectionExtractedDivisor P j e 2*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2*v):ℝ):ℝ):ℂ)

theorem reflectedDyadicCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r U B : ℝ)
    (hr : 0< r) (hU : 0<U) (hB : 0<B) (n v : Ideal O) (hn : n≠0) (hv : v≠0)
    (hη : ‖η n v‖≤1) (hlo : U/2≤(Ideal.absNorm n:ℝ)) (hlov : B/2≤(Ideal.absNorm v:ℝ)) :
    ‖reflectedDyadicCoefficient P hg j e η r n v‖≤
      1/(Real.sqrt U*B*r*Real.sqrt
        ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
          (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ))) := by
  let D := reflectionExtractedDivisor P j e 1
  let E := reflectionExtractedDivisor P j e 2
  let S := reflectionExtractedDivisor P j e 0
  have hnorm (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hDn := hnorm D (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 1)
  have hEn := hnorm E (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 2)
  have hSn := hnorm S (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 0)
  have hnn := hnorm n hn
  have hvn := hnorm v hv
  have hlocal := reflectedBranch_normalized_bound P hg j e
    (primaryGenerator (D*n)) (primaryGenerator (E*v))
    (Ideal.absNorm n:ℝ) (Ideal.absNorm v:ℝ) hnn hvn
  change ‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖ /
      (Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ)))≤
      1/(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ)*
        Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ))) at hlocal
  have hbase : 0<Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ)) := by positivity
  have hroot := dyadic_root_product_bound _ _ U B hnn hvn hU hB hlo hlov
  unfold reflectedDyadicCoefficient
  change ‖η n v*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*v):ℝ):ℝ):ℂ)‖≤_
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ ‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖/
      (4*r*Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) hη
    _ = (1/(4*r))*(‖reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*v))‖/
      (Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ)))) := by ring
    _ ≤ (1/(4*r))*(1/(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ)*
      Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ)))) :=
        mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = 1/(4*(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ))*r*
      Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ))) := by ring
    _ ≤ _ := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hr.le) hbase.le

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

def reflectedBranchBlock {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ)
    (σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  σ i k*completedSmoothDyadicBlock completedShellWindow completedShellWindow completedShellWindow
    W K Y ρ q S T (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1)) i k

theorem completed_reflected_branch_series
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖reflectedBranchBlock P hg j e W K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock P hg j e W K Y ρ q S T η σ i k‖^2)
        ≤C*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨C,hC,h⟩ := completed_smooth_series_rowPhase
    completedShellWindow completedShellWindow completedShellWindow (Real.log 2) (Real.log 2) (Real.log 2)
    hl hl hl completedShellWindow_support completedShellWindow_support completedShellWindow_support
    completedShellWindow_norm completedShellWindow_norm completedShellWindow_norm
    W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C,hC,?_⟩
  intro K Y hK hY ι _ P _ hg j e S T hS hT η hη σ hσ
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
        (Ideal.absNorm_eq_zero_iff.mp hz))
  exact h K Y _ hK hY (mul_pos (hn 0) (hn 2)) S T
    (fun i I hI => ⟨(hS i I hI).1,(hS i I hI).2.2⟩)
    (fun i I hI => ⟨(hT i I hI).1,(hT i I hI).2.2⟩)
    (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1))
    (fun i n hn v hv => reflectedDyadicCoefficient_norm P hg j e (η i)
      (ramifiedScale ρ q i.1) _ _ (ramifiedScale_pos ρ q hρ (by linarith) _) (by positivity) (by positivity)
      n v (hS i n hn).1 (hT i v hv).1 (hη i n hn v hv) (hS i n hn).2.1 (hT i v hv).2.1)
    σ hσ

end CompletedGauss

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.GaussSum.BranchScaling -/

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

def completedResidualScale (K : ℝ) (I Q : Ideal O) : ℝ :=
  K/((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ))

def completedBranchScale {ι : Type*} [Fintype ι]
    (K X : ℝ) (I F Q : Ideal O) (P : ι→Ideal O) (e : ι→Fin 3) : ℝ :=
  (completedResidualScale K I Q)^2*(Ideal.absNorm (∏i,P i):ℝ)^2/
    (X*(Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 1):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2):ℝ)^3)

theorem completed_reflected_fiber
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e W
          (completedResidualScale K I Q) (completedBranchScale K X I F Q P e) ρ q S T η σ i k‖^2)
        ≤C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_branch_series W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C,hC,?_⟩
  intro K X hK hX I F Q hI hQ hIK hscale ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _
    (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
      (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hk : 0<completedResidualScale K I Q := by linarith
    have hx : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  have hb := (h (completedResidualScale K I Q) (completedBranchScale K X I F Q P e)
    hscale hy P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hc := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hm := mul_le_mul_of_nonneg_left hc hC.le
  apply hb.trans
  convert hm using 1 <;> (try dsimp [completedResidualScale,completedBranchScale]) <;> ring

end CompletedGauss

open scoped BigOperators Classical
namespace LocalReflectionBrackets
variable {F : Type*} [Field F] [Fintype F]

def unitArgumentFactor (χ : MulChar F ℂ) (j : ℕ) (z : F) : ℂ :=
  if j=4 then 1 else (χ^(j+2))⁻¹ z

theorem bracket_mul_unit (χ : MulChar F ℂ) (j : ℕ) (z x : F) (hz : z≠0) :
    bracket χ j (z*x)=unitArgumentFactor χ j z*bracket χ j x := by
  by_cases hj4 : j=4
  · simp [unitArgumentFactor,bracket,hj4,hz]
  · by_cases hj0 : j=0
    · subst j
      simp only [unitArgumentFactor,bracket,show (0:ℕ)≠4 by decide,ite_false,ite_true,
        zero_add,map_mul]
      ring
    · simp only [unitArgumentFactor,bracket,ite_eq_right hj4,ite_eq_right hj0,map_mul]

theorem unitArgumentFactor_norm (χ : MulChar F ℂ) (j : ℕ) (z : F) (hz : z≠0) :
    ‖unitArgumentFactor χ j z‖=1 := by
  by_cases hj : j=4
  · simp [unitArgumentFactor,hj]
  · rw [unitArgumentFactor,ite_eq_right hj]
    exact FiniteRayExpansion.norm_char_unit ((χ^(j+2))⁻¹) (Units.mk0 z hz)

end LocalReflectionBrackets
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

theorem unit_ramified_quotient_ne_zero (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (u : Oˣ) (m : ℕ) :
    Ideal.Quotient.mk P ((u:O)*lambda^m)≠0 := by
  rw [map_mul,map_pow]
  apply mul_ne_zero
  · exact (u.isUnit.map (Ideal.Quotient.mk P)).ne_zero
  · exact pow_ne_zero _ (fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h))

def ramifiedBranchPhase {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) : ℂ :=
  ∏i,unitArgumentFactor (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) ((u:O)*lambda^m))

theorem ramifiedBranchPhase_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) : ‖ramifiedBranchPhase P hg j u m‖=1 := by
  rw [ramifiedBranchPhase,norm_prod]
  have hh (i : ι) := unitArgumentFactor_norm (actualSextic (P i) (hg i)) (j i)
    _ (unit_ramified_quotient_ne_zero (P i) (hg i) u m)
  simp only [hh,Finset.prod_const_one]

theorem ramified_bracket_full_expansion {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (u : Oˣ) (m : ℕ) (n b : O) :
    (∏i,bracket (actualSextic (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) ((u:O)*lambda^m*(n*b^3))))=
      ramifiedBranchPhase P hg j u m*∑e : ι→Fin 3,reflectedBranch P hg j e n b := by
  have hl (i : ι) : bracket (actualSextic (P i) (hg i)) (j i)
      (Ideal.Quotient.mk (P i) ((u:O)*lambda^m*(n*b^3)))=
      unitArgumentFactor (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) ((u:O)*lambda^m))*
      bracket (actualSextic (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)) := by
    rw [map_mul]
    exact bracket_mul_unit _ _ _ _ (unit_ramified_quotient_ne_zero (P i) (hg i) u m)
  simp_rw [hl]
  rw [Finset.prod_mul_distrib,prod_bracket_eq_full_branches P hg j n b]
  rfl

end CompletedGauss

namespace InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open ConcretePrimeRowBridge (idealGenerator)

local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def sourceLabelUnit (f : O) : Oˣ :=
  Classical.choose (exists_label_unit f (Ideal.span {f}) rfl)

lemma sourceLabelUnit_spec (f : O) : f=(sourceLabelUnit f : O)*idealGenerator (Ideal.span {f}) :=
  Classical.choose_spec (exists_label_unit f (Ideal.span {f}) rfl)

def sourceIdealPoint (z : O × O) : Ideal O × O := (Ideal.span {z.2},z.1)

def sourceUnitPoint (z : O × O) : Oˣ × (Ideal O × O) :=
  (sourceLabelUnit z.2,sourceIdealPoint z)

lemma sourceUnitPoint_injective : Function.Injective sourceUnitPoint := by
  intro x y h
  have hu : sourceLabelUnit x.2=sourceLabelUnit y.2 := congrArg Prod.fst h
  have hi : Ideal.span {x.2}=Ideal.span {y.2} := congrArg (fun z => z.2.1) h
  have hr : x.1=y.1 := congrArg (fun z => z.2.2) h
  apply Prod.ext hr
  rw [sourceLabelUnit_spec x.2,sourceLabelUnit_spec y.2,hu,hi]

def sourceIdealTarget (T : Finset (O × O)) : Finset (Ideal O × O) :=
  T.image sourceIdealPoint

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem sourceChildEnergy_le_ideal (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (O × O)) (V : ℝ → ℂ) (X : ℝ) (tn rn : Bool) (a b : ℝ) :
    sourceChildEnergy p hp hcop hg F Ψ m T V X tn rn a b ≤
      childEnergy p hp hcop hg F Ψ m (sourceIdealTarget T) V X tn rn a b := by
  let E : Oˣ × (Ideal O × O) → ℝ := fun z =>
    ‖idealChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b tn) rn z.1 z.2‖^2
  have hsub : T.image sourceUnitPoint ⊆ Finset.univ ×ˢ sourceIdealTarget T := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩
  calc
    _ = ∑ z ∈ T.image sourceUnitPoint,E z := by
      rw [Finset.sum_image (fun x _ y _ h => sourceUnitPoint_injective h)]
      apply Finset.sum_congr rfl
      intro z hz
      simp only [E,sourceUnitPoint,sourceIdealPoint,idealChildRow]
      rw [←sourceLabelUnit_spec]
    _ ≤ ∑ z ∈ Finset.univ ×ˢ sourceIdealTarget T,E z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro z hz hn
      exact sq_nonneg _
    _ = _ := by rw [Finset.sum_product]; rfl

theorem sourceGeometricMean_le_ideal (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (q : Frequency) :
    sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q ≤
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂ q := by
  apply mul_le_mul
    (Real.sqrt_le_sqrt (sourceChildEnergy_le_ideal p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2))
    (Real.sqrt_le_sqrt (sourceChildEnergy_le_ideal p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end

theorem sourceIdealTarget_bounds (T : Finset (O × O)) (K lengthScale : ℝ)
    (hT : ∀ z ∈ T, z.2 ≠ 0 ∧ elementNorm z.2 ≤ lengthScale ∧ elementNorm z.1 ≤ K) :
    ∀ z ∈ sourceIdealTarget T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hne,hn,hk⟩ := hT x hx
  refine ⟨Ideal.span_singleton_eq_bot.not.mpr hne,?_,hk⟩
  simpa only [sourceIdealPoint,elementNorm,eisEmbedding_norm_sq_eq_absNorm_span] using hn

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem positive_nested_density_bound (f : Frequency → ℝ) (C : ℝ)
    (hf : ∀ q, 0 ≤ f q)
    (hbound : ∀ q, f q ≤ C*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x,y,z)) ≤
      C*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  let I := ∫ t : ℝ,firstLogDensity 0 t
  have hz (x y : ℝ) : (∫ z : ℝ,f (x,y,z)) ≤
      C*firstLogDensity 0 x*firstLogDensity 0 y*I := by
    have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z : ℝ => hf (x,y,z)))
      ((firstLogDensity_integrable 0).const_mul (C*firstLogDensity 0 x*firstLogDensity 0 y))
      (Filter.Eventually.of_forall (fun z : ℝ => hbound (x,y,z)))
    simpa only [integral_const_mul,I] using h
  have hy (x : ℝ) : (∫ y : ℝ, ∫ z : ℝ,f (x,y,z)) ≤ C*firstLogDensity 0 x*I*I := by
    have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))
      (((firstLogDensity_integrable 0).const_mul (C*firstLogDensity 0 x)).mul_const I)
      (Filter.Eventually.of_forall (hz x))
    simpa only [integral_mul_const,integral_const_mul,I] using h
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => integral_nonneg
      (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z)))))
    ((((firstLogDensity_integrable 0).const_mul C).mul_const I).mul_const I)
    (Filter.Eventually.of_forall hy)
  simp only [integral_mul_const,integral_const_mul] at h
  convert h using 1 ; dsimp [I] ; ring

theorem polynomial_density_cost (B G : Frequency → ℝ) (J : ℕ) (S C E : ℝ)
    (hS : 0 < S) (hC : 0 ≤ C) (_hE : 0 ≤ E)
    (hB : ∀ q, 0 ≤ B q) (hG : ∀ q, 0 ≤ G q)
    (hdec : ∀ q, S*B q ≤ C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,B (x,y,z)*G (x,y,z)) ≤
      (C*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  apply positive_nested_density_bound _ (C*E/S)
    (fun q => mul_nonneg (hB q) (hG q))
  intro q
  have hc : 0 ≤ C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (firstLogDensity_nonneg _ _))
      (firstLogDensity_nonneg _ _)) (firstLogDensity_nonneg _ _)
  have hb := mul_le_mul (hdec q) (henergy q) (hG q) hc
  have heq :
      (C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)*
        (E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) =
      C*E*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2 := by
    rw [←density_weight_identity J q.1,←density_weight_identity J q.2.1,
      ←density_weight_identity J q.2.2]
    ring
  rw [heq] at hb
  calc
    _ ≤ (C*E*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2)/S := by
      apply (le_div_iff₀ hS).mpr
      convert hb using 1 ; ring
    _ = _ := by ring

theorem initialBinCost_of_child_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hchild : ∀ q,
      let s := secondLogSector p ∅ F K R Z M j
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X q ≤
        (Cchild*(X*initialLogLabel j))*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/Z)*Real.exp 2*Cchild*Cₛ*(∫ t : ℝ,firstLogDensity 0 t)^3)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := secondLogSector p ∅ F K R Z M j
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X
  let E := Cchild*(X*initialLogLabel j)
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hpR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hpR)
  have hlabel : 0 < initialLogLabel j := by
    unfold initialLogLabel secondLogE secondLogV
    exact mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) (Real.exp_pos _)
  have hE : 0 ≤ E := mul_nonneg hCc (mul_pos hX hlabel).le
  have hS : 0 < S := by
    dsimp [S]
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  have hG : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    intro q
    exact (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X q).trans (hchild q)
  have hb := polynomial_density_cost B G J S Cₛ E hS hCₛ hE hB hG hdec henergy
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3) := mul_le_mul_of_nonneg_left hb hpref
    _ = _ := by
      dsimp only [E,X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hpR.ne']
      have hz := hZ.ne'
      have hr := hpR.ne'
      field_simp

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma blockRow_mul (S : Finset ι) (e : ι→ℕ) (a b:O) :
    blockRow p hg S e (a*b)=blockRow p hg S e a*blockRow p hg S e b := by
  simp only [blockRow_eq_product,map_mul,Finset.prod_mul_distrib]

omit [DecidableEq ι] in
lemma blockRow_unit_mul_star (S : Finset ι) (e : ι→ℕ) (u:Oˣ) :
    blockRow p hg S e (u:O)*star (blockRow p hg S e (u:O))=1 := by
  exact GaussGeneratorTransport.finiteSexticRow_unit_mul_star
    (fun i:S=>Ideal.span {p i.val}) (fun i=>hg i.val) (fun i=>e i.val) u

omit [DecidableEq ι] in
lemma originalLabelColumn_unit_c (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (C : Finset ι→ℂ) (u c f : O) (S : Finset ι) :
    originalLabelColumn p hg B ε₁ ε₂ negative C (u*c) f S =
      originalLabelColumn p hg B ε₁ ε₂ negative C c f S*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u^4 := by
  simp only [originalLabelColumn,finiteSquarefreeRow_mul,mul_pow]
  ring

omit [DecidableEq ι] in
lemma row_four_eq_star_square (S : Finset ι) (u:O) :
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u^4=
      star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S (u^2)) := by
  have h1 : finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simpa only [h1,star_one,mul_one,one_mul] using
    row_four_star (fun i=>Ideal.span {p i}) hg S u 1

theorem threeGaussRowFactor_common_unit
    (N P B : Finset ι) (hNP:Disjoint N P) (hNB:Disjoint N B) (hPB:Disjoint P B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ) (u:Oˣ) (c f d h:O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) d h =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) d ((u:O)^2*h) := by
  have hU:=blockRow_unit_mul_star p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) (u^2)
  simp only [Units.val_pow_eq_pow_val] at hU
  simp only [threeGaussRowFactor,originalLabelColumn_unit_c,row_four_eq_star_square,
    star_mul,star_star,blockRow_mul]
  rw [threeBlockRow_factor p hg N P B hNP hNB hPB v ε₁ ε₂ ((u:O)^2)]
  simp only [star_mul,star_star]
  let a : ℂ := threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
    (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
    (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) d h *
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg N ((u:O)^2) *
    star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg P ((u:O)^2))
  convert congrArg (fun z:ℂ=>a*z) hU.symm using 1 <;>
    simp only [a,threeGaussRowFactor,star_mul] <;> ring

theorem actualFirstKernel_common_unit (F B : Finset ι) (hFB:Disjoint F B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ) (X₁ X₂ K:ℝ) (u:Oˣ) (c f d h:O) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) W V₁ V₂ X₁ X₂ K d h =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d ((u:O)^2*h) := by
  have hn : ‖eisEmbedding ((u:O)^2*h)‖=‖eisEmbedding h‖ := by
    rw [map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,one_mul]
  simp only [actualFirstKernel,Finset.mul_sum,hn]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP:Disjoint N P
  · simp only [hNP,ite_true]
    rw [threeGaussRowFactor_common_unit p hp hcop hg N P B hNP
      (hFB.mono_left (Finset.mem_powerset.mp hN)) (hFB.mono_left (Finset.mem_powerset.mp hP))
      v ε₁ ε₂ C₁ C₂ u c f d h]
    ring
  · simp only [hNP,ite_false,mul_zero]

omit [DecidableEq ι] in
theorem commonUnitPhase_norm (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (u:Oˣ) :
    ‖blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)‖=1 := by
  have h:=blockRow_unit_mul_star p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) (u^2)
  have hn:=congrArg norm h
  simp only [norm_mul,norm_star,norm_one,Units.val_pow_eq_pow_val] at hn
  nlinarith [norm_nonneg (blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2))]

def unitSquareRowEquiv (u:Oˣ) : O≃O where
  toFun h := (u:O)^2*h
  invFun h := ((u⁻¹:Oˣ):O)^2*h
  left_inv h := by
    dsimp only
    rw [←mul_assoc,←mul_pow]
    simp
  right_inv h := by
    dsimp only
    rw [←mul_assoc,←mul_pow]
    simp

theorem tsum_actualFirstKernel_common_unit (F B:Finset ι) (hFB:Disjoint F B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ) (X₁ X₂ K:ℝ) (u:Oˣ) (c f d:O) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) W V₁ V₂ X₁ X₂ K d h) =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    ∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d h := by
  let F₀ : O→ℂ := actualFirstKernel p hp hcop hg F B v ε₁ ε₂
    (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
    (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d
  let q := blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)
  calc
    _ = ∑'h:O,q*F₀ ((u:O)^2*h) := by
      apply tsum_congr
      intro h
      exact actualFirstKernel_common_unit p hp hcop hg F B hFB v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K u c f d h
    _ = q*∑'h:O,F₀ ((u:O)^2*h) := tsum_mul_left
    _ = q*∑'h:O,F₀ h := by
      exact congrArg (fun z:ℂ=>q*z) ((unitSquareRowEquiv u).tsum_eq F₀)

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

lemma blockRow_at_zero (S:Finset ι) (e:ι→ℕ) :
    blockRow p hg S e 0=if S=∅ then 1 else 0 := by
  by_cases hS:S=∅
  · simp [hS,blockRow_eq_product]
  · rw [ite_eq_right hS,blockRow_eq_product]
    obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero hi
    simp only [map_zero,MulChar.map_zero]

lemma threeGaussRowFactor_zero_nonempty
    (N P B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (d:O)
    (hne:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d 0=0 := by
  simp only [threeGaussRowFactor,blockRow_at_zero,ite_eq_right hne,star_zero,mul_zero]

theorem actualFirstKernel_zero
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ)
    (X₁ X₂ K:ℝ) (d:O) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d 0 =
      if cubeActiveSupport B v ε₁ ε₂=∅ then
        (V₁ (columnLog p X₁ ∅)*V₂ (columnLog p X₂ ∅))*(K:ℂ)*paperRadialFourier W 0*
          threeGaussRowFactor p hp hcop hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d 0 else 0 := by
  unfold actualFirstKernel
  by_cases hB:cubeActiveSupport B v ε₁ ε₂=∅
  · rw [ite_eq_left hB,Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single ∅]
      · simp only [Finset.disjoint_empty_left,ite_true,Finset.empty_union,hB,
          Finset.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one,map_zero,norm_zero,
          zero_pow (by decide:2≠0),mul_zero,zero_div]
      · intro P hP hP0
        have hn:(∅∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by simpa only [Finset.empty_union,hB,Finset.union_empty] using hP0
        simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg ∅ P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]
      · simp
    · intro N hN hN0
      apply Finset.sum_eq_zero
      intro P hP
      have hn:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by
        intro he
        exact hN0 (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
          have : i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂:=Finset.mem_union_left _ (Finset.mem_union_left _ hi)
          simp only [he, Finset.notMem_empty] at this))
      simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]
    · simp
  · rw [ite_eq_right hB]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro P hP
    have hn:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by
      intro he
      exact hB (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
        have : i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂:=Finset.mem_union_right _ hi
        simp only [he, Finset.notMem_empty] at this))
    simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]

theorem actualFirstKernel_truncate
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ)
    (X₁ X₂ K:ℝ) (hK:0<K) (d:O) (hd:d≠0) (T:Finset O) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)=
      (∑h∈T,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)+
      ∑'h:{h:O//h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val := by
  exact (actualFirstKernel_summable p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).sum_add_tsum_subtype_compl T |>.symm

end FirstPassCubeLabels

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.LocalCutoffs -/

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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv ContDiff

structure PositiveChartCutoff where
  func : EuclideanSpatial → ℝ
  smooth : ContDiff ℝ ∞ func
  compact : HasCompactSupport func
  positive : tsupport func ⊆ {p | 0 < p 2}

lemma kernelChartCutoff_exists (p : EuclideanSpatial) (hp : 0<p 2) :
    ∃χ : PositiveChartCutoff, χ.func p=1 ∧ Set.range χ.func ⊆ Set.Icc 0 1 ∧
      Set.InjOn (integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic)
        (tsupport χ.func) := by
  obtain ⟨U,hU,hw,hUinj⟩ :=
    kernelQuotient_localHomeomorph.isLocallyInjective (euclideanToHyperbolic p)
  have hn : {q : EuclideanSpatial | 0<q 2} ∩ euclideanToHyperbolic ⁻¹' U ∈ 𝓝 p :=
    inter_mem ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hp)
      ((euclideanToHyperbolic_contMDiffAt p hp).continuousAt (hU.mem_nhds hw))
  obtain ⟨χ,hχ,hcomp,hsmooth,hrange,hvalue⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hn
  refine ⟨⟨χ,hsmooth,hcomp,fun q hq => (hχ hq).1⟩,hvalue,hrange,?_⟩
  intro q hq r hr heq
  have hwEq := hUinj (hχ hq).2 (hχ hr).2 heq
  have hc := congrArg hyperbolicEuclideanCoordinates hwEq
  simpa only [hyperbolicEuclideanCoordinates_toHyperbolic _ (hχ hq).1,
    hyperbolicEuclideanCoordinates_toHyperbolic _ (hχ hr).1] using hc

def kernelLocalizedField (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : ℂ := χ.func p • kernelTestField f p

lemma kernelLocalizedField_compact (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    HasCompactSupport (kernelLocalizedField χ f) := χ.compact.smul_right

lemma kernelLocalizedField_tsupport (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    tsupport (kernelLocalizedField χ f) ⊆ tsupport χ.func := tsupport_smul_subset_left _ _

lemma kernelLocalizedField_smooth (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ContDiff ℝ ∞ (kernelLocalizedField χ f) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p 2
  · exact χ.smooth.contDiffAt.smul (kernelTestField_contDiffAt f p hp)
  · have hn : p ∉ tsupport χ.func := fun h => hp (χ.positive h)
    have hz := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hz] with q hq
    simp only [kernelLocalizedField,hq,Pi.zero_apply,zero_smul]

def kernelLocalizedSchwartz (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    𝓢(EuclideanSpatial,ℂ) :=
  (kernelLocalizedField_compact χ f).toSchwartzMap (kernelLocalizedField_smooth χ f)

lemma kernelLocalizedSchwartz_coe (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    (kernelLocalizedSchwartz χ f : EuclideanSpatial → ℂ)=kernelLocalizedField χ f := rfl

def kernelLocalizedH1 (χ : PositiveChartCutoff) (f : kernelSmoothTests) : EuclideanH1 := by
  let g := kernelLocalizedSchwartz χ f
  let v := WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} g).toLp 2 volume)
  refine ⟨WithLp.toLp 2 (g.toLp 2 volume,v),?_⟩
  change (g.toLp 2 volume,v)∈euclideanWeakGradientGraph
  exact schwartz_mem_euclideanWeakGradientGraph g

lemma kernelLocalizedH1_embedding (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    euclideanH1Embedding (kernelLocalizedH1 χ f)=
      (kernelLocalizedSchwartz χ f).toLp 2 volume := rfl

lemma kernelLocalizedH1_gradient (χ : PositiveChartCutoff) (f : kernelSmoothTests) (j : Fin 3) :
    euclideanH1Gradient (kernelLocalizedH1 χ f) j=
      (∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).toLp 2 volume := rfl

lemma kernelLocalizedField_fderiv (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0 < p 2) (u : EuclideanSpatial) :
    fderiv ℝ (kernelLocalizedField χ f) p u=
      χ.func p • fderiv ℝ (kernelTestField f) p u+
        (fderiv ℝ χ.func p u) • kernelTestField f p := by
  change fderiv ℝ (χ.func • kernelTestField f) p u=_
  rw [fderiv_smul (χ.smooth.differentiable (by simp)).differentiableAt
    ((kernelTestField_contDiffAt f p hp).differentiableAt (by simp))]
  rfl

lemma complex_norm_add_sq_le (z w : ℂ) :
    ‖z+w‖^2 ≤ 2*‖z‖^2+2*‖w‖^2 := by
  have hh := norm_add_le z w
  have hn := norm_nonneg (z+w)
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

lemma kernelLocalizedField_energy_bound (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    (p 2)^2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) ≤
    2*(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
      2*(p 2)^2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
  have hsum : (∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) ≤
      ∑j : Fin 3,(2*(χ.func p)^2*‖fderiv ℝ (kernelTestField f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2+
        2*‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2*
          ‖kernelTestField f p‖^2) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [kernelLocalizedField_fderiv χ f p hp]
    simpa only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc] using
      complex_norm_add_sq_le
        (χ.func p • fderiv ℝ (kernelTestField f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
        (fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p)
  have he : kernelTestEnergyDensity f (euclideanToHyperbolic p)=
      (p 2)^2*∑j : Fin 3,‖fderiv ℝ (kernelTestField f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2 := by
    rw [kernelTestEnergyDensity_eq_partials]
    have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
    have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
    simp only [hv,kernelTestPartial,hc]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (p 2))
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,
    mul_add,mul_assoc,mul_left_comm,mul_comm] using hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal

def kernelEuclideanProjection : EuclideanSpatial → KernelQuotient :=
  integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic

lemma kernelEuclideanProjection_measurable : Measurable kernelEuclideanProjection :=
  (measurable_integralOrbitProjection _).comp euclideanToHyperbolic_measurable

lemma euclideanToHyperbolic_measurePreserving_on (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (_hpos : S⊆euclideanUpperHalf) :
    MeasurePreserving euclideanToHyperbolic (hyperbolicEuclideanVolume.restrict S)
      (hyperbolicVolume.restrict (hyperbolicEuclideanCoordinates ⁻¹' S)) := by
  have hU : MeasurableSet (hyperbolicEuclideanCoordinates ⁻¹' S) :=
    hyperbolicEuclideanCoordinates_continuous.measurable hS
  have hset : euclideanToHyperbolic ⁻¹' (hyperbolicEuclideanCoordinates ⁻¹' S)=ᵐ[hyperbolicEuclideanVolume]S := by
    filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
    simp only [Set.mem_preimage,hyperbolicEuclideanCoordinates_toHyperbolic p hp]
  refine ⟨euclideanToHyperbolic_measurable,?_⟩
  rw [hyperbolicVolume,Measure.restrict_map euclideanToHyperbolic_measurable hU,
    Measure.restrict_congr_set hset]

lemma euclideanToHyperbolic_image_positive (S : Set EuclideanSpatial)
    (hpos : S⊆euclideanUpperHalf) :
    euclideanToHyperbolic '' S=hyperbolicEuclideanCoordinates ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa only [Set.mem_preimage,hyperbolicEuclideanCoordinates_toHyperbolic p (hpos hp)] using hp
  · intro hw
    exact ⟨hyperbolicEuclideanCoordinates w,hw,euclideanToHyperbolic_coordinates w⟩

lemma kernelEuclideanProjection_measurePreserving_on (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) :
    MeasurePreserving kernelEuclideanProjection (hyperbolicEuclideanVolume.restrict S)
      ((integralQuotientVolume globalKubotaKernel).restrict (kernelEuclideanProjection '' S)) := by
  have hU : MeasurableSet (hyperbolicEuclideanCoordinates ⁻¹' S) :=
    hyperbolicEuclideanCoordinates_continuous.measurable hS
  have hi : Set.InjOn (integralOrbitProjection globalKubotaKernel)
      (hyperbolicEuclideanCoordinates ⁻¹' S) := by
    intro u hu v hv heq
    have hh := hinj hu hv (by simpa only [kernelEuclideanProjection,Function.comp_apply,
      euclideanToHyperbolic_coordinates] using heq)
    have hh' := congrArg euclideanToHyperbolic hh
    simpa only [euclideanToHyperbolic_coordinates] using hh'
  have hcomp := (kernelProjection_measurePreserving_on _ hU hi).comp
    (euclideanToHyperbolic_measurePreserving_on S hS hpos)
  have himage : integralOrbitProjection globalKubotaKernel ''
      (hyperbolicEuclideanCoordinates ⁻¹' S)=kernelEuclideanProjection '' S := by
    rw [←euclideanToHyperbolic_image_positive S hpos,Set.image_image]
    rfl
  rwa [himage] at hcomp

lemma kernelEuclideanProjection_integral (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : AEStronglyMeasurable g (integralQuotientVolume globalKubotaKernel)) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)=
      ∫q in kernelEuclideanProjection '' S,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := hg.mono_measure (Measure.restrict_le_self (s := kernelEuclideanProjection '' S))
  rw [←hm.map_eq] at hh ⊢
  exact (integral_map hm.measurable.aemeasurable hh).symm

lemma kernelEuclideanProjection_integral_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (g : KernelQuotient → ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) (hgn : ∀q,0≤g q) :
    (∫p in S,g (kernelEuclideanProjection p)∂hyperbolicEuclideanVolume)≤
      ∫q,g q∂integralQuotientVolume globalKubotaKernel := by
  rw [kernelEuclideanProjection_integral S hS hpos hinj g hg.aestronglyMeasurable]
  exact setIntegral_le_integral hg (Eventually.of_forall hgn)

lemma kernelLocalEnergy_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (f : kernelSmoothTests) :
    (∫p in S,kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume)≤
      kernelDirichletEnergy f := by
  exact kernelEuclideanProjection_integral_le S hS hpos hinj _
    (kernelQuotientEnergyDensity_integrable f) (kernelQuotientEnergyDensity_nonneg f)

lemma kernelSmoothTestsToL2_norm_sq (f : kernelSmoothTests) :
    ‖kernelSmoothTestsToL2 f‖^2=
      ∫q,‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel := by
  calc
    ‖kernelSmoothTestsToL2 f‖^2=inner ℝ (kernelSmoothTestsToL2 f) (kernelSmoothTestsToL2 f) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫q,inner ℝ (kernelSmoothTestsToL2 f q) (kernelSmoothTestsToL2 f q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(kernelSmoothTests_memLp f).coeFn_toLp] with q hq
      change inner ℝ (((kernelSmoothTests_memLp f).toLp f.1) q)
        (((kernelSmoothTests_memLp f).toLp f.1) q)=_
      rw [hq,real_inner_self_eq_norm_sq]

lemma kernelLocalMass_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (f : kernelSmoothTests) :
    (∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)≤‖kernelSmoothTestsToL2 f‖^2 := by
  rw [kernelSmoothTestsToL2_norm_sq]
  exact kernelEuclideanProjection_integral_le S hS hpos hinj _
    (kernelSmoothTests_memLp f).norm.integrable_sq (fun _ => sq_nonneg _)

lemma euclideanVolume_le_heightCube_hyperbolic (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) :
    volume.restrict S≤ENNReal.ofReal (b^3) • hyperbolicEuclideanVolume.restrict S := by
  have hw : hyperbolicEuclideanVolume.restrict S=(volume.restrict S).withDensity hyperbolicDensity := by
    rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
      Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos]
  rw [hw]
  have hbd : (1 : EuclideanSpatial→ℝ≥0∞)≤ᵐ[volume.restrict S]
      ENNReal.ofReal (b^3) • hyperbolicDensity := by
    filter_upwards [ae_restrict_mem hS] with p hp
    have ht : 0<p 2 := hpos hp
    have hpow : (p 2)^3≤b^3 := pow_le_pow_left₀ ht.le (hheight p hp) 3
    have hreal : 1≤b^3*((p 2)^3)⁻¹ := by
      calc
        1=(p 2)^3*((p 2)^3)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ ht.ne')).symm
        _ ≤b^3*((p 2)^3)⁻¹ := mul_le_mul_of_nonneg_right hpow (by positivity)
    change (1 : ℝ≥0∞)≤ENNReal.ofReal (b^3)*ENNReal.ofReal (((p 2)^3)⁻¹)
    rw [←ENNReal.ofReal_mul (pow_nonneg hb 3)]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal
  simpa only [MeasureTheory.withDensity_one,MeasureTheory.withDensity_smul _ hyperbolicDensity_measurable] using
    (MeasureTheory.withDensity_mono hbd)

lemma kernelEuclideanProjection_volume_integral_le (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) (g : KernelQuotient→ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) (hgn : ∀q,0≤g q) :
    (∫p in S,g (kernelEuclideanProjection p))≤
      b^3*∫q,g q∂integralQuotientVolume globalKubotaKernel := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hgi := hm.integrable_comp_of_integrable hg.integrableOn
  have hh := integral_mono_measure
    (euclideanVolume_le_heightCube_hyperbolic S hS hpos b hb hheight)
    (Eventually.of_forall (fun p => hgn (kernelEuclideanProjection p)))
    (hgi.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure,ENNReal.toReal_ofReal (pow_nonneg hb 3)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (kernelEuclideanProjection_integral_le S hS hpos hinj g hg hgn) (pow_nonneg hb 3))

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

theorem completed_scaled_shape (ε k y H c B : ℝ) (hε : 0≤ε) (hk : 0<k)
    (hy : 0<y) (hH : 0<H) (hc : 0<c) (hcB : c≤B) (hB : 1≤B) :
    (k*(c*y))^ε*(k+c*y)/H≤B^(ε+1)*((k*y)^ε*(k+y)/H) := by
  have hB0 : 0<B := by linarith
  have hp : (k*(c*y))^ε≤B^ε*(k*y)^ε := by
    rw [show k*(c*y)=c*(k*y) by ring,Real.mul_rpow hc.le (mul_pos hk hy).le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hc.le hcB hε) (by positivity)
  have hs : k+c*y≤B*(k+y) := by nlinarith
  calc
    _ ≤ (B^ε*(k*y)^ε)*(B*(k+y))/H :=
      div_le_div_of_nonneg_right (mul_le_mul hp hs (by positivity) (by positivity)) hH.le
    _ = (B^ε*B)*((k*y)^ε*(k+y)/H) := by ring
    _ = _ := by rw [←Real.rpow_add_one hB0.ne']

theorem completedBranchScale_div {ι : Type*} [Fintype ι]
    (K X c : ℝ) (I F Q : Ideal O) (P : ι→Ideal O) (e : ι→Fin 3) :
    completedBranchScale K (X/c) I F Q P e=c*completedBranchScale K X I F Q P e := by
  unfold completedBranchScale
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem completed_reflected_fiber_fixed_scale
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃C : ℝ,0<C ∧ ∀K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e W
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_branch_series W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C*B^(2*deltaLoss+1),by positivity,?_⟩
  intro K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hk0 : 0<completedResidualScale K I Q := by linarith
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hX0 : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  rw [completedBranchScale_div]
  have hb := (h (completedResidualScale K I Q) (c*completedBranchScale K X I F Q P e)
    hk (mul_pos hc hy) P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hs := completed_scaled_shape (2*deltaLoss) (completedResidualScale K I Q)
    (completedBranchScale K X I F Q P e) _ c B (by positivity) hk0 hy
    (mul_pos (hj 0) (hj 2)) hc hcB hB
  have hcst := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hh := hs.trans (mul_le_mul_of_nonneg_left hcst (by positivity : 0≤B^(2*deltaLoss+1)))
  apply hb.trans
  have hfinal := mul_le_mul_of_nonneg_left hh hC.le
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale]) <;> ring

end

open ActualEisensteinCubic CanonicalQuadraticSieve

structure ReflectedBranchData (levelBound K : ℝ) (I F Q : Ideal O) where
  levelScale : ℝ
  levelScale_pos : 0<levelScale
  levelScale_le : levelScale≤levelBound
  primes : Finset (Ideal O)
  maximal : ∀p : primes,p.val.IsMaximal
  good : ∀p : primes,lambda∉p.val
  coprime : Pairwise (fun p r : primes => IsCoprime p.val r.val)
  divides : ∀p : primes,p.val∣I*Q
  nonresidual : ∀p : primes,¬p.val∣rowResidualPart I Q
  label : primes→Fin 3
  nColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  bColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  nBounds : ∀i,∀J∈nColumns i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2
  bBounds : ∀i,∀J∈bColumns i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1
  amplitude : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ
  amplitude_bound : ∀i,∀n∈nColumns i,∀b∈bColumns i,‖amplitude i n b‖≤1
  rowPhase : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ
  rowPhase_bound : ∀i k,‖rowPhase i k‖≤1

namespace ReflectedBranchData

def value {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedBranchData levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact ∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock (fun p : d.primes => p.val) d.good
    (fun p => completedLocalExponent I F p.val) d.label W
    (completedResidualScale K I Q) (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes => p.val) d.label)
    ρ q d.nColumns d.bColumns d.amplitude d.rowPhase i k

theorem energy_bound
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖d.value W X ρ q k‖^2)≤
        C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_fiber_fixed_scale W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨C,hC,?_⟩
  intro K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound

end ReflectedBranchData

structure ReflectedFiberData (rays : ℕ) (levelBound K : ℝ) (I F Q : Ideal O) where
  pool : Finset (Ideal O)
  maximal : ∀p : pool,p.val.IsMaximal
  divides : ∀p : pool,p.val∣I*Q
  branch : (Fin rays×(pool→Fin 6))→ReflectedBranchData levelBound K I F Q
  weight : (Fin rays×(pool→Fin 6))→ℂ
  weight_bound : ∀b,‖weight b‖≤1

namespace ReflectedFiberData

def value {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ :=
  ∑b,d.weight b*(d.branch b).value W X ρ q k

theorem finite_energy_bound {κ τ : Type*} [Fintype κ] [Fintype τ]
    (f : τ→κ→ℂ) (w : τ→ℂ) (hw : ∀t,‖w t‖≤1) (E : ℝ)
    (hf : ∀t,(∑k,‖f t k‖^2)≤E) :
    (∑k,‖∑t,w t*f t k‖^2)≤(Fintype.card τ:ℝ)^2*E := by
  have hpoint (k : κ) : ‖∑t,w t*f t k‖^2≤(Fintype.card τ:ℝ)*∑t,‖f t k‖^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : τ => (1:ℝ)) (fun t => ‖w t*f t k‖)
    have hn : ‖∑t,w t*f t k‖^2≤(∑t,‖w t*f t k‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    apply hn.trans
    apply (show (∑t,‖w t*f t k‖)^2≤(Fintype.card τ:ℝ)*∑t,‖w t*f t k‖^2 by simpa using h).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro t _
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw t)
  calc
    _ ≤ ∑k,(Fintype.card τ:ℝ)*∑t,‖f t k‖^2 := Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (Fintype.card τ:ℝ)*∑t,∑k,‖f t k‖^2 := by rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card τ:ℝ)*∑_t : τ,E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hf t)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem energy_bound
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖d.value W X ρ q k‖^2)≤
        C*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨Cb,hCb,hb⟩ := ReflectedBranchData.energy_bound W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨Cb*Cp,by positivity,?_⟩
  intro rays K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := finite_energy_bound
    (fun b => (d.branch b).value W X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖d.value W X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; ring

end ReflectedFiberData

open ActualEisensteinCubic CanonicalQuadraticSieve

theorem one_le_completedResidualScale (K : ℝ) (I Q : Ideal O)
    (hI : I≠0) (hIK : (Ideal.absNorm I:ℝ)≤K) : 1≤ completedResidualScale K I Q := by
  have hn : 1≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz =>
      squarefreeResidualPart_ne_zero (rowSimplePart I) Q (Ideal.absNorm_eq_zero_iff.mp hz))
  apply hn.trans
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  exact div_le_div_of_nonneg_right hIK (by positivity)

namespace ReflectedFiberData

def idealValue {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : Ideal O) : ℂ :=
  if h : J∈idealRange (completedResidualScale K I Q) then d.value W X ρ q ⟨J,h⟩ else 0

theorem idealValue_at {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : idealRange (completedResidualScale K I Q)) :
    d.idealValue W X ρ q J.val=d.value W X ρ q J := by
  simp only [idealValue,dite_eq_left J.property]

end ReflectedFiberData

def HasExactCompletedModels (rays : ℕ) (rows : Finset (Ideal O))
    (K X ρ q levelBound : ℝ) (F Q : Ideal O) (W : ℝ→ℂ) (Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ) : Prop :=
  ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
    (completedRowFiber rows Q A T).Nonempty →
    ∃I∈completedRowFiber rows Q A T,∃d : ReflectedFiberData rays levelBound K I F Q,
      ∀J∈completedRowFiber rows Q A T,
        completedT (Ψ J) W X=lengthScale*d.idealValue W X ρ q (rowResidualPart J Q)

theorem completed_energy_of_exact_models
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal O)) (F Q : Ideal O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ),HasExactCompletedModels rays rows K X ρ q levelBound F Q W Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) W X‖^2)≤
        C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^ε*
          (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨Cm,hCm,hm⟩ := ReflectedFiberData.energy_bound W a b ha hsupp hW deltaLoss ε ρ q levelBound hδ hε hρ hq hlevel
  obtain ⟨Co,hCo,ho⟩ := completed_outer_row_small_power ε hε
  refine ⟨Co*Cm,by positivity,?_⟩
  intro rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hexact
  let B : ℝ := Cm*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤B := by dsimp [B]; positivity
  have hblocks : ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber rows Q A T,‖completedT (Ψ I) W X‖^2)≤B/(Ideal.absNorm A:ℝ) := by
    intro A hA T hT
    by_cases hempty : (completedRowFiber rows Q A T).Nonempty
    · obtain ⟨I,hIf,d,hd⟩ := hexact A hA T hT hempty
      obtain ⟨hIr,hIA,hIT⟩ := Finset.mem_filter.mp hIf
      have hI := (hrows I hIr).1
      have hIK := (hrows I hIr).2
      have hk := one_le_completedResidualScale K I Q hI hIK
      have hdenergy := hm rays K X hK hX I F Q hI hQ hIK hk d
      have hembed := completedRowFiber_energy_le rows Q A T hbad K hrows
        (d.idealValue W X ρ q)
      have hscale : K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))=completedResidualScale K I Q := by
        simp only [completedResidualScale,hIA,hIT]
      rw [hscale] at hembed
      simp_rw [ReflectedFiberData.idealValue_at] at hembed
      have hsource : (∑J∈completedRowFiber rows Q A T,‖completedT (Ψ J) W X‖^2)=
          ‖lengthScale‖^2*∑J∈completedRowFiber rows Q A T,‖d.idealValue W X ρ q (rowResidualPart J Q)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hd J hJ,norm_mul,mul_pow]
      rw [hsource]
      apply (mul_le_mul_of_nonneg_left (hembed.trans hdenergy) (sq_nonneg _)).trans
      apply le_of_eq
      dsimp [B]
      rw [hIA]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
  have hh := ho rows Q hQ (fun I => ‖completedT (Ψ I) W X‖^2) B hB hblocks
  apply hh.trans_eq
  dsimp [B]
  ring

end CompletedGauss

end

end OAI

end

