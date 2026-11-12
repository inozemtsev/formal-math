module

public import Green64.Library.OAI.NumberTheory.DirichletL.MeanSquare.InputEnergy

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage -/

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem globalTwoPassage_quantitative
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
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := globalCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
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

def canonicalCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ K d x.2

end

theorem canonicalCubeFirstBlock_input_transfer
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
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
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
      ‖canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ K hK (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [canonicalCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
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
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
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

theorem canonicalTwoPassage_quantitative
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
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,canonicalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := canonicalCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
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

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid

theorem completed_branch_count_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(I : Ideal O),I≠0 → ∀{ι : Type*} [Fintype ι]
      (P : ι→Ideal O) [∀i,(P i).IsMaximal],Function.Injective P →
      (∀i,P i∣I) → (6:ℝ)^(2*Fintype.card ι)≤C*(Ideal.absNorm I:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/6) (by positivity)
  refine ⟨C^6,by positivity,?_⟩
  intro I hI ι _ P _ hinj hd
  let f : ι→primeSupport I := fun i => ⟨P i,by
    change P i∈(normalizedFactors I).toFinset
    exact Multiset.mem_toFinset.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr
      ⟨Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance,hd i⟩)⟩
  have hfi : Function.Injective f := by
    intro i j hij
    exact hinj (congrArg Subtype.val hij)
  have hcard : Fintype.card ι≤(primeSupport I).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hfi
  have htwo : (2:ℝ)^Fintype.card ι≤C*(Ideal.absNorm I:ℝ)^(ε/6) :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard).trans (hbound I hI)
  have hn : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  calc
    _ = (36:ℝ)^Fintype.card ι := by rw [pow_mul]; norm_num
    _ ≤ (64:ℝ)^Fintype.card ι := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^Fintype.card ι)^6 := by rw [←pow_mul, Nat.mul_comm, pow_mul]; norm_num
    _ ≤ (C*(Ideal.absNorm I:ℝ)^(ε/6))^6 := pow_le_pow_left₀ (by positivity) htwo 6
    _ = C^6*(Ideal.absNorm I:ℝ)^ε := by
      rw [mul_pow,←Real.rpow_mul_natCast hn.le]
      congr 2
      ring

end

open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum

theorem sum_completedRowFibers (S : Finset (Ideal O)) (Q : Ideal O) (f : Ideal O→ℝ) :
    (∑A∈S.image rowPowerfulPart,∑T∈S.image (fun I => rowMaskPart I Q),
      ∑I∈completedRowFiber S Q A T,f I)=∑I∈S,f I := by
  let mapPair : Ideal O→Ideal O×Ideal O := fun I => (rowPowerfulPart I,rowMaskPart I Q)
  have hm : ∀I∈S,mapPair I∈(S.image rowPowerfulPart)×ˢ(S.image (fun J => rowMaskPart J Q)) := by
    intro I hI
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  have hh := Finset.sum_fiberwise_of_maps_to hm f
  rw [Finset.sum_product] at hh
  simpa only [mapPair,Prod.mk.injEq,completedRowFiber] using hh

theorem rowMaskPart_image_card (S : Finset (Ideal O)) (Q : Ideal O) (hQ : Q≠0) :
    (S.image (fun I => rowMaskPart I Q)).card≤(idealDivisors Q).card := by
  apply Finset.card_le_card
  intro T hT
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hT
  exact (mem_idealDivisors hQ).mpr (rowMaskPart_dvd I Q)

theorem completed_outer_row_sum_bound (S : Finset (Ideal O)) (Q : Ideal O) (hQ : Q≠0)
    (f : Ideal O→ℝ) (C : ℝ) (hC : 0≤C)
    (hblocks : ∀A∈S.image rowPowerfulPart,∀T∈S.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber S Q A T,f I)≤C/(Ideal.absNorm A:ℝ)) :
    (∑I∈S,f I)≤1048576*((idealDivisors Q).card:ℝ)*C := by
  rw [←sum_completedRowFibers S Q f]
  calc
    _ ≤ ∑A∈S.image rowPowerfulPart,∑T∈S.image (fun I => rowMaskPart I Q),C/(Ideal.absNorm A:ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      exact Finset.sum_le_sum (fun T hT => hblocks A hA T hT)
    _ = ((S.image (fun I => rowMaskPart I Q)).card:ℝ)*C*
        ∑A∈S.image rowPowerfulPart,1/(Ideal.absNorm A:ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ ((S.image (fun I => rowMaskPart I Q)).card:ℝ)*C*1048576 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply powerful_inverse_norm_sum
      intro A hA
      obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
      exact rowPowerfulPart_powerful I
    _ ≤ ((idealDivisors Q).card:ℝ)*C*1048576 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (rowMaskPart_image_card S Q hQ)) hC) (by norm_num)
    _ = _ := by ring

theorem completed_outer_row_small_power (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀(S : Finset (Ideal O)) (Q : Ideal O),Q≠0 →
      ∀(f : Ideal O→ℝ) (C : ℝ),0≤C →
      (∀A∈S.image rowPowerfulPart,∀T∈S.image (fun I => rowMaskPart I Q),
        (∑I∈completedRowFiber S Q A T,f I)≤C/(Ideal.absNorm A:ℝ)) →
      (∑I∈S,f I)≤D*(Ideal.absNorm Q:ℝ)^ε*C := by
  obtain ⟨D,hD,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨1048576*D,by positivity,?_⟩
  intro S Q hQ f C hC hblocks
  apply (completed_outer_row_sum_bound S Q hQ f C hC hblocks).trans
  have hh := mul_le_mul_of_nonneg_right (hbound Q hQ) hC
  nlinarith

end CompletedGauss

open scoped BigOperators
namespace CompletedDyadic

def kernelTerm (t s A : ℝ) (n : ℕ) : ℝ := ((2:ℝ)^n)^s/(1+t*(2:ℝ)^n)^A

theorem pow_rpow_comm (s : ℝ) (n : ℕ) : ((2:ℝ)^n)^s=((2:ℝ)^s)^n := by
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem kernelTerm_nonneg (t s A : ℝ) (ht : 0<t) (n : ℕ) : 0≤kernelTerm t s A n := by
  unfold kernelTerm
  positivity

theorem kernelTerm_le_head (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤((2:ℝ)^s)^n := by
  rw [kernelTerm,←pow_rpow_comm]
  exact div_le_self (Real.rpow_nonneg (by positivity) _)
    (Real.one_le_rpow (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]) hA)

theorem kernelTerm_le_tail (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤t^(-A)*((2:ℝ)^(s-A))^n := by
  have hn : 0<(2:ℝ)^n := by positivity
  have htA : 0<t^A := Real.rpow_pos_of_pos ht _
  calc
    _ ≤ ((2:ℝ)^n)^s/(t*(2:ℝ)^n)^A := by
      unfold kernelTerm
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) hA)
    _ = t^(-A)*(((2:ℝ)^n)^s/((2:ℝ)^n)^A) := by
      rw [Real.mul_rpow ht.le hn.le,Real.rpow_neg ht.le]
      ring
    _ = _ := by rw [←Real.rpow_sub hn,pow_rpow_comm]

theorem ratio_lt_one (s A : ℝ) (hsA : s<A) : (2:ℝ)^(s-A)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsA)

theorem kernel_summable (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (hsA : s<A) :
    Summable (kernelTerm t s A) := by
  have hq := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s-A)) (ratio_lt_one s A hsA)
  exact (hq.mul_left (t^(-A))).of_nonneg_of_le (kernelTerm_nonneg t s A ht) (kernelTerm_le_tail t s A ht hA)

theorem kernel_sum_cutoff (t s A : ℝ) (ht : 0<t) (hs : 0<s) (hsA : s<A) (N : ℕ) :
    (∑'n : ℕ,kernelTerm t s A n)≤
      ((2:ℝ)^s)^N/((2:ℝ)^s-1)+t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
  have hA : 0≤A := by linarith
  have hp : 1<(2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hq : (2:ℝ)^(s-A)<1 := ratio_lt_one s A hsA
  have hq0 : 0≤(2:ℝ)^(s-A) := by positivity
  have hsum := kernel_summable t s A ht hA hsA
  have hhead : (∑n∈Finset.range N,kernelTerm t s A n)≤((2:ℝ)^s)^N/((2:ℝ)^s-1) := by
    apply (Finset.sum_le_sum (fun n _ => kernelTerm_le_head t s A ht hA n)).trans
    rw [geom_sum_eq hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hp.le)
  have htail : (∑'n : ℕ,kernelTerm t s A (n+N))≤
      t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
    have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A)*((2:ℝ)^(s-A))^N)
    have hb := Summable.tsum_le_tsum (fun n => show kernelTerm t s A (n+N)≤
      (t^(-A)*((2:ℝ)^(s-A))^N)*((2:ℝ)^(s-A))^n by
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using kernelTerm_le_tail t s A ht hA (n+N))
      ((summable_nat_add_iff N).mpr hsum) hgeo
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    simpa only [div_eq_mul_inv] using hb
  rw [←hsum.sum_add_tsum_nat_add N]
  exact add_le_add hhead htail

theorem kernel_sum_bound (s A : ℝ) (hs : 0<s) (hsA : s<A) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      Summable (kernelTerm t s A) ∧ (∑'n : ℕ,kernelTerm t s A n)≤C*t^(-s) := by
  let r : ℝ := (2:ℝ)^s
  let q : ℝ := (2:ℝ)^(s-A)
  have hr : 1< r := Real.one_lt_rpow (by norm_num) hs
  have hq : q<1 := ratio_lt_one s A hsA
  have hq0 : 0≤q := by dsimp [q]; positivity
  let C := r/(r-1)+1/(1-q)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  have hA : 0≤A := by linarith
  have hsum := kernel_summable t s A ht hA hsA
  refine ⟨hsum,?_⟩
  by_cases ht1 : 1≤t
  · have hg := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A))
    have hb := hsum.tsum_le_tsum (fun n => kernelTerm_le_tail t s A ht hA n) hg
    change (∑'n : ℕ,kernelTerm t s A n)≤∑'n : ℕ,t^(-A)*q^n at hb
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    calc
      _ ≤ t^(-A)/(1-q) := by simpa only [div_eq_mul_inv] using hb
      _ ≤ t^(-s)/(1-q) := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by linarith)
      _ ≤ C*t^(-s) := by
        have hp : 0≤ r/(r-1)*t^(-s) := by positivity
        calc
          _ ≤ r/(r-1)*t^(-s)+t^(-s)/(1-q) := le_add_of_nonneg_left hp
          _ = C*t^(-s) := by dsimp [C]; ring
  · have ht_le : t≤1 := le_of_not_ge ht1
    have hit : 1≤1/t := (one_le_div ht).mpr ht_le
    obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hit (by norm_num : (1:ℝ)<2)
    have hheadpow : r^(N+1)≤ r*t^(-s) := by
      change ((2:ℝ)^s)^(N+1)≤(2:ℝ)^s*t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ ((2:ℝ)/t)^s := by
          apply Real.rpow_le_rpow (by positivity) _ hs.le
          rw [pow_succ]
          calc
            _ ≤ (1/t)*2 := mul_le_mul_of_nonneg_right hN (by norm_num)
            _ = 2/t := by ring
        _ = _ := by rw [Real.div_rpow (by norm_num) ht.le,Real.rpow_neg ht.le]; ring
    have htailpow : t^(-A)*q^(N+1)≤t^(-s) := by
      change t^(-A)*((2:ℝ)^(s-A))^(N+1)≤t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ t^(-A)*(1/t)^(s-A) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hN'.le (by linarith)) (by positivity)
        _ = t^(-A)*t^(-(s-A)) := by rw [one_div,Real.inv_rpow ht.le,←Real.rpow_neg ht.le]
        _ = t^(-s) := by rw [←Real.rpow_add ht]; congr 1; ring
    have hb := kernel_sum_cutoff t s A ht hs hsA (N+1)
    change (∑'n : ℕ,kernelTerm t s A n)≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) at hb
    calc
      _ ≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) := hb
      _ ≤ (r*t^(-s))/(r-1)+t^(-s)/(1-q) := add_le_add
        (div_le_div_of_nonneg_right hheadpow (by linarith))
        (div_le_div_of_nonneg_right htailpow (by linarith))
      _ = C*t^(-s) := by dsimp [C]; ring

end CompletedDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.OutsideIdeals -/

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem idealRowSum_filter_squarefree (F : Finset (Ideal O))
    (hFp : ∀ I ∈ F, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      goodLambda ∉ P) {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (z : O) :
    idealRowSum F hFp hFg χ W z =
    idealRowSum (F.filter Squarefree)
      (fun I hI => hFp I (Finset.mem_filter.mp hI).1)
      (fun I hI => hFg I (Finset.mem_filter.mp hI).1) χ W z := by
  unfold idealRowSum
  calc
    _ = ∑ I ∈ F.filter Squarefree,
        ShortDraftHeckeBridge.baseChangeWeight χ I * W (Ideal.absNorm I) *
          idealSexticRow F hFp hFg I z := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro I hIF hIn
      have hs : ¬ Squarefree I := fun h => hIn (Finset.mem_filter.mpr ⟨hIF,h⟩)
      rw [baseChangeWeight_zero_of_not_squarefree χ I hs, zero_mul, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [idealSexticRow_ambient F (F.filter Squarefree) hFp
        (fun J hJ => hFp J (Finset.mem_filter.mp hJ).1) hFg
        (fun J hJ => hFg J (Finset.mem_filter.mp hJ).1) I
        (Finset.mem_filter.mp hI).1 hI z]

def outsideSquarefreeIdeals (S : Finset (Ideal O)) (D : ℕ) : Finset (Ideal O) :=
  (outsideIdealsUpTo S D).filter Squarefree

theorem outsideSquarefree_admissible (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) : ∀ I ∈ outsideSquarefreeIdeals S D, Admissible I := by
  intro I hI
  obtain ⟨ho,hs⟩ := Finset.mem_filter.mp hI
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  refine ⟨hn,hs,?_⟩
  intro P hP
  obtain ⟨hp,hd⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hPb
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P (hbad hPb) hd

theorem outside_good (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) :
    ∀ I ∈ outsideIdealsUpTo S D,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P := by
  apply outsideIdealsUpTo_good S D
  apply badPrime_cover_of_lambdaIdeal_mem
  exact hbad (Finset.mem_insert_self _ _)

theorem outside_pool_product_not_dvd (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P ∈ S, Prime P) (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    ∀ P ∈ S, ¬ P ∣ ∏ i ∈ T,i.val := by
  intro P hPS hdiv
  obtain ⟨i,hi,hPi⟩ := ((hSp P hPS).dvd_finsetProd_iff
    (fun i : primePool (outsideSquarefreeIdeals S D) => i.val)).mp hdiv
  obtain ⟨I,hIF,hiI⟩ := mem_primePool_iff.mp i.property
  have ho : I ∈ outsideIdealsUpTo S D := (Finset.mem_filter.mp hIF).1
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  have hd : i.val ∣ I := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hiI |>.2
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (hPi.trans hd)

theorem selectedIdealTest_outside (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hs : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D)
    (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    selectedIdealTest (outsideSquarefreeIdeals S D) (fun n => W (n/Z)) T =
    W (primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) T/Z) := by
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  rw [poolPrimary_norm F hF T]
  unfold selectedIdealTest
  by_cases hw : W ((Ideal.absNorm (∏ i ∈ T,i.val) : ℝ)/Z)=0
  · split_ifs
    · rfl
    · exact hw.symm
  · rw [ite_eq_left]
    have ha := poolProduct_admissible F hF T
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,outside_pool_product_not_dvd S D hSp T⟩,ha.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (fun hz => ha.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact_mod_cast ((div_le_iff₀ hZ).mp (hs _ hw)).trans hD

theorem outside_idealRowSum_initial_energy {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (W : ℝ → ℂ) (a b Z : ℝ) (ha : 0 < a) (hZ : 0 < Z)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hD : b*Z ≤ D) (z : O) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    ‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2/Z =
    ‖mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ (normCharacter χ) 1
      (normalizedColumn (poolPrimary F)
        (fun T => initialLogProfile W a b ha hs hW (columnLog (poolPrimary F) Z T))) z‖^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [idealRowSum_filter_squarefree]
  change ‖idealRowSum F (fun I hI => (hF I hI).1)
    (fun I hI P hP => ((hF I hI).2.2 P hP).1) χ (fun n => W (n/Z)) z‖^2/Z = _
  rw [idealRowSum_eq_mobiusRow F hF]
  have ht : selectedIdealTest F (fun n => W (n/Z)) =
      fun T => W (primeProductNorm (poolPrimary F) T/Z) := by
    funext T
    exact selectedIdealTest_outside S D hbad hSp W b Z hZ (fun t ht => (hs ht).2) hD T
  rw [ht]
  exact (mobiusRow_initial_energy (poolPrimary F) (poolPrimary_good F hF)
    (poolPrimary_ne_zero F hF) Finset.univ (normCharacter χ) 1 z Z hZ W a b ha hs hW).symm

end InitialMeanSquare

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource -/

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare

section
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_source {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (W : ℝ → ℂ) (a b Z Y : ℝ)
    (ha : 0 < a) (hZ : 0 < Z) (hY : 0 < Y)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hD : b*Z ≤ D) (T : Finset O)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0)
    (K : Finset (primePool (outsideSquarefreeIdeals S D)) →
      Finset (primePool (outsideSquarefreeIdeals S D)) → Finset O) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p, poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid (normCharacter χ)
    (∑ z ∈ T, ‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z ≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y (fun C E => (K C E).erase 0)‖+
      (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K).re+
      ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K‖-‖G ∅‖^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p, poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  have he := mobiusRow_finite_source p hg hp hinj (poolPrimary_odd F hF) Finset.univ
    (normCharacter χ) 1 G Y hY T hT hT0 K
  calc
    _ = ∑ z ∈ T, ‖mobiusRow p hg Finset.univ (normCharacter χ) 1 G z‖^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      exact outside_idealRowSum_initial_energy χ S D hbad hSp W a b Z ha hZ hs hW hD z
    _ ≤ _ := he

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma initial_actual_row_norm (x : SecondExpansionData ι) :
    ‖eisEmbedding (actualSecondRow p ∅ x.divisor x.frequency)‖^2 =
      elementNorm (sourceObservation p x).1 := by
  simp only [actualSecondRow, sourceObservation, elementNorm,
    map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm,
    primeProductNorm, Finset.prod_empty, map_one, norm_one, one_pow, one_mul]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma initialLogIndex_eq_second (x : SecondExpansionData ι) :
    initialLogIndex p x = secondLogIndex p ∅ x := by
  simp only [initialLogIndex, secondLogIndex, initial_actual_row_norm]

theorem initial_sector_coordinates (hp : ∀ i, p i ≠ 0)
    (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (Z M : ℝ) (hZ : 0 < Z) (j : SecondLogIndex)
    (x : SecondExpansionData ι) (hx : x ∈ secondLogSector p ∅ F K R Z M j) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    |sourceLogZ p Z X x| ≤ 2 ∧ |sourceLogE p (secondLogE j) x| ≤ 2 ∧
    |sourceLogV p (secondLogV j) x| ≤ 2 ∧ |sourceLogK p (secondLogK j) x| ≤ 2 := by
  obtain ⟨hx',hj⟩ := Finset.mem_filter.mp hx
  obtain ⟨hG,hE,hV,hk,hkf,hR,hs⟩ := secondSupportedSector_mem p F K R Z M x hx'
  have hsec := secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
    (Finset.mem_filter.mp hx').1
  have heq : initialLogIndex p x=j := (initialLogIndex_eq_second p x).trans hj
  have hc := initial_log_coordinates p hp Z hZ x hE hk
  dsimp only at hc ⊢
  rw [heq,quotient_norm_fixed p _ x hsec] at hc
  simpa only [sourceLogZ, sourceLogE, sourceLogV, sourceLogK, elementNorm,
    primeSubsetGenerator_norm_eq_productNorm] using hc

end

theorem initial_bin_transfer
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
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (Z H M : ℝ) (j : SecondLogIndex),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        let s := secondLogSector p ∅ F K R Z M j
        let X := initialLogColumn Z (primeProductNorm p R) j
        let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
        ∃ B : Frequency → ℝ,
          (∀ q, 0 ≤ B q) ∧
          (∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) W H‖ ≤
          (C*H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_sector_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j hZ hH hΨ
  dsimp only
  let s := secondLogSector p ∅ F K R Z M j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j hx)
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp hx).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x hx).1) (fun x hx => (hcoords x hx).2.1)
    (fun x hx => (hcoords x hx).2.2.1) (fun x hx => (hcoords x hx).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end InitialMeanSquare

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

theorem sum_powerset_split {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→β) :
    (∑S∈F.powerset,f S)=∑A∈B.powerset,∑U∈(F\B).powerset,f (A∪U) := by
  have hsplit (S : Finset ι) : S∩B∪S\B=S := by
    ext i
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have he : (∑S∈F.powerset,f S)=
      ∑AU∈B.powerset ×ˢ (F\B).powerset,f (AU.1∪AU.2) := by
    apply Finset.sum_bij (fun S _ => (S∩B,S\B))
    · intro S hS
      rw [Finset.mem_product,Finset.mem_powerset,Finset.mem_powerset]
      refine ⟨Finset.inter_subset_right,?_⟩
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) (Finset.mem_sdiff.mp hi).1,(Finset.mem_sdiff.mp hi).2⟩
    · intro S hS T hT he
      have hi := congrArg (fun AU : Finset ι×Finset ι => AU.1∪AU.2) he
      simpa only [hsplit] using hi
    · intro AU hAU
      rcases Finset.mem_product.mp hAU with ⟨hA,hU⟩
      have hAB := Finset.mem_powerset.mp hA
      have hUFB := Finset.mem_powerset.mp hU
      refine ⟨AU.1∪AU.2,Finset.mem_powerset.mpr (Finset.union_subset (hAB.trans hB) (hUFB.trans Finset.sdiff_subset)),?_⟩
      apply Prod.ext <;> ext i
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_inter,Finset.mem_union]
        tauto
      · have h1 : i∈AU.1 → i∈B := fun hi => hAB hi
        have h2 : i∈AU.2 → i∉B := fun hi => (Finset.mem_sdiff.mp (hUFB hi)).2
        simp only [Finset.mem_sdiff,Finset.mem_union]
        tauto
    · intro S hS
      rw [hsplit]
  simpa only [Finset.sum_product] using he

theorem sum_pair_split_cube {β : Type*} [AddCommMonoid β]
    (F B : Finset ι) (hB : B⊆F) (f : Finset ι→Finset ι→β) :
    (∑S∈F.powerset,∑T∈F.powerset,f S T)=
      ∑A₂∈B.powerset,∑A₁∈B.powerset,∑C∈(F\B).powerset,
        ∑N∈((F\B)\C).powerset,∑P∈((F\B)\C).powerset,
          if Disjoint N P then f ((A₂∪C)∪N) ((A₁∪C)∪P) else 0 := by
  rw [sum_powerset_split F B hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  simp_rw [sum_powerset_split F B hB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  rw [sum_pair_eq_overlap]
  simp only [Finset.union_assoc]

end FiniteOverlapDecomposition

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def canonicalSourceCoefficient (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏i∈S,p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4 * H S

theorem canonicalSourceCoefficient_union
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (D S : Finset ι) (hd : Disjoint D S) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f H (D∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) D *
      (columnCoefficient p hp hcop hg S *
        multiplicativeCoreColumn p Ψ m (fun U => H (D∪U)) S *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (∏i∈D,p i)^4 *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f^4) := by
  have hA := columnCoefficient_union_row_four p hp hcop hg hpr S D hd.symm
  rw [Finset.union_comm S D] at hA
  simp only [canonicalSourceCoefficient,hA,Finset.prod_union hd,map_mul,
    row_union _ hg D S hd,mask_union _ hg D S hd,mul_pow,multiplicativeCoreColumn]
  ring

theorem canonicalCube_pair_row
    (B C N P : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hcover : ∀ i∈B,0<v₁ i+v₂ i)
    (hCB : Disjoint C B) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N B) (hPB : Disjoint P B) (hNP : Disjoint N P)
    (z : O) :
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
      (((B.filter fun i => ε₂ i)∪C)∪N) z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg
        (((B.filter fun i => ε₁ i)∪C)∪P) z *
      star (multiplicityRow (fun i => Ideal.span {p i}) hg B v₂ z^3) *
      multiplicityRow (fun i => Ideal.span {p i}) hg B v₁ z^3 =
    rowCoprimeMask (fun i => Ideal.span {p i})
      (C∪cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
    blockRow p hg ((N∪P)∪cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
      (threeBlockExponent N P (fun i => v₁ i+v₂ i) ε₁ ε₂) z := by
  have hA₁C : Disjoint (B.filter fun i => ε₁ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂C : Disjoint (B.filter fun i => ε₂ i) C := hCB.symm.mono_left (Finset.filter_subset _ _)
  have hA₁P : Disjoint (B.filter fun i => ε₁ i) P := hPB.symm.mono_left (Finset.filter_subset _ _)
  have hA₂N : Disjoint (B.filter fun i => ε₂ i) N := hNB.symm.mono_left (Finset.filter_subset _ _)
  have hCp : Disjoint C (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) :=
    hCB.mono_right (Finset.filter_subset _ _)
  have hsel : cubePairRow (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂ z =
      rowCoprimeMask (fun i => Ideal.span {p i}) (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
      blockRow p hg (cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂)
        (fun i => (conductorExponent (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i)).val) z := by
    exact cubePairRow_conductor_selection (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂
      (fun i hi => by have := hcover i hi;omega) z
  rw [row_union _ hg _ N (Finset.disjoint_union_left.mpr ⟨hA₂N,hNC.symm⟩),
    row_union _ hg _ P (Finset.disjoint_union_left.mpr ⟨hA₁P,hPC.symm⟩),
    row_union _ hg _ C hA₂C,row_union _ hg _ C hA₁C]
  simp only [star_mul]
  calc
    _ = (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg C z)*
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg C z)*
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N z)*
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P z)*
      cubePairRow (fun i => Ideal.span {p i}) hg B v₁ v₂ ε₁ ε₂ z := by
        simp only [cubePairRow];ring
    _ = _ := by
      rw [ActualEisensteinCubic.finiteSquarefreeRow_self_pair (fun i => Ideal.span {p i}) hg C z,
        hsel,
        threeBlockRow_factor p hg N P B hNP hNB hPB,
        mask_union _ hg C _ hCp]
      ring

theorem canonicalSourceCoefficient_cube_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2∣p i-1) (Ψ : O→*ℂ) (m f : O)
    (H : Finset ι→ℂ) (B C S : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (hCB : Disjoint C B) (hSC : Disjoint S C) (hSB : Disjoint S B) :
    let A := B.filter (fun i => if negative then ε₂ i else ε₁ i)
    canonicalSourceCoefficient p hp hcop hg Ψ m f H ((A∪C)∪S) =
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) (A∪C) *
      (columnCoefficient p hp hcop hg S *
        originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => H ((A∪C)∪U)))
          (∏i∈C,p i) f S) := by
  dsimp only
  have hAC : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) C :=
    hCB.symm.mono_left (Finset.filter_subset _ _)
  have hAS : Disjoint (B.filter fun i => if negative then ε₂ i else ε₁ i) S :=
    hSB.symm.mono_left (Finset.filter_subset _ _)
  rw [canonicalSourceCoefficient_union p hp hcop hg hpr Ψ m f H _ S
    (Finset.disjoint_union_left.mpr ⟨hAS,hSC.symm⟩)]
  have hA : (∏i∈B.filter (fun i => if negative then ε₂ i else ε₁ i),p i) =
      aLabel p B (if negative then ε₂ else ε₁) := by
    cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,aLabel,primeProduct,
      Finset.prod_filter,bit]
    all_goals
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs <;> simp_all
  rw [Finset.prod_union hAC,hA]
  simp only [originalLabelColumn,cubeRadical,commonProduct_mask p hg hinj S B,ite_eq_left hSB,mul_one]
  ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalPairMode (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (d h : O) : ℂ :=
  (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖:ℂ))*
    paperRadialFourier W (K*‖eisEmbedding h‖^2/
      (‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h

lemma canonicalPairMode_summable (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    Summable (canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d) := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  let t := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  have ht : 0<t := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hs : Summable (fun h : O => paperRadialFourier W (t*‖eisEmbedding h‖^2)*star (blockRow p hg S e h)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W t ht)
    intro h
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (blockRow_norm_le_one p hg S e h)
  let a : ℂ := (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖eisEmbedding (∏i∈S,p i)‖:ℂ))*
    (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S => p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val))*blockRow p hg S e d
  apply (hs.mul_left a).congr
  intro h
  dsimp only [canonicalPairMode,threeGaussRowFactor,a,t,S,e]
  have ht' : K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂))*
      ‖eisEmbedding h‖^2 = K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) := by ring
  rw [ht']
  ring

lemma actualFirstKernel_summable (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    Summable (actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d) := by
  apply summable_sum
  intro N hN
  apply summable_sum
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    change Summable (canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d)
    exact
      canonicalPairMode_summable p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd
  · simp only [hNP,ite_false]
    exact summable_zero

theorem canonicalPair_first_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (M N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) :
    (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
      (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P))*
      (∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i}) M z*
        blockRow p hg ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)
          (threeBlockExponent N P v ε₁ ε₂) z*W (‖eisEmbedding z‖^2/K)) =
    ∑D∈M.powerset,(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/
      (primeProductNorm p D:ℂ)*
      ∑'h:O,canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  have he : ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
    intro i hi
    by_cases hn:i∈N
    · simp [threeBlockExponent,hn]
    by_cases hp':i∈P
    · simp [threeBlockExponent,hn,hp']
    · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
      simp only [threeBlockExponent,ite_eq_right hn,ite_eq_right hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  have he6 : ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hcop hg hc M _ _ he he6 W K hK]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  simp only [←tsum_mul_left]
  apply tsum_congr
  intro h
  dsimp only [canonicalPairMode,threeGaussRowFactor]
  rw [SecondPassArithmetic.primeSubsetGenerator_norm_eq_productNorm p D]
  simp only [primeProductNorm]
  ring

lemma tsum_actualFirstKernel (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)=
      ∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
        ∑'h:O,canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0 := by
  have hs (N P : Finset ι) : Summable (fun h:O => if Disjoint N P then
      canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0) := by
    by_cases hNP : Disjoint N P
    · simp only [hNP,ite_true]
      exact canonicalPairMode_summable p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd
    · simp only [hNP,ite_false]
      exact summable_zero
  change (∑'h:O,∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
      canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN => summable_sum (fun P hP => hs N P))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun P hP => hs N P)]
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs <;> simp

def disjointCanonicalSource (F M B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ K : ℝ) : ℂ :=
  ∑N∈F.powerset,∑P∈F.powerset,if Disjoint N P then
    (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
      (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P))*
      (∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i}) M z*
        blockRow p hg ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)
          (threeBlockExponent N P v ε₁ ε₂) z*W (‖eisEmbedding z‖^2/K)) else 0

theorem disjointCanonicalSource_poisson
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (F M B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) :
    disjointCanonicalSource p hp hcop hg F M B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K =
    ∑D∈M.powerset,(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/
      (primeProductNorm p D:ℂ)*
      ∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  simp_rw [tsum_actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK _
    (primeSubsetGenerator_ne_zero _ _)]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    exact canonicalPair_first_poisson p hp hcop hg hinj hc M N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK
  · simp only [hNP,ite_false,mul_zero,Finset.sum_const_zero]

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open MixedCrossSeparation (columnCoefficient)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def canonicalCubeSourcePair (B S T : Finset ι) (v₁ v₂ : ι→ℕ)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  star (canonicalSourceCoefficient p hp hcop hg Ψ₁ m₁ f H₁ S)*
    canonicalSourceCoefficient p hp hcop hg Ψ₂ m₂ f H₂ T*
    ∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg B v₂ z^3)*
      multiplicityRow (fun i=>Ideal.span {p i}) hg B v₁ z^3)*W (‖eisEmbedding z‖^2/K)

def canonicalCubeOuter (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) : ℂ :=
  star (canonicalSourceCoefficient p hp hcop hg Ψ₁ m₁ f (fun _=>1) (b.rightDivisor∪C))*
    canonicalSourceCoefficient p hp hcop hg Ψ₂ m₂ f (fun _=>1) (b.leftDivisor∪C)

def canonicalCubeResidual (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) : Finset ι→ℂ :=
  originalLabelColumn p hg b.support b.leftBit b.rightBit negative
    (multiplicativeCoreColumn p Ψ m (fun S=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪S)))
    (∏i∈C,p i) f

def canonicalCubeBeforePoisson (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    disjointCanonicalSource p hp hcop hg (pool\(b.support∪C))
      (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
      b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
      W (fun _=>1) (fun _=>1) 1 1 K

lemma cube_filter_left (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.leftBit i)=b.leftDivisor := by
  ext i
  simp only [CubeCoordinates.leftBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.1 hi)

lemma cube_filter_right (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.rightBit i)=b.rightDivisor := by
  ext i
  simp only [CubeCoordinates.rightBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.2 hi)

theorem canonicalCubeSourcePair_factor
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1)
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N P : Finset ι)
    (hCB : Disjoint C b.support) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N b.support) (hPB : Disjoint P b.support) (hNP : Disjoint N P)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeSourcePair p hp hcop hg b.support ((b.rightDivisor∪C)∪N) ((b.leftDivisor∪C)∪P)
      b.leftExponent b.rightExponent Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
    canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
      (star (columnCoefficient p hp hcop hg N*canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ N)*
        (columnCoefficient p hp hcop hg P*canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂ P))*
      ∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i})
        (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit) z*
        blockRow p hg ((N∪P)∪cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
          (threeBlockExponent N P (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) z*
        W (‖eisEmbedding z‖^2/K) := by
  have hN := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₁ m₁ f H₁
    b.support C N b.leftBit b.rightBit true hCB hNC hNB
  have hP := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₂ m₂ f H₂
    b.support C P b.leftBit b.rightBit false hCB hPC hPB
  simp only [Bool.false_eq_true,ite_true,ite_false,cube_filter_left b hb,cube_filter_right b hb] at hN hP
  have hz (z : O) := canonicalCube_pair_row p hg b.support C N P b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos hCB hNC hPC hNB hPB hNP z
  simp only [cube_filter_left b hb,cube_filter_right b hb] at hz
  simp only [canonicalCubeSourcePair,hN,hP,star_mul,canonicalCubeOuter,canonicalCubeResidual]
  simp only [Bool.false_eq_true,ite_true,ite_false]
  simp_rw [hz]
  ring

def canonicalCubeCorrelation (pool B : Finset ι) (v₁ v₂ : ι→ℕ)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑S∈pool.powerset,∑T∈pool.powerset,
    canonicalCubeSourcePair p hp hcop hg B S T v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K

theorem canonicalCubeCorrelation_eq_blocks
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (v₁ v₂ : ι→₀ℕ)
    (hB : v₁.support∪v₂.support⊆pool)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      ∑A₂∈(v₁.support∪v₂.support).powerset,∑A₁∈(v₁.support∪v₂.support).powerset,
        ∑C∈(pool\(v₁.support∪v₂.support)).powerset,
          canonicalCubeBeforePoisson p hp hcop hg pool ⟨v₁,v₂,A₁,A₂⟩ C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K := by
  unfold canonicalCubeCorrelation
  rw [FiniteOverlapDecomposition.sum_pair_split_cube pool _ hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  apply Finset.sum_congr rfl
  intro C hC
  let b : CubeCoordinates ι:=⟨v₁,v₂,A₁,A₂⟩
  have hb : b.Admissible:=⟨Finset.mem_powerset.mp hA₁,Finset.mem_powerset.mp hA₂⟩
  have hCB : Disjoint C b.support := Finset.disjoint_left.mpr (fun i hiC hiB =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hiC)).2 hiB)
  have hpool : (pool\(v₁.support∪v₂.support))\C=pool\(b.support∪C) := by
    ext i
    simp only [CubeCoordinates.support,b,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hpool]
  change _=canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  simp only [canonicalCubeBeforePoisson,disjointCanonicalSource,Finset.mul_sum,one_mul]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    have hNC : Disjoint N C:=Finset.disjoint_left.mpr (fun i hiN hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_right _ hiC))
    have hPC : Disjoint P C:=Finset.disjoint_left.mpr (fun i hiP hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_right _ hiC))
    have hNB : Disjoint N b.support:=Finset.disjoint_left.mpr (fun i hiN hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_left _ hiB))
    have hPB : Disjoint P b.support:=Finset.disjoint_left.mpr (fun i hiP hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_left _ hiB))
    simpa only [mul_assoc,b,CubeCoordinates.support] using canonicalCubeSourcePair_factor p hp hcop hg hinj hpr b hb C N P
      hCB hNC hPC hNB hPB hNP Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  · simp only [hNP,ite_false,mul_zero]

theorem canonicalCubeBeforePoisson_eq_all_modes
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
        ∑'h:O,actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
          W (fun _=>1) (fun _=>1) 1 1 K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  unfold canonicalCubeBeforePoisson
  rw [disjointCanonicalSource_poisson p hp hcop hg hinj hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK]

lemma canonicalSourceCoefficient_norm_le_one
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ:O→*ℂ) (hΨ:∀u,‖Ψ u‖≤1) (m f:O) (S:Finset ι) :
    ‖canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _=>1) S‖≤1 := by
  have hm : ‖rowCoprimeMask (fun i=>Ideal.span {p i}) S m‖≤1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  simp only [canonicalSourceCoefficient,norm_mul,norm_pow,mul_one,
    columnCoefficient_norm_one p hp hcop hg hc,one_mul]
  calc
    ‖Ψ (∏i∈S,p i)‖*‖rowCoprimeMask (fun i=>Ideal.span {p i}) S m‖*
      ‖finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S f‖^4 ≤ (1:ℝ)*1*1^4 := by
      exact mul_le_mul
        (mul_le_mul (hΨ _) hm (norm_nonneg _) (by norm_num))
        (pow_le_pow_left₀ (norm_nonneg _) (finiteSquarefreeRow_norm_le_one _ hg _ _) 4)
        (pow_nonneg (norm_nonneg _) 4) (by norm_num)
    _ = 1 := by norm_num

lemma canonicalCubeOuter_norm_le_one
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (b:CubeCoordinates ι) (C:Finset ι) (Ψ₁ Ψ₂:O→*ℂ)
    (hΨ₁:∀u,‖Ψ₁ u‖≤1) (hΨ₂:∀u,‖Ψ₂ u‖≤1) (m₁ m₂ f:O) :
    ‖canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f‖≤1 := by
  simp only [canonicalCubeOuter,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (canonicalSourceCoefficient_norm_le_one p hp hcop hg hc Ψ₁ hΨ₁ m₁ f _)).trans
    (canonicalSourceCoefficient_norm_le_one p hp hcop hg hc Ψ₂ hΨ₂ m₂ f _)

end SecondPassArithmetic

end

end OAI

end

