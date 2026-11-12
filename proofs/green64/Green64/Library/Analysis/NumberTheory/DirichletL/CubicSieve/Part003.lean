module

public import Green64.Library.OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy -/

section

namespace OAI

noncomputable section

namespace FirstPassCubeLabels

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

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

def actualFirstKernel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ lengthScale : ℝ) (d h : O) : ℂ :=
  ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
    (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
    paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
      (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0

def firstColumnEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
    rayIdealEnergy p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (normalizedColumn p C) V (columnLog p X) t d) negative h

theorem firstColumnEnergy_nonneg {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ)) :
    0 ≤ firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative C V X d h b := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (rayIdealEnergy_nonneg _ _ _ _ _ _)

theorem actual_first_kernel_energy_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := actual_first_kernel_to_ideal_rows p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  obtain ⟨b, hi, hb, _, he⟩ := hs lengthScale hL d h hd hh
  refine ⟨b, hi, hb, ?_⟩
  let D₁ := fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
    (normalizedColumn p C₁) V₁ (columnLog p X₁) t d
  let D₂ := fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
    (normalizedColumn p C₂) V₂ (columnLog p X₂) t d
  have hiE := cube_integral_norm_le_energy p hg F D₁ D₂
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  change actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h = _ at he
  rw [he, norm_mul]
  have hn : ‖(lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)‖ =
      lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
      abs_of_nonneg (norm_nonneg _)]
  rw [hn, mul_assoc]
  exact mul_le_mul_of_nonneg_left hiE (div_nonneg hL.le (norm_nonneg _))

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)

section Local
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i)

theorem row_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    finiteSquarefreeRow P hg (S ∪ T) a =
      finiteSquarefreeRow P hg S a * finiteSquarefreeRow P hg T a := by
  exact Finset.prod_union hd

include hg in
theorem mask_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    rowCoprimeMask P (S ∪ T) a = rowCoprimeMask P S a * rowCoprimeMask P T a := by
  simp only [← row_sixth P hg, row_union P hg S T hd, mul_pow]

omit [DecidableEq ι] in
theorem row_four_star (S : Finset ι) (f h : O) :
    finiteSquarefreeRow P hg S f ^ 4 * star (finiteSquarefreeRow P hg S h) =
      star (finiteSquarefreeRow P hg S (h * f ^ 2)) := by
  have hf : star (finiteSquarefreeRow P hg S (f ^ 2)) =
      finiteSquarefreeRow P hg S f ^ 4 := by
    rw [row_pow, star_pow, finiteSquarefreeRow_conj_as_row_label]
    calc
      _ = finiteSquarefreeRow P hg S f ^ 4 * finiteSquarefreeRow P hg S f ^ 6 := by ring
      _ = _ := by
        rw [row_sixth]
        simpa only [pow_one] using row_power_mul_mask_power P hg S f 4 1 (by decide)
  rw [finiteSquarefreeRow_mul, star_mul, hf]

def beforeDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) : ℂ :=
  finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S d *
    (rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
    finiteSquarefreeRow P hg S f ^ 4

def afterDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d : O) (S : Finset ι) : ℂ :=
  finiteSquarefreeRow P hg S (c * jLabel p B v ε₁ ε₂) ^ 4 *
    finiteSquarefreeRow P hg S d * rowCoprimeMask P S (b0Label p B v ε₁ ε₂)

theorem beforeDilationLabel_union {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O)
    (S T : Finset ι) (hd : Disjoint S T) :
    beforeDilationLabel P hg p B v ε₁ ε₂ side c d f (S ∪ T) =
      beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S *
      beforeDilationLabel P hg p B v ε₁ ε₂ side c d f T := by
  simp only [beforeDilationLabel, row_union P hg S T hd, mask_union P hg S T hd, mul_pow]
  ring

omit [DecidableEq ι] in
theorem beforeDilationLabel_norm_le_one {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) :
    ‖beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S‖ ≤ 1 := by
  have hm : ‖rowCoprimeMask P S (cubeRadical p B)‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  simp only [beforeDilationLabel, norm_mul, norm_pow]
  calc
    _ ≤ (1:ℝ)^4 * 1 * (1 * 1^4 * 1) * 1^4 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one P hg S _
    _ = 1 := by norm_num

omit [DecidableEq ι] in
theorem beforeDilationLabel_star_row {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (side : Bool) (c d f h : O) (S : Finset ι) :
    beforeDilationLabel P hg p B v ε₁ ε₂ side c d f S *
      star (finiteSquarefreeRow P hg S h) =
    afterDilationLabel P hg p B v ε₁ ε₂ c d S *
      star (finiteSquarefreeRow P hg S (h * f^2 * dilationLabel p B v ε₁ ε₂)) := by
  unfold beforeDilationLabel afterDilationLabel
  calc
    _ = (finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S d) *
      ((rowCoprimeMask P S (cubeRadical p B) *
        finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
        (finiteSquarefreeRow P hg S f ^ 4 * star (finiteSquarefreeRow P hg S h))) := by ring
    _ = _ := by
      rw [row_four_star, first_pass_after_dual_dilation P hg S p B v ε₁ ε₂ hv side]
      simp only [finiteSquarefreeRow_mul, mul_pow]
      ring
end Local

theorem rayIdealRow_eq_supportRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter) (h : O) :
    rayIdealRow p hg F C negative χ D h =
    supportConjugateSum (fun i => Ideal.span {p i}) hg (F \ D)
      (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) h := by
  symm
  exact FirstCauchyArithmetic.supportConjugateSum_eq_conjugateIdealRowSum
    (fun i => Ideal.span {p i}) hinj hg (F \ D) _ h

def dilatedRayColumn {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d y : O) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg (F \ D)
    (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) *
      C (D ∪ U) * afterDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ c d U) y

theorem rayIdealRow_beforeDilation {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (c d f h : O) :
    rayIdealRow p hg F
      (fun S => C S * beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f S)
      negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      dilatedRayColumn p hg F D C negative χ q B v ε₁ ε₂ c d
        (h * f ^ 2 * dilationLabel q B v ε₁ ε₂) := by
  rw [rayIdealRow_eq_supportRow p hinj]
  unfold dilatedRayColumn supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hd : Disjoint D U := by
    exact Finset.disjoint_left.mpr (fun i hiD hiU =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hiU)).2 hiD)
  dsimp only
  rw [beforeDilationLabel_union _ hg q B v ε₁ ε₂ side c d f D U hd]
  calc
    _ = beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f D *
      supportMobius (fun i => Ideal.span {p i}) U *
      ((if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg q B v ε₁ ε₂ side c d f U *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) := by ring
    _ = _ := by
      rw [beforeDilationLabel_star_row _ hg q B v ε₁ ε₂ hv side c d f h U]
      ring

def originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) (S : Finset ι) : ℂ :=
  C S * rowCoprimeMask (fun i => Ideal.span {p i}) S (cubeRadical p B) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S
      (aLabel p B (if negative then ε₂ else ε₁) * c) ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f ^ 4

def cubeCoreCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  if negative then
    star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) *
      MixedCrossSeparation.columnG p hp hcop hg S * C S *
      star (V (y S) * FourierBridge.logPhase t (-(y S)))
  else
    fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
      MixedCrossSeparation.columnG p hp hcop hg S * C S *
      (V (y S) * FourierBridge.logPhase t (-(y S)))

theorem cubeLogCoefficient_originalLabel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (c d f : O) (S : Finset ι) :
    cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d S =
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
  cases negative <;>
    simp only [cubeLogCoefficient, cubeCoreCoefficient, cubeMinusCoefficient,
      cubePlusCoefficient, FirstCauchyArithmetic.firstPassColumnMinus,
      FirstCauchyArithmetic.firstPassColumnPlus, logTwistMinus, logTwistPlus,
      originalLabelColumn, beforeDilationLabel, Bool.false_eq_true, ite_false, ite_true,
      finiteSquarefreeRow_mul, mul_pow] <;> ring

theorem rayIdealRow_cube_labels {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : O) :
    rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
        negative χ p B v ε₁ ε₂ c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂) := by
  have he : cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d =
    fun S => cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f S := by
    funext S
    exact cubeLogCoefficient_originalLabel p hp hcop hg B v ε₁ ε₂ negative C V y t c d f S
  rw [he]
  exact rayIdealRow_beforeDilation p hinj hg F D _ negative χ p B v ε₁ ε₂ hv negative c d f h

theorem first_cube_energy_small_power (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
      (y : Finset ι → ℝ) (t : ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∑ x ∈ s, ‖w x‖ * ‖rayIdealRow p hg F
        (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator x.1))
            V y t d) negative χ D x.2‖ ^ 2) ≤
      M * K * Y ^ deltaLoss * ∑ z ∈ T,
        ‖dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
          negative χ p B v ε₁ ε₂ c d z‖ ^ 2 := by
  obtain ⟨K, hK, hpush⟩ := SquarefreeDivisorBound.first_element_energy_small_power deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg F D B v ε₁ ε₂ hv negative χ C V y t c d s T w M Y hM hY hs hmap hT hnorm hw
  apply le_trans _ (hpush s T (dilationLabel p B v ε₁ ε₂) w
    (dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
      negative χ p B v ε₁ ε₂ c d) M Y hM hY hs hmap hT hnorm hw)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv negative χ C V y t c d,
    norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (beforeDilationLabel_norm_le_one _ hg p B v ε₁ ε₂ negative c d
      (ConcretePrimeRowBridge.idealGenerator x.1) D)

theorem normalized_originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) :
    normalizedColumn p (originalLabelColumn p hg B ε₁ ε₂ negative C c f) =
      originalLabelColumn p hg B ε₁ ε₂ negative (normalizedColumn p C) c f := by
  funext S
  simp only [normalizedColumn, originalLabelColumn, div_eq_mul_inv]
  ring

theorem firstColumnEnergy_original_labels {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V X d h b =
    ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
        ‖rayPairWeight p r D h‖ *
        (‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D‖ ^ 2 *
          ‖dilatedRayColumn p hg F D
            (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative
              (normalizedColumn p C) V (columnLog p X) t)
            negative (if negative then r.1 else r.2) p B v ε₁ ε₂ c d
            (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)‖ ^ 2) := by
  unfold firstColumnEnergy
  rw [normalized_originalLabelColumn]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  unfold rayIdealEnergy
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  rw [rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv negative _
    (normalizedColumn p C) V (columnLog p X) t c d f h, norm_mul, mul_pow]

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def firstDivisorWeight {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (E : Finset ι) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
    (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)

theorem retained_first_kernel_energy_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale →
      ∀ (Ω : Finset (Finset ι × O)) (w : Finset ι × O → ℂ),
      (∀ x ∈ Ω, x.2 ≠ 0) → ∃ b : (Finset ι × O) → 𝓢(ℝ, ℂ),
      (∀ x ∈ Ω, Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b x t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2) ^ A *
            (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b x t‖) ≤ K) ∧
      ‖∑ x ∈ Ω, (w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) := by
  obtain ⟨K, hK, hs⟩ := actual_first_kernel_energy_bound p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL Ω w hΩ
  let d := fun x : Finset ι × O => primeSubsetGenerator (fun i => Ideal.span {p i}) x.1
  have hfam : ∀ x : Finset ι × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ Ω →
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
      (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ (d x) x.2) ^ A *
        (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale (d x) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ (d x) x.2 b) *
        Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ (d x) x.2 b) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨b, hb⟩ := hs lengthScale hL (d x) x.2 (primeSubsetGenerator_ne_zero _ _) (hΩ x hx)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  refine ⟨b, fun x hx => ⟨(hb x hx).1, (hb x hx).2.1⟩, ?_⟩
  let U := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ (d x) x.2 (b x)
  let V := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ (d x) x.2 (b x)
  let a := fun x => ‖w x * firstDivisorWeight p x.1‖
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hU (x) : 0 ≤ U x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ _ _ _
  have hV (x) : 0 ≤ V x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ _ _ _
  have hterm (x) : a x * (Real.sqrt (U x) * Real.sqrt (V x)) =
      Real.sqrt (a x * U x) * Real.sqrt (a x * V x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt (a x)) ^ 2 * (Real.sqrt (U x) * Real.sqrt (V x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ Ω, ‖(w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale (d x) x.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x ∈ Ω, q * (Real.sqrt (a x * U x) * Real.sqrt (a x * V x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ a x * (q * Real.sqrt (U x) * Real.sqrt (V x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2.2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ Ω, Real.sqrt (a x * U x) * Real.sqrt (a x * V x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ Ω, a x * U x) * Real.sqrt (∑ x ∈ Ω, a x * V x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Ω
        (fun x => mul_nonneg (norm_nonneg _) (hU x))
        (fun x => mul_nonneg (norm_nonneg _) (hV x))) hq
    _ = _ := (mul_assoc _ _ _).symm

end

section
open scoped BigOperators Classical
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)

theorem blockRow_norm_le_one {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S : Finset ι) (e : ι → ℕ) (a : O) : ‖blockRow p hg S e a‖ ≤ 1 := by
  rw [blockRow_eq_product, norm_prod]
  calc
    _ ≤ ∏ i ∈ S, (1 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i hi
      let : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = 1 := by simp

theorem cubeBaseFactor_norm_le_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) :
    ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ ≤ 1 := by
  have he : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂,
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val ≠ 0 := by
    intro i hi
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hi).2
  simp only [cubeBaseFactor, norm_mul, norm_star,
    gaussBlock_norm_one p hp hcop hg hc _ _ he (fun _ _ => ZMod.val_lt _), one_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg _ _ _)).trans (blockRow_norm_le_one p hg _ _ _)

theorem rayPairWeight_norm_le {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) :
    ‖rayPairWeight p r D h‖ ≤ ‖crossCoeff r.1 r.2‖ := by
  rw [norm_rayPairWeight p hinj hc]
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D h‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  exact mul_le_of_le_one_right (norm_nonneg _) hm

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FourierBridge (logPhase)

def firstLogDensity (J : ℕ) (t : ℝ) : ℝ := ((1 + ‖t‖) ^ (J + 2))⁻¹

theorem firstLogDensity_nonneg (J : ℕ) (t : ℝ) : 0 ≤ firstLogDensity J t := by
  unfold firstLogDensity
  positivity

theorem firstLogDensity_integrable (J : ℕ) : Integrable (firstLogDensity J) volume := by
  have h := integrable_one_add_norm (E := ℝ) («μ» := (volume : Measure ℝ))
    (r := (J + 2 : ℕ)) (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) J])
  convert h using 1
  funext t
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

theorem firstLogDensity_moment_integrable (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * firstLogDensity J t) volume := by
  convert firstLogDensity_integrable 0 using 1
  funext t
  have ht : 1 + ‖t‖ ≠ 0 := ne_of_gt (by positivity)
  simp only [firstLogDensity, zero_add, pow_add, mul_inv_rev]
  field_simp

theorem two_variable_radial_envelope (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
        ∫ t : ℝ, (V₁ x * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) ∧
      (∀ t : ℝ, (1 + R) ^ A * ‖b t‖ ≤ K * firstLogDensity J t) := by
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let M : Bool → ℝ := fun j => if j then M₂ else M₁
  have hM : ∀ j, 0 ≤ M j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j := by
    intro j; cases j
    · exact hV₁
    · exact hV₂
  obtain ⟨K, hK, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_envelope
    W V (fun _ => -1) M hM hV A (J + 2)
  refine ⟨K, hK, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y
    have hs := hb (fun j => if j then y else x)
    simpa only [V, Fintype.prod_bool, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
      neg_one_mul, mul_neg_one, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using hs
  · intro t
    rw [firstLogDensity, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t‖) (J + 2))).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hpoint t

theorem actualFirstKernel_eq_separated {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (lengthScale : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W
      (firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h * Real.exp (-x-y)) =
      ∫ t : ℝ, (V₁ x * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
            (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
          (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
            (normalizedColumn p C₂) V₂ (columnLog p X₂) t d) h := by
  have hs := cube_integral_of_radial_separation p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ (normalizedColumn p C₁) (normalizedColumn p C₂) d h W V₁ V₂
    (columnLog p X₁) (columnLog p X₂)
    (firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) b hsep
  simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true]
  rw [← hs.2]
  unfold actualFirstKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · rw [ite_eq_left hNP, ite_eq_left hNP]
    have hNB := hFB.mono_left (Finset.mem_powerset.mp hN)
    have hPB := hFB.mono_left (Finset.mem_powerset.mp hP)
    rw [actual_radial_argument p hp N P (cubeActiveSupport B v ε₁ ε₂) hNP
      (hNB.mono_right (Finset.filter_subset _ _))
      (hPB.mono_right (Finset.filter_subset _ _)) lengthScale X₁ X₂ hX₁ hX₂ d h]
    have hpre := actual_pair_prefactor p hp hcop hg N P B hNP hNB hPB v ε₁ ε₂ C₁ C₂ lengthScale d h
    calc
      _ = (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)))) *
          (((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) := by ring
      _ = _ := by rw [hpre]; ring
  · simp [hNP]

theorem actual_first_kernel_energy_envelope {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  have hR : 0 < firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h := by
    unfold firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  rw [actualFirstKernel_eq_separated p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ lengthScale d h b hsep, norm_mul]
  have hi := cube_integral_norm_le_energy p hg F
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
      (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
      (normalizedColumn p C₂) V₂ (columnLog p X₂) t d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
    abs_of_nonneg (norm_nonneg _)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (div_nonneg hL.le (norm_nonneg _))

end FirstPassCubeLabels

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.DivisorBlocks -/

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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

def quotientBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue left right (fun D => quotientMatrix D rows left)
    (fun E => quotientMatrix E rows right) a b D E

theorem canonical_divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤
      256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
        (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  have hS0 (D) (hD : D ∈ S) : D ≠ 0 := by
    intro hz
    have hh := (hS D hD).1
    simp only [hz, map_zero, Nat.cast_zero] at hh
    linarith
  have hT0 (E) (hE : E ∈ T) : E ≠ 0 := by
    intro hz
    have hh := (hT E hE).1
    simp only [hz, map_zero, Nat.cast_zero] at hh
    linarith
  have hA (D) (hD : D ∈ S) :
      ‖FiniteSieveOperator.operator (quotientMatrix D rows left)‖ ^ 2 ≤ sieveNorm M (N / D₁) := by
    apply (quotientMatrix_squared_norm_le D (hS0 D hD) rows left hr hl M N hrows hleft).trans
    exact sieveNorm_mono le_rfl (div_le_div_of_nonneg_left (by linarith) (by linarith) (hS D hD).1)
  have hB (E) (hE : E ∈ T) :
      ‖FiniteSieveOperator.operator (quotientMatrix E rows right)‖ ^ 2 ≤ sieveNorm M (N / D₂) := by
    apply (quotientMatrix_squared_norm_le E (hT0 E hE) rows right hr hri M N hrows hright).trans
    exact sieveNorm_mono le_rfl (div_le_div_of_nonneg_left (by linarith) (by linarith) (hT E hE).1)
  have hsCard := DescentFiberCost.finite_ideal_count_real S (2 * D₁) (by linarith)
    hS0 (fun D hD => (hS D hD).2)
  have htCard := DescentFiberCost.finite_ideal_count_real T (2 * D₂) (by linarith)
    hT0 (fun E hE => (hT E hE).2)
  have hh := divisor_block_bound ε hε S T left right (fun j => (hleft j).1.1)
    (fun k => (hright k).1.1) N N (by linarith) (by linarith)
    (fun j => (hleft j).2) (fun k => (hright k).2)
    (fun D => quotientMatrix D rows left) (fun E => quotientMatrix E rows right) a b
    (sieveNorm M (N / D₁)) (sieveNorm M (N / D₂)) (sieveNorm_nonneg _ _) (sieveNorm_nonneg _ _) hA hB
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  have hb1 := sieveNorm_nonneg M (N / D₁)
  have hb2 := sieveNorm_nonneg M (N / D₂)
  change (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤ _ at hh
  apply hh.trans
  calc
    _ ≤ (128 * (2 * D₁)) * (128 * (2 * D₂)) *
        (sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
          (supportConstant ε hε * N ^ ε) * (supportConstant ε hε * N ^ ε)) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N ^ ε) * ∑ k, ‖b k‖ ^ 2) := by gcongr
    _ = _ := by ring

end

section
open ConcretePrimeRowBridge ActualEisensteinCubic

theorem quadraticRow_norm_le_one (I : Ideal O) (z : O) : ‖quadraticRow I z‖ ≤ 1 := by
  by_cases hI : Admissible I
  · rw [quadraticRow, dite_eq_left hI]
    exact QuadraticMainOperatorBound.ideal_quadraticRow_norm_le_one {I}
      (singletonPositive I hI) (singletonGood I hI) I z
  · simp [quadraticRow, hI]

theorem quadraticRow_mul (I J : Ideal O) (hIJ : Admissible (I * J)) (z : O) :
    quadraticRow (I * J) z = quadraticRow I z * quadraticRow J z := by
  have hI : Admissible I := admissible_of_dvd hIJ (dvd_mul_right I J)
  have hJ : Admissible J := admissible_of_dvd hIJ (dvd_mul_left J I)
  let F : Finset (Ideal O) := {I, J, I * J}
  have hF : ∀ K ∈ F, Admissible K := by
    intro K hK
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · exact hI
    · exact hJ
    · exact hIJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  have hIJF : I * J ∈ F := by simp [F]
  have hu : idealSupport F (I * J) = idealSupport F I ∪ idealSupport F J := by
    ext P
    simp only [mem_idealSupport_iff, UniqueFactorizationMonoid.normalizedFactors_mul hI.1 hJ.1,
      Multiset.mem_add, Finset.mem_union]
  have hd : Disjoint (idealSupport F I) (idealSupport F J) := by
    apply Finset.disjoint_left.mpr
    intro P hPI hPJ
    have hpI := (mem_idealSupport_iff F I P).mp hPI
    have hpJ := (mem_idealSupport_iff F J P).mp hPJ
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val hpI
    have hi : P.val ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpI
    have hj : P.val ∣ J := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpJ
    exact hp.not_isUnit ((IsRelPrime.of_squarefree_mul hIJ.2.1) hi hj)
  rw [quadraticRow_eq F hF (I * J) hIJF z, quadraticRow_eq F hF I hIF z,
    quadraticRow_eq F hF J hJF z]
  unfold idealSexticRow finiteSquarefreeRow
  rw [hu, Finset.prod_union hd, mul_pow]

theorem quadraticRow_divisor_factor (I D : Ideal O) (hI : Admissible I) (hD : D ∣ I) (z : O) :
    quadraticRow I z = quadraticRow D z * quadraticRow (idealQuotient D I) z := by
  have h := quadraticRow_mul D (idealQuotient D I) (by rwa [idealQuotient_mul hD]) z
  simpa only [idealQuotient_mul hD] using h

end

open IdealDivisorBilinearBlocks CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def originalBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue left right (fun _ i j => quadraticRow (left j) (primaryGenerator (rows i)))
    (fun _ i k => quadraticRow (right k) (primaryGenerator (rows i))) a b D E

theorem original_entry_factor {m n : Type*} (rows : m → Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (D : Ideal O) (i : m) (j : n) :
    quadraticRow (cols j) (primaryGenerator (rows i)) * (if D ∣ cols j then a j else 0) =
      quadraticRow D (primaryGenerator (rows i)) *
        (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) := by
  by_cases h : D ∣ cols j
  · simp only [h, ite_true, quotientMatrix]
    rw [quadraticRow_divisor_factor (cols j) D (hcols j) h]
    ring
  · simp [h, quotientMatrix]

theorem originalBlock_le_quotientBlock {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) :
    originalBlock rows left right a b D E ≤ quotientBlock rows left right a b D E := by
  change (∑ i, _) ≤ ∑ i, _
  apply Finset.sum_le_sum
  intro i _
  have heq : (∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (quadraticRow (left j) (primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0) =
      (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow E (primaryGenerator (rows i))) *
        (∑ j, ∑ k, if IsCoprime (left j) (right k) then
          star (quotientMatrix D rows left i j * (if D ∣ left j then a j else 0)) *
          (quotientMatrix E rows right i k * (if E ∣ right k then b k else 0)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : IsCoprime (left j) (right k)
    · rw [ite_eq_left h, ite_eq_left h]
      rw [original_entry_factor rows left hleft a D i j,
        original_entry_factor rows right hright b E i k, star_mul]
      ring
    · simp only [ite_eq_right h, mul_zero]
  change ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (quadraticRow (left j) (primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0‖ ≤ _
  rw [heq, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_mul (quadraticRow_norm_le_one D _) (quadraticRow_norm_le_one E _)
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem original_rectangular_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, originalBlock rows left right a b D E) ^ 2 ≤
      (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 := by
  apply pow_le_pow_left₀
  · exact Finset.sum_nonneg (fun D _ => Finset.sum_nonneg (fun E _ =>
      blockValue_nonneg left right _ _ a b D E))
  · apply Finset.sum_le_sum
    intro D hD
    exact Finset.sum_le_sum (fun E hE => originalBlock_le_quotientBlock
      rows left right hleft hright a b D E)

theorem canonical_original_divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, originalBlock rows left right a b D E) ^ 2 ≤
      256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
        (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  exact (original_rectangular_bound S T rows left right
    (fun j => (hleft j).1) (fun k => (hright k).1) a b).trans
      (canonical_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
        rows left right hr hl hri hrows hleft hright a b)

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction
open FiniteSieveOperator

theorem squared_norm_row_partition {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (P : m → Prop) [DecidablePred P] :
    ‖operator A‖ ^ 2 ≤
      ‖operator (fun (i : {i : m // P i}) j => A i.val j)‖ ^ 2 +
      ‖operator (fun (i : {i : m // ¬ P i}) j => A i.val j)‖ ^ 2 := by
  apply squared_norm_le_of_energy _ _ (by positivity)
  intro a
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i => ‖∑ j, A i j * a j‖ ^ 2)]
  have h₁ := energy_bound (fun (i : {i : m // P i}) j => A i.val j) a
  have h₂ := energy_bound (fun (i : {i : m // ¬ P i}) j => A i.val j) a
  exact (add_le_add h₁ h₂).trans_eq (by ring)
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel FiniteSieveOperator

def Supported (I : Ideal O) : Prop :=
  I ≠ 0 ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2

def fullRange (M : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊M⌋₊).filter Supported

theorem mem_fullRange {M : ℝ} {I : Ideal O} :
    I ∈ fullRange M ↔ Supported I ∧ (Ideal.absNorm I : ℝ) ≤ M := by
  rw [fullRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hM : 0 ≤ M := by
      by_contra hn
      have hz : ⌊M⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hM)
  · rintro ⟨ha, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha.1 (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, ha⟩

theorem admissible_supported {I : Ideal O} (hI : Admissible I) : Supported I :=
  ⟨hI.1, hI.2.2⟩

theorem squarefreePart_eq_self {I : Ideal O} (hI : Squarefree I) : squarefreePart I = I := by
  have h := (squarePart_mul_squarefree (show (1 : Ideal O) ≠ 0 from one_ne_zero) hI).2
  simpa only [one_pow, one_mul] using h

def highKernelRange (M K : ℝ) : Finset (Ideal O) :=
  (fullRange M).filter (fun I => K < (Ideal.absNorm (squarefreePart I) : ℝ))

theorem mem_highKernelRange {M K : ℝ} {I : Ideal O} :
    I ∈ highKernelRange M K ↔
      Supported I ∧ (Ideal.absNorm I : ℝ) ≤ M ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
  simp only [highKernelRange, Finset.mem_filter, mem_fullRange, and_assoc]

def highKernelMatrix (M N K : ℝ) : Matrix (highKernelRange M K) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)

def highKernelNorm (M N K : ℝ) : ℝ := ‖operator (highKernelMatrix M N K)‖ ^ 2

theorem highKernelNorm_nonneg (M N K : ℝ) : 0 ≤ highKernelNorm M N K := sq_nonneg _

theorem sieveNorm_le_low_add_high (M N K : ℝ) :
    sieveNorm M N ≤ sieveNorm K N + highKernelNorm M N K := by
  let P : idealRange M → Prop := fun I => (Ideal.absNorm I.val : ℝ) ≤ K
  let lo := {I : idealRange M // P I}
  let hi := {I : idealRange M // ¬ P I}
  have hlo : ‖operator (fun (I : lo) (J : idealRange N) => matrix M N I.val J)‖ ^ 2 ≤
      sieveNorm K N := by
    apply family_squared_norm_le (fun I : lo => I.val.val) (fun J : idealRange N => J.val)
    · intro I J h
      apply Subtype.ext
      exact Subtype.ext h
    · exact Subtype.val_injective
    · intro I
      exact ⟨(mem_idealRange.mp I.val.property).1, I.property⟩
    · intro J
      exact mem_idealRange.mp J.property
  let toHigh : hi → highKernelRange M K := fun I => ⟨I.val.val, by
    apply mem_highKernelRange.mpr
    have hI := mem_idealRange.mp I.val.property
    refine ⟨admissible_supported hI.1, hI.2, ?_⟩
    rw [squarefreePart_eq_self hI.1.2.1]
    exact lt_of_not_ge I.property⟩
  have hhighinj : Function.Injective toHigh := by
    intro I J h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : highKernelRange M K => I.val) h
  have hhi := FiniteSieveRestriction.submatrix_norm_le toHigh hhighinj
    (fun J : idealRange N => J) Function.injective_id (highKernelMatrix M N K)
  have hhisq : ‖operator (fun (I : hi) (J : idealRange N) => matrix M N I.val J)‖ ^ 2 ≤
      highKernelNorm M N K := pow_le_pow_left₀ (norm_nonneg _) hhi 2
  exact (FiniteSieveRestriction.squared_norm_row_partition (matrix M N) P).trans (add_le_add hlo hhisq)

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
namespace QuadraticKernelTransfer
open FourierBridge EisensteinSchwartzPoisson

theorem sum_norm_integral_bound {ι : Type*} [Fintype ι]
    (b : ℝ → ℂ) (φ : ι → ℝ → ℂ) (H : ℝ)
    (hint : ∀ i, Integrable (fun t => b t * φ i t))
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀ t, (∑ i, ‖φ i t‖) ≤ H) :
    (∑ i, ‖∫ t, b t * φ i t‖) ≤ H * ∫ t, ‖b t‖ := by
  calc
    _ ≤ ∑ i, ∫ t, ‖b t * φ i t‖ := Finset.sum_le_sum (fun i _ => norm_integral_le_integral_norm _)
    _ = ∫ t, ∑ i, ‖b t * φ i t‖ := (integral_finsetSum _ (fun i _ => (hint i).norm)).symm
    _ ≤ ∫ t, H * ‖b t‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => by positivity)) (hb.const_mul H)
      filter_upwards [] with t
      simp only [norm_mul, ← Finset.mul_sum]
      calc
        _ ≤ ‖b t‖ * H := mul_le_mul_of_nonneg_left (hφ t) (norm_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

theorem radial_two_variable_window (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, |x| ≤ L₁ → |y| ≤ L₂ →
        paperRadialFourier W (R * Real.exp (x+y)) =
          ∫ t, logPhase t x * logPhase t y * b t) ∧
      (1 + R) ^ A * (∫ t, ‖b t‖) ≤ C := by
  let V₁ : ℝ → ℂ := fun x => if |x| ≤ L₁ then 1 else 0
  let V₂ : ℝ → ℂ := fun x => if |x| ≤ L₂ then 1 else 0
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let lengthScale : Bool → ℝ := fun j => if j then L₂ else L₁
  have hL : ∀ j, 0 ≤ lengthScale j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ lengthScale j := by
    intro j x h
    cases j
    · change |x| ≤ L₁
      change (if |x| ≤ L₁ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
    · change |x| ≤ L₂
      change (if |x| ≤ L₂ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope W V (fun _ => 1) lengthScale hL hV A 0
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, hmass, _⟩ := hs R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y hx hy
    have h := hb (fun j => if j then y else x)
    simpa only [V, V₁, V₂, lengthScale, Fintype.prod_bool, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte, ite_eq_left hx, ite_eq_left hy, one_mul, mul_one,
      add_comm, mul_comm, mul_left_comm, mul_assoc] using h
  · simpa only [pow_zero, one_mul] using hmass

theorem radial_phase_integrable (b : 𝓢(ℝ, ℂ)) (c : ℂ) (x y : ℝ) :
    Integrable (fun t => b t * (logPhase t x * (c * logPhase t y))) := by
  apply (b.integrable.norm.mul_const ‖c‖).mono'
  · have hx := logPhase_continuous_left x
    have hy := logPhase_continuous_left y
    exact (by fun_prop : Continuous (fun t => b t * (logPhase t x * (c * logPhase t y)))).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [norm_mul, logPhase_norm, one_mul, mul_one]
    exact le_rfl

theorem radial_matrix_kernel_transfer (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n]
        (c : m → n → ℂ) (x : m → ℝ) (y : n → ℝ) (H : ℝ),
        0 ≤ H → (∀ i, |x i| ≤ L₁) → (∀ j, |y j| ≤ L₂) →
        (∀ t, (∑ i, ‖∑ j, c i j * logPhase t (y j)‖) ≤ H) →
        (1 + R) ^ A * (∑ i, ‖∑ j, c i j *
          paperRadialFourier W (R * Real.exp (x i + y j))‖) ≤ C * H := by
  obtain ⟨C, hC, hs⟩ := radial_two_variable_window W L₁ L₂ hL₁ hL₂ A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ c x y H hH hx hy hphase
  obtain ⟨b, hb, hmass⟩ := hs R hR
  let φ : m → ℝ → ℂ := fun i t => logPhase t (x i) * ∑ j, c i j * logPhase t (y j)
  have hint (i : m) : Integrable (fun t => b t * φ i t) := by
    have h := integrable_finsetSum (Finset.univ : Finset n)
      (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))
    simpa only [φ, Finset.mul_sum] using h
  have hid (i : m) : (∑ j, c i j * paperRadialFourier W (R * Real.exp (x i + y j))) =
      ∫ t, b t * φ i t := by
    rw [show (fun t => b t * φ i t) = fun t =>
      ∑ j, b t * (logPhase t (x i) * (c i j * logPhase t (y j))) by
        funext t; simp only [φ, Finset.mul_sum]]
    rw [integral_finsetSum _ (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb _ _ (hx i) (hy j), ← integral_const_mul]
    congr 1
    funext t
    ring
  have hp (t : ℝ) : (∑ i, ‖φ i t‖) ≤ H := by
    simpa only [φ, norm_mul, logPhase_norm, one_mul] using hphase t
  have hi := sum_norm_integral_bound b φ H hint b.integrable.norm hp
  simp only [← hid] at hi
  calc
    _ ≤ (1 + R) ^ A * (H * ∫ t, ‖b t‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = H * ((1 + R) ^ A * ∫ t, ‖b t‖) := by ring
    _ ≤ H * C := mul_le_mul_of_nonneg_left hmass hH
    _ = _ := mul_comm _ _

end QuadraticKernelTransfer

namespace CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def quotientTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (quotientMatrix D rows left i j * (if D ∣ left j then a j else 0)) *
      (quotientMatrix E rows right i k * (if E ∣ right k then b k else 0)) else 0

def divisorBlockCost (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
    (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
    (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2)

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem quotientTerm_phase (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p)
    (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    quotientTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k =
    quotientTerm rows left right a b D E i j k * logPhase t (y j + z k) := by
  unfold quotientTerm
  rw [logPhase_add]
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hD : D ∣ left j <;> by_cases hE : E ∣ right k <;>
      simp only [hc, hD, hE, ↓reduceIte, mul_zero, zero_mul, star_zero, star_mul, star_star] ; ring

theorem canonical_divisor_block_phase_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    (∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  have hb := canonical_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright
    (fun j => a j * star (logPhase t (y j))) (fun k => b k * logPhase t (z k))
  simp only [norm_mul, norm_star, logPhase_norm, mul_one] at hb
  change (∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k,
    quotientTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k‖) ^ 2 ≤
    divisorBlockCost ε hε D₁ D₂ M N a b at hb
  simp only [quotientTerm_phase] at hb
  have hcost : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := (sq_nonneg _).trans hb
  have hs := Real.sq_sqrt hcost
  have hp := Real.sqrt_nonneg (divisorBlockCost ε hε D₁ D₂ M N a b)
  have hsum : 0 ≤ ∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖ := by positivity
  nlinarith
end

theorem canonical_radial_divisor_block_bound
    (W : 𝓢(ℝ, ℂ)) (L₁ L₂ L₃ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ M N : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hN : 1 ≤ N)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (x : S → T → m → ℝ) (y : n → ℝ) (z : p → ℝ),
        (∀ D E i, |x D E i| ≤ L₁) → (∀ j, |y j| ≤ L₂) → (∀ k, |z k| ≤ L₃) →
        (1 + R) ^ A * (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
          quotientTerm rows left right a b D.val E.val i j k *
            paperRadialFourier W (R * Real.exp (x D E i + (y j + z k)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  obtain ⟨C, hC, hker⟩ := radial_matrix_kernel_transfer W L₁ (L₂ + L₃) hL₁ (add_nonneg hL₂ hL₃) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n p _ _ _ _ _ _ ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b x y z hx hy hz
  let c : (S × T × m) → (n × p) → ℂ := fun i j =>
    quotientTerm rows left right a b i.1.val i.2.1.val i.2.2 j.1 j.2
  have hp (t : ℝ) : (∑ i : S × T × m, ‖∑ j : n × p, c i j * logPhase t (y j.1 + z j.2)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
    have hb := canonical_divisor_block_phase_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
      rows left right hr hl hri hrows hleft hright a b y z t
    simp only [c, Fintype.sum_prod_type]
    let v : Ideal O → Ideal O → ℝ := fun D E => ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖
    change (∑ D : S, ∑ E : T, v D.val E.val) ≤ _
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, v D E.val)]
    have he (D : Ideal O) := Finset.sum_coe_sort T (v D)
    simp_rw [he]
    exact hb
  have hb := hker R hR c (fun i => x i.1 i.2.1 i.2.2) (fun j => y j.1 + z j.2)
    (Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b)) (Real.sqrt_nonneg _)
    (fun i => hx i.1 i.2.1 i.2.2)
    (fun j => (abs_add_le _ _).trans (add_le_add (hy j.1) (hz j.2))) hp
  simpa only [c, Fintype.sum_prod_type] using hb

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTerm_phase (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p)
    (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    originalTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k =
    originalTerm rows left right a b D E i j k * logPhase t (y j + z k) := by
  unfold originalTerm
  rw [logPhase_add]
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hD : D ∣ left j <;> by_cases hE : E ∣ right k <;>
      simp only [hc, hD, hE, ↓reduceIte, mul_zero, zero_mul, star_zero, star_mul, star_star] ; ring

theorem canonical_original_divisor_block_phase_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    (∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  have hb := canonical_original_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright
    (fun j => a j * star (logPhase t (y j))) (fun k => b k * logPhase t (z k))
  simp only [norm_mul, norm_star, logPhase_norm, mul_one] at hb
  change (∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k,
    originalTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k‖) ^ 2 ≤
    divisorBlockCost ε hε D₁ D₂ M N a b at hb
  simp only [originalTerm_phase] at hb
  have hcost : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := (sq_nonneg _).trans hb
  have hs := Real.sq_sqrt hcost
  have hp := Real.sqrt_nonneg (divisorBlockCost ε hε D₁ D₂ M N a b)
  have hsum : 0 ≤ ∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖ := by positivity
  nlinarith
end

theorem canonical_original_radial_divisor_block_bound
    (W : 𝓢(ℝ, ℂ)) (L₁ L₂ L₃ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ M N : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hN : 1 ≤ N)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (x : S → T → m → ℝ) (y : n → ℝ) (z : p → ℝ),
        (∀ D E i, |x D E i| ≤ L₁) → (∀ j, |y j| ≤ L₂) → (∀ k, |z k| ≤ L₃) →
        (1 + R) ^ A * (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
          originalTerm rows left right a b D.val E.val i j k *
            paperRadialFourier W (R * Real.exp (x D E i + (y j + z k)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  obtain ⟨C, hC, hker⟩ := radial_matrix_kernel_transfer W L₁ (L₂ + L₃) hL₁ (add_nonneg hL₂ hL₃) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n p _ _ _ _ _ _ ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b x y z hx hy hz
  let c : (S × T × m) → (n × p) → ℂ := fun i j =>
    originalTerm rows left right a b i.1.val i.2.1.val i.2.2 j.1 j.2
  have hp (t : ℝ) : (∑ i : S × T × m, ‖∑ j : n × p, c i j * logPhase t (y j.1 + z j.2)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
    have hb := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
      rows left right hr hl hri hrows hleft hright a b y z t
    simp only [c, Fintype.sum_prod_type]
    let v : Ideal O → Ideal O → ℝ := fun D E => ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖
    change (∑ D : S, ∑ E : T, v D.val E.val) ≤ _
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, v D E.val)]
    have he (D : Ideal O) := Finset.sum_coe_sort T (v D)
    simp_rw [he]
    exact hb
  have hb := hker R hR c (fun i => x i.1 i.2.1 i.2.2) (fun j => y j.1 + z j.2)
    (Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b)) (Real.sqrt_nonneg _)
    (fun i => hx i.1 i.2.1 i.2.2)
    (fun j => (abs_add_le _ _).trans (add_le_add (hy j.1) (hz j.2))) hp
  simpa only [c, Fintype.sum_prod_type] using hb

end CanonicalQuadraticSieve

end

end OAI

end

