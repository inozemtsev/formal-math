module

public import Green64.Library.Analysis.NumberTheory.DirichletL.QuadraticSieve.Part001
public import Green64.Library.OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.CrossFactorization -/

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
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss)

theorem blockCross_union_left {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T C : Finset ι)
    (hd : Disjoint S T) (e : ι → ℕ) :
    blockCross p hg (S ∪ T) C e = blockCross p hg S C e * blockCross p hg T C e :=
  Finset.prod_union hd

def threeBlockExponent {ι : Type*} [DecidableEq ι] (N P : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (i : ι) : ℕ :=
  if i ∈ N then 5 else if i ∈ P then 1
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val

theorem gaussBlock_three_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    gaussBlock p hp hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P * mixedCubeCross p hg N B v ε₁ ε₂ true *
        mixedCubeCross p hg P B v ε₁ ε₂ false := by
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hNC : Disjoint N C := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P C := hPB.mono_right (Finset.filter_subset _ _)
  have hNPC : Disjoint (N ∪ P) C := Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩
  have hN (i : ι) (hi : i ∈ N) : e i = 5 := by simp [e, threeBlockExponent, hi]
  have hP (i : ι) (hi : i ∈ P) : e i = 1 := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNP h hi
    simp [e, threeBlockExponent, hn, hi]
  have hC (i : ι) (hi : i ∈ C) : e i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNC h hi
    have hp' : i ∉ P := fun h => Finset.disjoint_left.mp hPC h hi
    simp [e, threeBlockExponent, hn, hp']
  have hcrossNP : blockCross p hg N P e = quadraticCrossPhase p hg N P := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hP k hk, pow_one]
    exact MixedCrossSeparation.mixed_cross_eq_quadratic p hg i k (hpr i) (hpr k)
  have hcrossNC : blockCross p hg N C e = mixedCubeCross p hg N B v ε₁ ε₂ true := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hC k hk]
    rfl
  have hcrossPC : blockCross p hg P C e = mixedCubeCross p hg P B v ε₁ ε₂ false := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hP i hi, hC k hk]
    rfl
  change gaussBlock p hp hg ((N ∪ P) ∪ C) e = _
  rw [gaussBlock_union p hp hg (N ∪ P) C hNPC, gaussBlock_union p hp hg N P hNP,
    blockCross_union_left p hg N P C hNP,
    gaussBlock_congr p hp hg N e (fun _ => 5) hN,
    gaussBlock_congr p hp hg P e (fun _ => 1) hP,
    gaussBlock_congr p hp hg C e _ hC, hcrossNP, hcrossNC, hcrossPC]
  ring

theorem canonicalProductGauss_three_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    canonicalProductGauss
      (fun i : ↥((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
      (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
      (fun i => threeBlockExponent N P v ε₁ ε₂ i.val) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (crtLabel p B v ε₁ ε₂ true)) *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂)) *
      (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P (crtLabel p B v ε₁ ε₂ false) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) := by
  have he : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i ≠ 0 := by
    intro i hi
    by_cases hn : i ∈ N
    · simp [threeBlockExponent, hn]
    by_cases hp' : i ∈ P
    · simp [threeBlockExponent, hn, hp']
    · have hiC : i ∈ cubeActiveSupport B v ε₁ ε₂ := by simpa [hn, hp'] using hi
      simp only [threeBlockExponent, ite_eq_right hn, ite_eq_right hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg _ _ he,
    gaussBlock_three_cube_partition p hp hg hpr N P B hNP hNB hPB,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr N B hNB,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr P B hPB]
  rfl

theorem gaussBlock_eq_mobius_converted {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) (side : Bool) :
    gaussBlock p hp hg S (fun _ => if side then 5 else 1) =
      FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) S *
        MixedCrossSeparation.convertedColumnBlock p hp hg S side := by
  have hinj : Function.Injective (fun i => Ideal.span {p i}) := by
    intro i k hik
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hik, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p k}).IsMaximal).ne_top ht
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [FirstCauchyArithmetic.supportMobius,
    prime_product_moebius (fun i => Ideal.span {p i}) hprime hinj S]
  unfold gaussBlock MixedCrossSeparation.convertedColumnBlock
  rw [← Finset.prod_neg]
  apply Finset.prod_congr rfl
  intro i hi
  have hl := MixedGaussConversion.neg_localGauss_eq_converted (p i) (hp i) (hg i) (hc i) (hpr i) side
  change (∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if side then 5 else 1)) *
      MixedGaussConversion.localGauss (p i) (hp i) (hg i) (if side then 5 else 1) =
    -((∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if side then 5 else 1)) *
      MixedGaussConversion.convertedLocal (p i) (hp i) (hg i) side)
  rw [← hl]
  ring

theorem a_weighted_three_cube_gauss {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) :
    star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
      canonicalProductGauss
        (fun i : ↥((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
        (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
        (fun i => threeBlockExponent N P v ε₁ ε₂ i.val) =
    (gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
      quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) *
      star (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
        FirstCauchyArithmetic.firstPassColumnMinus p hp hcop hg C₁ (crtLabel p B v ε₁ ε₂ true) N) *
      (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
        FirstCauchyArithmetic.firstPassColumnPlus p hp hcop hg C₂ (crtLabel p B v ε₁ ε₂ false) P) := by
  rw [canonicalProductGauss_three_cube_partition p hp hcop hg hpr N P B hNP hNB hPB]
  have hconvN := gaussBlock_eq_mobius_converted p hp hcop hg hc hpr N true
  have hconvP := gaussBlock_eq_mobius_converted p hp hcop hg hc hpr P false
  simp only [Bool.false_eq_true, ↓reduceIte] at hconvN hconvP
  rw [hconvN, hconvP]
  have hn := MixedCrossSeparation.columnCoefficient_cancel_true p hp hcop hg hc hpr N
  have hp' := MixedCrossSeparation.columnCoefficient_cancel_false p hp hcop hg hc hpr P
  simp only [FirstCauchyArithmetic.firstPassColumnMinus, FirstCauchyArithmetic.firstPassColumnPlus,
    star_mul, star_star, FirstCauchyArithmetic.star_supportMobius]
  calc
    _ = (star (MixedCrossSeparation.columnCoefficient p hp hcop hg N) *
        MixedCrossSeparation.convertedColumnBlock p hp hg N true) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P *
        MixedCrossSeparation.convertedColumnBlock p hp hg P false) *
      (star (C₁ N) * C₂ P *
        FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
        FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
        gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
          (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
        quadraticCrossPhase p hg N P *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (crtLabel p B v ε₁ ε₂ true)) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P (crtLabel p B v ε₁ ε₂ false)) := by ring
    _ = _ := by rw [hn, hp']; ring

end FirstPassCubeLabels

namespace QuadraticGaussRay
open EisensteinEPrimaryPhase ActualEisensteinCoordinates ActualEisensteinCubic

theorem quadraticRayValue_square (r : Coord) (hr : odd r) :
    quadraticRayValue (mul r r) = 1 := by
  have hi : (Complex.I : ℂ)⁻¹ = -Complex.I := by
    apply inv_eq_of_mul_eq_one_right
    norm_num
  have h : mul r r = (1, 0) ∨ mul r r = (3, 3) ∨ mul r r = (0, 1) := by
    decide +revert
  rcases h with h | h | h
  · rw [h]
    change breveGaussianFourTerms 1 0 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 3 3 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
  · rw [h]
    change breveGaussianFourTerms 0 1 = 1
    rw [breveGaussianFourTerms_formula]
    norm_num [hi]
    ring

theorem quadraticRayValue_same_residue_product (a b : ActualEisensteinCubic.O)
    (ha : odd (residue a)) (hab : residue a = residue b) :
    quadraticRayValue (residue (a * b)) = 1 := by
  rw [residue_mul, ← hab]
  exact quadraticRayValue_square _ ha

end QuadraticGaussRay

namespace QuadraticMainBoundaryFibers
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum QuadraticMainBoundary

def productIdeal (x : Ideal O × Ideal O × Ideal O) : Ideal O := x.1 * x.2.1 * x.2.2

theorem product_fiber_card_le (s : Finset (Ideal O × Ideal O × Ideal O))
    (G : Ideal O) (hG : G ≠ 0)
    (hdiv : ∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) (B : Ideal O) :
    (s.filter (fun x => productIdeal x = B)).card ≤ (idealDivisors G).card ^ 2 := by
  have hle : (s.filter (fun x => productIdeal x = B)).card ≤
      ((idealDivisors G) ×ˢ (idealDivisors G)).card := by
    apply Finset.card_le_card_of_injOn (fun x => (x.2.1, x.2.2))
    · intro x hx
      have hd := hdiv x (Finset.mem_filter.mp hx).1
      exact Finset.mem_product.mpr ⟨(mem_idealDivisors hG).mpr hd.1,
        (mem_idealDivisors hG).mpr hd.2⟩
    · intro x hx y hy hde
      obtain ⟨hD, hE⟩ := Prod.mk.inj hde
      have hd := hdiv x (Finset.mem_filter.mp hx).1
      have hD0 := ne_zero_of_dvd_ne_zero hG hd.1
      have hE0 := ne_zero_of_dvd_ne_zero hG hd.2
      have hprod := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      change x.1 * x.2.1 * x.2.2 = y.1 * y.2.1 * y.2.2 at hprod
      rw [← hD, ← hE] at hprod
      have hH : x.1 = y.1 := mul_right_cancel₀ hD0 (mul_right_cancel₀ hE0 hprod)
      exact Prod.ext hH (Prod.ext hD hE)
  simpa only [Finset.card_product, pow_two] using hle

theorem product_fiber_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O),
      G ≠ 0 → (∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) → ∀ B : Ideal O,
      ((s.filter (fun x => productIdeal x = B)).card : ℝ) ≤
        C * (Ideal.absNorm G : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by linarith)
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro s G hG hdiv B
  have hc : ((s.filter (fun x => productIdeal x = B)).card : ℝ) ≤
      ((idealDivisors G).card : ℝ) ^ 2 := by
    exact_mod_cast product_fiber_card_le s G hG hdiv B
  have hb := pow_le_pow_left₀ (by positivity : 0 ≤ ((idealDivisors G).card : ℝ))
    (hbound G hG) 2
  have heq : ((Ideal.absNorm G : ℝ) ^ (ε / 2)) ^ 2 = (Ideal.absNorm G : ℝ) ^ ε := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  apply hc.trans
  simpa only [mul_pow, heq] using hb

def boundaryCoefficient (K : ℝ) (s : Finset (Ideal O × Ideal O × Ideal O))
    (B : Ideal O) : ℂ :=
  ∑ x ∈ s.filter (fun x => productIdeal x = B),
    (UniqueFactorizationMonoid.moebius x.2.2 : ℂ) * (cutoffDifference K x.1 x.2.1 : ℝ)

theorem norm_cutoffDifference_le (K : ℝ) (H D : Ideal O) :
    ‖(cutoffDifference K H D : ℂ)‖ ≤ 1 := by
  unfold cutoffDifference
  split_ifs <;> norm_num

theorem boundaryCoefficient_norm_le_card (K : ℝ)
    (s : Finset (Ideal O × Ideal O × Ideal O)) (B : Ideal O) :
    ‖boundaryCoefficient K s B‖ ≤ (s.filter (fun x => productIdeal x = B)).card := by
  unfold boundaryCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _x ∈ s.filter (fun x => productIdeal x = B), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      have hm : ‖(UniqueFactorizationMonoid.moebius x.2.2 : ℂ)‖ ≤ 1 := by
        unfold UniqueFactorizationMonoid.moebius
        split_ifs <;> simp
      exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans (norm_cutoffDifference_le _ _ _)
    _ = _ := by simp

theorem boundaryCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O),
      G ≠ 0 → (∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G) → ∀ B : Ideal O,
      ‖boundaryCoefficient K s B‖ ≤ C * (Ideal.absNorm G : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := product_fiber_small_power ε hε
  exact ⟨C, hC, fun K s G hG hdiv B =>
    (boundaryCoefficient_norm_le_card K s B).trans (hbound s G hG hdiv B)⟩

theorem boundaryCoefficient_eq_zero_below (K : ℝ)
    (s : Finset (Ideal O × Ideal O × Ideal O)) (G : Ideal O) (hG : G ≠ 0)
    (hdiv : ∀ x ∈ s, x.2.1 ∣ G ∧ x.2.2 ∣ G)
    (B : Ideal O) (hB : (Ideal.absNorm B : ℝ) ≤ K) : boundaryCoefficient K s B = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  have hd := hdiv x hx'.1
  have hz := cutoffDifference_eq_zero_of_product_le K
    (ne_zero_of_dvd_ne_zero hG hd.1) (ne_zero_of_dvd_ne_zero hG hd.2)
    (by simpa only [← hx'.2, productIdeal] using hB)
  rw [hz, Complex.ofReal_zero, mul_zero]

end QuadraticMainBoundaryFibers

namespace CoprimeSieveOperator
open FiniteSieveOperator CoprimeMobiusExtension

theorem square_norm_sum {n : Type*} [Fintype n] (z : n → ℂ) :
    (↑(‖∑ j, z j‖ ^ 2) : ℂ) = ∑ j, ∑ k, star (z j) * z k := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, starRingEnd_apply]
  rw [Finset.sum_mul_sum]

theorem disjoint_gram_expansion {ι n : Type*} [DecidableEq ι] [Fintype n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B) (z : n → ℂ) :
    (∑ j, ∑ k, if Disjoint (support j) (support k) then star (z j) * z k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (↑(‖∑ j, if D ⊆ support j then z j else 0‖ ^ 2) : ℂ) := by
  have hp (j k : n) :
      (if Disjoint (support j) (support k) then star (z j) * z k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) := by
    calc
      _ = (if Disjoint (support j) (support k) then (1 : ℂ) else 0) * (star (z j) * z k) := by
        split_ifs <;> simp
      _ = _ := by
        rw [disjoint_indicator_expansion B _ _ (hs j) (hs k), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ j, ∑ D ∈ B.powerset, ∑ k,
        (-1 : ℂ) ^ D.card *
          (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ D ∈ B.powerset, ∑ j, ∑ k,
        (-1 : ℂ) ^ D.card *
          (if D ⊆ support j ∧ D ⊆ support k then star (z j) * z k else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      rw [square_norm_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : D ⊆ support j <;> by_cases hk : D ⊆ support k <;> simp [hj, hk]

theorem masked_coefficient_energy {ι n : Type*} [DecidableEq ι] [Fintype n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B) (a : n → ℂ) :
    (∑ D ∈ B.powerset, ∑ j, ‖if D ⊆ support j then a j else 0‖ ^ 2) =
      ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have heq : B.powerset.filter (fun D => D ⊆ support j) = (support j).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨And.right, fun h => ⟨h.trans (hs j), h⟩⟩
  have hite (D : Finset ι) : ‖if D ⊆ support j then a j else 0‖ ^ 2 =
      if D ⊆ support j then ‖a j‖ ^ 2 else 0 := by split_ifs <;> simp
  simp_rw [hite]
  rw [← Finset.sum_filter, heq]
  simp

theorem weighted_energy_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (↑(‖∑ j, A i j * a j‖ ^ 2) : ℂ)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  calc
    _ ≤ ∑ i, ‖w i * (↑(‖∑ j, A i j * a j‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, W * ‖∑ j, A i j * a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)
    _ = W * ∑ i, ‖∑ j, A i j * a j‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (energy_bound A a) hW

theorem coprime_gram_operator_bound {ι m n : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Finset ι) (support : n → Finset ι) (hs : ∀ j, support j ⊆ B)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (support j).card * ‖a j‖ ^ 2 := by
  have heq : (∑ i, w i * (∑ j, ∑ k,
      if Disjoint (support j) (support k) then
        star (A i j * a j) * (A i k * a k) else 0)) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ) := by
    simp_rw [disjoint_gram_expansion B support hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro i _
    have hz : (∑ j, if D ⊆ support j then A i j * a j else 0) =
        ∑ j, A i j * (if D ⊆ support j then a j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [hz]
    ring
  rw [heq]
  calc
    _ ≤ ∑ D ∈ B.powerset, ‖(-1 : ℂ) ^ D.card *
        ∑ i, w i * (↑(‖∑ j, A i j * (if D ⊆ support j then a j else 0)‖ ^ 2) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ B.powerset,
        W * ‖operator A‖ ^ 2 * ∑ j, ‖if D ⊆ support j then a j else 0‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro D _
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact weighted_energy_bound A (fun j => if D ⊆ support j then a j else 0) w W hW hw
    _ = _ := by
      rw [← Finset.mul_sum, masked_coefficient_energy B support hs a]

end CoprimeSieveOperator

namespace IdealCoprimeSieveOperator
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum CoprimeSieveOperator FiniteSieveOperator
open UniqueFactorizationMonoid

theorem primeSupport_disjoint_iff {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0) :
    Disjoint (primeSupport I) (primeSupport J) ↔ IsCoprime I J := by
  constructor
  · intro h
    have hr : IsRelPrime I J := (isRelPrime_iff_no_prime_factors hI).mpr (by
      intro P hPI hPJ hP
      apply Finset.disjoint_left.mp h
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hI).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPI⟩
      · apply Multiset.mem_toFinset.mpr
        exact (Ideal.mem_normalizedFactors_iff hJ).mpr
          ⟨Ideal.isPrime_of_prime hP, Ideal.dvd_iff_le.mp hPJ⟩)
    apply Ideal.isCoprime_iff_gcd.mpr
    exact associated_iff_eq.mp (associated_one_iff_isUnit.mpr (gcd_isUnit_iff_isRelPrime.mpr hr))
  · intro h
    exact Multiset.disjoint_toFinset.mpr (disjoint_normalizedFactors h.isRelPrime)

def supportConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose

theorem supportConstant_pos (ε : ℝ) (hε : 0 < ε) : 0 < supportConstant ε hε :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose_spec.1

theorem support_card_bound (ε : ℝ) (hε : 0 < ε) (I : Ideal O) (hI : I ≠ 0) :
    (2 : ℝ) ^ (primeSupport I).card ≤ supportConstant ε hε * (Ideal.absNorm I : ℝ) ^ ε :=
  (SquarefreeDivisorBound.prime_support_subsets_bound ε hε).choose_spec.2 I hI

theorem ideal_coprime_gram_operator_bound {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (_hN : 0 ≤ N) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ) (w : m → ℂ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    ‖∑ i, w i * (∑ j, ∑ k,
      if IsCoprime (column j) (column k) then
        star (A i j * a j) * (A i k * a k) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  let B : Finset (Ideal O) := Finset.univ.biUnion (fun j => primeSupport (column j))
  have hs (j : n) : primeSupport (column j) ⊆ B := by
    intro P hP
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hP⟩
  have h := coprime_gram_operator_bound B (fun j => primeSupport (column j)) hs A a w W hW hw
  simp_rw [primeSupport_disjoint_iff (hcol _) (hcol _)] at h
  apply h.trans
  have hmass : (∑ j, (2 : ℝ) ^ (primeSupport (column j)).card * ‖a j‖ ^ 2) ≤
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (support_card_bound ε hε (column j) (hcol j)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le)
        (supportConstant_pos ε hε).le)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hW (sq_nonneg ‖operator A‖))

open ConcretePrimeRowBridge

theorem actual_quadratic_coprime_gram_bound {m : Type*}
    [Fintype m] [DecidableEq m]
    (ε : ℝ) (hε : 0 < ε)
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ normalizedFactors I, goodLambda ∉ P)
    (r : m → O) (N : ℝ) (hN : 0 ≤ N)
    (hnorm : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ N)
    (a : F → ℂ) (w : m → ℂ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ i, ‖w i‖ ≤ W) :
    let A : Matrix m F ℂ := fun i J => (idealSexticRow F hFpos hFgood J.val (r i)) ^ 3
    ‖∑ i, w i * (∑ J : F, ∑ columnTwo : F,
      if IsCoprime J.val columnTwo.val then star (A i J * a J) * (A i columnTwo * a columnTwo) else 0)‖ ≤
      W * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) * ∑ J : F, ‖a J‖ ^ 2 := by
  dsimp only
  exact ideal_coprime_gram_operator_bound ε hε (fun J : F => J.val)
    (fun J => hFpos J.val J.property) N hN (fun J => hnorm J.val J.property)
    (fun i J => (idealSexticRow F hFpos hFgood J.val (r i)) ^ 3) a w W hW hw

end IdealCoprimeSieveOperator

open scoped BigOperators Classical
namespace QuadraticMainOperatorBound
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum QuadraticMainBoundary IdealCoprimeSieveOperator FiniteSieveOperator

def mainWeight (K : ℝ) (H D E : Ideal O) : ℂ :=
  (cutoffDifference K H D : ℂ) / (Real.sqrt (Ideal.absNorm (H * D * E) : ℝ) : ℂ)

theorem mainWeight_eq_zero_of_row_gt (K : ℝ) (H D E : Ideal O) (hD : D ≠ 0)
    (hH : K < (Ideal.absNorm H : ℝ)) : mainWeight K H D E = 0 := by
  have hc : cutoffDifference K H D = 0 := by
    by_contra h
    exact (not_le.mpr hH) ((cutoffDifference_nonzero_iff K H D hD).mp h).1
  simp [mainWeight, hc]

theorem mainWeight_norm_le (K : ℝ) (hK : 0 < K) (H D E : Ideal O)
    (hD : D ≠ 0) (hE : E ≠ 0) : ‖mainWeight K H D E‖ ≤ 1 / Real.sqrt K := by
  by_cases hc : cutoffDifference K H D = 0
  · simp [mainWeight, hc]
  have hn : K < (Ideal.absNorm (H * D * E) : ℝ) := by
    exact lt_of_not_ge (fun h => hc (cutoffDifference_eq_zero_of_product_le K hD hE h))
  have hsq : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hle := Real.sqrt_le_sqrt hn.le
  rw [mainWeight, cutoffDifference_eq_neg_one_of_nonzero K H D hD hc]
  simp only [norm_div, Complex.ofReal_neg, Complex.ofReal_one, norm_neg, norm_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact one_div_le_one_div_of_le hsq hle

theorem main_difference_operator_bound {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 < K)
    (G : Ideal O) (hG : G ≠ 0) (H : m → Ideal O)
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hN : 0 ≤ N) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N)
    (A : Matrix m n ℂ) (a : n → ℂ)
    (r : Ideal O → Ideal O → n → ℂ) (hr : ∀ D E j, ‖r D E j‖ ≤ 1) :
    ‖∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) *
      (∑ i, mainWeight K (H i) D E *
        (∑ j, ∑ k, if IsCoprime (column j) (column k) then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
          ∑ j, ‖a j‖ ^ 2) := by
  let B := (1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
    ∑ j, ‖a j‖ ^ 2
  have hB : 0 ≤ B := by
    have hC := (supportConstant_pos ε hε).le
    dsimp [B]
    positivity
  have hterm (D : Ideal O) (hD : D ∈ idealDivisors G)
      (E : Ideal O) (hE : E ∈ idealDivisors G) :
      ‖(UniqueFactorizationMonoid.moebius E : ℂ) *
        (∑ i, mainWeight K (H i) D E *
          (∑ j, ∑ k, if IsCoprime (column j) (column k) then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ ≤ B := by
    have hD0 := IdealDivisorBound.divisor_ne_zero hG hD
    have hE0 := IdealDivisorBound.divisor_ne_zero hG hE
    have he := ideal_coprime_gram_operator_bound ε hε column hcol N hN hnorm A
      (fun j => a j * r D E j) (fun i => mainWeight K (H i) D E) (1 / Real.sqrt K)
      (by positivity) (fun i => mainWeight_norm_le K hK (H i) D E hD0 hE0)
    have hm : (∑ j, ‖a j * r D E j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hr D E j)
    have heB : ‖∑ i, mainWeight K (H i) D E *
        (∑ j, ∑ k, if IsCoprime (column j) (column k) then
          star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0)‖ ≤ B := by
      apply he.trans
      exact mul_le_mul_of_nonneg_left hm (by
        have hC := (supportConstant_pos ε hε).le
        positivity)
    have hmu : ‖(UniqueFactorizationMonoid.moebius E : ℂ)‖ ≤ 1 := by
      unfold UniqueFactorizationMonoid.moebius
      split_ifs <;> simp
    rw [norm_mul]
    calc
      _ ≤ 1 * B := mul_le_mul hmu heB (norm_nonneg _) (by norm_num)
      _ = B := one_mul B
  calc
    _ ≤ ∑ D ∈ idealDivisors G, ‖∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
        (∑ i, mainWeight K (H i) D E *
          (∑ j, ∑ k, if IsCoprime (column j) (column k) then
            star (A i j * (a j * r D E j)) * (A i k * (a k * r D E k)) else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G, B := by
      apply Finset.sum_le_sum
      intro D hD
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun E hE => hterm D hD E hE))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, B]; ring

open ConcretePrimeRowBridge ActualEisensteinCubic

theorem ideal_quadraticRow_norm_le_one (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (J : Ideal O) (z : O) : ‖(idealSexticRow F hFpos hFgood J z) ^ 3‖ ≤ 1 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  rw [norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  exact finiteSquarefreeRow_norm_le_one (fun i : primePool F => i.val)
    (primePool_good F hFgood) (idealSupport F J) z

theorem actual_quadratic_main_difference_bound {m : Type*}
    [Fintype m] [DecidableEq m]
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 < K)
    (G : Ideal O) (hG : G ≠ 0) (H : m → Ideal O) (g : Ideal O → O)
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (N : ℝ) (hN : 0 ≤ N) (hnorm : ∀ J ∈ F, (Ideal.absNorm J : ℝ) ≤ N)
    (a : F → ℂ) :
    let A : Matrix m F ℂ := fun i J => (idealSexticRow F hFpos hFgood J.val (g (H i))) ^ 3
    let r : Ideal O → Ideal O → F → ℂ := fun D E J =>
      (idealSexticRow F hFpos hFgood J.val (g D * g E)) ^ 3
    ‖∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) *
      (∑ i, mainWeight K (H i) D E *
        (∑ J : F, ∑ columnTwo : F, if IsCoprime J.val columnTwo.val then
          star (A i J * (a J * r D E J)) * (A i columnTwo * (a columnTwo * r D E columnTwo)) else 0))‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * ‖operator A‖ ^ 2 * (supportConstant ε hε * N ^ ε) *
          ∑ J : F, ‖a J‖ ^ 2) := by
  dsimp only
  apply main_difference_operator_bound ε hε K hK G hG H (fun J : F => J.val)
    (fun J => hFpos J.val J.property) N hN (fun J => hnorm J.val J.property)
  intro D E J
  exact ideal_quadraticRow_norm_le_one F hFpos hFgood J.val (g D * g E)

end QuadraticMainOperatorBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets -/

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (columnPrimeCoprime quadraticCrossPhase)
open FiniteGaussPhase (canonicalProductGauss)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

def blockRow {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) : ℂ :=
  finiteSexticRow (fun i : S => Ideal.span {p i.val}) (fun i => hg i.val) (fun i => e i.val) u

theorem blockRow_eq_product {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) :
    blockRow p hg S e u = ∏ i ∈ S,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u) :=
  Finset.prod_coe_sort S (fun i =>
    (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u))

theorem blockRow_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) (u : O) :
    blockRow p hg (S ∪ T) e u = blockRow p hg S e u * blockRow p hg T e u := by
  simp only [blockRow_eq_product, Finset.prod_union hd]

theorem blockRow_congr {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (hef : ∀ i ∈ S, e i = f i) (u : O) : blockRow p hg S e u = blockRow p hg S f u := by
  simp only [blockRow_eq_product]
  exact Finset.prod_congr rfl (fun i hi => by rw [hef i hi])

theorem blockRow_one {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 1) u = finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u := by
  simp only [blockRow_eq_product, pow_one, finiteSquarefreeRow]

theorem blockRow_five {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 5) u = star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u) := by
  simp only [blockRow_eq_product, finiteSquarefreeRow, star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0), canonicalSextic_conj_as_row_label]
  ring

theorem threeBlockRow_factor {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (u : O) :
    blockRow p hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) u =
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N u) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P u *
      blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
        (fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) u := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  have hN : ∀ i ∈ N, threeBlockExponent N P v ε₁ ε₂ i = 5 := by
    intro i hi; simp [threeBlockExponent, hi]
  have hP : ∀ i ∈ P, threeBlockExponent N P v ε₁ ε₂ i = 1 := by
    intro i hi
    simp [threeBlockExponent, hi, show i ∉ N from fun hn => Finset.disjoint_left.mp hNP hn hi]
  have hC : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, threeBlockExponent N P v ε₁ ε₂ i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    simp [threeBlockExponent,
      show i ∉ N from fun hn => Finset.disjoint_left.mp hNC hn hi,
      show i ∉ P from fun hp => Finset.disjoint_left.mp hPC hp hi]
  rw [blockRow_union p hg (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    blockRow_union p hg N P hNP, blockRow_congr p hg N _ _ hN,
    blockRow_congr p hg P _ _ hP, blockRow_congr p hg _ _ _ hC,
    blockRow_five, blockRow_one]

theorem masked_block_radial_poisson_product {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z * blockRow p hg S e z *
      W (‖eisEmbedding z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) * canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) /
        (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * blockRow p hg S e d /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, star (blockRow p hg S e h) * paperRadialFourier W
            (lengthScale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2)) := by
  let Q := fun i : S => Ideal.span {p i.val}
  let q := fun i : S => p i.val
  let hQ := columnPrimeCoprime p hcop S
  let j := fun i : S => e i.val
  have h := canonical_masked_radial_poisson_collected (fun i => Ideal.span {p i}) hinj M
    Q hQ (fun i => hg i.val) (fun i => hc i.val) j
    (fun i => he i.val i.property) (fun i => he6 i.val i.property) W lengthScale hL
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding (∏ i ∈ S, p i)‖ := by
    rw [GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q, Finset.prod_coe_sort]
  dsimp only at h
  rw [hn] at h
  have hrow : finiteSexticRow Q (fun i => hg i.val) j = blockRow p hg S e := rfl
  rw [hrow] at h
  rw [h]
  let a := fun E : Finset ι =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * blockRow p hg S e d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)
  let F := fun E : Finset ι => fun t : ℝ =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    paperRadialFourier W (lengthScale * t / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2))
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset a F
  rw [hrow] at ht
  change ((lengthScale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hg i.val) j /
      (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) * _ = _
  calc
    _ = ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
        ∑ E ∈ M.powerset, a E * ∑' h : O, star (blockRow p hg S e h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [ht]; ring

def cubeBaseFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) : ℂ :=
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val
  gaussBlock p hp hg C e * blockRow p hg C e d * star (blockRow p hg C e h)

def threeGaussRowFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
    (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) *
    (blockRow p hg S e d * star (blockRow p hg S e h))

def cubeTransformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
    quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
    quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
    star (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
      FirstCauchyArithmetic.firstPassColumnMinus p hp hcop hg C₁ (d * crtLabel p B v ε₁ ε₂ true) N *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
    (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
      FirstCauchyArithmetic.firstPassColumnPlus p hp hcop hg C₂ (d * crtLabel p B v ε₁ ε₂ false) P *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h))

theorem threeGaussRowFactor_eq_transformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeTransformedPair p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  unfold threeGaussRowFactor
  dsimp only
  rw [a_weighted_three_cube_gauss p hp hcop hg hc hpr N P B hNP hNB hPB,
    threeBlockRow_factor p hg N P B hNP hNB hPB,
    threeBlockRow_factor p hg N P B hNP hNB hPB]
  simp only [cubeTransformedPair, cubeBaseFactor,
    FirstCauchyArithmetic.firstPassColumnMinus, FirstCauchyArithmetic.firstPassColumnPlus,
    finiteSquarefreeRow_mul, star_mul, star_star]
  ring

theorem a_weighted_three_block_radial_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (M N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
    let e := threeBlockExponent N P v ε₁ ε₂
    star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
      (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z * blockRow p hg S e z *
        W (‖eisEmbedding z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, paperRadialFourier W
            (lengthScale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2)) *
              cubeTransformedPair p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  dsimp only
  have he : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i ≠ 0 := by
    intro i hi
    by_cases hn : i ∈ N
    · simp [threeBlockExponent, hn]
    by_cases hp' : i ∈ P
    · simp [threeBlockExponent, hn, hp']
    · have hiC : i ∈ cubeActiveSupport B v ε₁ ε₂ := by simpa [hn, hp'] using hi
      simp only [threeBlockExponent, ite_eq_right hn, ite_eq_right hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  have he6 : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i < 6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hcop hg hc M _ _ he he6 W lengthScale hL]
  simp_rw [← threeGaussRowFactor_eq_transformedPair p hp hcop hg hc hpr N P B hNP hNB hPB]
  simp only [Finset.mul_sum, ← tsum_mul_left]
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro h
  unfold threeGaussRowFactor
  dsimp only
  ring

end FirstPassCubeLabels

section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace LocalLogFourier

theorem coupled_positive_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (FourierBridge.coefficientMomentBound 0 P +
      FourierBridge.coefficientMomentBound J P)
  let C : ℝ := B / m ^ A
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
        (FourierBridge.coefficientMomentBound_nonneg J P hP))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    simpa [C, B, P, b, K, Lwin, m] using hbound

end LocalLogFourier

namespace EisensteinSchwartzPoisson

theorem paperRadialFourier_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_schwartz V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end EisensteinSchwartzPoisson
end

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

section
abbrev O := ActualEisensteinCubic.O

variable {F : Type*} [Field F] [Fintype F]

def rootCard (F : Type*) [Fintype F] : ℝ := Real.sqrt (Fintype.card F)

theorem rootCard_pos : 0 < rootCard F := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩

theorem rootCard_sq : rootCard F ^ 2 = (Fintype.card F : ℝ) := Real.sq_sqrt (by positivity)

def tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) : ℂ :=
  (rootCard F : ℂ)⁻¹ * gaussSum (χ ^ j) ψ

def bracket (χ : MulChar F ℂ) (j : ℕ) (x : F) : ℂ :=
  if j = 4 then
    (rootCard F : ℂ)⁻¹ * (-1 + (Fintype.card F : ℂ) * if x = 0 then 1 else 0)
  else if j = 0 then (rootCard F : ℂ)⁻¹ * (χ ^ 2)⁻¹ x
  else (χ ^ (j + 2))⁻¹ x

def phase (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (ε : Fˣ) : ℂ :=
  if j = 4 then tau χ (ψ.mulShift (-1)) 4
  else if j = 0 then -tau χ ψ 2 * (χ ^ 2)⁻¹ ε
  else tau χ (ψ.mulShift (-1)) j * tau χ ψ (j + 2) * (χ ^ (j + 2))⁻¹ ε

theorem norm_tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχ : χ ^ j ≠ 1) (hψ : ψ.IsPrimitive) : ‖tau χ ψ j‖ = 1 :=
  ShortDraftGauss.norm_normalized_gaussSum (χ ^ j) ψ hχ hψ

theorem bracket_four_split (χ : MulChar F ℂ) (x : F) :
    bracket χ 4 x = -(rootCard F : ℂ)⁻¹ + (rootCard F : ℂ) * if x = 0 then 1 else 0 := by
  have hr : (rootCard F : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard F : ℂ) ^ 2 = (Fintype.card F : ℂ) := by exact_mod_cast (rootCard_sq (F := F))
  simp only [bracket, ↓reduceIte]
  rw [← hsq]
  field_simp

theorem bracket_four_cube_split (χ : MulChar F ℂ) (n b : F) :
    bracket χ 4 (n * b ^ 3) = -(rootCard F : ℂ)⁻¹ +
      (rootCard F : ℂ) * (if n = 0 then 1 else 0) +
      (rootCard F : ℂ) * (if n ≠ 0 ∧ b = 0 then 1 else 0) := by
  rw [bracket_four_split]
  by_cases hn : n = 0 <;> by_cases hb : b = 0 <;> simp [hn, hb]

theorem bracket_zero_mask (χ : MulChar F ℂ) (j : ℕ) (hj : j ≠ 4) :
    bracket χ j 0 = 0 := by simp [bracket, hj]

theorem norm_bracket_nonexceptional (χ : MulChar F ℂ) (j : ℕ)
    (hj4 : j ≠ 4) (hj0 : j ≠ 0) (x : F) :
    ‖bracket χ j x‖ = if x = 0 then 0 else 1 := by
  simp only [bracket, ite_eq_right hj4, ite_eq_right hj0]
  by_cases hx : x = 0
  · simp [hx]
  · rw [ite_eq_right hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ (j + 2))⁻¹) (Units.mk0 x hx)

theorem norm_bracket_zero (χ : MulChar F ℂ) (x : F) :
    ‖bracket χ 0 x‖ = (rootCard F)⁻¹ * if x = 0 then 0 else 1 := by
  simp only [bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]
  congr 1
  by_cases hx : x = 0
  · simp [hx]
  · rw [ite_eq_right hx]
    exact FiniteRayExpansion.norm_char_unit ((χ ^ 2)⁻¹) (Units.mk0 x hx)

theorem norm_bracket_four_nonzero (χ : MulChar F ℂ) (x : F) (hx : x ≠ 0) :
    ‖bracket χ 4 x‖ = (rootCard F)⁻¹ := by
  rw [bracket_four_split]
  simp [hx, Complex.norm_real, Real.norm_of_nonneg rootCard_pos.le]

theorem norm_bracket_four_zero (χ : MulChar F ℂ) :
    ‖bracket χ 4 (0 : F)‖ = ((Fintype.card F : ℝ) - 1) / rootCard F := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  simp only [bracket, ↓reduceIte, mul_one, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg rootCard_pos.le]
  have heq : (-1 + (Fintype.card F : ℂ)) = (((Fintype.card F : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hq)]
  ring

end

section
variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem shifted_power_nontrivial (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4) : χ ^ (j + 2) ≠ 1 := by
  by_cases hj : j = 5
  · subst j
    have heq : χ ^ (5 + 2) = χ ^ 1 := by
      rw [show (5 + 2 : ℕ) = 6 + 1 by decide, pow_add, h6, one_mul]
    rw [heq]
    exact hn 1 (by decide) (by decide)
  · exact hn (j + 2) (by omega) (by omega)

theorem phase_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (h6 : χ ^ 6 = 1) (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj6 : j < 6) (ε : Fˣ) :
    ‖phase χ ψ j ε‖ = 1 := by
  have hψminus : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (hψ (a := (-1 : F)) (by simp))
  by_cases hj4 : j = 4
  · subst j
    simp only [phase, ↓reduceIte]
    exact norm_tau χ _ 4 (hn 4 (by decide) (by decide)) hψminus
  by_cases hj0 : j = 0
  · subst j
    simp only [phase, ite_eq_right hj4, ↓reduceIte, norm_mul, norm_neg]
    rw [norm_tau χ ψ 2 (hn 2 (by decide) (by decide)) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num
  · simp only [phase, ite_eq_right hj4, ite_eq_right hj0, norm_mul]
    rw [norm_tau χ _ j (hn j hj0 hj6) hψminus,
      norm_tau χ ψ (j + 2) (shifted_power_nontrivial χ h6 hn j hj0 hj6 hj4) hψ,
      FiniteRayExpansion.norm_char_unit]
    norm_num

end

open ActualEisensteinCubic

noncomputable local instance quotientField (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P

noncomputable local instance quotientFintype (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_phase_norm (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (ε : (O ⧸ P)ˣ) :
    ‖phase (canonicalSextic P hgood) ψ j ε‖ = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  exact phase_norm (canonicalSextic P hgood) ψ (canonicalSextic_pow_six P hgood)
    (fun k hk0 hk6 => canonicalSextic_pow_ne_one P hgood hchar hk0 hk6) hψ j hj6 ε

end LocalReflectionBrackets

open scoped Classical BigOperators
open AddChar MulChar
namespace LocalReflectionBrackets

variable {F : Type*} [Field F] [Fintype F]

def activeRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ *
    ∑ h : Fˣ, (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
      (((χ⁻¹) ^ 2) (σ * h)) * ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

open ActualEisensteinCubic
noncomputable local instance quotientFieldNormalized (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
noncomputable local instance quotientFintypeNormalized (P : Ideal O) [P.IsMaximal] : Fintype (O ⧸ P) := Fintype.ofFinite _

theorem canonical_A5_normalized (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    activeRow (canonicalSextic P hgood) ψ j σ ε x =
      (((canonicalSextic P hgood)⁻¹) ^ 2) σ *
        phase (canonicalSextic P hgood) ψ j ε * bracket (canonicalSextic P hgood) j x := by
  let χ := canonicalSextic P hgood
  have hψne : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ (a := 1) one_ne_zero
  have hr : (rootCard (O ⧸ P) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt rootCard_pos)
  have hsq : (rootCard (O ⧸ P) : ℂ) ^ 2 = (Fintype.card (O ⧸ P) : ℂ) := by
    exact_mod_cast (rootCard_sq (F := O ⧸ P))
  by_cases hj0 : j = 0
  · subst j
    have hh := canonical_A5_jzero_active P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte]
    rw [← hsq]
    field_simp
  by_cases hj4 : j = 4
  · subst j
    have hh := canonical_A5_jfour P hgood hchar ψ hψne σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    have hqNat : 1 ≤ Fintype.card (O ⧸ P) := Fintype.card_pos_iff.mpr ⟨0⟩
    have hcardunits : (Fintype.card (O ⧸ P)ˣ : ℂ) = (Fintype.card (O ⧸ P) : ℂ) - 1 := by
      rw [Fintype.card_units, Nat.cast_sub hqNat, Nat.cast_one]
    have hsum : (if (ε : O ⧸ P) * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1) =
        -1 + (Fintype.card (O ⧸ P) : ℂ) * if x = 0 then 1 else 0 := by
      by_cases hx : x = 0
      · simp [hx, hcardunits]
        ring
      · simp [hx, mul_ne_zero (Units.ne_zero ε) hx]
    rw [hsum]
    simp only [phase, bracket, tau,  ↓reduceIte]
    rw [← hsq]
    field_simp
  · have hh := canonical_A5_nonexceptional P hgood hchar ψ j hj0 hj6 hj4 σ ε x
    simp only [Nat.card_eq_fintype_card] at hh
    rw [activeRow, hh]
    simp only [phase, bracket, tau, ite_eq_right hj4, ite_eq_right hj0]
    rw [← hsq]
    field_simp

theorem canonical_A5_norm_eq_bracket (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    ‖activeRow (canonicalSextic P hgood) ψ j σ ε x‖ =
      ‖bracket (canonicalSextic P hgood) j x‖ := by
  rw [canonical_A5_normalized P hgood hchar ψ hψ j hj6 σ ε x,
    norm_mul, norm_mul, canonical_phase_norm P hgood hchar ψ hψ j hj6 ε,
    FiniteRayExpansion.norm_char_unit, one_mul, one_mul]

theorem canonical_bracket_four_cube_split (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (n b : O) :
    bracket (canonicalSextic P hgood) 4 (Ideal.Quotient.mk P (n * b ^ 3)) =
      -(rootCard (O ⧸ P) : ℂ)⁻¹ + (rootCard (O ⧸ P) : ℂ) * (if n ∈ P then 1 else 0) +
      (rootCard (O ⧸ P) : ℂ) * (if n ∉ P ∧ b ∈ P then 1 else 0) := by
  rw [map_mul, map_pow, bracket_four_cube_split]
  simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]

end LocalReflectionBrackets

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion -/

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
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open MixedCrossSeparation (quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport firstPassColumnMinus firstPassColumnPlus)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)

def fixedRayExpansion {ι : Type*} (p : ι → O) (F S : Finset ι) : ℂ :=
  ∑ χ : RayCharacter, ∑ η : RayCharacter,
    crossCoeff χ η * supportRay p χ S * supportRay p η F

theorem fixedRayExpansion_eq_cross {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F S : Finset ι) (hd : Disjoint S F) :
    fixedRayExpansion p F S = quadraticCrossPhase p hg S F :=
  (RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc S F hd).symm

def cubeMinusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
    firstPassColumnMinus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ true) S

def cubePlusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
    firstPassColumnPlus p hp hcop hg C (d * crtLabel p B v ε₁ ε₂ false) S

def idealPairReindex {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (R : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (h : O) : ℂ :=
  let P := fun i => Ideal.span {p i}
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ R.powerset,
      (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
      star (conjugateIdealRowSum (supportIdealFamily P (R \ D))
        (supportIdealFamily_pos P (R \ D)) (supportIdealFamily_good P hg (R \ D))
        (fun I => star (supportRay p r.1 (recoveredSupport P (R \ D) I)) *
          C₁ (D ∪ recoveredSupport P (R \ D) I)) h) *
      conjugateIdealRowSum (supportIdealFamily P (R \ D))
        (supportIdealFamily_pos P (R \ D)) (supportIdealFamily_good P hg (R \ D))
        (fun I => supportRay p r.2 (recoveredSupport P (R \ D) I) *
          C₂ (D ∪ recoveredSupport P (R \ D) I)) h

theorem threeGaussRowFactor_eq_ray_columns {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
        star (supportMobius (fun i => Ideal.span {p i}) N *
          cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d N *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
        (supportMobius (fun i => Ideal.span {p i}) P *
          cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d P *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h)) := by
  rw [threeGaussRowFactor_eq_transformedPair p hp hcop hg hc hpr N P B hNP hNB hPB]
  unfold cubeTransformedPair cubeMinusCoefficient cubePlusCoefficient
  rw [fixedRayExpansion_eq_cross p hp hcop hg hc (cubeOddSupport B v ε₁ ε₂) N
      (hNB.mono_right (Finset.filter_subset _ _)),
    fixedRayExpansion_eq_cross p hp hcop hg hc (cubeOddSupport B v ε₁ ε₂) P
      (hPB.mono_right (Finset.filter_subset _ _))]
  simp only [star_mul, star_star]
  ring

theorem sum_threeGaussRowFactor_eq_ideal_rows {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (R B : Finset ι) (hRB : Disjoint R B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg R
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d) h := by
  let A := cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d
  let C := cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d
  have hsum :
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        quadraticCrossPhase p hg N P *
          star (supportMobius (fun i => Ideal.span {p i}) N * A N *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
          (supportMobius (fun i => Ideal.span {p i}) P * C P *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N hN
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hd : Disjoint N P
    · rw [ite_eq_left hd, ite_eq_left hd,
        threeGaussRowFactor_eq_ray_columns p hp hcop hg hc hpr N P B hd
          (hRB.mono_left (Finset.mem_powerset.mp hN))
          (hRB.mono_left (Finset.mem_powerset.mp hP))]
      dsimp only [A, C]
      ring
    · simp [hd]
  rw [hsum]
  congr 1
  exact FirstCauchyArithmetic.quadratic_phase_reindex_to_ideal_rows p hp hinj hg hc R A C h

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic
open FourierBridge (logPhase logPhase_norm logPhase_continuous_left)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem two_variable_radial_separation (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
        ∫ t : ℝ, (V₁ x * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K := by
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let M : Bool → ℝ := fun j => if j then M₂ else M₁
  have hM : ∀ j, 0 ≤ M j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j := by
    intro j; cases j
    · exact hV₁
    · exact hV₂
  obtain ⟨K, hK, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_schwartz
    W V (fun _ => -1) M hM hV A J
  refine ⟨K, hK, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hbound⟩ := hsep R hR
  refine ⟨b, ?_, hi, hbound⟩
  intro x y
  have hs := hb (fun j => if j then y else x)
  simpa only [V, Fintype.prod_bool, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    neg_one_mul, mul_neg_one, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using hs

def logTwistMinus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * star (V (y S) * logPhase t (-(y S)))

def logTwistPlus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * (V (y S) * logPhase t (-(y S)))

theorem threeGaussRowFactor_log_twist {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (t : ℝ) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h =
    (V₁ (y₁ N) * logPhase t (-(y₁ N))) * (V₂ (y₂ P) * logPhase t (-(y₂ P))) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  simp only [threeGaussRowFactor, logTwistMinus, logTwistPlus, star_mul, star_star]
  ring

theorem integrable_log_pair (b : 𝓢(ℝ, ℂ)) (x y : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => b t * (logPhase t x * logPhase t y * c)) volume := by
  apply b.integrable.mul_bdd (c := ‖c‖)
  · exact (((logPhase_continuous_left x).mul (logPhase_continuous_left y)).mul_const c).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp only [norm_mul, logPhase_norm, one_mul, le_refl])

theorem smooth_cube_pairs_to_ideal_rows {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
      Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h) volume ∧
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N) - y₂ P))) *
          threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
      ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_separation W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro R hR
  obtain ⟨b, hsep, hbint, hbnd⟩ := hs R hR
  let G : ℝ → Finset ι → Finset ι → ℂ := fun t N P => if Disjoint N P then
    b t * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0
  have hGint (N P : Finset ι) : Integrable (fun t => G t N P) volume := by
    by_cases hd : Disjoint N P
    · simp only [G, ite_eq_left hd]
      have hi := integrable_log_pair b (-(y₁ N)) (-(y₂ P))
        (V₁ (y₁ N) * V₂ (y₂ P) * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h)
      convert hi using 1
      funext t
      rw [threeGaussRowFactor_log_twist]
      ring
    · simp only [G, ite_eq_right hd]
      exact integrable_zero _ _ _
  have hGsum (t : ℝ) :
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) =
        b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
    calc
      _ = b t * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
          (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0) := by
            simp only [G, Finset.mul_sum, mul_ite, mul_zero]
      _ = _ := by
        rw [sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
        ring
  have hint : Integrable (fun t => ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) volume :=
    integrable_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))
  refine ⟨b, hbint, hbnd, ?_, ?_⟩
  · simpa only [hGsum] using hint
  · have hterm (N P : Finset ι) :
        (if Disjoint N P then
          (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N) - y₂ P))) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ∫ t : ℝ, G t N P := by
      by_cases hd : Disjoint N P
      · simp only [G, ite_eq_left hd]
        rw [hsep (y₁ N) (y₂ P), ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [threeGaussRowFactor_log_twist]
        ring
      · simp [G, hd]
    calc
      _ = ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, ∫ t : ℝ, G t N P := by
        apply Finset.sum_congr rfl
        intro N hN
        exact Finset.sum_congr rfl (fun P hP => hterm N P)
      _ = ∫ t : ℝ, ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P := by
        rw [integral_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))]
        apply Finset.sum_congr rfl
        intro N hN
        exact (integral_finsetSum _ (fun P _ => hGint N P)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hGsum t

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)

def primeProductNorm {ι : Type*} (p : ι → O) (S : Finset ι) : ℝ :=
  ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2

theorem primeProductNorm_pos {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2

theorem primeProductNorm_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

def columnLog {ι : Type*} (p : ι → O) (X : ℝ) (S : Finset ι) : ℝ :=
  Real.log (primeProductNorm p S / X)

def firstDualScale {ι : Type*} (p : ι → O) (C : Finset ι)
    (lengthScale X₁ X₂ : ℝ) (d h : O) : ℝ :=
  lengthScale * ‖eisEmbedding h‖ ^ 2 /
    (‖eisEmbedding d‖ ^ 2 * primeProductNorm p C * X₁ * X₂)

theorem actual_radial_argument {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (N P C : Finset ι)
    (hNP : Disjoint N P) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (lengthScale X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (d h : O) :
    firstDualScale p C lengthScale X₁ X₂ d h * Real.exp (-(columnLog p X₁ N) - columnLog p X₂ P) =
      lengthScale * ‖eisEmbedding h‖ ^ 2 /
        (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ C)) := by
  rw [primeProductNorm_union p (N ∪ P) C (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    primeProductNorm_union p N P hNP]
  simp only [columnLog, sub_eq_add_neg, Real.exp_add, Real.exp_neg]
  rw [Real.exp_log (div_pos (primeProductNorm_pos p hp N) hX₁),
    Real.exp_log (div_pos (primeProductNorm_pos p hp P) hX₂)]
  simp only [firstDualScale, div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp [ne_of_gt hX₁, ne_of_gt hX₂]

def normalizedColumn {ι : Type*} (p : ι → O) (C : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  C S / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)

theorem threeGaussRowFactor_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (normalizedColumn p C₁) (normalizedColumn p C₂) d h =
    ((‖eisEmbedding (∏ i ∈ N, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ P, p i)‖ : ℂ)⁻¹) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  have hs (x : ℝ) : star (x : ℂ) = (x : ℂ) := by simp
  have hsi (x : ℝ) : star ((x : ℂ)⁻¹) = (x : ℂ)⁻¹ := by simp
  simp only [threeGaussRowFactor, normalizedColumn, div_eq_mul_inv, star_mul, hsi]
  ring

theorem actual_pair_prefactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (lengthScale : ℝ) (d h : O) :
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
        (normalizedColumn p C₁) (normalizedColumn p C₂) d h := by
  rw [threeGaussRowFactor_normalized]
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩), Finset.prod_union hNP]
  simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem cube_integral_of_radial_separation {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (R : ℝ)
    (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
      ∫ t : ℝ, (V₁ x * FourierBridge.logPhase t (-x)) *
        (V₂ y * FourierBridge.logPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h) volume ∧
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
  let G : ℝ → Finset ι → Finset ι → ℂ := fun t N P => if Disjoint N P then
    b t * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0
  have hGint (N P : Finset ι) : Integrable (fun t => G t N P) volume := by
    by_cases hd : Disjoint N P
    · simp only [G, ite_eq_left hd]
      convert integrable_log_pair b (-(y₁ N)) (-(y₂ P))
        (V₁ (y₁ N) * V₂ (y₂ P) * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) using 1
      funext t
      rw [threeGaussRowFactor_log_twist]
      ring
    · simp only [G, ite_eq_right hd]
      exact integrable_zero _ _ _
  have hGsum (t : ℝ) :
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) =
        b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
    calc
      _ = b t * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
          (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0) := by
            simp only [G, Finset.mul_sum, mul_ite, mul_zero]
      _ = _ := by
        rw [sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
        ring
  have hint : Integrable (fun t => ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) volume :=
    integrable_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))
  constructor
  · simpa only [hGsum] using hint
  · have hterm (N P : Finset ι) :
        (if Disjoint N P then
          (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ∫ t : ℝ, G t N P := by
      by_cases hd : Disjoint N P
      · simp only [G, ite_eq_left hd]
        rw [hsep (y₁ N) (y₂ P), ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [threeGaussRowFactor_log_twist]
        ring
      · simp [G, hd]
    calc
      _ = ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, ∫ t : ℝ, G t N P := by
        apply Finset.sum_congr rfl
        intro N hN
        exact Finset.sum_congr rfl (fun P hP => hterm N P)
      _ = ∫ t : ℝ, ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P := by
        rw [integral_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))]
        apply Finset.sum_congr rfl
        intro N hN
        exact (integral_finsetSum _ (fun P _ => hGint N P)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hGsum t

theorem actual_first_kernel_to_ideal_rows {ι : Type*} [DecidableEq ι]
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
        Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
          idealPairReindex p hg F
            (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistMinus (normalizedColumn p C₁) V₁ (columnLog p X₁) t) d)
            (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistPlus (normalizedColumn p C₂) V₂ (columnLog p X₂) t) d) h) volume ∧
        (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
          (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
          ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
          threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
        ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
          idealPairReindex p hg F
            (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistMinus (normalizedColumn p C₁) V₁ (columnLog p X₁) t) d)
            (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
              (logTwistPlus (normalizedColumn p C₂) V₂ (columnLog p X₂) t) d) h := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_separation W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  let R := firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h
  have hR : 0 < R := by
    unfold R firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hb, hi, hbound⟩ := hs R hR
  have hpair := cube_integral_of_radial_separation p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    (normalizedColumn p C₁) (normalizedColumn p C₂) d h W V₁ V₂ (columnLog p X₁) (columnLog p X₂) R b hb
  refine ⟨b, hi, hbound, hpair.1, ?_⟩
  rw [← hpair.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · rw [ite_eq_left hNP, ite_eq_left hNP]
    have hNB : Disjoint N B := hFB.mono_left (Finset.mem_powerset.mp hN)
    have hPB : Disjoint P B := hFB.mono_left (Finset.mem_powerset.mp hP)
    have harg := actual_radial_argument p hp N P (cubeActiveSupport B v ε₁ ε₂) hNP
      (hNB.mono_right (Finset.filter_subset _ _)) (hPB.mono_right (Finset.filter_subset _ _))
      lengthScale X₁ X₂ hX₁ hX₂ d h
    change R * Real.exp (-(columnLog p X₁ N) - columnLog p X₂ P) = _ at harg
    rw [harg]
    have hpre := actual_pair_prefactor p hp hcop hg N P B hNP hNB hPB v ε₁ ε₂ C₁ C₂ lengthScale d h
    calc
      _ = (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)))) *
          (((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) := by ring
      _ = _ := by rw [hpre]; ring
  · simp [hNP]

end FirstPassCubeLabels

open scoped BigOperators Classical
namespace QuadraticDivisorSplit
abbrev O := ActualEisensteinCubic.O

theorem exists_unique_split (B C D : Ideal O) (hBC : IsCoprime B C)
    (hD : D ∣ B * C) :
    ∃! x : Ideal O × Ideal O, x.1 ∣ B ∧ x.2 ∣ C ∧ x.1 * x.2 = D := by
  obtain ⟨D₁, D₂, h₁, h₂, hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hD
  refine ⟨(D₁, D₂), ⟨h₁, h₂, hprod.symm⟩, ?_⟩
  intro y hy
  apply Prod.ext
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.mono hy.1 h₂).dvd_of_dvd_mul_right
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_right _ _
    · apply (hBC.mono h₁ hy.2.1).dvd_of_dvd_mul_right
      rw [hy.2.2, hprod]
      exact dvd_mul_right _ _
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.symm.mono hy.2.1 h₁).dvd_of_dvd_mul_left
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_left _ _
    · apply (hBC.symm.mono h₂ hy.1).dvd_of_dvd_mul_left
      rw [hy.2.2, hprod]
      exact dvd_mul_left _ _

theorem split_product_injective (B C : Ideal O) (hBC : IsCoprime B C) :
    Function.Injective (fun x : {x : Ideal O × Ideal O // x.1 ∣ B ∧ x.2 ∣ C} =>
      x.val.1 * x.val.2) := by
  intro x y hxy
  have hD : x.val.1 * x.val.2 ∣ B * C := mul_dvd_mul x.property.1 x.property.2
  obtain ⟨z, hz, huniq⟩ := exists_unique_split B C (x.val.1 * x.val.2) hBC hD
  apply Subtype.ext
  exact (huniq x.val ⟨x.property.1, x.property.2, rfl⟩).trans
    (huniq y.val ⟨y.property.1, y.property.2, hxy.symm⟩).symm

open IdealMobiusDivisorSum

theorem divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)

theorem sum_divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he

theorem residual_norm_le (D I : Ideal O) (hD : D ≠ 0) (N : ℝ)
    (hN : (Ideal.absNorm (D * I) : ℝ) ≤ N) :
    (Ideal.absNorm I : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hpos : (0 : ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  apply (le_div_iff₀ hpos).mpr
  simpa only [map_mul, Nat.cast_mul, mul_comm] using hN

end QuadraticDivisorSplit

end

end OAI

end

