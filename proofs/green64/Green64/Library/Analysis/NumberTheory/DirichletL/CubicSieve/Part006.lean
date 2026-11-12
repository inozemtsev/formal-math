module

public import Green64.Library.OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part005
public import Green64.Library.OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularRecursion

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks -/

section

namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem inputConjugateRow_smoothed_frequency_blocks
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
    ∑ G ∈ F.powerset,
      (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
      ∑ E : G.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)) *
        ∑' k : O,
          secondFrequencyKernel p hp hg hinj F Ψ Ψ m
            (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
            (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G hG
  change secondOverlapBlock p hp hg hinj F G Ψ m c d H W Y = _
  rw [secondOverlapBlock_eq_modes p hp hg hinj F G Ψ m c d H W Y hY]
  congr 1
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  congr 1
  apply tsum_congr
  intro k
  exact residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d
    (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) k W Y

theorem firstCoreInputRow_finite_le_frequency_blocks
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    let Ψ' := firstCoreTwist negative χ Ψ r
    let m' := m * FirstPassCubeLabels.b0Label p B v ε₁ ε₂
    let c' := c * FirstPassCubeLabels.jLabel p B v ε₁ ε₂
    let H' := firstCoreTest H V y negative t D
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑ G ∈ (F \ D).powerset,
        (↑(‖secondInputCoefficient p hg Ψ' m' c' d (fun _ => 1) G‖ ^ 2) : ℂ) *
        ∑ E : G.powerset,
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
            (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)) *
          ∑' k : O,
            secondFrequencyKernel p hp hg hinj (F \ D) Ψ' Ψ' m'
              (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c' d
              (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
              (fun U => H' (G ∪ U)) (fun U => H' (G ∪ U)) rowMajorant Y).re := by
  dsimp only
  have h := finite_row_energy_le_rowMajorant
    (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) T Y hY hT
  rw [firstCoreInputRow_smoothed_sign p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t rowMajorant Y,
    inputConjugateRow_smoothed_frequency_blocks p hp hg hinj hc] at h
  · exact h
  · exact hY

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportConjugateSum supportMobius)
open RayFourExpansion (RayCharacter)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma finiteSquarefreeRow_zero_of_nonempty (S : Finset ι) (hS : S.Nonempty) :
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 0 = 0 := by
  obtain ⟨i, hi⟩ := hS
  apply FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S 0
  have h : ∃ j ∈ S, (0 : O) ∈ Ideal.span {p j} := ⟨i, hi, Ideal.zero_mem _⟩
  simp only [rowCoprimeMask, ite_eq_left h]

theorem inputConjugateRow_zero (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) : inputConjugateRow p hg F Ψ m c d H 0 = H ∅ := by
  unfold inputConjugateRow supportConjugateSum
  rw [Finset.sum_eq_single ∅]
  · have hm : supportMobius (fun i => Ideal.span {p i}) ∅ = 1 := by
      simp only [supportMobius, Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one]
    rw [hm]
    simp [secondInputCoefficient, rowCoprimeMask, finiteSquarefreeRow]
  · intro S hS hne
    rw [finiteSquarefreeRow_zero_of_nonempty p hg S (Finset.nonempty_iff_ne_empty.mpr hne),
      star_zero, mul_zero]
  · simp

theorem firstCoreInputRow_zero
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t 0 =
      firstCoreTest H V y negative t D ∅ := by
  unfold firstCoreInputRow
  simp only [neg_zero, ite_self, inputConjugateRow_zero]

end

def nonzeroRowMajorantSum (P : O → ℂ) (Y : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else
    rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)

lemma nonzeroRowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => if z = 0 then 0 else
      rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz]
  simp

theorem nonzeroRowMajorantSum_eq_sub (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum P Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) -
        (↑(‖P 0‖ ^ 2) : ℂ) := by
  have h := (rowMajorant_summable P Y hY).tsum_eq_add_tsum_ite 0
  have h0 : rowMajorant (0 : ℝ) = 1 := rowMajorant_one 0 (by norm_num)
  simp only [map_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, h0, one_mul] at h
  change _ = _ + nonzeroRowMajorantSum P Y at h
  rw [h]
  ring

theorem finite_nonzero_row_energy_le_majorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤ (nonzeroRowMajorantSum P Y).re := by
  have hs := nonzeroRowMajorant_summable P Y hY
  unfold nonzeroRowMajorantSum
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (if z = 0 then (0 : ℂ) else
        rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : |‖eisEmbedding z‖ ^ 2 / Y| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)]
        apply (div_le_one hY).2
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [ite_eq_right (hT0 z hz), rowMajorant_one _ hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      split_ifs
      · norm_num
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem inputConjugateRow_nonzero_correction (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum (inputConjugateRow p hg F Ψ m c d H) Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) - (↑(‖H ∅‖ ^ 2) : ℂ) := by
  rw [nonzeroRowMajorantSum_eq_sub _ Y hY, inputConjugateRow_zero]

theorem firstCoreInputRow_nonzero_correction
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (Y : ℝ) (hY : 0 < Y) :
    nonzeroRowMajorantSum (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) Y =
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) -
          (↑(‖firstCoreTest H V y negative t D ∅‖ ^ 2) : ℂ) := by
  rw [nonzeroRowMajorantSum_eq_sub _ Y hY, firstCoreInputRow_zero]

theorem firstCoreInputRow_finite_le_corrected_source
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0) :
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re -
          ‖firstCoreTest H V y negative t D ∅‖ ^ 2 := by
  have h := finite_nonzero_row_energy_le_majorant
    (firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t) T Y hY hT hT0
  rw [firstCoreInputRow_nonzero_correction p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t Y hY,
    Complex.sub_re, Complex.ofReal_re] at h
  exact h

end

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

lemma firstCoreTest_empty_mass {ι : Type*} [DecidableEq ι]
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (t : ℝ) (D : Finset ι) :
    ‖firstCoreTest H V y negative t D ∅‖ ^ 2 = ‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2 := by
  cases negative <;> simp only [firstCoreTest, Finset.union_empty, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star, FourierBridge.logPhase_norm, mul_one, mul_pow]

theorem firstCoreInputRow_integrated_le_corrected_source
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0)
    {k : ℝ → ℝ} (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
    (∫ t : ℝ, k t *
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re) -
      (‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2) * ∫ t : ℝ, k t := by
  let mass := ‖H D‖ ^ 2 * ‖V (y D)‖ ^ 2
  let source := fun t : ℝ =>
    (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re
  have isource : Integrable (fun t : ℝ => k t * source t) volume :=
    firstCoreInputRow_majorant_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r Y hY hk
  have icorr : Integrable (fun t : ℝ => k t * (source t - mass)) volume := by
    simp only [mul_sub]
    exact isource.sub (hk.mul_const mass)
  have hpoint (t : ℝ) : k t * (∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      k t * (source t - mass) := by
    have h := firstCoreInputRow_finite_le_corrected_source p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t T Y hY hT hT0
    rw [firstCoreTest_empty_mass] at h
    exact mul_le_mul_of_nonneg_left h (hk0 t)
  calc
    _ ≤ ∫ t : ℝ, k t * (source t - mass) := by
      apply integral_mono _ icorr hpoint
      simp only [Finset.mul_sum]
      exact integrable_finsetSum _ (fun z hz =>
        firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk)
    _ = _ := by
      simp only [mul_sub]
      rw [integral_sub isource (hk.mul_const mass), integral_mul_const]
      dsimp only [source, mass]
      ring

end

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeRadical aLabel jLabel j2Label squarefreeLabel b0Label
  bit retained parity b0Exponent)

lemma span_dvd_of_element_dvd {a b : O} (h : a ∣ b) :
    (Ideal.span {a} : Ideal O) ∣ Ideal.span {b} := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨Ideal.span {c}, (Ideal.span_singleton_mul_span_singleton a c).symm⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_add (B : Finset ι) (u v : ι → ℕ) :
    primeProduct p B (fun i => u i + v i) = primeProduct p B u * primeProduct p B v := by
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma aLabel_dvd_primeProduct (B : Finset ι) (v : ι → ℕ) (ε : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : aLabel p B ε ∣ primeProduct p B v := by
  unfold aLabel primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  cases h : ε i <;> simp only [bit, h, Bool.false_eq_true, ite_false, ite_true]
  · exact Nat.zero_le _
  · exact hv i hi

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeRadical_dvd_jLabel_b0 (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : cubeRadical p B ∣ jLabel p B v ε₁ ε₂ * b0Label p B v ε₁ ε₂ := by
  have hle (i : ι) (hi : i ∈ B) :
      1 ≤ bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i) := by
    cases h : retained (parity (v i)) (ε₁ i) (ε₂ i)
    · have hp := FirstPassCubeLabels.b0Exponent_pos_of_not_retained (v i) (ε₁ i) (ε₂ i) (hv i hi) h
      simp only [bit,  Bool.false_eq_true, ite_false, zero_add]
      omega
    · simp only [bit,  ite_true]
      omega
  have hd := Finset.prod_dvd_prod_of_dvd (s := B) (fun i => p i ^ 1)
    (fun i => p i ^ (bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i)))
    (fun i hi => pow_dvd_pow (p i) (hle i hi))
  simpa only [cubeRadical, jLabel, b0Label, primeProduct, pow_one, pow_add,
    Finset.prod_mul_distrib] using hd

def actualSecondTuple (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (k : O) : SecondPassFiber.OldTuple where
  core := ![Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂},
    ∏ i ∈ C, Ideal.span {p i}, ∏ i ∈ E, Ideal.span {p i},
    Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)},
    Ideal.span {primeProduct p B v₁}, Ideal.span {aLabel p B ε₁},
    Ideal.span {aLabel p B ε₂}, ∏ i ∈ D, Ideal.span {p i}]
  v := ∏ i ∈ V, Ideal.span {p i}
  j2 := Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  row := k

def actualSecondLabel (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Ideal O :=
  Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂} *
    (∏ i ∈ C, Ideal.span {p i}) * (∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i})

def actualSecondRow (D E : Finset ι) (k : O) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) D *
    primeSubsetGenerator (fun i => Ideal.span {p i}) E * k

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_valid
    (B C D E V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C ∪ B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (k : O) :
    SecondPassFiber.Valid (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k)
      (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
      (actualSecondRow p D E k) := by
  have hJ := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2 p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
  have hb := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.cube_product_decomposition p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [primeProduct_add] at hb
  have hA₁ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₁ hv)
  have hA₂ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₂ hv)
  rw [primeProduct_add, ← Ideal.span_singleton_mul_span_singleton] at hA₁ hA₂
  have hrad := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [← Ideal.span_singleton_mul_span_singleton] at hrad
  have hD' : (∏ i ∈ D, Ideal.span {p i}) ∣
      (∏ i ∈ C, Ideal.span {p i}) * Ideal.span {cubeRadical p B} := by
    have hh := Finset.prod_dvd_prod_of_subset D (C ∪ B) (fun i => (Ideal.span {p i} : Ideal O)) hD
    rw [Finset.prod_union hCB] at hh
    simpa only [cubeRadical, FiniteGaussPhase.span_finset_prod] using hh
  have hD'' := hD'.trans (mul_dvd_mul_left (∏ i ∈ C, (Ideal.span {p i} : Ideal O)) hrad)
  constructor
  · rfl
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} =
          Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
    simpa only [← Ideal.span_singleton_mul_span_singleton] using hJ.symm
  · change Ideal.span {primeProduct p B v₁} * Ideal.span {primeProduct p B v₂} =
        Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)}
    simpa only [pow_two, ← Ideal.span_singleton_mul_span_singleton] using hb
  · exact hA₁
  · exact hA₂
  · apply hD''.trans
    refine ⟨(∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i}), ?_⟩
    simp only [actualSecondLabel]
    ring
  · rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_newLabel
    (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (k : O) :
    SecondPassFiber.newLabel (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k) =
      actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂ := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondTuple_newRow
    (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (k : O) :
    SecondPassFiber.newRow (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k) =
      actualSecondRow p D E k := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem actualSecondLabel_span
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Ideal.span {(primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂ *
      primeSubsetGenerator (fun i => Ideal.span {p i}) E * (∏ i ∈ V, p i))} =
      actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂ := by
  simp only [actualSecondLabel, ← Ideal.span_singleton_mul_span_singleton,
    primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
    FiniteGaussPhase.span_finset_prod]
  ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel b0Label primeProductNorm)

@[ext] structure SecondSupportData (ι : Type*) where
  common : Finset ι
  firstDivisor : Finset ι
  secondDivisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

instance {ι : Type*} : Inhabited (SecondSupportData ι) := ⟨⟨∅, ∅, ∅, ∅, 0⟩⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondSupportTuple (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : SecondPassFiber.OldTuple :=
  actualSecondTuple p B x.common x.firstDivisor x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂ x.frequency

def secondSupportLabel (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
    jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂ *
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor * (∏ i ∈ x.overlap, p i)

def secondSupportNewLabel (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondSupportData ι) : Ideal O :=
  actualSecondLabel p B x.common x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂

def secondSupportRow (x : SecondSupportData ι) : O :=
  actualSecondRow p x.firstDivisor x.secondDivisor x.frequency

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondSupportTuple_newLabel
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    SecondPassFiber.newLabel (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x) =
      secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
@[simp] theorem secondSupportTuple_newRow
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    SecondPassFiber.newRow (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x) = secondSupportRow p x := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportLabel_span
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (x : SecondSupportData ι) :
    Ideal.span {secondSupportLabel p B v₁ v₂ ε₁ ε₂ x} = secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x :=
  actualSecondLabel_span p B x.common x.secondDivisor x.overlap v₁ v₂ ε₁ ε₂

theorem secondSupportTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Function.Injective (secondSupportTuple p B v₁ v₂ ε₁ ε₂) := by
  intro x y h
  have hC := congrArg (fun z : SecondPassFiber.OldTuple => z.core 1) h
  have hD := congrArg (fun z : SecondPassFiber.OldTuple => z.core 7) h
  have hE := congrArg (fun z : SecondPassFiber.OldTuple => z.core 2) h
  have hV := congrArg SecondPassFiber.OldTuple.v h
  have hk := congrArg SecondPassFiber.OldTuple.row h
  apply SecondSupportData.ext
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hC
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hD
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hE
  · exact FirstCauchyArithmetic.family_product_injective _ hinj hV
  · exact hk

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportTuple_valid
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (x : SecondSupportData ι)
    (hCB : Disjoint x.common B) (hD : x.firstDivisor ⊆ x.common ∪ B) :
    SecondPassFiber.Valid (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x)
      (SecondPassFiber.newLabel (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x))
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
      (SecondPassFiber.newRow (secondSupportTuple p B v₁ v₂ ε₁ ε₂ x)) :=
  actualSecondTuple_valid p B x.common x.firstDivisor x.secondDivisor x.overlap hCB hD
    v₁ v₂ ε₁ ε₂ hv x.frequency

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sector_b0_ne_bot (hp : ∀ i, p i ≠ 0)
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} : Ideal O) ≠ ⊥ := by
  apply Ideal.span_singleton_eq_bot.not.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp i))

def secondSectorZ (X X₀ : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap * X₀ / X)

def secondSectorUd (D : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)‖ ^ 2 / D)

def secondSectorUe (E : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)‖ ^ 2 / E)

def secondSectorUv (V₀ : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (primeProductNorm p x.overlap / V₀)

def secondSectorKap (K : ℝ) (x : SecondSupportData ι) : ℝ :=
  Real.log (‖ConcreteTraceCRT.eisEmbedding (secondSupportRow p x)‖ ^ 2 / K)

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open SecondPassIntegration (tupleSourceSum tupleSource_uniform_transfer childGeometricMean)
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondSectorSource
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ)
    (D₀ E₀ V₀ X X₀ K Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSupportLabel p B v₁ v₂ ε₁ ε₂ x) (secondSupportRow p x) (-secondSupportRow p x)
    A₁ A₂ W windows (secondSectorZ p X X₀ x) (secondSectorUd p D₀ x)
    (secondSectorUe p E₀ x) (secondSectorUv p V₀ x) (secondSectorKap p K x)
    X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2))

theorem actual_second_sector_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (ε : ℝ) (hε : 0 < ε) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hwindows : ∀ j x, windows j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧
      ∀ D₀ E₀ V₀ X X₀ K Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1 + Y*K/(D₀*E₀^2*V₀^2*X₀^2))^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
          Cₛ * FirstPassCubeLabels.firstLogDensity J t₁ *
            FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow windows
          (secondSectorZ p X X₀ x) (secondSectorUd p D₀ x) (secondSectorUe p E₀ x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
          A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y‖ ≤
        (Bnd * Cₐ * (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, htrans⟩ :=
    tupleSource_uniform_transfer p hp hcop hg ε hε A₁ A₂ W windows M hM hwindows A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro D₀ E₀ V₀ X X₀ K Y hD₀ hE₀ hV₀ hX hX₀ hK hY
  have hR : 0 < Y*K/(D₀*E₀^2*V₀^2*X₀^2) := by positivity
  obtain ⟨b, hb, hbound⟩ := htrans _ hR
  refine ⟨b, hb, ?_⟩
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m hv hCB hD hBnd hL hmap hT0 hnorm hw
  let encode := secondSupportTuple p B v₁ v₂ ε₁ ε₂
  have hi : Function.Injective encode := secondSupportTuple_injective p hinj B v₁ v₂ ε₁ ε₂
  let decode := Function.invFun encode
  have hdec (x : SecondSupportData ι) : decode (encode x) = x := Function.leftInverse_invFun hi x
  let s' := s.image encode
  let w' := fun x => w (decode x)
  let label' := fun x => secondSupportLabel p B v₁ v₂ ε₁ ε₂ (decode x)
  let z' := fun x => secondSectorZ p X X₀ (decode x)
  let ud' := fun x => secondSectorUd p D₀ (decode x)
  let ue' := fun x => secondSectorUe p E₀ (decode x)
  let uv' := fun x => secondSectorUv p V₀ (decode x)
  let kap' := fun x => secondSectorKap p K (decode x)
  have hsvalid : ∀ x ∈ s', SecondPassFiber.Valid x (SecondPassFiber.newLabel x)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}) (SecondPassFiber.newRow x) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact secondSupportTuple_valid p B v₁ v₂ ε₁ ε₂ hv a (hCB a ha) (hD a ha)
  have hsmap : ∀ x ∈ s', (SecondPassFiber.newLabel x, SecondPassFiber.newRow x) ∈ T := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hmap a ha
  have hsw : ∀ x ∈ s', ‖w' x‖ * ‖outerWindow windows (z' x) (ud' x) (ue' x) (uv' x) (kap' x)‖ ≤ Bnd := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [w', z', ud', ue', uv', kap']
    rw [hdec]
    exact hw a ha
  have hslabel : ∀ x ∈ s', Ideal.span {label' x} = SecondPassFiber.newLabel x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [label']
    rw [hdec]
    exact secondSupportLabel_span p B v₁ v₂ ε₁ ε₂ a
  have hout := hbound s' T (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
    w' Bnd lengthScale label' F Ψ₁ Ψ₂ m z' ud' ue' uv' kap' X₀ X₀
    (sector_b0_ne_bot p hp B v₁ v₂ ε₁ ε₂) hBnd hL hsvalid hsmap hT0 hnorm hsw hslabel
  have hsource : tupleSourceSum p hp hcop hg s' w' label' F Ψ₁ Ψ₂ m
      A₁ A₂ W windows z' ud' ue' uv' kap' X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2)) =
      actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
        A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y := by
    unfold tupleSourceSum actualSecondSectorSource
    rw [Finset.sum_image (fun a ha c hc h => hi h)]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [w', label', z', ud', ue', uv', kap']
    rw [hdec]
    rfl
  rw [hsource] at hout
  exact hout

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FixedProfiles -/

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
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem secondGaussTerm_test_factors (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T =
      star (H₁ S) * H₂ T *
        secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
  simp only [secondGaussTerm, secondInputCoefficient, star_mul, mul_one]
  ring

theorem secondFrequencyKernel_log_tests (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) (W : 𝓢(ℝ, ℂ)) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (fun S => V₁ (columnLog p X₁ S)) (fun T => V₂ (columnLog p X₂ T)) W Y =
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y := by
  unfold secondFrequencyKernel actualSecondKernel
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd]
    rw [secondGaussTerm_test_factors]
    ring
  · simp [hd]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration

section
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem radialPairKernel_dyadic_normalization
    (V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (d e k : O) (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX : 0 < X) (hX₀ : 0 < X₀) (hK : 0 < K)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    radialPairKernel p e k W g₁ g₂ X X Y (V∪N) (V∪M) =
      (X : ℂ)⁻¹ *
      (conjugateProfile (halfNormalizationCLM U g₁)
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) *
      halfNormalizationCLM U g₂
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) *
      EisensteinSchwartzPoisson.paperRadialFourier W
        ((Y * K / (D * E ^ 2 * V₀ ^ 2 * X₀ ^ 2)) * Real.exp
          (Real.log (elementNorm (d*e*k) / K) - Real.log (elementNorm d / D) -
            2*Real.log (elementNorm e / E) - 2*Real.log (primeProductNorm p V / V₀) -
            columnLog p X₀ N - columnLog p X₀ M))) := by
  unfold radialPairKernel
  rw [normalizedColumn_pair_union p hp V N M hVN hVM X X₀ hX hX₀ U hUc hUs g₁ g₂ hU₁ hU₂,
    second_radial_dyadic_argument p hp V N M hVN hVM d e k hd he hk D E V₀ X₀ K Y hD hE hV₀ hX₀ hK]
  ring

variable [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildKernelPair_eq_postCommon
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (hd : d ≠ 0) (he : e ≠ 0) (hk : k ≠ 0)
    (D E V₀ X X₀ K Y : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hV₀ : 0 < V₀) (hX : 0 < X) (hX₀ : 0 < X₀) (hK : 0 < K)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) (windows : Fin 7 → ℝ → ℂ) :
    let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
    let A₂ := halfNormalizationCLM U g₂
    let z := Real.log (primeProductNorm p V * X₀ / X)
    let ud := Real.log (elementNorm d / D)
    let ue := Real.log (elementNorm e / E)
    let uv := Real.log (primeProductNorm p V / V₀)
    let kap := Real.log (elementNorm (d*e*k) / K)
    outerWindow windows z ud ue uv kap = 1 →
    (∀ a : ℝ, A₁ (z+a) ≠ 0 → windows 5 a = 1) →
    (∀ a : ℝ, A₂ (z+a) ≠ 0 → windows 6 a = 1) →
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
      (radialPairKernel p e k W g₁ g₂ X X Y) =
      (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
        (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
        z ud ue uv kap X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  dsimp only
  intro houter hcut₁ hcut₂
  rw [secondChildKernelPair_fixed_pool]
  simp only [postCommonSmoothPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hVN : Disjoint V N
  · by_cases hVM : Disjoint V M
    · rw [radialPairKernel_dyadic_normalization p hp V N M hVN hVM d e k hd he hk
        D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂, houter]
      by_cases h₁ : conjugateProfile (halfNormalizationCLM U g₁)
          (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) = 0
      · rw [h₁]; ring
      · by_cases h₂ : halfNormalizationCLM U g₂
            (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ M) = 0
        · rw [h₂]; ring
        · rw [hcut₁ _ h₁, hcut₂ _ h₂]; ring
    · rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₂ (m*r) c e
        (d*e*(-k)) (fun _ => 1) V M hVM]
      ring
  · rw [secondChildColumn_zero_of_overlap p hp hcop hg Ψ₁ (m*r) c e
      (d*e*k) (fun _ => 1) V N hVN, star_zero]
    ring

end

section
open JointLogSeparation

theorem halfNormalization_support_bound (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (A : ℝ)
    (hg : ∀ s, g s ≠ 0 → |s| ≤ A) :
    ∀ s, halfNormalizationCLM U g s ≠ 0 → |s| ≤ A := by
  intro s hs
  apply hg s
  intro hzero
  apply hs
  rw [halfNormalizationCLM_apply U hUc hUs, hzero, mul_zero]

lemma translated_support_bound (g : ℝ → ℂ) (A B z x : ℝ)
    (hg : ∀ s, g s ≠ 0 → |s| ≤ A) (hz : |z| ≤ B) (hx : g (z+x) ≠ 0) :
    |x| ≤ A+B := by
  have ht := hg (z+x) hx
  have ha : |x| ≤ |z+x| + |z| := by
    calc
      |x| = |(z+x)-z| := by congr 1; ring
      _ ≤ |z+x| + |z| := abs_sub _ _
  linarith

theorem exists_fixed_sector_windows (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ windows : Fin 7 → ℝ → ℂ,
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      (∀ z ud ue uv kap : ℝ,
        |z| ≤ B → |ud| ≤ B → |ue| ≤ B → |uv| ≤ B → |kap| ≤ B →
        outerWindow windows z ud ue uv kap = 1) ∧
      (∀ (g : ℝ → ℂ) (z : ℝ), (∀ s, g s ≠ 0 → |s| ≤ A) → |z| ≤ B →
        ∀ j x, g (z+x) ≠ 0 → windows j x = 1) := by
  obtain ⟨w, hwc, hws, hweq, hwsupp, hwzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff (A+B) (add_nonneg hA hB)
  refine ⟨fun _ => w, fun _ => hwc, fun _ => hws, ?_, ?_, ?_⟩
  · intro j s hs
    have hh := hwsupp (subset_closure hs)
    exact abs_le.mpr hh
  · intro z ud ue uv kap hz hd he hv hk
    have heq (s : ℝ) (hs : |s| ≤ B) : w s = 1 := hweq s (by linarith)
    simp only [outerWindow, heq z hz, heq ud hd, heq ue he, heq uv hv, heq kap hk,
      one_mul]
  · intro g z hg hz j x hx
    exact hweq x (translated_support_bound g A B z x hg hz hx)

end

open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

theorem exists_fixed_normalized_child_tests {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W g₁ g₂ X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  apply secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂ windows
  · exact hwo _ _ _ _ _ hz hud hue huv hkap
  · exact fun a ha => hwt A₁ _ hA₁ hz 5 a ha
  · exact fun a ha => hwt A₂ _ hA₂ hz 6 a ha

end SecondPassIntegration

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_normalized_child_tests elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondRawSector
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (X Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x *
    secondChildKernelPair p hp hcop hg F x.overlap Ψ₁ Ψ₂ m r
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
        jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
      x.frequency (-x.frequency)
      (radialPairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor)
        x.frequency W g₁ g₂ X X Y)

theorem actualSecondRawSector_fixed_profiles
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j t, windows j t ≠ 0 → |t| ≤ A+H+1) ∧
      ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O),
        (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p X X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        actualSecondRawSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r g₁ g₂ W X Y =
          (X : ℂ)⁻¹ * actualSecondSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ (m*r)
            A₁ A₂ W windows D E V₀ X X₀ K Y := by
  obtain ⟨A₁, A₂, windows, hwc, hws, hwb, hid⟩ :=
    exists_fixed_normalized_child_tests p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r hk hz hud hue huv hkap
  simp only [actualSecondRawSector, actualSecondSectorSource, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have heq := hid D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F x.overlap Ψ₁ Ψ₂ m r
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.common *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.secondDivisor) x.frequency
    (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) (hk x hx)
    (hz x hx) (hud x hx) (hue x hx) (huv x hx) (hkap x hx)
  rw [heq]
  simp only [secondSupportLabel, secondSupportRow, actualSecondRow,
    secondSectorZ, secondSectorUd, secondSectorUe, secondSectorUv, secondSectorKap,
    elementNorm, mul_neg]
  ring

end

open ActualEisensteinCubic
open FiniteGaussPhase (canonicalProductGauss_cross_factors)
open FirstCauchyArithmetic (activeGaussRowFactor supportMobius)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_zero_of_ne (S T : Finset ι) (hne : S ≠ T) (e : O) :
    activeGaussRowFactor p hp hinj hg S T e 0 = 0 := by
  have hs : (activeSupport S T).Nonempty := by
    by_contra hn
    apply hne
    have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
    exact Finset.Subset.antisymm he.1 he.2
  let : Nonempty (activeSupport S T) := hs.to_subtype
  unfold activeGaussRowFactor
  simp only [finiteSexticRow_zero, star_zero, mul_zero]

theorem activeGaussRowFactor_empty (e k : O) :
    activeGaussRowFactor p hp hinj hg ∅ ∅ e k = 1 := by
  have hempty : activeSupport (∅ : Finset ι) ∅ = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport (∅ : Finset ι) ∅) := ⟨fun x => by simpa [hempty] using x.property⟩
  simp only [activeGaussRowFactor, finiteSexticRow, star_one, mul_one,
    canonicalProductGauss_cross_factors, Fintype.prod_empty]

theorem secondGaussTerm_empty (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ ∅ ∅ =
      star (H₁ ∅) * H₂ ∅ := by
  have hm : supportMobius (fun i => Ideal.span {p i}) ∅ = 1 := by
    change (UniqueFactorizationMonoid.moebius (1 : Ideal O) : ℂ) = 1
    exact_mod_cast UniqueFactorizationMonoid.moebius_one
  simp only [secondGaussTerm, hm, one_mul, secondInputCoefficient, Finset.prod_empty,
    map_one, activeGaussRowFactor_empty, mul_one]
  simp [rowCoprimeMask, finiteSquarefreeRow]

theorem secondFrequencyKernel_zero (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ W Y =
      (Y : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier W 0 * star (H₁ ∅) * H₂ ∅ := by
  have hz (S T : Finset ι) (hne : S ≠ T) :
      secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ S T = 0 := by
    unfold secondGaussTerm
    rw [activeGaussRowFactor_zero_of_ne p hp hg hinj T S (Ne.symm hne) e, mul_zero]
  unfold secondFrequencyKernel
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp [secondGaussTerm_empty, mul_assoc]
    · intro T hT hne
      rw [hz ∅ T (Ne.symm hne)]
      simp
    · simp
  · intro S hS hne
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hd : Disjoint S T
    · have hneq : S ≠ T := by
        intro heq
        subst T
        exact hne ((show S = ∅ by simpa using Finset.disjoint_iff_inter_eq_empty.mp hd))
      rw [hz S T hneq]
      simp
    · simp [hd]
  · simp

end SecondPassArithmetic

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma symbol_cube_numerator (a d : O) (hd : denominatorCondition (a^3) d) :
    symbol (a^3) d=1 := by
  have hprimary : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd.2
  rw [symbol_pow_numerator a d hprimary 3]
  apply symbol_cube_of_isCoprime a d hprimary
  exact hd.1.of_isCoprime_of_dvd_left ⟨a^2,by ring⟩

theorem arithmeticResidueSum_cube (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3)=(Nat.card (AdmissibleResidue (a^3)):ℂ) := by
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Fintype (AdmissibleResidue (a^3)) := Fintype.ofFinite _
  rw [arithmeticResidueSum,tsum_fintype]
  have hterm (r : AdmissibleResidue (a^3)) :
      eisEmbedding (symbol (a^3) (denominatorRep (a^3) r.1))*
        ShortDraftTrace.breveE (cuspFrequency 0*eisEmbedding (denominatorRep (a^3) r.1)/
          eisEmbedding (a^3))=1 := by
    rw [symbol_cube_numerator a _ r.2,map_one]
    simp [cuspFrequency]
  simp only [hterm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card]

lemma admissibleResidue_nonempty (c : O) (hc : c ≠ 0) : Nonempty (AdmissibleResidue c) := by
  let d : AdmissibleDenominator c := ⟨1,isCoprime_one_right,by simp⟩
  exact ⟨((residueDenominatorEquiv c hc).symm d).1⟩

theorem arithmeticResidueSum_cube_ne_zero (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3) ≠ 0 := by
  rw [arithmeticResidueSum_cube a ha]
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Nonempty (AdmissibleResidue (a^3)) := admissibleResidue_nonempty _ (pow_ne_zero 3 ha)
  exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := AdmissibleResidue (a^3))).ne'

lemma denominatorCondition_congr (c d e : O) (h : 3*c ∣ d-e) :
    denominatorCondition c d ↔ denominatorCondition c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact denominatorCondition_shift c e n

lemma denominatorCondition_mul (c d t : O) (hd : denominatorCondition c d)
    (ht : denominatorCondition c t) : denominatorCondition c (d*t) := by
  refine ⟨hd.1.mul_right ht.1,?_⟩
  convert dvd_add (hd.2.mul_right t) ht.2 using 1 ; ring

lemma row_symbol_congr_modulus (c d e : O) (hlevel : (3:O) ∣ c)
    (he : (3:O) ∣ e-1) (h : 3*c ∣ d-e) : symbol c d=symbol c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact row_symbol_shift c e n hlevel he

lemma denominatorRep_product_congr (c t : O) (r : DenominatorResidue c) :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r)-t*denominatorRep c r := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [denominatorRep_spec,map_mul,denominatorRep_spec]

def residueMultiplication (c t : O) (ht : denominatorCondition c t)
    (r : AdmissibleResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1,
    (denominatorCondition_congr c _ _ (denominatorRep_product_congr c t r.1)).2
      (denominatorCondition_mul c t _ ht r.2)⟩

lemma denominatorCondition_coprime_modulus (c t : O) (ht : denominatorCondition c t) :
    IsCoprime (3*c) t := by
  obtain ⟨n,hn⟩ := ht.2
  have h3 : IsCoprime (3:O) t := ⟨-n,1,by linear_combination hn⟩
  exact h3.mul_left ht.1

lemma residueMultiplication_injective (c t : O) (ht : denominatorCondition c t) :
    Function.Injective (residueMultiplication c t ht) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {3*c}) t) := by
    have hh := (denominatorCondition_coprime_modulus c t ht).map
      (Ideal.Quotient.mk (Ideal.span {3*c}))
    have hz : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [hz,isCoprime_zero_left] using hh
  intro r q heq
  apply Subtype.ext
  exact hunit.mul_left_cancel (congrArg Subtype.val heq)

def residueMultiplicationEquiv (c : O) (hc : c ≠ 0) (t : O)
    (ht : denominatorCondition c t) : AdmissibleResidue c ≃ AdmissibleResidue c := by
  letI : Finite (AdmissibleResidue c) := finite_admissibleResidue c hc
  exact Equiv.ofBijective (residueMultiplication c t ht)
    ⟨residueMultiplication_injective c t ht,
      Finite.surjective_of_injective (residueMultiplication_injective c t ht)⟩

lemma residueMultiplication_phase (c : O) (hlevel : (3:O) ∣ c) (t : O)
    (ht : denominatorCondition c t) (r : AdmissibleResidue c) :
    symbol c (denominatorRep c (residueMultiplication c t ht r).1)=
      symbol c t*symbol c (denominatorRep c r.1) := by
  change symbol c (denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1))=
    symbol c t*symbol c (denominatorRep c r.1)
  rw [row_symbol_congr_modulus c _ (t*denominatorRep c r.1) hlevel
    (denominatorCondition_mul c t _ ht r.2).2 (denominatorRep_product_congr c t r.1)]
  exact symbol_mul_denominator c t (denominatorRep c r.1)

lemma arithmeticResidueSum_zero (c : O) :
    arithmeticResidueSum 0 c=∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c r.1)) := by
  simp only [arithmeticResidueSum,cuspFrequency,map_zero,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]

theorem arithmeticResidueSum_constant_eigen (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (t : O) (ht : denominatorCondition c t) :
    eisEmbedding (symbol c t)*arithmeticResidueSum 0 c=arithmeticResidueSum 0 c := by
  rw [arithmeticResidueSum_zero]
  have heq := (residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c => eisEmbedding (symbol c (denominatorRep c r.1)))
  calc
    _ = ∑' r : AdmissibleResidue c,eisEmbedding (symbol c t*symbol c (denominatorRep c r.1)) := by
      simp only [map_mul,tsum_mul_left]
    _ = _ := by
      convert heq using 1
      apply tsum_congr
      intro r
      exact congrArg eisEmbedding (residueMultiplication_phase c hlevel t ht r).symm

theorem arithmeticResidueSum_ne_zero_forces_trivial (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∀ t : O, denominatorCondition c t → symbol c t=1 := by
  intro t ht
  apply eisEmbedding_injective
  rw [map_one]
  apply (mul_right_cancel₀ hA)
  rw [arithmeticResidueSum_constant_eigen c hc hlevel t ht,one_mul]

end CubicEisenstein

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma coprime_of_dvd_sub_one (a b : O) (h : a ∣ b-1) : IsCoprime a b := by
  obtain ⟨r,hr⟩ := h
  exact ⟨-r,1,by linear_combination hr⟩

lemma primary_coprime_three (p : O) (hp : lambda^2 ∣ p-1) : IsCoprime p (3:O) :=
  (coprime_of_dvd_sub_one 3 p (three_dvd_primary_sub_one p hp)).symm

lemma exists_one_mod_and_prescribed (p m x : O) (hpm : IsCoprime p m) :
    ∃ t : O, m ∣ t-1 ∧ p ∣ t-x := by
  obtain ⟨r,u,hu⟩ := hpm
  refine ⟨1+m*u*(x-1),⟨u*(x-1),by ring⟩,⟨-r*(x-1),?_⟩⟩
  linear_combination (x-1)*hu

theorem constant_coefficient_primary_prime_exponent (c p b : O) (n : ℕ)
    (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hp : Prime p) (hprimary : lambda^2 ∣ p-1)
    (hpb : ¬p ∣ b) (hfactor : c=p^n*b) (hA : arithmeticResidueSum 0 c ≠ 0) :
    3 ∣ n := by
  by_contra hn
  let P : Ideal O := Ideal.span {p}
  let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ P := primary_maximal_divisor_good p hprimary P (Ideal.subset_span (by simp []))
  have hchar : (cubicChar P hg)^n ≠ 1 := by
    intro heq
    have hd := orderOf_dvd_of_pow_eq_one heq
    rw [cubicChar_order P hg] at hd
    exact hn hd
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hchar
  rw [MulChar.pow_apply_coe] at hu
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : O ⧸ P)
  have hp9 : IsCoprime p (9:O) := by
    simpa only [show (3:O)^2=9 by norm_num] using (primary_coprime_three p hprimary).pow_right (n := 2)
  have hpm : IsCoprime p (9*b) := hp9.mul_right (hp.coprime_iff_not_dvd.mpr hpb)
  obtain ⟨t,htm,htp⟩ := exists_one_mod_and_prescribed p (9*b) x hpm
  have h9 : (9:O) ∣ t-1 := (dvd_mul_right 9 b).trans htm
  have hb : b ∣ t-1 := (dvd_mul_left b 9).trans htm
  have h3 : (3:O) ∣ t-1 := (show (3:O) ∣ 9 from ⟨3,by norm_num⟩).trans h9
  have htprimary : lambda^2 ∣ t-1 := lambda_sq_dvd_three.trans h3
  have htu : Ideal.Quotient.mk P t=(u : O ⧸ P) := by
    rw [← hx]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr htp)
  have hpt : IsCoprime p t := hp.coprime_iff_not_dvd.mpr (by
    intro hdiv
    have hz : Ideal.Quotient.mk P t=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    rw [htu] at hz
    exact Units.ne_zero u hz)
  have hbt : IsCoprime b t := coprime_of_dvd_sub_one b t hb
  have hct : IsCoprime c t := by
    rw [hfactor]
    exact hpt.pow_left.mul_left hbt
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t ⟨hct,h3⟩
  have hbsym : symbol b t=1 := by
    have hh := symbol_denominator_congr b t 1 htprimary (by simp) h9 hb
    simpa only [symbol_one] using hh
  have hpsym : symbol p t=cubicChar P hg (u : O ⧸ P) := by
    rw [symbol_reciprocity p t hp.ne_zero (primary_ne_zero t htprimary) hprimary htprimary]
    change idealSymbol P t=_
    rw [idealSymbol_prime P hg,htu]
  rw [hfactor,symbol_mul_numerator _ _ t htprimary,symbol_pow_numerator p t htprimary,
    hbsym,mul_one,hpsym] at htriv
  exact hu htriv

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport -/

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
open MeasureTheory Set Filter
open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid

lemma multiset_cube_remainder {α : Type*} [DecidableEq α] (s : Multiset α) (p : α)
    (hdiv : ∀ q, q ≠ p → 3 ∣ s.count q) :
    ∃ t : Multiset α, s=(s.count p % 3) • {p} + 3 • t := by
  let t := Finsupp.toMultiset (s.toFinsupp.mapRange (fun n : ℕ => n/3) (by decide))
  refine ⟨t,?_⟩
  apply Multiset.ext.mpr
  intro q
  simp only [Multiset.count_add,Multiset.count_nsmul,Multiset.count_singleton,
    t,Finsupp.count_toMultiset,Finsupp.mapRange_apply,Multiset.toFinsupp_apply]
  by_cases hq : q=p
  · subst q
    simp only [ite_true,mul_one]
    omega
  · simp only [hq,ite_false,mul_zero,zero_add]
    exact (Nat.mul_div_cancel' (hdiv q hq)).symm

lemma residue_lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

lemma constant_coefficient_unramified_count [NormalizationMonoid O]
    (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0)
    (q : O) (hq : q ≠ normalize lambda) : 3 ∣ (normalizedFactors c).count q := by
  by_cases hmem : q ∈ normalizedFactors c
  · have hprime := prime_of_normalized_factor q hmem
    let P : Ideal O := Ideal.span {q}
    let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
    have hg : lambda ∉ P := by
      intro hl
      have ha : Associated q lambda :=
        hprime.associated_of_dvd residue_lambda_prime (Ideal.mem_span_singleton.mp hl)
      apply hq
      exact (normalize_normalized_factor q hmem).symm.trans
        (normalize_eq_normalize_iff_associated.mpr ha)
    obtain ⟨p,hP,hprimary,-⟩ := cubicJacobi_exists_primary_generator P hg
    have hqp : Associated q p := Ideal.span_singleton_eq_span_singleton.mp hP
    have hp : Prime p := hqp.prime_iff.mp hprime
    obtain ⟨b,hfactor,hpb⟩ := (FiniteMultiplicity.of_prime_left hp hc).exists_eq_pow_mul_and_not_dvd
    have hd := constant_coefficient_primary_prime_exponent c p b (multiplicity p c)
      hc hlevel hp hprimary hpb hfactor hA
    have hcount := multiplicity_eq_count_normalizedFactors hprime.irreducible hc
    rw [normalize_normalized_factor q hmem] at hcount
    rw [← hcount,← multiplicity_eq_of_associated_left hqp]
    exact hd
  · rw [Multiset.count_eq_zero.mpr hmem]
    exact dvd_zero _

theorem constant_coefficient_cube_reduction (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∃ (u : Oˣ) (r : ℕ) (a : O), r < 3 ∧ c=(u:O)*lambda^r*a^3 := by
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  let s := normalizedFactors c
  obtain ⟨t,ht⟩ := multiset_cube_remainder s (normalize lambda)
    (constant_coefficient_unramified_count c hc hlevel hA)
  let r := s.count (normalize lambda) % 3
  have hprod : s.prod=(normalize lambda)^r*t.prod^3 := by
    rw [ht,Multiset.prod_add,Multiset.prod_nsmul,Multiset.prod_singleton,Multiset.prod_nsmul]
  have hassoc : Associated (lambda^r*t.prod^3) c := by
    have hnorm : Associated ((normalize lambda)^r*t.prod^3) (lambda^r*t.prod^3) :=
      (normalize_associated lambda).pow_pow.mul_right _
    apply hnorm.symm.trans
    rw [← hprod]
    exact prod_normalizedFactors hc
  obtain ⟨u,hu⟩ := hassoc
  refine ⟨u,r,t.prod,Nat.mod_lt _ (by decide),?_⟩
  rw [← hu]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified

lemma constant_coefficient_ramified_equation (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (hA : arithmeticResidueSum 0 c ≠ 0) (u : Oˣ) (r : ℕ) (a : O) (ha : a ≠ 0)
    (hfactor : c=(u:O)*lambda^r*a^3) (A B : ℤ) :
    symbol (u:O) (primaryCoord A B)*(cubicExp A)^r=1 := by
  let t0 := primaryCoord A B
  have ht0 : lambda^2 ∣ t0-1 := primaryCoord_primary A B
  obtain ⟨w,hw⟩ := exists_coprime_three_shift t0 3 a ht0 (primary_coprime_three t0 ht0) ha
  let t := t0+3*w*3
  have ht : lambda^2 ∣ t-1 := primary_add_multiple_three t0 3 w ht0
  have h9 : (9:O) ∣ t-t0 := ⟨w,by dsimp [t]; ring⟩
  have hat : IsCoprime a t := hw.symm
  have hlt : IsCoprime lambda t :=
    coprime_of_dvd_sub_one lambda t ((show lambda ∣ lambda^2 from ⟨lambda,by ring⟩).trans ht)
  have hct : IsCoprime c t := by
    rw [hfactor,show (u:O)*lambda^r*a^3=(u:O)*(lambda^r*a^3) by ring]
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    exact hlt.pow_left.mul_left hat.pow_left
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t
    ⟨hct,three_dvd_primary_sub_one t ht⟩
  have hacube : symbol (a^3) t=1 := by
    rw [symbol_pow_numerator a t ht 3]
    exact symbol_cube_of_isCoprime a t ht hat
  rw [hfactor,symbol_mul_numerator _ _ t ht,symbol_mul_numerator _ _ t ht,
    symbol_pow_numerator lambda t ht r,hacube,mul_one,
    symbol_unit_congr_mod_nine (u:O) t t0 u.isUnit ht ht0 h9,
    symbol_lambda_congr_mod_nine t t0 ht ht0 h9,
    symbol_lambda_eq_linearRay t0 ht0] at htriv
  simpa only [t0,linearRay_primaryCoord,one_mul,zero_mul,add_zero] using htriv

lemma unit_eq_sign_of_symbol_class (u : Oˣ)
    (hu : symbol (u:O) (primaryCoord 0 1)=1) : (u:O)=1 ∨ (u:O)=-1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega (primaryCoord 0 1)=omega^2 := by
    rw [symbol_omega_eq_linearRay _ (primaryCoord_primary 0 1),linearRay_primaryCoord]
    norm_num [cubicExp]
  have hω2 : symbol (omega^2) (primaryCoord 0 1)=omega^4 := by
    rw [symbol_pow_numerator omega _ (primaryCoord_primary 0 1) 2,hω,← pow_mul]
  have hn2 : omega^2 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 2).not.mpr (by decide)
  have hn4 : omega^4 ≠ 1 := (omega_primitive.pow_eq_one_iff_dvd 4).not.mpr (by decide)
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · exact Or.inl (by rw [h,Units.val_one])
  · exact Or.inr (by rw [h,Units.val_neg,Units.val_one])
  · exact False.elim (hn2 (by simpa only [h,hη,hω] using hu))
  · exact False.elim (hn2 (by simpa only [h,Units.val_neg,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_pow_eq_pow_val,hη,hω2] using hu))
  · exact False.elim (hn4 (by simpa only [h,Units.val_neg,Units.val_pow_eq_pow_val,hη,
      (symbol_neg_numerator _ _ (primaryCoord_primary 0 1)),hω2] using hu))

theorem arithmeticResidueSum_ne_zero_implies_cube (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) : ∃ a : O,c=a^3 := by
  obtain ⟨u,r,a,hr,hfactor⟩ := constant_coefficient_cube_reduction c hc hlevel hA
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,zero_pow (by decide : (3:ℕ) ≠ 0),mul_zero] at hfactor
    exact hc hfactor
  have h01 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 0 1
  have husign := unit_eq_sign_of_symbol_class u (by
    simpa only [cubicExp_zero,one_pow,mul_one] using h01)
  have h10 := constant_coefficient_ramified_equation c hc hlevel hA u r a ha hfactor 1 0
  have hωr : omega^r=1 := by
    rcases husign with hu | hu
    · simpa only [hu,symbol_one_numerator _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
    · simpa only [hu,symbol_neg_one _ (primaryCoord_primary 1 0),one_mul,
        cubicExp,Int.reduceMod,Int.toNat_one,pow_one] using h10
  have hdiv : 3 ∣ r := (omega_primitive.pow_eq_one_iff_dvd r).mp hωr
  have hr0 : r=0 := by omega
  rw [hr0,pow_zero,mul_one] at hfactor
  rcases husign with hu | hu
  · refine ⟨a,?_⟩
    simpa only [hu,one_mul] using hfactor
  · refine ⟨-a,?_⟩
    rw [hfactor,hu]
    ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

theorem arithmeticResidueSum_ne_zero_iff_cube (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c ≠ 0 ↔ ∃ a : O,c=a^3 := by
  constructor
  · exact arithmeticResidueSum_ne_zero_implies_cube c hc hlevel
  · rintro ⟨a,rfl⟩
    have ha : a ≠ 0 := fun h => hc (by rw [h]; norm_num)
    exact arithmeticResidueSum_cube_ne_zero a ha

theorem arithmeticResidueSum_constant_formula (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    arithmeticResidueSum 0 c=
      if ∃ a : O,c=a^3 then (Nat.card (AdmissibleResidue c):ℂ) else 0 := by
  split_ifs with hcube
  · obtain ⟨a,rfl⟩ := hcube
    exact arithmeticResidueSum_cube a (fun h => hc (by rw [h]; norm_num))
  · exact not_ne_iff.mp (fun hA => hcube (arithmeticResidueSum_ne_zero_implies_cube c hc hlevel hA))

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

def idealZeroMask (D : Ideal O) (z : O) : ℂ :=
  if ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P then 0 else 1

theorem idealSupport_singleton_univ (D : Ideal O) :
    idealSupport {D} D = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro P
  apply (mem_idealSupport_iff {D} D P).mpr
  obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
  have hID : I = D := Finset.mem_singleton.mp hI
  simpa only [hID] using hP

theorem singleton_rowCoprimeMask_eq_idealZeroMask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : primePool {D} => P.val) Finset.univ z = idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (primePool {D})), z ∈ P.val) ↔
      ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
      have hID : I = D := Finset.mem_singleton.mp hI
      exact ⟨P.val, hID ▸ hP, hz⟩
    · rintro ⟨P, hP, hz⟩
      have hp : P ∈ primePool {D} := mem_primePool_iff.mpr ⟨D, Finset.mem_singleton_self D, hP⟩
      exact ⟨⟨P, hp⟩, Finset.mem_univ _, hz⟩
  simp only [rowCoprimeMask, idealZeroMask, he]

theorem canonical_quadraticRow_star (D : Ideal O) (hD : Admissible D) (z : O) :
    star (quadraticRow D z) = quadraticRow D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticInitialBound.quadraticRow_star _ _ _ _

theorem canonical_quadraticRow_squared (D : Ideal O) (hD : Admissible D) (z : O) :
    quadraticRow D z * quadraticRow D z = idealZeroMask D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  rw [← QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ z z, ← pow_two,
    QuadraticSquarefreeKernel.quadraticRow_square, idealSupport_singleton_univ]
  exact singleton_rowCoprimeMask_eq_idealZeroMask D z

def gcdMaskPrimes (D : Ideal O) : Finset (Ideal O) :=
  {Ideal.span {lambda}, Ideal.span {(2 : O)}} ∪
    (UniqueFactorizationMonoid.normalizedFactors D).toFinset

instance gcdMaskPrimes_maximal (D : Ideal O) (P : gcdMaskPrimes D) : P.val.IsMaximal := by
  rcases Finset.mem_union.mp P.property with hp | hp
  · rcases Finset.mem_insert.mp hp with hp | hp
    · rw [hp]
      exact lambdaIdeal_maximal
    · rw [Finset.mem_singleton.mp hp]
      exact twoIdeal_maximal
  · have h := UniqueFactorizationMonoid.prime_of_normalized_factor P.val (Multiset.mem_toFinset.mp hp)
    exact (Ideal.isPrime_of_prime h).isMaximal h.ne_zero

theorem gcdMaskPrimes_mask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : gcdMaskPrimes D => P.val) Finset.univ z =
      rowCoprimeMask badPrime Finset.univ z * idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (gcdMaskPrimes D)), z ∈ P.val) ↔
      (lambda ∣ z ∨ (2 : O) ∣ z) ∨
        ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      rcases Finset.mem_union.mp P.property with hp | hp
      · rcases Finset.mem_insert.mp hp with hp | hp
        · exact Or.inl (Or.inl (Ideal.mem_span_singleton.mp (hp ▸ hz)))
        · exact Or.inl (Or.inr (Ideal.mem_span_singleton.mp ((Finset.mem_singleton.mp hp) ▸ hz)))
      · exact Or.inr ⟨P.val, Multiset.mem_toFinset.mp hp, hz⟩
    · rintro ((hz | hz) | ⟨P, hP, hz⟩)
      · exact ⟨⟨Ideal.span {lambda}, Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩,
          Finset.mem_univ _, Ideal.mem_span_singleton.mpr hz⟩
      · exact ⟨⟨Ideal.span {(2 : O)}, Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩,
          Finset.mem_univ _, Ideal.mem_span_singleton.mpr hz⟩
      · exact ⟨⟨P, Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hP)⟩, Finset.mem_univ _, hz⟩
  change (if ∃ P ∈ (Finset.univ : Finset (gcdMaskPrimes D)), z ∈ P.val then (0 : ℂ) else 1) = _
  simp only [he]
  rw [badPrime_mask, supported_span_iff]
  unfold idealZeroMask
  by_cases hl : lambda ∣ z <;> by_cases ht : (2 : O) ∣ z <;>
    by_cases hd : ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P <;> simp [hl, ht, hd]

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance

theorem canonical_same_ray_pair_poisson
    {α : Type*} [DecidableEq α]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    (∑' z : O, rowCoprimeMask R S z * χ z * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let F : Finset (Ideal O) := {I, J}
  have hF : ∀ lengthScale ∈ F, Admissible lengthScale := by
    intro lengthScale hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hI
    · have hLJ := Finset.mem_singleton.mp hL
      simpa only [hLJ] using hJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  let p := poolPrimary F
  let A := idealSupport F I
  let B := idealSupport F J
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by change (Ideal.span {poolPrimary F i}).IsMaximal; rw [poolPrimary_span F hF i]; infer_instance
  have hd : Disjoint A B := idealSupport_disjoint_of_coprime F I J hcop
  have hpgI : primaryGenerator I = ∏ i ∈ A, p i := primaryGenerator_eq_poolProduct F hF I hIF
  have hpgJ : primaryGenerator J = ∏ i ∈ B, p i := primaryGenerator_eq_poolProduct F hF J hJF
  have hr : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i) := by
    rw [← hpgI, ← hpgJ]
    exact hray
  have hn : (∏ i ∈ A ∪ B, p i) = primaryGenerator I * primaryGenerator J := by
    rw [Finset.prod_union hd, ← hpgI, ← hpgJ]
  have hrowI (z : O) : QuadraticInitialBound.quadraticRow
      (fun i => Ideal.span {p i}) (poolPrimary_good F hF) A z = quadraticRow I z :=
    (quadraticRow_eq_primaryPool F hF I hIF z).symm
  have hrowJ (z : O) : QuadraticInitialBound.quadraticRow
      (fun i => Ideal.span {p i}) (poolPrimary_good F hF) B z = quadraticRow J z :=
    (quadraticRow_eq_primaryPool F hF J hJF z).symm
  have ht := same_ray_quadratic_pair_poisson R hinj S p (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    A B hd hr W M hM
  simpa only [hn, hrowI, hrowJ] using ht

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge ActualEisensteinCoordinates
open EisensteinSchwartzPoisson GaussGeneratorTransport QuadraticUnitInvariance PrimaryIdealUnitReindex

theorem canonical_pair_unit_invariant (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (u : Oˣ) (z : O) :
    quadraticRow I (u.val * z) * quadraticRow J (u.val * z) =
      quadraticRow I z * quadraticRow J z := by
  let F : Finset (Ideal O) := {I, J}
  have hF : ∀ lengthScale ∈ F, Admissible lengthScale := by
    intro lengthScale hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hI
    · have hLJ := Finset.mem_singleton.mp hL
      simpa only [hLJ] using hJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  let p := poolPrimary F
  let A := idealSupport F I
  let B := idealSupport F J
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by change (Ideal.span {poolPrimary F i}).IsMaximal; rw [poolPrimary_span F hF i]; infer_instance
  have hcA : Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) :=
    fun i j hij => poolPrimary_coprime F hF (fun h => hij (Subtype.ext h))
  have hcB : Pairwise (Function.onFun IsCoprime (fun i : B => Ideal.span {p i.val})) :=
    fun i j hij => poolPrimary_coprime F hF (fun h => hij (Subtype.ext h))
  have hr : residue (∏ i : A, p i.val) = residue (∏ i : B, p i.val) := by
    rw [Finset.prod_coe_sort, Finset.prod_coe_sort,
      ← primaryGenerator_eq_poolProduct F hF I hIF, ← primaryGenerator_eq_poolProduct F hF J hJF]
    exact hray
  have h := quadratic_pair_unit_invariant
    (fun i : A => p i.val) (fun i => poolPrimary_ne_zero F hF i.val) hcA
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val)
    (fun i : B => p i.val) (fun i => poolPrimary_ne_zero F hF i.val) hcB
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val) hr u z
  have hrowI (w : O) : finiteSexticRow (fun i : A => Ideal.span {p i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) w = quadraticRow I w :=
    (quadraticRow_eq_primarySubset F hF I hIF w).symm
  have hrowJ (w : O) : finiteSexticRow (fun i : B => Ideal.span {p i.val})
      (fun i => poolPrimary_good F hF i.val) (fun _ => 3) w = quadraticRow J w :=
    (quadraticRow_eq_primarySubset F hF J hJF w).symm
  simpa only [hrowI, hrowJ] using h

theorem canonical_masked_pair_summable {α : Type*} (R : α → Ideal O) (S : Finset α)
    (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hW
  intro z
  simp only [norm_mul]
  calc
    _ ≤ 1 * (1 * 1) * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ := by
      gcongr
      · exact rowCoprimeMask_norm_le_one R S z
      · exact quadraticRow_norm_le_one I z
      · exact quadraticRow_norm_le_one J z
    _ = _ := by ring

theorem canonical_pair_lattice_eq_primary_ideal_sum
    {α : Type*} (R : α → Ideal O) (S : Finset α)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (Nat.card Oˣ : ℂ) * ∑' lengthScale : GoodIdeal,
      rowCoprimeMask R S (primaryGenerator lengthScale.val) *
      (quadraticRow I (primaryGenerator lengthScale.val) * quadraticRow J (primaryGenerator lengthScale.val)) *
      W ((Ideal.absNorm lengthScale.val : ℝ) / M) := by
  have hs := canonical_masked_pair_summable R S I J W M hM
  have hu (u : Oˣ) (lengthScale : GoodIdeal) :
      rowCoprimeMask R S (u.val * primaryGenerator lengthScale.val) *
        (quadraticRow I (u.val * primaryGenerator lengthScale.val) * quadraticRow J (u.val * primaryGenerator lengthScale.val)) *
        W (‖eisEmbedding (u.val * primaryGenerator lengthScale.val)‖ ^ 2 / M) =
      rowCoprimeMask R S (primaryGenerator lengthScale.val) *
        (quadraticRow I (primaryGenerator lengthScale.val) * quadraticRow J (primaryGenerator lengthScale.val)) *
        W (‖eisEmbedding (primaryGenerator lengthScale.val)‖ ^ 2 / M) := by
    rw [rowCoprimeMask_unit_mul, canonical_pair_unit_invariant I J hI hJ hray,
      norm_eisEmbedding_unit_mul]
  have ht := tsum_ramified_mask_unit_invariant _ hs hu
  change (∑' z : O, if lambda ∣ z then (0 : ℂ) else _) = _ at ht
  have hn (lengthScale : GoodIdeal) := primaryGenerator_norm_sq lengthScale.val lengthScale.property
  simpa only [hn] using ht

theorem canonical_mask_lattice_eq_six_all_ideals
    {α : Type*} (R : α → Ideal O) (S : Finset α)
    (hmask : ∀ z : O, lambda ∣ z → rowCoprimeMask R S z = 0)
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (6 : ℂ) * ∑' lengthScale : Ideal O,
      rowCoprimeMask R S (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) := by
  have ht := canonical_pair_lattice_eq_primary_ideal_sum R S I J hI hJ hray W M hM
  rw [card_units_eq_six] at ht
  have hl : (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ∑' z : O, rowCoprimeMask R S z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M) := by
    apply tsum_congr
    intro z
    by_cases hz : lambda ∣ z
    · simp [hz, hmask z hz]
    · rw [ite_eq_right hz]
  rw [hl] at ht
  rw [ht]
  congr 1
  let f : Ideal O → ℂ := fun lengthScale => rowCoprimeMask R S (primaryGenerator lengthScale) *
    (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
    W ((Ideal.absNorm lengthScale : ℝ) / M)
  change (∑' lengthScale : GoodIdeal, f lengthScale.val) = ∑' lengthScale : Ideal O, f lengthScale
  have hsub : (∑' lengthScale : GoodIdeal, f lengthScale.val) =
      ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | primaryGenerator lengthScale ≠ 0} : Set (Ideal O)).indicator f lengthScale :=
    tsum_subtype _ f
  rw [hsub]
  apply tsum_congr
  intro lengthScale
  by_cases hg : primaryGenerator lengthScale ≠ 0
  · exact Set.indicator_of_mem hg f
  · rw [Set.indicator_of_notMem hg]
    have hz : primaryGenerator lengthScale = 0 := not_not.mp hg
    dsimp only [f]
    rw [hz, hmask 0 (dvd_zero _)]
    simp only [zero_mul]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_injective : Function.Injective badPrime := by
  have hgood : lambda ∉ (Ideal.span {(2 : O)} : Ideal O) := by
    have hg := cubicTwoIdeal_good
    change lambda ∉ cubicTwoIdeal at hg
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using hg
  intro i j hij
  cases i <;> cases j
  · rfl
  · exfalso
    apply hgood
    have he : (Ideal.span {lambda} : Ideal O) = Ideal.span {(2 : O)} := hij
    rw [← he]
    exact Ideal.subset_span (by simp)
  · exfalso
    apply hgood
    have he : (Ideal.span {(2 : O)} : Ideal O) = Ideal.span {lambda} := hij
    rw [he]
    exact Ideal.subset_span (by simp)
  · rfl

theorem supported_primaryGenerator_ne_zero (lengthScale : Ideal O) (hL : Supported lengthScale) :
    primaryGenerator lengthScale ≠ 0 :=
  primaryGenerator_ne_zero_of_good_factors lengthScale hL.1 (fun P hP => (hL.2 P hP).1)

theorem supported_span_primaryGenerator_iff (lengthScale : Ideal O) :
    Supported (Ideal.span {primaryGenerator lengthScale}) ↔ Supported lengthScale := by
  constructor
  · intro h
    have hn : primaryGenerator lengthScale ≠ 0 := by
      intro hz
      apply h.1
      simp [hz]
    rwa [(primaryGenerator_spec lengthScale hn).1] at h
  · intro h
    rw [(primaryGenerator_spec lengthScale (supported_primaryGenerator_ne_zero lengthScale h)).1]
    exact h

theorem badPrime_mask_primaryGenerator (lengthScale : Ideal O) :
    rowCoprimeMask badPrime Finset.univ (primaryGenerator lengthScale) = if Supported lengthScale then 1 else 0 := by
  rw [badPrime_mask, supported_span_primaryGenerator_iff]

theorem canonical_supported_lattice_eq_six_ideals
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask badPrime Finset.univ z *
      (quadraticRow I z * quadraticRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
    (6 : ℂ) * ∑' lengthScale : Ideal O, if Supported lengthScale then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0 := by
  have hm (z : O) (hz : lambda ∣ z) : rowCoprimeMask badPrime Finset.univ z = 0 := by
    rw [badPrime_mask]
    have hns : ¬Supported (Ideal.span {z}) := fun h => ((supported_span_iff z).mp h).1 hz
    exact ite_eq_right hns
  rw [canonical_mask_lattice_eq_six_all_ideals badPrime Finset.univ hm I J hI hJ hray W M hM]
  congr 1
  apply tsum_congr
  intro lengthScale
  rw [badPrime_mask_primaryGenerator]
  by_cases hL : Supported lengthScale <;> simp [hL]

theorem canonical_supported_pair_poisson
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    (∑' lengthScale : Ideal O, if Supported lengthScale then χ (primaryGenerator lengthScale) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset Bool).powerset,
          let d := primeSubsetGenerator badPrime E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, badPrime i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hlat := canonical_same_ray_pair_poisson badPrime badPrime_injective Finset.univ I J hI hJ hcop hray W M hM
  have hid := canonical_supported_lattice_eq_six_ideals I J hI hJ hray W M hM
  dsimp only at hlat ⊢
  rw [hid] at hlat
  calc
    _ = (6 : ℂ)⁻¹ * ((M : ℂ) / ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ * _) := by
      rw [← hlat]
      ring
    _ = _ := by ring

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts -/

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

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge QuadraticSquarefreeKernel

theorem supported_mul_iff (A B : Ideal O) : Supported (A * B) ↔ Supported A ∧ Supported B := by
  constructor
  · intro h
    have hA : A ≠ 0 := left_ne_zero_of_mul h.1
    have hB : B ≠ 0 := right_ne_zero_of_mul h.1
    refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩⟩
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inl hP)
    · intro P hP
      apply h.2 P
      rw [UniqueFactorizationMonoid.normalizedFactors_mul hA hB]
      exact Multiset.mem_add.mpr (Or.inr hP)
  · rintro ⟨hA, hB⟩
    refine ⟨mul_ne_zero hA.1 hB.1, ?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hA.1 hB.1] at hP
    rcases Multiset.mem_add.mp hP with hP | hP
    · exact hA.2 P hP
    · exact hB.2 P hP

theorem supported_sq_iff (A : Ideal O) : Supported (A ^ 2) ↔ Supported A := by
  rw [pow_two, supported_mul_iff, and_self]

theorem supported_square_parts (lengthScale : Ideal O) :
    Supported lengthScale ↔ Supported (squarePart lengthScale) ∧ Admissible (squarefreePart lengthScale) := by
  have he := supported_mul_iff (squarePart lengthScale ^ 2) (squarefreePart lengthScale)
  rw [squarePart_sq_mul_squarefreePart, supported_sq_iff] at he
  rw [he]
  have hsf := squarefree_squarefreePart lengthScale
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hsf, hB.2⟩
  · rintro ⟨hA, hB⟩
    exact ⟨hA, hB.1, hB.2.2⟩

def supportedSquarefreeEquiv : {lengthScale : Ideal O // Supported lengthScale} ≃
    ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}) where
  toFun lengthScale := (⟨squarePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).1⟩,
    ⟨squarefreePart lengthScale.val, ((supported_square_parts lengthScale.val).mp lengthScale.property).2⟩)
  invFun p := ⟨p.1.val ^ 2 * p.2.val,
    (supported_mul_iff _ _).mpr ⟨(supported_sq_iff _).mpr p.1.property, admissible_supported p.2.property⟩⟩
  left_inv lengthScale := Subtype.ext (squarePart_sq_mul_squarefreePart lengthScale.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).1
    · exact Subtype.ext (squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2

theorem supported_tsum_squarefree_decomposition (f : Ideal O → ℂ) :
    (∑' lengthScale : Ideal O, if Supported lengthScale then f lengthScale else 0) =
      ∑' p : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}), f (p.1.val ^ 2 * p.2.val) := by
  calc
    _ = ∑' lengthScale : {lengthScale : Ideal O // Supported lengthScale}, f lengthScale.val := by
      calc
        _ = ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)).indicator f lengthScale := by
          apply tsum_congr
          intro lengthScale
          rfl
        _ = _ := (tsum_subtype ({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)) f).symm
    _ = _ := (supportedSquarefreeEquiv.symm.tsum_eq (fun lengthScale => f lengthScale.val)).symm

theorem canonical_quadraticRow_argument_mul (D : Ideal O) (hD : Admissible D) (a b : O) :
    quadraticRow D (a * b) = quadraticRow D a * quadraticRow D b := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  simp only [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  exact QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ a b

theorem canonical_quadraticRow_square_argument (D : Ideal O) (hD : Admissible D) (a : O) :
    quadraticRow D (a ^ 2) = idealZeroMask D a := by
  rw [pow_two, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_squared D hD]

theorem canonical_quadraticRow_primary_squarefree (D : Ideal O) (hD : Admissible D)
    (A B : Ideal O) :
    quadraticRow D (primaryGenerator (A ^ 2 * B)) =
      idealZeroMask D (primaryGenerator A) * quadraticRow D (primaryGenerator B) := by
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (A ^ 2) = primaryGenerator A ^ 2 := map_pow primaryGeneratorHom A 2
  rw [hpow, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_square_argument D hD]

theorem canonical_high_pair_squarefree_decomposition
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : ℝ → ℂ) (M K : ℝ) :
    (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
    ∑' p : ({A : Ideal O // Supported A} × {B : Ideal O // Admissible B}),
      if K < (Ideal.absNorm p.2.val : ℝ) then
        (idealZeroMask I (primaryGenerator p.1.val) * idealZeroMask J (primaryGenerator p.1.val)) *
        (quadraticRow I (primaryGenerator p.2.val) * quadraticRow J (primaryGenerator p.2.val)) *
        W (((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)) / M) else 0 := by
  let f : Ideal O → ℂ := fun lengthScale => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
    (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M) else 0
  have he : (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ∑' lengthScale : Ideal O, if Supported lengthScale then f lengthScale else 0 := by
    apply tsum_congr
    intro lengthScale
    by_cases hL : Supported lengthScale <;> simp [hL, f]
  rw [he, supported_tsum_squarefree_decomposition]
  apply tsum_congr
  intro p
  dsimp only [f]
  rw [(squarePart_mul_squarefree p.1.property.1 p.2.property.2.1).2]
  by_cases hK : K < (Ideal.absNorm p.2.val : ℝ)
  · rw [ite_eq_left hK, ite_eq_left hK, canonical_quadraticRow_primary_squarefree I hI,
      canonical_quadraticRow_primary_squarefree J hJ]
    simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    ring
  · simp only [ite_eq_right hK]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson PrimaryIdealUnitReindex QuadraticSquarefreeKernel

theorem supported_generator_injective :
    Function.Injective (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => primaryGenerator lengthScale.val) := by
  intro I J h
  change primaryGenerator I.val = primaryGenerator J.val at h
  have hi := primaryGenerator_ne_zero_of_good_factors I.val I.property.1 (fun P hP => (I.property.2 P hP).1)
  have hj := primaryGenerator_ne_zero_of_good_factors J.val J.property.1 (fun P hP => (J.property.2 P hP).1)
  apply Subtype.ext
  rw [← (primaryGenerator_spec I.val hi).1, ← (primaryGenerator_spec J.val hj).1, h]

theorem supported_radial_norm_summable (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun lengthScale : Ideal O => if Supported lengthScale then ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ else 0) := by
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  have hp := hs.comp_injective supported_generator_injective
  have hi : Summable (fun lengthScale : {lengthScale : Ideal O // Supported lengthScale} => ‖W ((Ideal.absNorm lengthScale.val : ℝ) / M)‖) := by
    apply hp.congr
    intro lengthScale
    dsimp only [Function.comp_def]
    rw [primaryGenerator_norm_sq lengthScale.val (primaryGenerator_ne_zero_of_good_factors lengthScale.val
      lengthScale.property.1 (fun P hP => (lengthScale.property.2 P hP).1))]
  have ht : Summable (({lengthScale : Ideal O | Supported lengthScale} : Set (Ideal O)).indicator
      (fun lengthScale => ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖)) := (summable_subtype_iff_indicator).mp hi
  exact ht

def originalPairSource (I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) (lengthScale : Ideal O) : ℂ :=
  if Supported lengthScale then (star (quadraticRow I (primaryGenerator lengthScale)) *
    quadraticRow J (primaryGenerator lengthScale)) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0

def originalPairLow (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K then originalPairSource I J W M lengthScale else 0

def originalPairHigh (I J : Ideal O) (W : ℝ → ℂ) (M K : ℝ) (lengthScale : Ideal O) : ℂ :=
  if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then originalPairSource I J W M lengthScale else 0

theorem originalPairSource_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (originalPairSource I J W M) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun lengthScale => norm_nonneg _) _ (supported_radial_norm_summable W M hM)
  intro lengthScale
  by_cases hL : Supported lengthScale
  · simp only [originalPairSource, ite_eq_left hL, norm_mul, norm_star]
    calc
      _ ≤ (1 * 1) * ‖W ((Ideal.absNorm lengthScale : ℝ) / M)‖ := by
        gcongr
        · exact quadraticRow_norm_le_one I _
        · exact quadraticRow_norm_le_one J _
      _ = _ := by ring
  · simp only [originalPairSource, ite_eq_right hL, norm_zero, le_refl]

theorem originalPairLow_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairLow I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairHigh I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

theorem originalPairHigh_eq_source_sub_low (I J : Ideal O) (W : 𝓢(ℝ, ℂ))
    (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairHigh I J W M K lengthScale) =
      (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) -
        ∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale := by
  calc
    _ = ∑' lengthScale : Ideal O, (originalPairSource I J W M lengthScale - originalPairLow I J W M K lengthScale) := by
      apply tsum_congr
      intro lengthScale
      by_cases hK : (Ideal.absNorm (squarefreePart lengthScale) : ℝ) ≤ K
      · simp [originalPairHigh, originalPairLow, hK, not_lt.mpr hK]
      · simp [originalPairHigh, originalPairLow, hK, lt_of_not_ge hK]
    _ = _ := (originalPairSource_summable I J W M hM).tsum_sub (originalPairLow_summable I J W M K hM)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

theorem canonical_gcd_masked_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := primaryGenerator I * primaryGenerator J
    let χ := fun z => quadraticRow I z * quadraticRow J z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
      χ (primaryGenerator lengthScale) * W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  let R := fun P : gcdMaskPrimes D => P.val
  have hm (z : O) (hz : lambda ∣ z) : rowCoprimeMask R Finset.univ z = 0 := by
    rw [gcdMaskPrimes_mask, badPrime_mask]
    have hns : ¬Supported (Ideal.span {z}) := fun h => (supported_span_iff z).mp h |>.1 hz
    simp only [ite_eq_right hns, zero_mul]
  have hlat := canonical_same_ray_pair_poisson R Subtype.val_injective Finset.univ I J hI hJ hcop hray W M hM
  have hid := canonical_mask_lattice_eq_six_all_ideals R Finset.univ hm I J hI hJ hray W M hM
  have he : (∑' lengthScale : Ideal O, rowCoprimeMask R Finset.univ (primaryGenerator lengthScale) *
      (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
      W ((Ideal.absNorm lengthScale : ℝ) / M)) =
      ∑' lengthScale : Ideal O, if Supported lengthScale then idealZeroMask D (primaryGenerator lengthScale) *
        (quadraticRow I (primaryGenerator lengthScale) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0 := by
    apply tsum_congr
    intro lengthScale
    rw [gcdMaskPrimes_mask, badPrime_mask_primaryGenerator]
    by_cases hL : Supported lengthScale <;> simp [hL]
  rw [he] at hid
  dsimp only at hlat ⊢
  rw [hid] at hlat
  calc
    _ = (6 : ℂ)⁻¹ * ((M : ℂ) / ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ * _) := by
      rw [← hlat]
      ring
    _ = _ := by ring

theorem canonical_pair_divisor_mask (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (z : O) :
    star (quadraticRow I z) * quadraticRow J z =
      idealZeroMask D z *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by
  rw [canonical_quadraticRow_star I hI, quadraticRow_divisor_factor I D hI hDI,
    quadraticRow_divisor_factor J D hJ hDJ]
  calc
    _ = (quadraticRow D z * quadraticRow D z) *
        (quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z) := by ring
    _ = _ := by rw [canonical_quadraticRow_squared D (admissible_of_dvd hI hDI)]

theorem canonical_original_pair_poisson
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let I' := idealQuotient D I
    let J' := idealQuotient D J
    let n := primaryGenerator I' * primaryGenerator J'
    let χ := fun z => quadraticRow I' z * quadraticRow J' z
    let R := fun P : gcdMaskPrimes D => P.val
    (∑' lengthScale : Ideal O, if Supported lengthScale then
      (star (quadraticRow I (primaryGenerator lengthScale)) * quadraticRow J (primaryGenerator lengthScale)) *
        W ((Ideal.absNorm lengthScale : ℝ) / M) else 0) =
      ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hDI : D ∣ I := hgcd ▸ gcd_dvd_left I J
  have hDJ : D ∣ J := hgcd ▸ gcd_dvd_right I J
  have hD := admissible_of_dvd hI hDI
  have hIq := admissible_idealQuotient hI hDI
  have hJq := admissible_idealQuotient hJ hDJ
  have hcop := (gcd_eq_iff_quotient_coprime D I J hD.1 hDI hDJ).mp hgcd
  have hqray := columnRay_idealQuotient_eq D I J hI hJ hDI hDJ hray
  have h := canonical_gcd_masked_pair_poisson D (idealQuotient D I) (idealQuotient D J)
    hIq hJq hcop hqray W M hM
  simpa only [canonical_pair_divisor_mask D I J hI hJ hDI hDJ] using h

theorem residual_pair_nontrivial (D I J : Ideal O) (hDI : D ∣ I) (hDJ : D ∣ J)
    (hIJ : I ≠ J) : idealQuotient D I ≠ 1 ∨ idealQuotient D J ≠ 1 := by
  by_contra hn
  push Not at hn
  apply hIJ
  calc
    I = D * idealQuotient D I := (idealQuotient_mul hDI).symm
    _ = D := by rw [hn.1, mul_one]
    _ = D * idealQuotient D J := by rw [hn.2, mul_one]
    _ = J := idealQuotient_mul hDJ

theorem original_pair_dual_remove_zero (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (hIJ : I ≠ J) (f : O → ℂ) :
    (∑' z : O, quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z * f z) =
      ∑' z : O, if z = 0 then 0 else
        quadraticRow (idealQuotient D I) z * quadraticRow (idealQuotient D J) z * f z :=
  quadratic_pair_tsum_remove_zero _ _ (admissible_idealQuotient hI hDI)
    (admissible_idealQuotient hJ hDJ) (residual_pair_nontrivial D I J hDI hDJ hIJ) f

end

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss QuadraticSquarefreeKernel

def rayPairCoefficient (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I J : idealRange N) : ℂ :=
  if gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c then star (a I) * a J else 0

theorem annularRayGcdBlock_eq_pair_high
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        ∑' lengthScale : Ideal O, originalPairHigh I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale := by
  let W := QuadraticInitialBound.annularSieveCutoff
  let f := fun (I J : idealRange N) (lengthScale : Ideal O) =>
    rayPairCoefficient N D c a I J * originalPairHigh I.val J.val W M K lengthScale
  have hf (I J : idealRange N) : Summable (f I J) :=
    (originalPairHigh_summable I.val J.val W M K hM).mul_left _
  have hterm (lengthScale : Ideal O) :
      (if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
        W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) =
      ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := by
    rw [rayPairValue_eq]
    by_cases hs : Supported lengthScale
    · by_cases hk : K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)
      · have hsk : Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) := ⟨hs, hk⟩
        rw [ite_eq_left hsk]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        apply Finset.sum_congr rfl
        intro J _
        dsimp only [f, rayPairCoefficient, originalPairHigh, originalPairSource]
        rw [ite_eq_left hk, ite_eq_left hs]
        by_cases hc : gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c
        · rw [ite_eq_left hc, ite_eq_left hc]
          simp only [star_mul]
          ring
        · rw [ite_eq_right hc, ite_eq_right hc, zero_mul, mul_zero]
      · simp [f, originalPairHigh, hk]
    · simp [f, originalPairHigh, originalPairSource, hs]
  rw [annularRayGcdBlock_eq_tsum M N K hM D c a]
  change (∑' lengthScale : Ideal O, if Supported lengthScale ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then
    W ((Ideal.absNorm lengthScale : ℝ) / M) * rayPairValue N D c a lengthScale else 0) = _
  calc
    _ = ∑' lengthScale : Ideal O, ∑ I : idealRange N, ∑ J : idealRange N, f I J lengthScale := tsum_congr hterm
    _ = ∑ I : idealRange N, ∑' lengthScale : Ideal O, ∑ J : idealRange N, f I J lengthScale :=
      Summable.tsum_finsetSum (fun I _ => summable_sum (fun J _ => hf I J))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      rw [Summable.tsum_finsetSum (fun J _ => hf I J)]
      apply Finset.sum_congr rfl
      intro J _
      exact tsum_mul_left

theorem annularRayGcdBlock_eq_source_sub_low
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        ((∑' lengthScale : Ideal O, originalPairSource I.val J.val QuadraticInitialBound.annularSieveCutoff M lengthScale) -
          ∑' lengthScale : Ideal O, originalPairLow I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale) := by
  rw [annularRayGcdBlock_eq_pair_high M N K hM D c a]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  rw [originalPairHigh_eq_source_sub_low I.val J.val _ M K hM]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

def originalPairDualKernel (D I J : Ideal O) (W : ℝ → ℂ) (M : ℝ) : ℂ :=
  let I' := idealQuotient D I
  let J' := idealQuotient D J
  let n := primaryGenerator I' * primaryGenerator J'
  let χ := fun z => quadraticRow I' z * quadraticRow J' z
  let R := fun P : gcdMaskPrimes D => P.val
  ((M : ℂ) / (6 * ‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ (Finset.univ : Finset (gcdMaskPrimes D)).powerset,
      let d := primeSubsetGenerator R E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
      ∑' h : O, χ h * paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))

theorem originalPairSource_poisson (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D) (hray : columnRay I = columnRay J)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairSource I J W M lengthScale) = originalPairDualKernel D I J W M :=
  canonical_original_pair_poisson D I J hI hJ hgcd hray W M hM

theorem annularRayGcdBlock_poisson
    (M N K : ℝ) (hM : 0 < M) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : idealRange N, ∑ J : idealRange N, rayPairCoefficient N D c a I J *
        (originalPairDualKernel D I.val J.val QuadraticInitialBound.annularSieveCutoff M -
          ∑' lengthScale : Ideal O, originalPairLow I.val J.val QuadraticInitialBound.annularSieveCutoff M K lengthScale) := by
  rw [annularRayGcdBlock_eq_source_sub_low M N K hM D c a]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  by_cases hc : gcd I.val J.val = D ∧ columnRay I.val = c ∧ columnRay J.val = c
  · have hray : columnRay I.val = columnRay J.val := hc.2.1.trans hc.2.2.symm
    rw [originalPairSource_poisson D I.val J.val (mem_idealRange.mp I.property).1
      (mem_idealRange.mp J.property).1 hc.1 hray _ M hM]
  · simp only [rayPairCoefficient, ite_eq_right hc, zero_mul]

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic FirstPassCubeLabels JointLogSeparation

theorem columnLog_extract_common {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N : Finset ι) (hd : Disjoint G N)
    (X : ℝ) (hX : 0 < X) :
    columnLog p X (G∪N) = columnLog p (X / primeProductNorm p G) N := by
  have hG := primeProductNorm_pos p hp G
  unfold columnLog
  rw [primeProductNorm_union p G N hd]
  congr 1
  field_simp

theorem normalizedColumn_extract_fixed_profile {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N : Finset ι) (hd : Disjoint G N)
    (X : ℝ) (hX : 0 < X) (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) :
    normalizedColumn p (fun S => g (columnLog p X S)) (G∪N) =
      halfNormalizationCLM U g (columnLog p (X / primeProductNorm p G) N) /
        (Real.sqrt X : ℂ) := by
  have hG := primeProductNorm_pos p hp G
  rw [normalizedColumn_union_test p hp G N hd X (X / primeProductNorm p G)
    hX (div_pos hX hG) U hUc hUs g hU]
  have he : primeProductNorm p G * (X / primeProductNorm p G) / X = 1 := by field_simp
  rw [he, Real.log_one, zero_add]

theorem normalizedColumn_pair_extract_fixed_profiles {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (G N M : Finset ι)
    (hGN : Disjoint G N) (hGM : Disjoint G M) (X : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1)
    (hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1) :
    star (normalizedColumn p (fun S => g₁ (columnLog p X S)) (G∪N)) *
      normalizedColumn p (fun S => g₂ (columnLog p X S)) (G∪M) =
      (X : ℂ)⁻¹ * conjugateProfile (halfNormalizationCLM U g₁)
        (columnLog p (X / primeProductNorm p G) N) *
      halfNormalizationCLM U g₂ (columnLog p (X / primeProductNorm p G) M) := by
  have hG := primeProductNorm_pos p hp G
  rw [normalizedColumn_pair_union p hp G N M hGN hGM X (X / primeProductNorm p G)
    hX (div_pos hX hG) U hUc hUs g₁ g₂ hU₁ hU₂]
  have he : primeProductNorm p G * (X / primeProductNorm p G) / X = 1 := by field_simp
  rw [he, Real.log_one, zero_add, zero_add]

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassIntegration (tupleSourceSum tupleSource_uniform_transfer childGeometricMean)
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualSecondVariableSectorSource
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ)
    (D₀ E₀ V₀ : ℝ) (X : SecondSupportData ι → ℝ) (X₀ K Y : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSupportLabel p B v₁ v₂ ε₁ ε₂ x) (secondSupportRow p x) (-secondSupportRow p x)
    A₁ A₂ W windows (secondSectorZ p (X x) X₀ x) (secondSectorUd p D₀ x)
    (secondSectorUe p E₀ x) (secondSectorUv p V₀ x) (secondSectorKap p K x)
    X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2))

theorem actual_second_variable_sector_uniform_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (ε : ℝ) (hε : 0 < ε) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hwindows : ∀ j x, windows j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧
      ∀ D₀ E₀ V₀ X₀ K Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1 + Y*K/(D₀*E₀^2*V₀^2*X₀^2))^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
          Cₛ * FirstPassCubeLabels.firstLogDensity J t₁ *
            FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (X : SecondSupportData ι → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow windows
          (secondSectorZ p (X x) X₀ x) (secondSectorUd p D₀ x) (secondSectorUe p E₀ x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
          A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y‖ ≤
        (Bnd * Cₐ * (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, htrans⟩ :=
    tupleSource_uniform_transfer p hp hcop hg ε hε A₁ A₂ W windows M hM hwindows A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro D₀ E₀ V₀ X₀ K Y hD₀ hE₀ hV₀ hX₀ hK hY
  have hR : 0 < Y*K/(D₀*E₀^2*V₀^2*X₀^2) := by positivity
  obtain ⟨b, hb, hbound⟩ := htrans _ hR
  refine ⟨b, hb, ?_⟩
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m X hv hCB hD hBnd hL hmap hT0 hnorm hw
  let encode := secondSupportTuple p B v₁ v₂ ε₁ ε₂
  have hi : Function.Injective encode := secondSupportTuple_injective p hinj B v₁ v₂ ε₁ ε₂
  let decode := Function.invFun encode
  have hdec (x : SecondSupportData ι) : decode (encode x) = x := Function.leftInverse_invFun hi x
  let s' := s.image encode
  let w' := fun x => w (decode x)
  let label' := fun x => secondSupportLabel p B v₁ v₂ ε₁ ε₂ (decode x)
  let z' := fun x => secondSectorZ p (X (decode x)) X₀ (decode x)
  let ud' := fun x => secondSectorUd p D₀ (decode x)
  let ue' := fun x => secondSectorUe p E₀ (decode x)
  let uv' := fun x => secondSectorUv p V₀ (decode x)
  let kap' := fun x => secondSectorKap p K (decode x)
  have hsvalid : ∀ x ∈ s', SecondPassFiber.Valid x (SecondPassFiber.newLabel x)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}) (SecondPassFiber.newRow x) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact secondSupportTuple_valid p B v₁ v₂ ε₁ ε₂ hv a (hCB a ha) (hD a ha)
  have hsmap : ∀ x ∈ s', (SecondPassFiber.newLabel x, SecondPassFiber.newRow x) ∈ T := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hmap a ha
  have hsw : ∀ x ∈ s', ‖w' x‖ * ‖outerWindow windows (z' x) (ud' x) (ue' x) (uv' x) (kap' x)‖ ≤ Bnd := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [w', z', ud', ue', uv', kap']
    rw [hdec]
    exact hw a ha
  have hslabel : ∀ x ∈ s', Ideal.span {label' x} = SecondPassFiber.newLabel x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    dsimp only [label']
    rw [hdec]
    exact secondSupportLabel_span p B v₁ v₂ ε₁ ε₂ a
  have hout := hbound s' T (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
    w' Bnd lengthScale label' F Ψ₁ Ψ₂ m z' ud' ue' uv' kap' X₀ X₀
    (sector_b0_ne_bot p hp B v₁ v₂ ε₁ ε₂) hBnd hL hsvalid hsmap hT0 hnorm hsw hslabel
  have hsource : tupleSourceSum p hp hcop hg s' w' label' F Ψ₁ Ψ₂ m
      A₁ A₂ W windows z' ud' ue' uv' kap' X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2)) =
      actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
        A₁ A₂ W windows D₀ E₀ V₀ X X₀ K Y := by
    unfold tupleSourceSum actualSecondVariableSectorSource
    rw [Finset.sum_image (fun a ha c hc h => hi h)]
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [w', label', z', ud', ue', uv', kap']
    rw [hdec]
    rfl
  rw [hsource] at hout
  exact hout

end SecondPassArithmetic

end

end OAI

end

