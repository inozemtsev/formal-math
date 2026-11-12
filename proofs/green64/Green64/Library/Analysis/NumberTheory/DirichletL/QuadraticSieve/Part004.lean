module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Poisson.Part002

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / QuadraticSieve / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals -/

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
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_double_sum_real_factor_fun {n p : Type*} [Fintype n] [Fintype p]
    (u z : n → p → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z j k)‖ = c * ‖∑ j, ∑ k, u j k * z j k‖ := by
  have he : (∑ j, ∑ k, u j k * ((c : ℂ) * z j k)) =
      (c : ℂ) * ∑ j, ∑ k, u j k * z j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O)
    (left : n → Ideal O) (right : p → Ideal O) (M F : ℝ) (h : O)
    (d : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  ((Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def dualProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualProductDivisorMiddleAt W K rows left right a b M F P h := by
  classical
  unfold dualProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    dualProductDivisorMiddleAt W K rows left right a b M F P h ≤
      dualMiddleWindowAt W S T rows left right a b M F (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i j k => dualPrincipalKernel W rows left right M F h d i j k)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [dualMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold dualPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor_fun _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.dual_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hs := hexp.dual_middle_pool deltaLoss hδ ε hε S T B N M F U hB hN hM hF hU
    (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2))
    (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := dualProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M F P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => dualProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M F P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc in
theorem secondChildColumn_norm_le_test (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondChildColumn p hp hcop hg Ψ m f y H S‖ ≤ ‖H S‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondChildColumn,norm_mul,norm_pow,columnCoefficient_norm_one p hp hcop hg hc]
  calc
    _ ≤ 1 * 1 * 1 * 1^4 * 1 * ‖H S‖ := by
      gcongr <;> first
        | exact hΨ _
        | exact hm
        | exact finiteSquarefreeRow_norm_le_one _ hg S f
        | exact finiteSquarefreeRow_norm_le_one _ hg S y
    _ = _ := by ring

include hc in

theorem fixedChildRow_elementary
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m f y : O) (H : Finset ι → ℂ) (X M : ℝ) (hX : 1 ≤ X) (hM : 0 ≤ M)
    (hH : ∀ S, ‖H S‖ ≤ M) (hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ X) :
    ‖fixedChildRow p hp hcop hg F Ψ m H f y‖ ≤ 128 * X * M := by
  have heq : fixedChildRow p hp hcop hg F Ψ m H f y =
      ∑ S ∈ boundedPrimeSupports p F X, secondChildColumn p hp hcop hg Ψ m f y H S := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hHS : H S = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hS,hSupp S h⟩)
    simp only [secondChildColumn,hHS,mul_zero]
  rw [heq]
  calc
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, ‖secondChildColumn p hp hcop hg Ψ m f y H S‖ := norm_sum_le _ _
    _ ≤ ∑ S ∈ boundedPrimeSupports p F X, M :=
      Finset.sum_le_sum (fun S hS => (secondChildColumn_norm_le_test p hp hcop hg hc Ψ hΨ m f y H S).trans (hH S))
    _ = ((boundedPrimeSupports p F X).card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F X hX) hM

end SecondPassArithmetic

namespace DescentFiberCost
open ActualEisensteinCubic ConcreteTraceCRT
open ShortDraftLatticeCount ActualEisensteinCoordinates

theorem finite_element_count_real (S : Finset O) (K : ℝ) (hK : 1 ≤ K)
    (hS : ∀ z ∈ S, ‖eisEmbedding z‖^2 ≤ K) : (S.card : ℝ) ≤ 128*K := by
  have hbound : ∀ z ∈ S, q (coords z) ≤ (⌊K⌋₊ : ℕ) := by
    intro z hz
    have hq : (qNat z : ℝ) ≤ K := by
      rw [qNat_eq_absNorm_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
      exact hS z hz
    have hn := Nat.le_floor hq
    have he : (qNat z : ℤ) = q (coords z) := Int.toNat_of_nonneg (qO_nonneg z)
    rw [← he]
    exact_mod_cast hn
  have hcard := actual_eisenstein_count S ⌊K⌋₊ hbound
  have hr : (S.card : ℝ) ≤ 64*((⌊K⌋₊ : ℝ)+1) := by exact_mod_cast hcard
  have hf : (⌊K⌋₊ : ℝ) ≤ K := Nat.floor_le (by linarith)
  linarith

theorem finite_label_row_count (T : Finset (Ideal O × O)) (F K : ℝ)
    (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hT : ∀ z ∈ T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖eisEmbedding z.2‖^2 ≤ K) :
    (T.card : ℝ) ≤ 128^2 * F * K := by
  let I := T.image Prod.fst
  let R := T.image Prod.snd
  have hI : (I.card : ℝ) ≤ 128*F := by
    apply finite_ideal_count_real I F hF
    · intro J hJ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hJ
      exact (hT z hz).1
    · intro J hJ
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hJ
      exact (hT z hz).2.1
  have hR : (R.card : ℝ) ≤ 128*K := by
    apply finite_element_count_real R K hK
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    exact (hT z hz).2.2
  have hsub : T ⊆ I ×ˢ R := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  have hn := Finset.card_le_card hsub
  rw [Finset.card_product] at hn
  calc
    _ ≤ (I.card : ℝ) * R.card := by exact_mod_cast hn
    _ ≤ (128*F)*(128*K) := mul_le_mul hI hR (Nat.cast_nonneg _) (by linarith)
    _ = _ := by ring

end DescentFiberCost

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open FirstPassCubeLabels (primeProductNorm columnLog)

theorem childEnergy_elementary_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X F K A M a b : ℝ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (_hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV : ∀ s, ‖V s‖ ≤ M) (hVsupp : ∀ s, V s ≠ 0 → |s| ≤ A)
    (hT : ∀ z ∈ T, z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b / (X*F) ≤
      6 * 128^4 * K * (max 1 (X*Real.exp A))^2 * M^2 / X := by
  let H := fixedSecondTest p V X a b testNegative
  let Y := max 1 (X*Real.exp A)
  have hX0 : 0 < X := hX
  have hF0 : 0 < F := by linarith
  have hY : 1 ≤ Y := le_max_left _ _
  have hH : ∀ S, ‖H S‖ ≤ M := by
    intro S
    cases testNegative <;>
      simpa only [H,fixedSecondTest,Bool.false_eq_true,ite_false,ite_true,
        fixedColumnTest,norm_mul,norm_star,FourierBridge.logPhase_norm,mul_one] using hV (columnLog p X S)
  have hSupp : ∀ S, H S ≠ 0 → primeProductNorm p S ≤ Y := by
    intro S hS
    have hv : V (columnLog p X S) ≠ 0 := by
      intro hz
      apply hS
      cases testNegative <;> simp [H,fixedSecondTest,fixedColumnTest,hz]
    exact (columnLog_norm_upper p hp X A hX0 S ((le_abs_self _).trans (hVsupp _ hv))).trans
      (le_max_right _ _)
  have hrow (f y : O) : ‖fixedChildRow p hp hcop hg pool Ψ m H f y‖ ≤ 128*Y*M :=
    fixedChildRow_elementary p hp hcop hg hc hinj pool Ψ hΨ m f y H Y M hY hM hH hSupp
  have hu (u : Oˣ) : (∑ z ∈ T, ‖idealChildRow p hp hcop hg pool Ψ m H rowNegative u z‖^2) ≤
      (T.card : ℝ) * (128*Y*M)^2 := by
    calc
      _ ≤ ∑ z ∈ T, (128*Y*M)^2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact pow_le_pow_left₀ (norm_nonneg _) (hrow _ _) 2
      _ = _ := by simp
  have he := idealChildRow_unit_energy_le p hp hcop hg pool Ψ m H rowNegative T
    ((T.card : ℝ)*(128*Y*M)^2) hu
  change childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b ≤ _ at he
  have ht := DescentFiberCost.finite_label_row_count T F K hF hK hT
  apply (div_le_iff₀ (mul_pos hX0 hF0)).mpr
  calc
    _ ≤ 6*((T.card : ℝ)*(128*Y*M)^2) := he
    _ ≤ 6*((128^2*F*K)*(128*Y*M)^2) := by gcongr
    _ = (6*128^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*(X*F) := by
      dsimp [Y]
      field_simp

end SecondPassIntegration

namespace ShortDraftLatticeCount
open ActualEisensteinCubic ActualEisensteinCoordinates ConcreteTraceCRT

theorem rowNormBall_norm_sq_le (H : ℕ) (k : ActualEisensteinCubic.O) (hk : k ∈ rowNormBall H) :
    ‖eisEmbedding k‖^2 ≤ 3*((H : ℝ)+1)^2 := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hv
  obtain ⟨haL,haU⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hbL,hbU⟩ := Finset.mem_Icc.mp hb
  have ha2 : v.1^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haU) (show 0 ≤ (H : ℤ)+1+v.1 by linarith)]
  have hb2 : v.2^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbU) (show 0 ≤ (H : ℤ)+1+v.2 by linarith)]
  have hq : v.1*v.1-v.1*v.2+v.2*v.2 ≤ 3*((H : ℤ)+1)^2 := by
    nlinarith [sq_nonneg (v.1+v.2)]
  rw [eisEmbedding_eval_norm_sq]
  exact_mod_cast hq

end ShortDraftLatticeCount
namespace SecondPassArithmetic
open ActualEisensteinCubic ConcreteTraceCRT

theorem secondFrequencyCutoff_norm_sq_le (scale H : ℝ) (k : ActualEisensteinCubic.O)
    (hk : k ∈ secondFrequencyCutoff scale H) :
    ‖eisEmbedding k‖^2 ≤ 3*((⌈H/scale⌉₊ : ℝ)+1)^2 :=
  ShortDraftLatticeCount.rowNormBall_norm_sq_le _ k hk

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma green_identity_interval (f g : ℝ → ℂ) (a b : ℝ)
    (hf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ f x)
    (hg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ g x)
    (hdf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv f) x)
    (hdg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv g) x)
    (hif : IntervalIntegrable (deriv (deriv f)) volume a b)
    (hig : IntervalIntegrable (deriv (deriv g)) volume a b) :
    (∫x in a..b,deriv (deriv f) x*star (g x)-f x*star (deriv (deriv g) x)) =
      (deriv f b*star (g b)-f b*star (deriv g b)) -
      (deriv f a*star (g a)-f a*star (deriv g a)) := by
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    convert (((hdf x hx).hasDerivAt.mul (hg x hx).hasDerivAt.star).sub
      ((hf x hx).hasDerivAt.mul (hdg x hx).hasDerivAt.star)) using 1 ; ring
  · have hstar : IntervalIntegrable (fun x => star (deriv (deriv g) x)) volume a b := by
      apply hig.mono_fun
        ((aestronglyMeasurable_deriv (deriv g) _).star)
      exact Filter.Eventually.of_forall (fun x => by simp only [Pi.star_apply,norm_star,le_refl])
    exact (hif.mul_continuousOn hgc.star).sub (hstar.continuousOn_mul hfc)

lemma axisSlice_update (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    axisSlice f (Function.update p j t) j = axisSlice f p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

theorem actual_axis_local_regular (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε C : ℝ, 0<ε ∧ ∀t∈Metric.ball (p j) ε,
      0<(Function.update p j t) 2 ∧
      DifferentiableAt ℝ (axisSlice (upperEisensteinField s) p j) t ∧
      DifferentiableAt ℝ (deriv (axisSlice (upperEisensteinField s) p j)) t ∧
      ‖deriv (deriv (axisSlice (upperEisensteinField s) p j)) t‖≤C := by
  obtain ⟨ε,hε,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := axis_summable_derivative_bounds s hs p hv j
  refine ⟨ε,∑'r,M₂ r,hε,?_⟩
  intro t ht
  have hpos := (hbound t ht).1
  have hterms := eisenstein_axis_termwise s hs (Function.update p j t) hpos j
  simp only [axisSlice_update,Function.update_self] at hterms
  have heq := axisSlice_eventuallyEq_of_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) (Function.update p j t) hpos j
  simp only [axisSlice_update,Function.update_self] at heq
  refine ⟨hpos,(hterms.2.2.1.congr_of_eventuallyEq heq).differentiableAt,
    (hterms.2.2.2.congr_of_eventuallyEq heq.deriv).differentiableAt,?_⟩
  rw [heq.deriv.deriv_eq,hterms.2.2.2.deriv]
  exact tsum_of_norm_bounded hM₂.hasSum (fun r => ((hbound t ht).2 r).2.2)

lemma intervalIntegrable_second_of_bound (f : ℝ → ℂ) (C a b : ℝ)
    (hbound : ∀x∈Set.uIcc a b, ‖deriv (deriv f) x‖≤C) :
    IntervalIntegrable (deriv (deriv f)) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b).mono_fun
    (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  exact (hbound x (Set.uIoc_subset_uIcc hx)).trans (le_abs_self C)

theorem actual_eisenstein_local_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε : ℝ, 0<ε ∧ ∀a b : ℝ, Set.uIcc a b ⊆ Metric.ball (p j) ε →
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  obtain ⟨εs,Cs,hεs,hregs⟩ := actual_axis_local_regular s hs p hv j
  obtain ⟨εt,Ct,hεt,hregt⟩ := actual_axis_local_regular t ht p hv j
  refine ⟨min εs εt,lt_min hεs hεt,?_⟩
  intro a b hab
  have hsa (x : ℝ) (hx : x∈Set.uIcc a b) := hregs x
    (Metric.ball_subset_ball (min_le_left _ _) (hab hx))
  have hta (x : ℝ) (hx : x∈Set.uIcc a b) := hregt x
    (Metric.ball_subset_ball (min_le_right _ _) (hab hx))
  apply green_identity_interval
  · exact fun x hx => (hsa x hx).2.1
  · exact fun x hx => (hta x hx).2.1
  · exact fun x hx => (hsa x hx).2.2.1
  · exact fun x hx => (hta x hx).2.2.1
  · exact intervalIntegrable_second_of_bound _ Cs a b (fun x hx => (hsa x hx).2.2.2)
  · exact intervalIntegrable_second_of_bound _ Ct a b (fun x hx => (hta x hx).2.2.2)

lemma actual_axis_differentiable_at (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (ht : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (axisSlice (upperEisensteinField s) p j) t ∧
      DifferentiableAt ℝ (deriv (axisSlice (upperEisensteinField s) p j)) t := by
  obtain ⟨ε,C,hε,hreg⟩ := actual_axis_local_regular s hs (Function.update p j t) ht j
  have h := hreg t (by simpa only [Function.update_self] using Metric.mem_ball_self hε)
  simp only [axisSlice_update] at h
  exact ⟨h.2.1,h.2.2.1⟩

lemma actual_axis_second_locallyIntegrable (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (j : Fin 3) :
    LocallyIntegrableOn (deriv (deriv (axisSlice (upperEisensteinField s) p j)))
      {t : ℝ | 0<(Function.update p j t) 2} volume := by
  intro t ht
  obtain ⟨ε,C,hε,hreg⟩ := actual_axis_local_regular s hs (Function.update p j t) ht j
  simp only [axisSlice_update,Function.update_self,Function.update_idem] at hreg
  refine ⟨Metric.ball t ε,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hε),?_⟩
  have hconst : IntegrableOn (fun _ : ℝ => C) (Metric.ball t ε) volume := integrableOn_const
  apply hconst.mono' (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (hreg x hx).2.2.2

theorem actual_eisenstein_green_interval (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (j : Fin 3) (a b : ℝ)
    (hheight : ∀x∈Set.uIcc a b,0<(Function.update p j x) 2) :
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  apply green_identity_interval
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).2
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).2
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable s hs p j).integrableOn_compact_subset hheight isCompact_uIcc
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable t ht p j).integrableOn_compact_subset hheight isCompact_uIcc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT

lemma periodic_deriv {f : ℝ → ℂ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  exact funext hf

lemma embedding_rectangular_period :
    3*eisEmbedding (ActualEisensteinCoordinates.eval 1 2) = (3*Real.sqrt 3:ℝ)*Complex.I := by
  rw [eisEmbedding_eval]
  norm_num only [Int.cast_one,Int.cast_ofNat]
  unfold EisensteinEmbedding.omega3
  push_cast
  ring

lemma actual_axis_periodic_zero (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Function.Periodic (axisSlice (upperEisensteinField s) p 0) 3 := by
  intro x
  have h := upperEisenstein_periodic (1:O) ((x:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv s hs
  have hz : ((x+3:ℝ):ℂ)+(p 1:ℂ)*Complex.I =
      ((x:ℂ)+(p 1:ℂ)*Complex.I)+3*eisEmbedding (1:O) := by simp; ring
  unfold axisSlice upperEisensteinField
  simp only [Function.update,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,
    dite_false,dite_true]
  simp only [dite_eq_left hv]
  rw [hz]
  exact h

lemma actual_axis_periodic_one (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Function.Periodic (axisSlice (upperEisensteinField s) p 1) (3*Real.sqrt 3) := by
  intro y
  have h := upperEisenstein_periodic (ActualEisensteinCoordinates.eval 1 2)
    ((p 0:ℂ)+(y:ℂ)*Complex.I) (p 2) hv s hs
  have hz : (p 0:ℂ)+((y+3*Real.sqrt 3:ℝ):ℂ)*Complex.I =
      ((p 0:ℂ)+(y:ℂ)*Complex.I)+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 2) := by
    rw [embedding_rectangular_period]
    push_cast
    ring
  unfold axisSlice upperEisensteinField
  simp only [Function.update,show (0:Fin 3)≠1 by decide,show (2:Fin 3)≠1 by decide,
    dite_false,dite_true]
  simp only [dite_eq_left hv]
  rw [hz]
  exact h

lemma green_periodic_zero {f g : ℝ → ℂ} {T : ℝ}
    (hf : Function.Periodic f T) (hg : Function.Periodic g T) :
    (deriv f T*star (g T)-f T*star (deriv g T)) -
      (deriv f 0*star (g 0)-f 0*star (deriv g 0)) = 0 := by
  have hf0 : f T=f 0 := by simpa only [zero_add] using hf 0
  have hg0 : g T=g 0 := by simpa only [zero_add] using hg 0
  have hdf : deriv f T=deriv f 0 := by simpa only [zero_add] using periodic_deriv hf 0
  have hdg : deriv g T=deriv g 0 := by simpa only [zero_add] using periodic_deriv hg 0
  rw [hf0,hg0,hdf,hdg,sub_self]

theorem actual_green_real_period_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∫x in (0:ℝ)..3,
      deriv (deriv (axisSlice (upperEisensteinField s) p 0)) x *
        star (axisSlice (upperEisensteinField t) p 0 x) -
      axisSlice (upperEisensteinField s) p 0 x *
        star (deriv (deriv (axisSlice (upperEisensteinField t) p 0)) x)) = 0 := by
  rw [actual_eisenstein_green_interval s t hs ht p 0 0 3]
  · exact green_periodic_zero (actual_axis_periodic_zero s hs p hv) (actual_axis_periodic_zero t ht p hv)
  · intro x hx
    simpa only [Function.update_of_ne (show (2:Fin 3)≠0 by decide)] using hv

theorem actual_green_imag_period_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∫x in (0:ℝ)..(3*Real.sqrt 3),
      deriv (deriv (axisSlice (upperEisensteinField s) p 1)) x *
        star (axisSlice (upperEisensteinField t) p 1 x) -
      axisSlice (upperEisensteinField s) p 1 x *
        star (deriv (deriv (axisSlice (upperEisensteinField t) p 1)) x)) = 0 := by
  rw [actual_eisenstein_green_interval s t hs ht p 1 0 (3*Real.sqrt 3)]
  · exact green_periodic_zero (actual_axis_periodic_one s hs p hv) (actual_axis_periodic_one t ht p hv)
  · intro x hx
    simpa only [Function.update_of_ne (show (2:Fin 3)≠1 by decide)] using hv

def cuspRectangle : Set (ℝ × ℝ) := Set.Icc 0 3 ×ˢ Set.Icc 0 (3*Real.sqrt 3)

lemma cuspRectangle_volume : volume cuspRectangle = ENNReal.ofReal (9*Real.sqrt 3) := by
  rw [cuspRectangle,MeasureTheory.Measure.volume_eq_prod,MeasureTheory.Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
  norm_num only [sub_zero]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

lemma cuspRectangle_volume_twice_period : volume cuspRectangle = 2*volume periodDomain := by
  rw [cuspRectangle_volume,periodDomain_volume]
  have h2 : (2:ENNReal)=ENNReal.ofReal (2:ℝ) := by norm_num
  rw [h2,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

lemma rectangular_period_change_of_basis :
    (3:ℂ)=periodBasis 0 ∧
    (3*Real.sqrt 3:ℝ)*Complex.I=periodBasis 0+2*periodBasis 1 := by
  constructor
  · exact periodBasis_zero.symm
  · rw [periodBasis_zero,periodBasis_one]
    unfold EisensteinEmbedding.omega3
    push_cast
    ring

lemma rectangular_period_matrix_det :
    Matrix.det (!![(1:ℤ),1;0,2]) = 2 := by norm_num [Matrix.det_fin_two]

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity -/

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology

def greenWronskian (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv f x*star (g x)-f x*star (deriv g x)

def greenSecondTerm (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv (deriv f) x*star (g x)-f x*star (deriv (deriv g) x)

lemma hasDerivAt_greenWronskian (f g : ℝ → ℂ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hdf : DifferentiableAt ℝ (deriv f) x) (hdg : DifferentiableAt ℝ (deriv g) x) :
    HasDerivAt (greenWronskian f g) (greenSecondTerm f g x) x := by
  convert ((hdf.hasDerivAt.mul hg.hasDerivAt.star).sub
    (hf.hasDerivAt.mul hdg.hasDerivAt.star)) using 1
  · rfl
  · dsimp [greenSecondTerm]
    ring

lemma weighted_vertical_green (f g : ℝ → ℂ) (a b : ℝ)
    (hpos : ∀x∈Set.uIcc a b,0<x)
    (hf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ f x)
    (hg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ g x)
    (hdf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv f) x)
    (hdg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv g) x)
    (hif : IntervalIntegrable (deriv (deriv f)) volume a b)
    (hig : IntervalIntegrable (deriv (deriv g)) volume a b) :
    (∫x in a..b, greenSecondTerm f g x/(x:ℂ)-greenWronskian f g x/(x:ℂ)^2) =
      greenWronskian f g b/(b:ℂ)-greenWronskian f g a/(a:ℂ) := by
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hdfc : ContinuousOn (deriv f) (Set.uIcc a b) := fun x hx => (hdf x hx).continuousAt.continuousWithinAt
  have hdgc : ContinuousOn (deriv g) (Set.uIcc a b) := fun x hx => (hdg x hx).continuousAt.continuousWithinAt
  have hW : ContinuousOn (greenWronskian f g) (Set.uIcc a b) :=
    (hdfc.mul hgc.star).sub (hfc.mul hdgc.star)
  have hne : ∀x∈Set.uIcc a b,(x:ℂ)≠0 := fun x hx => Complex.ofReal_ne_zero.mpr (hpos x hx).ne'
  have hstar : IntervalIntegrable (fun x => star (deriv (deriv g) x)) volume a b := by
    apply hig.mono_fun ((aestronglyMeasurable_deriv (deriv g) _).star)
    exact Filter.Eventually.of_forall (fun x => by simp only [Pi.star_apply,norm_star,le_refl])
  have hG : IntervalIntegrable (greenSecondTerm f g) volume a b :=
    (hif.mul_continuousOn hgc.star).sub (hstar.continuousOn_mul hfc)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h := (hasDerivAt_greenWronskian f g x (hf x hx) (hg x hx) (hdf x hx) (hdg x hx)).div
      ((hasDerivAt_id x).ofReal_comp) (hne x hx)
    convert h using 1
    · rfl
    · simp only [id_eq,Complex.ofReal_one,mul_one]
      field_simp [hne x hx]

  · have hi₁ := hG.mul_continuousOn (Complex.continuous_ofReal.continuousOn.inv₀ hne)
    have hi₂ : IntervalIntegrable (fun x : ℝ => greenWronskian f g x/(x:ℂ)^2) volume a b :=
      (hW.div (Complex.continuous_ofReal.continuousOn.pow 2)
        (fun x hx => pow_ne_zero 2 (hne x hx))).intervalIntegrable
    simpa only [div_eq_mul_inv,Pi.inv_apply] using hi₁.sub hi₂

theorem actual_eisenstein_vertical_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫v in a..b,
      greenSecondTerm (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) v/(v:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) v/(v:ℂ)^2) =
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) b/(b:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) a/(a:ℂ) := by
  have hpos (x : ℝ) (hx : x∈Set.uIcc a b) : 0<x :=
    lt_of_lt_of_le (lt_min ha hb) hx.1
  have hsafe (x : ℝ) (hx : x∈Set.uIcc a b) : 0<(Function.update p 2 x) 2 := by
    simpa only [Function.update_self] using hpos x hx
  apply weighted_vertical_green _ _ a b hpos
  · exact fun x hx => (actual_axis_differentiable_at s hs p 2 x (hsafe x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at t ht p 2 x (hsafe x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at s hs p 2 x (hsafe x hx)).2
  · exact fun x hx => (actual_axis_differentiable_at t ht p 2 x (hsafe x hx)).2
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable s hs p 2).integrableOn_compact_subset hsafe isCompact_uIcc
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable t ht p 2).integrableOn_compact_subset hsafe isCompact_uIcc

lemma axisSlice_self (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) :
    axisSlice f p j (p j)=f p := by
  simp only [axisSlice,Function.update_eq_self]

theorem actual_eisenstein_green_density (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∑j : Fin 3,greenSecondTerm (axisSlice (upperEisensteinField s) p j)
      (axisSlice (upperEisensteinField t) p j) (p j)) / (p 2:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) (p 2) / (p 2:ℂ)^2 =
    (s*(s-2)-star (t*(t-2))) * upperEisensteinField s p * star (upperEisensteinField t p) /
      (p 2:ℂ)^3 := by
  have hne : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  calc
    _ = (axisLaplacian (upperEisensteinField s) p * star (upperEisensteinField t p) -
        upperEisensteinField s p * star (axisLaplacian (upperEisensteinField t) p)) / (p 2:ℂ)^3 := by
      simp only [greenSecondTerm,greenWronskian,axisSlice_self,axisLaplacian,
        Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,map_sub,map_mul,map_pow,
        map_sum,Complex.star_def,Complex.conj_ofReal]
      field_simp [hne]
      ; ring
    _ = _ := by
      rw [upperEisenstein_eigenfunction s hs p hv,upperEisenstein_eigenfunction t ht p hv]
      simp only [star_mul]
      ring

end CubicEisenstein

namespace CanonicalQuadraticSieve

theorem symmetric_truncation_scales (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    0 < X ∧ 0 < X₀/T ∧ X₀/T ≤ X ∧ X ≤ T*X₀ ∧ 0 ≤ T^4 := by
  have hT0 : 0 < T := by linarith
  have hX : 0 < X := by linarith
  refine ⟨hX,div_pos hX₀ hT0,?_,?_,by positivity⟩
  · apply (div_le_iff₀ hT0).mpr
    nlinarith
  · nlinarith

theorem symmetric_truncation_scalar_bound (m : ℕ) (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    ((X₀/T)/X)^(m+3) + 1/(1+(T*X₀)/X)^(m+3) +
      (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤
      (2 : ℝ)^(m+10)/T^m := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 < X := by linarith
  have hY : 0 < X₀/T := div_pos hX₀ hT0
  have hratio : (X₀/T)/X ≤ 2/T := by
    apply (div_le_iff₀ hX).mpr
    calc
      X₀/T ≤ (2*X)/T := div_le_div_of_nonneg_right (by linarith) hT0.le
      _ = (2/T)*X := by ring
  have hinv : 1/(1+(T*X₀)/X) ≤ 2/T := by
    have hz : T/2 ≤ (T*X₀)/X := (le_div_iff₀ hX).mpr (by nlinarith)
    calc
      _ ≤ 1/(T/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 2/T := by field_simp
  have hpow : (2/T)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hT0 m)
      (pow_le_pow_right₀ hT1 (by omega : m ≤ m+3))
  have h₁ : ((X₀/T)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m :=
    (pow_le_pow_left₀ (by positivity) hratio _).trans hpow
  have h₂ : 1/(1+(T*X₀)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    simpa only [div_pow,one_pow] using (pow_le_pow_left₀ (by positivity) hinv (m+3)).trans hpow
  have hnum : X/(X₀/T) ≤ 2*T := by
    apply (div_le_iff₀ hY).mpr
    have he : 2*T*(X₀/T) = 2*X₀ := by field_simp
    rw [he]
    exact hhi
  have hmin : 1/(2*T) ≤ min 1 (X/(T*X₀)) := by
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
      linarith
    · apply (le_div_iff₀ (mul_pos hT0 hX₀)).mpr
      have he : 1/(2*T)*(T*X₀)=X₀/2 := by field_simp
      rwa [he]
  have hfreq : T ≤ 1+X*T^4/(T*X₀) := by
    have ht2 : 2 ≤ T^2 := by nlinarith
    have ht4 : 2*T^2 ≤ T^4 := by nlinarith [sq_nonneg (T^2-2)]
    have hprod : T*(T*X₀) ≤ X*T^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg (T^2))]
    have hh := (le_div_iff₀ (mul_pos hT0 hX₀)).mpr hprod
    linarith
  have hden : (1/(2*T))^2*T^(m+3) ≤
      (min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3) := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hmin 2)
      (pow_le_pow_left₀ hT0.le hfreq (m+3)) (by positivity) (by positivity)
  have h₃ : (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤ 8/T^m := by
    calc
      _ ≤ (2*T)/((1/(2*T))^2*T^(m+3)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [pow_add]; field_simp; ring
  have hc : 2*(2 : ℝ)^(m+3)+8 ≤ (2 : ℝ)^(m+10) := by
    have hm : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  calc
    _ ≤ (2 : ℝ)^(m+3)/T^m + (2 : ℝ)^(m+3)/T^m + 8/T^m := add_le_add (add_le_add h₁ h₂) h₃
    _ = (2*(2 : ℝ)^(m+3)+8)/T^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)

def SecondSourceSupport {ι : Type*} [DecidableEq ι]
    (p : ι → O) (X M : ℝ) (x : SecondExpansionData ι) : Prop :=
  Disjoint x.sourceCommon x.overlap ∧
    primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem secondExpansionSource_singleton_zero_of_not_support
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hs : ¬ SecondSourceSupport p X M x) :
    secondExpansionSource p hp hcop hg F Ψ m c d z {x}
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y = 0 := by
  by_cases hd : Disjoint x.sourceCommon x.overlap
  · have hb : ¬ primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M :=
      fun hb => hs ⟨hd,hb⟩
    have hz (N : Finset ι) :
        normalizedColumn p (fun A => g (columnLog p X A))
          (x.sourceCommon ∪ (x.overlap ∪ N)) = 0 := by
      by_contra hn
      have h := normalizedColumn_subset_norm_bound p hp g M X hX hgM
        x.sourceCommon (x.overlap ∪ N) (x.sourceCommon ∪ x.overlap)
        (Finset.union_subset_union Finset.Subset.rfl Finset.subset_union_left) hn
      rw [FirstPassCubeLabels.primeProductNorm_union p _ _ hd] at h
      exact hb h
    simp only [secondExpansionSource, Finset.sum_singleton]
    have hk : secondChildKernelPair p hp hcop hg F x.overlap
        (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (-x.frequency)
        (secondSourcePairKernel p
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S))
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S)) W Y) = 0 := by
      unfold secondChildKernelPair
      apply Finset.sum_eq_zero
      intro N hN
      apply Finset.sum_eq_zero
      intro Q hQ
      simp only [secondSourcePairKernel, hz N, star_zero, zero_mul, zero_div, mul_zero]
    rw [hk]
    ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj
      (secondRayPlus Ψ z) m c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      (-x.frequency) (fun _ => 1) x.sourceCommon x.overlap (fun h => hd h.symm)
    rw [secondMaskQuotient_spec p x.divisor x.sourceCommon hE] at hz
    simp only [secondExpansionSource, Finset.sum_singleton,
      secondExpansionQuotient_of_subset p x hE, secondTotalWeight, secondCommonWeight, hz,
      mul_zero, zero_mul]

include hinj in

theorem secondExpansionSource_eq_supported
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (s : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon) :
    secondExpansionSource p hp hcop hg F Ψ m c d z s
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y =
    secondExpansionSource p hp hcop hg F Ψ m c d z
      (s.filter (SecondSourceSupport p X M))
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y := by
  classical
  unfold secondExpansionSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p X M x
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hz := secondExpansionSource_singleton_zero_of_not_support
      p hp hcop hg hinj F Ψ m c d z g W X Y M hX hgM x (hE x hx) hs
    simpa only [secondExpansionSource, Finset.sum_singleton] using hz

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def normLogBin (u : ℝ) : ℕ := ⌊Real.log u⌋₊
def normLogScale (j : ℕ) : ℝ := Real.exp (j : ℝ)

lemma normLogScale_pos (j : ℕ) : 0 < normLogScale j := Real.exp_pos _
lemma normLogScale_ge_one (j : ℕ) : 1 ≤ normLogScale j :=
  Real.one_le_exp (by positivity)

lemma normLogBin_error (u : ℝ) (hu : 1 ≤ u) :
    0 ≤ Real.log (u / normLogScale (normLogBin u)) ∧
      Real.log (u / normLogScale (normLogBin u)) ≤ 1 := by
  rw [Real.log_div (by linarith) (normLogScale_pos _).ne', normLogScale, Real.log_exp]
  exact ⟨sub_nonneg.mpr (Nat.floor_le (Real.log_nonneg hu)),
    by have h := Nat.lt_floor_add_one (Real.log u); dsimp [normLogBin]; linarith⟩

lemma normLogBin_scale_bounds (u : ℝ) (hu : 1 ≤ u) :
    normLogScale (normLogBin u) ≤ u ∧
      u ≤ normLogScale (normLogBin u) * Real.exp 1 := by
  have hu0 : 0 < u := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg hu))
    simpa only [Real.exp_log hu0, normLogScale, normLogBin] using h
  · have h := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log u)).le
    simpa only [Real.exp_log hu0, Real.exp_add, normLogScale, normLogBin] using h

lemma normLogBin_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normLogBin u ≤ normLogBin v := Nat.floor_mono (Real.log_le_log hu huv)

abbrev SecondLogIndex := ℕ × ℕ × ℕ

def secondLogE (j : SecondLogIndex) : ℝ := normLogScale j.1
def secondLogV (j : SecondLogIndex) : ℝ := normLogScale j.2.1
def secondLogK (j : SecondLogIndex) : ℝ := normLogScale j.2.2

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogIndex (D : Finset ι) (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor), normLogBin (primeProductNorm p x.overlap),
    normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2))

def secondLogX (R : Finset ι) (X : ℝ) (j : SecondLogIndex) : ℝ :=
  X / (secondLogE j * secondLogV j * primeProductNorm p R)

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogX_pos (R : Finset ι) (X : ℝ) (hX : 0 < X) (j : SecondLogIndex) :
    0 < secondLogX p R X j := by
  exact div_pos hX (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp R))

omit [DecidableEq ι] in
lemma actualSecondRow_ne_zero (D E : Finset ι) (k : O) (hk : k ≠ 0) :
    actualSecondRow p D E k ≠ 0 :=
  mul_ne_zero (mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)) hk

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

include hp in

omit [DecidableEq ι] in
theorem secondLogIndex_coordinates (C D R : Finset ι) (X : ℝ) (hX : 0 < X)
    (x : SecondExpansionData ι) (hk : x.frequency ≠ 0) :
    let j := secondLogIndex p D x
    let y := expansionSupportData C D x
    |secondSectorZ p (secondExpansionScale p X
      (primeSubsetGenerator (fun i => Ideal.span {p i}) R) y) (secondLogX p R X j) y| ≤ 2 ∧
    |secondSectorUd p (primeProductNorm p D) y| ≤ 2 ∧
    |secondSectorUe p (secondLogE j) y| ≤ 2 ∧
    |secondSectorUv p (secondLogV j) y| ≤ 2 ∧
    |secondSectorKap p (secondLogK j) y| ≤ 2 := by
  dsimp only
  have hE := normLogBin_error (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)
  have hV := normLogBin_error (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)
  have hK := normLogBin_error (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)
    (element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk))
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hX0 := hX.ne'
  have hNE := (FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor).ne'
  have he := (normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hv := (normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hratio :
      primeProductNorm p x.overlap * secondLogX p R X (secondLogIndex p D x) /
        secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (expansionSupportData C D x) =
      (primeProductNorm p x.divisor / normLogScale (normLogBin (primeProductNorm p x.divisor))) *
        (primeProductNorm p x.overlap / normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [secondLogX, secondExpansionScale, expansionSupportData, secondLogIndex,
      secondLogE, secondLogV, primeSubsetGenerator_norm_eq_productNorm]
    field_simp

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change |Real.log (primeProductNorm p x.overlap * _ / _)| ≤ 2
    rw [hratio, Real.log_mul (div_ne_zero hNE he)
      (div_ne_zero (FirstPassCubeLabels.primeProductNorm_pos p hp x.overlap).ne' hv)]
    rw [abs_of_nonneg (add_nonneg hE.1 hV.1)]
    linarith [hE.2,hV.2]
  · simp only [secondSectorUd, expansionSupportData, primeSubsetGenerator_norm_eq_productNorm,
      div_self (FirstPassCubeLabels.primeProductNorm_pos p hp D).ne', Real.log_one, abs_zero]
    norm_num
  · change |Real.log (‖eisEmbedding _‖^2 / _)| ≤ 2
    rw [primeSubsetGenerator_norm_eq_productNorm]
    change |Real.log (primeProductNorm p x.divisor / normLogScale (normLogBin (primeProductNorm p x.divisor)))| ≤ 2
    rw [abs_of_nonneg hE.1]
    linarith [hE.2]
  · change |Real.log (primeProductNorm p x.overlap / normLogScale (normLogBin (primeProductNorm p x.overlap)))| ≤ 2
    rw [abs_of_nonneg hV.1]
    linarith [hV.2]
  · change |Real.log (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 /
      normLogScale (normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)))| ≤ 2
    rw [abs_of_nonneg hK.1]
    linarith [hK.2]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_radial_scale (D R : Finset ι) (X Y : ℝ) (hX : X ≠ 0) (j : SecondLogIndex) :
    Y * secondLogK j / (primeProductNorm p D * (secondLogE j)^2 *
      (secondLogV j)^2 * (secondLogX p R X j)^2) =
    Y * secondLogK j * (primeProductNorm p R)^2 / (primeProductNorm p D * X^2) := by
  unfold secondLogX secondLogE secondLogV secondLogK normLogScale
  field_simp

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondBaseLabel (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂

include hp in
omit [DecidableEq ι] in
lemma secondBaseLabel_ne_zero (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    secondBaseLabel p B C v₁ v₂ ε₁ ε₂ ≠ 0 := by
  apply mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ (hp i)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportNewLabel_norm (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) :
    (Ideal.absNorm (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x)) : ℝ) =
      ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 *
        primeProductNorm p x.divisor * primeProductNorm p x.overlap := by
  rw [← secondSupportLabel_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [secondSupportLabel, expansionSupportData, secondBaseLabel,
    map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm, primeProductNorm]

include hp in
omit [DecidableEq ι] in
lemma secondSupportNewLabel_ne_bot (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) :
    secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x) ≠ ⊥ := by
  rw [← secondSupportLabel_span, ne_eq, Ideal.span_singleton_eq_bot]
  exact mul_ne_zero (mul_ne_zero (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂)
    (primeSubsetGenerator_ne_zero _ _)) (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

def secondLogLabelBound (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (j : SecondLogIndex) : ℝ :=
  ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 * secondLogE j * secondLogV j * Real.exp 2

include hp in
omit [DecidableEq ι] in
lemma secondLogLabelBound_ge_one (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (j : SecondLogIndex) : 1 ≤ secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))
        (normLogScale_ge_one _)) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))

include hp in

omit [DecidableEq ι] in
theorem secondLogIndex_target_bounds (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) (hk : x.frequency ≠ 0) :
    (Ideal.absNorm (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x)) : ℝ) ≤
        secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ (secondLogIndex p D x) ∧
    ‖eisEmbedding (secondSupportRow p (expansionSupportData C D x))‖^2 ≤
        secondLogK (secondLogIndex p D x) * Real.exp 1 := by
  have hE := (normLogBin_scale_bounds (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)).2
  have hV := (normLogBin_scale_bounds (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)).2
  have hK := (normLogBin_scale_bounds (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)
    (element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk))).2
  refine ⟨?_, hK⟩
  rw [secondSupportNewLabel_norm]
  calc
    _ ≤ ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 *
        (normLogScale (normLogBin (primeProductNorm p x.divisor))*Real.exp 1) *
        (normLogScale (normLogBin (primeProductNorm p x.overlap))*Real.exp 1) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hE (sq_nonneg _)) hV
        (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
        (mul_nonneg (sq_nonneg _) (mul_pos (normLogScale_pos _) (Real.exp_pos _)).le)
    _ = _ := by
      simp only [secondLogLabelBound, secondLogIndex, secondLogE, secondLogV]
      rw [show (2:ℝ)=1+1 by norm_num, Real.exp_add]
      ring

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_label_cost (B C R : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (X : ℝ) (j : SecondLogIndex) :
    secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j =
      X * ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 * Real.exp 2 /
        primeProductNorm p R := by
  unfold secondLogX secondLogLabelBound secondLogE secondLogV normLogScale
  field_simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def secondLogBinBox (U K : ℝ) : Finset SecondLogIndex :=
  Finset.range (normLogBin U + 1) ×ˢ
    (Finset.range (normLogBin U + 1) ×ˢ Finset.range (normLogBin K + 1))

lemma secondLogBinBox_card (U K : ℝ) :
    (secondLogBinBox U K).card = (normLogBin U + 1)^2 * (normLogBin K + 1) := by
  simp only [secondLogBinBox, Finset.card_product, Finset.card_range]
  ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSourceSupport_bounds (X M : ℝ) (x : SecondExpansionData ι)
    (hx : SecondSourceSupport p X M x) (hE : x.divisor ⊆ x.sourceCommon) :
    primeProductNorm p x.sourceCommon ≤ X*Real.exp M ∧
    primeProductNorm p x.divisor ≤ X*Real.exp M ∧
    primeProductNorm p x.overlap ≤ X*Real.exp M := by
  have hG := (le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (primeProductNorm_ge_one p hp x.overlap)).trans hx.2
  have hV := (le_mul_of_one_le_left (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (primeProductNorm_ge_one p hp x.sourceCommon)).trans hx.2
  exact ⟨hG, (primeProductNorm_mono p hp hE).trans hG, hV⟩

include hp in
lemma secondLogIndex_mem_box (D : Finset ι) (X M K : ℝ) (x : SecondExpansionData ι)
    (hx : SecondSourceSupport p X M x) (hE : x.divisor ⊆ x.sourceCommon)
    (hk : x.frequency ≠ 0)
    (hK : ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ K) :
    secondLogIndex p D x ∈ secondLogBinBox (X*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩ := secondSourceSupport_bounds p hp X M x hx hE
  simp only [secondLogBinBox, secondLogIndex, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hE',
    normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hV,
    normLogBin_mono (by have h := element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk); linarith) hK⟩

def secondSupportedSector (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) : Finset (SecondExpansionData ι) :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (SecondSourceSupport p X M)

def secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) : Finset (SecondExpansionData ι) :=
  (secondSupportedSector p F K R X M).filter (fun x => secondLogIndex p D x = j)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_mem (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F K R X M) :
    x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
      x.frequency ≠ 0 ∧ x.frequency ∈ K x.sourceCommon x.divisor ∧
      x.sourceCommon \ x.divisor = R ∧ SecondSourceSupport p X M x := by
  obtain ⟨hx,hs⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hr⟩ := Finset.mem_filter.mp hx
  obtain ⟨hG,hE,hV,hk⟩ := (mem_secondExpansionPool _ _ _).mp hx
  obtain ⟨hk0,hk⟩ := Finset.mem_erase.mp hk
  exact ⟨hG,hE,hV,hk0,hk,hr,hs⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogSector_subset (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    secondLogSector p D F K R X M j ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

include hp in

theorem sum_secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M Kmax : ℝ)
    (hK : ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax)
    (H : SecondExpansionData ι → ℂ) :
    (∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
      ∑ x ∈ secondLogSector p D F K R X M j, H x) =
      ∑ x ∈ secondSupportedSector p F K R X M, H x := by
  simp only [secondLogSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have hj := secondLogIndex_mem_box p hp D X M Kmax x hs hE hk0 (hK x hx)
  rw [Finset.sum_eq_single_of_mem (secondLogIndex p D x) hj]
  · simp
  · intro j hj hne
    simp [Ne.symm hne]

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_lower (D F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hX : 0 < X) (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F K R X M) :
    Real.exp (-M) ≤ secondLogX p R X (secondLogIndex p D x) := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have he := (normLogBin_scale_bounds (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)).1
  have hv := (normLogBin_scale_bounds (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)).1
  have hGR : primeProductNorm p x.sourceCommon = primeProductNorm p x.divisor * primeProductNorm p R := by
    rw [← hr, ← FirstPassCubeLabels.primeProductNorm_union p x.divisor (x.sourceCommon\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hE]
  have hprod : secondLogE (secondLogIndex p D x) * secondLogV (secondLogIndex p D x) * primeProductNorm p R ≤ X*Real.exp M := by
    calc
      _ ≤ primeProductNorm p x.divisor * primeProductNorm p x.overlap * primeProductNorm p R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul he hv (normLogScale_pos _).le
          (FirstPassCubeLabels.primeProductNorm_pos p hp _).le)
          (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
      _ = primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap := by rw [hGR]; ring
      _ ≤ _ := hs.2
  unfold secondLogX
  apply (le_div_iff₀ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp R))).mpr
  calc
    _ ≤ Real.exp (-M) * (X*Real.exp M) := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = X := by rw [Real.exp_neg]; field_simp

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.LogarithmicTargets -/

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
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogTargets (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    Finset (Ideal O × O) :=
  (secondLogSector p D F K R X M j).image (fun x =>
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogTargets_mem (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (x : SecondExpansionData ι) (hx : x ∈ secondLogSector p D F K R X M j) :
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)) ∈
      secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp in
lemma secondLogTargets_bounds (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (q : Ideal O × O) (hq : q ∈ secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    q.1 ≠ ⊥ ∧ (Ideal.absNorm q.1 : ℝ) ≤ secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j ∧
      q.2 ≠ 0 ∧ ‖eisEmbedding q.2‖^2 ≤ secondLogK j * Real.exp 1 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hx,hj⟩ := Finset.mem_filter.mp hx
  have hs := secondSupportedSector_mem p F K R X M x hx
  have hb := secondLogIndex_target_bounds p hp B C D v₁ v₂ ε₁ ε₂ x hs.2.2.2.1
  rw [hj] at hb
  exact ⟨secondSupportNewLabel_ne_bot p hp B C D v₁ v₂ ε₁ ε₂ x, hb.1,
    actualSecondRow_ne_zero p D x.divisor x.frequency hs.2.2.2.1, hb.2⟩

include hp in
lemma secondLogSector_coordinates (C D F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hX : 0 < X) (j : SecondLogIndex) (x : SecondExpansionData ι)
    (hx : x ∈ secondLogSector p D F K R X M j) :
    let y := expansionSupportData C D x
    |secondSectorZ p (secondExpansionScale p X
      (primeSubsetGenerator (fun i => Ideal.span {p i}) R) y) (secondLogX p R X j) y| ≤ 2 ∧
    |secondSectorUd p (primeProductNorm p D) y| ≤ 2 ∧
    |secondSectorUe p (secondLogE j) y| ≤ 2 ∧
    |secondSectorUv p (secondLogV j) y| ≤ 2 ∧
    |secondSectorKap p (secondLogK j) y| ≤ 2 := by
  obtain ⟨hx,hj⟩ := Finset.mem_filter.mp hx
  have hs := secondSupportedSector_mem p F K R X M x hx
  have h := secondLogIndex_coordinates p hp C D R X hX x hs.2.2.2.1
  dsimp only at h
  rw [hj] at h
  exact h

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_remainder_bound (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (x : SecondExpansionData ι) (hx : x ∈ secondSupportedSector p F K R X M) :
    primeProductNorm p R ≤ X*Real.exp M := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have h := (secondSourceSupport_bounds p hp X M x hs hE).1
  rw [← hr]
  exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans h

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_eq_empty (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hR : ¬ primeProductNorm p R ≤ X*Real.exp M) :
    secondSupportedSector p F K R X M = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hR (secondSupportedSector_remainder_bound p hp F R K X M x hx)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem truncatedSecondSource_eq_binned
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (D F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g W : 𝓢(ℝ,ℂ))
    (X Y M Kmax : ℝ) (hX : 0 < X) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) :
    let H := fun S => normalizedColumn p (fun A => g (columnLog p X A)) S
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondZero p hg F Ψ m c d H W Y K +
        ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
          ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            secondExpansionSource p hp hcop hg F Ψ m c d z
              (secondLogSector p D F K R X M j) H H W Y := by
  dsimp only
  rw [truncatedSecondSource_eq_nonzero_add_zero, add_comm,
    truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  simp only [boundedPrimeSupports, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro R hR
  have hE : ∀ x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R,
      x.divisor ⊆ x.sourceCommon := by
    intro x hx
    exact ((mem_secondExpansionPool _ _ _).mp (Finset.mem_filter.mp hx).1).2.1
  have hs := secondExpansionSource_eq_supported p hp hcop hg hinj F Ψ m c d z
    g W X Y M hX hgM (secondExpansionSector F (fun G E => (K G E).erase 0) R) hE
  rw [hs]
  change secondExpansionSource p hp hcop hg F Ψ m c d z (secondSupportedSector p F K R X M)
      _ _ W Y = _
  by_cases hNR : primeProductNorm p R ≤ X*Real.exp M
  · rw [ite_eq_left hNR]
    simp only [secondExpansionSource]
    exact (sum_secondLogSector p hp D F K R X M Kmax (hK R hR) _).symm
  · rw [ite_eq_right hNR, secondSupportedSector_eq_empty p hp F R K X M hNR]
    simp only [secondExpansionSource, Finset.sum_empty]

include hinj in
theorem truncatedSecondSource_norm_le_binned
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (D F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g W : 𝓢(ℝ,ℂ))
    (X Y M Kmax : ℝ) (hX : 0 < X) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) :
    let H := fun S => normalizedColumn p (fun A => g (columnLog p X A)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K‖ ≤
      ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ +
        ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
          ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            ‖secondExpansionSource p hp hcop hg F Ψ m c d z
              (secondLogSector p D F K R X M j) H H W Y‖ := by
  dsimp only
  rw [truncatedSecondSource_eq_binned p hp hcop hg hinj hc hpr D F Ψ m c d g W X Y M Kmax hX hgM K hK]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact le_rfl
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro z hz
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro R hR
    exact norm_sum_le _ _

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

lemma supported_cutoff_denominator (E G U : ℝ) (hE : E ≤ G) (hG : 1 ≤ G) :
    E * (U/G)^2 ≤ U^2 := by
  have hG0 : 0 < G := by linarith
  have hEG : E ≤ G^2 := by nlinarith
  have he : E/G^2 ≤ 1 := (div_le_one (sq_pos_of_pos hG0)).mpr hEG
  calc
    E*(U/G)^2 = U^2*(E/G^2) := by ring
    _ ≤ U^2*1 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := mul_one _

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def firstCoreSecondRowBound (D A : Finset ι) (X Y M Z : ℝ) : ℝ :=
  3 * primeProductNorm p D * ((X/primeProductNorm p A)*Real.exp M) *
    ((⌈Z*(((X/primeProductNorm p A)*Real.exp M)^2)/Y⌉₊ : ℝ)+1)^2

include hp in

theorem firstCoreSecondCutoff_supported_row_bound
    (D A F R : Finset ι) (X Y M Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 ≤ Z)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F (firstCoreSecondCutoff p A X Y M Z) R
      (X/primeProductNorm p A) M) :
    ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤
      firstCoreSecondRowBound p D A X Y M Z := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F
    (firstCoreSecondCutoff p A X Y M Z) R (X/primeProductNorm p A) M x hx
  let U := (X/primeProductNorm p A)*Real.exp M
  have hU : 0 < U := mul_pos (div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A)) (Real.exp_pos _)
  have hNE := FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor
  have hNG := FirstPassCubeLabels.primeProductNorm_pos p hp x.sourceCommon
  have hEupper : primeProductNorm p x.divisor ≤ U :=
    (secondSourceSupport_bounds p hp _ M x hs hE).2.1
  have hden : primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2 ≤ U^2 := by
    rw [show ((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M =
      U/primeProductNorm p x.sourceCommon by dsimp [U]; ring]
    exact supported_cutoff_denominator _ _ _ (primeProductNorm_mono p hp hE) (primeProductNorm_ge_one p hp _)
  have hdenpos : 0 < primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2 := by
    exact mul_pos hNE (sq_pos_of_pos (mul_pos (div_pos (div_pos hX
      (FirstPassCubeLabels.primeProductNorm_pos p hp A)) hNG) (Real.exp_pos _)))
  have hratio : Z / (Y / (primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2)) ≤ Z*U^2/Y := by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hZ) hY.le
  have hceil : (⌈Z / (Y / (primeProductNorm p x.divisor *
      (((X/primeProductNorm p A)/primeProductNorm p x.sourceCommon)*Real.exp M)^2))⌉₊ : ℝ) ≤
      (⌈Z*U^2/Y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hratio
  have hkbound := secondFrequencyCutoff_norm_sq_le _ Z x.frequency hk
  simp only [ primeSubsetGenerator_norm_eq_productNorm] at hkbound
  have hkbound' : ‖eisEmbedding x.frequency‖^2 ≤ 3*((⌈Z*U^2/Y⌉₊ : ℝ)+1)^2 := by
    apply hkbound.trans
    gcongr
  have hrow : ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 =
      primeProductNorm p D * primeProductNorm p x.divisor * ‖eisEmbedding x.frequency‖^2 := by
    simp only [actualSecondRow, map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm]
  rw [hrow]
  calc
    _ ≤ (primeProductNorm p D * U) * (3*((⌈Z*U^2/Y⌉₊ : ℝ)+1)^2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hEupper (FirstPassCubeLabels.primeProductNorm_pos p hp D).le)
        hkbound' (sq_nonneg _) (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp D) hU).le
    _ = firstCoreSecondRowBound p D A X Y M Z := by unfold firstCoreSecondRowBound; dsimp [U]; ring

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm jLabel b0Label)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (densityChildEnergy)

theorem normalized_binned_second_density_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (Y : ℝ), 0 < Y → ∀ θ : ℝ,
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X Kmax : ℝ) (K : Finset ι → Finset ι → Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X →
        (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
          ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) →
        let c := secondBaseLabel p B C v₁ v₂ ε₁ ε₂
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Hcol := fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S
        ‖truncatedSecondSource p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
          |Y| * ‖paperRadialFourier W 0‖ *
            (∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d
              (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖^2) +
          ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
            ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            (Y * primeProductNorm p R / X^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
              (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
            (Cₛ*(1+‖θ‖)^(J+2)*(1+‖θ‖)^(J+2) /
              (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X^2))^decayOrder) *
            densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
              (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
              (windows 5) (windows 6) (secondLogX p R X j) (secondLogX p R X j) J := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hbound⟩ :=
    normalized_twisted_second_sector_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g g W hU hU M 2 hM (by norm_num) hgM hgM ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro Y hY θ B C D F v₁ v₂ ε₁ ε₂ Ψ m X Kmax K hv hCB hD hΨ hX hzero hK
  dsimp only
  have hθ : ∀ t, (frequencyTwist g θ) t ≠ 0 → |t| ≤ M := by
    intro t ht
    exact hgM t (fun hz => ht (by simp only [frequencyTwist_apply,hz,mul_zero]))
  apply (truncatedSecondSource_norm_le_binned p hp hcop hg hinj hc hpr D F Ψ m
    (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
    (frequencyTwist g θ) W X Y M Kmax hX hθ K hK).trans
  apply add_le_add
  · have hd := truncatedSecondZero_norm_le p hg hinj F Ψ m
      (secondBaseLabel p B C v₁ v₂ ε₁ ε₂) (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) W Y K hzero
    simpa only [secondInputCoefficient_frequencyTwist_norm] using hd
  · apply Finset.sum_le_sum
    intro z hz
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    have hcoord := secondLogSector_coordinates p hp C D F R K X M hX j
    have hb := hbound (primeProductNorm p D) (secondLogE j) (secondLogV j)
      (secondLogX p R X j) (secondLogK j) Y
      (FirstPassCubeLabels.primeProductNorm_pos p hp D)
      (normLogScale_pos _) (normLogScale_pos _) (secondLogX_pos p hp R X hX j)
      (normLogScale_pos _) hY θ θ B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondLogSector p D F K R X M j) (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      X (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)
      (secondLogSector_subset p D F K R X M j) hv hCB hD hΨ hX
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))
      (fun x hx => (hcoord x hx).1) (fun x hx => (hcoord x hx).2.1)
      (fun x hx => (hcoord x hx).2.2.1) (fun x hx => (hcoord x hx).2.2.2.1)
      (fun x hx => (hcoord x hx).2.2.2.2)
      (secondLogTargets_mem p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      (fun q hq => (secondLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).1)
      (fun q hq => (secondLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).2.1)
    simpa only [secondBaseLabel, primeSubsetGenerator_norm_eq_productNorm,
      secondLogX_radial_scale p D R X Y hX.ne' j] using hb

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_binned_finite_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z t : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Usupp := X' * Real.exp M
        let K := firstCoreSecondCutoff p A₀ X Y M Z
        let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2) +
          ‖firstCoreTest (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X)
            negative t A₀ ∅‖^2 ≤
        (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
            (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
              ∑ j ∈ secondLogBinBox Usupp Kmax,
              (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                  Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
                (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
                (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  have hUbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU s
    intro hz
    exact hs (by simp only [firstCoreBaseProfile_apply,hz,zero_mul])
  have hMbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → |s| ≤ M := by
    intro s hs
    apply hgM s
    intro hz
    exact hs (by simp only [firstCoreBaseProfile_apply,hz,zero_mul])
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_binned_second_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      (firstCoreBaseProfile g V negative) rowMajorant hUbase M hM hMbase ε hε decayOrder J
  obtain ⟨Ctail,hCtail,htail⟩ :=
    firstCoreSecondCutoff_tail_fixed_source p hp hg hinj hc tailOrder g V rowMajorant negative
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  dsimp only
  have hX' : 0 < X / primeProductNorm p A₀ :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A₀)
  have hΨ' : ∀ a : O, ‖firstCoreTwist negative χ Ψ r₁ a‖ ≤ 1 :=
    fun a => (firstCoreTwist_norm_le negative χ Ψ r₁ a).trans (hΨ a)
  have hb := htrans Y hY (firstCoreModeHeight negative t) B C D (F\A₀)
    v₁ v₂ ε₁ ε₂ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂) (X / primeProductNorm p A₀)
    (firstCoreSecondRowBound p D A₀ X Y M Z) (firstCoreSecondCutoff p A₀ X Y M Z)
    hv hCB hD hΨ' hX'
    (fun G hG E hE => firstCoreSecondCutoff_zero p A₀ X Y M Z G E)
    (fun R hR x hx => firstCoreSecondCutoff_supported_row_bound p hp D A₀ (F\A₀) R
      X Y M Z hX hY hZ x hx)
  simp only [firstCoreModeHeight_norm, secondBaseLabel] at hb
  have ht := htail F A₀ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) t X Y M Z hΨ' hX hY hZ hgM
  have hf := firstCoreInputRow_finite_le_truncated_tail p hp hg hinj hc F A₀ B
    (fun i => v₁ i+v₂ i) ε₁ ε₂ negative χ Ψ m g V X hX Y hY
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) r₁ t Srows hSrows hSrows0
    (firstCoreSecondCutoff p A₀ X Y M Z)
  simp only [firstCoreModeProfile] at hf ht ⊢
  apply hf.trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add
    · exact hb
    · exact ht
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

@[fun_prop] lemma quadraticHeightDenominator_continuous (A B C D : ℝ) :
    Continuous (fun p : SpatialCoordinates => quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)) := by
  unfold quadraticHeightDenominator
  fun_prop

lemma rowSmoothPower_continuousAt (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) : ContinuousAt (rowSmoothPower s u) p := by
  have hq := row_denominator_pos u hu p hv
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  have hlog := (hvc.log hv.ne').sub
    ((quadraticHeightDenominator_continuous (Complex.normSq (u 0))
      (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt.log hq.ne')
  exact Complex.continuous_exp.continuousAt.comp
    ((Complex.continuous_ofReal.continuousAt.comp hlog).const_mul s)

lemma rowLogD_continuousAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ContinuousAt (fun q => rowLogD u q j) p := by
  have hq := row_denominator_pos u hu p hv
  have hvn := hv.ne'
  have hqn := hq.ne'
  have hvn2 := pow_ne_zero 2 hvn
  have hqn2 := pow_ne_zero 2 hqn
  have hqc := (quadraticHeightDenominator_continuous (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt (x := p)
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  fin_cases j
  · dsimp [rowLogD,spatialLogD,heightLogDx]
    fun_prop (disch := aesop)
  · dsimp [rowLogD,spatialLogD,heightLogDy]
    fun_prop (disch := aesop)
  · exact (continuousAt_const.div hvc hvn).sub
      ((hvc.const_mul (2*Complex.normSq (u 0))).div hqc hqn)

lemma rowLogDD_continuousAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ContinuousAt (fun q => rowLogDD u q j) p := by
  have hq := row_denominator_pos u hu p hv
  have hvn := hv.ne'
  have hqn := hq.ne'
  have hvn2 := pow_ne_zero 2 hvn
  have hqn2 := pow_ne_zero 2 hqn
  have hqc := (quadraticHeightDenominator_continuous (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1))).continuousAt (x := p)
  have hvc : ContinuousAt (fun q : SpatialCoordinates => q 2) p := (continuous_apply 2).continuousAt
  fin_cases j
  · dsimp [rowLogDD,spatialLogDD,heightLogDxx]
    fun_prop (disch := aesop)
  · dsimp [rowLogDD,spatialLogDD,heightLogDyy]
    fun_prop (disch := aesop)
  · exact (continuousAt_const.div (hvc.pow 2) hvn2).neg.sub
      (((hqc.const_mul (2*Complex.normSq (u 0))).sub
        ((hvc.const_mul (2*Complex.normSq (u 0))).mul
          (hvc.const_mul (2*Complex.normSq (u 0))))).div (hqc.pow 2) hqn2)

def smoothFirstCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*s*(rowLogD (embeddedRow r) p j:ℂ)
def smoothSecondCoefficient (s : ℂ) (r : CuspCosets) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  smoothSummand s r p*(s^2*(rowLogD (embeddedRow r) p j:ℂ)^2+s*(rowLogDD (embeddedRow r) p j:ℂ))

lemma smoothFirstCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothFirstCoefficient s r j p=deriv (axisSlice (smoothSummand s r) p j) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothFirstCoefficient smoothSummand
  ring

lemma smoothSecondCoefficient_eq_deriv (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSecondCoefficient s r j p=deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  unfold axisSlice smoothSummand
  rw [deriv_const_mul_field',deriv_const_mul_field]
  have hd := (row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).deriv
  unfold axisSlice at hd
  rw [hd]
  unfold smoothSecondCoefficient smoothSummand
  ring

lemma smoothCoefficients_continuousAt (s : ℂ) (r : CuspCosets) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ContinuousAt (smoothFirstCoefficient s r j) p ∧ ContinuousAt (smoothSecondCoefficient s r j) p := by
  have hF : ContinuousAt (smoothSummand s r) p :=
    (rowSmoothPower_continuousAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv).const_mul _
  have hD := Complex.continuous_ofReal.continuousAt.comp
    (rowLogD_continuousAt (embeddedRow r) (embeddedRow_ne_zero r) p hv j)
  have hDD := Complex.continuous_ofReal.continuousAt.comp
    (rowLogDD_continuousAt (embeddedRow r) (embeddedRow_ne_zero r) p hv j)
  exact ⟨(hF.mul_const s).mul hD,hF.mul ((hD.pow 2).const_mul (s^2) |>.add (hDD.const_mul s))⟩

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma spatial_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ∃ U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧
      ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀q∈U, 0<q 2 ∧ ∀r : CuspCosets,
        ‖smoothSummand s r q‖≤M₀ r ∧ ∀j : Fin 3,
        ‖smoothFirstCoefficient s r j q‖≤M₁ r ∧
        ‖smoothSecondCoefficient s r j q‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := clampedCoordinates deltaLoss hδ
  let C := rowBound (coordinateSection (path p))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path p))]
  let U : Set SpatialCoordinates := {q | deltaLoss<q 2 ∧ rowBound (coordinateSection (path q))<C}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 2)).inter
    (isOpen_lt (continuous_coordinate_rowBound.comp (continuous_clampedCoordinates deltaLoss hδ)) continuous_const)
  have hpU : p∈U := by constructor <;> dsimp [deltaLoss,C] <;> linarith
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨U,hU,hpU,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro q hq
  have hpos : 0<q 2 := lt_trans hδ hq.1
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r q‖≤M r := by
    rw [smoothSummand_eq_clamped s r q deltaLoss hδ hq.1.le]
    exact hbound (path q,s) hq.2.le le_rfl le_rfl r
  have hfrac : 1 / q 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hq.1.le
  have hfrac₂ : 7 / (q 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith [hq.1]
  refine ⟨hm,fun j => ?_⟩
  rw [smoothFirstCoefficient_eq_deriv _ _ _ _ hpos,smoothSecondCoefficient_eq_deriv _ _ _ _ hpos]
  constructor
  · apply (norm_smooth_axis_deriv s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply (norm_smooth_axis_deriv2 s r q hpos j).trans
    apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

def eisensteinFirstPartial (s : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  deriv (axisSlice (upperEisensteinField s) p j) (p j)

def eisensteinSecondPartial (s : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  deriv (deriv (axisSlice (upperEisensteinField s) p j)) (p j)

lemma eisensteinPartials_eq_tsum (s : ℂ) (hs : 2<s.re) (j : Fin 3)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    eisensteinFirstPartial s j p=(∑'r,smoothFirstCoefficient s r j p) ∧
    eisensteinSecondPartial s j p=(∑'r,smoothSecondCoefficient s r j p) := by
  have ht := eisenstein_axis_termwise s hs p hv j
  have heq := axisSlice_eventuallyEq_of_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) p hv j
  constructor
  · unfold eisensteinFirstPartial
    rw [heq.deriv_eq,ht.2.2.1.deriv]
    exact tsum_congr (fun r => (smoothFirstCoefficient_eq_deriv _ _ _ _ hv).symm)
  · unfold eisensteinSecondPartial
    rw [heq.deriv.deriv_eq,ht.2.2.2.deriv]
    exact tsum_congr (fun r => (smoothSecondCoefficient_eq_deriv _ _ _ _ hv).symm)

lemma actual_spatial_continuousAt (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    ContinuousAt (upperEisensteinField s) p ∧ ∀j : Fin 3,
    ContinuousAt (eisensteinFirstPartial s j) p ∧
    ContinuousAt (eisensteinSecondPartial s j) p := by
  obtain ⟨U,hU,hpU,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := spatial_summable_derivative_bounds s hs p hv
  have hf (r : CuspCosets) : ContinuousOn (smoothSummand s r) U := by
    intro q hq
    exact ((rowSmoothPower_continuousAt s (embeddedRow r) (embeddedRow_ne_zero r) q
      (hbound q hq).1).const_mul _).continuousWithinAt
  have hsum := continuousOn_tsum hf hM₀ (fun r q hq => ((hbound q hq).2 r).1)
  have heq : (upperEisensteinField s) =ᶠ[𝓝 p] smoothEisenstein s := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact upperEisensteinField_eq_smooth s q (hbound q hq).1
  refine ⟨(hsum.continuousAt (hU.mem_nhds hpU)).congr heq.symm,fun j => ?_⟩
  have hc₁ (r : CuspCosets) : ContinuousOn (smoothFirstCoefficient s r j) U := by
    intro q hq
    exact ((smoothCoefficients_continuousAt s r j q (hbound q hq).1).1).continuousWithinAt
  have hc₂ (r : CuspCosets) : ContinuousOn (smoothSecondCoefficient s r j) U := by
    intro q hq
    exact ((smoothCoefficients_continuousAt s r j q (hbound q hq).1).2).continuousWithinAt
  have hsum₁ := continuousOn_tsum hc₁ hM₁ (fun r q hq => (((hbound q hq).2 r).2 j).1)
  have hsum₂ := continuousOn_tsum hc₂ hM₂ (fun r q hq => (((hbound q hq).2 r).2 j).2)
  have heq₁ : eisensteinFirstPartial s j =ᶠ[𝓝 p] (fun q => ∑'r,smoothFirstCoefficient s r j q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (eisensteinPartials_eq_tsum s hs j q (hbound q hq).1).1
  have heq₂ : eisensteinSecondPartial s j =ᶠ[𝓝 p] (fun q => ∑'r,smoothSecondCoefficient s r j q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    exact (eisensteinPartials_eq_tsum s hs j q (hbound q hq).1).2
  exact ⟨(hsum₁.continuousAt (hU.mem_nhds hpU)).congr heq₁.symm,
    (hsum₂.continuousAt (hU.mem_nhds hpU)).congr heq₂.symm⟩

end CubicEisenstein

end

end OAI

end

