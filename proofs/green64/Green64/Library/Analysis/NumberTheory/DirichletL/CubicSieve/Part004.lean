module

public import Green64.Library.OAI.NumberTheory.DirichletL.CubicSieve.RayCoefficients

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.SecondPoisson -/

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

section

open scoped BigOperators Classical SchwartzMap ContDiff
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (activeGaussRowFactor)

theorem masked_pair_second_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S T : Finset ι) (hd : Disjoint S T)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let n := ∏ i : activeSupport T S, p i.val
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S z) *
      W (‖eisEmbedding z‖ ^ 2 / Y)) =
    ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding e‖ ^ 2 : ℝ)) *
          ∑' k : O, paperRadialFourier W
            (Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
              activeGaussRowFactor p hp hinj hg T S e k := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let Q := activePrimes P T S
  let q : activeSupport T S → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime P hinj T S
  let j := activeExponent T S
  let row := finiteSexticRow Q (fun i => hg i.val) j
  let n := ∏ i, q i
  have hr (z : O) : star (finiteSquarefreeRow P hg T z) * finiteSquarefreeRow P hg S z = row z := by
    rw [finiteSquarefreeRow_pair_activeSupport]
    simp [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask, row, Q, j]
  have h := canonical_masked_radial_poisson_collected P hinj M Q hQ
    (fun i => hg i.val) (fun i => hc i.val) j
    (activeExponent_ne_zero T S) (activeExponent_lt_six T S) W Y hY
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q
  dsimp only at h
  rw [hn] at h
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset
    (fun E => let e := primeSubsetGenerator P E
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
        (‖eisEmbedding e‖ ^ 2 : ℝ))
    (fun E t => let e := primeSubsetGenerator P E
      paperRadialFourier W (Y * t / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)))
  calc
    _ = ∑' z : O, rowCoprimeMask P M z * row z * W (‖eisEmbedding z‖ ^ 2 / Y) := by
      apply tsum_congr
      intro z
      rw [hr]
    _ = ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
          ∑ E ∈ M.powerset,
            ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row (primeSubsetGenerator P E) /
              (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 : ℝ)) *
            ∑' k : O, star (row k) * paperRadialFourier W
              (Y * ‖eisEmbedding k‖ ^ 2 /
                (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))) := by
      rw [h]
      ring
    _ = _ := by
      rw [ht]
      simp only [Finset.mul_sum, ← tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      apply tsum_congr
      intro k
      dsimp only [activeGaussRowFactor]
      ring

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (columnLog primeProductNorm firstDualScale normalizedColumn)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondGaussTerm (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) S *
    secondInputCoefficient p hg Ψ₁ (m * (e * r)) c d H₁ S) *
  (supportMobius (fun i => Ideal.span {p i}) T *
    secondInputCoefficient p hg Ψ₂ (m * (e * r)) c d H₂ T) *
    activeGaussRowFactor p hp hinj hg T S e k

def actualSecondKernel (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T)) *
    ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T
    else 0

def secondLogTest (V : ℝ → ℂ) (X t : ℝ) (negative : Bool) (S : Finset ι) : ℂ :=
  (V (columnLog p X S) *
    (if negative then star (logPhase t (-(columnLog p X S))) else logPhase t (-(columnLog p X S)))) /
      (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)

theorem secondGaussTerm_log_twist (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ t : ℝ) (S T : Finset ι) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T =
    (logPhase t (-(columnLog p X₁ S)) * logPhase t (-(columnLog p X₂ T))) *
      (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
        secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) := by
  simp only [secondGaussTerm, secondInputCoefficient, secondLogTest, normalizedColumn,
    ite_true, Bool.false_eq_true, ite_false, star_mul, star_div₀, star_star,
    one_div, star_inv₀]
  ring

theorem actualSecondKernel_eq_integral
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, star (V₁ x) * V₂ y *
      paperRadialFourier W (firstDualScale p ∅ Y X₁ X₂ e k * Real.exp (-x-y)) =
      ∫ t : ℝ, (star (V₁ x) * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false)) volume ∧
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * ∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
  let G := fun (t : ℝ) (S T : Finset ι) => if Disjoint S T then b t *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T else 0
  have hGi (S T : Finset ι) : Integrable (fun t => G t S T) volume := by
    by_cases hd : Disjoint S T
    · simp only [G, ite_eq_left hd, secondGaussTerm_log_twist]
      convert FirstPassCubeLabels.integrable_log_pair b (-(columnLog p X₁ S)) (-(columnLog p X₂ T))
        (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
            (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) using 1
    · simp only [G, ite_eq_right hd]
      exact integrable_zero _ _ _
  have hGs (t : ℝ) : (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) =
      b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
    simp only [G, secondActualPair, secondGaussTerm, Finset.mul_sum, mul_ite, mul_zero]
  have hI : Integrable (fun t => ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) volume :=
    integrable_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T))
  constructor
  · simpa only [hGs] using hI
  · rw [← integral_congr_ae (Filter.Eventually.of_forall hGs)]
    rw [integral_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T)), Finset.mul_sum]
    unfold actualSecondKernel
    apply Finset.sum_congr rfl
    intro S hS
    rw [integral_finsetSum _ (fun T _ => hGi S T), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hd : Disjoint S T
    · simp only [G, ite_eq_left hd, secondGaussTerm_log_twist]
      have harg := FirstPassCubeLabels.actual_radial_argument p hp S T ∅ hd
        (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) Y X₁ X₂ hX₁ hX₂ e k
      simp only [Finset.union_empty] at harg
      rw [← harg]
      have hn : secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T =
        ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
        simp only [secondGaussTerm, secondInputCoefficient, normalizedColumn, one_div,
          mul_one, star_mul, map_inv₀, Complex.star_def, Complex.conj_ofReal]
        ring
      rw [hn]
      rw [Finset.prod_union hd]
      simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
      have hh := congrArg (fun z : ℂ => (Y : ℂ) * z *
        ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T)
        (hsep (columnLog p X₁ S) (columnLog p X₂ T))
      rw [← integral_const_mul, ← integral_mul_const, ← integral_mul_const] at hh
      convert hh using 1
      · ring
      · rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        ring
    · simp [hd, G]

end

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildSum_continuous
    (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S)) :
    Continuous (fun t : ℝ => secondChildSum p hp hcop hg F V Ψ m r c d e k (H t)) := by
  unfold secondChildSum
  apply continuous_finsetSum
  intro N hN
  have hh := hc (V ∪ N)
  unfold secondChildColumn
  fun_prop

theorem secondChildSum_uniform_bound
    (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖secondChildSum p hp hcop hg F V Ψ m r c d e k (H t)‖ ≤ M := by
  refine ⟨∑ N ∈ (F \ V).powerset,
    ‖secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
      (fun U => H 0 (V ∪ U)) N‖, by positivity, ?_⟩
  intro t
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro N hN
  simp only [secondChildColumn, norm_mul, hn]
  exact le_rfl

theorem secondTotalEnergy_nonneg
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : Finset ι → ℂ) (negative : Bool) :
    0 ≤ secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H negative := by
  unfold secondTotalEnergy
  positivity

theorem secondTotalEnergy_continuous
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S)) (negative : Bool) :
    Continuous (fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) := by
  unfold secondTotalEnergy
  apply continuous_finsetSum
  intro z hz
  apply continuous_finsetSum
  intro V hV
  exact continuous_const.mul ((secondChildSum_continuous p hp hcop hg F V
    (if negative then secondRayMinus Ψ₁ z else secondRayPlus Ψ₂ z)
    m r c d e (if negative then k else -k) H hc).norm.pow 2)

theorem secondTotalEnergy_uniform_bound
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative ≤ M := by
  choose M hM hbound using fun (z : SecondRayIndex) (V : Finset ι) =>
    secondChildSum_uniform_bound p hp hcop hg F V
      (if negative then secondRayMinus Ψ₁ z else secondRayPlus Ψ₂ z)
      m r c d e (if negative then k else -k) H hn
  refine ⟨∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
    ‖secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V)‖ * (M z V)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro z hz
  apply Finset.sum_le_sum
  intro V hV
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hbound z V t) 2) (norm_nonneg _)

theorem secondTotalEnergy_integrable
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S))
    (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) volume := by
  obtain ⟨M, hM, hb⟩ := secondTotalEnergy_uniform_bound p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H hn negative
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H hc negative).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative)]
      exact hb t)

theorem second_integral_norm_le_energy
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => H₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => H₂ t S))
    (hn₁ : ∀ t S, ‖H₁ t S‖ = ‖H₁ 0 S‖)
    (hn₂ : ∀ t S, ‖H₂ t S‖ = ‖H₂ 0 S‖) (b : 𝓢(ℝ, ℂ)) :
    ‖∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false) := by
  let E₁ := fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true
  let E₂ := fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false
  let w := fun t : ℝ => ‖b t‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false
  have hw : ∀ t, 0 ≤ w t := fun t => norm_nonneg _
  have i₁ : Integrable (fun t => w t * E₁ t) volume :=
    secondTotalEnergy_integrable p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₁ hc₁ hn₁ true b
  have i₂ : Integrable (fun t => w t * E₂ t) volume :=
    secondTotalEnergy_integrable p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₂ hc₂ hn₂ false b
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f := Real.continuous_sqrt.comp (b.continuous.norm.mul
    (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₁ hc₁ true))
  have hg' : Continuous g := Real.continuous_sqrt.comp (b.continuous.norm.mul
    (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₂ hc₂ false))
  have hfsq (t : ℝ) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : ℝ) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : ℝ) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)‖ ≤
      ∫ t : ℝ, f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (secondActualPair_norm_le p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, w t * E₁ t) * Real.sqrt (∫ t : ℝ, w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (firstDualScale firstLogDensity primeProductNorm_pos)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogTest_continuous (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (S : Finset ι) :
    Continuous (fun t : ℝ => secondLogTest p V X t negative S) := by
  have h := FourierBridge.logPhase_continuous_left (-(FirstPassCubeLabels.columnLog p X S))
  cases negative <;> simp only [secondLogTest, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogTest_norm (V : ℝ → ℂ) (X t : ℝ) (negative : Bool) (S : Finset ι) :
    ‖secondLogTest p V X t negative S‖ = ‖secondLogTest p V X 0 negative S‖ := by
  cases negative <;> simp only [secondLogTest, Bool.false_eq_true, ite_false, ite_true,
    norm_div, norm_mul, norm_star, FourierBridge.logPhase_norm]

def secondKernelEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (b : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k
    (secondLogTest p V X t negative) negative

theorem actual_second_kernel_uniform_energy_envelope
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ x, V₂ x ≠ 0 → |x| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ e k : O, e ≠ 0 → k ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p ∅ Y X₁ X₂ e k) ^ A * ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ (Ψ₁ Ψ₂ : O →* ℂ) (m r c d : O),
          ‖actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y‖ ≤
            Y * Real.sqrt (secondKernelEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k V₁ X₁ true b) *
              Real.sqrt (secondKernelEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k V₂ X₂ false b) := by
  have hV₁' : ∀ x, star (V₁ x) ≠ 0 → |x| ≤ M₁ := by
    intro x hx
    exact hV₁ x (by intro h; simp [h] at hx)
  obtain ⟨K, hK, hs⟩ := FirstPassCubeLabels.two_variable_radial_envelope W (fun x => star (V₁ x)) V₂
    M₁ M₂ hM₁ hM₂ hV₁' hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro Y hY e k he hk
  have hR : 0 < firstDualScale p ∅ Y X₁ X₂ e k := by
    unfold firstDualScale
    exact div_pos (mul_pos hY (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hk)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro Ψ₁ Ψ₂ m r c d
  rw [(actualSecondKernel_eq_integral p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y
    hX₁ hX₂ b hsep).2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  have hi := second_integral_norm_le_energy p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ m r c d e k
    (fun t => secondLogTest p V₁ X₁ t true) (fun t => secondLogTest p V₂ X₂ t false)
    (secondLogTest_continuous p V₁ X₁ true) (secondLogTest_continuous p V₂ X₂ false)
    (fun t S => secondLogTest_norm p V₁ X₁ t true S)
    (fun t S => secondLogTest_norm p V₂ X₂ t false S) b
  change Y * _ ≤ Y * Real.sqrt _ * Real.sqrt _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi hY.le

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassFiber (OldTuple newLabel newRow Valid)

theorem second_energy_selected_family {κ : Type*} [Fintype κ] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (P : κ → Ideal O × O → ℂ) (sel : OldTuple → κ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (sel x) (newLabel x, newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : κ, ∑ z ∈ t, ‖P u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := SecondPassFiber.second_energy_pushforward ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale P sel hb0 hB hL hvalid hmap ht hnorm hw
  calc
    _ ≤ ∑ x ∈ s, ‖w x‖ * ∑ u : κ, ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum
        (s := Finset.univ) (a := sel x)
        (f := fun u : κ => ‖P u (newLabel x, newRow x)‖ ^ 2)
        (fun u _ => sq_nonneg _) (Finset.mem_univ (sel x))
    _ = ∑ u : κ, ∑ x ∈ s, ‖w x‖ * ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ u : κ, B * C * (lengthScale * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P u z‖ ^ 2 := by
      exact Finset.sum_le_sum (fun u _ => hb s t b0 w (P u) B lengthScale hb0 hB hL hvalid hmap ht hnorm hw)
    _ = _ := by rw [Finset.mul_sum]

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)

local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def tupleLabelElement (x : OldTuple) : O :=
  idealGenerator (x.core 0) * idealGenerator (x.core 1) * idealGenerator (x.core 2) * idealGenerator x.v

theorem tupleLabelElement_span (x : OldTuple) :
    Ideal.span {tupleLabelElement x} = newLabel x := by
  simp only [tupleLabelElement, newLabel, ← Ideal.span_singleton_mul_span_singleton, span_idealGenerator]

theorem exists_label_unit (f : O) (I : Ideal O) (hf : Ideal.span {f} = I) :
    ∃ u : Oˣ, f = (u : O) * idealGenerator I := by
  have hs : Ideal.span {idealGenerator I} = Ideal.span {f} := (span_idealGenerator I).trans hf.symm
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def tupleLabelUnit (x : OldTuple) : Oˣ :=
  Classical.choose (exists_label_unit (tupleLabelElement x) (newLabel x) (tupleLabelElement_span x))

theorem tupleLabelUnit_spec (x : OldTuple) :
    tupleLabelElement x = (tupleLabelUnit x : O) * idealGenerator (newLabel x) :=
  Classical.choose_spec (exists_label_unit (tupleLabelElement x) (newLabel x) (tupleLabelElement_span x))

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (f y : O) : ℂ :=
  ∑ N ∈ F.powerset, secondChildColumn p hp hcop hg Ψ m f y H N

def idealChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (u : Oˣ) (z : Ideal O × O) : ℂ :=
  fixedChildRow p hp hcop hg F Ψ m H ((u : O) * idealGenerator z.1)
    (if negative then -z.2 else z.2)

theorem tuple_child_eq_unit_sector (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (x : OldTuple) :
    fixedChildRow p hp hcop hg F Ψ m H (tupleLabelElement x)
      (if negative then -newRow x else newRow x) =
    idealChildRow p hp hcop hg F Ψ m H negative (tupleLabelUnit x) (newLabel x, newRow x) := by
  rw [tupleLabelUnit_spec]
  rfl

theorem fixed_child_second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ *
        ‖fixedChildRow p hp hcop hg F Ψ m H (tupleLabelElement x)
          (if negative then -newRow x else newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := second_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale F Ψ m H negative hb0 hB hL hvalid hmap ht hnorm hw
  have hh := hb s t b0 w B lengthScale (idealChildRow p hp hcop hg F Ψ m H negative)
    tupleLabelUnit hb0 hB hL hvalid hmap ht hnorm hw
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [tuple_child_eq_unit_sector]

theorem idealChildRow_unit_energy_le (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (t : Finset (Ideal O × O)) (E : ℝ)
    (hE : ∀ u : Oˣ, (∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2) ≤ E) :
    (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2) ≤ 6 * E := by
  have hc : Fintype.card Oˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  calc
    _ ≤ ∑ u : Oˣ, E := Finset.sum_le_sum (fun u _ => hE u)
    _ = _ := by simp [hc]

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.Rows -/

section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open scoped BigOperators Classical MatrixGroups

section
abbrev K := ActualEisensteinCubic.K
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def row (M : levelThree) : Fin 2 → O := (M : SL(2,O)) 1

lemma row_mul (M N : levelThree) :
    row (M*N) = Matrix.vecMul (row M) (N : SL(2,O)) := by
  funext j
  simp only [row, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma row_ne_zero (M : levelThree) : row M ≠ 0 := by
  intro hz
  have hc : (M : SL(2,O)) 1 0 = 0 := congrFun hz 0
  have hd : (M : SL(2,O)) 1 1 = 0 := congrFun hz 1
  have h : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

lemma character_eq_of_row_eq (M N : levelThree) (hr : row M = row N) :
    complexCharacter M = complexCharacter N := by
  have hrow : row (M*N⁻¹) = row 1 := by
    rw [row_mul, hr, ← row_mul]
    simp
  have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0 = 0 := by
    simpa [row, Matrix.one_apply] using congrFun hrow 0
  have hchar : complexCharacter (M*N⁻¹) = 1 := by
    change eisEmbedding (value (M*N⁻¹)) = 1
    rw [value_zero_lower_left _ hc, map_one]
  calc
    complexCharacter M = complexCharacter ((M*N⁻¹)*N) := by congr 1; group
    _ = complexCharacter (M*N⁻¹) * complexCharacter N := map_mul _ _ _
    _ = complexCharacter N := by rw [hchar, one_mul]

lemma row_eq_one_of_lower_left_zero (M : levelThree)
    (hc : (M : SL(2,O)) 1 0 = 0) : row M = row 1 := by
  have hdet : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 = 1 := by
    have hd : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
        (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
    simpa only [hc, mul_zero, sub_zero] using hd
  have ha := A3_primary_unit_eq_one _ (IsUnit.of_mul_eq_one _ hdet)
    (levelThree_primary M)
  have hd : (M : SL(2,O)) 1 1 = 1 := by simpa only [ha, one_mul] using hdet
  funext j
  fin_cases j <;> simp [row, hc, hd]

def cuspStabilizer : Subgroup levelThree where
  carrier := {M | row M = row 1}
  one_mem' := rfl
  mul_mem' := by
    intro M N hM hN
    change row (M*N) = row 1
    rw [row_mul, hM, ← row_mul]
    simpa using hN
  inv_mem' := by
    intro M hM
    have h : row (M*M⁻¹) = row 1 := by simp
    rw [row_mul, hM, ← row_mul] at h
    simpa using h

lemma mem_cuspStabilizer_iff (M : levelThree) :
    M ∈ cuspStabilizer ↔ (M : SL(2,O)) 1 0 = 0 := by
  constructor
  · intro h
    simpa [row, Matrix.one_apply] using congrFun h 0
  · exact row_eq_one_of_lower_left_zero M

lemma row_eq_iff_left_cusp (M N : levelThree) : row M = row N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  constructor
  · intro h
    refine ⟨M*N⁻¹, ?_, by group⟩
    change row (M*N⁻¹) = row 1
    rw [row_mul, h, ← row_mul]
    simp
  · rintro ⟨T,hT,rfl⟩
    change row T = row 1 at hT
    rw [row_mul, hT, ← row_mul, one_mul]

def cuspRelation : Setoid levelThree := Setoid.ker row

abbrev CuspCosets := Quotient cuspRelation

def cosetOf (M : levelThree) : CuspCosets := Quotient.mk _ M

lemma cosetOf_eq_iff (M N : levelThree) : cosetOf M = cosetOf N ↔
    ∃ T : levelThree, T ∈ cuspStabilizer ∧ M = T*N := by
  rw [← row_eq_iff_left_cusp]
  exact Quotient.eq

def cosetRow : CuspCosets → (Fin 2 → O) :=
  Quotient.lift row (fun _ _ h => h)

@[simp] lemma cosetRow_cosetOf (M : levelThree) : cosetRow (cosetOf M) = row M := rfl

lemma cosetRow_injective : Function.Injective cosetRow := by
  intro x y
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      intro h
      exact Quotient.sound h

lemma cosetRow_ne_zero (x : CuspCosets) : cosetRow x ≠ 0 := by
  induction x using Quotient.inductionOn with | _ M => exact row_ne_zero M

def cosetCharacter : CuspCosets → ℂ :=
  Quotient.lift complexCharacter (fun M N h => character_eq_of_row_eq M N h)

@[simp] lemma cosetCharacter_cosetOf (M : levelThree) :
    cosetCharacter (cosetOf M) = complexCharacter M := rfl

lemma norm_cosetCharacter (x : CuspCosets) : ‖cosetCharacter x‖ = 1 := by
  induction x using Quotient.inductionOn with | _ M => exact norm_complexCharacter M

def rightTranslate (M : levelThree) : CuspCosets → CuspCosets :=
  Quotient.map (fun N => N*M) (by
    intro A B h
    change row (A*M) = row (B*M)
    rw [row_mul, row_mul, show row A = row B from h])

@[simp] lemma rightTranslate_cosetOf (M N : levelThree) :
    rightTranslate M (cosetOf N) = cosetOf (N*M) := rfl

lemma rightTranslate_mul (M N : levelThree) (x : CuspCosets) :
    rightTranslate N (rightTranslate M x) = rightTranslate (M*N) x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf ((A*M)*N) = cosetOf (A*(M*N))
    rw [mul_assoc]

@[simp] lemma rightTranslate_one (x : CuspCosets) : rightTranslate 1 x = x := by
  induction x using Quotient.inductionOn with | _ A =>
    change cosetOf (A*1) = cosetOf A
    rw [mul_one]

def rightEquiv (M : levelThree) : CuspCosets ≃ CuspCosets where
  toFun := rightTranslate M
  invFun := rightTranslate M⁻¹
  left_inv x := by rw [rightTranslate_mul]; simp
  right_inv x := by rw [rightTranslate_mul]; simp

lemma cosetRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    cosetRow (rightEquiv M x) = Matrix.vecMul (cosetRow x) (M : SL(2,O)) := by
  induction x using Quotient.inductionOn with | _ N => exact row_mul N M

lemma cosetCharacter_rightEquiv (M : levelThree) (x : CuspCosets) :
    cosetCharacter (rightEquiv M x) = cosetCharacter x * complexCharacter M := by
  induction x using Quotient.inductionOn with | _ N => exact map_mul _ _ _

def complexMatrix : levelThree →* SL(2,ℂ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) eisEmbedding).comp levelThree.subtype

lemma complexMatrix_apply (M : levelThree) (i j : Fin 2) :
    complexMatrix M i j = eisEmbedding ((M : SL(2,O)) i j) := rfl

def embeddedRow (x : CuspCosets) : Fin 2 → ℂ := eisEmbedding ∘ cosetRow x

lemma embeddedRow_ne_zero (x : CuspCosets) : embeddedRow x ≠ 0 := by
  intro hz
  apply cosetRow_ne_zero x
  funext i
  apply eisEmbedding_injective
  simpa only [embeddedRow, Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hz i

lemma embeddedRow_rightEquiv (M : levelThree) (x : CuspCosets) :
    embeddedRow (rightEquiv M x) = Matrix.vecMul (embeddedRow x) (complexMatrix M : SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow, Function.comp_apply, cosetRow_rightEquiv,
    Matrix.vecMul, dotProduct, map_sum, map_mul, complexMatrix_apply]

end

section
open ActualEisensteinCubic ConcreteTraceCRT

def integerLattice : Submodule ℤ ((Fin 2 × Fin 2) → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2 × Fin 2)))

instance : DiscreteTopology integerLattice := by
  unfold integerLattice
  infer_instance

instance : IsZLattice ℝ integerLattice := by
  unfold integerLattice
  infer_instance

def integerPoint (n : (Fin 2 × Fin 2) → ℤ) : integerLattice :=
  ⟨fun i => (n i : ℝ), by
    rw [integerLattice, (Pi.basisFun ℝ (Fin 2 × Fin 2)).mem_span_iff_repr_mem ℤ]
    intro i
    exact ⟨n i, by simp⟩⟩

lemma integerPoint_injective : Function.Injective integerPoint := by
  intro a b hab
  funext i
  have h := congrArg (fun x : integerLattice => (x : (Fin 2 × Fin 2) → ℝ) i) hab
  change (a i : ℝ) = (b i : ℝ) at h
  exact_mod_cast h

lemma integerPoint_norm (n : (Fin 2 × Fin 2) → ℤ) : ‖integerPoint n‖ = ‖n‖ := by
  change ‖fun i => (n i : ℝ)‖ = ‖n‖
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← Int.norm_eq_abs] using norm_le_pi_norm n i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← Int.norm_eq_abs] using norm_le_pi_norm (fun i => (n i : ℝ)) i

lemma summable_integer_four_rpow (k : ℝ) (hk : 4 < k) :
    Summable (fun n : (Fin 2 × Fin 2) → ℤ => ‖n‖ ^ (-k)) := by
  have hf : Module.finrank ℤ integerLattice = 4 := by
    rw [ZLattice.rank ℝ integerLattice]
    simp
  have hs := ZLattice.summable_norm_rpow integerLattice (-k) (by rw [hf]; norm_num; linarith)
  apply (hs.comp_injective integerPoint_injective).congr
  intro n
  change ‖integerPoint n‖ ^ (-k) = ‖n‖ ^ (-k)
  rw [integerPoint_norm]

def rowCoordinates (v : Fin 2 → O) : (Fin 2 × Fin 2) → ℤ :=
  fun i => if i.2 = 0 then (ActualEisensteinCoordinates.coords (v i.1)).1
    else (ActualEisensteinCoordinates.coords (v i.1)).2

lemma rowCoordinates_injective : Function.Injective rowCoordinates := by
  intro v w hvw
  funext i
  apply latticeCoordEquiv.injective
  apply Prod.ext
  · exact congrFun hvw (i,0)
  · exact congrFun hvw (i,1)

lemma coordinates_norm_bound (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ 2 * ‖fun i => eisEmbedding (v i)‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hi := norm_le_pi_norm (fun j => eisEmbedding (v j)) i.1
  have hq := eisEmbedding_eval_norm_sq
    (ActualEisensteinCoordinates.coords (v i.1)).1
    (ActualEisensteinCoordinates.coords (v i.1)).2
  rw [ActualEisensteinCoordinates.eval_coords] at hq
  push_cast at hq
  have hcoord (a b : ℝ) (t : ℝ) (ht : 0 ≤ t)
      (heq : t ^ 2 = a*a-a*b+b*b) : |a| ≤ 2*t ∧ |b| ≤ 2*t := by
    constructor <;> apply (abs_le).mpr <;> constructor <;>
      nlinarith [sq_nonneg (a-b), sq_nonneg (a+b), sq_nonneg (a-2*b), sq_nonneg (b-2*a)]
  have hh := hcoord _ _ ‖eisEmbedding (v i.1)‖ (norm_nonneg _) hq
  dsimp only [rowCoordinates]
  split_ifs
  · simpa only [Int.norm_eq_abs] using hh.1.trans (mul_le_mul_of_nonneg_left hi (by norm_num))
  · simpa only [Int.norm_eq_abs] using hh.2.trans (mul_le_mul_of_nonneg_left hi (by norm_num))

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def rowEnergy (v : Fin 2 → ℂ) : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2

lemma rowEnergy_nonneg (v : Fin 2 → ℂ) : 0 ≤ rowEnergy v := by
  unfold rowEnergy; positivity

lemma norm_le_sqrt_rowEnergy (v : Fin 2 → ℂ) : ‖v‖ ≤ Real.sqrt (rowEnergy v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply Real.le_sqrt_of_sq_le
  fin_cases i <;> dsimp [rowEnergy] <;> nlinarith [sq_nonneg ‖v 0‖, sq_nonneg ‖v 1‖]

lemma rowEnergy_pos (v : Fin 2 → ℂ) (hv : v ≠ 0) : 0 < rowEnergy v := by
  have h := norm_le_sqrt_rowEnergy v
  have hn := norm_pos_iff.mpr hv
  exact Real.sqrt_pos.mp (lt_of_lt_of_le hn h)

def rowOperator (g : SL(2,ℂ)) : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLinearMapRight' (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap

@[simp] lemma rowOperator_apply (g : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator g v = Matrix.vecMul v (g : Matrix (Fin 2) (Fin 2) ℂ) := rfl

lemma rowOperator_mul (g h : SL(2,ℂ)) (v : Fin 2 → ℂ) :
    rowOperator h (rowOperator g v) = rowOperator (g*h) v := by
  simp only [rowOperator_apply, Matrix.vecMul_vecMul, Matrix.SpecialLinearGroup.coe_mul]

@[simp] lemma rowOperator_one (v : Fin 2 → ℂ) : rowOperator 1 v = v := by
  simp only [rowOperator_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

lemma rowOperator_ne_zero (g : SL(2,ℂ)) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    rowOperator g v ≠ 0 := by
  intro hz
  have h := congrArg (rowOperator g⁻¹) hz
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one, map_zero] at h
  exact hv h

def rowBound (g : SL(2,ℂ)) : ℝ := 2 * (1 + ‖rowOperator g⁻¹‖)

lemma rowBound_pos (g : SL(2,ℂ)) : 0 < rowBound g := by unfold rowBound; positivity

lemma coordinates_le_transformed_energy (g : SL(2,ℂ)) (v : Fin 2 → O) :
    ‖rowCoordinates v‖ ≤ rowBound g *
      Real.sqrt (rowEnergy (rowOperator g (fun i => eisEmbedding (v i)))) := by
  have hi := (rowOperator g⁻¹).le_opNorm (rowOperator g (fun i => eisEmbedding (v i)))
  rw [rowOperator_mul, mul_inv_cancel, rowOperator_one] at hi
  have hb := coordinates_norm_bound v
  have he := norm_le_sqrt_rowEnergy (rowOperator g (fun i => eisEmbedding (v i)))
  have hm := mul_le_mul_of_nonneg_left he (norm_nonneg (rowOperator g⁻¹))
  dsimp only [rowBound]
  nlinarith [Real.sqrt_nonneg (rowEnergy (rowOperator g (fun i => eisEmbedding (v i))))]

lemma norm_coordinates_ne_zero (x : CuspCosets) : 0 < ‖rowCoordinates (cosetRow x)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  apply cosetRow_ne_zero x
  apply rowCoordinates_injective
  have hz0 : rowCoordinates (0 : Fin 2 → O) = 0 := by
    apply norm_le_zero_iff.mp
    have he : (fun i : Fin 2 => eisEmbedding ((0 : Fin 2 → O) i)) =
        (0 : Fin 2 → ℂ) := by
      funext i
      exact map_zero _
    have hh := coordinates_norm_bound (0 : Fin 2 → O)
    rw [he, norm_zero, mul_zero] at hh
    exact hh
  rw [hz0]
  exact hz

def summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) : ℂ :=
  (cosetCharacter x)⁻¹ *
    (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s)

lemma norm_summand (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    ‖summand g s x‖ = rowEnergy (rowOperator g (embeddedRow x)) ^ (-s.re) := by
  rw [summand, norm_mul, norm_inv, norm_cosetCharacter, inv_one, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x)))]
  rfl

lemma norm_summand_bound (g : SL(2,ℂ)) (s : ℂ) (hs : 0 < s.re) (x : CuspCosets) :
    ‖summand g s x‖ ≤ (rowBound g) ^ (2*s.re) *
      ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re)) := by
  rw [norm_summand]
  have hn := norm_coordinates_ne_zero x
  have hb := rowBound_pos g
  have he := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  have hbd := coordinates_le_transformed_energy g (cosetRow x)
  change ‖rowCoordinates (cosetRow x)‖ ≤ rowBound g *
    Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) at hbd
  have hle : (‖rowCoordinates (cosetRow x)‖ / rowBound g) ^ 2 ≤
      rowEnergy (rowOperator g (embeddedRow x)) := by
    have hd : ‖rowCoordinates (cosetRow x)‖ / rowBound g ≤
        Real.sqrt (rowEnergy (rowOperator g (embeddedRow x))) :=
      (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hbd)
    have hsq := Real.sq_sqrt he.le
    nlinarith [div_pos hn hb, Real.sqrt_nonneg (rowEnergy (rowOperator g (embeddedRow x)))]
  have hp := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos (div_pos hn hb)) hle (by linarith : -s.re ≤ 0)
  convert hp using 1
  rw [← Real.rpow_natCast_mul (div_nonneg hn.le hb.le) 2 (-s.re),
    Real.div_rpow hn.le hb.le]
  simp only [Nat.cast_ofNat, mul_neg, Real.rpow_neg hb.le, div_eq_mul_inv, inv_inv]
  exact mul_comm _ _

theorem summable_norm_summand (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun x : CuspCosets => ‖summand g s x‖) := by
  have hsum := summable_integer_four_rpow (2*s.re) (by linarith)
  have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
    rowCoordinates_injective.comp cosetRow_injective
  have hcomp : Summable (fun x : CuspCosets => ‖rowCoordinates (cosetRow x)‖ ^ (-(2*s.re))) := by
    apply (hsum.comp_injective hinj).congr
    intro x
    rfl
  exact (hcomp.mul_left ((rowBound g) ^ (2*s.re))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun x => norm_summand_bound g s (by linarith) x)

theorem summable_summand (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    Summable (summand g s) := (summable_norm_summand g s hs).of_norm

def eisenstein (g : SL(2,ℂ)) (s : ℂ) : ℂ := ∑' x : CuspCosets, summand g s x

lemma transformedRow_rightEquiv (M : levelThree) (g : SL(2,ℂ)) (x : CuspCosets) :
    rowOperator g (embeddedRow (rightEquiv M x)) =
      rowOperator (complexMatrix M * g) (embeddedRow x) := by
  rw [embeddedRow_rightEquiv, ← rowOperator_apply, rowOperator_mul]

lemma summand_automorphy (M : levelThree) (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    summand (complexMatrix M * g) s x =
      complexCharacter M * summand g s (rightEquiv M x) := by
  have hM : complexCharacter M ≠ 0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  simp only [summand, cosetCharacter_rightEquiv, transformedRow_rightEquiv,
    mul_inv_rev]
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hM, one_mul]

theorem eisenstein_automorphy (M : levelThree) (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    eisenstein (complexMatrix M * g) s = complexCharacter M * eisenstein g s := by
  have hleft := summable_summand (complexMatrix M * g) s hs
  have hright := summable_summand g s hs
  have hreindex : HasSum (fun x : CuspCosets => summand g s (rightEquiv M x))
      (eisenstein g s) := (rightEquiv M).hasSum_iff.mpr hright.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact hleft.hasSum.unique (hscale.congr_fun (fun x => summand_automorphy M g s x))

lemma summand_differentiable (g : SL(2,ℂ)) (x : CuspCosets) :
    Differentiable ℂ (fun s : ℂ => summand g s x) := by
  have hq : (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))).ne'
  exact ((differentiable_id.neg).const_cpow (Or.inl hq)).const_mul _

lemma norm_summand_strip (g : SL(2,ℂ)) (a b : ℝ) (s : ℂ)
    (ha : a ≤ s.re) (hb : s.re ≤ b) (x : CuspCosets) :
    ‖summand g s x‖ ≤ ‖summand g (a : ℂ) x‖ + ‖summand g (b : ℂ) x‖ := by
  simp only [norm_summand, Complex.ofReal_re]
  have hq := rowEnergy_pos _ (rowOperator_ne_zero g _ (embeddedRow_ne_zero x))
  by_cases hq1 : 1 ≤ rowEnergy (rowOperator g (embeddedRow x))
  · exact (Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg ha)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hq.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hq (le_of_not_ge hq1)
        (neg_le_neg hb)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hq.le _))

theorem eisenstein_differentiableOn_strip (g : SL(2,ℂ)) (a b : ℝ)
    (ha : 2 < a) (hab : a < b) :
    DifferentiableOn ℂ (eisenstein g) {s : ℂ | a < s.re ∧ s.re < b} := by
  have hsa := summable_norm_summand g (a : ℂ) (by simpa using ha)
  have hsb := summable_norm_summand g (b : ℂ) (by simpa using lt_trans ha hab)
  apply Complex.differentiableOn_tsum_of_summable_norm (hsa.add hsb)
    (fun x => (summand_differentiable g x).differentiableOn)
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  · intro x s hs
    exact norm_summand_strip g a b s hs.1.le hs.2.le x

theorem eisenstein_differentiableAt (g : SL(2,ℂ)) (s : ℂ) (hs : 2 < s.re) :
    DifferentiableAt ℂ (eisenstein g) s := by
  let a := (2+s.re)/2
  let b := s.re+1
  have ha : 2 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hsU : s ∈ {z : ℂ | a < z.re ∧ z.re < b} := by
    constructor <;> dsimp [a,b] <;> linarith
  exact (eisenstein_differentiableOn_strip g a b ha hab s hsU).differentiableAt
    (((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hsU)

theorem eisenstein_differentiableOn (g : SL(2,ℂ)) :
    DifferentiableOn ℂ (eisenstein g) {s : ℂ | 2 < s.re} := by
  intro s hs
  exact (eisenstein_differentiableAt g s hs).differentiableWithinAt

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) : SL(2,ℂ) :=
  ⟨!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹], by
    have hr : (Real.sqrt v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
    simp [Matrix.det_fin_two, hr]⟩

lemma rowOperator_upperSection_zero (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowOperator (upperSection z v hv) u 0 = u 0 * (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma rowOperator_upperSection_one (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowOperator (upperSection z v hv) u 1 = (u 0*z + u 1) / (Real.sqrt v : ℂ) := by
  change Matrix.vecMul u (!![(Real.sqrt v : ℂ), z / (Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) _ = _
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

def heightDenominator (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  ‖u 0*z + u 1‖ ^ 2 + ‖u 0‖ ^ 2 * v ^ 2

lemma rowEnergy_upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) (u : Fin 2 → ℂ) :
    rowEnergy (rowOperator (upperSection z v hv) u) = heightDenominator z v u / v := by
  rw [rowEnergy, rowOperator_upperSection_zero, rowOperator_upperSection_one,
    norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg v),
    mul_pow, div_pow, Real.sq_sqrt hv.le]
  unfold heightDenominator
  field_simp
  ring

lemma heightDenominator_pos (z : ℂ) (v : ℝ) (hv : 0 < v)
    (u : Fin 2 → ℂ) (hu : u ≠ 0) : 0 < heightDenominator z v u := by
  have h := rowEnergy_pos _ (rowOperator_ne_zero (upperSection z v hv) u hu)
  rw [rowEnergy_upperSection] at h
  exact ((div_pos_iff.mp h).resolve_right (by rintro ⟨_,hneg⟩; linarith)).1

def transformedHeight (z : ℂ) (v : ℝ) (u : Fin 2 → ℂ) : ℝ :=
  v / heightDenominator z v u

lemma summand_upperSection (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    summand (upperSection z v hv) s x = (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s := by
  rw [summand, rowEnergy_upperSection]
  congr 1
  have hq := heightDenominator_pos z v hv (embeddedRow x) (embeddedRow_ne_zero x)
  have hinv : (transformedHeight z v (embeddedRow x) : ℂ) =
      ((heightDenominator z v (embeddedRow x) / v : ℝ) : ℂ)⁻¹ := by
    simp only [transformedHeight, Complex.ofReal_div, inv_div]
  rw [hinv, Complex.inv_cpow_ofReal_nonneg (div_nonneg hq.le hv.le), Complex.cpow_neg]

def upperEisenstein (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) : ℂ :=
  eisenstein (upperSection z v hv) s

theorem upperEisenstein_eq_source_series (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    upperEisenstein z v hv s = ∑' x : CuspCosets, (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s :=
  tsum_congr (summand_upperSection z v hv s)

theorem source_series_summable (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun x : CuspCosets => (cosetCharacter x)⁻¹ *
      (transformedHeight z v (embeddedRow x) : ℂ) ^ s) :=
  (summable_summand (upperSection z v hv) s hs).congr (summand_upperSection z v hv s)

lemma ofReal_rowEnergy (u : Fin 2 → ℂ) :
    (rowEnergy u : ℂ) = dotProduct u (star u) := by
  simp only [rowEnergy, Complex.ofReal_add, ← Complex.normSq_eq_norm_sq, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Complex.star_def, Complex.mul_conj]

lemma rowEnergy_unitary (k : SL(2,ℂ))
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (u : Fin 2 → ℂ) : rowEnergy (rowOperator k u) = rowEnergy u := by
  apply Complex.ofReal_injective
  rw [ofReal_rowEnergy, ofReal_rowEnergy, rowOperator_apply, Matrix.star_vecMul,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  have hu := Matrix.mem_unitaryGroup_iff.mp hk
  change (k : Matrix (Fin 2) (Fin 2) ℂ) *
    Matrix.conjTranspose (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 at hu
  rw [hu, Matrix.vecMul_one]

theorem eisenstein_right_unitary (g k : SL(2,ℂ)) (s : ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    eisenstein (g*k) s = eisenstein g s := by
  apply tsum_congr
  intro x
  simp only [summand, ← rowOperator_mul, rowEnergy_unitary k hk]

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace -/

section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open scoped BigOperators Classical MatrixGroups Matrix

section
open CubicKubota

def compactSubgroup : Subgroup (SL(2,ℂ)) where
  carrier := {k | (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ}
  one_mem' := (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
  mul_mem' := by
    intro a b ha hb
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem ha hb
  inv_mem' := by
    intro k hk
    have hinv : (k⁻¹ : SL(2,ℂ)) * k = 1 := inv_mul_cancel k
    have hmat : ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg
          (fun a : SL(2,ℂ) => (a : Matrix (Fin 2) (Fin 2) ℂ)) hinv
    have he := Matrix.left_inv_eq_left_inv hmat (Matrix.mem_unitaryGroup_iff'.mp hk)
    change ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [he]
    exact Unitary.star_mem hk

abbrev HyperbolicSpace := SL(2,ℂ) ⧸ compactSubgroup

def hyperbolicEisenstein (s : ℂ) : HyperbolicSpace → ℂ :=
  Quotient.lift (fun g => eisenstein g s) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (eisenstein_right_unitary g (g⁻¹*h) s hk).symm)

@[simp] lemma hyperbolicEisenstein_mk (s : ℂ) (g : SL(2,ℂ)) :
    hyperbolicEisenstein s (g : HyperbolicSpace) = eisenstein g s := rfl

theorem hyperbolicEisenstein_automorphy (M : levelThree) (s : ℂ) (hs : 2 < s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (complexMatrix M • w) =
      complexCharacter M * hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_automorphy M g s hs

def upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) : HyperbolicSpace :=
  (upperSection z v hv : HyperbolicSpace)

lemma hyperbolicEisenstein_upperPoint (s : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicEisenstein s (upperPoint z v hv) = upperEisenstein z v hv s := rfl

def complexBottomRow (g : SL(2,ℂ)) : Fin 2 → ℂ := g 1

lemma complexBottomRow_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) = rowOperator h (complexBottomRow g) := by
  funext j
  simp only [complexBottomRow, rowOperator_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma complexBottomRow_ne_zero (g : SL(2,ℂ)) : complexBottomRow g ≠ 0 := by
  intro hz
  have hc : g 1 0 = 0 := congrFun hz 0
  have hd : g 1 1 = 0 := congrFun hz 1
  have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

def liftedHeight (g : SL(2,ℂ)) : ℝ := (rowEnergy (complexBottomRow g))⁻¹

lemma liftedHeight_pos (g : SL(2,ℂ)) : 0 < liftedHeight g :=
  inv_pos.mpr (rowEnergy_pos _ (complexBottomRow_ne_zero g))

lemma liftedHeight_right_unitary (g k : SL(2,ℂ)) (hk : k ∈ compactSubgroup) :
    liftedHeight (g*k) = liftedHeight g := by
  simp only [liftedHeight, complexBottomRow_mul, rowEnergy_unitary k hk]

def hyperbolicHeight : HyperbolicSpace → ℝ :=
  Quotient.lift liftedHeight (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (liftedHeight_right_unitary g (g⁻¹*h) hk).symm)

@[simp] lemma hyperbolicHeight_mk (g : SL(2,ℂ)) :
    hyperbolicHeight (g : HyperbolicSpace) = liftedHeight g := rfl

lemma hyperbolicHeight_pos (w : HyperbolicSpace) : 0 < hyperbolicHeight w := by
  induction w using Quotient.inductionOn with | _ g => exact liftedHeight_pos g

theorem hyperbolicHeight_action_upperPoint (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicHeight (g • upperPoint z v hv) =
      v / (‖g 1 0*z + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * v ^ 2) := by
  change liftedHeight (g * upperSection z v hv) = _
  rw [liftedHeight, complexBottomRow_mul, rowEnergy_upperSection, inv_div]
  rfl

def cosetHeight (x : CuspCosets) : HyperbolicSpace → ℝ :=
  Quotient.lift (fun g : SL(2,ℂ) => (rowEnergy (rowOperator g (embeddedRow x)))⁻¹) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh, ← rowOperator_mul, rowEnergy_unitary (g⁻¹*h) hk])

lemma cosetHeight_cosetOf (M : levelThree) (w : HyperbolicSpace) :
    cosetHeight (cosetOf M) w = hyperbolicHeight (complexMatrix M • w) := by
  induction w using Quotient.inductionOn with | _ g =>
    change (rowEnergy (rowOperator g (embeddedRow (cosetOf M))))⁻¹ =
      liftedHeight (complexMatrix M * g)
    rw [liftedHeight, complexBottomRow_mul]
    rfl

theorem hyperbolicEisenstein_eq_height_series (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w = ∑' x : CuspCosets,
      (cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s := by
  induction w using Quotient.inductionOn with | _ g =>
    apply tsum_congr
    intro x
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem height_series_summable_norm (s : ℂ) (hs : 2 < s.re) (w : HyperbolicSpace) :
    Summable (fun x : CuspCosets =>
      ‖(cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s‖) := by
  induction w using Quotient.inductionOn with | _ g =>
    apply (summable_norm_summand g s hs).congr
    intro x
    congr 1
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem hyperbolicEisenstein_differentiableOn (w : HyperbolicSpace) :
    DifferentiableOn ℂ (fun s : ℂ => hyperbolicEisenstein s w) {s : ℂ | 2 < s.re} := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_differentiableOn g

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def upperTranslation (a : O) : levelThree := by
  let M : SL(2,O) := ⟨!![1, 3*a; 0, 1], by simp⟩
  refine ⟨M, ?_⟩
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  have h3 : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (3 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) ((!![(1 : O), 3*a; 0, 1]) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  fin_cases i <;> fin_cases j <;> simp [h3, map_mul]

lemma complexCharacter_upperTranslation (a : O) : complexCharacter (upperTranslation a) = 1 := by
  change eisEmbedding (value (upperTranslation a)) = 1
  rw [value_zero_lower_left _ (by rfl), map_one]

lemma upperTranslation_section (a : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    complexMatrix (upperTranslation a) * upperSection z v hv =
      upperSection (z + 3*eisEmbedding a) v hv := by
  apply Subtype.ext
  funext i j
  change (((!![(1 : O), 3*a; 0, 1]).map eisEmbedding) *
    !![(Real.sqrt v : ℂ), z/(Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) i j =
    (!![(Real.sqrt v : ℂ), (z+3*eisEmbedding a)/(Real.sqrt v : ℂ);
      0, (Real.sqrt v : ℂ)⁻¹]) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, map_mul] ;
    norm_num only [map_ofNat] ; ring

theorem upperEisenstein_periodic (a : O) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein (z + 3*eisEmbedding a) v hv s = upperEisenstein z v hv s := by
  unfold upperEisenstein
  rw [← upperTranslation_section, eisenstein_automorphy _ _ _ hs,
    complexCharacter_upperTranslation, one_mul]

end

open MeasureTheory Set Filter
open scoped BigOperators Classical

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

def hyperbolicKernel (s : ℂ) (z : ℂ) : ℂ := ((1+‖z‖^2 : ℝ) : ℂ) ^ (-s)

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace

lemma breveE_norm (z : ℂ) : ‖ShortDraftTrace.breveE z‖ = 1 := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z))‖ = 1
  rw [Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

def sourceFourierKernel (s freq : ℂ) : ℂ :=
  ∫ z : ℂ, hyperbolicKernel s z * ShortDraftTrace.breveE (-freq*z)

lemma sourceFourierKernel_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun z : ℂ => hyperbolicKernel s z * ShortDraftTrace.breveE (-freq*z)) := by
  apply (hyperbolicKernel_integrable s hs).norm.mono'
  · have hker : Continuous (hyperbolicKernel s) := by
      unfold hyperbolicKernel
      apply Continuous.cpow
      · fun_prop
      · exact continuous_const
      · intro z
        exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
    have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
      change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
        ((-freq*z)+starRingEnd ℂ (-freq*z))))
      fun_prop
    exact (hker.mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by simp only [norm_mul, breveE_norm, mul_one, le_refl])

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
    using integral_hyperbolicKernel s hs

lemma sourceFrequency_inner (z freq : ℂ) : inner ℝ z (2*starRingEnd ℂ freq) = 2*(freq*z).re := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change ((2 * starRingEnd ℂ freq) * starRingEnd ℂ z).re = _
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma traceIntegral_eq_fourier (f : ℂ → ℂ) (freq : ℂ) :
    (∫ z : ℂ, f z * ShortDraftTrace.breveE (-freq*z)) = 𝓕 f (2*starRingEnd ℂ freq) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [sourceFrequency_inner]
    change f z *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))) = _
    simp only [smul_eq_mul]
    rw [mul_comm (f z)]
    congr 1
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring)

lemma sourceFourierKernel_eq_fourier (s freq : ℂ) :
    sourceFourierKernel s freq = 𝓕 (hyperbolicKernel s) (2*starRingEnd ℂ freq) :=
  traceIntegral_eq_fourier (hyperbolicKernel s) freq

lemma hyperbolicKernel_laplace (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    hyperbolicKernel s z * Complex.Gamma s =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(s-1) *
        Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ) * t) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs
    (by positivity : 0 < 1+‖z‖^2)
  simp only [neg_mul]
  rw [h]
  congr 1
  rw [hyperbolicKernel, one_div, Complex.inv_cpow_ofReal_nonneg (by positivity),
    Complex.cpow_neg]

lemma source_gaussian_fourier (t : ℝ) (ht : 0 < t) (freq : ℂ) :
    𝓕 (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) (2*starRingEnd ℂ freq) =
      (Real.pi : ℂ)/t * Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  rw [fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℂ)≠0),
    Complex.cpow_one, norm_mul, Complex.norm_conj, Complex.norm_ofNat]
  congr 2
  push_cast
  ring

def gaussianMixture (s freq : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (t : ℂ)^(s-1) * Complex.exp (-t) *
    Complex.exp (-(t : ℂ)*‖z‖^2) * ShortDraftTrace.breveE (-freq*z)

lemma norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ‖gaussianMixture s freq t z‖ =
      t ^ (s.re-1) * Real.exp (-t) * Real.exp (-t*‖z‖^2) := by
  simp only [gaussianMixture, norm_mul, breveE_norm, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re,
    Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, Complex.neg_im, neg_zero, zero_mul, sub_zero]

lemma gaussianMixture_slice_integrable (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    Integrable (gaussianMixture s freq t) := by
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by simpa using ht : 0 < (t : ℂ).re) 0 (0 : ℂ)
  apply ((hg.const_mul ((t : ℂ)^(s-1)*Complex.exp (-t))).norm).mono'
  · unfold gaussianMixture
    change AEStronglyMeasurable (fun z : ℂ => (t : ℂ)^(s-1)*Complex.exp (-t)*
      Complex.exp (-(t : ℂ)*‖z‖^2) *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  · exact Eventually.of_forall fun z => by
      simp only [gaussianMixture, norm_mul, breveE_norm, mul_one, le_refl]

lemma integral_norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, ‖gaussianMixture s freq t z‖) =
      Real.pi * (Real.exp (-t)*t^(s.re-2)) := by
  simp_rw [norm_gaussianMixture s freq t ht]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℝ)≠0),
    Real.rpow_one]
  have hp : t^(s.re-1)/t = t^(s.re-2) := by
    calc
      t^(s.re-1)/t = t^(s.re-1)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((s.re-1)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1; ring
  calc
    t^(s.re-1)*Real.exp (-t)*(Real.pi/t) = Real.pi*(Real.exp (-t)*(t^(s.re-1)/t)) := by ring
    _ = _ := by rw [hp]

theorem gaussianMixture_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    unfold gaussianMixture
    change AEStronglyMeasurable (fun p : ℝ × ℂ =>
      (p.1 : ℂ)^(s-1)*Complex.exp (-p.1)*Complex.exp (-(p.1 : ℂ)*‖p.2‖^2)*
      Complex.exp (2*Real.pi*Complex.I*((-freq*p.2)+starRingEnd ℂ (-freq*p.2)))) _
    fun_prop
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact gaussianMixture_slice_integrable s freq t ht
  · have hgamma := (Real.GammaIntegral_convergent (by linarith : 0 < s.re-1)).const_mul Real.pi
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [integral_norm_gaussianMixture s freq t ht]
    congr 2
    ring_nf

open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace

lemma gaussianMixture_laplace_form (s freq : ℂ) (t : ℝ) (z : ℂ) :
    gaussianMixture s freq t z =
      ((t : ℂ)^(s-1) * Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t)) *
        ShortDraftTrace.breveE (-freq*z) := by
  have he : Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2) =
      Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (t : ℂ)^(s-1) * (Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2)) *
        ShortDraftTrace.breveE (-freq*z) := by unfold gaussianMixture; ring
    _ = _ := by rw [he]

lemma integral_gaussianMixture_t (s freq : ℂ) (hs : 0 < s.re) (z : ℂ) :
    (∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z) =
      (hyperbolicKernel s z * Complex.Gamma s)*ShortDraftTrace.breveE (-freq*z) := by
  simp_rw [gaussianMixture_laplace_form]
  rw [integral_mul_const, ← hyperbolicKernel_laplace s hs z]

lemma integral_gaussianMixture_z (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, gaussianMixture s freq t z) =
      (Real.pi : ℂ) * ((t : ℂ)^(s-2) *
        Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t)) := by
  have hfac : (fun z : ℂ => gaussianMixture s freq t z) =
      (fun z : ℂ => ((t : ℂ)^(s-1)*Complex.exp (-t))*
        (Complex.exp (-(t : ℂ)*‖z‖^2)*ShortDraftTrace.breveE (-freq*z))) := by
    funext z
    unfold gaussianMixture
    ring
  rw [hfac, integral_const_mul, traceIntegral_eq_fourier, source_gaussian_fourier t ht freq]
  have hp : (t : ℂ)^(s-1)/(t : ℂ) = (t : ℂ)^(s-2) := by
    calc
      _ = (t : ℂ)^(s-1)/(t : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^((s-1)-1) := (Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')).symm
      _ = _ := by congr 1; ring
  calc
    _ = (Real.pi : ℂ)*(((t : ℂ)^(s-1)/t)*
        (Complex.exp (-(t : ℂ))*Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t))) := by ring
    _ = _ := by rw [hp, ← Complex.exp_add]; congr 2; ring_nf

theorem sourceFourierKernel_gamma (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ)^(s-2) * Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  have hmix := gaussianMixture_integrable s freq hs
  calc
    _ = ∫ z : ℂ, (hyperbolicKernel s z * Complex.Gamma s)*
        ShortDraftTrace.breveE (-freq*z) := by
      rw [sourceFourierKernel, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    _ = ∫ z : ℂ, ∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => (integral_gaussianMixture_t s freq (by linarith) z).symm
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ z : ℂ, gaussianMixture s freq t z :=
      (integral_integral_swap hmix).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_gaussianMixture_z s freq t ht

def schlafliIntegral (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(ν-1)*
    Complex.exp (-(t : ℂ) - (x : ℂ)^2/(4*t))

lemma schlafliIntegral_integrable (ν : ℂ) (x : ℝ) (hν : 0 < ν.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(ν-1)*
      Complex.exp (-(t : ℂ)-(x : ℂ)^2/(4*t))) (Set.Ioi 0) := by
  apply (Real.GammaIntegral_convergent hν).mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hre : (-(t : ℂ)-(x : ℂ)^2/(4*t)).re = -t-x^2/(4*t) := by
      rw [show -(t : ℂ)-(x : ℂ)^2/(4*t) = ((-t-x^2/(4*t) : ℝ) : ℂ) by push_cast; rfl]
      rfl
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, hre]
    simp only [Complex.sub_re, Complex.one_re]
    have he := Real.exp_le_exp.mpr (show -t-x^2/(4*t) ≤ -t by linarith [div_nonneg (sq_nonneg x) (show 0 ≤ 4*t by positivity)])
    have hb := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le (ν.re-1))
    simpa only [mul_comm] using hb

def schlafliBesselK (ν : ℂ) (x : ℝ) : ℂ :=
  (1/2 : ℂ)*(x/2 : ℂ)^(-ν)*schlafliIntegral ν x

lemma sourceFourierKernel_gamma_schlafli (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖) := by
  rw [sourceFourierKernel_gamma s freq hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [show s-2=(s-1)-1 by ring]
  apply congrArg (fun w : ℂ => (t : ℂ)^((s-1)-1)*Complex.exp w)
  push_cast
  ring

theorem sourceFourierKernel_bessel (s freq : ℂ) (hs : 1 < s.re) (hf : freq ≠ 0) :
    sourceFourierKernel s freq =
      (2*Real.pi : ℂ)/Complex.Gamma s *
        (2*Real.pi*‖freq‖ : ℂ)^(s-1) *
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖) := by
  have hg := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hz : (2*Real.pi*‖freq‖ : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hf))
  have hp : (2*Real.pi*‖freq‖ : ℂ)^(s-1) * (2*Real.pi*‖freq‖ : ℂ)^(-(s-1)) = 1 := by
    rw [← Complex.cpow_add _ _ hz, add_neg_cancel, Complex.cpow_zero]
  have hreorder : (2*Real.pi : ℂ)/Complex.Gamma s *
      (2*Real.pi*‖freq‖ : ℂ)^(s-1) * schlafliBesselK (s-1) (4*Real.pi*‖freq‖) =
      ((2*Real.pi : ℂ)*(2*Real.pi*‖freq‖ : ℂ)^(s-1)*
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖))/Complex.Gamma s := by ring
  rw [hreorder]
  apply (eq_div_iff hg).mpr
  rw [sourceFourierKernel_gamma_schlafli s freq hs]
  unfold schlafliBesselK
  push_cast
  have hhalf : (4*(Real.pi : ℂ)*‖freq‖)/2 = 2*Real.pi*‖freq‖ := by ring
  rw [hhalf]
  linear_combination -((Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖))*hp

theorem sourceFourierKernel_four_thirds (freq : ℂ) (hf : freq ≠ 0) :
    sourceFourierKernel (4/3 : ℂ) freq =
      (2*Real.pi : ℂ)/Complex.Gamma (4/3) *
        (2*Real.pi*‖freq‖ : ℂ)^(1/3 : ℂ) *
        schlafliBesselK (1/3) (4*Real.pi*‖freq‖) := by
  convert sourceFourierKernel_bessel (4/3) freq (by norm_num) hf using 1 ; norm_num

end CubicEisenstein

end

end OAI

end

