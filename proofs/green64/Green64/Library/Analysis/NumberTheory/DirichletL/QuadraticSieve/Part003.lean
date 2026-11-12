module

public import Green64.Library.Analysis.NumberTheory.DirichletL.QuadraticSieve.Part002

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / QuadraticSieve / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.TruncatedSecondTransfer -/

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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex TruncatedPrincipalPoisson

def squarefreeIdealRange (K : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊K⌋₊).filter Squarefree

theorem mem_squarefreeIdealRange {K : ℝ} {I : Ideal O} :
    I ∈ squarefreeIdealRange K ↔ Squarefree I ∧ (Ideal.absNorm I : ℝ) ≤ K := by
  rw [squarefreeIdealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, hs⟩
    refine ⟨hs, ?_⟩
    have hK : 0 ≤ K := by
      by_contra hn
      have hz : ⌊K⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hK)
  · rintro ⟨hs, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => hs.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, hs⟩

theorem tsum_squarefree_norm_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : squarefreeIdealRange K, f B.val := by
  let e : squarefreeIdealRange K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealRange.mp B.property).1⟩
  have he : Function.Injective e := by
    intro B C h
    apply Subtype.ext
    exact congrArg (fun D : {B : Ideal O // Squarefree B} => D.val) h
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (ite_eq_right hn)
    exact ⟨⟨B.val, mem_squarefreeIdealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩
  have ht := he.tsum_eq hs
  change (∑' B, F B) = _
  rw [← ht, tsum_fintype]
  apply Finset.sum_congr rfl
  intro B _
  exact ite_eq_left (mem_squarefreeIdealRange.mp B.property).2

theorem dualSquarefreeLow_principal_finite
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    dualSquarefreeLow I J W t K =
      ∑ B : squarefreeIdealRange K, unrestrictedPairCharacter I J B.val *
        dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
          (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) := by
  rw [dualSquarefreeLow_principal I J hI hJ hray W t K ht]
  exact tsum_squarefree_norm_cutoff K (fun B => unrestrictedPairCharacter I J B *
    dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
      (Real.sqrt (1 / (t * (Ideal.absNorm B : ℝ)))))

theorem canonical_nonprincipal_dual_finite_truncated
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hnt : I ≠ 1 ∨ J ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t)
    (Y Z lengthScale : Ideal O → ℝ) :
    (∑' h : O, (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) =
      (∑ B : squarefreeIdealRange K,
        let X := Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))
        let P := fun P : primePool {I * J} => P.val
        let V := quadraticTransformedSquareProfile W
        unrestrictedPairCharacter I J B.val *
          (principalTruncation P Finset.univ V X (Z B.val) +
           middleTruncation P Finset.univ V X (Y B.val) (Z B.val) (lengthScale B.val) +
           truncationError P Finset.univ V X (Y B.val) (Z B.val) (lengthScale B.val))) +
      6 * dualSquarefreeTail I J W t K := by
  rw [canonical_nonprincipal_dual_ideal_reindex I J hI hJ hray hnt W t ht,
    dual_ideal_low_add_tail I J W t K ht, mul_add,
    dualSquarefreeLow_principal_finite I J hI hJ hray W t K ht, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro B _
  have hB : 0 < (Ideal.absNorm B.val : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (fun h => (mem_squarefreeIdealRange.mp B.property).1.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
  have hX : 0 < Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ))) :=
    Real.sqrt_pos.mpr (one_div_pos.mpr (mul_pos ht hB))
  rw [dualPrincipalIdeal_truncated I J hI hJ hnt (quadraticTransformedSquareProfile W)
    _ (Y B.val) (Z B.val) (lengthScale B.val) hX]
  dsimp only
  ring

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def secondDiagonalMass (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) : ℝ :=
  ∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d H G‖ ^ 2 *
    ∏ i ∈ G, (1 - (1 : ℝ) / Ideal.absNorm (Ideal.span {p i}))

include hinj in

theorem truncatedSecondZero_eq_density
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) :
    truncatedSecondZero p hg F Ψ m c d H W Y K =
      (Y : ℂ) * paperRadialFourier W 0 * (secondDiagonalMass p hg F Ψ m c d H : ℂ) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  unfold truncatedSecondZero secondDiagonalMass
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro G hG
  have hd : (∑ E : G.powerset, if (0 : O) ∈ K G E.val then
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)
      else 0) = ∏ i ∈ G, (1 - (1 : ℂ) / Ideal.absNorm (Ideal.span {p i})) := by
    have hi (E : G.powerset) := hzero G hG E.val E.property
    simp only [hi, ite_true, primeSubsetGenerator_norm_sq, Complex.ofReal_natCast]
    rw [Finset.sum_coe_sort (s := G.powerset) (f := fun E : Finset ι =>
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (Ideal.absNorm (∏ i ∈ E, Ideal.span {p i}) : ℂ))]
    exact primeSubset_moebius_norm_sum _ hprime hinj G
  rw [hd]
  have hi : secondInputCoefficient p hg Ψ m c d H G =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) G * H G := by
    simp only [secondInputCoefficient, mul_one]
  have hh : star (H G) * H G = (‖H G‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hi, norm_mul, mul_pow, Complex.ofReal_mul]
  rw [mul_assoc (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2)) (star (H G)), hh]

omit [DecidableEq ι] in
theorem secondDiagonalMass_nonneg_le
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) :
    0 ≤ secondDiagonalMass p hg F Ψ m c d H ∧
      secondDiagonalMass p hg F Ψ m c d H ≤
        ∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d H G‖ ^ 2 := by
  constructor
  · exact Finset.sum_nonneg (fun G hG => mul_nonneg (sq_nonneg _)
      (primeDensity_nonneg_le_one (fun i => Ideal.span {p i}) G).1)
  · apply Finset.sum_le_sum
    intro G hG
    exact mul_le_of_le_one_right (sq_nonneg _)
      (primeDensity_nonneg_le_one (fun i => Ideal.span {p i}) G).2

include hinj in

theorem truncatedSecondZero_norm_le
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ ≤
      |Y| * ‖paperRadialFourier W 0‖ *
        ∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d H G‖ ^ 2 := by
  rw [truncatedSecondZero_eq_density p hg hinj F Ψ m c d H W Y K hzero]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_of_nonneg (secondDiagonalMass_nonneg_le p hg F Ψ m c d H).1]
  exact mul_le_mul_of_nonneg_left (secondDiagonalMass_nonneg_le p hg F Ψ m c d H).2
    (mul_nonneg (abs_nonneg _) (norm_nonneg _))

end
section

open ActualEisensteinCubic

def secondDyadicSector {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ) : Finset (SecondExpansionData ι) :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (fun x => label R x = j)

theorem secondDyadicSector_subset {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ) :
    secondDyadicSector F K R label j ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R :=
  Finset.filter_subset _ _

theorem sum_secondDyadicSector {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (label : Finset ι → SecondExpansionData ι → κ) (H : SecondExpansionData ι → ℂ) :
    (∑ j : κ, ∑ x ∈ secondDyadicSector F K R label j, H x) =
      ∑ x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R, H x := by
  simp only [secondDyadicSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem truncatedSecondSource_eq_zero_add_dyadic
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (label : Finset ι → SecondExpansionData ι → κ) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondZero p hg F Ψ m c d H W Y K +
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset, ∑ j : κ,
        secondExpansionSource p hp hcop hg F Ψ m c d z
          (secondDyadicSector F K R label j) H H W Y := by
  rw [truncatedSecondSource_eq_nonzero_add_zero, add_comm,
    truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro R hR
  simp only [secondExpansionSource, sum_secondDyadicSector]

theorem truncatedSecondSource_norm_le_zero_add_dyadic
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
    (label : Finset ι → SecondExpansionData ι → κ) :
    ‖truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K‖ ≤
      ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ +
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset, ∑ j : κ,
        ‖secondExpansionSource p hp hcop hg F Ψ m c d z
          (secondDyadicSector F K R label j) H H W Y‖ := by
  rw [truncatedSecondSource_eq_zero_add_dyadic p hp hcop hg hinj hc hpr F Ψ m c d H W Y K label]
  apply (norm_add_le _ _).trans
  gcongr
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro z hz
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro R hR
  exact norm_sum_le _ _

end

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (tripleCoefficient)
open SecondPassIntegration (childGeometricMean)

theorem normalized_truncated_second_transfer
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (D₀ E₀ V₀ X₀ K₀ : Finset ι → κ → ℝ) (Y : ℝ),
        (∀ R j, 0 < D₀ R j) → (∀ R j, 0 < E₀ R j) → (∀ R j, 0 < V₀ R j) →
        (∀ R j, 0 < X₀ R j) → (∀ R j, 0 < K₀ R j) → 0 < Y →
      ∃ b : Finset ι → κ → 𝓢(ℝ, ℂ),
      (∀ R j t₁ t₂ t₃,
        (1+Y*K₀ R j/(D₀ R j*(E₀ R j)^2*(V₀ R j)^2*(X₀ R j)^2))^decayOrder *
          ‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b R j t₃‖ ≤
          Cₛ*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X : ℝ) (K : Finset ι → Finset ι → Finset O)
        (label : Finset ι → SecondExpansionData ι → κ)
        (T : Finset ι → κ → Finset (Ideal O × O)) (lengthScale : Finset ι → κ → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X →
        (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) →
        (∀ R ∈ F.powerset, ∀ j, 0 ≤ lengthScale R j) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorZ p
            (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
              (expansionSupportData C D x)) (X₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUd p (D₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUe p (E₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorUv p (V₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          |secondSectorKap p (K₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ F.powerset, ∀ j, ∀ x ∈ secondDyadicSector F K R label j,
          (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
            secondSupportRow p (expansionSupportData C D x)) ∈ T R j) →
        (∀ R ∈ F.powerset, ∀ j, ∀ t ∈ T R j, t.1 ≠ ⊥) →
        (∀ R ∈ F.powerset, ∀ j, ∀ t ∈ T R j, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale R j) →
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
          jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Hcol := fun S => normalizedColumn p (fun A => g (columnLog p X A)) S
        ‖truncatedSecondSource p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
          |Y| * ‖paperRadialFourier W 0‖ *
            (∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d Hcol G‖ ^ 2) +
          ∑ z : SecondRayIndex, ∑ R ∈ F.powerset, ∑ j : κ,
            (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
                X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
              (lengthScale R j * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
              ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) (b R j) (t₁,t₂,t₃)‖ *
                childGeometricMean p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
                  (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) (T R j)
                  (windows 5) (windows 6) (X₀ R j) (X₀ R j) (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_second_sector_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g g W hU hU A H hA hH hgA hgA ε hε decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  have hall := fun R j => htrans (D₀ R j) (E₀ R j) (V₀ R j) (X₀ R j) (K₀ R j) Y
    (hD₀ R j) (hE₀ R j) (hV₀ R j) (hX₀ R j) (hK₀ R j) hY
  choose b hb hbound using hall
  refine ⟨b,hb,?_⟩
  intro B C D F v₁ v₂ ε₁ ε₂ Ψ m X K label T lengthScale hv hCB hD hΨ hX hzero hL
    hz hud hue huv hkap hmap hT hnorm
  dsimp only
  apply (truncatedSecondSource_norm_le_zero_add_dyadic p hp hcop hg hinj hc hpr F Ψ m
    _ _ _ W Y K label).trans
  apply add_le_add
  · exact truncatedSecondZero_norm_le p hg hinj F Ψ m _ _ _ W Y K hzero
  · apply Finset.sum_le_sum
    intro z hz'
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    exact hbound R j B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondDyadicSector F K R label j) (T R j) X (lengthScale R j)
      (secondDyadicSector_subset F K R label j) hv hCB hD hΨ hX (hL R hR j)
      (hz R hR j) (hud R hR j) (hue R hR j) (huv R hR j) (hkap R hR j)
      (hmap R hR j) (hT R hR j) (hnorm R hR j)

end

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem postCommonSmoothPair_twisted_fixed_tests
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) t₁ * (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_kernel_twisted_profiles A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  obtain ⟨hid, hpoint, hint⟩ := hb θ₁ θ₂
  refine ⟨hpoint, ?_⟩
  intro F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V
    z ud ue uv kap X₁ X₂ R b (hid z ud ue uv kap)

end SecondPassArithmetic

namespace SecondPassIntegration

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem tupleSource_twisted_uniform_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ, (1 + R)^A * ‖(𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) t₁ * (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        Cₛ * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) * FirstPassCubeLabels.firstLogDensity J t₁ *
          FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ (s : Finset OldTuple) (T : Finset (Ideal O × O)) (b0 : Ideal O)
        (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ : ℝ),
        b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
        (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
        ‖tupleSourceSum p hp hcop hg s w label F Ψ₁ Ψ₂ m (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V z ud ue uv kap X₁ X₂ R‖ ≤
          (B * Cₐ * (lengthScale * Ideal.absNorm b0)^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, htrans⟩ := integrated_fixed_second_mode_transfer p hp hcop hg ε hε
  obtain ⟨Cₛ, hCₛ, hsep⟩ := postCommonSmoothPair_twisted_fixed_tests p hp hcop hg A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro R hR
  obtain ⟨b, hb⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  obtain ⟨hpoint, hid⟩ := hb θ₁ θ₂
  refine ⟨hpoint, ?_⟩
  intro s T b0 w B lengthScale label F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hb0 hB hL hv hm ht hn hw hl
  have hsource := tupleSource_eq_integratedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans s T b0 (tupleOuterWeight V w z ud ue uv kap) B lengthScale label F Ψ₁ Ψ₂ m
    (V 5) (V 6) X₁ X₂ (𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) b hb0 hB hL hv hm ht hn
  · intro q x hx
    rw [tupleOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact tupleOuterWeight_continuous V w z ud ue uv kap x
  · exact hl

end

open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

theorem exists_fixed_twisted_normalized_child_tests {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ (θ₁ θ₂ D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows
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
  intro θ₁ θ₂ D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  have htw₁ : ∀ s, frequencyTwist g₁ θ₁ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have htw₂ : ∀ s, frequencyTwist g₂ θ₂ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₁ : ∀ s, frequencyTwist A₁ (-θ₁) s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₂ : ∀ s, frequencyTwist A₂ θ₂ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hh := secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs
    (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂ windows
  dsimp only at hh
  rw [normalized_conjugate_frequencyTwist U hUc hUs,
    halfNormalization_twist U hUc hUs] at hh
  exact hh (hwo _ _ _ _ _ hz hud hue huv hkap)
    (fun a ha => hwt (frequencyTwist A₁ (-θ₁)) _ hsupp₁ hz 5 a ha)
    (fun a ha => hwt (frequencyTwist A₂ θ₂) _ hsupp₂ hz 6 a ha)

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassIntegration (tupleSourceSum tupleSource_twisted_uniform_transfer childGeometricMean)
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem actual_second_variable_sector_twisted_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (ε : ℝ) (hε : 0 < ε) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (windows : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hwindows : ∀ j x, windows j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧
      ∀ D₀ E₀ V₀ X₀ K Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ,
        (1 + Y*K/(D₀*E₀^2*V₀^2*X₀^2))^A * ‖(𝓕 (frequencyTwist A₁ θ₁)) t₁ * (𝓕 (frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
          Cₛ * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) * FirstPassCubeLabels.firstLogDensity J t₁ *
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
          (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) W windows D₀ E₀ V₀ X X₀ K Y‖ ≤
        (Bnd * Cₐ * (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 (frequencyTwist A₁ θ₁)) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, Cₛ, hCₛ, htrans⟩ :=
    tupleSource_twisted_uniform_transfer p hp hcop hg ε hε A₁ A₂ W windows M hM hwindows A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro D₀ E₀ V₀ X₀ K Y hD₀ hE₀ hV₀ hX₀ hK hY
  have hR : 0 < Y*K/(D₀*E₀^2*V₀^2*X₀^2) := by positivity
  obtain ⟨b, hb⟩ := htrans _ hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  obtain ⟨hpoint,hbound⟩ := hb θ₁ θ₂
  refine ⟨hpoint, ?_⟩
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
      (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) W windows z' ud' ue' uv' kap' X₀ X₀ (Y*K/(D₀*E₀^2*V₀^2*X₀^2)) =
      actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m
        (frequencyTwist A₁ θ₁) (frequencyTwist A₂ θ₂) W windows D₀ E₀ V₀ X X₀ K Y := by
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

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.TwistedProfiles -/

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
open JointLogSeparation
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (exists_fixed_twisted_normalized_child_tests elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem actualSecondRawVariableSector_twisted_profiles
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j t, windows j t ≠ 0 → |t| ≤ A+H+1) ∧
      ∀ (θ₁ θ₂ D E V₀ X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K →
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (w : SecondSupportData ι → ℂ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O) (X : SecondSupportData ι → ℝ),
        (∀ x ∈ s, 0 < X x) →
        (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p (X x) X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W X Y =
          actualSecondVariableSectorSource p hp hcop hg B v₁ v₂ ε₁ ε₂ s
            (fun x => w x * (X x : ℂ)⁻¹) F Ψ₁ Ψ₂ (m*r)
            (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows D E V₀ X X₀ K Y := by
  obtain ⟨A₁, A₂, windows, hwc, hws, hwb, hid⟩ :=
    exists_fixed_twisted_normalized_child_tests p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro θ₁ θ₂ D E V₀ X₀ K Y hD hE hV₀ hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r X hX hk hz hud hue huv hkap
  simp only [actualSecondRawVariableSector, actualSecondVariableSectorSource]
  apply Finset.sum_congr rfl
  intro x hx
  have heq := hid θ₁ θ₂ D E V₀ (X x) X₀ K Y hD hE hV₀ (hX x hx) hX₀ hK F x.overlap Ψ₁ Ψ₂ m r
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
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label firstLogDensity)
open SecondPassIntegration (childGeometricMean)
open JointLogSeparation

theorem actual_raw_twisted_sector_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      (∀ z ud ue uv kap : ℝ, ‖outerWindow windows z ud ue uv kap‖ ≤ Cw) ∧
      ∀ D E V₀ X₀ K Y : ℝ, 0 < D → 0 < E → 0 < V₀ → 0 < X₀ → 0 < K → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K/(D*E^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 (frequencyTwist A₁ (-θ₁))) t₁*(𝓕 (frequencyTwist A₂ θ₂)) t₂*b t₃‖ ≤
          Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (s : Finset (SecondSupportData ι)) (T : Finset (Ideal O × O))
        (w : SecondSupportData ι → ℂ) (Bnd lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r : O) (X : SecondSupportData ι → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) →
        (∀ x ∈ s, Disjoint x.common B) →
        (∀ x ∈ s, x.firstDivisor ⊆ x.common ∪ B) →
        (∀ x ∈ s, 0 < X x) → (∀ x ∈ s, x.frequency ≠ 0) →
        (∀ x ∈ s, |secondSectorZ p (X x) X₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D x| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E x| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ x| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K x| ≤ H) →
        0 ≤ Bnd → 0 ≤ lengthScale →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ x, secondSupportRow p x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x * (X x : ℂ)⁻¹‖ * ‖outerWindow windows
          (secondSectorZ p (X x) X₀ x) (secondSectorUd p D x) (secondSectorUe p E x)
          (secondSectorUv p V₀ x) (secondSectorKap p K x)‖ ≤ Bnd) →
        ‖actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W X Y‖ ≤
          (Bnd*Cₐ*(lengthScale*Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 (frequencyTwist A₁ (-θ₁))) (𝓕 (frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ (m*r) T (windows 5) (windows 6)
                X₀ X₀ (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ :=
    actualSecondRawVariableSector_twisted_profiles p hp hcop hg g₁ g₂ W A H hA hH hg₁ hg₂
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound windows hwc (fun j => (hws j).continuous)
  have hM : ∀ j : Fin 7, 0 ≤ (fun _ : Fin 7 => A+H+1) j := by intro j; dsimp; linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ :=
    actual_second_variable_sector_twisted_transfer p hp hcop hg hinj ε hε A₁ A₂ W windows
      (fun _ => A+H+1) hM hwb decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hwglobal,?_⟩
  intro D E V₀ X₀ K Y hD hE hV₀ hX₀ hK hY
  obtain ⟨b,hb⟩ := htrans D E V₀ X₀ K Y hD hE hV₀ hX₀ hK hY
  refine ⟨b,?_⟩
  intro θ₁ θ₂
  obtain ⟨hpoint,hbound⟩ := hb (-θ₁) θ₂
  refine ⟨?_,?_⟩
  · simpa only [norm_neg] using hpoint
  intro B v₁ v₂ ε₁ ε₂ s T w Bnd lengthScale F Ψ₁ Ψ₂ m r X hv hCB hdiv hX hk hz hud hue huv hkap
    hBnd hL hmap hT hnorm hw
  rw [hid θ₁ θ₂ D E V₀ X₀ K Y hD hE hV₀ hX₀ hK B v₁ v₂ ε₁ ε₂ s w F Ψ₁ Ψ₂ m r X
    hX hk hz hud hue huv hkap]
  exact hbound B v₁ v₂ ε₁ ε₂ s T (fun x => w x*(X x : ℂ)⁻¹) Bnd lengthScale F Ψ₁ Ψ₂ (m*r) X
    hv hCB hdiv hBnd hL hmap hT hnorm hw

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open FourierBridge (logPhase)
open SecondPassIntegration (conjugateProfile)

def firstCoreBaseProfile (g V : 𝓢(ℝ, ℂ)) (negative : Bool) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (if negative then conjugateProfile V else V) g

def firstCoreModeHeight (negative : Bool) (t : ℝ) : ℝ := if negative then t else -t

def firstCoreModeProfile (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (firstCoreBaseProfile g V negative) (firstCoreModeHeight negative t)

theorem firstCoreBaseProfile_apply (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (s : ℝ) :
    firstCoreBaseProfile g V negative s = g s * (if negative then star (V s) else V s) := by
  cases negative <;>
    simp only [firstCoreBaseProfile, Bool.false_eq_true, ite_false, ite_true,
      SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.hasTemperateGrowth _),
      smul_eq_mul, SecondPassIntegration.conjugateProfile_apply] <;> ring

lemma logPhase_neg_argument (t s : ℝ) : logPhase t (-s) = logPhase (-t) s := by
  unfold logPhase
  congr 1
  push_cast
  ring

theorem firstCoreModeProfile_apply (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ) :
    firstCoreModeProfile g V negative t s = g s *
      (if negative then star (V s * logPhase t (-s)) else V s * logPhase t (-s)) := by
  cases negative <;>
    simp only [firstCoreModeProfile, frequencyTwist_apply, firstCoreModeHeight,
      firstCoreBaseProfile_apply, Bool.false_eq_true, ite_false, ite_true,
      star_mul, logPhase_neg_argument, SecondPassIntegration.logPhase_conjugate, neg_neg] <;> ring

theorem firstCoreModeProfile_norm (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ) :
    ‖firstCoreModeProfile g V negative t s‖ = ‖g s‖ * ‖V s‖ := by
  rw [firstCoreModeProfile_apply]
  cases negative <;> simp [FourierBridge.logPhase_norm]

theorem firstCoreModeProfile_support (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t s : ℝ)
    (h : firstCoreModeProfile g V negative t s ≠ 0) : g s ≠ 0 ∧ V s ≠ 0 := by
  have hn : ‖g s‖ * ‖V s‖ ≠ 0 := by
    rw [← firstCoreModeProfile_norm g V negative t s]
    exact norm_ne_zero_iff.mpr h
  exact ⟨norm_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1,
    norm_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).2⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem firstCoreTest_eq_normalized_mode (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (t : ℝ)
    (D S : Finset ι) (hDS : Disjoint D S) (X : ℝ) (hX : 0 < X) :
    firstCoreTest (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X)
        negative t D S =
      (‖eisEmbedding (∏ i ∈ D, p i)‖ : ℂ)⁻¹ *
        normalizedColumn p (fun A => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) A)) S := by
  simp only [firstCoreTest, normalizedColumn,
    SecondPassIntegration.columnLog_extract_common p hp D S hDS X hX,
    Finset.prod_union hDS, map_mul, norm_mul, Complex.ofReal_mul,
    firstCoreModeProfile_apply]
  ring

theorem firstCoreInputRow_eq_mode_row
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z =
      (‖eisEmbedding (∏ i ∈ D, p i)‖ : ℂ)⁻¹ *
      inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) A))) (if negative then -z else z) := by
  unfold firstCoreInputRow inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hDS : Disjoint D S := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right
  simp only [secondInputCoefficient, firstCoreTest_eq_normalized_mode p hp g V negative t D S hDS X hX]
  ring

theorem firstCoreInputRow_mode_norm_sq
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) :
    ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun A => g (columnLog p X A))) V (columnLog p X) c d r t z‖ ^ 2 =
      (primeProductNorm p D)⁻¹ *
      ‖inputConjugateRow p hg (F\D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (normalizedColumn p (fun A => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) A))) (if negative then -z else z)‖ ^ 2 := by
  rw [firstCoreInputRow_eq_mode_row p hp hg F D B v ε₁ ε₂ negative χ Ψ m g V X hX c d r t z]
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_pow, inv_pow, primeProductNorm]

end SecondPassArithmetic

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical MatrixGroups Matrix Topology

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

abbrev UpperCoordinates := {p : ℂ × ℝ // 0 < p.2}

def coordinateSection (w : UpperCoordinates) : SL(2,ℂ) :=
  upperSection w.1.1 w.1.2 w.2

lemma continuous_coordinate_inverse_operator :
    Continuous (fun w : UpperCoordinates => rowOperator (coordinateSection w)⁻¹) := by
  have hroot : Continuous (fun w : UpperCoordinates => (Real.sqrt w.1.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_snd.comp continuous_subtype_val))
  have hne : ∀ w : UpperCoordinates, (Real.sqrt w.1.2 : ℂ) ≠ 0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  change Continuous (fun w : UpperCoordinates =>
    Matrix.vecMul u (Matrix.adjugate (coordinateSection w : Matrix (Fin 2) (Fin 2) ℂ)) i)
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,coordinateSection,upperSection,
    Matrix.SpecialLinearGroup.coe_mk,Matrix.adjugate_fin_two]
  fin_cases i
  · change Continuous (fun w : UpperCoordinates =>
      u 0 * (Real.sqrt w.1.2 : ℂ)⁻¹ + u 1 * (-0))
    exact (continuous_const.mul (hroot.inv₀ hne)).add
      (continuous_const.mul continuous_const)
  · change Continuous (fun w : UpperCoordinates =>
      u 0 * (-(w.1.1 / (Real.sqrt w.1.2 : ℂ))) + u 1 * (Real.sqrt w.1.2 : ℂ))
    exact (continuous_const.mul ((continuous_fst.comp continuous_subtype_val).div hroot hne).neg).add
      (continuous_const.mul hroot)

lemma continuous_coordinate_rowBound :
    Continuous (fun w : UpperCoordinates => rowBound (coordinateSection w)) :=
  continuous_const.mul (continuous_const.add continuous_coordinate_inverse_operator.norm)

lemma continuous_coordinate_summand (x : CuspCosets) :
    Continuous (fun p : UpperCoordinates × ℂ => summand (coordinateSection p.1) p.2 x) := by
  have hv : Continuous (fun p : UpperCoordinates × ℂ => p.1.1.2) :=
    (continuous_snd.comp continuous_subtype_val).comp continuous_fst
  have hz : Continuous (fun p : UpperCoordinates × ℂ => p.1.1.1) :=
    (continuous_fst.comp continuous_subtype_val).comp continuous_fst
  simp only [coordinateSection,summand_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    apply hv.div
    · unfold heightDenominator
      exact ((continuous_const.mul hz).add continuous_const).norm.pow 2 |>.add
        (continuous_const.mul (hv.pow 2))
    · intro p
      exact (heightDenominator_pos _ _ p.1.2 _ (embeddedRow_ne_zero x)).ne'
  · exact continuous_snd
  · intro p
    exact Complex.ofReal_mem_slitPlane.mpr (div_pos p.1.2
      (heightDenominator_pos _ _ p.1.2 _ (embeddedRow_ne_zero x)))

lemma coordinate_summable_majorant (C a b : ℝ) (hC : 0 < C)
    (ha : 2 < a) (hb : 2 < b) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x,0 ≤ M x) ∧
      ∀ p : UpperCoordinates × ℂ,
        rowBound (coordinateSection p.1) ≤ C → a ≤ p.2.re → p.2.re ≤ b →
        ∀ x, ‖summand (coordinateSection p.1) p.2 x‖ ≤ M x := by
  let weight (t : ℝ) (x : CuspCosets) :=
    C^(2*t)*‖rowCoordinates (cosetRow x)‖^(-(2*t))
  have hsum (t : ℝ) (ht : 2<t) : Summable (weight t) := by
    have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
      rowCoordinates_injective.comp cosetRow_injective
    exact ((summable_integer_four_rpow (2*t) (by linarith)).comp_injective hinj).mul_left _
  refine ⟨fun x => weight a x + weight b x,(hsum a ha).add (hsum b hb),?_,?_⟩
  · intro x
    dsimp [weight]
    positivity
  · intro p hbound hpa hpb x
    apply (norm_summand_strip (coordinateSection p.1) a b p.2 hpa hpb x).trans
    apply add_le_add
    · apply (norm_summand_bound (coordinateSection p.1) (a:ℂ) (by simpa using lt_trans (by norm_num) ha) x).trans
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (rowBound_pos _).le hbound (by simpa only [Complex.ofReal_re] using (show 0 ≤ 2*a by linarith))) (by positivity)
    · apply (norm_summand_bound (coordinateSection p.1) (b:ℂ) (by simpa using lt_trans (by norm_num) hb) x).trans
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (rowBound_pos _).le hbound (by simpa only [Complex.ofReal_re] using (show 0 ≤ 2*b by linarith))) (by positivity)

theorem coordinate_eisenstein_continuousAt (p : UpperCoordinates × ℂ) (hp : 2 < p.2.re) :
    ContinuousAt (fun q : UpperCoordinates × ℂ => eisenstein (coordinateSection q.1) q.2) p := by
  let a : ℝ := (2+p.2.re)/2
  let b : ℝ := p.2.re+1
  let C : ℝ := rowBound (coordinateSection p.1)+1
  let region : Set (UpperCoordinates × ℂ) := {q |
    rowBound (coordinateSection q.1) < C ∧ a < q.2.re ∧ q.2.re < b}
  have ha : 2<a := by dsimp [a]; linarith
  have hb : 2<b := by dsimp [b]; linarith
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection p.1)]
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C a b hC ha hb
  have hopen : IsOpen region := by
    exact (isOpen_lt (continuous_coordinate_rowBound.comp continuous_fst) continuous_const).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)).inter
        (isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const))
  have hmem : p ∈ region := by
    dsimp [region,a,b,C]
    constructor
    · linarith
    · constructor <;> linarith
  have hcont : ContinuousOn (fun q : UpperCoordinates × ℂ =>
      ∑' x : CuspCosets, summand (coordinateSection q.1) q.2 x) region := by
    apply continuousOn_tsum (fun x => (continuous_coordinate_summand x).continuousOn) hM
    intro x q hq
    exact hbound q hq.1.le hq.2.1.le hq.2.2.le x
  exact (hcont p hmem).continuousAt (hopen.mem_nhds hmem)

theorem coordinate_eisenstein_tendstoUniformlyOn (C a b : ℝ) (hC : 0<C)
    (ha : 2<a) (hb : 2<b) :
    TendstoUniformlyOn
      (fun f : Finset CuspCosets => fun p : UpperCoordinates × ℂ =>
        ∑ x ∈ f, summand (coordinateSection p.1) p.2 x)
      (fun p => eisenstein (coordinateSection p.1) p.2) atTop
      {p | rowBound (coordinateSection p.1) ≤ C ∧ a ≤ p.2.re ∧ p.2.re ≤ b} := by
  obtain ⟨M,hM,_,hbound⟩ := coordinate_summable_majorant C a b hC ha hb
  exact tendstoUniformlyOn_tsum hM (fun x p hp => hbound p hp.1 hp.2.1 hp.2.2 x)

theorem coordinate_eisenstein_continuousOn :
    ContinuousOn (fun p : UpperCoordinates × ℂ =>
      eisenstein (coordinateSection p.1) p.2) {p | 2 < p.2.re} :=
  fun p hp => (coordinate_eisenstein_continuousAt p hp).continuousWithinAt

theorem upperEisenstein_joint_continuousAt (p : UpperCoordinates × ℂ)
    (hp : 2 < p.2.re) :
    ContinuousAt (fun q : UpperCoordinates × ℂ =>
      upperEisenstein q.1.1.1 q.1.1.2 q.1.2 q.2) p :=
  coordinate_eisenstein_continuousAt p hp

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

def logRatioPower (s : ℂ) (v q : ℝ) : ℂ :=
  Complex.exp (s * ((Real.log v - Real.log q : ℝ) : ℂ))

lemma logRatioPower_eq_cpow (s : ℂ) {v q : ℝ} (hv : 0<v) (hq : 0<q) :
    logRatioPower s v q = ((v/q : ℝ):ℂ)^s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hv hq).ne'),
    ← Complex.ofReal_log (div_pos hv hq).le, Real.log_div hv.ne' hq.ne']
  unfold logRatioPower
  congr 1
  ring

lemma hasDerivAt_logRatioPower (s : ℂ) {f g : ℝ → ℝ} {x f' g' : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (fun t => logRatioPower s (f t) (g t))
      (logRatioPower s (f x) (g x) * s * ((f'/f x-g'/g x : ℝ):ℂ)) x := by
  convert (((hf.log hf0).sub (hg.log hg0)).ofReal_comp.const_mul s).cexp using 1 <;>
    dsimp [logRatioPower] ; ring

lemma hasDerivAt_deriv_logRatioPower (s : ℂ) (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t, HasDerivAt f (df t) t) (hg : ∀t, HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (deriv (fun t => logRatioPower s (f t) (g t)))
      (logRatioPower s (f x) (g x) *
        (s^2 * ((df x/f x-dg x/g x : ℝ):ℂ)^2 +
         s * (((ddf*f x-df x*df x)/(f x)^2 -
           (ddg*g x-dg x*dg x)/(g x)^2 : ℝ):ℂ))) x := by
  have hnear : ∀ᶠ t in 𝓝 x, f t ≠ 0 ∧ g t ≠ 0 :=
    ((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)
  have heq : (deriv (fun t => logRatioPower s (f t) (g t))) =ᶠ[𝓝 x]
      (fun t => logRatioPower s (f t) (g t) * s * ((df t/f t-dg t/g t : ℝ):ℂ)) := by
    filter_upwards [hnear] with t ht
    exact (hasDerivAt_logRatioPower s (hf t) (hg t) ht.1 ht.2).deriv
  have hfirst := hasDerivAt_logRatioPower s (hf x) (hg x) hf0 hg0
  have hsecond := ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).ofReal_comp
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (hfirst.mul_const s).mul hsecond using 1 ;
    simp only [Pi.sub_apply,Pi.div_apply] ; ring

def quadraticHeightDenominator (A B C D x y v : ℝ) : ℝ :=
  A*(x^2+y^2+v^2)+2*(B*x+C*y)+D

lemma quadraticHeightDenominator_hasDerivAt_x (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D t y v)
      (2*(A*x+B)) x := by
  convert (((((hasDerivAt_id x).pow 2).add_const (y^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id x).const_mul B).add_const (C*y)).const_mul 2) |>.add_const D using 1 <;>
    dsimp [quadraticHeightDenominator] ; ring

lemma quadraticHeightDenominator_hasDerivAt_y (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x t v)
      (2*(A*y+C)) y := by
  convert (((((hasDerivAt_id y).pow 2).const_add (x^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id y).const_mul C).const_add (B*x)).const_mul 2) |>.add_const D using 1 <;>
    dsimp [quadraticHeightDenominator] ; ring

lemma quadraticHeightDenominator_hasDerivAt_v (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x y t)
      (2*A*v) v := by
  convert ((((hasDerivAt_id v).pow 2).const_add (x^2+y^2)).const_mul A).add_const
    (2*(B*x+C*y)+D) using 1 <;> dsimp [quadraticHeightDenominator] <;> ring_nf

def spatialHeightPower (s : ℂ) (A B C D x y v : ℝ) : ℂ :=
  logRatioPower s v (quadraticHeightDenominator A B C D x y v)

def heightLogDx (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*x+B)/quadraticHeightDenominator A B C D x y v)
def heightLogDy (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*y+C)/quadraticHeightDenominator A B C D x y v)
def heightLogDv (A B C D x y v : ℝ) : ℝ :=
  1/v - 2*A*v/quadraticHeightDenominator A B C D x y v

def heightLogDxx (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*x+B))*(2*(A*x+B)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDyy (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*y+C))*(2*(A*y+C)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDvv (A B C D x y v : ℝ) : ℝ :=
  -(1/v^2) - ((2*A*quadraticHeightDenominator A B C D x y v -
    (2*A*v)*(2*A*v))/(quadraticHeightDenominator A B C D x y v)^2)

lemma deriv_spatialHeightPower_v (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (spatialHeightPower s A B C D x y) v =
      spatialHeightPower s A B C D x y v * s * (heightLogDv A B C D x y v : ℂ) := by
  exact (hasDerivAt_logRatioPower s (hasDerivAt_id v)
    (quadraticHeightDenominator_hasDerivAt_v A B C D x y v) hv hq).deriv

lemma deriv2_spatialHeightPower_x (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (fun t => spatialHeightPower s A B C D t y v)) x =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDx A B C D x y v : ℂ)^2 +
          s*(heightLogDxx A B C D x y v : ℂ)) := by
  have h := hasDerivAt_deriv_logRatioPower s (fun _ => v)
    (fun t => quadraticHeightDenominator A B C D t y v) (fun _ => 0)
    (fun t => 2*(A*t+B)) x 0 (2*A)
    (fun t => hasDerivAt_const t v)
    (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t y v)
    (hasDerivAt_const x 0) (by simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul A |>.add_const B).const_mul 2)
    hv hq
  simpa only [spatialHeightPower,heightLogDx,heightLogDxx,zero_div,zero_sub,zero_mul,sub_zero] using h.deriv

lemma deriv2_spatialHeightPower_y (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (fun t => spatialHeightPower s A B C D x t v)) y =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDy A B C D x y v : ℂ)^2 +
          s*(heightLogDyy A B C D x y v : ℂ)) := by
  have h := hasDerivAt_deriv_logRatioPower s (fun _ => v)
    (fun t => quadraticHeightDenominator A B C D x t v) (fun _ => 0)
    (fun t => 2*(A*t+C)) y 0 (2*A)
    (fun t => hasDerivAt_const t v)
    (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D x t v)
    (hasDerivAt_const y 0) (by simpa only [id_eq,mul_one] using ((hasDerivAt_id y).const_mul A |>.add_const C).const_mul 2)
    hv hq
  simpa only [spatialHeightPower,heightLogDy,heightLogDyy,zero_div,zero_sub,zero_mul,sub_zero] using h.deriv

lemma deriv2_spatialHeightPower_v (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (spatialHeightPower s A B C D x y)) v =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDv A B C D x y v : ℂ)^2 +
          s*(heightLogDvv A B C D x y v : ℂ)) := by
  change deriv (deriv (fun t => logRatioPower s t
    (quadraticHeightDenominator A B C D x y t))) v = _
  have h := hasDerivAt_deriv_logRatioPower s (fun t => t)
    (fun t => quadraticHeightDenominator A B C D x y t) (fun _ => 1)
    (fun t => 2*A*t) v 0 (2*A)
    (fun t => hasDerivAt_id t)
    (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D x y t)
    (hasDerivAt_const v 1) (by simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (2*A))
    hv hq
  simpa only [spatialHeightPower,heightLogDv,heightLogDvv,zero_mul,zero_sub,one_mul,neg_div] using h.deriv

lemma quadraticHeight_gradient_square (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) :
    (A*x+B)^2 + (A*y+C)^2 + (A*v)^2 =
      A*quadraticHeightDenominator A B C D x y v := by
  unfold quadraticHeightDenominator
  nlinarith [hrel]

lemma heightLog_eikonal (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * ((heightLogDx A B C D x y v)^2 +
      (heightLogDy A B C D x y v)^2 + (heightLogDv A B C D x y v)^2) = 1 := by
  calc
    _ = 1 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDx heightLogDy heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = 1 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

lemma heightLog_laplacian (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * (heightLogDxx A B C D x y v +
      heightLogDyy A B C D x y v + heightLogDvv A B C D x y v) -
      v*heightLogDv A B C D x y v = -2 := by
  calc
    _ = -2 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDxx heightLogDyy heightLogDvv heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = -2 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

def hyperbolicLaplacian (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2 * (deriv (deriv (fun t => f t y v)) x +
    deriv (deriv (fun t => f x t v)) y + deriv (deriv (f x y)) v) -
    (v:ℂ)*deriv (f x y) v

theorem spatialHeightPower_eigenfunction (s : ℂ) (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    hyperbolicLaplacian (spatialHeightPower s A B C D) x y v =
      s*(s-2)*spatialHeightPower s A B C D x y v := by
  have he : (v:ℂ)^2 * ((heightLogDx A B C D x y v : ℂ)^2 +
      (heightLogDy A B C D x y v : ℂ)^2 + (heightLogDv A B C D x y v : ℂ)^2) = 1 := by
    exact_mod_cast heightLog_eikonal A B C D x y v hrel hv hq
  have hl : (v:ℂ)^2 * ((heightLogDxx A B C D x y v : ℂ) +
      (heightLogDyy A B C D x y v : ℂ) + (heightLogDvv A B C D x y v : ℂ)) -
      (v:ℂ)*(heightLogDv A B C D x y v : ℂ) = -2 := by
    exact_mod_cast heightLog_laplacian A B C D x y v hrel hv hq
  unfold hyperbolicLaplacian
  rw [deriv2_spatialHeightPower_x s A B C D x y v hv hq,
    deriv2_spatialHeightPower_y s A B C D x y v hv hq,
    deriv2_spatialHeightPower_v s A B C D x y v hv hq,
    deriv_spatialHeightPower_v s A B C D x y v hv hq]
  calc
    _ = spatialHeightPower s A B C D x y v *
        (s^2*((v:ℂ)^2*((heightLogDx A B C D x y v : ℂ)^2 +
          (heightLogDy A B C D x y v : ℂ)^2 + (heightLogDv A B C D x y v : ℂ)^2)) +
        s*((v:ℂ)^2*((heightLogDxx A B C D x y v : ℂ) +
          (heightLogDyy A B C D x y v : ℂ) + (heightLogDvv A B C D x y v : ℂ)) -
          (v:ℂ)*(heightLogDv A B C D x y v : ℂ))) := by ring
    _ = _ := by rw [he,hl]; ring

lemma complex_row_quadratic_relation (c d : ℂ) :
    Complex.normSq c * Complex.normSq d = (c*star d).re^2 + (-(c*star d).im)^2 := by
  simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

lemma heightDenominator_eq_quadratic (u : Fin 2 → ℂ) (x y v : ℝ) :
    heightDenominator ((x:ℂ)+(y:ℂ)*Complex.I) v u =
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  unfold heightDenominator quadraticHeightDenominator
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

def actualHeightPower (s : ℂ) (u : Fin 2 → ℂ) (x y v : ℝ) : ℂ :=
  ((transformedHeight ((x:ℂ)+(y:ℂ)*Complex.I) v u : ℝ) : ℂ)^s

lemma actualHeightPower_eq_spatial (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (x y v : ℝ) (hv : 0<v) :
    actualHeightPower s u x y v =
      spatialHeightPower s (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  rw [actualHeightPower,spatialHeightPower,logRatioPower_eq_cpow s hv]
  · rw [transformedHeight,heightDenominator_eq_quadratic]
  · rw [← heightDenominator_eq_quadratic]
    exact heightDenominator_pos _ _ hv u hu

theorem actualHeightPower_eigenfunction (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (x y v : ℝ) (hv : 0<v) :
    hyperbolicLaplacian (actualHeightPower s u) x y v =
      s*(s-2)*actualHeightPower s u x y v := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have heq (x' y' v' : ℝ) (hv' : 0<v') :
      actualHeightPower s u x' y' v' = spatialHeightPower s A B C D x' y' v' :=
    actualHeightPower_eq_spatial s u hu x' y' v' hv'
  have hxeq : (fun t => actualHeightPower s u t y v) =
      (fun t => spatialHeightPower s A B C D t y v) := funext fun t => heq t y v hv
  have hyeq : (fun t => actualHeightPower s u x t v) =
      (fun t => spatialHeightPower s A B C D x t v) := funext fun t => heq x t v hv
  have hveq : actualHeightPower s u x y =ᶠ[𝓝 v] spatialHeightPower s A B C D x y := by
    filter_upwards [isOpen_Ioi.mem_nhds (show v ∈ Set.Ioi 0 from hv)] with t ht
    exact heq x y t ht
  have hq : quadraticHeightDenominator A B C D x y v≠0 := by
    rw [← heightDenominator_eq_quadratic]
    exact (heightDenominator_pos _ _ hv u hu).ne'
  rw [heq x y v hv]
  convert spatialHeightPower_eigenfunction s A B C D x y v
    (complex_row_quadratic_relation (u 0) (u 1)) hv.ne' hq using 1
  unfold hyperbolicLaplacian
  rw [hxeq,hyeq,hveq.deriv_eq,hveq.deriv.deriv_eq]

lemma hyperbolicLaplacian_const_mul (c : ℂ) (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) :
    hyperbolicLaplacian (fun x y v => c*f x y v) x y v =
      c*hyperbolicLaplacian f x y v := by
  unfold hyperbolicLaplacian
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

theorem eisenstein_summand_eigenfunction (s : ℂ) (r : CuspCosets) (x y v : ℝ) (hv : 0<v) :
    hyperbolicLaplacian
      (fun x y v => (cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v) x y v =
      s*(s-2)*((cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v) := by
  rw [hyperbolicLaplacian_const_mul,
    actualHeightPower_eigenfunction s (embeddedRow r) (embeddedRow_ne_zero r) x y v hv]
  ring

lemma eigenfunction_summand_eq_actual_series (s : ℂ) (r : CuspCosets)
    (x y v : ℝ) (hv : 0<v) :
    (cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v =
      summand (upperSection ((x:ℂ)+(y:ℂ)*Complex.I) v hv) s r := by
  rw [summand_upperSection]
  rfl

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Fourier.LogDensity -/

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

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation
open FirstPassCubeLabels

def tripleLogDensity (J : ℕ) (t : Frequency) : ℝ :=
  firstLogDensity J t.1 * (firstLogDensity J t.2.1 * firstLogDensity J t.2.2)

lemma tripleLogDensity_integrable (J : ℕ) : Integrable (tripleLogDensity J) :=
  (firstLogDensity_integrable J).mul_prod
    ((firstLogDensity_integrable J).mul_prod (firstLogDensity_integrable J))

lemma tripleLogDensity_nonneg (J : ℕ) (t : Frequency) : 0 ≤ tripleLogDensity J t :=
  mul_nonneg (firstLogDensity_nonneg _ _) (mul_nonneg
    (firstLogDensity_nonneg _ _) (firstLogDensity_nonneg _ _))

lemma tripleLogDensity_bounded_integrable (J : ℕ) (G : Frequency → ℝ)
    (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) :
    Integrable (fun t => tripleLogDensity J t * G t) :=
  (tripleLogDensity_integrable J).mul_bdd hG.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleLogDensity_slice_integrable (J : ℕ) (G : Frequency → ℝ)
    (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) (x : ℝ) :
    Integrable (fun yz : ℝ × ℝ => tripleLogDensity J (x,yz) * G (x,yz)) := by
  have hc : Integrable (fun yz : ℝ × ℝ =>
      firstLogDensity J x * (firstLogDensity J yz.1 * firstLogDensity J yz.2)) :=
    ((firstLogDensity_integrable J).mul_prod (firstLogDensity_integrable J)).const_mul _
  apply hc.mul_bdd
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

theorem triple_coefficient_density_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ)
    (G : Frequency → ℝ) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (M : ℝ) (hM : ∀ t, G t ≤ M) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ,
      S * ‖b₁ t₁*b₂ t₂*b₃ t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ * G (t₁,t₂,t₃)) ≤
    C * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleLogDensity J (t₁,t₂,t₃) * G (t₁,t₂,t₃)) := by
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    simpa only [Real.norm_of_nonneg (hG0 t)] using hM t
  have hc := tripleCoefficient_norm_bounded_integrable b₁ b₂ b₃ G hG M hGb
  have hd := tripleLogDensity_bounded_integrable J G hG M hGb
  rw [nested_eq_integral _ hc (tripleCoefficient_norm_slice_integrable b₁ b₂ b₃ G hG M hGb),
    nested_eq_integral _ hd (tripleLogDensity_slice_integrable J G hG M hGb),
    ← integral_const_mul, ← integral_const_mul]
  apply integral_mono (hc.const_mul S) (hd.const_mul C)
  intro t
  have hh := mul_le_mul_of_nonneg_right (hpoint t.1 t.2.1 t.2.2) (hG0 t)
  simpa only [tripleCoefficient, tripleLogDensity, mul_assoc] using hh

end JointLogSeparation

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation

def densityChildEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (J : ℕ) : ℝ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    tripleLogDensity J (t₁,t₂,t₃) *
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)

theorem child_coefficient_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hpoint : ∀ t₁ t₂ t₃ : ℝ, S * ‖b₁ t₁*b₂ t₂*b₃ t₃‖ ≤
      C * FirstPassCubeLabels.firstLogDensity J t₁ *
        FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) :
    S * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
        childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) ≤
    C * densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  exact triple_coefficient_density_bound b₁ b₂ b₃ J G hG hG0 M hM S C hpoint

end SecondPassIntegration

namespace JointLogSeparation
open FirstPassCubeLabels

lemma one_add_norm_sub_le (x y : ℝ) :
    1 + ‖x-y‖ ≤ (1+‖x‖)*(1+‖y‖) := by
  have hn := norm_sub_le x y
  have hprod := mul_nonneg (norm_nonneg x) (norm_nonneg y)
  nlinarith

theorem difference_height_weight_le (x y z : ℝ) (J : ℕ) :
    (1+‖x-z‖)^J * (1+‖y-z‖)^J ≤
      (1+‖x‖)^(2*J) * (1+‖y‖)^(2*J) * (1+‖z‖)^(2*J) := by
  have hx := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖x-z‖) (one_add_norm_sub_le x z) J
  have hy := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖y-z‖) (one_add_norm_sub_le y z) J
  calc
    _ ≤ ((1+‖x‖)*(1+‖z‖))^J * ((1+‖y‖)*(1+‖z‖))^J :=
      mul_le_mul hx hy (by positivity) (by positivity)
    _ = (1+‖x‖)^J * (1+‖y‖)^J * (1+‖z‖)^(2*J) := by
      rw [mul_pow, mul_pow, two_mul, pow_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1 ≤ 1+‖x‖) (by omega : J ≤ 2*J))
        (pow_le_pow_right₀ (by linarith [norm_nonneg y] : 1 ≤ 1+‖y‖) (by omega : J ≤ 2*J))
        (by positivity) (by positivity)

theorem triple_density_polynomial_bound (G : Frequency → ℝ)
    (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t) (M : ℝ) (hM : ∀ t, G t ≤ M)
    (J : ℕ) (D : ℝ)
    (hbound : ∀ t, G t ≤ D * (1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, tripleLogDensity J (x,y,z) * G (x,y,z)) ≤
      D * (∫ t : ℝ, firstLogDensity 0 t)^3 := by
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by
    simpa only [Real.norm_of_nonneg (hG0 t)] using hM t
  have hi := tripleLogDensity_bounded_integrable J G hG M hGb
  rw [nested_eq_integral _ hi (tripleLogDensity_slice_integrable J G hG M hGb)]
  have hh : ∀ t : Frequency, tripleLogDensity J t * G t ≤ D * tripleLogDensity 0 t := by
    intro t
    calc
      _ ≤ tripleLogDensity J t *
          (D * (1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) :=
        mul_le_mul_of_nonneg_left (hbound t) (tripleLogDensity_nonneg J t)
      _ = _ := by
        dsimp only [tripleLogDensity]
        rw [← density_weight_identity J t.1, ← density_weight_identity J t.2.1,
          ← density_weight_identity J t.2.2]
        ring
  calc
    _ ≤ ∫ t : Frequency, D * tripleLogDensity 0 t :=
      integral_mono hi ((tripleLogDensity_integrable 0).const_mul D) hh
    _ = D * (∫ t : Frequency, tripleLogDensity 0 t) := integral_const_mul _ _
    _ = _ := by
      have hslice (x : ℝ) : Integrable (fun yz : ℝ × ℝ => tripleLogDensity 0 (x,yz)) := by
        simpa only [tripleLogDensity, Measure.volume_eq_prod] using
          ((firstLogDensity_integrable 0).mul_prod (firstLogDensity_integrable 0)).const_mul
            (firstLogDensity 0 x)
      rw [← nested_eq_integral _ (tripleLogDensity_integrable 0) hslice]
      simp only [tripleLogDensity, integral_const_mul, integral_mul_const]
      ring

end JointLogSeparation
end

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem ideals_coprime_of_relprime (A B : Ideal O) (h : IsRelPrime A B) : IsCoprime A B := by
  apply Ideal.isCoprime_iff_gcd.mpr
  simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp (h (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B))

theorem squarefree_quotient_gcd_coprime (B G : Ideal O) (hB : Squarefree B) :
    IsCoprime (idealQuotient (gcd B G) B) G := by
  let D := gcd B G
  have hDB : D ∣ B := GCDMonoid.gcd_dvd_left B G
  have hDG : D ∣ G := GCDMonoid.gcd_dvd_right B G
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hB.ne_zero hDB
  have hc : IsCoprime (idealQuotient D B) (idealQuotient D G) :=
    (gcd_eq_iff_quotient_coprime D B G hD hDB hDG).mp rfl
  have hmul : Squarefree (D * idealQuotient D B) := by rw [idealQuotient_mul hDB]; exact hB
  have hdq : IsCoprime D (idealQuotient D B) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hmul).1
  have hh := hdq.symm.mul_right hc
  rw [idealQuotient_mul hDG] at hh
  exact hh

theorem gcd_mul_of_coprime_divisor (D H G : Ideal O) (hDG : D ∣ G) (hHG : IsCoprime H G) :
    gcd (D * H) G = D := by
  have hleft : D ∣ gcd (D * H) G := GCDMonoid.dvd_gcd (dvd_mul_right D H) hDG
  have hcop : IsCoprime (gcd (D * H) G) H :=
    (hHG.mono (dvd_refl H) (GCDMonoid.gcd_dvd_right (D * H) G)).symm
  have hright : gcd (D * H) G ∣ D := hcop.dvd_of_dvd_mul_right (GCDMonoid.gcd_dvd_left _ _)
  exact associated_iff_eq.mp (associated_of_dvd_dvd hright hleft)

def squarefreeGcdEquiv (G : Ideal O) (hG : Squarefree G) :
    {B : Ideal O // Squarefree B} ≃
      (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G} where
  toFun B := (⟨gcd B.val G, (mem_idealDivisors hG.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)⟩,
    ⟨idealQuotient (gcd B.val G) B.val,
      B.property.squarefree_of_dvd (idealQuotient_dvd (GCDMonoid.gcd_dvd_left _ _)),
      squarefree_quotient_gcd_coprime B.val G B.property⟩)
  invFun p := ⟨p.1.val * p.2.val, squarefree_mul_iff.mpr
    ⟨(p.2.property.2.mono (dvd_refl _) ((mem_idealDivisors hG.ne_zero).mp p.1.property)).symm.isRelPrime,
      hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp p.1.property), p.2.property.1⟩⟩
  left_inv B := Subtype.ext (idealQuotient_mul (GCDMonoid.gcd_dvd_left B.val G))
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2
    · apply Subtype.ext
      change idealQuotient (gcd (p.1.val * p.2.val) G) (p.1.val * p.2.val) = p.2.val
      rw [gcd_mul_of_coprime_divisor p.1.val p.2.val G
        ((mem_idealDivisors hG.ne_zero).mp p.1.property) p.2.property.2]
      have hD : p.1.val ≠ 0 := ne_zero_of_dvd_ne_zero hG.ne_zero
        ((mem_idealDivisors hG.ne_zero).mp p.1.property)
      exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right p.1.val p.2.val))

theorem squarefree_gcd_tsum (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Squarefree B}, f B.val) =
      ∑' p : (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        f (p.1.val * p.2.val) :=
  ((squarefreeGcdEquiv G hG).symm.tsum_eq (fun B => f B.val)).symm

def coprimeSquarefreeRange (G : Ideal O) (K : ℝ) : Finset (Ideal O) :=
  (squarefreeIdealRange K).filter (fun H => IsCoprime H G)

theorem squarefree_cutoff_summable (K : ℝ) (f : Ideal O → ℂ) :
    Summable (fun B : {B : Ideal O // Squarefree B} =>
      if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) := by
  let e : squarefreeIdealRange K → {B : Ideal O // Squarefree B} :=
    fun B => ⟨B.val, (mem_squarefreeIdealRange.mp B.property).1⟩
  apply summable_of_hasFiniteSupport
  apply (Set.finite_range e).subset
  intro B hB
  have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
    by_contra hn
    exact hB (ite_eq_right hn)
  exact ⟨⟨B.val, mem_squarefreeIdealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩

theorem norm_le_mul_of_ne_zero (D H : Ideal O) (hD : D ≠ 0) :
    Ideal.absNorm H ≤ Ideal.absNorm (D * H) := by
  have hD1 : 1 ≤ Ideal.absNorm D := Nat.one_le_iff_ne_zero.mpr
    (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  simpa only [one_mul, map_mul] using Nat.mul_le_mul_right (Ideal.absNorm H) hD1

theorem coprime_squarefree_cutoff (G D : Ideal O) (hD : D ≠ 0) (K : ℝ) (f : Ideal O → ℂ) :
    (∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
      if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0) =
      ∑ H : coprimeSquarefreeRange G K,
        if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0 := by
  let e : coprimeSquarefreeRange G K → {H : Ideal O // Squarefree H ∧ IsCoprime H G} :=
    fun H => ⟨H.val, (mem_squarefreeIdealRange.mp (Finset.mem_filter.mp H.property).1).1,
      (Finset.mem_filter.mp H.property).2⟩
  have he : Function.Injective e := by
    intro H J h
    apply Subtype.ext
    exact congrArg (fun C : {H : Ideal O // Squarefree H ∧ IsCoprime H G} => C.val) h
  let F : {H : Ideal O // Squarefree H ∧ IsCoprime H G} → ℂ := fun H =>
    if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then f (D * H.val) else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro H hH
    have hN : (Ideal.absNorm (D * H.val) : ℝ) ≤ K := by
      by_contra hn
      exact hH (ite_eq_right hn)
    have hHN : (Ideal.absNorm H.val : ℝ) ≤ K :=
      (Nat.cast_le.mpr (norm_le_mul_of_ne_zero D H.val hD)).trans hN
    exact ⟨⟨H.val, Finset.mem_filter.mpr
      ⟨mem_squarefreeIdealRange.mpr ⟨H.property.1, hHN⟩, H.property.2⟩⟩, Subtype.ext rfl⟩
  simpa only [tsum_fintype, F, e] using (he.tsum_eq hs).symm

theorem squarefree_gcd_finite_sum (G : Ideal O) (hG : Squarefree G) (K : ℝ) (f : Ideal O → ℂ) :
    (∑ B : squarefreeIdealRange K, f B.val) =
      ∑ D : idealDivisors G, ∑ H : coprimeSquarefreeRange G K,
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0 := by
  let F : {B : Ideal O // Squarefree B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs := (squarefreeGcdEquiv G hG).symm.summable_iff.mpr (squarefree_cutoff_summable K f)
  have he := ((squarefreeGcdEquiv G hG).symm.tsum_eq F).symm
  calc
    _ = ∑' B : {B : Ideal O // Squarefree B}, F B := (tsum_squarefree_norm_cutoff K f).symm
    _ = ∑' p : (idealDivisors G) × {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        F ((squarefreeGcdEquiv G hG).symm p) := he
    _ = ∑' D : idealDivisors G, ∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        F ((squarefreeGcdEquiv G hG).symm (D, H)) := hs.tsum_prod
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro D _
      change (∑' H : {H : Ideal O // Squarefree H ∧ IsCoprime H G},
        if (Ideal.absNorm (D.val * H.val) : ℝ) ≤ K then f (D.val * H.val) else 0) = _
      exact coprime_squarefree_cutoff G D.val
        (ne_zero_of_dvd_ne_zero hG.ne_zero ((mem_idealDivisors hG.ne_zero).mp D.property)) K f

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

theorem canonical_quadraticRow_one (I : Ideal O) (hI : Admissible I) : quadraticRow I 1 = 1 := by
  rw [quadraticRow, dite_eq_left hI]
  simp [idealSexticRow, finiteSquarefreeRow]

theorem unrestrictedPairCharacter_one (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : unrestrictedPairCharacter I J 1 = 1 := by
  have h := unrestrictedPairCharacter_span I J hI hJ hray 1
  simpa only [Ideal.span_singleton_one, canonical_quadraticRow_one I hI,
    canonical_quadraticRow_one J hJ, one_mul, Ideal.one_eq_top] using h

def normalizedIdealPair (I J lengthScale : Ideal O) : ℂ :=
  unrestrictedPairCharacter I J lengthScale / (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ)

theorem normalizedIdealPair_mul (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (A B : Ideal O) :
    normalizedIdealPair I J (A * B) = normalizedIdealPair I J A * normalizedIdealPair I J B := by
  simp only [normalizedIdealPair, unrestrictedPairCharacter_mul I J hI hJ hray,
    map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, div_mul_div_comm]

def normalizedIdealPairHom (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) : Ideal O →* ℂ where
  toFun := normalizedIdealPair I J
  map_one' := by
    rw [normalizedIdealPair, unrestrictedPairCharacter_one I J hI hJ hray, map_one]
    norm_num
  map_mul' := normalizedIdealPair_mul I J hI hJ hray

theorem normalizedIdealPair_square (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (lengthScale : Ideal O) :
    normalizedIdealPair I J lengthScale ^ 2 =
      (idealZeroMask I (idealGenerator lengthScale) * idealZeroMask J (idealGenerator lengthScale)) / (Ideal.absNorm lengthScale : ℂ) := by
  have hc : unrestrictedPairCharacter I J lengthScale ^ 2 =
      idealZeroMask I (idealGenerator lengthScale) * idealZeroMask J (idealGenerator lengthScale) := by
    unfold unrestrictedPairCharacter
    calc
      _ = (quadraticRow I (idealGenerator lengthScale) * quadraticRow I (idealGenerator lengthScale)) *
        (quadraticRow J (idealGenerator lengthScale) * quadraticRow J (idealGenerator lengthScale)) := by ring
      _ = _ := by rw [canonical_quadraticRow_squared I hI, canonical_quadraticRow_squared J hJ]
  have hn : (Real.sqrt (Ideal.absNorm lengthScale : ℝ) : ℂ) ^ 2 = (Ideal.absNorm lengthScale : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Ideal.absNorm lengthScale) : (0 : ℝ) ≤ _)
  rw [normalizedIdealPair, div_pow, hc, hn]

theorem squarefree_divisor_sum_eq_support (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors G, f D) =
      ∑ S ∈ (IdealMobiusDivisorSum.primeSupport G).powerset, f (∏ P ∈ S, P) := by
  have hfilter : (idealDivisors G).filter Squarefree = idealDivisors G := by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact hG.squarefree_of_dvd ((mem_idealDivisors hG.ne_zero).mp hD)
  rw [← hfilter, squarefree_divisors_eq_image G hG.ne_zero, Finset.sum_image]
  intro S hS T hT hST
  exact support_product_injective (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hST

theorem normalizedIdealPair_double_divisor
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (hray : columnRay I = columnRay J)
    (G : Ideal O) (hG : Squarefree G) :
    (∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
      (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J (D * E)) =
      ∏ P ∈ IdealMobiusDivisorSum.primeSupport G,
        (1 - (idealZeroMask I (idealGenerator P) * idealZeroMask J (idealGenerator P)) /
          (Ideal.absNorm P : ℂ)) := by
  rw [squarefree_divisor_sum_eq_support G hG]
  simp_rw [squarefree_divisor_sum_eq_support G hG]
  have hprod (S : Finset (Ideal O)) : normalizedIdealPair I J (∏ P ∈ S, P) =
      ∏ P ∈ S, normalizedIdealPair I J P := map_prod (normalizedIdealPairHom I J hI hJ hray) (fun P => P) S
  have hm (E : Finset (Ideal O)) (hE : E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset) :
      (UniqueFactorizationMonoid.moebius (∏ P ∈ E, P) : ℂ) = (-1 : ℂ) ^ E.card :=
    moebius_support_product (Finset.mem_powerset.mp hE)
  have heq : (∑ D ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
      ∑ E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
        (UniqueFactorizationMonoid.moebius (∏ P ∈ E, P) : ℂ) *
          normalizedIdealPair I J ((∏ P ∈ D, P) * ∏ P ∈ E, P)) =
      ∑ D ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
        ∑ E ∈ (IdealMobiusDivisorSum.primeSupport G).powerset,
          (-1 : ℂ) ^ E.card * (∏ P ∈ D, normalizedIdealPair I J P) *
            ∏ P ∈ E, normalizedIdealPair I J P := by
    apply Finset.sum_congr rfl
    intro D hD
    apply Finset.sum_congr rfl
    intro E hE
    rw [hm E hE, normalizedIdealPair_mul I J hI hJ hray, hprod D, hprod E]
    ring
  rw [heq]
  have hh := QuadraticDivisorCancellation.double_divisor_factorization
    (normalizedIdealPair I J) (IdealMobiusDivisorSum.primeSupport G) ∅ (by simp)
  simpa only [Finset.union_empty, Finset.powerset_empty, Finset.sum_singleton,
    Finset.prod_empty, Finset.card_empty, pow_zero, mul_one,
    normalizedIdealPair_square I J hI hJ] using hh

end
section

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open IdealMobiusDivisorSum QuadraticMainBoundary

def idealNormCutoff (K : ℝ) (H : Ideal O) : ℂ := if (Ideal.absNorm H : ℝ) ≤ K then 1 else 0

def normalizedPairPartial (I J : Ideal O) (K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, normalizedIdealPair I J B.val

def normalizedPairCoprimePartial (I J G : Ideal O) (K : ℝ) : ℂ :=
  ∑ H : coprimeSquarefreeRange G K, normalizedIdealPair I J H.val

def normalizedPairDivisors (I J G : Ideal O) : ℂ :=
  ∑ E ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J E

def normalizedPairDensity (I J G : Ideal O) : ℂ :=
  ∏ P ∈ IdealMobiusDivisorSum.primeSupport G,
    (1 - (idealZeroMask I (ConcretePrimeRowBridge.idealGenerator P) *
      idealZeroMask J (ConcretePrimeRowBridge.idealGenerator P)) / (Ideal.absNorm P : ℂ))

theorem normalizedPairPartial_split (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (G : Ideal O) (hG : Squarefree G) (K : ℝ) :
    normalizedPairPartial I J K =
      ∑ H : coprimeSquarefreeRange G K, ∑ D ∈ idealDivisors G,
        normalizedIdealPair I J H.val * normalizedIdealPair I J D * idealNormCutoff K (H.val * D) := by
  rw [normalizedPairPartial, squarefree_gcd_finite_sum G hG K]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro H _
  rw [Finset.sum_coe_sort (idealDivisors G)
    (fun D => if (Ideal.absNorm (D * H.val) : ℝ) ≤ K then normalizedIdealPair I J (D * H.val) else 0)]
  apply Finset.sum_congr rfl
  intro D hD
  rw [mul_comm D H.val]
  rw [normalizedIdealPair_mul I J hI hJ hray]
  unfold idealNormCutoff
  split_ifs <;> ring

theorem normalizedPair_main_difference
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (hray : columnRay I = columnRay J)
    (G : Ideal O) (hG : Squarefree G) (K : ℝ) :
    normalizedPairPartial I J K * normalizedPairDivisors I J G -
      normalizedPairCoprimePartial I J G K * normalizedPairDensity I J G =
      ∑ H : coprimeSquarefreeRange G K, ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) * normalizedIdealPair I J (H.val * D * E) *
          (cutoffDifference K H.val D : ℂ) := by
  have hd : normalizedPairDensity I J G =
      ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (normalizedIdealPair I J D * normalizedIdealPair I J E) := by
    rw [normalizedPairDensity, ← normalizedIdealPair_double_divisor I J hI hJ hray G hG]
    simp only [normalizedIdealPair_mul I J hI hJ hray]
  rw [normalizedPairPartial_split I J hI hJ hray G hG K, hd]
  unfold normalizedPairDivisors normalizedPairCoprimePartial
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro H _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hHN : (Ideal.absNorm H.val : ℝ) ≤ K :=
    (mem_squarefreeIdealRange.mp (Finset.mem_filter.mp H.property).1).2
  have hc : (cutoffDifference K H.val D : ℂ) = idealNormCutoff K (H.val * D) - 1 := by
    unfold cutoffDifference idealNormCutoff
    rw [ite_eq_left hHN]
    split_ifs <;> norm_num
  rw [hc, normalizedIdealPair_mul I J hI hJ hray,
    normalizedIdealPair_mul I J hI hJ hray]
  ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

def commonMaskIdeal (D : Ideal O) : Ideal O := ∏ P ∈ gcdMaskPrimes D, P

theorem commonMaskIdeal_squarefree (D : Ideal O) : Squarefree (commonMaskIdeal D) := by
  have hp (P : Ideal O) (hP : P ∈ gcdMaskPrimes D) : Prime P := by
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P, hP⟩
    exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro P hP Q hQ hne
    let : P.IsMaximal := gcdMaskPrimes_maximal D ⟨P, hP⟩
    let : Q.IsMaximal := gcdMaskPrimes_maximal D ⟨Q, hQ⟩
    exact (Ideal.isCoprime_of_isMaximal hne).isRelPrime
  · intro P hP
    exact (hp P hP).squarefree

theorem fixedBadPrimes_dvd_commonMaskIdeal (D P : Ideal O) (hP : P ∈ fixedBadPrimes) :
    P ∣ commonMaskIdeal D := by
  apply Finset.dvd_prod_of_mem
  exact Finset.mem_union_left _ hP

theorem admissible_of_squarefree_coprime_bad
    (H G : Ideal O) (hH : Squarefree H) (hc : IsCoprime H G)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) : Admissible H := by
  refine ⟨hH.ne_zero, hH, ?_⟩
  intro P hP
  have hp : Prime P := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  apply (prime_good_iff_not_bad P).mpr
  intro hb
  exact hp.not_isUnit (hc.isRelPrime (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) (hbad P hb))

theorem coprimeSquarefreeRange_subset_idealRange (G : Ideal O)
    (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) (K : ℝ) :
    coprimeSquarefreeRange G K ⊆ idealRange K := by
  intro H hH
  obtain ⟨hHs, hc⟩ := Finset.mem_filter.mp hH
  obtain ⟨hsf, hN⟩ := mem_squarefreeIdealRange.mp hHs
  exact mem_idealRange.mpr ⟨admissible_of_squarefree_coprime_bad H G hsf hc hbad, hN⟩

theorem commonMask_coprimeSquarefreeRange_subset (D : Ideal O) (K : ℝ) :
    coprimeSquarefreeRange (commonMaskIdeal D) K ⊆ idealRange K :=
  coprimeSquarefreeRange_subset_idealRange _ (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP) K

theorem commonMaskIdeal_eq_fixed_mul (D : Ideal O) (hD : Admissible D) :
    commonMaskIdeal D = (∏ P ∈ fixedBadPrimes, P) * D := by
  have hd : Disjoint fixedBadPrimes (IdealMobiusDivisorSum.primeSupport D) := by
    apply Finset.disjoint_left.mpr
    intro P hp hP
    have hfac := Multiset.mem_toFinset.mp hP
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hfac
    let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
    exact (prime_good_iff_not_bad P).mp (hD.2.2 P hfac) hp
  change (∏ P ∈ fixedBadPrimes ∪ IdealMobiusDivisorSum.primeSupport D, P) = _
  rw [Finset.prod_union hd, squarefree_support_product_self hD.2.1]

theorem commonMaskIdeal_norm (D : Ideal O) (hD : Admissible D) :
    Ideal.absNorm (commonMaskIdeal D) = Ideal.absNorm (∏ P ∈ fixedBadPrimes, P) * Ideal.absNorm D := by
  rw [commonMaskIdeal_eq_fixed_mul D hD, map_mul]

end CanonicalQuadraticSieve

end

end OAI

end

