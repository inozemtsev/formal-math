module

public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / QuadraticSieve / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalTruncation -/

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

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex

def lowPrincipalIdeal (I J : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' A : {A : Ideal O // Supported A},
    (idealZeroMask I (primaryGenerator A.val) * idealZeroMask J (primaryGenerator A.val)) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)

def lowPrincipalLattice (I J : Ideal O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ z *
    W ((‖eisEmbedding z‖ ^ 2 / X) ^ 2)

theorem lowPrincipalLattice_eq_six_ideal (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (X : ℝ) (hX : 0 < X) :
    lowPrincipalLattice I J W X = 6 * lowPrincipalIdeal I J W X := by
  let R := fun P : gcdMaskPrimes (I * J) => P.val
  let V := quadraticSquareProfile W
  let f : O → ℂ := fun z => rowCoprimeMask R Finset.univ z * V (‖eisEmbedding z‖ ^ 2 / X)
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one R Finset.univ z)
  have h0 : f 0 = 0 := by
    dsimp only [f, R]
    rw [jointMask_zero, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hnorm (A : Ideal O) : ‖eisEmbedding (idealGenerator A)‖ ^ 2 = (Ideal.absNorm A : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span, span_idealGenerator]
  simp only [f, V, quadraticSquareProfile_apply, hnorm] at he
  have hid : (∑' A : NonzeroIdeal, rowCoprimeMask R Finset.univ (idealGenerator A.val) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)) = lowPrincipalIdeal I J W X := by
    let F : Ideal O → ℂ := fun A => if Supported A then
      (idealZeroMask I (primaryGenerator A) * idealZeroMask J (primaryGenerator A)) *
        W (((Ideal.absNorm A : ℝ) / X) ^ 2) else 0
    calc
      _ = ∑' A : NonzeroIdeal, F A.val := by
        apply tsum_congr
        intro A
        rw [jointMask_generator I J hI hJ]
        by_cases hA : Supported A.val <;> simp [hA, F]
      _ = ∑' A : Ideal O, F A := by
        apply tsum_subtype_eq_of_support_subset
        intro A hA
          hz
        subst A
        exact hA (by simp [F, Supported])
      _ = _ := by
        calc
          _ = ∑' A : Ideal O, ({A : Ideal O | Supported A} : Set (Ideal O)).indicator
              (fun A => (idealZeroMask I (primaryGenerator A) * idealZeroMask J (primaryGenerator A)) *
                W (((Ideal.absNorm A : ℝ) / X) ^ 2)) A := by
            apply tsum_congr
            intro A
            rfl
          _ = _ := (_root_.tsum_subtype _ _).symm
  rw [hid] at he
  exact he

theorem lowPrincipalIdeal_eq_lattice (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (X : ℝ) (hX : 0 < X) :
    lowPrincipalIdeal I J W X = (6 : ℂ)⁻¹ * lowPrincipalLattice I J W X := by
  rw [lowPrincipalLattice_eq_six_ideal I J hI hJ W X hX]
  ring

theorem originalPairLow_principal_lattice
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑' B : {B : Ideal O // Admissible B}, if (Ideal.absNorm B.val : ℝ) ≤ K then
        (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
          ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B.val : ℝ))))
      else 0 := by
  rw [originalPairLow_squarefree_tsum I J hI hJ W M K hM]
  apply tsum_congr
  intro B
  by_cases hB : (Ideal.absNorm B.val : ℝ) ≤ K
  · rw [ite_eq_left hB, ite_eq_left hB]
    congr 1
    have hN : 0 < (Ideal.absNorm B.val : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hX : 0 < Real.sqrt (M / (Ideal.absNorm B.val : ℝ)) := Real.sqrt_pos.mpr (div_pos hM hN)
    rw [← lowPrincipalIdeal_eq_lattice I J hI hJ W _ hX]
    unfold lowPrincipalIdeal
    apply tsum_congr
    intro A
    congr 2
    rw [div_pow, Real.sq_sqrt (div_pos hM hN).le]
    field_simp
  · simp only [ite_eq_right hB]

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson TruncatedPrincipalPoisson IdealCoprimeSieveOperator

def lowPrincipalMain (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Z : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * principalTruncation (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Z

def lowPrincipalMiddle (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * middleTruncation (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Y Z lengthScale

def lowPrincipalError (I J : Ideal O) (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (6 : ℂ)⁻¹ * truncationError (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
    (quadraticSquareProfile W) X Y Z lengthScale

theorem lowPrincipalIdeal_truncated (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ) (hX : 0 < X) :
    lowPrincipalIdeal I J W X =
      lowPrincipalMain I J W X Z + lowPrincipalMiddle I J W X Y Z lengthScale + lowPrincipalError I J W X Y Z lengthScale := by
  have he : lowPrincipalLattice I J W X =
      ∑' z : O, rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ z *
        (if z = 0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖ ^ 2 / X)) := by
    apply tsum_congr
    intro z
    by_cases hz : z = 0
    · subst z
      simp only [jointMask_zero, zero_mul]
    · simp only [ite_eq_right hz, quadraticSquareProfile_apply]
  rw [lowPrincipalIdeal_eq_lattice I J hI hJ W X hX, he]
  unfold lowPrincipalMain lowPrincipalMiddle lowPrincipalError truncationError
  ring

theorem gcdMaskPrimes_card_le (D : Ideal O) :
    (gcdMaskPrimes D).card ≤ 2 + (IdealMobiusDivisorSum.primeSupport D).card := by
  change (fixedBadPrimes ∪ IdealMobiusDivisorSum.primeSupport D).card ≤ _
  exact (Finset.card_union_le _ _).trans_eq (by rw [fixedBadPrimes_card])

theorem gcdMaskPrimes_subsets_bound (ε : ℝ) (hε : 0 < ε) (D : Ideal O) (hD : D ≠ 0) :
    (2 : ℝ) ^ (gcdMaskPrimes D).card ≤
      4 * supportConstant ε hε * (Ideal.absNorm D : ℝ) ^ ε := by
  calc
    _ ≤ (2 : ℝ) ^ (2 + (IdealMobiusDivisorSum.primeSupport D).card) :=
      pow_le_pow_right₀ (by norm_num) (gcdMaskPrimes_card_le D)
    _ = 4 * (2 : ℝ) ^ (IdealMobiusDivisorSum.primeSupport D).card := by rw [pow_add]; norm_num
    _ ≤ 4 * (supportConstant ε hε * (Ideal.absNorm D : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (support_card_bound ε hε D hD) (by norm_num)
    _ = _ := by ring

theorem lowPrincipalError_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (I J : Ideal O) (_hI : Admissible I) (_hJ : Admissible J)
        (W : SchwartzMap ℝ ℂ) (X Y Z lengthScale : ℝ),
        0 < X → 0 < Y → Y ≤ X → X ≤ Z → 0 ≤ lengthScale →
        ‖lowPrincipalError I J W X Y Z lengthScale‖ ≤
          (4 * supportConstant ε hε * ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) ^ ε) *
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
          ((Y / X) ^ A + 1 / (1 + Z / X) ^ A +
            (X / Y) / ((min 1 (X / Z)) ^ 2 * (1 + X * lengthScale / Z) ^ A)) := by
  obtain ⟨s, C, hC, hb⟩ := truncationError_bound A
  refine ⟨s, C, hC, ?_⟩
  intro ε hε I J hI hJ W X Y Z lengthScale hX hY hYX hXZ hL
  have h := hb (fun P : gcdMaskPrimes (I * J) => P.val) Subtype.val_injective Finset.univ
    (quadraticSquareProfile W) X Y Z lengthScale hX hY hYX hXZ hL
  have hc := gcdMaskPrimes_subsets_bound ε hε (I * J) (mul_ne_zero hI.1 hJ.1)
  simp only [Finset.card_univ, Fintype.card_coe] at h
  simp only [map_mul, Nat.cast_mul] at hc
  have hnorm : ‖lowPrincipalError I J W X Y Z lengthScale‖ ≤
      ‖truncationError (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ
        (quadraticSquareProfile W) X Y Z lengthScale‖ := by
    unfold lowPrincipalError
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    norm_num
  apply hnorm.trans (h.trans ?_)
  have hZ : 0 < Z := hX.trans_le hXZ
  gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss

theorem tsum_admissible_norm_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Admissible B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : idealRange K, f B.val := by
  let e : idealRange K → {B : Ideal O // Admissible B} :=
    fun B => ⟨B.val, (mem_idealRange.mp B.property).1⟩
  have he : Function.Injective e := by
    intro B C h
    apply Subtype.ext
    exact congrArg (fun D : {B : Ideal O // Admissible B} => D.val) h
  let F : {B : Ideal O // Admissible B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (ite_eq_right hn)
    exact ⟨⟨B.val, mem_idealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩
  have ht := he.tsum_eq hs
  change (∑' B, F B) = _
  rw [← ht, tsum_fintype]
  apply Finset.sum_congr rfl
  intro B _
  exact ite_eq_left (mem_idealRange.mp B.property).2

theorem originalPairLow_principal_finite
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ) (M K : ℝ) (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑ B : idealRange K,
        (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
          ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B.val : ℝ)))) := by
  rw [originalPairLow_principal_lattice I J hI hJ W M K hM]
  exact tsum_admissible_norm_cutoff K (fun B : Ideal O =>
    (quadraticRow I (primaryGenerator B) * quadraticRow J (primaryGenerator B)) *
      ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B : ℝ)))))

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstCauchyArithmetic (activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_norm_le_one
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (e k : O) :
    ‖activeGaussRowFactor p hp hinj hg S T e k‖ ≤ 1 := by
  have hr (a : O) : ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
      (fun i => hg i.val) (activeExponent S T) a‖ ≤ 1 := by
    rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
    exact (mul_le_mul (finiteSquarefreeRow_norm_le_one _ hg _ _)
      (finiteSquarefreeRow_norm_le_one _ hg _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hGauss := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : activeSupport S T => p i.val) (fun i => hp i.val)
    (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T)
    (fun i => hg i.val) (fun i => hc i.val) (activeExponent S T)
    (activeExponent_ne_zero S T) (activeExponent_lt_six S T)
  simp only [activeGaussRowFactor, norm_mul, norm_star, hGauss, one_mul]
  exact (mul_le_mul (hr e) (hr k) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem secondPairRadialMode_tail
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : O // H ≤ scale * ‖eisEmbedding k‖^2},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro S T e he W Y H hY hH
  dsimp only
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hnorm : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn)
  have hscale : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he))) (sq_pos_of_pos hnorm))
  let tailSet : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let c := Y / ‖eisEmbedding n‖
  have hc0 : 0 ≤ c := (div_pos hY hnorm).le
  have hpnt (k : tailSet) : ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖ := by
    have ha : Y * ‖eisEmbedding k.val‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
        scale * ‖eisEmbedding k.val‖^2 := by dsimp [scale]; ring
    simp only [secondPairRadialMode, norm_mul]
    change ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
    rw [ha, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hY, abs_of_pos hnorm]
    exact mul_le_of_le_one_right (by positivity)
      (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k.val)
  have hmajor : Summable (fun k : tailSet =>
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖) :=
    ((EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale).subtype tailSet).mul_left c
  have hsmall : Summable (fun k : tailSet => ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑' k : tailSet, c * ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := hsmall.tsum_le_tsum hpnt hmajor
    _ = c * ∑' k : tailSet, ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound W scale H hscale hH) hc0

end
section

open ActualEisensteinCubic

def secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) : Finset (SecondExpansionData ι) :=
  F.powerset.biUnion (fun G => G.powerset.biUnion (fun E =>
    F.powerset.biUnion (fun V => (K G E).image (fun k => ⟨G,E,V,k⟩))))

theorem mem_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (x : SecondExpansionData ι) :
    x ∈ secondExpansionPool F K ↔
      x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
        x.frequency ∈ K x.sourceCommon x.divisor := by
  simp only [secondExpansionPool, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨G,hG,E,hE,V,hV,k,hk,hx⟩
    subst x
    exact ⟨hG,hE,hV,hk⟩
  · rintro ⟨hG,hE,hV,hk⟩
    exact ⟨x.sourceCommon,hG,x.divisor,hE,x.overlap,hV,x.frequency,hk,rfl⟩

theorem sum_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (H : SecondExpansionData ι → ℂ) :
    (∑ x ∈ secondExpansionPool F K, H x) =
      ∑ G ∈ F.powerset, ∑ E ∈ G.powerset, ∑ V ∈ F.powerset, ∑ k ∈ K G E, H ⟨G,E,V,k⟩ := by
  unfold secondExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro G hG
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro V hV
        rw [Finset.sum_image]
        intro k hk k' hk' heq
        exact congrArg SecondExpansionData.frequency heq
      · intro V hV V' hV' hne
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
        exact hne (congrArg SecondExpansionData.overlap heq).symm
    · intro E hE E' hE' hne
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨V,hV,hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨V',hV',hx'⟩ := Finset.mem_biUnion.mp hx'
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
      exact hne (congrArg SecondExpansionData.divisor heq).symm
  · intro G hG G' hG' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨E,hE,V,hV,hx⟩ := (by simpa only [Finset.mem_biUnion] using hx)
    obtain ⟨E',hE',V',hV',hx'⟩ := (by simpa only [Finset.mem_biUnion] using hx')
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
    exact hne (congrArg SecondExpansionData.sourceCommon heq).symm

def secondExpansionSector {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) : Finset (SecondExpansionData ι) :=
  (secondExpansionPool F K).filter (fun x => x.sourceCommon \ x.divisor = R)

theorem sum_secondExpansionSector {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (H : SecondExpansionData ι → ℂ) :
    (∑ R ∈ F.powerset, ∑ x ∈ secondExpansionSector F K R, H x) =
      ∑ x ∈ secondExpansionPool F K, H x := by
  simp only [secondExpansionSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hR : x.sourceCommon \ x.divisor ∈ F.powerset :=
    Finset.mem_powerset.mpr ((Finset.sdiff_subset).trans ((mem_secondExpansionPool F K x).mp hx).1)
  rw [Finset.sum_eq_single_of_mem (x.sourceCommon \ x.divisor) hR]
  · simp
  · intro R hR hne
    simp [Ne.symm hne]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem secondExpansionSector_valid (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (x : SecondExpansionData ι) (hx : x ∈ secondExpansionSector F K R) :
    InSecondQuotientSector p (primeSubsetGenerator (fun i => Ideal.span {p i}) R) x := by
  obtain ⟨hx,hR⟩ := Finset.mem_filter.mp hx
  have hE := ((mem_secondExpansionPool F K x).mp hx).2.1
  refine ⟨hE,?_⟩
  rw [secondMaskQuotient_span, hR, primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator]

theorem truncatedSecondSource_eq_expansionPool
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ z : SecondRayIndex, secondExpansionSource p hp hcop hg F Ψ m c d z
        (secondExpansionPool F K) H H W Y := by
  rw [truncatedSecondSource_eq_child_sectors p hp hg hinj hcop hc hpr]
  simp only [secondExpansionSource, sum_secondExpansionPool]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro k hk
  have hs : (⟨G,E.val,V,k⟩ : SecondExpansionData ι).divisor ⊆
      (⟨G,E.val,V,k⟩ : SecondExpansionData ι).sourceCommon := Finset.mem_powerset.mp E.property
  simp only [secondExpansionQuotient_of_subset p _ hs]
  simp only [mul_assoc]

theorem truncatedSecondSource_eq_fixed_sectors
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset,
        secondExpansionSource p hp hcop hg F Ψ m c d z
          (secondExpansionSector F K R) H H W Y := by
  rw [truncatedSecondSource_eq_expansionPool p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [secondExpansionSource, sum_secondExpansionSector]

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn jLabel)
open JointLogSeparation (halfNormalizationCLM)

theorem normalized_truncatedSecondSource_eq_raw_sectors {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (Ψ : O →* ℂ) (m : O) (X Y : ℝ) (hX : 0 < X)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (K : Finset ι → Finset ι → Finset O) :
    let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
    truncatedSecondSource p hp hg hinj F Ψ m c d
      (fun A => normalizedColumn p (fun S => g (columnLog p X S)) A) W Y K =
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset,
        actualSecondRawVariableSector p hp hcop hg B v₁ v₂ ε₁ ε₂
          ((secondExpansionSector F K R).image (expansionSupportData C D))
          (secondExpansionPushWeight C D (secondExpansionSector F K R)
            (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y))
          F (secondRayMinus Ψ z) (secondRayPlus Ψ z) m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (halfNormalizationCLM U g) (halfNormalizationCLM U g) W
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)) Y := by
  dsimp only
  rw [truncatedSecondSource_eq_fixed_sectors p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro R hR
  exact secondExpansionSource_eq_raw_variable_sector p hp hcop hg hinj hpr B C D F
    v₁ v₂ ε₁ ε₂ Ψ m _ z (secondExpansionSector F K R)
    (fun x hx => secondExpansionSector_valid p F K R x hx)
    X Y hX U hUc hUs g g W hU hU

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc

theorem secondPairRadialMode_summable_norm (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => ‖secondPairRadialMode p hp hg hinj S T e k W Y‖) := by
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hs : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hn))))
  have hmajor := (EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hs).mul_left
    ‖(Y : ℂ)/(‖eisEmbedding n‖ : ℂ)‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
  intro k
  have ha : Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
      scale * ‖eisEmbedding k‖^2 := by dsimp [scale]; ring
  simp only [secondPairRadialMode, norm_mul]
  change ‖(Y : ℂ)/(‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
  rw [ha]
  exact mul_le_of_le_one_right (by positivity)
    (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k)

theorem secondPairRadialMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H → ∀ K : Finset O,
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∀ k : O, k ∉ K → H ≤ scale * ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
        (Y/‖eisEmbedding n‖) *
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_tail p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro S T e he W Y H hY hH K
  dsimp only
  intro hK
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  let small : Set O := {k | k ∉ K}
  let large : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let f : small → large := fun k => ⟨k.val,hK k.val k.property⟩
  have hi : Function.Injective f := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : large => z.val) heq)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : small, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      norm_tsum_le_tsum_norm (hs.subtype small)
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs -/

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
open FirstPassCubeLabels (columnLog primeProductNorm primeProductNorm_pos)
open ConcreteTraceCRT (eisEmbedding)

theorem columnLog_norm_upper {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (X M : ℝ) (hX : 0 < X) (S : Finset ι) (hS : columnLog p X S ≤ M) :
    primeProductNorm p S ≤ X * Real.exp M := by
  have he := Real.exp_le_exp.mpr hS
  rw [columnLog, Real.exp_log (div_pos (primeProductNorm_pos p hp S) hX)] at he
  exact (div_le_iff₀ hX).mp he |>.trans_eq (mul_comm _ _)

def secondFrequencyCutoff (scale H : ℝ) : Finset O :=
  ShortDraftLatticeCount.rowNormBall ⌈H/scale⌉₊

theorem mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖eisEmbedding k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hk
  exact_mod_cast hk.trans (Nat.le_ceil (H/scale))

theorem secondFrequencyCutoff_zero (scale H : ℝ) : (0 : O) ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  simp

theorem outside_secondFrequencyCutoff (scale H : ℝ) (hs : 0 < scale) (k : O)
    (hk : k ∉ secondFrequencyCutoff scale H) : H < scale * ‖eisEmbedding k‖^2 := by
  have hnorm : H/scale < ‖eisEmbedding k‖^2 := lt_of_not_ge (fun h => hk (mem_secondFrequencyCutoff scale H k h))
  have h := (div_lt_iff₀ hs).mp hnorm
  simpa only [mul_comm] using h

theorem active_norm_sq_disjoint {ι : Type*} [DecidableEq ι] (p : ι → O)
    (S T : Finset ι) (hd : Disjoint S T) :
    ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
      primeProductNorm p S * primeProductNorm p T := by
  rw [Finset.prod_coe_sort]
  simp only [activeSupport, Finset.sdiff_eq_self_of_disjoint hd,
    Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.prod_union hd.symm, map_mul, norm_mul, mul_pow]
  simp only [primeProductNorm]
  ring

theorem secondFrequencyCutoff_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (X Y M H : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (e : O) (he : e ≠ 0)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : columnLog p X S ≤ M) (hT : columnLog p X T ≤ M) (k : O)
    (hk : k ∉ secondFrequencyCutoff (Y/(‖eisEmbedding e‖^2*(X*Real.exp M)^2)) H) :
    H ≤ (Y/(‖eisEmbedding e‖^2*‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
      ‖eisEmbedding k‖^2 := by
  have hNe : 0 < ‖eisEmbedding e‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  have hU : 0 < X*Real.exp M := mul_pos hX (Real.exp_pos M)
  have hslow : 0 < Y/(‖eisEmbedding e‖^2*(X*Real.exp M)^2) :=
    div_pos hY (mul_pos hNe (sq_pos_of_pos hU))
  have hbS := columnLog_norm_upper p hp X M hX S hS
  have hbT := columnLog_norm_upper p hp X M hX T hT
  have hprod : primeProductNorm p S * primeProductNorm p T ≤ (X*Real.exp M)^2 := by
    simpa only [pow_two] using mul_le_mul hbS hbT (primeProductNorm_pos p hp T).le hU.le
  have hscale : Y/(‖eisEmbedding e‖^2*(X*Real.exp M)^2) ≤
      Y/(‖eisEmbedding e‖^2*‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2) := by
    rw [active_norm_sq_disjoint p S T hd]
    exact div_le_div_of_nonneg_left hY.le
      (mul_pos hNe (mul_pos (primeProductNorm_pos p hp S) (primeProductNorm_pos p hp T)))
      (mul_le_mul_of_nonneg_left hprod hNe.le)
  exact (outside_secondFrequencyCutoff _ H hslow k hk).le.trans
    (mul_le_mul_of_nonneg_right hscale (sq_nonneg _))

end
section

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def truncatedSecondZero (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (K : Finset ι → Finset ι → Finset O) : ℂ :=
  (Y : ℂ) * paperRadialFourier W 0 *
    ∑ G ∈ F.powerset,
      (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) * star (H G) * H G *
      ∑ E : G.powerset, if 0 ∈ K G E.val then
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E.val, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖ ^ 2 : ℝ)
        else 0

theorem truncatedSecondSource_eq_nonzero_add_zero
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      truncatedSecondSource p hp hg hinj F Ψ m c d H W Y (fun G E => (K G E).erase 0) +
        truncatedSecondZero p hg F Ψ m c d H W Y K := by
  unfold truncatedSecondSource truncatedSecondZero
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G hG
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  by_cases h0 : 0 ∈ K G E.val
  · rw [← Finset.sum_erase_add _ _ h0]
    congr 1
    simp only [ite_eq_left h0, secondFrequencyKernel_zero, Finset.union_empty,
      secondSourceCommonCoefficient]
    ring
  · simp only [Finset.erase_eq_of_notMem h0, ite_eq_right h0, mul_zero, add_zero]

theorem secondExpansionSector_frequency_ne_zero
    (F : Finset ι) (K : Finset ι → Finset ι → Finset O) (R : Finset ι)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondExpansionSector F (fun G E => (K G E).erase 0) R) :
    x.frequency ≠ 0 := by
  have h := (mem_secondExpansionPool F (fun G E => (K G E).erase 0) x).mp
    (Finset.mem_filter.mp hx).1
  exact (Finset.mem_erase.mp h.2.2.2).1

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog normalizedColumn jLabel b0Label firstLogDensity)
open JointLogSeparation (halfNormalizationCLM halfNormalizationCLM_apply outerWindow tripleCoefficient)
open SecondPassIntegration (childGeometricMean)

theorem normalized_second_sector_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (hU₁ : ∀ t, g₁ t ≠ 0 → U t = 1)
    (hU₂ : ∀ t, g₂ t ≠ 0 → U t = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ D₀ E₀ V₀ X₀ K₀ Y : ℝ,
      0 < D₀ → 0 < E₀ → 0 < V₀ → 0 < X₀ → 0 < K₀ → 0 < Y →
      ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ,
        (1+Y*K₀/(D₀*E₀^2*V₀^2*X₀^2))^decayOrder * ‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖ ≤
          Cₛ*firstLogDensity J t₁*firstLogDensity J t₂*firstLogDensity J t₃) ∧
      ∀ (B C D R F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (s : Finset (SecondExpansionData ι))
        (T : Finset (Ideal O × O)) (X lengthScale : ℝ),
        s ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R →
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ lengthScale →
        (∀ x ∈ s, |secondSectorZ p
          (secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
            (expansionSupportData C D x)) X₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUd p D₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUe p E₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorUv p V₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, |secondSectorKap p K₀ (expansionSupportData C D x)| ≤ H) →
        (∀ x ∈ s, (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
          secondSupportRow p (expansionSupportData C D x)) ∈ T) →
        (∀ t ∈ T, t.1 ≠ ⊥) → (∀ t ∈ T, (Ideal.absNorm t.1 : ℝ) ≤ lengthScale) →
        ‖secondExpansionSource p hp hcop hg F Ψ m
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
            jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z s
          (fun S => normalizedColumn p (fun A => g₁ (columnLog p X A)) S)
          (fun S => normalizedColumn p (fun A => g₂ (columnLog p X A)) S) W Y‖ ≤
        (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
            X ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (lengthScale * Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R) T
              (windows 5) (windows 6) X₀ X₀ (t₁,t₂,t₃)) := by
  have hn₁ : ∀ t, halfNormalizationCLM U g₁ t ≠ 0 → |t| ≤ A := by
    intro t ht
    apply hg₁ t
    intro h
    apply ht
    rw [halfNormalizationCLM_apply U hUc hUs, h, mul_zero]
  have hn₂ : ∀ t, halfNormalizationCLM U g₂ t ≠ 0 → |t| ≤ A := by
    intro t ht
    apply hg₂ t
    intro h
    apply ht
    rw [halfNormalizationCLM_apply U hUc hUs, h, mul_zero]
  obtain ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hW,htrans⟩ :=
    actual_raw_variable_sector_transfer p hp hcop hg hinj
      (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A H hA hH hn₁ hn₂ ε hε decayOrder J
  refine ⟨A₁,A₂,windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  obtain ⟨b,hb,hbound⟩ := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
  refine ⟨b,hb,?_⟩
  intro B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K s T X lengthScale hs hv hCB hD hΨ hX hL hz hud hue huv hkap hmap hT hnorm
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  have hsector : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x (hs hx)
  rw [secondExpansionSource_eq_raw_variable_sector p hp hcop hg hinj hpr B C D F v₁ v₂ ε₁ ε₂
    Ψ m r z s hsector X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂]
  have hrow : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact secondExpansionSector_frequency_ne_zero F K R x (hs hx)
  have liftP : ∀ P : SecondSupportData ι → Prop,
      (∀ x ∈ s, P (expansionSupportData C D x)) →
      ∀ y ∈ s.image (expansionSupportData C D), P y := by
    intro P hP y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hP x hx
  have hxscale : ∀ y : SecondSupportData ι, 0 < secondExpansionScale p X r y := by
    intro y
    exact div_pos hX (mul_pos
      (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _))
      (SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)))
  have hw : ∀ y ∈ s.image (expansionSupportData C D),
      ‖secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y) y *
        (secondExpansionScale p X r y : ℂ)⁻¹‖ *
      ‖outerWindow windows (secondSectorZ p (secondExpansionScale p X r y) X₀ y)
        (secondSectorUd p D₀ y) (secondSectorUe p E₀ y) (secondSectorUv p V₀ y)
        (secondSectorKap p K₀ y)‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ * Cw := by
    intro y hy
    exact mul_le_mul (secondNormalizedPushWeight_norm_le p hp hcop hg hinj hc C D Ψ m c d r z
      X Y hX hY.le s hsector (fun x hx => hΨ _) (fun x hx => hΨ _) y hy)
      (hW _ _ _ _ _) (norm_nonneg _) (by positivity)
  exact hbound B v₁ v₂ ε₁ ε₂ (s.image (expansionSupportData C D)) T
    (secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y))
    (Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ * Cw) lengthScale F
    (secondRayMinus Ψ z) (secondRayPlus Ψ z) m r (secondExpansionScale p X r)
    hv (liftP _ (fun x hx => hCB)) (liftP _ (fun x hx => hD))
    (fun y hy => hxscale y) (liftP _ hrow) (liftP _ hz) (liftP _ hud)
    (liftP _ hue) (liftP _ huv) (liftP _ hkap) (by positivity) hL
    (liftP _ hmap) hT hnorm hw

end SecondPassArithmetic

open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def ramifiedIdeal : Ideal O := Ideal.span {lambda}

lemma ramifiedIdeal_prime : Prime ramifiedIdeal := by
  exact Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.ne_zero)
    ((Ideal.span_singleton_prime residue_lambda_prime.ne_zero).mpr residue_lambda_prime)

lemma goodIdeal_iff_not_ramified (I : Ideal O) :
    primaryGenerator I ≠ 0 ↔ ¬ ramifiedIdeal ∣ I := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator I,
    PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff,
    Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]

lemma ramifiedIdeal_absNorm : Ideal.absNorm ramifiedIdeal=3 := absNorm_span_lambda

lemma prime_power_remainder_multiplicity {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] {p a : R} (hp : Prime p) (ha : ¬ p ∣ a) (n : ℕ) :
    multiplicity p (p^n*a)=n := by
  apply multiplicity_eq_of_dvd_of_not_dvd ⟨a,rfl⟩
  intro hd
  rw [pow_succ] at hd
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero)).mp hd)

abbrev NonzeroIdeal := {I : Ideal O // I ≠ 0}

def lambdaFactorMap (p : ℕ × GoodIdeal) : NonzeroIdeal :=
  ⟨ramifiedIdeal^p.1*p.2.1,mul_ne_zero (pow_ne_zero _ ramifiedIdeal_prime.ne_zero)
    (primaryGenerator_ne_zero_ideal _ p.2.2)⟩

lemma lambdaFactorMap_bijective : Function.Bijective lambdaFactorMap := by
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh : ramifiedIdeal^n*I.1=ramifiedIdeal^m*J.1 := congrArg Subtype.val heq
    have hn : n=m := by
      have hm := congrArg (multiplicity ramifiedIdeal) hh
      rw [prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified I.1).mp I.2),
        prime_power_remainder_multiplicity ramifiedIdeal_prime
        ((goodIdeal_iff_not_ramified J.1).mp J.2)] at hm
      exact hm
    subst m
    have hIJ : I=J := Subtype.ext (mul_left_cancel₀ (pow_ne_zero n ramifiedIdeal_prime.ne_zero) hh)
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩ := (FiniteMultiplicity.of_prime_left ramifiedIdeal_prime I.2).exists_eq_pow_mul_and_not_dvd
    refine ⟨(multiplicity ramifiedIdeal I.1,⟨J,(goodIdeal_iff_not_ramified J).mpr hnot⟩), ?_⟩
    exact Subtype.ext hJ.symm

def lambdaFactorEquiv : ℕ × GoodIdeal ≃ NonzeroIdeal :=
  Equiv.ofBijective lambdaFactorMap lambdaFactorMap_bijective

lemma ideal_pow_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun I : Ideal O => I^n) := by
  intro I J h
  dsimp only at h
  apply le_antisymm
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]
  · apply Ideal.dvd_iff_le.mp
    apply (pow_dvd_pow_iff_dvd hn).mp
    rw [h]

lemma lambdaFactor_generator_span (n : ℕ) (I : GoodIdeal) :
    Ideal.span {lambda^n*primaryGenerator I.1}=ramifiedIdeal^n*I.1 := by
  rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    (primaryGenerator_spec I.1 I.2).1]
  rfl

lemma three_dvd_lambda_sq : (3:O) ∣ lambda^2 := by
  have h := three_dvd_primary_sub_one (lambda^2+1) (show lambda^2 ∣ lambda^2+1-1 by simp)
  simpa only [add_sub_cancel_right] using h

lemma unit_cube_eq_sign (u : Oˣ) : (u:O)^3=1 ∨ (u:O)^3= -1 := by
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ ActualEisensteinCubic.K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η:O)=omega := rfl
  have hlist : u ∈ ([1,-1,η,-η,η^2,-η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hlist
  rcases hlist with h | h | h | h | h | h
  · left; simp [h]
  · right; norm_num [h]
  · left; simpa only [h,hη] using omega_primitive.pow_eq_one
  · right
    rw [h,Units.val_neg,hη]
    have hh := omega_primitive.pow_eq_one
    linear_combination -hh
  · left
    rw [h,Units.val_pow_eq_pow_val,hη,show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one]
    simp
  · right
    rw [h,Units.val_neg,Units.val_pow_eq_pow_val,hη]
    simp only [neg_pow,show (-1:O)^3= -1 by norm_num,
      show (omega^2)^3=(omega^3)^2 by ring,omega_primitive.pow_eq_one,one_pow,mul_one]

def cubeSign : Bool → O
  | false => 1
  | true => -1

lemma cubeSign_isUnit (b : Bool) : IsUnit (cubeSign b) := by
  cases b <;> simp [cubeSign]

lemma cubeSign_cube (b : Bool) : (cubeSign b)^3=cubeSign b := by
  cases b <;> norm_num [cubeSign]

lemma cubeSign_injective : Function.Injective cubeSign := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals norm_num [cubeSign] at h

def cubeBase (n : ℕ) (I : GoodIdeal) : O := lambda^(n+1)*primaryGenerator I.1

def cubeColumn (b : Bool) (n : ℕ) (I : GoodIdeal) : O := cubeSign b*(cubeBase n I)^3

lemma cubeBase_ne_zero (n : ℕ) (I : GoodIdeal) : cubeBase n I ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ residue_lambda_prime.ne_zero) I.2

lemma cubeColumn_ne_zero (b : Bool) (n : ℕ) (I : GoodIdeal) : cubeColumn b n I ≠ 0 :=
  mul_ne_zero (cubeSign_isUnit b).ne_zero (pow_ne_zero 3 (cubeBase_ne_zero n I))

lemma cubeColumn_cube (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=(cubeSign b*cubeBase n I)^3 := by
  rw [mul_pow,cubeSign_cube]
  rfl

lemma cubeColumn_level (b : Bool) (n : ℕ) (I : GoodIdeal) : (3:O) ∣ cubeColumn b n I := by
  have h3 : (3:O) ∣ lambda^(3*(n+1)) := three_dvd_lambda_sq.trans (pow_dvd_pow lambda (by omega))
  have heq : cubeColumn b n I=cubeSign b*(lambda^(3*(n+1))*(primaryGenerator I.1)^3) := by
    simp only [cubeColumn,cubeBase,mul_pow,← pow_mul]
    congr 2
    ring
  rw [heq]
  exact (h3.mul_right _).mul_left _

lemma cubeColumn_span (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.span {cubeColumn b n I}=(ramifiedIdeal^(n+1)*I.1)^3 := by
  rw [cubeColumn,Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),
    ← Ideal.span_singleton_pow]
  change (Ideal.span {lambda^(n+1)*primaryGenerator I.1})^3=_
  rw [lambdaFactor_generator_span]

abbrev CubeLower := {c : LevelLower // c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3}

def cubeColumnMap (p : Bool × ℕ × GoodIdeal) : CubeLower :=
  ⟨⟨cubeColumn p.1 p.2.1 p.2.2,cubeColumn_level p.1 p.2.1 p.2.2⟩,
    cubeColumn_ne_zero p.1 p.2.1 p.2.2,⟨cubeSign p.1*cubeBase p.2.1 p.2.2,
      cubeColumn_cube p.1 p.2.1 p.2.2⟩⟩

lemma cubeColumnMap_injective : Function.Injective cubeColumnMap := by
  rintro ⟨b,n,I⟩ ⟨d,m,J⟩ h
  have hc : cubeColumn b n I=cubeColumn d m J := congrArg (fun c : CubeLower => c.1.1) h
  have hs := congrArg (fun a : O => Ideal.span {a}) hc
  rw [cubeColumn_span,cubeColumn_span] at hs
  have hr := ideal_pow_injective (by decide : (3:ℕ) ≠ 0) hs
  have hp : lambdaFactorMap (n+1,I)=lambdaFactorMap (m+1,J) := Subtype.ext hr
  have he := lambdaFactorMap_bijective.1 hp
  have hnm : n=m := Nat.succ.inj (congrArg Prod.fst he)
  have hIJ : I=J := congrArg Prod.snd he
  subst m; subst J
  have hbd : b=d := cubeSign_injective (mul_right_cancel₀
    (pow_ne_zero 3 (cubeBase_ne_zero n I)) hc)
  subst d
  rfl

lemma cubeColumnMap_surjective : Function.Surjective cubeColumnMap := by
  intro c
  obtain ⟨a,ha⟩ := c.2.2
  have ha0 : a ≠ 0 := by intro h; rw [h,zero_pow (by decide)] at ha; exact c.2.1 ha
  let A : NonzeroIdeal := ⟨Ideal.span {a},Ideal.span_singleton_eq_bot.not.mpr ha0⟩
  obtain ⟨⟨k,I⟩,hAI⟩ := lambdaFactorMap_bijective.2 A
  have hfact : ramifiedIdeal^k*I.1=Ideal.span {a} := congrArg Subtype.val hAI
  have hla : lambda ∣ a := by
    apply residue_lambda_prime.dvd_of_dvd_pow
    have hlam3 : lambda ∣ (3:O) :=
      (dvd_pow_self lambda (by decide : 2 ≠ 0)).trans lambda_sq_dvd_three
    rw [← ha]
    exact hlam3.trans c.1.2
  have hk : k ≠ 0 := by
    intro hk
    have hIeq : I.1=Ideal.span {a} := by simpa only [hk,pow_zero,one_mul] using hfact
    apply (goodIdeal_iff_not_ramified I.1).mp I.2
    rw [hIeq,Ideal.dvd_iff_le,ramifiedIdeal,Ideal.span_singleton_le_span_singleton]
    exact hla
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hspan : Ideal.span {cubeBase n I}=Ideal.span {a} :=
    (lambdaFactor_generator_span (n+1) I).trans hfact
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  rcases unit_cube_eq_sign u with hu1 | hum1
  · refine ⟨(false,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn false n I=c.1.1
    rw [ha,← hu,mul_pow,hu1,mul_one]
    simp only [cubeColumn,cubeSign,one_mul]
  · refine ⟨(true,n,I),Subtype.ext (Subtype.ext ?_)⟩
    change cubeColumn true n I=c.1.1
    rw [ha,← hu,mul_pow,hum1]
    simp only [cubeColumn,cubeSign]
    ring

def cubeColumnEquiv : Bool × ℕ × GoodIdeal ≃ CubeLower :=
  Equiv.ofBijective cubeColumnMap ⟨cubeColumnMap_injective,cubeColumnMap_surjective⟩

lemma cubeColumn_expanded (b : Bool) (n : ℕ) (I : GoodIdeal) :
    cubeColumn b n I=lambda^(3*(n+1))*(cubeSign b*primaryGenerator I.1)^3 := by
  simp only [cubeColumn,cubeBase,mul_pow,cubeSign_cube,← pow_mul]
  rw [Nat.mul_comm (n+1) 3]
  ring

lemma cubeColumn_arithmetic_sum (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticResidueSum 0 (cubeColumn b n I)=
      (3^(3*(n+1))*Ideal.absNorm I.1^2*idealTotient I.1:ℕ) := by
  have ha : cubeSign b*cubeBase n I ≠ 0 :=
    mul_ne_zero (cubeSign_isUnit b).ne_zero (cubeBase_ne_zero n I)
  have hA := arithmeticResidueSum_cube _ ha
  rw [← cubeColumn_cube] at hA
  rw [hA,cubeColumn_expanded]
  have hc : IsCoprime (cubeSign b*primaryGenerator I.1) (3:O) :=
    (isCoprime_mul_unit_left_left (cubeSign_isUnit b) _ _).mpr
      (primary_coprime_three _ (primaryGenerator_spec I.1 I.2).2)
  have hs : Ideal.span {cubeSign b*primaryGenerator I.1}=I.1 := by
    rw [Ideal.span_singleton_mul_left_unit (cubeSign_isUnit b),(primaryGenerator_spec I.1 I.2).1]
  rw [card_admissible_cube_product (n+1) _ (mul_ne_zero (cubeSign_isUnit b).ne_zero I.2) hc,hs]

lemma cubeColumn_norm (b : Bool) (n : ℕ) (I : GoodIdeal) :
    Ideal.absNorm (Ideal.span {cubeColumn b n I})=3^(3*(n+1))*Ideal.absNorm I.1^3 := by
  rw [cubeColumn_span,map_pow,map_mul,map_pow,ramifiedIdeal_absNorm,mul_pow,← pow_mul]
  rw [Nat.mul_comm (n+1) 3]

def ramifiedRatio (s : ℂ) : ℂ := (3:ℂ)^(3-3*s)

lemma cube_norm_weight_algebra (s : ℂ) (n N : ℕ) (hN : N ≠ 0) :
    ((3^(3*(n+1))*N^3:ℕ):ℂ)^(-s) * (3^(3*(n+1))*N^2:ℕ) =
      ramifiedRatio s^(n+1) * (N:ℂ)^(-(3*s-2)) := by
  have hNc : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hsplit : ((3:ℂ)^(3*(n+1):ℕ)*(N:ℂ)^3)^(-s)=
      (3:ℂ)^((3*(n+1):ℕ)*(-s))*(N:ℂ)^(3*(-s)) := by
    have hm := Complex.natCast_mul_natCast_cpow (3^(3*(n+1))) (N^3) (-s)
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hm
    rw [hm]
    have h3 : ((3:ℂ)^(3*(n+1):ℕ))^(-s)=(3:ℂ)^((3*(n+1):ℕ)*(-s)) := by
      simpa only [Nat.cast_ofNat] using
        (Complex.natCast_cpow_natCast_mul 3 (3*(n+1)) (-s)).symm
    have hN' : ((N:ℂ)^3)^(-s)=(N:ℂ)^(3*(-s)) := by
      simpa only [Nat.cast_ofNat] using (Complex.natCast_cpow_natCast_mul N 3 (-s)).symm
    rw [h3,hN']
  rw [hsplit]
  have hpoly : (3:ℂ)^(3*(n+1):ℕ)*(N:ℂ)^2 =
      (3:ℂ)^((3*(n+1):ℕ):ℂ)*(N:ℂ)^(2:ℂ) := by
    norm_num only [Complex.cpow_natCast,Complex.cpow_ofNat]
  rw [hpoly]
  calc
    _ = ((3:ℂ)^((3*(n+1):ℕ)*(-s))*(3:ℂ)^((3*(n+1):ℕ):ℂ))*
        ((N:ℂ)^(3*(-s))*(N:ℂ)^(2:ℂ)) := by ring
    _ = (3:ℂ)^((3*(n+1):ℕ)*(-s)+(3*(n+1):ℕ)) * (N:ℂ)^(3*(-s)+2) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (3:ℂ) ≠ 0),← Complex.cpow_add _ _ hNc]
    _ = ramifiedRatio s^(n+1) * (N:ℂ)^(-(3*s-2)) := by
      unfold ramifiedRatio
      rw [← Complex.cpow_mul_nat]
      congr 1 <;> congr 1 <;> push_cast <;> ring

lemma cubeColumn_dirichletTerm (s : ℂ) (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticDirichletTerm s 0 (cubeColumnMap (b,n,I)).1 =
      ramifiedRatio s^(n+1) * ((idealTotient I.1:ℂ)*unramifiedNormWeight (3*s-2) I.1) := by
  have hI : Ideal.absNorm I.1 ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I.1 I.2)
  change (if cubeColumn b n I=0 then 0 else
    ((‖eisEmbedding (cubeColumn b n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (cubeColumn b n I)) = _
  rw [ite_eq_right (cubeColumn_ne_zero b n I),eisEmbedding_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,cubeColumn_norm,cubeColumn_arithmetic_sum,
    unramifiedNormWeight_of_good _ _ I.2]
  calc
    _ = (((3^(3*(n+1))*Ideal.absNorm I.1^3:ℕ):ℂ)^(-s) *
        (3^(3*(n+1))*Ideal.absNorm I.1^2:ℕ))*(idealTotient I.1:ℂ) := by
      push_cast
      ring
    _ = (ramifiedRatio s^(n+1)*(Ideal.absNorm I.1:ℂ)^(-(3*s-2)))*(idealTotient I.1:ℂ) := by
      rw [cube_norm_weight_algebra s n (Ideal.absNorm I.1) hI]
    _ = _ := by ring

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ConstantDirichletSeries -/

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

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

lemma constant_dirichlet_support (s : ℂ) :
    Function.support (arithmeticDirichletTerm s 0) ⊆
      {c : LevelLower | c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3} := by
  intro c hc
  change arithmeticDirichletTerm s 0 c ≠ 0 at hc
  by_cases hzero : c.1=0
  · simp [arithmeticDirichletTerm,hzero] at hc
  · refine ⟨hzero, ?_⟩
    have hA : arithmeticResidueSum 0 c.1 ≠ 0 := by
      intro hA
      apply hc
      simp only [arithmeticDirichletTerm,ite_eq_right hzero,hA,mul_zero]
    exact (arithmeticResidueSum_ne_zero_iff_cube c.1 hzero c.2).mp hA

lemma totient_sum_good (s : ℂ) :
    (∑' I : GoodIdeal,(idealTotient I.1:ℂ)*unramifiedNormWeight s I.1)=unramifiedTotientSeries s := by
  unfold unramifiedTotientSeries
  apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryGenerator I ≠ 0})
    (f := fun I : Ideal O => (idealTotient I:ℂ)*unramifiedNormWeight s I)
  intro I hI
  change (idealTotient I:ℂ)*unramifiedNormWeight s I ≠ 0 at hI
  change primaryGenerator I ≠ 0
  intro hg
  apply hI
  rw [unramifiedNormWeight_of_bad _ I hg,mul_zero]

lemma norm_ramifiedRatio_lt_one (s : ℂ) (hs : 1<s.re) : ‖ramifiedRatio s‖<1 := by
  change ‖((3:ℝ):ℂ)^(3-3*s)‖<1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  norm_num
  linarith

theorem constantDirichlet_summable_norm (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    Summable (fun c : LevelLower => ‖arithmeticDirichletTerm s 0 c‖) := by
  have hs1 : 1<s.re := by linarith
  have hw : 2<(3*s-2).re := by norm_num; linarith
  have hq := norm_ramifiedRatio_lt_one s hs1
  have hqn : Summable (fun n : ℕ => ‖ramifiedRatio s^(n+1)‖) := by
    have hh := (summable_geometric_of_lt_one (norm_nonneg (ramifiedRatio s)) hq).mul_right
      ‖ramifiedRatio s‖
    simpa only [pow_succ,norm_mul,norm_pow] using hh
  have hi := (unramifiedTotientSeries_summable_norm (3*s-2) hw).subtype
    (fun I : Ideal O => primaryGenerator I ≠ 0)
  have hni := hqn.mul_norm hi
  have hb : Summable (fun _ : Bool => ‖(1:ℂ)‖) := summable_of_hasFiniteSupport (Set.toFinite _)
  have hfull := hb.mul_norm hni
  have hp : Summable (fun p : Bool × ℕ × GoodIdeal =>
      ‖arithmeticDirichletTerm s 0 (cubeColumnMap p).1‖) := by
    apply hfull.congr
    rintro ⟨b,n,I⟩
    simp only [one_mul,cubeColumn_dirichletTerm]
  have hsub : Summable (fun c : CubeLower => ‖arithmeticDirichletTerm s 0 c.1‖) :=
    cubeColumnEquiv.summable_iff.mp hp
  have hind := (summable_subtype_iff_indicator
    (s := {c : LevelLower | c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3})
    (f := fun c => ‖arithmeticDirichletTerm s 0 c‖)).mp hsub
  apply hind.congr
  intro c
  by_cases hc : c.1 ≠ 0 ∧ ∃ a : O,c.1=a^3
  · simp [Set.indicator,hc]
  · have hz : arithmeticDirichletTerm s 0 c=0 := by
      by_contra h
      exact hc (constant_dirichlet_support s h)
    simp [Set.indicator,hc,hz]

lemma ramified_geometric_sum (s : ℂ) (hs : 1<s.re) :
    (∑' n : ℕ,ramifiedRatio s^(n+1))=((3:ℂ)^(3*s-3)-1)⁻¹ := by
  have hn := norm_ramifiedRatio_lt_one s hs
  have hne : ramifiedRatio s ≠ 0 := by
    unfold ramifiedRatio
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (by norm_num)
  have hone : ramifiedRatio s ≠ 1 := by intro h; rw [h,norm_one] at hn; exact lt_irrefl 1 hn
  have hi : (3:ℂ)^(3*s-3)=(ramifiedRatio s)⁻¹ := by
    rw [ramifiedRatio,← Complex.cpow_neg]
    congr 1
    ring
  simp_rw [pow_succ]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hn,hi]
  field_simp

theorem arithmeticDirichletSeries_zero_totient (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    arithmeticDirichletSeries s 0 =
      2*((3:ℂ)^(3*s-3)-1)⁻¹*unramifiedTotientSeries (3*s-2) := by
  have hc := (constantDirichlet_summable_norm s hs).of_norm
  have hsub : Summable (fun c : CubeLower => arithmeticDirichletTerm s 0 c.1) := hc.subtype _
  have hp := cubeColumnEquiv.summable_iff.mpr hsub
  change Summable (fun p : Bool × ℕ × GoodIdeal =>
    arithmeticDirichletTerm s 0 (cubeColumnMap p).1) at hp
  calc
    _ = ∑' c : CubeLower,arithmeticDirichletTerm s 0 c.1 :=
      (tsum_subtype_eq_of_support_subset (constant_dirichlet_support s)).symm
    _ = ∑' p : Bool × ℕ × GoodIdeal,arithmeticDirichletTerm s 0 (cubeColumnMap p).1 :=
      (cubeColumnEquiv.tsum_eq _).symm
    _ = ∑' b : Bool,∑' n : ℕ,∑' I : GoodIdeal,
        arithmeticDirichletTerm s 0 (cubeColumnMap (b,n,I)).1 := by
      rw [hp.tsum_prod]
      apply tsum_congr
      intro b
      exact (hp.prod_factor b).tsum_prod
    _ = ∑' b : Bool,∑' n : ℕ,∑' I : GoodIdeal,
        ramifiedRatio s^(n+1)*((idealTotient I.1:ℂ)*unramifiedNormWeight (3*s-2) I.1) := by
      apply tsum_congr; intro b
      apply tsum_congr; intro n
      exact tsum_congr (fun I => cubeColumn_dirichletTerm s b n I)
    _ = ∑' _ : Bool,∑' n : ℕ,ramifiedRatio s^(n+1)*unramifiedTotientSeries (3*s-2) := by
      apply tsum_congr; intro b
      apply tsum_congr; intro n
      rw [tsum_mul_left,totient_sum_good]
    _ = ∑' _ : Bool,((3:ℂ)^(3*s-3)-1)⁻¹*unramifiedTotientSeries (3*s-2) := by
      apply tsum_congr; intro b
      rw [tsum_mul_right,ramified_geometric_sum s (by linarith)]
    _ = _ := by
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul]
      ring

theorem scatteringCoefficient_zero_zeta (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    scatteringCoefficient s 0 =
      (2/((9*Real.sqrt 3/2:ℝ):ℂ))*
      ((3:ℂ)^(3*s-3)-1)⁻¹ *
      (unramifiedIdealZeta (3*s-3)/unramifiedIdealZeta (3*s-2)) := by
  rw [scatteringCoefficient,arithmeticDirichletSeries_zero_totient s hs,
    unramifiedTotientSeries_quotient (3*s-2) (by
      norm_num
      linarith)]
  rw [show 3*s-2-1=3*s-3 by ring]
  ring

theorem eisensteinConstantCoefficient_zeta (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    eisensteinFourierCoefficient v hv s 0 = (v:ℂ)^s+
      (v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*
      ((2/((9*Real.sqrt 3/2:ℝ):ℂ))*((3:ℂ)^(3*s-3)-1)⁻¹*
        (unramifiedIdealZeta (3*s-3)/unramifiedIdealZeta (3*s-2))) := by
  rw [eisensteinConstantCoefficient_formula v hv s hs,scatteringCoefficient_zero_zeta s (by linarith)]

end CubicEisenstein

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem matrix_eq_primePool (M N : ℝ) (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I)
    (hM : idealRange M ⊆ F) (hN : idealRange N ⊆ F) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    matrix M N = QuadraticInitialBound.quadraticMatrix (poolPrimary F)
      (poolPrimary_good F hF)
      (fun I : idealRange M => idealSupport F I.val)
      (fun J : idealRange N => idealSupport F J.val) := by
  ext I J
  change quadraticRow J.val (primaryGenerator I.val) = _
  rw [quadraticRow_eq_primaryPool F hF J.val (hN J.property)]
  rw [primaryGenerator_eq_poolProduct F hF I.val (hM I.property)]
  rfl

theorem sieveNorm_reverse_le (M N : ℝ) :
    sieveNorm M N ≤ 262144 * sieveNorm N M := by
  let F := idealRange M ∪ idealRange N
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI | hI
    · exact (mem_idealRange.mp hI).1
    · exact (mem_idealRange.mp hI).1
  have hM : idealRange M ⊆ F := Finset.subset_union_left
  have hN : idealRange N ⊆ F := Finset.subset_union_right
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have h := QuadraticInitialBound.quadraticSieveNorm_reverse_le
    (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (poolPrimary_odd F hF)
    (fun I : idealRange M => idealSupport F I.val)
    (fun J : idealRange N => idealSupport F J.val)
  simpa only [QuadraticInitialBound.quadraticSieveNorm,
    ← matrix_eq_primePool M N F hF hM hN,
    ← matrix_eq_primePool N M F hF hN hM, sieveNorm] using h

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex
open TruncatedPrincipalPoisson QuadraticSquarefreeKernel

def dualPrincipalIdeal (I J : Ideal O) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' A : NonzeroIdeal,
    (idealZeroMask I (idealGenerator A.val) * idealZeroMask J (idealGenerator A.val)) *
      V ((Ideal.absNorm A.val : ℝ) / X)

def dualPrincipalLattice (I J : Ideal O) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun P : primePool {I * J} => P.val) Finset.univ z *
    V (‖eisEmbedding z‖ ^ 2 / X)

theorem idealZeroMask_pair_zero (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hnt : I ≠ 1 ∨ J ≠ 1) : idealZeroMask I 0 * idealZeroMask J 0 = 0 := by
  rw [← canonical_quadraticRow_squared I hI, ← canonical_quadraticRow_squared J hJ]
  calc
    _ = (quadraticRow I 0 * quadraticRow J 0) ^ 2 := by ring
    _ = 0 := by rw [quadratic_pair_zero_of_nontrivial I J hI hJ hnt]; ring

theorem dualPrincipalIdeal_eq_lattice (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hnt : I ≠ 1 ∨ J ≠ 1) (V : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    dualPrincipalIdeal I J V X = (6 : ℂ)⁻¹ * dualPrincipalLattice I J V X := by
  let P := fun P : primePool {I * J} => P.val
  let f : O → ℂ := fun z => rowCoprimeMask P Finset.univ z * V (‖eisEmbedding z‖ ^ 2 / X)
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one P Finset.univ z)
  have hm (z : O) : rowCoprimeMask P Finset.univ z = idealZeroMask I z * idealZeroMask J z := by
    rw [singleton_rowCoprimeMask_eq_idealZeroMask, idealZeroMask_mul I J hI.1 hJ.1]
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [hm, idealZeroMask_pair_zero I J hI hJ hnt, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hd : (∑' A : NonzeroIdeal, f (idealGenerator A.val)) = dualPrincipalIdeal I J V X := by
    apply tsum_congr
    intro A
    simp only [f, hm, idealGenerator_norm_sq]
  change dualPrincipalLattice I J V X = 6 * ∑' A : NonzeroIdeal, f (idealGenerator A.val) at he
  rw [hd] at he
  rw [he]
  ring

theorem dualPrincipalIdeal_truncated (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hnt : I ≠ 1 ∨ J ≠ 1) (V : 𝓢(ℝ, ℂ)) (X Y Z lengthScale : ℝ) (hX : 0 < X) :
    dualPrincipalIdeal I J V X = (6 : ℂ)⁻¹ *
      (principalTruncation (fun P : primePool {I * J} => P.val) Finset.univ V X Z +
       middleTruncation (fun P : primePool {I * J} => P.val) Finset.univ V X Y Z lengthScale +
       truncationError (fun P : primePool {I * J} => P.val) Finset.univ V X Y Z lengthScale) := by
  rw [dualPrincipalIdeal_eq_lattice I J hI hJ hnt V X hX]
  congr 1
  unfold truncationError
  have he : dualPrincipalLattice I J V X =
      ∑' z : O, rowCoprimeMask (fun P : primePool {I * J} => P.val) Finset.univ z *
        (if z = 0 then 0 else V (‖eisEmbedding z‖ ^ 2 / X)) := by
    apply tsum_congr
    intro z
    by_cases hz : z = 0
    · subst z
      rw [singleton_rowCoprimeMask_eq_idealZeroMask, idealZeroMask_mul I J hI.1 hJ.1,
        idealZeroMask_pair_zero I J hI hJ hnt, zero_mul, zero_mul]
    · simp only [ite_eq_right hz]
  rw [he]
  ring

theorem canonical_pair_ideal_fourier_summable (I J : Ideal O) (W : 𝓢(ℝ, ℂ))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun lengthScale : NonzeroIdeal => unrestrictedPairCharacter I J lengthScale.val *
      paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))) := by
  have hi : Function.Injective (fun lengthScale : NonzeroIdeal => idealGenerator lengthScale.val) := by
    intro A B he
    apply Subtype.ext
    have hs := congrArg (fun z : O => Ideal.span {z}) he
    simpa only [span_idealGenerator] using hs
  have h := (canonical_pair_fourier_summable I J W t ht).comp_injective hi
  simpa only [Function.comp_def, idealGenerator_norm_sq, unrestrictedPairCharacter] using h

theorem canonical_nonprincipal_dual_principal
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (hnt : I ≠ 1 ∨ J ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    (∑' h : O, (quadraticRow I h * quadraticRow J h) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) =
      (6 : ℂ) * ∑' B : {B : Ideal O // Squarefree B},
        unrestrictedPairCharacter I J B.val *
          dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
            (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) := by
  rw [canonical_nonprincipal_dual_squarefree I J hI hJ hray hnt W t ht]
  congr 1
  let F : (NonzeroIdeal × {B : Ideal O // Squarefree B}) → ℂ := fun p =>
    (idealZeroMask I (idealGenerator p.1.val) * idealZeroMask J (idealGenerator p.1.val)) *
    unrestrictedPairCharacter I J p.2.val * paperRadialFourier W
      (t * ((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ)))
  have hf : Summable F := by
    have hs := decompositionEquiv.symm.summable_iff.mpr
      (canonical_pair_ideal_fourier_summable I J W t ht)
    apply hs.congr
    intro p
    change unrestrictedPairCharacter I J (p.1.val ^ 2 * p.2.val) *
      paperRadialFourier W (t * (Ideal.absNorm (p.1.val ^ 2 * p.2.val) : ℝ)) = F p
    rw [unrestrictedPairCharacter_mul I J hI hJ hray,
      unrestrictedPairCharacter_square I J hI hJ hray]
    simp only [F, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  change (∑' p, F p) = _
  calc
    _ = ∑' p : ({B : Ideal O // Squarefree B} × NonzeroIdeal), F (p.2, p.1) :=
      (Equiv.prodComm _ _).tsum_eq (fun p => F (p.2, p.1))
    _ = ∑' B : {B : Ideal O // Squarefree B}, ∑' A : NonzeroIdeal, F (A, B) := hf.prod_symm.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      rw [dualPrincipalIdeal, ← tsum_mul_left]
      apply tsum_congr
      intro A
      have hB : 0 < (Ideal.absNorm B.val : ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
      have htb : 0 < t * (Ideal.absNorm B.val : ℝ) := mul_pos ht hB
      have harg : ((Ideal.absNorm A.val : ℝ) / Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) ^ 2 =
          t * ((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) := by
        rw [div_pow, Real.sq_sqrt (one_div_pos.mpr htb).le]
        field_simp

      simp only [F, quadraticTransformedSquareProfile_apply, harg]
      ring

end
section

open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open QuadraticMainOperatorBound IdealCoprimeSieveOperator DivisorBlockCauchy

def canonicalMainBoundary (H : Finset (Ideal O)) (G : Ideal O) (K N : ℝ)
    (a : idealRange N → ℂ) : ℂ :=
  ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
    (UniqueFactorizationMonoid.moebius E : ℂ) *
    (∑ B : H, mainWeight K B.val D E *
      (∑ J : idealRange N, ∑ lengthScale : idealRange N, if IsCoprime J.val lengthScale.val then
        star (quadraticRow J.val (primaryGenerator B.val) *
          (a J * quadraticRow J.val (primaryGenerator D * primaryGenerator E))) *
        (quadraticRow lengthScale.val (primaryGenerator B.val) *
          (a lengthScale * quadraticRow lengthScale.val (primaryGenerator D * primaryGenerator E))) else 0))

theorem canonicalMainBoundary_bound
    (ε : ℝ) (hε : 0 < ε) (K N : ℝ) (hK : 0 < K) (hN : 0 ≤ N)
    (H : Finset (Ideal O)) (hH : H ⊆ idealRange K) (G : Ideal O) (hG : G ≠ 0)
    (a : idealRange N → ℂ) :
    ‖canonicalMainBoundary H G K N a‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * sieveNorm K N * (supportConstant ε hε * N ^ ε) *
          ∑ J, ‖a J‖ ^ 2) := by
  let A : Matrix H (idealRange N) ℂ := fun B J => quadraticRow J.val (primaryGenerator B.val)
  let r : Ideal O → Ideal O → idealRange N → ℂ := fun D E J =>
    quadraticRow J.val (primaryGenerator D * primaryGenerator E)
  have he := main_difference_operator_bound ε hε K hK G hG
    (fun B : H => B.val) (fun J : idealRange N => J.val)
    (fun J => (mem_idealRange.mp J.property).1.1) N hN
    (fun J => (mem_idealRange.mp J.property).2) A a r
    (fun D E J => quadraticRow_norm_le_one J.val _)
  have hA : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤ sieveNorm K N :=
    family_squared_norm_le (fun B : H => B.val) (fun J : idealRange N => J.val)
      Subtype.val_injective Subtype.val_injective K N
      (fun B => mem_idealRange.mp (hH B.property)) (fun J => mem_idealRange.mp J.property)
  change ‖canonicalMainBoundary H G K N a‖ ≤ _ at he
  apply he.trans
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  gcongr

theorem canonicalMainBoundary_small_power
    (ε : ℝ) (hε : 0 < ε) (K N : ℝ) (hK : 0 < K) (hN : 0 ≤ N)
    (H : Finset (Ideal O)) (hH : H ⊆ idealRange K) (G : Ideal O) (hG : G ≠ 0)
    (a : idealRange N → ℂ) :
    ‖canonicalMainBoundary H G K N a‖ ≤
      (divisorConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε) ^ 2 *
        ((1 / Real.sqrt K) * sieveNorm K N * (supportConstant ε hε * N ^ ε) *
          ∑ J, ‖a J‖ ^ 2) := by
  apply (canonicalMainBoundary_bound ε hε K N hK hN H hH G hG a).trans
  have hd : ((idealDivisors G).card : ℝ) ≤ divisorConstant ε hε * (Ideal.absNorm G : ℝ) ^ ε :=
    (IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 G hG
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  have hB := sieveNorm_nonneg K N
  gcongr

theorem canonicalMainBoundary_reverse
    (ε : ℝ) (hε : 0 < ε) (K N : ℝ) (hK : 0 < K) (hN : 0 ≤ N)
    (H : Finset (Ideal O)) (hH : H ⊆ idealRange K) (G : Ideal O) (hG : G ≠ 0)
    (a : idealRange N → ℂ) :
    ‖canonicalMainBoundary H G K N a‖ ≤
      ((idealDivisors G).card : ℝ) ^ 2 *
        ((262144 / Real.sqrt K) * sieveNorm N K * (supportConstant ε hε * N ^ ε) *
          ∑ J, ‖a J‖ ^ 2) := by
  apply (canonicalMainBoundary_bound ε hε K N hK hN H hH G hG a).trans
  have hs : 0 ≤ supportConstant ε hε := (supportConstant_pos ε hε).le
  calc
    _ ≤ ((idealDivisors G).card : ℝ) ^ 2 *
        ((1 / Real.sqrt K) * (262144 * sieveNorm N K) * (supportConstant ε hε * N ^ ε) *
          ∑ J, ‖a J‖ ^ 2) := by gcongr; exact sieveNorm_reverse_le K N
    _ = _ := by ring

end

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction

def CoefficientOnShell (N X : ℝ) (a : idealRange N → ℂ) : Prop :=
  ∀ J, a J ≠ 0 → X / 2 < (Ideal.absNorm J.val : ℝ) ∧ (Ideal.absNorm J.val : ℝ) ≤ X

theorem column_dyadic_exists (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale) (J : idealRange N) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < (Ideal.absNorm J.val : ℝ) ∧
      (Ideal.absNorm J.val : ℝ) ≤ (2 : ℝ) ^ j := by
  have hn : 1 ≤ Ideal.absNorm J.val := Nat.one_le_iff_ne_zero.mpr
    (fun hz => (mem_idealRange.mp J.property).1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  exact exists_dyadic_shell (Ideal.absNorm J.val) lengthScale hn ((mem_idealRange.mp J.property).2.trans hNL)

def columnDyadicSector (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale) (J : idealRange N) : Fin (lengthScale + 1) :=
  ⟨(column_dyadic_exists N lengthScale hNL J).choose,
    Finset.mem_range.mp (column_dyadic_exists N lengthScale hNL J).choose_spec.1⟩

def dyadicColumnCoefficient (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (j : Fin (lengthScale + 1)) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  sectorCoefficient (columnDyadicSector N lengthScale hNL) j a

theorem dyadicColumnCoefficient_shell (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (j : Fin (lengthScale + 1)) (a : idealRange N → ℂ) :
    CoefficientOnShell N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a) := by
  intro J hJ
  have he : columnDyadicSector N lengthScale hNL J = j := by
    by_contra hn
    exact hJ (by simp only [dyadicColumnCoefficient, sectorCoefficient, ite_eq_right hn])
  have hs := (column_dyadic_exists N lengthScale hNL J).choose_spec.2
  have hv : (columnDyadicSector N lengthScale hNL J).val = j.val := congrArg Fin.val he
  change (column_dyadic_exists N lengthScale hNL J).choose = j.val at hv
  simpa only [hv] using hs

theorem dyadicColumnCoefficient_energy (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    (∑ j : Fin (lengthScale + 1), ∑ J, ‖dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2) = ∑ J, ‖a J‖ ^ 2 :=
  sectorCoefficient_energy (columnDyadicSector N lengthScale hNL) a

theorem weighted_energy_column_shells {m : Type*} [Fintype m]
    (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (A : Matrix m (idealRange N) ℂ) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i)
    (a : idealRange N → ℂ) :
    (∑ i, v i * ‖∑ J, A i J * a J‖ ^ 2) ≤
      (lengthScale + 1 : ℝ) * ∑ j : Fin (lengthScale + 1), ∑ i,
        v i * ‖∑ J, A i J * dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2 := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, dyadicColumnCoefficient] using
    sector_weighted_energy_bound A (columnDyadicSector N lengthScale hNL) a v hv

theorem annularHighEnergy_column_shells (M N K : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ (lengthScale + 1 : ℝ) *
      ∑ j : Fin (lengthScale + 1), annularHighEnergy M N K (dyadicColumnCoefficient N lengthScale hNL j a) := by
  exact weighted_energy_column_shells N lengthScale hNL
    (fun I : highKernelRange (2 * M) K => fun J => quadraticRow J.val (primaryGenerator I.val))
    (fun I => annularHighWeight M I.val) (fun _ => QuadraticInitialBound.annularSieveBump.nonneg) a

def coefficientAtScale (N X : ℝ) (a : idealRange N → ℂ) (J : idealRange X) : ℂ :=
  if h : J.val ∈ idealRange N then a ⟨J.val, h⟩ else 0

theorem coefficientAtScale_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell X X (coefficientAtScale N X a) := by
  intro J hJ
  unfold coefficientAtScale at hJ
  split_ifs at hJ with h
  · exact ha ⟨J.val, h⟩ hJ
  · exact (hJ rfl).elim

theorem coefficientAtScale_row_sum (N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) (z : O) :
    (∑ J : idealRange N, quadraticRow J.val z * a J) =
      ∑ J : idealRange X, quadraticRow J.val z * coefficientAtScale N X a J := by
  let f : Ideal O → ℂ := fun I => if h : I ∈ idealRange N then quadraticRow I z * a ⟨I, h⟩ else 0
  have hleft : (∑ J : idealRange N, quadraticRow J.val z * a J) = ∑ I ∈ idealRange N, f I := by
    rw [← Finset.sum_coe_sort (idealRange N) f]
    apply Finset.sum_congr rfl
    intro J _
    simp only [f, dite_eq_left J.property]
  have hright : (∑ J : idealRange X, quadraticRow J.val z * coefficientAtScale N X a J) =
      ∑ I ∈ idealRange X, f I := by
    rw [← Finset.sum_coe_sort (idealRange X) f]
    apply Finset.sum_congr rfl
    intro J _
    unfold coefficientAtScale
    split_ifs with h <;> simp only [f, h, ↓reduceDIte, mul_zero]
  rw [hleft, hright]
  rcases le_total N X with hNX | hXN
  · apply Finset.sum_subset (idealRange_mono hNX)
    intro I hIX hIN
    simp only [f, dite_eq_right hIN]
  · symm
    apply Finset.sum_subset (idealRange_mono hXN)
    intro I hIN hIX
    have haI : a ⟨I, hIN⟩ = 0 := by
      by_contra hn
      exact hIX (mem_idealRange.mpr ⟨(mem_idealRange.mp hIN).1, ha ⟨I, hIN⟩ hn⟩)
    simp only [f, dite_eq_left hIN, haI, mul_zero]

theorem coefficientAtScale_energy (N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) :
    (∑ J : idealRange N, ‖a J‖ ^ 2) = ∑ J : idealRange X, ‖coefficientAtScale N X a J‖ ^ 2 := by
  let f : Ideal O → ℝ := fun I => if h : I ∈ idealRange N then ‖a ⟨I, h⟩‖ ^ 2 else 0
  have hleft : (∑ J : idealRange N, ‖a J‖ ^ 2) = ∑ I ∈ idealRange N, f I := by
    rw [← Finset.sum_coe_sort (idealRange N) f]
    apply Finset.sum_congr rfl
    intro J _
    simp only [f, dite_eq_left J.property]
  have hright : (∑ J : idealRange X, ‖coefficientAtScale N X a J‖ ^ 2) =
      ∑ I ∈ idealRange X, f I := by
    rw [← Finset.sum_coe_sort (idealRange X) f]
    apply Finset.sum_congr rfl
    intro J _
    unfold coefficientAtScale
    split_ifs with h <;> simp only [f, h, ↓reduceDIte, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [hleft, hright]
  rcases le_total N X with hNX | hXN
  · apply Finset.sum_subset (idealRange_mono hNX)
    intro I hIX hIN
    simp only [f, dite_eq_right hIN]
  · symm
    apply Finset.sum_subset (idealRange_mono hXN)
    intro I hIN hIX
    have haI : a ⟨I, hIN⟩ = 0 := by
      by_contra hn
      exact hIX (mem_idealRange.mpr ⟨(mem_idealRange.mp hIN).1, ha ⟨I, hIN⟩ hn⟩)
    simp only [f, dite_eq_left hIN, haI, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem annularHighEnergy_coefficientAtScale (M N X K : ℝ) (a : idealRange N → ℂ)
    (ha : ∀ J, a J ≠ 0 → (Ideal.absNorm J.val : ℝ) ≤ X) :
    annularHighEnergy M N K a = annularHighEnergy M X K (coefficientAtScale N X a) := by
  unfold annularHighEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

theorem annularHighEnergy_column_shells_at_scale (M N K : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ (lengthScale + 1 : ℝ) * ∑ j : Fin (lengthScale + 1),
      annularHighEnergy M ((2 : ℝ) ^ j.val) K
        (coefficientAtScale N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a)) := by
  apply (annularHighEnergy_column_shells M N K lengthScale hNL a).trans_eq
  apply congrArg (fun x : ℝ => (lengthScale + 1 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro j _
  exact annularHighEnergy_coefficientAtScale M N _ K _
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)

theorem dyadicColumnCoefficient_at_scale_energy (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : idealRange N → ℂ) :
    (∑ j : Fin (lengthScale + 1), ∑ J : idealRange ((2 : ℝ) ^ j.val),
      ‖coefficientAtScale N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a) J‖ ^ 2) =
        ∑ J : idealRange N, ‖a J‖ ^ 2 := by
  calc
    _ = ∑ j : Fin (lengthScale + 1), ∑ J : idealRange N, ‖dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact (coefficientAtScale_energy N _ _
        (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)).symm
    _ = _ := dyadicColumnCoefficient_energy N lengthScale hNL a

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns -/

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

def columnDyadicLength (N : ℝ) : ℕ := ⌈Real.log N / Real.log 2⌉₊

theorem columnDyadicLength_cover (N : ℝ) : N ≤ (2 : ℝ) ^ columnDyadicLength N := by
  apply Real.pow_le_of_le_log (by norm_num : (0 : ℝ) < 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log N / Real.log 2))

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

theorem annularHighEnergy_column_shells_small_power
    (ε : ℝ) (hε : 0 < ε) (M N K : ℝ) (hN : 1 ≤ N) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ ((2 + 1 / (ε * Real.log 2)) * N ^ ε) *
      ∑ j : Fin (columnDyadicLength N + 1),
        annularHighEnergy M ((2 : ℝ) ^ j.val) K
          (coefficientAtScale N ((2 : ℝ) ^ j.val)
            (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)) := by
  apply (annularHighEnergy_column_shells_at_scale M N K (columnDyadicLength N)
    (columnDyadicLength_cover N) a).trans
  apply mul_le_mul_of_nonneg_right (columnDyadicLength_small_power ε hε N hN)
  apply Finset.sum_nonneg
  intro j _
  unfold annularHighEnergy
  exact Finset.sum_nonneg (fun I _ => mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (sq_nonneg _))

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

theorem squarefreePart_norm_le (lengthScale : Ideal O) (hL : lengthScale ≠ 0) :
    Ideal.absNorm (squarefreePart lengthScale) ≤ Ideal.absNorm lengthScale := by
  have hd : squarefreePart lengthScale ∣ lengthScale :=
    ⟨squarePart lengthScale ^ 2, (squarePart_sq_mul_squarefreePart lengthScale).symm.trans (mul_comm _ _)⟩
  exact Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (fun h => hL (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hd)

def dualSquarefreeTail (I J : Ideal O) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)},
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))

theorem dualSquarefreeTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t K : ℝ), 0 < t → 0 ≤ K →
        ‖dualSquarefreeTail I J W t K‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 t) ^ 2 * (1 + t * K) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro I J W t K ht hK
  let Q := {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}
  have hgen : Function.Injective (fun lengthScale : Q => idealGenerator lengthScale.val) := by
    intro lengthScale R h
    apply Subtype.ext
    simpa only [span_idealGenerator] using congrArg (fun z : O => Ideal.span {z}) h
  have hlat := paperRadialFourier_lattice_summable_norm W t ht
  have hQ : Summable (fun lengthScale : Q => ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) := by
    have hs := hlat.comp_injective hgen
    simpa only [Function.comp_def, idealGenerator_norm_sq] using hs
  have hp (lengthScale : Q) :
      ‖unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖ ≤
        ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖ := by
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    unfold unrestrictedPairCharacter
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (quadraticRow_norm_le_one I _) (quadraticRow_norm_le_one J _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hnorm : Summable (fun lengthScale : Q =>
      ‖unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hQ
  let f : Q → {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2} := fun lengthScale =>
    ⟨idealGenerator lengthScale.val, by
      rw [idealGenerator_norm_sq]
      apply mul_le_mul_of_nonneg_left _ ht.le
      exact lengthScale.property.2.le.trans (Nat.cast_le.mpr (squarefreePart_norm_le lengthScale.val lengthScale.property.1))⟩
  have hf : Function.Injective f := by
    intro lengthScale R h
    apply hgen
    exact congrArg (fun z : {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2} => z.val) h
  have hi : (∑' lengthScale : Q, ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) ≤
      ∑' z : {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2},
        ‖paperRadialFourier W (t * ‖eisEmbedding z.val‖ ^ 2)‖ := by
    apply hQ.tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) _ (hlat.subtype _)
    intro lengthScale
    simp only [f, idealGenerator_norm_sq]
    rfl
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum hp hQ).trans (hi.trans (hb W t (t * K) ht (mul_nonneg ht.le hK))))

end CanonicalQuadraticSieve

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

def fullIdealWeight (s : ℂ) (I : Ideal O) : ℂ :=
  if I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)

lemma fullIdealWeight_good (s : ℂ) (I : GoodIdeal) : fullIdealWeight s I.1=unramifiedNormWeight s I.1 := by
  rw [fullIdealWeight,ite_eq_right (primaryGenerator_ne_zero_ideal _ I.2),unramifiedNormWeight_of_good _ _ I.2]

lemma norm_fullIdealWeight (s : ℂ) (I : NonzeroIdeal) :
    ‖fullIdealWeight s I.1‖=‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^(-2*s.re) := by
  rw [fullIdealWeight,ite_eq_right I.2]
  have hn : 0<‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (ConcretePrimeRowBridge.idealGenerator_ne_zero _ I.2))
  have hnorm : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^2=(Ideal.absNorm I.1:ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hcast : (Ideal.absNorm I.1:ℂ)=((‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator I.1)‖^2:ℝ):ℂ) := by
    exact_mod_cast hnorm.symm
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn),← Real.rpow_natCast_mul hn.le 2]
  congr 1
  simp only [Complex.neg_re,Nat.cast_ofNat]
  ring

theorem fullIdealWeight_summable_norm (s : ℂ) (hs : 1<s.re) :
    Summable (fun I : Ideal O => ‖fullIdealWeight s I‖) := by
  have hinj : Function.Injective (fun I : NonzeroIdeal => ConcretePrimeRowBridge.idealGenerator I.1) :=
    ConcretePrimeRowBridge.idealGenerator_injective.comp Subtype.val_injective
  have hlat := (summable_embedding_rpow (-2*s.re) (by linarith)).comp_injective hinj
  have hsub : Summable (fun I : NonzeroIdeal => ‖fullIdealWeight s I.1‖) := by
    simpa only [Function.comp_def,norm_fullIdealWeight] using hlat
  have hind := (summable_subtype_iff_indicator (s := {I : Ideal O | I ≠ 0})
    (f := fun I => ‖fullIdealWeight s I‖)).mp hsub
  apply hind.congr
  intro I
  by_cases hI : I=0
  · subst I
    simp [Set.indicator,fullIdealWeight]
  · have hIbot : I ≠ ⊥ := hI
    simp [Set.indicator,hIbot,fullIdealWeight]

def fullIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O,fullIdealWeight s I

lemma fullIdealWeight_norm_fiber (s : ℂ) (n : ℕ) :
    (∑' I : {I : Ideal O // Ideal.absNorm I=n},fullIdealWeight s I.1)=
      LSeries.term (fun n => (Nat.card {I : Ideal O // Ideal.absNorm I=n}:ℂ)) s n := by
  by_cases hn : n=0
  · subst n
    have hzero (I : {I : Ideal O // Ideal.absNorm I=0}) : fullIdealWeight s I.1=0 := by
      have hz : I.1=(0:Ideal O) := Ideal.absNorm_eq_zero_iff.mp I.2
      rw [fullIdealWeight,ite_eq_left hz]
    simp only [hzero,tsum_zero,LSeries.term_zero]
  · let : Fintype {I : Ideal O // Ideal.absNorm I=n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := O) n).fintype
    have hterm (I : {I : Ideal O // Ideal.absNorm I=n}) : fullIdealWeight s I.1=(n:ℂ)^(-s) := by
      have hI : I.1 ≠ 0 := fun h => hn (by rw [← I.2,h,map_zero])
      rw [fullIdealWeight,ite_eq_right hI,I.2]
    simp only [hterm,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      LSeries.term_of_ne_zero hn,Nat.card_eq_fintype_card,Complex.cpow_neg,div_eq_mul_inv]

theorem fullIdealZeta_eq_dedekindZeta (s : ℂ) (hs : 1<s.re) :
    fullIdealZeta s=NumberField.dedekindZeta ActualEisensteinCubic.K s := by
  have h := (fullIdealWeight_summable_norm s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ =>
    ∑' I : {I : Ideal O // Ideal.absNorm I=n},fullIdealWeight s I.1) (fullIdealZeta s) at h
  simp_rw [fullIdealWeight_norm_fiber] at h
  exact h.tsum_eq.symm

lemma fullIdealWeight_lambdaFactor (s : ℂ) (n : ℕ) (I : GoodIdeal) :
    fullIdealWeight s (lambdaFactorMap (n,I)).1=((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
  rw [fullIdealWeight,ite_eq_right (lambdaFactorMap (n,I)).2]
  change (Ideal.absNorm (ramifiedIdeal^n*I.1):ℂ)^(-s)=_
  rw [map_mul,map_pow,ramifiedIdeal_absNorm,Nat.cast_mul,
    unramifiedNormWeight_of_good _ _ I.2]
  rw [Complex.natCast_mul_natCast_cpow]
  congr 1
  have h := (Complex.natCast_cpow_natCast_mul 3 n (-s)).symm.trans (Complex.cpow_nat_mul 3 n (-s))
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

theorem unramifiedIdealZeta_eq_dedekindZeta (s : ℂ) (hs : 1<s.re) :
    unramifiedIdealZeta s=(1-(3:ℂ)^(-s))*NumberField.dedekindZeta ActualEisensteinCubic.K s := by
  have hnorm : ‖(3:ℂ)^(-s)‖<1 := by
    change ‖((3:ℝ):ℂ)^(-s)‖<1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp only [Complex.neg_re]
    linarith
  have hne : 1-(3:ℂ)^(-s) ≠ 0 := by
    intro h
    have hz : (3:ℂ)^(-s)=1 := (sub_eq_zero.mp h).symm
    rw [hz,norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  have hsub : Summable (fun I : NonzeroIdeal => fullIdealWeight s I.1) :=
    (fullIdealWeight_summable_norm s hs).of_norm.subtype _
  have hp := lambdaFactorEquiv.summable_iff.mpr hsub
  change Summable (fun p : ℕ × GoodIdeal => fullIdealWeight s (lambdaFactorMap p).1) at hp
  have hfull : fullIdealZeta s=(1-(3:ℂ)^(-s))⁻¹*unramifiedIdealZeta s := by
    calc
      _ = ∑' I : NonzeroIdeal,fullIdealWeight s I.1 := by
        symm
        apply tsum_subtype_eq_of_support_subset
        intro I hI
        change I ≠ 0
        intro hz
        exact hI (by simp [fullIdealWeight,hz])
      _ = ∑' p : ℕ × GoodIdeal,fullIdealWeight s (lambdaFactorMap p).1 :=
        (lambdaFactorEquiv.tsum_eq _).symm
      _ = ∑' n : ℕ,∑' I : GoodIdeal,((3:ℂ)^(-s))^n*unramifiedNormWeight s I.1 := by
        rw [hp.tsum_prod]
        apply tsum_congr; intro n
        exact tsum_congr (fun I => fullIdealWeight_lambdaFactor s n I)
      _ = ∑' n : ℕ,((3:ℂ)^(-s))^n*unramifiedIdealZeta s := by
        apply tsum_congr; intro n
        rw [tsum_mul_left]
        apply congrArg (fun z : ℂ => ((3:ℂ)^(-s))^n*z)
        apply tsum_subtype_eq_of_support_subset (f := unramifiedNormWeight s)
          (s := {I : Ideal O | primaryGenerator I ≠ 0})
        intro I hI
        change primaryGenerator I ≠ 0
        intro hz
        exact hI (unramifiedNormWeight_of_bad s I hz)
      _ = _ := by rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hnorm]
  rw [← fullIdealZeta_eq_dedekindZeta s hs,hfull,← mul_assoc,mul_inv_cancel₀ hne,one_mul]

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

lemma constantDirichletTerm_differentiable (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s 0 c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,ite_eq_left hc]
    exact differentiable_const _
  · have hq : ((‖eisEmbedding c.1‖^2:ℝ):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)))
    simp only [arithmeticDirichletTerm,ite_eq_right hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma constantDirichletTerm_norm_mono (a : ℝ) (s : ℂ) (ha : a ≤ s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s 0 c‖ ≤ ‖arithmeticDirichletTerm (a:ℂ) 0 c‖ := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,ite_eq_left hc,norm_zero,le_refl]
  · have hpos : 0<‖eisEmbedding c.1‖^2 := sq_pos_of_pos
      (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
    have hq : 1≤‖eisEmbedding c.1‖^2 := by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
    simp only [arithmeticDirichletTerm,ite_eq_right hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.neg_re,Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha))
      (norm_nonneg _)

theorem arithmeticDirichletSeries_zero_differentiableAt (s : ℂ) (hs : (4:ℝ)/3<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z 0) s := by
  let a : ℝ := ((4:ℝ)/3+s.re)/2
  have ha : (4:ℝ)/3<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := constantDirichlet_summable_norm (a:ℂ) (by simpa using ha)
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z 0) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (constantDirichletTerm_differentiable c).differentiableOn) hopen
    intro c z hz
    exact constantDirichletTerm_norm_mono a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

lemma unramifiedNormWeight_differentiable (I : Ideal O) :
    Differentiable ℂ (fun s : ℂ => unramifiedNormWeight s I) := by
  by_cases hI : primaryGenerator I=0
  · simp only [unramifiedNormWeight_of_bad _ I hI]
    exact differentiable_const _
  · have hn : (Ideal.absNorm I:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hI))
    simp only [unramifiedNormWeight_of_good _ I hI]
    exact differentiable_id.neg.const_cpow (Or.inl hn)

lemma unramifiedNormWeight_norm_mono (a : ℝ) (s : ℂ) (ha : a ≤ s.re) (I : Ideal O) :
    ‖unramifiedNormWeight s I‖≤‖unramifiedNormWeight (a:ℂ) I‖ := by
  by_cases hI : primaryGenerator I=0
  · simp only [unramifiedNormWeight_of_bad _ I hI,norm_zero,le_refl]
  · have hn : Ideal.absNorm I ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I hI)
    have hpos : (0:ℝ)<Ideal.absNorm I := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hq : (1:ℝ)≤Ideal.absNorm I := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    simp only [unramifiedNormWeight_of_good _ I hI]
    change ‖((Ideal.absNorm I:ℝ):ℂ)^(-s)‖≤‖((Ideal.absNorm I:ℝ):ℂ)^(-(a:ℂ))‖
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos,Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    exact Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg ha)

theorem unramifiedIdealZeta_differentiableAt (s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ unramifiedIdealZeta s := by
  let a : ℝ := (1+s.re)/2
  have ha : 1<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := unramifiedNormWeight_summable_norm (a:ℂ) (by simpa using ha)
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ unramifiedIdealZeta {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun I => (unramifiedNormWeight_differentiable I).differentiableOn) hopen
    intro I z hz
    exact unramifiedNormWeight_norm_mono a z hz.le I
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

end

open Filter
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss

def unramifiedZetaResidue : ℂ :=
  (2/3:ℂ)*(NumberField.dedekindZeta_residue ActualEisensteinCubic.K:ℂ)

lemma unramifiedZetaResidue_ne_zero : unramifiedZetaResidue ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  exact Complex.ofReal_ne_zero.mpr
    (NumberField.dedekindZeta_residue_pos ActualEisensteinCubic.K).ne'

theorem unramifiedIdealZeta_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-1)*unramifiedIdealZeta (x:ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 unramifiedZetaResidue) := by
  have hcont : Continuous (fun x : ℝ => 1-(3:ℂ)^(-(x:ℂ))) :=
    continuous_const.sub (Complex.continuous_ofReal.neg.const_cpow (Or.inl (by norm_num)))
  have heuler : Tendsto (fun x : ℝ => 1-(3:ℂ)^(-(x:ℂ))) (𝓝[>] (1:ℝ)) (𝓝 (2/3:ℂ)) := by
    apply (hcont.tendsto' 1 (2/3:ℂ) ?_).mono_left nhdsWithin_le_nhds
    norm_num [Complex.cpow_neg]
  have h := heuler.mul (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT ActualEisensteinCubic.K)
  change Tendsto (fun x : ℝ => (1-(3:ℂ)^(-(x:ℂ)))*
    (((x:ℂ)-1)*NumberField.dedekindZeta ActualEisensteinCubic.K (x:ℂ)))
      (𝓝[>] (1:ℝ)) (𝓝 unramifiedZetaResidue) at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [unramifiedIdealZeta_eq_dedekindZeta (x:ℂ) hx']
  ring

lemma cusp_volume_ne_zero : ((9*Real.sqrt 3/2:ℝ):ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  positivity

def constantArithmeticResidue : ℂ := unramifiedZetaResidue /
  (3*((9*Real.sqrt 3/2:ℝ):ℂ)*unramifiedIdealZeta 2)

lemma constantArithmeticResidue_ne_zero : constantArithmeticResidue ≠ 0 := by
  apply div_ne_zero unramifiedZetaResidue_ne_zero
  exact mul_ne_zero (mul_ne_zero (by norm_num) cusp_volume_ne_zero)
    (unramifiedIdealZeta_ne_zero 2 (by norm_num))

lemma tendsto_three_mul_sub_three_four_thirds :
    Tendsto (fun x : ℝ => 3*x-3) (𝓝[>] ((4:ℝ)/3)) (𝓝[>] (1:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · apply ((continuous_const.mul continuous_id).sub continuous_const).tendsto' _ _ (by norm_num)
      |>.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx ⊢
    linarith

theorem scatteringCoefficient_zero_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*scatteringCoefficient (x:ℂ) 0)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 constantArithmeticResidue) := by
  have hn0 := unramifiedIdealZeta_oneSidedResidue.comp tendsto_three_mul_sub_three_four_thirds
  have hn : Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*unramifiedIdealZeta (3*(x:ℂ)-3))
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (unramifiedZetaResidue/3)) := by
    convert hn0.div_const (3:ℂ) using 1
    ext x
    dsimp only [Function.comp_def]
    push_cast
    ring
  have harg : Tendsto (fun x : ℝ => 3*(x:ℂ)-2) (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).tendsto' _ _ ?_).mono_left
      nhdsWithin_le_nhds
    norm_num
  have hz := (unramifiedIdealZeta_differentiableAt 2 (by norm_num)).continuousAt.tendsto.comp harg
  have hdncont : Continuous (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1) :=
    (((Complex.continuous_ofReal.const_mul 3).sub continuous_const).const_cpow
      (Or.inl (by norm_num))).sub continuous_const
  have hdn : Tendsto (fun x : ℝ => (3:ℂ)^(3*(x:ℂ)-3)-1)
      (𝓝[>] ((4:ℝ)/3)) (𝓝 (2:ℂ)) := by
    apply (hdncont.tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
    norm_num
  have hp := ((hdn.inv₀ (by norm_num)).const_mul
    (2/((9*Real.sqrt 3/2:ℝ):ℂ))).mul
      (hn.div hz (unramifiedIdealZeta_ne_zero 2 (by norm_num)))
  have hlimit : (2/((9*Real.sqrt 3/2:ℝ):ℂ))*(2:ℂ)⁻¹*
      ((unramifiedZetaResidue/3)/unramifiedIdealZeta 2)=constantArithmeticResidue := by
    unfold constantArithmeticResidue
    ring
  rw [hlimit] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (4:ℝ)/3<(x:ℂ).re := by simpa only [Set.mem_Ioi,Complex.ofReal_re] using hx
  rw [scatteringCoefficient_zero_zeta (x:ℂ) hx']
  dsimp only [Pi.div_apply,Function.comp_def]
  ring

end CubicEisenstein

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss

theorem idealQuotient_in_shell (I D : Ideal O) (hI : Admissible I) (hDI : D ∣ I)
    (N : ℝ) (hlo : N / 2 < (Ideal.absNorm I : ℝ)) (hhi : (Ideal.absNorm I : ℝ) ≤ N) :
    (N / (Ideal.absNorm D : ℝ)) / 2 < (Ideal.absNorm (idealQuotient D I) : ℝ) ∧
      (Ideal.absNorm (idealQuotient D I) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hDI
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  have he : (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm D : ℝ) = (Ideal.absNorm I : ℝ) := by
    rw [mul_comm, ← Nat.cast_mul, ← map_mul, idealQuotient_mul hDI]
  refine ⟨?_, idealQuotient_norm_le hD hDI N hhi⟩
  have hh : (N / 2) / (Ideal.absNorm D : ℝ) < (Ideal.absNorm (idealQuotient D I) : ℝ) := by
    apply (div_lt_iff₀ hDN).mpr
    simpa only [he] using hlo
  convert hh using 1 ; ring

theorem residual_modulus_norm_shell (I J D : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (N : ℝ) (hN : 0 < N)
    (hIs : N / 2 < (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (hJs : N / 2 < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ N) :
    (N / (Ideal.absNorm D : ℝ)) / 2 <
      ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ∧
    ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ≤
      N / (Ideal.absNorm D : ℝ) := by
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hDI
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  have hQ := admissible_idealQuotient hI hDI
  have hT := admissible_idealQuotient hJ hDJ
  have hqi := idealQuotient_in_shell I D hI hDI N hIs.1 hIs.2
  have hqj := idealQuotient_in_shell J D hJ hDJ N hJs.1 hJs.2
  let X := N / (Ideal.absNorm D : ℝ)
  have hX : 0 < X := div_pos hN hDN
  have hn : ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ^ 2 =
      (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) := by
    rw [map_mul, norm_mul, mul_pow,
      primaryGenerator_norm_sq _ (primaryGenerator_admissible _ hQ),
      primaryGenerator_norm_sq _ (primaryGenerator_admissible _ hT)]
  have hlo : (X / 2) * (X / 2) <
      (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) :=
    mul_lt_mul hqi.1 hqj.1.le (by positivity) (by positivity)
  have hhi : (Ideal.absNorm (idealQuotient D I) : ℝ) * (Ideal.absNorm (idealQuotient D J) : ℝ) ≤ X * X :=
    mul_le_mul hqi.2 hqj.2 (Nat.cast_nonneg _) hX.le
  have hnorm := norm_nonneg (eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J)))
  constructor
  · nlinarith
  · nlinarith

theorem residual_poisson_prefactor_le (I J D : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hDI : D ∣ I) (hDJ : D ∣ J) (M N : ℝ) (hM : 0 ≤ M) (hN : 0 < N)
    (hIs : N / 2 < (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (hJs : N / 2 < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ N) :
    M / ‖eisEmbedding (primaryGenerator (idealQuotient D I) * primaryGenerator (idealQuotient D J))‖ ≤
      2 * M * (Ideal.absNorm D : ℝ) / N := by
  have hs := residual_modulus_norm_shell I J D hI hJ hDI hDJ N hN hIs hJs
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hDI
  have hDN : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  have hp : 0 < (N / (Ideal.absNorm D : ℝ)) / 2 := by positivity
  calc
    _ ≤ M / ((N / (Ideal.absNorm D : ℝ)) / 2) := div_le_div_of_nonneg_left hM hp hs.1.le
    _ = _ := by field_simp

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

def dualSquarefreeLow (I J : Ideal O) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' lengthScale : NonzeroIdeal, if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) else 0

theorem dual_ideal_low_add_tail (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    (∑' lengthScale : NonzeroIdeal, unrestrictedPairCharacter I J lengthScale.val *
      paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))) =
      dualSquarefreeLow I J W t K + dualSquarefreeTail I J W t K := by
  let F : Ideal O → ℂ := fun lengthScale => unrestrictedPairCharacter I J lengthScale *
    paperRadialFourier W (t * (Ideal.absNorm lengthScale : ℝ))
  have hs : Summable (fun lengthScale : NonzeroIdeal => F lengthScale.val) := canonical_pair_ideal_fourier_summable I J W t ht
  have hl : Summable (fun lengthScale : NonzeroIdeal => if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then F lengthScale.val else 0) :=
    hs.indicator _
  have hh : Summable (fun lengthScale : NonzeroIdeal => if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) :=
    hs.indicator _
  have htail : (∑' lengthScale : NonzeroIdeal, if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) =
      dualSquarefreeTail I J W t K := by
    have hleft : (∑' lengthScale : NonzeroIdeal, if K < (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) then F lengthScale.val else 0) =
        ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | lengthScale ≠ 0} : Set (Ideal O)).indicator
          (fun lengthScale => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then F lengthScale else 0) lengthScale := by
      exact tsum_subtype {lengthScale : Ideal O | lengthScale ≠ 0}
        (fun lengthScale : Ideal O => if K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) then F lengthScale else 0)
    have hright : (∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}, F lengthScale.val) =
        ∑' lengthScale : Ideal O, ({lengthScale : Ideal O | lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)} : Set (Ideal O)).indicator F lengthScale :=
      tsum_subtype _ _
    change _ = ∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}, F lengthScale.val
    rw [hleft, hright]
    apply tsum_congr
    intro lengthScale
    by_cases h0 : lengthScale = 0 <;> by_cases hK : K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ) <;>
      simp [Set.indicator, h0, hK, F]
  rw [← htail, dualSquarefreeLow, ← hl.tsum_add hh]
  apply tsum_congr
  intro lengthScale
  by_cases hK : (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K
  · simp only [hK, not_lt_of_ge hK, ite_true, ite_false, add_zero, F]
  · simp only [hK, lt_of_not_ge hK, ite_true, ite_false, zero_add, F]

theorem dualSquarefreeLow_principal
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hray : columnRay I = columnRay J) (W : 𝓢(ℝ, ℂ)) (t K : ℝ) (ht : 0 < t) :
    dualSquarefreeLow I J W t K =
      ∑' B : {B : Ideal O // Squarefree B}, if (Ideal.absNorm B.val : ℝ) ≤ K then
        unrestrictedPairCharacter I J B.val *
          dualPrincipalIdeal I J (quadraticTransformedSquareProfile W)
            (Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) else 0 := by
  let G : NonzeroIdeal → ℂ := fun lengthScale => if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) else 0
  let F : (NonzeroIdeal × {B : Ideal O // Squarefree B}) → ℂ := fun p =>
    if (Ideal.absNorm p.2.val : ℝ) ≤ K then
      (idealZeroMask I (idealGenerator p.1.val) * idealZeroMask J (idealGenerator p.1.val)) *
      unrestrictedPairCharacter I J p.2.val * paperRadialFourier W
        (t * ((Ideal.absNorm p.1.val : ℝ) ^ 2 * (Ideal.absNorm p.2.val : ℝ))) else 0
  have hg : Summable G := (canonical_pair_ideal_fourier_summable I J W t ht).indicator _
  have hterm (p : NonzeroIdeal × {B : Ideal O // Squarefree B}) : G (decompositionEquiv.symm p) = F p := by
    change (if (Ideal.absNorm (squarefreePart (p.1.val ^ 2 * p.2.val)) : ℝ) ≤ K then
      unrestrictedPairCharacter I J (p.1.val ^ 2 * p.2.val) *
        paperRadialFourier W (t * (Ideal.absNorm (p.1.val ^ 2 * p.2.val) : ℝ)) else 0) = F p
    rw [(squarePart_mul_squarefree p.1.property p.2.property).2]
    by_cases hK : (Ideal.absNorm p.2.val : ℝ) ≤ K
    · simp only [hK, ite_true, F, unrestrictedPairCharacter_mul I J hI hJ hray,
        unrestrictedPairCharacter_square I J hI hJ hray, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
    · simp only [hK, ite_false, F]
  have hf : Summable F := (decompositionEquiv.symm.summable_iff.mpr hg).congr hterm
  calc
    _ = ∑' p : NonzeroIdeal × {B : Ideal O // Squarefree B}, G (decompositionEquiv.symm p) :=
      (decompositionEquiv.symm.tsum_eq G).symm
    _ = ∑' p, F p := tsum_congr hterm
    _ = ∑' p : ({B : Ideal O // Squarefree B} × NonzeroIdeal), F (p.2, p.1) :=
      (Equiv.prodComm _ _).tsum_eq (fun p => F (p.2, p.1))
    _ = ∑' B : {B : Ideal O // Squarefree B}, ∑' A : NonzeroIdeal, F (A, B) := hf.prod_symm.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      by_cases hK : (Ideal.absNorm B.val : ℝ) ≤ K
      · rw [ite_eq_left hK, dualPrincipalIdeal, ← tsum_mul_left]
        apply tsum_congr
        intro A
        have hB : 0 < (Ideal.absNorm B.val : ℝ) := by
          exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
        have htb : 0 < t * (Ideal.absNorm B.val : ℝ) := mul_pos ht hB
        have harg : ((Ideal.absNorm A.val : ℝ) / Real.sqrt (1 / (t * (Ideal.absNorm B.val : ℝ)))) ^ 2 =
            t * ((Ideal.absNorm A.val : ℝ) ^ 2 * (Ideal.absNorm B.val : ℝ)) := by
          rw [div_pow, Real.sq_sqrt (one_div_pos.mpr htb).le]
          field_simp
        simp only [F, ite_eq_left hK, quadraticTransformedSquareProfile_apply, harg]
        ring
      · simp only [F, ite_eq_right hK, tsum_zero]

end CanonicalQuadraticSieve

end

end OAI

end

