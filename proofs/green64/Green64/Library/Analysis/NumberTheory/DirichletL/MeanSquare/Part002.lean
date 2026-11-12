module

public import Green64.Library.Analysis.NumberTheory.DirichletL.GaussSum.Part006
public import Green64.Library.OAI.NumberTheory.DirichletL.CubicSieve.PaddedPassage

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / MeanSquare / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.HighRadialBounds -/

section

namespace OAI

noncomputable section

namespace InitialMeanSquare

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
open scoped BigOperators Classical

section

open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open CanonicalQuadraticSieve (Admissible)

theorem initial_squarefree_target_geometry {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (Z M : ℝ) (j : SecondLogIndex) :
    let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),
      Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 1 := by
  dsimp only
  intro z hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxs,hsq⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxp,hj⟩ := Finset.mem_filter.mp hxs
  have hk := (secondSupportedSector_mem p F K R Z M x hxp).2.2.2.1
  have hgeom := initial_log_target_bounds p hp x hk
  rw [initialLogIndex_eq_second,hj] at hgeom
  refine ⟨initial_squarefree_label_admissible p hp hg hc x hsq,?_,sourceRow_nonzero p x hk,hgeom.2⟩
  simpa only [sourceIdealPoint,elementNorm,eisEmbedding_norm_sq_eq_absNorm_span] using hgeom.1

end

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialSquarefreeBinCost_of_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let E := densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hS : 0 < S := by dsimp [S]; positivity
  have hd := initial_source_density_transfer p hp hcop hg F (secondRayMinus Ψ ray)
    (secondRayPlus Ψ ray) (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6)
    X X B J S Cₛ hS hCₛ hB (fun q => by
      simpa only [S,tripleLogDensity,mul_assoc] using hdec q)
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ/S)*E) := mul_le_mul_of_nonneg_left hd hpref
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ/S)*(Cchild*(X*initialLogLabel j)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdensity (div_nonneg hCₛ hS.le)) hpref
    _ = _ := by
      dsimp only [X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hR.ne'
      field_simp

end

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

lemma initial_bin_row_scale_le (U K : ℝ) (hK : 1 ≤ K) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U K) : secondLogK j ≤ K := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin K+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have hscale : secondLogK j ≤ normLogScale (normLogBin K) := by
    unfold secondLogK normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.2
  exact hscale.trans (normLogBin_scale_bounds K hK).1

theorem initial_bin_cost_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M Kmax ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hKmax : 1 ≤ Kmax) (hε : 0 ≤ ε)
    (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) (J N : ℕ)
    (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      (H*Real.exp 4*Cchild*Cₛ*(Kmax*Real.exp 2)^ε)/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by
  have hb := initialSquarefreeBinCost_of_density_bound p hp hcop hg F R Ψ m ray K
    Z H M ε Cₛ Cchild hZ hH hCₛ j windows B J N hB hdec hdensity
  have hR := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hden : 1 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
    apply one_le_pow₀
    have hnon : 0 ≤ H*secondLogK j*(primeProductNorm p R)^2/Z^2 := by positivity
    linarith
  have hnum : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
      ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε := by positivity
  have hrow : (secondLogK j*Real.exp 2)^ε ≤ (Kmax*Real.exp 2)^ε :=
    Real.rpow_le_rpow (mul_pos hk (Real.exp_pos 2)).le
    (mul_le_mul_of_nonneg_right (initial_bin_row_scale_le (Z*Real.exp M) Kmax hKmax j hj)
      (Real.exp_pos 2).le) hε
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε :=
      hb.trans (div_le_self hnum hden)
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(Kmax*Real.exp 2)^ε :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = _ := by ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem outside_prime_divisor_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I Q : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) (hQ : Prime Q)
    (hd : Q ∣ I) : Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  have hQpos : 1 ≤ Ideal.absNorm Q := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have hQI : Ideal.absNorm Q ≤ Ideal.absNorm I :=
    Nat.le_of_dvd (mem_outsideIdealsUpTo.mp hI).1 (map_dvd Ideal.absNorm hd)
  have hQo : Q ∈ outsideIdealsUpTo S D := mem_outsideIdealsUpTo.mpr
    ⟨hQpos, hQI.trans (mem_outsideIdealsUpTo.mp hI).2.1,
      fun P hP hPQ => (mem_outsideIdealsUpTo.mp hI).2.2 P hP (hPQ.trans hd)⟩
  apply mem_primePool_iff.mpr
  refine ⟨Q, Finset.mem_filter.mpr ⟨hQo,hQ.squarefree⟩,?_⟩
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.ne_zero).mpr
    ⟨hQ,dvd_rfl⟩

theorem outside_factors_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) :
    ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  intro Q hQ
  obtain ⟨hprime,hdiv⟩ :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (outsideIdealsUpTo_ne_bot S D I hI)).mp hQ
  exact outside_prime_divisor_mem_pool S D hI hprime hdiv

theorem outside_prime_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {Q : Ideal O} (hQ : Prime Q) (hQD : Ideal.absNorm Q ≤ D)
    (hQS : ∀ P ∈ S, ¬ P ∣ Q) :
    Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  apply outside_prime_divisor_mem_pool S D (I := Q) _ hQ dvd_rfl
  exact mem_outsideIdealsUpTo.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr
      (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz)),hQD,hQS⟩

end

section

open MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialElementaryConstant (A V : ℝ) : ℝ := 6*128^4*(Real.exp A*V)^2

lemma initialElementaryConstant_nonneg (A V : ℝ) : 0 ≤ initialElementaryConstant A V := by
  unfold initialElementaryConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_child_energy_elementary (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X lengthScale K A Vmax a b : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV : ∀ t,‖V t‖ ≤ Vmax) (hs : ∀ t,V t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (tn rn : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X tn rn a b ≤
      initialElementaryConstant A Vmax*K*X^2*lengthScale := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · have hb := childEnergy_elementary_normalized p hp hcop hg hc hinj F Ψ hΨ m T V
      X lengthScale K A Vmax a b hX hL hK hA hVmax hV hs hT tn rn
    have hXL : 0 < X*lengthScale := mul_pos hX (zero_lt_one.trans_le hL)
    have hb' := (div_le_iff₀ hXL).mp hb
    rw [max_eq_right hscale] at hb'
    convert hb' using 1
    unfold initialElementaryConstant
    field_simp

  · rw [childEnergy_subunit p hp hcop hg F Ψ m T V X A hX hs
      (lt_of_not_ge hscale) a b tn rn]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)

include hc hinj in

theorem initial_child_geometric_elementary (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (q : Frequency) :
    childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤
      initialElementaryConstant A Vmax*K*(X*lengthScale)^2 := by
  let E := initialElementaryConstant A Vmax*K*X^2*lengthScale
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)
  have he₁ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₁ hΨ₁ m T V₁
    X lengthScale K A Vmax q.1 q.2.2 hX hL hK hA hVmax hV₁ hs₁ hT true false
  have he₂ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₂ hΨ₂ m T V₂
    X lengthScale K A Vmax q.2.1 q.2.2 hX hL hK hA hVmax hV₂ hs₂ hT false true
  have hb : childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤ E := by
    calc
      _ ≤ Real.sqrt E*Real.sqrt E := mul_le_mul (Real.sqrt_le_sqrt he₁)
        (Real.sqrt_le_sqrt he₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = E := Real.mul_self_sqrt hE
  apply hb.trans
  calc
    E ≤ E*lengthScale := le_mul_of_one_le_right hE hL
    _ = _ := by dsimp only [E]; ring

include hp in

theorem initial_subbin_target_bounds (F R : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (Z M : ℝ) (j : SecondLogIndex)
    (s : Finset (SecondExpansionData ι)) (hs : s ⊆ secondLogSector p ∅ F K R Z M j) :
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),z.1 ≠ ⊥ ∧
      (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
  apply sourceIdealTarget_bounds
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  have hx' := hs hx
  obtain ⟨hxsec,hj⟩ := Finset.mem_filter.mp hx'
  have hk := (secondSupportedSector_mem p F K R Z M x hxsec).2.2.2.1
  have hji : initialLogIndex p x=j := (initialLogIndex_eq_second p x).trans hj
  have ht := initial_log_target_bounds p hp x hk
  rw [hji] at ht
  refine ⟨?_,ht.1,?_⟩
  · exact mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  · exact ht.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num))
      (normLogScale_pos _).le)

include hc hinj in

theorem initial_subbin_geometric_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z M A Vmax : ℝ)
    (hZ : 0 < Z) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (q : Frequency) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
    childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (sourceIdealTarget (s.image (sourceObservation p))) V₁ V₂ X X q ≤
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*(X*initialLogLabel j)^2 := by
  dsimp only
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < initialLogColumn Z (primeProductNorm p R) j :=
    div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hL : 1 ≤ initialLogLabel j := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  exact initial_child_geometric_elementary p hp hcop hg hc hinj F
    (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (fun a => (secondRayMinus_norm_le Ψ ray a).trans (hΨ a))
    (fun a => (secondRayPlus_norm_le Ψ ray a).trans (hΨ a)) _ _ V₁ V₂
    _ _ _ A Vmax hX hL hrow hA hVmax hV₁ hV₂ hs₁ hs₂
    (initial_subbin_target_bounds p hp F R K Z M j s hs) q

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRestrictedBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (Z H ε : ℝ) (j : SecondLogIndex)
    (V₁ V₂ : ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃))

lemma initialRestrictedBinCost_full {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray
      (secondLogSector p ∅ F K R Z M j) Z H ε j (windows 5) (windows 6) B =
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B := rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_subbin_density_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃)) ≤
    (Cs*(initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2)/
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N)*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  dsimp only
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) V₁ V₂ X X
  let E := initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hE : 0 ≤ E := mul_nonneg
    (mul_nonneg (initialElementaryConstant_nonneg A Vmax) (mul_nonneg hk.le (Real.exp_pos _).le))
    (sq_nonneg _)
  have hG : ∀ q,0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound (q : Frequency) : G q ≤ E :=
    (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) V₁ V₂ X X q).trans
    (initial_subbin_geometric_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z M A Vmax
      hZ hA hVmax j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ q)
  have hweighted (q : Frequency) :
      G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    have h₁ := one_le_pow₀ (show 1 ≤ 1+‖q.1‖ by linarith [norm_nonneg q.1]) (n := J)
    have h₂ := one_le_pow₀ (show 1 ≤ 1+‖q.2.1‖ by linarith [norm_nonneg q.2.1]) (n := J)
    have h₃ := one_le_pow₀ (show 1 ≤ 1+‖q.2.2‖ by linarith [norm_nonneg q.2.2]) (n := J)
    exact (hbound q).trans ((le_mul_of_one_le_right hE h₁).trans
      ((le_mul_of_one_le_right (mul_nonneg hE (zero_le_one.trans h₁)) h₂).trans
        (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hE (zero_le_one.trans h₁))
          (zero_le_one.trans h₂)) h₃)))
  exact polynomial_density_cost B G J _ Cs E (by positivity) hCs hE hB hG hdec hweighted

include hc hinj in

theorem initial_subbin_cost_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
    ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  have hb := initial_subbin_density_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    A Vmax Cs hZ hH hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  have h := mul_le_mul_of_nonneg_left hb hpref
  apply h.trans_eq
  rw [initial_log_mass Z (primeProductNorm p R) hR.ne',mul_pow]
  have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
  rw [he]
  have hz := hZ.ne'
  have hr := hR.ne'
  field_simp

end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRadial (Z H R : ℝ) (j : SecondLogIndex) : ℝ :=
  H*secondLogK j*R^2/Z^2

theorem initial_radial_absorbs_rows (Z H R k : ℝ) (N : ℕ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hR : 1 ≤ R) (hk : 0 ≤ k) :
    H*k^2/(1+H*k*R^2/Z^2)^(N+2) ≤ Z^4/(1+H*k*R^2/Z^2)^N := by
  let r := H*k*R^2/Z^2
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have h1 : 0 < 1+r := by linarith
  have hHR : 1 ≤ H*R^4 := one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hR)
  have he : Z^4*r^2=(H*k^2)*(H*R^4) := by
    dsimp [r]
    field_simp

  have hnum : H*k^2 ≤ Z^4*r^2 := by
    rw [he]
    exact le_mul_of_one_le_right (mul_nonneg hH0 (sq_nonneg k)) hHR
  change H*k^2/(1+r)^(N+2) ≤ Z^4/(1+r)^N
  calc
    _ ≤ Z^4*r^2/(1+r)^(N+2) := div_le_div_of_nonneg_right hnum (pow_nonneg h1.le _)
    _ ≤ Z^4*(1+r)^2/(1+r)^(N+2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg h1.le _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr (by linarith) 2) (by positivity)
    _ = _ := by rw [pow_add]; field_simp

def initialHighRadialConstant (A Vmax Cs : ℝ) : ℝ :=
  Real.exp 8*initialElementaryConstant A Vmax*Cs*(∫ t : ℝ,firstLogDensity 0 t)^3

lemma initialHighRadialConstant_nonneg (A Vmax Cs : ℝ) (hCs : 0 ≤ Cs) :
    0 ≤ initialHighRadialConstant A Vmax Cs := by
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hc := initialElementaryConstant_nonneg A Vmax
  unfold initialHighRadialConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_subbin_cost_radial_decay (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
      initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖/(1+initialRadial Z H (primeProductNorm p R) j)^N := by
  have hH0 := zero_lt_one.trans_le hH
  have hb := initial_subbin_cost_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    ε A Vmax Cs hZ hH0 hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J (N+2) hB hdec
  have hR1 := primeProductNorm_ge_one p hp R
  have hR0 := zero_lt_one.trans_le hR1
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hrowpow : (secondLogK j*Real.exp 2)^ε ≤ secondLogK j*Real.exp 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hrow hε
  have hcc := initialElementaryConstant_nonneg A Vmax
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hpref : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖ := by positivity
  have hden : 0 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) := by positivity
  apply hb.trans
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*
        (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
        (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*
        (secondLogK j*Real.exp 2)/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrowpow hpref) hden
    _ = (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (H*(secondLogK j)^2/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)) := by
      unfold initialHighRadialConstant
      have he : Real.exp 4*(Real.exp 2)^2=Real.exp 8 := by
        rw [pow_two,←Real.exp_add,←Real.exp_add]; norm_num
      rw [←he]
      ring
    _ ≤ (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (Z^4/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N) :=
      mul_le_mul_of_nonneg_left (initial_radial_absorbs_rows Z H (primeProductNorm p R)
        (secondLogK j) N hZ hH hR1 hk.le) (by positivity)
    _ = _ := by unfold initialRadial; ring

end InitialMeanSquare

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.SourceRemainders -/

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
open scoped BigOperators Classical

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialHighRadialCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ)
    (Z H U Kmax ε θ : ℝ) (V₁ V₂ : ℝ → ℂ) : ℝ :=
  ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F U,∑ j ∈ secondLogBinBox U Kmax,
    if Z^θ < initialRadial Z H (primeProductNorm p R) j then
      initialRestrictedBinCost p hp hcop hg F R Ψ m ray (s ray R j) Z H ε j V₁ V₂ (B ray R j)
    else 0

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_high_radial_sum (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε θ A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (hs : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
      s ray R j ⊆ secondLogSector p ∅ F K R Z M j)
    (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J N : ℕ)
    (hB : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q)
    (hdec : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤
      (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := by
  have hconstant := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hzpow : 0 < Z^θ := Real.rpow_pos_of_pos hZ _
  unfold initialHighRadialCost
  apply initial_harmonic_aggregation p hinj F U Kmax _ (by positivity)
  intro ray R hR j hj
  split_ifs with hh
  · have hc' := initial_subbin_cost_radial_decay p hp hcop hg hc hinj F R Ψ hΨ m ray K
      Z H M ε A Vmax Cs hZ hH hε hA hVmax hCs j (s ray R j) (hs ray R hR j hj)
      V₁ V₂ hV₁ hV₂ hs₁ hs₂ (B ray R j) J N (hB ray R hR j hj) (hdec ray R hR j hj)
    have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
    have hd : (Z^θ)^N ≤ (1+initialRadial Z H (primeProductNorm p R) j)^N :=
      pow_le_pow_left₀ hzpow.le (by linarith) N
    have hnum : 0 ≤ initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by positivity
    apply hc'.trans
    calc
      _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖)/(Z^θ)^N :=
        div_le_div_of_nonneg_left hnum (pow_pos hzpow _) hd
      _ = _ := by ring
  · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
    positivity

end

theorem initial_log_harmonic_polynomial :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := initial_log_box_small_power 1 (by norm_num)
  refine ⟨C*(256*Real.exp 1),by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  have hc := hbound Y U Kmax hY hU hK hUY hKY
  rw [Real.rpow_one] at hc
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hY)
  have hlog : (normLogBin U : ℝ)+1 ≤ 2*Y := by linarith
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ (256*Real.exp 1)*Y := by
    have he := Real.exp_pos (1:ℝ)
    nlinarith
  have hnon : 0 ≤ 128*Real.exp 1*(normLogBin U+1 : ℝ) := by positivity
  calc
    _ ≤ (C*Y)*((256*Real.exp 1)*Y) := mul_le_mul hc hh hnon (by positivity)
    _ = _ := by ring

theorem initial_high_radial_order (θ τ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ,38+τ ≤ θ*(N : ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((38+τ)/θ)
  refine ⟨N,?_⟩
  have hh := (div_lt_iff₀ hθ).mp hN
  linarith

theorem initial_high_radial_negligible (θ τ A Vmax Cs Ccap : ℝ) (N : ℕ)
    (hN : 38+τ ≤ θ*(N : ℝ)) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hCs : 0 ≤ Cs) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
      (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε : ℝ),
      1 ≤ Z → 1 ≤ H → 0 < U → 0 < Kmax → ε ≤ 1 →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
        s ray R j ⊆ secondLogSector p ∅ F K R Z M j) →
      ∀ (V₁ V₂ : ℝ → ℂ),
      (∀ t,‖V₁ t‖ ≤ Vmax) → (∀ t,‖V₂ t‖ ≤ Vmax) →
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) → (∀ t,V₂ t ≠ 0 → |t| ≤ A) →
      ∀ (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J : ℕ),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q) →
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
        Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) →
      initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤ C*Z^(-τ) := by
  obtain ⟨Clog,hClog,hlog⟩ := initial_log_harmonic_polynomial
  let Cbase := initialHighRadialConstant A Vmax Cs*initialRayMass*Clog*Ccap^2
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hray := initialRayMass_nonneg
  have hbase : 0 ≤ Cbase := by
    dsimp [Cbase]
    exact mul_nonneg (mul_nonneg (mul_nonneg hfixed initialRayMass_nonneg) hClog.le) (sq_nonneg _)
  refine ⟨Cbase+1,by linarith,?_⟩
  intro ι _ p hp _ hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε hZ hH hU hK hε hUcap hKcap
    s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J hB hdec
  have hZ0 := zero_lt_one.trans_le hZ
  have hy : 1 ≤ Ccap*Z^17 := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog (Ccap*Z^17) U Kmax hy hU hK hUcap hKcap
  have hb := initial_high_radial_sum p hp hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε θ
    A Vmax Cs hZ0 hH hε hA hVmax hCs s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hscalar : Z^(38 : ℕ)/(Z^θ)^N ≤ Z^(-τ) := by
    have he : Z^(38 : ℕ)/(Z^θ)^N=Z^((38 : ℝ)-θ*(N : ℝ)) := by
      rw [Real.rpow_sub hZ0,Real.rpow_mul_natCast hZ0.le]
      norm_cast
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := hb
    _ = ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (Clog*(Ccap*Z^17)^2) := mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = Cbase*(Z^(38 : ℕ)/(Z^θ)^N) := by dsimp [Cbase]; ring
    _ ≤ Cbase*Z^(-τ) := mul_le_mul_of_nonneg_left hscalar hbase
    _ ≤ (Cbase+1)*Z^(-τ) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ0.le _)

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

theorem initialErrorFrequencyBound_le (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    initialErrorFrequencyBound a b Z H ≤
      48*(1+Real.exp (initialErrorWindow a b))^16*Z^16 := by
  let Q := 1+Z*Real.exp (initialErrorWindow a b)
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    have hh : 0 ≤ Z*Real.exp (initialErrorWindow a b) := by positivity
    linarith
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have h3 : Q^3/H ≤ Q^3 := div_le_self (pow_nonneg hQ0 _) hH
  have hinner : 1+Q^3/H ≤ 2*Q^3 := by linarith [one_le_pow₀ hQ (n := 3)]
  have hT : initialTailHeight Z H (initialErrorWindow a b) ≤ 2*Q^5 := by
    change Q^2*(1+Q^3/H) ≤ 2*Q^5
    calc
      _ ≤ Q^2*(2*Q^3) := mul_le_mul_of_nonneg_left hinner (sq_nonneg Q)
      _ = _ := by ring
  have hT0 : 0 ≤ initialTailHeight Z H (initialErrorWindow a b) :=
    (initialTailHeight_pos Z H _ hZ0 hH0).le
  have hv : initialTailHeight Z H (initialErrorWindow a b)*Q^3/H ≤ 2*Q^8 := by
    calc
      _ ≤ initialTailHeight Z H (initialErrorWindow a b)*Q^3 :=
        div_le_self (mul_nonneg hT0 (pow_nonneg hQ0 _)) hH
      _ ≤ (2*Q^5)*Q^3 := mul_le_mul_of_nonneg_right hT (pow_nonneg hQ0 _)
      _ = _ := by ring
  have hv2 : initialTailHeight Z H (initialErrorWindow a b)*Q^3/H+2 ≤ 4*Q^8 := by
    linarith [one_le_pow₀ hQ (n := 8)]
  have hb : initialErrorFrequencyBound a b Z H ≤ 48*Q^16 := by
    unfold initialErrorFrequencyBound
    change 3*(initialTailHeight Z H (initialErrorWindow a b)*Q^3/H+2)^2 ≤ _
    calc
      _ ≤ 3*(4*Q^8)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hv2 2) (by norm_num)
      _ = _ := by ring
  have hQZ : Q ≤ (1+Real.exp (initialErrorWindow a b))*Z := by
    dsimp [Q]
    nlinarith
  calc
    _ ≤ 48*Q^16 := hb
    _ ≤ 48*((1+Real.exp (initialErrorWindow a b))*Z)^16 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQZ 16) (by norm_num)
    _ = _ := by rw [mul_pow]; ring

def initialErrorRowBound (a b Z H : ℝ) : ℝ :=
  Z*Real.exp (initialErrorWindow a b)*initialErrorFrequencyBound a b Z H

lemma initialErrorRowBound_pos (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H) :
    0 < initialErrorRowBound a b Z H := by
  have ht := initialTailHeight_pos Z H (initialErrorWindow a b) hZ hH
  unfold initialErrorRowBound initialErrorFrequencyBound
  positivity

theorem initialErrorRowBound_valid {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F (fun _ _ => initialErrorCutoff a b Z H) R Z
      (initialErrorWindow a b)) :
    elementNorm (sourceObservation p x).1 ≤ initialErrorRowBound a b Z H := by
  obtain ⟨hG,hE,hV,hk,hkf,hR,hs⟩ := secondSupportedSector_mem p F
    (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) x hx
  have he := (secondSourceSupport_bounds p hp Z (initialErrorWindow a b) x hs hE).2.1
  have hf := initialErrorCutoff_norm_bound a b Z H hZ hH x.frequency hkf
  have hh := mul_le_mul he hf (sq_nonneg ‖eisEmbedding x.frequency‖) (by positivity)
  simpa only [initialErrorRowBound,sourceObservation,elementNorm,map_mul,norm_mul,mul_pow,
    primeSubsetGenerator_norm_eq_productNorm] using hh

def initialPolynomialCap (a b : ℝ) : ℝ :=
  1+Real.exp (initialErrorWindow a b)+
    48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16

lemma initialPolynomialCap_ge_one (a b : ℝ) : 1 ≤ initialPolynomialCap a b := by
  unfold initialPolynomialCap
  have he := Real.exp_pos (initialErrorWindow a b)
  have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
  linarith

theorem initial_actual_bin_polynomial_caps (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    Z*Real.exp (initialErrorWindow a b) ≤ initialPolynomialCap a b*Z^17 ∧
    initialErrorRowBound a b Z H ≤ initialPolynomialCap a b*Z^17 := by
  have he := Real.exp_pos (initialErrorWindow a b)
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hz17 : Z ≤ Z^17 := by
    simpa only [pow_one] using pow_le_pow_right₀ hZ (by decide : 1 ≤ 17)
  have hC1 : Real.exp (initialErrorWindow a b) ≤ initialPolynomialCap a b := by
    unfold initialPolynomialCap
    have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
    linarith
  have hC2 : 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 ≤
      initialPolynomialCap a b := by
    unfold initialPolynomialCap
    have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
    linarith
  constructor
  · calc
      _ ≤ Real.exp (initialErrorWindow a b)*Z^17 := by
        rw [mul_comm Z]; exact mul_le_mul_of_nonneg_left hz17 he.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hC1 (pow_nonneg hZ0 _)
  · have hb := mul_le_mul_of_nonneg_left (initialErrorFrequencyBound_le a b Z H hZ hH)
      (mul_nonneg hZ0 he.le)
    change initialErrorRowBound a b Z H ≤ _ at hb
    calc
      _ ≤ (Z*Real.exp (initialErrorWindow a b))*(48*(1+Real.exp (initialErrorWindow a b))^16*Z^16) := hb
      _ = (48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16)*Z^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 (pow_nonneg hZ0 _)

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem initial_two_windows_bounded (V₁ V₂ : ℝ → ℂ)
    (hc₁ : HasCompactSupport V₁) (hc₂ : HasCompactSupport V₂)
    (hs₁ : Continuous V₁) (hs₂ : Continuous V₂) :
    ∃ A Vmax : ℝ,0 ≤ A ∧ 0 ≤ Vmax ∧
      (∀ t,‖V₁ t‖ ≤ Vmax) ∧ (∀ t,‖V₂ t‖ ≤ Vmax) ∧
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) ∧ (∀ t,V₂ t ≠ 0 → |t| ≤ A) := by
  obtain ⟨A₁,hA₁,hbound₁⟩ := hc₁.exists_pos_le_norm
  obtain ⟨A₂,hA₂,hbound₂⟩ := hc₂.exists_pos_le_norm
  obtain ⟨B₁,hB₁⟩ := hc₁.exists_bound_of_continuous hs₁
  obtain ⟨B₂,hB₂⟩ := hc₂.exists_bound_of_continuous hs₂
  refine ⟨max A₁ A₂,max 0 (max B₁ B₂),?_,le_max_left _ _,?_,?_,?_,?_⟩
  · exact hA₁.le.trans (le_max_left _ _)
  · intro t
    exact (hB₁ t).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro t
    exact (hB₂ t).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro t ht
    have hh : ‖t‖ < A₁ := lt_of_not_ge (fun h => ht (hbound₁ t h))
    simpa only [Real.norm_eq_abs] using hh.le.trans (le_max_left A₁ A₂)
  · intro t ht
    have hh : ‖t‖ < A₂ := lt_of_not_ge (fun h => ht (hbound₂ t h))
    simpa only [Real.norm_eq_abs] using hh.le.trans (le_max_right A₁ A₂)

theorem initial_high_radial_source
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b θ τ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hθ : 0 < θ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (Z H : ℝ),
      1 ≤ Z → 1 ≤ H → (∀ x,‖Ψ x‖ ≤ 1) →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray R j,s ray R j ⊆ secondLogSector p ∅ F
        (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) j) →
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      C*Z^(-τ) := by
  obtain ⟨N,hN⟩ := initial_high_radial_order θ τ hθ
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W (initialErrorWindow a b) hM hU hgs ε hε (N+2) 0
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded (windows 5) (windows 6) (hwc 5) (hwc 6)
      (hws 5).continuous (hws 6).continuous
  obtain ⟨Ch,hCh,hh⟩ := initial_high_radial_negligible θ τ A Vmax Cs (initialPolynomialCap a b)
    N hN hA hVmax hCs (initialPolynomialCap_ge_one a b)
  refine ⟨Ct*Ch+1,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m Z H hZ hH hΨ s hs
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  let K := fun (_ _ : Finset ι) => initialErrorCutoff a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hcost := hh p hp hcop hg hc hinj F Ψ hΨ m K Z H
    (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H)
    (initialErrorWindow a b) ε hZ hH (by positivity) (initialErrorRowBound_pos a b Z H hZ0 hH0)
    hε1 (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
    s (fun ray R _ j _ => hs ray R j) (windows 5) (windows 6) hV₁ hV₂ hs₁ hs₂ B 0
    (fun ray R _ j _ => (hB ray R j).1) (fun ray R _ j _ => (hB ray R j).2.1)
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := by
    unfold initialHighRadialCost
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hjrad
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialRestrictedBinCost,G,B] ; ring
    · simp
  calc
    _ ≤ Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := hsum
    _ ≤ Ct*(Ch*Z^(-τ)) := mul_le_mul_of_nonneg_left hcost hCt
    _ ≤ (Ct*Ch+1)*Z^(-τ) := by
      have hz := Real.rpow_nonneg hZ0.le (-τ)
      nlinarith

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeBlockExponent_ne_zero_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
  intro i hi
  by_cases hn:i∈N
  · simp [threeBlockExponent,hn]
  by_cases hp':i∈P
  · simp [threeBlockExponent,hn,hp']
  · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
    simp only [threeBlockExponent,ite_eq_right hn,ite_eq_right hp']
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2

lemma threeBlockExponent_lt_six_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
  intro i hi
  unfold threeBlockExponent
  split_ifs <;> first | omega | exact ZMod.val_lt _

lemma threeGaussRowFactor_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O) :
    ‖threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h‖≤‖C₁ N‖*‖C₂ P‖ := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hG := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i:S=>p i.val) (fun i=>hp i.val) (columnPrimeCoprime p hcop S)
    (fun i=>hg i.val) (fun i=>hc i.val) (fun i=>e i.val)
    (fun i=>threeBlockExponent_ne_zero_on N P B v ε₁ ε₂ i.val i.property)
    (fun i=>threeBlockExponent_lt_six_on N P B v ε₁ ε₂ i.val i.property)
  change ‖star (columnCoefficient p hp hcop hg N*C₁ N)*
    (columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S=>p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val)*
    (blockRow p hg S e d*star (blockRow p hg S e h))‖≤_
  simp only [norm_mul,norm_star,SecondPassArithmetic.columnCoefficient_norm_one p hp hcop hg hc,
    hG,one_mul,mul_one]
  apply mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg S e d)).trans (blockRow_norm_le_one p hg S e h)

lemma canonicalPairMode_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d h : O) :
    ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖)*
        (‖C₁ N‖*‖C₂ P‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖ := by
  have hn : 0<‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi=>hp i)))
  have ha : K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
      primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) =
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by ring
  simp only [canonicalPairMode,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hK,abs_of_pos hn,ha]
  calc
    _ ≤ (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖*
      (‖C₁ N‖*‖C₂ P‖) := mul_le_mul_of_nonneg_left
        (threeGaussRowFactor_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ d h) (by positivity)
    _ = _ := by ring

end

theorem full_uniform_canonicalPairMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K H : ℝ),0<K → 0≤H → ∀(d : O),d≠0 → ∀T:Finset O,
      let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      (∀h:O,h∉T → H≤ scale*‖eisEmbedding h‖^2) →
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K H hK hH d hd T
  dsimp only
  intro hT
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  let c := ‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖)
  have hscale : 0<scale := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hc0 : 0≤ c := by dsimp [c]; positivity
  let small : Set O := {h|h∉T}
  let large : Set O := {h|H≤ scale*‖eisEmbedding h‖^2}
  let f : small→large := fun h=>⟨h.val,hT h.val h.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x:large=>x.val) hab)
  have hrad := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale
  have hmajor := (hrad.subtype small).mul_left c
  have hpnt (h:small) :
      ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
    canonicalPairMode_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d h.val
  have hsmall := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑'h:small,‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖ :=
      norm_tsum_le_tsum_norm hsmall
    _ ≤ ∑'h:small,c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      hsmall.tsum_le_tsum hpnt hmajor
    _ = c*∑'h:small,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ := tsum_mul_left
    _ ≤ c*∑'h:large,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      mul_le_mul_of_nonneg_left ((hrad.subtype small).tsum_le_tsum_of_inj f hfi
        (fun _ _=>norm_nonneg _) (fun _=>le_rfl) (hrad.subtype large)) hc0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb W scale H hscale hH) hc0

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open SecondPassArithmetic (firstFrequencyDisk outside_firstFrequencyDisk columnLog_norm_upper)

def canonicalFirstFrequencyRadius {ι : Type*} [DecidableEq ι]
    (p : ι→O) (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (d : O) (X₁ X₂ K P : ℝ) : ℝ :=
  P*(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*X₁*X₂)/K

theorem firstFrequencyDisk_uniform {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0)
    (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hNQ : Disjoint N Q) (hNB : Disjoint N B) (hQB : Disjoint Q B)
    (d : O) (hd : d≠0) (X₁ X₂ K P M₁ M₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hK : 0<K)
    (hN : columnLog p X₁ N≤M₁) (hQ : columnLog p X₂ Q≤M₂)
    (h : O) (hh : h∉firstFrequencyDisk
      (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)) :
    P/Real.exp (M₁+M₂)≤
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by
  let S := cubeActiveSupport B v ε₁ ε₂
  have hNS : Disjoint N S := hNB.mono_right (Finset.filter_subset _ _)
  have hQS : Disjoint Q S := hQB.mono_right (Finset.filter_subset _ _)
  have hNQS : Disjoint (N∪Q) S := Finset.disjoint_union_left.mpr ⟨hNS,hQS⟩
  have hnorm : primeProductNorm p ((N∪Q)∪S)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p S := by
    rw [primeProductNorm_union p _ _ hNQS,primeProductNorm_union p _ _ hNQ]
  have hNd : 0<‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hU₁ : 0<X₁*Real.exp M₁ := mul_pos hX₁ (Real.exp_pos _)
  have hU₂ : 0<X₂*Real.exp M₂ := mul_pos hX₂ (Real.exp_pos _)
  let slow := K/(‖eisEmbedding d‖^2*(X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S)
  have hs : 0<slow := div_pos hK (mul_pos (mul_pos (mul_pos hNd hU₁) hU₂) (primeProductNorm_pos p hp S))
  have hn := columnLog_norm_upper p hp X₁ M₁ hX₁ N hN
  have hq := columnLog_norm_upper p hp X₂ M₂ hX₂ Q hQ
  have hprod : primeProductNorm p N*primeProductNorm p Q≤(X₁*Real.exp M₁)*(X₂*Real.exp M₂) :=
    mul_le_mul hn hq (primeProductNorm_pos p hp Q).le hU₁.le
  have hscale : slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪S)) := by
    apply div_le_div_of_nonneg_left hK.le
      (mul_pos hNd (primeProductNorm_pos p hp _))
    rw [hnorm]
    calc
      _ ≤ ‖eisEmbedding d‖^2*((X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
      _ = _ := by ring
  have hr : (P/Real.exp (M₁+M₂))/slow=
      canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P := by
    dsimp [slow,canonicalFirstFrequencyRadius,S]
    rw [Real.exp_add]
    field_simp

  have ho := outside_firstFrequencyDisk _ h hh
  rw [←hr] at ho
  have hbase : P/Real.exp (M₁+M₂)≤ slow*‖eisEmbedding h‖^2 := by
    have hz := (div_lt_iff₀ hs).mp ho
    simpa only [mul_comm] using hz.le
  exact hbase.trans (mul_le_mul_of_nonneg_right hscale (sq_nonneg _))

theorem full_uniform_canonicalPairMode_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      Disjoint N Q → Disjoint N B → Disjoint Q B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K P M₁ M₂ : ℝ),0<X₁ → 0<X₂ → 0<K → 0≤P →
      columnLog p X₁ N≤M₁ → columnLog p X₂ Q≤M₂ → ∀(d : O),d≠0 →
      let S := (N∪Q)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ Q)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ Q‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 scale)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N Q B v ε₁ ε₂ hNQ hNB hQB C₁ C₂ W V₁ V₂ X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP hN hQ d hd
  apply hb p hp hcop hg hc N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K _ hK
    (div_nonneg hP (Real.exp_pos _).le) d hd
  intro h hh
  exact firstFrequencyDisk_uniform p hp N Q B v ε₁ ε₂ hNQ hNB hQB d hd
    X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hN hQ h hh

end FirstPassCubeLabels

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.DualZeroMode -/

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
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FiniteGaussPhase (canonicalProductGauss_cross_factors)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeGaussRowFactor_empty
    (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O)
    (hB : cubeActiveSupport B v ε₁ ε₂=∅) :
    threeGaussRowFactor p hp hcop hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d h=
      star (C₁ ∅)*C₂ ∅ := by
  let : IsEmpty {i:ι // i∈(((∅:Finset ι)∪∅)∪cubeActiveSupport B v ε₁ ε₂)} :=
    ⟨fun x=>by simpa [hB] using x.property⟩
  simp [MixedCrossSeparation.columnCoefficient,FiniteGaussPhase.canonicalProductCoefficient,
    threeGaussRowFactor,canonicalProductGauss_cross_factors,FiniteGaussPhase.angularFactor,
    blockRow,finiteSexticRow]

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma canonicalCubeResidual_empty (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) :
    canonicalCubeResidual p hg b C negative Ψ m f H ∅=
      H ((if negative then b.rightDivisor else b.leftDivisor)∪C) := by
  simp [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,
    finiteSquarefreeRow,rowCoprimeMask]

def canonicalCubeDualZero (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) 0

theorem canonicalCubeDualZero_eq_density
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
          (star (H₁ (b.rightDivisor∪C))*H₂ (b.leftDivisor∪C))*
          (K:ℂ)*paperRadialFourier W 0*
          ∏i∈C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit,
            (1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i}))
      else 0 := by
  unfold canonicalCubeDualZero
  simp_rw [actualFirstKernel_zero]
  split_ifs with hB
  · simp only [threeGaussRowFactor_empty p hp hcop hg _ _ _ _ _ _ _ _ hB,
      canonicalCubeResidual_empty,Bool.false_eq_true,ite_true,ite_false,one_mul]
    rw [←Finset.sum_mul]
    have hprime (i : ι) : Prime (Ideal.span {p i}) :=
      Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
    have hd (D : Finset ι) : (primeProductNorm p D:ℂ)=
        (Ideal.absNorm (∏i∈D,Ideal.span {p i}):ℂ) := by
      rw [primeProductNorm_eq_ideal_norm,Complex.ofReal_natCast]
    simp_rw [hd]
    rw [primeSubset_moebius_norm_sum _ hprime hinj]
    ring
  · simp only [mul_zero,Finset.sum_const_zero]

theorem canonicalCubeDualZero_norm_le
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        ‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖*|K| *‖paperRadialFourier W 0‖ else 0 := by
  rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
  split_ifs with hB
  · let M := C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
    have hprod : (∏i∈M,(1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i})))=
        ((∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i}))):ℝ) := by
      simp only [Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,
        Complex.ofReal_div,Complex.ofReal_natCast]
    rw [show (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)=M from rfl,hprod]
    simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).1]
    calc
      _ ≤ 1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖*
          ∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i})) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (abs_nonneg _)) (norm_nonneg _))
          (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).1
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_of_le_one_right
          (show 0≤(1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖) by positivity)
          (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).2
  · simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels

theorem boundedPrimeSupports_card_positive {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (X : ℝ) (hX : 0<X) :
    ((boundedPrimeSupports p F X).card:ℝ)≤128*X := by
  by_cases hx : 1≤X
  · exact boundedPrimeSupports_card p hinj F X hx
  · have he : boundedPrimeSupports p F X=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hx ((primeProductNorm_ge_one p hp S).trans (Finset.mem_filter.mp hS).2)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end SecondPassArithmetic

namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open SecondPassArithmetic (boundedPrimeSupports boundedPrimeSupports_card_positive
  columnLog_norm_upper firstFrequencyDisk primeProductNorm_ge_one)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem actualFirstKernel_complement_eq_pairs
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) (T : Finset O) :
    (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val)=
      ∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
        ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val
        else 0 := by
  have hs (N Q : Finset ι) : Summable (fun h:{h:O // h∉T}=>if Disjoint N Q then
      canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0) := by
    by_cases hNQ : Disjoint N Q
    · simp only [hNQ,ite_true]
      exact (canonicalPairMode_summable p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).subtype _
    · simp only [hNQ,ite_false]
      exact summable_zero
  change (∑'h:{h:O // h∉T},∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
    canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN=>summable_sum (fun Q hQ=>hs N Q))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun Q hQ=>hs N Q)]
  apply Finset.sum_congr rfl
  intro Q hQ
  split_ifs <;> simp

end

theorem full_uniform_actualFirstKernel_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_disk_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let T:=firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
  let slow:=K/(‖eisEmbedding d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖eisEmbedding d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P/Real.exp (M₁+M₂):=div_nonneg hP (Real.exp_pos _).le
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖eisEmbedding d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (eisEmbedding (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P/Real.exp (M₁+M₂))^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hcop hg hc N R B v ε₁ ε₂ hNR hNB hRB C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP (hS₁ N hNF hn) (hS₂ R hRF hr) d hd
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [ite_eq_left hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,ite_eq_right hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ (128*U₁)*(128*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))
  (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hinj

theorem canonicalCubeDualZero_support
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (ell K M : ℝ) (hell : 0<ell) (hgM : ∀t,g₁ t≠0→t≤M)
    (hC : ¬primeProductNorm p C≤ell*Real.exp M) :
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K=0 := by
  have hz : g₁ (columnLog p ell (b.rightDivisor∪C))=0 := by
    by_contra h
    exact hC ((primeProductNorm_mono p hp (Finset.subset_union_right)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
  split_ifs <;> simp [hz]

include hc

theorem canonicalCubeDualZero_fixed_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (G₁ G₂ ell K : ℝ) (hG₁ : 0≤G₁) (_hG₂ : 0≤G₂)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) :
    ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        G₁*G₂*|K| *‖paperRadialFourier W 0‖ else 0 := by
  apply (canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hg₁ _) (hg₂ _) (norm_nonneg _) hG₁) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

theorem canonicalCubeZero_common_sum_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ ell K M : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hell : 0<ell)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) (hgM : ∀t,g₁ t≠0→t≤M) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (128*(ell*Real.exp M))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by
  let z (C:Finset ι) (I:Ideal O):ℂ:=canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
    (ConcretePrimeRowBridge.idealGenerator I)
    (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K
  let Q:ℝ:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hL:0<ell*Real.exp M:=mul_pos hell (Real.exp_pos _)
  have heq : (∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I)=
      ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,a C I*z C I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hC hnot
    have hbnd : ¬primeProductNorm p C≤ell*Real.exp M:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
    apply Finset.sum_eq_zero
    intro I hI
    rw [show z C I=0 from canonicalCubeDualZero_support p hp hcop hg hinj pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell K M hell hgM hbnd,mul_zero]
  change ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I‖≤_
  rw [heq]
  by_cases hb : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  · rw [ite_eq_left hb]
    have hpnt (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)) (I:Ideal O) (hI:I∈labels):‖a C I*z C I‖≤Q:=by
      rw [norm_mul]
      have hz:=canonicalCubeDualZero_fixed_bound p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I) g₁ g₂ W G₁ G₂ ell K hG₁ hG₂ hg₁ hg₂
      rw [ite_eq_left hb] at hz
      exact mul_le_mul (ha C (Finset.mem_filter.mp hC).1 I hI) hz (norm_nonneg _) hΓ
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,‖a C I*z C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,Q:=
        Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun I hI=>hpnt C hC I hI))
      _ = ((boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)).card:ℝ)*(labels.card:ℝ)*Q:=by simp;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj _ _ hL) (Nat.cast_nonneg _)) hQ
  · rw [ite_eq_right hb]
    have hz (C:Finset ι) (I:Ideal O):z C I=0:=by
      dsimp [z]
      rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj,ite_eq_right hb]
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]

end

theorem full_uniform_canonicalFirstZero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ ell K M B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<ell → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) → (∀t,g₁ t≠0→t≤M) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      C*B^(1+ε)*(ell*Real.exp M)*F*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) := by
  obtain ⟨C,hC,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨C*128*128,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M B F hΓ hG₁ hG₂ hell hB hF hΨ₁ hΨ₂ hadm hb1 hb2 hI0 hIF ha hg₁ hg₂ hgM
  let Q:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  let good:=fun b:CubeCoordinates ι=>cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:((bs.filter good).card:ℝ)≤C*B^(1+ε):=by
    have h:=hcount p hp hinj (bs.filter good) B 1 hB (by norm_num)
      (fun b hb=>hadm b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb1 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb2 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>by
        have he : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ := (Finset.mem_filter.mp hb).2
        rw [he]
        simp)
    simpa only [mul_one] using h
  calc
    _ ≤ ∑b∈bs,‖∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,if good b then (128*(ell*Real.exp M))*(labels.card:ℝ)*Q else 0:=by
      apply Finset.sum_le_sum
      intro b hb
      exact canonicalCubeZero_common_sum_bound p hp hcop hg hinj hc pool b labels (a b) Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M hΓ hG₁ hG₂ hell (ha b hb) hg₁ hg₂ hgM
    _ = ((bs.filter good).card:ℝ)*((128*(ell*Real.exp M))*(labels.card:ℝ)*Q):=by
      rw [←Finset.sum_filter];simp
    _ ≤ (C*B^(1+ε))*((128*(ell*Real.exp M))*(128*F)*Q):=by
      apply mul_le_mul hbcount _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlabel (by positivity)) hQ
    _ = _ := by dsimp [Q];ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma originalLabelColumn_core_norm_le
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀u,‖Ψ u‖≤1) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H) c f S‖≤‖H S‖ := by
  have hm (z:O):‖rowCoprimeMask (fun i=>Ideal.span {p i}) S z‖≤1:=by
    unfold rowCoprimeMask;split_ifs <;> simp
  have hrow (z:O):‖finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z‖^4≤1:=by
    simpa using pow_le_pow_left₀ (norm_nonneg _)
      (finiteSquarefreeRow_norm_le_one (fun i=>Ideal.span {p i}) hg S z) 4
  simp only [originalLabelColumn,multiplicativeCoreColumn,norm_mul,norm_pow]
  calc
    _ ≤ 1*‖H S‖*1*1*1 := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul
            (mul_le_mul_of_nonneg_right
              ((mul_le_mul (hΨ _) (hm m) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) (norm_nonneg _))
            (hm _) (norm_nonneg _) (by positivity))
          (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity))
        (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma originalLabelColumn_core_test_ne_zero
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι)
    (h : originalLabelColumn p hg B ε₁ ε₂ negative
      (multiplicativeCoreColumn p Ψ m H) c f S≠0) : H S≠0 := by
  intro hz
  apply h
  simp only [originalLabelColumn,multiplicativeCoreColumn,hz,mul_zero,zero_mul]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem canonicalFirstFrequencyRadius_eq_global
    (b : CubeCoordinates ι) (hb : b.Admissible) (C D : Finset ι)
    (Ksrc K ell : ℝ) (hKsrc : 0<Ksrc) (hK : 0<K) :
    canonicalFirstFrequencyRadius p b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit (primeSubsetGenerator (fun i=>Ideal.span {p i}) D)
      (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
      (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) Ksrc (Ksrc/K)=
    globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D) := by
  have hl:b.swap.leftBit=b.rightBit:=rfl
  have hr:b.swap.rightBit=b.leftBit:=rfl
  simp only [canonicalFirstFrequencyRadius,globalFirstFrequencyScale,sourceGlobalBlock,
    cube_swap_support,cube_swap_sum,hl,hr,
    cubeActiveSupport_swap,primeSubsetGenerator_norm_eq_productNorm,
    CubeCoordinates.aLabel_left p b hb,CubeCoordinates.aLabel_right p b hb]
  change (Ksrc/K)*(primeProductNorm p D*primeProductNorm p
    (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*
    (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))*
    (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)))/Ksrc = _
  have hC:primeProductNorm p C≠0:=(primeProductNorm_pos p hp C).ne'
  have hL:primeProductNorm p b.leftDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  have hR:primeProductNorm p b.rightDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  simp only [primeProductNorm]
  simp only [primeProductNorm] at hC hL hR
  field_simp

end

theorem full_uniform_canonicalSource_kernel_tail (A : ℕ) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι),b.Admissible → ∀ C D:Finset ι,Disjoint C b.support →
      ∀(Ψ₁ Ψ₂:O→*ℂ),(∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      ∀(m₁ m₂ f:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (G₁ G₂ M₁ M₂ Ksrc K ell:ℝ),
      0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
      let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
      let U₁:=X₁*Real.exp M₁
      let U₂:=X₂*Real.exp M₂
      let slow:=Ksrc/(primeProductNorm p D*primeProductNorm p
        (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*U₁*U₂)
      let T:=firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun S=>g₁ (columnLog p ell S)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun S=>g₂ (columnLog p ell S)))
        W (fun _=>1) (fun _=>1) 1 1 Ksrc
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Ksrc)*
        ((Ctail*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+(Ksrc/K)/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,Ctail,hCtail,hbound⟩:=full_uniform_actualFirstKernel_disk_remainder A
  refine ⟨s,Ctail,hCtail,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool b hb C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂
  dsimp only
  let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
  let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
  have hX₁:0<X₁:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hX₂:0<X₂:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hFB:Disjoint (pool\(b.support∪C)) b.support:=Finset.disjoint_left.mpr (fun i hi hb=>
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hb))
  let C₁:=originalLabelColumn p hg b.support b.leftBit b.rightBit true
    (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) (∏i∈C,p i) f
  let C₂:=originalLabelColumn p hg b.support b.leftBit b.rightBit false
    (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) (∏i∈C,p i) f
  have hcoef₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₁ N‖≤G₁:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit true Ψ₁ hΨ₁ m₁ _ f _ N).trans (hg₁ _)
  have hcoef₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₂ N‖≤G₂:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit false Ψ₂ hΨ₂ m₂ _ f _ N).trans (hg₂ _)
  have hs₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₁ N≠0):columnLog p X₁ N≤M₁:=
    hM₁ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit true Ψ₁ m₁ _ f _ N hn)
  have hs₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₂ N≠0):columnLog p X₂ N≤M₂:=
    hM₂ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit false Ψ₂ m₂ _ f _ N hn)
  have h:=hbound p hp hinj hcop hg hc (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit hFB C₁ C₂ W
    G₁ G₂ X₁ X₂ Ksrc (Ksrc/K) M₁ M₂ hG₁ hG₂ hX₁ hX₂ hKsrc (div_pos hKsrc hK).le
    hcoef₁ hcoef₂ hs₁ hs₂ (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
  rw [canonicalFirstFrequencyRadius_eq_global p hp b hb C D Ksrc K ell hKsrc hK] at h
  simp only [primeSubsetGenerator_norm_eq_productNorm] at h
  have heq := fun h:O=>canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ f
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h g₁ g₂ W Ksrc ell hell
  simp_rw [heq]
  exact h

end SecondPassArithmetic

end

end OAI

end

