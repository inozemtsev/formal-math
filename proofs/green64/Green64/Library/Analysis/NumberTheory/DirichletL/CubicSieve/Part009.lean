module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.PrincipalNormalization -/

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
open SecondPassFiber (newLabel newRow)
open ConcretePrimeRowBridge (idealGenerator)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLabel (x : GlobalSecondData ι) : O :=
  secondSupportLabel p x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit (expansionSupportData x.common x.firstDivisor x.source)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondLabel_span (x : GlobalSecondData ι) :
    Ideal.span {globalSecondLabel p x}=newLabel (globalSecondTuple p x) :=
  actualSecondLabel_span p x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

def globalSecondLabelUnit (x : GlobalSecondData ι) : Oˣ :=
  Classical.choose (exists_label_unit (globalSecondLabel p x)
    (newLabel (globalSecondTuple p x)) (globalSecondLabel_span p x))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondLabelUnit_spec (x : GlobalSecondData ι) :
    globalSecondLabel p x=(globalSecondLabelUnit p x : O)*idealGenerator (newLabel (globalSecondTuple p x)) :=
  Classical.choose_spec (exists_label_unit (globalSecondLabel p x)
    (newLabel (globalSecondTuple p x)) (globalSecondLabel_span p x))

theorem global_second_energy_pushforward
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Finset (GlobalSecondData ι)) (t : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈t) →
      (∀ z∈t,z.1 ≠ ⊥) → (∀ z∈t,(Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x∈s,‖w x‖ ≤ B) →
      (∑ x∈s,‖w x‖ * ‖fixedChildRow p hp hcop hg F Ψ m H (globalSecondLabel p x)
        (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖^2) ≤
      B*C*(lengthScale*Ideal.absNorm q.1)^ε *
        ∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ m H negative u z‖^2 := by
  obtain ⟨C,hC,hcard⟩ := globalSecond_fiber_card p hinj ε hε
  refine ⟨C,hC,?_⟩
  intro s t q w B lengthScale F Ψ m H negative hq hB hL hs hfixed hmap ht hnorm hw
  let f : GlobalSecondData ι → Oˣ × (Ideal O × O) := fun x =>
    (globalSecondLabelUnit p x,newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))
  let P : Oˣ × (Ideal O × O) → ℂ := fun z => idealChildRow p hp hcop hg F Ψ m H negative z.1 z.2
  have hm : ∀ x∈s,f x∈Finset.univ ×ˢ t := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,hmap x hx⟩
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward s (Finset.univ ×ˢ t) f w P B hm hw
  have he : (∑ x∈s,‖w x‖ * ‖fixedChildRow p hp hcop hg F Ψ m H (globalSecondLabel p x)
      (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖^2) =
      ∑ x∈s,‖w x‖ * ‖P (f x)‖^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [globalSecondLabelUnit_spec p x]
    rfl
  rw [he]
  apply hpush.trans
  calc
    _ ≤ ∑ z∈Finset.univ ×ˢ t,B*C*(lengthScale*Ideal.absNorm q.1)^ε * ‖P z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hzt := (Finset.mem_product.mp hz).2
      have hc := hcard (s.filter (fun x => f x=z)) q z.2.1 z.2.2
        (fun x hx => hs x (Finset.mem_filter.mp hx).1) (ht z.2 hzt) hq
        (fun x hx => hfixed x (Finset.mem_filter.mp hx).1)
        (fun x hx => congrArg (fun z : Oˣ × (Ideal O × O) => z.2.1) (Finset.mem_filter.mp hx).2)
        (fun x hx => congrArg (fun z : Oˣ × (Ideal O × O) => z.2.2) (Finset.mem_filter.mp hx).2)
      have hn : (Ideal.absNorm z.2.1 : ℝ)*Ideal.absNorm q.1 ≤ lengthScale*Ideal.absNorm q.1 :=
        mul_le_mul_of_nonneg_right (hnorm z.2 hzt) (by positivity)
      have hc' := hc.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hn hε.le) hC.le)
      have hfinal := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' hB) (sq_nonneg ‖P z‖)
      simpa only [mul_assoc] using hfinal
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_product]

def globalSecondMode (s : Finset (GlobalSecondData ι)) (w : GlobalSecondData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ x∈s,w x * star (fixedChildRow p hp hcop hg F Ψ₁ m H₁
    (globalSecondLabel p x) (newRow (globalSecondTuple p x))) *
    fixedChildRow p hp hcop hg F Ψ₂ m H₂ (globalSecondLabel p x) (-newRow (globalSecondTuple p x))

theorem global_second_mode_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Finset (GlobalSecondData ι)) (t : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ),
      q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈t) →
      (∀ z∈t,z.1 ≠ ⊥) → (∀ z∈t,(Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x∈s,‖w x‖ ≤ B) →
      ‖globalSecondMode p hp hcop hg s w F Ψ₁ Ψ₂ m H₁ H₂‖ ≤
      B*C*(lengthScale*Ideal.absNorm q.1)^ε *
        Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) *
        Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) := by
  obtain ⟨C,hC,hpush⟩ := global_second_energy_pushforward p hp hcop hg hinj ε hε
  refine ⟨C,hC,?_⟩
  intro s t q w B lengthScale F Ψ₁ Ψ₂ m H₁ H₂ hq hB hL hs hfixed hmap ht hnorm hw
  let P₁ := fun x => fixedChildRow p hp hcop hg F Ψ₁ m H₁ (globalSecondLabel p x) (newRow (globalSecondTuple p x))
  let P₂ := fun x => fixedChildRow p hp hcop hg F Ψ₂ m H₂ (globalSecondLabel p x) (-newRow (globalSecondTuple p x))
  have h₁ := hpush s t q w B lengthScale F Ψ₁ m H₁ false hq hB hL hs hfixed hmap ht hnorm hw
  have h₂ := hpush s t q w B lengthScale F Ψ₂ m H₂ true hq hB hL hs hfixed hmap ht hnorm hw
  simp only [Bool.false_eq_true,ite_false,ite_true] at h₁ h₂
  let D := B*C*(lengthScale*Ideal.absNorm q.1)^ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCau := DescentWeightedCauchy.weighted_cauchy s w P₂ P₁
  have he : globalSecondMode p hp hcop hg s w F Ψ₁ Ψ₂ m H₁ H₂ =
      ∑ x∈s,w x*P₂ x*star (P₁ x) := by
    unfold globalSecondMode
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [P₁,P₂]
    ring
  rw [he]
  apply hCau.trans
  calc
    _ ≤ Real.sqrt (D*∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) *
      Real.sqrt (D*∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) := by
        gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD,Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D)^2 *
          Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖^2) *
          Real.sqrt (∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel cubeRadical)
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (newLabel newRow)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem rowCoprimeMask_congr_span (S : Finset ι) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) :
    rowCoprimeMask (fun i => Ideal.span {p i}) S a = rowCoprimeMask (fun i => Ideal.span {p i}) S b := by
  have hm (i : ι) : a ∈ Ideal.span {p i} ↔ b ∈ Ideal.span {p i} := by
    rw [← Ideal.span_singleton_le_iff_mem, h, Ideal.span_singleton_le_iff_mem]
  simp only [rowCoprimeMask,hm]

theorem fixedChildRow_congr_mask_span (F : Finset ι) (Ψ : O →* ℂ) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hp hcop hg F Ψ a H f y = fixedChildRow p hp hcop hg F Ψ b H f y := by
  simp only [fixedChildRow,secondChildColumn,rowCoprimeMask_congr_span p _ h]

theorem secondChildColumn_zero_of_mask_label_mem (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hmf : m*f ∈ Ideal.span {p i}) :
    secondChildColumn p hp hcop hg Ψ m f y H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hmf with hm|hf
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m=0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i∈S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondChildColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S f=0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i∈S,f ∈ Ideal.span {p i} from ⟨i,hi,hf⟩)]
    have hr := FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S f hz
    simp only [secondChildColumn,hr,zero_pow (by decide : (4 : ℕ) ≠ 0),mul_zero,zero_mul]

theorem fixedChildRow_restore_killed_pool (F B : Finset ι) (Ψ : O →* ℂ)
    (m f y : O) (H : Finset ι → ℂ) (hB : ∀ i∈B,m*f ∈ Ideal.span {p i}) :
    fixedChildRow p hp hcop hg (F\B) Ψ m H f y = fixedChildRow p hp hcop hg F Ψ m H f y := by
  unfold fixedChildRow
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
  intro S hS hn
  have hd : ¬ Disjoint B S := by
    intro hd
    apply hn
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) hi,
      fun hiB => Finset.disjoint_left.mp hd hiB hi⟩
  obtain ⟨i,hiB,hiS⟩ := Finset.not_disjoint_iff.mp hd
  exact secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f y H S i hiS (hB i hiB)

def globalSecondMask (m : O) (x : GlobalSecondData ι) : O :=
  (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit *
    primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)) *
    ∏ i∈x.firstCommon,p i

def fixedTripleMask (m : O) (q : Ideal O × Ideal O × Ideal O) : O :=
  m*idealGenerator q.1*idealGenerator q.2.1*idealGenerator q.2.2

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondMask_span (m : O) (x : GlobalSecondData ι) :
    Ideal.span {globalSecondMask p m x}=Ideal.span {fixedTripleMask m (globalSecondFixedTriple p x)} := by
  simp only [globalSecondMask,fixedTripleMask,globalSecondFixedTriple,
    ← Ideal.span_singleton_mul_span_singleton,span_idealGenerator,
    primeSubsetGenerator,FiniteGaussPhase.span_finset_prod]
  ring

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondMask_kills_cube_common (m : O) (x : GlobalSecondData ι) :
    ∀ i∈x.cube.support∪x.common,globalSecondMask p m x*globalSecondLabel p x ∈ Ideal.span {p i} := by
  intro i hi
  let J := jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit
  let b0 := b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit
  rcases Finset.mem_union.mp hi with hi|hi
  · have hd : p i ∣ J*b0 := (Finset.dvd_prod_of_mem p hi).trans
      (cubeRadical_dvd_jLabel_b0 p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit x.cube.support_pos)
    have he : globalSecondMask p m x*globalSecondLabel p x =
        (J*b0)*(m*primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)*
          (∏ i∈x.firstCommon,p i)*primeSubsetGenerator (fun i => Ideal.span {p i}) x.common*
          primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor*(∏ i∈x.source.overlap,p i)) := by
      simp only [globalSecondMask,globalSecondLabel,secondSupportLabel,expansionSupportData,J,b0]
      ring
    rw [he]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_left hd _)
  · have hC : primeSubsetGenerator (fun i => Ideal.span {p i}) x.common ∈ Ideal.span {p i} := by
      have hs : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) x.common} ≤ Ideal.span {p i} := by
        rw [primeSubsetGenerator,span_idealGenerator]
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun i => Ideal.span {p i}) hi)
      exact hs (Ideal.subset_span (Set.mem_singleton _))
    have hlabel : globalSecondLabel p x ∈ Ideal.span {p i} := by
      apply Ideal.mul_mem_right
      apply Ideal.mul_mem_right
      apply Ideal.mul_mem_right
      exact hC
    exact Ideal.mul_mem_left _ _ hlabel

theorem globalSecondRawRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (x : GlobalSecondData ι) (y : O) :
    fixedChildRow p hp hcop hg ((F\(x.cube.support∪x.common))\x.firstCommon) Ψ
      (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit *
        primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
      H (globalSecondLabel p x) y =
    fixedChildRow p hp hcop hg F Ψ (fixedTripleMask m (globalSecondFixedTriple p x))
      H (globalSecondLabel p x) y := by
  rw [fixedChildRow_fixed_pool p hp hcop hg hinj]
  change fixedChildRow p hp hcop hg (F\(x.cube.support∪x.common)) Ψ (globalSecondMask p m x)
    H (globalSecondLabel p x) y = _
  rw [fixedChildRow_restore_killed_pool p hp hcop hg F (x.cube.support∪x.common) Ψ
    (globalSecondMask p m x) (globalSecondLabel p x) y H (globalSecondMask_kills_cube_common p m x)]
  exact fixedChildRow_congr_mask_span p hp hcop hg F Ψ (globalSecondMask_span p m x) H _ _

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def signedProductDivisorSum (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ)*H d i j k else 0

def correctionRectangleMajorant (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * H (D*E) i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem signedProductDivisorSum_le_rectangles (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    ‖signedProductDivisorSum rows left right a b P H‖ ≤
      correctionRectangleMajorant S T rows left right a b P H := by
  classical
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hpair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1) (hright x.2)
  have hK : ∀ j k d, d ∣ left j*right k → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hpair (j,k) d hd
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d.val i j k else 0 else 0
  have he : signedProductDivisorSum rows left right a b P H =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val:ℂ)*A i j k d := by
    unfold signedProductDivisorSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K (left j*right k) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ left j*right k <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P H
  have hi (i : m) : (∑ d : K, ‖∑ j, ∑ k, A i j k d‖) =
      ∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
        originalTerm rows left right a b 1 1 i j k * H d i j k else 0‖ else 0 := by
    rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0‖)]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]
  simp_rw [hi]
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans
  unfold correctionRectangleMajorant
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  by_cases hd : D*E ∈ K
  · simp only [hd, ite_true]
    exact le_rfl
  · simp only [hd, ite_false]
    positivity

theorem HasSieveExponent.small_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i → (Ideal.absNorm (D*E):ℝ) ≤
      U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    correctionRectangleMajorant S T rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)) := by
  classical
  by_cases hc : D₁*D₂ ≤ (2*U)*(N*Real.sqrt (F/(M*B)))
  · apply le_trans (b := smallPrincipalCorrection S T rows left right a b M F)
    · unfold correctionRectangleMajorant smallPrincipalCorrection
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro E _
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> first | exact le_rfl | positivity
    · exact hexp.small_principal_correction deltaLoss hδ ε hε S T D₁ D₂ B N M F (2*U)
        hD₁ hD₂ hB hN hM hF hD₁N hD₂N hS hT rows left right hr hl hri
        (fun i => ⟨(hrows i).1,(hrows i).2.2⟩) hleft hright a b hc
  · have hz : correctionRectangleMajorant S T rows left right a b P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) = 0 := by
      unfold correctionRectangleMajorant
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
          (Ideal.absNorm D) (Ideal.absNorm E) U hM hF (by linarith) (hrows i).2.1
          (by linarith) hU (by linarith) (by linarith) (hS D hD).1 (hT E hE).1
        simpa only [map_mul,Nat.cast_mul] using hP D hD E hE i hp
      simp only [hn,ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.small_principal_divisor_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    ‖signedProductDivisorSum rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2))) := by
  classical
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hS := columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2)
  have hT := columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2)
  apply (signedProductDivisorSum_le_rectangles S T rows left right a b P _ hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)).trans
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.small_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M F U
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hF hU
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P (fun D _ E _ i hp => hP (D*E) i hp)

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

lemma source_large_cut_lower (M B b N T d : ℝ)
    (hM : 0 < M) (_hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B) (hN : 0 ≤ N) (hT : 0 < T)
    (hd : T*Real.sqrt (M/b) ≤ d) :
    Real.sqrt (M/B)*N ≤ ((4*N/T)/4)*d := by
  have hs : Real.sqrt (M/B) ≤ Real.sqrt (M/b) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM.le hb hbB)
  have hsd : Real.sqrt (M/B) ≤ d/T := (le_div_iff₀ hT).mpr (by nlinarith)
  calc
    _ ≤ (d/T)*N := mul_le_mul_of_nonneg_right hsd hN
    _ = _ := by ring

lemma dual_large_cut_lower (M F B b N T d : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B)
    (hN : 0 < N) (hT : 0 < T) (hd : T*(N*Real.sqrt (F/(M*b))) ≤ d) :
    Real.sqrt ((M/F)/B)*N ≤ ((4*M/(F*T))/4)*d := by
  have hs : Real.sqrt (F/(M*B)) ≤ Real.sqrt (F/(M*b)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hF.le (by positivity) (mul_le_mul_of_nonneg_left hbB hM.le))
  have hnd : N*Real.sqrt (F/(M*B)) ≤ d/T := by
    apply (le_div_iff₀ hT).mpr
    calc
      _ = T*(N*Real.sqrt (F/(M*B))) := by ring
      _ ≤ T*(N*Real.sqrt (F/(M*b))) := by gcongr
      _ ≤ d := hd
  rw [dual_middle_scale_identity M F B N hM hF hB hN]
  calc
    _ ≤ ((M/(F*N))*(d/T))*N := by gcongr
    _ = _ := by field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.source_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*Real.sqrt (M/(Ideal.absNorm (rows i):ℝ)) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b M (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*N/T+Real.sqrt M*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N M (4*N/T) hB hN hM (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact source_large_cut_lower M B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)

theorem HasSieveExponent.dual_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b (M/F) (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*M/(F*T)+Real.sqrt (M/F)*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N (M/F) (4*M/(F*T)) hB hN (by positivity) (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact dual_large_cut_lower M F B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM hF (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_large_principal_normalization
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)
    (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, rows i ≠ 0) (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0) :
    (∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
      (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
        ((Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ))):ℝ):ℂ) *
        ∑ d ∈ idealDivisors (left j*right k), if P d i then
          (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0)) =
      principalDivisorCorrection rows left right a b (M/F) P := by
  classical
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  unfold principalDivisorCorrection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [←Complex.ofReal_mul, dual_principal_prefactor_identity M F (Ideal.absNorm (rows i))
    (Ideal.absNorm (left j)) (Ideal.absNorm (right k)) hM hF (hpos _ (hrows i))
      (hpos _ (hleft j)) (hpos _ (hright k)), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i
  · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
    ring
  · simp only [hd,ite_false,mul_zero]

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicSectors -/

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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

variable {m n : Type*} [Fintype m] [Fintype n]

def lowPrincipalErrorSum (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    lowPrincipalError (cols j) (cols k) W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)))
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / T)
      (T * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (T ^ 4)

theorem lowPrincipal_actual_error_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖lowPrincipalErrorSum rows cols a W M T‖ ≤
            16384 * B * N *
              ((4 * supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ l) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := lowPrincipal_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro ε hε B N M T hB hN hM hT rows cols hr hc hrows hcols a W
  let E := (4 * supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    lowPrincipalError (cols j) (cols k) W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)))
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / T)
      (T * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (T ^ 4)
  have hsc := (supportConstant_pos ε hε).le
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ E := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hX : 0 < Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) := Real.sqrt_pos.mpr (div_pos hM hi)
    have hh := hb ε hε (cols j) (cols k) (hcols j).1 (hcols k).1 W _ _ T hX
      (show Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / 2 ≤ Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) by linarith)
      (show Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) ≤ 2 * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) by linarith) hT
    change ‖error i j k‖ ≤ _ at hh
    apply hh.trans
    dsimp only [E]
    gcongr
    · exact (hcols j).2
    · exact (hcols k).2
  exact actual_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2⟩) a E hE error herr

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem sqrt_product_column_shell (N i j : ℝ) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    N / 2 ≤ Real.sqrt (i * j) ∧ Real.sqrt (i * j) ≤ N := by
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hlo : (N / 2) ^ 2 ≤ i * j := by
    simpa only [pow_two] using mul_le_mul hi.1 hj.1 (by linarith : 0 ≤ N / 2) hi0.le
  have hhi : i * j ≤ N ^ 2 := by
    simpa only [pow_two] using mul_le_mul hi.2 hj.2 hj0.le hN.le
  have hs := Real.sq_sqrt (mul_pos hi0 hj0).le
  have hp := Real.sqrt_nonneg (i * j)
  constructor <;> nlinarith

theorem dual_truncation_reference_bounds (M F b N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    0 < N * Real.sqrt (F / (M * b)) ∧
      (N * Real.sqrt (F / (M * b))) / 2 ≤ Real.sqrt (F * i * j / (M * b)) ∧
      Real.sqrt (F * i * j / (M * b)) ≤ 2 * (N * Real.sqrt (F / (M * b))) := by
  have hr : 0 < Real.sqrt (F / (M * b)) := Real.sqrt_pos.mpr (by positivity)
  have he : Real.sqrt (F * i * j / (M * b)) = Real.sqrt (F / (M * b)) * Real.sqrt (i * j) := by
    rw [← Real.sqrt_mul (show 0 ≤ F / (M * b) by positivity)]
    congr 1
    ring
  obtain ⟨hlo, hhi⟩ := sqrt_product_column_shell N i j hN hi hj
  refine ⟨mul_pos hN hr, ?_, ?_⟩
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hlo hr.le]
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hhi hr.le, mul_pos hN hr]

theorem dual_truncation_prefactor_bound (M F N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    M / (Real.sqrt (i * j) * F) ≤ 2 * M / (F * N) := by
  obtain ⟨hlo, _⟩ := sqrt_product_column_shell N i j hN hi hj
  calc
    _ ≤ M / ((N / 2) * F) := div_le_div_of_nonneg_left hM.le (by positivity)
      (mul_le_mul_of_nonneg_right hlo hF.le)
    _ = _ := by field_simp

variable {m n : Type*} [Fintype m] [Fintype n]

def dualPrincipalErrorSum (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M F N T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))

theorem dualPrincipal_actual_error_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M F T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 0 < F → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖dualPrincipalErrorSum rows cols a W M F N T‖ ≤
            16384 * B * N *
              ((2 * M / (F * N)) * ((supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l)) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := primePool_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols a W
  let E₀ := (supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))
  have hsc := (supportConstant_pos ε hε).le
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ (2 * M / (F * N)) * E₀ := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    obtain ⟨hX₀, hlo, hhi⟩ := dual_truncation_reference_bounds M F (Ideal.absNorm (rows i)) N
      (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k)) hM hF hi (by linarith) (hcols j).2 (hcols k).2
    have hh := hb ε hε (cols j * cols k) (mul_ne_zero (hcols j).1.1 (hcols k).1.1) W
      _ _ T hX₀ hlo hhi hT
    simp only [map_mul, Nat.cast_mul] at hh
    have he : ‖truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4)‖ ≤ E₀ := by
      apply hh.trans
      dsimp only [E₀]
      gcongr
      · exact (hcols j).2.2
      · exact (hcols k).2.2
    dsimp only [error]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul
      (dual_truncation_prefactor_bound M F N (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k))
        hM hF (by linarith) (hcols j).2 (hcols k).2) he (norm_nonneg _) (by positivity)
  exact actual_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2.2⟩) a _ (by positivity) error herr

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondSquarefreeLogSector (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    Finset (SecondExpansionData ι) :=
  (secondLogSector p D F K R X M j).filter
    (fun x => Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSquarefreeLogSector_subset (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j ⊆ secondLogSector p D F K R X M j :=
  Finset.filter_subset _ _

def secondSquarefreeLogTargets (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    Finset (Ideal O × O) :=
  (secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j).image (fun x =>
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSquarefreeLogTargets_subset (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j ⊆
      secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j :=
  Finset.image_subset_image (secondSquarefreeLogSector_subset p B C D F v₁ v₂ ε₁ ε₂ K R X M j)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSquarefreeLogTargets_mem (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (x : SecondExpansionData ι) (hx : x ∈ secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)) ∈
      secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSquarefreeLogTargets_squarefree (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (q : Ideal O × O) (hq : q ∈ secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    Squarefree q.1 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  exact (Finset.mem_filter.mp hx).2

include hp in
lemma secondSquarefreeLogTargets_bounds (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (q : Ideal O × O) (hq : q ∈ secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    q.1 ≠ ⊥ ∧ (Ideal.absNorm q.1 : ℝ) ≤ secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j ∧
      q.2 ≠ 0 ∧ ‖eisEmbedding q.2‖^2 ≤ secondLogK j * Real.exp 1 :=
  secondLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q
    (secondSquarefreeLogTargets_subset p B C D F v₁ v₂ ε₁ ε₂ K R X M j hq)

include hp in
lemma secondSquarefreeLogSector_coordinates (B C D F R : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (X M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (x : SecondExpansionData ι)
    (hx : x ∈ secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    let y := expansionSupportData C D x
    |secondSectorZ p (secondExpansionScale p X
      (primeSubsetGenerator (fun i => Ideal.span {p i}) R) y) (secondLogX p R X j) y| ≤ 2 ∧
    |secondSectorUd p (primeProductNorm p D) y| ≤ 2 ∧
    |secondSectorUe p (secondLogE j) y| ≤ 2 ∧
    |secondSectorUv p (secondLogV j) y| ≤ 2 ∧
    |secondSectorKap p (secondLogK j) y| ≤ 2 :=
  secondLogSector_coordinates p hp C D F R K X M hX j x
    (secondSquarefreeLogSector_subset p B C D F v₁ v₂ ε₁ ε₂ K R X M j hx)

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondExpansionSource_log_eq_squarefree
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (Ψ : O →* ℂ) (m d : O) (z : SecondRayIndex) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m (secondBaseLabel p B C v₁ v₂ ε₁ ε₂) d z
      (secondLogSector p D F K R X M j) H₁ H₂ W Y =
    secondExpansionSource p hp hcop hg F Ψ m (secondBaseLabel p B C v₁ v₂ ε₁ ε₂) d z
      (secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j) H₁ H₂ W Y := by
  apply secondExpansionSource_eq_squarefree p hp hcop hg B C v₁ v₂ ε₁ ε₂ hCB F Ψ m d z
  intro x hx
  have hs := secondSupportedSector_mem p F K R X M x (Finset.mem_filter.mp hx).1
  exact hs.2.1

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm jLabel b0Label)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (densityChildEnergy)

theorem normalized_squarefree_binned_second_density_transfer
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
              (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
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
    rw [secondExpansionSource_log_eq_squarefree p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ hCB
      K R X M j Ψ m (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z _ _ W Y]
    have hcoord := secondSquarefreeLogSector_coordinates p hp B C D F R v₁ v₂ ε₁ ε₂ K X M hX j
    have hb := hbound (primeProductNorm p D) (secondLogE j) (secondLogV j)
      (secondLogX p R X j) (secondLogK j) Y
      (FirstPassCubeLabels.primeProductNorm_pos p hp D)
      (normLogScale_pos _) (normLogScale_pos _) (secondLogX_pos p hp R X hX j)
      (normLogScale_pos _) hY θ θ B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j) (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      X (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)
      ((secondSquarefreeLogSector_subset p B C D F v₁ v₂ ε₁ ε₂ K R X M j).trans
        (secondLogSector_subset p D F K R X M j)) hv hCB hD hΨ hX
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))
      (fun x hx => (hcoord x hx).1) (fun x hx => (hcoord x hx).2.1)
      (fun x hx => (hcoord x hx).2.2.1) (fun x hx => (hcoord x hx).2.2.2.1)
      (fun x hx => (hcoord x hx).2.2.2.2)
      (secondSquarefreeLogTargets_mem p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      (fun q hq => (secondSquarefreeLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).1)
      (fun q hq => (secondSquarefreeLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).2.1)
    simpa only [secondBaseLabel, primeSubsetGenerator_norm_eq_productNorm,
      secondLogX_radial_scale p D R X Y hX.ne' j] using hb

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_squarefree_binned_finite_transfer
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
                (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
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
    normalized_squarefree_binned_second_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
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

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_squarefree_binned_integrated_transfer
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
        (X Z : ℝ) (Srows : Finset O),
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
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity (2*(J+2)) t * (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2)) ≤
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity 0 t) * (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
            (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
              ∑ j ∈ secondLogBinBox Usupp Kmax,
              (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                  Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ /
                (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
                (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,hpoint⟩ :=
    firstCoreInputRow_squarefree_binned_finite_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M hM hgM ε hε tailOrder decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  dsimp only
  let v := fun i => v₁ i+v₂ i
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let Ψ' := firstCoreTwist negative χ Ψ r₁
  let m' := m*b0Label p B v ε₁ ε₂
  let c' := c*jLabel p B v ε₁ ε₂
  let X' := X/primeProductNorm p A₀
  let Usupp := X'*Real.exp M
  let K := firstCoreSecondCutoff p A₀ X Y M Z
  let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
  let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
  let f := fun t => ∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
    (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2
  let diag := |Y| * ‖paperRadialFourier rowMajorant 0‖*
    (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2)
  let tail := Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder
  let childAt := fun t : ℝ => ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  let child := ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  have hchild (t : ℝ) : childAt t = ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*child := by
    dsimp only [child, childAt]
    simp only [    Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change (∫ t, firstLogDensity (2*(J+2)) t*f t) ≤
    (∫ t, firstLogDensity 0 t)*(primeProductNorm p A₀)⁻¹*(diag+child+tail)
  apply FirstPassCubeLabels.integral_pair_moment_bound J f
  · dsimp only [f]
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro z hz
    exact firstCoreInputRow_integrable p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ z
      (FirstPassCubeLabels.firstLogDensity_integrable (2*(J+2)))
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le
  · dsimp [diag]
    positivity
  · dsimp [tail]
    positivity
  · intro t
    have hb := hpoint Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows
      hv hCB hD hΨ hX hZ hSrows hSrows0
    change f t + _ ≤ (primeProductNorm p A₀)⁻¹*(diag+childAt t+tail) at hb
    rw [hchild] at hb
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans hb

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.SquarefreeTransfer -/

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

namespace SecondPassArithmetic

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy childGeometricMean childEnergy)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondSquarefreeLogNormalizedEnergy (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) : ℝ :=
  densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
    (secondLogX p R X j) (secondLogX p R X j) J /
  (secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)

lemma secondSquarefreeLogNormalizedEnergy_nonneg
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    0 ≤ secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  apply div_nonneg
  · apply integral_nonneg
    intro t₁
    apply integral_nonneg
    intro t₂
    apply integral_nonneg
    intro t₃
    exact mul_nonneg (JointLogSeparation.tripleLogDensity_nonneg _ _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · exact mul_nonneg (secondLogX_pos p hp R X hX j).le
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))

lemma secondSquarefreeLogNormalizedEnergy_empty
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ)
    (hT : secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j = ∅) :
    secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J = 0 := by
  simp only [secondSquarefreeLogNormalizedEnergy, hT, densityChildEnergy, childGeometricMean, childEnergy,
    Finset.sum_empty, Finset.sum_const_zero, Real.sqrt_zero, mul_zero, integral_zero, zero_div]

theorem secondSquarefreeLog_normalized_cost
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X Y M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    (Y*primeProductNorm p R/X^2) *
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
        (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
        (secondLogX p R X j) (secondLogX p R X j) J =
    (Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X) *
      secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  unfold secondSquarefreeLogNormalizedEnergy
  rw [secondLogX_label_cost]
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hc := (zero_lt_one.trans_le (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))).ne'
  have hcn : ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖ ≠ 0 := by
    intro h; apply hc; rw [h]; norm_num
  field_simp

end SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter crossCoeff)
open SecondPassIntegration (densityChildEnergy)

def firstCoreSquarefreeBudget
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (M ε : ℝ) (tailOrder decayOrder J : ℕ)
    (Y : ℝ) (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex) (X Z : ℝ) : ℝ :=
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
  (primeProductNorm p A₀)⁻¹ *
    (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
        (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
      (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
        ∑ j ∈ secondLogBinBox Usupp Kmax,
        (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
            Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
        (Cₛ /
          (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
        densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
          (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
          (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
      Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder)

theorem firstInputFamilyEnergy_squarefree_transfer
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
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X Z : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        firstInputFamilyEnergy p hg F B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m
          (fun S => g (columnLog p X S)) V X
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) (2*(J+2)) Srows ≤
        (∫ t : ℝ, firstLogDensity 0 t) *
          ∑ a : RayCharacter × RayCharacter, ∑ A₀ ∈ F.powerset,
            ‖crossCoeff a.1 a.2‖ * ∑ r : FirstCoreIndex,
              ‖firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r‖ *
                firstCoreSquarefreeBudget p hp hcop hg windows Cₐ Cₛ Cw Ctail
                  g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
                  (if negative then a.1 else a.2) Ψ m r X Z := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,hbound⟩ :=
    firstCoreInputRow_squarefree_binned_integrated_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M hM hgM ε hε tailOrder decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ m X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  unfold firstInputFamilyEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro A₀ hA₀
  apply Finset.sum_le_sum
  intro r hr
  have hb := hbound Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ (if negative then a.1 else a.2)
    Ψ m r X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  have he : (∫ t : ℝ, firstLogDensity (2*(J+2)) t *
      ∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative
        (if negative then a.1 else a.2) Ψ m (normalizedColumn p (fun S => g (columnLog p X S)))
        V (columnLog p X) (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) D) r t z‖^2) ≤
      (∫ t : ℝ, firstLogDensity 0 t) *
        firstCoreSquarefreeBudget p hp hcop hg windows Cₐ Cₛ Cw Ctail
          g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
          (if negative then a.1 else a.2) Ψ m r X Z := by
    simpa only [firstCoreSquarefreeBudget, mul_assoc] using hb
  have hw := mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg (crossCoeff a.1 a.2))
    (norm_nonneg (firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r)))
  convert hw using 1 <;> (try simp only [Finset.mul_sum]) <;> ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity
  actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

structure SquarefreeBudgetData where
  windows : Fin 7 → ℝ → ℂ
  arithmetic : ℝ
  smooth : ℝ
  windowBound : ℝ
  tail : ℝ
  arithmetic_pos : 0 < arithmetic
  smooth_nonneg : 0 ≤ smooth
  windowBound_nonneg : 0 ≤ windowBound
  tail_pos : 0 < tail

def firstSquarefreeFamilyBudget {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (data : SquarefreeBudgetData)
    (g V : 𝓢(ℝ,ℂ)) (negative : Bool) (M ε : ℝ) (tailOrder decayOrder J : ℕ)
    (Y : ℝ) (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (Ψ : O →* ℂ) (m : O) (X Z : ℝ) : ℝ :=
  ∑ a : RayCharacter × RayCharacter, ∑ A₀ ∈ F.powerset,
    ‖crossCoeff a.1 a.2‖ * ∑ r : FirstCoreIndex,
      ‖firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r‖ *
        firstCoreSquarefreeBudget p hp hcop hg data.windows data.arithmetic data.smooth data.windowBound data.tail
          g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
          (if negative then a.1 else a.2) Ψ m r X Z

theorem first_passage_squarefree_child_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B C D : Finset ι) (hFB : Disjoint F B) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O)
    (hΨ₁ : ∀ a, ‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a, ‖Ψ₂ a‖ ≤ 1)
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ))
    (U₁ U₂ : ℝ → ℂ) (hUc₁ : HasCompactSupport U₁) (hUs₁ : ContDiff ℝ ∞ U₁)
    (hUc₂ : HasCompactSupport U₂) (hUs₂ : ContDiff ℝ ∞ U₂)
    (hU₁ : ∀ t, g₁ t ≠ 0 → U₁ t=1) (hU₂ : ∀ t, g₂ t ≠ 0 → U₂ t=1)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ N₁ N₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ M₁) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ M₂)
    (hV₁ : ∀ t, V₁ t ≠ 0 → |t| ≤ N₁) (hV₂ : ∀ t, V₂ t ≠ 0 → |t| ≤ N₂)
    (ε deltaLoss : ℝ) (hε : 0 < ε) (hδ : 0 < deltaLoss) (tailOrder decayOrder J : ℕ) :
    ∃ (data₁ data₂ : SquarefreeBudgetData) (K₀ : ℝ), 0 ≤ K₀ ∧
      ∀ (lengthScale : ℝ), 0 < lengthScale → ∀ (s : Finset (Ideal O × O)) (T : Finset O)
        (w : Ideal O × O → ℂ) (M Y Z : ℝ),
      0 ≤ M → 0 < Y → 0 ≤ Z →
      (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B (fun i => v₁ i+v₂ i) ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1)) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by
  obtain ⟨windows₁,A₁,S₁,H₁,Q₁,hA₁,hS₁,hH₁,hQ₁,hleft⟩ :=
    firstInputFamilyEnergy_squarefree_transfer p hp hcop hg hinj hc hpr U₁ hUc₁ hUs₁
      g₁ V₁ true hU₁ M₁ hM₁ hg₁ ε hε tailOrder decayOrder J
  obtain ⟨windows₂,A₂,S₂,H₂,Q₂,hA₂,hS₂,hH₂,hQ₂,hright⟩ :=
    firstInputFamilyEnergy_squarefree_transfer p hp hcop hg hinj hc hpr U₂ hUc₂ hUs₂
      g₂ V₂ false hU₂ M₂ hM₂ hg₂ ε hε tailOrder decayOrder J
  let data₁ : SquarefreeBudgetData := ⟨windows₁,A₁,S₁,H₁,Q₁,hA₁,hS₁,hH₁,hQ₁⟩
  let data₂ : SquarefreeBudgetData := ⟨windows₂,A₂,S₂,H₂,Q₂,hA₂,hS₂,hH₂,hQ₂⟩
  obtain ⟨K₀,hK₀,hfirst⟩ := first_passage_transfer_input_family p hp hinj hcop hg hc hpr
    F B hFB (fun i => v₁ i+v₂ i) ε₁ ε₂ hv Ψ₁ Ψ₂ m₁ m₂
    (fun S => g₁ (columnLog p X₁ S)) (fun S => g₂ (columnLog p X₂ S))
    (fun G hG => hΨ₁ _) (fun G hG => hΨ₂ _) W V₁ V₂ X₁ X₂ hX₁ hX₂
    N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  let I₀ : ℝ := ∫ t, firstLogDensity 0 t
  have hI₀ : 0 ≤ I₀ := integral_nonneg (FirstPassCubeLabels.firstLogDensity_nonneg 0)
  refine ⟨data₁,data₂,K₀*I₀,mul_nonneg hK₀ hI₀,?_⟩
  intro lengthScale hL s T w M Y Z hM hY hZ hs hs0 hmap hT0 hT hw
  dsimp only
  have h₁ := hleft Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z T hv hCB hD hΨ₁ hX₁ hZ hT hT0
  have h₂ := hright Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z T hv hCB hD hΨ₂ hX₂ hZ hT hT0
  change _ ≤ I₀*firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
    tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z at h₁
  change _ ≤ I₀*firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
    tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z at h₂
  have hb := hfirst lengthScale hL (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
    s T w M Y hM hY.le hs hs0 hmap hT0 hT hw
  apply hb.trans
  calc
    _ ≤ (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (I₀*firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (I₀*firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hI₀, Real.sqrt_mul hI₀]
      calc
        _ = (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
          (M*K₀*Y^deltaLoss) * (Real.sqrt I₀)^2 *
          Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
            tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
          Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
            tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by ring
        _ = _ := by rw [Real.sq_sqrt hI₀]; ring

end SecondPassArithmetic

namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

theorem actual_first_kernel_full_uniform_envelope
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
      (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ C₁ C₂ : Finset ι → ℂ,
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂ lengthScale hL d h hd hh
  have hR : 0 < firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h := by
    unfold firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro C₁ C₂
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

end

open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

theorem first_passage_full_uniform_transfer
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (C₁ C₂ : Finset ι → ℂ) (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T) := by
  obtain ⟨H, hH, hsep⟩ := actual_first_kernel_full_uniform_envelope
    W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ 0 J
  obtain ⟨K, hK, hpush⟩ := first_column_energy_integral deltaLoss hδ
  refine ⟨H * K, mul_nonneg hH hK.le, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv C₁ C₂ X₁ X₂ hX₁ hX₂
  have hsep := hsep p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  let A₁ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let A₂ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hfam : ∀ x : Ideal O × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ s →
      (∀ t : ℝ, ‖b t‖ ≤ H * firstLogDensity J t) ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
        q * Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 b) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨b, hb, hk⟩ := hsep lengthScale hL d x.2 hd (hnonzero x hx)
      refine ⟨b, fun _ => ⟨?_, hk (A₁ x) (A₂ x)⟩⟩
      simpa only [pow_zero, one_mul] using hb
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  let E₁ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 (b x)
  let E₂ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 (b x)
  let O₁ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T
  let O₂ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T
  let P := M * H * K * Y ^ deltaLoss
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg hM hH) hK.le) (Real.rpow_nonneg hY deltaLoss)
  have hE₁ (x) : 0 ≤ E₁ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true _ _ _ _ _ _
  have hE₂ (x) : 0 ≤ E₂ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false _ _ _ _ _ _
  have hdom : ∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t := fun x hx => (hb x hx).1
  have hsum₁ : (∑ x ∈ s, ‖w x‖ * E₁ x) ≤ P * O₁ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv true C₁ V₁ X₁ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hsum₂ : (∑ x ∈ s, ‖w x‖ * E₂ x) ≤ P * O₂ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv false C₂ V₂ X₂ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hterm (x) : ‖w x‖ * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) =
      Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt ‖w x‖) ^ 2 * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ s, ‖w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, q * (Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ ‖w x‖ * (q * Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ s, Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ s, ‖w x‖ * E₁ x) * Real.sqrt (∑ x ∈ s, ‖w x‖ * E₂ x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s
        (fun x => mul_nonneg (norm_nonneg _) (hE₁ x))
        (fun x => mul_nonneg (norm_nonneg _) (hE₂ x))) hq
    _ ≤ q * (Real.sqrt (P * O₁) * Real.sqrt (P * O₂)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hsum₁) (Real.sqrt_le_sqrt hsum₂)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hq
    _ = _ := by
      rw [Real.sqrt_mul hP, Real.sqrt_mul hP]
      calc
        _ = q * (Real.sqrt P)^2 * Real.sqrt O₁ * Real.sqrt O₂ := by ring
        _ = _ := by rw [Real.sq_sqrt hP]; dsimp only [P]; ring

end FirstPassCubeLabels
end

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem first_passage_full_uniform_input_family
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι → ℂ)
      (_hΨ₁ : ∀ D ∈ F.powerset, ‖Ψ₁ (∏ i ∈ D, p i)‖ ≤ 1)
      (_hΨ₂ : ∀ D ∈ F.powerset, ‖Ψ₂ (∏ i ∈ D, p i)‖ ≤ 1)
      (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true (multiplicativeCoreColumn p Ψ₁ m₁ H₁)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
  obtain ⟨K, hK, hb⟩ := FirstPassCubeLabels.first_passage_full_uniform_transfer
    W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨(32 * 512) * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ hΨ₁ hΨ₂ X₁ X₂ hX₁ hX₂
  have hb := hb p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv
    (multiplicativeCoreColumn p Ψ₁ m₁ H₁) (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
    X₁ X₂ hX₁ hX₂
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have hf := hb lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have h₁ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ true
    Ψ₁ m₁ H₁ V₁ X₁ c d J T hΨ₁
  have h₂ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ false
    Ψ₂ m₂ H₂ V₂ X₂ c d J T hΨ₂
  have hq : 0 ≤ lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ :=
    div_nonneg hL.le (norm_nonneg _)
  have hfactor : 0 ≤ M * K * Y ^ deltaLoss :=
    mul_nonneg (mul_nonneg hM hK) (Real.rpow_nonneg hY deltaLoss)
  calc
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ H₁) V₁ X₁ c d J T) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ H₂) V₂ X₂ c d J T) := hf
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512)]
      calc
        _ = (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
            (Real.sqrt (32 * 512)) ^ 2 *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32 * 512)]; ring

end SecondPassArithmetic

end

end OAI

end

