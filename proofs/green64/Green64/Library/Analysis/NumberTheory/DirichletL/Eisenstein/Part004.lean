module

public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part011

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CuspHeight -/

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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernelCompact_smooth_cutoff (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃χ : KernelQuotient→ℝ,ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ ∧
      HasCompactSupport χ ∧ (∀q∈K,χ=ᶠ[𝓝 q](fun _ => 1)) ∧ ∀q,χ q∈Set.Icc 0 1 := by
  obtain ⟨J,hJ,hKJ⟩ := exists_compact_superset hK
  obtain ⟨χ,hχone,hχzero,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ,SpatialCoordinates) hK.isClosed hKJ (n := (⊤ : ℕ∞))
  refine ⟨χ,χ.contMDiff,?_,?_,hχrange⟩
  · apply HasCompactSupport.of_support_subset_isCompact hJ
    intro q hq
    by_contra hn
    exact hq (hχzero q hn)
  · intro q hq
    exact hχone.filter_mono (nhds_le_nhdsSet hq)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

lemma integral_upper_triangular_height_all (M : SL(2,ActualEisensteinCubic.O))
    (hc : M 1 0=0) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix M • w)=hyperbolicHeight w := by
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  rw [integral_upper_triangular_height M hc,hyperbolicHeight_upperPoint]

def fullMatrixHeight (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) : ℝ :=
  hyperbolicHeight (integralComplexMatrix M • w)

def fullCuspHeightRelation : Setoid (SL(2,ActualEisensteinCubic.O)) := Setoid.ker fullMatrixHeight
abbrev FullCuspClasses := Quotient fullCuspHeightRelation

def fullCuspOf (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses := Quotient.mk _ M

def fullCuspHeight : FullCuspClasses→HyperbolicSpace→ℝ :=
  Quotient.lift fullMatrixHeight (fun _ _ h => h)

lemma fullCuspHeight_of (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspOf M) w=fullMatrixHeight M w := rfl

lemma fullCuspHeight_continuous (x : FullCuspClasses) : Continuous (fullCuspHeight x) := by
  induction x using Quotient.inductionOn with
  | _ M => exact hyperbolicHeight_continuous.comp (continuous_hyperbolic_action (integralComplexMatrix M))

lemma fullMatrixHeight_eq_of_lower_zero (M N : SL(2,ActualEisensteinCubic.O))
    (h : (M*N⁻¹) 1 0=0) : fullMatrixHeight M=fullMatrixHeight N := by
  funext w
  have hh := integral_upper_triangular_height_all (M*N⁻¹) h (integralComplexMatrix N • w)
  simpa only [fullMatrixHeight,map_mul,map_inv,mul_smul,inv_smul_smul] using hh

lemma fullCuspOf_eq_iff (M N : SL(2,ActualEisensteinCubic.O)) :
    fullCuspOf M=fullCuspOf N ↔ (M*N⁻¹) 1 0=0 := by
  constructor
  · intro h
    by_contra hc
    have he : fullMatrixHeight M=fullMatrixHeight N := Quotient.exact h
    let w := upperPoint 0 2 (by norm_num : (0:ℝ)<2)
    have hh := congrFun he (integralComplexMatrix N⁻¹ • w)
    have hp := integral_hyperbolicHeight_mul_le_one (M*N⁻¹) hc w
    have hN : hyperbolicHeight w=2 := hyperbolicHeight_upperPoint _ _ _
    change hyperbolicHeight (integralComplexMatrix M • (integralComplexMatrix N⁻¹ • w))=
      hyperbolicHeight (integralComplexMatrix N • (integralComplexMatrix N⁻¹ • w)) at hh
    simp only [map_inv,smul_inv_smul] at hh
    simp only [map_mul,map_inv,mul_smul] at hp
    rw [hh,hN] at hp
    norm_num at hp
  · intro h
    exact Quotient.sound (fullMatrixHeight_eq_of_lower_zero M N h)

def fullCuspTranslate (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses→FullCuspClasses :=
  Quotient.map (fun N => N*M) (by
    intro N P h
    change fullMatrixHeight (N*M)=fullMatrixHeight (P*M)
    funext w
    have hh := congrFun h (integralComplexMatrix M • w)
    simpa only [fullMatrixHeight,map_mul,mul_smul] using hh)

lemma fullCuspTranslate_mul (M N : SL(2,ActualEisensteinCubic.O)) (x : FullCuspClasses) :
    fullCuspTranslate N (fullCuspTranslate M x)=fullCuspTranslate (M*N) x := by
  induction x using Quotient.inductionOn with
  | _ P => change fullCuspOf ((P*M)*N)=fullCuspOf (P*(M*N)); rw [mul_assoc]

lemma fullCuspTranslate_one (x : FullCuspClasses) : fullCuspTranslate 1 x=x := by
  induction x using Quotient.inductionOn with
  | _ P => change fullCuspOf (P*1)=fullCuspOf P; rw [mul_one]

def fullCuspRightEquiv (M : SL(2,ActualEisensteinCubic.O)) : FullCuspClasses≃FullCuspClasses where
  toFun := fullCuspTranslate M
  invFun := fullCuspTranslate M⁻¹
  left_inv x := by rw [fullCuspTranslate_mul,mul_inv_cancel,fullCuspTranslate_one]
  right_inv x := by rw [fullCuspTranslate_mul,inv_mul_cancel,fullCuspTranslate_one]

lemma fullCuspHeight_translate (M : SL(2,ActualEisensteinCubic.O)) (x : FullCuspClasses)
    (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspRightEquiv M x) w=fullCuspHeight x (integralComplexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N => change fullMatrixHeight (N*M) w=fullMatrixHeight N (integralComplexMatrix M • w)
           simp only [fullMatrixHeight,map_mul,mul_smul]

lemma fullCuspHeight_high_unique (w : HyperbolicSpace) (x y : FullCuspClasses)
    (hx : 1<fullCuspHeight x w) (hy : 1<fullCuspHeight y w) : x=y := by
  induction x using Quotient.inductionOn with
  | _ M =>
    induction y using Quotient.inductionOn with
    | _ N =>
      apply (fullCuspOf_eq_iff M N).mpr
      by_contra hc
      have hp := integral_hyperbolicHeight_mul_le_one (M*N⁻¹) hc (integralComplexMatrix N • w)
      simp only [map_mul,map_inv,mul_smul,inv_smul_smul] at hp
      change 1<fullMatrixHeight M w at hx
      change 1<fullMatrixHeight N w at hy
      change fullMatrixHeight M w*fullMatrixHeight N w≤1 at hp
      nlinarith [mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]

lemma fullCusp_profile_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    Function.HasFiniteSupport (fun x : FullCuspClasses => F (fullCuspHeight x w)) := by
  have hs : Set.Subsingleton {x : FullCuspClasses | 1<fullCuspHeight x w} :=
    fun x hx y hy => fullCuspHeight_high_unique w x y hx hy
  apply hs.finite.subset
  intro x hx
  by_contra hn
  exact hx (hF _ (le_of_not_gt hn))

def fullCuspProfileSum (F : ℝ→ℝ) (w : HyperbolicSpace) : ℝ :=
  ∑'x : FullCuspClasses,F (fullCuspHeight x w)

lemma fullCuspProfileSum_summable (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    Summable (fun x : FullCuspClasses => F (fullCuspHeight x w)) :=
  summable_of_hasFiniteSupport (fullCusp_profile_finite F hF w)

lemma fullCuspProfileSum_invariant (F : ℝ→ℝ) (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) :
    fullCuspProfileSum F (integralComplexMatrix M • w)=fullCuspProfileSum F w := by
  unfold fullCuspProfileSum
  simp only [←fullCuspHeight_translate M]
  exact (fullCuspRightEquiv M).tsum_eq (fun x : FullCuspClasses => F (fullCuspHeight x w))

lemma fullCuspProfileSum_eq_single (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (w : HyperbolicSpace) (x : FullCuspClasses) (hx : 1<fullCuspHeight x w) :
    fullCuspProfileSum F w=F (fullCuspHeight x w) := by
  apply tsum_eq_single x
  intro y hy
  apply hF
  by_contra hn
  exact hy (fullCuspHeight_high_unique w y x (lt_of_not_ge hn) hx)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

def cuspBarrierProfile (a b v : ℝ) : ℝ := cuspTransition a b v*(v-1)

lemma cuspBarrierProfile_smooth (a b : ℝ) : ContDiff ℝ ∞ (cuspBarrierProfile a b) :=
  (cuspTransition_contDiff a b).mul (contDiff_id.sub contDiff_const)

lemma cuspBarrierProfile_zero (a b : ℝ) (hab : a<b) (v : ℝ) (hv : v≤a) :
    cuspBarrierProfile a b v=0 := by
  rw [cuspBarrierProfile,cuspTransition_zero a b v hab hv,zero_mul]

lemma cuspBarrierProfile_nonneg (a b : ℝ) (ha : 1≤a) (hab : a<b) (v : ℝ) :
    0≤ cuspBarrierProfile a b v := by
  by_cases hv : v≤a
  · rw [cuspBarrierProfile_zero a b hab v hv]
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (ha.trans (le_of_not_ge hv)))

def cuspBarrier (a b : ℝ) (w : HyperbolicSpace) : ℝ :=
  1+fullCuspProfileSum (cuspBarrierProfile a b) w

lemma cuspBarrier_summable (a b : ℝ) (ha : 1≤a) (hab : a<b) (w : HyperbolicSpace) :
    Summable (fun x : FullCuspClasses => cuspBarrierProfile a b (fullCuspHeight x w)) :=
  fullCuspProfileSum_summable _ (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha)) w

lemma cuspBarrier_one_le (a b : ℝ) (ha : 1≤a) (hab : a<b) (w : HyperbolicSpace) :
    1≤ cuspBarrier a b w := by
  exact le_add_of_nonneg_right (tsum_nonneg (fun x => cuspBarrierProfile_nonneg a b ha hab _))

lemma cuspBarrier_invariant (a b : ℝ) (M : SL(2,ActualEisensteinCubic.O)) (w : HyperbolicSpace) :
    cuspBarrier a b (integralComplexMatrix M • w)=cuspBarrier a b w := by
  rw [cuspBarrier,cuspBarrier,fullCuspProfileSum_invariant]

theorem cuspBarrier_high (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b<v) :
    cuspBarrier a b (integralComplexMatrix M • upperPoint z v hv)=v := by
  rw [cuspBarrier_invariant]
  have hx : fullCuspHeight (fullCuspOf 1) (upperPoint z v hv)=v := by
    simp only [fullCuspHeight_of,fullMatrixHeight,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspBarrier,fullCuspProfileSum_eq_single _
    (fun y hy => cuspBarrierProfile_zero a b hab y (hy.trans ha)) _ (fullCuspOf 1)
      (by rw [hx]; linarith),hx,cuspBarrierProfile,cuspTransition_one a b v hab hbv.le,one_mul]
  ring

def kernelQuotientBarrier (a b : ℝ) : KernelQuotient→ℝ :=
  Quotient.lift (cuspBarrier a b) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (cuspBarrier_invariant a b (M:SL(2,ActualEisensteinCubic.O)) w).symm)

lemma kernelQuotientBarrier_one_le (a b : ℝ) (ha : 1≤a) (hab : a<b) (q : KernelQuotient) :
    1≤kernelQuotientBarrier a b q := by
  induction q using Quotient.inductionOn with
  | _ w => exact cuspBarrier_one_le a b ha hab w

lemma kernelQuotientBarrier_fordCusp (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (M : SL(2,ActualEisensteinCubic.O)) (p : UpperCoordinates) (hp : b<p.1.2) :
    kernelQuotientBarrier a b (fordOrbitChart globalKubotaKernel M p)=p.1.2 :=
  cuspBarrier_high a b ha hab M⁻¹ p.1.1 p.1.2 p.2 hp

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

lemma principal_high_locally_finite (w : HyperbolicSpace) :
    ∃U : Set HyperbolicSpace,IsOpen U ∧ w∈U ∧ ∃T : Finset CuspCosets,
      ∀z∈U,∀x∉T,cosetHeight x z<1 := by
  obtain ⟨U,hU,hw,T,hT⟩ := locally_finite_high_rows (hyperbolicSpatialCoordinates w)
    (hyperbolicSpatialCoordinates_positive w)
  refine ⟨hyperbolicSpatialCoordinates ⁻¹' U,hU.preimage hyperbolicSpatialCoordinates_continuous,
    hw,T,?_⟩
  intro z hz x hx
  have hh := (hT _ hz).2 x hx
  rw [←cosetHeight_upperPoint_rowHeight x _ (hyperbolicSpatialCoordinates_positive z),
    hyperbolicSpatialCoordinates_reconstruct] at hh
  exact hh

def fullCuspFromPrincipal (r : SL(2,ActualEisensteinCubic.O)) : CuspCosets→FullCuspClasses :=
  Quotient.lift (fun N : CubicKubota.levelThree => fullCuspOf ((N:SL(2,ActualEisensteinCubic.O))*r⁻¹)) (by
    intro N P h
    apply Quotient.sound
    funext w
    have he : cosetOf N=cosetOf P := Quotient.sound h
    have hh := congrArg (fun x => cosetHeight x (integralComplexMatrix r⁻¹ • w)) he
    simpa only [cosetHeight_cosetOf,fullMatrixHeight,map_mul,mul_smul,integralComplexMatrix_levelThree] using hh)

lemma fullCuspFromPrincipal_height (r : SL(2,ActualEisensteinCubic.O)) (x : CuspCosets)
    (w : HyperbolicSpace) :
    fullCuspHeight (fullCuspFromPrincipal r x) w=cosetHeight x (integralComplexMatrix r⁻¹ • w) := by
  induction x using Quotient.inductionOn with
  | _ N =>
    change fullMatrixHeight ((N:SL(2,ActualEisensteinCubic.O))*r⁻¹) w=cosetHeight (cosetOf N) _
    simp only [fullMatrixHeight,cosetHeight_cosetOf,map_mul,mul_smul,integralComplexMatrix_levelThree]

lemma fullCusp_finite_principal_cover :
    ∃S : Finset (SL(2,ActualEisensteinCubic.O)),∀x : FullCuspClasses,
      ∃r∈S,∃y : CuspCosets,fullCuspFromPrincipal r y=x := by
  let : CubicKubota.levelThree.FiniteIndex := levelThree_finiteIndex
  obtain ⟨S,hS⟩ := finite_right_representatives CubicKubota.levelThree
  refine ⟨S,fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | _ M =>
    obtain ⟨r,hr,hM⟩ := hS M⁻¹
    have hm : M*r∈CubicKubota.levelThree := by
      simpa only [mul_inv_rev,inv_inv] using CubicKubota.levelThree.inv_mem hM
    refine ⟨r,hr,cosetOf ⟨M*r,hm⟩,?_⟩
    change fullCuspOf ((M*r)*r⁻¹)=fullCuspOf M
    rw [mul_inv_cancel_right]

lemma full_high_locally_finite (w : HyperbolicSpace) :
    ∃U : Set HyperbolicSpace,IsOpen U ∧ w∈U ∧ ∃T : Finset FullCuspClasses,
      ∀z∈U,∀x∉T,fullCuspHeight x z<1 := by
  obtain ⟨S,hS⟩ := fullCusp_finite_principal_cover
  choose U hU hw T hT using fun r : S => principal_high_locally_finite (integralComplexMatrix r.1⁻¹ • w)
  let V : Set HyperbolicSpace := ⋂r : S,(fun z => integralComplexMatrix r.1⁻¹ • z) ⁻¹' U r
  let B : Finset FullCuspClasses := Finset.univ.biUnion (fun r : S => (T r).image (fullCuspFromPrincipal r.1))
  refine ⟨V,isOpen_iInter_of_finite (fun r => (hU r).preimage (continuous_hyperbolic_action _)),?_,B,?_⟩
  · exact Set.mem_iInter.mpr hw
  · intro z hz x hx
    obtain ⟨r,hr,y,hxy⟩ := hS x
    let i : S := ⟨r,hr⟩
    have hy : y∉T i := by
      intro hy
      apply hx
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨y,hy,hxy⟩⟩
    rw [←hxy,fullCuspFromPrincipal_height]
    exact hT i _ (Set.mem_iInter.mp hz i) y hy

lemma fullCuspProfileSum_locally_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (w : HyperbolicSpace) :
    ∃T : Finset FullCuspClasses,fullCuspProfileSum F =ᶠ[𝓝 w]
      (fun z => ∑x∈T,F (fullCuspHeight x z)) := by
  obtain ⟨U,hU,hw,T,hT⟩ := full_high_locally_finite w
  refine ⟨T,?_⟩
  filter_upwards [hU.mem_nhds hw] with z hz
  apply tsum_eq_sum
  intro x hx
  exact hF _ (hT z hz x hx).le

lemma fullCuspProfileSum_continuous (F : ℝ→ℝ) (hF : ∀v≤1,F v=0) (hFc : Continuous F) :
    Continuous (fullCuspProfileSum F) := by
  rw [continuous_iff_continuousAt]
  intro w
  obtain ⟨T,hT⟩ := fullCuspProfileSum_locally_finite F hF w
  apply ContinuousAt.congr _ hT.symm
  exact (continuous_finsetSum T (fun x hx => hFc.comp (fullCuspHeight_continuous x))).continuousAt

lemma cuspBarrier_continuous (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    Continuous (cuspBarrier a b) :=
  continuous_const.add (fullCuspProfileSum_continuous _
    (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha)) (cuspBarrierProfile_smooth a b).continuous)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups

lemma fullCuspHeight_chart_contDiffAt (x : FullCuspClasses) (p : SpatialCoordinates)
    (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => fullCuspHeight x (hyperbolicSpatialChart.symm q)) p := by
  induction x using Quotient.inductionOn with
  | _ M =>
    have hh : ContDiffAt ℝ ∞ (fun q => mobiusSpatial (integralComplexMatrix M) q 2) p :=
      (contDiff_apply ℝ ℝ 2).contDiffAt.comp p
        (mobiusSpatial_contDiffAt _ p (hyperbolicSpatialChart_target_positive hp))
    apply hh.congr_of_eventuallyEq
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with q hq
    rw [hyperbolicSpatialChart_symm_eq hq]
    exact congrArg (fun r : SpatialCoordinates => r 2)
      (mobiusSpatial_coordinates (integralComplexMatrix M) q
        (hyperbolicSpatialChart_target_positive hq))

lemma fullCuspProfileSum_chart_contDiffAt (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (hFc : ContDiff ℝ ∞ F) (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => fullCuspProfileSum F (hyperbolicSpatialChart.symm q)) p := by
  obtain ⟨T,hT⟩ := fullCuspProfileSum_locally_finite F hF (hyperbolicSpatialChart.symm p)
  have hc := hyperbolicSpatialChart.continuousAt_symm hp
  have he := hT.comp_tendsto hc
  apply ContDiffAt.congr_of_eventuallyEq _ he
  exact ContDiffAt.sum (fun x hx => hFc.contDiffAt.comp p
    (fullCuspHeight_chart_contDiffAt x p hp))

lemma cuspBarrier_chart_contDiffAt (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    ContDiffAt ℝ ∞ (fun q => cuspBarrier a b (hyperbolicSpatialChart.symm q)) p :=
  contDiffAt_const.add (fullCuspProfileSum_chart_contDiffAt _
    (fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha))
    (cuspBarrierProfile_smooth a b) p hp)

lemma kernelQuotientBarrier_continuous (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    Continuous (kernelQuotientBarrier a b) :=
  (cuspBarrier_continuous a b ha hab).quotient_lift _

lemma kernelQuotientBarrier_contMDiff (a b : ℝ) (ha : 1≤a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (kernelQuotientBarrier a b) := by
  intro q
  rw [contMDiffAt_iff]
  refine ⟨(kernelQuotientBarrier_continuous a b ha hab).continuousAt,?_⟩
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hh := cuspBarrier_chart_contDiffAt a b ha hab _ hp
  have he : (fun p => kernelQuotientBarrier a b ((kernelQuotientChart q).symm p))=
      (fun p => cuspBarrier a b (hyperbolicSpatialChart.symm p)) := by
    funext p
    rw [kernelQuotientChart_symm]
    rfl
  have hh' := (he.symm ▸ hh).contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

lemma cuspBarrier_euclidean_contDiffAt (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun q => cuspBarrier a b (euclideanToHyperbolic q)) p :=
  (((kernelQuotientBarrier_contMDiff a b ha hab).comp kernelProjection_contMDiff)
    (euclideanToHyperbolic p) |>.comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

def positiveHeightLaplacian (F : ℝ→ℝ) (v : ℝ) : ℝ :=
  v*deriv F v-v^2*deriv (deriv F) v

def cuspBarrierDefectProfile (a b v : ℝ) : ℝ :=
  positiveHeightLaplacian (cuspBarrierProfile a b) v-cuspBarrierProfile a b v

lemma positiveHeightLaplacian_smooth (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (positiveHeightLaplacian F) := by
  have hD : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  exact (contDiff_id.mul hD).sub ((contDiff_id.pow 2).mul ((contDiff_infty_iff_deriv.mp hD).2))

lemma cuspBarrierDefectProfile_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (cuspBarrierDefectProfile a b) :=
  (positiveHeightLaplacian_smooth _ (cuspBarrierProfile_smooth a b)).sub
    (cuspBarrierProfile_smooth a b)

lemma cuspBarrierDefectProfile_zero (a b v : ℝ) (hab : a<b) (hv : v<a) :
    cuspBarrierDefectProfile a b v=0 := by
  have he : cuspBarrierProfile a b =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds hv] with x hx
    exact cuspBarrierProfile_zero a b hab x hx.le
  have hd := he.deriv_eq
  have hdd : deriv (deriv (cuspBarrierProfile a b)) v=0 := by
    simpa only [show deriv (fun _ : ℝ => (0:ℝ))=(fun _ => 0) from funext (fun x => deriv_const x 0),deriv_const] using he.deriv.deriv_eq
  simp only [deriv_const] at hd
  simp only [cuspBarrierDefectProfile,positiveHeightLaplacian,he.eq_of_nhds,hd,hdd,mul_zero,sub_zero]

lemma cuspBarrierDefectProfile_one (a b v : ℝ) (hab : a<b) (hv : b<v) :
    cuspBarrierDefectProfile a b v=1 := by
  have he : cuspBarrierProfile a b =ᶠ[𝓝 v] (fun x => x-1) := by
    filter_upwards [Ioi_mem_nhds hv] with x hx
    rw [cuspBarrierProfile,cuspTransition_one a b x hab hx.le,one_mul]
  have hd := he.deriv_eq
  have hlin : deriv (fun x : ℝ => x-1)=(fun _ => 1) := by ext x; simp
  have hdd : deriv (deriv (cuspBarrierProfile a b)) v=0 := by
    simpa only [hlin,deriv_const] using he.deriv.deriv_eq
  simp only [deriv_sub_const,deriv_id''] at hd
  simp only [cuspBarrierDefectProfile,positiveHeightLaplacian,he.eq_of_nhds,hd,hdd]
  ring

def cuspBarrierDefect (a b : ℝ) (w : HyperbolicSpace) : ℝ :=
  -1+fullCuspProfileSum (cuspBarrierDefectProfile a b) w

lemma cuspBarrierDefect_invariant (a b : ℝ) (M : SL(2,ActualEisensteinCubic.O))
    (w : HyperbolicSpace) :
    cuspBarrierDefect a b (integralComplexMatrix M • w)=cuspBarrierDefect a b w := by
  rw [cuspBarrierDefect,cuspBarrierDefect,fullCuspProfileSum_invariant]

lemma cuspBarrierDefect_high (a b : ℝ) (ha : 1<a) (hab : a<b)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b<v) :
    cuspBarrierDefect a b (integralComplexMatrix M • upperPoint z v hv)=0 := by
  rw [cuspBarrierDefect_invariant]
  have hx : fullCuspHeight (fullCuspOf 1) (upperPoint z v hv)=v := by
    simp only [fullCuspHeight_of,fullMatrixHeight,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspBarrierDefect,fullCuspProfileSum_eq_single _
    (fun y hy => cuspBarrierDefectProfile_zero a b y hab (hy.trans_lt ha)) _ (fullCuspOf 1)
      (by rw [hx]; linarith),hx,cuspBarrierDefectProfile_one a b v hab hbv]
  ring

def kernelQuotientBarrierDefect (a b : ℝ) : KernelQuotient→ℝ :=
  Quotient.lift (cuspBarrierDefect a b) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (cuspBarrierDefect_invariant a b (M:SL(2,ActualEisensteinCubic.O)) w).symm)

lemma kernelQuotientBarrierDefect_hasCompactSupport (a b : ℝ) (ha : 1<a) (hab : a<b) :
    HasCompactSupport (kernelQuotientBarrierDefect a b) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS b
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S b ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r b := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (cuspBarrierDefect_high a b ha hab r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)

lemma kernelQuotientBarrierDefect_continuous (a b : ℝ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelQuotientBarrierDefect a b) := by
  apply Continuous.quotient_lift
  exact continuous_const.add (fullCuspProfileSum_continuous _
    (fun v hv => cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha))
    (cuspBarrierDefectProfile_smooth a b).continuous)

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

def fullCuspRow (x : FullCuspClasses) : Fin 2→ℂ :=
  complexBottomRow (integralComplexMatrix x.out)

lemma fullCuspRow_ne_zero (x : FullCuspClasses) : fullCuspRow x≠0 :=
  complexBottomRow_ne_zero _

lemma fullCuspRow_height (x : FullCuspClasses) (p : SpatialCoordinates) (hp : 0<p 2) :
    rowHeight (fullCuspRow x) p=fullCuspHeight x (upperPoint (spatialHorizontal p) (p 2) hp) := by
  have hx : fullCuspOf x.out=x := Quotient.out_eq x
  conv_rhs => rw [←hx]
  rw [fullCuspHeight_of,fullMatrixHeight,hyperbolicHeight_action_upperPoint]
  rw [rowHeight_eq_transformedHeight]
  simp only [transformedHeight,heightDenominator,fullCuspRow,complexBottomRow,spatialHorizontal]

def fullCuspProfileField (F : ℝ→ℝ) (p : SpatialCoordinates) : ℝ :=
  ∑'x : FullCuspClasses,F (rowHeight (fullCuspRow x) p)

lemma fullCuspProfileField_eq (F : ℝ→ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    fullCuspProfileField F p=fullCuspProfileSum F (upperPoint (spatialHorizontal p) (p 2) hp) := by
  simp only [fullCuspProfileField,fullCuspProfileSum,fullCuspRow_height _ p hp]

lemma fullCuspRows_locally_finite (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃T : Finset FullCuspClasses,∀ᶠq in 𝓝 p,∀x∉T,rowHeight (fullCuspRow x) q<1 := by
  let w := upperPoint (spatialHorizontal p) (p 2) hp
  obtain ⟨U,hU,hw,T,hT⟩ := full_high_locally_finite w
  have ht : p∈hyperbolicSpatialChart.target := by
    have he : hyperbolicSpatialChart w=p := by
      simp only [w,hyperbolicSpatialChart_apply,hyperbolicSpatialCoordinates,spatialHorizontal,
        hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
      ext j
      fin_cases j <;> simp
    rw [←he]
    exact hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have he : hyperbolicSpatialChart.symm p=w := by
    rw [hyperbolicSpatialChart_symm_eq ht]
  have hnear := (hyperbolicSpatialChart.continuousAt_symm ht) (by simpa only [he] using hU.mem_nhds hw)
  refine ⟨T,?_⟩
  filter_upwards [hnear,hyperbolicSpatialChart.open_target.mem_nhds ht] with q hq hqt
  have hpos := hyperbolicSpatialChart_target_positive hqt
  intro x hx
  rw [fullCuspRow_height x q hpos,←hyperbolicSpatialChart_symm_eq hqt]
  exact hT _ hq x hx

lemma fullCuspProfileField_locally_finite (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃T : Finset FullCuspClasses,fullCuspProfileField F =ᶠ[𝓝 p]
      (fun q => ∑x∈T,F (rowHeight (fullCuspRow x) q)) := by
  obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
  refine ⟨T,?_⟩
  filter_upwards [hT] with q hq
  apply tsum_eq_sum
  intro x hx
  exact hF _ (hq x hx).le

lemma cast_profile_deriv (F : ℝ→ℝ) (hF : Differentiable ℝ F) (v : ℝ) :
    deriv (fun y => (F y:ℂ)) v=((deriv F v:ℝ):ℂ) :=
  (hF v).hasDerivAt.ofReal_comp.deriv

lemma cast_profile_deriv2 (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F) (v : ℝ) :
    deriv (deriv (fun y => (F y:ℂ))) v=((deriv (deriv F) v:ℝ):ℂ) := by
  have he : deriv (fun y => (F y:ℂ))=(fun y => ((deriv F y:ℝ):ℂ)) :=
    funext (cast_profile_deriv F (hF.differentiable (by simp)))
  rw [he]
  exact cast_profile_deriv (deriv F) (((contDiff_infty_iff_deriv.mp hF).2).differentiable (by simp)) v

lemma fullCuspProfile_row_laplacian (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F)
    (x : FullCuspClasses) (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (F (rowHeight (fullCuspRow x) q):ℂ)) p=
      (positiveHeightLaplacian F (rowHeight (fullCuspRow x) p):ℂ) := by
  rw [rowProfile_laplacian (fun y => (F y:ℂ)) (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v hF.contDiffAt)
    _ (fullCuspRow_ne_zero x) p hp,cast_profile_deriv F (hF.differentiable (by simp)),cast_profile_deriv2 F hF]
  simp only [positiveHeightLaplacian,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

lemma fullCuspProfileField_laplacian (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F)
    (hzero : ∀v≤1,F v=0) (hLzero : ∀v≤1,positiveHeightLaplacian F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (fullCuspProfileField F q:ℂ)) p=
      (fullCuspProfileField (positiveHeightLaplacian F) p:ℂ) := by
  obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
  have he : (fun q => (fullCuspProfileField F q:ℂ)) =ᶠ[𝓝 p]
      (fun q => ∑x∈T,(F (rowHeight (fullCuspRow x) q):ℂ)) := by
    filter_upwards [hT] with q hq
    have hh : fullCuspProfileField F q=∑x∈T,F (rowHeight (fullCuspRow x) q) :=
      tsum_eq_sum (fun x hx => hzero _ (hq x hx).le)
    rw [hh]
    push_cast
    rfl
  have hval : fullCuspProfileField (positiveHeightLaplacian F) p=
      ∑x∈T,positiveHeightLaplacian F (rowHeight (fullCuspRow x) p) :=
    tsum_eq_sum (fun x hx => hLzero _ (hT.self_of_nhds x hx).le)
  have hreg : ∀x∈T,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (fun z => (F (rowHeight (fullCuspRow x) z):ℂ)) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (fun z => (F (rowHeight (fullCuspRow x) z):ℂ)) q j)) (q j) := by
    intro x hx q hq j
    have hd := rowProfile_axis_derivatives (fun v => (F v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v hF.contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) q hq j
    exact ⟨hd.1.differentiableAt,hd.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p he,axisLaplacian_finset_sum T _ hreg p hp,hval]
  rw [←Finset.sum_neg_distrib]
  push_cast
  exact Finset.sum_congr rfl (fun x hx => fullCuspProfile_row_laplacian F hF x p hp)

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm -/

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups

namespace CubicEisenstein

def kernelTestPartial (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) : ℂ :=
  fderiv ℝ (kernelTestField f) (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)

lemma kernelTestPartial_add (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f+g) w j=kernelTestPartial f w j+kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f+g)=kernelTestField f+kernelTestField g := rfl
  rw [he,fderiv_add ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestPartial_sub (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f-g) w j=kernelTestPartial f w j-kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f-g)=kernelTestField f-kernelTestField g := rfl
  rw [he,fderiv_sub ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestPartial_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (c•f) w j=c*kernelTestPartial f w j := by
  unfold kernelTestPartial
  have he : kernelTestField (c•f)=c•kernelTestField f := rfl
  rw [he,fderiv_const_smul ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestEnergyDensity_eq_partials (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w=(hyperbolicHeight w)^2*∑j:Fin 3,‖kernelTestPartial f w j‖^2 := by
  have hd := ((kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)).hasFDerivAt
  have hr := (Complex.reCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  change fderiv ℝ (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)=_ at hr
  change fderiv ℝ (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)=_ at hi
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change (kernelTestPartial f w j).re^2+(kernelTestPartial f w j).im^2=‖kernelTestPartial f w j‖^2
  simpa only [Complex.normSq_apply,pow_two] using Complex.normSq_eq_norm_sq (kernelTestPartial f w j)

lemma kernelTestEnergyDensity_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (c•f) w=‖c‖^2*kernelTestEnergyDensity f w := by
  simp only [kernelTestEnergyDensity_eq_partials,kernelTestPartial_smul,norm_mul,mul_pow,←Finset.mul_sum]
  ring

lemma kernelTestEnergyDensity_parallelogram (f g : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (f+g) w+kernelTestEnergyDensity (f-g) w=
      2*(kernelTestEnergyDensity f w+kernelTestEnergyDensity g w) := by
  simp only [kernelTestEnergyDensity_eq_partials,kernelTestPartial_add,kernelTestPartial_sub]
  rw [←mul_add,←Finset.sum_add_distrib]
  simp only [parallelogram_law_with_norm ℂ,←Finset.mul_sum,Finset.sum_add_distrib]
  ring

lemma kernelQuotientEnergyDensity_smul (c : ℂ) (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelQuotientEnergyDensity (c•f) q=‖c‖^2*kernelQuotientEnergyDensity f q := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_smul c f w

lemma kernelQuotientEnergyDensity_parallelogram (f g : kernelSmoothTests) (q : KernelQuotient) :
    kernelQuotientEnergyDensity (f+g) q+kernelQuotientEnergyDensity (f-g) q=
      2*(kernelQuotientEnergyDensity f q+kernelQuotientEnergyDensity g q) := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_parallelogram f g w

lemma kernelDirichletEnergy_smul (c : ℂ) (f : kernelSmoothTests) :
    kernelDirichletEnergy (c•f)=‖c‖^2*kernelDirichletEnergy f := by
  unfold kernelDirichletEnergy
  simp_rw [kernelQuotientEnergyDensity_smul]
  exact integral_const_mul _ _

lemma kernelDirichletEnergy_parallelogram (f g : kernelSmoothTests) :
    kernelDirichletEnergy (f+g)+kernelDirichletEnergy (f-g)=
      2*(kernelDirichletEnergy f+kernelDirichletEnergy g) := by
  unfold kernelDirichletEnergy
  rw [←integral_add (kernelQuotientEnergyDensity_integrable _) (kernelQuotientEnergyDensity_integrable _)]
  simp_rw [kernelQuotientEnergyDensity_parallelogram]
  rw [integral_const_mul,integral_add (kernelQuotientEnergyDensity_integrable _) (kernelQuotientEnergyDensity_integrable _)]

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups InnerProductSpace

def kernelGradientAt (w : HyperbolicSpace) : kernelSmoothTests→ₗ[ℂ]EuclideanSpace ℂ (Fin 3) where
  toFun f := WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*kernelTestPartial f w j)
  map_add' f g := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_add,mul_add]
  map_smul' c f := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_smul,smul_eq_mul,mul_left_comm]

lemma kernelGradientAt_norm_sq (w : HyperbolicSpace) (f : kernelSmoothTests) :
    ‖kernelGradientAt w f‖^2=kernelTestEnergyDensity f w := by
  rw [PiLp.norm_sq_eq_of_L2,kernelTestEnergyDensity_eq_partials]
  change (∑j:Fin 3,‖(hyperbolicHeight w:ℂ)*kernelTestPartial f w j‖^2)=_
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (hyperbolicHeight_pos w).le,
    Finset.mul_sum]

def kernelDirichletPairDensity (f g : kernelSmoothTests) (q : KernelQuotient) : ℂ :=
  ((kernelQuotientEnergyDensity (f+g) q:ℂ)-(kernelQuotientEnergyDensity (f-g) q:ℂ)+
    ((kernelQuotientEnergyDensity (f-Complex.I•g) q:ℂ)-
      (kernelQuotientEnergyDensity (f+Complex.I•g) q:ℂ))*Complex.I)/4

lemma kernelDirichletPairDensity_coordinate (f g : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=
      inner ℂ (kernelGradientAt w f) (kernelGradientAt w g) := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [←map_add,←map_sub,←map_smul,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
  rfl

lemma kernelDirichletPairDensity_integrable (f g : kernelSmoothTests) :
    Integrable (kernelDirichletPairDensity f g) (integralQuotientVolume globalKubotaKernel) := by
  have hf : ∀h : kernelSmoothTests,Integrable (fun q => (kernelQuotientEnergyDensity h q:ℂ))
      (integralQuotientVolume globalKubotaKernel) := fun h =>
    (kernelQuotientEnergyDensity_integrable h).ofReal
  exact ((hf (f+g)).sub (hf (f-g)) |>.add (((hf (f-Complex.I•g)).sub (hf (f+Complex.I•g))).mul_const _)).div_const _

lemma kernelDirichletPairDensity_add_right (f g h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (g+h) q=kernelDirichletPairDensity f g q+kernelDirichletPairDensity f h q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_add,inner_add_right]

lemma kernelDirichletPairDensity_smul_right (c : ℂ) (f g : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (c•g) q=c*kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_smul,inner_smul_right]

lemma kernelDirichletPairDensity_conj (f g : kernelSmoothTests) (q : KernelQuotient) :
    star (kernelDirichletPairDensity g f q)=kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change star (kernelDirichletPairDensity g f (integralOrbitProjection globalKubotaKernel w))=
      kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)
    rw [kernelDirichletPairDensity_coordinate,kernelDirichletPairDensity_coordinate]
    exact inner_conj_symm _ _

lemma kernelDirichletPairDensity_self (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f f q=(kernelQuotientEnergyDensity f q:ℂ) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f f (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_coordinate,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
    rfl

def kernelDirichletForm (f g : kernelSmoothTests) : ℂ :=
  ∫q,kernelDirichletPairDensity f g q ∂integralQuotientVolume globalKubotaKernel

lemma kernelDirichletForm_add_right (f g h : kernelSmoothTests) :
    kernelDirichletForm f (g+h)=kernelDirichletForm f g+kernelDirichletForm f h := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_add_right]
  exact integral_add (kernelDirichletPairDensity_integrable f g) (kernelDirichletPairDensity_integrable f h)

lemma kernelDirichletForm_smul_right (c : ℂ) (f g : kernelSmoothTests) :
    kernelDirichletForm f (c•g)=c*kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_smul_right]
  exact integral_const_mul _ _

lemma kernelDirichletForm_conj (f g : kernelSmoothTests) :
    star (kernelDirichletForm g f)=kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp only [Complex.star_def]
  rw [←integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (kernelDirichletPairDensity_conj f g)

lemma kernelDirichletForm_self (f : kernelSmoothTests) :
    kernelDirichletForm f f=(kernelDirichletEnergy f:ℂ) := by
  unfold kernelDirichletForm kernelDirichletEnergy
  simp_rw [kernelDirichletPairDensity_self]
  exact integral_complex_ofReal

lemma kernelDirichletForm_self_nonneg (f : kernelSmoothTests) : 0≤(kernelDirichletForm f f).re := by
  rw [kernelDirichletForm_self,Complex.ofReal_re]
  exact kernelDirichletEnergy_nonneg f

end CubicEisenstein

namespace CompletedGauss

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open CanonicalQuadraticSieve ActualEisensteinCubic

theorem integrated_product_quadratic (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : ℝ→Ideal O→Ideal O→ℂ,
      (∀n b,Continuous (fun t => β t n b)) →
      (∀t,∀n∈S,∀b∈T,‖β t n b‖≤lengthScale) →
    ∀rowPhase : idealRange K→ℝ→ℂ,(∀k,Continuous (rowPhase k)) → (∀k t,‖rowPhase k t‖≤1) →
    ∀b : 𝓢(ℝ,ℂ),
      (∑k : idealRange K,‖∫t : ℝ,b t*(rowPhase k t*
        ∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β t n v)‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2*(∫t : ℝ,‖b t‖)^2 := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_scaled ε hε
  refine ⟨C,hC,?_⟩
  intro K U B lengthScale hK hU hB hL S T hS hT β hβc hβ rowPhase hωc hω b
  let E := C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2
  have hE : 0≤E := by dsimp [E]; positivity
  let φ : idealRange K→ℝ→ℂ := fun k t => rowPhase k t*
    ∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β t n v
  have hφc (k : idealRange K) : Continuous (φ k) := by
    apply (hωc k).mul
    apply continuous_finsetSum
    intro n hn
    apply continuous_finsetSum
    intro v hv
    exact continuous_const.mul (hβc n v)
  have hφbound (t : ℝ) : (∑k,‖φ k t‖^2)≤E := by
    apply le_trans _ (hbound K U B lengthScale hK hU hB hL S T hS hT (β t) (hβ t))
    apply Finset.sum_le_sum
    intro k hk
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω k t)) 2
  have hpoint (k : idealRange K) (t : ℝ) : ‖φ k t‖≤Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖φ j t‖) (Finset.mem_univ k)).trans (hφbound t)
  have hφint (k : idealRange K) : Integrable (fun t : ℝ => b t*φ k t) :=
    b.integrable.mul_bdd (hφc k).aestronglyMeasurable (Filter.Eventually.of_forall (hpoint k))
  exact finite_integral_energy_bound b φ E hE b.integrable.norm hφint hφbound

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve

def completedRowFiber (S : Finset (Ideal O)) (Q A T : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => rowPowerfulPart I=A ∧ rowMaskPart I Q=T)

theorem rowResidualPart_injective_on_fiber (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hS : ∀I∈S,I≠0) : Set.InjOn (fun I => rowResidualPart I Q) (completedRowFiber S Q A T) := by
  intro I hI J hJ he
  change rowResidualPart I Q=rowResidualPart J Q at he
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
  calc
    I = rowPowerfulPart I*rowMaskPart I Q*rowResidualPart I Q := (row_powerful_mask_residual_product I Q (hS I hIS)).symm
    _ = rowPowerfulPart J*rowMaskPart J Q*rowResidualPart J Q := by rw [hIA,hJA,hIT,hJT,he]
    _ = J := row_powerful_mask_residual_product J Q (hS J hJS)

theorem completedRowFiber_residual_range (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (I : Ideal O)
    (hI : I∈completedRowFiber S Q A T) :
    rowResidualPart I Q∈idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))) := by
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  apply mem_idealRange.mpr
  refine ⟨rowResidualPart_admissible I Q hbad,?_⟩
  rw [rowResidualPart_norm I Q (hS I hIS).1,hIA,hIT]
  exact div_le_div_of_nonneg_right (hS I hIS).2 (by positivity)

theorem completedRowFiber_energy_le (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (f : Ideal O→ℂ) :
    (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)≤
      ∑J : idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))),‖f J.val‖^2 := by
  let U := (completedRowFiber S Q A T).image (fun I => rowResidualPart I Q)
  have he : (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)=∑J∈U,‖f J‖^2 := by
    rw [Finset.sum_image (rowResidualPart_injective_on_fiber S Q A T (fun I hI => (hS I hI).1))]
  rw [he,Finset.sum_coe_sort (s := idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ)))) (f := fun J : Ideal O => ‖f J‖^2)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact completedRowFiber_residual_range S Q A T hbad K hS I hI
  · intro _ _ _
    exact sq_nonneg _

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve

theorem completed_kernel_three_window
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*CubicReflectionKernel.paperKernel (Vstar W)
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨C,hC,h⟩ := completed_kernel_log_separation V slope M hm hv W a b ha hsupp hW A 0
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

theorem completed_smooth_quadratic
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      quadraticRow k.val (primaryGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar W)
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨Ck,hCk,hkernel⟩ := completed_kernel_three_window V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ W a b ha hsupp hW A
  refine ⟨Cq*(Ck^2+1),by positivity,?_⟩
  intro K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  obtain ⟨g,hsep,hg⟩ := hkernel R hR
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*FourierBridge.logPhase t (-2*yr k)
  let βt : ℝ→Ideal O→Ideal O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*FourierBridge.logPhase t (yn n))*(V₂ (yb v)*FourierBridge.logPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖FourierBridge.logPhase t x‖=1 := FourierBridge.logPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal O) (hn : n∈S) (v : Ideal O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (FourierBridge.logPhase_continuous_left _)
  have hβtc (n v : Ideal O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (FourierBridge.logPhase_continuous_left _))).mul
      (continuous_const.mul (FourierBridge.logPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*CubicReflectionKernel.paperKernel (Vstar W)
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,quadraticRow k.val (primaryGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal O) : Integrable (fun t : ℝ =>
        g t*(rowPhase k t*(quadraticRow k.val (primaryGenerator (n*v))*βt t n v))) := by
      apply g.integrable.mul_bdd (c := ‖quadraticRow k.val (primaryGenerator (n*v))*β n v‖)
      · exact ((hrowPhasec k).mul (continuous_const.mul (hβtc n v))).aestronglyMeasurable
      · filter_upwards [] with t
        simp only [rowPhase,βt,norm_mul,hphase,mul_one]
        have hv01 : ‖V₀ (yr k)‖*‖V₁ (yn n)‖≤1 := by
          simpa only [one_mul] using mul_le_mul (hV₀n (yr k)) (hV₁n (yn n)) (norm_nonneg _) zero_le_one
        have hv012 : (‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖≤1 := by
          simpa only [one_mul] using mul_le_mul hv01 (hV₂n (yb v)) (norm_nonneg _) zero_le_one
        calc
          _ = (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*
            ((‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖) := by ring
          _ ≤ (‖quadraticRow k.val (primaryGenerator (n*v))‖*‖β n v‖)*1 :=
            mul_le_mul_of_nonneg_left hv012 (by positivity)
          _ = _ := by ring
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (fun v hv => hint n v))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum _ (fun v hv => hint n v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hsep (yr k) (yn n) (yb v),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [rowPhase,βt]
    ring
  simp_rw [he]
  apply hi.trans
  have hpow : 0<(1+R)^A := by positivity
  have hmass : (∫t : ℝ,‖g t‖)≤Ck/(1+R)^A := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hg)
  have hmass2 := pow_le_pow_left₀ (integral_nonneg (fun t => norm_nonneg _)) hmass 2
  have hbase : 0≤Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by positivity
  calc
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*(Ck/(1+R)^A)^2 :=
      mul_le_mul_of_nonneg_left hmass2 hbase
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*((Ck^2+1)/(1+R)^(2*A)) := by
      apply mul_le_mul_of_nonneg_left _ hbase
      rw [div_pow,←pow_mul]
      have hp : A*2=2*A := Nat.mul_comm _ _
      rw [hp]
      exact div_le_div_of_nonneg_right (by nlinarith : Ck^2≤Ck^2+1) (by positivity)
    _ = _ := by ring

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff

namespace InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

def initialLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  ((CubicReflectionKernel.logProfile_compact W a b ha hs).mul_left
    (f := fun t : ℝ => (Real.exp (t/2) : ℂ))).toSchwartzMap (by
      change ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (t/2) : ℂ)*W (Real.exp t))
      have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (t/2)) :=
        Real.contDiff_exp.comp (contDiff_id.div_const 2)
      exact (Complex.ofRealCLM.contDiff.comp he).mul
        (hW.comp Real.contDiff_exp))

@[simp] lemma initialLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    initialLogProfile W a b ha hs hW t =
      (Real.exp (t/2) : ℂ)*W (Real.exp t) := rfl

theorem initialLogProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∀ t, initialLogProfile W a b ha hs hW t ≠ 0 →
      |t| ≤ |Real.log a|+|Real.log b|+1 := by
  intro t ht
  have hw : W (Real.exp t) ≠ 0 := by
    intro hz
    simp only [initialLogProfile_apply, hz, mul_zero] at ht
    exact ht rfl
  have hm := hs hw
  have hlo : Real.log a ≤ t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  have hhi : t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos t) hm.2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem initialLogProfile_normalized {ι : Type*} (p : ι → O)
    (hp : ∀ i, p i ≠ 0) (S : Finset ι) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S =
      (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p S/Z) := by
  let n := ‖eisEmbedding (∏ i ∈ S,p i)‖
  have hn : 0 < n := norm_pos_iff.mpr
    (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
  have hpos : 0 < n^2/Z := div_pos (sq_pos_of_pos hn) hZ
  have hexp : Real.exp (Real.log (n^2/Z)/2)=n/Real.sqrt Z := by
    rw [←JointLogSeparation.sqrt_exp_half, Real.exp_log hpos,
      Real.sqrt_div (sq_nonneg n), Real.sqrt_sq hn.le]
  change ((Real.exp (Real.log (n^2/Z)/2) : ℂ)*W (Real.exp (Real.log (n^2/Z)))) /
    (n : ℂ) = (Real.sqrt Z : ℂ)⁻¹*W (n^2/Z)
  rw [hexp, Real.exp_log hpos, Complex.ofReal_div]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hsz : (Real.sqrt Z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hZ).ne'
  field_simp

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma mobiusRow_mul (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (c : ℂ) (z : O) :
    mobiusRow p hg F Ψ m (fun S => c*H S) z = c*mobiusRow p hg F Ψ m H z := by
  simp only [mobiusRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [inputColumn]
  ring

omit [DecidableEq ι] in
theorem mobiusRow_initial_normalization (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z =
      (Real.sqrt Z : ℂ)⁻¹*mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z := by
  have hc : normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) =
      fun T => (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p T/Z) := by
    funext T
    exact initialLogProfile_normalized p hp T Z hZ W a b ha hs hW
  rw [hc, mobiusRow_mul]

omit [DecidableEq ι] in
theorem mobiusRow_initial_energy (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ‖mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z‖^2 =
      ‖mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z‖^2/Z := by
  rw [mobiusRow_initial_normalization p hg hp F Ψ m z Z hZ W a b ha hs hW,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hZ), mul_pow, inv_pow, Real.sq_sqrt hZ.le]
  ring

end InitialMeanSquare

end

end OAI

end

