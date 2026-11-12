module

public import Green64.Library.Analysis.NumberTheory.DirichletL.MeanSquare.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.BarrierPotential -/

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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma axisLaplacian_const_add (c : ℂ) (f : SpatialCoordinates→ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c+f q) p=axisLaplacian f p := by
  unfold axisLaplacian axisSlice
  simp only [deriv_const_add,deriv_const_add']

lemma fullCuspProfileField_summable (F : ℝ→ℝ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    Summable (fun x => F (rowHeight (fullCuspRow x) p)) := by
  simpa only [fullCuspRow_height _ p hp] using
    fullCuspProfileSum_summable F hF (upperPoint (spatialHorizontal p) (p 2) hp)

lemma fullCuspProfileField_add (F G : ℝ→ℝ) (hF : ∀v≤1,F v=0) (hG : ∀v≤1,G v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    fullCuspProfileField (fun v => F v+G v) p=fullCuspProfileField F p+fullCuspProfileField G p :=
  (fullCuspProfileField_summable F hF p hp).tsum_add
    (fullCuspProfileField_summable G hG p hp)

lemma cuspBarrierProfile_laplacian_zero (a b v : ℝ) (ha : 1<a) (hab : a<b) (hv : v≤1) :
    positiveHeightLaplacian (cuspBarrierProfile a b) v=0 := by
  have hh := cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  rw [cuspBarrierDefectProfile,cuspBarrierProfile_zero a b hab v (hv.trans ha.le),sub_zero] at hh
  exact hh

def cuspBarrierField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  1+fullCuspProfileField (cuspBarrierProfile a b) p

def cuspBarrierDefectField (a b : ℝ) (p : SpatialCoordinates) : ℝ :=
  -1+fullCuspProfileField (cuspBarrierDefectProfile a b) p

lemma cuspBarrierField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierField a b p=cuspBarrier a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierField,cuspBarrier,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierDefectField_eq (a b : ℝ) (p : SpatialCoordinates) (hp : 0<p 2) :
    cuspBarrierDefectField a b p=cuspBarrierDefect a b (upperPoint (spatialHorizontal p) (p 2) hp) := by
  rw [cuspBarrierDefectField,cuspBarrierDefect,fullCuspProfileField_eq _ p hp]

lemma cuspBarrierField_laplace_defect (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (fun q => (cuspBarrierField a b q:ℂ)) p-(cuspBarrierField a b p:ℂ)=
      (cuspBarrierDefectField a b p:ℂ) := by
  have hF : ∀v≤1,cuspBarrierProfile a b v=0 :=
    fun v hv => cuspBarrierProfile_zero a b hab v (hv.trans ha.le)
  have hD : ∀v≤1,cuspBarrierDefectProfile a b v=0 :=
    fun v hv => cuspBarrierDefectProfile_zero a b v hab (hv.trans_lt ha)
  have hid : positiveHeightLaplacian (cuspBarrierProfile a b)=
      fun v => cuspBarrierDefectProfile a b v+cuspBarrierProfile a b v := by
    funext v
    rw [cuspBarrierDefectProfile,sub_add_cancel]
  have hh := fullCuspProfileField_laplacian _ (cuspBarrierProfile_smooth a b) hF
    (fun v hv => cuspBarrierProfile_laplacian_zero a b v ha hab hv) p hp
  simp only [cuspBarrierField,Complex.ofReal_add,Complex.ofReal_one,axisLaplacian_const_add]
  rw [hh,hid,fullCuspProfileField_add _ _ hD hF p hp]
  simp only [cuspBarrierDefectField,Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_one]
  ring

def kernelBarrierPotential (a b : ℝ) (q : KernelQuotient) : ℝ :=
  1+kernelQuotientBarrierDefect a b q/kernelQuotientBarrier a b q

lemma kernelBarrierPotential_lower (a b : ℝ) (ha : 1<a) (hab : a<b) :
    ∃K : Set KernelQuotient,IsCompact K ∧ ∃C : ℝ,0≤C ∧
      ∀q,1-C*(K.indicator (fun _ => (1:ℝ))) q≤kernelBarrierPotential a b q := by
  let D := kernelQuotientBarrierDefect a b
  let K := tsupport D
  have hK : IsCompact K := kernelQuotientBarrierDefect_hasCompactSupport a b ha hab
  obtain ⟨C,hC⟩ := (kernelQuotientBarrierDefect_hasCompactSupport a b ha hab).exists_bound_of_continuous
    (kernelQuotientBarrierDefect_continuous a b ha hab)
  refine ⟨K,hK,max C 0,le_max_right _ _,fun q => ?_⟩
  have hphi := kernelQuotientBarrier_one_le a b ha.le hab q
  have hpos : 0<kernelQuotientBarrier a b q := by linarith
  by_cases hq : q∈K
  · rw [Set.indicator_of_mem hq,mul_one,kernelBarrierPotential]
    have hD : -max C 0≤D q := by
      have hn : -‖D q‖≤D q := neg_abs_le (D q)
      exact (neg_le_neg ((hC q).trans (le_max_left C 0))).trans hn
    have hdiv : -max C 0≤D q/kernelQuotientBarrier a b q := by
      apply (le_div_iff₀ hpos).mpr
      have hm : -max C 0*kernelQuotientBarrier a b q≤-max C 0 := by
        nlinarith [mul_nonneg (le_max_right C 0) (sub_nonneg.mpr hphi)]
      exact hm.trans hD
    linarith
  · rw [Set.indicator_of_notMem hq,mul_zero,sub_zero,kernelBarrierPotential]
    have hz : D q=0 := image_eq_zero_of_notMem_tsupport hq
    change 1≤1+D q/kernelQuotientBarrier a b q
    rw [hz,zero_div,add_zero]

lemma cuspBarrier_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrier a b (euclideanToHyperbolic p)=cuspBarrierField a b p.ofLp := by
  rw [cuspBarrierField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma cuspBarrierDefect_euclidean_eq (a b : ℝ) (p : EuclideanSpatial) (hp : 0<p 2) :
    cuspBarrierDefect a b (euclideanToHyperbolic p)=cuspBarrierDefectField a b p.ofLp := by
  rw [cuspBarrierDefectField_eq a b p.ofLp hp,euclideanToHyperbolic_positive p hp]
  congr 1
  simp only [spatialHorizontal,mul_comm]

lemma kernelQuotientBarrier_laplace_defect (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelQuotientBarrier a b (kernelEuclideanProjection p)+
          kernelQuotientBarrierDefect a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  have hf : ∀q,0<q 2→ ContDiffAt ℝ ∞
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) q :=
    fun q hq => Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt a b ha.le hab q hq)
  rw [positiveEuclideanLaplacian_eq_axis _ hf p hp]
  have he : ∀q : SpatialCoordinates,0<q 2→
      (kernelQuotientBarrier a b (kernelEuclideanProjection (WithLp.toLp 2 q)):ℂ)=
        (cuspBarrierField a b q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq a b (WithLp.toLp 2 q) hq)
  rw [axisLaplacian_congr_positive _ _ he p.ofLp hp]
  have hh := cuspBarrierField_laplace_defect a b ha hab p.ofLp hp
  change -axisLaplacian _ p.ofLp=((cuspBarrier a b (euclideanToHyperbolic p)+
    cuspBarrierDefect a b (euclideanToHyperbolic p):ℝ):ℂ)
  rw [cuspBarrier_euclidean_eq a b p hp,cuspBarrierDefect_euclidean_eq a b p hp,Complex.ofReal_add]
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernelBarrierPotential_continuous (a b : ℝ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelBarrierPotential a b) := by
  apply continuous_const.add
  exact (kernelQuotientBarrierDefect_continuous a b ha hab).div
    (kernelQuotientBarrier_continuous a b ha.le hab) (fun q => by
      have hq := kernelQuotientBarrier_one_le a b ha.le hab q
      linarith)

lemma kernelBarrierPotential_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian
      (fun q => (kernelQuotientBarrier a b (kernelEuclideanProjection q):ℂ)) p=
        ((kernelBarrierPotential a b (kernelEuclideanProjection p)*
          kernelQuotientBarrier a b (kernelEuclideanProjection p):ℝ):ℂ) := by
  rw [kernelQuotientBarrier_laplace_defect a b ha hab p hp]
  apply congrArg Complex.ofReal
  have hn : kernelQuotientBarrier a b (kernelEuclideanProjection p)≠0 := by
    have hq := kernelQuotientBarrier_one_le a b ha.le hab (kernelEuclideanProjection p)
    linarith
  rw [kernelBarrierPotential,add_mul,one_mul,div_mul_cancel₀ _ hn]

lemma kernelSmoothTest_weighted_mass_integrable (V : KernelQuotient→ℝ) (hV : Continuous V)
    (f : kernelSmoothTests) :
    Integrable (fun q => V q*‖f.1 q‖^2) (integralQuotientVolume globalKubotaKernel) := by
  apply (hV.mul (f.2.1.continuous.norm.pow 2)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact f.2.2
  intro q hq
  by_contra hn
  have hz : f.1 q=0 := image_eq_zero_of_notMem_tsupport hn
  apply hq
  change V q*‖f.1 q‖^2=0
  rw [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero]

lemma kernelBarrierPotential_weighted_integrable (a b : ℝ) (ha : 1<a) (hab : a<b)
    (f : kernelSmoothTests) :
    Integrable (fun q => kernelBarrierPotential a b q*‖f.1 q‖^2)
      (integralQuotientVolume globalKubotaKernel) :=
  kernelSmoothTest_weighted_mass_integrable _ (kernelBarrierPotential_continuous a b ha hab) f

end

open scoped ComplexConjugate

theorem ground_state_square_completion (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    ‖d‖^2 - b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) =
      ‖d - (b/a : ℝ)*z‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  field_simp
  ; ring

theorem ground_state_directional_inequality (a b : ℝ) (ha : a ≠ 0) (z d : ℂ) :
    b*((2*(conj z*d).re*a - ‖z‖^2*b)/a^2) ≤ ‖d‖^2 := by
  have hh := ground_state_square_completion a b ha z d
  nlinarith [sq_nonneg ‖d - (b/a : ℝ)*z‖]

end CubicEisenstein

namespace SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstQuantitativeBudget_below_rank (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (windows : Fin 7→ℝ→ℂ) (C Cd Ct Γ E oldHeight B M H U A₀ Vmax : ℝ) (N J Ntail : ℕ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤C → 0≤Γ → 0≤E → 1≤U → 1≤B → 0≤H →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B) →
      (∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail side≤
        (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*(((X/B^3)*(Real.exp 1*B)^3)*F)*
          (((Real.exp 1*B)*U)^ε*(Cd+Ct*globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail)+
           C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
             (canonicalDensityConstant E J oldHeight*Clo+globalTerminalConstant A₀ Vmax*(Ksrc/Z^η)*Chi/Z^(η*N))) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_state_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks side
    windows C Cd Ct Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hΓ hE hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ ih
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hK0 : 0<Ksrc := zero_lt_one.trans_le hstate.row_ge_one
  have hKcut : 0<Ksrc/Z^η := div_pos hK0 (Real.rpow_pos_of_pos hZ0 _)
  have hell : 0<X/B^3 := div_pos hstate.column_pos (pow_pos hB0 _)
  have hBsup : 1≤Real.exp 1*B :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  apply hbound p hp hcop hg hc hinj pool blocks side Ψ m windows C Cd Ct Γ E oldHeight
    (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U Z η A₀ Vmax N J Ntail
    hC hΓ hE hU hKcut hell hBsup hstate.label_ge_one hH hKU hellU hBU hHU heU hZ0
    hA hV hV₁ hV₂ hVs₁ hVs₂ (fun u=>hstate.coefficient.norm_le hbase u) hb₁ hb₂
  dsimp only
  intro a r j hj ray q hq s
  let source := globalQuantitativeSource p pool blocks (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side
  have hk : ∀x∈source,x.source.frequency≠0 :=
    globalQuantitativeSource_frequency_ne_zero p pool blocks (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side
  have hb₁' : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B :=
    fun x hx=>hb₁ x.first.block (globalQuantitativeSource_block_mem p pool blocks
      (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side x hx)
  have hb₂' : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B :=
    fun x hx=>hb₂ x.first.block (globalQuantitativeSource_block_mem p pool blocks
      (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U side x hx)
  have hs := canonicalStateCondition_cutoff_retained p hp base bad Z η Ψ m labels X F Ksrc hstate
    hpbad source side q j hq (if side then a.1 else a.2) r ray B
    hZ hZbig hη hηsmall hB0 hprogress hk hb₁' hb₂' (Finset.mem_filter.mp hj).2.le
  have hr : fixedDepthRank Z (globalLogRep j 8*Real.exp 1)<fixedDepthRank Z Ksrc := by
    have := hs.1
    omega
  exact ⟨(ih _ _ _ _ _ _ hs.2.1 hr s).1,(ih _ _ _ _ _ _ hs.2.2 hr s).2⟩

end

section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem reopenedCanonicalFirstErrors (g : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0→|t|≤M) (ε : ℝ) (hε : 0<ε) (A : ℕ) :
    ∃Czero Ctail : ℝ,0≤Czero ∧ 0≤Ctail ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (Γ t Ksrc Kcut ell B F lengthScale : ℝ),
      0≤Γ → 0<Ksrc → 0<Kcut → 0<ell → 1≤B → 1≤F → 1≤lengthScale → ell*Real.exp M≤lengthScale →
      (∀u,‖Ψ u‖≤1) → (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,I≠⊥) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      (‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc ell‖≤
        Czero*B^(1+ε)*ell*F*Γ^2*Ksrc) ∧
      (‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc Kcut ell‖≤
        Ctail*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
          (1+(Ksrc/Kcut)/Real.exp (2*M))^A) := by
  obtain ⟨Cz,hCz,hzero⟩ := full_uniform_canonicalFirstZero_bound ε hε
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_canonicalSourceTail_bound ε hε A
  let G : ℝ := SchwartzMap.seminorm ℝ 0 0 g
  have hG : 0≤G := apply_nonneg _ _
  have hgG : ∀x,‖g x‖≤G := fun x=>SchwartzMap.norm_le_seminorm ℝ g x
  have hgupper : ∀x,g x≠0→x≤M := fun x hx=>(le_abs_self x).trans (hgM x hx)
  refine ⟨Cz*Real.exp M*G^2*‖paperRadialFourier rowMajorant 0‖,
    Ct*G^2*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant,by positivity,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool Q labels β Ψ m Γ t Ksrc Kcut ell B F lengthScale
    hΓ hKsrc hKcut hell hB hF hL hML hΨ hβ hQB hI0 hIF
  dsimp only
  have hΨt : ∀u,‖normHeightTwist Ψ t u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ t u).trans (hΨ u)
  have hb₁ := fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).1
  have hb₂ := fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).2
  have ha : ∀b∈reopenedCubeFamily Q,∀D∈(pool\b.support).powerset,∀I∈labels,
      ‖reopenedPairCoefficient β b D I‖≤Γ^2 :=
    fun b hb D hD I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb D I hI
  constructor
  · have hz := hzero p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant (Γ^2) G G ell Ksrc M B F (sq_nonneg Γ) hG hG hell hB hF
      hΨt hΨt (reopenedCubeFamily_admissible Q) hb₁ hb₂ hI0 hIF ha hgG hgG hgupper
    change ‖canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant Ksrc ell‖≤_ at hz
    rw [abs_of_pos hKsrc] at hz
    exact hz.trans_eq (by ring)
  · have ht := htail p hp hinj hcop hg hc pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant (Γ^2) G G M M Ksrc Kcut ell B F lengthScale
      (sq_nonneg Γ) hG hG hKsrc hKcut hell hB hF hL hML hML hΨt hΨt
      (reopenedCubeFamily_admissible Q) hb₁ hb₂ hI0 hIF ha hgG hgG hgupper hgupper
    exact ht.trans_eq (by rw [show M+M=2*M by ring]; ring)

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)
open JointLogSeparation (frequencyTwist)

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem reopenedCanonicalRow_two_heights (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (g : 𝓢(ℝ,ℂ))
    (X oldHeight newHeight : ℝ) (hX : 0<X) :
    ‖reopenedCanonicalRow p hp hcop hg pool Q β (normHeightTwist Ψ oldHeight) m f
      (fun S=>frequencyTwist g newHeight (columnLog p X S)) z‖=
    ‖reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f
      (fun S=>frequencyTwist g (oldHeight+newHeight) (columnLog p X S)) z‖ := by
  rw [reopenedCanonicalRow_frequencyTwist_norm p hp hcop hg pool Q β
      (normHeightTwist Ψ oldHeight) m f z g X newHeight hX,
    normHeightTwist_twice,
    reopenedCanonicalRow_frequencyTwist_norm p hp hcop hg pool Q β Ψ m f z g X
      (oldHeight+newHeight) hX]

theorem reopenedCanonicalEnergy_two_heights (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X Ksrc oldHeight newHeight : ℝ) (hX : 0<X) :
    (∑I∈labels,nonzeroRowMajorantSum
      (reopenedCanonicalRow p hp hcop hg pool Q (β I) (normHeightTwist Ψ oldHeight) m
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>frequencyTwist g newHeight (columnLog p X S))) Ksrc).re=
    (∑I∈labels,nonzeroRowMajorantSum
      (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>frequencyTwist g (oldHeight+newHeight) (columnLog p X S))) Ksrc).re := by
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro I hI
  unfold nonzeroRowMajorantSum
  apply tsum_congr
  intro z
  rw [reopenedCanonicalRow_two_heights p hp hcop hg pool Q (β I) Ψ m _ z g X oldHeight newHeight hX]

end

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

theorem CanonicalStateCondition.row_bound
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/40) :
    K≤(X*F)*Z^(-((1:ℝ)/40)) := by
  have hn := element_norm_ge_one m h.mask_ne_zero
  calc
    K = K*1 := (mul_one _).symm
    _ ≤ K*‖eisEmbedding m‖^2 :=
      mul_le_mul_of_nonneg_left hn (zero_le_one.trans h.row_ge_one)
    _ ≤ _ := h.invariant_reserved hZ hη hbudget

theorem canonicalFirstZero_normalization (C Γ X F K B Z ε : ℝ)
    (hC : 0≤C) (hX : 0<X) (hF : 0≤F) (hK : 0≤K) (hB : 1≤B)
    (hrow : K≤(X*F)*Z^(-((1:ℝ)/40))) :
    B*(C*(Real.exp 1*B)^(1+ε)*(X/B^3)*F*Γ^2*K)≤
      (C*(Real.exp 1)^(1+ε))*B^ε*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hc : 0≤C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F) := by
    positivity
  calc
    _ = (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K/B := by
      rw [Real.mul_rpow (Real.exp_pos _).le hB0.le,Real.rpow_add hB0,Real.rpow_one]
      field_simp

    _ ≤ (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K :=
      div_le_self (mul_nonneg hc hK) hB
    _ ≤ (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*((X*F)*Z^(-((1:ℝ)/40))) :=
      mul_le_mul_of_nonneg_left hrow hc
    _ = _ := by ring

end

theorem canonicalFirstTail_numerator (C Γ B₀ B lengthScale F K U ε : ℝ)
    (hC : 0≤C) (_hB₀ : 0≤B₀) (hB : 0≤B) (hL : 0≤lengthScale) (hF : 0≤F)
    (hK : 1≤K) (hU : 1≤U) (hε : 0≤ε)
    (hB₀U : B₀≤U) (hBU : B≤U) (hLU : lengthScale≤U) (hFU : F≤U) (hKU : K≤U) :
    B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*K*(1+lengthScale^3*B^4/K)^2)≤
      4*C*Γ^2*U^(25+ε) := by
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hratio : lengthScale^3*B^4/K≤U^7 := by
    calc
      _ ≤ lengthScale^3*B^4 := div_le_self (mul_nonneg (pow_nonneg hL _) (pow_nonneg hB _)) hK
      _ ≤ U^3*U^4 := by gcongr
      _ = U^7 := by ring
  have hU7 : 1≤U^7 := one_le_pow₀ hU
  have hs : (1+lengthScale^3*B^4/K)^2≤4*U^14 := by
    have hnonneg : 0≤lengthScale^3*B^4/K := div_nonneg (by positivity) hK0.le
    have ha : 1+lengthScale^3*B^4/K≤2*U^7 := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤1+lengthScale^3*B^4/K) ha 2
    nlinarith [show (U^7)^2=U^14 by ring]
  calc
    _ ≤ U*(C*U^(4+ε)*U^4*U*Γ^2*U*(4*U^14)) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_add hU0,Real.rpow_add hU0]
      norm_num
      ring

theorem canonicalCutoff_ratio (Ksrc Z η : ℝ) (hK : 0<Ksrc) (hZ : 0<Z) :
    Ksrc/(Ksrc/Z^η)=Z^η := by
  have hz := (Real.rpow_pos_of_pos hZ η).ne'
  field_simp

theorem canonicalFirstTail_polynomial (C Γ B₀ B lengthScale F Ksrc U Z η ε M : ℝ) (A : ℕ)
    (hC : 0≤C) (hB₀ : 0≤B₀) (hB : 0≤B) (hL : 0≤lengthScale) (hF : 0≤F)
    (hK : 1≤Ksrc) (hU : 1≤U) (hε : 0≤ε) (hZ : 0<Z)
    (hB₀U : B₀≤U) (hBU : B≤U) (hLU : lengthScale≤U) (hFU : F≤U) (hKU : Ksrc≤U) :
    B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
      (1+(Ksrc/(Ksrc/Z^η))/Real.exp (2*M))^A)≤
      (4*C*Γ^2*(Real.exp (2*M))^A)*U^(25+ε)/Z^(η*(A:ℝ)) := by
  have hK0 : 0<Ksrc := zero_lt_one.trans_le hK
  have hη : 0<Z^η := Real.rpow_pos_of_pos hZ _
  have hden : 0<(Z^η/Real.exp (2*M))^A := pow_pos (div_pos hη (Real.exp_pos _)) _
  rw [canonicalCutoff_ratio Ksrc Z η hK0 hZ]
  calc
    _ = (B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2))/(1+Z^η/Real.exp (2*M))^A := by ring
    _ ≤ (4*C*Γ^2*U^(25+ε))/(1+Z^η/Real.exp (2*M))^A :=
      div_le_div_of_nonneg_right (canonicalFirstTail_numerator C Γ B₀ B lengthScale F Ksrc U ε
        hC hB₀ hB hL hF hK hU hε hB₀U hBU hLU hFU hKU) (by positivity)
    _ ≤ (4*C*Γ^2*U^(25+ε))/(Z^η/Real.exp (2*M))^A := by
      exact div_le_div_of_nonneg_left (by positivity) hden
        (pow_le_pow_left₀ (div_pos hη (Real.exp_pos _)).le (by linarith) A)
    _ = _ := by
      rw [div_pow,←Real.rpow_natCast (Z^η) A,←Real.rpow_mul hZ.le]
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring

open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem CanonicalStateCondition.terminal_energy
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hbase : ∀u,‖base u‖≤1) (hZ : 1<Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/40)
    (V : ℝ→ℂ) (A M t : ℝ) (hM : 0≤M)
    (hV : ∀s,‖V s‖≤M) (hVs : ∀s,V s≠0→|s|≤A)
    (hstop : fixedDepthRank Z K=0 ∨ X≤1) :
    canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ t) m labels V X K≤
      canonicalTerminalConstant A M*(X*F)^2 := by
  have hKF : K≤F := by
    rcases hstop with hr|hx
    · exact ((fixedDepthRank_zero_iff Z K hZ (zero_lt_one.trans_le hstate.row_ge_one)).mp hr).trans
        hstate.label_ge_one
    · have hi := hstate.invariant_reserved hZ.le hη hbudget
      have hz : Z^(-((1:ℝ)/40))≤1 := by
        simpa only [Real.rpow_zero] using
          Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num : -((1:ℝ)/40)≤0)
      have hi' : K*‖ConcreteTraceCRT.eisEmbedding m‖^2≤X*F :=
        hi.trans ((mul_le_mul_of_nonneg_left hz
          (mul_nonneg hstate.column_pos.le (zero_le_one.trans hstate.label_ge_one))).trans_eq (mul_one _))
      exact smallColumn_row_le_label m hstate.mask_ne_zero X F K hx
        (zero_le_one.trans hstate.label_ge_one) (zero_le_one.trans hstate.row_ge_one) hi'
  apply canonicalLogEnergy_terminal p hp hcop hg hc hinj pool (normHeightTwist Ψ t)
    (fun u=>(normHeightTwist_norm_le Ψ t u).trans (hstate.coefficient.norm_le hbase u)) m labels V X F K A M
    hstate.column_pos hstate.label_ge_one hstate.row_ge_one hKF hM hV hVs
  · exact fun I hI=>(hstate.label_bounds I hI).1
  · exact fun I hI=>(hstate.label_bounds I hI).2.2.2

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.CutoffOrders -/

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

namespace SecondPassArithmetic

theorem exists_polynomial_cutoff_order (p q η R : ℝ) (hη : 0<η) :
    ∃N : ℕ,0<N ∧ ∀C Z : ℝ,0≤C → 1≤Z →
      (C*Z^p)^q/Z^(η*N)≤C^q*Z^(-R) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((p*q+R)/η))
  have hN0 : 0<N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hNR : (p*q+R)/η<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hexp : p*q-η*(N:ℝ)≤-R := by
    have hm := (div_lt_iff₀ hη).mp hNR
    nlinarith
  refine ⟨N,hN0,?_⟩
  intro C Z hC hZ
  have hZ0 : 0<Z := by linarith
  calc
    _ = C^q*Z^(p*q-η*N) := by
      rw [Real.mul_rpow hC (by positivity),←Real.rpow_mul hZ0.le,Real.rpow_sub hZ0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (Real.rpow_nonneg hC _)

theorem canonicalFirstTail_reopening_order (η ε R : ℝ) (hη : 0<η) (hε : 0≤ε) :
    ∃N : ℕ,0<N ∧ ∀Cscale C Γ B₀ B lengthScale F Ksrc Z M : ℝ,
      1≤Cscale → 0≤C → 0≤B₀ → 0≤B → 0≤lengthScale → 0≤F → 1≤Ksrc → 1≤Z →
      B₀≤Cscale*Z^4 → B≤Cscale*Z^4 → lengthScale≤Cscale*Z^4 → F≤Cscale*Z^4 → Ksrc≤Cscale*Z^4 →
      B₀*(C*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
        (1+(Ksrc/(Ksrc/Z^η))/Real.exp (2*M))^N)≤
        (4*C*Γ^2*(Real.exp (2*M))^N*Cscale^(25+ε))*Z^(-R) := by
  obtain ⟨N,hN,horder⟩ := exists_polynomial_cutoff_order 4 (25+ε) η R hη
  refine ⟨N,hN,?_⟩
  intro Cscale C Γ B₀ B lengthScale F Ksrc Z M hCs hC hB₀ hB hL hF hK hZ hB₀U hBU hLU hFU hKU
  have hU : 1≤Cscale*Z^4 := one_le_mul_of_one_le_of_one_le hCs (one_le_pow₀ hZ)
  have hb := canonicalFirstTail_polynomial C Γ B₀ B lengthScale F Ksrc (Cscale*Z^4) Z η ε M N
    hC hB₀ hB hL hF hK hU hε (by linarith) hB₀U hBU hLU hFU hKU
  have ho := horder Cscale Z (by linarith) hZ
  have ho' : (Cscale*Z^4)^(25+ε)/Z^(η*N)≤Cscale^(25+ε)*Z^(-R) := by
    norm_num [Real.rpow_natCast] at ho ⊢
    exact ho
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left ho'
    (show 0≤4*C*Γ^2*(Real.exp (2*M))^N by positivity)
  convert hm using 1 <;> ring

theorem reopening_terminal_order (η R : ℝ) (hη : 0<η) :
    ∃N : ℕ,0<N ∧ ∀Z Ksrc : ℝ,1≤Z → 0≤Ksrc → Ksrc≤Z^3 →
      (Ksrc/Z^η)/Z^(η*N)≤Z^(-R) := by
  obtain ⟨N,hN,horder⟩ := exists_polynomial_cutoff_order 3 1 η R hη
  refine ⟨N,hN,?_⟩
  intro Z Ksrc hZ hK hKZ
  have hb : Ksrc/Z^η≤Z^3 := (div_le_self hK (Real.one_le_rpow hZ hη.le)).trans hKZ
  have ho : Z^3/Z^(η*N)≤Z^(-R) := by
    have hh := horder 1 Z zero_le_one hZ
    norm_num [Real.rpow_natCast] at hh ⊢
    exact hh
  exact (div_le_div_of_nonneg_right hb (by positivity)).trans ho

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CompletedGauss (actualSextic)
open ConcreteTraceCRT (eisEmbedding)

theorem sixth_roots_reduce_injective (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) {x y : ActualEisensteinCubic.O}
    (hx : x^6=1) (hy : y^6=1)
    (hxy : Ideal.Quotient.mk P x=Ideal.Quotient.mk P y) : x=y := by
  let : Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
  have hs : x^2=y^2 := cubic_roots_reduce_injective P hg
    (by simpa only [←pow_mul] using hx)
    (by simpa only [←pow_mul] using hy)
    (by simpa only [map_pow] using congrArg (fun z : ActualEisensteinCubic.O⧸P=>z^2) hxy)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h|h
  · exact h
  · have hy0 : Ideal.Quotient.mk P y≠0 := by
      intro hz
      have he := congrArg (Ideal.Quotient.mk P) hy
      simp only [map_pow,map_one,hz,zero_pow (by decide : (6:ℕ)≠0)] at he
      exact zero_ne_one he
    have he : -(Ideal.Quotient.mk P y)=Ideal.Quotient.mk P y := by
      simpa only [h,map_neg] using hxy
    have htwo : (2 : ActualEisensteinCubic.O⧸P)*Ideal.Quotient.mk P y=0 := by linear_combination -he
    exact False.elim ((Ring.two_ne_zero hc) ((mul_eq_zero.mp htwo).resolve_right hy0))

lemma unit_pow_six (u : ActualEisensteinCubic.Oˣ) : (u.val : ActualEisensteinCubic.O)^6=1 := by
  have h := pow_card_eq_one' (x:=u)
  rw [PrimaryIdealUnitReindex.card_units_eq_six] at h
  exact congrArg Units.val h

theorem actualSextic_unit_euler (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) (u : ActualEisensteinCubic.Oˣ) :
    actualSextic P hg (Ideal.Quotient.mk P u.val) =
      eisEmbedding (u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6)) := by
  let : Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
  have hdata : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧ χ^6=1 ∧
      ∀v : (ActualEisensteinCubic.O⧸P)ˣ,Ideal.Quotient.mk P (χ v)=v.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6) := by
    refine ⟨_,rfl,(sexticChar_powers P hg).2.2,?_⟩
    exact sexticChar_reduce_unit P hg hc
  obtain ⟨χ,hχ,hχ6,hreduce⟩ := hdata
  let v : (ActualEisensteinCubic.O⧸P)ˣ := Units.map (Ideal.Quotient.mk P).toMonoidHom u
  have hx : χ v.val ^ 6=1 := by
    rw [←MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),hχ6]
    exact MulChar.one_apply v.isUnit
  have hy : (u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6))^6=1 := by
    rw [←pow_mul,Nat.mul_comm, pow_mul,unit_pow_six,one_pow]
  have he : χ v.val=u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6) :=
    sixth_roots_reduce_injective P hg hc hx hy (by simpa [v] using hreduce v)
  rw [hχ]
  change eisEmbedding (χ v.val)=_
  exact congrArg eisEmbedding he

end CanonicalUnitEuler

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

lemma kernel_mass_le_weighted_mass_add_core
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ)
    (V : KernelQuotient→ℝ) (hV : Continuous V)
    (hlow : ∀q,1-C*(K.indicator (fun _ => (1:ℝ))) q≤V q)
    (f : kernelSmoothTests) :
    ‖kernelSmoothTestsToL2 f‖^2≤
      (∫q,V q*‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)+
        C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2 := by
  have hi : Integrable (fun q => ‖f.1 q‖^2) (integralQuotientVolume globalKubotaKernel) :=
    (kernelSmoothTests_memLp f).norm.integrable_sq
  have hki := hi.indicator hK
  have hw := kernelSmoothTest_weighted_mass_integrable V hV f
  have hpoint : ∀q,‖f.1 q‖^2-C*(K.indicator (fun q => ‖f.1 q‖^2)) q≤V q*‖f.1 q‖^2 := by
    intro q
    have hh := mul_le_mul_of_nonneg_right (hlow q) (sq_nonneg ‖f.1 q‖)
    by_cases hq : q∈K
    · simp only [Set.indicator_of_mem hq] at hh ⊢
      nlinarith
    · simp only [Set.indicator_of_notMem hq,mul_zero,sub_zero,one_mul] at hh ⊢
      exact hh
  have hh := integral_mono (hi.sub (hki.const_mul C)) hw hpoint
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi (hki.const_mul C),integral_const_mul,integral_indicator hK,
    ←kernelSmoothTestsToL2_norm_sq,←kernelMassRestriction_smooth_norm_sq K hK] at hh
  linarith

lemma kernel_compact_coercivity_extend
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ)
    (hcore : ∀f : kernelSmoothTests,‖kernelSmoothTestsToL2 f‖^2≤kernelDirichletEnergy f+
      C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2)
    (u : KernelEnergyGraph) :
    ‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+C*‖kernelEnergyMassRestriction K hK u‖^2 := by
  exact kernelEnergyGraphCore_dense.induction_on u
    (isClosed_le (by fun_prop) (by fun_prop)) (fun f => by
      change ‖kernelSmoothTestsToL2 f‖^2≤‖kernelGradientToL2 f‖^2+
        C*‖kernelMassRestrictionCLM K hK (kernelSmoothTestsToL2 f)‖^2
      rw [kernelGradientToL2_norm_sq]
      exact hcore f)

lemma kernel_barrier_coercivity_of_ground_state
    (hground : ∀f : kernelSmoothTests,
      (∫q,kernelBarrierPotential 2 3 q*‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
        kernelDirichletEnergy f) :
    ∃K : Set KernelQuotient,∃hK : IsCompact K,∃C : ℝ,0≤C ∧
      IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) ∧
      ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
        C*‖kernelEnergyMassRestriction K hK.measurableSet u‖^2 := by
  obtain ⟨K,hK,C,hC,hlow⟩ := kernelBarrierPotential_lower 2 3 (by norm_num) (by norm_num)
  refine ⟨K,hK,C,hC,kernelEnergyMassRestriction_isCompact K hK,?_⟩
  apply kernel_compact_coercivity_extend
  intro f
  exact (kernel_mass_le_weighted_mass_add_core K hK.measurableSet C
    (kernelBarrierPotential 2 3) (kernelBarrierPotential_continuous 2 3 (by norm_num) (by norm_num))
    hlow f).trans (add_le_add (hground f) le_rfl)

end

open scoped Topology ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ground_state_test_fderiv (f : E → ℂ) (u : E → ℝ) (x v : E)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (hux : u x ≠ 0) :
    fderiv ℝ (fun y => ‖f y‖^2/u y) x v =
      (2*(conj (f x)*fderiv ℝ f x v).re*u x - ‖f x‖^2*fderiv ℝ u x v)/(u x)^2 := by
  have hc : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    simpa only [zero_add,one_smul,Pi.add_apply,id_eq] using!
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v)
  have hx : (fun t : ℝ => x+t•v) 0 = x := by simp
  have hfc : HasDerivAt (fun t : ℝ => f (x+t•v)) (fderiv ℝ f x v) 0 := by
    have hh : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ)•v) := by simpa using hf.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have huc : HasDerivAt (fun t : ℝ => u (x+t•v)) (fderiv ℝ u x v) 0 := by
    have hh : HasFDerivAt u (fderiv ℝ u x) (x+(0:ℝ)•v) := by simpa using hu.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have hzero : (fun t : ℝ => u (x+t•v)) 0 ≠ 0 := by simpa using hux
  have hq := hfc.norm_sq.div huc hzero
  have hdiff : DifferentiableAt ℝ (fun y => ‖f y‖^2/u y) x := by
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using! (hf.norm_sq (𝕜 := ℂ)).mul (hu.inv hux)
  have hqc : HasDerivAt (fun t : ℝ => ‖f (x+t•v)‖^2/u (x+t•v))
      (fderiv ℝ (fun y => ‖f y‖^2/u y) x v) 0 := by
    have hh : HasFDerivAt (fun y => ‖f y‖^2/u y)
        (fderiv ℝ (fun y => ‖f y‖^2/u y) x) (x+(0:ℝ)•v) := by simpa using hdiff.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have he := hqc.unique hq
  simpa only [zero_smul,add_zero,real_inner_eq_re_inner ℂ,RCLike.inner_apply',RCLike.re_to_complex] using he

theorem ground_state_fderiv_inequality (f : E → ℂ) (u : E → ℝ) (x v : E)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (hux : u x ≠ 0) :
    fderiv ℝ u x v * fderiv ℝ (fun y => ‖f y‖^2/u y) x v ≤ ‖fderiv ℝ f x v‖^2 := by
  rw [ground_state_test_fderiv f u x v hf hu hux]
  exact ground_state_directional_inequality (u x) (fderiv ℝ u x v) hux (f x) (fderiv ℝ f x v)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
namespace CubicEisenstein

section

def kernelGroundStateTest (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests) : kernelSmoothTests := by
  have hn : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (fun q => ‖f.1 q‖^2) :=
    (contDiff_norm_sq ℂ).contMDiff.comp f.2.1
  have hg := hn.div₀ hφ (fun q => (hpos q).ne')
  refine ⟨fun q => ((‖f.1 q‖^2/φ q : ℝ) : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp hg, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact f.2.2
  intro q hq
  by_contra hh
  have hz : f.1 q = 0 := image_eq_zero_of_notMem_tsupport hh
  exact hq (by simp [hz])

@[simp] theorem kernelGroundStateTest_apply (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests) (q : KernelQuotient) :
    (kernelGroundStateTest φ hφ hpos f).1 q = ((‖f.1 q‖^2/φ q : ℝ) : ℂ) := rfl

theorem kernelGroundStateTest_tsupport (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests) :
    tsupport (kernelGroundStateTest φ hφ hpos f).1 ⊆ tsupport f.1 := by
  apply closure_minimal _ (isClosed_tsupport f.1)
  intro q hq
  by_contra hh
  have hz : f.1 q = 0 := image_eq_zero_of_notMem_tsupport hh
  exact hq (by simp [hz])

def kernelTruncatedWeight (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ) : kernelSmoothTests := by
  refine ⟨fun q => ((χ q*φ q : ℝ) : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp (hχ.mul hφ), ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact hχK
  intro q hq
  by_contra hh
  have hz : χ q = 0 := image_eq_zero_of_notMem_tsupport hh
  exact hq (by simp [hz])

@[simp] theorem kernelTruncatedWeight_apply (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ) (q : KernelQuotient) :
    (kernelTruncatedWeight χ φ hχ hχK hφ).1 q = ((χ q*φ q : ℝ) : ℂ) := rfl

theorem kernelRealLift_contDiffAt (φ : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt ℝ ∞ (fun p => φ (kernelEuclideanProjection p)) p :=
  (((hφ.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

theorem kernelEuclideanProjection_continuousAt (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContinuousAt kernelEuclideanProjection p :=
  (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
    (euclideanToHyperbolic_contMDiffAt p hp).continuousAt

theorem kernelTruncatedWeight_field_eq (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (p : EuclideanSpatial) (hp : 0 < p 2)
    (hχone : χ =ᶠ[𝓝 (kernelEuclideanProjection p)] (fun _ => 1)) :
    kernelTestField (kernelTruncatedWeight χ φ hχ hχK hφ) =ᶠ[𝓝 p]
      (fun q => (φ (kernelEuclideanProjection q) : ℂ)) := by
  have he := hχone.comp_tendsto (kernelEuclideanProjection_continuousAt p hp)
  filter_upwards [he] with q hq
  change χ (kernelEuclideanProjection q) = 1 at hq
  change ((χ (kernelEuclideanProjection q)*φ (kernelEuclideanProjection q) : ℝ) : ℂ) = _
  rw [hq,one_mul]

theorem kernelTruncatedPotential_memLp (χ φ V : KernelQuotient → ℝ)
    (hχ : Continuous χ) (hχK : HasCompactSupport χ) (hφ : Continuous φ) (hV : Continuous V) :
    MemLp (fun q => ((χ q*V q*φ q : ℝ) : ℂ)) 2 (integralQuotientVolume globalKubotaKernel) := by
  have hc : Continuous (fun q => ((χ q*V q*φ q : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((hχ.mul hV).mul hφ)
  apply hc.memLp_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact hχK
  intro q hq
  by_contra hh
  have hz : χ q = 0 := image_eq_zero_of_notMem_tsupport hh
  exact hq (by simp [hz])

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ComplexConjugate

theorem ground_state_ofReal_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v : E) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => (u y : ℂ)) x v = (fderiv ℝ u x v : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ u) x v = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv]
  rfl

theorem ground_state_self_product (z : ℂ) : (star z*z).re = ‖z‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.star_def,Complex.mul_re,
    Complex.conj_re,Complex.conj_im]
  ring

theorem kernelEnergyDensity_euclidean (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    kernelQuotientEnergyDensity f (kernelEuclideanProjection p) =
      (p 2)^2 * ∑ j : Fin 3, ‖fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector j)‖^2 := by
  have hh := congrArg Complex.re (kernelDirichletPairDensity_euclidean f f p hp)
  rw [kernelDirichletPairDensity_self] at hh
  rw [← Complex.ofReal_pow,Complex.mul_re] at hh
  simpa only [Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum,ground_state_self_product] using hh

theorem kernelGroundState_pair_le_at
    (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0 < p 2)
    (hχone : χ =ᶠ[𝓝 (kernelEuclideanProjection p)] (fun _ => 1)) :
    (kernelDirichletPairDensity (kernelTruncatedWeight χ φ hχ hχK hφ)
      (kernelGroundStateTest φ hφ hpos f) (kernelEuclideanProjection p)).re ≤
      kernelQuotientEnergyDensity f (kernelEuclideanProjection p) := by
  let u : EuclideanSpatial → ℝ := fun q => φ (kernelEuclideanProjection q)
  let F : EuclideanSpatial → ℂ := kernelTestField f
  have hu : DifferentiableAt ℝ u p := (kernelRealLift_contDiffAt φ hφ p hp).differentiableAt (by simp)
  have hF : DifferentiableAt ℝ F p := (kernelTestField_contDiffAt f p hp).differentiableAt (by simp)
  have hu0 : u p ≠ 0 := (hpos _).ne'
  have hG : DifferentiableAt ℝ (fun q => ‖F q‖^2/u q) p := by
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using! (hF.norm_sq (𝕜 := ℂ)).mul (hu.inv hu0)
  have hh (j : Fin 3) :
      fderiv ℝ (kernelTestField (kernelTruncatedWeight χ φ hχ hχK hφ)) p (euclideanCoordinateVector j) =
        (fderiv ℝ u p (euclideanCoordinateVector j) : ℂ) := by
    rw [(kernelTruncatedWeight_field_eq χ φ hχ hχK hφ p hp hχone).fderiv_eq]
    exact ground_state_ofReal_fderiv u p _ hu
  have hg (j : Fin 3) :
      fderiv ℝ (kernelTestField (kernelGroundStateTest φ hφ hpos f)) p (euclideanCoordinateVector j) =
        (fderiv ℝ (fun q => ‖F q‖^2/u q) p (euclideanCoordinateVector j) : ℂ) := by
    change fderiv ℝ (fun q => ((‖F q‖^2/u q : ℝ) : ℂ)) p (euclideanCoordinateVector j) = _
    exact ground_state_ofReal_fderiv _ p _ hG
  rw [kernelDirichletPairDensity_euclidean _ _ p hp,kernelEnergyDensity_euclidean f p hp]
  simp only [hh,hg,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,
    ← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  exact ground_state_fderiv_inequality F u p (euclideanCoordinateVector j) hF hu hu0

theorem kernelGroundState_pair_le
    (χ φ : KernelQuotient → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ χ) (hχK : HasCompactSupport χ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (f : kernelSmoothTests)
    (hχone : ∀ q ∈ tsupport f.1, χ =ᶠ[𝓝 q] (fun _ => 1)) (q : KernelQuotient) :
    (kernelDirichletPairDensity (kernelTruncatedWeight χ φ hχ hχK hφ)
      (kernelGroundStateTest φ hφ hpos f) q).re ≤ kernelQuotientEnergyDensity f q := by
  by_cases hq : q ∈ tsupport f.1
  · induction q using Quotient.inductionOn with
    | _ w =>
      have he : kernelEuclideanProjection (hyperbolicEuclideanCoordinates w) =
          integralOrbitProjection globalKubotaKernel w := by
        simp only [kernelEuclideanProjection,Function.comp_apply,euclideanToHyperbolic_coordinates]
      have hh := kernelGroundState_pair_le_at χ φ hχ hχK hφ hpos f
        (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
        (by rw [he]; exact hχone _ hq)
      rwa [he] at hh
  · rw [kernelDirichletPairDensity_zero_of_notMem _ _ q
      (fun h => hq (kernelGroundStateTest_tsupport φ hφ hpos f h)),Complex.zero_re]
    exact kernelQuotientEnergyDensity_nonneg f q

theorem kernel_ground_state_inequality (φ V : KernelQuotient → ℝ)
    (hφ : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ φ)
    (hpos : ∀ q, 0 < φ q) (hV : Continuous V)
    (hPDE : ∀ p : EuclideanSpatial, 0 < p 2 →
      positiveEuclideanLaplacian (fun q => (φ (kernelEuclideanProjection q) : ℂ)) p =
        ((V (kernelEuclideanProjection p)*φ (kernelEuclideanProjection p) : ℝ) : ℂ))
    (f : kernelSmoothTests) :
    (∫ q, V q*‖f.1 q‖^2 ∂integralQuotientVolume globalKubotaKernel) ≤ kernelDirichletEnergy f := by
  obtain ⟨χ,hχ,hχK,hχone,hχrange⟩ := kernelCompact_smooth_cutoff (tsupport f.1) f.2.2
  let h := kernelTruncatedWeight χ φ hχ hχK hφ
  let g := kernelGroundStateTest φ hφ hpos f
  let A : KernelQuotient → ℂ := fun q => ((χ q*V q*φ q : ℝ) : ℂ)
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    kernelTruncatedPotential_memLp χ φ V hχ.continuous hχK hφ.continuous hV
  have hcoord : ∀ p : EuclideanSpatial, 0 < p 2 →
      kernelEuclideanProjection p ∈ tsupport g.1 →
      kernelCoordinateLaplacian h p = A (kernelEuclideanProjection p) := by
    intro p hp hpg
    have hfmem : kernelEuclideanProjection p ∈ tsupport f.1 :=
      kernelGroundStateTest_tsupport φ hφ hpos f hpg
    have hlocal := hχone (kernelEuclideanProjection p) hfmem
    change positiveEuclideanLaplacian (kernelTestField h) p = _
    rw [positiveEuclideanLaplacian_congr _ _ p
      (kernelTruncatedWeight_field_eq χ φ hχ hχK hφ p hp hlocal),hPDE p hp]
    dsimp only [A]
    rw [hlocal.eq_of_nhds,one_mul]
  have hprod (q : KernelQuotient) : star (A q)*g.1 q = ((V q*‖f.1 q‖^2 : ℝ) : ℂ) := by
    change star ((χ q*V q*φ q : ℝ) : ℂ) * ((‖f.1 q‖^2/φ q : ℝ) : ℂ) = _
    by_cases hfzero : f.1 q = 0
    · simp [hfzero]
    · have hq : q ∈ tsupport f.1 := subset_tsupport f.1 hfzero
      have hχq : χ q = 1 := (hχone q hq).eq_of_nhds
      have hφq : φ q ≠ 0 := (hpos q).ne'
      simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,hχq,one_mul]
      congr 1
      field_simp
  have hgreen : kernelDirichletForm h g =
      ((∫ q, V q*‖f.1 q‖^2 ∂integralQuotientVolume globalKubotaKernel : ℝ) : ℂ) := by
    rw [kernelDirichletForm_supported_equation h g A hA hcoord]
    simp_rw [hprod]
    exact integral_complex_ofReal
  have hbound : (∫ q, (kernelDirichletPairDensity h g q).re
      ∂integralQuotientVolume globalKubotaKernel) ≤ kernelDirichletEnergy f := by
    exact integral_mono (kernelDirichletPairDensity_integrable h g).re
      (kernelQuotientEnergyDensity_integrable f)
      (fun q => kernelGroundState_pair_le χ φ hχ hχK hφ hpos f hχone q)
  have hreal : (∫ q, (kernelDirichletPairDensity h g q).re
      ∂integralQuotientVolume globalKubotaKernel) = (kernelDirichletForm h g).re := by
    simpa only [kernelDirichletForm,RCLike.re_to_complex] using integral_re (kernelDirichletPairDensity_integrable h g)
  rw [hreal,hgreen,Complex.ofReal_re] at hbound
  exact hbound

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

theorem kernel_actual_barrier_ground_state (f : kernelSmoothTests) :
    (∫q,kernelBarrierPotential 2 3 q*‖f.1 q‖^2∂integralQuotientVolume globalKubotaKernel)≤
      kernelDirichletEnergy f :=
  kernel_ground_state_inequality (kernelQuotientBarrier 2 3) (kernelBarrierPotential 2 3)
    (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num))
    (fun q => lt_of_lt_of_le zero_lt_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) q))
    (kernelBarrierPotential_continuous 2 3 (by norm_num) (by norm_num))
    (kernelBarrierPotential_equation 2 3 (by norm_num) (by norm_num)) f

theorem kernel_global_exterior_coercivity :
    ∃K : Set KernelQuotient,∃hK : IsCompact K,∃C : ℝ,0≤C ∧
      IsCompactOperator (kernelEnergyMassRestriction K hK.measurableSet) ∧
      ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
        C*‖kernelEnergyMassRestriction K hK.measurableSet u‖^2 :=
  kernel_barrier_coercivity_of_ground_state kernel_actual_barrier_ground_state

end CubicEisenstein

namespace SecondPassArithmetic

theorem lowerCubeBin_mass_product (X F B : ℝ) (hB : B≠0) :
    B*((X/B^3)*(Real.exp 1*B)^2*F)*((X/B^3)*(Real.exp 1*B)^3*F)=
      Real.exp 5*(X*F)^2 := by
  have he : (Real.exp 1)^5=Real.exp 5 := by
    rw [show (5:ℝ)=1+1+1+1+1 by norm_num]
    simp only [Real.exp_add]
    ring
  simp only [mul_pow]
  rw [←he]
  field_simp

theorem canonicalBudget_sqrt_product (b₁ b₂ D₁ D₂ Q : ℝ)
    (hD₁ : 0≤D₁) (hD₂ : 0≤D₂) (hQ : 0≤Q)
    (h₁ : b₁≤D₁*Q) (h₂ : b₂≤D₂*Q) :
    Real.sqrt b₁*Real.sqrt b₂≤Real.sqrt D₁*Real.sqrt D₂*Q := by
  calc
    _ ≤ Real.sqrt (D₁*Q)*Real.sqrt (D₂*Q) :=
      mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hD₁,Real.sqrt_mul hD₂]
      calc
        _ = Real.sqrt D₁*Real.sqrt D₂*(Real.sqrt Q*Real.sqrt Q) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hQ]

theorem canonicalPairBudget_normalized
    (X F B Ksrc Kcut Cf cap U power E t D₁ D₂ b₁ b₂ : ℝ) (J : ℕ)
    (hX : 0<X) (hF : 0≤F) (hB : 0<B) (hKsrc : 0≤Ksrc) (hKcut : 0<Kcut)
    (hCf : 0≤Cf) (hcap : 0≤ cap) (hU : 0≤U) (hE : 0≤E)
    (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (h₁ : b₁≤D₁*((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J))
    (h₂ : b₂≤D₂*((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J)) :
    B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap*
      Real.sqrt b₁*Real.sqrt b₂)≤
    (Real.exp 5*Cf*Real.sqrt D₁*Real.sqrt D₂)*(X*F)^2*
      (Ksrc/Kcut)*cap*U^power*E*(1+‖t‖)^(2*J) := by
  let Q:=((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J)
  have hQ : 0≤Q := by dsimp only [Q];positivity
  have hs := canonicalBudget_sqrt_product b₁ b₂ D₁ D₂ Q hD₁ hD₂ hQ
    (by simpa only [Q,mul_assoc] using h₁) (by simpa only [Q,mul_assoc] using h₂)
  have hfac : 0≤B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  calc
    _ = (B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap))*(Real.sqrt b₁*Real.sqrt b₂) := by ring
    _ ≤ _ := hh
    _ = _ := by
      dsimp only [Q]
      calc
        _ = (B*((X/B^3)*(Real.exp 1*B)^2*F)*((X/B^3)*(Real.exp 1*B)^3*F))*
            ((Ksrc/Kcut)*Cf*cap*Real.sqrt D₁*Real.sqrt D₂*U^power*E*(1+‖t‖)^(2*J)) := by ring
        _ = _ := by rw [lowerCubeBin_mass_product X F B hB.ne'];ring

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.ReopeningBounds -/

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

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem reopenedCanonicalRow_filter (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι→ℂ)
    (keep : (ι→₀ℕ)→Prop) [DecidablePred keep]
    (hβ : ∀v∈Q,¬keep v→β v=0) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z=
      reopenedCanonicalRow p hp hcop hg pool (Q.filter keep) β Ψ m f H z := by
  unfold reopenedCanonicalRow
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hvnot
  have hn : ¬keep v := fun h=>hvnot (Finset.mem_filter.mpr ⟨hv,h⟩)
  simp only [hβ v hv hn,zero_mul,Finset.sum_const_zero]

theorem reopenedCanonicalRow_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι→ℂ)
    (hβ : ∀v∈Q,β v=0) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z=0 := by
  unfold reopenedCanonicalRow
  apply Finset.sum_eq_zero
  intro v hv
  simp only [hβ v hv,zero_mul,Finset.sum_const_zero]

end SecondPassArithmetic

namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation

def progressingCubes (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (H₀ : ℝ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)) :=
  Q.filter (fun v=>H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))

theorem separatedCubeCoefficient_eq_zero_of_small (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (B ξ : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)
    (hsmall : ¬H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)) :
    separatedCubeCoefficient
      (fun u=>reopenedCubeCoefficient H₀ Ψ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
      (fun u=>(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u):ℝ)) B ξ v=0 := by
  have hz : reopenedCubeCoefficient H₀ Ψ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hn
    exact hsmall (reopenedCubeCoefficient_support H₀ Ψ _ hn).2
  simp only [separatedCubeCoefficient,hz,zero_mul]

theorem outsideCanonicalBin_filter (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ→ℂ) (X H₀ : ℝ) :
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀=
      outsideCanonicalBin S D hbad (progressingCubes S D H₀ Q) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin progressingCubes
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hvnot
  have hn : ¬H₀≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) :=
    fun h=>hvnot (Finset.mem_filter.mpr ⟨hv,h⟩)
  have hz : largeCubeCoefficient H₀ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hh
    exact hn (largeCubeCoefficient_support H₀ _ hh).2
  simp only [hz,zero_mul]

theorem progressingCubes_progress (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z F B : ℝ) (hF : 1≤F) (hB : 1≤B)
    (hQ : (progressingCubes S D (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0) Q).Nonempty)
    (hupper : ∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*B) :
    Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F := by
  by_cases hsmall : F<Z^((1:ℝ)/1000)
  · obtain ⟨v,hv⟩ := hQ
    obtain ⟨hvQ,hlo⟩ := Finset.mem_filter.mp hv
    simp only [ite_eq_left hsmall] at hlo
    have he := hlo.trans (hupper v hvQ)
    have hbpos : 0≤Real.exp 1*B := mul_nonneg (Real.exp_pos _).le (zero_le_one.trans hB)
    exact he.trans (le_mul_of_one_le_right hbpos hF)
  · have hb : 1≤Real.exp 1*B :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
    exact (le_of_not_gt hsmall).trans (le_mul_of_one_le_left (zero_le_one.trans hF) hb)

theorem progressingActiveBin_progress (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (b X Z F : ℝ) (j : ℕ) (hF : 1≤F)
    (hQ : (progressingCubes S D (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)
      (activeCubeLogBin S D b X j)).Nonempty) :
    Z^((1:ℝ)/1000)≤(Real.exp 1*normLogScale j)*F :=
  progressingCubes_progress S D (activeCubeLogBin S D b X j) Z F (normLogScale j) hF
    (normLogScale_ge_one j) hQ (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).2)

theorem outsideCanonicalBin_zero_of_empty_filter (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (hQ : progressingCubes S D H₀ Q=∅) :
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀=0 := by
  rw [outsideCanonicalBin_filter S D hbad Q Ψ m f z W X H₀,hQ]
  simp only [outsideCanonicalBin,Finset.sum_empty]

theorem reopenedCanonicalRow_progressing (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ Ξ : ActualEisensteinCubic.O→*ℂ) (m f z : ActualEisensteinCubic.O) (H₀ B ξ : ℝ)
    (H : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D))→ℂ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β:=separatedCubeCoefficient (fun v=>reopenedCubeCoefficient H₀ Ξ (cubeIdeal F v))
      (fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)) B ξ
    reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q β Ψ m f H z=
    reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ
      (progressingCubes S D H₀ Q) β Ψ m f H z := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  apply reopenedCanonicalRow_filter
  intro v hv hsmall
  exact separatedCubeCoefficient_eq_zero_of_small S D H₀ Ξ B ξ v hsmall

end CanonicalRowCompletion

namespace SecondPassArithmetic

section

open MeasureTheory
open FirstPassCubeLabels (firstLogDensity)

def canonicalBudgetCoefficient (C Cd Ct Tmax Clo Chi A M : ℝ) : ℝ :=
  (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*
    (Cd+Ct*Tmax+C*globalRayTripleConstant*
      (6*(∫t : ℝ,firstLogDensity 0 t)^3*Clo+globalTerminalConstant A M*Chi))

theorem canonicalBudgetCoefficient_nonneg (C Cd Ct Tmax Clo Chi A M : ℝ)
    (hC : 0≤C) (hCd : 0≤Cd) (hCt : 0≤Ct) (hTmax : 0≤Tmax)
    (hClo : 0≤Clo) (hChi : 0≤Chi) :
    0≤ canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A M := by
  have hi : 0≤∫t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t=>FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have ht := globalTerminalConstant_nonneg A M
  unfold canonicalBudgetCoefficient globalRayTripleConstant
  positivity

theorem canonicalBudgetScalar_bound
    (C Cd Ct Tmax Clo Chi A M Γ P E t B U deltaLoss ε tailFactor terminalFactor : ℝ) (J : ℕ)
    (hC : 0≤C) (hCd : 0≤Cd) (hCt : 0≤Ct) (hTmax : 0≤Tmax)
    (_hClo : 0≤Clo) (hChi : 0≤Chi) (hΓ : 0≤Γ) (hP : 0≤P)
    (hE : 1≤E) (hB : 0≤B) (hBU : B≤U) (hU : 1≤U) (hδ : 0≤deltaLoss) (hε : 0≤ε)
    (htail : tailFactor≤Tmax) (hterminal : terminalFactor≤1) :
    (∫s : ℝ,firstLogDensity 0 s)*(512*(512*32))*Γ*P*
      ((B*U)^ε*(Cd+Ct*tailFactor)+C*globalRayTripleConstant*U^(deltaLoss+8*ε)*
        (canonicalDensityConstant E J t*Clo+globalTerminalConstant A M*Chi*terminalFactor))≤
    canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A M*
      Γ*P*U^(deltaLoss+8*ε)*E*(1+‖t‖)^(2*J) := by
  have hi : 0≤∫s : ℝ,firstLogDensity 0 s :=
    integral_nonneg (fun s=>FirstPassCubeLabels.firstLogDensity_nonneg 0 s)
  have ht := globalTerminalConstant_nonneg A M
  have hRT : 0≤globalRayTripleConstant := by unfold globalRayTripleConstant;positivity
  have hU0 : 0<U := zero_lt_one.trans_le hU
  have hpow : (B*U)^ε≤U^(deltaLoss+8*ε) := by
    calc
      _ ≤ (U^2)^ε := Real.rpow_le_rpow (mul_nonneg hB hU0.le) (by nlinarith) hε
      _ = U^(2*ε) := by rw [←Real.rpow_natCast U 2,←Real.rpow_mul hU0.le];norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hheight : 1≤(1+‖t‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg t])
  have he : 1≤E*(1+‖t‖)^(2*J) := one_le_mul_of_one_le_of_one_le hE hheight
  have hdiag : (B*U)^ε*(Cd+Ct*tailFactor)≤
      U^(deltaLoss+8*ε)*(Cd+Ct*Tmax)*(E*(1+‖t‖)^(2*J)) := by
    calc
      _ ≤ (B*U)^ε*(Cd+Ct*Tmax) := by gcongr
      _ ≤ U^(deltaLoss+8*ε)*(Cd+Ct*Tmax) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he
  have hchild : canonicalDensityConstant E J t*Clo+globalTerminalConstant A M*Chi*terminalFactor≤
      (6*(∫s : ℝ,firstLogDensity 0 s)^3*Clo+globalTerminalConstant A M*Chi)*
        (E*(1+‖t‖)^(2*J)) := by
    have hterm : globalTerminalConstant A M*Chi*terminalFactor≤
        globalTerminalConstant A M*Chi*(E*(1+‖t‖)^(2*J)) :=
      mul_le_mul_of_nonneg_left (hterminal.trans he) (mul_nonneg ht hChi)
    unfold canonicalDensityConstant
    nlinarith
  have hrest := mul_le_mul_of_nonneg_left hchild
    (mul_nonneg (mul_nonneg hC hRT) (Real.rpow_nonneg hU0.le (deltaLoss+8*ε)))
  have hsum := add_le_add hdiag hrest
  have hwhole := mul_le_mul_of_nonneg_left hsum
    (show 0≤(∫s : ℝ,firstLogDensity 0 s)*(512*(512*32))*Γ*P by positivity)
  exact hwhole.trans_eq (by unfold canonicalBudgetCoefficient;ring)

end
section

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstQuantitativeBudget_bounded (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (windows : Fin 7→ℝ→ℂ) (C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax : ℝ) (N J Ntail : ℕ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤C → 0≤Cd → 0≤Ct → 0≤Tmax → 0≤Γ → 1≤E → 1≤U → 1≤B → 0≤H →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B) →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail≤Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 →
      (∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail side≤
        canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A₀ Vmax*
          Γ*(((X/B^3)*(Real.exp 1*B)^3)*F)*U^(deltaLoss+8*ε)*E*(1+‖oldHeight‖)^(2*J) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_below_rank deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks side
    windows C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hCd hCt hTmax hΓ hE hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ htail hterminal ih
  have hb := hbound p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate
    pool blocks side windows C Cd Ct Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hΓ (zero_le_one.trans hE) hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ ih
  have hX:=hstate.column_pos
  have hF : 0≤F:=zero_le_one.trans hstate.label_ge_one
  have hP : 0≤((X/B^3)*(Real.exp 1*B)^3)*F := by positivity
  have hs := canonicalBudgetScalar_bound C Cd Ct Tmax Clo Chi A₀ Vmax Γ
    (((X/B^3)*(Real.exp 1*B)^3)*F) E oldHeight (Real.exp 1*B) U deltaLoss ε
    (globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail)
    ((Ksrc/Z^η)/Z^(η*(N:ℝ))) J hC hCd hCt hTmax hClo.le hChi.le hΓ hP hE
    (by positivity) hBU hU hδ.le hε.le htail hterminal
  apply hb.trans
  convert hs using 1 ; ring

end

def reopeningScaleConstant (A M : ℝ) : ℝ := 1+Real.exp (A+1)+Real.exp M

def reopeningAuxiliaryScale (A M κ Z : ℝ) : ℝ := reopeningScaleConstant A M*Z^(κ+3)

lemma reopeningScaleConstant_one (A M : ℝ) : 1≤ reopeningScaleConstant A M := by
  unfold reopeningScaleConstant
  linarith [Real.exp_pos (A+1),Real.exp_pos M]

lemma reopeningScaleConstant_exp (A M : ℝ) : Real.exp A≤ reopeningScaleConstant A M := by
  have h : Real.exp A≤Real.exp (A+1) := Real.exp_le_exp.mpr (by linarith)
  unfold reopeningScaleConstant
  linarith [Real.exp_pos M]

theorem globalFirstRowCap_reopening (Z η X F Ksrc B : ℝ)
    (hZ : 0<Z) (hK : 0<Ksrc) (hB : 0<B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F =
      (Real.exp 1)^8*X^2*F^2*Z^η/Ksrc := by
  unfold globalFirstRowCap
  field_simp

theorem globalFirstRowCap_reopening_bound (Z η X F Ksrc B : ℝ)
    (hZ : 1≤Z) (_hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F ≤ (Real.exp 1)^8*Z^13 := by
  rw [globalFirstRowCap_reopening Z η X F Ksrc B (by linarith) (by linarith) (by linarith)]
  have hηZ : Z^η≤Z := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ hη1
  calc
    _ ≤ (Real.exp 1)^8*X^2*F^2*Z^η := div_le_self (by positivity) hK
    _ ≤ (Real.exp 1)^8*(Z^3)^2*(Z^3)^2*Z := by gcongr
    _ = _ := by ring

theorem globalFirstRowCap_reopening_small_power (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) (hδ : 0≤deltaLoss) :
    (max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F))^deltaLoss ≤
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have he : 1≤Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hb := globalFirstRowCap_reopening_bound Z η X F Ksrc B hZ hη hη1 hX hXZ hF hFZ hK hB
  have hmax : max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)≤(Real.exp 1)^8*Z^13 :=
    max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ he) (one_le_pow₀ hZ)) hb
  apply (Real.rpow_le_rpow (by positivity) hmax hδ).trans_eq
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
  norm_num

theorem reopeningAuxiliaryScale_bounds (A M κ Z η X F Ksrc B : ℝ)
    (hκ : 0≤κ) (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (_hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    let U := reopeningAuxiliaryScale A M κ Z
    1≤U ∧ Ksrc/Z^η≤U ∧ X/B^3≤U ∧ Real.exp 1*B≤U ∧ F≤U ∧ Z^κ≤U ∧
      Real.exp M≤U ∧ (X/B^3)*Real.exp M≤U ∧ (X/B^3)⁻¹≤U := by
  let C := reopeningScaleConstant A M
  have hC : 1≤C := reopeningScaleConstant_one A M
  have hCZ : C≤C*Z^(κ+3) := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hZ (by linarith))
  have hZ3 : Z^3≤Z^(κ+3) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num; linarith)
  have hZκ : Z^κ≤Z^(κ+3) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hbase : Z^(κ+3)≤C*Z^(κ+3) := le_mul_of_one_le_left (by positivity) hC
  have hKcut : Ksrc/Z^η≤Z^3 :=
    (div_le_self (by linarith) (Real.one_le_rpow hZ hη)).trans hKZ
  have hell : X/B^3≤X := div_le_self (by linarith) (one_le_pow₀ hB)
  have hB3 : B≤B^3 := by nlinarith [sq_nonneg (B-1)]
  have hBsup : Real.exp 1*B≤Real.exp (A+1)*Z^3 := by
    calc
      _ ≤ Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add]; ring
  have hCA : Real.exp (A+1)≤C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos M]
  have hCM : Real.exp M≤C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos (A+1)]
  have hinv : (X/B^3)⁻¹≤Real.exp A := by
    rw [inv_div]
    exact (div_le_iff₀ (by linarith : 0<X)).mpr hactive
  change 1≤C*Z^(κ+3) ∧ _
  refine ⟨hC.trans hCZ,hKcut.trans (hZ3.trans hbase),
    (hell.trans hXZ).trans (hZ3.trans hbase),?_,hFZ.trans (hZ3.trans hbase),
    hZκ.trans hbase,hCM.trans hCZ,?_,hinv.trans ((reopeningScaleConstant_exp A M).trans hCZ)⟩
  · exact hBsup.trans (mul_le_mul hCA hZ3 (by positivity) (by linarith))
  · calc
      _ ≤ Z^3*Real.exp M := mul_le_mul_of_nonneg_right (hell.trans hXZ) (Real.exp_pos _).le
      _ ≤ Z^(κ+3)*C := mul_le_mul hZ3 hCM (Real.exp_pos _).le (by positivity)
      _ = _ := mul_comm _ _

theorem globalFirstTailFactor_envelope (K ell B F U H : ℝ) (N : ℕ)
    (hK : 0≤K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F)
    (hU : 1≤U) (hH : 0≤H) (hKU : K≤U) (hiell : ell⁻¹≤U) :
    globalFirstTailFactor K ell B F U H N≤4096*U^20/(1+H)^N := by
  have hBi : B⁻¹≤1 := inv_le_one_of_one_le₀ hB
  have hFi : F⁻¹≤1 := inv_le_one_of_one_le₀ hF
  have hratio : K*U^2/(ell^2*B^2*F^2)≤U^5 := by
    calc
      _ = K*U^2*(ell⁻¹)^2*(B⁻¹)^2*(F⁻¹)^2 := by field_simp
      _ ≤ U*U^2*U^2*1^2*1^2 := by gcongr
      _ = _ := by ring
  have hone : 1+U≤2*U := by linarith
  have hinner : 1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2))≤16*U^8 := by
    calc
      _ ≤ 1+(2*U)^3*U^5 := by gcongr
      _ = 1+8*U^8 := by ring
      _ ≤ _ := by have hh : 1≤U^8 := one_le_pow₀ hU; linarith
  unfold globalFirstTailFactor
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (2*U)^4*(16*U^8)^2 := by gcongr
    _ = _ := by ring

theorem globalFirstTailFactor_reopening_power (A M κ Z η X F Ksrc B : ℝ) (N : ℕ)
    (hκ : 0≤κ) (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningAuxiliaryScale A M κ Z) (Z^κ) N ≤
      (4096*(reopeningScaleConstant A M)^20)*Z^(20*(κ+3)-κ*N) := by
  have hZ0 : 0<Z := by linarith
  have hB0 : 0<B := by linarith
  have hX0 : 0<X := by linarith
  have hs := reopeningAuxiliaryScale_bounds A M κ Z η X F Ksrc B hκ hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hBsup : 1≤Real.exp 1*B := one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hbound := globalFirstTailFactor_envelope (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
    (reopeningAuxiliaryScale A M κ Z) (Z^κ) N (by positivity) (by positivity) hBsup hF hs.1
    (by positivity) hs.2.1 hs.2.2.2.2.2.2.2.2
  apply hbound.trans
  have hden : (Z^κ)^N≤(1+Z^κ)^N := pow_le_pow_left₀ (by positivity) (by linarith [Real.rpow_pos_of_pos hZ0 κ]) N
  calc
    _ ≤ 4096*(reopeningAuxiliaryScale A M κ Z)^20/(Z^κ)^N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      unfold reopeningAuxiliaryScale
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_mul_natCast hZ0.le,
        Real.rpow_sub hZ0]
      ring_nf

theorem globalFirstTailFactor_reopening_arbitrary_decay (A M κ R : ℝ) (hκ : 0<κ) :
    ∃N : ℕ,0<N ∧ ∀Z η X F Ksrc B : ℝ,
      1≤Z → 0≤η → 1≤X → X≤Z^3 → 1≤F → F≤Z^3 →
      1≤Ksrc → Ksrc≤Z^3 → 1≤B → B^3≤Real.exp A*X →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
        (reopeningAuxiliaryScale A M κ Z) (Z^κ) N ≤
        (4096*(reopeningScaleConstant A M)^20)*Z^(-R) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((20*(κ+3)+R)/κ))
  have hN0 : 0<N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hNR : (20*(κ+3)+R)/κ<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hexp : 20*(κ+3)-κ*(N:ℝ)≤-R := by
    have hm := (div_lt_iff₀ hκ).mp hNR
    nlinarith
  refine ⟨N,hN0,?_⟩
  intro Z η X F Ksrc B hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  exact (globalFirstTailFactor_reopening_power A M κ Z η X F Ksrc B N hκ.le hZ hη
    hX hXZ hF hFZ hK hKZ hB hactive).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity))

theorem globalFirstTailFactor_reopening_nat_decay (A M Z η X F Ksrc B : ℝ) (R : ℕ)
    (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningScaleConstant A M*Z^4) Z (R+80) ≤
      (4096*(reopeningScaleConstant A M)^20)*Z^(-(R:ℝ)) := by
  have h := globalFirstTailFactor_reopening_power A M 1 Z η X F Ksrc B (R+80)
    (by norm_num) hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hpow : 20*((1:ℝ)+3)-1*((R+80:ℕ):ℝ)=-(R:ℝ) := by push_cast; ring
  rw [hpow] at h
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at h ⊢
  exact h

lemma reopening_cutoff_ratio (Z η Ksrc : ℝ) (hZ : 0<Z) (hK : 0<Ksrc) :
    Ksrc/(Ksrc/Z^η)=Z^η := by field_simp

lemma globalFirstRowCap_reopening_rpow (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) (hδ : 0≤deltaLoss) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss ≤
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have hcap : 0≤globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F := by
    unfold globalFirstRowCap
    positivity
  exact (Real.rpow_le_rpow hcap (le_max_right 1 _) hδ).trans
    (globalFirstRowCap_reopening_small_power Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ)

lemma reopening_cube_bound (A M Z X B : ℝ) (hZ : 1≤Z) (_hX : 1≤X)
    (hXZ : X≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    Real.exp 1*B≤ reopeningScaleConstant A M*Z^3 := by
  have hB3 : B≤B^3 := by nlinarith [sq_nonneg (B-1)]
  have hC : Real.exp (A+1)≤ reopeningScaleConstant A M := by
    unfold reopeningScaleConstant
    linarith [Real.exp_pos M]
  calc
    _ ≤ Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
    _ ≤ Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
    _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
    _ = Real.exp (A+1)*Z^3 := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

theorem reopening_diagonal_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hactive : B^3≤Real.exp A*X) (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(13*deltaLoss+7*ε) := by
  let C := reopeningScaleConstant A M
  have hC : 1≤C := reopeningScaleConstant_one A M
  have hb := reopening_cube_bound A M Z X B hZ hX hXZ hB hactive
  have hprod : (Real.exp 1*B)*(C*Z^4)≤C^2*Z^7 := by
    calc
      _ ≤ (C*Z^3)*(C*Z^4) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hpow : ((Real.exp 1*B)*(C*Z^4))^ε≤(C^2)^ε*Z^(7*ε) := by
    apply (Real.rpow_le_rpow (by positivity) hprod hε).trans_eq
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
    norm_num
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _ ≤ (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*((C^2)^ε*Z^(7*ε)) :=
      mul_le_mul hcap hpow (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by rw [Real.rpow_add (by linarith : 0<Z)]; dsimp [C]; ring

theorem reopening_recursive_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hδ : 0≤deltaLoss) (_hε : 0≤ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(17*deltaLoss+32*ε) := by
  have hC : 0< reopeningScaleConstant A M := lt_of_lt_of_le zero_lt_one (reopeningScaleConstant_one A M)
  have he : (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)=
      reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε) := by
    rw [Real.mul_rpow hC.le (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
    congr 2
    ring
  rw [he]
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _ ≤ (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*
      (reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε)) :=
      mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := by
      have hh : 17*deltaLoss+32*ε=13*deltaLoss+(4*deltaLoss+32*ε) := by ring
      rw [hh]
      simp only [Real.rpow_add (by linarith : 0<Z)]
      ring

theorem reopening_diagonal_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hactive : B^3≤Real.exp A*X) (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(η+13*deltaLoss+7*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_diagonal_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hactive hδ hε) (by positivity)).trans_eq
  rw [show η+13*deltaLoss+7*ε=η+(13*deltaLoss+7*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

theorem reopening_recursive_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(η+17*deltaLoss+32*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_recursive_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hδ hε) (by positivity)).trans_eq
  rw [show η+17*deltaLoss+32*ε=η+(17*deltaLoss+32*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

end SecondPassArithmetic

end

end OAI

end

