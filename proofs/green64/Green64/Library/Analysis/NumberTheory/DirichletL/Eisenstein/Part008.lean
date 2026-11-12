module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CutoffApproximation -/

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

section BoundedConvergence
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] («μ» : Measure α)

omit [CompleteSpace E] in
lemma l2_norm_sq_integral (f : Lp E 2 «μ») : ‖f‖^2=∫a,‖f a‖^2∂«μ» := by
  calc
    ‖f‖^2=inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫a,inner ℝ (f a) (f a)∂«μ» := L2.inner_def _ _
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

omit [CompleteSpace E] in
lemma l2_toLp_sub_norm_sq (f g : α→E) (hf : MemLp f 2 «μ») (hg : MemLp g 2 «μ») :
    ‖hf.toLp f-hg.toLp g‖^2=∫a,‖f a-g a‖^2∂«μ» := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp] with a ha hf hg
  rw [ha]
  simp only [Pi.sub_apply,hf,hg]

omit [CompleteSpace E] in
theorem l2_tendsto_of_bounded_eventuallyEq [IsFiniteMeasure «μ»]
    (f : ℕ→α→E) (g : α→E) (hf : ∀n,MemLp (f n) 2 «μ») (hg : MemLp g 2 «μ»)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hfB : ∀n a,‖f n a‖≤B) (hgC : ∀a,‖g a‖≤C)
    (hlim : ∀a,∀ᶠn : ℕ in atTop,f n a=g a) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hsq : Tendsto (fun n => ∫a,‖f n a-g a‖^2∂«μ») atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence («μ» := «μ»)
      (F := fun n a => ‖f n a-g a‖^2) (f := fun _ => (0:ℝ)) (fun _ => (B+C)^2)
      (fun n => ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2)
      (integrable_const _) ?_ ?_
    · simpa only [integral_zero] using h
    · intro n
      exact Eventually.of_forall (fun a => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hB hC)).mpr
        exact (norm_sub_le _ _).trans (add_le_add (hfB n a) (hgC a)))
    · exact Eventually.of_forall (fun a => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hlim a] with n hn
        simp only [hn,sub_self,norm_zero,zero_pow (by decide : 2≠0)])
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
    simpa only [l2_toLp_sub_norm_sq] using hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hsqrt

end BoundedConvergence

instance kernelFundamentalVolume_finite : IsFiniteMeasure KernelFundamentalVolume := by
  refine ⟨?_⟩
  change (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)) Set.univ<⊤
  rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact hyperbolicFundamentalSet_volume_lt_top globalKubotaKernel globalKubotaKernel_le_levelThree

def kernelFunctionField (f : KernelQuotient→ℂ) (p : EuclideanSpatial) : ℂ :=
  f (kernelEuclideanProjection p)

lemma kernelFunctionField_smooth (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelFunctionField f) p :=
  (((hf.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

def kernelFunctionGradient (f : KernelQuotient→ℂ) (w : HyperbolicSpace) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*
    fderiv ℝ (kernelFunctionField f) (hyperbolicEuclideanCoordinates w) (euclideanCoordinateVector j))

lemma kernelFunctionGradient_continuous (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    Continuous (kernelFunctionGradient f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  apply (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelFunctionField_smooth f hf _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma norm_three_vector_bound (v : EuclideanSpace ℂ (Fin 3)) (B : ℝ) (hB : 0≤B)
    (hv : ∀j,‖v j‖≤B) : ‖v‖≤3*B := by
  have hsq : ‖v‖^2≤3*B^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑j : Fin 3,B^2 := Finset.sum_le_sum (fun j hj =>
        (sq_le_sq₀ (norm_nonneg _) hB).mpr (hv j))
      _ = _ := by simp
  nlinarith [norm_nonneg v,sq_nonneg B]

lemma kernelFunctionGradient_bound (f : KernelQuotient→ℂ) (B : ℝ) (hB : 0≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤B)
    (w : HyperbolicSpace) : ‖kernelFunctionGradient f w‖≤3*B := by
  apply norm_three_vector_bound _ B hB
  intro j
  exact hgrad (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) j

lemma kernelFunctionGradient_memLp (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B : ℝ) (hB : 0≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤B) :
    MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume :=
  MemLp.of_bound (kernelFunctionGradient_continuous f hf).aestronglyMeasurable (3*B)
    (Eventually.of_forall (kernelFunctionGradient_bound f B hB hgrad))

def kernelFunctionCutoff (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) : kernelSmoothTests := by
  refine ⟨fun q => (kernelExhaustionCutoff n q:ℂ)*f q,?_,?_⟩
  · have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1*z.2) := contDiff_fst.mul contDiff_snd
    exact hm.contMDiff.comp
      ((Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)).prodMk_space hf)
  · apply HasCompactSupport.of_support_subset_isCompact (kernelExhaustionCutoff_hasCompactSupport n)
    intro q hq
    by_contra hn
    have hz : kernelExhaustionCutoff n q=0 := image_eq_zero_of_notMem_tsupport hn
    exact hq (by simp [hz])

lemma kernelFunctionCutoff_apply (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) (q : KernelQuotient) :
    (kernelFunctionCutoff n f hf).1 q=(kernelExhaustionCutoff n q:ℂ)*f q := rfl

lemma kernelFunctionCutoff_field (n : ℕ) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    kernelTestField (kernelFunctionCutoff n f hf)=
      fun p => (kernelExhaustionCutoff n (kernelEuclideanProjection p):ℂ)*kernelFunctionField f p := rfl

lemma kernelFunctionGradient_of_test (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelFunctionGradient f.1 w=kernelGradientAt w f := by
  unfold kernelFunctionGradient
  simp only [euclideanCoordinateVector_eq_basis]
  rfl

lemma kernelFunctionCutoff_field_eventually (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    ∀ᶠn : ℕ in atTop,kernelTestField (kernelFunctionCutoff n f hf)=ᶠ[𝓝 p]kernelFunctionField f := by
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [kernelExhaustionCutoff_eventually_one_near (kernelEuclideanProjection p)] with n hn
  filter_upwards [hn.comp_tendsto hc] with q hq
  change kernelExhaustionCutoff n (kernelEuclideanProjection q)=1 at hq
  change (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)*kernelFunctionField f q=kernelFunctionField f q
  rw [hq]
  simp

lemma kernelFunctionCutoff_gradient_eventually (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) (w : HyperbolicSpace) :
    ∀ᶠn : ℕ in atTop,kernelGradientAt w (kernelFunctionCutoff n f hf)=kernelFunctionGradient f w := by
  filter_upwards [kernelFunctionCutoff_field_eventually f hf
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)] with n hn
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  change (hyperbolicHeight w:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf)) _ _=
    (hyperbolicHeight w:ℂ)*fderiv ℝ (kernelFunctionField f) _ _
  rw [hn.fderiv_eq,euclideanCoordinateVector_eq_basis]

lemma kernelFunctionCutoff_mass_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B : ℝ) (_hB : 0≤B) (hbound : ∀q,‖f q‖≤B) (n : ℕ) (q : KernelQuotient) :
    ‖(kernelFunctionCutoff n f hf).1 q‖≤B := by
  rw [kernelFunctionCutoff_apply,norm_mul,Complex.norm_of_nonneg (kernelExhaustionCutoff_bounds n q).1]
  exact (mul_le_mul (kernelExhaustionCutoff_bounds n q).2 (hbound q) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

lemma kernelFunctionCutoff_scaled_deriv_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B G D : ℝ) (hB : 0≤B) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (hcut : ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤D)
    (n : ℕ) (p : EuclideanSpatial) (hp : 0<p 2) (j : Fin 3) :
    ‖(p 2:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf)) p (euclideanCoordinateVector j)‖≤G+B*D := by
  let c : EuclideanSpatial→ℂ:=fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)
  have hc : DifferentiableAt ℝ c p :=
    (kernelFunctionField_smooth (fun q => (kernelExhaustionCutoff n q:ℂ))
      (Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)) p hp).differentiableAt (by simp)
  have hd := (kernelFunctionField_smooth f hf p hp).differentiableAt (by simp)
  rw [kernelFunctionCutoff_field,fderiv_fun_mul hc hd]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  have he : (p 2:ℂ)*(c p*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)+
      kernelFunctionField f p*fderiv ℝ c p (euclideanCoordinateVector j))=
      c p*((p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j))+
        kernelFunctionField f p*((p 2:ℂ)*fderiv ℝ c p (euclideanCoordinateVector j)) := by ring
  change ‖(p 2:ℂ)*(c p*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)+
      kernelFunctionField f p*fderiv ℝ c p (euclideanCoordinateVector j))‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  have hc1 : ‖c p‖≤1 := by
    rw [Complex.norm_of_nonneg (kernelExhaustionCutoff_bounds n _).1]
    exact (kernelExhaustionCutoff_bounds n _).2
  have hleft : ‖c p‖*‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G :=
    (mul_le_mul hc1 (hgrad p hp j) (norm_nonneg _) zero_le_one).trans_eq (one_mul G)
  have hright : ‖kernelFunctionField f p‖*‖(p 2:ℂ)*fderiv ℝ c p (euclideanCoordinateVector j)‖≤B*D :=
    mul_le_mul (hfB (kernelEuclideanProjection p)) (hcut n p hp j) (norm_nonneg _) hB
  simpa only [norm_mul] using add_le_add hleft hright

lemma kernelFunctionCutoff_gradient_bound (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    ∃D : ℝ,0≤D ∧ ∀n : ℕ,∀w : HyperbolicSpace,‖kernelGradientAt w (kernelFunctionCutoff n f hf)‖≤D := by
  obtain ⟨D,hD,hcut⟩ := kernelExhaustionCutoff_scaled_fderiv_bound
  refine ⟨3*(G+B*D),by positivity,?_⟩
  intro n w
  apply norm_three_vector_bound _ (G+B*D) (by positivity)
  intro j
  change ‖(hyperbolicHeight w:ℂ)*fderiv ℝ (kernelTestField (kernelFunctionCutoff n f hf))
    (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)‖≤_
  rw [←euclideanCoordinateVector_eq_basis]
  exact kernelFunctionCutoff_scaled_deriv_bound f hf B G D hB hfB hgrad hcut n
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) j

theorem kernelFunctionCutoff_mass_tendsto (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (B : ℝ) (hB : 0≤B) (hbound : ∀q,‖f q‖≤B) :
    Tendsto (fun n => kernelSmoothTestsToL2 (kernelFunctionCutoff n f hf)) atTop (𝓝 (hfL.toLp f)) := by
  apply l2_tendsto_of_bounded_eventuallyEq (integralQuotientVolume globalKubotaKernel)
    (fun n => (kernelFunctionCutoff n f hf).1) f
    (fun n => kernelSmoothTests_memLp (kernelFunctionCutoff n f hf)) hfL B B hB hB
    (kernelFunctionCutoff_mass_bound f hf B hB hbound) hbound
  intro q
  filter_upwards [kernelExhaustionCutoff_eventually_one q] with n hn
  rw [kernelFunctionCutoff_apply,hn]
  simp

theorem kernelFunctionCutoff_gradient_tendsto (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    Tendsto (fun n => kernelGradientToL2 (kernelFunctionCutoff n f hf)) atTop
      (𝓝 (hgL.toLp (kernelFunctionGradient f))) := by
  obtain ⟨D,hD,hbound⟩ := kernelFunctionCutoff_gradient_bound f hf B G hB hG hfB hgrad
  apply l2_tendsto_of_bounded_eventuallyEq KernelFundamentalVolume
    (fun n w => kernelGradientAt w (kernelFunctionCutoff n f hf)) (kernelFunctionGradient f)
    (fun n => kernelGradientAt_memLp (kernelFunctionCutoff n f hf)) hgL D (3*G) hD (by positivity)
    hbound (kernelFunctionGradient_bound f G hG hgrad)
  exact kernelFunctionCutoff_gradient_eventually f hf

theorem kernel_bounded_smooth_energy_exists (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G) :
    ∃u : KernelEnergyGraph,kernelEnergyMass u=hfL.toLp f ∧
      kernelEnergyGradient u=hgL.toLp (kernelFunctionGradient f) := by
  let x : KernelEnergyAmbient:=WithLp.toLp 2 (hfL.toLp f,hgL.toLp (kernelFunctionGradient f))
  have hm := kernelFunctionCutoff_mass_tendsto f hf hfL B hB hfB
  have hg := kernelFunctionCutoff_gradient_tendsto f hf hgL B G hB hG hfB hgrad
  have hp := hm.prodMk_nhds hg
  have ht : Tendsto (fun n => kernelEnergyCore (kernelFunctionCutoff n f hf)) atTop (𝓝 x) := by
    have h := (WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).symm.continuous.continuousAt.tendsto.comp hp
    exact h
  have hx : x∈kernelEnergyGraphSubmodule := by
    change x∈closure (Set.range kernelEnergyCore)
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun n => ⟨kernelFunctionCutoff n f hf,rfl⟩))
  exact ⟨⟨x,hx⟩,rfl,rfl⟩

def kernelEisensteinRemainderL2 (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) : KernelQuotientL2 :=
  (kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs).toLp
    (kernelEisensteinRemainder a b s (by linarith))

lemma kernelEisensteinRemainderL2_ae (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    kernelEisensteinRemainderL2 a b ha hab s hs=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelEisensteinRemainder a b s (by linarith) :=
  (kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs).coeFn_toLp

theorem kernelEisensteinRemainder_energy (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    ∃u : KernelEnergyGraph,kernelEnergyMass u=kernelEisensteinRemainderL2 a b ha hab s hs := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  have hgrad' : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G := hgrad
  have hgL := kernelFunctionGradient_memLp f hf G hG hgrad'
  obtain ⟨u,hu,hgu⟩ := kernel_bounded_smooth_energy_exists f hf hfL hgL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad'
  exact ⟨u,hu⟩

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold Matrix

lemma axis_update_contDiff (p : SpatialCoordinates) (j : Fin 3) :
    ContDiff ℝ ∞ (fun t => Function.update p j t) := by
  apply contDiff_pi.mpr
  intro k
  by_cases h : k=j
  · subst k
    simpa only [Function.update_self,id_eq] using! (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t))
  · simpa only [Function.update_of_ne h] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => p k))

lemma smooth_positive_axis_regular (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice f p j) (p j) ∧
      DifferentiableAt ℝ (deriv (axisSlice f p j)) (p j) := by
  have hh : ContDiffAt ℝ ∞ (axisSlice f p j) (p j) := by
    have hfp : ContDiffAt ℝ ∞ f (Function.update p j (p j)) := by
      simpa only [Function.update_eq_self] using hf p hp
    have h := hfp.comp (p j) (axis_update_contDiff p j).contDiffAt
    simpa only [axisSlice,Function.comp_def,Function.update_eq_self] using! h
  exact ⟨hh.differentiableAt (by simp),(hh.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma axisLaplacian_sub_smooth (f g : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ ContDiffAt ℝ ∞ f p) (hg : ∀p,0<p 2→ ContDiffAt ℝ ∞ g p)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => f q-g q) p=axisLaplacian f p-axisLaplacian g p := by
  let F : Fin 2→SpatialCoordinates→ℂ:=![f,fun q => (-1:ℂ)*g q]
  have hF : ∀i : Fin 2,∀q,0<q 2→ ContDiffAt ℝ ∞ (F i) q := by
    intro i q hq
    fin_cases i
    · exact hf q hq
    · exact contDiffAt_const.mul (hg q hq)
  have hh := axisLaplacian_finset_sum Finset.univ F
    (fun i hi q hq j => smooth_positive_axis_regular (F i) (hF i) q hq j) p hp
  have he : (fun q => ∑i : Fin 2,F i q)=(fun q => f q-g q) := by
    funext q
    simp [F,Fin.sum_univ_two,sub_eq_add_neg]
  rw [he] at hh
  simp only [Fin.sum_univ_two,F,Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  rw [axisLaplacian_const_mul] at hh
  simpa only [neg_one_mul,sub_eq_add_neg] using hh

lemma eisensteinRemainder_coordinate_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (eisensteinRemainderField a b s) p=
      smoothCuspSeedDefectField a b s p+s*(2-s)*eisensteinRemainderField a b s p := by
  have hD := actual_smoothCuspSeed_laplace_defect a b s ha hab p hp
  unfold eisensteinRemainderField
  rw [axisLaplacian_sub_smooth _ _ (smoothEisenstein_contDiffAt s hs)
    (actual_smoothCuspSeed_contDiffAt a b s ha hab) p hp,smoothEisenstein_eigenfunction s hs p hp]
  linear_combination hD

lemma kernelQuotientDefect_euclidean_eq (a b : ℝ) (s : ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    kernelQuotientDefect a b s (kernelEuclideanProjection p)=smoothCuspSeedDefectField a b s p.ofLp := by
  unfold kernelEuclideanProjection
  simp only [Function.comp_apply]
  rw [euclideanToHyperbolic_positive p hp]
  change smoothCuspSeedDefect a b s _=smoothCuspSeedDefectField a b s p.ofLp
  rw [smoothCuspSeedDefectField,dite_eq_left hp]
  simp only [mul_comm Complex.I]

theorem kernelEisensteinRemainder_operator_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian (kernelFunctionField (kernelEisensteinRemainder a b s hs)) p=
      kernelQuotientDefect a b s (kernelEuclideanProjection p)+
        kernelEisensteinSpectralParameter s*kernelEisensteinRemainder a b s hs (kernelEuclideanProjection p) := by
  let f := kernelFunctionField (kernelEisensteinRemainder a b s hs)
  have hf : ∀q,0<q 2→ ContDiffAt ℝ ∞ f q := kernelEisensteinRemainder_euclidean_smooth a b ha hab s hs
  have he : ∀q : SpatialCoordinates,0<q 2→f (WithLp.toLp 2 q)=eisensteinRemainderField a b s q := by
    intro q hq
    exact kernelEisensteinRemainder_euclidean_eq a b s hs (WithLp.toLp 2 q) hq
  rw [positiveEuclideanLaplacian_eq_axis f hf p hp,
    axisLaplacian_congr_positive _ _ he p.ofLp hp,
    eisensteinRemainder_coordinate_equation a b ha hab s hs p.ofLp hp,
    kernelQuotientDefect_euclidean_eq a b s p hp,kernelEisensteinRemainder_euclidean_eq a b s hs p hp]
  rfl

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernelFunctionCutoff_uniform_near (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (K : Set KernelQuotient) (hK : IsCompact K) :
    ∃N : ℕ,∀n≥N,∀p : EuclideanSpatial,0<p 2→kernelEuclideanProjection p∈K→
      kernelTestField (kernelFunctionCutoff n f hf)=ᶠ[𝓝 p]kernelFunctionField f := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image
    (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousOn
  obtain ⟨N,hN⟩ := exists_nat_gt C
  refine ⟨N,?_⟩
  intro n hn p hp hpK
  have hheight : kernelQuotientBarrier 2 3 (kernelEuclideanProjection p)<(n:ℝ)+1 := by
    have hh := hC ⟨kernelEuclideanProjection p,hpK,rfl⟩
    have hcast : (N:ℝ)≤n := by exact_mod_cast hn
    linarith
  have hnear := (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousAt.eventually_lt_const hheight
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [hc hnear] with q hq
  change (kernelExhaustionProfile n (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)):ℂ)*
    kernelFunctionField f q=kernelFunctionField f q
  rw [kernelExhaustionProfile_one n _ hq.le]
  simp

lemma kernelBoundedFunction_form_equation (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hgL : MemLp (kernelFunctionGradient f) 2 KernelFundamentalVolume)
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p))
    (g : kernelSmoothTests) :
    inner ℂ (hgL.toLp (kernelFunctionGradient f)) (kernelGradientToL2 g)=
      inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g) := by
  obtain ⟨N,hN⟩ := kernelFunctionCutoff_uniform_near f hf (tsupport g.1) g.2.2
  have hconstant : ∀ᶠn : ℕ in atTop,
      inner ℂ (kernelGradientToL2 (kernelFunctionCutoff n f hf)) (kernelGradientToL2 g)=
        inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [kernelGradientToL2_inner,kernelL2_inner_toLp_smooth]
    apply kernelDirichletForm_supported_equation (kernelFunctionCutoff n f hf) g A hA
    intro p hp hpg
    change positiveEuclideanLaplacian (kernelTestField (kernelFunctionCutoff n f hf)) p=A (kernelEuclideanProjection p)
    rw [positiveEuclideanLaplacian_congr _ _ p (hN n hn p hp hpg)]
    exact hEq p hp
  have hlim : Tendsto (fun n => inner ℂ (kernelGradientToL2 (kernelFunctionCutoff n f hf))
      (kernelGradientToL2 g)) atTop (𝓝 (inner ℂ (hgL.toLp (kernelFunctionGradient f)) (kernelGradientToL2 g))) :=
    (kernelFunctionCutoff_gradient_tendsto f hf hgL B G hB hG hfB hgrad).inner
      (tendsto_const_nhds (x := kernelGradientToL2 g))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconstant.mono (fun n hn => hn.symm)))

theorem kernel_bounded_smooth_operator_graph (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f)
    (hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel))
    (B G : ℝ) (hB : 0≤B) (hG : 0≤G) (hfB : ∀q,‖f q‖≤B)
    (hgrad : ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (kernelFunctionField f) p (euclideanCoordinateVector j)‖≤G)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p)) :
    (hfL.toLp f,hA.toLp A)∈kernelEnergyLaplacian.graph := by
  have hgL := kernelFunctionGradient_memLp f hf G hG hgrad
  obtain ⟨u,hum,hug⟩ := kernel_bounded_smooth_energy_exists f hf hfL hgL B G hB hG hfB hgrad
  have hform (v : KernelEnergyGraph) :
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ (hA.toLp A) (kernelEnergyMass v) := by
    exact kernelEnergyGraphCore_dense.induction_on v
      (isClosed_eq (by fun_prop : Continuous (fun v : KernelEnergyGraph =>
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)))
        (by fun_prop : Continuous (fun v : KernelEnergyGraph => inner ℂ (hA.toLp A) (kernelEnergyMass v))))
      (fun g => by
        rw [hug,kernelEnergyGradient_core,kernelEnergyMass_core]
        exact kernelBoundedFunction_form_equation f hf hgL B G hB hG hfB hgrad A hA hEq g)
  have hu : u=kernelVariationalSolution (hfL.toLp f+hA.toLp A) := by
    apply kernelVariationalSolution_unique
    intro v
    rw [hum,hform v,inner_add_left]
  have hm := congrArg kernelEnergyMass hu
  rw [hum] at hm
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  exact hm.symm

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

theorem kernelEisensteinRemainderL2_graph (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    (kernelEisensteinRemainderL2 a b ha hab s hs,
      kernelL2Defect a b (by linarith) hab s+kernelEisensteinSpectralParameter s •
        kernelEisensteinRemainderL2 a b ha hab s hs)∈kernelEnergyLaplacian.graph := by
  let f := kernelEisensteinRemainder a b s (by linarith)
  have hf := kernelEisensteinRemainder_smooth a b ha hab s (by linarith)
  have hfL : MemLp f 2 (integralQuotientVolume globalKubotaKernel) :=
    kernel_eisenstein_sub_seed_memLp a b ha.le hab s hs
  have hfB : ∀q,‖f q‖≤eisensteinRemainderBound b s := by
    intro q
    induction q using Quotient.inductionOn with
    | _ w => exact eisenstein_sub_seed_bounded a b ha.le hab s hs w
  obtain ⟨G,hG,hgrad⟩ := kernelEisensteinRemainder_scaled_fderiv_bound a b ha hab s hs
  let A : KernelQuotient→ℂ := fun q => kernelQuotientDefect a b s q+
    kernelEisensteinSpectralParameter s*f q
  have hD := kernelQuotientDefect_memLp a b s (by linarith) hab
  have hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel) :=
    hD.add (hfL.const_smul (kernelEisensteinSpectralParameter s))
  have hEq : ∀p : EuclideanSpatial,0<p 2→
      positiveEuclideanLaplacian (kernelFunctionField f) p=A (kernelEuclideanProjection p) := by
    intro p hp
    exact kernelEisensteinRemainder_operator_equation a b ha hab s (by linarith) p hp
  have hgraph := kernel_bounded_smooth_operator_graph f hf hfL
    (eisensteinRemainderBound b s) G (eisensteinRemainderBound_nonneg b s) hG hfB hgrad A hA hEq
  have hAL : hA.toLp A=kernelL2Defect a b (by linarith) hab s+
      kernelEisensteinSpectralParameter s • kernelEisensteinRemainderL2 a b ha hab s hs := by
    exact (hD.toLp_add (hfL.const_smul (kernelEisensteinSpectralParameter s))).trans
      (congrArg (fun x => hD.toLp (kernelQuotientDefect a b s)+x)
        (hfL.toLp_const_smul (kernelEisensteinSpectralParameter s)))
  rw [hAL] at hgraph
  exact hgraph

theorem kernelEisensteinL2Correction_eq_remainder (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelEisensteinL2Correction a b (by linarith) hab s=
      kernelEisensteinRemainderL2 a b ha hab s hs := by
  exact kernelEisensteinL2Correction_unique a b (by linarith) hab s
    (kernelSpectralFormOperator_isUnit_nonreal _
      (kernelEisensteinSpectralParameter_nonreal s (by linarith) (by linarith)))
    _ (kernelEisensteinRemainderL2_graph a b ha hab s hs)

theorem kernelEisensteinL2Correction_initial_overlap (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelEisensteinL2Correction a b (by linarith) hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s (by linarith) q-kernelQuotientSeed a b s q := by
  rw [kernelEisensteinL2Correction_eq_remainder a b ha hab s hs hi]
  exact kernelEisensteinRemainderL2_ae a b ha hab s hs

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ScatteringCoefficients -/

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
open scoped BigOperators Classical Topology MatrixGroups

def cubicEisensteinResidue : KernelQuotientL2 :=
  kernelEisensteinResidueVector 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_nonzero_character :
    cubicEisensteinResidue≠0 ∧
      ∀M : CubicKubota.levelThree,kernelLevelPullback M cubicEisensteinResidue=
        CubicKubota.complexCharacter M • cubicEisensteinResidue := by
  apply kernelEisensteinResidueVector_nonzero_character_of_initial_overlap 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinResidue_ne_zero : cubicEisensteinResidue≠0 :=
  cubicEisensteinResidue_nonzero_character.1

lemma cubicEisensteinResidue_character (M : CubicKubota.levelThree) :
    kernelLevelPullback M cubicEisensteinResidue=
      CubicKubota.complexCharacter M • cubicEisensteinResidue :=
  cubicEisensteinResidue_nonzero_character.2 M

lemma cubicEisensteinResidue_eigenvector :
    (cubicEisensteinResidue,(8/9:ℂ) • cubicEisensteinResidue)∈kernelEnergyLaplacian.graph :=
  kernelEisensteinResidueVector_graph 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_limit :
    Tendsto (fun s : ℂ => (s-4/3) • kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 cubicEisensteinResidue) :=
  kernelEisensteinResidueVector_limit 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinResidue_cusp_average :
    kernelCuspStripAverage cubicEisensteinResidue=cuspConstantAverageResidue := by
  apply kernelEisensteinResidueVector_average_of_overlap 2 3 (by norm_num) (by norm_num)
  intro s hs hi
  apply kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num) s (by linarith)
  exact kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi

lemma cubicEisensteinCorrection_not_continuousAt :
    ¬ContinuousAt (kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num)) (4/3:ℂ) := by
  intro hc
  have hh := ((tendsto_id.sub_const (4/3:ℂ)).smul hc.tendsto).mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self,zero_smul] at hh
  exact cubicEisensteinResidue_ne_zero (tendsto_nhds_unique cubicEisensteinResidue_limit hh)

lemma cubicEisensteinResidue_local_limit (S : Set KernelQuotient) (hS : IsCompact S) :
    Tendsto (fun s : ℂ => (s-4/3) •
      kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet cubicEisensteinResidue)) :=
  kernelLocalCorrectedSeed_residue_limit S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_initial_ae (S : Set KernelQuotient) (hS : IsCompact S)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num) s : KernelQuotient→ℂ)
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        S.indicator (kernelQuotientEisenstein s (by linarith)) := by
  have hlocal := kernelLocalCorrectedSeed_ae_eq S hS 2 3 (by norm_num) (by norm_num) s
  have hoverlap := kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi
  filter_upwards [hlocal,hoverlap] with q hq hc
  rw [hq]
  by_cases hmem : q∈S
  · rw [Set.indicator_of_mem hmem,Set.indicator_of_mem hmem]
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hc]
    ring
  · rw [Set.indicator_of_notMem hmem,Set.indicator_of_notMem hmem]

lemma cubicEisensteinLocalFamily_meromorphicAt (S : Set KernelQuotient) (hS : IsCompact S) :
    MeromorphicAt (kernelLocalCorrectedSeed S hS 2 3 (by norm_num) (by norm_num)) (4/3:ℂ) :=
  kernelLocalCorrectedSeed_meromorphicAt S hS 2 3 (by norm_num) (by norm_num)

lemma cubicEisensteinLocalFamily_not_continuousAt :
    ¬ContinuousAt (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num)) (4/3:ℂ) := by
  have hnonzero : kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet cubicEisensteinResidue≠0 := by
    intro hz
    have hh := congrArg kernelCuspStripAverage hz
    rw [kernelCuspStripAverage_restrict,map_zero,cubicEisensteinResidue_cusp_average] at hh
    exact cuspConstantAverageResidue_ne_zero hh
  intro hc
  have hh := ((tendsto_id.sub_const (4/3:ℂ)).smul hc.tendsto).mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  simp only [sub_self,zero_smul] at hh
  exact hnonzero (tendsto_nhds_unique
    (cubicEisensteinResidue_local_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact) hh)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

def whittakerHeight (v : ℝ) : ℝ := max 5 v
def whittakerBase (p : ℝ × ℂ) : ℝ := whittakerHeight p.1*(1+‖p.2‖^2)
def whittakerIntegrand (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  (whittakerHeight p.1:ℂ)⁻¹*(whittakerBase p:ℂ)^(-s)*
    ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2)
def whittakerIntegrandDeriv (freq s : ℂ) (p : ℝ × ℂ) : ℂ :=
  -(Real.log (whittakerBase p):ℂ)*whittakerIntegrand freq s p
def whittakerProductVolume : Measure (ℝ × ℂ) :=
  (volume.restrict (Set.Icc (5:ℝ) 6)).prod volume

lemma whittakerHeight_ge_one (v : ℝ) : 1≤whittakerHeight v := by
  exact (by norm_num : (1:ℝ)≤5).trans (le_max_left _ _)

lemma whittakerBase_ge (p : ℝ × ℂ) : 1+‖p.2‖^2≤whittakerBase p := by
  exact le_mul_of_one_le_left (by positivity) (whittakerHeight_ge_one p.1)

lemma whittakerBase_ge_one (p : ℝ × ℂ) : 1≤whittakerBase p :=
  (by nlinarith [sq_nonneg ‖p.2‖] : 1≤1+‖p.2‖^2).trans (whittakerBase_ge p)

lemma whittakerBase_pos (p : ℝ × ℂ) : 0<whittakerBase p :=
  zero_lt_one.trans_le (whittakerBase_ge_one p)

lemma whittakerIntegrand_continuous (freq s : ℂ) : Continuous (whittakerIntegrand freq s) := by
  have hv : Continuous (fun p : ℝ × ℂ => whittakerHeight p.1) := by
    unfold whittakerHeight
    fun_prop
  have hb : Continuous whittakerBase := by unfold whittakerBase; fun_prop
  have hp : Continuous (fun p : ℝ × ℂ => (whittakerBase p:ℂ)^(-s)) :=
    (Complex.continuous_ofReal.comp hb).cpow continuous_const
      (fun p => Complex.ofReal_mem_slitPlane.mpr (whittakerBase_pos p))
  have hi : Continuous (fun p : ℝ × ℂ => (whittakerHeight p.1:ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp hv).inv₀ (fun p => by
      change (whittakerHeight p.1:ℂ)≠0
      exact_mod_cast (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).ne')
  have hc : Continuous (fun p : ℝ × ℂ =>
      ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2)) := by
    change Continuous (fun p : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-(freq*whittakerHeight p.1)*p.2)+starRingEnd ℂ (-(freq*whittakerHeight p.1)*p.2))))
    fun_prop
  exact (hi.mul hp).mul hc

lemma whittakerIntegrandDeriv_continuous (freq s : ℂ) : Continuous (whittakerIntegrandDeriv freq s) := by
  have hb : Continuous whittakerBase := by unfold whittakerBase whittakerHeight; fun_prop
  have hl : Continuous (fun p => Real.log (whittakerBase p)) :=
    hb.log (fun p => (whittakerBase_pos p).ne')
  exact (Complex.continuous_ofReal.comp hl).neg.mul (whittakerIntegrand_continuous freq s)

lemma whittakerIntegrand_hasDerivAt (freq s : ℂ) (p : ℝ × ℂ) :
    HasDerivAt (fun w => whittakerIntegrand freq w p) (whittakerIntegrandDeriv freq s p) s := by
  have hn : (whittakerBase p:ℂ)≠0 := by exact_mod_cast (whittakerBase_pos p).ne'
  have hh := (((hasDerivAt_id s).neg.const_cpow (Or.inl hn)).const_mul
    ((whittakerHeight p.1:ℂ)⁻¹)).mul_const
      (ShortDraftTrace.breveE (-(freq*whittakerHeight p.1)*p.2))
  convert hh using 1
  · rfl
  · rw [←Complex.ofReal_log (whittakerBase_pos p).le]
    unfold whittakerIntegrandDeriv whittakerIntegrand
    simp only [Pi.neg_apply,id_eq]
    ring

lemma whittakerIntegrand_norm (freq s : ℂ) (p : ℝ × ℂ) :
    ‖whittakerIntegrand freq s p‖=(whittakerHeight p.1)⁻¹*(whittakerBase p)^(-s.re) := by
  unfold whittakerIntegrand
  rw [norm_mul,norm_mul,breveE_norm,mul_one,norm_inv,
    Complex.norm_of_nonneg (zero_lt_one.trans_le (whittakerHeight_ge_one p.1)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos (whittakerBase_pos p)]
  rfl

lemma whittakerIntegrand_norm_bound (freq s : ℂ) (p : ℝ × ℂ)
    (b : ℝ) (hb : 0≤b) (hs : b≤ s.re) :
    ‖whittakerIntegrand freq s p‖≤(1+‖p.2‖^2)^(-b) := by
  rw [whittakerIntegrand_norm]
  calc
    _ ≤ (whittakerBase p)^(-s.re) := by
      exact mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
        (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))
    _ ≤ (whittakerBase p)^(-b) :=
      Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)
    _ ≤ (1+‖p.2‖^2)^(-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)

lemma whittakerIntegrandDeriv_norm_bound (freq s : ℂ) (p : ℝ × ℂ)
    (b ε : ℝ) (hb : 0≤b) (hε : 0<ε) (hs : b+ε≤ s.re) :
    ‖whittakerIntegrandDeriv freq s p‖≤ε⁻¹*(1+‖p.2‖^2)^(-b) := by
  have hlog := Real.log_nonneg (whittakerBase_ge_one p)
  unfold whittakerIntegrandDeriv
  rw [norm_mul,norm_neg,Complex.norm_of_nonneg hlog,whittakerIntegrand_norm]
  calc
    _ ≤ Real.log (whittakerBase p)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (Real.rpow_nonneg (whittakerBase_pos p).le _)
          (inv_le_one_of_one_le₀ (whittakerHeight_ge_one p.1))) hlog
    _ ≤ ((whittakerBase p)^ε/ε)*(whittakerBase p)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (Real.log_le_rpow_div (whittakerBase_pos p).le hε)
        (Real.rpow_nonneg (whittakerBase_pos p).le _)
    _ = ε⁻¹*(whittakerBase p)^(ε-s.re) := by
      rw [Real.rpow_sub (whittakerBase_pos p),Real.rpow_neg (whittakerBase_pos p).le]
      ring
    _ ≤ ε⁻¹*(whittakerBase p)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (whittakerBase_ge_one p) (by linarith)) (by positivity)
    _ ≤ ε⁻¹*(1+‖p.2‖^2)^(-b) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (whittakerBase_ge p) (by linarith)) (by positivity)

lemma whittaker_bound_integrable (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) whittakerProductVolume := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Set.Icc (5:ℝ) 6)) := integrable_const _
  unfold whittakerProductVolume
  simpa only [one_mul] using hv.mul_prod hk

lemma whittakerIntegrand_integrable (freq s : ℂ) (hs : 1<s.re) :
    Integrable (whittakerIntegrand freq s) whittakerProductVolume := by
  exact (whittaker_bound_integrable s.re hs).mono'
    (whittakerIntegrand_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p => whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl))

lemma whittakerProduct_differentiableAt (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ (fun w => ∫p,whittakerIntegrand freq w p∂whittakerProductVolume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume) (F := whittakerIntegrand freq)
    (F' := whittakerIntegrandDeriv freq)
    (bound := fun p => ε⁻¹*(1+‖p.2‖^2)^(-b)) hU
    (Eventually.of_forall (fun w => (whittakerIntegrand_continuous freq w).aestronglyMeasurable))
    (whittakerIntegrand_integrable freq s hs)
    (whittakerIntegrandDeriv_continuous freq s).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le))
    ((whittaker_bound_integrable b hb).const_mul ε⁻¹)
    (Eventually.of_forall (fun p w _ => whittakerIntegrand_hasDerivAt freq w p))
  exact h.2.differentiableAt

lemma whittakerIntegrand_eq (freq s : ℂ) (v : ℝ) (hv : 5≤v) (z : ℂ) :
    whittakerIntegrand freq s (v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hvp : 0<v := by linarith
  have hvn : (v:ℂ)≠0 := by exact_mod_cast hvp.ne'
  have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(-s)*(v:ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hvn,Complex.cpow_one,div_eq_mul_inv]
  unfold whittakerIntegrand whittakerBase whittakerHeight hyperbolicKernel
  simp only [max_eq_right hv,Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hvp.le (by positivity),hp]
  ring

lemma whittakerProduct_eq_average (freq s : ℂ) (hs : 1<s.re) :
    (∫p,whittakerIntegrand freq s p∂whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := whittakerIntegrand_integrable freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => whittakerIntegrand_eq freq s v hv.1 z)
    _ = _ := integral_const_mul _ _

theorem cuspWhittakerAverage_differentiableAt (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p,whittakerIntegrand freq w p∂whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (whittakerProduct_eq_average freq w hw).symm
  exact (whittakerProduct_differentiableAt freq s hs).congr_of_eventuallyEq he

end

section
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT

lemma arithmeticDirichletTerm_differentiable (h : ActualEisensteinCubic.O) (c : LevelLower) :
    Differentiable ℂ (fun s : ℂ => arithmeticDirichletTerm s h c) := by
  by_cases hc : c.1=0
  · simp only [arithmeticDirichletTerm,ite_eq_left hc]
    exact differentiable_const _
  · have hq : ((‖eisEmbedding c.1‖^2:ℝ):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)))
    simp only [arithmeticDirichletTerm,ite_eq_right hc]
    exact (differentiable_id.neg.const_cpow (Or.inl hq)).mul_const _

lemma arithmeticDirichletTerm_norm_mono (h : ActualEisensteinCubic.O)
    (a : ℝ) (s : ℂ) (ha : a≤ s.re) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖≤‖arithmeticDirichletTerm (a:ℂ) h c‖ := by
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

theorem arithmeticDirichletSeries_differentiableAt (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => arithmeticDirichletSeries z h) s := by
  let a : ℝ := (2+s.re)/2
  have ha : 2<a := by dsimp [a]; linarith
  have has : a<s.re := by dsimp [a]; linarith
  have hsum := arithmeticDirichletTerm_summable_norm (a:ℂ) (by simpa using ha) h
  have hopen : IsOpen {z : ℂ | a<z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun z => arithmeticDirichletSeries z h) {z : ℂ | a<z.re} := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun c => (arithmeticDirichletTerm_differentiable h c).differentiableOn) hopen
    intro c z hz
    exact arithmeticDirichletTerm_norm_mono h a z hz.le c
  exact (hd s has).differentiableAt (hopen.mem_nhds has)

theorem scatteringCoefficient_differentiableAt (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 2<s.re) :
    DifferentiableAt ℂ (fun z => scatteringCoefficient z h) s :=
  (arithmeticDirichletSeries_differentiableAt h s hs).div_const _

theorem scatteringCoefficient_analyticOnNhd (h : ActualEisensteinCubic.O) :
    AnalyticOnNhd ℂ (fun z => scatteringCoefficient z h) {z : ℂ | 2<z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (scatteringCoefficient_differentiableAt h z hz).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal

local notation "O" => ActualEisensteinCubic.O

lemma cuspPeriodStrip_measure_ne_top : hyperbolicVolume (cuspPeriodStrip 5 6)≠(⊤:ℝ≥0∞) := by
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := hm.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simp only [Set.preimage_univ,Measure.restrict_apply_univ] at hh
  rw [hh]
  exact measure_ne_top _ _

instance cuspStripFiniteVolume : IsFiniteMeasure (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) :=
  isFiniteMeasure_restrict.mpr cuspPeriodStrip_measure_ne_top

abbrev CuspStripL2 := Lp ℂ 2 (hyperbolicVolume.restrict (cuspPeriodStrip 5 6))

def kernelCuspPullback : KernelQuotientL2→L[ℂ]CuspStripL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    (kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num))).toContinuousLinearMap.comp
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet)

lemma kernelCuspPullback_ae_eq (F : KernelQuotientL2) :
    kernelCuspPullback F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip 5 6)]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hr := LpToLpRestrictCLM_coeFn ℂ kernelCuspStripSet F
  have hc := hm.quasiMeasurePreserving.ae_eq_comp hr
  have hp := Lp.coeFn_compMeasurePreserving
    (LpToLpRestrictCLM KernelQuotient ℂ ℂ (integralQuotientVolume globalKubotaKernel) 2 kernelCuspStripSet F) hm
  filter_upwards [hp,hc] with w hw hc
  exact hw.trans hc

def cuspFourierPhase (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ℂ :=
  ShortDraftTrace.breveE (-cuspFrequency h*hyperbolicHorizontal w)

lemma cuspFourierPhase_continuous (h : ActualEisensteinCubic.O) : Continuous (cuspFourierPhase h) := by
  have hc : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency h*z)+starRingEnd ℂ (-cuspFrequency h*z))))
    fun_prop
  exact hc.comp hyperbolicHorizontal_continuous

lemma cuspFourierPhase_norm (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ‖cuspFourierPhase h w‖=1 :=
  breveE_norm _

lemma cuspFourierTest_memLp (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspFourierPhase h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspFourierPhase_continuous h).star.aestronglyMeasurable 1
  exact Eventually.of_forall (fun w => by rw [norm_star,cuspFourierPhase_norm])

def cuspFourierTestL2 (h : ActualEisensteinCubic.O) : CuspStripL2 :=
  (cuspFourierTest_memLp h).toLp (fun w => star (cuspFourierPhase h w))

def kernelCuspFourier (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspFourierTestL2 h)).comp kernelCuspPullback

lemma kernelCuspFourier_integral (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspFourier h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspFourierPhase h w∂hyperbolicVolume := by
  change inner ℂ (cuspFourierTestL2 h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspFourierTest_memLp h),kernelCuspPullback_ae_eq F] with w hw hp
  rw [RCLike.inner_apply,cuspFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspFourier_restrict (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspFourier h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspFourier h F := by
  rw [kernelCuspFourier_integral,kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

def kernelCuspFourierFamily (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspFourier h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspFourierFamily_meromorphicAt (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelCuspFourierFamily h a b ha hab) (4/3:ℂ) :=
  meromorphicAt_clm (kernelCuspFourier h)
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)

lemma kernelCuspFourierFamily_residue_limit (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspFourierFamily h a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := (kernelCuspFourier h).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspFourier_restrict,kernelCuspFourierFamily] using hh

lemma kernelCuspFourierFamily_actual_integral (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)*
        cuspFourierPhase h w∂hyperbolicVolume := by
  rw [kernelCuspFourierFamily,kernelCuspFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

lemma kernelCuspFourierFamily_of_initial_overlap (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s hs := by
    filter_upwards [hoverlap] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hcorrected (s := kernelCuspStripSet))
  rw [kernelCuspFourierFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [hp] with w hw
  exact congrArg (fun z : ℂ => z*cuspFourierPhase h w)
    (hw.trans (kernelQuotientEisenstein_mk s hs w))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "O" => ActualEisensteinCubic.O

lemma hyperbolicEisenstein_cusp_fourier_average (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((if h=0 then (v:ℂ)^s else 0)+
          (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspFourierPhase h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
      cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    rw [eisensteinFourierCoefficient]
    exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
  dsimp only
  rw [hh,eisensteinFourierCoefficient_formula v hpos s hs h]

def cuspWhittakerHeightFactor (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)

lemma hyperbolicEisenstein_cusp_fourier_nonzero (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspFourierPhase h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [hyperbolicEisenstein_cusp_fourier_average s hs h]
  simp only [ite_eq_right hh,zero_add]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h)*
        ((9*Real.sqrt 3/2:ℝ):ℂ)/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma cuspWhittakerHeightFactor_bessel (s : ℂ) (hs : 1<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspWhittakerHeightFactor s h=
      ∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1)*
        ((2*Real.pi:ℂ)/Complex.Gamma s*
          (2*Real.pi*‖cuspFrequency h*v‖:ℂ)^(s-1)*
          schlafliBesselK (s-1) (4*Real.pi*‖cuspFrequency h*v‖)) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  dsimp only
  rw [sourceFourierKernel_bessel s _ hs
    (mul_ne_zero (cuspFrequency_ne_zero h hh) (Complex.ofReal_ne_zero.mpr hpos.ne'))]

def kernelResidualFourierDatum (h : ActualEisensteinCubic.O) (a b : ℝ) (ha : 0<a) (hab : a<b) : ℂ :=
  kernelCuspFourier h (kernelEisensteinResidueVector a b ha hab)

lemma kernelCuspFourierFamily_nonzero_of_initial_overlap (h : ActualEisensteinCubic.O) (hh : h≠0)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : 2<s.re)
    (hoverlap : kernelEisensteinL2Correction a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) :
    kernelCuspFourierFamily h a b ha hab s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h := by
  rw [kernelCuspFourierFamily_of_initial_overlap h a b ha hab s hs hoverlap,
    hyperbolicEisenstein_cusp_fourier_nonzero s hs h hh]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma sourceFourierKernel_continuous_freq (s : ℂ) (hs : 1<s.re) :
    Continuous (sourceFourierKernel s) := by
  change Continuous (fun freq : ℂ => ∫z : ℂ,hyperbolicKernel s z*ShortDraftTrace.breveE (-freq*z))
  apply continuous_of_dominated (bound := fun z => ‖hyperbolicKernel s z‖)
  · exact fun freq => (sourceFourierKernel_integrable s freq hs).aestronglyMeasurable
  · exact fun freq => Eventually.of_forall (fun z => by rw [norm_mul,breveE_norm,mul_one])
  · exact (hyperbolicKernel_integrable s hs).norm
  · filter_upwards with z
    change Continuous (fun freq : ℂ => hyperbolicKernel s z*
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop

lemma schlafliIntegrand_real (nu x t : ℝ) (ht : 0<t) :
    (t:ℂ)^((nu:ℂ)-1)*Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))=
      ((t^(nu-1)*Real.exp (-t-x^2/(4*t)):ℝ):ℂ) := by
  have hp := Complex.ofReal_cpow ht.le (nu-1)
  simp only [Complex.ofReal_sub,Complex.ofReal_one] at hp
  rw [Complex.ofReal_mul,hp,Complex.ofReal_exp]
  congr 2
  push_cast
  rfl

lemma schlafliIntegral_real_re_pos (nu x : ℝ) (hnu : 0<nu) :
    0<(schlafliIntegral (nu:ℂ) x).re := by
  let f : ℝ→ℂ := fun t => (t:ℂ)^((nu:ℂ)-1)*Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t))
  have hi : IntegrableOn f (Set.Ioi (0:ℝ)) volume := schlafliIntegral_integrable (nu:ℂ) x hnu
  have hp (t : ℝ) (ht : 0<t) : 0<(f t).re := by
    rw [show f t=((t^(nu-1)*Real.exp (-t-x^2/(4*t)):ℝ):ℂ) from schlafliIntegrand_real nu x t ht,
      Complex.ofReal_re]
    exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  change 0<RCLike.re (∫t in Set.Ioi (0:ℝ),f t)
  rw [←integral_re hi]
  apply (integral_pos_iff_support_of_nonneg_ae ?_ hi.re).mpr
  · have heq : Function.support (fun t => RCLike.re (f t))=ᵐ[volume.restrict (Set.Ioi (0:ℝ))] Set.univ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply propext
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact (hp t ht).ne'
    rw [measure_congr heq,Measure.restrict_apply_univ]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hp t ht).le

lemma sourceFourierKernel_real_re_pos (sigma : ℝ) (hsigma : 1<sigma) (freq : ℂ) :
    0<(sourceFourierKernel (sigma:ℂ) freq).re := by
  have hh := sourceFourierKernel_gamma_schlafli (sigma:ℂ) freq hsigma
  have hre := congrArg Complex.re hh
  have hsch : 0<(schlafliIntegral ((sigma:ℂ)-1) (4*Real.pi*‖freq‖)).re := by
    convert schlafliIntegral_real_re_pos (sigma-1) (4*Real.pi*‖freq‖) (by linarith) using 1 ; push_cast ; rfl
  rw [Complex.Gamma_ofReal] at hre
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] at hre
  have hg := Real.Gamma_pos_of_pos (show 0<sigma by linarith)
  have hp := mul_pos Real.pi_pos hsch
  nlinarith

lemma cuspWhittakerHeightFactor_integrable (s : ℂ) (hs : 1<s.re) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))
      (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  exact ((Complex.continuousAt_ofReal_cpow_const v (-s-1) (Or.inr hpos.ne')).mul
    ((sourceFourierKernel_continuous_freq s hs).continuousAt.comp
      ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt

lemma cuspWhittakerHeightFactor_real_re_pos (sigma : ℝ) (hsigma : 1<sigma) (h : ActualEisensteinCubic.O) :
    0<(cuspWhittakerHeightFactor (sigma:ℂ) h).re := by
  let f : ℝ→ℂ := fun v => (v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)
  have hi : IntegrableOn f (Set.Icc (5:ℝ) 6) volume :=
    cuspWhittakerHeightFactor_integrable (sigma:ℂ) hsigma h
  have hp (v : ℝ) (hv : v∈Set.Icc (5:ℝ) 6) : 0<(f v).re := by
    have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
    have he := Complex.ofReal_cpow hpos.le (-sigma-1)
    simp only [Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_one] at he
    change 0<((v:ℂ)^(-(sigma:ℂ)-1)*sourceFourierKernel (sigma:ℂ) (cuspFrequency h*v)).re
    rw [←he,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_pos (Real.rpow_pos_of_pos hpos _) (sourceFourierKernel_real_re_pos sigma hsigma _)
  change 0<RCLike.re (∫v in Set.Icc (5:ℝ) 6,f v)
  rw [←integral_re hi]
  apply (integral_pos_iff_support_of_nonneg_ae ?_ hi.re).mpr
  · have heq : Function.support (fun v => RCLike.re (f v))=ᵐ[volume.restrict (Set.Icc (5:ℝ) 6)] Set.univ := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      apply propext
      simp only [Function.mem_support,Set.mem_univ,iff_true]
      exact (hp v hv).ne'
    rw [measure_congr heq,Measure.restrict_apply_univ]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (hp v hv).le

lemma cuspWhittakerHeightFactor_center_ne_zero (h : ActualEisensteinCubic.O) :
    cuspWhittakerHeightFactor (4/3:ℂ) h≠0 := by
  intro he
  have hh := cuspWhittakerHeightFactor_real_re_pos (4/3:ℝ) (by norm_num) h
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hh
  rw [he,Complex.zero_re] at hh
  exact lt_irrefl 0 hh

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.WhittakerContinuation -/

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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspWhittakerHeightFactor_analyticAt (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspWhittakerHeightFactor w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact cuspWhittakerAverage_differentiableAt (cuspFrequency h) w hw

lemma kernelCuspFourierFamily_analyticAt_nonreal (h : ActualEisensteinCubic.O) (a b : ℝ)
    (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspFourierFamily h a b ha hab) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspFourier h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact a b ha hab s hs hi) rfl

def continuedNonzeroScattering (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)

def nonzeroScatteringResidue (h : ActualEisensteinCubic.O) : ℂ :=
  kernelCuspFourier h cubicEisensteinResidue /
    (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)

lemma continuedNonzeroScattering_meromorphicAt_center (h : ActualEisensteinCubic.O) :
    MeromorphicAt (continuedNonzeroScattering h) (4/3:ℂ) := by
  exact (kernelCuspFourierFamily_meromorphicAt h 2 3 (by norm_num) (by norm_num)).div
    ((analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num))).meromorphicAt)

lemma continuedNonzeroScattering_meromorphicOn_upper (h : ActualEisensteinCubic.O) :
    MeromorphicOn (continuedNonzeroScattering h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  intro s hs
  exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
    s (ne_of_gt hs.1) (ne_of_gt hs.2)).meromorphicAt.div
    ((analyticAt_const.mul (cuspWhittakerHeightFactor_analyticAt h s hs.1)).meromorphicAt)

lemma continuedNonzeroScattering_residue_limit (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*continuedNonzeroScattering h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (nonzeroScatteringResidue h)) := by
  have hden : Tendsto (fun s : ℂ => ((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3:ℂ) h)) := (continuousAt_const.mul
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt).tendsto.mono_left
      (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hlimit := (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).div hden
    (mul_ne_zero cusp_volume_ne_zero (cuspWhittakerHeightFactor_center_ne_zero h))
  change Tendsto (fun s : ℂ =>
      ((s-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s)/
        (((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor s h))
      (𝓝[≠] (4/3:ℂ)) (𝓝 (nonzeroScatteringResidue h)) at hlimit
  convert hlimit using 1
  funext s
  exact (mul_div_assoc _ _ _).symm

lemma continuedNonzeroScattering_initial (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ)
    (hs : 4<s.re) (hi : 0<s.im) (hH : cuspWhittakerHeightFactor s h≠0) :
    continuedNonzeroScattering h s=scatteringCoefficient s h := by
  unfold continuedNonzeroScattering
  rw [kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
    (by norm_num) (by norm_num) s (by linarith)
    (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi)]
  field_simp [cusp_volume_ne_zero,hH]

lemma cuspWhittakerHeightFactor_ne_zero_near_five (h : ActualEisensteinCubic.O) :
    ∀ᶠ s : ℂ in 𝓝 (5:ℂ),4<s.re ∧ cuspWhittakerHeightFactor s h≠0 := by
  have hpos := cuspWhittakerHeightFactor_real_re_pos 5 (by norm_num) h
  have hH : cuspWhittakerHeightFactor (5:ℂ) h≠0 := by
    intro he
    norm_num only [Complex.ofReal_ofNat] at hpos
    rw [he,Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hre : ∀ᶠ s : ℂ in 𝓝 (5:ℂ),4<s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact hre.and ((cuspWhittakerHeightFactor_analyticAt h 5 (by norm_num)).continuousAt.eventually_ne hH)

lemma kernelCuspFourierFamily_eq_upper (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h)
      {s : ℂ | 2<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 2<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (2:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)) domain := by
    intro s hs
    exact kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s (by linarith [hs.1]) hs.2.ne'
  have hright : AnalyticOnNhd ℂ
      (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (analyticAt_const.mul (scatteringCoefficient_analyticOnNhd h s hs.1)).mul
      (cuspWhittakerHeightFactor_analyticAt h s (by linarith [hs.1]))
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3
      (by norm_num) (by norm_num) s (by linarith [hs.1])
      (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

lemma continuedNonzeroScattering_eq_upper (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ)
    (hs : 2<s.re) (hi : 0<s.im) (hH : cuspWhittakerHeightFactor s h≠0) :
    continuedNonzeroScattering h s=scatteringCoefficient s h := by
  unfold continuedNonzeroScattering
  rw [kernelCuspFourierFamily_eq_upper h hh ⟨hs,hi⟩]
  field_simp [cusp_volume_ne_zero,hH]

lemma continuedNonzeroScattering_initial_open (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ∃U : Set ℂ,IsOpen U ∧ U.Nonempty ∧ U⊆{s : ℂ | 4<s.re ∧ 0<s.im} ∧
      Set.EqOn (continuedNonzeroScattering h) (fun s => scatteringCoefficient s h) U := by
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp (cuspWhittakerHeightFactor_ne_zero_near_five h)
  let z : ℂ := 5+(ε/2:ℝ)*Complex.I
  have hz : dist z (5:ℂ)<ε := by
    have hdist : dist z (5:ℂ)=ε/2 := by
      simp [z,dist_eq_norm,hε.le]
    rw [hdist]
    linarith
  have hzim : 0<z.im := by simpa [z] using half_pos hε
  refine ⟨Metric.ball (5:ℂ) ε ∩ {s : ℂ | 0<s.im},
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im),⟨z,hz,hzim⟩,?_,?_⟩
  · intro s hs
    exact ⟨(hball hs.1).1,hs.2⟩
  · intro s hs
    exact continuedNonzeroScattering_initial h hh s (hball hs.1).1 hs.2 (hball hs.1).2

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma weightedWhittakerIntegrand_integrable (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s p) whittakerProductVolume := by
  apply ((whittaker_bound_integrable s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrand_continuous freq s)).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl) (norm_nonneg _) (norm_nonneg _))

lemma weightedWhittakerProduct_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w p∂whittakerProductVolume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w p)
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w p)
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrand_continuous freq w)).aestronglyMeasurable))
    (weightedWhittakerIntegrand_integrable ρ freq s hs)
    ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrandDeriv_continuous freq s)).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ => (whittakerIntegrand_hasDerivAt freq w p).const_mul (ρ p.1)))
  exact h.2.differentiableAt

lemma weightedWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq s p∂whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := weightedWhittakerIntegrand_integrable ρ freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        rw [whittakerIntegrand_eq freq s v hv.1 z]
        ring)
    _ = _ := integral_const_mul _ _

theorem cuspWeightedWhittakerAverage_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w p∂whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (weightedWhittakerProduct_eq_average ρ freq w hw).symm
  exact (weightedWhittakerProduct_differentiableAt ρ freq s hs).congr_of_eventuallyEq he

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

theorem kernelCompact_projection_measure_bound (K : Set HyperbolicSpace) (hK : IsCompact K) :
    ∃N : ℕ,Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (N:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel := by
  choose e he heq using kernelQuotient_localHomeomorph
  have hcover : K⊆⋃w : HyperbolicSpace,(e w).source := by
    intro w _
    exact Set.mem_iUnion.mpr ⟨w,he w⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun w => (e w).source) (fun w => (e w).open_source) hcover
  have hinj (w : HyperbolicSpace) :
      Set.InjOn (integralOrbitProjection globalKubotaKernel) (e w).source := by
    rw [heq w]
    exact (e w).injOn
  refine ⟨t.card,Measure.le_iff.mpr ?_⟩
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.smul_apply]
  change hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ K)≤
    (t.card:ℝ≥0∞)*integralQuotientVolume globalKubotaKernel B
  calc
    _ ≤ hyperbolicVolume (⋃w∈t,(integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) := by
      apply measure_mono
      rintro w ⟨hw,hK⟩
      obtain ⟨v,hv,hwv⟩ := Set.mem_iUnion₂.mp (ht hK)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,hw,hwv⟩
    _ ≤ ∑w∈t,hyperbolicVolume ((integralOrbitProjection globalKubotaKernel) ⁻¹' B ∩ (e w).source) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑_w∈t,integralQuotientVolume globalKubotaKernel B := by
      apply Finset.sum_le_sum
      intro w hw
      have hm := kernelProjection_measurePreserving_on (e w).source (e w).open_source.measurableSet (hinj w)
      rw [←Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),
        ←Measure.map_apply (measurable_integralOrbitProjection _) hB,hm.map_eq]
      exact Measure.restrict_le_self B
    _ = _ := by simp [nsmul_eq_mul]

section DominatedComplexL2
variable {α : Type*} [MeasurableSpace α] {«μ» ν : Measure α} {c : ℝ≥0∞}

def dominatedComplexL2 (hc : c≠⊤) (h : ν≤ c•«μ») : Lp ℂ 2 «μ»→L[ℂ]Lp ℂ 2 ν where
  toFun := Lp.LpToLpOfMeasureLeSMul hc h
  map_add' := map_add (Lp.LpToLpOfMeasureLeSMul hc h)
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hc h (z•f),
      Lp.coeFn_LpToLpOfMeasureLeSMul hc h f,
      Lp.coeFn_smul z (Lp.LpToLpOfMeasureLeSMul hc h f),
      (Measure.absolutelyContinuous_of_le_smul h).ae_eq (Lp.coeFn_smul z f)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,Pi.smul_apply] at *
    rw [h1,h3,h2,h4]
  cont := (Lp.LpToLpOfMeasureLeSMul hc h).continuous

lemma dominatedComplexL2_ae (hc : c≠⊤) (h : ν≤ c•«μ») (f : Lp ℂ 2 «μ») :
    dominatedComplexL2 hc h f=ᵐ[ν]f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hc h f

lemma dominatedComplexL2_norm_le (hc : c≠⊤) (h : ν≤ c•«μ») (f : Lp ℂ 2 «μ») :
    ‖dominatedComplexL2 hc h f‖≤ c.toReal^((1:ℝ)/2)*‖f‖ := by
  have hb := (Lp.LpToLpOfMeasureLeSMul hc h : Lp ℂ 2 «μ»→L[ℝ]Lp ℂ 2 ν).le_opNorm f
  have hn := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) hc h
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] using hn

end DominatedComplexL2

def kernelCompactMultiplicity (K : Set HyperbolicSpace) (hK : IsCompact K) : ℕ :=
  (kernelCompact_projection_measure_bound K hK).choose

lemma kernelCompactMultiplicity_spec (K : Set HyperbolicSpace) (hK : IsCompact K) :
    Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)≤
      (kernelCompactMultiplicity K hK:ℝ≥0∞) • integralQuotientVolume globalKubotaKernel :=
  (kernelCompact_projection_measure_bound K hK).choose_spec

def kernelCompactPullbackCLM (K : Set HyperbolicSpace) (hK : IsCompact K) :
    KernelQuotientL2→L[ℂ]Lp ℂ 2 (hyperbolicVolume.restrict K) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    ⟨measurable_integralOrbitProjection _,rfl⟩).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤)
        (kernelCompactMultiplicity_spec K hK))

theorem kernelCompactPullbackCLM_ae (K : Set HyperbolicSpace) (hK : IsCompact K)
    (F : KernelQuotientL2) :
    kernelCompactPullbackCLM K hK F=ᵐ[hyperbolicVolume.restrict K]
      fun w => F (integralOrbitProjection globalKubotaKernel w) := by
  have hm : MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict K)
      (Measure.map (integralOrbitProjection globalKubotaKernel) (hyperbolicVolume.restrict K)) :=
    ⟨measurable_integralOrbitProjection _,rfl⟩
  have he := dominatedComplexL2_ae
    (by simp : (kernelCompactMultiplicity K hK:ℝ≥0∞)≠⊤) (kernelCompactMultiplicity_spec K hK) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans (hm.quasiMeasurePreserving.ae_eq_comp he)

lemma whittaker_bound_integrable_finite («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) («μ».prod volume) := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) «μ» := integrable_const _
  simpa only [one_mul] using hv.mul_prod hk

lemma scaledWhittakerIntegrand_integrable («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s (c*p.1,p.2)) («μ».prod volume) := by
  apply ((whittaker_bound_integrable_finite «μ» s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrand_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s (c*p.1,p.2) s.re (by linarith) le_rfl)
        (norm_nonneg _) (norm_nonneg _))

lemma scaledWhittakerProduct_differentiableAt («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w (c*p.1,p.2)∂«μ».prod volume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := «μ».prod volume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w (c*p.1,p.2))
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w (c*p.1,p.2))
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul
        ((whittakerIntegrand_continuous freq w).comp (by fun_prop))).aestronglyMeasurable))
    (scaledWhittakerIntegrand_integrable «μ» ρ c freq s hs)
    ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrandDeriv_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w (c*p.1,p.2) b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable_finite «μ» b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ =>
      (whittakerIntegrand_hasDerivAt freq w (c*p.1,p.2)).const_mul (ρ p.1)))
  exact h.2.differentiableAt

lemma whittakerIntegrand_scale (c v : ℝ) (hc : 0<c) (hv : 0<v) (hcv : 5≤ c*v)
    (freq s : ℂ) (z : ℂ) :
    (c:ℂ)^(s+1)*whittakerIntegrand (freq/c) s (c*v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
  have hcn : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  rw [whittakerIntegrand_eq (freq/c) s (c*v) hcv z,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le hv.le]
  have he : -(freq/(c:ℂ)*((c:ℂ)*v))*z=-(freq*v)*z := by field_simp
  rw [he]
  have hp : (c:ℂ)^(s+1)*(c:ℂ)^(-s-1)=1 := by
    rw [←Complex.cpow_add _ _ hcn,show s+1+(-s-1)=0 by ring,Complex.cpow_zero]
  calc
    _ = ((c:ℂ)^(s+1)*(c:ℂ)^(-s-1))*
      ((v:ℂ)^(-s-1)*(hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z))) := by ring
    _ = _ := by rw [hp,one_mul]

lemma scaledWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    ((5/a:ℝ):ℂ)^(s+1)*
      (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*p.1,p.2)
        ∂(volume.restrict (Set.Icc a b)).prod volume)=
      ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := scaledWhittakerIntegrand_integrable (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs
  rw [integral_prod _ hi,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hvp : 0<v := ha.trans_le hv.1
  have hcv : 5≤(5/a)*v := by
    calc
      5=(5/a)*a := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 (by positivity)
  rw [←integral_const_mul]
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*
        (hyperbolicKernel s z*ShortDraftTrace.breveE (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        calc
          _ = ρ v*(((5/a:ℝ):ℂ)^(s+1)*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*v,z)) := by ring
          _ = _ := by rw [whittakerIntegrand_scale (5/a) v (by positivity) hvp hcv freq s z]; ring)
    _ = _ := integral_const_mul _ _

theorem cuspWeightedWhittakerInterval_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have hc : ((5/a:ℝ):ℂ)≠0 := by exact_mod_cast (show (5/a:ℝ)≠0 by positivity)
  have hd := ((differentiableAt_id.add_const (1:ℂ)).const_cpow (Or.inl hc)).mul
    (scaledWhittakerProduct_differentiableAt (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact (scaledWhittakerProduct_eq_average ρ a b ha freq w hw).symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cuspWeightedFourierPhase (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*cuspFourierPhase h w

lemma cuspWeightedFourierPhase_continuous (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Continuous (cuspWeightedFourierPhase ρ h) :=
  (ρ.continuous.comp hyperbolicHeight_continuous).mul (cuspFourierPhase_continuous h)

lemma cuspWeightedFourierPhase_bound (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (w : HyperbolicSpace) :
    ‖cuspWeightedFourierPhase ρ h w‖≤‖ρ‖ := by
  rw [cuspWeightedFourierPhase,norm_mul,cuspFourierPhase_norm,mul_one]
  exact ρ.norm_coe_le_norm _

lemma cuspWeightedFourierTest_memLp (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspWeightedFourierPhase ρ h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip 5 6)) := by
  apply MemLp.of_bound (cuspWeightedFourierPhase_continuous ρ h).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star]; exact cuspWeightedFourierPhase_bound ρ h w)

def cuspWeightedFourierTestL2 (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : CuspStripL2 :=
  (cuspWeightedFourierTest_memLp ρ h).toLp (fun w => star (cuspWeightedFourierPhase ρ h w))

def kernelCuspWeightedFourier (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspWeightedFourierTestL2 ρ h)).comp kernelCuspPullback

lemma kernelCuspWeightedFourier_integral (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspWeightedFourier ρ h F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  change inner ℂ (cuspWeightedFourierTestL2 ρ h) (kernelCuspPullback F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspWeightedFourierTest_memLp ρ h),kernelCuspPullback_ae_eq F] with w hw hp
  rw [RCLike.inner_apply,cuspWeightedFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspWeightedFourier_restrict (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspWeightedFourier ρ h (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspWeightedFourier ρ h F := by
  rw [kernelCuspWeightedFourier_integral,kernelCuspWeightedFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelMassRestriction_coe kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet F)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _))

def kernelCuspWeightedFourierFamily (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspWeightedFourier ρ h
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num) s)

lemma kernelCuspWeightedFourierFamily_meromorphicAt (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MeromorphicAt (kernelCuspWeightedFourierFamily ρ h) (4/3:ℂ) :=
  meromorphicAt_clm (kernelCuspWeightedFourier ρ h)
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact
      2 3 (by norm_num) (by norm_num))

lemma kernelCuspWeightedFourierFamily_analyticAt_nonreal (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspWeightedFourierFamily ρ h) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspWeightedFourier ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal kernelCuspAverageCompact
        kernelCuspAverageCompact_isCompact 2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma kernelCuspWeightedFourierFamily_residue_limit (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspWeightedFourierFamily ρ h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspWeightedFourier ρ h cubicEisensteinResidue)) := by
  have hh := (kernelCuspWeightedFourier ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspWeightedFourier_restrict,
    kernelCuspWeightedFourierFamily] using hh

lemma kernelCuspWeightedFourierFamily_initial (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspWeightedFourierFamily ρ h s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [kernelCuspWeightedFourierFamily,kernelCuspWeightedFourier_integral]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (cubicEisensteinLocalFamily_initial_ae kernelCuspAverageCompact kernelCuspAverageCompact_isCompact s hs hi)
    (s := kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩),
    kernelQuotientEisenstein_mk]

def cuspWeightedWhittakerHeightFactor (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc (5:ℝ) 6,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))

lemma hyperbolicEisenstein_cusp_weighted_fourier_nonzero (ρ : BoundedContinuousFunction ℝ ℂ)
    (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWeightedWhittakerHeightFactor ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  have hexp : ∀v∈Set.Icc (5:ℝ) 6,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) := by
    intro v hv
    have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinFourierCoefficient_formula v hpos s hs h,ite_eq_right hh,zero_add]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp]
    ring
  calc
    _ = ∫v in Set.Icc (5:ℝ) 6,(((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
        (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) :=
      setIntegral_congr_fun measurableSet_Icc hexp
    _ = _ := integral_const_mul _ _

lemma kernelCuspWeightedFourierFamily_initial_factor (ρ : BoundedContinuousFunction ℝ ℂ)
    (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspWeightedFourierFamily ρ h s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspWeightedWhittakerHeightFactor ρ s h := by
  rw [kernelCuspWeightedFourierFamily_initial ρ h s hs hi,
    hyperbolicEisenstein_cusp_weighted_fourier_nonzero ρ s (by linarith) h hh]

end CubicEisenstein

end

end OAI

end

