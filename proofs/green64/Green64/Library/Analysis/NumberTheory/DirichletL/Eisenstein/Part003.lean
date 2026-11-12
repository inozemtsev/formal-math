module

public import Green64.Library.Analysis.NumberTheory.DirichletL.QuadraticSieve.Part007

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicVolume -/

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
open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal Matrix

lemma linear_preserves_hyperbolicVolume (A : EuclideanSpatial →L[ℝ] EuclideanSpatial)
    (k : ℝ) (hk : 0<k) (hh : ∀p,(A p) 2=k*p 2) (hd : |A.det|=k^3) :
    Measure.map A hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  have hdet : A.det≠0 := by intro he; rw [he,abs_zero] at hd; exact (pow_ne_zero 3 hk.ne') hd.symm
  have hker : LinearMap.ker A.toLinearMap=⊥ := by
    by_contra hn
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
  have hinj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective A := (LinearMap.injective_iff_surjective).mp hinj
  apply hyperbolic_volume_map_of_jacobian A (fun _ => A) A.continuous.measurable
    (fun p hp => A.hasFDerivAt) hinj.injOn
  · apply Set.Subset.antisymm
    · rintro q ⟨p,hp,rfl⟩
      exact show 0<(A p) 2 by rw [hh]; exact mul_pos hk hp
    · intro q hq
      obtain ⟨p,hp⟩ := hsurj q
      refine ⟨p,?_,hp⟩
      change 0<p 2
      have h := hh p
      rw [hp] at h
      exact (mul_pos_iff_of_pos_left hk).mp (h.symm ▸ hq)
  · intro p hp
    rw [hd,hyperbolicDensity,hyperbolicDensity,hh]
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp

lemma translation_preserves_hyperbolicVolume (u : EuclideanSpatial) (hu : u 2=0) :
    Measure.map (fun p => p+u) hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply hyperbolic_volume_map_of_jacobian (fun p => p+u) (fun _ => ContinuousLinearMap.id ℝ _)
    (continuous_id.add continuous_const).measurable
    (fun p hp => (hasFDerivAt_id p).add_const u) (add_left_injective u).injOn
  · apply Set.Subset.antisymm
    · rintro q ⟨p,hp,rfl⟩
      simpa [euclideanUpperHalf,hu] using hp
    · intro p hp
      refine ⟨p-u,?_,sub_add_cancel p u⟩
      simpa [euclideanUpperHalf,hu] using hp
  · intro p hp
    have hid : (ContinuousLinearMap.id ℝ EuclideanSpatial).det=1 := by
      change LinearMap.det (LinearMap.id : EuclideanSpatial →ₗ[ℝ] EuclideanSpatial)=1
      simp
    simp [hyperbolicDensity,hu,hid]

def euclideanMatrixOperator (M : Matrix (Fin 3) (Fin 3) ℝ) :
    EuclideanSpatial →L[ℝ] EuclideanSpatial := M.toEuclideanLin.toContinuousLinearMap

lemma euclideanMatrixOperator_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (p : EuclideanSpatial)
    (j : Fin 3) : euclideanMatrixOperator M p j=∑i,M j i*p i := rfl

lemma euclideanMatrixOperator_det (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (euclideanMatrixOperator M).det=M.det := by
  change LinearMap.det (Matrix.toEuclideanLin M)=M.det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,LinearMap.det_toLin]

def euclideanWeylReflection : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanMatrixOperator !![-1,0,0;0,1,0;0,0,1]

lemma euclideanWeylReflection_apply (p : EuclideanSpatial) :
    euclideanWeylReflection p 0= -p 0 ∧ euclideanWeylReflection p 1=p 1 ∧
      euclideanWeylReflection p 2=p 2 := by
  simp [euclideanWeylReflection,euclideanMatrixOperator_apply,Fin.sum_univ_three]

lemma euclideanWeylReflection_preserves_hyperbolicVolume :
    Measure.map euclideanWeylReflection hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply linear_preserves_hyperbolicVolume euclideanWeylReflection 1 (by norm_num)
  · intro p
    simpa using (euclideanWeylReflection_apply p).2.2
  · norm_num [euclideanWeylReflection,euclideanMatrixOperator_det,Matrix.det_fin_three]

def euclideanComplexDilation (β : ℂ) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  euclideanMatrixOperator !![(β^2).re,-(β^2).im,0;(β^2).im,(β^2).re,0;0,0,Complex.normSq β]

lemma euclideanComplexDilation_apply (β : ℂ) (p : EuclideanSpatial) :
    euclideanComplexDilation β p 0=(β^2).re*p 0-(β^2).im*p 1 ∧
      euclideanComplexDilation β p 1=(β^2).im*p 0+(β^2).re*p 1 ∧
      euclideanComplexDilation β p 2=Complex.normSq β*p 2 := by
  simp [euclideanComplexDilation,euclideanMatrixOperator_apply,Fin.sum_univ_three,sub_eq_add_neg]

lemma euclideanComplexDilation_det (β : ℂ) :
    (euclideanComplexDilation β).det=Complex.normSq β^3 := by
  rw [euclideanComplexDilation,euclideanMatrixOperator_det,Matrix.det_fin_three]
  have h : (β^2).re^2+(β^2).im^2=(Complex.normSq β)^2 := by
    simpa [Complex.normSq_apply,sq] using map_pow Complex.normSq β 2
  change (β^2).re*(β^2).re*Complex.normSq β-(β^2).re*0*0-
    (-(β^2).im)*(β^2).im*Complex.normSq β+(-(β^2).im)*0*0+
    0*(β^2).im*0-0*(β^2).re*0=Complex.normSq β^3
  calc
    _ = ((β^2).re^2+(β^2).im^2)*Complex.normSq β := by ring
    _ = _ := by rw [h]; ring

lemma euclideanComplexDilation_preserves_hyperbolicVolume (β : ℂ) (hβ : β≠0) :
    Measure.map (euclideanComplexDilation β) hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply linear_preserves_hyperbolicVolume (euclideanComplexDilation β) (Complex.normSq β)
    (Complex.normSq_pos.mpr hβ) (fun p => (euclideanComplexDilation_apply β p).2.2)
  rw [euclideanComplexDilation_det,abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg β) 3)]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

instance hyperbolicMeasurableSpace : MeasurableSpace HyperbolicSpace := borel HyperbolicSpace
instance hyperbolicBorelSpace : BorelSpace HyperbolicSpace := ⟨rfl⟩

lemma continuous_hyperbolic_action (g : SL(2,ℂ)) :
    Continuous (fun w : HyperbolicSpace => g • w) := by
  apply (QuotientGroup.isQuotientMap_mk compactSubgroup).continuous_iff.mpr
  exact continuous_hyperbolicProjection.comp (continuous_complexSL_mul g)

def positiveCoordinateHeight (p : EuclideanSpatial) : ℝ := if 0<p 2 then p 2 else 1
lemma positiveCoordinateHeight_pos (p : EuclideanSpatial) : 0<positiveCoordinateHeight p := by
  unfold positiveCoordinateHeight
  split_ifs with hp
  · exact hp
  · norm_num

def euclideanToUpperCoordinates (p : EuclideanSpatial) : UpperCoordinates :=
  ⟨((p 0:ℂ)+Complex.I*(p 1:ℂ),positiveCoordinateHeight p),positiveCoordinateHeight_pos p⟩

def euclideanToHyperbolic (p : EuclideanSpatial) : HyperbolicSpace :=
  upperPoint (euclideanToUpperCoordinates p).1.1 (euclideanToUpperCoordinates p).1.2
    (euclideanToUpperCoordinates p).2

lemma euclideanToUpperCoordinates_measurable : Measurable euclideanToUpperCoordinates := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · change Measurable (fun p : EuclideanSpatial => (p 0:ℂ)+Complex.I*(p 1:ℂ))
    fun_prop
  · exact Measurable.ite euclideanUpperHalf_measurable (by fun_prop) measurable_const

lemma euclideanToHyperbolic_measurable : Measurable euclideanToHyperbolic :=
  continuous_upperCoordinates.measurable.comp euclideanToUpperCoordinates_measurable

lemma euclideanToHyperbolic_positive (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanToHyperbolic p=upperPoint ((p 0:ℂ)+Complex.I*(p 1:ℂ)) (p 2) hp := by
  unfold euclideanToHyperbolic euclideanToUpperCoordinates positiveCoordinateHeight
  simp only [ite_eq_left hp]

def hyperbolicVolume : Measure HyperbolicSpace :=
  Measure.map euclideanToHyperbolic hyperbolicEuclideanVolume

lemma hyperbolicEuclideanVolume_ae_positive :
    ∀ᵐp∂hyperbolicEuclideanVolume,0<p 2 := by
  exact (ae_restrict_mem euclideanUpperHalf_measurable).filter_mono
    ((withDensity_absolutelyContinuous (volume.restrict euclideanUpperHalf) hyperbolicDensity).ae_le)

lemma hyperbolicVolume_map_of_coordinate_action (g : SL(2,ℂ))
    (f : EuclideanSpatial → EuclideanSpatial) (hf : Measurable f)
    (hvol : Measure.map f hyperbolicEuclideanVolume=hyperbolicEuclideanVolume)
    (hcompat : ∀p,0<p 2 → euclideanToHyperbolic (f p)=g • euclideanToHyperbolic p) :
    Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume := by
  unfold hyperbolicVolume
  rw [Measure.map_map (continuous_hyperbolic_action g).measurable euclideanToHyperbolic_measurable]
  calc
    _ = Measure.map (euclideanToHyperbolic ∘ f) hyperbolicEuclideanVolume := by
      apply Measure.map_congr
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      exact (hcompat p hp).symm
    _ = _ := by rw [←Measure.map_map euclideanToHyperbolic_measurable hf,hvol]

lemma matrix_point_coordinates (g : SL(2,ℂ)) :
    (g : HyperbolicSpace)=upperPoint (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g) := by
  obtain ⟨k,hk,hg⟩ := matrix_iwasawa_factor g
  apply Eq.symm
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  change (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g∈compactSubgroup
  have hcancel : (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g=k := by
    calc
      _ = (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*
          (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k) :=
        congrArg (fun M => (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*M) hg
      _ = k := inv_mul_cancel_left _ _
  rwa [hcancel]

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

def matrixCross (g : SL(2,ℂ)) : ℂ := g 0 0*star (g 1 0)+g 0 1*star (g 1 1)

lemma matrixHorizontal_eq_cross_height (g : SL(2,ℂ)) :
    matrixHorizontal g=matrixCross g*(liftedHeight g:ℂ) := by
  unfold matrixHorizontal matrixCross liftedHeight
  rw [Complex.ofReal_inv]
  rfl

lemma matrixCross_upperSection (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    matrixCross (g*upperSection z v hv)=
      ((g 0 0*z+g 0 1)*star (g 1 0*z+g 1 1)+
        g 0 0*star (g 1 0)*(v:ℂ)^2)/(v:ℂ) := by
  have hr : (Real.sqrt v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hv).ne'
  have hrs : (Real.sqrt v:ℂ)^2=(v:ℂ) := by exact_mod_cast Real.sq_sqrt hv.le
  simp only [matrixCross,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  change (g 0 0*(Real.sqrt v:ℂ)+g 0 1*0)*star (g 1 0*(Real.sqrt v:ℂ)+g 1 1*0)+
    (g 0 0*(z/(Real.sqrt v:ℂ))+g 0 1*(Real.sqrt v:ℂ)⁻¹)*
      star (g 1 0*(z/(Real.sqrt v:ℂ))+g 1 1*(Real.sqrt v:ℂ)⁻¹)=_
  simp only [mul_zero,add_zero,star_add,star_mul,Complex.star_def,
    map_inv₀,map_div₀,Complex.conj_ofReal]
  rw [←hrs]
  field_simp
  ; ring

lemma mobius_denominator_pos (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    0<‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2 := by
  exact heightDenominator_pos z v hv (complexBottomRow g) (complexBottomRow_ne_zero g)

lemma upperPoint_congr {z z' : ℂ} {v v' : ℝ} (hv : 0<v) (hv' : 0<v')
    (hz : z=z') (hvv : v=v') : upperPoint z v hv=upperPoint z' v' hv' := by
  subst z'
  subst v'
  rfl

theorem mobius_upperPoint (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0<v) :
    g • upperPoint z v hv=
      upperPoint
        (((g 0 0*z+g 0 1)*star (g 1 0*z+g 1 1)+g 0 0*star (g 1 0)*(v:ℂ)^2)/
          ((‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2:ℝ):ℂ))
        (v/(‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2))
        (div_pos hv (mobius_denominator_pos g z v hv)) := by
  have hh : liftedHeight (g*upperSection z v hv)=
      v/(‖g 1 0*z+g 1 1‖^2+‖g 1 0‖^2*v^2) :=
    hyperbolicHeight_action_upperPoint g z v hv
  change (QuotientGroup.mk (g*upperSection z v hv) : HyperbolicSpace)=_
  rw [matrix_point_coordinates]
  apply upperPoint_congr _ _ _ hh
  rw [matrixHorizontal_eq_cross_height,matrixCross_upperSection,hh,Complex.ofReal_div]
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

def complexTranslation (b : ℂ) : SL(2,ℂ) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def complexDiagonal (b : ℂ) (hb : b≠0) : SL(2,ℂ) :=
  ⟨!![b,0;0,b⁻¹],by simp [Matrix.det_fin_two,hb]⟩
def complexWeyl : SL(2,ℂ) := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma complexTranslation_action (b z : ℂ) (v : ℝ) (hv : 0<v) :
    complexTranslation b • upperPoint z v hv=upperPoint (z+b) v hv := by
  change (QuotientGroup.mk (complexTranslation b*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+b) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (complexTranslation b : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + b) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring

lemma complexWeyl_action (z : ℂ) (v : ℝ) (hv : 0<v) :
    complexWeyl • upperPoint z v hv=
      upperPoint (-star z/((‖z‖^2+v^2:ℝ):ℂ)) (v/(‖z‖^2+v^2))
        (div_pos hv (by nlinarith [sq_nonneg ‖z‖])) := by
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp [complexWeyl]
  · simp [complexWeyl]

lemma complexDiagonal_action (b : ℂ) (hb : b≠0) (z : ℂ) (v : ℝ) (hv : 0<v) :
    complexDiagonal b hb • upperPoint z v hv=
      upperPoint (b^2*z) (Complex.normSq b*v) (mul_pos (Complex.normSq_pos.mpr hb) hv) := by
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · change ((b*z+0)*star (0*z+b⁻¹)+b*star 0*(v:ℂ)^2)/
        ((‖0*z+b⁻¹‖^2+‖(0:ℂ)‖^2*v^2:ℝ):ℂ)=b^2*z
    simp only [zero_mul,mul_zero,zero_add,add_zero,star_zero,norm_zero,zero_pow (by decide : 2≠0)]
    rw [norm_inv,inv_pow,Complex.ofReal_inv]
    simp only [Complex.star_def,map_inv₀]
    have hq : ((‖b‖^2:ℝ):ℂ)=b*star b := by
      simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj b).symm
    rw [hq]
    have hbs : star b≠0 := star_ne_zero.mpr hb
    simp only [Complex.star_def] at hbs ⊢
    field_simp

  · change v/(‖0*z+b⁻¹‖^2+‖(0:ℂ)‖^2*v^2)=Complex.normSq b*v
    simp only [zero_mul,zero_add,add_zero,norm_zero,zero_pow (by decide : 2≠0),norm_inv,inv_pow]
    rw [Complex.normSq_eq_norm_sq]
    field_simp

lemma complex_bruhat_nonzero (g : SL(2,ℂ)) (hc : g 1 0≠0) :
    g=complexTranslation (g 0 0/g 1 0)*complexDiagonal (g 1 0)⁻¹ (inv_ne_zero hc)*
      complexWeyl*complexTranslation (g 1 1/g 1 0) := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) =
    (complexTranslation (g 0 0 / g 1 0) : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexDiagonal (g 1 0)⁻¹ (inv_ne_zero hc) : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexWeyl : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexTranslation (g 1 1 / g 1 0) : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,complexDiagonal,complexWeyl,Matrix.mul_apply,Fin.sum_univ_two,hc] <;>
      field_simp ; linear_combination -hd

lemma complex_bruhat_zero (g : SL(2,ℂ)) (hc : g 1 0=0) :
    ∃ha : g 0 0≠0,g=complexDiagonal (g 0 0) ha*complexTranslation (g 0 1/g 0 0) := by
  have hd : g 0 0*g 1 1=1 := by simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using g.property
  have ha : g 0 0≠0 := by intro h; simp [h] at hd
  refine ⟨ha,?_⟩
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) =
    (complexDiagonal (g 0 0) ha : Matrix (Fin 2) (Fin 2) ℂ) *
    (complexTranslation (g 0 1 / g 0 0) : Matrix (Fin 2) (Fin 2) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,complexDiagonal,Matrix.mul_apply,Fin.sum_univ_two,hc] <;>
      field_simp ; linear_combination hd

def euclideanHorizontalTranslation (b : ℂ) : EuclideanSpatial := WithLp.toLp 2 ![b.re,b.im,0]

lemma complexTranslation_preserves_hyperbolicVolume (b : ℂ) :
    Measure.map (fun w => complexTranslation b • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action (complexTranslation b)
    (fun p => p+euclideanHorizontalTranslation b) (continuous_id.add continuous_const).measurable
    (translation_preserves_hyperbolicVolume _ rfl)
  intro p hp
  have hq : 0<(p+euclideanHorizontalTranslation b) 2 := by simpa [euclideanHorizontalTranslation] using hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexTranslation_action]
  apply upperPoint_congr
  · apply Complex.ext <;> simp [euclideanHorizontalTranslation]
  · simp [euclideanHorizontalTranslation]

lemma complexDiagonal_preserves_hyperbolicVolume (b : ℂ) (hb : b≠0) :
    Measure.map (fun w => complexDiagonal b hb • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action (complexDiagonal b hb)
    (euclideanComplexDilation b) (euclideanComplexDilation b).continuous.measurable
    (euclideanComplexDilation_preserves_hyperbolicVolume b hb)
  intro p hp
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b p
  have hq : 0<(euclideanComplexDilation b p) 2 := by rw [h2]; exact mul_pos (Complex.normSq_pos.mpr hb) hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexDiagonal_action]
  apply upperPoint_congr
  · rw [h0,h1]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] ; ring
  · exact h2

lemma euclidean_complex_norm_sq (p : EuclideanSpatial) :
    ‖(p 0:ℂ)+Complex.I*(p 1:ℂ)‖^2+(p 2)^2=‖p‖^2 := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three,sq]

def euclideanWeylAction (p : EuclideanSpatial) : EuclideanSpatial :=
  euclideanWeylReflection (euclideanInversion p)

lemma euclideanWeylAction_measurable : Measurable euclideanWeylAction :=
  euclideanWeylReflection.continuous.measurable.comp euclideanInversion_measurable

lemma euclideanWeylAction_preserves_hyperbolicVolume :
    Measure.map euclideanWeylAction hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  rw [show euclideanWeylAction=euclideanWeylReflection ∘ euclideanInversion from rfl,
    ←Measure.map_map euclideanWeylReflection.continuous.measurable euclideanInversion_measurable,
    euclideanInversion_preserves_hyperbolicVolume,euclideanWeylReflection_preserves_hyperbolicVolume]

lemma euclideanWeylAction_apply (p : EuclideanSpatial) :
    euclideanWeylAction p 0= -((1/‖p‖)^2*p 0) ∧
      euclideanWeylAction p 1=(1/‖p‖)^2*p 1 ∧
      euclideanWeylAction p 2=(1/‖p‖)^2*p 2 := by
  simpa [euclideanWeylAction,euclideanInversion_apply] using
    euclideanWeylReflection_apply (euclideanInversion p)

lemma complexWeyl_preserves_hyperbolicVolume :
    Measure.map (fun w => complexWeyl • w) hyperbolicVolume=hyperbolicVolume := by
  apply hyperbolicVolume_map_of_coordinate_action complexWeyl euclideanWeylAction
    euclideanWeylAction_measurable euclideanWeylAction_preserves_hyperbolicVolume
  intro p hp
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  have hnc : (‖p‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  obtain ⟨h0,h1,h2⟩ := euclideanWeylAction_apply p
  have hq : 0<euclideanWeylAction p 2 := by
    rw [h2]
    exact mul_pos (sq_pos_of_ne_zero (one_div_ne_zero hn)) hp
  rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexWeyl_action]
  apply upperPoint_congr
  · rw [h0,h1,euclidean_complex_norm_sq]
    simp only [Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,
      Complex.ofReal_one,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
    field_simp
    ; ring
  · rw [h2,euclidean_complex_norm_sq]
    field_simp

lemma hyperbolicVolume_invariant_mul (g h : SL(2,ℂ))
    (hg : Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume)
    (hh : Measure.map (fun w => h • w) hyperbolicVolume=hyperbolicVolume) :
    Measure.map (fun w => (g*h) • w) hyperbolicVolume=hyperbolicVolume := by
  rw [show (fun w : HyperbolicSpace => (g*h) • w)=(fun w => g • w) ∘ (fun w => h • w) by
    funext w; exact mul_smul g h w,
    ←Measure.map_map (continuous_hyperbolic_action g).measurable (continuous_hyperbolic_action h).measurable,
    hh,hg]

theorem hyperbolicVolume_invariant (g : SL(2,ℂ)) :
    Measure.map (fun w => g • w) hyperbolicVolume=hyperbolicVolume := by
  by_cases hc : g 1 0=0
  · obtain ⟨ha,hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact hyperbolicVolume_invariant_mul _ _ (complexDiagonal_preserves_hyperbolicVolume _ ha)
      (complexTranslation_preserves_hyperbolicVolume _)
  · rw [complex_bruhat_nonzero g hc]
    exact hyperbolicVolume_invariant_mul _ _
      (hyperbolicVolume_invariant_mul _ _
        (hyperbolicVolume_invariant_mul _ _ (complexTranslation_preserves_hyperbolicVolume _)
          (complexDiagonal_preserves_hyperbolicVolume _ (inv_ne_zero hc)))
        complexWeyl_preserves_hyperbolicVolume)
      (complexTranslation_preserves_hyperbolicVolume _)

end CubicEisenstein

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def globalBinTripleRange (B : ℝ) (j : GlobalLogIndex) : ℝ :=
  (B*Real.sqrt (globalLogRep j 9)/globalLogRep j 4)*globalLogRep j 2*globalLogRep j 3

def globalBinFirstCoefficient (K ell B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  K/(globalLogRep j 5*ell*B^2*F*Real.sqrt (globalLogRep j 9))

def globalBinChildCharge (B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  128^3*(Real.exp 1)^14*globalPooledDelta B F j*B^2/globalLogRep j 4

theorem globalBinTripleRange_nonneg (B : ℝ) (hB : 0 ≤ B) (j : GlobalLogIndex) :
    0 ≤ globalBinTripleRange B j := by
  unfold globalBinTripleRange
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  have h4 := (globalLogRep_pos j 4).le
  positivity

theorem globalBin_complete_cost (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) (ray : SecondRayIndex) :
    globalBinFirstCoefficient K ell B F j *
      globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
      (globalPooledColumnScale ell j*globalPooledLabelScale j) *
      (128^3*(Real.exp 1)^3*globalBinTripleRange B j) =
    globalBinChildCharge B F j*‖secondRayCoefficient ray‖ := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  have hs := (Real.sqrt_pos.mpr (globalLogRep_pos j 9)).ne'
  have he : Real.exp 4=(Real.exp 1)^4 := by simp
  unfold globalBinFirstCoefficient globalPooledOuterBound globalPooledRowScale
    globalPooledColumnScale globalPooledLabelScale globalBinTripleRange globalBinChildCharge globalPooledDelta
  rw [he]
  field_simp [h]

theorem globalBin_mass_balance (ell B F : ℝ) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalBinChildCharge B F j*(globalPooledColumnScale ell j*globalPooledLabelScale j) =
      128^3*(Real.exp 1)^18*((ell*B^3)*F) := by
  rw [globalPooled_mass ell B F hB hF]
  have hD := (globalPooledDelta_pos B F hB hF j).ne'
  have hJ := (globalLogRep_pos j 4).ne'
  have he : Real.exp 4=(Real.exp 1)^4 := by simp
  unfold globalBinChildCharge
  rw [he]
  field_simp

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalBin_active_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    Real.sqrt (globalLogRep (globalScaleIndex p side x) 9) ≤ globalCubeActiveRoot p x ∧
    globalCubeActiveRoot p x ≤ Real.sqrt (globalLogRep (globalScaleIndex p side x) 9)*Real.exp 1 := by
  have hr := globalScaleIndex_bounds p hp side x hk 9
  change globalLogRep (globalScaleIndex p side x) 9 ≤ (globalCubeActiveRoot p x)^2 ∧
    (globalCubeActiveRoot p x)^2 ≤ globalLogRep (globalScaleIndex p side x) 9*Real.exp 1 at hr
  have hx := (globalCubeActiveRoot_pos p hp x).le
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨hx,hr.1⟩
  · have hs := Real.sq_sqrt (globalLogRep_pos (globalScaleIndex p side x) 9).le
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hrep := (globalLogRep_pos (globalScaleIndex p side x) 9).le
    have hm : (globalCubeActiveRoot p x)^2 ≤
        (Real.sqrt (globalLogRep (globalScaleIndex p side x) 9)*Real.exp 1)^2 := by
      calc
        _ ≤ globalLogRep (globalScaleIndex p side x) 9*Real.exp 1 := hr.2
        _ ≤ globalLogRep (globalScaleIndex p side x) 9*(Real.exp 1)^2 := by gcongr; nlinarith
        _ = _ := by rw [mul_pow,hs]
    exact (sq_le_sq₀ hx (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos 1).le)).mp hm

include hp in
theorem globalBin_first_coefficient_bound (K ell B F : ℝ) (hK : 0 ≤ K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) :
    K/(primeProductNorm p x.firstDivisor*ell*B^2*F*globalCubeActiveRoot p x) ≤
      globalBinFirstCoefficient K ell B F (globalScaleIndex p side x) := by
  have hd := (globalScaleIndex_bounds p hp side x hk 5).1
  have ha := (globalBin_active_bounds p hp side x hk).1
  change globalLogRep (globalScaleIndex p side x) 5 ≤ primeProductNorm p x.firstDivisor at hd
  have h5 := globalLogRep_pos (globalScaleIndex p side x) 5
  have hs := Real.sqrt_pos.mpr (globalLogRep_pos (globalScaleIndex p side x) 9)
  have hd0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstDivisor).le
  unfold globalBinFirstCoefficient
  apply div_le_div_of_nonneg_left hK (by positivity)
  gcongr

include hp in
theorem globalBin_triple_bounds (B : ℝ) (hB : 0 < B) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    let j := globalScaleIndex p side x
    (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) ≤ B*(Real.sqrt (globalLogRep j 9)*Real.exp 1)/globalLogRep j 4 ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.1 : ℝ) ≤ globalLogRep j 2*Real.exp 1 ∧
    (Ideal.absNorm (globalSecondFixedTriple p x).2.2 : ℝ) ≤ globalLogRep j 3*Real.exp 1 := by
  dsimp only
  exact globalSecondFixedTriple_norm_bounds p hp x B _ _ _ _ hB.le (globalLogRep_pos _ 4)
    hb₁ hb₂ (globalBin_active_bounds p hp side x hk).2
    (globalScaleIndex_bounds p hp side x hk 4).1
    (globalScaleIndex_bounds p hp side x hk 2).2 (globalScaleIndex_bounds p hp side x hk 3).2

include hp in

theorem globalBin_triple_count (B : ℝ) (hB : 0 < B) (side : Bool)
    (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hj : ∀ x∈s,globalScaleIndex p side x=j)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ((s.image (globalSecondFixedTriple p)).card : ℝ) ≤
      128^3*(Real.exp 1)^3*globalBinTripleRange B j := by
  by_cases hs : s.Nonempty
  · obtain ⟨x,hxs⟩ := hs
    have hb := globalBin_triple_bounds p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
    dsimp only at hb
    rw [hj x hxs] at hb
    have hn : 1 ≤ (Ideal.absNorm (globalSecondFixedTriple p x).1 : ℝ) := by
      have hh : 1 ≤ Ideal.absNorm (globalSecondFixedTriple p x).1 :=
        Nat.one_le_iff_ne_zero.mpr (fun h => (globalSecondFixedTriple_nonzero p hp x).1 (Ideal.absNorm_eq_zero_iff.mp h))
      exact_mod_cast hh
    have hcount := globalSecondFixedTriple_count p hp s B
      (Real.sqrt (globalLogRep j 9)*Real.exp 1) (globalLogRep j 4)
      (globalLogRep j 2*Real.exp 1) (globalLogRep j 3*Real.exp 1)
      hB.le (globalLogRep_pos j 4) (hn.trans hb.1)
      (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 2) (Real.one_le_exp (by norm_num)))
      (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 3) (Real.one_le_exp (by norm_num))) hb₁ hb₂
      (fun y hy => by have hh := (globalBin_active_bounds p hp side y (hk y hy)).2; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 4).1; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 2).2; rwa [hj y hy] at hh)
      (fun y hy => by have hh := (globalScaleIndex_bounds p hp side y (hk y hy) 3).2; rwa [hj y hy] at hh)
    convert hcount using 1 ; unfold globalBinTripleRange ; ring
  · have hz : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hz]
    simp only [Finset.image_empty,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (by positivity) (globalBinTripleRange_nonneg B hB.le j)

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.GlobalBinLoss -/

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

namespace CanonicalQuadraticSieve

theorem list_prod_le_power (xs : List ℝ) (U : ℝ) (hU : 0≤U)
    (hxs : ∀x∈xs, 0≤x ∧ x≤U) : xs.prod≤U^xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀y∈xs, 0≤y ∧ y≤U := fun y hy => hxs y (by simp [hy])
    simp only [List.prod_cons,List.length_cons,pow_succ]
    have hp : 0≤xs.prod := List.prod_nonneg (fun y hy => (ht y hy).1)
    exact (mul_le_mul hx.2 (ih ht) hp hU).trans_eq (mul_comm _ _)

theorem list_prod_budget (xs budget : List ℝ) (U : ℝ) (hU : 1≤U)
    (hbudget : ∀x∈budget, 0≤x ∧ x≤U) (hxs : ∀x∈xs, x∈budget) (hlen : xs.length≤8) :
    xs.prod≤U^8 := by
  apply (list_prod_le_power xs U (by linarith) (fun x hx => hbudget x (hxs x hx))).trans
  exact pow_le_pow_right₀ hU hlen

theorem poisson_nine_terms_box
    (d lk ln f e vh vz dv uh du lat cd cs ct cp M N T a b eD eS tail U S : ℝ)
    (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈([d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp] : List ℝ), 0≤x ∧ x≤U)
    (hM : 0≤M) (hN : 0≤N) (hT : 1≤T) (ha : 0≤a)
    (hMS : M≤S) (hNS : N≤S) (hTa : T*a≤S)
    (hb : 0≤b ∧ b≤S) (hED : 0≤eD ∧ eD≤S) (hES : 0≤eS ∧ eS≤S)
    (htail : 0≤tail ∧ tail≤S) :
    d*lk*(8*vh*ln^2*f*e*(M+a) + 8*vz*ln^2*f*e*(M+2*T*a) +
      8*ln^2*lat*dv*f*e*(M+2*T*a) + 65536*cd*eD) +
    1536*d*ct*tail +
    lk*(2*uh*d*ln^2*f*e*(4*N/T+a) + 2*d*ln^2*lat*du*f*e*(N+2*T*a) +
      32768*cs*eS) + uh*d^2*cp*b ≤ 262144*U^8*S := by
  let budget : List ℝ := [d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp]
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈budget) (hn : xs.length≤8) : xs.prod≤U^8 :=
    list_prod_budget xs budget U hU hbudget hx hn
  have hc1 : d*lk*vh*ln^2*f*e≤U^8 := by
    have hh := hp [d,lk,vh,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc2 : d*lk*vz*ln^2*f*e≤U^8 := by
    have hh := hp [d,lk,vz,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc3 : d*lk*ln^2*lat*dv*f*e≤U^8 := by
    have hh := hp [d,lk,ln,ln,lat,dv,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc4 : d*lk*cd≤U^8 := by
    have hh := hp [d,lk,cd] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc5 : d*ct≤U^8 := by
    have hh := hp [d,ct] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc6 : lk*uh*d*ln^2*f*e≤U^8 := by
    have hh := hp [lk,uh,d,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc7 : lk*d*ln^2*lat*du*f*e≤U^8 := by
    have hh := hp [lk,d,ln,ln,lat,du,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc8 : lk*cs≤U^8 := by
    have hh := hp [lk,cs] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc9 : uh*d^2*cp≤U^8 := by
    have hh := hp [uh,d,d,cp] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have haS : a≤S := (by nlinarith only [ha, hT] : a≤T*a).trans hTa
  have hdiv : N/T≤N := div_le_self hN hT
  have h1 : M+a≤2*S := by linarith only [hMS, haS]
  have h2 : M+2*T*a≤3*S := by nlinarith only [hMS, hTa]
  have h3 : M+2*T*a≤3*S := h2
  have h6 : 4*N/T+a≤5*S := by rw [mul_div_assoc]; linarith only [hdiv, hNS, haS]
  have h7 : N+2*T*a≤3*S := by nlinarith only [hNS, hTa]
  have hU8 : 0≤U^8 := by positivity
  have ht1 := mul_le_mul hc1 h1 (by positivity : 0≤M+a) hU8
  have ht2 := mul_le_mul hc2 h2 (by positivity : 0≤M+2*T*a) hU8
  have ht3 := mul_le_mul hc3 h3 (by positivity : 0≤M+2*T*a) hU8
  have ht4 := mul_le_mul hc4 hED.2 hED.1 hU8
  have ht5 := mul_le_mul hc5 htail.2 htail.1 hU8
  have ht6 := mul_le_mul hc6 h6 (by positivity : 0≤4*N/T+a) hU8
  have ht7 := mul_le_mul hc7 h7 (by positivity : 0≤N+2*T*a) hU8
  have ht8 := mul_le_mul hc8 hES.2 hES.1 hU8
  have ht9 := mul_le_mul hc9 hb.2 hb.1 hU8
  nlinarith only [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, mul_nonneg hU8 hS]

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonUnitBudget
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [(IdealMobiusDivisorSum.idealDivisors G).card,
   (columnDyadicLength K+1:ℕ), (columnDyadicLength N+1:ℕ),
   256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2,
   divisorExponentConstant hexp deltaLoss hδ*((2*K)*N)^deltaLoss,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant,
   supportConstant ε hε*(N*N)^ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)),
   supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)),
   CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W,
   supportConstant ε hε*N^ε*CP*(K*N)^deltaLoss]

theorem poissonComparisonMajorant_unit_box
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T U S : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 0≤K) (hN : 0<N) (hM : 0≤M) (hT : 1≤T) (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp deltaLoss hδ ε hε G K N W, 0≤x ∧ x≤U)
    (hMS : M≤S) (hNS : N≤S) (hmid : T*Real.sqrt M*(2*K)^(α-1/2)≤S)
    (hpr : Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2)≤S)
    (hED : K*M/T^l≤S) (hES : K*N/T^l≤S)
    (htail : M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)≤S) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
      (fun _ : Unit => (1:ℂ)) W ≤ 262144*U^8*S := by
  have hh := poisson_nine_terms_box
    ((IdealMobiusDivisorSum.idealDivisors G).card:ℝ)
    (columnDyadicLength K+1:ℕ) (columnDyadicLength N+1:ℕ)
    (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)
    (divisorExponentConstant hexp deltaLoss hδ*((2*K)*N)^deltaLoss)
    ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖
    ‖quadraticTransformedSquareProfile W 0‖
    (dualMiddleDecayConstant (quadraticTransformedSquareProfile W))
    ‖paperRadialFourier (quadraticSquareProfile W) 0‖
    (originalMiddleDecayConstant (quadraticSquareProfile W)) nonzeroLatticeEnvelopeConstant
    (supportConstant ε hε*(N*N)^ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)))
    (supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)))
    (CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    (supportConstant ε hε*N^ε*CP*(K*N)^deltaLoss)
    M N T (Real.sqrt M*(2*K)^(α-1/2))
    (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))
    (K*M/T^l) (K*N/T^l)
    (M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))
    U S hU hS hbudget hM hN.le hT (by positivity) hMS hNS
    (by simpa only [mul_assoc] using hmid) ⟨by positivity,hpr⟩
    ⟨by positivity,hED⟩ ⟨by positivity,hES⟩ ⟨by positivity,htail⟩
  convert hh using 1
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,
    mul_one,one_mul,div_one]
  field_simp
  ; ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem globalBin_mask_bound (B F : ℝ) (hB : 0 < B) (hF : 1 ≤ F)
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 ≤
      ‖eisEmbedding m‖^2*(Real.exp 1)^2*globalPooledDelta B F (globalScaleIndex p side x) := by
  let j := globalScaleIndex p side x
  have hb0 := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).2.1
  have he : ‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 =
      ‖eisEmbedding (globalSecondMask p m x)‖^2 := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span,globalSecondMask_span]
  rw [he]
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have ht0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have hr0 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hj2 := (globalLogRep_pos j 2).le
  have hj3 := (globalLogRep_pos j 3).le
  have ha := globalLogRep_ge_one j 0
  change ‖eisEmbedding ((m*_*_)*∏ i∈x.firstCommon,p i)‖^2 ≤ _
  rw [SecondPassIntegration.restored_child_mask_norm]
  calc
    _ ≤ ‖eisEmbedding m‖^2*B*(globalLogRep j 3*Real.exp 1)*(globalLogRep j 2*Real.exp 1) := by gcongr
    _ ≤ ‖eisEmbedding m‖^2*(B*F*globalLogRep j 0)*(globalLogRep j 3*Real.exp 1)*(globalLogRep j 2*Real.exp 1) := by
      gcongr
      calc
        B = B*1*1 := by ring
        _ ≤ _ := by gcongr
    _ = _ := by unfold globalPooledDelta;ring

include hp in

theorem globalBin_invariant (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 1 ≤ F) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    let j := globalScaleIndex p side x
    (globalLogRep j 8*Real.exp 1)*‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 /
      (globalPooledColumnScale ell j*globalPooledLabelScale j) ≤
    (globalBinRadial ell (globalPooledRowScale K ell B F j) j/(Real.exp 1)^2)*
      (K*‖eisEmbedding m‖^2/((ell*B^3)*F)) := by
  dsimp only
  let j := globalScaleIndex p side x
  have hm := globalBin_mask_bound p hp B F hB hF side x hk m hb₁ hb₂
  have hcol := globalPooledColumnScale_pos ell hell j
  have hlab : 0 < globalPooledLabelScale j := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
  have hk8 := globalLogRep_pos j 8
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  calc
    _ ≤ (globalLogRep j 8*Real.exp 1)*
        (‖eisEmbedding m‖^2*(Real.exp 1)^2*globalPooledDelta B F j)/
        (globalPooledColumnScale ell j*globalPooledLabelScale j) := by gcongr
    _ = _ := by
      have h (i : Fin 10) := (globalLogRep_pos j i).ne'
      have he : Real.exp 4=(Real.exp 1)^4 := by simp
      dsimp only [j] at h ⊢
      unfold globalPooledColumnScale globalPooledLabelScale globalPooledDelta globalPooledRowScale globalBinRadial
      rw [he]
      unfold globalPooledColumnScale
      field_simp [h]

include hp in
theorem globalBin_invariant_small_padding (Z η K ell B F : ℝ) (hZ : 1 < Z)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 1 ≤ F)
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hpad : globalBinRadial ell (globalPooledRowScale K ell B F (globalScaleIndex p side x))
      (globalScaleIndex p side x) ≤ Z^η) :
    let j := globalScaleIndex p side x
    (globalLogRep j 8*Real.exp 1)*‖eisEmbedding (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 /
      (globalPooledColumnScale ell j*globalPooledLabelScale j) ≤
    Z^η*(K*‖eisEmbedding m‖^2/((ell*B^3)*F)) := by
  dsimp only
  apply (globalBin_invariant p hp K ell B F hK hell hB hF side x hk m hb₁ hb₂).trans
  have hz0 : 0 < Z := zero_lt_one.trans hZ
  have hpow : 0 ≤ Z^η := (Real.rpow_pos_of_pos hz0 η).le
  have he : 1 ≤ (Real.exp 1)^2 := one_le_pow₀ (Real.one_le_exp (by norm_num))
  have hr : globalBinRadial ell (globalPooledRowScale K ell B F (globalScaleIndex p side x))
      (globalScaleIndex p side x)/(Real.exp 1)^2 ≤ Z^η :=
    (div_le_iff₀ (sq_pos_of_pos (Real.exp_pos 1))).mpr (hpad.trans (le_mul_of_one_le_right hpow he))
  apply mul_le_mul_of_nonneg_right hr
  positivity

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)

def globalBinTriples {ι : Type*} [DecidableEq ι] (p : ι → O)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex) : Finset (Ideal O × Ideal O × Ideal O) :=
  (globalLogSector p s side j).image (globalSecondFixedTriple p)

def globalBinLossScale (B : ℝ) (j : GlobalLogIndex) : ℝ :=
  globalPooledLabelScale j*(B*(Real.sqrt (globalLogRep j 9)*Real.exp 1)/globalLogRep j 4)

def globalDescentWeight (C ε θ₁ θ₂ K ell B F : ℝ) (A J : ℕ) (j : GlobalLogIndex)
    (ray : SecondRayIndex) (q : Ideal O × Ideal O × Ideal O) : ℝ :=
  C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalBinFirstCoefficient K ell B F j *
    globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
    (globalPooledLabelScale j*Ideal.absNorm q.1)^ε /
    (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A *
    (globalPooledColumnScale ell j*globalPooledLabelScale j)

theorem globalPooledRowScale_pos (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) : 0 < globalPooledRowScale K ell B F j := by
  have h1 := globalLogRep_pos j 1
  have h4 := globalLogRep_pos j 4
  have h5 := globalLogRep_pos j 5
  unfold globalPooledRowScale
  positivity

theorem globalBinFirstCoefficient_nonneg (K ell B F : ℝ) (hK : 0 ≤ K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) : 0 ≤ globalBinFirstCoefficient K ell B F j := by
  have h5 := globalLogRep_pos j 5
  have hs := Real.sqrt_pos.mpr (globalLogRep_pos j 9)
  unfold globalBinFirstCoefficient
  positivity

theorem globalDescentWeight_nonneg (C ε θ₁ θ₂ K ell B F : ℝ) (A J : ℕ) (j : GlobalLogIndex)
    (ray : SecondRayIndex) (q : Ideal O × Ideal O × Ideal O)
    (hC : 0 ≤ C) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) :
    0 ≤ globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q := by
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hrow := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hrad := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell hrow j
  have hcol := globalPooledColumnScale_pos ell hell j
  have hlab := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).le
  have h0 := (globalLogRep_pos j 0).le
  have h1 := (globalLogRep_pos j 1).le
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  unfold globalDescentWeight globalPooledOuterBound
  positivity

theorem globalPositiveBin_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O),
      0 < K → 0 < ell → 0 < B → 0 < F → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalArithmeticBinSource p hp hcop hg s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨C,hC,htrans⟩ := full_uniform_globalArithmeticBin_twisted_transfer ε hε A₁ A₂ W V M hM hV hVc hVs A J
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj hc θ₁ θ₂ K ell B F s side j pool Ψ m hK hell hB hF hΨ hs hk
  have hy := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hmass : globalPooledColumnScale ell j*globalPooledLabelScale j ≠ 0 :=
    (mul_pos (globalPooledColumnScale_pos ell hell j) (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))).ne'
  calc
    _ ≤ globalBinFirstCoefficient K ell B F j *
        ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        ‖globalArithmeticBinSource p hp hcop hg s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ := by
      apply mul_le_mul_of_nonneg_left _ hfirst
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ray hray
      exact norm_sum_le _ _
    _ = ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalBinFirstCoefficient K ell B F j *
        ‖globalArithmeticBinSource p hp hcop hg s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ := by simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
      have hq0 : q.1 ≠ ⊥ := by
        rw [← hqx]
        exact (globalSecondFixedTriple_nonzero p hp x).1
      have ht := htrans p hp hcop hg hinj hc θ₁ θ₂ s side q j pool Ψ m ray ell
        (globalPooledRowScale K ell B F j) hell hy hq0 hΨ hs hk
      have ht' := mul_le_mul_of_nonneg_left ht hfirst
      apply ht'.trans_eq
      have hc0 := (globalPooledColumnScale_pos ell hell j).ne'
      have hl0 := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).ne'
      unfold globalDescentWeight
      field_simp

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalBinTriples_label_bound (B : ℝ) (hB : 0 < B) (side : Bool)
    (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (q : Ideal O × Ideal O × Ideal O) (hq : q∈globalBinTriples p s side j) :
    (Ideal.absNorm q.1 : ℝ) ≤ B*(Real.sqrt (globalLogRep j 9)*Real.exp 1)/globalLogRep j 4 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hxs,hj⟩ := Finset.mem_filter.mp hx
  have h := (globalBin_triple_bounds p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)).1
  rwa [hj] at h

include hp in

theorem globalDescentWeight_mass (C ε θ₁ θ₂ K ell B F : ℝ) (A J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (side : Bool) (s : Finset (GlobalSecondData ι)) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
        (globalPooledColumnScale ell j*globalPooledLabelScale j)) ≤
    (C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*(globalBinLossScale B j)^ε /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A) *
      (128^3*(Real.exp 1)^18*(512*32^2))*((ell*B^3)*F) := by
  let Mchild := globalPooledColumnScale ell j*globalPooledLabelScale j
  let D := C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*(globalBinLossScale B j)^ε /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A
  have hmass : 0 < Mchild := mul_pos (globalPooledColumnScale_pos ell hell j)
    (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))
  have hY := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hR := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell hY j
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hL : 0 < globalPooledLabelScale j := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
  have h0 := (globalLogRep_pos j 0).le
  have h1 := (globalLogRep_pos j 1).le
  have h2 := (globalLogRep_pos j 2).le
  have h3 := (globalLogRep_pos j 3).le
  have h4 := (globalLogRep_pos j 4).le
  have hD : 0 ≤ D := by unfold D globalBinLossScale;positivity
  have hcount : ((globalBinTriples p s side j).card : ℝ) ≤ 128^3*(Real.exp 1)^3*globalBinTripleRange B j := by
    apply globalBin_triple_count p hp B hB side (globalLogSector p s side j) j
    · intro x hx;exact (Finset.mem_filter.mp hx).2
    · intro x hx;exact hk x (Finset.mem_filter.mp hx).1
    · intro x hx;exact hb₁ x (Finset.mem_filter.mp hx).1
    · intro x hx;exact hb₂ x (Finset.mem_filter.mp hx).1
  have hterm (ray : SecondRayIndex) :
      (∑ q∈globalBinTriples p s side j,globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q*Mchild) ≤
      D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*‖secondRayCoefficient ray‖ := by
    have ho : 0 ≤ globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j := by
      unfold globalPooledOuterBound;positivity
    calc
      _ ≤ ∑ q∈globalBinTriples p s side j,
          D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hloss : (globalPooledLabelScale j*Ideal.absNorm q.1)^ε ≤ (globalBinLossScale B j)^ε :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left
            (globalBinTriples_label_bound p hp B hB side s j hk hb₁ hb₂ q hq) hL.le) hε.le
        unfold globalDescentWeight D
        calc
          _ ≤ C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalBinFirstCoefficient K ell B F j *
              globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *
              (globalBinLossScale B j)^ε /(1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A *Mchild*Mchild := by
                gcongr
          _ = _ := by ring
      _ = ((globalBinTriples p s side j).card : ℝ)*
          (D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2) := by simp
      _ ≤ (128^3*(Real.exp 1)^3*globalBinTripleRange B j)*
          (D*globalBinFirstCoefficient K ell B F j*globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j*Mchild^2) := by
        gcongr
      _ = D*(globalBinChildCharge B F j*Mchild)*‖secondRayCoefficient ray‖ := by
        have hc := globalBin_complete_cost K ell B F hK hell hB hF j ray
        change globalBinFirstCoefficient K ell B F j * _ * Mchild * _ = _ at hc
        calc
          _ = D*(globalBinFirstCoefficient K ell B F j *
              globalPooledOuterBound ray ell (globalPooledRowScale K ell B F j) j *Mchild *
              (128^3*(Real.exp 1)^3*globalBinTripleRange B j))*Mchild := by ring
          _ = _ := by rw [hc];ring
      _ = _ := by rw [show globalBinChildCharge B F j*Mchild=128^3*(Real.exp 1)^18*((ell*B^3)*F) from globalBin_mass_balance ell B F hB hF j]
  calc
    _ ≤ ∑ ray : SecondRayIndex,D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*‖secondRayCoefficient ray‖ :=
      Finset.sum_le_sum (fun ray _ => hterm ray)
    _ = D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*(∑ ray : SecondRayIndex,‖secondRayCoefficient ray‖) := by rw [Finset.mul_sum]
    _ ≤ D*(128^3*(Real.exp 1)^18*((ell*B^3)*F))*(512*32^2) := by
      apply mul_le_mul_of_nonneg_left secondRayCoefficient_mass
      positivity
    _ = _ := by dsimp only [D];ring

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

namespace CubicEisenstein

def matrixGram (g : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ)*star (g : Matrix (Fin 2) (Fin 2) ℂ)

lemma matrixGram_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixGram (g*k)=matrixGram g := by
  have hku : (k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ)=1 :=
    Matrix.mem_unitaryGroup_iff.mp hk
  unfold matrixGram
  simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
  calc
    _ = (g : Matrix (Fin 2) (Fin 2) ℂ)*
        ((k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ))*
        star (g : Matrix (Fin 2) (Fin 2) ℂ) := by noncomm_ring
    _ = _ := by rw [hku]; simp

def hyperbolicGram : HyperbolicSpace → Matrix (Fin 2) (Fin 2) ℂ :=
  Quotient.lift matrixGram (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixGram_right_unitary g (g⁻¹*h) hk).symm)

lemma hyperbolicGram_continuous : Continuous hyperbolicGram := by
  apply Continuous.quotient_lift
  exact continuous_complexSL_coe.mul continuous_complexSL_coe.star

lemma hyperbolicGram_injective : Function.Injective hyperbolicGram := by
  intro w w' hw
  induction w using Quotient.inductionOn with | _ g =>
    induction w' using Quotient.inductionOn with | _ h =>
      change matrixGram g=matrixGram h at hw
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change (g⁻¹*h:SL(2,ℂ))∈compactSubgroup
      apply Matrix.mem_unitaryGroup_iff.mpr
      have hgi : ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
          (g:Matrix (Fin 2) (Fin 2) ℂ)=1 :=
        congrArg (fun x : SL(2,ℂ) => (x:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel g)
      have hgis : star (g:Matrix (Fin 2) (Fin 2) ℂ)*
          star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=1 := by
        simpa only [star_mul,star_one] using congrArg star hgi
      simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
      calc
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram h*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by unfold matrixGram; noncomm_ring
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram g*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by rw [hw]
        _ = (((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(g:Matrix (Fin 2) (Fin 2) ℂ))*
            (star (g:Matrix (Fin 2) (Fin 2) ℂ)*star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)) := by
          unfold matrixGram
          noncomm_ring
        _ = 1 := by rw [hgi,hgis]; simp

instance hyperbolicT2Space : T2Space HyperbolicSpace :=
  T2Space.of_injective_continuous hyperbolicGram_injective hyperbolicGram_continuous

def complexMatrixRow (g : SL(2,ℂ)) (i : Fin 2) : Fin 2 → ℂ := fun j => g i j

lemma complexMatrixRow_mul (g h : SL(2,ℂ)) (i : Fin 2) :
    complexMatrixRow (g*h) i=rowOperator h (complexMatrixRow g i) := by
  funext j
  simp only [complexMatrixRow,rowOperator_apply,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Matrix.vecMul,dotProduct]

def matrixFrobenius (g : SL(2,ℂ)) : ℝ :=
  rowEnergy (complexMatrixRow g 0)+rowEnergy (complexMatrixRow g 1)

lemma matrixFrobenius_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixFrobenius (g*k)=matrixFrobenius g := by
  simp only [matrixFrobenius,complexMatrixRow_mul,rowEnergy_unitary k hk]

def hyperbolicFrobenius : HyperbolicSpace → ℝ :=
  Quotient.lift matrixFrobenius (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixFrobenius_right_unitary g (g⁻¹*h) hk).symm)

lemma matrixFrobenius_continuous : Continuous matrixFrobenius := by
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  unfold matrixFrobenius rowEnergy complexMatrixRow
  exact ((he 0 0).norm.pow 2 |>.add ((he 0 1).norm.pow 2)).add
    ((he 1 0).norm.pow 2 |>.add ((he 1 1).norm.pow 2))

lemma hyperbolicFrobenius_continuous : Continuous hyperbolicFrobenius :=
  matrixFrobenius_continuous.quotient_lift _

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.FundamentalDomain -/

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

section
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O

def integralRowPair (M : SL(2,O)) : (Fin 2 → O)×(Fin 2 → O) :=
  (fun j => M 0 j,fun j => M 1 j)

lemma integralRowPair_injective : Function.Injective integralRowPair := by
  intro M N h
  apply Subtype.ext
  funext i j
  fin_cases i
  · exact congrFun (congrArg Prod.fst h) j
  · exact congrFun (congrArg Prod.snd h) j

lemma matrixFrobenius_integral (M : SL(2,O)) (g : SL(2,ℂ)) :
    matrixFrobenius (integralComplexMatrix M*g)=
      integralRowEnergy g (integralRowPair M).1+integralRowEnergy g (integralRowPair M).2 := by
  rw [matrixFrobenius,complexMatrixRow_mul,complexMatrixRow_mul]
  rfl

lemma integralRowEnergy_nonneg (g : SL(2,ℂ)) (v : Fin 2 → O) : 0 ≤ integralRowEnergy g v := by
  unfold integralRowEnergy rowEnergy
  positivity

theorem integral_frobenius_sublevel_finite (g : SL(2,ℂ)) (C : ℝ) :
    Set.Finite {M : SL(2,O) | matrixFrobenius (integralComplexMatrix M*g)≤C} := by
  have hs := integralRowEnergy_sublevel_finite g C
  apply (Set.Finite.preimage integralRowPair_injective.injOn (hs.prod hs)).subset
  intro M hM
  change integralRowEnergy g (integralRowPair M).1≤C ∧ integralRowEnergy g (integralRowPair M).2≤C
  change matrixFrobenius (integralComplexMatrix M*g)≤C at hM
  rw [matrixFrobenius_integral] at hM
  exact ⟨by linarith [integralRowEnergy_nonneg g (integralRowPair M).2],
    by linarith [integralRowEnergy_nonneg g (integralRowPair M).1]⟩

theorem integral_hyperbolic_sublevel_finite (w : HyperbolicSpace) (C : ℝ) :
    Set.Finite {M : SL(2,O) | hyperbolicFrobenius (integralComplexMatrix M • w)≤C} := by
  induction w using Quotient.inductionOn with | _ g =>
    exact integral_frobenius_sublevel_finite g C

theorem subgroup_hyperbolic_sublevel_finite (H : Subgroup (SL(2,O)))
    (w : HyperbolicSpace) (C : ℝ) :
    Set.Finite {M : H | hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤C} := by
  exact Set.Finite.preimage Subtype.val_injective.injOn (integral_hyperbolic_sublevel_finite w C)

theorem subgroup_orbit_minimum (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,∀N : H,
      hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤
        hyperbolicFrobenius (integralComplexMatrix (N:SL(2,O)) • w) := by
  let S : Set H := {M | hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)≤hyperbolicFrobenius w}
  have hs : Set.Finite S := subgroup_hyperbolic_sublevel_finite H w _
  have hne : S.Nonempty := ⟨1,by simp [S]⟩
  obtain ⟨M,hM,hmin⟩ := Set.exists_min_image S
    (fun M : H => hyperbolicFrobenius (integralComplexMatrix (M:SL(2,O)) • w)) hs hne
  refine ⟨M,fun N => ?_⟩
  by_cases hN : N∈S
  · exact hmin N hN
  · exact hM.trans (le_of_lt (lt_of_not_ge hN))

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O

lemma integralComplexMatrix_injective : Function.Injective integralComplexMatrix := by
  intro M N h
  apply Subtype.ext
  funext i j
  apply eisEmbedding_injective
  exact congrArg (fun A : SL(2,ℂ) => A i j) h

lemma levelThree_trace_divisible_nine (M : levelThree) :
    (9:O)∣((M:SL(2,O)) 0 0+(M:SL(2,O)) 1 1-2) := by
  have ha : (3:O)∣((M:SL(2,O)) 0 0-1) := by simpa using levelThree_entry M 0 0
  have hd : (3:O)∣((M:SL(2,O)) 1 1-1) := by simpa using levelThree_entry M 1 1
  have hb : (3:O)∣(M:SL(2,O)) 0 1 := by simpa using levelThree_entry M 0 1
  have hc : (3:O)∣(M:SL(2,O)) 1 0 := by simpa using levelThree_entry M 1 0
  have hdet : (M:SL(2,O)) 0 0*(M:SL(2,O)) 1 1-(M:SL(2,O)) 0 1*(M:SL(2,O)) 1 0=1 := by
    simpa only [Matrix.det_fin_two] using (M:SL(2,O)).property
  have he : (M:SL(2,O)) 0 0+(M:SL(2,O)) 1 1-2=
      (M:SL(2,O)) 0 1*(M:SL(2,O)) 1 0-
        ((M:SL(2,O)) 0 0-1)*((M:SL(2,O)) 1 1-1) := by linear_combination hdet
  rw [he]
  exact dvd_sub (by simpa only [show (3:O)*3=9 by ring] using mul_dvd_mul hb hc) (by simpa only [show (3:O)*3=9 by ring] using mul_dvd_mul ha hd)

lemma unitary_row_normSq (k : SL(2,ℂ)) (hk : k∈compactSubgroup) (i : Fin 2) :
    Complex.normSq (k i 0)+Complex.normSq (k i 1)=1 := by
  have hu := Matrix.mem_unitaryGroup_iff.mp hk
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A i i).re) hu
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,Matrix.one_apply_eq,
    Complex.add_re,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.one_re] at he
  simp only [Complex.normSq_apply]
  nlinarith

lemma unitary_trace_norm_le_two (k : SL(2,ℂ)) (hk : k∈compactSubgroup) : ‖k 0 0+k 1 1‖≤2 := by
  have h0 := unitary_row_normSq k hk 0
  have h1 := unitary_row_normSq k hk 1
  have ha : ‖k 0 0‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at h0
    nlinarith [norm_nonneg (k 0 0),Complex.normSq_nonneg (k 0 1)]
  have hd : ‖k 1 1‖≤1 := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at h1
    nlinarith [norm_nonneg (k 1 1),sq_nonneg ‖k 1 0‖]
  exact (norm_add_le _ _).trans (by linarith)

lemma unitary_trace_two_eq_one (k : SL(2,ℂ)) (hk : k∈compactSubgroup)
    (ht : k 0 0+k 1 1=2) : k=1 := by
  have h0 := unitary_row_normSq k hk 0
  have h1 := unitary_row_normSq k hk 1
  have htR := congrArg Complex.re ht
  norm_num [Complex.add_re] at htR
  have hs : Complex.normSq (k 0 0-1)+Complex.normSq (k 0 1)+
      Complex.normSq (k 1 0)+Complex.normSq (k 1 1-1)=0 := by
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero] at *
    nlinarith
  have ha : k 0 0=1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)]))
  have hb : k 0 1=0 := Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)])
  have hc : k 1 0=0 := Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)])
  have hd : k 1 1=1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp (by
    nlinarith [Complex.normSq_nonneg (k 0 0-1),Complex.normSq_nonneg (k 0 1),
      Complex.normSq_nonneg (k 1 0),Complex.normSq_nonneg (k 1 1-1)]))
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simpa using (by first | exact ha | exact hb | exact hc | exact hd)

lemma matrix_trace_conjugate (g h : SL(2,ℂ)) :
    (g⁻¹*h*g) 0 0+(g⁻¹*h*g) 1 1=h 0 0+h 1 1 := by
  have ht := Matrix.trace_mul_cycle
    (((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ))
    (h:Matrix (Fin 2) (Fin 2) ℂ) (g:Matrix (Fin 2) (Fin 2) ℂ)
  have hi : (g:Matrix (Fin 2) (Fin 2) ℂ)*(((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ))=1 :=
    congrArg (fun A : SL(2,ℂ) => (A:Matrix (Fin 2) (Fin 2) ℂ)) (mul_inv_cancel g)
  rw [hi,Matrix.one_mul] at ht
  simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.trace,Matrix.diag_apply,Fin.sum_univ_two] using ht

lemma levelThree_unitary_conjugate_eq_one (M : levelThree) (g : SL(2,ℂ))
    (hk : g⁻¹*complexMatrix M*g∈compactSubgroup) : M=1 := by
  let k := g⁻¹*complexMatrix M*g
  have htr := matrix_trace_conjugate g (complexMatrix M)
  have hnorm : ‖complexMatrix M 0 0+complexMatrix M 1 1-2‖≤4 := by
    have hb := unitary_trace_norm_le_two k hk
    rw [htr] at hb
    have hn := norm_sub_le (complexMatrix M 0 0+complexMatrix M 1 1) (2:ℂ)
    norm_num at hn
    linarith
  obtain ⟨a,ha⟩ := levelThree_trace_divisible_nine M
  have hmap : complexMatrix M 0 0+complexMatrix M 1 1-2=(9:ℂ)*eisEmbedding a := by
    change eisEmbedding ((M:SL(2,O)) 0 0)+eisEmbedding ((M:SL(2,O)) 1 1)-2=(9:ℂ)*eisEmbedding a
    simpa only [map_add,map_sub,map_ofNat,map_mul] using congrArg eisEmbedding ha
  have haz : a=0 := by
    by_contra hne
    have hn := one_le_normSq_embedding a hne
    rw [Complex.normSq_eq_norm_sq] at hn
    have hn1 : 1≤‖eisEmbedding a‖ := by nlinarith [norm_nonneg (eisEmbedding a)]
    rw [hmap,norm_mul] at hnorm
    norm_num at hnorm
    linarith
  have ht2 : k 0 0+k 1 1=2 := by
    rw [htr]
    apply sub_eq_zero.mp
    rw [hmap,haz,map_zero,mul_zero]
  have hk1 : k=1 := unitary_trace_two_eq_one k hk ht2
  have hM1 : complexMatrix M=1 := by
    have h := congrArg (fun A : SL(2,ℂ) => g*A*g⁻¹) hk1
    simpa [k,mul_assoc] using h
  apply Subtype.ext
  apply integralComplexMatrix_injective
  simpa only [map_one,integralComplexMatrix_levelThree] using hM1

theorem levelThree_action_free (M : levelThree) (w : HyperbolicSpace)
    (hw : complexMatrix M • w=w) : M=1 := by
  induction w using Quotient.inductionOn with | _ g =>
    apply levelThree_unitary_conjugate_eq_one M g
    have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hw.symm)
    simpa only [mul_assoc,smul_eq_mul] using hrel

end

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O

def hyperbolicKeyCoordinates (w : HyperbolicSpace) : Fin 9 → ℝ :=
  ![hyperbolicFrobenius w,(hyperbolicGram w 0 0).re,(hyperbolicGram w 0 0).im,
    (hyperbolicGram w 0 1).re,(hyperbolicGram w 0 1).im,
    (hyperbolicGram w 1 0).re,(hyperbolicGram w 1 0).im,
    (hyperbolicGram w 1 1).re,(hyperbolicGram w 1 1).im]

def hyperbolicOrderKey (w : HyperbolicSpace) : Lex (Fin 9 → ℝ) := toLex (hyperbolicKeyCoordinates w)

lemma hyperbolicOrderKey_injective : Function.Injective hyperbolicOrderKey := by
  intro w u h
  have hc : hyperbolicKeyCoordinates w=hyperbolicKeyCoordinates u := congrArg ofLex h
  apply hyperbolicGram_injective
  funext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  · exact congrFun hc 1
  · exact congrFun hc 2
  · exact congrFun hc 3
  · exact congrFun hc 4
  · exact congrFun hc 5
  · exact congrFun hc 6
  · exact congrFun hc 7
  · exact congrFun hc 8

lemma hyperbolicOrderKey_lt_of_frobenius {w u : HyperbolicSpace}
    (h : hyperbolicFrobenius w<hyperbolicFrobenius u) : hyperbolicOrderKey w<hyperbolicOrderKey u := by
  refine ⟨0,?_,h⟩
  intro j hj
  exact False.elim (not_lt_of_ge (Fin.zero_le j) hj)

attribute [fun_prop] hyperbolicGram_continuous hyperbolicFrobenius_continuous

lemma hyperbolicKeyCoordinates_continuous (i : Fin 9) :
    Continuous (fun w => hyperbolicKeyCoordinates w i) := by
  fin_cases i <;> simp only [hyperbolicKeyCoordinates] <;> fun_prop

lemma hyperbolicOrderKey_lt_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (f g : X → HyperbolicSpace) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {x | hyperbolicOrderKey (f x)<hyperbolicOrderKey (g x)} := by
  change MeasurableSet {x | ∃i : Fin 9,(∀j : Fin 9,j < i → hyperbolicKeyCoordinates (f x) j=hyperbolicKeyCoordinates (g x) j) ∧
    hyperbolicKeyCoordinates (f x) i<hyperbolicKeyCoordinates (g x) i}
  simp only [Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact (isClosed_eq ((hyperbolicKeyCoordinates_continuous j).comp hf)
      ((hyperbolicKeyCoordinates_continuous j).comp hg)).measurableSet
  · exact measurableSet_lt ((hyperbolicKeyCoordinates_continuous i).comp hf).measurable
      ((hyperbolicKeyCoordinates_continuous i).comp hg).measurable

lemma hyperbolicOrderKey_le_measurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (f g : X → HyperbolicSpace) (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {x | hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x)} := by
  have he : {x | hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x)}=
      {x | hyperbolicOrderKey (g x)<hyperbolicOrderKey (f x)}ᶜ := by
    ext x
    change hyperbolicOrderKey (f x)≤hyperbolicOrderKey (g x) ↔ ¬hyperbolicOrderKey (g x)<hyperbolicOrderKey (f x)
    exact ⟨fun h => not_lt_of_ge h,fun h => le_of_not_gt h⟩
  rw [he]
  exact (hyperbolicOrderKey_lt_measurable g f hg hf).compl

instance integralSLCountable : Countable (SL(2,O)) := by
  let : Countable O := latticeCoordEquiv.injective.countable
  let : Countable (Matrix (Fin 2) (Fin 2) O) := inferInstanceAs (Countable (Fin 2 → Fin 2 → O))
  exact inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) O // A.det=1})

instance integralSubgroupHyperbolicAction (H : Subgroup (SL(2,O))) : MulAction H HyperbolicSpace :=
  MulAction.compHom HyperbolicSpace (integralComplexMatrix.comp H.subtype)

lemma integralSubgroup_smul (H : Subgroup (SL(2,O))) (M : H) (w : HyperbolicSpace) :
    M • w=integralComplexMatrix (M:SL(2,O)) • w := rfl

def hyperbolicFundamentalSet (H : Subgroup (SL(2,O))) : Set HyperbolicSpace :=
  {w | ∀M : H,hyperbolicOrderKey w≤hyperbolicOrderKey (M • w)}

lemma hyperbolicFundamentalSet_measurable (H : Subgroup (SL(2,O))) :
    MeasurableSet (hyperbolicFundamentalSet H) := by
  unfold hyperbolicFundamentalSet
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro M
  exact hyperbolicOrderKey_le_measurable _ _ continuous_id
    (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O))))

lemma exists_key_orbit_minimum (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,∀N : H,hyperbolicOrderKey (M • w)≤hyperbolicOrderKey (N • w) := by
  let S : Set H := {M | hyperbolicFrobenius (M • w)≤hyperbolicFrobenius w}
  have hs : Set.Finite S := subgroup_hyperbolic_sublevel_finite H w _
  have hne : S.Nonempty := ⟨1,by simp [S]⟩
  obtain ⟨M,hM,hmin⟩ := Set.exists_min_image S (fun M : H => hyperbolicOrderKey (M • w)) hs hne
  refine ⟨M,fun N => ?_⟩
  by_cases hN : N∈S
  · exact hmin N hN
  · apply le_of_lt
    apply hyperbolicOrderKey_lt_of_frobenius
    exact hM.trans_lt (lt_of_not_ge hN)

lemma hyperbolicFundamentalSet_covers (H : Subgroup (SL(2,O))) (w : HyperbolicSpace) :
    ∃M : H,M • w∈hyperbolicFundamentalSet H := by
  obtain ⟨M,hM⟩ := exists_key_orbit_minimum H w
  refine ⟨M,fun N => ?_⟩
  simpa only [mul_smul] using hM (N*M)

lemma hyperbolicFundamentalSet_orbit_unique (H : Subgroup (SL(2,O))) (w : HyperbolicSpace)
    (hw : w∈hyperbolicFundamentalSet H) (M : H)
    (hMw : M • w∈hyperbolicFundamentalSet H) : M • w=w := by
  apply hyperbolicOrderKey_injective
  apply le_antisymm
  · simpa only [inv_smul_smul] using hMw M⁻¹
  · exact hw M

lemma subgroup_action_free (H : Subgroup (SL(2,O))) (hH : H≤levelThree) (M : H)
    (w : HyperbolicSpace) (hM : M • w=w) : M=1 := by
  have he := levelThree_action_free (⟨(M:SL(2,O)),hH M.property⟩ : levelThree) w hM
  apply Subtype.ext
  exact congrArg (fun N : levelThree => (N:SL(2,O))) he

theorem hyperbolicFundamentalSet_isFundamentalDomain (H : Subgroup (SL(2,O))) (hH : H≤levelThree) :
    IsFundamentalDomain H (hyperbolicFundamentalSet H) hyperbolicVolume := by
  apply IsFundamentalDomain.mk' (hyperbolicFundamentalSet_measurable H).nullMeasurableSet
  intro w
  obtain ⟨M,hM⟩ := hyperbolicFundamentalSet_covers H w
  refine ⟨M,hM,fun N hN => ?_⟩
  have he : (N*M⁻¹) • (M • w)=M • w :=
    hyperbolicFundamentalSet_orbit_unique H (M • w) hM (N*M⁻¹) (by
      simpa only [mul_smul,inv_smul_smul] using hN)
  have hNM : N*M⁻¹=1 := subgroup_action_free H hH _ _ he
  exact mul_inv_eq_one.mp hNM

lemma globalKubotaKernel_le_levelThree : globalKubotaKernel≤levelThree := by
  intro M hM
  exact ((globalKubotaKernel_mem M).mp hM).choose

theorem globalKubotaKernel_isFundamentalDomain :
    IsFundamentalDomain globalKubotaKernel (hyperbolicFundamentalSet globalKubotaKernel) hyperbolicVolume :=
  hyperbolicFundamentalSet_isFundamentalDomain _ globalKubotaKernel_le_levelThree

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "O" => ActualEisensteinCubic.O

instance integralSubgroupMeasurableAction (H : Subgroup (SL(2,O))) :
    MeasurableConstSMul H HyperbolicSpace :=
  ⟨fun M => (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))).measurable⟩

instance integralSubgroupVolumeInvariant (H : Subgroup (SL(2,O))) :
    SMulInvariantMeasure H HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul M s hs := by
    have hm := (continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))).measurable
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s)
      (hyperbolicVolume_invariant (integralComplexMatrix (M:SL(2,O))))
    simpa only [Measure.map_apply hm hs,integralSubgroup_smul] using he

lemma measurable_integralOrbitProjection (H : Subgroup (SL(2,O))) :
    Measurable (integralOrbitProjection H) := measurable_quotient_mk' (s := integralOrbitRel H)

def integralQuotientVolume (H : Subgroup (SL(2,O))) : Measure (IntegralOrbitQuotient H) :=
  Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))

lemma quotient_projection_measurePreserving (H : Subgroup (SL(2,O))) :
    MeasurePreserving (integralOrbitProjection H)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet H)) (integralQuotientVolume H) :=
  ⟨measurable_integralOrbitProjection H,rfl⟩

theorem integralQuotientVolume_independent (H : Subgroup (SL(2,O))) (hH : H≤levelThree)
    (D : Set HyperbolicSpace) (hD : IsFundamentalDomain H D hyperbolicVolume) :
    Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict D)=integralQuotientVolume H := by
  apply Measure.ext
  intro S hS
  have hp := measurable_integralOrbitProjection H
  unfold integralQuotientVolume
  rw [Measure.map_apply hp hS,Measure.map_apply hp hS,Measure.restrict_apply (hp hS),
    Measure.restrict_apply (hp hS)]
  apply hD.measure_set_eq (hyperbolicFundamentalSet_isFundamentalDomain H hH) (hp hS)
  intro M
  ext w
  change integralOrbitProjection H (M • w)∈S ↔ integralOrbitProjection H w∈S
  rw [integralSubgroup_smul,integralOrbitProjection_eq]

lemma integralQuotientVolume_integral (H : Subgroup (SL(2,O)))
    (f : IntegralOrbitQuotient H → ℂ) (hf : AEStronglyMeasurable f (integralQuotientVolume H)) :
    (∫q,f q∂integralQuotientVolume H)=
      ∫w in hyperbolicFundamentalSet H,f (integralOrbitProjection H w)∂hyperbolicVolume :=
  integral_map (measurable_integralOrbitProjection H).aemeasurable hf

lemma hyperbolicEuclideanVolume_ne_zero : hyperbolicEuclideanVolume≠0 := by
  have hU : IsOpen euclideanUpperHalf := isOpen_lt continuous_const (by fun_prop)
  have hne : euclideanUpperHalf.Nonempty := ⟨WithLp.toLp 2 ![0,0,1],by norm_num [euclideanUpperHalf]⟩
  have hpos : 0<volume euclideanUpperHalf := hU.measure_pos volume hne
  have hAC : (volume.restrict euclideanUpperHalf) ≪ hyperbolicEuclideanVolume := by
    apply withDensity_absolutelyContinuous' hyperbolicDensity_measurable.aemeasurable
    filter_upwards [ae_restrict_mem euclideanUpperHalf_measurable] with p hp
    apply ne_of_gt
    change 0<ENNReal.ofReal ((p 2)^3)⁻¹
    apply ENNReal.ofReal_pos.mpr
    exact inv_pos.mpr (pow_pos hp 3)
  intro hz
  have hh : (volume.restrict euclideanUpperHalf) Set.univ=0 := hAC (by rw [hz]; simp)
  simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
  exact hpos.ne' hh

lemma hyperbolicVolume_ne_zero : hyperbolicVolume≠0 :=
  (Measure.map_ne_zero_iff euclideanToHyperbolic_measurable.aemeasurable).mpr hyperbolicEuclideanVolume_ne_zero

lemma integralQuotientVolume_ne_zero (H : Subgroup (SL(2,O))) (hH : H≤levelThree) :
    integralQuotientVolume H≠0 := by
  apply (Measure.map_ne_zero_iff (measurable_integralOrbitProjection H).aemeasurable).mpr
  intro hz
  have hD := MeasureTheory.IsFundamentalDomain.measure_ne_zero hyperbolicVolume_ne_zero
    (hyperbolicFundamentalSet_isFundamentalDomain H hH)
  have hh := congrArg (fun ν : Measure HyperbolicSpace => ν Set.univ) hz
  simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hh
  exact hD hh

abbrev KernelQuotientL2 := Lp ℂ 2 (integralQuotientVolume globalKubotaKernel)
example : InnerProductSpace ℂ KernelQuotientL2 := inferInstance
example : CompleteSpace KernelQuotientL2 := inferInstance

lemma kernel_eisenstein_invariant (M : globalKubotaKernel) (s : ℂ) (hs : 2<s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (M • w)=hyperbolicEisenstein s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := hyperbolicEisenstein_automorphy (⟨(M:SL(2,O)),hM⟩ : levelThree) s hs w
  rw [hchar,one_mul] at he
  exact he

def kernelQuotientEisenstein (s : ℂ) (hs : 2<s.re) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (hyperbolicEisenstein s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_eisenstein_invariant M s hs w).symm)

lemma kernelQuotientEisenstein_mk (s : ℂ) (hs : 2<s.re) (w : HyperbolicSpace) :
    kernelQuotientEisenstein s hs (integralOrbitProjection globalKubotaKernel w)=
      hyperbolicEisenstein s w := rfl

lemma kernel_seed_invariant (a b : ℝ) (s : ℂ) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (M • w)=smoothCuspSeed a b s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := smoothCuspSeed_automorphy a b s (⟨(M:SL(2,O)),hM⟩ : levelThree) w
  rw [hchar,one_mul] at he
  exact he

lemma kernel_defect_invariant (a b : ℝ) (s : ℂ) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (M • w)=smoothCuspSeedDefect a b s w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,O))).mp M.property
  have he := smoothCuspSeedDefect_automorphy a b s (⟨(M:SL(2,O)),hM⟩ : levelThree) w
  rw [hchar,one_mul] at he
  exact he

def kernelQuotientSeed (a b : ℝ) (s : ℂ) : IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (smoothCuspSeed a b s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_seed_invariant a b s M w).symm)

def kernelQuotientDefect (a b : ℝ) (s : ℂ) : IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (smoothCuspSeedDefect a b s) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    exact (kernel_defect_invariant a b s M w).symm)

end CubicEisenstein

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

def largeCubeCoefficient (H₀ : ℝ) (B : Ideal O) : ℂ :=
  if B=⊥ then 0 else ∑ H∈idealDivisors B,
    if H₀ ≤ (Ideal.absNorm H : ℝ) then (UniqueFactorizationMonoid.moebius H : ℂ) else 0

theorem largeCubeCoefficient_zero (H₀ : ℝ) : largeCubeCoefficient H₀ ⊥=0 := by
  simp [largeCubeCoefficient]

theorem largeCubeCoefficient_norm_le (H₀ : ℝ) (B : Ideal O) :
    ‖largeCubeCoefficient H₀ B‖ ≤ (idealDivisors B).card := by
  by_cases hB : B=⊥
  · simp [hB,largeCubeCoefficient]
  · rw [largeCubeCoefficient,ite_eq_right hB]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ H∈idealDivisors B,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro H hH
        by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
        · simp only [ite_eq_left h]
          by_cases hsf : Squarefree H
          · simp [hsf.moebius_eq]
          · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsf]
        · simp [h]
      _ = _ := by simp

theorem largeCubeCoefficient_support (H₀ : ℝ) (B : Ideal O)
    (h : largeCubeCoefficient H₀ B ≠ 0) : B≠⊥ ∧ H₀ ≤ (Ideal.absNorm B : ℝ) := by
  have hB : B≠⊥ := fun hb => h (by simp [hb,largeCubeCoefficient])
  refine ⟨hB,?_⟩
  rw [largeCubeCoefficient,ite_eq_right hB] at h
  obtain ⟨H,hH,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hlarge : H₀ ≤ (Ideal.absNorm H : ℝ) := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  have hdiv := (mem_idealDivisors hB).mp hH
  have hpos : 0 < Ideal.absNorm B := Nat.pos_iff_ne_zero.mpr (fun hn => hB (Ideal.absNorm_eq_zero_iff.mp hn))
  exact hlarge.trans (by exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hdiv))

theorem large_cube_convolution (H₀ : ℝ) (c : Ideal O →* ℂ) (hc0 : c 0=0)
    (f : Ideal O → ℂ)
    (hfinite : (Function.support (fun p : Ideal O × Ideal O =>
      (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2))).Finite) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then
        (UniqueFactorizationMonoid.moebius H : ℂ)*c (H*J)*f (H*J) else 0) =
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*c B*f B := by
  let F : Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.1 : ℝ) then
      (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2) else 0
  have hF : Summable F := summable_of_hasFiniteSupport (hfinite.subset (by
    intro p hp
    by_contra hn
    have he : (UniqueFactorizationMonoid.moebius p.1 : ℂ)*c (p.1*p.2)*f (p.1*p.2)=0 := not_ne_iff.mp hn
    exact hp (by dsimp [F];rw [he];simp)))
  have hfiber (B : Ideal O) : (∑' p : MulFiber B,F p.val)=largeCubeCoefficient H₀ B*c B*f B := by
    by_cases hB : B=0
    · subst B
      have hz : ∀ p : MulFiber 0,F p.val=0 := by
        intro p
        dsimp [F]
        rw [p.property,hc0]
        simp
      simp [hz,largeCubeCoefficient]
    · let e := mulFiberDivisorEquiv B hB
      have hsum : (∑' p : MulFiber B,
          if H₀ ≤ (Ideal.absNorm p.val.1 : ℝ) then (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) else 0) =
          largeCubeCoefficient H₀ B := by
        calc
          _ = ∑' H : {H : Ideal O // H∈idealDivisors B},
              if H₀ ≤ (Ideal.absNorm H.val : ℝ) then (UniqueFactorizationMonoid.moebius H.val : ℂ) else 0 :=
            e.tsum_eq _
          _ = _ := by
            rw [tsum_fintype,largeCubeCoefficient,ite_eq_right (show B≠⊥ from hB)]
            exact (Finset.sum_subtype (idealDivisors B) (fun H => Iff.rfl)
              (fun H => if H₀ ≤ (Ideal.absNorm H : ℝ) then (UniqueFactorizationMonoid.moebius H : ℂ) else 0)).symm
      calc
        _ = ∑' p : MulFiber B,
            (if H₀ ≤ (Ideal.absNorm p.val.1 : ℝ) then (UniqueFactorizationMonoid.moebius p.val.1 : ℂ) else 0)*(c B*f B) := by
          apply tsum_congr
          intro p
          dsimp [F]
          rw [p.property]
          split_ifs <;> ring
        _ = _ := by rw [tsum_mul_right,hsum];ring
  have hs := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B,F p.val) (∑' p,F p) at hs
  simp_rw [hfiber] at hs
  rw [← hF.tsum_prod]
  exact hs.tsum_eq.symm

theorem large_cube_inner_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) (I : Ideal O) :
    (∑' H : Ideal O,∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0) =
    ∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let f : Ideal O → ℂ := fun B =>
    columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I : ℝ) : ℂ)*
      Vstar W ((Ideal.absNorm I : ℝ)*(Ideal.absNorm B : ℝ)^3/X)
  have heq (H J : Ideal O) :
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ (H*J)*f (H*J)=expandedTerm Ψ W X I H J := by
    simp only [f,expandedTerm,map_mul,Nat.cast_mul,mul_pow,mul_assoc]
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hp : (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X I p.1 p.2)).Finite := by
    change ((fun p : Ideal O × Ideal O => (I,p)) ⁻¹'
      Function.support (fun p : Ideal O × Ideal O × Ideal O => expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => (Prod.mk.inj hab).2) hf
  have hg := large_cube_convolution H₀ (cubeWeight Ψ) (cubeWeight_zero Ψ) f (by simpa only [heq] using hp)
  rw [show (∑' H : Ideal O, ∑' J : Ideal O,
      if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0)=
      ∑' B : Ideal O,largeCubeCoefficient H₀ B*cubeWeight Ψ B*f B by simpa only [heq] using hg]
  apply tsum_congr
  intro B
  dsimp [f,summand]
  ring

theorem large_cube_reopen (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) :
    (∑' H : Ideal O, if H₀ ≤ (Ideal.absNorm H : ℝ) then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        completedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) else 0) =
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let F : Ideal O × Ideal O × Ideal O → ℂ := fun p =>
    if H₀ ≤ (Ideal.absNorm p.2.1 : ℝ) then expandedTerm Ψ W X p.1 p.2.1 p.2.2 else 0
  have hF : Summable F := summable_of_hasFiniteSupport
    ((finite_support_expandedTerm Ψ W hW X hX).subset (by
      intro p hp
      by_contra hn
      have he : expandedTerm Ψ W X p.1 p.2.1 p.2.2=0 := not_ne_iff.mp hn
      exact hp (by simp [F,he])))
  let e : (Ideal O × Ideal O × Ideal O) ≃ (Ideal O × Ideal O × Ideal O) := {
    toFun := fun p => (p.2.1,p.1,p.2.2)
    invFun := fun p => (p.2.1,p.1,p.2.2)
    left_inv := by rintro ⟨I,H,J⟩;rfl
    right_inv := by rintro ⟨I,H,J⟩;rfl }
  have hswap : Summable (fun p => F (e p)) := e.summable_iff.mpr hF
  calc
    _ = ∑' H : Ideal O,∑' I : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0 := by
      apply tsum_congr
      intro H
      by_cases h : H₀ ≤ (Ideal.absNorm H : ℝ)
      · simp only [ite_eq_left h,weighted_completedT_reopen]
      · simp only [ite_eq_right h,tsum_zero]
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F (e p) := by
      rw [hswap.tsum_prod]
      apply tsum_congr
      intro H
      exact (hswap.prod_factor H).tsum_prod.symm
    _ = ∑' p : Ideal O × Ideal O × Ideal O,F p := e.tsum_eq F
    _ = ∑' I : Ideal O,∑' H : Ideal O,∑' J : Ideal O,
        if H₀ ≤ (Ideal.absNorm H : ℝ) then expandedTerm Ψ W X I H J else 0 := by
      rw [hF.tsum_prod]
      apply tsum_congr
      intro I
      exact (hF.prod_factor I).tsum_prod
    _ = _ := tsum_congr (large_cube_inner_reopen Ψ W hW X H₀ hX)

theorem completed_cube_inverse_split (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹*(∑' I : Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I : ℝ)/X)) =
    (∑' H : Ideal O, if (Ideal.absNorm H : ℝ)<H₀ then
      (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
        completedT Ψ W (X/(Ideal.absNorm H : ℝ)^3) else 0) +
    ∑' I : Ideal O,∑' B : Ideal O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let f := fun H : Ideal O => (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    completedT Ψ W (X/(Ideal.absNorm H : ℝ)^3)
  have hf := cube_inverse_finite_support Ψ W hW X hX
  have hs : Summable (fun H : Ideal O => if (Ideal.absNorm H : ℝ)<H₀ then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  have hl : Summable (fun H : Ideal O => if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0) :=
    summable_of_hasFiniteSupport (hf.subset (by
      intro H hH
      by_contra hn
      have he : f H=0 := not_ne_iff.mp hn
      exact hH (by simp only [he,ite_self])))
  rw [completed_cube_inverse Ψ W hW X hX,←large_cube_reopen Ψ W hW X H₀ hX]
  change (∑' H,f H)=(∑' H,if (Ideal.absNorm H : ℝ)<H₀ then f H else 0)+
    ∑' H,if H₀ ≤ (Ideal.absNorm H : ℝ) then f H else 0
  rw [← hs.tsum_add hl]
  apply tsum_congr
  intro H
  by_cases h : (Ideal.absNorm H : ℝ)<H₀
  · simp [h,not_le.mpr h]
  · simp [h,le_of_not_gt h]

theorem large_cube_block_progress (H₀ B F : ℝ) (hB : 0 ≤ B) (hF : 1 ≤ F)
    (I : Ideal O) (hI : largeCubeCoefficient H₀ I ≠ 0) (hIB : (Ideal.absNorm I : ℝ) ≤ B) :
    H₀ ≤ B*F := by
  have hlarge := (largeCubeCoefficient_support H₀ I hI).2
  exact (hlarge.trans hIB).trans (le_mul_of_one_le_right hB hF)

end CompletedGauss

end

end OAI

end

