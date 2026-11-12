module

public import Green64.Library.Analysis.NumberTheory.DirichletL.QuadraticSieve.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CuspIntegration -/

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

def spatialTriple (x y v : ℝ) : SpatialCoordinates := ![x,y,v]
@[simp] lemma spatialTriple_zero (x y v : ℝ) : spatialTriple x y v 0=x := rfl
@[simp] lemma spatialTriple_one (x y v : ℝ) : spatialTriple x y v 1=y := rfl
@[simp] lemma spatialTriple_two (x y v : ℝ) : spatialTriple x y v 2=v := rfl

def cuspCylinderMeasure (a b : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (volume.restrict (Set.Icc a b)).prod
    ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod
      (volume.restrict (Set.Icc 0 3)))

def cuspBoxIntegral (a b : ℝ) (f : SpatialCoordinates → ℂ) : ℂ :=
  ∫q, f (spatialTriple q.2.2 q.2.1 q.1) ∂cuspCylinderMeasure a b

lemma continuous_spatialTriple {X : Type*} [TopologicalSpace X]
    {x y v : X → ℝ} (hx : Continuous x) (hy : Continuous y) (hv : Continuous v) :
    Continuous (fun p => spatialTriple (x p) (y p) (v p)) := by
  rw [continuous_pi_iff]
  intro j
  fin_cases j <;> assumption

lemma continuous_cuspBox_integrand (f : SpatialCoordinates → ℂ) (hf : Continuous f) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1)) :=
  hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) (by fun_prop))

lemma integrable_cuspBox (f : SpatialCoordinates → ℂ) (hf : Continuous f) (a b : ℝ) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  have h : IntegrableOn (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (Set.Icc a b ×ˢ (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3)) volume :=
    (continuous_cuspBox_integrand f hf).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  simpa only [cuspCylinderMeasure,Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using h

lemma cuspBoxIntegral_add (f g : SpatialCoordinates → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) : cuspBoxIntegral a b (fun p => f p+g p)=cuspBoxIntegral a b f+cuspBoxIntegral a b g :=
  integral_add (integrable_cuspBox f hf a b) (integrable_cuspBox g hg a b)
lemma cuspBoxIntegral_sub (f g : SpatialCoordinates → ℂ) (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) : cuspBoxIntegral a b (fun p => f p-g p)=cuspBoxIntegral a b f-cuspBoxIntegral a b g :=
  integral_sub (integrable_cuspBox f hf a b) (integrable_cuspBox g hg a b)
lemma cuspBoxIntegral_const_mul (c : ℂ) (f : SpatialCoordinates → ℂ) (a b : ℝ) :
    cuspBoxIntegral a b (fun p => c*f p)=c*cuspBoxIntegral a b f := integral_const_mul _ _

lemma cuspBoxIntegral_eq_iterated (f : SpatialCoordinates → ℂ) (hf : Continuous f)
    (a b : ℝ) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v) := by
  unfold cuspBoxIntegral cuspCylinderMeasure
  rw [integral_prod _ (integrable_cuspBox f hf a b)]
  have hY : (0:ℝ)≤3*Real.sqrt 3 := by positivity
  simp_rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hY,
    intervalIntegral.integral_of_le (show (0:ℝ)≤3 by norm_num),← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v => by
    have hc : Continuous (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v)) :=
      hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) continuous_const)
    have hi : IntegrableOn (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v))
        (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3) volume :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hi' : Integrable (fun q : ℝ×ℝ => f (spatialTriple q.2 q.1 v))
        ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3))) := by
      simpa only [Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using hi
    exact integral_prod _ hi')

lemma cuspBoxIntegral_eq_vertical (f : SpatialCoordinates → ℂ) (hf : Continuous f)
    (a b : ℝ) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, ∫v in a..b, f (spatialTriple x y v) := by
  unfold cuspBoxIntegral cuspCylinderMeasure
  rw [integral_prod_symm _ (integrable_cuspBox f hf a b)]
  have hc : Continuous (fun q : (ℝ×ℝ)×ℝ => f (spatialTriple q.1.2 q.1.1 q.2)) :=
    hf.comp (continuous_spatialTriple (by fun_prop) (by fun_prop) (by fun_prop))
  have hcI : Continuous (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v)) :=
    continuous_parametric_integral_of_continuous hc isCompact_Icc
  have hi : IntegrableOn (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v))
      (Set.Icc 0 (3*Real.sqrt 3) ×ˢ Set.Icc 0 3) volume :=
    hcI.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi' : Integrable (fun q : ℝ×ℝ => ∫v in Set.Icc a b, f (spatialTriple q.2 q.1 v))
      ((volume.restrict (Set.Icc 0 (3*Real.sqrt 3))).prod (volume.restrict (Set.Icc 0 3))) := by
    simpa only [Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using hi
  rw [integral_prod _ hi']
  have hY : (0:ℝ)≤3*Real.sqrt 3 := by positivity
  simp_rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hY,
    intervalIntegral.integral_of_le (show (0:ℝ)≤3 by norm_num),← integral_Icc_eq_integral_Ioc]

lemma rectangle_interval_swap (f : ℝ→ℝ→ℂ) (hf : Continuous f.uncurry) :
    (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f x y)=
      ∫x in (0:ℝ)..3, ∫y in (0:ℝ)..(3*Real.sqrt 3), f x y := by
  apply intervalIntegral_intervalIntegral_swap
  have hc : Continuous (Function.uncurry (fun y x => f x y)) := hf.comp continuous_swap
  exact (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

def greenSecondField (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  greenSecondTerm (axisSlice (upperEisensteinField s) p j)
    (axisSlice (upperEisensteinField t) p j) (p j)
def greenWronskianField (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenWronskian (axisSlice (upperEisensteinField s) p 2)
    (axisSlice (upperEisensteinField t) p 2) (p 2)
def greenAxisDensity (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) : ℂ :=
  greenSecondField s t j p/(p 2:ℂ)
def greenVerticalDensity (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenAxisDensity s t 2 p-greenWronskianField s t p/(p 2:ℂ)^2
def greenBoundaryFlux (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  greenWronskianField s t p/(p 2:ℂ)

def clampHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : SpatialCoordinates :=
  spatialTriple (p 0) (p 1) (max deltaLoss (p 2))
lemma clampHeight_continuous (deltaLoss : ℝ) : Continuous (clampHeight deltaLoss) :=
  continuous_spatialTriple (continuous_apply 0) (continuous_apply 1)
    (continuous_const.max (continuous_apply 2))
lemma clampHeight_eq (deltaLoss : ℝ) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) : clampHeight deltaLoss p=p := by
  ext j
  fin_cases j <;> simp [clampHeight,spatialTriple,max_eq_right hp]

def extendAboveHeight (deltaLoss : ℝ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) : ℂ :=
  f (clampHeight deltaLoss p)
lemma extendAboveHeight_continuous (deltaLoss : ℝ) (hδ : 0<deltaLoss) (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ ContinuousAt f p) : Continuous (extendAboveHeight deltaLoss f) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact (hf (clampHeight deltaLoss p) (lt_of_lt_of_le hδ (le_max_left _ _))).comp
    (clampHeight_continuous deltaLoss).continuousAt
lemma extendAboveHeight_eq (deltaLoss : ℝ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates)
    (hp : deltaLoss≤p 2) : extendAboveHeight deltaLoss f p=f p := by
  rw [extendAboveHeight,clampHeight_eq deltaLoss p hp]

lemma greenSecondField_update (s t : ℂ) (j : Fin 3) (p : SpatialCoordinates) (x : ℝ) :
    greenSecondField s t j (Function.update p j x)=
      greenSecondTerm (axisSlice (upperEisensteinField s) p j)
        (axisSlice (upperEisensteinField t) p j) x := by
  simp only [greenSecondField,axisSlice_update,Function.update_self]
lemma greenWronskianField_update (s t : ℂ) (p : SpatialCoordinates) (x : ℝ) :
    greenWronskianField s t (Function.update p 2 x)=
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) x := by
  simp only [greenWronskianField,axisSlice_update,Function.update_self]

lemma greenFields_continuousAt (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∀j,ContinuousAt (greenAxisDensity s t j) p) ∧
    ContinuousAt (greenVerticalDensity s t) p ∧ ContinuousAt (greenBoundaryFlux s t) p := by
  have hS := actual_spatial_continuousAt s hs p hv
  have hT := actual_spatial_continuousAt t ht p hv
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  have hn : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hG (j : Fin 3) : ContinuousAt (greenSecondField s t j) p := by
    unfold greenSecondField greenSecondTerm
    simp only [axisSlice_self]
    exact (((hS.2 j).2.mul hT.1.star).sub (hS.1.mul (hT.2 j).2.star))
  have hW : ContinuousAt (greenWronskianField s t) p := by
    unfold greenWronskianField greenWronskian
    simp only [axisSlice_self]
    exact (((hS.2 2).1.mul hT.1.star).sub (hS.1.mul (hT.2 2).1.star))
  exact ⟨fun j => (hG j).div hV hn,((hG 2).div hV hn).sub (hW.div (hV.pow 2) (pow_ne_zero 2 hn)),
    hW.div hV hn⟩

lemma actual_green_fields_density (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    greenAxisDensity s t 0 p+greenAxisDensity s t 1 p+greenVerticalDensity s t p=
      (s*(s-2)-star (t*(t-2)))*upperEisensteinField s p*star (upperEisensteinField t p)/(p 2:ℂ)^3 := by
  have h := actual_eisenstein_green_density s t hs ht p hv
  simp only [Fin.sum_univ_three,add_div] at h
  calc
    _ = _ := by
      unfold greenVerticalDensity greenAxisDensity greenSecondField greenWronskianField
      ring
    _ = _ := h

lemma spatialTriple_update_zero (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple 0 y v) 0 x := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]
lemma spatialTriple_update_one (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple x 0 v) 1 y := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]
lemma spatialTriple_update_two (x y v : ℝ) :
    spatialTriple x y v=Function.update (spatialTriple x y 0) 2 v := by
  ext j; fin_cases j <;> simp [spatialTriple,Function.update]

lemma actual_green_axis_zero_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (y v : ℝ) (hv : 0<v) :
    (∫x in (0:ℝ)..3, greenAxisDensity s t 0 (spatialTriple x y v))=0 := by
  have hf : (fun x => greenAxisDensity s t 0 (spatialTriple x y v))=
      (fun x => greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple 0 y v) 0)
        (axisSlice (upperEisensteinField t) (spatialTriple 0 y v) 0) x/(v:ℂ)) := by
    funext x
    unfold greenAxisDensity
    simp only [spatialTriple_two]
    rw [spatialTriple_update_zero,greenSecondField_update]
  rw [hf,intervalIntegral.integral_div]
  have h := actual_green_real_period_zero s t hs ht (spatialTriple 0 y v) hv
  simp only [greenSecondTerm,h,zero_div]

lemma actual_green_axis_one_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (x v : ℝ) (hv : 0<v) :
    (∫y in (0:ℝ)..(3*Real.sqrt 3), greenAxisDensity s t 1 (spatialTriple x y v))=0 := by
  have hf : (fun y => greenAxisDensity s t 1 (spatialTriple x y v))=
      (fun y => greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple x 0 v) 1)
        (axisSlice (upperEisensteinField t) (spatialTriple x 0 v) 1) y/(v:ℂ)) := by
    funext y
    unfold greenAxisDensity
    simp only [spatialTriple_two]
    rw [spatialTriple_update_one,greenSecondField_update]
  rw [hf,intervalIntegral.integral_div]
  have h := actual_green_imag_period_zero s t hs ht (spatialTriple x 0 v) hv
  simp only [greenSecondTerm,h,zero_div]

lemma actual_green_vertical_integral (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (x y a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫v in a..b, greenVerticalDensity s t (spatialTriple x y v))=
      greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  have hG (v : ℝ) : greenSecondField s t 2 (spatialTriple x y v)=
      greenSecondTerm (axisSlice (upperEisensteinField s) (spatialTriple x y 0) 2)
        (axisSlice (upperEisensteinField t) (spatialTriple x y 0) 2) v := by
    rw [spatialTriple_update_two,greenSecondField_update]
  have hW (v : ℝ) : greenWronskianField s t (spatialTriple x y v)=
      greenWronskian (axisSlice (upperEisensteinField s) (spatialTriple x y 0) 2)
        (axisSlice (upperEisensteinField t) (spatialTriple x y 0) 2) v := by
    rw [spatialTriple_update_two,greenWronskianField_update]
  simp only [greenVerticalDensity,greenAxisDensity,greenBoundaryFlux,spatialTriple_two,hG,hW]
  exact actual_eisenstein_vertical_green s t hs ht (spatialTriple x y 0) a b ha hb

lemma cuspCylinder_ae_height (a b : ℝ) :
    ∀ᵐq ∂cuspCylinderMeasure a b, q.1∈Set.Icc a b :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)

lemma cuspBoxIntegral_congr (a b : ℝ) (f g : SpatialCoordinates → ℂ)
    (heq : ∀p, p 2∈Set.Icc a b→f p=g p) :
    cuspBoxIntegral a b f=cuspBoxIntegral a b g := by
  apply integral_congr_ae
  filter_upwards [cuspCylinder_ae_height a b] with q hq
  exact heq (spatialTriple q.2.2 q.2.1 q.1) hq

lemma cuspBoxIntegral_extendAboveHeight (a b : ℝ) (f : SpatialCoordinates → ℂ) :
    cuspBoxIntegral a b (extendAboveHeight a f)=cuspBoxIntegral a b f :=
  cuspBoxIntegral_congr a b _ _ (fun p hp => extendAboveHeight_eq a f p hp.1)

lemma integrable_cuspBox_of_positive_continuity (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ ContinuousAt f p) (a b : ℝ) (ha : 0<a) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => f (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  have hi := integrable_cuspBox (extendAboveHeight a f) (extendAboveHeight_continuous a ha f hf) a b
  apply hi.congr
  filter_upwards [cuspCylinder_ae_height a b] with q hq
  exact extendAboveHeight_eq a f _ hq.1

lemma cuspBox_green_axis_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenAxisDensity s t 0))=0 := by
  let f := extendAboveHeight a (greenAxisDensity s t 0)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 0)
  rw [cuspBoxIntegral_eq_iterated _ hf a b hab]
  trans ∫v in a..b, (0:ℂ)
  · apply intervalIntegral.integral_congr
    intro v hv
    have hav : a≤v := by simpa only [min_eq_left hab,spatialTriple_two] using hv.1
    have hext (x y : ℝ) : f (spatialTriple x y v)=greenAxisDensity s t 0 (spatialTriple x y v) :=
      extendAboveHeight_eq a _ _ hav
    change (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v))=0
    simp_rw [hext,actual_green_axis_zero_integral s t hs ht _ v (lt_of_lt_of_le ha hav)]
    simp only [intervalIntegral.integral_zero]
  · simp only [intervalIntegral.integral_zero]

lemma cuspBox_green_axis_one (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenAxisDensity s t 1))=0 := by
  let f := extendAboveHeight a (greenAxisDensity s t 1)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 1)
  rw [cuspBoxIntegral_eq_iterated _ hf a b hab]
  trans ∫v in a..b, (0:ℂ)
  · apply intervalIntegral.integral_congr
    intro v hv
    have hav : a≤v := by simpa only [min_eq_left hab,spatialTriple_two] using hv.1
    have hext (x y : ℝ) : f (spatialTriple x y v)=greenAxisDensity s t 1 (spatialTriple x y v) :=
      extendAboveHeight_eq a _ _ hav
    change (∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v))=0
    rw [rectangle_interval_swap (fun x y => f (spatialTriple x y v))
      (hf.comp (continuous_spatialTriple continuous_fst continuous_snd continuous_const))]
    simp_rw [hext,actual_green_axis_one_integral s t hs ht _ v (lt_of_lt_of_le ha hav)]
    simp only [intervalIntegral.integral_zero]
  · simp only [intervalIntegral.integral_zero]

lemma cuspBox_green_vertical (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b (extendAboveHeight a (greenVerticalDensity s t))=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  let f := extendAboveHeight a (greenVerticalDensity s t)
  have hf : Continuous f := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).2.1)
  rw [cuspBoxIntegral_eq_vertical _ hf a b hab]
  apply intervalIntegral.integral_congr
  intro y hy
  apply intervalIntegral.integral_congr
  intro x hx
  calc
    _ = ∫v in a..b, greenVerticalDensity s t (spatialTriple x y v) := by
      apply intervalIntegral.integral_congr
      intro v hv
      exact extendAboveHeight_eq a _ _ (by simpa only [min_eq_left hab,spatialTriple_two] using hv.1)
    _ = _ := actual_green_vertical_integral s t hs ht x y a b ha (lt_of_lt_of_le ha hab)

def eisensteinHermitianDensity (s t : ℂ) (p : SpatialCoordinates) : ℂ :=
  upperEisensteinField s p*star (upperEisensteinField t p)/(p 2:ℂ)^3

lemma integrable_eisensteinHermitianDensity (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => eisensteinHermitianDensity s t (spatialTriple q.2.2 q.2.1 q.1))
      (cuspCylinderMeasure a b) := by
  apply integrable_cuspBox_of_positive_continuity _ _ a b ha
  intro p hp
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  exact (((actual_spatial_continuousAt s hs p hp).1).mul
    (actual_spatial_continuousAt t ht p hp).1.star).div (hV.pow 3)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem actual_eisenstein_cylinder_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (s*(s-2)-star (t*(t-2)))*cuspBoxIntegral a b (eisensteinHermitianDensity s t)=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  let f₀ := extendAboveHeight a (greenAxisDensity s t 0)
  let f₁ := extendAboveHeight a (greenAxisDensity s t 1)
  let f₂ := extendAboveHeight a (greenVerticalDensity s t)
  have h₀ : Continuous f₀ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 0)
  have h₁ : Continuous f₁ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).1 1)
  have h₂ : Continuous f₂ := extendAboveHeight_continuous a ha _ (fun p hp => (greenFields_continuousAt s t hs ht p hp).2.1)
  have hD : cuspBoxIntegral a b (fun p => f₀ p+f₁ p+f₂ p)=
      (s*(s-2)-star (t*(t-2)))*cuspBoxIntegral a b (eisensteinHermitianDensity s t) := by
    rw [← cuspBoxIntegral_const_mul]
    apply cuspBoxIntegral_congr
    intro p hp
    change extendAboveHeight a (greenAxisDensity s t 0) p+
      extendAboveHeight a (greenAxisDensity s t 1) p+
      extendAboveHeight a (greenVerticalDensity s t) p=_
    rw [extendAboveHeight_eq _ _ _ hp.1,extendAboveHeight_eq _ _ _ hp.1,extendAboveHeight_eq _ _ _ hp.1,
      actual_green_fields_density s t hs ht p (lt_of_lt_of_le ha hp.1)]
    unfold eisensteinHermitianDensity
    ring
  rw [← hD,cuspBoxIntegral_add (fun p => f₀ p+f₁ p) f₂ (h₀.add h₁) h₂,
    cuspBoxIntegral_add f₀ f₁ h₀ h₁]
  rw [cuspBox_green_axis_zero s t hs ht a b ha hab,cuspBox_green_axis_one s t hs ht a b ha hab,
    cuspBox_green_vertical s t hs ht a b ha hab]
  simp only [zero_add]

lemma cuspBoxIntegral_eq_iterated_positive (f : SpatialCoordinates → ℂ)
    (hf : ∀p,0<p 2→ ContinuousAt f p) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    cuspBoxIntegral a b f=
      ∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3, f (spatialTriple x y v) := by
  rw [← cuspBoxIntegral_extendAboveHeight a b f,
    cuspBoxIntegral_eq_iterated _ (extendAboveHeight_continuous a ha f hf) a b hab]
  apply intervalIntegral.integral_congr
  intro v hv
  have hav : a≤v := by simpa only [min_eq_left hab] using hv.1
  apply intervalIntegral.integral_congr
  intro y hy
  apply intervalIntegral.integral_congr
  intro x hx
  exact extendAboveHeight_eq a f _ hav

lemma eisensteinHermitianDensity_continuousAt (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContinuousAt (eisensteinHermitianDensity s t) p := by
  have hV : ContinuousAt (fun q : SpatialCoordinates => (q 2:ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp (continuous_apply 2).continuousAt
  exact (((actual_spatial_continuousAt s hs p hp).1).mul
    (actual_spatial_continuousAt t ht p hp).1.star).div (hV.pow 3)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem actual_eisenstein_cylinder_green_iterated (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (s*(s-2)-star (t*(t-2)))*
      (∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        upperEisensteinField s (spatialTriple x y v)*star (upperEisensteinField t (spatialTriple x y v))/(v:ℂ)^3)=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  have h := actual_eisenstein_cylinder_green s t hs ht a b ha hab
  rw [cuspBoxIntegral_eq_iterated_positive _
    (eisensteinHermitianDensity_continuousAt s t hs ht) a b ha hab] at h
  exact h

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_subtype_powerset_products (S : Finset (Ideal O)) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset S).powerset, f (∏ P ∈ E, P.val)) =
      ∑ E ∈ S.powerset, f (∏ P ∈ E, P) := by
  classical
  have hS : (Finset.univ : Finset S).image Subtype.val = S := by
    ext P
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, exists_prop,
      exists_eq_right]
  conv_rhs => rw [← hS, Finset.powerset_image]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro E hE
    congr 1
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => Subtype.val_injective h
  · exact fun _ _ _ _ h => Finset.image_injective Subtype.val_injective h

theorem primePool_singleton_eq_primeSupport (G : Ideal O) :
    primePool {G} = primeSupport G := by
  simp [primePool, primeSupport]

theorem primePool_subset_sum_eq_divisors (G : Ideal O) (hG : Squarefree G) (f : Ideal O → ℂ) :
    (∑ E ∈ (Finset.univ : Finset (primePool {G})).powerset,
      f (∏ P ∈ E, P.val)) = ∑ d ∈ idealDivisors G, f d := by
  rw [sum_subtype_powerset_products, primePool_singleton_eq_primeSupport]
  exact (squarefree_divisor_sum_eq_support G hG f).symm

theorem middleTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      (X : ℂ) * ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
            ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
              paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
        else 0 := by
  classical
  let f : Ideal O → ℂ := fun d =>
    if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) *
        ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊,
          paperRadialFourier W ((X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2)
    else 0
  change middleTruncation _ _ W X Y Z lengthScale = (X : ℂ) * ∑ d ∈ idealDivisors G, f d
  rw [← primePool_subset_sum_eq_divisors G hG f]
  unfold middleTruncation middleDivisors smallDivisors
  simp only [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [f, subsetNorm, subsetMobius]
  push_cast
  by_cases hY : Y < (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) <;>
    by_cases hZ : (Ideal.absNorm (∏ P ∈ E, P.val) : ℝ) ≤ Z <;> simp only [hY, hZ, and_self,
      false_and, and_false, ite_true, ite_false]

theorem middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) :
    middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((X / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_divisors G hG, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hc, and_self, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    have harg : (X / (Ideal.absNorm d : ℝ)) * ‖eisEmbedding h‖ ^ 2 =
        X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ) := by ring
    rw [harg]
    push_cast
    ring
  · simp only [hc, ite_false, mul_zero, Finset.sum_const_zero]

theorem principalTruncation_eq_ideal_divisors (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (X Z : ℝ) :
    principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      (X : ℂ) * paperRadialFourier W 0 *
        (∏ P : primePool {G}, (1 - (1 : ℂ) / Ideal.absNorm P.val)) -
      (X : ℂ) * paperRadialFourier W 0 *
        (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d : ℝ) then
          (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d : ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d : ℂ) else 0) := by
  classical
  rw [← primePool_subset_sum_eq_divisors G hG
    (fun d => if Z < (Ideal.absNorm d : ℝ) then
      (UniqueFactorizationMonoid.moebius d : ℂ) / (Ideal.absNorm d : ℂ) else 0),
    ← primePool_subset_sum_eq_divisors G hG
    (fun d => if (Ideal.absNorm d : ℝ) ≤ Z then (UniqueFactorizationMonoid.moebius d : ℂ) else 0)]
  unfold principalTruncation largeDivisors smallDivisors
  simp only [Finset.sum_filter, subsetNorm, subsetMobius, Complex.ofReal_natCast]

end

open ActualEisensteinCubic

theorem finite_middle_triangle
    {m n p H D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype H] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → H → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d‖ ≤
      ∑ h, ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k h d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ h, ∑ d, muCoefficient d * A i j k h d) =
      ∑ h, ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k h d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset m)) (t := (Finset.univ : Finset H)),
      Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h hh
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

theorem finite_nonzero_frequency_sum_le (H : Finset O) (hH : ∀ h ∈ H, h ≠ 0)
    (f : O → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hs : Summable (fun h : {h : O // h ≠ 0} => f h.val)) :
    (∑ h ∈ H, f h) ≤ ∑' h : {h : O // h ≠ 0}, f h.val := by
  classical
  let e : H → {h : O // h ≠ 0} := fun h => ⟨h.val, hH h.val h.property⟩
  have he : Function.Injective e := by
    intro h k hh
    apply Subtype.ext
    exact congrArg (fun x : {h : O // h ≠ 0} => x.val) hh
  have hsH : Summable (fun h : H => f h.val) :=
    summable_of_hasFiniteSupport (Set.toFinite _)
  have hb := hsH.tsum_le_tsum_of_inj e he (fun h _ => hf h.val) (fun _ => le_rfl) hs
  rw [tsum_fintype, Finset.sum_coe_sort H f] at hb
  exact hb

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem sum_two_finite_subtypes {α β A : Type*} [AddCommMonoid A]
    (S : Finset α) (T : Finset β) (f : α → β → A) :
    (∑ a : S, ∑ b : T, f a.val b.val) = ∑ a ∈ S, ∑ b ∈ T, f a b := by
  rw [Finset.sum_coe_sort S (fun a => ∑ b : T, f a b.val)]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_coe_sort T (f a))

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem original_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ left j * right k then
            originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ left j * right k then
          originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
        else 0 else 0))]
  by_cases hc : IsCoprime (left j) (right k)
  · have hsq : Squarefree (left j * right k) :=
      squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
    rw [middleTruncation_eq_ideal_frequencies _ hsq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K (left j * right k) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ left j * right k
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, originalPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h.val d.val i
      else 0 else 0
  have he : originalTruncatedMiddle W rows left right a b M Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold originalTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact original_truncated_pair_expansion W K rows left right a b M Y Z lengthScale hleft hright hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d.val i
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold originalProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.original_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    ‖originalTruncatedMiddle W rows left right a b M Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => left x.1 * right x.2
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1).1.1 (hright x.2).1.1
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ left j * right k) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.original_product_divisor_middle deltaLoss hδ ε hε K B N M U hB hN hM hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := (mem_rowNormDisk.mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, originalProductDivisorMiddleAt W K rows left right a b M P h :=
      originalTruncatedMiddle_le_product_divisors W K rows left right a b M Y Z lengthScale
        (fun j => (hleft j).1) (fun k => (hright k).1) hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, originalProductDivisorMiddleAt W K rows left right a b M P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => originalProductDivisorMiddleAt_nonneg W K rows left right a b M P h) hb.1
    _ ≤ _ := hb.2

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.SmoothCuspCutoffs -/

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

def cuspTransition (a b v : ℝ) : ℝ := Real.smoothTransition ((v-a)/(b-a))

lemma cuspTransition_contDiff (a b : ℝ) : ContDiff ℝ ∞ (cuspTransition a b) := by
  unfold cuspTransition
  fun_prop

lemma cuspTransition_zero (a b v : ℝ) (hab : a<b) (hv : v≤a) : cuspTransition a b v=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) (sub_pos.mpr hab).le)
lemma cuspTransition_one (a b v : ℝ) (hab : a<b) (hv : b≤v) : cuspTransition a b v=1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).mpr (by linarith))

lemma cuspTransition_derivatives (a b v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    deriv (cuspTransition a b) v=0 ∧ deriv (deriv (cuspTransition a b)) v=0 := by
  rcases hv with hv | hv
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspTransition_zero a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩
  · have heq : cuspTransition a b =ᶠ[𝓝 v] (fun _ => (1:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hv] with x hx
      exact cuspTransition_one a b x hab hx.le
    exact ⟨heq.deriv_eq.trans (deriv_const _ _),heq.deriv.deriv_eq.trans (by simp)⟩

def positiveHeightPower (s : ℂ) (v : ℝ) : ℂ := logRatioPower s v 1
lemma positiveHeightPower_eq_cpow (s : ℂ) (v : ℝ) (hv : 0<v) :
    positiveHeightPower s v=(v:ℂ)^s := by
  simpa only [positiveHeightPower,div_one] using logRatioPower_eq_cpow s hv (by norm_num : (0:ℝ)<1)

lemma positiveHeightPower_hasDerivAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (positiveHeightPower s) (positiveHeightPower s v*s/(v:ℂ)) v := by
  convert hasDerivAt_logRatioPower s (hasDerivAt_id v) (hasDerivAt_const v (1:ℝ)) hv one_ne_zero using 1
  · rfl
  · simp [positiveHeightPower,div_eq_mul_inv]

lemma positiveHeightPower_hasDerivAt_deriv (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (positiveHeightPower s))
      (positiveHeightPower s v*s*(s-1)/(v:ℂ)^2) v := by
  convert hasDerivAt_deriv_logRatioPower s id (fun _ => 1) (fun _ => 1) (fun _ => 0) v 0 0
    (fun x => hasDerivAt_id x) (fun x => hasDerivAt_const x (1:ℝ))
    (hasDerivAt_const v (1:ℝ)) (hasDerivAt_const v (0:ℝ)) hv one_ne_zero using 1
  · rfl
  · simp only [id_eq,zero_mul,mul_one,sub_self,sub_zero,one_pow,div_one,
      Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_pow,
      Complex.ofReal_zero,positiveHeightPower]
    field_simp [Complex.ofReal_ne_zero.mpr hv]
    ; ring

def cuspSeedProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  (cuspTransition a b v:ℂ)*positiveHeightPower s v

lemma cuspSeedProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v≤a) :
    cuspSeedProfile a b s v=0 := by simp [cuspSeedProfile,cuspTransition_zero a b v hab hv]
lemma cuspSeedProfile_incoming (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : b≤v) (hpos : 0<v) : cuspSeedProfile a b s v=(v:ℂ)^s := by
  simp [cuspSeedProfile,cuspTransition_one a b v hab hv,positiveHeightPower_eq_cpow s v hpos]

lemma cuspSeedProfile_hasDerivAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (cuspSeedProfile a b s)
      (((deriv (cuspTransition a b) v:ℝ):ℂ)*positiveHeightPower s v+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s/(v:ℂ))) v := by
  exact (((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp).mul
    (positiveHeightPower_hasDerivAt s v hv)

lemma cuspSeedProfile_hasDerivAt_deriv (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    HasDerivAt (deriv (cuspSeedProfile a b s))
      (((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)*positiveHeightPower s v+
        2*((deriv (cuspTransition a b) v:ℝ):ℂ)*(positiveHeightPower s v*s/(v:ℂ))+
        (cuspTransition a b v:ℂ)*(positiveHeightPower s v*s*(s-1)/(v:ℂ)^2)) v := by
  have hχ := ((cuspTransition_contDiff a b).differentiable (by simp) v).hasDerivAt.ofReal_comp
  have hdχ := (((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2).differentiable
    (by simp) v).hasDerivAt.ofReal_comp
  have hH := positiveHeightPower_hasDerivAt s v hv
  have hdH := positiveHeightPower_hasDerivAt_deriv s v hv
  have heq : deriv (cuspSeedProfile a b s) =ᶠ[𝓝 v]
      (fun x => ((deriv (cuspTransition a b) x:ℝ):ℂ)*positiveHeightPower s x+
        (cuspTransition a b x:ℂ)*deriv (positiveHeightPower s) x) := by
    filter_upwards [eventually_ne_nhds hv] with x hx
    rw [(cuspSeedProfile_hasDerivAt a b s x hx).deriv,(positiveHeightPower_hasDerivAt s x hx).deriv]
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (hdχ.mul hH).add (hχ.mul hdH) using 1
  · rw [hH.deriv]
    ring

def cuspSeedDefectProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v*((v:ℂ)^2*((deriv (deriv (cuspTransition a b)) v:ℝ):ℂ)+
    (2*s-1)*(v:ℂ)*((deriv (cuspTransition a b) v:ℝ):ℂ))

lemma cuspSeedProfile_laplace_defect (a b : ℝ) (s : ℂ) (v : ℝ) (hv : v≠0) :
    (v:ℂ)^2*deriv (deriv (cuspSeedProfile a b s)) v-
      (v:ℂ)*deriv (cuspSeedProfile a b s) v-s*(s-2)*cuspSeedProfile a b s v=
        cuspSeedDefectProfile a b s v := by
  rw [(cuspSeedProfile_hasDerivAt a b s v hv).deriv,(cuspSeedProfile_hasDerivAt_deriv a b s v hv).deriv]
  unfold cuspSeedDefectProfile cuspSeedProfile
  field_simp [Complex.ofReal_ne_zero.mpr hv]
  ; ring

lemma cuspSeedDefectProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ) (hab : a<b) (hv : v<a ∨ b<v) :
    cuspSeedDefectProfile a b s v=0 := by
  obtain ⟨h₁,h₂⟩ := cuspTransition_derivatives a b v hab hv
  simp [cuspSeedDefectProfile,h₁,h₂]

lemma cuspSeedDefectProfile_hasCompactSupport (a b : ℝ) (s : ℂ) (hab : a<b) :
    HasCompactSupport (cuspSeedDefectProfile a b s) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro v hv
  by_contra hn
  have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  exact hv (cuspSeedDefectProfile_zero a b s v hab hout)

def rowHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  p 2 / quadraticHeightDenominator (Complex.normSq (u 0)) (u 0*star (u 1)).re
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

lemma rowHeight_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    0< rowHeight u p := div_pos hp (row_denominator_pos u hu p hp)
lemma rowHeight_eq_transformedHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) :
    rowHeight u p=transformedHeight ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) u := by
  rw [transformedHeight,heightDenominator_eq_quadratic]
  rfl
lemma cosetHeight_upperPoint_rowHeight (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    cosetHeight r (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=rowHeight (embeddedRow r) p := by
  change (rowEnergy (rowOperator (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) (embeddedRow r)))⁻¹=_
  rw [rowEnergy_upperSection,inv_div,heightDenominator_eq_quadratic]
  rfl

lemma rowHeight_contDiffAt (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (rowHeight u) p := by
  have hq : ContDiffAt ℝ ∞
      (fun q : SpatialCoordinates => quadraticHeightDenominator (Complex.normSq (u 0))
        (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (q 0) (q 1) (q 2)) p := by
    unfold quadraticHeightDenominator
    fun_prop
  exact (show ContDiffAt ℝ ∞ (fun q : SpatialCoordinates => q 2) p by fun_prop).div hq
    (row_denominator_pos u hu p hp).ne'

lemma rowSmoothPower_eq_height (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) : rowSmoothPower s u p=(rowHeight u p:ℂ)^s :=
  logRatioPower_eq_cpow s hp (row_denominator_pos u hu p hp)

lemma norm_smoothSummand_three (r : CuspCosets) (p : SpatialCoordinates) (hp : 0<p 2) :
    ‖smoothSummand 3 r p‖=(rowHeight (embeddedRow r) p)^3 := by
  rw [smoothSummand,rowSmoothPower_eq_height 3 _ (embeddedRow_ne_zero r) p hp,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul]
  rw [show (3:ℂ)=(3:ℕ) by norm_num,Complex.cpow_natCast,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)]

lemma locally_finite_high_rows (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃U : Set SpatialCoordinates, IsOpen U ∧ p∈U ∧ ∃S : Finset CuspCosets,
      ∀q∈U, 0<q 2 ∧ ∀r∉S,rowHeight (embeddedRow r) q<1 := by
  obtain ⟨U,hU,hpU,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ :=
    spatial_summable_derivative_bounds 3 (by norm_num) p hp
  have hevent : ∀ᶠr in Filter.cofinite,M₀ r<1 :=
    hM₀.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  have hfinite : Set.Finite {r | ¬M₀ r<1} := Filter.eventually_cofinite.mp hevent
  refine ⟨U,hU,hpU,hfinite.toFinset,?_⟩
  intro q hq
  refine ⟨(hbound q hq).1,?_⟩
  intro r hr
  have hrM : M₀ r<1 := by simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,not_not] using hr
  have hnorm := ((hbound q hq).2 r).1
  rw [norm_smoothSummand_three r q (hbound q hq).1] at hnorm
  have hpos := (rowHeight_pos _ (embeddedRow_ne_zero r) q (hbound q hq).1).le
  nlinarith [sq_nonneg (rowHeight (embeddedRow r) q-1)]

def heightPoincareField (F : ℝ → ℂ) (p : SpatialCoordinates) : ℂ :=
  ∑'r : CuspCosets,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma heightPoincareField_locally_finite (F : ℝ → ℂ) (hF : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ∃S : Finset CuspCosets, heightPoincareField F =ᶠ[𝓝 p]
      (fun q => ∑r∈S,(cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) q)) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  refine ⟨S,?_⟩
  filter_upwards [hU.mem_nhds hpU] with q hq
  apply tsum_eq_sum
  intro r hr
  rw [hF _ ((hrows q hq).2 r hr).le,mul_zero]

lemma heightPoincareField_contDiffAt (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField F) p := by
  obtain ⟨S,hS⟩ := heightPoincareField_locally_finite F hzero p hp
  apply ContDiffAt.congr_of_eventuallyEq _ hS
  apply ContDiffAt.sum
  intro r hr
  exact contDiffAt_const.mul ((hF _ (rowHeight_pos _ (embeddedRow_ne_zero r) p hp)).comp p
    (rowHeight_contDiffAt _ (embeddedRow_ne_zero r) p hp))

lemma heightPoincareField_eq_cuspCorrection (F : ℝ → ℂ) (hzero : ∀v≤1,F v=0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    heightPoincareField F p=cuspCutoffCorrection 1 F
      (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) := by
  unfold heightPoincareField cuspCutoffCorrection
  apply tsum_congr
  intro r
  rw [cuspCutoffTerm,cosetHeight_upperPoint_rowHeight]
  split_ifs with h
  · rfl
  · rw [hzero _ (le_of_not_gt h),mul_zero]

open CubicKubota

lemma positiveHeightPower_contDiffAt (s : ℂ) (v : ℝ) (hv : v≠0) :
    ContDiffAt ℝ ∞ (positiveHeightPower s) v := by
  have hlog : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log x:ℂ)) v :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp v (Real.contDiffAt_log.mpr hv)
  have hs : ContDiffAt ℝ ∞ (fun x : ℝ => s*(Real.log x:ℂ)) v := contDiffAt_const.mul hlog
  unfold positiveHeightPower logRatioPower
  simpa only [Real.log_one,sub_zero] using hs.cexp

lemma cuspSeedProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedProfile a b s) v :=
  (Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspTransition_contDiff a b).contDiffAt).mul
    (positiveHeightPower_contDiffAt s v hv.ne')

lemma cuspSeedDefectProfile_contDiffAt (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ContDiffAt ℝ ∞ (cuspSeedDefectProfile a b s) v := by
  have hχ₁ : ContDiff ℝ ∞ (deriv (cuspTransition a b)) :=
    (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
  have hχ₂ : ContDiff ℝ ∞ (deriv (deriv (cuspTransition a b))) :=
    (contDiff_infty_iff_deriv.mp hχ₁).2
  have hd₁ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₁.contDiffAt
  have hd₂ := Complex.ofRealCLM.contDiff.contDiffAt.comp v hχ₂.contDiffAt
  have hid : ContDiffAt ℝ ∞ (fun x : ℝ => (x:ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt
  exact (positiveHeightPower_contDiffAt s v hv.ne').mul
    (((hid.pow 2).mul hd₂).add ((contDiffAt_const.mul hid).mul hd₁))

lemma cuspSeedDefectProfile_continuous (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Continuous (cuspSeedDefectProfile a b s) := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v<a
  · have heq : cuspSeedDefectProfile a b s =ᶠ[𝓝 v] (fun _ => (0:ℂ)) := by
      filter_upwards [Iio_mem_nhds hv] with x hx
      exact cuspSeedDefectProfile_zero a b s x hab (Or.inl hx)
    exact continuousAt_const.congr heq.symm
  · exact (cuspSeedDefectProfile_contDiffAt a b s v (lt_of_lt_of_le ha (le_of_not_gt hv))).continuousAt

lemma cuspSeedDefectProfile_integrable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Integrable (cuspSeedDefectProfile a b s) volume :=
  (cuspSeedDefectProfile_continuous a b s ha hab).integrable_of_hasCompactSupport
    (cuspSeedDefectProfile_hasCompactSupport a b s hab)

def smoothCuspSeed (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedProfile a b s)

def smoothCuspSeedDefect (a b : ℝ) (s : ℂ) : HyperbolicSpace → ℂ :=
  cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s)

lemma smoothCuspSeed_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeed a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeed a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w
lemma smoothCuspSeedDefect_automorphy (a b : ℝ) (s : ℂ) (M : levelThree) (w : HyperbolicSpace) :
    smoothCuspSeedDefect a b s (complexMatrix M • w)=complexCharacter M*smoothCuspSeedDefect a b s w :=
  cuspCutoffCorrection_automorphy 1 le_rfl _ M w

lemma smoothCuspSeed_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeed a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le)) p hp).symm
lemma smoothCuspSeedDefect_coordinate (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefect a b s (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp)=
      heightPoincareField (cuspSeedDefectProfile a b s) p :=
  (heightPoincareField_eq_cuspCorrection _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha))) p hp).symm

lemma smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedProfile a b s)) p :=
  heightPoincareField_contDiffAt _ (fun v hv => cuspSeedProfile_zero a b s v hab (hv.trans ha.le))
    (cuspSeedProfile_contDiffAt a b s) p hp
lemma smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (heightPoincareField (cuspSeedDefectProfile a b s)) p :=
  heightPoincareField_contDiffAt _
    (fun v hv => cuspSeedDefectProfile_zero a b s v hab (Or.inl (lt_of_le_of_lt hv ha)))
    (cuspSeedDefectProfile_contDiffAt a b s) p hp

lemma cuspCutoffCorrection_upperPoint (F : ℝ → ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) (h1v : 1<v) :
    cuspCutoffCorrection 1 F (upperPoint z v hv)=F v := by
  have hh : cosetHeight (cosetOf 1) (upperPoint z v hv)=v := by
    rw [cosetHeight_cosetOf,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [cuspCutoffCorrection_eq 1 le_rfl _ _ (cosetOf 1) (hh.symm ▸ h1v),hh,
    cosetCharacter_cosetOf,map_one,inv_one,one_mul]

lemma smoothCuspSeed_incoming (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b≤v) :
    smoothCuspSeed a b s (upperPoint z v hv)=(v:ℂ)^s := by
  rw [smoothCuspSeed,cuspCutoffCorrection_upperPoint _ z v hv (lt_of_lt_of_le (ha.trans hab) hbv)]
  exact cuspSeedProfile_incoming a b s v hab hbv hv

lemma smoothCuspSeedDefect_support (a b : ℝ) (s : ℂ) (hab : a<b) (w : HyperbolicSpace)
    (hw : smoothCuspSeedDefect a b s w≠0) :
    ∃r : CuspCosets, a≤ cosetHeight r w ∧ cosetHeight r w≤b := by
  by_contra hn
  apply hw
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  calc
    _ = ∑'r : CuspCosets, (0:ℂ) := by
      apply tsum_congr
      intro r
      have hout : cosetHeight r w<a ∨ b<cosetHeight r w := by
        have h := not_exists.mp hn r
        simpa only [not_and_or,not_le] using h
      simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
    _ = 0 := tsum_zero

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def rowLogHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  Real.log (p 2)-Real.log (quadraticHeightDenominator (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2))

lemma exp_rowLogHeight (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    Real.exp (rowLogHeight u p)=rowHeight u p := by
  rw [rowLogHeight,Real.exp_sub,Real.exp_log hp,Real.exp_log (row_denominator_pos u hu p hp)]
  rfl

lemma hasDerivAt_deriv_log_ratio (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t,HasDerivAt f (df t) t) (hg : ∀t,HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x≠0) (hg0 : g x≠0) :
    HasDerivAt (deriv (fun t => Real.log (f t)-Real.log (g t)))
      ((ddf*f x-df x*df x)/(f x)^2-(ddg*g x-dg x*dg x)/(g x)^2) x := by
  have heq : deriv (fun t => Real.log (f t)-Real.log (g t)) =ᶠ[𝓝 x]
      (fun t => df t/f t-dg t/g t) := by
    filter_upwards [((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)] with t ht
    exact (((hf t).log ht.1).sub ((hg t).log ht.2)).deriv
  exact ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).congr_of_eventuallyEq heq

lemma rowLogHeight_hasDerivAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (fun t => rowLogHeight u (Function.update p j t)) (rowLogD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := ((hasDerivAt_const (p 0) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_const (p 1) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_id (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDv,Function.update,A,B,C,D,Pi.sub_def] using! h

lemma rowLogHeight_hasDerivAt_deriv (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (fun t => rowLogHeight u (Function.update p j t))) (rowLogDD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDxx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDyy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio id
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDvv,Function.update,A,B,C,D,div_eq_mul_inv] using h

lemma complex_profile_second_chain (F : ℝ → ℂ) (g : ℝ → ℝ) (x dg ddg : ℝ) (dF ddF : ℂ)
    (hg : HasDerivAt g dg x) (hdg : HasDerivAt (deriv g) ddg x)
    (hF : HasDerivAt F dF (g x)) (hdF : HasDerivAt (deriv F) ddF (g x))
    (hlocal : ∀ᶠy in 𝓝 x,DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ F (g y)) :
    HasDerivAt (deriv (fun y => F (g y))) (ddF*(dg:ℂ)^2+dF*(ddg:ℂ)) x := by
  have heq : deriv (fun y => F (g y)) =ᶠ[𝓝 x]
      (fun y => (deriv g y:ℝ) • deriv F (g y)) := by
    filter_upwards [hlocal] with y hy
    exact (hy.2.hasDerivAt.scomp y hy.1.hasDerivAt).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert hdg.smul (hdF.scomp x hg) using 1
  · rfl
  · simp only [Function.comp_apply,hg.deriv,hF.deriv,Complex.real_smul]
    ring

lemma positiveProfile_differentiable (F : ℝ → ℂ)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (v : ℝ) (hv : 0<v) :
    DifferentiableAt ℝ F v ∧ DifferentiableAt ℝ (deriv F) v :=
  ⟨(hF v hv).differentiableAt (by simp),
    ((hF v hv).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma positiveProfile_exp_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (t : ℝ) :
    HasDerivAt (fun y => F (Real.exp y))
      (deriv F (Real.exp t)*(Real.exp t:ℂ)) t ∧
    HasDerivAt (deriv (fun y => F (Real.exp y)))
      (deriv (deriv F) (Real.exp t)*(Real.exp t:ℂ)^2+
        deriv F (Real.exp t)*(Real.exp t:ℂ)) t := by
  have hdf := positiveProfile_differentiable F hF (Real.exp t) (Real.exp_pos t)
  constructor
  · simpa only [Complex.real_smul,mul_comm,Function.comp_def] using! hdf.1.hasDerivAt.scomp t (Real.hasDerivAt_exp t)
  · apply complex_profile_second_chain F Real.exp t (Real.exp t) (Real.exp t)
      (deriv F (Real.exp t)) (deriv (deriv F) (Real.exp t)) (Real.hasDerivAt_exp t)
      (by simpa only [Real.deriv_exp] using Real.hasDerivAt_exp t) hdf.1.hasDerivAt hdf.2.hasDerivAt
    exact Filter.Eventually.of_forall (fun y =>
      ⟨Real.differentiable_exp y,(positiveProfile_differentiable F hF _ (Real.exp_pos y)).1⟩)

lemma rowProfile_axis_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (fun q => F (rowHeight u q)) p j)
      (deriv F (rowHeight u p)*(rowHeight u p:ℂ)*(rowLogD u p j:ℂ)) (p j) ∧
    HasDerivAt (deriv (axisSlice (fun q => F (rowHeight u q)) p j))
      (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2*(rowLogD u p j:ℂ)^2+
       deriv F (rowHeight u p)*(rowHeight u p:ℂ)*
        ((rowLogD u p j:ℂ)^2+(rowLogDD u p j:ℂ))) (p j) := by
  let g : ℝ → ℝ := fun t => rowLogHeight u (Function.update p j t)
  let G : ℝ → ℂ := fun t => F (Real.exp t)
  have hg : HasDerivAt g (rowLogD u p j) (p j) := rowLogHeight_hasDerivAt u hu p hp j
  have hdg : HasDerivAt (deriv g) (rowLogDD u p j) (p j) := rowLogHeight_hasDerivAt_deriv u hu p hp j
  have hgval : g (p j)=rowLogHeight u p := by simp [g,Function.update_eq_self]
  have hexp : Real.exp (g (p j))=rowHeight u p := by rw [hgval,exp_rowLogHeight u hu p hp]
  have hG := positiveProfile_exp_derivatives F hF (g (p j))
  have hnear : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 :=
    ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
      (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
  have heq : axisSlice (fun q => F (rowHeight u q)) p j =ᶠ[𝓝 (p j)] (fun t => G (g t)) := by
    filter_upwards [hnear] with t ht
    change F (rowHeight u (Function.update p j t))=F (Real.exp (rowLogHeight u (Function.update p j t)))
    rw [exp_rowLogHeight u hu _ ht]
  constructor
  · have hh := hG.1.scomp (p j) hg
    apply HasDerivAt.congr_of_eventuallyEq _ heq
    convert hh using 1
    · rfl
    · simp only [Complex.real_smul,hexp]
      ring
  · have hlocal : ∀ᶠy in 𝓝 (p j),DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ G (g y) := by
      filter_upwards [hnear] with y hy
      constructor
      · have h := rowLogHeight_hasDerivAt u hu (Function.update p j y) hy j
        simpa only [Function.update_idem,Function.update_self] using h.differentiableAt
      · exact (positiveProfile_exp_derivatives F hF (g y)).1.differentiableAt
    have hh := complex_profile_second_chain G g (p j) (rowLogD u p j) (rowLogDD u p j)
      _ _ hg hdg hG.1 hG.2 hlocal
    apply HasDerivAt.congr_of_eventuallyEq _ heq.deriv
    convert hh using 1
    · rw [hexp]
      ring

lemma rowLog_eikonal (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*((rowLogD u p 0)^2+(rowLogD u p 1)^2+(rowLogD u p 2)^2)=1 := by
  exact heightLog_eikonal _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'
lemma rowLog_laplacian (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*(rowLogDD u p 0+rowLogDD u p 1+rowLogDD u p 2)-(p 2)*rowLogD u p 2= -2 := by
  exact heightLog_laplacian _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'

theorem rowProfile_laplacian (F : ℝ → ℂ) (hF : ∀v,0<v→ ContDiffAt ℝ ∞ F v)
    (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => F (rowHeight u q)) p=
      (rowHeight u p:ℂ)^2*deriv (deriv F) (rowHeight u p)-(rowHeight u p:ℂ)*deriv F (rowHeight u p) := by
  have hp0 := rowProfile_axis_derivatives F hF u hu p hp 0
  have hp1 := rowProfile_axis_derivatives F hF u hu p hp 1
  have hp2 := rowProfile_axis_derivatives F hF u hu p hp 2
  unfold axisLaplacian
  rw [Fin.sum_univ_three,hp0.2.deriv,hp1.2.deriv,hp2.2.deriv,hp2.1.deriv]
  have hE := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_eikonal u hu p hp)
  have hD := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_laplacian u hu p hp)
  push_cast at hE hD
  linear_combination
    (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2+
      deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hE+
    (deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hD

open Filter
open scoped BigOperators Classical Topology ContDiff

lemma axisLaplacian_congr_eventuallyEq (f g : SpatialCoordinates → ℂ) (p : SpatialCoordinates)
    (heq : f =ᶠ[𝓝 p] g) : axisLaplacian f p=axisLaplacian g p := by
  have haxis (j : Fin 3) : axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
    have ht : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 p) := by
      have h : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 (Function.update p j (p j))) :=
        (continuous_axis_update p j).continuousAt
      simpa only [Function.update_eq_self] using h
    exact heq.comp_tendsto ht
  unfold axisLaplacian
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => (haxis j).deriv.deriv_eq)
  · rw [(haxis 2).deriv_eq]

lemma axisLaplacian_const_mul (c : ℂ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c*f q) p=c*axisLaplacian f p := by
  unfold axisLaplacian
  simp only [Fin.sum_univ_three]
  unfold axisSlice
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

lemma axisLaplacian_finset_sum {ι : Type*} (S : Finset ι) (f : ι → SpatialCoordinates → ℂ)
    (hreg : ∀i∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f i) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f i) q j)) (q j))
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => ∑i∈S,f i q) p=∑i∈S,axisLaplacian (f i) p := by
  have hpair (j : Fin 3) :
      deriv (axisSlice (fun q => ∑i∈S,f i q) p j) (p j)=∑i∈S,deriv (axisSlice (f i) p j) (p j) ∧
      deriv (deriv (axisSlice (fun q => ∑i∈S,f i q) p j)) (p j)=
        ∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j) := by
    have hfirst (x : ℝ) (hx : 0<(Function.update p j x) 2) :
        HasDerivAt (axisSlice (fun q => ∑i∈S,f i q) p j)
          (∑i∈S,deriv (axisSlice (f i) p j) x) x := by
      have hi (i : ι) (hiS : i∈S) : DifferentiableAt ℝ (axisSlice (f i) p j) x := by
        simpa only [axisSlice_update,Function.update_self] using (hreg i hiS (Function.update p j x) hx j).1
      convert HasDerivAt.sum (fun i hiS => (hi i hiS).hasDerivAt) using 1
      ext y
      simp only [axisSlice,Finset.sum_apply]
    have hnear : ∀ᶠx in 𝓝 (p j),0<(Function.update p j x) 2 :=
      ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
        (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
    have heq : deriv (axisSlice (fun q => ∑i∈S,f i q) p j) =ᶠ[𝓝 (p j)]
        (fun x => ∑i∈S,deriv (axisSlice (f i) p j) x) := by
      filter_upwards [hnear] with x hx
      exact (hfirst x hx).deriv
    have hsecond : HasDerivAt (deriv (axisSlice (fun q => ∑i∈S,f i q) p j))
        (∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j)) (p j) := by
      apply (HasDerivAt.sum (fun i hiS => (hreg i hiS p hp j).2.hasDerivAt)).congr_of_eventuallyEq
      filter_upwards [heq] with x hx
      simpa only [Finset.sum_apply] using hx
    exact ⟨(hfirst (p j) (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)).deriv,hsecond.deriv⟩
  unfold axisLaplacian
  simp_rw [(hpair _).1,(hpair _).2]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,Finset.sum_sub_distrib]

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.DualMiddleExpansion -/

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
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem scaled_middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Y Z lengthScale : ℝ) :
    (c : ℂ) * middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            ((((c * X) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_frequencies G hG]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hp, and_self, ite_true]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

theorem dual_normalized_middle_expansion (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (M F b i j Y Z lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    ((M / (Real.sqrt (i * j) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {G} => P.val) Finset.univ W
        (Real.sqrt (F * i * j / (M * b))) Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((Real.sqrt ((M / F) / b) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W
                (Real.sqrt (F * i * j / (M * b)) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  rw [scaled_middleTruncation_eq_ideal_frequencies G hG,
    dual_principal_prefactor_identity M F b i j hM hF hb hi hj]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hrows : ∀ i, Admissible (rows i))
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
        middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
          (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
            (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale) =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ left j * right k then
            originalTerm rows left right a b 1 1 i j k *
              dualPrincipalKernel W rows left right M F h.val d.val i j k
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ left j * right k then
          originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
        else 0 else 0))]
  by_cases hc : IsCoprime (left j) (right k)
  · have hsq : Squarefree (left j * right k) :=
      squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
    have hpos (I : Ideal O) (hI : Admissible I) : 0 < (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hI.1 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [dual_normalized_middle_expansion _ hsq _ _ _ _ _ _ _ _ _ hM hF
      (hpos _ (hrows i)) (hpos _ (hleft j)) (hpos _ (hright k)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K (left j * right k) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ left j * right k
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, dualPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hrows : ∀ i, Admissible (rows i))
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h.val d.val i j k
      else 0 else 0
  have he : dualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold dualTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact dual_truncated_pair_expansion W K rows left right a b M F Y Z lengthScale hM hF hrows hleft hright hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d.val i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold dualProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => left x.1 * right x.2
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1).1.1 (hright x.2).1.1
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ left j * right k) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.dual_product_divisor_middle deltaLoss hδ ε hε K B N M F U hB hN hM hF hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := (mem_rowNormDisk.mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F P h :=
      dualTruncatedMiddle_le_product_divisors W K rows left right a b M F Y Z lengthScale hM hF (fun i => (hrows i).1)
        (fun j => (hleft j).1) (fun k => (hright k).1) hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, dualProductDivisorMiddleAt W K rows left right a b M F P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => dualProductDivisorMiddleAt_nonneg W K rows left right a b M F P h) hb.1
    _ ≤ _ := hb.2

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel primeProduct bit)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem primeSpanProduct_squarefree (S : Finset ι) :
    Squarefree (∏ i ∈ S, Ideal.span {p i}) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance).squarefree

omit [DecidableEq ι] in
theorem row_nonzero_notMem (S : Finset ι) (c : O)
    (h : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ≠ 0) :
    ∀ i ∈ S, c ∉ Ideal.span {p i} := by
  intro i hi hc
  have hzero : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 6 = 0 := by
    rw [← FirstPassCubeLabels.row_pow, finiteSquarefreeRow_sixth_power, ite_eq_left ⟨i,hi,hc⟩]
  exact pow_ne_zero 6 h hzero

omit [DecidableEq ι] in
theorem primeSpanProduct_isCoprime_of_row_nonzero (S : Finset ι) (c : O)
    (h : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ≠ 0) :
    IsCoprime (∏ i ∈ S, Ideal.span {p i}) (Ideal.span {c}) := by
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : (Ideal.span {p i}).IsMaximal)
    htop (show Ideal.span {p i} ≤ Ideal.span {p i} ⊔ Ideal.span {c} from le_sup_left)
  have hc : c ∈ Ideal.span {p i} := by
    rw [he]
    exact (show Ideal.span {c} ≤ Ideal.span {p i} ⊔ Ideal.span {c} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton c))
  exact row_nonzero_notMem p hg S c h i hi hc

def firstRetainedSupport (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun i => FirstPassCubeLabels.retained (FirstPassCubeLabels.parity (v i)) (ε₁ i) (ε₂ i))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem jLabel_eq_retainedProduct (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    jLabel p B v ε₁ ε₂ = ∏ i ∈ firstRetainedSupport B v ε₁ ε₂, p i := by
  unfold jLabel primeProduct firstRetainedSupport
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  cases hb : FirstPassCubeLabels.retained (FirstPassCubeLabels.parity (v i)) (ε₁ i) (ε₂ i) <;> simp [bit,hb]

include hcop in
theorem firstBaseLabel_squarefree (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hCB : Disjoint C B) :
    Squarefree (Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B v ε₁ ε₂}) := by
  have hCJ : Disjoint C (firstRetainedSupport B v ε₁ ε₂) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hCB
  rw [← Ideal.span_singleton_mul_span_singleton, jLabel_eq_retainedProduct,
    FiniteGaussPhase.span_finset_prod, primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
    ← Finset.prod_union hCJ]
  exact primeSpanProduct_squarefree p hcop _

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondArithmeticWeight (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
    secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap)

theorem secondArithmeticWeight_coprime (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (h : secondArithmeticWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    IsCoprime (Ideal.span {c}) (∏ i ∈ x.divisor, Ideal.span {p i}) ∧
    IsCoprime (Ideal.span {c}) (∏ i ∈ x.overlap, Ideal.span {p i}) ∧
    IsCoprime (∏ i ∈ x.divisor, Ideal.span {p i}) (∏ i ∈ x.overlap, Ideal.span {p i}) := by
  have hG : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.sourceCommon c ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondSourceCommonCoefficient, secondInputCoefficient,
      hz, zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Complex.ofReal_zero]
  have hV : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.overlap c ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondTotalWeight, secondCommonWeight, secondPreColumn,
      hz, zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, star_zero]
  have hVe : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.overlap
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondTotalWeight, secondCommonWeight, secondPreColumn,
      hz, mul_zero, zero_mul, star_zero]
  have hGc := primeSpanProduct_isCoprime_of_row_nonzero p hg x.sourceCommon c hG
  have hEc : IsCoprime (∏ i ∈ x.divisor, Ideal.span {p i}) (Ideal.span {c}) := by
    apply IsCoprime.prod_left
    intro i hi
    exact (IsCoprime.prod_left_iff.mp hGc) i (hE hi)
  have hVc := primeSpanProduct_isCoprime_of_row_nonzero p hg x.overlap c hV
  have hVE := primeSpanProduct_isCoprime_of_row_nonzero p hg x.overlap _ hVe
  rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator] at hVE
  exact ⟨hEc.symm,hVc.symm,hVE.symm⟩

theorem secondArithmeticWeight_squarefree (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hc : Squarefree (Ideal.span {c}))
    (h : secondArithmeticWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    Squarefree (Ideal.span {c} * (∏ i ∈ x.divisor, Ideal.span {p i}) *
      (∏ i ∈ x.overlap, Ideal.span {p i})) := by
  obtain ⟨hcE,hcV,hEV⟩ := secondArithmeticWeight_coprime p hp hcop hg Ψ m c d z x hE h
  apply squarefree_mul_iff.mpr
  refine ⟨(hcV.mul_left hEV).isRelPrime,?_,primeSpanProduct_squarefree p hcop _⟩
  exact squarefree_mul_iff.mpr ⟨hcE.isRelPrime,hc,primeSpanProduct_squarefree p hcop _⟩

theorem actualSecondLabel_squarefree_of_weight
    (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B)
    (Ψ : O →* ℂ) (m d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (h : secondArithmeticWeight p hp hcop hg Ψ m
      (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
        jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) d z x ≠ 0) :
    Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂) := by
  have hs := secondArithmeticWeight_squarefree p hp hcop hg Ψ m _ d z x hE
    (firstBaseLabel_squarefree p hcop B C (fun i => v₁ i+v₂ i) ε₁ ε₂ hCB) h
  rw [← Ideal.span_singleton_mul_span_singleton, primeSubsetGenerator,
    ConcretePrimeRowBridge.span_idealGenerator, mul_comm (∏ i ∈ C, Ideal.span {p i})] at hs
  exact hs

theorem secondExpansionSource_eq_squarefree
    (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B)
    (F : Finset ι) (Ψ : O →* ℂ) (m d : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂
    secondExpansionSource p hp hcop hg F Ψ m c d z s H₁ H₂ W Y =
    secondExpansionSource p hp hcop hg F Ψ m c d z
      (s.filter (fun x => Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂)))
      H₁ H₂ W Y := by
  dsimp only
  unfold secondExpansionSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂)
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs]
    have hw : secondArithmeticWeight p hp hcop hg Ψ m
        (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
          jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) d z x = 0 := by
      by_contra hn
      exact hs (actualSecondLabel_squarefree_of_weight p hp hcop hg B C v₁ v₂ ε₁ ε₂ hCB
        Ψ m d z x (hE x hx) hn)
    unfold secondArithmeticWeight at hw
    rcases mul_eq_zero.mp hw with hA | hB
    · rw [hA]
      ring
    · rw [hB]
      ring

end

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy childGeometricMean childEnergy)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondLogNormalizedEnergy (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) : ℝ :=
  densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
    (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
    (secondLogX p R X j) (secondLogX p R X j) J /
  (secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)

lemma secondLogNormalizedEnergy_nonneg
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    0 ≤ secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
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

lemma secondLogNormalizedEnergy_empty
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ)
    (hT : secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j = ∅) :
    secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J = 0 := by
  simp only [secondLogNormalizedEnergy, hT, densityChildEnergy, childGeometricMean, childEnergy,
    Finset.sum_empty, Finset.sum_const_zero, Real.sqrt_zero, mul_zero, integral_zero, zero_div]

theorem secondLog_normalized_cost
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X Y M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    (Y*primeProductNorm p R/X^2) *
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
        (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
        (secondLogX p R X j) (secondLogX p R X j) J =
    (Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X) *
      secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  unfold secondLogNormalizedEnergy
  rw [secondLogX_label_cost]
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hc := (zero_lt_one.trans_le (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))).ne'
  have hcn : ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖ ≠ 0 := by
    intro h; apply hc; rw [h]; norm_num
  field_simp

include hp in

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_second_normalized_child_cost
    (A B C R : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (X Y : ℝ) (hX : 0 < X) (j : SecondLogIndex) :
    (primeProductNorm p A)⁻¹ *
      (Y*primeProductNorm p R/(X/primeProductNorm p A)^2) *
      (secondLogX p R (X/primeProductNorm p A) j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j) =
    Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X := by
  rw [secondLogX_label_cost]
  have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp A).ne'
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  field_simp

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem secondBinnedIndex_mass (F : Finset ι) (U Kmax : ℝ) :
    (∑ z : SecondRayIndex, ∑ _R ∈ boundedPrimeSupports p F U,
      ∑ _j ∈ secondLogBinBox U Kmax, ‖secondRayCoefficient z‖) ≤
    (512*32^2) * (128*max 1 U) *
      (((normLogBin U+1)^2*(normLogBin Kmax+1) : ℕ) : ℝ) := by
  have hsub : boundedPrimeSupports p F U ⊆ boundedPrimeSupports p F (max 1 U) := by
    intro R hR
    obtain ⟨hR,hN⟩ := Finset.mem_filter.mp hR
    exact Finset.mem_filter.mpr ⟨hR,hN.trans (le_max_right _ _)⟩
  have hc : ((boundedPrimeSupports p F U).card : ℝ) ≤ 128*max 1 U := by
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (boundedPrimeSupports_card p hinj F (max 1 U) (le_max_left _ _))
  have he : (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F U,
      ∑ j ∈ secondLogBinBox U Kmax, ‖secondRayCoefficient z‖) =
      (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) *
        (boundedPrimeSupports p F U).card * (secondLogBinBox U Kmax).card := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_mul]
    ring_nf
  rw [he, secondLogBinBox_card]
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul secondRayCoefficient_mass hc (by positivity) (by positivity)
  · positivity

end SecondPassArithmetic

namespace FirstPassCubeLabels
open scoped BigOperators
open MeasureTheory

lemma firstLogDensity_pair_moment (J : ℕ) (t : ℝ) :
    firstLogDensity (2*(J+2)) t * ((1+‖t‖)^(J+2) * (1+‖t‖)^(J+2)) = firstLogDensity 0 t := by
  rw [← pow_add, show J+2+(J+2)=2*(J+2) by omega, mul_comm]
  exact JointLogSeparation.density_weight_identity _ _

lemma firstLogDensity_le_zero (J : ℕ) (t : ℝ) : firstLogDensity J t ≤ firstLogDensity 0 t := by
  have h := pow_le_pow_right₀ (show 1 ≤ 1+‖t‖ by linarith [norm_nonneg t]) (show 2 ≤ J+2 by omega)
  apply inv_anti₀ (by positivity : 0 < (1+‖t‖)^2) h

lemma integral_pair_moment_bound (J : ℕ) (f : ℝ → ℝ)
    (hf : Integrable (fun t => firstLogDensity (2*(J+2)) t * f t))
    (a d c q : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (h : ∀ t, f t ≤ a*(d + ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*c + q)) :
    (∫ t, firstLogDensity (2*(J+2)) t * f t) ≤
      (∫ t, firstLogDensity 0 t) * a * (d+c+q) := by
  have hi := (firstLogDensity_integrable 0).mul_const (a*(d+c+q))
  have hm : ∀ t, firstLogDensity (2*(J+2)) t * f t ≤ firstLogDensity 0 t*(a*(d+c+q)) := by
    intro t
    apply (mul_le_mul_of_nonneg_left (h t) (firstLogDensity_nonneg _ _)).trans
    have h1 := mul_le_mul_of_nonneg_right (firstLogDensity_le_zero (2*(J+2)) t) (mul_nonneg ha hd)
    have h2 := mul_le_mul_of_nonneg_right (firstLogDensity_le_zero (2*(J+2)) t) (mul_nonneg ha hq)
    have he := firstLogDensity_pair_moment J t
    calc
      _ = firstLogDensity (2*(J+2)) t*(a*d) +
          (firstLogDensity (2*(J+2)) t*((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2)))*(a*c) +
          firstLogDensity (2*(J+2)) t*(a*q) := by ring
      _ ≤ firstLogDensity 0 t*(a*d) + firstLogDensity 0 t*(a*c) + firstLogDensity 0 t*(a*q) := by
        rw [he]
        exact add_le_add (add_le_add h1 le_rfl) h2
      _ = _ := by ring
  have hh := integral_mono hf hi hm
  rw [integral_mul_const] at hh
  simpa only [mul_assoc] using hh

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_binned_integrated_transfer
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
                (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,hpoint⟩ :=
    firstCoreInputRow_binned_finite_transfer p hp hcop hg hinj hc hpr U hUc hUs
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
      (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  let child := ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
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

