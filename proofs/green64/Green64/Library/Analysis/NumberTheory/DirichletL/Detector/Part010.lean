module

public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part021
public import Mathlib.MeasureTheory.Integral.Prod
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Detector / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Detector.InitialScales -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

def sourceScale (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)

lemma sourceMellinWeight_eq_scale (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z=sourceScale X Y Z x w z*profile W0 W1 x w z := by
  unfold sourceMellinWeight sourceScale profile
  ring

lemma sourceScale_continuous (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Continuous (fun q : (ℂ × ℂ) × ℂ =>sourceScale X Y Z q.1.1 q.1.2 q.2) := by
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceScale
  exact (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>(1/2:ℂ)-q.2)).const_cpow (Or.inl hx)).mul
    (((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>q.1.1+q.2-1)).const_cpow (Or.inl hz)))) |>.mul
      ((by fun_prop : Continuous (fun q : (ℂ × ℂ) × ℂ =>q.1.2-1)).const_cpow (Or.inl hy))

lemma sourceScale_norm (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    ‖sourceScale X Y Z x w z‖=X^(1/2-z.re)*Z^(x.re+z.re-1)*Y^(w.re-1) := by
  simp only [sourceScale,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
    Complex.norm_cpow_eq_rpow_re_of_pos hY,Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  norm_num [Complex.sub_re,Complex.add_re]

theorem sourceMellinWeight_initial_integrable (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Integrable (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  let G := fun p : HeightSpace=>sourceScale X Y Z
    ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)
  have hc0 := (sourceScale_continuous X Y Z hX hY hZ).comp
    (show Continuous (fun p : HeightSpace=>(((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),
      (ξ:ℂ)+p.1.2*Complex.I)) by fun_prop)
  have hc : Continuous G := by simpa only [G,Function.comp_def] using hc0
  have hb (p : HeightSpace) : ‖G p‖≤(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))*jointHeight p.1.1 p.1.2 p.2^0 := by
    simp only [G,sourceScale_norm X Y Z hX hY hZ]
    simp
  simpa only [sourceMellinWeight_eq_scale,onLines,G] using
    profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 σ ξ υ hξ G
      hc.aestronglyMeasurable _ 0 hb

lemma sourceMellinWeight_initial_continuous (W0 W1 : SchwartzMap ℝ ℂ)
    (a1 b1 : ℝ) (ha1 : 0<a1) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ ξ υ : ℝ) (hξ : 0<ξ) :
    Continuous (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I)) := by
  have hc := (sourceScale_continuous X Y Z hX hY hZ).comp
    (show Continuous (fun p : HeightSpace=>(((σ:ℂ)+p.1.1*Complex.I,(υ:ℂ)+p.2*Complex.I),
      (ξ:ℂ)+p.1.2*Complex.I)) by fun_prop)
  simpa only [Function.comp_def,Pi.mul_def,sourceMellinWeight_eq_scale,onLines] using
    hc.mul (onLines_continuous W0 W1 a1 b1 ha1 hW1 σ ξ υ hξ)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.InitialFubini -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

theorem source_initial_integral_tsum (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    (∫p : HeightSpace,∑'i : FullHighIndex, initialHighOnLines S D η mask σ υ ξ i p*
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
      ∑'i : FullHighIndex, ∫p : HeightSpace,initialHighOnLines S D η mask σ υ ξ i p*
        sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  exact initialHigh_integral_tsum_test S D η mask hm σ υ ξ hσ hυ hξ _
    (sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ σ ξ υ (by linarith))

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.ContourShear -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

def sourceHeightShear : HeightSpace ≃ᵐ HeightSpace where
  toFun p := ((p.1.1+p.1.2,p.1.2),p.2)
  invFun p := ((p.1.1-p.1.2,p.1.2),p.2)
  left_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  right_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  measurable_toFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1+p.1.2,p.1.2),p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1-p.1.2,p.1.2),p.2))
    fun_prop

lemma sourceHeightShear_preserving : MeasurePreserving sourceHeightShear heightMeasure heightMeasure := by
  exact (measurePreserving_add_prod (volume:Measure ℝ) volume).prod (MeasurePreserving.id volume)

lemma sourceHeightShear_integral (F : HeightSpace→ℂ) :
    (∫p,F (sourceHeightShear p) ∂heightMeasure)=∫p,F p ∂heightMeasure :=
  sourceHeightShear_preserving.integral_comp' F

theorem source_contour_shear (F : ℂ→ℂ→ℂ→ℂ) (σ ξ υ : ℝ) :
    (∫p : HeightSpace,F (((σ:ℂ)+p.1.1*Complex.I)+((ξ:ℂ)+p.1.2*Complex.I)-1)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure)=
    ∫p : HeightSpace,F (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I)
      ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I) ∂heightMeasure := by
  have hh := sourceHeightShear_integral (fun p : HeightSpace=>F
    (((σ+ξ-1:ℝ):ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((ξ:ℂ)+p.1.2*Complex.I))
  convert hh using 1
  congr 1
  funext p
  dsimp only [sourceHeightShear,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
  congr 2 ; push_cast ; ring

lemma sourceMellinWeight_shear (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z (t+1-z) w z=
      (X:ℂ)^(1/2-z)*(Z:ℂ)^t*(Y:ℂ)^(w-1)*Complex.exp (t^2)*
        mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w := by
  simp only [sourceMellinWeight,show t+1-z+z-1=t by ring]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.InitialSubseries -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

abbrev RawHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×Ideal O)

def rawHighEmbedding (p : RawHighIndex) : FullHighIndex := (p.1,(p.2.1,(p.2.2,1)))

lemma rawHighEmbedding_injective : Function.Injective rawHighEmbedding := by
  rintro ⟨h,⟨ij,k⟩⟩ ⟨h',⟨ij',k'⟩⟩ he
  simpa only [rawHighEmbedding,Prod.mk.injEq,and_true] using he

theorem initialHigh_integral_tsum_subseries {ι : Type*} [Countable ι]
    (e : ι→FullHighIndex) (he : Function.Injective e)
    (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) :
    (∫p,∑'i : ι, initialHighOnLines S D η mask σ υ ξ (e i) p*T p ∂heightMeasure)=
      ∑'i : ι, ∫p,initialHighOnLines S D η mask σ υ ξ (e i) p*T p ∂heightMeasure := by
  let F := fun i p=>initialHighOnLines S D η mask σ υ ξ (e i) p*T p
  have hb (i : ι) (p : HeightSpace) :
      ‖F i p‖≤ initialHighMajorant σ υ ξ (e i)*‖T p‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (initialHighOnLines_norm_le S D η mask hm σ υ ξ (e i) p) (norm_nonneg _)
  have hF (i : ι) : Integrable (F i) heightMeasure := by
    apply (hT.norm.const_mul (initialHighMajorant σ υ ξ (e i))).mono'
    · exact (initialHighOnLines_continuous S D η mask σ υ ξ (e i)).aestronglyMeasurable.mul hT.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hb i)
  have hsum : Summable (fun i : ι=>∫p,‖F i p‖ ∂heightMeasure) := by
    apply Summable.of_nonneg_of_le (fun i=>integral_nonneg (fun _=>norm_nonneg _))
      (fun i=>?_) (((initialHighMajorant_summable σ υ ξ hσ hυ hξ).comp_injective he).mul_right
        (∫p,‖T p‖ ∂heightMeasure))
    rw [←integral_const_mul]
    exact integral_mono (hF i).norm (hT.norm.const_mul _) (hb i)
  exact (integral_tsum_of_summable_integral_norm hF hsum).symm

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.InitialProduct -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O

theorem initialHigh_counting_product_integrable {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (e : ι→FullHighIndex) (he : Function.Injective e)
    (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) (hcT : Continuous T) :
    Integrable (fun p : ι×HeightSpace=>initialHighOnLines S D η mask σ υ ξ (e p.1) p.2*T p.2)
      ((Measure.count:Measure ι).prod heightMeasure) := by
  have hb : Integrable (fun i : ι=>initialHighMajorant σ υ ξ (e i)) Measure.count := by
    rw [integrable_count_iff]
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (initialHighMajorant_nonneg _ _ _ _)] using
      (initialHighMajorant_summable σ υ ξ hσ hυ hξ).comp_injective he
  apply (hb.mul_prod hT.norm).mono'
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro i
    exact ((initialHighOnLines_continuous S D η mask σ υ ξ (e i)).mul hcT).measurable
  · apply Filter.Eventually.of_forall
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (initialHighOnLines_norm_le S D η mask hm σ υ ξ (e p.1) p.2) (norm_nonneg _)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.OuterMellin -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss

lemma outer_source_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hr : 0< r) :
    W r=verticalIntegral σ (fun w=>(r:ℂ)^(-w)*mellin W w) := by
  simpa only [verticalIntegral,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,
    Complex.ofReal_ofNat] using compactMellin_inversion W a b ha hW (W.smooth (⊤:ℕ∞)) σ r hr

lemma outer_source_scaled_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ N Y : ℝ) (hN : 0<N) (hY : 0<Y) :
    (Y:ℂ)⁻¹*W (N/Y)=
      verticalIntegral σ (fun w=>(Y:ℂ)^(w-1)*(N:ℂ)^(-w)*mellin W w) := by
  rw [outer_source_vertical_inverse W a b ha hW σ (N/Y) (div_pos hN hY)]
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he (w : ℂ) : (Y:ℂ)⁻¹*((N/Y:ℝ):ℂ)^(-w)=(Y:ℂ)^(w-1)*(N:ℂ)^(-w) := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hN.le hY.le,div_eq_mul_inv,
      ←Complex.cpow_neg,neg_neg]
    rw [show w-1=(-1)+w by ring,Complex.cpow_add _ _ hy,Complex.cpow_neg_one]
    ring
  unfold verticalIntegral
  simp_rw [←he,mul_assoc,integral_const_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.NestedMellin -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def nestedMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      verticalIntegral υ (fun w=>(Y:ℂ)^(w-1)*(qs:ℂ)^(-w)*mellin W1 w*
        (CanonicalRowCompletion.idealRowHom C.generator s.val /
          (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ)))*
        verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
          ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
            (elementNorm C.generator*qs*X) ξ t p.1 p.2))
    else 0

lemma verticalIntegral_mul_const (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun s=>F s*c)=verticalIntegral σ F*c := by
  unfold verticalIntegral
  rw [integral_mul_const,mul_assoc]

theorem markedPhysicalProbe_eq_nested_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hξ : 1<ξ) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      nestedMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z ξ υ := by
  rw [markedPhysicalProbe_eq_radial_mellin η S hS hSne D W0 W1 a0 b0 ha0 hW0 X Y Z ξ hX hZ hξ]
  unfold radialMellinPhysicalProbe nestedMellinPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    rw [verticalIntegral_mul_const,verticalIntegral_mul_const,
      ←outer_source_scaled_inverse W1 a1 b1 ha1 hW1 υ (Ideal.absNorm s.val:ℝ) Y
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)) hY]
    ring
  · simp only [mul_zero]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RawMellinTerm -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def rawPhysicalMellinTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (H : O) (t w z : ℂ) : ℂ :=
  physicalMellinCoefficientTerm η C S D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) X H t z *fullIdealWeight w K*
    (Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*mellin (paperRadialFourier W0) z*mellin W1 w

theorem rawPhysicalMellinTerm_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D I J K : Ideal O) (hK : Supported K)
    (hKS : ∀P∈S,¬P∣K) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (H : NonzeroFrequency) (t w z : ℂ) :
    rawPhysicalMellinTerm η (calibrationForSet S hS) S D I J K hK W0 W1 X Y Z H.val t w z=
      sourceMellinWeight W0 W1 X Y Z (t+1-z) w z *
        fullHighCoefficient S D η (fun h=>star ((calibrationForSet S hS).residueMonoid h.val))
          (t+1-z) w z (rawHighEmbedding (H,((I,J),K))) := by
  have hcs : IsCoprime (calibrationForSet S hS).generator (primaryGenerator K) := by
    apply calibrationForSet_coprime_of_excluded S hS
    rw [(primaryGenerator_spec K (supported_primaryGenerator_ne_zero K hK)).1]
    exact hKS
  unfold rawPhysicalMellinTerm
  rw [physicalMellinCoefficientTerm_eq_guarded η S hS hbad D I J (primaryGenerator K)
    ((supported_span_primaryGenerator_iff K).mpr hK) hcs X hX H.val H.property t z,
    guardedHighMellinCoefficient_eq_high η (calibrationForSet S hS) S hpS D I J K hK hKS X H.val
      (t+1-z) w z,sourceMellinWeight_shear]
  simp only [fullHighCoefficient,frequencyWeight,rawHighEmbedding]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RawPhysicalIntegral -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def SourceRawIndex (S : Finset (Ideal O)) :=
  {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}

instance (S : Finset (Ideal O)) : Countable (SourceRawIndex S) := inferInstanceAs (Countable {_p : RawHighIndex // _})

def sourceRawEmbedding (S : Finset (Ideal O)) (i : SourceRawIndex S) : FullHighIndex :=
  rawHighEmbedding i.val

lemma sourceRawEmbedding_injective (S : Finset (Ideal O)) : Function.Injective (sourceRawEmbedding S) :=
  rawHighEmbedding_injective.comp Subtype.val_injective

def originalRawOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  rawPhysicalMellinTerm η (calibrationForSet S hS) S D i.val.2.1.1 i.val.2.1.2 i.val.2.2 i.property.1
    W0 W1 X Y Z i.val.1.val ((4:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

theorem originalRaw_counting_product_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=>originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  let mask := fun H : NonzeroFrequency=>star ((calibrationForSet S hS).residueMonoid H.val)
  have hm (H : NonzeroFrequency) : ‖mask H‖≤1 := by
    simpa only [mask,norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  let T := fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
  have hT : Integrable T heightMeasure := sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ 3 2 3 (by norm_num)
  have hcT : Continuous T := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ 3 2 3 (by norm_num)
  have hi := initialHigh_counting_product_integrable (sourceRawEmbedding S) (sourceRawEmbedding_injective S)
    S D η mask hm 3 3 2 (by norm_num) (by norm_num) (by norm_num) T hT hcT
  have hp := (MeasurePreserving.id (Measure.count:Measure (SourceRawIndex S))).prod
    (sourceHeightShear_preserving.symm sourceHeightShear)
  have hh := hp.integrable_comp_of_integrable hi
  apply hh.congr
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [Function.comp_def,Prod.map]
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ p.1.property.1
    p.1.property.2 W0 W1 X Y Z hX p.1.val.1]
  have he : (4:ℂ)+p.2.1.1*Complex.I+1-((2:ℂ)+p.2.1.2*Complex.I)=
      3+((p.2.1.1-p.2.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hsh : sourceHeightShear.symm p.2=((p.2.1.1-p.2.1.2,p.2.1.2),p.2.2) := rfl
  simp only [he,initialHighOnLines,T,hsh,sourceRawEmbedding,mask,id_eq,Complex.ofReal_ofNat]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MixedFubini -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

lemma count_product {A B : Type*} [Countable A] [Countable B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count:Measure A).prod (Measure.count:Measure B)=Measure.count := by
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  rw [←Set.singleton_prod_singleton,Measure.prod_prod]
  simp

lemma count_equiv_preserving {A B : Type*} [Countable A] [Countable B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (e : A≃ᵐB) : MeasurePreserving e Measure.count Measure.count := by
  refine ⟨e.measurable,?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply e.measurable (measurableSet_singleton b)]
  have he : e ⁻¹' {b}={e.symm b} := by ext a;simp [e.eq_symm_apply]
  rw [he]
  simp

def quadShuffle {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D) where
  toFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  invFun p := ((p.1.1,p.2.1),(p.1.2,p.2.2))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by change Measurable (fun p : (A×B)×(C×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop
  measurable_invFun := by change Measurable (fun p : (A×C)×(B×D)=>((p.1.1,p.2.1),(p.1.2,p.2.2)));fun_prop

lemma quadShuffle_preserving {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μA : Measure A) (μB : Measure B)
    (μC : Measure C) (μD : Measure D) [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (quadShuffle : (A×B)×(C×D) ≃ᵐ (A×C)×(B×D))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 := (MeasurePreserving.id μA).prod ((measurePreserving_prodAssoc μB μC μD).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ:=μB) (ν:=μC)).prod (MeasurePreserving.id μD))
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

def physicalNestingEquiv {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F] :
    (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))) where
  toFun p := (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2)))))
  invFun p := ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1))
  left_inv p := rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun p : (A×(B×C))×((D×E)×F)=>
      (p.1.1,(p.2.2,(p.2.1.1,(p.1.2.1,(p.2.1.2,p.1.2.2))))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : A×(F×(D×(B×(E×C))))=>
      ((p.1,(p.2.2.2.1,p.2.2.2.2.2)),((p.2.2.1,p.2.2.2.2.1),p.2.1)))
    fun_prop

lemma physicalNesting_preserving {A B C D E F : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E] [MeasurableSpace F]
    (μA : Measure A) (μB : Measure B) (μC : Measure C)
    (μD : Measure D) (μE : Measure E) (μF : Measure F)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] [SFinite μE] [SFinite μF] :
    MeasurePreserving (physicalNestingEquiv : (A×(B×C))×((D×E)×F) ≃ᵐ A×(F×(D×(B×(E×C)))))
      ((μA.prod (μB.prod μC)).prod ((μD.prod μE).prod μF))
      (μA.prod (μF.prod (μD.prod (μB.prod (μE.prod μC))))) := by
  have h1 := measurePreserving_prodAssoc μA (μB.prod μC) ((μD.prod μE).prod μF)
  have hr := (Measure.measurePreserving_swap (μ:=(μB.prod μC).prod (μD.prod μE)) (ν:=μF)).comp
    ((measurePreserving_prodAssoc (μB.prod μC) (μD.prod μE) μF).symm MeasurableEquiv.prodAssoc)
  have hq := quadShuffle_preserving μB μC μD μE
  have hs := (Measure.measurePreserving_swap (μ:=μB) (ν:=μD)).prod
    (Measure.measurePreserving_swap (μ:=μC) (ν:=μE))
  have ha := measurePreserving_prodAssoc μD μB (μE.prod μC)
  exact ((MeasurePreserving.id μA).prod
    (((MeasurePreserving.id μF).prod (ha.comp (hs.comp hq))).comp hr)).comp h1

lemma integral_count_eq_tsum {A : Type*} [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A→ℂ) (hf : Integrable f Measure.count) :
    (∫a,f a ∂Measure.count)=∑'a,f a := by
  simpa using integral_countable hf

theorem integral_physical_nesting {A B C : Type*} [Countable A] [Countable B] [Countable C]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (F : A×(ℝ×(ℝ×(B×(ℝ×C))))→ℂ)
    (hF : Integrable F ((Measure.count:Measure A).prod (volume.prod (volume.prod
      ((Measure.count:Measure B).prod (volume.prod (Measure.count:Measure C))))))) :
    (∫p,F p ∂((Measure.count:Measure A).prod (volume.prod (volume.prod
      ((Measure.count:Measure B).prod (volume.prod (Measure.count:Measure C)))))))=
      ∑'a : A,∫w : ℝ,∫t : ℝ,∑'b : B,∫z : ℝ,∑'c : C,F (a,(w,(t,(b,(z,c))))) := by
  rw [integral_prod _ hF,integral_count_eq_tsum _ hF.integral_prod_left]
  apply tsum_congr
  intro a
  have ha := (Measure.ae_count_iff.mp hF.prod_right_ae) a
  rw [integral_prod _ ha]
  apply integral_congr_ae
  filter_upwards [ha.prod_right_ae] with w hw
  rw [integral_prod _ hw]
  apply integral_congr_ae
  filter_upwards [hw.prod_right_ae] with t ht
  rw [integral_prod _ ht,integral_count_eq_tsum _ ht.integral_prod_left]
  apply tsum_congr
  intro b
  have hb := (Measure.ae_count_iff.mp ht.prod_right_ae) b
  rw [integral_prod _ hb]
  apply integral_congr_ae
  filter_upwards [hb.prod_right_ae] with z hz
  exact integral_count_eq_tsum _ hz

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RawIndexGrouping -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

abbrev SourceOuter (S : Finset (Ideal O)) := {K : Ideal O // Supported K ∧ ∀P∈S,¬P∣K}
abbrev CompletedPair := Ideal O×Ideal O

def sourceRawGrouping (S : Finset (Ideal O)) :
    SourceRawIndex S ≃ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toFun i := (⟨i.val.2.2,i.property⟩,(i.val.2.1,i.val.1))
  invFun i := ⟨(i.2.2,(i.2.1,i.1.val)),i.1.property⟩
  left_inv _i := rfl
  right_inv _i := rfl

def sourceRawGroupingMeasurable (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    SourceRawIndex S ≃ᵐ SourceOuter S×(CompletedPair×NonzeroFrequency) where
  toEquiv := sourceRawGrouping S
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

lemma sourceRawGrouping_preserving (S : Finset (Ideal O))
    [MeasurableSpace (SourceRawIndex S)] [MeasurableSingletonClass (SourceRawIndex S)]
    [MeasurableSpace (SourceOuter S)] [MeasurableSingletonClass (SourceOuter S)]
    [MeasurableSpace CompletedPair] [MeasurableSingletonClass CompletedPair]
    [MeasurableSpace NonzeroFrequency] [MeasurableSingletonClass NonzeroFrequency] :
    MeasurePreserving (sourceRawGroupingMeasurable S) Measure.count
      ((Measure.count:Measure (SourceOuter S)).prod
        ((Measure.count:Measure CompletedPair).prod (Measure.count:Measure NonzeroFrequency))) := by
  rw [count_product,count_product]
  exact count_equiv_preserving _

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.OuterIndex -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def sourceOuterEquiv (S : Finset (Ideal O)) : SourceOuter S ≃
    {K : {I : Ideal O // Supported I} // ∀P∈S,¬P∣K.val} where
  toFun K := ⟨⟨K.val,K.property.1⟩,K.property.2⟩
  invFun K := ⟨K.val.val,K.val.property,K.property⟩
  left_inv _K := rfl
  right_inv _K := rfl

lemma sourceOuter_tsum (S : Finset (Ideal O)) (f : {I : Ideal O // Supported I}→ℂ) :
    (∑'K : {I : Ideal O // Supported I},if ∀P∈S,¬P∣K.val then f K else 0)=
      ∑'K : SourceOuter S,f ⟨K.val,K.property.1⟩ := by
  have hs := tsum_subtype {K : {I : Ideal O // Supported I} | ∀P∈S,¬P∣K.val} f
  have he := (sourceOuterEquiv S).tsum_eq (fun K=>f K.val)
  calc
    _ = ∑' K : {I : Ideal O // Supported I},
        Set.indicator {K | ∀ P ∈ S, ¬P ∣ K.val} f K := by
      apply tsum_congr
      intro K
      simp only [Set.indicator, Set.mem_ofPred_eq]
      split_ifs <;> rfl
    _ = _ := hs.symm.trans he.symm

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RawArithmetic -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def rawArithmeticSeries (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) : ℂ :=
  ∑'p : RawHighIndex,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
    x w z (rawHighEmbedding p)

lemma rawHighCoefficient_outer_support (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : RawHighIndex)
    (hp : fullHighCoefficient S D η mask x w z (rawHighEmbedding p)≠0) :
    Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2 := by
  have hb : bareIdealHighCoefficient η p.1.val p.2.1.1 p.2.1.2 p.2.2 1≠0 := by
    intro hz
    exact hp (by simp only [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,bareIdealHighSummand,hz,mul_zero,zero_mul])
  have hs : Supported p.2.2 := by
    unfold bareIdealHighCoefficient at hb
    split_ifs at hb with hh
    · exact hh.2.2.2.1
    · exact False.elim (hb rfl)
  refine ⟨hs,?_⟩
  by_contra hn
  exact hp (by simp [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,highIdealMask,hn])

lemma rawArithmeticSeries_eq_sourceRaw (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) :
    rawArithmeticSeries S D η C x w z=
      ∑'i : SourceRawIndex S,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
        x w z (sourceRawEmbedding S i) := by
  unfold rawArithmeticSeries sourceRawEmbedding
  change _ = ∑'i : {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}, _
  symm
  apply tsum_subtype_eq_of_support_subset (f:=fun p : RawHighIndex=>
    fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val)) x w z (rawHighEmbedding p))
    (s:={p : RawHighIndex | Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2})
  intro p hp
  exact rawHighCoefficient_outer_support S D η _ x w z p hp

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RawNesting -/

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance : MeasurableSpace O := ⊤
local instance : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Ideal O) := ⊤
local instance : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩

local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

abbrev PhysicalNestedSpace (S : Finset (Ideal O)) := SourceOuter S×(ℝ×(ℝ×(CompletedPair×(ℝ×NonzeroFrequency))))

def physicalRawNesting (S : Finset (Ideal O)) : SourceRawIndex S×HeightSpace ≃ᵐ PhysicalNestedSpace S :=
  ((sourceRawGroupingMeasurable S).prodCongr (MeasurableEquiv.refl HeightSpace)).trans physicalNestingEquiv

lemma physicalRawNesting_preserving (S : Finset (Ideal O)) :
    MeasurePreserving (physicalRawNesting S)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
        ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
  exact (physicalNesting_preserving Measure.count Measure.count Measure.count volume volume volume).comp
    ((sourceRawGrouping_preserving S).prod (MeasurePreserving.id heightMeasure))

def originalNestedOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (p : PhysicalNestedSpace S) : ℂ :=
  originalRawOnLines η S hS D W0 W1 X Y Z
    ⟨(p.2.2.2.2.2,(p.2.2.2.1,p.1.val)),p.1.property⟩ ((p.2.2.1,p.2.2.2.2.1),p.2.1)

theorem originalRaw_integral_eq_nesting (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
    ∑'K : SourceOuter S,∫w : ℝ,∫t : ℝ,∑'IJ : CompletedPair,∫z : ℝ,∑'H : NonzeroFrequency,
      originalNestedOnLines η S hS D W0 W1 X Y Z (K,(w,(t,(IJ,(z,H))))) := by
  have hi := originalRaw_counting_product_integrable η S hS hpS hbad D W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hp := physicalRawNesting_preserving S
  have hj := (hp.symm (physicalRawNesting S)).integrable_comp_of_integrable hi
  have he := hp.integral_comp' (originalNestedOnLines η S hS D W0 W1 X Y Z)
  have he' : (∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure))=
      ∫p : PhysicalNestedSpace S,originalNestedOnLines η S hS D W0 W1 X Y Z p
        ∂((Measure.count:Measure (SourceOuter S)).prod (volume.prod (volume.prod
          ((Measure.count:Measure CompletedPair).prod (volume.prod (Measure.count:Measure NonzeroFrequency)))))) := by
    exact he
  rw [he']
  apply integral_physical_nesting
  exact hj

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RawRadialJoin -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion ProbeCompleted ProbeRow CubicEisenstein
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma verticalIntegral_const_mul (σ : ℝ) (F : ℂ→ℂ) (c : ℂ) :
    verticalIntegral σ (fun z=>c*F z)=c*verticalIntegral σ F := by
  unfold verticalIntegral
  rw [integral_const_mul]
  ring

def rawRadialOuterFactor (C : CalibrationData) (K : Ideal O)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (t w : ℂ) : ℂ :=
  (Y:ℂ)^(w-1)*fullIdealWeight w K*mellin W1 w*
    (idealRowHom C.generator K /
      (C.tau*C.residueMonoid (primaryGenerator K)*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)))*
    (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))

lemma rawPhysicalMellinTerm_radial_join (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D I J K : Ideal O) (hK : Supported K)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ : ℝ) (t w : ℂ) :
    verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C S D I J K hK W0 W1 X Y Z H.val t w z)=
    rawRadialOuterFactor C K W1 X Y Z t w*
      radialMellinSpectralTerm η C S D (primaryGenerator K)
        ((supported_span_primaryGenerator_iff K).mpr hK) W0
          (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X) ξ t I J := by
  have hgen := (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K hK)).1
  have hn : elementNorm (primaryGenerator K)=(Ideal.absNorm K:ℝ) := by
    unfold elementNorm
    rw [hgen]
  unfold rawPhysicalMellinTerm physicalMellinCoefficientTerm radialMellinSpectralTerm
  split_ifs with hA
  · dsimp only
    simp only [hn,hgen]
    let c := rawRadialOuterFactor C K W1 X Y Z t w *
      (spectralSummand S D (baseRowCoefficient η C.Xi (primaryGenerator K)
        ((supported_span_primaryGenerator_iff K).mpr hK)) t I J *
        ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X/elementNorm (C.generator*completedIndex I J):ℝ):ℂ))
    have hp (z : ℂ) (H : NonzeroFrequency) :
        idealRowHom C.generator K /
          (C.tau*C.residueMonoid (primaryGenerator K)*
            (Real.sqrt (elementNorm C.generator*(Ideal.absNorm K:ℝ)*X):ℂ)) *
          (Real.sqrt (Ideal.absNorm K):ℂ)⁻¹ *
          spectralSummand S D (baseRowCoefficient η C.Xi (primaryGenerator K)
            ((supported_span_primaryGenerator_iff K).mpr hK)) t I J *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
          actualCongruenceCoefficient C (completedIndex I J) (primaryGenerator K) hA H.val *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X*elementNorm H.val /
            elementNorm ((C.generator*completedIndex I J)*primaryGenerator K):ℝ):ℂ)^(-z) *
          fullIdealWeight w K*(Y:ℂ)^(w-1)*(Z:ℂ)^t*Complex.exp (t^2)*
          mellin (paperRadialFourier W0) z*mellin W1 w =
        c*(actualCongruenceCoefficient C (completedIndex I J) (primaryGenerator K) hA H.val *
          ((elementNorm C.generator*(Ideal.absNorm K:ℝ)*X*elementNorm H.val /
            elementNorm ((C.generator*completedIndex I J)*primaryGenerator K):ℝ):ℂ)^(-z)*
          mellin (paperRadialFourier W0) z) := by
      dsimp only [c,rawRadialOuterFactor]
      ring
    simp only [Complex.ofReal_mul,Complex.ofReal_div] at hp ⊢
    simp_rw [hp,tsum_mul_left]
    rw [verticalIntegral_const_mul]
    dsimp only [c]
    simp only [Complex.ofReal_mul,Complex.ofReal_div]
    ring_nf
    congr 1
    apply congrArg (verticalIntegral ξ)
    funext z
    apply tsum_congr
    intro H
    congr 1 ; congr 1 ; ring_nf
  · simp only [zero_mul,tsum_zero,verticalIntegral,integral_zero,mul_zero]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RawNestedJoin -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def rawNestedPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) : ℂ :=
  ∑'K : SourceOuter C.excluded,verticalIntegral υ (fun w=>verticalIntegral 4 (fun t=>
    ∑'IJ : CompletedPair,verticalIntegral ξ (fun z=>∑'H : NonzeroFrequency,
      rawPhysicalMellinTerm η C C.excluded D IJ.1 IJ.2 K.val K.property.1 W0 W1 X Y Z H.val t w z)))

theorem nestedMellinPhysicalProbe_eq_raw (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z ξ υ : ℝ) :
    nestedMellinPhysicalProbe η C D W0 W1 X Y Z ξ υ=
      rawNestedPhysicalProbe η C D W0 W1 X Y Z ξ υ := by
  unfold nestedMellinPhysicalProbe rawNestedPhysicalProbe
  rw [sourceOuter_tsum]
  apply tsum_congr
  intro K
  dsimp only
  simp_rw [rawPhysicalMellinTerm_radial_join,tsum_mul_left]
  apply congrArg (verticalIntegral υ)
  funext w
  unfold rawRadialOuterFactor
  simp only [fullIdealWeight,ite_eq_right K.property.1.1]
  unfold verticalIntegral
  simp_rw [mul_assoc,integral_const_mul]
  simp only [Complex.ofReal_natCast]
  ring_nf
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  ring_nf

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.PhysicalRawIntegral -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance : MeasurableSpace O := ⊤
local instance : MeasurableSingletonClass O := ⟨fun _=>trivial⟩
local instance : MeasurableSpace (Ideal O) := ⊤
local instance : MeasurableSingletonClass (Ideal O) := ⟨fun _=>trivial⟩
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

def rawPhysicalTotalIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : SourceRawIndex S×HeightSpace,originalRawOnLines η S hS D W0 W1 X Y Z p.1 p.2
      ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)

theorem rawNestedPhysicalProbe_eq_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawNestedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z 2 3=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  unfold rawPhysicalTotalIntegral
  rw [originalRaw_integral_eq_nesting η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  unfold rawNestedPhysicalProbe
  simp only [calibrationForSet_excluded]
  simp only [verticalIntegral,integral_const_mul,tsum_mul_left]
  unfold originalNestedOnLines originalRawOnLines
  simp only [Complex.ofReal_ofNat]
  ring_nf
  congr 1
  let e : SourceOuter S ≃ SourceOuter (calibrationForSet S hS).excluded :=
    Equiv.subtypeEquivRight (fun K=>by rw [calibrationForSet_excluded])
  rw [←e.tsum_eq]
  apply tsum_congr
  intro K
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro w
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply tsum_congr
  intro IJ
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  apply tsum_congr
  intro H
  congr 1 ; ring

theorem markedPhysicalProbe_eq_raw_integral (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_nested_mellin η S hS hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 2 3 hX hY hZ (by norm_num),nestedMellinPhysicalProbe_eq_raw]
  exact rawNestedPhysicalProbe_eq_integral η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RawSourceIntegral -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

def rawSourceOnLines (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (i : SourceRawIndex S) (p : HeightSpace) : ℂ :=
  initialHighOnLines S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val))
    3 3 2 (sourceRawEmbedding S i) p *sourceMellinWeight W0 W1 X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)

lemma originalRawOnLines_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (i : SourceRawIndex S) (p : HeightSpace) :
    originalRawOnLines η S hS D W0 W1 X Y Z i p=
      rawSourceOnLines η S hS D W0 W1 X Y Z i (sourceHeightShear.symm p) := by
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ i.property.1
    i.property.2 W0 W1 X Y Z hX i.val.1]
  have he : (4:ℂ)+p.1.1*Complex.I+1-((2:ℂ)+p.1.2*Complex.I)=
      3+((p.1.1-p.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hs : sourceHeightShear.symm p=((p.1.1-p.1.2,p.1.2),p.2) := rfl
  simp only [rawSourceOnLines,initialHighOnLines,he,hs,sourceRawEmbedding,Complex.ofReal_ofNat]
  ring

lemma rawSourceOnLines_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : SourceRawIndex S×HeightSpace=>rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  have hm (H : NonzeroFrequency) : ‖star ((calibrationForSet S hS).residueMonoid H.val)‖≤1 := by
    simpa only [norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  unfold rawSourceOnLines
  apply initialHigh_counting_product_integrable (sourceRawEmbedding S) (sourceRawEmbedding_injective S)
    S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) hm 3 3 2
    (by norm_num) (by norm_num) (by norm_num)
    (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
      ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I))
  · exact sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ 3 2 3 (by norm_num)
  · exact sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
      X Y Z hX hY hZ 3 2 3 (by norm_num)

lemma rawPhysicalTotalIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : SourceRawIndex S×HeightSpace,rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2
          ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  unfold rawPhysicalTotalIntegral
  congr 1
  let e : SourceRawIndex S×HeightSpace ≃ᵐ SourceRawIndex S×HeightSpace :=
    (MeasurableEquiv.refl (SourceRawIndex S)).prodCongr sourceHeightShear.symm
  have hp : MeasurePreserving e ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) :=
    (MeasurePreserving.id _).prod (sourceHeightShear_preserving.symm sourceHeightShear)
  have he := hp.integral_comp' (fun p : SourceRawIndex S×HeightSpace=>
    rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
  refine Eq.trans ?_ he
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  exact originalRawOnLines_eq_source η S hS hpS hbad D W0 W1 X Y Z hX p.1 p.2

def rawSourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    rawArithmeticSeries S D η (calibrationForSet S hS) ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

lemma rawPhysicalTotalIntegral_eq_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      rawSourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [rawPhysicalTotalIntegral_eq_source η S hS hpS hbad D W0 W1 X Y Z hX]
  unfold rawSourceTripleIntegral
  congr 1
  have hi := rawSourceOnLines_integrable η S hS D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

theorem markedPhysicalProbe_eq_raw_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      rawSourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_raw_integral η S hS hpS hbad hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  exact rawPhysicalTotalIntegral_eq_triple η S hS hpS hbad D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SixthArray -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeCompleted
open HeckeInverseAmplification ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma bareIdealHighCoefficient_sixth (η : HeckeFamily.Character)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (hL : Supported p.2.val)
    (I J K : Ideal O) :
    bareIdealHighCoefficient η (sixthFrequencyEquiv p).val I J K 1=
      bareIdealHighCoefficient η p.1.val I J K p.2.val := by
  rw [sixthFrequencyEquiv_primary p hL]
  unfold bareIdealHighCoefficient
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K
  · simp only [h.1,h.2.1,h.2.2.1,h.2.2.2,hL,supported_one_ideal,and_self,dite_eq_left]
    congr 1
    simp only [primaryGenerator_one,one_pow,mul_one]
  · have h1 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun hh=>h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    have h2 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported p.2.val) :=
      fun hh=>h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    rw [dite_eq_right h1,dite_eq_right h2]

lemma rawHighCoefficient_sixth (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Ideal O) (η : HeckeFamily.Character) (x w z : ℂ)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (I J K : Ideal O) :
    fullHighCoefficient S D η
      (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) x w z
      (rawHighEmbedding (sixthFrequencyEquiv p,((I,J),K)))=
    star ((calibrationForSet S hS).residueMonoid p.1.val)*
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*
      markedIdealHighSummand S D η p.1.val x w z I J K p.2.val := by
  have hOne : ∀P∈S,¬P∣(1:Ideal O) := fun P hP=> (hprime P hP).not_dvd_one
  change star ((calibrationForSet S hS).residueMonoid (sixthFrequencyEquiv p).val)*
    frequencyWeight z (sixthFrequencyEquiv p)*
      markedIdealHighSummand S D η (sixthFrequencyEquiv p).val x w z I J K 1=_
  rw [sixthFrequencyWeight]
  rw [sixthFrequencyEquiv_apply,calibration_sixth_frequency_mask]
  by_cases hL : ∀P∈S,¬P∣p.2.val
  · have hs := supported_of_source_exclusions S hbad p.2.val p.2.property hL
    have hb := bareIdealHighCoefficient_sixth η p hs I J K
    rw [sixthFrequencyEquiv_apply] at hb
    simp only [ite_eq_left hL,mul_one,markedIdealHighSummand,highIdealMask,ite_eq_left hOne,
      bareIdealHighSummand,hb]
    have hw1 : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
    rw [hw1]
    ring
  · simp only [ite_eq_right hL,mul_zero,zero_mul,markedIdealHighSummand,highIdealMask]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SixthSeries -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve HeckeInverseAmplification ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev SixthInnerIndex := HeckeInverseAmplification.NonzeroIdeal×((Id×Id)×Id)

def sixthRawEquiv : FreeRow×SixthInnerIndex ≃ RawHighIndex :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr sixthFrequencyEquiv (Equiv.refl _))

def nonzeroLastEquiv : SixthInnerIndex ≃ {p : (Id×Id)×(Id×Id) // p.2.2≠0} where
  toFun p := ⟨(p.2.1,(p.2.2,p.1.val)),p.1.property⟩
  invFun p := (⟨p.val.2.2,p.property⟩,(p.val.1,p.val.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

lemma markedIdealHighSummand_last_zero (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K : Id) :
    markedIdealHighSummand S D η u x w z I J K 0=0 := by
  have hz : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (0:Id)) :=
    fun h=>h.2.2.2.2.1 rfl
  simp only [markedIdealHighSummand,bareIdealHighSummand,bareIdealHighCoefficient,
    dite_eq_right hz,zero_mul,mul_zero]

lemma markedIdealHighSeries_eq_sixth_inner (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) :
    markedIdealHighSeries S D η u x w z=
      ∑'p : SixthInnerIndex,markedIdealHighSummand S D η u x w z p.2.1.1 p.2.1.2 p.2.2 p.1.val := by
  have he := nonzeroLastEquiv.tsum_eq (fun p=>
    markedIdealHighSummand S D η u x w z p.val.1.1 p.val.1.2 p.val.2.1 p.val.2.2)
  change (∑'p : SixthInnerIndex,markedIdealHighSummand S D η u x w z p.2.1.1 p.2.1.2 p.2.2 p.1.val)=_ at he
  rw [he]
  unfold markedIdealHighSeries
  symm
  apply tsum_subtype_eq_of_support_subset
    (f:=fun p : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (s:={p : (Id×Id)×(Id×Id) | p.2.2≠0})
  intro p hp hz
  apply hp
  change markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2=0
  rw [hz,markedIdealHighSummand_last_zero]

theorem rawArithmeticSeries_eq_sixth_high (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    rawArithmeticSeries S D η (calibrationForSet S hS) x w z=
      ∑'u : FreeRow,star ((calibrationForSet S hS).residueMonoid u.val)*
        frequencyWeight z ⟨u.val,u.property.1⟩*markedIdealHighSeries S D η u.val x w z := by
  let mask : NonzeroFrequency→ℂ := fun H=>star ((calibrationForSet S hS).residueMonoid H.val)
  have hm (H : NonzeroFrequency) : ‖mask H‖≤1 := by
    simpa only [mask,norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  have hs := (fullHighSummand_summable S D η x w z hx hw hz mask hm).comp_injective
    rawHighEmbedding_injective
  have ht : Summable (fun p : FreeRow×SixthInnerIndex=>
      fullHighCoefficient S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) x w z
        (rawHighEmbedding (sixthRawEquiv p))) := hs.comp_injective sixthRawEquiv.injective
  unfold rawArithmeticSeries
  rw [←sixthRawEquiv.tsum_eq]
  rw [ht.tsum_prod]
  apply tsum_congr
  intro u
  rw [markedIdealHighSeries_eq_sixth_inner,←tsum_mul_left]
  apply tsum_congr
  intro p
  exact rawHighCoefficient_sixth S hS hprime hbad D η x w z (u,p.1) p.2.1.1 p.2.1.2 p.2.2

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SourceTriple -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary ProbeCompleted HeckeInverseAmplification CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def sourceRowSeries (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (C : CalibrationData) (D : Ideal O) (x w z : ℂ) : ℂ :=
  ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
    markedIdealHighSeries S D η u.val x w z

def sourceTripleIntegral (η : HeckeFamily.Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,P.IsMaximal) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫p : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
      ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I) ∂heightMeasure

lemma rawSourceTripleIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    rawSourceTripleIntegral η S hS D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  unfold rawSourceTripleIntegral sourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  dsimp only
  congr 1
  unfold sourceRowSeries
  exact rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

theorem markedPhysicalProbe_eq_source_triple (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      sourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [markedPhysicalProbe_eq_raw_triple η S hS hpS hbad hSne D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ]
  exact rawSourceTripleIntegral_eq_source η S hS hpS hbad D W0 W1 X Y Z

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SourceIntegrable -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
local instance (S : Finset (Ideal O)) : MeasurableSpace (SourceRawIndex S) := ⊤
local instance (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

lemma sourceRows_initial_integrable (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : HeightSpace=>
      sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+p.1.1*Complex.I)
        ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)*
      sourceRowSeries η S (calibrationForSet S hS) D ((3:ℂ)+p.1.1*Complex.I)
        ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  have hi := rawSourceOnLines_integrable η S hS D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  apply hi.integral_prod_right.congr
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp]
  have he := rawArithmeticSeries_eq_sixth_high S hS hpS hbad D η
    ((3:ℂ)+p.1.1*Complex.I) ((3:ℂ)+p.2*Complex.I) ((2:ℂ)+p.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
  change rawArithmeticSeries S D η (calibrationForSet S hS) _ _ _=
    sourceRowSeries η S (calibrationForSet S hS) D _ _ _ at he
  rw [←he,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.TupleScaling -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical

lemma sourceMellinWeight_subset (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z Q R : ℝ)
    (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hQ : 0<Q) (hR : 0<R)
    (a x w z : ℂ) :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*a*sourceMellinWeight W0 W1 (X/Q) (Y/Q) (Z*R) x w z=
      sourceMellinWeight W0 W1 X Y Z x w z*(Q:ℂ)^(z-w-1)*a*(R:ℂ)^(x+z-1) := by
  rw [sourceMellinWeight_marked W0 W1 (X/Q) (Y/Q) Z R hZ hR x w z]
  calc
    _ = a*(R:ℂ)^(x+z-1)*
        (((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z) := by ring
    _ = _ := by rw [sourceMellinWeight_rescaled W0 W1 X Y Z Q hX hY hQ x w z];ring

lemma tuple_norm_pos {K : ℕ} (p : Fin K→ActualEisensteinCubic.O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) : 0<elementNorm (∏i∈J,p i) := by
  apply elementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.TupleMellin -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def tupleSourceSeries {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,
    (-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)*
      sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

def tupleSourceTripleIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    tupleSourceSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

theorem compensatedTuple_eq_source_triple {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      tupleSourceTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  let A : Finset (Fin K)→ℂ := fun J=>(-1:ℂ)^J.card*
    ((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))
  let F : Finset (Fin K)→HeightSpace→ℂ := fun J t=>
    sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
      (Z*elementNorm (∏i∈Finset.univ\J,p i))
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
  have hF (J : Finset (Fin K)) : Integrable (F J) heightMeasure :=
    sourceRows_initial_integrable η S hS hpS hbad _ W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
      (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J)))
  have hpoint (J : Finset (Fin K)) (t : HeightSpace) :
      A J*F J t=sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
      ((-1:ℂ)^J.card*(elementNorm (∏i∈J,p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-((3:ℂ)+t.2*Complex.I)-1)*
        star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
        (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(((3:ℂ)+t.1.1*Complex.I)+((2:ℂ)+t.1.2*Complex.I)-1)*
        sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
          ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)) := by
    have he := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
      (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
      (tuple_norm_pos p hp (Finset.univ\J))
      (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i)))
      ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    dsimp only [A,F]
    linear_combination (-1:ℂ)^J.card * he *
      sourceRowSeries η S (calibrationForSet S hS) (Ideal.span {∏i∈Finset.univ\J,p i})
        ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
  have hleft : compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,∫t,A J*F J t ∂heightMeasure := by
    unfold compensatedTuple ProbeCompensation.tupleOperation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only
    rw [markedPhysicalProbe_eq_source_triple η S hS hpS hbad hSne _ W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
      (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J)))]
    rw [integral_const_mul]
    change A J*(((1/(2*Real.pi):ℝ):ℂ)^3*∫t,F J t ∂heightMeasure)=_
    ring
  rw [hleft,←integral_finsetSum _ (fun J _=>(hF J).const_mul (A J))]
  unfold tupleSourceTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun J _=>hpoint J t)

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.TupleProducts -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

lemma tuple_norm_cpow {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0)
    (J : Finset (Fin K)) (s : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^s=∏i∈J,(elementNorm (p i):ℂ)^s := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,elementNorm_one,Complex.ofReal_one,Complex.one_cpow]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,elementNorm_mul,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (elementNorm_pos _ (hp i)).le (tuple_norm_pos p hp J).le,
      ih,Finset.prod_insert hi]

lemma tuple_target_star {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) :
    star (HeckeFamily.elementCoeff η (∏i∈J,p i))=∏i∈J,star (HeckeFamily.elementCoeff η (p i)) := by
  change star (ProbeRow.targetMonoid η (∏i∈J,p i))=_
  rw [map_prod,star_prod]
  rfl

lemma tuple_source_scalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (x w z : ℂ) :
    (elementNorm (∏i∈J,p i):ℂ)^(z-w-1)*
      star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))*
      (elementNorm (∏i∈Finset.univ\J,p i):ℂ)^(x+z-1)=
    (∏i,(elementNorm (p i):ℂ)^(z-1))*
      (∏i∈J,(elementNorm (p i):ℂ)^(-w))*
      (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x) := by
  rw [tuple_norm_cpow p hp J,tuple_norm_cpow p hp (Finset.univ\J),tuple_target_star]
  have he (i : Fin K) : (elementNorm (p i):ℂ)^(z-w-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^(-w) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  have hf (i : Fin K) : (elementNorm (p i):ℂ)^(x+z-1)=
      (elementNorm (p i):ℂ)^(z-1)*(elementNorm (p i):ℂ)^x := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (elementNorm_pos _ (hp i)).ne')]
    congr 1
    ring
  simp only [he,hf,Finset.prod_mul_distrib]
  have hc := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i : Fin K=>(elementNorm (p i):ℂ)^(z-1))
  rw [←hc]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.TupleRows -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceRowSummand_summable (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (D : Id) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    Summable (fun u : FreeRow=>star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S D η u.val x w z) := by
  let e : FreeRow×((Id×Id)×(Id×Id))→FullHighIndex := fun p=>(⟨p.1.val,p.1.property.1⟩,p.2)
  have he : Function.Injective e := by
    intro a b h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun t : FullHighIndex=>t.1.val) h
    · exact congrArg (fun t : FullHighIndex=>t.2) h
  have hs := (fullHighSummand_summable S D η x w z hx hw hz
    (fun H=>star (C.residueMonoid H.val))
    (fun H=>by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val)).comp_injective he
  have ht := hs.prod
  apply ht.congr
  intro u
  dsimp only [Function.comp_def,e]
  exact tsum_mul_left (a:=star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩)
    (f:=fun c : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u.val x w z c.1.1 c.1.2 c.2.1 c.2.2)

def tupleIndexedCoefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) (x w : ℂ) : ℂ :=
  (-1:ℂ)^J.card*(∏i∈J,(elementNorm (p i):ℂ)^(-w))*
    (∏i∈Finset.univ\J,star (HeckeFamily.elementCoeff η (p i))*(elementNorm (p i):ℂ)^x)

def indexedCompensatedHigh {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (u : O) (x w z : ℂ) : ℂ :=
  ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
    markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z

lemma tupleSourceSeries_common_scale {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑J∈(Finset.univ:Finset (Fin K)).powerset,tupleIndexedCoefficient η p J x w*
          sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z := by
  unfold tupleSourceSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_source_scalar η p hp J x w z
  unfold tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*he*
    sourceRowSeries η S C (Ideal.span {∏i∈Finset.univ\J,p i}) x w z

theorem tupleSourceSeries_eq_rows {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    tupleSourceSeries η S C p x w z=
      (∏i,(elementNorm (p i):ℂ)^(z-1))*
        ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
          indexedCompensatedHigh η S p u.val x w z := by
  rw [tupleSourceSeries_common_scale η S C p hp]
  congr 1
  let f : Finset (Fin K)→FreeRow→ℂ := fun J u=>tupleIndexedCoefficient η p J x w*
    (star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u.val x w z)
  have hf (J : Finset (Fin K)) : Summable (f J) :=
    (sourceRowSummand_summable η S C _ x w z hx hw hz).mul_left _
  have hsum := Summable.tsum_finsetSum (s:=(Finset.univ:Finset (Fin K)).powerset)
    (f:=f) (fun J _=>hf J)
  unfold sourceRowSeries
  simp only [←tsum_mul_left]
  change (∑J∈(Finset.univ:Finset (Fin K)).powerset,∑'u,f J u)=_
  rw [←hsum]
  apply tsum_congr
  intro u
  unfold indexedCompensatedHigh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [f]
  ring

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.TupleKernel -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def tuplePhysicalScalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))

lemma tuple_scaled_coefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    tuplePhysicalScalar η p J*
      sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
        (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z=
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      tupleIndexedCoefficient η p J x w := by
  have ha := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
    (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
    (tuple_norm_pos p hp (Finset.univ\J))
    (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))) x w z
  have hb := tuple_source_scalar η p hp J x w z
  unfold tuplePhysicalScalar tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*ha +
    (-1:ℂ)^J.card*sourceMellinWeight W0 W1 X Y Z x w z*hb

lemma compensatedRow_kernel_subsets {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (hp : ∀i,p i≠0) (u : O) (a : ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      (a*indexedCompensatedHigh η S p u x w z)=
    ∑J∈(Finset.univ:Finset (Fin K)).powerset,tuplePhysicalScalar η p J*
      ((a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z)*
        sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
          (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z) := by
  unfold indexedCompensatedHigh
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_scaled_coefficient η p hp J W0 W1 X Y Z hX hY hZ x w z
  linear_combination -a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z*he

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.TuplePrime -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma span_tupleProduct {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    Ideal.span {∏i∈J,p i}=∏i∈J,Ideal.span {p i} := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Ideal.span_singleton_one,Ideal.one_eq_top]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,←Ideal.span_singleton_mul_span_singleton,ih,Finset.prod_insert hi]

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

theorem indexedCompensatedHigh_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hs : ∀i,Supported (P i).val)
    (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
      spectralCompensatedHigh S (Finset.univ.image P) η x w z
        (fun Q=>star (HeckeFamily.idealCoeff η Q.val)*(Ideal.absNorm Q.val:ℂ)^x)
        (fun Q=>(Ideal.absNorm Q.val:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedHigh
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.card_image_of_injective J hP,←Finset.image_sdiff _ _ hP]
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (primaryGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (hs i)]
    norm_cast
  have hc (i : Fin K) : HeckeFamily.elementCoeff η (primaryGenerator (P i).val)=
      HeckeFamily.idealCoeff η (P i).val := targetMonoid_primaryGenerator η (P i).val (hs i)
  simp only [tupleIndexedCoefficient,hnorm,hc,span_tupleProduct,
    span_primaryGenerator_of_supported _ (hs _)]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CanonicalSlots -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def canonicalSlotSupport (T : Finset PrimeIdeal) : Finset O :=
  T.image (fun P=>primaryGenerator P.val)

lemma primaryPrime_injective {P Q : PrimeIdeal} (hP : Supported P.val) (hQ : Supported Q.val)
    (h : primaryGenerator P.val=primaryGenerator Q.val) : P=Q := by
  apply Subtype.ext
  have hh := congrArg (fun a : O=>Ideal.span {a}) h
  simpa only [span_primaryGenerator_of_supported _ hP,span_primaryGenerator_of_supported _ hQ] using hh

lemma canonicalSlotSupport_nonzero (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (a : O) (ha : a∈canonicalSlotSupport T) : a≠0 := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact supported_primaryGenerator_ne_zero P.val (hT P hP)

def canonicalSlotEquiv (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val) :
    ↥T ≃ ↥(canonicalSlotSupport T) :=
  Equiv.ofBijective
    (fun P=>⟨primaryGenerator P.val.val,Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩⟩)
    ⟨by
      intro P Q h
      apply Subtype.ext
      exact primaryPrime_injective (hT P.val P.property) (hT Q.val Q.property) (congrArg Subtype.val h),by
      intro a
      obtain ⟨P,hP,he⟩ := Finset.mem_image.mp a.property
      exact ⟨⟨P,hP⟩,Subtype.ext he⟩⟩

@[simp] lemma canonicalSlotEquiv_val (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : (canonicalSlotEquiv T hT P).val=primaryGenerator P.val.val := rfl

lemma canonicalSlotEquiv_span (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : Ideal.span {(canonicalSlotEquiv T hT P).val}=P.val.val :=
  span_primaryGenerator_of_supported _ (hT P.val P.property)

lemma canonicalSlotEquiv_norm (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : elementNorm (canonicalSlotEquiv T hT P).val=(Ideal.absNorm P.val.val:ℝ) :=
  primaryTuple_norm P.val (hT P.val P.property)

def canonicalTupleEquiv {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) :
    (∀i,↥(T i)) ≃ (∀i,↥(canonicalSlotSupport (T i))) :=
  Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))

@[simp] lemma canonicalTupleEquiv_val {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (P : ∀i,↥(T i)) (i : Fin K) :
    (canonicalTupleEquiv T hT P i).val=primaryGenerator (P i).val.val := rfl

theorem sum_canonical_element_tuples {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),F (fun i=>primaryGenerator (P i).val.val) := by
  exact ((canonicalTupleEquiv T hT).sum_comp (fun p=>F (fun i=>(p i).val))).symm

lemma canonicalSlotSupport_disjoint (T U : Finset PrimeIdeal)
    (hT : ∀P∈T,Supported P.val) (hU : ∀P∈U,Supported P.val) (hdis : Disjoint T U) :
    Disjoint (canonicalSlotSupport T) (canonicalSlotSupport U) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨P,hP,hPa⟩ := Finset.mem_image.mp ha
  obtain ⟨Q,hQ,hQa⟩ := Finset.mem_image.mp hb
  have he : P=Q := primaryPrime_injective (hT P hP) (hU Q hQ) (hPa.trans hQa.symm)
  exact Finset.disjoint_left.mp hdis hP (he.symm ▸ hQ)

lemma idealTuple_injective_of_disjoint {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j))) (P : ∀i,↥(T i)) :
    Function.Injective (fun i=>(P i).val) := by
  intro i j he
  by_contra hij
  apply Finset.disjoint_left.mp (hdis hij) (P i).property
  rw [show (P i).val=(P j).val from he]
  exact (P j).property

lemma canonicalElementTuple_injective_of_disjoint {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j))) (P : ∀i,↥(T i)) :
    Function.Injective (fun i=>primaryGenerator (P i).val.val) := by
  intro i j he
  apply idealTuple_injective_of_disjoint T hdis P
  exact primaryPrime_injective (hT i _ (P i).property) (hT j _ (P j).property) he

theorem sum_canonical_weighted_tuples {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),
      (∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Y i))*
        F (fun i=>primaryGenerator (P i).val.val) := by
  rw [sum_canonical_element_tuples T hT (fun p=>(∏i,W i (elementNorm (p i)/Y i))*F p)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [primaryTuple_norm (P _).val (hT _ _ (P _).property)]

def idealSlotOfPrimary (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a})) : Finset PrimeIdeal :=
  A.attach.image (fun a : A => (⟨Ideal.span {a.val}, hp a.val a.property⟩ : PrimeIdeal))

lemma idealSlotOfPrimary_supported (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a}))
    (hs : ∀a∈A,Supported (Ideal.span {a})) :
    ∀P∈idealSlotOfPrimary A hp,Supported P.val := by
  intro P hP
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hP
  exact hs a.val a.property

lemma primarySlotNormalization (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a}))
    (hs : ∀a∈A,Supported (Ideal.span {a}))
    (hprimary : ∀a∈A,ConcretePrimeRowBridge.goodLambda^2∣a-1) :
    canonicalSlotSupport (idealSlotOfPrimary A hp)=A := by
  have hg (a : A) : primaryGenerator (Ideal.span {a.val})=a.val := by
    apply primaryGenerator_span a.val
    · intro hz
      have hn := (hs a.val a.property).1
      exact hn (by simp [hz])
    · exact hprimary a.val a.property
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨P,hP,hPa⟩ := Finset.mem_image.mp ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hP
    change primaryGenerator (Ideal.span {b.val})=a at hPa
    rw [hg b] at hPa
    exact hPa ▸ b.property
  · intro ha
    apply Finset.mem_image.mpr
    refine ⟨⟨Ideal.span {a},hp a ha⟩,?_,?_⟩
    · exact Finset.mem_image.mpr ⟨⟨a,ha⟩,by simp,rfl⟩
    · exact hg ⟨a,ha⟩

lemma canonicalSlotSupport_disjoint_iff (T U : Finset PrimeIdeal)
    (hT : ∀P∈T,Supported P.val) (hU : ∀P∈U,Supported P.val) :
    Disjoint (canonicalSlotSupport T) (canonicalSlotSupport U)↔Disjoint T U := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    exact Finset.disjoint_left.mp h (Finset.mem_image.mpr ⟨P,hP,rfl⟩)
      (Finset.mem_image.mpr ⟨P,hQ,rfl⟩)
  · exact canonicalSlotSupport_disjoint T U hT hU

lemma originalPrimarySlots_disjoint (A B : Finset O)
    (hAp : ∀a∈A,Prime (Ideal.span {a})) (hBp : ∀b∈B,Prime (Ideal.span {b}))
    (hAs : ∀a∈A,Supported (Ideal.span {a})) (hBs : ∀b∈B,Supported (Ideal.span {b}))
    (hAn : ∀a∈A,ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hBn : ∀b∈B,ConcretePrimeRowBridge.goodLambda^2∣b-1) (h : Disjoint A B) :
    Disjoint (idealSlotOfPrimary A hAp) (idealSlotOfPrimary B hBp) := by
  apply (canonicalSlotSupport_disjoint_iff _ _
    (idealSlotOfPrimary_supported A hAp hAs) (idealSlotOfPrimary_supported B hBp hBs)).mp
  simpa only [primarySlotNormalization A hAp hAs hAn,primarySlotNormalization B hBp hBs hBn] using h

theorem sum_original_primary_weighted_tuples {K : ℕ} (A : Fin K→Finset O)
    (hp : ∀i a,a∈A i→Prime (Ideal.span {a}))
    (hs : ∀i a,a∈A i→Supported (Ideal.span {a}))
    (hn : ∀i a,a∈A i→ ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(A i)),(∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val))=
      ∑P : (∀i,↥(idealSlotOfPrimary (A i) (hp i))),
        (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Y i))*F (fun i=>primaryGenerator (P i).val.val) := by
  have he (i : Fin K) := primarySlotNormalization (A i) (hp i) (hs i) (hn i)
  have hh := sum_canonical_weighted_tuples (fun i=>idealSlotOfPrimary (A i) (hp i))
    (fun i=>idealSlotOfPrimary_supported (A i) (hp i) (hs i)) W Y F
  let G (B : Fin K→Finset O) : ℂ :=
    ∑p : (∀i,↥(B i)),(∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val)
  have hfun : (fun i=>canonicalSlotSupport (idealSlotOfPrimary (A i) (hp i)))=A := funext he
  change G (fun i=>canonicalSlotSupport (idealSlotOfPrimary (A i) (hp i)))=_ at hh
  rw [hfun] at hh
  exact hh

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowSlotMarks -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSelectedIdeal_eq_product {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) :
    lowSelectedIdeal slots J b=∏i : SelectedSlot J,Ideal.span {(b i).val} := by
  change CanonicalRowCompletion.principalIdealHom (∏i : SelectedSlot J,(b i).val)=_
  exact map_prod CanonicalRowCompletion.principalIdealHom _ _

lemma lowSelectedIdeal_dvd_iff {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) : lowSelectedIdeal slots J b∣A ↔ ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A := by
  rw [lowSelectedIdeal_eq_product]
  constructor
  · intro h i
    exact (Finset.dvd_prod_of_mem (fun i : SelectedSlot J=>Ideal.span {(b i).val}) (Finset.mem_univ i)).trans h
  · exact Fintype.prod_dvd_of_coprime hcop

lemma lowSelectedIdeal_mark {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J)
    (hcop : Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})))
    (A : Id) :
    (if lowSelectedIdeal slots J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_dvd_iff slots J b hcop]
  by_cases h : ∀i : SelectedSlot J,Ideal.span {(b i).val}∣A
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right (fun hall=>hi (hall i))]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

def lowCanonicalSelectedPrime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) : PrimeIdeal :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).val

lemma lowCanonicalSelectedPrime_mem {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    lowCanonicalSelectedPrime T hT J b i∈T i.val :=
  ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i)).property

lemma lowCanonicalSelectedPrime_span {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    Ideal.span {(b i).val}=(lowCanonicalSelectedPrime T hT J b i).val := by
  have hh := canonicalSlotEquiv_span (T i.val) (hT i.val)
    ((canonicalSlotEquiv (T i.val) (hT i.val)).symm (b i))
  simpa only [Equiv.apply_symm_apply,lowCanonicalSelectedPrime] using hh

lemma lowCanonicalSelectedPrime_injective {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Function.Injective (lowCanonicalSelectedPrime T hT J b) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  exact Finset.disjoint_left.mp (hdis hne) (lowCanonicalSelectedPrime_mem T hT J b i)
    (hij.symm ▸ lowCanonicalSelectedPrime_mem T hT J b j)

lemma lowCanonicalSelected_coprime {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (fun i j : SelectedSlot J=>IsCoprime (Ideal.span {(b i).val}) (Ideal.span {(b j).val})) := by
  intro i j hij
  rw [lowCanonicalSelectedPrime_span T hT J b i,lowCanonicalSelectedPrime_span T hT J b j]
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))

theorem lowCanonicalSelected_mark {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (A : Id) :
    (if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
      ∏i : SelectedSlot J,if (lowCanonicalSelectedPrime T hT J b i).val∣A then (1:ℂ) else 0 := by
  rw [lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b)]
  simp_rw [lowCanonicalSelectedPrime_span T hT J b]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowPrimeFamily -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowCanonicalSelectedPrime_maximal {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    (lowCanonicalSelectedPrime T hT J b i).val.IsMaximal :=
  (Ideal.isPrime_of_prime (lowCanonicalSelectedPrime T hT J b i).property).isMaximal
    (lowCanonicalSelectedPrime T hT J b i).property.ne_zero

lemma lowCanonicalSelectedPrime_good {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    ConcretePrimeRowBridge.goodLambda∉(lowCanonicalSelectedPrime T hT J b i).val ∧
      ringChar (O⧸(lowCanonicalSelectedPrime T hT J b i).val)≠2 := by
  have hs := hT i.val _ (lowCanonicalSelectedPrime_mem T hT J b i)
  exact hs.2 _ ((Ideal.mem_normalizedFactors_iff hs.1).mpr
    ⟨Ideal.isPrime_of_prime (lowCanonicalSelectedPrime T hT J b i).property,le_rfl⟩)

def lowCanonicalPrimeFamily {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    InverseReflectedPhase.PrimeFamily (SelectedSlot J) where
  ideal i := (lowCanonicalSelectedPrime T hT J b i).val
  maximal := lowCanonicalSelectedPrime_maximal T hT J b
  good i := (lowCanonicalSelectedPrime_good T hT J b i).1

lemma lowCanonicalPrimeFamily_generator {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    (lowCanonicalPrimeFamily T hT J b).generator i=(b i).val := by
  let := lowCanonicalSelectedPrime_maximal T hT J b i
  change primaryPrime (lowCanonicalSelectedPrime T hT J b i).val=(b i).val
  rw [primaryPrime_eq_primaryGenerator]
  have hh := congrArg Subtype.val ((canonicalSlotEquiv (T i.val) (hT i.val)).apply_symm_apply (b i))
  simpa only [canonicalSlotEquiv_val,lowCanonicalSelectedPrime] using hh

lemma lowCanonicalPrimeFamily_pairwise {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (Function.onFun IsCoprime (lowCanonicalPrimeFamily T hT J b).ideal) := by
  intro i j hij
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))

lemma lowCanonicalPrimeFamily_odd {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    ringChar (O⧸(lowCanonicalPrimeFamily T hT J b).ideal i)≠2 :=
  (lowCanonicalSelectedPrime_good T hT J b i).2

lemma lowCanonicalPrimeFamily_product {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b=
      ∏i : SelectedSlot J,(lowCanonicalPrimeFamily T hT J b).ideal i := by
  rw [lowSelectedIdeal_eq_product]
  simp_rw [lowCanonicalSelectedPrime_span T hT J b]
  rfl

theorem lowCanonicalInverseRow_eq {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J)
    (R t : ℝ) (σ : RayRing) (m : O) :
    lowMarkedInverseRow η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b) R t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) R
          (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
  unfold lowMarkedInverseRow
  have he : (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
      (fun A : Id=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
    funext A
    exact lowCanonicalSelected_mark T hT hdis J b A
  rw [he]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowInverseEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open RayFourExpansion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCorrectionEnergy : ℝ := ∑χ : RayCharacter,‖ProbeCompleted.correctionCoeff χ‖^2

lemma lowCorrectionEnergy_nonneg : 0≤lowCorrectionEnergy :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

lemma fixed_correction_energy {ι κ : Type*} [Fintype ι] (R : Finset κ) (c : ι→ℂ) (F : ι→κ→ℂ) :
    (∑m∈R,‖∑χ : ι,c χ*F χ m‖^2)≤
      (∑χ : ι,‖c χ‖^2)*∑χ : ι,∑m∈R,‖F χ m‖^2 := by
  calc
    _≤∑m∈R,(∑χ : ι,‖c χ‖^2)*(∑χ : ι,‖F χ m‖^2) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        _≤(∑χ : ι,‖c χ‖*‖F χ m‖)^2 := by
          apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>by positivity))).mpr
          simpa only [norm_mul] using norm_sum_le Finset.univ (fun χ=>c χ*F χ m)
        _≤_ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _=_ := by rw [←Finset.mul_sum,Finset.sum_comm]

theorem lowSelectedInverseRow_energy {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (R : Finset O) :
    (∑m∈R,‖lowSelectedInverseRow F c η S hS D T t σ m‖^2)≤
      lowCorrectionEnergy*∑χ : RayCharacter,∑m∈R,
        ‖∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0)‖^2 := by
  simp_rw [lowSelectedInverseRow_correction]
  exact fixed_correction_energy R ProbeCompleted.correctionCoeff _

theorem lowCanonicalSelected_energy {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) :
    (∑m∈R,‖lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ m‖^2)≤
      lowCorrectionEnergy*∑χ : RayCharacter,∑m∈R,
        ‖∑b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J,
          (∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val)*
          InverseMoment.markedCompletedT
            (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
              (calibrationForSet S hS).generator 1 m)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
            (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0)‖^2 := by
  have hh := lowSelectedInverseRow_energy Finset.univ
    (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
    η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ R
  simp_rw [lowSelectedWeight_eq_product] at hh
  have he (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
    funext A
    exact lowCanonicalSelected_mark T hT hdis J b A
  simp_rw [he] at hh
  exact hh

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowElementRows -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowElementRowPoint (m : O) : Oˣ×Id :=
  (InitialMeanSquare.sourceLabelUnit m,Ideal.span {m})

def lowIdealRowElement (p : Oˣ×Id) : O := p.1.val*idealGenerator p.2

lemma lowIdealRowElement_point (m : O) : lowIdealRowElement (lowElementRowPoint m)=m :=
  (InitialMeanSquare.sourceLabelUnit_spec m).symm

lemma lowElementRowPoint_injective : Function.Injective lowElementRowPoint :=
  Function.LeftInverse.injective lowIdealRowElement_point

lemma lowIdealRowElement_span (p : Oˣ×Id) : Ideal.span {lowIdealRowElement p}=p.2 := by
  rw [lowIdealRowElement,Ideal.span_singleton_mul_left_unit p.1.isUnit,span_idealGenerator]

lemma lowElementRowPoint_element (p : Oˣ×Id) (hp : p.2≠0) :
    lowElementRowPoint (lowIdealRowElement p)=p := by
  apply Prod.ext
  · apply Units.ext
    have hh := InitialMeanSquare.sourceLabelUnit_spec (lowIdealRowElement p)
    rw [lowIdealRowElement_span] at hh
    exact (mul_right_cancel₀ (idealGenerator_ne_zero p.2 hp) hh).symm
  · exact lowIdealRowElement_span p

lemma lowIdealRowElement_norm (p : Oˣ×Id) :
    elementNorm (lowIdealRowElement p)=(Ideal.absNorm p.2:ℝ) := by
  unfold elementNorm
  rw [lowIdealRowElement_span]

def lowIdealRows (R : Finset O) : Finset Id := R.image (fun m=>Ideal.span {m})

lemma lowIdealRows_nonzero (R : Finset O) (hR : ∀m∈R,m≠0) (I : Id) (hI : I∈lowIdealRows R) : I≠0 := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact Ideal.span_singleton_eq_bot.not.mpr (hR m hm)

lemma lowIdealRows_norm_bound (R : Finset O) (Q : ℝ) (hR : ∀m∈R,elementNorm m≤Q)
    (I : Id) (hI : I∈lowIdealRows R) : (Ideal.absNorm I:ℝ)≤Q := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hI
  exact hR m hm

theorem sum_low_element_rows (R : Finset O) (hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,F m)=∑u : Oˣ,∑I∈lowIdealRows R,
      if u.val*idealGenerator I∈R then F (u.val*idealGenerator I) else 0 := by
  let P := (Finset.univ×ˢlowIdealRows R).filter (fun p : Oˣ×Id=>lowIdealRowElement p∈R)
  have he : (∑m∈R,F m)=∑p∈P,F (lowIdealRowElement p) := by
    apply Finset.sum_bij (fun m hm=>lowElementRowPoint m)
    · intro m hm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact Finset.mem_image.mpr ⟨m,hm,rfl⟩
      · rwa [lowIdealRowElement_point]
    · intro m hm n hn he
      exact lowElementRowPoint_injective he
    · intro p hp
      obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
      refine ⟨lowIdealRowElement p,hpr,?_⟩
      exact lowElementRowPoint_element p (lowIdealRows_nonzero R hR _ (Finset.mem_product.mp hp).2)
    · intro m hm
      rw [lowIdealRowElement_point]
  rw [he]
  dsimp only [P]
  rw [Finset.sum_filter,Finset.sum_product]
  rfl

theorem low_element_energy_le_units (R : Finset O) (_hR : ∀m∈R,m≠0) (F : O→ℂ) :
    (∑m∈R,‖F m‖^2)≤∑u : Oˣ,∑I∈lowIdealRows R,‖F (u.val*idealGenerator I)‖^2 := by
  let P : Finset (Oˣ×Id) := Finset.univ×ˢlowIdealRows R
  have hsub : R.image lowElementRowPoint⊆P := by
    intro p hp
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨m,hm,rfl⟩⟩
  have he : (∑m∈R,‖F m‖^2)=∑p∈R.image lowElementRowPoint,‖F (lowIdealRowElement p)‖^2 := by
    rw [Finset.sum_image (fun m _ n _ h=>lowElementRowPoint_injective h)]
    simp only [lowIdealRowElement_point]
  rw [he]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _=>sq_nonneg ‖F (lowIdealRowElement p)‖)
  simpa only [P,Finset.sum_product,lowIdealRowElement] using hh

lemma low_rowTwist_label_one (Ψ : O→*ℂ) (m : O) (u : Oˣ) (I : Id) :
    CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)=
      CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id))
        (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I) := by
  have he : (InitialMeanSquare.sourceLabelUnit (1:O)).val*idealGenerator (1:Id)=1 := by
    simpa only [Ideal.span_singleton_one,Ideal.one_eq_top] using (InitialMeanSquare.sourceLabelUnit_spec (1:O)).symm
  have harg : m^6*(idealGenerator (1:Id))^4*
      (((InitialMeanSquare.sourceLabelUnit 1)^4*u).val*idealGenerator I)=m^6*1^4*(u.val*idealGenerator I) := by
    simp only [Units.val_mul,Units.val_pow_eq_pow_val,one_pow]
    calc
      _=m^6*((InitialMeanSquare.sourceLabelUnit (1:O)).val*idealGenerator (1:Id))^4*(u.val*idealGenerator I) := by ring
      _=_ := by rw [he];ring
  unfold CanonicalRowCompletion.rowTwist
  rw [harg]

lemma low_units_label_one_sum (F : (O→*ℂ)→ℝ) (Ψ : O→*ℂ) (m : O) (I : Id) :
    (∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m 1 (u.val*idealGenerator I)))=
      ∑u : Oˣ,F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)) := by
  simp_rw [low_rowTwist_label_one]
  exact Equiv.sum_comp (Equiv.mulLeft ((InitialMeanSquare.sourceLabelUnit (1:O))^4))
    (fun u : Oˣ=>F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I)))

lemma low_element_rowTwist_energy (R : Finset O) (hR : ∀z∈R,z≠0)
    (Ψ : O→*ℂ) (m : O) (F : (O→*ℂ)→ℂ) :
    (∑z∈R,‖F (CanonicalRowCompletion.rowTwist Ψ m 1 z)‖^2)≤
      ∑u : Oˣ,∑I∈lowIdealRows R,
        ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2 := by
  apply (low_element_energy_le_units R hR (fun z=>F (CanonicalRowCompletion.rowTwist Ψ m 1 z))).trans_eq
  rw [Finset.sum_comm,Finset.sum_comm (f:=fun (u : Oˣ) (I : Id)=>
    ‖F (CanonicalRowCompletion.rowTwist Ψ m (idealGenerator (1:Id)) (u.val*idealGenerator I))‖^2)]
  apply Finset.sum_congr rfl
  intro I hI
  exact low_units_label_one_sum (fun Ψ=>‖F Ψ‖^2) Ψ m I

lemma lowNumeratorRows_nonzero (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : z≠0 := by
  intro he
  have hh := (lowNumeratorRows_mem a b ha hb Q hQ z).mp hz
  rw [he,elementNorm,Ideal.span_singleton_zero,Ideal.absNorm_bot,Nat.cast_zero,zero_div] at hh
  exact hh (lowOuterCutoff_small a b ha 0 (by positivity))

lemma lowNumeratorRows_norm_bound (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (z : O) (hz : z∈lowNumeratorRows a b ha hb Q hQ) : elementNorm z≤2*b*Q := by
  have hh := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ z).mp hz)).2
  exact (div_le_iff₀ hQ).mp hh

theorem lowSelectedInverseRow_ideal_energy {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (X t : ℝ) (σ : RayFourExpansion.RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow F c η S hS D X t σ z‖^2)≤
      lowCorrectionEnergy*∑χ : RayFourExpansion.RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
        ‖∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator (idealGenerator (1:Id)) (u.val*idealGenerator I))
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
          (fun A=>if D k∣A then (1:ℂ) else 0)‖^2 := by
  apply (lowSelectedInverseRow_energy F c η S hS D X t σ R).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (calibrationForSet S hS).generator (fun Ψ=>∑k∈F,c k*InverseMoment.markedCompletedT Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X (fun A=>if D k∣A then (1:ℂ) else 0))

lemma low_unit_card : Fintype.card Oˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowPeriodSupport -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma lowCalibrationGood_dvd (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator) : D.numeratorGood∣C.generator := by
  refine ⟨D.numeratorUnit.val*λ₀^D.numeratorLambda*(2:O)^D.numeratorTwo,?_⟩
  have hh := D.numeratorFactor
  simp only [one_pow,one_mul] at hh
  change C.generator=D.numeratorUnit.val*λ₀^D.numeratorLambda*(2:O)^D.numeratorTwo*D.numeratorGood at hh
  exact hh.trans (by ring)

theorem lowBaseModulus_coprime (η : HeckeFamily.Character) (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator)
    (hLam : λ₀∣C.generator) (h2 : (2:O)∣C.generator)
    (n : O) (hcn : IsCoprime C.generator n) (hη : HeckeFamily.elementCoeff η n≠0) :
    IsCoprime (Ideal.span {n}) (lowBaseModulus η C C.generator D*Ideal.span {(72:O)}) := by
  have heta : IsCoprime (Ideal.span {n}) η.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hη)
  have hcal : IsCoprime (Ideal.span {n}) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hcn.symm
  have hgood : IsCoprime (Ideal.span {n}) (Ideal.span {D.numeratorGood}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (hcn.of_isCoprime_of_dvd_left (lowCalibrationGood_dvd C D)).symm
  have htwo : IsCoprime n (2:O) := (hcn.of_isCoprime_of_dvd_left h2).symm
  have hs := supported_of_coprime_bad C.generator n hLam h2 hcn
  have hnine := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n ((supported_span_iff n).mp hs).1).symm
  have hseventy : IsCoprime n (72:O) := by
    convert (htwo.pow_right : IsCoprime n ((2:O)^3)).mul_right hnine using 1 ;norm_num
  have h72 : IsCoprime (Ideal.span {n}) (Ideal.span {(72:O)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hseventy
  have h4 : IsCoprime (Ideal.span {n}) (Ideal.span {(4:O)}) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    convert htwo.pow_right (n:=2) using 1 ;norm_num
  unfold lowBaseModulus calibrationRowModulus
  exact (heta.mul_right (hcal.mul_right
    (((isCoprime_one_right).mul_right hcal).mul_right h72 |>.mul_right hgood))).mul_right h4 |>.mul_right h72

theorem lowSingleSlotWeight_zero_of_period (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (P t : ℝ) (n : O) (hcn : IsCoprime (calibrationForSet S hS).generator n)
    (hperiod : ¬IsCoprime (Ideal.span {n})
      (lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator
        (calibrationLowData S hS)*Ideal.span {(72:O)})) :
    lowSingleSlotWeight η W P t n=0 := by
  have heta : HeckeFamily.elementCoeff η n=0 := by
    by_contra hh
    exact hperiod (lowBaseModulus_coprime η _ _ (calibration_generator_bad S hS hbad).1
      (calibration_generator_bad S hS hbad).2 n hcn hh)
  simp [lowSingleSlotWeight,heta]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.LowPeriodFilter -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sum_tuple_filter_zero {ι α : Type*} [Fintype ι] [DecidableEq α]
    (T : ι→Finset α) (good : ι→α→Prop) [∀i,DecidablePred (good i)]
    (c : ι→α→ℂ) (hc : ∀i a,a∈T i→¬good i a→c i a=0) (F : (ι→α)→ℂ) :
    (∑p : ∀i,T i,(∏i,c i (p i).val)*F (fun i=>(p i).val))=
      ∑p : ∀i,(T i).filter (good i),(∏i,c i (p i).val)*F (fun i=>(p i).val) := by
  let forget : (∀i,(T i).filter (good i))→(∀i,T i) := fun p i=>⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩
  have hinj : Function.Injective forget := by
    intro p q h
    funext i
    exact Subtype.ext (congrArg (fun a=> (a i).val) h)
  let H : (∀i,T i)→ℂ := fun p=>(∏i,c i (p i).val)*F (fun i=>(p i).val)
  have hz (p : ∀i,T i) (hp : p∉Finset.univ.image forget) : H p=0 := by
    by_contra hh
    have hn : ∀i,good i (p i).val := by
      intro i
      by_contra hbad
      have hc0 := hc i (p i).val (p i).property hbad
      have hprod : (∏j,c j (p j).val)=0 := Finset.prod_eq_zero (Finset.mem_univ i) hc0
      exact hh (by dsimp [H];rw [hprod,zero_mul])
    let q : ∀i,(T i).filter (good i) := fun i=>⟨(p i).val,Finset.mem_filter.mpr ⟨(p i).property,hn i⟩⟩
    exact hp (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩)
  have he := Finset.sum_subset (Finset.subset_univ (Finset.univ.image forget))
    (fun p hp hnot=>hz p hnot)
  change (∑p,H p)=_
  rw [←he,Finset.sum_image (fun p _ q _ h=>hinj h)]

def lowPeriodIdeal (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS)*Ideal.span {(72:O)}

def lowPeriodSlotFilter {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→Finset O) : ι→Finset O :=
  fun i=>(T i).filter (fun a=>IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS))

lemma lowPeriodSlotFilter_coprime {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→Finset O) (i : ι) (a : O)
    (ha : a∈lowPeriodSlotFilter η S hS T i) :
    IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS) := (Finset.mem_filter.mp ha).2

lemma canonical_prime_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (P : PrimeIdeal) (hP : CanonicalQuadraticSieve.Supported P.val) (hout : P.val∉S) :
    IsCoprime (calibrationForSet S hS).generator (CompletedGauss.primaryGenerator P.val) := by
  apply calibrationForSet_coprime_of_excluded S hS
  intro Q hQ hdiv
  rw [span_primaryGenerator_of_supported P.val hP] at hdiv
  have hpmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have he : P.val=Q := Ideal.IsMaximal.eq_of_le hpmax (hS Q hQ).ne_top (Ideal.dvd_iff_le.mp hdiv)
  exact hout (he.symm ▸ hQ)

lemma canonical_slot_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (T : Finset PrimeIdeal)
    (hT : ∀P∈T,CanonicalQuadraticSieve.Supported P.val) (hout : ∀P∈T,P.val∉S)
    (a : O) (ha : a∈canonicalSlotSupport T) : IsCoprime (calibrationForSet S hS).generator a := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact canonical_prime_calibration_coprime S hS P (hT P hP) (hout P hP)

theorem low_slot_polynomial_period_filter {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (T : ι→Finset O)
    (hcop : ∀i a,a∈T i→IsCoprime (calibrationForSet S hS).generator a)
    (W : ι→ℝ→ℂ) (P : ι→ℝ) (t : ℝ) (F : (ι→O)→ℂ) :
    (∑p : ∀i,T i,(∏i,lowSingleSlotWeight η (W i) (P i) t (p i).val)*F (fun i=>(p i).val))=
      ∑p : ∀i,lowPeriodSlotFilter η S hS T i,
        (∏i,lowSingleSlotWeight η (W i) (P i) t (p i).val)*F (fun i=>(p i).val) := by
  apply sum_tuple_filter_zero T (fun i a=>IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS))
    (fun i a=>lowSingleSlotWeight η (W i) (P i) t a) _ F
  intro i a ha hnot
  exact lowSingleSlotWeight_zero_of_period η S hS hbad (W i) (P i) t a (hcop i a ha) hnot

def lowPeriodPrimeList (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) : Finset PrimeIdeal :=
  T.filter (fun P=>IsCoprime P.val (lowPeriodIdeal η S hS))

lemma lowPeriodPrimeList_subset (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) :
    lowPeriodPrimeList η S hS T⊆T := Finset.filter_subset _ _

lemma lowPeriodPrimeList_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal)
    (P : PrimeIdeal) (hP : P∈lowPeriodPrimeList η S hS T) :
    IsCoprime P.val (lowPeriodIdeal η S hS) := (Finset.mem_filter.mp hP).2

lemma lowPeriodPrimeList_disjoint {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→Finset PrimeIdeal)
    (hT : Pairwise (fun i j=>Disjoint (T i) (T j))) :
    Pairwise (fun i j=>Disjoint (lowPeriodPrimeList η S hS (T i)) (lowPeriodPrimeList η S hS (T j))) := by
  intro i j hij
  exact (hT hij).mono (lowPeriodPrimeList_subset η S hS _) (lowPeriodPrimeList_subset η S hS _)

theorem low_canonical_polynomial_period_filter {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→PrimeIdeal)→ℂ) :
    (∑p : ∀i,T i,(∏i,lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator (p i).val.val))*F (fun i=>(p i).val))=
      ∑p : ∀i,lowPeriodPrimeList η S hS (T i),
        (∏i,lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator (p i).val.val))*F (fun i=>(p i).val) := by
  apply sum_tuple_filter_zero T (fun i P=>IsCoprime P.val (lowPeriodIdeal η S hS))
    (fun i P=>lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator P.val)) _ F
  intro i P hP hnot
  apply lowSingleSlotWeight_zero_of_period η S hS hbad (W i) (Y i) t _
    (canonical_prime_calibration_coprime S hS P (hT i P hP) (hout i P hP))
  change ¬IsCoprime (Ideal.span {CompletedGauss.primaryGenerator P.val}) (lowPeriodIdeal η S hS)
  rwa [span_primaryGenerator_of_supported P.val (hT i P hP)]

end SevenEighths.ProbePhysical
end

end OAI

end

