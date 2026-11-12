module

public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part011
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part005
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.StripActual
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeCounting.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part021

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / PrimeRows / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalShift -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma physicalRow_w_height_bound {K : ℕ} (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (hxw : 1+eps≤x.re+1/2) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,(1/2:ℝ)≤v → ∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_w_growth (eps/2) S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu x z hx hz (by linarith)
  refine ⟨9*C,by positivity,?_⟩
  intro v hv t
  have hb := hbound ((v:ℂ)+t*I) (by simpa using hv)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have h3 : (3+|t|)^2≤9*(height t)^2 := by
    unfold height
    nlinarith [abs_nonneg t]
  nlinarith

theorem nonprincipal_w_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤ r) (hl : (1/2:ℝ)≤l)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (hxw : 1+eps≤x.re+1/2) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z hx hz hxw
  exact nonprincipal_w_integral_eq_of_polynomial eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x z l r C 2 hC.le hlr (by linarith) (by linarith)
    hz (by linarith) (fun v hv t=>hbound v (hl.trans hv.1) t)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.IteratedShift -/

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩

def shiftedRowInner {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z l : ℝ) (q : ℝ×ℝ) : ℂ :=
  ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((3:ℂ)+q.1*I) ((l:ℂ)+t*I) ((2:ℂ)+q.2*I)

theorem rowIntegral_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (heps' : eps≤5/2)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (l : ℝ) (hl : (1/2:ℝ)≤l) (hl3 : l≤3) :
    Integrable (shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l) (volume.prod volume) ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q ∂(volume.prod volume) := by
  let p : Fin K→O := fun i=>CompletedGauss.primaryGenerator (P i).val
  have hp : ∀i,p i≠0 := fun i=>(supported_primeGenerator_prime (P i)
    (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=>Subtype.ext (congrArg (fun v : NonzeroFrequency=>v.val) h)
  have hF := compensatedRows_counting_product_integrable e he η S (calibrationForSet S hmax) p hp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hi : Integrable (compensatedRowOnLines η S (calibrationForSet S hmax) p W0 W1 X Y Z (e u))
      heightMeasure := (Measure.ae_count_iff.mp hF.prod_right_ae) u
  have heq (q : ℝ×ℝ) :
      (∫t : ℝ,compensatedRowOnLines η S (calibrationForSet S hmax) p W0 W1 X Y Z (e u) (q,t))=
        shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q := by
    have hs := nonprincipal_w_integral_eq eps heps S hS hfirst hmax P hPS η u hu W0 W1
      a1 b1 ha1 hW1 X Y Z hY ((3:ℂ)+q.1*I) ((2:ℂ)+q.2*I) l 3 hl3 hl
      (by norm_num) (by norm_num) (by norm_num;linarith)
    unfold shiftedRowInner
    rw [hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>(continuedPhysicalRowKernel_initial S hS hmax P hP hPS
      η u W0 W1 X Y Z (q,t)).symm)
  refine ⟨?_,?_⟩
  · exact hi.integral_prod_left.congr (Filter.Eventually.of_forall heq)
  · unfold rowIntegral
    rw [integral_prod _ hi]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall heq)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.WeightedTuple -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem tupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→ProbePhysical.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def calibratedTupleValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
  (∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1))*
  physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z

theorem calibratedTupleValue_factor {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
            (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
            (((P i).val.absNorm:ℂ)^(-w))) := by
  unfold calibratedTupleValue
  rw [physicalCompensatedRow_indexed S hS P hP hPS]
  simp only [Finset.prod_mul_distrib]
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.Measurable -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α]
    (Q : ℂ) (hQ : Q≠0) (f : α→ℂ) (hf : Measurable f) : Measurable (fun t=>Q^(f t)) :=
  ((continuous_id.const_cpow (Or.inl hQ)).measurable).comp hf

lemma rowClosedMarked_measurable {α : Type*} [MeasurableSpace α]
    (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda∉Ideal.span {p}) (η a ρ : ℂ) (j : ℕ)
    (X W V : α→ℂ) (hX : Measurable X) (hW : Measurable W) (hV : Measurable V) :
    Measurable (fun t=>rowClosedMarked p hp hg η a (X t) (W t) (V t) ρ j) := by
  unfold rowClosedMarked rowBaseFinite rowMarkedTerm rowWeightedScalar weightedScalar evenRatio
  simp only [Nat.reduceAdd,Nat.reduceMul,OfNat.ofNat_ne_zero,Nat.one_ne_zero,ite_false]
  fun_prop

lemma continuedMarkedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedMarkedLocal η u P hs (x t) (w t) (z t)) := by
  have hQ : (P.val.absNorm:ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  let : (Ideal.span {primaryGenerator P.val}:Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (supported_primeGenerator_prime P hs).irreducible
  unfold continuedMarkedLocal
  apply rowClosedMarked_measurable
  · exact measurable_const_cpow _ hQ _ hx.neg
  · exact measurable_const_cpow _ hQ _ hw.neg
  · unfold coordV
    apply measurable_const_cpow _ (by exact_mod_cast hQ)
    fun_prop

lemma ramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>ramifiedCorrection η u P hs (x t) (w t) (z t)) := by
  have hm := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  simp_rw [ramifiedCorrection_eq_marked]
  unfold coordV
  fun_prop (disch := exact hQ)

lemma idealUnramifiedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>idealUnramifiedCorrection η u P (x t) (w t) (z t)) := by
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealUnramifiedCorrection unramifiedClosed ProbeLocal.continuedCorrection markedFactor
    coordV coordR coordW coordD coordK
  fun_prop (disch := exact hQ)

lemma continuedCorrection_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>continuedCorrection S hS η u (x t) (w t) (z t)) := by
  letI : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  letI : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  unfold continuedCorrection ramifiedProduct unramifiedProduct
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro P hP
    exact ramifiedCorrection_measurable η u P.val _ x w z hx hw hz
  · apply Measurable.tprod
    intro P
    unfold unramifiedFactor
    split_ifs
    · exact measurable_const
    · exact idealUnramifiedCorrection_measurable η u P.val x w z hx hw hz

lemma continuedCompensatedLocal_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal) (hs : Supported P.val)
    (x w z B q : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z)
    (hB : Measurable B) (hq : Measurable q) :
    Measurable (fun t=>continuedCompensatedLocal η u P hs (x t) (w t) (z t) (B t) (q t)) := by
  have hM := continuedMarkedLocal_measurable η u P hs x w z hx hw hz
  have hQ : ((P.val.absNorm:ℝ):ℂ)≠0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold continuedCompensatedLocal ProbeLocal.compensatedReplacement coordV coordW coordD
  fun_prop (disch := exact hQ)

lemma LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  apply measurable_of_countable_not_continuousAt
  apply ((Set.finite_singleton (1:ℂ)).insert 0).countable.mono
  intro s hs
  by_contra hn
  have h0 : s≠0 := fun h=>hn (by simp [h])
  have h1 : s≠1 := fun h=>hn (by simp [h])
  exact hs (LFunction_differentiableAt χ h0 (Or.inl h1)).continuousAt

lemma regularizedL_measurable (χ : Character) : Measurable (HeckeReciprocal.regularizedL χ) := by
  apply measurable_of_countable_not_continuousAt
  apply (Set.countable_singleton (0:ℂ)).mono
  intro s hs
  by_contra hn
  exact hs (HeckeReciprocal.regularizedL_differentiableAt χ (by simpa using hn)).continuousAt

lemma reciprocal_measurable (χ : Character) : Measurable (HeckeReciprocal.reciprocal χ) := by
  have hL := LFunction_measurable χ
  have hR := regularizedL_measurable χ
  unfold HeckeReciprocal.reciprocal
  split_ifs <;> fun_prop

lemma continuedL_measurable (χ : Character) : Measurable (HeckeOrigin.continued χ) := by
  have hL := LFunction_measurable χ
  have hR := (HeckeOrigin.poleRemoved_entire χ).continuous.measurable
  unfold HeckeOrigin.continued
  split_ifs <;> fun_prop

lemma physicalCompensatedRow_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>physicalCompensatedRow S hS T hT η u (x t) (w t) (z t)) := by
  unfold physicalCompensatedRow continuedCompensatedRow
  apply Measurable.mul
  · exact (((LFunction_measurable _).comp (by fun_prop)).mul
      ((continuedL_measurable _).comp hw)).mul ((reciprocal_measurable _).comp hx)
  · apply Measurable.mul
    · exact continuedCorrection_measurable _ _ η u x w z hx hw hz
    · apply Finset.measurable_prod
      intro P hP
      have hQ : (P.val.val.absNorm:ℂ)≠0 := by
        exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero)
      apply continuedCompensatedLocal_measurable _ _ _ _ x w z _ _ hx hw hz
      · exact (measurable_const_cpow _ hQ x hx).const_mul _
      · exact measurable_const_cpow _ hQ _ hw.neg

lemma calibratedTupleValue_measurable {α : Type*} [MeasurableSpace α] {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (x w z : α→ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t=>calibratedTupleValue S hS hmax η u P hPS W Y (x t) (w t) (z t)) := by
  unfold calibratedTupleValue
  apply Measurable.mul
  · apply Measurable.const_mul
    apply Finset.measurable_prod
    intro i hi
    apply Measurable.const_mul
    apply measurable_const_cpow _ _ _ (hz.sub measurable_const)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr (P i).property.ne_zero)
  · exact physicalCompensatedRow_measurable S hS _ _ η u x w z hx hw hz

lemma calibratedTupleValue_onLines_aestronglyMeasurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (σ υ ξ : ℝ)
    (μ : Measure ((ℝ×ℝ)×ℝ)) :
    AEStronglyMeasurable (fun t : (ℝ×ℝ)×ℝ=>
      calibratedTupleValue S hS hmax η u P hPS W Y
        ((σ:ℂ)+t.1.1*Complex.I) ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)) μ :=
  (calibratedTupleValue_measurable S hS hmax η u P hPS W Y _ _ _
    (by fun_prop) (by fun_prop) (by fun_prop)).aestronglyMeasurable

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.PhysicalBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physical_tuple_sum (K : ℕ) (e δ a b r B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤ r) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → HeckeZeroSupremum.beta+8*e≤x.re →
      (1/2:ℝ)≤w.re → z.re=r →
      (∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
        (fun i=>hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨CL,hCL,hL⟩ := calibrated_scalar_growth e (δ/2) he he' (by linarith) (by linarith) S hS hmax
  obtain ⟨CG,hCG,hG⟩ := continued_selected_tuple_with_correction K (δ/2) a b r B (by linarith) ha hb hr hB
  refine ⟨CL*CG,mul_pos hCL hCG,?_⟩
  intro η u hu T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have ht : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val ∧ (4:ℝ)≤P.val.absNorm := by
    intro i P hP
    exact ⟨outside_prime_supported S hS.bad P (hT i P hP),by exact_mod_cast hS.tail.norm_four P (hT i P hP)⟩
  let L : ℂ := star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)
  let G : (∀i,T i)→ℂ := fun P=>continuedCorrection
    (markExclusions S (Finset.univ.image (fun i=>(P i).val)))
    (markedSourceExclusions S hS (Finset.univ.image (fun i=>(P i).val))) η u x w z*
    ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u (P i).val (ht i (P i).val (P i).property).1 x w z
        (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
        (((P i).val.val.absNorm:ℂ)^(-w))
  have heq (P:∀i,T i) : calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i (P i).val (P i).property) W Y x w z=L*G P :=
    calibratedTupleValue_factor S hS hmax η u _ (hdis P) _ W Y x w z
  have hLb : ‖L‖≤CL*(η.modulus.absNorm:ℝ)^(δ/2)*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2 :=
    hL η u hu x w z hxβ hw (by rw [hz];exact hr)
  have hGb : (∑P:(∀i,T i),‖G P‖)≤CG*N^(δ/2)*∏i,(Y i)^r :=
    hG (1/4) S hS hfirst η u T ht Y hY W hWS hWB x w z hx hw hz (by linarith)
  have hη : (η.modulus.absNorm:ℝ)^(δ/2)≤(η.modulus.absNorm:ℝ)^δ :=
    Real.rpow_le_rpow_of_exponent_le (HeckeLogarithmicInput.modulus_norm_ge_one η) (by linarith)
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  simp_rw [heq,norm_mul]
  rw [←Finset.mul_sum]
  calc
    _ ≤ (CL*(η.modulus.absNorm:ℝ)^(δ/2)*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2)*
        (CG*N^(δ/2)*∏i,(Y i)^r) :=
      mul_le_mul hLb hGb (Finset.sum_nonneg fun _ _=>norm_nonneg _) (by positivity)
    _ ≤ (CL*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2)*
        (CG*N^(δ/2)*∏i,(Y i)^r) := by gcongr
    _ = (CL*CG)*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ)*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
      have hp : N^(3/5+δ/2)*N^(δ/2)=N^(3/5+δ) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (CL*CG)*(η.modulus.absNorm:ℝ)^δ*(N^(3/5+δ/2)*N^(δ/2))*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.RowCount -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => HeckeFamily.O

lemma freeRow_count (R : Finset FreeRow) (H : ℝ) (hH : 1≤H)
    (hR : ∀u∈R,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤H) :
    (R.card:ℝ)≤128*H := by
  have hc := DescentFiberCost.finite_element_count_real (R.image Subtype.val) H hH (by
    intro a ha
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hR u hu)
  rw [Finset.card_image_of_injective R Subtype.val_injective] at hc
  exact hc

lemma frequencyWeight_ideal_norm (z : ℂ) (u : FreeRow) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖=
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-z.re) := by
  have hN : (0:ℝ)<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  unfold frequencyWeight elementNorm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.neg_re]

lemma dyadic_weighted_rows (a r C U : ℝ) (hC : 0≤C) (hU : 1≤U)
    (R : Finset FreeRow)
    (hR : ∀u∈R,U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(1+a-r) := by
  have hU0 : 0<U := by linarith
  have hcard : (R.card:ℝ)≤256*U := by
    have hc := freeRow_count R (2*U) (by linarith) (fun u hu=>(hR u hu).2)
    linarith
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (a-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := hU0.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      calc
        _ ≤ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-r)*
            (C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(a-r) := by
          rw [show a-r=(-r)+a by ring,Real.rpow_add hN]
          ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U
            ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) (a-r) (by norm_num) (by norm_num) hU0
            (by simpa only [one_mul] using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) := by simp
    _ ≤ (256*U)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hp : U*U^(a-r)=U^(1+a-r) := by
        rw [show 1+a-r=1+(a-r) by ring,Real.rpow_add hU0,Real.rpow_one]
      calc
        _ = (256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r))*(U*U^(a-r)) := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.DyadBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physical_row_dyad (K : ℕ) (e δ a b r B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤ r) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (U : ℝ),1≤U → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → HeckeZeroSupremum.beta+8*e≤x.re →
      (1/2:ℝ)≤w.re → z.re=r →
      (∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_tuple_sum K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
  let A : ℝ := ProbeSelectedPrimeSums.annularPower 1 2 (3/5+δ-r)
  have hA : 0<A := by
    have hh := le_max_left ((1:ℝ)^(3/5+δ-r)) ((2:ℝ)^(3/5+δ-r))
    rw [Real.one_rpow] at hh
    simpa only [A,ProbeSelectedPrimeSums.annularPower,Real.one_rpow] using (lt_of_lt_of_le zero_lt_one hh)
  refine ⟨256*C*A,by positivity,?_⟩
  intro η U hU R hR T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
  let F : FreeRow→ℝ := fun u=>∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
    (fun i=>hT i (P i).val (P i).property) W Y x w z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^δ*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  have hD : 0≤D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈R) : F u≤D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ) := by
    have hh := hmain η u (hR u hu).1 T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
    apply hh.trans_eq
    dsimp [D]
    ring
  have heq (u : FreeRow) :
      (∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)=
      ‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    simp only [norm_mul,Finset.mul_sum,F]
  simp_rw [heq]
  apply (dyadic_weighted_rows (3/5+δ) r D U hD hU R (fun u hu=>(hR u hu).2) F hF z hz).trans_eq
  change 256*D*A*U^(1+(3/5+δ)-r)=_
  rw [show (1:ℝ)+(3/5+δ)-r=8/5+δ-r by ring]
  dsimp [D]
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def physicalDyadNorm {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℝ :=
  ∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i (P i).val (P i).property) W Y x w z‖

lemma physicalDyadNorm_nonneg {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    0≤physicalDyadNorm S hS hmax η R T hT W Y x w z := by
  exact Finset.sum_nonneg fun u hu=>Finset.sum_nonneg fun P hP=>norm_nonneg _

lemma physicalDyadNorm_onLines_aestronglyMeasurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (σ υ r : ℝ) : AEStronglyMeasurable (fun p : HeightSpace=>physicalDyadNorm S hS hmax η R T hT W Y
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  unfold physicalDyadNorm
  simp_rw [norm_mul,frequencyWeight_ideal_norm]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  convert Finset.aestronglyMeasurable_sum R (fun u hu=>
    Finset.aestronglyMeasurable_sum (Finset.univ : Finset (∀i,T i)) (fun P hP=>
      (calibratedTupleValue_onLines_aestronglyMeasurable S hS hmax η u
        (fun i=>(P i).val) (fun i=>hT i (P i).val (P i).property) W Y σ υ r heightMeasure).norm.const_mul
          (((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-r)))) using 1
  ext p
  simp only [Finset.sum_apply]

theorem calibrated_physical_dyad_integral (K : ℕ) (e δ a b r B σ υ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤ r) (hB : 0≤B)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hυ : (1/2:ℝ)≤υ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (U : ℝ),1≤U → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀X Y0 Z : ℝ,0<X → 0<Y0 → 0<Z →
      Integrable (fun p : HeightSpace=>‖sourceMellinWeight W0 W1 X Y0 Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
          physicalDyadNorm S hS hmax η R T hT W Y
            ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure ∧
      (∫p : HeightSpace,‖sourceMellinWeight W0 W1 X Y0 Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
          physicalDyadNorm S hS hmax η R T hT W Y
            ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I) ∂heightMeasure)
      ≤C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*(∏i,(Y i)^r)*
        (X^(1/2-r)*Z^(σ+r-1)*Y0^(υ-1)) := by
  obtain ⟨C,hC,hD⟩ := calibrated_physical_row_dyad K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
  obtain ⟨D,hDp,hP⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r υ υ (by linarith)
  refine ⟨D*C,mul_pos hDp hC,?_⟩
  intro η U hU R hR T hT hdis Y hY W hWS hWB X Y0 Z hX hY0 hZ
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*(∏i,(Y i)^r)
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  have hA : 0≤A := by dsimp [A];positivity
  have hbnd (p : HeightSpace) : physicalDyadNorm S hS hmax η R T hT W Y
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)
      ≤A*(3+|p.1.1|)^2*(3+|p.2|)^2 := by
    have hh := hD η U hU R hR T hT hdis Y hY W hWS hWB
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)
      (by simpa using hσ) (by simpa using hσβ) (by simpa using hυ) (by simp)
    simpa only [A,physicalDyadNorm,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,mul_one,mul_zero,add_zero,zero_add] using hh
  obtain ⟨hi,hb⟩ := hP σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y0 Z hX hY0 hZ A hA _
    (physicalDyadNorm_onLines_aestronglyMeasurable S hS hmax η R T hT W Y σ υ r)
    (fun p=>physicalDyadNorm_nonneg S hS hmax η R T hT W Y _ _ _) hbnd
  refine ⟨hi,hb.trans_eq ?_⟩
  dsimp [A]
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.FixedIntegral -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma continuedPhysicalRowKernel_eq_calibratedTuple {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (hW : ∀i,W i (((P i).val.absNorm:ℝ)/Yp i)=1) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      sourceMellinWeight W0 W1 X Y Z x w z*frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u P hPS W Yp x w z := by
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      (Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold continuedPhysicalRowKernel calibratedTupleValue
  simp only [hW,one_mul,hnorm]
  ring

theorem continuedPhysicalRowKernel_integrable {K : ℕ}
    (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
    (hυ : (1/2:ℝ)≤υ) (hr : (17/50:ℝ)≤ r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : HeightSpace=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  let W : Fin K→ℝ→ℂ := fun _ y=>if y=1 then 1 else 0
  let Yp : Fin K→ℝ := fun i=>(P i).val.absNorm
  let T : Fin K→Finset ProbePhysical.PrimeIdeal := fun i=>{P i}
  have hT (i : Fin K) (Q : ProbePhysical.PrimeIdeal) (hQ : Q∈T i) : Q.val∉S := by
    have heq : Q=P i := Finset.mem_singleton.mp hQ
    simpa only [heq] using hPS i
  let P0 : ∀i,T i := fun i=>⟨P i,Finset.mem_singleton_self _⟩
  have hTP (Q : ∀i,T i) : (fun i=>(Q i).val)=P := by
    funext i
    exact Finset.mem_singleton.mp (Q i).property
  have hdis (Q : ∀i,T i) : Function.Injective (fun i=>(Q i).val) := by rw [hTP Q];exact hP
  have hYp (i : Fin K) : 1≤Yp i := by
    dsimp [Yp]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (P i).property.ne_zero)
  have hWS (i : Fin K) : Function.support (W i)⊆Icc (1:ℝ) 1 := by
    intro y hy
    by_cases h : y=1
    · simpa only [h] using (show (1:ℝ)∈Icc 1 1 from ⟨le_rfl,le_rfl⟩)
    · simp [W,h,Function.mem_support] at hy
  have hWB (i : Fin K) (y : ℝ) : ‖W i y‖≤1 := by dsimp [W];split_ifs <;> simp
  have hWeq (i : Fin K) : W i (((P i).val.absNorm:ℝ)/Yp i)=1 := by
    have hn : Yp i≠0 := by linarith [hYp i]
    simp [W,Yp,div_self hn]
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  have hU : 1≤U := by
    dsimp [U]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e (1/2) 1 1 r 1 σ υ he he'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by norm_num) hσ hσβ hυ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hR (v : FreeRow) (hv : v∈({u}:Finset FreeRow)) :
      v.val≠1 ∧ U≤((Ideal.span {v.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {v.val}:Ideal O).absNorm:ℝ)≤2*U := by
    have hvu := Finset.mem_singleton.mp hv
    subst v
    exact ⟨hu,le_rfl,by change U≤2*U;linarith⟩
  have hi := (hmain η U hU {u} hR T hT hdis Yp hYp W hWS hWB X Y Z hX hY hZ).1
  have hm := calibratedTupleValue_onLines_aestronglyMeasurable S hS hmax η u P hPS W Yp σ υ r heightMeasure
  have hfn : (elementNorm u.val:ℂ)≠0 := by
    exact_mod_cast (elementNorm_pos u.val u.property.1).ne'
  have hf : Continuous (fun p : HeightSpace=>frequencyWeight ((r:ℂ)+p.1.2*Complex.I) ⟨u.val,u.property.1⟩) := by
    unfold frequencyWeight
    exact (by fun_prop : Continuous (fun p : HeightSpace=>-((r:ℂ)+p.1.2*Complex.I))).const_cpow (Or.inl hfn)
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r υ (by linarith)
  have hme : AEStronglyMeasurable (fun p : HeightSpace=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
    simp_rw [continuedPhysicalRowKernel_eq_calibratedTuple S hS hmax P hPS η u W0 W1 X Y Z W Yp hWeq]
    exact (hs.mul hf).aestronglyMeasurable.mul hm
  apply hi.mono' hme
  apply Filter.Eventually.of_forall
  intro p
  rw [continuedPhysicalRowKernel_eq_calibratedTuple S hS hmax P hPS η u W0 W1 X Y Z W Yp hWeq]
  rw [mul_assoc,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  dsimp only [physicalDyadNorm]
  rw [Finset.sum_singleton]
  have hh := Finset.single_le_sum (fun Q (_ : Q∈(Finset.univ:Finset (∀i,T i)))=>norm_nonneg
    (frequencyWeight ((r:ℂ)+p.1.2*Complex.I) ⟨u.val,u.property.1⟩*
      calibratedTupleValue S hS hmax η u (fun i=>(Q i).val)
        (fun i=>hT i (Q i).val (Q i).property) W Yp ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I))) (Finset.mem_univ P0)
  exact hh

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.TailScales -/

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma selected_scale_power {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ) (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(1/6:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(23/48:ℝ))^((1/2:ℝ)-1))=Z^(β-11/16-79/800+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

lemma small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤Z) (hU : 1≤U)
    (hUsmall : U≤Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=(1/6:ℝ)) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(23/48:ℝ))^((1/2:ℝ)-1))≤Z^(β-11/16-63/800+8*e) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(β-11/16-79/800+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1;ring

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(1/6:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(17/48:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(23/48:ℝ))^((2:ℝ)-1))=
      Z^((53/32:ℝ)+(13/16:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.SmallDyad -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def absolutePhysicalDyadIntegral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) : ℝ :=
  ∫p : HeightSpace,‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
      physicalDyadNorm S hS hmax η R T hT W Yp ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I) ∂heightMeasure

theorem small_physical_dyad_bound (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z U : ℝ),1≤Z → 1≤U → U≤Z^(1/100:ℝ) →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    (HeckeZeroSupremum.beta+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) le_rfl le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU hUsmall R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=>Z^(length i)) hYp W hWS hWB
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  have hscale := small_row_scale_bound Z U δ hZ hU hUsmall hδ.le hδ' length hl HeckeZeroSupremum.beta e
  calc
    _ ≤ C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
        ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
          (Z^(23/48:ℝ))^((1/2:ℝ)-1)) := hh
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*(U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
        ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
          (Z^(23/48:ℝ))^((1/2:ℝ)-1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.LargeDyad -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_dyad_bound (K : ℕ) (δ a b B r : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤ r)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z U : ℝ),1≤Z → 1≤U →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((53/32:ℝ)+(13/16:ℝ)*r)*U^(8/5+δ-r) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K (1/2000) δ a b r B
    2 2 (by norm_num) (by norm_num) hδ hδ' ha hb hr hB
    (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num)
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=>Z^(length i)) hYp W hWS hWB
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  apply hh.trans_eq
  calc
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*U^(8/5+δ-r)*
      ((∏i,(Z^(length i))^r)*((Z^(17/48:ℝ))^(1/2-r)*Z^(2+r-1)*(Z^(23/48:ℝ))^((2:ℝ)-1))) := by ring
    _ = _ := by rw [large_source_scale Z hZ0 length hl r];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.GeometricTail -/

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0<Z) (n : ℕ) :
    Z^((53/32:ℝ)+(13/16:ℝ)*r)*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ< r) :
    Summable (fun n : ℕ=>Z^((53/32:ℝ)+(13/16:ℝ)*r)*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ< r) :
    (∑'n : ℕ,Z^((53/32:ℝ)+(13/16:ℝ)*r)*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma exists_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤ r ∧ 8/5+δ< r ∧
      (53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r≤-saving := by
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.LargeTail -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma absolutePhysicalDyadIntegral_nonneg {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) :
    0≤absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  apply integral_nonneg
  intro p
  exact mul_nonneg (norm_nonneg _) (physicalDyadNorm_nonneg S hS hmax η R T hT W Yp _ _ _)

theorem large_physical_dyads_summable (K : ℕ) (δ a b B r ζ : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤ r) (hr' : 8/5+δ< r) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r) := by
  obtain ⟨C,hC,hmain⟩ := large_physical_dyad_bound K δ a b B r hδ hδ' hr ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hq : (2:ℝ)^(8/5+δ-r)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨C*(1-(2:ℝ)^(8/5+δ-r))⁻¹,mul_pos hC (inv_pos.mpr (sub_pos.mpr hq)),?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r
  let g : ℕ→ℝ := fun n=>Z^((53/32:ℝ)+(13/16:ℝ)*r)*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ
  have hf0 (n : ℕ) : 0≤f n := absolutePhysicalDyadIntegral_nonneg S hS hmax η (R n) T hT W _ W0 W1 _ _ _ _ _ _
  have hbnd (n : ℕ) : f n≤A*g n := by
    have hUn : 1≤Z^((13/16:ℝ)+ζ)*(2:ℝ)^n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hZ (by linarith)) (one_le_pow₀ (by norm_num))
    have hh := hmain η Z (Z^((13/16:ℝ)+ζ)*(2:ℝ)^n) hZ hUn (R n) (hR n) T hT hdis length hl0 hl W hWS hWB
    simpa only [A,g,mul_assoc] using hh
  have hg : Summable g := large_geometric_summable Z ζ δ r hZ0 hr'
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbnd (hg.mul_left A)
  refine ⟨hf,?_⟩
  calc
    (∑'n,f n) ≤ ∑'n,A*g n := hf.tsum_le_tsum hbnd (hg.mul_left A)
    _ = A*(∑'n,g n) := tsum_mul_left
    _ = A*(Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹) := by
      rw [show (∑'n,g n)=_ from large_geometric_sum Z ζ δ r hZ0 hr']
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.LargeSaving -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_tail_arbitrary_saving (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃r C : ℝ,(17/50:ℝ)≤ r ∧ 0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,hr,hr',hpower⟩ := exists_large_tail_line ζ δ saving hζ
  obtain ⟨C,hC,hmain⟩ := large_physical_dyads_summable K δ a b B r ζ hδ hδ' hr hr' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨r,C,hr,hC,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hs,hb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  refine ⟨hs,hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpower) (by positivity)

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.SmallSum -/

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma small_dyadic_square_sum : ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
    (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^(2:ℝ))≤C*H^(2:ℝ) := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound 2 3 (by norm_num) (by norm_num)
  refine ⟨8*C,by positivity,?_⟩
  intro H hH F hF
  obtain ⟨hs,hb⟩ := hmain H⁻¹ (inv_pos.mpr hH)
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^(2:ℝ)≤8*CompletedDyadic.kernelTerm H⁻¹ 2 3 n := by
    have hd : 0<1+H⁻¹*(2:ℝ)^n := by positivity
    have hu : H⁻¹*(2:ℝ)^n≤1 := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_le_one hH).mpr (hF n hn)
    have hh : (1+H⁻¹*(2:ℝ)^n)^3≤(2:ℝ)^3 := pow_le_pow_left₀ hd.le (by linarith) 3
    unfold CompletedDyadic.kernelTerm
    norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hd 3)).mpr
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ((2:ℝ)^n))
    norm_num at hm
    nlinarith only [hm]
  calc
    _ ≤ ∑n∈F,8*CompletedDyadic.kernelTerm H⁻¹ 2 3 n := Finset.sum_le_sum hpoint
    _ = 8*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ 2 3 n := (Finset.mul_sum _ _ _).symm
    _ ≤ 8*∑'n,CompletedDyadic.kernelTerm H⁻¹ 2 3 n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by norm_num)
    _ ≤ 8*(C*(H⁻¹)^(-2:ℝ)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.SmallTail -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_physical_dyads_sum (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50))
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    (HeckeZeroSupremum.beta+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) le_rfl le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨D,hD,hsmall⟩ := small_dyadic_square_sum
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)
  have hA : 0≤A := by dsimp [A];positivity
  have hbnd (n : ℕ) (hn : n∈F) :
      absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
      ≤A*((2:ℝ)^n)^(2:ℝ) := by
    have hUn : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hh := (hmain η ((2:ℝ)^n) hUn (R n) (hR n hn) T hT hdis (fun i=>Z^(length i)) hYp
      W hWS hWB (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
    have hpow : ((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))≤((2:ℝ)^n)^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hUn (by linarith)
    have hscale := small_source_scale Z hZ0 length hl HeckeZeroSupremum.beta e
    calc
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))*
          Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e) := by
        apply hh.trans_eq
        rw [←hscale]
        ring
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(2:ℝ)*
          Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e) := by gcongr
      _ = _ := by dsimp [A];ring
  calc
    _ ≤ ∑n∈F,A*((2:ℝ)^n)^(2:ℝ) := Finset.sum_le_sum hbnd
    _ = A*∑n∈F,((2:ℝ)^n)^(2:ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(D*(Z^(1/100:ℝ))^(2:ℝ)) := mul_le_mul_of_nonneg_left
      (hsmall (Z^(1/100:ℝ)) (Real.rpow_pos_of_pos hZ0 _) F hF) hA
    _ = _ := by
      dsimp [A]
      rw [←Real.rpow_mul hZ0.le]
      have he : Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)*Z^((1/100:ℝ)*2)=
          Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
        rw [←Real.rpow_add hZ0]
        congr 1
        ring
      calc
        _ = (C*D)*(η.modulus.absNorm:ℝ)^δ*
            (Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)*Z^((1/100:ℝ)*2)) := by ring
        _ = _ := by rw [he]

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.ZContour -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma physicalCompensatedRow_first_z (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>physicalCompensatedRow S hS T hT η u x w z) z := by
  have hz0 : 6*z≠0 := by intro h;have hh:=congrArg Complex.re h;norm_num [Complex.mul_re] at hh;linarith
  have hz1 : 6*z≠1 := by intro h;have hh:=congrArg Complex.re h;norm_num [Complex.mul_re] at hh;linarith
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hz1)).comp z
      (differentiableAt_id.const_mul 6)).mul_const _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_z eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_z η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z (by linarith) (by linarith)

lemma sourceMellinWeight_differentiableAt_z (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w z : ℂ) (hz : 0<z.re) :
    DifferentiableAt ℂ (fun z=>sourceMellinWeight W0 W1 X Y Z x w z) z := by
  have hxc : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hzc : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hm := (ProbeRadialMellin.radial_mellin_analytic W0 z hz).differentiableAt
  unfold sourceMellinWeight
  fun_prop (disch := first | exact Or.inl hxc | exact Or.inl hzc)

theorem continuedPhysicalRowKernel_differentiableAt_z {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z := by
  have hm := sourceMellinWeight_differentiableAt_z W0 W1 X Y Z hX hZ x w z (by linarith)
  have hp : Differentiable ℂ (fun z : ℂ=>∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1)) := by
    apply Differentiable.fun_finsetProd
    intro i hi
    have hp0 := (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
    have hn : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (elementNorm_pos _ hp0).ne'
    exact (differentiable_id.sub_const 1).const_cpow (Or.inl hn)
  have hNu : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hfreq : Differentiable ℂ (fun z=>frequencyWeight z ⟨u.val,u.property.1⟩) :=
    differentiable_id.neg.const_cpow (Or.inl hNu)
  exact ((hm.mul (hp z)).mul (hfreq z)).mul
    ((physicalCompensatedRow_first_z eps heps S hS hfirst _ (contourTupleOutside S P hPS) η u x w z hx hw hz hxw).const_mul _)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.ZGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalRow_first_z_bounded (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) :
    ∃C : ℝ,0≤C ∧ ∀z : ℂ,(17/50:ℝ)≤z.re →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤C := by
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := HeckeReciprocalBound.bound 2*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  have hLb : 0≤HeckeReciprocalBound.bound 2 := by unfold HeckeReciprocalBound.bound; positivity
  have hL : 0≤L := by dsimp [L];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro z hz
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤HeckeReciprocalBound.bound 2 :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z hx hw hz hxw
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x.re x w z hx le_rfl
      hw hz (by linarith [hfirst.positive])
  unfold physicalCompensatedRow continuedCompensatedRow
  simp only [norm_mul]
  rw [mul_assoc L]
  apply mul_le_mul _ (mul_le_mul hh' hg (norm_nonneg _) (by dsimp [N];positivity))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hL
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl (norm_nonneg _)) (norm_nonneg _)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.XGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalRow_first_x_growth (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃C : ℝ,0≤C ∧ ∀x : ℂ,l≤x.re → x.re≤ r →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|x.im|)^2 := by
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e 1 he he' (by norm_num) (by norm_num) S hS.prime
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm r
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖
  let B : ℝ := Cr*(η.modulus.absNorm:ℝ)*N
  have hL : 0≤L := by dsimp [L];positivity
  have hB : 0≤B := by dsimp [B,N];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*B*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x hxl hxr
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤B*(3+|x.im|)^2 := by
    simpa only [Real.rpow_one] using hr η u x (hlβ.trans hxl)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z (hl.trans hxl) hw hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) r x w z (hl.trans hxl) hxr
      hw hz (by linarith [hfirst.positive])
  unfold physicalCompensatedRow continuedCompensatedRow
  simp only [norm_mul]
  calc
    _ ≤ L*(B*(3+|x.im|)^2)*((Ch*N)*(∏P:T,A P)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrec hL)
        (mul_le_mul hh' hg (norm_nonneg _) (by dsimp [N];positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.XBoundary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def xRowScalar {K : ℕ} (P : Fin K→ProbePhysical.PrimeIdeal) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y : ℝ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Y:ℂ)^(w-1)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_x_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      xRowScalar P u W0 W1 X Y w z*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel xRowScalar sourceMellinWeight
  ring

lemma coupled_gaussian_bound (z : ℂ) {l r v : ℝ} (hl : 0<l) (hv : v∈Icc l r) (t : ℝ) :
    ‖Complex.exp ((((v:ℂ)+t*I)+z-1)^2)‖≤
      Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)) := by
  rw [Complex.norm_exp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : ((((v:ℂ)+t*I)+z-1)^2).re=(v+z.re-1)^2-(t+z.im)^2 := by simp [pow_two]
  rw [hre]
  have hvp : 0<v := hl.trans_le hv.1
  have hA : |v+z.re-1|≤|z.re|+r+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le z.re,le_abs_self z.re,hv.2]
  have hh := pow_le_pow_left₀ (abs_nonneg (v+z.re-1)) hA 2
  rw [sq_abs] at hh
  linarith

theorem continuedPhysicalRowKernel_x_gaussian {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((v:ℂ)+t*I) w z‖≤
        B*Continuation.polynomialGaussian 2 (t+z.im) := by
  obtain ⟨C,hC,hrow⟩ := physicalRow_first_x_growth e eps he he' S hS hfirst _
    (contourTupleOutside S P hPS) η u w z l r hl hlβ hw hz hlw
  let A := ‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1)*
    Real.exp ((|z.re|+r+1)^2)*C
  have hA : 0≤A := by dsimp [A,scaleBound];positivity
  refine ⟨A*(2*(3+|z.im|)^2),by positivity,?_⟩
  intro v hv t
  have hZb := cpow_le_scaleBound hZ (((v:ℂ)+t*I)+z-1)
    (show (((v:ℂ)+t*I)+z-1).re∈Icc (l+z.re-1) (r+z.re-1) by
      simpa using And.intro (by linarith [hv.1] : l+z.re-1≤v+z.re-1)
        (by linarith [hv.2] : v+z.re-1≤ r+z.re-1))
  have hgb := coupled_gaussian_bound z (by linarith : 0<l) hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u ((v:ℂ)+t*I) w z‖≤C*(3+|t|)^2 := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
    simpa using hrow ((v:ℂ)+t*I) (by simpa using hv.1) (by simpa using hv.2)
  rw [continuedPhysicalRowKernel_x_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1))*
        (Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)))*(C*(3+|t|)^2) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hZb (norm_nonneg _)) hgb
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (scaleBound_pos _ _ _).le))
        hr (norm_nonneg _) (by unfold scaleBound;positivity)
    _ = A*(3+|t|)^2*Real.exp (-((t+z.im)^2)) := by dsimp [A];ring
    _ ≤ A*(2*(3+|z.im|)^2*(1+|t+z.im|^2))*Real.exp (-((t+z.im)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Continuation.shifted_height_two t z.im) hA) (Real.exp_pos _).le
    _ = _ := by unfold Continuation.polynomialGaussian;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.XShift -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem first_x_integral_eq {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((l:ℂ)+t*I) w z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((r:ℂ)+t*I) w z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_x_gaussian e (eps/2) he he' S hS hfirst hmax P hPS
    η u W0 W1 X Y Z hZ w z l r hl hlβ hw hz (by linarith)
  apply Continuation.vertical_integral_eq_of_shifted_polynomial_gaussian_bound
    (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z.im 2 hlr _ hbound
  intro x hx
  apply (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hZ x w z (hl.trans hx.1) hw hz (by linarith [hx.1]) ?_).differentiableWithinAt
  intro hpole
  exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt _ (by linarith [hx.1]) (by tauto)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

