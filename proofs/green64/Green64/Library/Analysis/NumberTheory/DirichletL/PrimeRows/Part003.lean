module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeCounting.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part019
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part009
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.StripActual
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / PrimeRows / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalContour -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma calibrated_physicalRow_first_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun w=>star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z) w := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiableAt_const _
  · have hp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    apply DifferentiableAt.const_mul
    unfold physicalCompensatedRow continuedCompensatedRow
    apply DifferentiableAt.mul
    · exact ((HeckeOrigin.continued_differentiableAt _ (Or.inr hp)).const_mul _).mul_const _
    · apply DifferentiableAt.mul
      · exact (continuedCorrection_first_boundary_w eps heps (markExclusions S T)
          (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
          hx hw hz hxw).differentiableAt
      · apply DifferentiableAt.fun_finsetProd
        intro P hP
        exact (continuedCompensatedLocal_first_differentiable_w η u P.val _
          (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z
          (by linarith) (by linarith)) w

theorem contourTupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→ProbePhysical.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def continuedPhysicalRowKernel {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z x w z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z)

theorem continuedPhysicalRowKernel_initial {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (t : ProbeMellinBoundary.HeightSpace) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)=
    compensatedRowOnLines η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z ⟨u.val,u.property.1⟩ t := by
  unfold continuedPhysicalRowKernel physicalCompensatedRow compensatedRowOnLines
  rw [continuedCompensatedRow_eq_indexed S hS P hP hPS η u _ _ _
    (by norm_num) (by norm_num) (by norm_num)]
  ring

lemma sourceMellinWeight_differentiable_w (W0 W1 : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) :
    Differentiable ℂ (fun w=>sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hm : Differentiable ℂ (mellin W1) := fun w=>
    CubicReflectionKernel.compact_source_mellin_differentiable W1 a b ha hW (W1.smooth (⊤:ℕ∞)) w
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hy)

theorem continuedPhysicalRowKernel_differentiableAt_w {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) w := by
  exact (((sourceMellinWeight_differentiable_w W0 W1 a b ha hW X Y Z hY x z) w).mul_const _ |>.mul_const _).mul
    (calibrated_physicalRow_first_w eps heps S hS hfirst hmax _ (contourTupleOutside S P hPS) η u hu x w z hx hw hz hxw)

theorem nonprincipal_w_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r T : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hr : -(1/100:ℝ)≤ r)
    (hz : (17/50:ℝ)≤z.re) (hxl : 1+eps≤x.re+l) (hxr : 1+eps≤x.re+r) :
    let F := fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro w hw
    have hwlo : min l r≤w.re := hw.1.1
    have hw' : -(1/100:ℝ)≤w.re := (le_min hl hr).trans hwlo
    have hxw : 1+eps≤x.re+w.re := by
      have := (le_min (by linarith : 1+eps-x.re≤l) (by linarith : 1+eps-x.re≤ r)).trans hwlo
      linarith
    exact (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
      W0 W1 a b ha hW X Y Z hY x w z hx hw' hz hxw).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.BufferedContour -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma reciprocal_differentiableAt_of_nonzero (χ : Character) (s : ℂ) (h0 : s≠0)
    (hnz : ¬(χ.residue=1 ∧ s=1) → LFunction χ s≠0) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal χ) s := by
  by_cases hχ : χ.residue=1
  · have hr : HeckeReciprocal.regularizedL χ s≠0 := by
      by_cases hs : s=1
      · subst s
        exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ
      · rw [HeckeReciprocal.regularizedL_eq χ h0 hs]
        exact mul_ne_zero (sub_ne_zero.mpr hs) (hnz (by simp [hs]))
    have he : HeckeReciprocal.reciprocal χ=(fun z=>(z-1)/HeckeReciprocal.regularizedL χ z) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,ite_eq_left hχ]
    rw [he]
    exact (differentiableAt_id.sub_const 1).div
      (HeckeReciprocal.regularizedL_differentiableAt χ h0) hr
  · have he : HeckeReciprocal.reciprocal χ=(fun z=>(LFunction χ z)⁻¹) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,ite_eq_right hχ]
    rw [he]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv (hnz (by simp [hχ]))

theorem physicalCompensatedRow_buffered_differentiableAt_x
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>physicalCompensatedRow S hS T hT η u x w z) x := by
  have hx0 : x≠0 := by intro h;norm_num [h] at hx
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (reciprocal_differentiableAt_of_nonzero _ x hx0 hnz).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z (by linarith) (by linarith)

lemma sourceMellinWeight_differentiable_x (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) :
    Differentiable ℂ (fun x=>sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hz)

theorem continuedPhysicalRowKernel_buffered_differentiableAt_x {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) x :=
  (((sourceMellinWeight_differentiable_x W0 W1 X Y Z hZ w z) x).mul_const _ |>.mul_const _).mul
    ((physicalCompensatedRow_buffered_differentiableAt_x eps heps S hS hfirst _
      (contourTupleOutside S P hPS) η u x w z hx hw hz hxw hnz).const_mul _)

theorem buffered_x_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r T : ℝ)
    (hl : (51/100:ℝ)≤l) (hr : (51/100:ℝ)≤ r) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hlw : 1+eps≤l+w.re) (hrw : 1+eps≤ r+w.re)
    (hnz : ∀x∈(uIcc l r ×ℂ uIcc (-T) T),
      ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
        LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro x hx
    have hxlo : min l r≤x.re := hx.1.1
    have hx' : (51/100:ℝ)≤x.re := (le_min hl hr).trans hxlo
    have hxw : 1+eps≤x.re+w.re := by
      have := (le_min (by linarith : 1+eps-w.re≤l) (by linarith : 1+eps-w.re≤ r)).trans hxlo
      linarith
    exact (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hZ x w z hx' hw hz hxw (hnz x hx)).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.DetectorZeros -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily

def detectorEntire (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue=1 then HeckeOrigin.poleRemoved χ s else HeckeOrigin.continued χ s

lemma detectorEntire_eq_nonprincipal (χ : Character) (hχ : χ.residue≠1) :
    detectorEntire χ=LFunction χ := by
  funext s
  simp only [detectorEntire,HeckeOrigin.continued,ite_eq_right hχ]

lemma detectorEntire_entire (χ : Character) : Differentiable ℂ (detectorEntire χ) := by
  by_cases hχ : χ.residue=1
  · have he : detectorEntire χ=HeckeOrigin.poleRemoved χ := by funext s;simp [detectorEntire,hχ]
    rw [he]
    exact HeckeOrigin.poleRemoved_entire χ
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    exact LFunction_entire_nonprincipal χ hχ

lemma detectorEntire_zero_iff (χ : Character) {s : ℂ} (hs : 0<s.re) :
    detectorEntire χ s=0 ↔ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · simp only [detectorEntire,ite_eq_left hχ]
    by_cases h1 : s=1
    · subst s
      simp [HeckeOrigin.poleRemoved_one_ne_zero χ hχ,hχ]
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
      simp [mul_eq_zero,sub_ne_zero.mpr h1,h1]
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    simp [hχ]

lemma detectorEntire_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1<s.re) :
    detectorEntire χ s≠0 := by
  intro hz
  exact LFunction_ne_zero_of_one_lt_re χ hs ((detectorEntire_zero_iff χ (by linarith)).mp hz).1

def detectorZeros (χ : Character) (T : ℝ) : Set ℂ :=
  {s | s∈HeckeDetectorZeros.rectangle T ∧ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1)}

lemma detectorZeros_finite (χ : Character) (T : ℝ) : (detectorZeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (detectorEntire χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (detectorEntire_entire χ)
  have hc := ha.preimage_zero_mem_codiscreteWithin
    (detectorEntire_ne_zero_of_one_lt_re χ (by norm_num : 1<(2:ℂ).re))
    (Set.mem_univ (2:ℂ)) isConnected_univ
  have hf := (HeckeDetectorZeros.rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (HeckeDetectorZeros.rectangle T)) hc)
  convert hf using 1
  ext s
  by_cases hs : s∈HeckeDetectorZeros.rectangle T
  · have hr : 0<s.re := by have h:=hs.1;linarith
    simp [detectorZeros,hs,detectorEntire_zero_iff χ hr]
  · simp [detectorZeros,hs]

def detectorZeroFinset (χ : Character) (T : ℝ) : Finset ℂ := (detectorZeros_finite χ T).toFinset

@[simp] lemma mem_detectorZeroFinset (χ : Character) (T : ℝ) (s : ℂ) :
    s∈detectorZeroFinset χ T ↔ (51/100:ℝ)≤ s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  simp only [detectorZeroFinset,Set.Finite.mem_toFinset,detectorZeros,HeckeDetectorZeros.rectangle,Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def detectorFamilyZeros (χ : ι→Character) (T : ℝ) : Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i=>(detectorZeroFinset (χ i) T).image (fun s=>(i,s)))

@[simp] lemma mem_detectorFamilyZeros (χ : ι→Character) (T : ℝ) (i : ι) (s : ℂ) :
    (i,s)∈detectorFamilyZeros χ T ↔ (51/100:ℝ)≤ s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) := by
  simp [detectorFamilyZeros]

def detectorRealParts (χ : ι→Character) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((detectorFamilyZeros χ T).image (fun p=>p.2.re))

lemma detectorRealParts_nonempty (χ : ι→Character) (T : ℝ) : (detectorRealParts χ T).Nonempty :=
  Finset.insert_nonempty _ _

def detectorMaximum (χ : ι→Character) (T : ℝ) : ℝ :=
  (detectorRealParts χ T).max' (detectorRealParts_nonempty χ T)

lemma detectorMaximum_mem (χ : ι→Character) (T : ℝ) : detectorMaximum χ T∈detectorRealParts χ T :=
  Finset.max'_mem _ _

lemma detectorMaximum_bounds (χ : ι→Character) (T : ℝ) :
    (51/100:ℝ)≤detectorMaximum χ T ∧ detectorMaximum χ T≤1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · norm_num
    · obtain ⟨⟨i,s⟩,hs,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_detectorFamilyZeros χ T i s |>.mp hs).2.1

lemma detector_zero_re_le_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : (51/100:ℝ)≤ s.re) (ht : |s.im|≤T) (hz : LFunction (χ i) s=0)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : s.re≤detectorMaximum χ T := by
  have hle : s.re≤1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s),(mem_detectorFamilyZeros χ T i s).mpr ⟨hs,hle,ht,hz,hpole⟩,rfl⟩)

lemma detectorMaximum_attained (χ : ι→Character) (T : ℝ)
    (hmax : (51/100:ℝ)<detectorMaximum χ T) :
    ∃i s,LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) ∧
      |s.im|≤T ∧ s.re=detectorMaximum χ T := by
  have hm := detectorMaximum_mem χ T
  rcases Finset.mem_insert.mp hm with hm|hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩,hs,heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_detectorFamilyZeros χ T i s).mp hs
    exact ⟨i,s,hz.2.2.2.1,hz.2.2.2.2,hz.2.2.1,heq⟩

lemma detectorMaximum_mono (χ : ι→Character) {T T' : ℝ} (hT : T≤T') :
    detectorMaximum χ T≤detectorMaximum χ T' := by
  rcases lt_or_ge (51/100:ℝ) (detectorMaximum χ T) with hm|hm
  · obtain ⟨i,s,hz,hpole,ht,heq⟩ := detectorMaximum_attained χ T hm
    rw [←heq]
    exact detector_zero_re_le_maximum χ T' i (by rw [heq];exact hm.le) (ht.trans hT) hz hpole
  · exact hm.trans (detectorMaximum_bounds χ T').1

lemma detector_nonzero_above_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : detectorMaximum χ T<s.re) (ht : |s.im|≤T)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : LFunction (χ i) s≠0 := by
  intro hz
  exact (not_lt_of_ge (detector_zero_re_le_maximum χ T i
    ((detectorMaximum_bounds χ T).1.trans hs.le) ht hz hpole)) hs

lemma detector_reciprocal_differentiableAt (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : detectorMaximum χ T<s.re) (ht : |s.im|≤T) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal (χ i)) s := by
  apply reciprocal_differentiableAt_of_nonzero (χ i) s
    (by intro h;have hb:=(detectorMaximum_bounds χ T).1;norm_num [h] at hs;linarith)
  exact detector_nonzero_above_maximum χ T i hs ht

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.DetectorBins -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily
variable {ι : Type*} [Fintype ι]

lemma detector_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e))
    (hpole : ¬((χ j).residue=1 ∧ s=1)) : LFunction (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e≤ s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  have him : |s.im|≤3*(i+1:ℕ)*T := by
    have ht' := abs_add_le (s.im-t) t
    rw [sub_add_cancel] at ht'
    push_cast at ht ⊢
    nlinarith [hi.trans hn]
  exact detector_nonzero_above_maximum χ _ j (hmax.trans_le hre) him hpole

lemma detectorEntire_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e)) :
    detectorEntire (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr
  have hre : 0<s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  intro hz
  obtain ⟨hL,hpole⟩ := (detectorEntire_zero_iff (χ j) hre).mp hz
  exact detector_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht hs hpole hL

lemma exists_detector_buffered_bin (χ : ι→Character)
    (T e : ℝ) (hT : 2<T) (he : 0<e) (n : ℕ) (hn : 0<n)
    (hwidth : (49/100:ℝ)≤n*e) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n ∧
      let a : ℝ := 51/100+e*k
      a≤1 ∧ a≤detectorMaximum χ (3*i*T) ∧
      detectorMaximum χ (3*i*T)<a+e ∧
      detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e ∧
      (51/100<a → ∃j s,LFunction (χ j) s=0 ∧ ¬((χ j).residue=1 ∧ s=1) ∧
        a≤ s.re ∧ s.re<a+e ∧ |s.im|≤3*i*T) ∧
      (∀j t,|t|≤(3*i+2:ℕ)*T → ∀s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e),
        detectorEntire (χ j) s≠0) := by
  let M : ℕ→ℝ := fun j=>detectorMaximum χ (3*(j+1:ℕ)*T)
  obtain ⟨i,hk,k,hone,hlo,hhi,hnext⟩ := Detector.exists_buffered_bin M hn he
    (fun j _=>detectorMaximum_bounds χ _) hwidth
  refine ⟨i+1,k,by omega,by omega,hone,hlo,hhi,?_,?_,?_⟩
  · exact hnext
  · intro ha
    obtain ⟨j,s,hz,hpole,ht,hs⟩ := detectorMaximum_attained χ (3*(i+1:ℕ)*T) (lt_of_lt_of_le ha hlo)
    exact ⟨j,s,hz,hpole,by rw [hs];exact hlo,by rw [hs];exact hhi,ht⟩
  · intro j t ht s hs
    apply detectorEntire_nonzero_on_buffered_disk χ T (51/100+e*k) e (i+1) hT
      (by nlinarith [Nat.cast_nonneg (α:=ℝ) k]) he hnext j t ht hs

lemma detectorMaximum_eq_nonprincipal (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ) :
    detectorMaximum χ T=HeckeDetectorZeros.zeroMaximum χ hχ T := by
  have hz (i : ι) : detectorZeroFinset (χ i) T=HeckeDetectorZeros.zeroFinset (χ i) (hχ i) T := by
    ext s
    simp [hχ i]
  have hr : detectorRealParts χ T=HeckeDetectorZeros.realParts χ hχ T := by
    simp only [detectorRealParts,HeckeDetectorZeros.realParts,detectorFamilyZeros,HeckeDetectorZeros.familyZeros,hz]
  unfold detectorMaximum HeckeDetectorZeros.zeroMaximum
  simp only [hr]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.BufferedBin -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def sourceDetectorFamily (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) : Sum Bool ι→Character :=
  Sum.elim (fun b=>if b then rowCharacter S hS u else (targetRow η u).excludePrimes S hS) ψ

omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_denominator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl false)=(targetRow η u).excludePrimes S hS := rfl

omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_numerator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl true)=rowCharacter S hS u := rfl

lemma source_bin_denominator_nonzero (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) (T a e : ℝ) (i : ℕ) (he : 0<e)
    (hmax : detectorMaximum (sourceDetectorFamily S hS η u ψ) (3*(i+1:ℕ)*T)<a+2*e)
    (x : ℂ) (hx : a+16*e≤x.re) (ht : |x.im|≤3*(i+1:ℕ)*T)
    (hpole : ¬(((targetRow η u).excludePrimes S hS).residue=1 ∧ x=1)) :
    LFunction ((targetRow η u).excludePrimes S hS) x≠0 :=
  detector_nonzero_above_maximum (sourceDetectorFamily S hS η u ψ) _ (Sum.inl false)
    (by linarith) ht hpole

theorem source_buffered_x_rectangle {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmaxS : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (ψ : ι→Character)
    (T a e : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hfirst : FirstTail (4*e) S)
    (hmax : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*T)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z)
    (w z : ℂ) (hw : w.re=1-a-6*e) (hz : (17/50:ℝ)≤z.re)
    (r H : ℝ) (hr : a+16*e≤ r) (hH : 0≤H) (hHT : H≤3*(i+1:ℕ)*T) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmaxS P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -H..H,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+t*I))+
        I*((∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+(-H)*I))-
          (∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+H*I))) := by
  apply buffered_x_rectangle (8*e) (by positivity) S hS
    (by convert hfirst using 1 ; ring) hmaxS P hPS η u W0 W1 X Y Z hZ w z (a+16*e) r H
    (by linarith) (by linarith) (by rw [hw];linarith) hz (by rw [hw];linarith) (by rw [hw];linarith)
  intro x hx hpole
  have hxr : a+16*e≤x.re := by simpa only [min_eq_left hr] using hx.1.1
  have hxi : |x.im|≤H := by
    apply abs_le.mpr
    simpa only [uIcc_of_le (by linarith : -H≤H),Set.mem_preimage,Set.mem_Icc] using hx.2
  exact source_bin_denominator_nonzero S hS.prime η u ψ T a e i he hmax x hxr (hxi.trans hHT) hpole

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.DiskControl -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

lemma poleRemoved_eq_regularizedL (χ : Character) {s : ℂ} (hs : 0<s.re) :
    HeckeOrigin.poleRemoved χ s=HeckeReciprocal.regularizedL χ s := by
  by_cases h1 : s=1
  · subst s;exact HeckeOrigin.poleRemoved_one χ
  · have h0 : s≠0 := by intro h;simp [h] at hs
    rw [HeckeOrigin.poleRemoved_eq χ h0 h1,HeckeReciprocal.regularizedL_eq χ h0 h1]

lemma regular_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0<s.re) : regular χ s=regular ψ s*factors χ.modulus ψ s := by
  by_cases hχ : χ.residue=1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [regular,ite_eq_left hχ,ite_eq_left hψ,HeckePrincipalStrip.sourceNormalized,
      poleRemoved_eq_regularizedL χ hs,poleRemoved_eq_regularizedL ψ hs]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue≠1 := fun h=>hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    rw [regular_eq_nonprincipal χ hχ,regular_eq_nonprincipal ψ hψ]
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

lemma regular_eq_detector (χ : Character) (s : ℂ) :
    regular χ s=if χ.residue=1 then detectorEntire χ s/(s+1) else detectorEntire χ s := by
  by_cases hχ : χ.residue=1
  · simp [regular,detectorEntire,HeckePrincipalStrip.sourceNormalized,hχ]
  · simp [regular,detectorEntire_eq_nonprincipal χ hχ,hχ]

lemma regular_nonzero_of_detector (χ : Character) {s : ℂ} (hs : 0<s.re)
    (hz : detectorEntire χ s≠0) : regular χ s≠0 := by
  rw [regular_eq_detector]
  split_ifs
  · apply div_ne_zero hz
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  · exact hz

lemma reciprocal_norm_le_regular_inverse_on_positive (χ : Character) {s : ℂ}
    (hs : 0<s.re) (hz : regular χ s≠0) :
    ‖HeckeReciprocal.reciprocal χ s‖≤‖(regular χ s)⁻¹‖ := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · by_cases h1 : s=1
    · subst s
      rw [HeckeReciprocal.reciprocal_principal_one χ hχ,norm_zero]
      exact norm_nonneg _
    have hp : s+1≠0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
      linarith
    have hL : LFunction χ s≠0 := by
      intro h
      apply hz
      simp [regular,hχ,HeckePrincipalStrip.sourceNormalized,HeckeOrigin.poleRemoved_eq χ h0 h1,h]
    have heq : HeckeReciprocal.reciprocal χ s=((s-1)/(s+1))*(regular χ s)⁻¹ := by
      rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
      simp only [regular,ite_eq_left hχ,HeckePrincipalStrip.sourceNormalized,HeckeOrigin.poleRemoved_eq χ h0 h1]
      field_simp
    rw [heq,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hp)).mpr (principal_regular_factor_bound hs.le)
  · simp only [HeckeReciprocal.reciprocal,regular,ite_eq_right hχ,le_refl]

theorem original_regular_disk_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character), ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular χ z‖ + ‖HeckeReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  obtain ⟨Dp,B,hDp,_,hprimitive⟩ := HeckeLogarithmicActual.disk_control e ε he he' hε
  obtain ⟨Cd,hCd,hdelete⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Dp*Cd,mul_pos hDp hCd,?_⟩
  intro χ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [regular_eq_of_mask χ ψ hmask hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).1 z hz
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := hdelete χ.modulus ψ z hzre
  have hL : regular χ z = regular ψ z*factors χ.modulus ψ z :=
    regular_eq_of_mask χ ψ hmask hzpos
  have hR : HeckeReciprocal.reciprocal χ z =
      HeckeReciprocal.reciprocal ψ z*(factors χ.modulus ψ z)⁻¹ :=
    HeckeDeletionReciprocal.reciprocal_eq_of_mask χ ψ hmask hzpos
  have hrec := reciprocal_norm_le_regular_inverse_on_positive ψ hzpos (hzeroψ z hz2)
  have hdel1 : ‖factors χ.modulus ψ z‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg ((factors χ.modulus ψ z)⁻¹)]
  have hdel2 : ‖(factors χ.modulus ψ z)⁻¹‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ z)]
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ t := (Real.exp_pos 1).le.trans (complexity_ge_exp ψ t)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  rw [hL,hR,norm_mul,norm_mul]
  calc
    _ ≤ (‖regular ψ z‖+‖(regular ψ z)⁻¹‖)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (regular ψ z))
      have h2 := mul_le_mul hrec hdel2 (norm_nonneg _) (norm_nonneg _)
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_regular_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (T a : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e →
      ∀j t,|t|≤(3*i+2:ℕ)*T →
      ∀z∈closedBall ((2:ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖≤
          C*(presentationComplexity (χ j) t)^ε := by
  obtain ⟨C,hC,hbound⟩ := original_regular_disk_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ T a i hT ha ha1 hmax j t ht z hz
  apply hbound (χ j) a t (by linarith) ha1 _ z hz
  intro w hw
  have hre : 0<w.re := by have h:=LogarithmicControl.disk_re_gt hw;linarith
  exact regular_nonzero_of_detector (χ j) hre
    (detectorEntire_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht (ball_subset_closedBall hw))

theorem buffered_rectangle_reciprocal_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (T a H : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      H≤(3*i+2:ℕ)*T → detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e →
      ∀j z,a+16*e≤z.re → z.re≤2 → |z.im|≤H →
        ‖HeckeReciprocal.reciprocal (χ j) z‖≤C*(presentationComplexity (χ j) H)^ε := by
  obtain ⟨C,hC,hbound⟩ := buffered_regular_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ T a H i hT ha ha1 hHT hmax j z hzl hzr hzi
  have hz : z∈closedBall ((2:ℂ)+z.im*Complex.I) (2-a-6*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2:ℂ)+z.im*Complex.I)=((z.re-2:ℝ):ℂ) := by apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have hb := hbound χ T a i hT ha ha1 hmax j z.im (hzi.trans hHT) z hz
  have hc : presentationComplexity (χ j) z.im≤presentationComplexity (χ j) H := by
    unfold presentationComplexity complexity
    have hH : 0≤H := (abs_nonneg _).trans hzi
    rw [abs_of_nonneg hH]
    gcongr
  have hnonneg : 0≤presentationComplexity (χ j) z.im := by
    unfold presentationComplexity complexity
    positivity
  apply (le_trans (le_add_of_nonneg_left (norm_nonneg _)) hb).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnonneg hc hε.le) hC.le

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.RowReflectedAllocation -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ComplexConjugate
open Set Complex
namespace SevenEighths.ProbeRowReflectedAllocation
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeFiniteDeletion HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma prod_rpow_nonneg {ι : Type*} (T : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ T, 0 ≤ q i) (A : ℝ) :
    (∏ i ∈ T, q i) ^ A = ∏ i ∈ T, (q i) ^ A := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      Real.mul_rpow (hq i (Finset.mem_insert_self i T))
        (Finset.prod_nonneg (fun j hj => hq j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))]

lemma selected_exponent_allocation {a e : ℝ} (ha : 51/100 ≤ a)
    (he : 0 < e) {j : ℕ} (hj : 2 ≤ j) :
    -(1-a-6*e) ≤ (j-1 : ℕ)*(a-1/2+6*e)-1/2 := by
  have hA : 0 ≤ a-1/2+6*e := by linarith
  have hj' : (1 : ℝ) ≤ (j-1 : ℕ) := by exact_mod_cast (show 1 ≤ j-1 by omega)
  nlinarith [mul_le_mul_of_nonneg_right hj' hA]

theorem allocation_of_deficit {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ i, 1 ≤ q i) (j : Fin k → ℕ) (hj : ∀ i, 2 ≤ j i)
    (N D a e : ℝ) (hN : 0 ≤ N) (ha : 51/100 ≤ a) (he : 0 < e)
    (hdef : N * ∏ i, q i ^ (j i-1) ≤ D) :
    N ^ (a-1/2+6*e) * ∏ i, q i ^ (-(1-a-6*e)) ≤
      D ^ (a-1/2+6*e) * ∏ i, q i ^ (-(1/2 : ℝ)) := by
  let A := a-1/2+6*e
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hq0 (i) : 0 ≤ q i := (by linarith [hq i])
  have hlocal (i) : q i ^ (-(1-a-6*e)) ≤
      (q i ^ (j i-1)) ^ A * q i ^ (-(1/2 : ℝ)) := by
    rw [← Real.rpow_natCast_mul (hq0 i), ← Real.rpow_add (by linarith [hq i])]
    apply Real.rpow_le_rpow_of_exponent_le (hq i)
    exact selected_exponent_allocation ha he (hj i)
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => Real.rpow_nonneg (hq0 i) _)
    (fun i _ => hlocal i)
  rw [Finset.prod_mul_distrib, ← prod_rpow_nonneg Finset.univ
    (fun i => q i ^ (j i-1)) (fun i _ => pow_nonneg (hq0 i) _) A] at hprod
  have hD0 : 0 ≤ ∏ i, q i ^ (j i-1) := Finset.prod_nonneg (fun i _ => pow_nonneg (hq0 i) _)
  calc
    _ ≤ N ^ A * ((∏ i, q i ^ (j i-1)) ^ A * ∏ i, q i ^ (-(1/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hN _)
    _ = (N * ∏ i, q i ^ (j i-1)) ^ A * ∏ i, q i ^ (-(1/2 : ℝ)) := by
      rw [Real.mul_rpow hN hD0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (mul_nonneg hN hD0) hdef hA)
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hq0 i) _))

lemma prime_norm_ge_one (P : Ideal O) (hP : Prime P) : (1 : ℝ) ≤ P.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)

lemma original_row_conductor_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((rowCharacter S hS u).modulus.absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm := by
  exact_mod_cast (by simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm]
    using rowCharacter_conductor S hS u)

lemma original_row_deletion_radical_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm :=
  by
    let χ := rowCharacter S hS u
    have hd : radical χ.modulus ∣ χ.modulus := by
      unfold radical SmoothMobiusCorrection.primeProduct
      rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O => J)]
      exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
    have hn : ((radical χ.modulus).absNorm : ℝ) ≤ χ.modulus.absNorm := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
    exact hn.trans (original_row_conductor_le S hS u)

theorem row_same_primitive_allocation (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
        if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (j : Fin k → ℕ), (∀ i, 2 ≤ j i) →
          (∀ i, P i ^ j i ∣ Ideal.span {u.val}) →
          ∀ a e : ℝ, 51/100 ≤ a → 0 < e →
          (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
              ∏ i, ((P i).absNorm : ℝ) ^ (-(1-a-6*e)) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) ^
              (a-1/2+6*e) * ∏ i, ((P i).absNorm : ℝ) ^ (-(1/2 : ℝ)) := by
  obtain ⟨ψ, hle, hp, hm, hdef⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis j hj hdiv a e ha he
  apply allocation_of_deficit _ (fun i => prime_norm_ge_one _ (hP i)) j hj
    _ _ a e (by positivity) ha he
  exact_mod_cast hdef k P hP hdis j hj hdiv

lemma actual_multiplicity_divisor (u : FreeRow) (p : O) (hp : Prime p) :
    (Ideal.span {p} : Ideal O) ^ multiplicity p u.val ∣ Ideal.span {u.val} ∧
      multiplicity p u.val < 6 := by
  refine ⟨⟨Ideal.span {unitPart u p hp}, ?_⟩, multiplicity_lt_six u p hp⟩
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun x : O => (Ideal.span {x} : Ideal O)) (unitPart_spec u p hp).1

lemma actual_ideal_multiplicity (u : FreeRow) (P : Ideal O) (hP : Prime P) :
    P ^ multiplicity P (Ideal.span {u.val} : Ideal O) ∣ Ideal.span {u.val} ∧
      multiplicity P (Ideal.span {u.val} : Ideal O) < 6 := by
  refine ⟨pow_multiplicity_dvd _ _, ?_⟩
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hP.irreducible
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1), normalize_eq]
  exact u.property.2 P

theorem buffered_reflected_right_bound (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι), (χ j).residue ≠ 1 →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) (1-conj w)‖ ≤
        C * (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := buffered_regular_control e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro ι _ χ B a i hB ha ha1 hmax j hχ w hw hwi
  have hwr : (1-conj w).re = a+6*e := by simp; linarith
  have hwm : (1-conj w).im = w.im := by simp
  have hz : 1-conj w ∈ Metric.closedBall ((2 : ℂ)+w.im*I) (2-a-6*e) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : 1-conj w-((2 : ℂ)+w.im*I) = ((a+6*e-2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp; linarith
      · simp
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have h := hb χ B a i hB ha ha1 hmax j w.im hwi (1-conj w) hz
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal _ hχ] at h
  have hH : 0 ≤ (3*i+2 : ℕ)*B := (abs_nonneg _).trans hwi
  have hc : presentationComplexity (χ j) w.im ≤
      presentationComplexity (χ j) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    rw [abs_of_nonneg hH]
    gcongr
  apply (le_trans (le_add_of_nonneg_right (norm_nonneg _)) h).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by
    unfold presentationComplexity HeckeLogarithmic.complexity; positivity) hc hε.le) hC.le

theorem central_deletion_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ ψ : Character) (a e : ℝ),
      0 < e → 51/100 ≤ a → a ≤ 1 →
      ∀ w : ℂ, w.re = 1-a-6*e →
      ‖factors χ.modulus ψ w‖ * ‖(factors χ.modulus ψ (1-conj w))⁻¹‖ ≤
        C * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+2*ε) := by
  obtain ⟨Cl, hCl, hl⟩ := factors_any_re_subpower_bound ε hε
  obtain ⟨Cr, hCr, hr⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cl*Cr, mul_pos hCl hCr, ?_⟩
  intro χ ψ a e he ha ha1 w hw
  have hR := HeckeDyadic.radical_norm_ge_one χ.modulus
  have hR0 : 0 < ((radical χ.modulus).absNorm : ℝ) := by linarith
  have hleft : ‖factors χ.modulus ψ w‖ ≤
      Cl * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+ε) := by
    apply (hl χ.modulus ψ w).trans
    apply mul_le_mul_of_nonneg_left _ hCl.le
    apply Real.rpow_le_rpow_of_exponent_le hR
    have hm : max (-w.re) 0 ≤ 6*e := max_le (by rw [hw]; linarith) (by positivity)
    linarith
  have hright : ‖(factors χ.modulus ψ (1-conj w))⁻¹‖ ≤
      Cr * ((radical χ.modulus).absNorm : ℝ) ^ ε := by
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans
      (hr χ.modulus ψ (1-conj w) (by simp; linarith))
  calc
    _ ≤ (Cl * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+ε)) *
        (Cr * ((radical χ.modulus).absNorm : ℝ) ^ ε) :=
      mul_le_mul hleft hright (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hR0]
      congr 2
      ring

theorem buffered_same_primitive_reflected (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι) (ψ : Character), FiniteFourier.IsPrimitiveOnIdeals ψ.residue →
      (χ j).residue ≠ 1 →
      (∀ I : Ideal O, idealCoeff (χ j) I =
        if IsCoprime I (χ j).modulus then idealCoeff ψ I else 0) →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) w‖ ≤ C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
        ((radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
        (3+(3*i+2 : ℕ)*B)^2 *
        (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨Cg, hCg, hg⟩ := HeckeDyadicReflection.original_reflected_bound
  obtain ⟨Cb, hCb, hb⟩ := buffered_reflected_right_bound e ε he he' hε
  obtain ⟨Cd, hCd, hd⟩ := central_deletion_bound ε hε
  refine ⟨Cg*Cb*Cd, by positivity, ?_⟩
  intro ι _ χ B a i hB ha ha1 hmax j ψ hp hχ hm w hw hwi
  have hr := hg (χ j) ψ hp hχ hm w (by rw [hw]; linarith) (by rw [hw]; linarith)
  have hexp : 1/2-w.re = a-1/2+6*e := by rw [hw]; ring
  rw [hexp] at hr
  have hright := hb χ B a i hB ha ha1 hmax j hχ w hw hwi
  have hdel := hd (χ j) ψ a e he ha ha1 w hw
  have hpc0 : 0 ≤ presentationComplexity (χ j) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity
  calc
    _ ≤ Cg * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) * (3+|w.im|)^2 *
        ‖LFunction (χ j) (1-conj w)‖ *
        (‖factors (χ j).modulus ψ w‖ * ‖(factors (χ j).modulus ψ (1-conj w))⁻¹‖) := hr
    _ ≤ Cg * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) * (3+(3*i+2 : ℕ)*B)^2 *
        (Cb * (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε) *
        (Cd * ((radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε)) := by
      gcongr
    _ = _ := by ring

theorem source_calibrated_reflected_allocation (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
      (hmaxS : ∀ P ∈ S, P.IsMaximal)
      (_hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
      (u : FreeRow), u.val ≠ 1 →
      ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
          if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
        (((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) →
          (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1) ∧
        ∀ {ι : Type*} [Fintype ι] (η : Character) (twists : ι → Character)
          (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
          detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1 : ℕ)*B) < a+2*e →
          ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ j, Prime (P j)) → Function.Injective P →
          ∀ (v : Fin k → ℕ), (∀ j, 2 ≤ v j) →
            (∀ j, P j ^ v j ∣ Ideal.span {u.val}) →
            ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
            ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
                HeckeOrigin.continued (rowCharacter S hS u) w‖ *
                ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) ≤
              C * (((fixedConductorConstant S : ℝ) *
                (Ideal.span {u.val} : Ideal O).absNorm) ^ (a-1/2+6*e) *
                ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) *
                ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
                (3+(3*i+2 : ℕ)*B)^2 *
                (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := buffered_same_primitive_reflected e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro S hS hmaxS hbad u hu
  obtain ⟨ψ, hle, hp, hm, hall⟩ := row_same_primitive_allocation S hS u
  have hactive (hc : (ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) :
      (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1 := by
    have hn := calibrated_row_nonprincipal S hS hmaxS hbad u hu hc
    exact ⟨hn, fun h => hn ((principal_iff_of_mask _ ψ hm).mpr h)⟩
  refine ⟨ψ, hle, hp, hm, hactive, ?_⟩
  intro ι _ η twists B a i hB ha ha1 hbin k P hP hdis v hv hdiv w hw hwi
  have hpc0 : 0 ≤ presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity
  by_cases hc : (ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val = 0
  · simp only [hc, star_zero, zero_mul, norm_zero]
    positivity
  · have hn := (hactive hc).1
    have hL := hb (sourceDetectorFamily S hS η u twists) B a i hB ha ha1 hbin
      (Sum.inl true) ψ hp hn hm w hw hwi
    simp only [sourceDetectorFamily_numerator] at hL
    have hcal : ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val)‖ ≤ 1 := by
      rw [norm_star]
      exact (ProbePhysical.calibrationForSet S hmaxS).residueMonoid_norm_le_one _
    have hweighted : ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
        HeckeOrigin.continued (rowCharacter S hS u) w‖ ≤ ‖LFunction (rowCharacter S hS u) w‖ := by
      rw [HeckeOrigin.continued, ite_eq_right hn, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcal
    have hal := hall k P hP hdis v hv hdiv a e ha he
    rw [← hw] at hal
    have hprod0 : 0 ≤ ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) :=
      Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _)
    calc
      _ ≤ (C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
          ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) :=
        mul_le_mul_of_nonneg_right (hweighted.trans hL) hprod0
      _ = (C * ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ((ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
          ∏ j, ((P j).absNorm : ℝ) ^ (-w.re)) := by ring
      _ ≤ (C * ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ((((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) ^
            (a-1/2+6*e)) * ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hal (by positivity)
      _ = _ := by ring

theorem source_actual_valuation_reflection (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
      (hmaxS : ∀ P ∈ S, P.IsMaximal)
      (_hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
      (u : FreeRow), u.val ≠ 1 →
      ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
          if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
        (((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) →
          (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1) ∧
        ∀ {ι : Type*} [Fintype ι] (η : Character) (twists : ι → Character)
          (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
          detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1 : ℕ)*B) < a+2*e →
          ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ j, Prime (P j)) → Function.Injective P →
          (∀ j, 2 ≤ multiplicity (P j) (Ideal.span {u.val} : Ideal O)) →
          (∀ j, multiplicity (P j) (Ideal.span {u.val} : Ideal O) < 6) ∧
          ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
            ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
                HeckeOrigin.continued (rowCharacter S hS u) w‖ *
                ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) ≤
              C * (((fixedConductorConstant S : ℝ) *
                (Ideal.span {u.val} : Ideal O).absNorm) ^ (a-1/2+6*e) *
                ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) *
                ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
                (3+(3*i+2 : ℕ)*B)^2 *
                (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := source_calibrated_reflected_allocation e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro S hS hmaxS hbad u hu
  obtain ⟨ψ, hle, hp, hm, hactive, hbound⟩ := hb S hS hmaxS hbad u hu
  refine ⟨ψ, hle, hp, hm, hactive, ?_⟩
  intro ι _ η twists B a i hB ha ha1 hbin k P hP hdis hv
  refine ⟨fun j => (actual_ideal_multiplicity u (P j) (hP j)).2, ?_⟩
  exact hbound η twists B a i hB ha ha1 hbin k P hP hdis
    (fun j => multiplicity (P j) (Ideal.span {u.val} : Ideal O)) hv
    (fun j => (actual_ideal_multiplicity u (P j) (hP j)).1)

end SevenEighths.ProbeRowReflectedAllocation

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalBoundary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def rowKernelScalar {K : ℕ} (P : Fin K→ProbePhysical.PrimeIdeal) (u : FreeRow)
    (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (x z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_w_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      rowKernelScalar P u W0 X Z x z*(Y:ℂ)^(w-1)*mellin W1 w*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel rowKernelScalar sourceMellinWeight
  ring

theorem continuedPhysicalRowKernel_cauchy {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r C : ℝ) (N : ℕ) (hC : 0≤C)
    (hpoly : ∀v∈Icc l r,∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^N) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((v:ℂ)+t*I) z‖≤B*cauchy t := by
  obtain ⟨D,hD,hm⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a b ha hW
    (W1.smooth ⊤) l r (N+2)
  have hscale := (scaleBound_pos Y (l-1) (r-1)).le
  let A := ‖rowKernelScalar P u W0 X Z x z‖*scaleBound Y (l-1) (r-1)*C
  refine ⟨A*D,by dsimp [A]; positivity,?_⟩
  intro v hv t
  have hYbd := cpow_le_scaleBound hY (((v:ℂ)+t*I)-1)
    (show (((v:ℂ)+t*I)-1).re∈Icc (l-1) (r-1) by simpa using hv)
  have hm' : height t^2*(height t^N*‖mellin W1 ((v:ℂ)+t*I)‖)≤D := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using hm v hv t
  have hmc : height t^N*‖mellin W1 ((v:ℂ)+t*I)‖≤D*cauchy t :=
    CubicReflectionKernel.weighted_two_to_cauchy
      (mul_nonneg (pow_nonneg (height_pos t).le N) (norm_nonneg _)) t hm'
  rw [continuedPhysicalRowKernel_w_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖rowKernelScalar P u W0 X Z x z‖*scaleBound Y (l-1) (r-1)*
        ‖mellin W1 ((v:ℂ)+t*I)‖)*(C*height t^N) := by
      apply mul_le_mul _ (hpoly v hv t) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYbd (norm_nonneg _)) (norm_nonneg _)
    _ = A*(height t^N*‖mellin W1 ((v:ℂ)+t*I)‖) := by dsimp [A]; ring
    _ ≤ A*(D*cauchy t) := mul_le_mul_of_nonneg_left hmc (by dsimp [A]; positivity)
    _ = _ := by ring

theorem nonprincipal_w_integral_eq_of_polynomial {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r C : ℝ) (N : ℕ) (hC : 0≤C)
    (hlr : l≤ r) (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l)
    (hz : (17/50:ℝ)≤z.re) (hxl : 1+eps≤x.re+l)
    (hpoly : ∀v∈Icc l r,∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^N) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_cauchy S hS hmax P hPS η u W0 W1 a b ha hW
    X Y Z hY x z l r C N hC hpoly
  apply Continuation.vertical_integral_eq_of_even_envelope
    (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) cauchy cauchy_integrable
    (by intro t; simp [cauchy]) cauchy_tendsto hlr _ hbound
  intro w hw
  exact (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x w z hx (hl.trans hw.1) hz (by linarith [hw.1])).differentiableWithinAt

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.SelectedFirstBounds -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion

lemma compensatedReplacement_crude (V W D M B q : ℂ) (A E : ℝ)
    (hA : 0≤A) (hE : 0≤E) (hV : ‖V‖≤1) (hW : ‖W‖≤A)
    (hD : ‖D‖≤1/2) (hM : ‖M‖≤388) (hB : ‖B‖≤E) (hq : ‖q‖≤A) :
    ‖ProbeLocal.compensatedReplacement V W D M B q‖≤
      2*((E+A)*2*(1+A)*388+A*(1+A)) := by
  have h1V : ‖1-V‖≤2 := by have h := norm_sub_le (1:ℂ) V;rw [norm_one] at h;linarith
  have h1W : ‖1-W‖≤1+A := by have h := norm_sub_le (1:ℂ) W;rw [norm_one] at h;linarith
  have h1VW : ‖1-V*W‖≤1+A := by
    apply (norm_sub_le (1:ℂ) (V*W)).trans
    rw [norm_one,norm_mul]
    have hm := (mul_le_mul hV hW (norm_nonneg _) (by norm_num)).trans_eq (one_mul A)
    linarith
  have hi := ProbeLocal.inv_one_sub_norm_le_two D hD
  unfold ProbeLocal.compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ ((‖B-q‖*‖1-V‖*‖1-W‖*‖M‖)+‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*M) (q*(1-V*W))
    _ ≤ ((E+A)*2*(1+A)*388+A*(1+A))*2 := by
      have hbq : ‖B-q‖≤E+A := (norm_sub_le B q).trans (add_le_add hB hq)
      gcongr
    _ = _ := by ring

def selectedFirstBound (Q R : ℝ) : ℝ :=
  2*((Q^R+Q^(1/100:ℝ))*2*(1+Q^(1/100:ℝ))*388+Q^(1/100:ℝ)*(1+Q^(1/100:ℝ)))

lemma selectedFirstBound_nonneg (Q R : ℝ) (hQ : 0≤Q) : 0≤ selectedFirstBound Q R := by
  unfold selectedFirstBound
  positivity

theorem continuedCompensatedLocal_first_bound (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:ℝ)≤P.val.absNorm) (R : ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hxR : x.re≤R) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hxw : 1≤x.re+w.re) :
    ‖continuedCompensatedLocal η u P hs x w z
      (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))‖≤
        selectedFirstBound P.val.absNorm R := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  have hV := first_region_V_half _ hQ z hz
  have hD : ‖coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x‖≤1/2 :=
    (coordD_norm_le _ hQ0 _ _ x (idealCoeff_norm_le_one η _) (idealRowHom_norm u.val _)).trans
      (rpow_le_half _ _ hQ (by linarith))
  have hM : ‖continuedMarkedLocal η u P hs x w z‖≤388 := by
    rw [continuedMarkedLocal_eq_quotient η u P hs x w z
      (ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV),div_eq_mul_inv,norm_mul]
    have hH := ramifiedCorrection_first_bound η u P hs hQ x w z hx hw hz hxw
    have hn : ‖ramifiedCorrection η u P hs x w z-1‖≤194 := by
      have h := norm_sub_le (ramifiedCorrection η u P hs x w z) (1:ℂ)
      rw [norm_one] at h
      linarith
    exact (mul_le_mul hn (ProbeLocal.inv_one_sub_norm_le_two _ hV) (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have hW : ‖coordW P.val.absNorm (idealRowHom u.val P.val) w‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) :=
    (coordW_norm_le _ hQ0 _ w (idealRowHom_norm u.val _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hq : ‖(P.val.absNorm:ℂ)^(-w)‖≤(P.val.absNorm:ℝ)^(1/100:ℝ) := by
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hB : ‖star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x‖≤(P.val.absNorm:ℝ)^R := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)).trans
    rw [show (P.val.absNorm:ℂ)=((P.val.absNorm:ℝ):ℂ) from by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hxR
  exact compensatedReplacement_crude _ _ _ _ _ _ _ _ (by positivity) (by positivity)
    (hV.trans (by norm_num)) hW hD hM hB hq

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.FirstWGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem nonprincipal_first_growth (χ : Character) (hχ : χ.residue≠1) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,-(1/100:ℝ)≤ s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(3+|s.im|)^2 := by
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=>hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  obtain ⟨Cd,hCd,hd⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound 1 (by norm_num)
  let R : ℝ := (HeckeDeletionBounds.radical χ.modulus).absNorm
  have hR : 1≤R := by
    dsimp only [R]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  let C : ℝ := HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*Cd*R^(101/100:ℝ)
  have hC : 0≤C := by dsimp [C];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro s hs
  have hl := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hl
  have hdel : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*R^(101/100:ℝ) := by
    apply (hd χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    exact Real.rpow_le_rpow_of_exponent_le hR (by have hm : max (-s.re) 0≤(1/100:ℝ) := max_le (by linarith) (by norm_num); linarith)
  rw [HeckeOrigin.continued,ite_eq_right hχ,HeckeDyadicReflection.LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*R^(101/100:ℝ)) := mul_le_mul hl hdel (norm_nonneg _) (by positivity)
    _ = C*(3+|s.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|s.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

theorem calibrated_numerator_first_growth (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (u : FreeRow) (hu : u.val≠1) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,-(1/100:ℝ)≤ s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤C*(3+|s.im|)^2 := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · refine ⟨1,by norm_num,?_⟩
    intro s hs
    simp only [hc,star_zero,zero_mul,norm_zero,one_mul]
    positivity
  · obtain ⟨C,hC,hbound⟩ := nonprincipal_first_growth (rowCharacter S hS.prime u)
      (calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc)
    refine ⟨C,hC,?_⟩
    intro s hs
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
      (hbound s hs)

theorem calibrated_physicalRow_first_w_growth (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    ∃C : ℝ,0<C ∧ ∀w : ℂ,l≤w.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  let C : ℝ := L*Cn*(Ch*N)*∏P:T,A P
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  have hC : 0≤C := by dsimp [C,L,N];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro w hw
  have hn' := hn w (hl.trans hw)
  have hh' := hh eps S hS hfirst T η u x w z hx (hl.trans hw) hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x.re x w z hx le_rfl
      (hl.trans hw) hz (by linarith [hfirst.positive])
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
        ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [he,norm_mul,norm_mul,norm_mul]
  have hh'' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh'
  calc
    _ ≤ L*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      rw [norm_mul]
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [L,N];positivity)
      apply mul_le_mul _ hh'' (norm_nonneg _) (by dsimp [L,N];positivity)
      exact mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = C*(3+|w.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|w.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CoarseUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma selectedFirstBound_polynomial {Q : ℝ} (hQ : 1≤Q) : selectedFirstBound Q 2≤8192*Q^3 := by
  have hQ0 : 0≤Q := by linarith
  have hsmall : Q^(1/100:ℝ)≤Q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1/100:ℝ)≤1)
  have hsmall0 : 0≤Q^(1/100:ℝ) := Real.rpow_nonneg hQ0 _
  have hQQ : Q≤Q^2 := by nlinarith
  have hQ2 : 0≤Q^2 := sq_nonneg Q
  have hQ3 : Q^2≤Q^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sq_nonneg Q)]
  unfold selectedFirstBound
  rw [Real.rpow_two]
  calc
    _ ≤ 2*((2*Q^2)*2*(2*Q)*388+Q*(2*Q)) := by gcongr <;> nlinarith
    _ ≤ _ := by nlinarith

theorem nonprincipal_first_uniform_growth :
    ∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 → ∀s : ℂ,-(1/100:ℝ)≤ s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(χ.modulus.absNorm:ℝ)^3*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hd⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound 1 (by norm_num)
  let U := HeckeLogarithmicInput.uniformConstant
  have hU : 0≤U := HeckeLogarithmicInput.uniformConstant_nonneg
  refine ⟨1+U*Cd,by positivity,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=>hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hN : (1:ℝ)≤χ.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one χ
  have hψN : (1:ℝ)≤ψ.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one ψ
  have hQ' : (ψ.modulus.absNorm:ℝ)≤χ.modulus.absNorm := by exact_mod_cast hQ
  have hpow : (ψ.modulus.absNorm:ℝ)^(3/5:ℝ)≤χ.modulus.absNorm := by
    apply le_trans _ hQ'
    simpa using Real.rpow_le_rpow_of_exponent_le hψN (by norm_num : (3/5:ℝ)≤1)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hl : ‖LFunction ψ s‖≤U*(χ.modulus.absNorm:ℝ)*(3+|s.im|)^2 := by
    exact hg.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hU) (sq_nonneg _))
  have hdel : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*(χ.modulus.absNorm:ℝ)^2 := by
    apply (hd χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    calc
      _ ≤ (χ.modulus.absNorm:ℝ)^(max (-s.re) 0+1) := Real.rpow_le_rpow (by positivity)
        (HeckeDyadic.radical_norm_le_modulus χ) (by positivity)
      _ ≤ (χ.modulus.absNorm:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN
        (by have hm : max (-s.re) 0≤(1/100:ℝ) := max_le (by linarith) (by norm_num);linarith)
      _ = _ := Real.rpow_two _
  rw [HeckeOrigin.continued,ite_eq_right hχ,HeckeDyadicReflection.LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (U*(χ.modulus.absNorm:ℝ)*(3+|s.im|)^2)*(Cd*(χ.modulus.absNorm:ℝ)^2) :=
      mul_le_mul hl hdel (norm_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤χ.modulus.absNorm) 3) (sq_nonneg (3+|s.im|))]

theorem calibrated_numerator_first_uniform_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀u : FreeRow,u.val≠1 → ∀s : ℂ,-(1/100:ℝ)≤ s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^3*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := nonprincipal_first_uniform_growth
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨C*(1+A^3),by positivity,?_⟩
  intro u hu s hs
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul,norm_zero]
    positivity
  · have hnp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    have hg := hmain (rowCharacter S hS.prime u) hnp s hs
    have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖≤1 := by
      rw [norm_star]
      exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
    have hQ : ((rowCharacter S hS.prime u).modulus.absNorm:ℝ)≤
        A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
      have h := rowCharacter_conductor S hS.prime u
      dsimp [A]
      exact_mod_cast (by simpa only [mul_right_comm] using h)
    rw [norm_mul]
    calc
      _ ≤ ‖HeckeOrigin.continued (rowCharacter S hS.prime u) s‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hcal
      _ ≤ C*((rowCharacter S hS.prime u).modulus.absNorm:ℝ)^3*(3+|s.im|)^2 := hg
      _ ≤ C*(A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))^3*(3+|s.im|)^2 := by gcongr
      _ ≤ _ := by
        rw [mul_pow]
        nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm) 3)
          (sq_nonneg (3+|s.im|))]

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.FirstJoint -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physicalRow_first_joint_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) :
    ∃C : ℝ,0≤C ∧ ∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*L*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hx hw hz
  have hn' := hn w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤L :=
    HeckeReciprocalBound.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by rw [hx];norm_num) hx.le hw hz (by rw [hx];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*L)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hL)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.BufferedGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_joint_growth
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e) :
    ∃C : ℝ,0≤C ∧ ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)
  have hR : 0≤R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤R :=
    hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*R)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hR)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.BufferedHeightGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_height_growth
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    : ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) 0)/9
  have hR : 0≤R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤R*(3+|H|)^2 := by
    have hr := hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
    have hscale : Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)=R*(3+|H|)^2 := by
      dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
      rw [Real.rpow_one]
      ring
    simpa only [sourceDetectorFamily_denominator,hscale] using hr
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(R*(3+|H|)^2))*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (by positivity)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CoarsePhysical -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem buffered_denominator_polynomial_growth (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (ψ : ι→Character)
      (a B H : ℝ) (i : ℕ),(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H →
      ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^2*(3+|H|)^2 := by
  obtain ⟨C,hC,hbound⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨2*C*(1+A^2),by positivity,?_⟩
  intro η u ψ a B H i ha haTop hB hH hbin x hxl hxr hxi
  let χ := (targetRow η u).excludePrimes S hS
  have hb := hbound (sourceDetectorFamily S hS η u ψ) B a H i hB ha haTop hH hbin (Sum.inl false) x hxl hxr hxi
  simp only [sourceDetectorFamily_denominator,Real.rpow_one] at hb
  have hQ : (χ.modulus.absNorm:ℝ)≤(η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    have hh := targetRow_excluded_conductor S hS η u
    dsimp [χ,A]
    exact_mod_cast (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hh)
  apply hb.trans
  unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity
  have hrad := HeckeDyadic.radical_norm_le_modulus χ
  calc
    _ ≤ C*((χ.modulus.absNorm:ℝ)*(2*(χ.modulus.absNorm:ℝ)*(3+|H|)^2)) := by gcongr
    _ ≤ C*(((η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))*
        (2*((η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))*(3+|H|)^2)) := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg ((η.modulus.absNorm:ℝ)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)*(3+|H|))]

def coarsePrimeCost (T : Finset ProbePhysical.PrimeIdeal) : ℝ := ∏P∈T,(8192:ℝ)*(P.val.absNorm:ℝ)^3

lemma coarsePrimeCost_nonneg (T : Finset ProbePhysical.PrimeIdeal) : 0≤ coarsePrimeCost T := by
  unfold coarsePrimeCost
  positivity

theorem calibrated_physicalRow_buffered_polynomial_growth
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (ψ : ι→Character),
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*
          coarsePrimeCost T*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_denominator_polynomial_growth (ι:=ι) e he he' S hS.prime
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*Cr*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT ψ a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn u hu w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec := hreciprocal η u ψ a B H i ha ha1 hB hH hbin x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤ coarsePrimeCost T := by
    rw [norm_prod]
    unfold coarsePrimeCost
    conv_rhs => rw [←Finset.prod_attach]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    have hQ : (4:ℝ)≤P.val.val.absNorm := by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)
    exact (continuedCompensatedLocal_first_bound η u P.val _ hQ 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)).trans (selectedFirstBound_polynomial (by linarith))
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(Cr*(η.modulus.absNorm:ℝ)^2*N^2*(3+|H|)^2))*(Cn*N^3*(3+|w.im|)^2)*(Ch*N)*coarsePrimeCost T := by
      apply mul_le_mul _ hg (norm_nonneg _) (by have hc:=coarsePrimeCost_nonneg T;dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (by positivity)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by dsimp [N];ring

theorem calibrated_physicalRow_first_joint_polynomial_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S),∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4*coarsePrimeCost T*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*L*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hn' := hn u hu w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤L :=
    HeckeReciprocalBound.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤ coarsePrimeCost T := by
    rw [norm_prod]
    unfold coarsePrimeCost
    conv_rhs => rw [←Finset.prod_attach]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    apply (continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by rw [hx];norm_num) hx.le hw hz (by rw [hx];linarith)).trans
    exact selectedFirstBound_polynomial (by have hn:=hS.tail.norm_four P.val (hT P.val P.property);exact_mod_cast (by omega : 1≤P.val.val.absNorm))
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*L)*(Cn*N^3*(3+|w.im|)^2)*(Ch*N)*coarsePrimeCost T := by
      apply mul_le_mul _ hg (norm_nonneg _) (by have hc:=coarsePrimeCost_nonneg T;dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hL)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by dsimp [N];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.FirstWShift -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma physicalRow_first_w_height_bound {K : ℕ} (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,l≤v → ∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_w_growth (eps/2) S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu x z l hx hl hz (by linarith)
  refine ⟨9*C,by positivity,?_⟩
  intro v hv t
  have hb := hbound ((v:ℂ)+t*I) (by simpa using hv)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have h3 : (3+|t|)^2≤9*(height t)^2 := by unfold height;nlinarith [abs_nonneg t]
  nlinarith

theorem nonprincipal_first_w_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  exact nonprincipal_w_integral_eq_of_polynomial eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x z l r C 2 hC.le hlr hx hl hz hxw
    (fun v hv t=>hbound v hv.1 t)

lemma nonprincipal_first_w_vertical_integrable {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    Integrable (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z) := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  obtain ⟨B,hB,hb⟩ := continuedPhysicalRowKernel_cauchy S hS hmax P hPS η u W0 W1 a b ha hW X Y Z hY x z l l C 2 hC.le
    (fun v hv t=>hbound v hv.1 t)
  have hc : Continuous (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
      W0 W1 a b ha hW X Y Z hY x ((l:ℂ)+t*I) z hx (by simpa using hl) hz
      (by simpa using hxw)).continuousAt.comp (f:=fun t : ℝ=>(l:ℂ)+t*I)
    fun_prop
  exact (cauchy_integrable.const_mul B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>hb l ⟨le_rfl,le_rfl⟩ t))

theorem finite_rows_first_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character)
    (F : Finset FreeRow) (hF : ∀u∈F,u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    (∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  rw [integral_finsetSum F (fun u hu=>nonprincipal_first_w_vertical_integrable eps heps S hS hfirst hmax P hPS η u (hF u hu)
    W0 W1 a b ha hW X Y Z hY x z l hx hl hz hxw),
    integral_finsetSum F (fun u hu=>nonprincipal_first_w_vertical_integrable eps heps S hS hfirst hmax P hPS η u (hF u hu)
      W0 W1 a b ha hW X Y Z hY x z r hx (hl.trans hlr) hz (by linarith))]
  exact Finset.sum_congr rfl (fun u hu=>nonprincipal_first_w_integral_eq eps heps S hS hfirst hmax P hPS η u (hF u hu)
    W0 W1 a b ha hW X Y Z hY x z l r hlr hx hl hz hxw)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.SlotSums -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continued_selected_slot_bound (eps a b r B : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤ r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset ProbePhysical.PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b →
      (∀y,‖W y‖≤B) → ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      (∑P : T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
          (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^r := by
  obtain ⟨C,hC,hmain⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed eps a b r (1/2) B 961
    heps ha hb (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact Subtype.ext h
  let G : T→ℂ := fun P=>continuedCompensatedLocal η u P.val (hT P.val P.property).1 x w z
    (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  have hg (P : T) (_ : P∈Finset.univ) : ‖G P‖≤
      961*(if f P∣Ideal.span {u.val} then (Ideal.absNorm (f P):ℝ)^(1/2:ℝ) else 1) := by
    have hh := continuedCompensatedLocal_bound η u P.val (hT P.val P.property).1
      (hT P.val P.property).2 x w z hx hw (by rw [hz];exact hr)
    apply hh.trans
    by_cases hp : f P∣Ideal.span {u.val}
    · simp only [show P.val.val=f P from rfl,ite_eq_left hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_exponent_le (by have := (hT P.val P.property).2;change 1≤(P.val.val.absNorm:ℝ);linarith)
        (max_le (by linarith) (by norm_num))
    · simp only [show P.val.val=f P from rfl,ite_eq_right hp,le_refl]
  exact hmain f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G hg z hz

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.TupleFactor -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalCompensatedRow_indexed {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ) :
    let hT : ∀Q∈Finset.univ.image P,Q.val∉S := by
      intro Q hQ
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
      exact hPS i
    physicalCompensatedRow S hS (Finset.univ.image P) hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,continuedCompensatedLocal η u (P i)
          (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  dsimp only
  unfold physicalCompensatedRow continuedCompensatedRow
  congr 2
  symm
  apply Finset.prod_bij (fun i _=>⟨P i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  · intro i _; exact Finset.mem_attach _ _
  · intro i _ j _ h; exact hP (congrArg Subtype.val h)
  · intro Q _
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp Q.property
    exact ⟨i,hi,Subtype.ext he⟩
  · intro i _; rfl

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.TupleGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem nonprincipal_positive_growth (σ δ : ℝ) (hσ : 0<σ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 → ∀s : ℂ,σ≤ s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(χ.modulus.absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := HeckeDeletionBounds.factors_subpower_bound σ δ hσ hδ
  refine ⟨(1+HeckeLogarithmicInput.uniformConstant)*Cd,
    mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg]) hCd,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=>hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hd : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*(χ.modulus.absNorm:ℝ)^δ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hdel χ.modulus χ.modulus_ne_bot ψ s hs)
  have hQ' : (ψ.modulus.absNorm:ℝ)^(3/5:ℝ)≤(χ.modulus.absNorm:ℝ)^(3/5:ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  have hN : (0:ℝ)<χ.modulus.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  rw [HeckeOrigin.continued,ite_eq_right hχ,
    HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ (by linarith),norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*(χ.modulus.absNorm:ℝ)^δ) := mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ ((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*(χ.modulus.absNorm:ℝ)^δ) := by gcongr;linarith
    _ = _ := by rw [Real.rpow_add hN];ring

theorem calibrated_numerator_positive_growth (σ δ : ℝ) (hσ : 0<σ) (hδ : 0<δ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow),u.val≠1 → ∀s : ℂ,σ≤ s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := nonprincipal_positive_growth σ δ hσ hδ
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨C*(1+A^(3/5+δ)),mul_pos hC (by positivity),?_⟩
  intro u hu s hs
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul,norm_zero]
    positivity
  · have hnp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    have hg := hmain (rowCharacter S hS.prime u) hnp s hs
    have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖≤1 := by
      rw [norm_star]
      exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
    have hQ : ((rowCharacter S hS.prime u).modulus.absNorm:ℝ)≤
        A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
      have h := rowCharacter_conductor S hS.prime u
      dsimp [A]
      exact_mod_cast (by simpa only [mul_right_comm] using h)
    rw [norm_mul]
    calc
      _ ≤ ‖HeckeOrigin.continued (rowCharacter S hS.prime u) s‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hcal
      _ ≤ C*((rowCharacter S hS.prime u).modulus.absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := hg
      _ ≤ C*(A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))^(3/5+δ)*(3+|s.im|)^2 := by
        gcongr
      _ ≤ C*(1+A^(3/5+δ))*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
        rw [Real.mul_rpow hA (by positivity)]
        calc
          _ = C*A^(3/5+δ)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by ring
          _ ≤ _ := by gcongr;linarith

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.ScalarGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_scalar_growth (e δ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hδ : 0<δ) (hδ' : δ≤1) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 → ∀(x w z : ℂ),
      HeckeZeroSupremum.beta+8*e≤x.re → (1/2:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)‖≤
        C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*
          (3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_positive_growth (1/2) (δ/2) (by norm_num) (by linarith) S hS hmax
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e (δ/2) he he' (by linarith) (by linarith) S hS.prime
  let B : ℝ := HeckeReciprocalBound.bound 2
  have hB : 0≤B := tsum_nonneg (fun _=>norm_nonneg _)
  refine ⟨(1+B)*Cn*Cr,by positivity,?_⟩
  intro η u hu x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hn' := hn u hu w hw
  have hr' := hr η u x hx
  have hz' : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤1+B := by
    apply (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2) (s:=6*z) ?_).trans
    · dsimp [B];linarith
    · norm_num [Complex.mul_re];linarith
  have hη : (η.modulus.absNorm:ℝ)^(δ/2)≤(η.modulus.absNorm:ℝ)^δ :=
    Real.rpow_le_rpow_of_exponent_le (HeckeLogarithmicInput.modulus_norm_ge_one η) (by linarith)
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)=
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x := by ring
  rw [he,norm_mul,norm_mul]
  calc
    _ ≤ (1+B)*(Cn*N^(3/5+δ/2)*(3+|w.im|)^2)*
        (Cr*(η.modulus.absNorm:ℝ)^(δ/2)*N^(δ/2)*(3+|x.im|)^2) := by
      apply mul_le_mul _ hr' (norm_nonneg _) (by positivity)
      exact mul_le_mul hz' hn' (norm_nonneg _) (by positivity)
    _ ≤ (1+B)*(Cn*N^(3/5+δ/2)*(3+|w.im|)^2)*
        (Cr*(η.modulus.absNorm:ℝ)^δ*N^(δ/2)*(3+|x.im|)^2) := by gcongr
    _ = ((1+B)*Cn*Cr)*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ)*(3+|x.im|)^2*(3+|w.im|)^2 := by
      have hp : N^(3/5+δ/2)*N^(δ/2)=N^(3/5+δ) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = ((1+B)*Cn*Cr)*(η.modulus.absNorm:ℝ)^δ*(N^(3/5+δ/2)*N^(δ/2))*(3+|x.im|)^2*(3+|w.im|)^2 := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.TupleSums -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continued_selected_tuple_bound (K : ℕ) (eps a b r B : ℝ) (heps : 0<eps)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤ r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
      (hT : ∀i P,P∈T i→Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      (∑P : (∀i, T i),‖∏i,
        W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
        continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
          (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
          (((P i).val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏i,(Y i)^r := by
  let d : ℝ := eps/((K:ℝ)+1)
  have hd : 0<d := div_pos heps (by positivity)
  obtain ⟨C,hC,hmain⟩ := continued_selected_slot_bound d a b r B hd ha hb hr hB
  refine ⟨C^K,pow_pos hC K,?_⟩
  intro η u T hT Y hY W hWS hWB x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 1≤N := by
    dsimp [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hdK : d*(K:ℝ)≤eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<(K:ℝ)+1)]
    nlinarith
  have hpow : (N^d)^K≤N^eps := by
    rw [←Real.rpow_mul_natCast (by linarith : 0≤N)]
    exact Real.rpow_le_rpow_of_exponent_le hN hdK
  let F : ∀i:Fin K,T i→ℂ := fun i P=>
    W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u P.val (hT i P.val P.property).1 x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w))
  change (∑P:(∀i,T i),‖∏i,F i (P i)‖)≤C^K*N^eps*∏i,(Y i)^r
  simp_rw [norm_prod]
  rw [←Fintype.prod_sum (fun i P=>‖F i P‖)]
  calc
    _ ≤ ∏i:Fin K, (C*N^d*(Y i)^r) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact Finset.sum_nonneg fun _ _=>norm_nonneg _
      · intro i _; exact hmain η u (T i) (hT i) (Y i) (hY i) (W i) (hWS i) (hWB i) x w z hx hw hz
    _ = C^K*(N^d)^K*∏i:Fin K,(Y i)^r := by
      simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    _ ≤ C^K*N^eps*∏i:Fin K,(Y i)^r := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _)

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.TupleBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem continued_selected_tuple_with_correction (K : ℕ) (δ a b r B : ℝ)
    (hδ : 0<δ) (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤ r) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : Character) (u : FreeRow)
      (T : Fin K→Finset ProbePhysical.PrimeIdeal)
      (hT : ∀i P,P∈T i→Supported P.val ∧ (4:ℝ)≤P.val.absNorm)
      (Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (1/2:ℝ)≤w.re → z.re=r →
      1+eps≤x.re+w.re →
      (∑P : (∀i,T i),‖continuedCorrection
        (markExclusions S (Finset.univ.image (fun i=>(P i).val)))
        (markedSourceExclusions S hS (Finset.univ.image (fun i=>(P i).val))) η u x w z*
        ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
            (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
            (((P i).val.val.absNorm:ℂ)^(-w))‖)
      ≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ*∏i,(Y i)^r := by
  obtain ⟨C₁,hC₁,hmain⟩ := continued_selected_tuple_bound K (δ/2) a b r B (by linarith) ha hb hr hB
  obtain ⟨C₂,hC₂,hcorr⟩ := unselectedCorrection_first_subpower (δ/2) (by linarith)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  intro eps S hS hfirst η u T hT Y hY W hWS hWB x w z hx hw hz hxw
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  let F : (∀i,T i)→ℂ := fun P=>∏i,
    W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u (P i).val (hT i (P i).val (P i).property).1 x w z
        (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
        (((P i).val.val.absNorm:ℂ)^(-w))
  calc
    _ ≤ ∑P:(∀i,T i),(C₂*N^(δ/2))*‖F P‖ := by
      apply Finset.sum_le_sum
      intro P _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hcorr eps S hS hfirst (Finset.univ.image (fun i=>(P i).val)) η u x w z
          (by linarith) (by linarith) (by rw [hz];exact hr) hxw) (norm_nonneg _)
    _ = (C₂*N^(δ/2))*∑P:(∀i,T i),‖F P‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ (C₂*N^(δ/2))*(C₁*N^(δ/2)*∏i,(Y i)^r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hmain η u T hT Y hY W hWS hWB x w z hx hw hz
    _ = (C₂*C₁)*N^δ*∏i,(Y i)^r := by
      have hp : N^(δ/2)*N^(δ/2)=N^δ := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (C₂*C₁)*(N^(δ/2)*N^(δ/2))*∏i,(Y i)^r := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.WGrowth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physicalRow_w_growth (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+1/2) :
    ∃C : ℝ,0<C ∧ ∀w : ℂ,(1/2:ℝ)≤w.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_positive_growth (1/2) 1 (by norm_num) (by norm_num) S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>961*((P.val.val.absNorm:ℝ)^(1/2:ℝ)+1)
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  let C : ℝ := L*(Cn*N^(3/5+1:ℝ))*(Ch*N)*∏P:T,A P
  have hC : 0≤C := by dsimp [C,L,A,N];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro w hw
  have hn' := hn u hu w hw
  have hh' := hh eps S hS hfirst T η u x w z (by linarith) (by linarith) hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    change (∏P:T,‖continuedCompensatedLocal η u P.val _ x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖)≤_
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P _
    have hQ : (4:ℝ)≤P.val.val.absNorm := by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)
    apply (continuedCompensatedLocal_bound η u P.val _ hQ x w z hx hw hz).trans
    dsimp [A]
    by_cases hp : P.val.val∣Ideal.span {u.val}
    · rw [ite_eq_left hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤P.val.val.absNorm)
        (max_le (by linarith) (by norm_num) : max (1-w.re) 0≤(1/2:ℝ))).trans
      linarith
    · rw [ite_eq_right hp]
      have hnq := Real.rpow_nonneg (show (0:ℝ)≤P.val.val.absNorm by positivity) (1/2:ℝ)
      nlinarith
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
        ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [he,norm_mul,norm_mul,norm_mul]
  have hh'' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh'
  have hn'' : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w‖≤Cn*N^(3/5+1:ℝ)*(3+|w.im|)^2 := hn'
  calc
    _ ≤ L*(Cn*N^(3/5+1:ℝ)*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      rw [norm_mul]
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [L,N];positivity)
      apply mul_le_mul _ hh'' (norm_nonneg _) (by dsimp [L,N];positivity)
      exact mul_le_mul_of_nonneg_left hn'' (by positivity)
    _ = C*(3+|w.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|w.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

