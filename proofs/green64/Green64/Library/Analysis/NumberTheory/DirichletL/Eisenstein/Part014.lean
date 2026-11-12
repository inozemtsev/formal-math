module

public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.BesselDerivatives
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part013
public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part014

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.InverseCuspCoordinates -/

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
open scoped BigOperators Classical Topology ComplexConjugate MatrixGroups Matrix

def inverseCuspCoordinates (c d : ℂ) (v : ℝ) (z : ℂ) : ℂ×ℝ :=
  (-d/c-star z/(c^2*((v^2+‖z‖^2:ℝ):ℂ)),v/(‖c‖^2*(v^2+‖z‖^2)))

lemma inverseCuspCoordinates_height_pos (c d : ℂ) (v : ℝ) (z : ℂ)
    (hc : c≠0) (hv : 0<v) : 0<(inverseCuspCoordinates c d v z).2 := by
  dsimp [inverseCuspCoordinates]
  positivity

lemma inverseCuspCoordinates_line (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) :
    inverseCuspCoordinates c d v ((t:ℂ)*direction)=inverseCuspPath c d v direction t := by
  simp only [inverseCuspCoordinates,inverseCuspPath,star_mul,Complex.star_def,
    Complex.conj_ofReal,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_comm]

theorem inverse_cusp_action (g : SL(2,ℂ)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    g⁻¹ • upperPoint (z+g 0 0/g 1 0) v hv =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have h00 : (g⁻¹) 0 0=g 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h01 : (g⁻¹) 0 1= -g 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h10 : (g⁻¹) 1 0= -g 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h11 : (g⁻¹) 1 1=g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have hl : (-g 1 0)*(z+g 0 0/g 1 0)+g 0 0= -(g 1 0*z) := by
    field_simp
    ; ring
  have ht : g 1 1*(z+g 0 0/g 1 0)+(-g 0 1)=g 1 1*z+1/g 1 0 := by
    field_simp
    linear_combination hdet
  have hden : ‖-(g 1 0*z)‖^2+‖-g 1 0‖^2*v^2=
      ‖g 1 0‖^2*(v^2+‖z‖^2) := by rw [norm_neg,norm_neg,norm_mul,mul_pow];ring
  have hnormc : ((‖g 1 0‖^2:ℝ):ℂ)=g 1 0*star (g 1 0) := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj (g 1 0)).symm
  have hnormz : ((‖z‖^2:ℝ):ℂ)=z*star z := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj z).symm
  have hT : v^2+‖z‖^2≠0 := by positivity
  have hTc : ((v^2+‖z‖^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT
  have hcc : star (g 1 0)≠0 := star_ne_zero.mpr hc
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · rw [h00,h01,h10,h11,hl,ht,hden]
    dsimp [inverseCuspCoordinates]
    rw [Complex.ofReal_mul,hnormc]
    simp only [Complex.star_def,map_neg,map_mul]
    simp only [Complex.star_def] at hcc
    field_simp [hc,hcc,hTc]
    rw [Complex.ofReal_add,Complex.ofReal_pow,hnormz]
    simp only [Complex.star_def,]
    ; ring
  · rw [h10,h11,hl,hden]
    rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

lemma real_linear_horizontal_decompose (A : (ℂ×ℝ)→L[ℝ]ℂ) (z : ℂ) :
    A (z,0)=(z.re:ℂ)*A (1,0)+(z.im:ℂ)*A (Complex.I,0) := by
  have hz : ((z,0):ℂ×ℝ)=z.re • (1,0)+z.im • (Complex.I,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_add,Prod.smul_fst,Complex.real_smul,mul_one] using z.re_add_im.symm
    · simp
  rw [hz,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma real_linear_wirtinger_swap (A : (ℂ×ℝ)→L[ℝ]ℂ) (k : ℂ) :
    (1/2:ℂ)*(A (k,0)+Complex.I*A (-Complex.I*k,0))=
      k*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  rw [real_linear_horizontal_decompose A k,real_linear_horizontal_decompose A (-Complex.I*k)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,zero_mul,neg_mul,one_mul,
    zero_add,zero_sub,Complex.ofReal_neg]
  conv_rhs => lhs; rw [←k.re_add_im]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem inverse_cusp_wirtingerBar (c d : ℂ) (v : ℝ) (hc : c≠0) (hv : 0<v)
    (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    horizontalWirtingerBar (fun z=>F (inverseCuspCoordinates c d v z)) 0=
      (-1/(c^2*(v:ℂ)^2))*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  have h1 := (inverseCuspPath_comp_hasDerivAt c d v 1 hc hv F A hF).deriv
  have hI := (inverseCuspPath_comp_hasDerivAt c d v Complex.I hc hv F A hF).deriv
  have he1 : (fun t : ℝ=>F (inverseCuspCoordinates c d v (t:ℂ)))=
      (fun t : ℝ=>F (inverseCuspPath c d v 1 t)) := by
    funext t
    rw [←inverseCuspCoordinates_line]
    simp only [mul_one]
  have heI : (fun t : ℝ=>F (inverseCuspCoordinates c d v ((t:ℂ)*Complex.I)))=
      (fun t : ℝ=>F (inverseCuspPath c d v Complex.I t)) := by
    funext t
    rw [inverseCuspCoordinates_line]
  rw [horizontalWirtingerBar]
  simp only [zero_add]
  rw [he1,heI,h1,hI]
  simp only [star_one,Complex.star_def,Complex.conj_I,neg_neg]
  convert real_linear_wirtinger_swap A (-1/(c^2*(v:ℂ)^2)) using 1 ;
    congr 2 ; ring_nf

def horizontalWirtingerZ (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ=>f (z+(t:ℂ))) 0-
    Complex.I*deriv (fun t : ℝ=>f (z+(t:ℂ)*Complex.I)) 0)

lemma horizontalWirtingerZ_eq_fderiv (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerZ (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ,h1,hI]

theorem inverse_cusp_wirtinger_rule (c d : ℂ) (v : ℝ) (hc : c≠0) (hv : 0<v)
    (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    horizontalWirtingerBar (fun z=>F (inverseCuspCoordinates c d v z)) 0=
      (-1/(c^2*(v:ℂ)^2))*
        horizontalWirtingerZ (fun z=>F (z,1/(‖c‖^2*v))) (-d/c) := by
  rw [horizontalWirtingerZ_eq_fderiv F A _ _ hF]
  exact inverse_cusp_wirtingerBar c d v hc hv F A hF

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

theorem cusp_mellin_reflection (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) (2*s)=
      A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  have he : (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹)))=
      (fun v : ℝ=>A • ((v:ℂ)^(-2:ℂ) • g ((Q*v)⁻¹))) := by
    funext v; simp only [smul_eq_mul]
  rw [he,mellin_const_smul,mellin_cpow_smul]
  have hm := mellin_comp_mul_left (fun v : ℝ=>g v⁻¹) (2*s+(-2:ℂ)) hQ
  rw [mellin_comp_inv] at hm
  rw [hm]
  simp only [smul_eq_mul]
  rw [show -(2*s+(-2:ℂ))=2-2*s by ring]
  ring

theorem cusp_mellin_reflection_of_identity (f g : ℝ→ℂ) (A s : ℂ)
    (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) :
    mellin f (2*s)=A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  rw [←cusp_mellin_reflection g A s Q hQ]
  unfold mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [hfg v hv]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalPhaseCLM (freq : ℂ) : ℂ →L[ℝ] ℂ :=
  (2*Real.pi*Complex.I:ℂ) •
    (freq • ContinuousLinearMap.id ℝ ℂ +
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (freq • ContinuousLinearMap.id ℝ ℂ))

lemma horizontalPhaseCLM_apply (freq direction : ℂ) :
    horizontalPhaseCLM freq direction = horizontalPhaseMultiplier freq direction := by
  simp [horizontalPhaseCLM,horizontalPhaseMultiplier]
  ring

lemma brevePhase_hasFDerivAt (freq z : ℂ) :
    HasFDerivAt (fun w : ℂ => ShortDraftTrace.breveE (freq*w))
      (ShortDraftTrace.breveE (freq*z) • horizontalPhaseCLM freq) z := by
  have hh := (horizontalPhaseCLM freq).hasFDerivAt.cexp (x:=z)
  convert! hh using 1

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def amplitudeDeriv (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*
    (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)+
      (v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v))

lemma amplitude_hasDerivAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    HasDerivAt (fun y : ℝ => coeff.amplitude y h) (coeff.amplitudeDeriv v h) v := by
  by_cases hh : h=0
  · simp only [amplitude,amplitudeDeriv,ite_eq_left hh]
    exact hasDerivAt_const v 0
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hslope : HasDerivAt (fun y : ℝ => 4*Real.pi*‖cuspFrequency h‖*y)
      (4*Real.pi*‖cuspFrequency h‖) v := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (4*Real.pi*‖cuspFrequency h‖)
  have hk := (schlafliBesselK_cubic_hasDerivAt (4*Real.pi*‖cuspFrequency h‖*v)
    (by positivity)).scomp v hslope
  have hvd := (Complex.ofRealCLM.hasDerivAt (x:=v)).mul hk
  have hfull := hvd.const_mul (coeff.value h)
  simp only [amplitude,amplitudeDeriv,ite_eq_right hh]
  convert! hfull using 1 <;> simp [Function.comp_def,Pi.mul_apply,Complex.ofRealCLM_apply,Complex.real_smul,mul_assoc]

def termFDeriv (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℂ :=
  if h=0 then 0 else
    (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (coeff.amplitudeDeriv p.1 h*ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p • (horizontalPhaseCLM (cuspFrequency h)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℂ)

lemma term_hasFDerivAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt (coeff.term h) (coeff.termFDeriv h p) p := by
  by_cases hh : h=0
  · have hzero : coeff.term h=(fun _ : ℝ × ℂ => (0:ℂ)) := by
      funext q
      simp only [term,ite_eq_left hh]
    rw [hzero,termFDeriv,ite_eq_left hh]
    exact hasFDerivAt_const (𝕜:=ℝ) (0:ℂ) p
  have hvd := (coeff.amplitude_hasDerivAt p.1 hp h).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  have hzd := (brevePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜:=ℝ) (p:=p))
  have hprod : HasFDerivAt (fun q : ℝ × ℂ => coeff.amplitude q.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*q.2)) (coeff.termFDeriv h p) p := by
    convert! hvd.mul hzd using 1
    apply ContinuousLinearMap.ext
    intro direction
    simp only [termFDeriv,ite_eq_right hh]
    change (direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))+
      coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2 =
      coeff.amplitude p.1 h*(ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        horizontalPhaseCLM (cuspFrequency h) direction.2)+
      ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        ((direction.1:ℂ)*coeff.amplitudeDeriv p.1 h)
    rw [coeff.term_eq_amplitude p.1 hp h p.2]
    ring
  apply hprod.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.term_eq_amplitude q.1 hq h q.2

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma weighted_bessel_bounds (a : ℝ) (ha : 0<a) :
    ∃A B : ℝ,0≤A ∧ 0≤B ∧ ∀(h : ActualEisensteinCubic.O),h≠0 → ∀v : ℝ,a≤v →
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) ∧
      ‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hKu := (cubicBesselUpperAway_pos delta hdelta).le
  have hKd := cubicBesselDerivativeUpper_nonneg delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,C*cubicBesselDerivativeUpper delta,
    mul_nonneg hC hKu,mul_nonneg hC hKd,?_⟩
  intro h hh v hv
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hv ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  have hcombine (y D : ℝ) (hy : 0≤y) (hD : 0≤D)
      (hbound : y≤D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :
      ‖coeff.value h‖*y≤(C*D)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
    calc
      _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*
          (D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
        mul_le_mul (hcoeff h hh) hbound hy (by positivity)
      _ = (C*D)*Real.exp ((Real.pi*a)*‖cuspFrequency h‖-
          (4*Real.pi*‖cuspFrequency h‖*v)/2) := by
        rw [show (Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2=
          (Real.pi*a)*‖cuspFrequency h‖+(-(4*Real.pi*‖cuspFrequency h‖*v)/2) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos Real.pi_pos hr).le]
  exact ⟨hcombine _ _ (norm_nonneg _) hKu
    (schlafliBesselK_cubic_upper_away delta _ hdelta hx),
    hcombine _ _ (norm_nonneg _) hKd
    (schlafliBesselK_cubic_derivative_bound delta _ hdelta hx)⟩

lemma amplitudeDeriv_norm_le (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖coeff.amplitudeDeriv v h‖≤
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      (v*(4*Real.pi*‖cuspFrequency h‖))*
        (‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) := by
  rw [amplitudeDeriv,ite_eq_right hh,norm_mul]
  calc
    _ ≤ ‖coeff.value h‖*(‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      ‖(v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_mul,norm_mul,Complex.norm_of_nonneg hv.le,
        Complex.norm_of_nonneg (by positivity : 0≤4*Real.pi*‖cuspFrequency h‖)]
      ring

lemma termFDeriv_norm_le (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) :
    ‖coeff.termFDeriv h p‖≤‖coeff.amplitudeDeriv p.1 h‖+
      ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := by
  by_cases hh : h=0
  · simp only [termFDeriv,ite_eq_left hh,norm_zero]
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  simp only [termFDeriv,ite_eq_right hh]
  change ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖≤_
  calc
    _ ≤ ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))‖+
      ‖coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖ := norm_add_le _ _
    _ = ‖direction.1‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*‖horizontalPhaseMultiplier (cuspFrequency h) direction.2‖ := by
      rw [norm_mul,norm_mul,Complex.norm_real,breveE_norm,mul_one,norm_mul,
        horizontalPhaseCLM_apply]
    _ ≤ ‖direction‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*((4*Real.pi*‖cuspFrequency h‖)*‖direction‖) := by
      gcongr
      · exact norm_fst_le direction
      · exact (horizontalPhaseMultiplier_norm _ _).trans (by
          gcongr
          exact norm_snd_le direction)
    _ = _ := by ring

lemma termFDeriv_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.termFDeriv h p‖≤C*((1+‖cuspFrequency h‖)*
        Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨A,B,hA,hB,hweighted⟩ := coeff.weighted_bessel_bounds a ha
  obtain ⟨T,hT,hterm⟩ := coeff.slab_bound a b ha hab
  let D := B*b*(4*Real.pi)+T*(4*Real.pi)
  have hb : 0<b := ha.trans_le hab
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨A+D,add_nonneg hA hD,?_⟩
  intro h p hp
  by_cases hh : h=0
  · simp only [termFDeriv,ite_eq_left hh,norm_zero]
    positivity
  have hv : 0<p.1 := ha.trans_le hp.1
  obtain ⟨hKu,hKd⟩ := hweighted h hh p.1 hp.1
  have hamp : ‖coeff.amplitudeDeriv p.1 h‖≤
      A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
      (b*(4*Real.pi*‖cuspFrequency h‖))*
        (B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
    apply (coeff.amplitudeDeriv_norm_le p.1 hv h hh).trans
    gcongr
    exact hp.2
  calc
    _ ≤ ‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := coeff.termFDeriv_norm_le h p
    _ ≤ (A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
        (b*(4*Real.pi*‖cuspFrequency h‖))*(B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))+
        (T*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))*(4*Real.pi*‖cuspFrequency h‖) := by
      gcongr
      exact hterm h p hp
    _ = (A+D*‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
      dsimp [D]
      ring
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [mul_nonneg hA (norm_nonneg (cuspFrequency h))]

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O

lemma summable_one_add_norm_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => (1+‖cuspFrequency h‖)*Real.exp (-a*‖cuspFrequency h‖)) := by
  simpa only [add_mul,one_mul] using
    (summable_exp_neg_cuspFrequency_norm a ha).add (summable_norm_mul_exp_neg_cuspFrequency a ha)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma termFDeriv_summable (p : ℝ × ℂ) (hp : 0<p.1) :
    Summable (fun h : ActualEisensteinCubic.O => coeff.termFDeriv h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _)
    (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

lemma series_hasFDerivAt (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt coeff.series (∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p) p := by
  let a := p.1/2
  let b := 2*p.1
  have ha : 0<a := by dsimp [a];linarith
  have hab : a≤b := by dsimp [a,b];linarith
  have hap : a<p.1 := by dsimp [a];linarith
  have hpb : p.1<b := by dsimp [b];linarith
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  have hsum := (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a)
    (mul_pos Real.pi_pos ha)).mul_left C
  let slab : Set (ℝ × ℂ) := Set.Ioo a b ×ˢ Set.univ
  have hslab : IsOpen slab := isOpen_Ioo.prod isOpen_univ
  have hconn : IsPreconnected slab := isPreconnected_Ioo.prod isPreconnected_univ
  have hpSlab : p∈slab := ⟨⟨hap,hpb⟩,Set.mem_univ _⟩
  exact hasFDerivAt_tsum_of_isPreconnected hsum hslab hconn
    (fun h q hq => coeff.term_hasFDerivAt h q (ha.trans hq.1.1))
    (fun h q hq => hbound h q ⟨hq.1.1.le,hq.1.2.le⟩)
    hpSlab (coeff.summable p hp) hpSlab

lemma series_differentiableAt (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ coeff.series p := (coeff.series_hasFDerivAt p hp).differentiableAt

lemma fullFunction_cusp_eq (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    coeff.fullFunction constant (cuspCoordinateLift p)=
      constant*(p.1:ℂ)^(2/3:ℂ)+coeff.series p := by
  rw [show p=(p.1,p.2) from rfl,cuspCoordinateLift_positive p.1 p.2 hp]
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]

lemma fullFunction_cusp_differentiableAt (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hc := ((hasDerivAt_ofReal_cpow_const hp.ne' (r:=(2/3:ℂ))
    (by norm_num)).const_mul constant).differentiableAt.comp p
      (differentiableAt_fst (𝕜:=ℝ) (p:=p))
  have ht : DifferentiableAt ℝ (fun q : ℝ × ℂ =>
      constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p := by
    convert! hc.add (coeff.series_differentiableAt p hp) using 1
  apply ht.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

lemma fullFunction_split_differentiableAt (constant : ℂ) (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => coeff.fullFunction constant (cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : DifferentiableAt ℝ (fun q : ℂ × ℝ => (q.2,q.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  exact (coeff.fullFunction_cusp_differentiableAt constant (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

def truncatedCuspProfile (c : ℝ) (f : ℝ→ℂ) (x : ℝ) : ℂ :=
  if c<x then f x else 0

lemma truncatedCuspProfile_eventually_top (c : ℝ) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop c] with x hx
  simp only [truncatedCuspProfile,ite_eq_left hx]

lemma truncatedCuspProfile_eventually_zero (c : ℝ) (hc : 0<c) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[𝓝[>] 0] 0 := by
  have he : ∀ᶠx : ℝ in 𝓝[>] 0,x<c := (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with x hx
  simp only [truncatedCuspProfile,ite_eq_right (not_lt_of_ge hx.le),Pi.zero_apply]

lemma truncatedCuspProfile_locallyIntegrable (c : ℝ) (hc : 0<c) (f : ℝ→ℂ)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    LocallyIntegrable (truncatedCuspProfile c f) volume := by
  have hcont : Continuous (fun x : ℝ=>f (max (c/2) x)) :=
    hf.comp_continuous (continuous_const.max continuous_id)
      (fun x=>lt_of_lt_of_le (by linarith : 0<c/2) (le_max_left _ _))
  have he : truncatedCuspProfile c f=
      (Set.Ioi c).indicator (fun x : ℝ=>f (max (c/2) x)) := by
    funext x
    by_cases hx : c<x
    · have hm : max (c/2) x=x := max_eq_right (by linarith)
      simp [truncatedCuspProfile,Set.indicator,hx,hm]
    · simp [truncatedCuspProfile,Set.indicator,hx]
  rw [he]
  exact hcont.locallyIntegrable.indicator measurableSet_Ioi

theorem truncatedCuspProfile_mellin_entire (c decay : ℝ) (hc : 0<c) (hdecay : 0<decay)
    (f : ℝ→ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (hbound : f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x))) :
    (∀s : ℂ,MellinConvergent (truncatedCuspProfile c f) s) ∧
      Differentiable ℂ (mellin (truncatedCuspProfile c f)) := by
  have hlocal := (truncatedCuspProfile_locallyIntegrable c hc f hf).locallyIntegrableOn (Set.Ioi 0)
  have htop : truncatedCuspProfile c f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x)) :=
    hbound.congr' (truncatedCuspProfile_eventually_top c f).symm Filter.EventuallyEq.rfl
  have hzero (b : ℝ) : truncatedCuspProfile c f =O[𝓝[>] 0] (fun x : ℝ=>x^(-b)) :=
    (Asymptotics.isBigO_zero (fun x : ℝ=>x^(-b)) (𝓝[>] 0)).congr'
      (truncatedCuspProfile_eventually_zero c hc f).symm Filter.EventuallyEq.rfl
  constructor
  · intro s
    exact mellinConvergent_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)
  · intro s
    exact mellin_differentiableAt_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.SourceBesselExpansion -/

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

section
local notation "Eis" => ActualEisensteinCubic.O

lemma opposite_height_fourier_average (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
      cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
    cuspWeightedFourierPhase ρ h w
  have hg:Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
  have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*unramifiedCubicGaussSeries s (9*h) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    have he (z:ℂ) : oppositeEisenstein z v hv0 s*(ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ρ v*(oppositeEisenstein z v hv0 s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by ring
    simp_rw [he]
    rw [integral_const_mul,oppositeEisenstein_fourier v hv0 s hs h]
    ring
  have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
    rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
    congr 1
    exact Complex.cpow_natCast _ 3
  dsimp only
  rw [hinner,hp]
  ring

lemma oppositeHeight_cross_identity (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    Set.EqOn (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*
      cuspWhittakerHeightFactor s h) domain := fun s hs=>
    (translatedHeightFamily_analyticAt a b ha ρ h oppositeSource s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspIntervalWhittakerHeightFactor a b ρ s h) domain := fun s hs=>
    (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedHeightFamily a b ha ρ h oppositeSource s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedHeightFamily_initial a b ha ρ h oppositeSource s hs.1 hs.2,
      opposite_height_fourier_average a b ha ρ h s (by linarith [hs.1]),
      translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      opposite_cusp_fourier_average s (by linarith [hs.1])]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedHeightFourier_opposite_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  have hfixed := (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hvar := (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hl:=((translatedHeightFamily_residue_limit a b ha ρ h oppositeSource).mul hfixed).comp upperVertical_tendsto_cubic_punctured
  have hr:=((translatedCuspFamily_residue_limit h oppositeSource 2 3 (by norm_num) (by norm_num)).mul hvar).comp
    upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedHeightFamily a b ha ρ h oppositeSource ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspIntervalWhittakerHeightFactor a b ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeHeight_cross_identity a b ha ρ h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      translatedCuspFourier h oppositeSource cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hev
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero h)
  rw [heq,translatedCuspFourier_unramified_residue]
  ring

end

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_height_fourier_right_T (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip a b,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspWeightedFourierPhase ρ h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspWeightedFourierPhase ρ h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspWeightedFourierPhase_continuous ρ h)
  change (∫w in cuspPeriodStrip a b,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip a b,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha f hf.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha f hf),
    cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0:0<v:=ha.trans_le hv.1
  have hslice : (∫z in periodDomain,f (cuspCoordinateLift (v,z)))=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫z in periodDomain,g (cuspCoordinateLift (v,z)) := by
    simp only [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
      cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    simpa only [mul_assoc] using period_integral_fourier_translation
      (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0)*ρ v)
      (fun m z=>congrArg (fun q:ℂ=>q*ρ v) (hyperbolicEisenstein_rational_periodic r m s hs z v hv0)) h (n:ℂ)
  dsimp only
  rw [hslice]
  ring

lemma translatedHeightFourier_residue_scaled_of_initial (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume) :
    translatedHeightFourier a b ha ρ h M cubicEisensteinResidue=
      c*translatedHeightFourier a b ha ρ h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedHeightFamily a b ha ρ h M
  let g : ℂ→ℂ := fun s=>c*translatedHeightFamily a b ha ρ h N s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedHeightFamily_analyticAt a b ha ρ h M s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedHeightFamily_analyticAt a b ha ρ h N s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedHeightFamily_initial a b ha ρ h M s hs.1 hs.2,
      translatedHeightFamily_initial a b ha ρ h N s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedHeightFamily_residue_limit a b ha ρ h M).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedHeightFamily_residue_limit a b ha ρ h N).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  dsimp only [f,g] at hv
  dsimp only [Function.comp_def]
  linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hv

lemma translatedHeightFourier_one (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h 1 F=kernelCuspHeightFourier a b ha ρ h F := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

lemma translatedHeightFourier_bruhat (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) (e:Fin 2) (sector:Fin 3⊕(Fin 3×Fin 3)) :
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep (e,sector))) cubicEisensteinResidue=
      match sector with
      | Sum.inl _=>kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue
      | Sum.inr ab=>ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
        translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue := by
  cases sector with
  | inl index =>
    rw [←one_mul (kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue),←translatedHeightFourier_one a b ha ρ h]
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    simp only [map_one,one_smul,one_mul]
  | inr ab =>
    apply translatedHeightFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    change (∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s (rationalComplex ModularGroup.S •
        (rationalComplex (ModularGroup.T^ab.2.val) • w))*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume
    simpa only [map_mul,mul_smul] using
      rational_height_fourier_right_T a b ha ρ ModularGroup.S ab.2.val h s (by linarith)

theorem kernelSourceProjection_height_fourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      (4:ℂ)⁻¹*(kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
        sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue) := by
  rw [kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  change (24:ℂ)⁻¹*(∑i:RationalBruhatIndex,
    translatedHeightFourier a b ha ρ h (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=_
  rw [Fintype.sum_prod_type]
  simp_rw [translatedHeightFourier_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_mul]
  change (24:ℂ)⁻¹*((2:ℂ)*(3*kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue+
    3*(sourceRayPhaseSum h*translatedHeightFourier a b ha ρ h oppositeSource cubicEisensteinResidue)))=_
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspIntervalWhittakerHeightFactor_zero_center (a b:ℝ) (_ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) 0=
      (3*(Real.pi:ℂ))*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero (4/3) (by norm_num)]
  have he : -(4/3:ℂ)-1=-(7/3:ℂ) := by ring
  rw [he]
  ring

lemma kernelCuspHeightFourier_principal_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspHeightFourier_zero_residue_seven_thirds,cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    simp only [principalArithmeticResidue,ite_true]
    ring
  · simpa only [principalArithmeticResidue,ite_eq_right hh] using kernelCuspHeightFourier_residue_factor a b ha ρ h hh

lemma principalArithmeticResidue_not_horizontal (h:Eis) (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    principalArithmeticResidue h=0 := by
  have h0:h≠0 := by intro he;subst h;simp [cuspFrequency] at hh
  rw [principalArithmeticResidue,ite_eq_right h0,nonzeroScatteringResidue,
    kernelCuspFourier_residue_eq_zero_of_not_horizontal h hh,zero_div]

theorem kernelSourceProjection_height_residue (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  rw [kernelSourceProjection_height_fourier,kernelCuspHeightFourier_principal_residue,
    translatedHeightFourier_opposite_residue,sourceRayPhaseSum_eq,sourceArithmeticResidue]
  split_ifs with hh
  · field_simp [cusp_volume_ne_zero]

  · rw [principalArithmeticResidue_not_horizontal h hh]
    ring

def sourceResidualFourierCoefficient (h:Eis) : ℂ := cubicBesselNormalizer h*sourceArithmeticResidue h

def sourceResidualFullModeAmplitude (v:ℝ) (h:Eis) : ℂ :=
  if h=0 then (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
  else sourceResidualFourierCoefficient h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma sourceResidualFullModeAmplitude_zero_density (v:ℝ) (hv:0<v) :
    sourceResidualFullModeAmplitude v 0/(v:ℂ)^3=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)) := by
  simpa [sourceResidualFullModeAmplitude,cubicResidualFullModeAmplitude] using
    cubicResidualFullModeAmplitude_zero_density v hv

lemma sourceResidualFullModeAmplitude_nonzero_density (v:ℝ) (hv:0<v) (h:Eis) (hh:h≠0) :
    sourceResidualFullModeAmplitude v h/(v:ℂ)^3=sourceResidualFourierCoefficient h*
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [sourceResidualFullModeAmplitude,ite_eq_right hh]
  have hv0:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

lemma kernelSourceProjection_height_bessel (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (hh:h≠0) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFourierCoefficient h*
        ∫v in Set.Icc a b,ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [kernelSourceProjection_height_residue,cuspIntervalWhittakerHeightFactor_center_bessel a b ha ρ h hh,
    sourceResidualFourierCoefficient]
  ring

theorem kernelSourceProjection_height_full (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (h:Eis) :
    kernelCuspHeightFourier a b ha ρ h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  by_cases hh:h=0
  · subst h
    rw [kernelSourceProjection_height_residue,sourceArithmeticResidue_zero,
      cuspIntervalWhittakerHeightFactor_zero_center a b ha ρ]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v 0/(v:ℂ)^3))=
        ((3*(Real.pi:ℂ))*constantArithmeticResidue)*∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
      ring
    rw [he]
    ring
  · rw [kernelSourceProjection_height_bessel a b ha ρ h hh]
    have he : (∫v in Set.Icc a b,ρ v*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3))=
        sourceResidualFourierCoefficient h*∫v in Set.Icc a b,
          ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [sourceResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh]
      ring
    rw [he]
    ring

end

local notation "O" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖*
        ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖≤C := by
  obtain ⟨C,hC,hbound⟩ := kernelCuspHeightFourier_uniform_bound a b ha
  let area : ℂ := ((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea : 0<‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C*‖(kernelSourceProjection cubicEisensteinResidue)‖/‖area‖,div_nonneg (mul_nonneg hC (norm_nonneg _)) harea.le,?_⟩
  intro h hh
  have heq := kernelSourceProjection_height_bessel a b ha (BoundedContinuousFunction.const ℝ (1:ℂ)) h hh
  have hhbound := hbound (BoundedContinuousFunction.const ℝ (1:ℂ)) h (kernelSourceProjection cubicEisensteinResidue)
  rw [heq] at hhbound
  simp only [BoundedContinuousFunction.const_apply,one_mul,BoundedContinuousFunction.norm_const_eq,
    norm_one,mul_one,norm_mul,mul_assoc] at hhbound
  apply (le_div_iff₀ harea).mpr
  simpa only [area,mul_assoc,mul_comm,mul_left_comm] using hhbound

lemma sourceResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖sourceResidualFourierCoefficient h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let b : ℝ := ε/(9*Real.pi)
  let a : ℝ := b/2
  have hb : 0<b := div_pos hε (by positivity)
  have ha : 0<a := half_pos hb
  have hab : a<b := by dsimp [a]; linarith
  obtain ⟨C,hC,hbound⟩ := sourceResidualFourierCoefficient_interval_bound a b ha
  let D : ℝ := (b-a)*cubicBesselLowerConstant/b^2
  have hD : 0<D := div_pos (mul_pos (sub_pos.mpr hab) cubicBesselLowerConstant_pos) (sq_pos_of_pos hb)
  refine ⟨C/D,div_nonneg hC hD.le,?_⟩
  intro h hh
  have hlow := cubicBesselHeight_average_lower a b ha hab h hh
  have hscale : -9*Real.pi*b*‖cuspFrequency h‖=-(ε*‖cuspFrequency h‖) := by
    dsimp [b]
    field_simp
  rw [hscale] at hlow
  have hmul := (mul_le_mul_of_nonneg_left hlow (norm_nonneg (sourceResidualFourierCoefficient h))).trans
    (hbound h hh)
  have he : 0<Real.exp (-(ε*‖cuspFrequency h‖)) := Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD he)).mpr at hmul
  calc
    _ ≤ C/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hmul
    _ = (C/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg]; field_simp

def sourceBesselCoefficients : SubexponentialBesselCoefficients where
  value := sourceResidualFourierCoefficient
  growth := sourceResidualFourierCoefficient_subexponential

def sourceBesselFunction : HyperbolicSpace→ℂ :=
  sourceBesselCoefficients.fullFunction ((3*(Real.pi:ℂ))*constantArithmeticResidue)

lemma sourceBesselFunction_continuous : Continuous sourceBesselFunction :=
  sourceBesselCoefficients.fullFunction_continuous _

lemma sourceBesselFunction_fourier (v:ℝ) (hv:0<v) (h:ActualEisensteinCubic.O) :
    (∫z in periodDomain,sourceBesselFunction (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  rw [sourceBesselFunction,sourceBesselCoefficients.fullFunction_fourier]
  by_cases hh:h=0
  · simp [sourceResidualFullModeAmplitude,hh]
  · simp only [ite_eq_right hh,SubexponentialBesselCoefficients.amplitude,sourceResidualFullModeAmplitude]
    rfl

lemma sourceBesselFunction_period (v:ℝ) (hv:0<v) (z:ℂ) (n:ActualEisensteinCubic.O) :
    sourceBesselFunction (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      sourceBesselFunction (upperPoint z v hv) :=
  sourceBesselCoefficients.fullFunction_period _ v hv z n

lemma sourceBesselFunction_height_memLp (v:ℝ) (hv:0<v) :
    MemLp (fun z:ℂ=>sourceBesselFunction (cuspCoordinateLift (v,z))) 2 (volume.restrict periodDomain) :=
  sourceBesselCoefficients.fullFunction_height_memLp _ v hv

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma sourceResidualFullMode_density_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => sourceResidualFullModeAmplitude v h/(v:ℂ)^3)
      (Set.Icc a b) volume := by
  by_cases hh : h=0
  · subst h
    have hi : IntegrableOn (fun v : ℝ =>
        (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)))
        (Set.Icc a b) volume := by
      apply ContinuousOn.integrableOn_Icc
      intro v hv
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const v
        (-(7/3:ℂ)) (Or.inr (ha.trans_le hv.1).ne'))).continuousWithinAt
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (sourceResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)).symm
  · apply ((cubicBesselHeight_integrable a b ha h hh).const_mul
      (sourceResidualFourierCoefficient h)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (sourceResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh).symm

lemma projectedResidue_slice_coefficient_ae (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  apply interval_ae_eq_of_boundedContinuous_height_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h (kernelSourceProjection cubicEisensteinResidue))
    ((sourceResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [←kernelCuspHeightFourier_eq_slice_integral a b ha ρ h (kernelSourceProjection cubicEisensteinResidue),
    kernelSourceProjection_height_full a b ha ρ h,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)

lemma projectedResidue_all_slice_coefficients_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      kernelCuspSliceCoefficient (kernelSourceProjection cubicEisensteinResidue) h v =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(sourceResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  exact ae_all_iff.mpr (fun h => projectedResidue_slice_coefficient_ae a b ha h)

lemma projectedResidue_all_fourier_integrals_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,
        (kernelSourceProjection cubicEisensteinResidue) (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  filter_upwards [projectedResidue_all_slice_coefficients_ae a b ha,
    ae_restrict_mem measurableSet_Icc] with v hv hvmem
  intro h
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hvmem.1).ne'
  have he := hv h
  unfold kernelCuspSliceCoefficient at he
  rw [←mul_div_assoc] at he
  exact (div_left_inj' (pow_ne_zero 3 hv0)).mp he

theorem projectedResidue_cell_slices_ae (a b:ℝ) (ha:0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z:ℂ=>kernelSourceProjection cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z))))
      =ᵐ[volume.restrict periodDomain] (fun z=>sourceBesselFunction (cuspCoordinateLift (v,z))) := by
  filter_upwards [projectedResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha (kernelSourceProjection cubicEisensteinResidue),
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos:0<v:=ha.trans_le hv.1
  apply periodDomain_L2_ext _ _ hL (sourceBesselFunction_height_memLp v hpos)
  intro h
  rw [hfour h]
  symm
  simpa only [cuspCoordinateLift_positive v _ hpos] using sourceBesselFunction_fourier v hpos h

theorem sourceBesselFunction_represents_projection :
    (fun w=>kernelSourceProjection cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceBesselFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable (kernelSourceProjection cubicEisensteinResidue)).measurable.comp
      (measurable_integralOrbitProjection _)) sourceBesselFunction_continuous.measurable
  · intro v hv z n
    exact congrArg (kernelSourceProjection cubicEisensteinResidue) (kernelProjection_upper_period v hv z n)
  · exact sourceBesselFunction_period
  · exact projectedResidue_cell_slices_ae

theorem cubicSourceResidualFunction_eq_bessel : cubicSourceResidualFunction=sourceBesselFunction := by
  have he : cubicSourceResidualFunction=ᵐ[hyperbolicVolume]sourceBesselFunction := by
    filter_upwards [cubicSourceResidualFunction_represents_projection,sourceBesselFunction_represents_projection]
      with w hw hs
    exact hw.symm.trans hs
  exact Measure.eq_of_ae_eq he cubicSourceResidualFunction_continuous sourceBesselFunction_continuous

theorem cubicSourceResidualFunction_fourier_full (v:ℝ) (hv:0<v) (h:ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicSourceResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceResidualFullModeAmplitude v h := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_fourier v hv h

theorem cubicSourceResidualFunction_bessel (v:ℝ) (hv:0<v) (z:ℂ) :
    cubicSourceResidualFunction (upperPoint z v hv)=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)+
      ∑'h:ActualEisensteinCubic.O,(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [cubicSourceResidualFunction_eq_bessel,sourceBesselFunction,SubexponentialBesselCoefficients.fullFunction,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    sourceBesselCoefficients.series_bessel v hv z]
  rfl

theorem sourceResidual_series_uniform (a b:ℝ) (ha:0<a) (hab:a≤b) :
    TendstoUniformlyOn (fun t : Finset ActualEisensteinCubic.O => fun p : ℝ × ℂ => ∑ h ∈ t, sourceBesselCoefficients.term h p)
      sourceBesselCoefficients.series atTop {p : ℝ × ℂ | p.1 ∈ Set.Icc a b} :=
  sourceBesselCoefficients.series_uniform a b ha hab

theorem sourceResidual_bessel_normal (a b:ℝ) (ha:0<a) (hab:a≤b) :
    ∃g : ActualEisensteinCubic.O→ℝ, Summable g ∧ ∀(h:ActualEisensteinCubic.O)(v:ℝ),v∈Set.Icc a b→∀z:ℂ,
      ‖(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z)‖≤g h := by
  obtain ⟨C,hC,hbound⟩:=sourceBesselCoefficients.slab_bound a b ha hab
  refine ⟨fun h=>C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖),
    (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C,?_⟩
  intro h v hv z
  have he:=hbound h (v,z) hv
  rw [sourceBesselCoefficients.term_eq_amplitude v (ha.trans_le hv.1) h z] at he
  exact he

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ReflectedCuspMellin -/

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
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

def reflectedCuspProfile (A : ℂ) (Q : ℝ) (g : ℝ→ℂ) (v : ℝ) : ℂ :=
  A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))

lemma reflectedCuspProfile_mellin (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (reflectedCuspProfile A Q g) s=
      A*(Q:ℂ)^(2-s)*mellin g (2-s) := by
  unfold reflectedCuspProfile
  have hh := cusp_mellin_reflection g A (s/2) Q hQ
  simpa only [show (2*(s/2):ℂ)=s by ring,reflectedCuspProfile] using hh

lemma reflectedCuspProfile_mellinConvergent (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ)
    (hQ : 0<Q) (hg : MellinConvergent g (2-s)) :
    MellinConvergent (reflectedCuspProfile A Q g) s := by
  unfold reflectedCuspProfile
  have hinv : MellinConvergent (fun t : ℝ=>g t⁻¹) (s-2) := by
    have hh := (MellinConvergent.comp_rpow (f := g) (s := s-2)
      (a := -1) (by norm_num : (-1:ℝ)≠0)).mpr
        (show MellinConvergent g ((s-2)/(-1:ℝ)) by
          simpa only [show ((s-2)/(-1:ℝ):ℂ)=2-s by push_cast;ring] using hg)
    simpa only [Real.rpow_neg_one] using hh
  have hscale := (MellinConvergent.comp_mul_left (f := fun t : ℝ=>g t⁻¹)
    (s := s-2) hQ).mpr hinv
  have hpow := (MellinConvergent.cpow_smul (f := fun t : ℝ=>g (Q*t)⁻¹)
    (s := s) (a := -2)).mpr (by simpa only [sub_eq_add_neg] using hscale)
  simpa only [reflectedCuspProfile,smul_eq_mul] using hpow.const_smul A

lemma cusp_truncation_reflection_ae (f g : ℝ→ℂ) (A : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    f =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun v=>truncatedCuspProfile 1 f v+
        reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) := by
  have hne : ∀ᵐv : ℝ ∂volume.restrict (Set.Ioi 0),v≠1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with v hv hv1
  have hrel : 1/Q<(Q*v)⁻¹ ↔ v<1 := by
    rw [inv_eq_one_div,div_lt_div_iff₀ hQ (mul_pos hQ hv)]
    constructor <;> intro hh <;> nlinarith
  by_cases hhi : 1<v
  · have hlo : ¬1/Q<(Q*v)⁻¹ := fun hh=>not_lt_of_ge hhi.le (hrel.mp hh)
    simp only [truncatedCuspProfile,ite_eq_left hhi,reflectedCuspProfile,ite_eq_right hlo,
      mul_zero,add_zero]
  · have hlo : 1/Q<(Q*v)⁻¹ := hrel.mpr (lt_of_le_of_ne (le_of_not_gt hhi) hv1)
    simp only [truncatedCuspProfile,ite_eq_right hhi,reflectedCuspProfile,ite_eq_left hlo,zero_add]
    exact hfg v hv

theorem cusp_mellin_entire (f g : ℝ→ℂ) (A : ℂ) (Q decayF decayG : ℝ)
    (hQ : 0<Q) (hdecayF : 0<decayF) (hdecayG : 0<decayG)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ=>Real.exp (-decayF*v)))
    (hgbound : g =O[atTop] (fun v : ℝ=>Real.exp (-decayG*v)))
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    (∀s : ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  obtain ⟨hfc,hfd⟩ := truncatedCuspProfile_mellin_entire 1 decayF (by norm_num) hdecayF f hf hfbound
  obtain ⟨hgc,hgd⟩ := truncatedCuspProfile_mellin_entire (1/Q) decayG
    (by positivity) hdecayG g hg hgbound
  have hae := cusp_truncation_reflection_ae f g A Q hQ hfg
  have hresult (s : ℂ) : HasMellin f s
      (mellin (truncatedCuspProfile 1 f) s+
        A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) := by
    have hr := reflectedCuspProfile_mellinConvergent
      (truncatedCuspProfile (1/Q) g) A s Q hQ (hgc (2-s))
    have hsum := hasMellin_add (hfc s) hr
    constructor
    · apply hsum.1.congr
      filter_upwards [hae] with v hv
      exact congrArg (fun z : ℂ=>(v:ℂ)^(s-1) • z) hv.symm
    · have he : mellin f s=mellin (fun v=>truncatedCuspProfile 1 f v+
          reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) s := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with v hv
        rw [hv]
      rw [he,hsum.2,reflectedCuspProfile_mellin _ _ _ _ hQ]
  refine ⟨fun s=>(hresult s).1,?_⟩
  have he : mellin f=(fun s : ℂ=>mellin (truncatedCuspProfile 1 f) s+
      A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) :=
    funext (fun s=>(hresult s).2)
  rw [he]
  let : NeZero (Q:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hQ.ne'⟩
  have hp := (differentiable_const_cpow_of_neZero (Q:ℂ)).comp
    ((differentiable_const (2:ℂ)).sub differentiable_id)
  exact hfd.add (((differentiable_const A).mul hp).mul
    (hgd.comp ((differentiable_const (2:ℂ)).sub differentiable_id)))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def directionalTerm (h : ActualEisensteinCubic.O) (v : ℝ) (z direction : ℂ) : ℂ :=
  horizontalPhaseMultiplier (cuspFrequency h) direction*coeff.term h (v,z)

lemma term_horizontal_hasDerivAt (h : ActualEisensteinCubic.O) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))
      (coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (brevePhase_hasDerivAt (cuspFrequency h) z direction t).const_mul
    (coeff.amplitude v h)
  have hf : (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))=
      (fun x : ℝ => coeff.amplitude v h*
        ShortDraftTrace.breveE (cuspFrequency h*(z+(x:ℂ)*direction))) := by
    funext x
    exact coeff.term_eq_amplitude v hv h _
  rw [hf]
  convert hh using 1
  rw [directionalTerm,coeff.term_eq_amplitude v hv h]
  ring

lemma directionalTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),v∈Set.Icc a b →
      ‖coeff.directionalTerm h v z direction‖≤
        C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hv
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h (v,z) hv)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma directionalTerm_summable (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => coeff.directionalTerm h v z direction) := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound v v hv le_rfl direction
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h v z ⟨le_rfl,le_rfl⟩)
  exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C

lemma series_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.series (v,z+(x:ℂ)*direction))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound v v hv le_rfl direction
  have hs := (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : ActualEisensteinCubic.O => coeff.term h (v,z+(0:ℂ)*direction)) := by
    simpa only [zero_mul,add_zero] using coeff.summable (v,z) hv
  exact hasDerivAt_tsum hs (fun h x => coeff.term_horizontal_hasDerivAt h v hv z direction x)
    (fun h x => hbound h v (z+(x:ℂ)*direction) ⟨le_rfl,le_rfl⟩) hz t

lemma fullFunction_horizontal_hasDerivAt (constant : ℂ) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.fullFunction constant (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (coeff.series_horizontal_hasDerivAt v hv z direction t).const_add
    (constant*(v:ℂ)^(2/3:ℂ))
  simpa only [fullFunction,function,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint] using hh

theorem fullFunction_wirtingerBar (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w => coeff.fullFunction constant (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*star (cuspFrequency h))*coeff.term h (v,z) := by
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  have hs1 := coeff.directionalTerm_summable v hv z 1
  have hsI := (coeff.directionalTerm_summable v hv z Complex.I).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_add hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

lemma fullFunction_wirtingerBar_summable (v : ℝ) (hv : 0<v) (z : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => (2*Real.pi*Complex.I*star (cuspFrequency h))*coeff.term h (v,z)) := by
  have hs := ((coeff.directionalTerm_summable v hv z 1).add
    ((coeff.directionalTerm_summable v hv z Complex.I).mul_left Complex.I)).mul_left (1/2:ℂ)
  apply hs.congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma term_cusp_bound (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.term h (v,z)‖≤C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,mul_nonneg hC (cubicBesselUpperAway_pos delta hdelta).le,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · simp only [term,ite_eq_left hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hav ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [coeff.term_bessel h hh v hv z,norm_mul,norm_mul,norm_mul,
    breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*v*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hcoeff h hh) hv.le)
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*cubicBesselUpperAway delta)*v*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*v)/2=
        -(4*Real.pi*‖cuspFrequency h‖*v/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hav (mul_pos Real.pi_pos hr).le]

lemma directionalTerm_cusp_majorant (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃D : ℝ,0≤D ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.directionalTerm h v z direction‖≤
        (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*
          (‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := coeff.term_cusp_bound a ha
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · subst h
    simp only [directionalTerm,term,ite_true,mul_zero,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
      Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
      (show 0≤Real.pi*v/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
    unfold residualCuspDecayRate
    nlinarith
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h v z hav)
        (norm_nonneg _) (by positivity)
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*(Real.exp (-(2*residualCuspDecayRate)*v)*
          Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖))) := by
      gcongr
    _ = _ := by ring

lemma directionalSeries_cusp_decay (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(z : ℂ),a≤v →
      ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z direction‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hbound⟩ := coeff.directionalTerm_cusp_majorant a ha direction
  have hc := residualCuspDecayRate_pos
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hs := summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by positivity,?_⟩
  intro v z hav
  have hsum := tsum_of_norm_bounded
    (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v)))
    (fun h => hbound h v z hav)
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*
        Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem fullFunction_wirtingerBar_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := coeff.directionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := coeff.directionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma spatialComplexSplit_differentiable : Differentiable ℝ spatialComplexSplit := by
  change Differentiable ℝ (fun p : EuclideanSpatial => (p 2,(p 0:ℂ)+(p 1:ℂ)*Complex.I))
  fun_prop

lemma spatialComplexSplit_symm_differentiable : Differentiable ℝ spatialComplexSplit.symm := by
  change Differentiable ℝ (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  have hlin := (WithLp.linearEquiv 2 ℝ (Fin 3→ℝ)).symm.toContinuousLinearMap.differentiable
  have hcoords : Differentiable ℝ (fun q : ℝ × ℂ => ![q.2.re,q.2.im,q.1]) := by
    apply differentiable_pi.mpr
    intro j
    fin_cases j
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.re)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.im)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.1)
      fun_prop
  exact hlin.comp hcoords

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_euclidean_differentiableAt (constant : ℂ) (p : EuclideanSpatial) (hp : 0<p 2) :
    DifferentiableAt ℝ (fun q : EuclideanSpatial => coeff.fullFunction constant (euclideanToHyperbolic q)) p := by
  have hh := (coeff.fullFunction_cusp_differentiableAt constant (spatialComplexSplit p) hp).comp p
    spatialComplexSplit_differentiable.differentiableAt
  simpa only [Function.comp_def,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply] using hh

lemma fullFunction_translate_cusp_differentiableAt (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (g • cuspCoordinateLift q)) p := by
  have hx : 0<(spatialComplexSplit.symm p) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hp
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g (spatialComplexSplit.symm p) hx
  have hh := ((coeff.fullFunction_euclidean_differentiableAt constant
    (euclideanAction g (spatialComplexSplit.symm p)) (euclideanAction_positive _ _)).comp _
      hA.differentiableAt).comp p spatialComplexSplit_symm_differentiable.differentiableAt
  simpa only [Function.comp_def,euclideanAction,euclideanToHyperbolic_coordinates,cuspCoordinateLift] using hh

lemma fullFunction_translate_split_differentiableAt (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => coeff.fullFunction constant (g • cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : DifferentiableAt ℝ (fun q : ℂ × ℝ => (q.2,q.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  exact (coeff.fullFunction_translate_cusp_differentiableAt constant g (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceResidualFunction (g • cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_differentiableAt
    ((3*(Real.pi:ℂ))*constantArithmeticResidue) g p hp

lemma cubicSourceResidualFunction_split_differentiableAt (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceResidualFunction (cuspCoordinateLift (q.2,q.1))) p := by
  simpa only [one_smul] using cubicSourceResidualFunction_translate_split_differentiableAt 1 p hp

lemma cubicSourceResidualFunction_wirtingerBar (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*star (cuspFrequency h))*sourceBesselCoefficients.term h (v,z) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerBar _ v hv z

lemma cubicSourceResidualFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerBar_cusp_decay _ a ha

end

local notation "O" => ActualEisensteinCubic.O

lemma horizontalPhaseMultiplier_wirtingerZ (freq : ℂ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq 1-
      Complex.I*horizontalPhaseMultiplier freq Complex.I)=2*Real.pi*Complex.I*freq := by
  simp only [horizontalPhaseMultiplier,mul_one,star_mul,Complex.star_def,
    Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ring

lemma horizontalWirtingerBar_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerBar (fun w => star (f w)) z=star (horizontalWirtingerZ f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp []

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_wirtingerZ (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*cuspFrequency h)*coeff.term h (v,z) := by
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerZ,h1,hI]
  have hs1 := coeff.directionalTerm_summable v hv z 1
  have hsI := (coeff.directionalTerm_summable v hv z Complex.I).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_sub hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v,z)*horizontalPhaseMultiplier_wirtingerZ (cuspFrequency h)

lemma fullFunction_wirtingerZ_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := coeff.directionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := coeff.directionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerZ,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_wirtingerZ (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*cuspFrequency h)*sourceBesselCoefficients.term h (v,z) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerZ _ v hv z

lemma cubicSourceResidualFunction_wirtingerZ_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerZ_cusp_decay _ a ha

def cubicSourceConjugateFunction (w : HyperbolicSpace) : ℂ := star (cubicSourceResidualFunction w)

lemma cubicSourceConjugateFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceConjugateFunction (g • cuspCoordinateLift (q.2,q.1))) p :=
  (cubicSourceResidualFunction_translate_split_differentiableAt g p hp).star

lemma cubicSourceConjugateFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicSourceConjugateFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerZ_cusp_decay a ha
  refine ⟨C,hC,?_⟩
  intro v hv z hav
  simpa only [cubicSourceConjugateFunction,horizontalWirtingerBar_star,norm_star] using hbound v hv z hav

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

lemma horizontalWirtingerBar_translate (f : ℂ→ℂ) (a : ℂ) :
    horizontalWirtingerBar (fun z=>f (z+a)) 0=horizontalWirtingerBar f a := by
  unfold horizontalWirtingerBar
  simp only [zero_add]
  have h1 : (fun t : ℝ=>f ((t:ℂ)+a))=(fun t : ℝ=>f (a+(t:ℂ))) := by
    funext t
    rw [add_comm]
  have hI : (fun t : ℝ=>f ((t:ℂ)*Complex.I+a))=(fun t : ℝ=>f (a+(t:ℂ)*Complex.I)) := by
    funext t
    rw [add_comm]
  rw [h1,hI]

lemma cuspDerivative_of_transform (f : HyperbolicSpace→ℂ) (g H : SL(2,ℂ))
    (κ : ℂ) (htransform : ∀w,f (g•w)=κ*f (H•w)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v)
    (hD : DifferentiableAt ℝ
      (fun q : ℂ × ℝ=>f (H•cuspCoordinateLift (q.2,q.1)))
      (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))) :
    horizontalWirtingerBar (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)=
      (κ*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  let FH : ℂ × ℝ→ℂ := fun q=>f (H•cuspCoordinateLift (q.2,q.1))
  let base : ℂ × ℝ := (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))
  let D := fderiv ℝ FH base
  have hF : HasFDerivAt FH D base := hD.hasFDerivAt
  have hscaled : HasFDerivAt (fun q=>κ*FH q) (κ • D) base := hF.const_mul κ
  have he := inverse_cusp_wirtingerBar (g 1 0) (g 1 1) v hc hv
    (fun q=>κ*FH q) (κ • D) hscaled
  have hline : (fun z=>κ*FH (inverseCuspCoordinates (g 1 0) (g 1 1) v z))=
      (fun z=>f (upperPoint (z+g 0 0/g 1 0) v hv)) := by
    funext z
    have ht := htransform (g⁻¹•upperPoint (z+g 0 0/g 1 0) v hv)
    rw [smul_inv_smul,inverse_cusp_action g hc v hv z] at ht
    change κ*f (H•cuspCoordinateLift
      ((inverseCuspCoordinates (g 1 0) (g 1 1) v z).2,
       (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1))=_
    rw [cuspCoordinateLift_positive _ _ (inverseCuspCoordinates_height_pos _ _ _ _ hc hv)]
    exact ht.symm
  rw [hline] at he
  have hshift := horizontalWirtingerBar_translate (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)
  rw [hshift] at he
  have hz := horizontalWirtingerZ_eq_fderiv FH D (-g 1 1/g 1 0) (1/(‖g 1 0‖^2*v)) hF
  have hFH : (fun z=>FH (z,1/(‖g 1 0‖^2*v)))=
      (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity))) := by
    funext z
    exact congrArg (fun w=>f (H•w)) (cuspCoordinateLift_positive _ _ (by positivity))
  rw [hFH] at hz
  rw [hz]
  rw [he]
  simp only [_root_.smul_apply,smul_eq_mul]
  ring

lemma cubicSourceResidualFunction_levelThree (G : CubicKubota.levelThree) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (complexMatrix G•w)=
      CubicKubota.complexCharacter G*cubicSourceResidualFunction w := by
  have hh := cubicSourceResidualFunction_automorphy (CubicKubota.sourceLevelInclusion G) w
  change cubicSourceResidualFunction (complexMatrix G•w)=
    CubicKubota.levelTwoComplexCharacter ⟨G.val,CubicKubota.levelThree_le_levelTwo G.property⟩*
      cubicSourceResidualFunction w at hh
  rw [CubicKubota.levelTwoComplexCharacter_restrict] at hh
  exact hh

lemma cubicSourceConjugateFunction_levelThree (G : CubicKubota.levelThree) (w : HyperbolicSpace) :
    cubicSourceConjugateFunction (complexMatrix G•w)=
      star (CubicKubota.complexCharacter G)*cubicSourceConjugateFunction w := by
  simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_levelThree,star_mul]
  ring

theorem cubicSourceResidualFunction_cuspDerivative (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceResidualFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (CubicKubota.complexCharacter G*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceResidualFunction (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceResidualFunction g H
    (CubicKubota.complexCharacter G) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceResidualFunction_levelThree]
  · exact cubicSourceResidualFunction_translate_split_differentiableAt H _ (by positivity)

theorem cubicSourceConjugateFunction_cuspDerivative (G : CubicKubota.levelThree)
    (g H : SL(2,ℂ)) (hfactor : g=complexMatrix G*H) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (star (CubicKubota.complexCharacter G)*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceConjugateFunction (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceConjugateFunction g H
    (star (CubicKubota.complexCharacter G)) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceConjugateFunction_levelThree]
  · exact cubicSourceConjugateFunction_translate_split_differentiableAt H _ (by positivity)

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Mellin.VerticalContourShift -/

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

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

lemma gaussian_regulator_norm (ε σ t : ℝ) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖=Real.exp (ε*(σ^2-t^2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

lemma gaussian_regulator_norm_le (ε σ t : ℝ) (hε0 : 0≤ε) (hε1 : ε≤1) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖≤Real.exp (σ^2) := by
  rw [gaussian_regulator_norm]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg σ,sq_nonneg t,mul_nonneg hε0 (sq_nonneg t),
    mul_nonneg (sub_nonneg.mpr hε1) (sq_nonneg σ)]

def gaussianRegulatorSequence (n : ℕ) : ℝ := 1/((n:ℝ)+1)

lemma gaussianRegulatorSequence_pos (n : ℕ) : 0<gaussianRegulatorSequence n := by
  unfold gaussianRegulatorSequence
  positivity

lemma gaussianRegulatorSequence_le_one (n : ℕ) : gaussianRegulatorSequence n≤1 := by
  unfold gaussianRegulatorSequence
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) n]

lemma gaussianRegulatorSequence_tendsto : Tendsto gaussianRegulatorSequence atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem gaussian_regulator_integral_tendsto (g : ℝ→ℂ) (hg : Integrable g) (σ : ℝ) :
    Tendsto (fun n : ℕ=>∫t : ℝ,
      Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)*g t)
      atTop (𝓝 (∫t : ℝ,g t)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ=>Real.exp (σ^2)*‖g t‖)
  · intro n
    have hc : Continuous (fun t : ℝ=>
        Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)) := by fun_prop
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact hg.norm.const_mul _
  · intro n
    exact Filter.Eventually.of_forall (fun t=>by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (gaussian_regulator_norm_le _ σ t (gaussianRegulatorSequence_pos n).le
          (gaussianRegulatorSequence_le_one n)) (norm_nonneg _))
  · filter_upwards with t
    have hε : Tendsto (fun n : ℕ=>(gaussianRegulatorSequence n:ℂ)) atTop (𝓝 0) :=
      by simpa only [Function.comp_def,Complex.ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp gaussianRegulatorSequence_tendsto
    have he := (Complex.continuous_exp.tendsto 0).comp
      (by simpa only [zero_mul] using hε.mul_const (((σ:ℂ)+t*Complex.I)^2))
    simpa only [Function.comp_def,Complex.exp_zero,one_mul] using he.mul_const (g t)

lemma rpow_between_endpoints (y a b σ : ℝ) (hy : 0<y) (ha : a≤σ) (hb : σ≤b) :
    y^σ≤y^a+y^b := by
  by_cases h1 : 1≤y
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hy.le a))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge h1) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le b))

theorem mellin_uniform_strip_bound (f : ℝ→ℂ) (a b : ℝ)
    (ha : MellinConvergent f (a:ℂ)) (hb : MellinConvergent f (b:ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,a≤ s.re→s.re≤b→‖mellin f s‖≤C := by
  let B : ℝ→ℝ := fun y=>‖(y:ℂ)^((a:ℂ)-1)*f y‖+‖(y:ℂ)^((b:ℂ)-1)*f y‖
  have hB : IntegrableOn B (Set.Ioi 0) := by
    exact ha.norm.add hb.norm
  refine ⟨∫y in Set.Ioi 0,B y,integral_nonneg (fun y=>add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro s hsa hsb
  unfold mellin
  apply norm_integral_le_of_norm_le hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 0<y at hy
  have hp := rpow_between_endpoints y (a-1) (b-1) (s.re-1) hy (by linarith) (by linarith)
  change ‖(y:ℂ)^(s-1)*f y‖≤B y
  dsimp only [B]
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (f y))

end VerticalContourShift

namespace GaussianMoment

lemma gaussian_le_inverse_quadratic (c t:ℝ) (hc:0<c) :
    Real.exp (-c*t^2)≤(1+2/c)/(1+t^2) := by
  have h0:Real.exp (-c*t^2)≤1:=by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg t]
  have h1:t^2*Real.exp (-c*t^2)≤2/c:=by
    have hm:=gaussian_moment_term_bound (t^2) c (sq_nonneg t) hc
    have he:Real.exp (-(c*t^2/2))≤1:=by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg t]
    exact hm.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left he (div_nonneg (by norm_num) hc.le))
  apply (le_div_iff₀ (by positivity : 0<1+t^2)).mpr
  nlinarith

lemma linear_height_young (A ε t:ℝ) (hε:0<ε) :
    A*|t|≤ε*t^2/2+A^2/(2*ε) := by
  have hs:0≤ε^2*t^2-2*ε*A*|t|+A^2:=by
    calc
      0≤(ε*|t|-A)^2:=sq_nonneg _
      _=ε^2*t^2-2*ε*A*|t|+A^2:=by rw [sub_sq,mul_pow,sq_abs];ring
  apply le_of_mul_le_mul_left (a := 2*ε) ?_
    (mul_pos (by norm_num : (0:ℝ)<2) hε)
  calc
    2*ε*(A*|t|)≤ε^2*t^2+A^2:=by nlinarith [hs]
    _=2*ε*(ε*t^2/2+A^2/(2*ε)):=by field_simp

theorem gaussian_regulator_strip_bound (a b A B ε:ℝ) (hB:0≤B) (hε:0<ε)
    (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|))
    (σ t:ℝ) (hσ:σ∈Set.Icc a b) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤
      (B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε))/(1+t^2) := by
  let R:ℝ:=max |a| |b|
  have hR:0≤R:=le_trans (abs_nonneg a) (le_max_left _ _)
  have hsabs:|σ|≤R:=abs_le_max_abs_abs hσ.1 hσ.2
  have hs:σ^2≤R^2:=by
    calc
      _=|σ|^2:=(sq_abs σ).symm
      _≤R^2:=pow_le_pow_left₀ (abs_nonneg σ) hsabs 2
  have hre:((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2).re=ε*(σ^2-t^2):=by
    simp [pow_two,Complex.mul_re,Complex.mul_im]

  have hE:ε*(σ^2-t^2)+A*|t|≤
      (ε*R^2+A^2/(2*ε))-(ε/2)*t^2:=by
    have hy:=linear_height_young A ε t hε
    nlinarith
  have hg:=gaussian_le_inverse_quadratic (ε/2) t (by positivity)
  have hg':Real.exp (-(ε/2)*t^2)≤(1+4/ε)/(1+t^2):=by
    convert hg using 1 ;field_simp ;ring
  rw [norm_mul,Complex.norm_exp,hre]
  calc
    _≤Real.exp (ε*(σ^2-t^2))*(B*Real.exp (A*|t|)):=
      mul_le_mul_of_nonneg_left (hf σ hσ t) (Real.exp_pos _).le
    _=B*Real.exp (ε*(σ^2-t^2)+A*|t|):=by rw [Real.exp_add];ring
    _≤B*Real.exp ((ε*R^2+A^2/(2*ε))-(ε/2)*t^2):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hB
    _=(B*Real.exp (ε*R^2+A^2/(2*ε)))*Real.exp (-(ε/2)*t^2):=by
      rw [Real.exp_sub,div_eq_mul_inv,←Real.exp_neg,neg_mul]
      ring
    _≤(B*Real.exp (ε*R^2+A^2/(2*ε)))*((1+4/ε)/(1+t^2)):=
      mul_le_mul_of_nonneg_left hg' (mul_nonneg hB (Real.exp_pos _).le)
    _=_:=by dsimp only [R];ring

theorem gaussian_regulator_strip_decay (a b A B ε:ℝ) (_hab:a≤b) (_hA:0≤A)
    (hB:0≤B) (hε:0<ε) (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|)) :
    ∃K:ℝ,0≤K ∧ ∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤K/(1+t^2) := by
  refine ⟨B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε),by positivity,?_⟩
  intro σ hσ t
  exact gaussian_regulator_strip_bound a b A B ε hB hε f hf σ t hσ

end GaussianMoment

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

theorem integral_eq_of_exponential_strip_growth
    (f : ℂ→ℂ) (a b A B : ℝ) (hab : a≤b) (hA : 0≤A) (hB : 0≤B)
    (hdiff : ∀z : ℂ,a≤z.re→z.re≤b→DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)))
    (hb : Integrable (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)))
    (hbound : ∀σ∈Set.Icc a b,∀t : ℝ,‖f ((σ:ℂ)+t*Complex.I)‖≤B*Real.exp (A*|t|)) :
    (∫t : ℝ,f ((a:ℂ)+t*Complex.I))=∫t : ℝ,f ((b:ℂ)+t*Complex.I) := by
  let F : ℕ→ℂ→ℂ := fun n z=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)*f z
  have hreg (n : ℕ) : Continuous (fun z : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)) := by
    fun_prop
  have hint (n : ℕ) (σ : ℝ) (hσ : Integrable (fun t : ℝ=>f ((σ:ℂ)+t*Complex.I))) :
      Integrable (fun t : ℝ=>F n ((σ:ℂ)+t*Complex.I)) := by
    apply hσ.bdd_mul (c:=Real.exp (σ^2))
    · exact ((hreg n).comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t=>gaussian_regulator_norm_le _ σ t
        (gaussianRegulatorSequence_pos n).le (gaussianRegulatorSequence_le_one n))
  have heq (n : ℕ) :
      (∫t : ℝ,F n ((a:ℂ)+t*Complex.I))=∫t : ℝ,F n ((b:ℂ)+t*Complex.I) := by
    obtain ⟨K,hK,hdec⟩ := GaussianMoment.gaussian_regulator_strip_decay a b A B
      (gaussianRegulatorSequence n) hab hA hB (gaussianRegulatorSequence_pos n) f hbound
    apply integral_eq_of_strip_decay (F n) a b K hab
    · intro z hza hzb
      have hg : Differentiable ℂ (fun w : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*w^2)) := by
        fun_prop
      exact hg.differentiableAt.mul (hdiff z hza hzb)
    · exact hint n a ha
    · exact hint n b hb
    · exact hdec
  have hleft := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)) ha a
  have hright := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)) hb b
  change Tendsto (fun n=>∫t : ℝ,F n ((a:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((a:ℂ)+t*Complex.I))) at hleft
  change Tendsto (fun n=>∫t : ℝ,F n ((b:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((b:ℂ)+t*Complex.I))) at hright
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end VerticalContourShift

namespace CubicGammaExponential
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

lemma norm_Gamma_le_real (z : ℂ) (hz : 0<z.re) :
    ‖Complex.Gamma z‖≤Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖≤Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    _ ≤ ‖Complex.exp (-z*Complex.I)‖+‖Complex.exp (z*Complex.I)‖ := norm_sub_le _ _
    _ = Real.exp z.im+Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im|+Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _)) (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = _ := by ring

lemma Gamma_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im≠0) : Complex.Gamma z≠0 := by
  apply Complex.Gamma_ne_zero
  intro n he
  apply hz
  have h:=congrArg Complex.im he
  simpa using h

lemma inverse_Gamma_reflection (z : ℂ) (hz : z.im≠0) :
    (Complex.Gamma z)⁻¹=Complex.Gamma (1-z)*Complex.sin (Real.pi*z)/Real.pi := by
  have hg:=Gamma_ne_zero_of_im_ne_zero z hz
  have hh:=Gamma_ne_zero_of_im_ne_zero (1-z) (by simpa using hz)
  have hp : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : Complex.sin (Real.pi*z)≠0 := by
    intro hs
    have he:=Complex.Gamma_mul_Gamma_one_sub z
    rw [hs,div_zero] at he
    exact (mul_ne_zero hg hh) he
  apply mul_left_cancel₀ hg
  rw [mul_inv_cancel₀ hg]
  symm
  calc
    _ = (Complex.Gamma z*Complex.Gamma (1-z))*Complex.sin (Real.pi*z)/Real.pi := by ring
    _ = 1 := by
      rw [Complex.Gamma_mul_Gamma_one_sub,div_mul_cancel₀ _ hs,div_self hp]

lemma inverse_Gamma_norm_of_left (z : ℂ) (hz : z.re<1) (hi : z.im≠0) :
    ‖(Complex.Gamma z)⁻¹‖≤
      (Real.Gamma (1-z.re)/Real.pi)*Real.exp (Real.pi*|z.im|) := by
  rw [inverse_Gamma_reflection z hi,norm_div,norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hgamma:=norm_Gamma_le_real (1-z) (by simp;linarith)
  have hsin:=norm_sin_le_exp_abs_im (Real.pi*z)
  simp only [Complex.sub_re,Complex.one_re] at hgamma
  have him : |((Real.pi:ℂ)*z).im|=Real.pi*|z.im| := by
    simp [abs_mul]
  rw [him] at hsin
  calc
    _ ≤ (Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|))/Real.pi :=
      div_le_div_of_nonneg_right
        (mul_le_mul hgamma hsin (norm_nonneg _) (Real.Gamma_pos_of_pos (by linarith)).le)
        Real.pi_pos.le
    _ = _ := by ring

lemma inverse_Gamma_norm_le_shift_left (z : ℂ) (n : ℕ) (hi : 1≤|z.im|) :
    ‖(Complex.Gamma z)⁻¹‖≤‖(Complex.Gamma (z-n))⁻¹‖ := by
  have he:=congrArg norm (CubicReflectionKernel.inverse_Gamma_shift (z-n) n)
  simp only [sub_add_cancel,norm_mul] at he
  have hprod : 1≤‖∏k∈Finset.range n,(z-(n:ℂ)+k)‖ := by
    rw [norm_prod]
    apply Finset.one_le_prod₀
    intro k hk
    calc
      1 ≤ |z.im| := hi
      _ = |(z-(n:ℂ)+k).im| := by simp
      _ ≤ _ := Complex.abs_im_le_norm _
  rw [he]
  exact le_mul_of_one_le_left (norm_nonneg _) hprod

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀x∈Set.Icc a b,Real.Gamma x≤C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx=>ha.trans_le hx.1)
  obtain ⟨C,hC⟩:=(isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

lemma inverse_Gamma_compact_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t∈Set.Icc (-1:ℝ) 1,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C := by
  have hc : Continuous (fun p : ℝ×ℝ=>
      ‖(Complex.Gamma ((p.1:ℂ)+p.2*Complex.I))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)).norm
  obtain ⟨C,hC⟩:=((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))).bddAbove_image hc.continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  intro σ hσ t ht
  exact (hC ⟨(σ,t),⟨hσ,ht⟩,rfl⟩).trans (by linarith [le_abs_self C])

theorem inverse_Gamma_strip_exp_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t : ℝ,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C*Real.exp (Real.pi*|t|) := by
  obtain ⟨n,hn⟩:=exists_nat_gt b
  obtain ⟨Cg,hCg,hg⟩:=real_Gamma_compact_bound ((n:ℝ)+1-b) ((n:ℝ)+1-a) (by linarith)
  obtain ⟨Cc,hCc,hc⟩:=inverse_Gamma_compact_strip_bound a b
  refine ⟨Cc+Cg/Real.pi,by positivity,?_⟩
  intro σ hσ t
  have hexp : 1≤Real.exp (Real.pi*|t|) := Real.one_le_exp (by positivity)
  by_cases ht:|t|≤1
  · have hsmall:=hc σ hσ t (abs_le.mp ht)
    calc
      _ ≤ Cc := hsmall
      _ ≤ Cc+Cg/Real.pi := le_add_of_nonneg_right (by positivity)
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        le_mul_of_one_le_right (by positivity) hexp
  · have ht1 : 1 < |t| :=lt_of_not_ge ht
    have ht0 : t≠0 := by intro ht0;subst t;norm_num at ht1
    let z : ℂ := (σ:ℂ)+t*Complex.I
    let w : ℂ := z-n
    have hw : w.re<1 := by
      dsimp [w,z]
      simp only [Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
        sub_zero,add_zero]
      linarith [hσ.2]
    have hwi : w.im≠0 := by simpa [w,z] using ht0
    have he : 1-w.re=(n:ℝ)+1-σ := by simp [w,z];ring
    have hi : w.im=t := by simp [w,z]
    have hbound:=inverse_Gamma_norm_of_left w hw hwi
    rw [he,hi] at hbound
    have hgbound:=hg ((n:ℝ)+1-σ) ⟨by linarith [hσ.2],by linarith [hσ.1]⟩
    calc
      _ ≤ ‖(Complex.Gamma w)⁻¹‖ :=
        inverse_Gamma_norm_le_shift_left z n (by simpa [z] using ht1.le)
      _ ≤ (Real.Gamma ((n:ℝ)+1-σ)/Real.pi)*Real.exp (Real.pi*|t|) := hbound
      _ ≤ (Cg/Real.pi)*Real.exp (Real.pi*|t|) := by gcongr
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCc.le) (Real.exp_pos _).le

theorem inverse_Gamma_strip_exp_bound_complex (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀z : ℂ,z.re∈Set.Icc a b →
      ‖(Complex.Gamma z)⁻¹‖≤C*Real.exp (Real.pi*|z.im|) := by
  obtain ⟨C,hC,hb⟩:=inverse_Gamma_strip_exp_bound a b
  refine ⟨C,hC,?_⟩
  intro z hz
  simpa only [Complex.re_add_im] using hb z.re hz z.im

theorem inverse_cubic_Gamma_pair_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖(Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹‖≤
        C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨C1,hC1,h1⟩:=inverse_Gamma_strip_exp_bound_complex (a+1/3) (b+1/3)
  obtain ⟨C2,hC2,h2⟩:=inverse_Gamma_strip_exp_bound_complex (a+2/3) (b+2/3)
  refine ⟨C1*C2,mul_pos hC1 hC2,?_⟩
  intro s hs
  have hb1:=h1 (s+1/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  have hb2:=h2 (s+2/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  norm_num at hb1 hb2
  rw [mul_inv_rev,norm_mul,norm_inv,norm_inv]
  calc
    _ ≤ (C2*Real.exp (Real.pi*|s.im|))*(C1*Real.exp (Real.pi*|s.im|)) :=
      mul_le_mul hb2 hb1 (by positivity) (by positivity)
    _ = C1*C2*Real.exp (2*Real.pi*|s.im|) := by
      rw [show 2*Real.pi*|s.im|=Real.pi*|s.im|+Real.pi*|s.im| by ring,Real.exp_add]
      ring

end CubicGammaExponential

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

lemma cubic_bessel_mellin_norm_scale (s : ℂ) (r : ℝ) (hr : 0< r) :
    (∫v : ℝ in Set.Ioi 0,‖(v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*r*v)‖)=
    r^(-(2*s.re+1))*(∫v : ℝ in Set.Ioi 0,
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖) := by
  let g : ℝ→ℝ := fun v=>‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖
  have hp (v : ℝ) (hv : 0<v) :
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*r*v)‖=
        r^(-(2*s.re))*g (r*v) := by
    dsimp only [g]
    rw [norm_mul,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hr hv)]
    simp only [show (2*s).re=2*s.re by simp]
    rw [Real.mul_rpow hr.le hv.le]
    rw [show 4*Real.pi*r*v=4*Real.pi*(r*v) by ring]
    have hc : r^(-(2*s.re))*r^(2*s.re)=1 := by
      rw [←Real.rpow_add hr]
      simp
    linear_combination -(v^(2*s.re)*‖schlafliBesselK (1/3) (4*Real.pi*(r*v))‖)*hc
  calc
    _=∫v : ℝ in Set.Ioi 0,r^(-(2*s.re))*g (r*v) :=
      setIntegral_congr_fun measurableSet_Ioi hp
    _=r^(-(2*s.re))*(r⁻¹*(∫v : ℝ in Set.Ioi 0,g v)) := by
      rw [integral_const_mul,integral_comp_mul_left_Ioi g 0 hr]
      simp
    _=_ := by
      rw [←mul_assoc,←Real.rpow_neg_one,←Real.rpow_add hr]
      congr 2
      ring

lemma weighted_cubic_bessel_integral_norm (s : ℂ) (freq a : ℂ) (hf : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,‖a*((v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v))‖)=
    (‖a‖*‖freq‖^(-(2*s.re+1)))*(∫v : ℝ in Set.Ioi 0,
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖) := by
  simp only [norm_mul,integral_const_mul]
  rw [←integral_const_mul]
  have h:=cubic_bessel_mellin_norm_scale s ‖freq‖ (norm_pos_iff.mpr hf)
  simp only [norm_mul] at h
  rw [integral_const_mul,h]
  ring

theorem cubic_bessel_series_mellin {α : Type*} [Countable α]
    (freq a : α→ℂ) (hf : ∀i,freq i≠0) (s : ℂ) (hs : -(1/3)<s.re)
    (ha : Summable (fun i=>‖a i‖*‖freq i‖^(-(2*s.re+1)))) :
    (∫v : ℝ in Set.Ioi 0,∑'i,a i*((v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq i‖*v)))=
    ∑'i,a i*(((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
      ((4*Real.pi*‖freq i‖:ℝ):ℂ)^(2*s+1)) := by
  have hi (i : α) := (source_cubic_bessel_mellin_integrable s (freq i) hs (hf i)).const_mul (a i)
  have hsum : Summable (fun i=>∫v : ℝ in Set.Ioi 0,
      ‖a i*((v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq i‖*v))‖) := by
    simp only [weighted_cubic_bessel_integral_norm s _ _ (hf _)]
    exact ha.mul_right _
  rw [←integral_tsum_of_summable_integral_norm hi hsum]
  apply tsum_congr
  intro i
  rw [integral_const_mul,source_cubic_bessel_mellin s (freq i) hs (hf i)]

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

lemma positive_sqrt_cpow_twice (r : ℝ) (hr : 0< r) (s : ℂ) :
    (Real.sqrt r:ℂ)^(2*s+1)=(r:ℂ)^(s+1/2) := by
  have ha : Complex.arg (Real.sqrt r:ℂ)=0 :=
    Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg r)
  have h := Complex.cpow_nat_mul' (x:=(Real.sqrt r:ℂ)) (n:=2)
    (by simpa only [ha,mul_zero] using (neg_lt_zero.mpr Real.pi_pos))
    (by simpa only [ha,mul_zero] using Real.pi_pos.le) (s+1/2)
  have hs : (Real.sqrt r:ℂ)^2=(r:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt hr.le]
  norm_num only at h
  simpa only [hs,show (2:ℂ)*(s+1/2)=2*s+1 by ring] using h

lemma radial_bessel_coefficient_norm (r q σ : ℝ) (hr : 0< r) (hq : 0<q) (a : ℂ) :
    ‖a*(r:ℂ)‖*‖((q*Real.sqrt r:ℝ):ℂ)‖^(-(2*σ+1))=
      q^(-(2*σ+1))*(‖a‖*r^(1/2-σ)) := by
  rw [norm_mul,Complex.norm_of_nonneg hr.le,
    Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr hr)).le,
    Real.mul_rpow hq.le (Real.sqrt_nonneg r),Real.sqrt_eq_rpow,
    ←Real.rpow_mul hr.le]
  have hp : r*r^((1/2)*(-(2*σ+1)))=r^(1/2-σ) := by
    calc
      _=r^1*r^((1/2)*(-(2*σ+1))) := by rw [Real.rpow_one]
      _=r^(1+(1/2)*(-(2*σ+1))) := (Real.rpow_add hr _ _).symm
      _=_ := by congr 1;ring
  calc
    _=q^(-(2*σ+1))*(‖a‖*(r*r^((1/2)*(-(2*σ+1))))) := by ring
    _=_ := by rw [hp]

lemma radial_bessel_coefficient_identity (r q : ℝ) (hr : 0< r) (hq : 0<q)
    (a B s : ℂ) :
    (a*(r:ℂ))*(B/((q*Real.sqrt r:ℝ):ℂ)^(2*s+1))=
      (B/(q:ℂ)^(2*s+1))*(a*(r:ℂ)^(1/2-s)) := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hq.le (Real.sqrt_nonneg r),
    positive_sqrt_cpow_twice r hr s]
  have hp : (r:ℂ)/(r:ℂ)^(s+1/2)=(r:ℂ)^(1/2-s) := by
    have h := Complex.cpow_sub (1:ℂ) (s+1/2) (Complex.ofReal_ne_zero.mpr hr.ne')
    rw [Complex.cpow_one] at h
    simpa only [show (1:ℂ)-(s+1/2)=1/2-s by ring] using h.symm
  calc
    _=(B/(q:ℂ)^(2*s+1))*(a*((r:ℂ)/(r:ℂ)^(s+1/2))) := by ring
    _=_ := by rw [hp]

def radialBesselProfile {α : Type*} (r : α→ℝ) (a : α→ℂ) (q v : ℝ) : ℂ :=
  ∑'i,(a i*(r i:ℂ))*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*q*Real.sqrt (r i)*v)

theorem radialBesselProfile_mellin {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0< r i) (a : α→ℂ) (q : ℝ) (hq : 0<q)
    (s : ℂ) (hs : -(1/3)<s.re)
    (ha : Summable (fun i=>‖a i‖*(r i)^(1/2-s.re))) :
    mellin (radialBesselProfile r a q) (2*s)=
      (((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*q:ℝ):ℂ)^(2*s+1))*(∑'i,a i*(r i:ℂ)^(1/2-s)) := by
  let f : α→ℂ := fun i=>((q*Real.sqrt (r i):ℝ):ℂ)
  have hf (i : α) : f i≠0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos hq (Real.sqrt_pos.mpr (hr i))).ne'
  have has : Summable (fun i=>‖a i*(r i:ℂ)‖*‖f i‖^(-(2*s.re+1))) := by
    simp only [f,radial_bessel_coefficient_norm _ q s.re (hr _) hq]
    exact ha.mul_left _
  have hid := cubic_bessel_series_mellin f (fun i=>a i*(r i:ℂ)) hf s hs has
  calc
    _=(∫v : ℝ in Set.Ioi 0,∑'i,(a i*(r i:ℂ))*((v:ℂ)^(2*s)*
        schlafliBesselK (1/3) (4*Real.pi*‖f i‖*v))) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only [radialBesselProfile]
      simp only [smul_eq_mul]
      rw [←tsum_mul_left]
      apply tsum_congr
      intro i
      have hp : (v:ℂ)^(2*s-1)*(v:ℂ)=(v:ℂ)^(2*s) := by
        calc
          _=(v:ℂ)^(2*s-1)*(v:ℂ)^1 := by rw [Complex.cpow_one]
          _=(v:ℂ)^((2*s-1)+1) :=
            (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')).symm
          _=_ := by rw [sub_add_cancel]
      have hn : ‖f i‖=q*Real.sqrt (r i) :=
        Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
      rw [hn]
      have hk : 4*Real.pi*q*Real.sqrt (r i)*v=4*Real.pi*(q*Real.sqrt (r i))*v := by ring
      rw [hk]
      change (v:ℂ)^(2*s-1)*_=_
      linear_combination (a i*(r i:ℂ))*schlafliBesselK (1/3) (4*Real.pi*(q*Real.sqrt (r i))*v)*hp
    _=_ := by
      rw [hid,←tsum_mul_left]
      apply tsum_congr
      intro i
      have hn : ‖f i‖=q*Real.sqrt (r i) :=
        Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
      rw [hn,show 4*Real.pi*(q*Real.sqrt (r i))=(4*Real.pi*q)*Real.sqrt (r i) by ring]
      exact radial_bessel_coefficient_identity (r i) (4*Real.pi*q) (hr i)
        (by positivity) (a i) _ s

end CubicEisenstein

end

end OAI

end

