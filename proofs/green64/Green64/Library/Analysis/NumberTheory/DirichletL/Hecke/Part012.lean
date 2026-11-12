module

public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.PrimeDyadic
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealLogDerivative.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part007
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Green64.Library.Analysis.PrimeNumberTheorem.Part002
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.IdealOperations
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Hecke / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicEuler -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def eulerBound (b : ℝ) : ℝ :=
  ∑' I : NonzeroIdeal, IdealMangoldt.value I.val * (norm I)^(-b)

theorem eulerBound_summable {b : ℝ} (hb : 1<b) :
    Summable (fun I : NonzeroIdeal => IdealMangoldt.value I.val * (norm I)^(-b)) := by
  have ha (I : Ideal O) : ‖IdealEuler.normWeight 0 I‖ ≤ 1 := by
    change ‖CubicEisenstein.fullIdealWeight 0 I‖ ≤ 1
    by_cases hI : I = 0
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_left_iff.mpr (fun h => (h hI).elim), norm_zero]
      norm_num
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_right_iff.mpr (fun h => (hI h).elim)]
      simp
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (IdealEuler.normWeight 0) ha (b : ℂ) (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NonzeroIdeal => I.val))
  convert hf using 1
  ext I
  simp only [Function.comp_apply, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight,
    ite_eq_right_iff.mpr (fun h => (I.property h).elim), neg_zero, Complex.cpow_zero, one_mul]
  change IdealMangoldt.value I.val * (norm I)^(-b) =
    ‖(IdealMangoldt.value I.val : ℂ) * (norm I : ℂ)^(-(b : ℂ))‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp

theorem series_norm_le (χ : Character) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤ s.re) : ‖series χ s‖ ≤ eulerBound b := by
  rw [series_eq_tsum χ (hb.trans_le hs)]
  have hbound (I : NonzeroIdeal) :
      ‖coefficient χ I.val * (norm I : ℂ)^(-s)‖ ≤
        IdealMangoldt.value I.val * (norm I)^(-b) := by
    rw [norm_mul]
    have hn : 1 ≤ norm I := by
      unfold HeckeDyadic.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hc : ‖coefficient χ I.val‖ ≤ IdealMangoldt.value I.val := by
      rw [coefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (IdealMangoldt.value_nonneg _)]
      exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg _) (idealCoeff_norm_le_one χ _)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re]
    exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))
      (Real.rpow_nonneg (norm_pos I).le _) (IdealMangoldt.value_nonneg _)

  have hf := (eulerBound_summable hb).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hbound (eulerBound_summable hb))

end SevenEighths.HeckePrimeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicContour -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def integrand (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+HeckeDyadic.shift σ freq-(1/2 : ℂ)) *
    series χ (s+HeckeDyadic.shift σ freq)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    {s : ℂ} (hz : LFunction χ s≠0) : DifferentiableAt ℂ (series χ) s := by
  have h := (LFunction_entire_nonprincipal χ hχ).analyticAt s
  exact (h.deriv.neg.div h hz).differentiableAt

theorem series_differentiableAt_right (χ : Character) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ) s := by
  have ha : AnalyticAt ℂ (LFunction χ) s := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 1)).2 ?_ s hs
    intro z hz
    exact (LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hz) (Or.inl (by intro h; norm_num [h] at hz))).differentiableWithinAt
  exact (ha.deriv.neg.div ha (LFunction_ne_zero_of_one_lt_re χ hs)).differentiableAt

theorem integrand_differentiableAt (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ) (s+HeckeDyadic.shift σ freq)) :
    DifferentiableAt ℂ (integrand χ W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (HeckeDyadic.shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (HeckeDyadic.shift σ freq))

theorem integrand_norm (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ (s+HeckeDyadic.shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*eulerBound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ hc (by simp))
  positivity

theorem finite_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1< r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle χ hχ W a b ha hWs hW D σ freq l r T hD hz]

end SevenEighths.HeckePrimeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicEstimates -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem absolute_tail_bound (χ : Character) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1< r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _)))
  · exact hT
  · intro t
    rw [integrand_norm χ W D σ freq hD]
    have hb := series_norm_le χ hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ W D σ freq hD]
      have hb := CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hm t)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
        sub_self, add_zero]
      calc
        _ ≤ (C/(1+t^2))*D^(l+σ-1/2)*K :=
          mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hD.le _))
            (hs t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem horizontal_join_bound (χ : Character) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hC : 0≤C) (_hK : 0≤K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤C)
    (hs : ∀ x ∈ Icc l r, ‖series χ ((x : ℂ)+y*I+shift σ freq)‖≤K) :
    ‖∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hr : 1< r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ (s+shift σ freq)‖≤K) :
    ‖polynomial χ W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end SevenEighths.HeckePrimeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicBuffered -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Metric MeasureTheory Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeLogarithmic HeckeDeletionBounds

def binCost (B : ℝ) (χ : Character) (H : ℝ) : ℝ :=
  B*Real.log (complexity χ H) + localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ)

theorem binCost_nonneg {B : ℝ} (hB : 0≤B) (χ : Character) (H : ℝ) : 0≤binCost B χ H := by
  have hc : 1≤ complexity χ H :=
    (Real.one_le_exp (by norm_num : (0 : ℝ)≤1)).trans (complexity_ge_exp χ H)
  have hr : (1 : ℝ)≤(radical χ.modulus).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  exact add_nonneg (mul_nonneg hB (Real.log_nonneg hc))
    (mul_nonneg (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le (Real.log_nonneg hr))

theorem polynomial_bound_in_bin (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ→ℂ) (α β : ℝ), 0<α → Function.support W⊆Icc α β →
      ContDiff ℝ ∞ W → ∀ D σ freq L C₂ Cn : ℝ, ∀ n : ℕ,
      1≤D → 0≤L → 0≤C₂ → 0≤Cn → |freq|+L≤(3*i+2 : ℕ)*T →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x∈Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W D σ freq‖ ≤ (1/(2*Real.pi))*
        (C₂*D^(a+8*e-1/2)*binCost B (χ j) ((3*i+2 : ℕ)*T)*Real.pi +
          2*(Cn*D^(3/2 : ℝ)*binCost B (χ j) ((3*i+2 : ℕ)*T)/(1+L)^n)*|2-a-8*e| +
          (Cn*D^(3/2 : ℝ)*eulerBound 2)/(1+L)^n*Real.pi) := by
  obtain ⟨B,hB,hbound⟩ := HeckePrimeDyadicControl.buffered_rectangle_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W α β hα hWs hW D σ freq L C₂ Cn n
    hD hL hC₂ hCn hfreq hm₂ hmn
  have hlr : a+8*e-σ≤2-σ := by linarith
  have hmem (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :
      a+8*e≤(s+HeckeDyadic.shift σ freq).re ∧ (s+HeckeDyadic.shift σ freq).re≤2 ∧
        |(s+HeckeDyadic.shift σ freq).im|≤(3*i+2 : ℕ)*T := by
    convert HeckeDyadic.translated_rectangle_mem (a := a+2*e) (e := e)
      (by linarith) (by linarith) hlr hL hfreq hs using 1 ; ring_nf
  have hs (s : ℂ) (hs : s ∈ (uIcc (a+8*e-σ) (2-σ) ×ℂ uIcc (-L) L)) :=
    hbound χ hχ T a i hT ha ha' hmax j (s+HeckeDyadic.shift σ freq)
      (hmem s hs).1 (hmem s hs).2.1 (hmem s hs).2.2
  have hh := polynomial_bound_of_rectangle (χ j) (hχ j) W α β hα hWs hW
    D σ freq (a+8*e-σ) (2-σ) L C₂ Cn (binCost B (χ j) ((3*i+2 : ℕ)*T)) n
    hD hlr (by linarith) hL hC₂ hCn (binCost_nonneg hB _ _)
    hm₂ hmn (fun s h => (hs s h).1) (fun s h => by
      simpa only [series, neg_div, norm_neg, logDeriv_apply, binCost] using (hs s h).2)
  convert hh using 1 ; congr 1 ; ring_nf

end SevenEighths.HeckePrimeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicScale -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds HeckeLogarithmic

theorem binCost_le_log (χ : Character) (B U H η : ℝ)
    (hB : 0≤B) (hU : 2≤U) (hQ : (χ.modulus.absNorm : ℝ)≤U)
    (hheight : (3+|H|)^2≤U^η) :
    binCost B χ H ≤ (B*(2+η)+localBound (1/2))*Real.log U := by
  have hUp : 0<U := by linarith
  have hcp : 0<complexity χ H := (Real.exp_pos 1).trans_le (complexity_ge_exp χ H)
  have hcomplex : complexity χ H ≤ 2*U^(1+η) := by
    unfold complexity
    calc
      2*(χ.modulus.absNorm : ℝ)*(3+|H|)^2 ≤ 2*U*U^η := by gcongr
      _ = _ := by rw [Real.rpow_add hUp, Real.rpow_one]; ring
  have hlog : Real.log (complexity χ H) ≤ (2+η)*Real.log U := by
    apply (Real.log_le_log hcp hcomplex).trans
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hUp _).ne', Real.log_rpow hUp]
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ)<2) hU
    nlinarith
  have hrad : 0<((radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero χ.modulus))
  have hrlog := Real.log_le_log hrad ((radical_norm_le_modulus χ).trans hQ)
  unfold binCost
  calc
    _ ≤ B*((2+η)*Real.log U)+localBound (1/2)*Real.log U :=
      add_le_add (mul_le_mul_of_nonneg_left hlog hB)
        (mul_le_mul_of_nonneg_left hrlog (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le)
    _ = _ := by ring

theorem binCost_le_power (χ : Character) (B U H η ε : ℝ)
    (hB : 0≤B) (hU : 2≤U) (hQ : (χ.modulus.absNorm : ℝ)≤U)
    (hη : 0≤η) (hε : 0<ε) (hheight : (3+|H|)^2≤U^η) :
    binCost B χ H ≤ ((B*(2+η)+localBound (1/2))/ε)*U^ε := by
  apply (binCost_le_log χ B U H η hB hU hQ hheight).trans
  have hc : 0≤B*(2+η)+localBound (1/2) := by
    exact add_nonneg (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2)).le
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_rpow_div (by linarith : 0≤U) hε) hc
  convert hh using 1 ; ring

end SevenEighths.HeckePrimeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicScaled -/

section

namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic HeckeDeletionBounds

theorem scaled_direct_bound (e κ η : ℝ) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0<A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R σ freq V C₂ Cn : ℝ) (n : ℕ),
      2≤U → (χ j).modulus.absNorm≤U → 0≤ r → r≤R → 0≤V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^2≤U^η → 0≤C₂ → 0≤Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+8*e-σ : ℝ) : ℂ)+t*I)‖≤C₂) →
      (∀ x ∈ Icc (a+8*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn) →
      ‖polynomial (χ j) W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+8*e)*r+κ)+C*Cn*U^(2*R+κ)/(1+V)^n := by
  obtain ⟨B,hB,hbound⟩ := polynomial_bound_in_bin e he he'
  let Cb := (B*(2+η)+localBound (1/2))/κ
  have hCb : 0<Cb := div_pos
    (add_pos_of_nonneg_of_pos (mul_nonneg hB (by linarith))
      (localBound_pos (by norm_num : (0 : ℝ)<1/2))) hκ
  let E := eulerBound 2
  have hE : 0≤E := tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  let C := 1+Cb*Real.pi+4*Cb+E*Real.pi
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    U r R σ freq V C₂ Cn n hU2 hQ hr hrR hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤H := by dsimp [H]; positivity
  have hU : 1≤U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B' hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hC₂ hCn hfreq hm₂ hmn
  have hcost : binCost B (χ j) H ≤ Cb*U^κ :=
    binCost_le_power (χ j) B U H η κ hB hU2 hQ hη hκ (by rw [abs_of_nonneg hH]; exact hheight)
  have hcentral : (U^r)^(a+8*e-1/2)*binCost B (χ j) H ≤
      Cb*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ ≤ (U^r)^(a+8*e-1/2)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = _ := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]; congr 2; ring
  have hexternal : (U^r)^(3/2 : ℝ)*binCost B (χ j) H ≤ Cb*U^(2*R+κ) := by
    calc
      _ ≤ (U^r)^(3/2 : ℝ)*(Cb*U^κ) :=
        mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _)
      _ = Cb*U^(r*(3/2)+κ) := by rw [←Real.rpow_mul hUp.le, mul_left_comm, ←Real.rpow_add hUp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)) hCb.le
  have hpow : (U^r)^(3/2 : ℝ)≤U^(2*R+κ) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-8*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+8*e-1/2)*binCost B (χ j) H*Real.pi≤
      (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ) := by
    calc
      _ = (C₂*Real.pi)*((U^r)^(a+8*e-1/2)*binCost B (χ j) H) := by ring
      _ ≤ (C₂*Real.pi)*(Cb*U^((a-1/2+8*e)*r+κ)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*binCost B (χ j) H/(1+V)^n)*|2-a-8*e|≤
      (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ = 2*Cn*((U^r)^(3/2 : ℝ)*binCost B (χ j) H)/(1+V)^n*|2-a-8*e| := by ring
      _ ≤ 2*Cn*(Cb*U^(2*R+κ))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+κ)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤binCost B (χ j) H := binCost_nonneg hB _ _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : Cb*Real.pi≤C := by dsimp [C]; nlinarith only [hCb, mul_nonneg hE Real.pi_pos.le]
  have heC : 4*Cb+E*Real.pi≤C := by dsimp [C]; nlinarith only [mul_nonneg hCb.le Real.pi_pos.le]
  calc
    _ ≤ (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb)*Cn*U^(2*R+κ)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (Cb*Real.pi)*C₂*U^((a-1/2+8*e)*r+κ)+
        (4*Cb+E*Real.pi)*Cn*U^(2*R+κ)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end SevenEighths.HeckePrimeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicSource -/

section

namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem source_log_profile_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq L : ℝ,
      0≤ r → r≤R → σmin≤σ → σ≤σmax → L∈Icc (0 : ℝ) 1 →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖polynomial (χ k) (PrimeLogProfile.profile W L) ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ η he he' hκ hη
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+κ) 0
    hτ hdmax (by positivity) (by norm_num)
  obtain ⟨C₂,hC₂,hm₂⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) 2
  obtain ⟨Cn,hCn,hmn⟩ := PrimeLogProfile.uniform_mellin_decay W A B hA hWs hW
    (-σmax) (2-σmin) (n+2)
  refine ⟨Cd*C₂+Cd*Cn*(2 : ℝ)^n,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq L
    hr hrR hσmin hσmax hL k hQ hfreq hheight
  let U := Z^d
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hs : Icc (a+8*e-σ) (2-σ)⊆Icc (-σmax) (2-σmin) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hleft : a+8*e-σ∈Icc (-σmax) (2-σmin) := by
    constructor <;> linarith
  have hb := hdirect χ hχ (Z^τ) a i hT ha ha' hmax k
    (PrimeLogProfile.profile W L) A B hA
    ((PrimeLogProfile.profile_support W L).trans hWs)
    (PrimeLogProfile.profile_smooth W A B hA hWs hW L)
    U r R σ freq (Z^τ/2) C₂ Cn n hU2 hQ hr hrR (by positivity)
    hfreq hheight hC₂.le hCn.le (hm₂ L hL _ hleft) (fun x hx => hmn L hL x (hs hx))
  have htail' := htail Z d 0 hZ hd hd' (by norm_num)
  simp only [Real.rpow_zero,mul_one] at htail'
  have hexp : (a-1/2+8*e)*r+κ≤(a-1/2)*r+ε := by
    nlinarith [mul_le_mul_of_nonneg_left hrR (by positivity : 0≤8*e)]
  have hp : 0≤(a-1/2)*r+ε := by
    have : 0≤8*e*R := by positivity
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr]
  calc
    _ ≤ Cd*C₂*U^((a-1/2)*r+ε)+Cd*Cn*(2 : ℝ)^n := by
      apply hb.trans
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hexp) (by positivity)
      · calc
          _ = (Cd*Cn)*(U^(2*R+κ)/(1+Z^τ/2)^n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ (Cd*C₂+Cd*Cn*(2 : ℝ)^n)*U^((a-1/2)*r+ε) := by
      rw [add_mul]
      apply add_le_add (le_refl _)
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hU hp)

end SevenEighths.HeckePrimeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.RayFamily -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayFamily
open HeckeFamily

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def character (χ : RayOrthogonality.rayCharacters M) : Character :=
  Character.ofResidue M (NeZero.ne M) χ.val ((RayOrthogonality.mem_rayCharacters_iff M χ.val).mp χ.property)

theorem idealCoeff_character (χ : RayOrthogonality.rayCharacters M) (I : Ideal O) :
    idealCoeff (character M χ) I = RayOrthogonality.idealCharacter M χ I := rfl

theorem principal_iff (χ : RayOrthogonality.rayCharacters M) :
    (character M χ).residue = 1 ↔ χ = 1 := by
  change χ.val = 1 ↔ χ = 1
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem character_entire (χ : RayOrthogonality.rayCharacters M) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M χ).mp h))

theorem character_boundary_ne_zero (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ rfl

theorem average_idealCoeff (I : Ideal O) :
    (RayOrthogonality.rayCard M : ℂ)⁻¹ *
      ∑ χ : RayOrthogonality.rayCharacters M, idealCoeff (character M χ) I =
      if I ∈ RayOrthogonality.principalIdeals M then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayOrthogonality.average_idealCharacters M I

theorem mangoldt_LSeries (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (IdealLogDerivative.coeff (RayOrthogonality.idealCharacter M χ)) s =
      (if χ = 1 then (1 : ℂ)/(s-1) else 0) +
        HeckeLogDerivative.poleSubtracted (character M χ) s := by
  have h := HeckeLogDerivative.coeff_LSeries_eq_poleSubtracted (character M χ) hs
  change LSeries (IdealLogDerivative.coeff (idealCoeff (character M χ))) s = _ at h
  have heq : idealCoeff (character M χ) = RayOrthogonality.idealCharacter M χ := rfl
  rw [heq, principal_iff] at h
  by_cases hc : χ = 1 <;> simpa [hc] using h

theorem poleSubtracted_analyticAt (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (HeckeLogDerivative.poleSubtracted (character M χ)) s :=
  HeckeLogDerivative.poleSubtracted_analyticAt _ hs

end SevenEighths.HeckeRayFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.FixedEuler -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma fixedPrimeProduct_ne_zero (S : Finset Id) (hS : ∀P∈S,Prime P) :
    (∏P∈S,P)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)

def fixedSourcePrincipal (S : Finset Id) (hS : ∀P∈S,Prime P) : Character :=
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  HeckeRayFamily.character (∏P∈S,P) 1

lemma prime_coprime_fixedProduct (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    IsCoprime P.val (∏Q∈S,Q) ↔ P.val∉S := by
  rw [IsCoprime.prod_right_iff]
  constructor
  · intro h hP
    exact P.property.not_isUnit (isCoprime_self.mp (h P.val hP))
  · intro h Q hQ
    exact primeIdeal_coprime P ⟨Q,hS Q hQ⟩ (fun he=>h ((congrArg Subtype.val he).symm ▸ hQ))

lemma fixedSourcePrincipal_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (fixedSourcePrincipal S hS) P.val=if P.val∈S then 0 else 1 := by
  unfold fixedSourcePrincipal
  rw [HeckeRayFamily.idealCoeff_character,RayOrthogonality.idealCharacter_one]
  change (if P.val=0 then (0:ℂ) else if IsCoprime P.val (∏Q∈S,Q) then 1 else 0)=_
  simp only [P.property.ne_zero,ite_false,prime_coprime_fixedProduct S hS P]
  split_ifs <;> simp_all

lemma excludedTarget_prime (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (η.excludePrimes S hS) P.val=if P.val∈S then 0 else idealCoeff η P.val := by
  rw [idealCoeff_excludePrimes]
  have he : (∀Q∈S,IsCoprime P.val Q) ↔ P.val∉S := by
    rw [←IsCoprime.prod_right_iff]
    exact prime_coprime_fixedProduct S hS P
  simp only [he]
  split_ifs <;> simp_all

theorem LFunction_hasProd_outside (χ : Character) (S : Finset Id) (a : Id→ℂ)
    (ha : ∀P : PrimeIdeal,idealCoeff χ P.val=if P.val∈S then 0 else a P.val)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-a P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction χ s) := by
  have h := IdealEuler.euler_hasProd (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs
  rw [←LFunction_eq_series χ hs] at h
  have he (P : PrimeIdeal) : (1-IdealEuler.weighted (idealCoeff χ) s P.val)⁻¹=
      if P.val∈S then 1 else (1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹ := by
    change (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹=_
    rw [ha]
    split_ifs <;> simp only [zero_mul,sub_zero,inv_one]
  simp only [he] at h
  apply (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal|P.val∉S})
    (f:=fun P : PrimeIdeal=>(1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem fixedSourcePrincipal_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction (fixedSourcePrincipal S hS) s) := by
  simpa only [one_mul] using
    LFunction_hasProd_outside (fixedSourcePrincipal S hS) S (fun _=>1) (fixedSourcePrincipal_prime S hS) s hs

theorem excludedTarget_hasProd (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (η.excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (idealCoeff η) (excludedTarget_prime η S hS) s hs

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.HighLFactorization -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem principalHigh_L_factorization (S : Finset Id) (hS : ∀P∈S,Prime P)
    (hgood : ∀P : PrimeIdeal,P.val∉S → Supported P.val) (htail : CorrectionTail S)
    (η : Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hH := globalClosedCorrection_multipliable η S htail x w z (by linarith) (by linarith) (by linarith)
  have he := (((fixedSourcePrincipal_hasProd S hS (6*z) hz1).mul
    (fixedSourcePrincipal_hasProd S hS w hw1)).mul
      ((excludedTarget_hasProd η S hS x hx1).inv₀
        (LFunction_ne_zero_of_one_lt_re (η.excludePrimes S hS) hx1))).mul hH.hasProd
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ((1-CubicEisenstein.fullIdealWeight (6*z) P.val.val)⁻¹ *
       (1-CubicEisenstein.fullIdealWeight w P.val.val)⁻¹ *
       ((1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight x P.val.val)⁻¹)⁻¹) *
       idealClosedCorrection η P.val x w z = idealHighLocalFactor η P.val.val x w z := by
    rw [idealHighLocalFactor_rational η P.val (hgood P.val P.property) x w z hx hw hz]
    simp only [CubicEisenstein.fullIdealWeight,P.val.property.ne_zero,ite_false,
      Complex.ofReal_natCast,div_eq_mul_inv,mul_inv_rev,inv_inv]
    rw [show -(6*z)=(-6:ℂ)*z by ring]
    ring
  have he' : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z) := by
    simpa only [hlocal,div_eq_mul_inv,globalClosedCorrection] using he
  exact (excludedIdealHighSeries_hasProd_outside S hS η x w z hx hw hz).unique he'

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SourceExclusions -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_prime_supported (S : Finset Id) (hbad : fixedBadPrimes⊆S)
    (P : PrimeIdeal) (hP : P.val∉S) : Supported P.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  refine ⟨P.property.ne_zero,?_⟩
  intro Q hQ
  have heq : Q=P.val := by
    simpa only [normalizedFactors_irreducible P.property.irreducible,normalize_eq,
      Multiset.mem_singleton] using hQ
  subst Q
  exact (prime_good_iff_not_bad P.val).mpr (fun h=>hP (hbad h))

structure SourceExclusions (S : Finset Id) : Prop where
  prime : ∀P∈S,Prime P
  bad : fixedBadPrimes⊆S
  tail : CorrectionTail S

theorem exists_source_exclusions (S₀ : Finset Id) (hp : ∀P∈S₀,Prime P)
    (hbad : fixedBadPrimes⊆S₀) :
    ∃S : Finset Id,S₀⊆S ∧ SourceExclusions S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,?_⟩
  constructor
  · intro P hP
    rcases Finset.mem_union.mp hP with hP|hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  · exact hbad.trans Finset.subset_union_left
  · apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

theorem source_principalHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z :=
  principalHigh_L_factorization S hS.prime (outside_prime_supported S hS.bad) hS.tail η x w z hx hw hz

theorem source_globalCorrection_principal (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x : ℂ) :
    globalClosedCorrection η S x 1 (1/6)=principalCorrection η S x :=
  globalClosedCorrection_principal η S (outside_prime_supported S hS.bad) x

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.MarkedProduct -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler ProbeEulerFinsupp
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma source_idealHighLocalFactor_ne_zero (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    idealHighLocalFactor η P.val x w z≠0 := by
  rw [idealHighLocalFactor_rational η P (outside_prime_supported S hS.bad P hP) x w z hx hw hz]
  have hQ : (1:ℝ)<Ideal.absNorm P.val := by
    have hh := hS.tail.norm_four P hP
    exact_mod_cast (by omega : 1<Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)<Ideal.absNorm P.val := by linarith
  have hD : ‖HeckeFamily.idealCoeff η P.val*(Ideal.absNorm P.val:ℂ)^(-x)‖<1 := by
    rw [norm_mul,Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    apply (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (HeckeFamily.idealCoeff_norm_le_one η P.val)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  have hV : ‖(Ideal.absNorm P.val:ℂ)^(-6*z)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hQ
    norm_num [Complex.mul_re]
    linarith
  have hW : ‖(Ideal.absNorm P.val:ℂ)^(-w)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hQ0),Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  apply mul_ne_zero
  · exact div_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hD)
      (mul_ne_zero (one_sub_ne_zero_of_norm_lt_one _ hV) (one_sub_ne_zero_of_norm_lt_one _ hW))
  · exact factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))

theorem markedIdealHighSeries_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  let R := fun P : PrimeIdeal=>if P∈T then
    idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z else 1
  have hR : HasProd R (∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T) (f:=R) (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [R,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := (excludedIdealHighSeries_hasProd S hS.prime η x w z hx hw hz).mul hR
  have heq (P : PrimeIdeal) :
      (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)*R P=
      ∑'b : HighValuation,markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b := by
    by_cases hp : P∈T
    · rw [selectedLocal_outside S hS.prime T η P (hT P hp) x w z hx hw hz,ite_eq_left hp]
      have hu : (∑'b : HighValuation,excludedHighPrimeTerm S η x w z P b)=idealHighLocalFactor η P.val x w z := by
        simpa only [excludedHighPrimeTerm,excludedHighArray,ite_eq_right (hT P hp)] using
          excludedHighLocalFactor S hS.prime η x w z hx hw hz P
      rw [hu,show R P=idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z from ite_eq_left hp]
      exact mul_div_cancel₀ _ (source_idealHighLocalFactor_ne_zero S hS η P (hT P hp) x w z hx hw hz)
    · simp only [R,hp,ite_false,mul_one,markedLocal,one_mul]
  have he' : HasProd (fun P : PrimeIdeal=>∑'b : HighValuation,
      markedLocal T completedValuationMark (excludedHighPrimeTerm S η x w z) P b)
      (markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z) := by
    convert he using 1
    funext P
    exact (heq P).symm
  exact (markedIdealHighSeries_hasProd S hS.prime T η x w z hx hw hz).unique he'

theorem source_markedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T,P.val) η 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z := by
  rw [markedIdealHighSeries_eq_product S hS T hT η x w z hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.SpectralCompensation -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def spectralCompensatedHigh (S : Finset Id) (T : Finset PrimeIdeal)
    (η : HeckeFamily.Character) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η 1 x w z

theorem spectralCompensatedHigh_eq_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      markedIdealHighSeries S 1 η 1 x w z *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedIdealHighSeries_eq_product S hS (T\J)
    (fun P hP=>hT P (Finset.mem_sdiff.mp hP).1) η x w z hx hw hz]
  simp only [mul_div_assoc,Finset.prod_mul_distrib]
  ring

theorem spectralCompensatedHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(B P*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q P) := by
  rw [spectralCompensatedHigh_eq_product S hS T hT η x w z B q hx hw hz,
    source_principalHigh_L_factorization S hS η x w z hx hw hz]

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CompensationActual -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma initialPrime_denominators (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ)
    (hx : 0<x.re) (hw : 0<w.re) (hz : 0<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    (1-coordV Q z≠0) ∧ (1-coordW Q 1 w≠0) ∧
      (1-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x≠0) := by
  dsimp only
  have hQ : (1:ℝ)<Ideal.absNorm P.val := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1<Ideal.absNorm P.val)
  have hQ0 : (0:ℝ)<Ideal.absNorm P.val := by linarith
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  constructor
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply one_sub_ne_zero_of_norm_lt_one
    apply (coordD_norm_le _ hQ0 _ 1 x (HeckeFamily.idealCoeff_norm_le_one η P.val) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

lemma idealClosedCorrection_eq_continued (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) :
    let Q : ℝ := Ideal.absNorm P.val
    idealClosedCorrection η P x w z=continuedCorrection (coordV Q z) (coordW Q 1 w)
      (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) := rfl

lemma standardFactor_times_continued (V W D M : ℂ)
    (hV : 1-V≠0) (hW : 1-W≠0) (hD : 1-D≠0) :
    (1-D)/((1-V)*(1-W))*continuedCorrection V W D M=localFactor V W M := by
  unfold continuedCorrection localFactor
  field_simp
  ring

lemma idealHighLocalFactor_eq_raw (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : CanonicalQuadraticSieve.Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z=
      localFactor (coordV Q z) (coordW Q 1 w) (idealMarkedClosed η P x w z) := by
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have he := idealHighLocalFactor_rational η P hs x w z hx hw hz
  have hc := standardFactor_times_continued (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) hd.1 hd.2.1 hd.2.2
  rw [←idealClosedCorrection_eq_continued] at hc
  dsimp only at he hc ⊢
  rw [he]
  simpa only [coordV,coordW,coordD,star_one,mul_one,one_mul] using hc

theorem idealCompensatedRatio_eq_continued (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (P : PrimeIdeal) (hP : P.val∉S) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    B*idealMarkedLocalFactor η P x w z/idealHighLocalFactor η P.val x w z-q=
      compensatedReplacement (coordV Q z) (coordW Q 1 w)
        (coordD Q (HeckeFamily.idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z) B q /
          idealClosedCorrection η P x w z := by
  have hs := outside_prime_supported S hS.bad P hP
  have hd := initialPrime_denominators η P x w z (by linarith) (by linarith) (by linarith)
  have hraw := idealHighLocalFactor_eq_raw η P hs x w z hx hw hz
  have hn := source_idealHighLocalFactor_ne_zero S hS η P hP x w z hx hw hz
  rw [hraw] at hn
  have hH : idealClosedCorrection η P x w z≠0 :=
    factor_ne_zero_of_defect _ ((idealClosedCorrection_bound η P (hS.tail.norm_four P hP)
      x w z (by linarith) (by linarith) (by linarith)).trans (hS.tail.half ⟨P,hP⟩))
  have he := compensatedReplacement_eq_raw (coordV (Ideal.absNorm P.val) z)
    (coordW (Ideal.absNorm P.val) 1 w) (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
    (idealMarkedClosed η P x w z) B q hd.1 hd.2.1 hd.2.2 hn
  rw [←continuedCorrection_eq_raw _ _ _ _ hd.1 hd.2.1 hd.2.2,
    ←idealClosedCorrection_eq_continued] at he
  dsimp only at hraw he ⊢
  rw [idealMarkedLocalFactor_rational η P hs x w z hx hz,hraw,he]
  exact (mul_div_cancel_left₀ _ hH).symm

theorem spectralCompensatedHigh_continued (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : HeckeFamily.Character)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedHigh S T η x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
       HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
       HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z) *
        ∏P∈T,(compensatedReplacement (coordV (Ideal.absNorm P.val) z)
          (coordW (Ideal.absNorm P.val) 1 w)
          (coordD (Ideal.absNorm P.val) (HeckeFamily.idealCoeff η P.val) 1 x)
          (idealMarkedClosed η P x w z) (B P) (q P) / idealClosedCorrection η P x w z) := by
  rw [spectralCompensatedHigh_L_factorization S hS T hT η x w z B q hx hw hz]
  congr 1
  apply Finset.prod_congr rfl
  intro P hP
  exact idealCompensatedRatio_eq_continued S hS η P (hT P hP) x w z (B P) (q P) hx hw hz

end SevenEighths.ProbePhysical
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrincipalResidue -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrincipalResidue
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem coefficients_sum_positive (χ : Character) (hχ : χ.residue=1) :
    ∃ c : ℝ, 0<c ∧ (∑ a, coefficients χ a)=(c : ℂ) := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  have heq : (∑ a, coefficients χ a) =
      (Nat.card (coordinateQuotientHom χ).ker : ℂ) *
        (Fintype.card (O ⧸ χ.modulus)ˣ : ℂ) := by
    calc
      _ = ∑ a, χ.residue (coordinateQuotientHom χ (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact coefficients_eq_quotient_character χ a
      _ = ∑ a : ZMod χ.period × ZMod χ.period,
          χ.residue (coordinateQuotientHom χ a) :=
        e.bijective.sum_comp (fun a => χ.residue (coordinateQuotientHom χ a))
      _ = _ := by
        rw [sum_comp_additiveHom _ (coordinateQuotientHom_surjective χ), hχ,
          MulChar.sum_one_eq_card_units]
  refine ⟨(Nat.card (coordinateQuotientHom χ).ker : ℝ) * Fintype.card (O ⧸ χ.modulus)ˣ, ?_, ?_⟩
  · exact mul_pos (Nat.cast_pos.mpr (Nat.card_pos (α := (coordinateQuotientHom χ).ker)))
      (Nat.cast_pos.mpr (Fintype.card_pos (α := (O ⧸ χ.modulus)ˣ)))
  · simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using heq

theorem principal_residue_positive (χ : Character) (hχ : χ.residue=1) :
    ∃ R : ℝ, 0<R ∧ HeckeOrigin.poleRemoved χ 1=(R : ℂ) := by
  obtain ⟨c,hc,he⟩ := coefficients_sum_positive χ hχ
  have hN : (0 : ℝ)<χ.period := Nat.cast_pos.mpr (NeZero.pos χ.period)
  let d : ℝ := (((χ.period : ℝ)^2)^(-(1/2 : ℝ))) *
    ((3*(χ.period : ℝ)^2)^(-(1/2 : ℝ)))
  have hd : 0<d := mul_pos (Real.rpow_pos_of_pos (sq_pos_of_pos hN) _)
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hN)) _)
  refine ⟨Real.pi*(2*d*c)/6, by positivity, ?_⟩
  rw [HeckeOrigin.poleRemoved_one, HeckeReciprocal.regularizedL_at_one,
    HeckeTheta.pair_g₀, he]
  simp only [HeckeTheta.dualScalar, d, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]

theorem fixed_principal_residue_positive (M : Ideal O) [NeZero M] :
    ∃ R : ℝ, 0<R ∧ HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1) 1=(R : ℂ) :=
  principal_residue_positive _ rfl

end SevenEighths.HeckePrincipalResidue

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.RayQuotient -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayQuotient
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def character (χ : RayQuotient.Characters M H) : Character :=
  HeckeRayFamily.character M (RayQuotient.toFullRay M H hH χ)

theorem idealCoeff_character (χ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (character M H hH χ) I = RayQuotient.idealCharacter M H hH χ I := rfl

theorem principal_iff (χ : RayQuotient.Characters M H) :
    (character M H hH χ).residue = 1 ↔ χ = 1 := by
  rw [character, HeckeRayFamily.principal_iff, RayQuotient.toFullRay_eq_one]

theorem character_entire (χ : RayQuotient.Characters M H) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M H hH χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M H hH χ).mp h))

theorem character_boundary_ne_zero (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M H hH χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M H hH χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M H hH 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ ((principal_iff M H hH 1).mpr rfl)

theorem average_idealCoeff (I : Ideal O) :
    (RayQuotient.classNumber M H : ℂ)⁻¹ *
      ∑ χ : RayQuotient.Characters M H, idealCoeff (character M H hH χ) I =
      if I ∈ RayQuotient.identityClass M H then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayQuotient.average_idealCharacters M H hH I

theorem mangoldt_LSeries (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s =
      (if χ = 1 then (1 : ℂ)/(s-1) else 0) +
        HeckeLogDerivative.poleSubtracted (character M H hH χ) s := by
  have h := HeckeLogDerivative.coeff_LSeries_eq_poleSubtracted (character M H hH χ) hs
  change LSeries (IdealLogDerivative.coeff (idealCoeff (character M H hH χ))) s = _ at h
  have heq : idealCoeff (character M H hH χ) = RayQuotient.idealCharacter M H hH χ := rfl
  rw [heq, principal_iff] at h
  by_cases hc : χ = 1 <;> simpa [hc] using h

theorem poleSubtracted_analyticAt (χ : RayQuotient.Characters M H)
    {s : ℂ} (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (HeckeLogDerivative.poleSubtracted (character M H hH χ)) s :=
  HeckeLogDerivative.poleSubtracted_analyticAt _ hs

end SevenEighths.HeckeRayQuotient

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeCounting.Progressions -/

section

namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction LSeries
open scoped Topology

theorem residueClass_chebyshev {q : ℕ} (a : ZMod q) :
    ∃ C : ℝ, ∀ N : ℕ,
      cumsum (fun n : ℕ => ‖(vonMangoldt.residueClass a n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨C, fun N => le_trans ?_ (hC N)⟩
  unfold cumsum
  apply Finset.sum_le_sum
  intro n hn
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt.residueClass_nonneg a n),
    abs_of_nonneg vonMangoldt_nonneg] using vonMangoldt.residueClass_le a n

theorem residueClass_summable {q : ℕ} (a : ZMod q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (vonMangoldt.residueClass a n : ℂ)) σ) := by
  have hs : LSeriesSummable (fun n => (vonMangoldt.residueClass a n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      lt_of_le_of_lt (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a) (by
        exact_mod_cast hσ)
  simpa only [← nterm_eq_norm_term] using hs.norm

theorem residueClass_ratio_tendsto {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ => cumsum (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (vonMangoldt.residueClass_nonneg a)
    (fun σ hσ => residueClass_summable a hσ)
    (residueClass_chebyshev a)
    (vonMangoldt.continuousOn_LFunctionResidueClassAux a)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
    vonMangoldt.eqOn_LFunctionResidueClassAux ha

end SevenEighths.PNT

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeCounting.PrimeMass -/

section

namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction
open scoped Topology BigOperators

theorem cumsum_div_tendsto_zero_of_summable_div {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hsum : Summable (fun n => f n / n)) :
    Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 0) := by
  let F : ℕ → ℕ → ℝ := fun N n => if n < N then f n / N else 0
  have hlim (n : ℕ) : Tendsto (fun N => F N n) atTop (𝓝 0) := by
    apply (tendsto_const_div_atTop_nhds_zero_nat (f n)).congr'
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [F, hN]
  have hbound : ∀ N n, ‖F N n‖ ≤ f n / n := by
    intro N n
    by_cases hn : n = 0
    · subst n
      simp [F, hzero]
    by_cases hN : n < N
    · simp only [F, ite_eq_left hN, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hf n) (Nat.cast_nonneg N))]
      exact div_le_div_of_nonneg_left (hf n)
        (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn)
        (show (n : ℝ) ≤ N by exact_mod_cast hN.le)
    · simp only [F, ite_eq_right hN, norm_zero]
      exact div_nonneg (hf n) (by positivity)
  have h := tendsto_tsum_of_dominated_convergence hsum hlim
    (Filter.Eventually.of_forall hbound)
  have heq (N : ℕ) : (∑' n, F N n) = cumsum f N / N := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      simp only [Finset.mem_range] at hn
      simp [F, hn])]
    rw [cumsum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    simp [F, Finset.mem_range.mp hn]
  simpa only [heq, tsum_zero] using h

theorem retained_ratio_tendsto {f : ℕ → ℝ} {A : ℝ} (keep : ℕ → Prop)
    [DecidablePred keep] (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (hremainder : Summable (fun n => (if keep n then 0 else f n) / n)) :
    Tendsto (fun N : ℕ => cumsum (fun n => if keep n then f n else 0) N / N)
      atTop (𝓝 A) := by
  have hrem := cumsum_div_tendsto_zero_of_summable_div
    (f := fun n => if keep n then 0 else f n)
    (fun n => by split_ifs <;> first | exact le_rfl | exact hf n)
    (by simp [hzero]) hremainder
  have h := hmass.sub hrem
  have heq (N : ℕ) :
      cumsum f N / N - cumsum (fun n => if keep n then 0 else f n) N / N =
      cumsum (fun n => if keep n then f n else 0) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp
  simpa only [heq, sub_zero] using h

theorem prime_residueClass_ratio_tendsto {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ =>
      cumsum (fun n => if n.Prime then vonMangoldt.residueClass a n else 0) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) :=
  retained_ratio_tendsto Nat.Prime (vonMangoldt.residueClass_nonneg a)
    (vonMangoldt.residueClass_apply_zero a) (residueClass_ratio_tendsto a ha)
    (vonMangoldt.summable_residueClass_non_primes_div a)

end SevenEighths.PNT

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeCounting.IdealPrimeMass -/

section

namespace OAI

namespace SevenEighths.PNT.IdealPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter
open SevenEighths.IdealMangoldt
open scoped BigOperators Classical Topology

noncomputable section

def primeClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ Prime I} n

def higherClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ ¬Prime I} n

theorem value_prime {P : Ideal O} (hP : Prime P) : value P = Real.log (Ideal.absNorm P) := by
  simpa only [pow_one] using value_pow hP (k := 1) (by decide)

theorem prime_of_isPrimePow_of_norm_prime {I : Ideal O}
    (hI : IsPrimePow I) (hn : (Ideal.absNorm I).Prime) : Prime I := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  rw [map_pow] at hn
  rw [hn.eq_one_of_pow, pow_one]
  exact hP

theorem value_eq_zero_of_nonprime_of_norm_prime {I : Ideal O}
    (hI : ¬Prime I) (hn : (Ideal.absNorm I).Prime) : value I = 0 := by
  apply ite_eq_right
  exact fun hpow => hI (prime_of_isPrimePow_of_norm_prime hpow hn)

theorem primeClassCoeff_eq_sum_log (C : Set (Ideal O)) (n : ℕ) :
    primeClassCoeff C n =
      ∑ P ∈ (normFiber n).filter (fun P => P ∈ C ∧ Prime P), Real.log (Ideal.absNorm P) := by
  unfold primeClassCoeff classCoeff coeff
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : I ∈ C ∧ Prime I
  · simp [h, value_prime h.2]
  · simp only [Set.mem_ofPred_eq, h, ite_false, zero_mul]

theorem primeClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ primeClassCoeff C n :=
  classCoeff_nonneg _ n

theorem higherClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ higherClassCoeff C n :=
  classCoeff_nonneg _ n

theorem classCoeff_eq_prime_add_higher (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n = primeClassCoeff C n + higherClassCoeff C n := by
  unfold primeClassCoeff higherClassCoeff classCoeff coeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hC : I ∈ C <;> by_cases hP : Prime I <;> simp [hC, hP]

@[simp] theorem higherClassCoeff_zero (C : Set (Ideal O)) : higherClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

@[simp] theorem primeClassCoeff_zero (C : Set (Ideal O)) : primeClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

theorem higherClassCoeff_eq_zero_of_prime (C : Set (Ideal O)) {n : ℕ} (hn : n.Prime) :
    higherClassCoeff C n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  simp only [Set.mem_ofPred_eq]
  split_ifs with h
  · rw [value_eq_zero_of_nonprime_of_norm_prime h.2
      (by simpa only [(mem_normFiber n I).mp hI] using hn), mul_zero]
  · exact zero_mul _

theorem higherClassCoeff_le_nonprime_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    higherClassCoeff C n ≤ 2 * (if n.Prime then 0 else vonMangoldt n) := by
  by_cases hn : n.Prime
  · rw [higherClassCoeff_eq_zero_of_prime C hn, ite_eq_left hn, mul_zero]
  · rw [ite_eq_right hn]
    exact classCoeff_le_two_vonMangoldt _ n

theorem summable_nonprime_vonMangoldt_div :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt n) / n) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  simpa only [vonMangoldt.residueClass, Subsingleton.elim (α := ZMod 1) _ 0,
    Set.ofPred_true, Set.indicator_univ] using h

theorem higherClassCoeff_summable_div (C : Set (Ideal O)) :
    Summable (fun n : ℕ => higherClassCoeff C n / n) := by
  apply (summable_nonprime_vonMangoldt_div.mul_left 2).of_nonneg_of_le
  · intro n
    exact div_nonneg (higherClassCoeff_nonneg C n) (Nat.cast_nonneg n)
  · intro n
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (higherClassCoeff_le_nonprime_vonMangoldt C n)
      (Nat.cast_nonneg n)

theorem higherClassCoeff_ratio_tendsto_zero (C : Set (Ideal O)) :
    Tendsto (fun N : ℕ => cumsum (higherClassCoeff C) N / N) atTop (𝓝 0) :=
  cumsum_div_tendsto_zero_of_summable_div (higherClassCoeff_nonneg C)
    (higherClassCoeff_zero C) (higherClassCoeff_summable_div C)

theorem primeClassCoeff_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => cumsum (primeClassCoeff C) N / N) atTop (𝓝 A) := by
  have h' := h.sub (higherClassCoeff_ratio_tendsto_zero C)
  have heq (N : ℕ) :
      cumsum (classCoeff C) N / N - cumsum (higherClassCoeff C) N / N =
        cumsum (primeClassCoeff C) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [classCoeff_eq_prime_add_higher, add_sub_cancel_right]
  simpa only [heq, sub_zero] using h'

def primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset.filter
    (fun P => P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N)

@[simp] theorem mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) (P : Ideal O) :
    P ∈ primeIdealsBelow C N ↔ P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N := by
  simp only [primeIdealsBelow, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.2.2.le, h⟩⟩

theorem zero_not_mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) :
    (0 : Ideal O) ∉ primeIdealsBelow C N := by
  intro h
  exact ((mem_primeIdealsBelow C N 0).mp h).2.1.ne_zero rfl

def primeLogMass (C : Set (Ideal O)) (N : ℕ) : ℝ :=
  ∑ P ∈ primeIdealsBelow C N, Real.log (Ideal.absNorm P)

theorem primeLogMass_eq_cumsum (C : Set (Ideal O)) (N : ℕ) :
    primeLogMass C N = cumsum (primeClassCoeff C) N := by
  have hmap : ∀ P ∈ primeIdealsBelow C N, Ideal.absNorm P ∈ Finset.range N := by
    intro P hP
    exact Finset.mem_range.mpr ((mem_primeIdealsBelow C N P).mp hP).2.2
  rw [primeLogMass, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold cumsum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_primeIdealsBelow, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_range.mp hn⟩, heq⟩
  · intro P hP
    rfl

theorem primeLogMass_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => primeLogMass C N / N) atTop (𝓝 A) := by
  simpa only [primeLogMass_eq_cumsum] using primeClassCoeff_ratio_tendsto C h

end

end SevenEighths.PNT.IdealPrimeMass

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimePowers -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrimePowers
open HeckeFamily UniqueFactorizationMonoid

theorem nonprime_primePow_powerful {I : Ideal O} (hpow : IsPrimePow I) (hprime : ¬Prime I) :
    CompletedGauss.PowerfulIdeal I := by
  obtain ⟨P,k,hP,hk,rfl⟩ := hpow
  have hk2 : 2≤k := by
    by_contra h
    have hk1 : k=1 := by omega
    subst k
    exact hprime (by simpa using hP)
  refine ⟨pow_ne_zero _ hP.ne_zero,?_⟩
  intro Q hQ
  rw [hP.irreducible.normalizedFactors_pow] at hQ ⊢
  have hQP := (Multiset.mem_replicate.mp hQ).2
  subst Q
  simpa using hk2

def logWeight (I : Ideal O) : ℝ := IdealMangoldt.value I / Real.log (Ideal.absNorm I)

theorem logWeight_nonneg (I : Ideal O) : 0≤logWeight I :=
  div_nonneg (IdealMangoldt.value_nonneg _) (Real.log_natCast_nonneg _)

theorem logWeight_le_one (I : Ideal O) : logWeight I≤1 := by
  by_cases hlog : Real.log (Ideal.absNorm I)=0
  · simp [logWeight,hlog]
  · apply (div_le_one (lt_of_le_of_ne (Real.log_natCast_nonneg _) (Ne.symm hlog))).mpr
    exact IdealLogDerivative.value_le_log_norm I

theorem logWeight_prime {P : Ideal O} (hP : Prime P) : logWeight P=1 := by
  have hp2 : (2 : ℝ)≤P.absNorm := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
  have hp : 0<Real.log (P.absNorm : ℝ) := Real.log_pos (by linarith)
  rw [logWeight, PNT.IdealPrimeMass.value_prime hP, div_self hp.ne']

theorem logWeight_eq_zero {I : Ideal O} (hI : ¬IsPrimePow I) : logWeight I=0 := by
  simp only [logWeight, IdealMangoldt.value, ite_eq_right hI, zero_div]

theorem sum_prime_extraction (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
      (∑ I∈S.filter Prime, idealCoeff χ I*f I) =
      ∑ I∈S.filter (fun I => IsPrimePow I ∧ ¬Prime I),
        (logWeight I : ℂ)*idealCoeff χ I*f I := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hP : Prime I
  · simp only [hP, ite_true, not_true_eq_false, and_false, ite_false,
      logWeight_prime hP, Complex.ofReal_one, one_mul, sub_self]
  · by_cases hp : IsPrimePow I
    · simp [hP,hp]
    · simp [hP,hp,logWeight_eq_zero hp]

theorem prime_extraction_error (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ)
      (X B : ℝ), 1≤X → 0≤B →
      (∀ I∈S, (I.absNorm : ℝ)≤X) → (∀ I∈S, ‖f I‖≤B) →
      ‖(∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
        (∑ I∈S.filter Prime, idealCoeff χ I*f I)‖ ≤ C*X^(1/2+ε)*B := by
  obtain ⟨C,hC,hcount⟩ := CompletedGauss.powerful_ideal_count ε hε
  refine ⟨C,hC,?_⟩
  intro χ S f X B hX hB hnorm hf
  rw [sum_prime_extraction]
  let A := S.filter (fun I => IsPrimePow I ∧ ¬Prime I)
  have hA : (A.card : ℝ)≤C*X^(1/2+ε) := by
    apply hcount A X hX
    intro I hI
    obtain ⟨hIS,hpow,hprime⟩ := Finset.mem_filter.mp hI
    exact ⟨nonprime_primePow_powerful hpow hprime,hnorm I hIS⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _I∈A, B := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (logWeight_nonneg _)]
      have hcoeff : logWeight I*‖idealCoeff χ I‖≤1 :=
        (mul_le_of_le_one_right (logWeight_nonneg I) (idealCoeff_norm_le_one χ I)).trans
          (logWeight_le_one I)
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans
        (by simpa using hf I (Finset.mem_filter.mp hI).1)
    _ = (A.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hA hB

end SevenEighths.HeckePrimePowers

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Set
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def annulusSet (b D : ℝ) : Finset (Ideal O) := idealsUpTo ⌊max 1 b*D⌋₊

def annularWeight (W : ℝ→ℂ) (D σ freq : ℝ) (I : Ideal O) : ℂ :=
  W ((I.absNorm : ℝ)/D)*(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ freq)

def primePolynomial (χ : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter Prime,
    idealCoeff χ I*annularWeight W D σ freq I

theorem annular_support (W : ℝ→ℂ) (a b D : ℝ) (ha : 0<a) (hD : 0<D)
    (hWs : Function.support W⊆Icc a b) (I : Ideal O)
    (hw : W ((I.absNorm : ℝ)/D)≠0) : I∈annulusSet b D := by
  have hs := hWs hw
  apply mem_idealsUpTo.mpr
  constructor
  · have hnorm : 0<(I.absNorm : ℝ) := by
      have := (le_div_iff₀ hD).mp hs.1
      nlinarith
    exact_mod_cast hnorm
  · have hn := (div_le_iff₀ hD).mp hs.2
    exact Nat.le_floor (hn.trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))

theorem log_polynomial_eq_finite (χ : Character) (W : ℝ→ℂ) (a b D σ freq : ℝ)
    (ha : 0<a) (hD : 0<D) (hWs : Function.support W⊆Icc a b)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log D) :
    HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ I∈annulusSet b D,
        (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
  rw [PrimeLogProfile.profile_eq_log_division W a b D ha hWs hD hlarge]
  unfold HeckePrimeDyadic.polynomial
  congr 1
  have he : (fun I : NonzeroIdeal => HeckePrimeDyadic.summand χ
      (fun y => W y/(Real.log (D*y) : ℂ)) D σ freq I) =
      fun I : NonzeroIdeal => (HeckePrimePowers.logWeight I.val : ℂ)*
        idealCoeff χ I.val*annularWeight W D σ freq I.val := by
    funext I
    unfold HeckePrimeDyadic.summand HeckePrimeDyadic.coefficient annularWeight
    dsimp only [HeckePrimePowers.logWeight, HeckeDyadic.norm]
    rw [mul_div_cancel₀ _ hD.ne']
    simp only [Complex.ofReal_div]
    ring
  rw [he]
  calc
    _ = ∑' I : Ideal O, (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
      apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I≠0})
        (f := fun I : Ideal O => (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I)
      intro I hI hzero
      subst I
      exact hI (by simp [HeckePrimePowers.logWeight])
    _ = _ := by
      apply tsum_eq_sum
      intro I hI
      have hw : W ((I.absNorm : ℝ)/D)=0 := by
        by_contra hh
        exact hI (annular_support W a b D ha hD hWs I hh)
      simp [annularWeight,hw]

theorem fixed_profile_norm_bound (W : ℝ→ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0<a) :
    ∃ B : ℝ, 0<B ∧ ∀ σ∈Icc lo hi, ∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B := by
  let K : Set (ℝ×ℝ) := Icc lo hi ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ×ℝ => ‖W p.2‖*p.2^(-p.1)) K := by
    apply (hW.comp continuous_snd).norm.continuousOn.mul
    exact continuous_snd.continuousOn.rpow continuous_fst.neg.continuousOn
      (fun p hp => Or.inl (ne_of_gt (ha.trans_le hp.2.1)))
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc
  refine ⟨|M|+1,by positivity,?_⟩
  intro σ hσ y hy
  exact (hM (Set.mem_image_of_mem _ (show (σ,y)∈K from ⟨hσ,hy⟩))).trans
    (by linarith [le_abs_self M])

theorem extraction_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (W : ℝ→ℂ) (a b D σ freq B : ℝ),
      0<a → 1≤D → Function.support W⊆Icc a b →
      2*(|Real.log a|+|Real.log b|)+1≤Real.log D → 0≤B →
      (∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B) →
      ‖HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq -
        primePolynomial χ W b D σ freq‖≤
        C*(max 1 b)^((1/2 : ℝ)+ε)*D^ε*B := by
  obtain ⟨C,hC,herr⟩ := HeckePrimePowers.prime_extraction_error ε hε
  refine ⟨C,hC,?_⟩
  intro χ W a b D σ freq B ha hD hWs hlarge hB hWbound
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hX : 1≤ max 1 b*D := hD.trans (le_mul_of_one_le_left hDp.le (le_max_left _ _))
  have hnorm (I : Ideal O) (hI : I∈annulusSet b D) : (I.absNorm : ℝ)≤ max 1 b*D := by
    exact (Nat.cast_le.mpr (mem_idealsUpTo.mp hI).2).trans
      (Nat.floor_le (by positivity))
  have hw (I : Ideal O) (_hI : I∈annulusSet b D) : ‖annularWeight W D σ freq I‖≤B := by
    by_cases hz : W ((I.absNorm : ℝ)/D)=0
    · simpa [annularWeight,hz] using hB
    · have hs := hWs hz
      have hy : 0<(I.absNorm : ℝ)/D := ha.trans_le hs.1
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simpa only [Complex.neg_re,shift_re] using hWbound _ hs
  have hb := herr χ (annulusSet b D) (annularWeight W D σ freq) (max 1 b*D) B
    hX hB hnorm hw
  have hn : ‖(D : ℂ)^(-(1/2 : ℂ))‖=D^(-(1/2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hDp]
    norm_num
  rw [log_polynomial_eq_finite χ W a b D σ freq ha hDp hWs hlarge,
    primePolynomial,←mul_sub,norm_mul,hn]
  calc
    _ ≤ D^(-(1/2 : ℝ))*(C*(max 1 b*D)^(1/2+ε)*B) := by
      exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hDp.le _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤ max 1 b) hDp.le]
      have he : D^(-(1/2 : ℝ))*D^(1/2+ε)=D^ε := by
        rw [←Real.rpow_add hDp]
        congr 1
        ring
      calc
        _ = C*(max 1 b)^(1/2+ε)*(D^(-(1/2 : ℝ))*D^(1/2+ε))*B := by ring
        _ = _ := by rw [he]

end SevenEighths.HeckePrimeAnnular

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeBin -/

section

namespace OAI

noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic

theorem prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤ r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      ∀ k : ι, (χ k).modulus.absNorm≤Z^d →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖primePolynomial (χ k) W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨Cp,hCp,hprime⟩ := HeckePrimeDyadic.source_log_profile_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ he he' hκ hη hbudget
  let ξ := ε/(R+1)
  have hξ : 0<ξ := div_pos hε (by positivity)
  obtain ⟨Ce,hCe,herror⟩ := extraction_bound ξ hξ
  obtain ⟨Bf,hBf,hprofile⟩ := fixed_profile_norm_bound W hW.continuous A B σmin σmax hA
  let E := Ce*(max 1 B)^(1/2+ξ)*Bf
  have hE : 0<E := by dsimp [E]; positivity
  refine ⟨Cp+E,by positivity,?_⟩
  intro Z d hZ hd hd' hU2 hT ι _ χ hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge k hQ hfreq hheight
  let U := Z^d
  let D := U^r
  have hU : 1≤U := Real.one_le_rpow hZ hd
  have hUp : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤D := Real.one_le_rpow hU hr
  have hlog : 1≤Real.log D := by
    linarith [abs_nonneg (Real.log A),abs_nonneg (Real.log B)]
  have hL : 1/Real.log D∈Icc (0 : ℝ) 1 :=
    ⟨by positivity,(div_le_one (by linarith)).mpr hlog⟩
  have hp := hprime Z d hZ hd hd' hU2 hT χ hχ a i ha ha' hmax
    r σ freq (1/Real.log D) hr hrR hσmin hσmax hL k hQ hfreq hheight
  have he := herror (χ k) W A B D σ freq Bf hA hD hWs hlarge hBf.le
    (hprofile σ ⟨hσmin,hσmax⟩)
  have hpow : D^ξ≤U^((a-1/2)*r+ε) := by
    dsimp [D]
    rw [←Real.rpow_mul hUp.le]
    apply Real.rpow_le_rpow_of_exponent_le hU
    have hxi : ξ*(R+1)=ε := by dsimp [ξ]; field_simp
    nlinarith [mul_nonneg (show 0≤a-1/2 by linarith) hr,
      mul_le_mul_of_nonneg_right hrR hξ.le]
  have he' : ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
      primePolynomial (χ k) W B D σ freq‖≤E*U^((a-1/2)*r+ε) := by
    apply he.trans
    calc
      _ = E*D^ξ := by dsimp [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hE.le
  calc
    _ ≤ ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq‖+
        ‖HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
          primePolynomial (χ k) W B D σ freq‖ := by
      have hid : primePolynomial (χ k) W B D σ freq =
          HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
          (HeckePrimeDyadic.polynomial (χ k) (PrimeLogProfile.profile W (1/Real.log D)) D σ freq-
            primePolynomial (χ k) W B D σ freq) := by ring
      conv_lhs => rw [hid]
      exact norm_sub_le _ _
    _ ≤ Cp*U^((a-1/2)*r+ε)+E*U^((a-1/2)*r+ε) := add_le_add hp he'
    _ = _ := by ring

end SevenEighths.HeckePrimeAnnular

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeRay -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.HeckePrimeRay
open HeckeFamily HeckePrimeAnnular
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def twistedFamily (η : Character) (θ : RayQuotient.Characters M H) : Character :=
  η.product (HeckeRayQuotient.character M H hH θ)

def rayPrimePolynomial (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter
    (fun I => Prime I ∧ I∈RayQuotient.identityClass M H),
      idealCoeff η I*annularWeight W D σ freq I

theorem finite_average (η : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S.filter (fun I => I∈RayQuotient.identityClass M H), idealCoeff η I*f I) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, ∑ I∈S,
          idealCoeff (twistedFamily M H hH η θ) I*f I := by
  rw [Finset.sum_filter,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [twistedFamily,idealCoeff_product]
  have hs : (∑ θ : RayQuotient.Characters M H,
      idealCoeff η I*idealCoeff (HeckeRayQuotient.character M H hH θ) I*f I) =
      (idealCoeff η I*f I)*∑ θ : RayQuotient.Characters M H,
        idealCoeff (HeckeRayQuotient.character M H hH θ) I := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro θ _
    ring
  rw [hs,mul_left_comm,HeckeRayQuotient.average_idealCoeff M H hH I]
  split_ifs <;> simp

theorem rayPrimePolynomial_eq_average (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) :
    rayPrimePolynomial M H η W b D σ freq =
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          primePolynomial (twistedFamily M H hH η θ) W b D σ freq := by
  unfold rayPrimePolynomial
  have hfilter : (annulusSet b D).filter (fun I => Prime I ∧ I∈RayQuotient.identityClass M H) =
      ((annulusSet b D).filter Prime).filter (fun I => I∈RayQuotient.identityClass M H) := by
    ext I
    simp only [Finset.mem_filter]
    tauto
  rw [hfilter,finite_average M H hH η _ (annularWeight W D σ freq)]
  simp only [primePolynomial]
  rw [←Finset.mul_sum]
  ring

theorem rayPrimePolynomial_norm_le (η : Character) (W : ℝ→ℂ) (b D σ freq C : ℝ)
    (hbound : ∀ θ : RayQuotient.Characters M H,
      ‖primePolynomial (twistedFamily M H hH η θ) W b D σ freq‖≤C) :
    ‖rayPrimePolynomial M H η W b D σ freq‖≤C := by
  rw [rayPrimePolynomial_eq_average M H hH η W b D σ freq,norm_mul,norm_inv]
  have hcard : (0 : ℝ)<RayQuotient.classNumber M H := by
    exact_mod_cast RayQuotient.classNumber_pos M H
  have heq : Fintype.card (RayQuotient.Characters M H)=RayQuotient.classNumber M H :=
    RayOrthogonality.card_characters H
  have hn : ‖(RayQuotient.classNumber M H : ℂ)‖=(RayQuotient.classNumber M H : ℝ) := by simp
  rw [hn]
  calc
    _ ≤ (RayQuotient.classNumber M H : ℝ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H, C :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun θ _ => hbound θ)))
        (by positivity)
    _ = C := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,heq]; rw [←mul_assoc,inv_mul_cancel₀ hcard.ne',one_mul]

theorem ray_prime_bin_bound (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e κ η σmin σmax : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*R+κ≤ε) :
    ∃ C : ℝ, 0<C ∧ ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (ηrow : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH ηrow θ).residue≠1)
      (a : ℝ) (i : ℕ), 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH ηrow) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, 0≤ r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀ θ : RayQuotient.Characters M H,
        (twistedFamily M H hH ηrow θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H ηrow W B ((Z^d)^r) σ freq‖≤
        C*(Z^d)^((a-1/2)*r+ε) := by
  obtain ⟨C,hC,hbound⟩ := prime_bin_bound W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  refine ⟨C,hC,?_⟩
  intro Z d hZ hd hd' hU hT ηrow hχ a i ha ha' hmax r σ freq hr hrR
    hσmin hσmax hlarge hQ hfreq hheight
  apply rayPrimePolynomial_norm_le M H hH
  intro θ
  exact hbound Z d hZ hd hd' hU hT (twistedFamily M H hH ηrow) hχ a i ha ha' hmax
    r σ freq hr hrR hσmin hσmax hlarge θ (hQ θ) hfreq hheight

end SevenEighths.HeckePrimeRay

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeBins -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckePrimeAmplitudeBins

def amplitude (P cap mesh : ℝ) (Q : ℂ) : ℝ :=
  if Q=0 then 0 else min cap (max 0 (mesh*(⌊Real.log ‖Q‖/(mesh*Real.log P)⌋ : ℤ)))

theorem amplitude_bounds (P cap mesh : ℝ) (Q : ℂ) (hcap : 0≤ cap) :
    0≤amplitude P cap mesh Q ∧ amplitude P cap mesh Q≤ cap := by
  unfold amplitude
  split_ifs
  · exact ⟨le_rfl,hcap⟩
  · exact ⟨le_min hcap (le_max_left _ _),min_le_left _ _⟩

theorem amplitude_upper (P cap mesh : ℝ) (Q : ℂ) (hP : 1<P) (hm : 0< mesh)
    (hbound : ‖Q‖≤P^(cap+mesh)) :
    ‖Q‖≤P^(amplitude P cap mesh Q+mesh) := by
  by_cases hQ : Q=0
  · subst Q
    simp only [norm_zero,amplitude,ite_true,zero_add]
    exact Real.rpow_nonneg (by linarith) _
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0<Real.log P := Real.log_pos hP
  have hd : 0< mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  by_cases hc : cap≤ max 0 (mesh*(n : ℝ))
  · simpa [amplitude,hQ,n,min_eq_left hc] using hbound
  · have he : amplitude P cap mesh Q=max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,ite_eq_right hQ]
      exact min_eq_right (le_of_not_ge hc)
    rw [he]
    apply (Real.le_rpow_iff_log_le hx (by linarith : 0<P)).mpr
    have hn : Real.log ‖Q‖/(mesh*Real.log P)<(n : ℝ)+1 := Int.lt_floor_add_one _
    have hn' := (div_lt_iff₀ hd).mp hn
    have hg := mul_le_mul_of_nonneg_right (le_max_right 0 (mesh*(n : ℝ))) hl.le
    nlinarith

theorem amplitude_lower (P cap mesh : ℝ) (Q : ℂ) (hP : 1<P) (hm : 0< mesh)
    (hg : 0<amplitude P cap mesh Q) :
    P^(amplitude P cap mesh Q)≤‖Q‖ := by
  have hQ : Q≠0 := by intro h; simp [amplitude,h] at hg
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0<Real.log P := Real.log_pos hP
  have hd : 0< mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have hpos : 0< mesh*(n : ℝ) := by
    have hmin : amplitude P cap mesh Q≤ max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,ite_eq_right hQ]
      exact min_le_right _ _
    have ht : 0< max 0 (mesh*(n : ℝ)) := hg.trans_le hmin
    exact (lt_max_iff.mp ht).resolve_left (lt_irrefl _)
  have he : amplitude P cap mesh Q=min cap (mesh*(n : ℝ)) := by
    simp only [amplitude,ite_eq_right hQ]
    rw [max_eq_right hpos.le]
  have hn : (n : ℝ)≤Real.log ‖Q‖/(mesh*Real.log P) := Int.floor_le _
  have hn' := (le_div_iff₀ hd).mp hn
  have hb : amplitude P cap mesh Q*Real.log P≤Real.log ‖Q‖ := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_right (min_le_right cap (mesh*(n : ℝ))) hl.le
    nlinarith
  have hpow : 0<P^(amplitude P cap mesh Q) := Real.rpow_pos_of_pos (by linarith) _
  apply (Real.log_le_log_iff hpow hx).mp
  rw [Real.log_rpow (by linarith : 0<P)]
  exact hb

def labels (cap mesh : ℝ) : Finset ℝ :=
  insert 0 (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))

theorem amplitude_mem_labels (P cap mesh : ℝ) (Q : ℂ) (hm : 0< mesh) :
    amplitude P cap mesh Q∈labels cap mesh := by
  by_cases hQ : Q=0
  · simp [amplitude,hQ,labels]
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have he : amplitude P cap mesh Q=min cap (max 0 (mesh*(n : ℝ))) := by
    simp only [amplitude,ite_eq_right hQ]
    rfl
  rw [he]
  by_cases hc : cap≤ max 0 (mesh*(n : ℝ))
  · rw [min_eq_left hc]
    simp [labels]
  rw [min_eq_right (le_of_not_ge hc)]
  by_cases hn : mesh*(n : ℝ)≤0
  · rw [max_eq_left hn]
    simp [labels]
  have hn' : 0< mesh*(n : ℝ) := lt_of_not_ge hn
  rw [max_eq_right hn'.le]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨n,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
  · have hh : (0 : ℝ)≤(n : ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : (n : ℝ)≤ cap/mesh := by
      apply (le_div_iff₀ hm).mpr
      have hlt : max 0 (mesh*(n : ℝ))<cap := lt_of_not_ge hc
      have : mesh*(n : ℝ)≤ max 0 (mesh*(n : ℝ)) := le_max_right _ _
      nlinarith
    exact_mod_cast hh.trans (Int.le_ceil _)

theorem squared_spike (U w cap mesh : ℝ) (Q : ℂ) (hU : 1<U) (hw : 0<w)
    (hm : 0< mesh) (hg : 0<amplitude (U^w) cap mesh Q) :
    U^(2*w*amplitude (U^w) cap mesh Q)≤‖Q‖^2 := by
  have hP : 1<U^w := Real.one_lt_rpow hU hw
  have hb := amplitude_lower (U^w) cap mesh Q hP hm hg
  have hs := (sq_le_sq₀ (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _) (norm_nonneg _)).mpr hb
  convert hs using 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (Real.rpow_nonneg (by linarith : (0 : ℝ)≤U) _),
    ←Real.rpow_mul (by linarith : (0 : ℝ)≤U)]
  congr 1
  ring

theorem product_upper {ι : Type*} (slots : Finset ι) (w : ι→ℝ) (Q : ι→ℂ)
    (U cap mesh : ℝ) (hU : 1<U) (hm : 0< mesh)
    (hw : ∀ i∈slots, 0<w i)
    (hQ : ∀ i∈slots, ‖Q i‖≤(U^(w i))^(cap+mesh)) :
    ‖∏ i∈slots, Q i‖≤U^((∑ i∈slots, w i*amplitude (U^(w i)) cap mesh (Q i))+
      mesh*(∑ i∈slots,w i)) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i∈slots, (U^(w i))^(amplitude (U^(w i)) cap mesh (Q i)+mesh) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi =>
        amplitude_upper _ cap mesh (Q i) (Real.one_lt_rpow hU (hw i hi)) hm (hQ i hi))
    _ = ∏ i∈slots, U^(w i*(amplitude (U^(w i)) cap mesh (Q i)+mesh)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (Real.rpow_mul (by linarith : (0 : ℝ)≤U) _ _).symm
    _ = _ := by
      rw [←Real.rpow_sum_of_pos (by linarith : 0<U)]
      congr 1
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,←Finset.sum_mul, mul_comm mesh]

theorem common_bin_selection {ι : Type*} (slots : Finset ι) (w g : ι→ℝ)
    (U δ mesh binWidth q z : ℝ) (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤ mesh)
    (hbin : 0<binWidth) (hw : ∀ i∈slots, 0<w i) (hwm : ∀ i∈slots, w i≤ mesh)
    (hg : ∀ i∈slots, 0≤g i ∧ g i≤δ/2)
    (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z)
    (hzs : z≤∑ i∈slots,w i) (hmean : q*(∑ i∈slots,w i)≤∑ i∈slots,w i*g i) :
    ∃ T : Finset ι, T⊆slots ∧ (∀ i∈T,0<g i) ∧ (∑ i∈T,w i)≤z ∧
      ∀ Q : ι→ℂ, (∀ i∈slots,amplitude (U^(w i)) (δ/2) binWidth (Q i)=g i) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T,Q i‖^2 := by
  have hm : q*(∑ i∈slots,w i)≤∑ i∈slots,w i*max (g i) 0 := by
    convert hmean using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [max_eq_left (hg i hi).1]
  obtain ⟨T,hTs,hTp,hTw,hTb⟩ := HeckeDetectorSlotSelection.selected_product_spike
    slots w g U δ mesh q z hU.le hδ hmesh (fun i hi => (hw i hi).le) hwm
    (fun i hi => (hg i hi).2) hq hqδ hz hzs hm
  refine ⟨T,hTs,hTp,hTw,?_⟩
  intro Q hQ
  apply hTb Q
  intro i hi hgi
  rw [←hQ i hi] at hgi ⊢
  exact squared_spike U (w i) (δ/2) binWidth (Q i) hU (hw i hi) hbin hgi

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeScale -/

section

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeAmplitudeBins

theorem upper_allowance_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0<dmin) (hmesh : 0< mesh) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r cap : ℝ, dmin≤d → rmin≤ r →
      C*(Z^d)^(cap*r+ε)≤((Z^d)^r)^(cap+mesh) := by
  have hh := HeckeDyadic.constant_absorbed_eventually C (dmin*(rmin*mesh-ε))
    (mul_pos hd (by linarith))
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ
  intro d r cap hd' hr'
  have hZp : 0<Z := by linarith
  have hU : 0<Z^d := Real.rpow_pos_of_pos hZp _
  have hgr : rmin*mesh-ε≤ r*mesh-ε := by nlinarith
  have hexp : dmin*(rmin*mesh-ε)≤d*(r*mesh-ε) :=
    mul_le_mul hd' hgr (by linarith) (hd.trans_le hd').le
  have hc : C≤(Z^d)^(r*mesh-ε) := by
    apply hC.trans
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  calc
    _ ≤ (Z^d)^(r*mesh-ε)*(Z^d)^(cap*r+ε) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hU.le _)
    _ = ((Z^d)^r)^(cap+mesh) := by
      rw [←Real.rpow_add hU,←Real.rpow_mul hU.le]
      congr 1
      ring

theorem actual_bins_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0<dmin) (hr : 0< rmin) (hmesh : 0< mesh) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → ∀ r cap : ℝ, rmin≤ r → 0≤ cap →
      ∀ Q : ℂ, ‖Q‖≤C*(Z^d)^(cap*r+ε) →
      0≤amplitude ((Z^d)^r) cap mesh Q ∧
      amplitude ((Z^d)^r) cap mesh Q≤ cap ∧
      amplitude ((Z^d)^r) cap mesh Q∈labels cap mesh ∧
      ‖Q‖≤((Z^d)^r)^(amplitude ((Z^d)^r) cap mesh Q+mesh) ∧
      (0<amplitude ((Z^d)^r) cap mesh Q →
        (Z^d)^(2*r*amplitude ((Z^d)^r) cap mesh Q)≤‖Q‖^2) := by
  filter_upwards [upper_allowance_eventually C dmin rmin ε mesh hd hmesh hgap,
    eventually_gt_atTop (1 : ℝ)] with Z hallow hZ
  intro d hd' r cap hr' hcap Q hQ
  have hU : 1<Z^d := Real.one_lt_rpow hZ (hd.trans_le hd')
  have hP : 1<(Z^d)^r := Real.one_lt_rpow hU (hr.trans_le hr')
  have hb := amplitude_bounds ((Z^d)^r) cap mesh Q hcap
  exact ⟨hb.1,hb.2,amplitude_mem_labels _ cap mesh Q hmesh,
    amplitude_upper _ cap mesh Q hP hmesh (hQ.trans (hallow d r cap hd' hr')),
    squared_spike (Z^d) r cap mesh Q hU (hr.trans_le hr') hmesh⟩

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeRow -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckePrimeRow
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem identityClass_coprime {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    IsCoprime I M := by
  obtain ⟨hI,a,ha,u,hu,huH⟩ := hI
  rw [←ha]
  exact (IdealCharacter.isUnit_mk_iff_isCoprime M a).mp (hu ▸ u.isUnit)

omit [NeZero M] in
theorem identityClass_coprime_larger {I J : Ideal O}
    (hI : I∈RayQuotient.identityClass M H) (hMJ : M≤J) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply top_unique
  rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hI)]
  exact sup_le_sup_left hMJ I

omit [NeZero M] in
theorem identityClass_prime_good (m : O) (hmLam : λ₀∣m) (hMm : M≤Ideal.span {m})
    (P : Ideal O) [P.IsMaximal] (hP : P∈RayQuotient.identityClass M H) : λ₀∉P := by
  have hm : m∉P := (SixthPowerAverage.prime_coprime_span_iff P m).mp
    (identityClass_coprime_larger M H hP hMm)
  intro hLam
  obtain ⟨a,rfl⟩ := hmLam
  exact hm (P.mul_mem_right a hLam)

include hH in
theorem identityClass_principal_coeff {I : Ideal O} (hI : I∈RayQuotient.identityClass M H) :
    idealCoeff (HeckeRayFamily.character M 1) I=1 := by
  have hc := identityClass_coprime M H hI
  change RayQuotient.idealCharacter M H hH 1 I=1
  rw [RayQuotient.idealCharacter_one M H hH I,ite_eq_right hI.1,ite_eq_left hc]

include hH in
theorem exists_actual_prime_row (m u : O) (hm : m≠0) (hu : u≠0)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (hMm : M≤Ideal.span {m}) :
    ∃ χ : Character, χ.modulus.absNorm≤ rowConductorBound (HeckeRayFamily.character M 1) m 1 u ∧
      ∀ (P : Ideal O) [P.IsMaximal] (hg : λ₀∉P),
      P∈RayQuotient.identityClass M H →
      idealCoeff χ P = starRingEnd ℂ
        (CompletedGauss.actualSextic P hg (Ideal.Quotient.mk P u)) := by
  obtain ⟨χ,hbound,hχ⟩ := exists_row_character_with_conductor (HeckeRayFamily.character M 1) m 1 u hm one_ne_zero hu hmLam hm2
  refine ⟨χ.inverse,hbound,?_⟩
  intro P _ hg hP
  have hc : IsCoprime P (Ideal.span {m}) := by
    rw [Ideal.isCoprime_iff_sup_eq] at ⊢
    apply top_unique
    rw [←Ideal.isCoprime_iff_sup_eq.mp (identityClass_coprime M H hP)]
    exact sup_le_sup_left hMm P
  rw [idealCoeff_inverse_conj,idealCoeff_eq_row _ χ m 1 u hχ,
    identityClass_principal_coeff M H hH hP,one_mul,one_pow,mul_one,
    idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,ite_eq_left hc,one_mul,
    idealRowHom_prime u P hg]

def canonicalPrimeAmplitude (u : O) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ P∈(HeckePrimeAnnular.annulusSet b D).filter
    (fun P => Prime P ∧ P∈RayQuotient.identityClass M H),
    starRingEnd ℂ (idealRowHom u P)*W ((P.absNorm : ℝ)/D)*
      (((P.absNorm : ℝ)/D : ℝ) : ℂ)^(z-1)

include hH in

theorem exists_amplitude_character (m u : O) (hm : m≠0) (hu : u≠0)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (hMm : M≤Ideal.span {m}) :
    ∃ χ : Character, χ.modulus.absNorm≤ rowConductorBound (HeckeRayFamily.character M 1) m 1 u ∧
      ∀ (W : ℝ→ℂ) (b D : ℝ) (z : ℂ),
        canonicalPrimeAmplitude M H u W b D z =
          HeckePrimeRay.rayPrimePolynomial M H χ W b D (1-z.re) z.im := by
  obtain ⟨χ,hbound,hχ⟩ := exists_actual_prime_row M H hH m u hm hu hmLam hm2 hMm
  refine ⟨χ,hbound,?_⟩
  intro W b D z
  unfold canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hprime,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hg := identityClass_prime_good M H m hmLam hMm P hclass
  have hc := hχ P hg hclass
  rw [←idealRowHom_prime u P hg] at hc
  rw [hc]
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  ring

end SevenEighths.HeckePrimeRow

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeNonprincipal -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckePrimeNonprincipal
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem inverse_twist_elementCoeff (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n) (n : O) :
    elementCoeff ((χ.inverse.product θ).inverse) n =
      rowTwist (elementHom (η.product θ.inverse)) m f z n := by
  rw [elementCoeff_inverse,elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,hχ]
  change _ = elementCoeff (η.product θ.inverse) n * idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  change (elementCoeff θ n)⁻¹ *
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) = _
  ring

theorem twisted_nonprincipal (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤ c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime (((η.product θ.inverse).modulus*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c)) :
    (χ.inverse.product θ).residue≠1 := by
  have hn := HeckeRowNonprincipal.actual_row_nonprincipal (η.product θ.inverse)
    ((χ.inverse.product θ).inverse) m f z hmLam hm2 u a b r hr hpr hx P J hg hchar hJ
    hc hc6 hsplit hcop (inverse_twist_elementCoeff η χ θ m f z hχ)
  intro h
  apply hn
  change (χ.inverse.product θ).residue⁻¹=1
  rw [h,inv_one]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem fixed_twist_modulus (θ : RayQuotient.Characters M H) :
    ((HeckeRayFamily.character M 1).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change M⊓M=M
  simp

theorem fixed_ray_twisted_nonprincipal (χ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom (HeckeRayFamily.character M 1)) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤ c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ.inverse θ).residue≠1 := by
  apply twisted_nonprincipal (HeckeRayFamily.character M 1) χ
    (HeckeRayQuotient.character M H hH θ) m f z hχ hmLam hm2 u a b r hr hpr hx
    P J hg hchar hJ hc hc6 hsplit
  rwa [fixed_twist_modulus M H hH θ]

end SevenEighths.HeckePrimeNonprincipal

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeScale -/

section

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeScale
open HeckeFamily

theorem log_scale_eventually (dmin rmin K : ℝ) (hd : 0<dmin) (hr : 0< rmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r : ℝ, dmin≤d → rmin≤ r →
      K≤Real.log ((Z^d)^r) := by
  have hlog : ∀ᶠ Z : ℝ in atTop, max 0 (K/(dmin*rmin))≤Real.log Z :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with Z hlog hZ
  intro d r hd' hr'
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.log_rpow (Real.rpow_pos_of_pos hZp _),Real.log_rpow hZp]
  have hp : 0<dmin*rmin := mul_pos hd hr
  have hk : K≤dmin*rmin*Real.log Z := by
    have hh := (div_le_iff₀ hp).mp ((le_max_right 0 _).trans hlog)
    nlinarith
  have hprod : dmin*rmin≤d*r := mul_le_mul hd' hr' hr.le (hd.trans_le hd').le
  have hl : 0≤Real.log Z := (le_max_left _ _).trans hlog
  nlinarith [mul_le_mul_of_nonneg_right hprod hl]

theorem product_modulus_bound (χ ψ : Character) :
    (χ.product ψ).modulus.absNorm≤χ.modulus.absNorm*ψ.modulus.absNorm := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus ψ.modulus

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem twisted_modulus_bound (χ : Character) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤χ.modulus.absNorm*M.absNorm :=
  product_modulus_bound χ (HeckeRayQuotient.character M H hH θ)

theorem twisted_row_modulus_bound (χ : Character) (m u : O)
    (hχ : χ.modulus.absNorm≤HeckeRowClosure.rowConductorBound (HeckeRayFamily.character M 1) m 1 u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {m}).absNorm*(Ideal.span {(72 : O)}).absNorm*(Ideal.span {u}).absNorm := by
  apply (twisted_modulus_bound M H hH χ θ).trans
  have hn := Nat.mul_le_mul_right M.absNorm hχ
  simpa [HeckeRowClosure.rowConductorBound,HeckeRayFamily.character,
    Character.ofResidue,pow_two,mul_assoc,mul_left_comm,mul_comm] using hn

end SevenEighths.HeckePrimeScale

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorPrimeFamily -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckeDetectorPrimeFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

structure RowData (M : Ideal O) where
  m : O
  u : O
  m_ne_zero : m≠0
  u_ne_zero : u≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m
  modulus_le : M≤Ideal.span {m}

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def RowData.base (data : RowData M) : Character :=
  Classical.choose (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)

theorem RowData.base_spec (data : RowData M) (n : O) :
    elementCoeff (data.base M) n=
      rowTwist (elementHom (HeckeRayFamily.character M 1)) data.m 1 data.u n :=
  (Classical.choose_spec (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)).2 n

theorem RowData.base_conductor (data : RowData M) :
    (data.base M).modulus.absNorm≤ rowConductorBound (HeckeRayFamily.character M 1) data.m 1 data.u :=
  (Classical.choose_spec (exists_row_character_with_conductor (HeckeRayFamily.character M 1)
    data.m 1 data.u data.m_ne_zero one_ne_zero data.u_ne_zero data.lambda_dvd data.two_dvd)).1

def RowData.character (data : RowData M) : Character := (data.base M).inverse

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH in
theorem RowData.coefficient_on_ray (data : RowData M) (P : Ideal O) [P.IsMaximal]
    (hg : λ₀∉P) (hP : P∈RayQuotient.identityClass M H) :
    idealCoeff (data.character M) P=starRingEnd ℂ (idealRowHom data.u P) := by
  have hc := HeckePrimeRow.identityClass_coprime_larger M H hP data.modulus_le
  rw [RowData.character,idealCoeff_inverse_conj,
    idealCoeff_eq_row _ (data.base M) data.m 1 data.u (data.base_spec M),
    HeckePrimeRow.identityClass_principal_coeff M H hH hP,one_mul,one_pow,mul_one,
    idealRowHom_argument_mul,idealRowHom_prime_sixth_mask data.m P hg,ite_eq_left hc,one_mul]

include hH in
theorem RowData.amplitude_eq (data : RowData M) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨_,hprime,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H data.m data.lambda_dvd data.modulus_le P hclass
  rw [data.coefficient_on_ray M H hH P hg hclass]
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  ring

theorem RowData.twisted_conductor (data : RowData M) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm := by
  apply HeckePrimeScale.twisted_row_modulus_bound M H hH (data.character M) data.m data.u
  exact data.base_conductor M

theorem RowData.twisted_nonprincipal (data : RowData M)
    (unit : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : data.u=(unit : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤ c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {data.m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).residue≠1 := by
  exact HeckePrimeNonprincipal.fixed_ray_twisted_nonprincipal M H hH (data.base M)
    data.m 1 data.u (data.base_spec M) data.lambda_dvd data.two_dvd unit a b r hr hpr
    (by simpa using hx) P J hg hchar hJ hc hc6 hsplit hcop θ

structure Ramification (data : RowData M) where
  unit : Oˣ
  lambda_power : ℕ
  two_power : ℕ
  remaining : O
  supported : CanonicalQuadraticSieve.Supported (Ideal.span {remaining})
  primary : λ₀^2∣remaining-1
  decomposition : data.u=(unit : O)*λ₀^lambda_power*(2 : O)^two_power*remaining
  prime : Ideal O
  rest : Ideal O
  maximal : prime.IsMaximal
  prime_good : λ₀∉prime
  odd : ringChar (O ⧸ prime)≠2
  rest_supported : CanonicalQuadraticSieve.Supported rest
  multiplicity : ℕ
  multiplicity_pos : 1≤ multiplicity
  not_sixfold : ¬6∣multiplicity
  split : Ideal.span {remaining}=prime^multiplicity*rest
  coprime : IsCoprime ((M*Ideal.span {data.m}*Ideal.span {(72 : O)})*rest) (prime^multiplicity)

theorem Ramification.nonprincipal {data : RowData M} (cert : Ramification M data)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (data.character M) θ).residue≠1 := by
  let := cert.maximal
  exact data.twisted_nonprincipal M H hH cert.unit cert.lambda_power cert.two_power
    cert.remaining cert.supported cert.primary cert.decomposition cert.prime cert.rest cert.prime_good
    cert.odd cert.rest_supported cert.multiplicity_pos cert.not_sixfold cert.split cert.coprime θ

end SevenEighths.HeckeDetectorPrimeFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRelativePrime -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

theorem idealCoeff_ne_zero_of_coprime (ν : Character) (J : Ideal O)
    (hJ : J≠0) (hc : IsCoprime J ν.modulus) : idealCoeff ν J≠0 := by
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν hg]
  apply MulChar.apply_ne_zero_iff.mpr
  apply (IdealCharacter.isUnit_mk_iff_isCoprime ν.modulus _).mpr
  simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc

theorem idealCoeff_inverse (ν : Character) (J : Ideal O) :
    idealCoeff ν.inverse J=(idealCoeff ν J)⁻¹ := by
  by_cases hJ : J=0
  · subst J
    simp only [map_zero,inv_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,idealCoeff_span ν.inverse hg,
    idealCoeff_span ν hg,HeckeFamily.elementCoeff_inverse]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem relative_coefficient_on_ray (ν χ : Character) (hM : M≤ν.modulus)
    (J : Ideal O) (hJ : J∈RayQuotient.identityClass M H) :
    idealCoeff ((ν.product χ).product ν.inverse) J=idealCoeff χ J := by
  have hn := idealCoeff_ne_zero_of_coprime ν J hJ.1
    (HeckePrimeRow.identityClass_coprime_larger M H hJ hM)
  rw [idealCoeff_product,idealCoeff_product,idealCoeff_inverse]
  field_simp

theorem physical_eq_relative_average (data : RowData M) (ν : Character)
    (hM : M≤ν.modulus) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          HeckePrimeAnnular.primePolynomial
            ((ν.product (data.character M)).product
              (ν.inverse.product (HeckeRayQuotient.character M H hH θ)))
            W b D (1-z.re) z.im := by
  rw [data.amplitude_eq M H hH]
  have he : HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im=
      HeckePrimeRay.rayPrimePolynomial M H ((ν.product (data.character M)).product ν.inverse)
        W b D (1-z.re) z.im := by
    unfold HeckePrimeRay.rayPrimePolynomial
    congr 1
    apply Finset.sum_congr rfl
    intro J hJ
    rw [relative_coefficient_on_ray M H ν (data.character M) hM J (Finset.mem_filter.mp hJ).2.2]
  rw [he,HeckePrimeRay.rayPrimePolynomial_eq_average M H hH]
  congr 1
  apply Finset.sum_congr rfl
  intro θ hθ
  unfold HeckePrimeAnnular.primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [HeckePrimeRay.twistedFamily,idealCoeff_product]
  ring

end SevenEighths.HeckeDetectorRelativePrime

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeActual -/

section

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckePrimeAmplitudeActual
open HeckeFamily HeckePrimeRay HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ray_amplitude_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ r σ freq : ℝ, rmin≤ r → r≤R → σmin≤σ → σ≤σmax →
      (∀ θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  have hbins := actual_bins_eventually C dmin rmin ε mesh hdmin hrmin hmesh hgap
  have hlog := HeckePrimeScale.log_scale_eventually dmin rmin
    (2*(|Real.log A|+|Real.log B|)+1) hdmin hrmin
  filter_upwards [hbins,hlog,eventually_ge_atTop (1 : ℝ)] with Z hb hl hZ
  intro d hd hd' hU hT χ hχ a i ha ha' hmax r σ freq hr hr' hσ hσ' hQ hf ht
  have hestimate := hbound Z d hZ (hdmin.trans_le hd).le hd' hU hT χ hχ a i
    ha ha' hmax r σ freq (hrmin.trans_le hr).le hr' hσ hσ' (hl d r hd hr) hQ hf ht
  exact hb d hd r (a-1/2) hr (by linarith) _ hestimate

end SevenEighths.HeckePrimeAmplitudeActual

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalBins -/

section

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace SevenEighths.HeckeDetectorPhysicalBins
open HeckeFamily HeckeDetectorPrimeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem physical_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (data : RowData M) (cert : Ramification M data) (a : ℝ) (i : ℕ),
      51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum
        (HeckePrimeRay.twistedFamily M H hH (data.character M))
        (cert.nonprincipal M H hH) (3*(i+1 : ℕ)*Z^τ)<a+2*e →
    ∀ (r : ℝ) (z : ℂ), rmin≤ r → r≤R → σmin≤1-z.re → 1-z.re≤σmax →
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm≤Z^d →
      |z.im|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H data.u W B ((Z^d)^r) z
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  have hh := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA hWs hW
    R dmin dmax rmin τ ε e κ η mesh σmin σmax hR hdmin hdmax hrmin
    hτ hε he he' hκ hη hmesh hbudget hgap
  filter_upwards [hh] with Z hZ
  intro d hd hd' hU hT data cert a i ha ha' hnext r z hr hr' hs hs' hQ hf ht
  have hQ' (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤Z^d := by
    have hb := data.twisted_conductor M H hH θ
    have hb' : ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤
        ((M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
          (Ideal.span {data.u}).absNorm : ℕ) : ℝ) := by exact_mod_cast hb
    exact hb'.trans (by exact_mod_cast hQ)
  have hb := hZ d hd hd' hU hT (data.character M) (cert.nonprincipal M H hH)
    a i ha ha' hnext r (1-z.re) z.im hr hr' hs hs' hQ' hf ht
  simpa only [data.amplitude_eq M H hH] using hb

end SevenEighths.HeckeDetectorPhysicalBins

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorPhysicalSelection
open HeckeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def physical {Row Slot : Type*} (row : Row→O) (W : Slot→ℝ→ℂ)
    (b w : Slot→ℝ) (z : Slot→ℂ) (U : ℝ) (u : Row) (s : Slot) : ℂ :=
  HeckePrimeRow.canonicalPrimeAmplitude M H (row u) (W s) (b s) (U^(w s)) (z s)

def weightedMean {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ) : ℝ :=
  (∑ s∈slots,w s*g s)/(∑ s∈slots,w s)

theorem weightedMean_bounds {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ)
    (δ : ℝ) (hw : ∀ s∈slots,0≤w s) (hL : 0<∑ s∈slots,w s)
    (hg : ∀ s∈slots,0≤g s ∧ g s≤δ/2) :
    0≤weightedMean slots w g ∧ weightedMean slots w g≤δ/2 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun s hs => mul_nonneg (hw s hs) (hg s hs).1)) hL.le
  · apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ ∑ s∈slots,w s*(δ/2) := Finset.sum_le_sum (fun s hs =>
        mul_le_mul_of_nonneg_left (hg s hs).2 (hw s hs))
      _ = _ := by rw [←Finset.sum_mul]; ring

omit [NeZero M] in
theorem select_physical_product {Row Slot : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b w g : Slot→ℝ)
    (zs : Slot→ℂ) (U δ mesh binWidth z : ℝ)
    (hU : 1<U) (hδ : 0≤δ) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<w s) (hwm : ∀ s∈slots,w s≤ mesh)
    (hL : 0<∑ s∈slots,w s) (hz : 0≤z) (hzL : z≤∑ s∈slots,w s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      amplitude (U^(w s)) (δ/2) binWidth (physical M H row W b w zs U u s)=g s) :
    ∃ selected : Finset Slot, selected⊆slots ∧ (∀ s∈selected,0<g s) ∧
      (∑ s∈selected,w s)≤z ∧
      ∀ u∈rows, U^(2*weightedMean slots w g*z-δ*mesh)≤
        ‖∏ s∈selected,physical M H row W b w zs U u s‖^2 := by
  obtain ⟨u0,hu0⟩ := hne
  have hg (s : Slot) (hs : s∈slots) : 0≤g s ∧ g s≤δ/2 := by
    rw [←hbins u0 hu0 s hs]
    exact amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ (fun s hs => (hw s hs).le) hL hg
  have hm : weightedMean slots w g*(∑ s∈slots,w s)≤∑ s∈slots,w s*g s := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := common_bin_selection slots w g U δ mesh binWidth
    (weightedMean slots w g) z hU hδ hmesh hbin hw hwm hg hq hqδ hz hzL hm
  exact ⟨selected,hsub,hpositive,hlen,fun u hu => hspike _ (hbins u hu)⟩

end SevenEighths.HeckeDetectorPhysicalSelection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorFiberSpikes -/

section

namespace OAI

noncomputable section
open scoped Classical
open Set
namespace SevenEighths.HeckeDetectorFiberSpikes
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem fiber_spikes {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(w u).label=label)
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    ∀ u∈rows,
      (w u).zero.re∈Icc (0 : ℝ) 1 ∧
      |(w u).frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T ∧
      U^((2*a-1)*r-2*ε)≤
        ‖polynomial (χ u label) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
          (U^r) (w u).zero.re (w u).frequency‖^2 ∧
      U^((2*a-1)*m-2*ε)≤
        ‖polynomial (χ u label) false positiveAnnular (U^m) (w u).zero.re (w u).frequency‖^2 := by
  dsimp only
  intro u hu
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by rw [(w u).left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by rw [(w u).right_exponent hU,hK u hu]
  refine ⟨⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩,(w u).frequency_bound,?_,?_⟩
  · simpa only [hr,hlabel u hu,Witness.frequency] using (w u).inverse_spike
  · simpa only [hm,hlabel u hu,Witness.frequency] using (w u).plain_spike

end SevenEighths.HeckeDetectorFiberSpikes

end

end OAI

end

