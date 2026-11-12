module

public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.DyadicMellin
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part006

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Hecke / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Hecke.DyadicContour -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

def integrand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+shift σ freq-(1/2 : ℂ)) *
    series χ inverse (s+shift σ freq)

theorem series_norm_le (χ : Character) (inverse : Bool) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤ s.re) :
    ‖series χ inverse s‖ ≤ HeckeReciprocalBound.bound b := by
  cases inverse
  · exact HeckeStripActual.LFunction_norm_le χ hb hs
  · exact HeckeReciprocalBound.reciprocal_norm_le χ hb hs

theorem series_differentiableAt_right (χ : Character) (inverse : Bool) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hs) (Or.inl (by intro h; norm_num [h] at hs))
  · exact HeckeReciprocal.reciprocal_differentiableAt χ
      (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one hs)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) {s : ℂ} (hz : inverse=true → LFunction χ s≠0) :
    DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_entire_nonprincipal χ hχ s
  · have he : series χ true = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [series, HeckeReciprocal.reciprocal, hχ]
    rw [he]
    exact (LFunction_entire_nonprincipal χ hχ s).inv (hz rfl)

theorem integrand_differentiableAt (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ inverse) (s+shift σ freq)) :
    DifferentiableAt ℂ (integrand χ inverse W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (shift σ freq))

theorem integrand_norm (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ inverse W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ inverse (s+shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ inverse (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*HeckeReciprocalBound.bound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ inverse W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ inverse hc (by simp))
  positivity

theorem finite_rectangle (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ inverse W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ inverse (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ inverse W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1< r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ inverse W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ inverse W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle χ hχ inverse W a b ha hWs hW D σ freq l r T hD hz]

end SevenEighths.HeckeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DyadicEstimates -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem rapid_tail_bound (F : ℝ → ℂ) (C T : ℝ) (n : ℕ) (hC : 0≤C) (hT : 0≤T)
    (hF : ∀ t : ℝ, (1+|t|)^(n+2)*‖F t‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, F t‖ ≤ C/(1+T)^n*Real.pi := by
  have hen (t : ℝ) (ht : t ∈ (Icc (-T) T)ᶜ) :
      ‖F t‖≤(C/(1+T)^n)*(1+t^2)⁻¹ := by
    have ht' : T≤|t| := by
      by_contra h
      have hab : |t|<T := lt_of_not_ge h
      exact ht ⟨(abs_lt.mp hab).1.le, (abs_lt.mp hab).2.le⟩
    have hp : (1+T)^n*(1+t^2)≤(1+|t|)^(n+2) := by
      rw [pow_add]
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by linarith) (by linarith) n
      · nlinarith [sq_abs t, abs_nonneg t]
      · positivity
      · positivity
    have hh : ‖F t‖*((1+T)^n*(1+t^2))≤C :=
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by simpa [mul_comm] using hF t)
    have hb := (le_div_iff₀ (by positivity : 0<(1+T)^n*(1+t^2))).mpr hh
    simpa [div_mul_eq_div_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb
  have hint := (integrable_inv_one_add_sq.const_mul (C/(1+T)^n))
  calc
    _ ≤ ∫ t : ℝ in (Icc (-T) T)ᶜ, (C/(1+T)^n)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
      exact hen t ht
    _ ≤ ∫ t : ℝ, (C/(1+T)^n)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem absolute_tail_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1< r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun _ => norm_nonneg _))
  · exact hT
  · intro t
    rw [integrand_norm χ inverse W D σ freq hD]
    have hb := series_norm_le χ inverse hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ inverse ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ inverse ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ inverse W D σ freq hD]
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

end SevenEighths.HeckeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DyadicJoins -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem horizontal_join_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hC : 0≤C) (_hK : 0≤K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤C)
    (hs : ∀ x ∈ Icc l r, ‖series χ inverse ((x : ℂ)+y*I+shift σ freq)‖≤K) :
    ‖∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ inverse W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem profile_strip_decay (a b : ℝ) (ha : 0<a) (l r : ℝ) (n : ℕ) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ)⊆Icc a b →
      ∀ x ∈ Icc l r, ∀ y : ℝ,
      (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  CubicReflectionKernel.mellin_strip_source_bound a b ha l r n

end SevenEighths.HeckeDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationColumn -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_reciprocal_identity (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    {s : ℂ} (hs : 1<s.re) :
    series χ true s=(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s))*series ψ true s := by
  have hL : LFunction ψ s=LFunction χ s*(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s)) := by
    rw [LFunction_eq_series ψ hs,LFunction_eq_series χ hs,hm,
      IdealEuler.series_deletePrimes {P} (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs]
    simp only [Finset.prod_singleton]
    change IdealEuler.series (idealCoeff χ) s *
      (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)=_
    rw [CubicEisenstein.fullIdealWeight,ite_eq_right P.property.ne_zero]
  have h0 : s≠0 := by intro h; norm_num [h] at hs
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  simp only [series,ite_true,HeckeReciprocal.reciprocal_eq_inv χ h0 h1,
    HeckeReciprocal.reciprocal_eq_inv ψ h0 h1]
  have hχ := LFunction_ne_zero_of_one_lt_re χ hs
  have hψ := LFunction_ne_zero_of_one_lt_re ψ hs
  apply (mul_right_cancel₀ hψ)
  rw [mul_assoc,inv_mul_cancel₀ hψ,mul_one,hL]
  rw [←mul_assoc,inv_mul_cancel₀ hχ,one_mul]

lemma rescaled_power (D N : ℝ) (hD : 0<D) (hN : 0<N) (w : ℂ) :
    (D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w)=
      (N : ℂ)^(-(1/2 : ℂ))*((D/N : ℝ) : ℂ)^(w-(1/2 : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hD hN).ne')]
  rw [←Complex.ofReal_log hD.le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log (div_pos hD hN).le,Real.log_div hD.ne' hN.ne']
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem prime_column_identity (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    polynomial χ true W D σ freq=polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq := by
  let N : ℝ := P.val.absNorm
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc : 1<(2-σ)+σ := by linarith
  have he (t : ℝ) : integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)=
      integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)-
      (idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ)))*
        integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I) := by
    let w : ℂ := (((2-σ : ℝ) : ℂ)+t*I)+shift σ freq
    have hw : 1<w.re := by dsimp [w]; simp
    have hr := prime_reciprocal_identity χ ψ P hm hw
    have hp := rescaled_power D N hD hN w
    unfold integrand
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series χ true w=_
    rw [hr]
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*
      ((1-idealCoeff χ P.val*(N : ℂ)^(-w))*series ψ true w)=_
    calc
      _ = mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series ψ true w-
          idealCoeff χ P.val*mellin W _*((D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w))*series ψ true w := by ring
      _ = _ := by rw [hp]; ring
  have hI := integrand_vertical_integrable ψ true W a b ha hWs hW D (2-σ) σ freq hD hc
  have hJ := integrand_vertical_integrable ψ true W a b ha hWs hW (D/N) (2-σ) σ freq (div_pos hD hN) hc
  rw [polynomial_mellin χ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW (D/(P.val.absNorm : ℝ)) (2-σ) σ freq (div_pos hD hN) hc]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))=_
  simp_rw [he]
  rw [integral_sub hI (hJ.const_mul _),integral_const_mul]
  change _=(1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))-
    idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ))*
      ((1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I)))
  ring

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationMask -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem row_coeff_zero_unsupported (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (J : Ideal O) (hJ : ¬Supported J) :
    idealCoeff χ J=0 := by
  by_cases hz : J=0
  · subst J
    exact map_zero _
  let n := ConcretePrimeRowBridge.idealGenerator J
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero J hz
  have hs : Ideal.span {n}=J := ConcretePrimeRowBridge.span_idealGenerator J
  rw [←hs,idealCoeff_span χ hn,heq]
  exact rowTwist_zero_of_not_supported (elementHom η) m f z n hmLam hm2 (hs ▸ hJ)

theorem prime_coprime_iff (P : SmoothMobiusCorrection.PrimeIdeal) (J : Ideal O) :
    IsCoprime J P.val ↔ ¬P.val∣J := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  rw [isCoprime_comm,Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint,
    ←Ideal.dvd_iff_le]

theorem amplified_row_prime_mask (η χ ψ : Character) (m f z a : O)
    (P : SmoothMobiusCorrection.PrimeIdeal) (hspan : Ideal.span {a}=P.val)
    (hχ : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hψ : ∀ n : O, elementCoeff ψ n=rowTwist (elementHom η) m f (z*a^6) n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) :
    idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ) := by
  ext J
  rw [IdealEuler.deletePrimes_apply]
  simp only [Finset.mem_singleton,forall_eq]
  by_cases hs : Supported J
  · rw [idealCoeff_eq_row η ψ m f (z*a^6) hψ,
      show m^6*f^4*(z*a^6)=(m^6*f^4*z)*a^6 by ring,
      idealRowHom_argument_mul,idealRowHom_sixth_mask a J hs,hspan,prime_coprime_iff]
    by_cases hd : P.val∣J
    · simp [hd]
    · simp only [hd,not_false_eq_true,ite_true,mul_one]
      exact (idealCoeff_eq_row η χ m f z hχ J).symm
  · rw [row_coeff_zero_unsupported η ψ m f (z*a^6) hψ hmLam hm2 J hs,
      row_coeff_zero_unsupported η χ m f z hχ hmLam hm2 J hs]
    simp

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_column_energy (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ true W D σ freq‖^2≤
      2*(‖polynomial ψ true W D σ freq‖^2+
        ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖^2) := by
  have hN : (1 : ℝ)≤P.val.absNorm := by
    exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
  have hNp : (0 : ℝ)<P.val.absNorm := by linarith
  have hc : ‖idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
    rw [norm_mul]
    have hh : ‖(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
      change ‖((P.val.absNorm : ℝ) : ℂ)^(-(1/2 : ℂ))‖≤1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNp]
      norm_num
      exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (idealCoeff_norm_le_one χ P.val)).trans hh
  rw [prime_column_identity χ ψ P hm W a b ha hWs hW D σ freq hD]
  have hn := norm_sub_le (polynomial ψ true W D σ freq)
    (idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)
  rw [norm_mul] at hn
  have hb := mul_le_of_le_one_left
    (norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)) hc
  nlinarith [norm_nonneg (polynomial ψ true W D σ freq),
    norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    norm_nonneg (polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    sq_nonneg (‖polynomial ψ true W D σ freq‖-
      ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖)]

theorem finite_amplification (rows : Finset FreeRow) (multipliers : Finset NonzeroIdeal)
    (target : Finset O) (F : FreeRow→ℝ) (E : O→ℝ) (K : ℝ)
    (hK : 0≤K) (hE : ∀ u, 0≤E u)
    (hmap : ∀ u∈rows, ∀ A∈multipliers, rowMap (u,A)∈target)
    (hamp : ∀ u∈rows, ∀ A∈multipliers, F u≤K*E (rowMap (u,A))) :
    (multipliers.card : ℝ)*(∑ u∈rows, F u)≤K*∑ v∈target, E v := by
  have hs : (multipliers.card : ℝ)*(∑ u∈rows, F u)=
      ∑ p∈rows×ˢmultipliers, F p.1 := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const,nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hs]
  calc
    _ ≤ ∑ p∈rows×ˢmultipliers, K*E (rowMap p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hu,hA⟩ := Finset.mem_product.mp hp
      exact hamp p.1 hu p.2 hA
    _ = K*∑ v∈(rows×ˢmultipliers).image rowMap, E v := by
      rw [Finset.mul_sum,Finset.sum_image]
      exact fun p hp q hq h => rowMap_injective h
    _ ≤ K*∑ v∈target, E v := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hu,hA⟩ := Finset.mem_product.mp hp
        exact hmap p.1 hu p.2 hA
      · intro v hv hn
        exact hE v

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily -/

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeRowClosure
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
abbrev NonzeroElement := UnrestrictedIdealReindex.NonzeroElement

structure RowData where
  η : Character
  m : O
  f : O
  m_ne_zero : m≠0
  f_ne_zero : f≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m

def RowData.character (data : RowData) (u : NonzeroElement) : Character :=
  Classical.choose (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)

theorem RowData.character_spec (data : RowData) (u : NonzeroElement) (n : O) :
    elementCoeff (data.character u) n=
      CanonicalRowCompletion.rowTwist (elementHom data.η) data.m data.f u.val n :=
  Classical.choose_spec (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd) n

def amplifiedElement (u : NonzeroElement) (A : NonzeroIdeal) : NonzeroElement :=
  ⟨u.val*(ConcretePrimeRowBridge.idealGenerator A.val)^6,
    mul_ne_zero u.property (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero A.val A.property))⟩

theorem RowData.amplified_prime_mask (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) :
    idealCoeff (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))=
      IdealEuler.deletePrimes {P} (idealCoeff (data.character u)) := by
  exact amplified_row_prime_mask data.η (data.character u)
    (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) data.m data.f u.val
    (ConcretePrimeRowBridge.idealGenerator P.val) P
    (ConcretePrimeRowBridge.span_idealGenerator P.val)
    (data.character_spec u) (data.character_spec (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))
    data.lambda_dvd data.two_dvd

theorem RowData.prime_column (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    polynomial (data.character u) true W D σ freq=
      polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq-
      idealCoeff (data.character u) P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq :=
  prime_column_identity _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

theorem RowData.prime_energy (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial (data.character u) true W D σ freq‖^2≤
      2*(‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq‖^2+
        ‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq‖^2) :=
  prime_column_energy _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

