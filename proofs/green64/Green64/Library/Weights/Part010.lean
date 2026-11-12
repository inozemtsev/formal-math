module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Weights / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceCompactCollarSymbol -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1000000

noncomputable def collarD434 (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.derivCLM ℝ ℂ f
noncomputable def collarZ434 (h t u : ℝ) : ℝ := h * Real.exp (-u) * t / (2*Real.pi)
noncomputable def sourceCompactCollarSymbol434 (chi kappa : 𝓢(ℝ,ℂ)) (h t u : ℝ) : ℂ :=
  chi u * (Real.exp (-u) : ℂ) * kappa (collarZ434 h t u)

 theorem collarD434_apply (f : 𝓢(ℝ,ℂ)) (u : ℝ) : collarD434 f u = deriv f u :=
  SchwartzMap.derivCLM_apply ℝ f u

 theorem collar_schwartz_hasDerivAt434 (f : 𝓢(ℝ,ℂ)) (u : ℝ) :
    HasDerivAt f (collarD434 f u) u := by
  rw [collarD434_apply]
  exact ((f.smooth 1).differentiable (by norm_num)).differentiableAt.hasDerivAt

 theorem collar_z_hasDerivAt434 (h t u : ℝ) :
    HasDerivAt (collarZ434 h t) (-collarZ434 h t u) u := by
  have he := (Real.hasDerivAt_exp (-u)).comp u ((hasDerivAt_id u).neg)
  convert ((he.const_mul h).mul_const t).div_const (2*Real.pi) using 1
  · funext x; rfl
  · simp only [collarZ434]; ring

 theorem source_compact_collar_symbol_smooth434 (chi kappa : 𝓢(ℝ,ℂ)) (h t : ℝ) :
    ContDiff ℝ ∞ (sourceCompactCollarSymbol434 chi kappa h t) := by
  have hc := chi.smooth ⊤
  have hk := kappa.smooth ⊤
  have hz : ContDiff ℝ ∞ (collarZ434 h t) := by
    unfold collarZ434
    fun_prop
  unfold sourceCompactCollarSymbol434
  exact (hc.mul (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp
    (contDiff_neg)))).mul (hk.comp hz)

 theorem source_compact_collar_symbol_compact434
    (chi kappa : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (chi : ℝ → ℂ)) (h t : ℝ) :
    HasCompactSupport (sourceCompactCollarSymbol434 chi kappa h t) := by
  exact (hc.mul_right).mul_right

noncomputable def sourceCompactCollarSymbolSchwartz434
    (chi kappa : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (chi : ℝ → ℂ)) (h t : ℝ) : 𝓢(ℝ,ℂ) :=
  (source_compact_collar_symbol_compact434 chi kappa hc h t).toSchwartzMap
    (source_compact_collar_symbol_smooth434 chi kappa h t)

 theorem source_compact_collar_symbol_first434 (chi kappa : 𝓢(ℝ,ℂ)) (h t u : ℝ) :
    HasDerivAt (sourceCompactCollarSymbol434 chi kappa h t)
      ((Real.exp (-u) : ℂ) *
        ((collarD434 chi u - chi u) * kappa (collarZ434 h t u) -
          chi u * (collarZ434 h t u : ℂ) * collarD434 kappa (collarZ434 h t u))) u := by
  have he := ((Real.hasDerivAt_exp (-u)).comp u ((hasDerivAt_id u).neg)).ofReal_comp
  have hk := (collar_schwartz_hasDerivAt434 kappa (collarZ434 h t u)).scomp u
    (collar_z_hasDerivAt434 h t u)
  convert ((collar_schwartz_hasDerivAt434 chi u).mul he).mul hk using 1
  · funext x; rfl
  · simp only [Pi.mul_apply, Function.comp_def, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_one, Complex.real_smul]
    ring

noncomputable def sourceCompactCollarFirst434 (chi kappa : 𝓢(ℝ,ℂ)) (h t u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) *
    ((collarD434 chi u - chi u) * kappa (collarZ434 h t u) -
      chi u * (collarZ434 h t u : ℂ) * collarD434 kappa (collarZ434 h t u))
noncomputable def sourceCompactCollarSecond434 (chi kappa : 𝓢(ℝ,ℂ)) (h t u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) *
    ((collarD434 (collarD434 chi) u - 2*collarD434 chi u + chi u) * kappa (collarZ434 h t u) +
      (3*chi u - 2*collarD434 chi u) * (collarZ434 h t u : ℂ) *
        collarD434 kappa (collarZ434 h t u) +
      chi u * (collarZ434 h t u : ℂ)^2 * collarD434 (collarD434 kappa) (collarZ434 h t u))

 theorem source_compact_collar_symbol_deriv434 (chi kappa : 𝓢(ℝ,ℂ)) (h t : ℝ) :
    deriv (sourceCompactCollarSymbol434 chi kappa h t) = sourceCompactCollarFirst434 chi kappa h t := by
  funext u
  exact (source_compact_collar_symbol_first434 chi kappa h t u).deriv

 theorem source_compact_collar_symbol_second434 (chi kappa : 𝓢(ℝ,ℂ)) (h t u : ℝ) :
    HasDerivAt (sourceCompactCollarFirst434 chi kappa h t)
      (sourceCompactCollarSecond434 chi kappa h t u) u := by
  have he := ((Real.hasDerivAt_exp (-u)).comp u ((hasDerivAt_id u).neg)).ofReal_comp
  have hz := (collar_z_hasDerivAt434 h t u).ofReal_comp
  have hk := (collar_schwartz_hasDerivAt434 kappa (collarZ434 h t u)).scomp u
    (collar_z_hasDerivAt434 h t u)
  have hdk := (collar_schwartz_hasDerivAt434 (collarD434 kappa) (collarZ434 h t u)).scomp u
    (collar_z_hasDerivAt434 h t u)
  have hc := collar_schwartz_hasDerivAt434 chi u
  have hdc := collar_schwartz_hasDerivAt434 (collarD434 chi) u
  convert he.mul (((hdc.sub hc).mul hk).sub ((hc.mul hz).mul hdk)) using 1
  · funext x; rfl
  · simp only [sourceCompactCollarSecond434, Pi.mul_apply, Pi.sub_apply, Function.comp_def,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one, Complex.real_smul]
    ring

 theorem source_compact_collar_symbol_second_deriv434 (chi kappa : 𝓢(ℝ,ℂ)) (h t : ℝ) :
    deriv (deriv (sourceCompactCollarSymbol434 chi kappa h t)) =
      sourceCompactCollarSecond434 chi kappa h t := by
  rw [source_compact_collar_symbol_deriv434]
  funext u
  exact (source_compact_collar_symbol_second434 chi kappa h t u).deriv

 theorem source_compact_collar_symbol_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (chi : ℝ → ℂ)) (h t : ℝ) :
    Integrable (sourceCompactCollarSymbol434 chi kappa h t) :=
  (sourceCompactCollarSymbolSchwartz434 chi kappa hc h t).integrable

 theorem collar_fourier_derivative434 (f : 𝓢(ℝ,ℂ)) (s : ℝ) :
    (𝓕 (collarD434 f)) s = (2*(Real.pi : ℂ)*Complex.I*(s : ℂ)) * (𝓕 f) s := by
  have hD : (collarD434 f : ℝ → ℂ) = deriv (f : ℝ → ℂ) :=
    funext (collarD434_apply f)
  have hi : Integrable (deriv (f : ℝ → ℂ)) := by
    rw [← hD]
    exact (collarD434 f).integrable
  have he := congrFun (Real.fourier_deriv f.integrable
    ((f.smooth 1).differentiable (by norm_num)) hi) s
  rw [← hD, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe] at he
  simpa only [smul_eq_mul] using he

 theorem collar_fourier_twice_derivative434 (f : 𝓢(ℝ,ℂ)) (s : ℝ) :
    (𝓕 (collarD434 (collarD434 f))) s =
      (2*(Real.pi : ℂ)*Complex.I*(s : ℂ))^2 * (𝓕 f) s := by
  rw [collar_fourier_derivative434,collar_fourier_derivative434]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCollarUniformDecay -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1500000

/-- Every Schwartz derivative component has a fixed polynomially weighted bound. -/
theorem collar_schwartz_weighted_bound434 (f : 𝓢(ℝ,ℂ)) (j r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, (1+|z|)^j * |z|^r * ‖f z‖ ≤ C := by
  obtain ⟨C0,hC0,h0⟩ := f.decay r 0
  obtain ⟨C1,hC1,h1⟩ := f.decay (j+r) 0
  have hz0 (z : ℝ) : |z|^r * ‖f z‖ ≤ C0 := by
    simpa using h0 z
  have hz1 (z : ℝ) : |z|^(j+r) * ‖f z‖ ≤ C1 := by
    simpa using h1 z
  refine ⟨2^j*(C0+C1),by positivity,?_⟩
  intro z
  by_cases hz : |z| ≤ 1
  · have hp : (1+|z|)^j ≤ (2:ℝ)^j := pow_le_pow_left₀ (by positivity) (by linarith) j
    calc
      _ ≤ 2^j * (|z|^r * ‖f z‖) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ 2^j*C0 := mul_le_mul_of_nonneg_left (hz0 z) (by positivity)
      _ ≤ _ := by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) j]
  · have hp : (1+|z|)^j ≤ (2*|z|)^j := pow_le_pow_left₀ (by positivity) (by linarith) j
    calc
      _ ≤ (2*|z|)^j * |z|^r * ‖f z‖ := by gcongr
      _ = 2^j * (|z|^(j+r)*‖f z‖) := by rw [mul_pow,pow_add]; ring
      _ ≤ 2^j*C1 := mul_le_mul_of_nonneg_left (hz1 z) (by positivity)
      _ ≤ _ := by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) j]

/-- Compact logarithmic centers preserve decay uniformly in h and t.
This covers kappa, z*kappa', and z^2*kappa'' by choosing f and r. -/
theorem collar_scaled_schwartz_weighted_bound434
    (f : 𝓢(ℝ,ℂ)) (B : ℝ) (j r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h t u : ℝ, |u| ≤ B →
      (1+|h*t|)^j * |collarZ434 h t u|^r * ‖f (collarZ434 h t u)‖ ≤ C := by
  obtain ⟨C0,hC0,h0⟩ := collar_schwartz_weighted_bound434 f j r
  let c : ℝ := 1+2*Real.pi*Real.exp B
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c^j*C0,by positivity,?_⟩
  intro h t u hu
  have he : Real.exp u ≤ Real.exp B := Real.exp_le_exp.mpr ((le_abs_self u).trans hu)
  have hid : h*t = (2*Real.pi*Real.exp u)*collarZ434 h t u := by
    unfold collarZ434
    rw [Real.exp_neg]
    field_simp
  have hscale : |h*t| ≤ (2*Real.pi*Real.exp B)*|collarZ434 h t u| := by
    rw [hid,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi*Real.exp u)]
    gcongr
  have hbase : 1+|h*t| ≤ c*(1+|collarZ434 h t u|) := by
    dsimp [c]
    nlinarith [Real.pi_pos,Real.exp_pos B,abs_nonneg (collarZ434 h t u)]
  have hp : (1+|h*t|)^j ≤ c^j*(1+|collarZ434 h t u|)^j := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbase j
  calc
    _ ≤ (c^j*(1+|collarZ434 h t u|)^j) * |collarZ434 h t u|^r *
      ‖f (collarZ434 h t u)‖ := by gcongr
    _ = c^j*((1+|collarZ434 h t u|)^j * |collarZ434 h t u|^r *
      ‖f (collarZ434 h t u)‖) := by ring
    _ ≤ c^j*C0 := mul_le_mul_of_nonneg_left (h0 _) (pow_nonneg hc.le j)

noncomputable def collarComponent434 (g f : 𝓢(ℝ,ℂ)) (r : ℕ) (h t u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * g u * (collarZ434 h t u : ℂ)^r * f (collarZ434 h t u)

 theorem collar_component_uniform434 (g f : 𝓢(ℝ,ℂ)) (B : ℝ) (j r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h t u : ℝ, |u| ≤ B →
      (1+|h*t|)^j * ‖collarComponent434 g f r h t u‖ ≤ C := by
  obtain ⟨C0,hC0,h0⟩ := collar_scaled_schwartz_weighted_bound434 f B j r
  let G : ℝ := 1+(SchwartzMap.seminorm ℝ 0 0) g
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨Real.exp B*G*C0,by positivity,?_⟩
  intro h t u hu
  have he : Real.exp (-u) ≤ Real.exp B := Real.exp_le_exp.mpr ((neg_le_abs u).trans hu)
  have hg : ‖g u‖ ≤ G := (SchwartzMap.norm_le_seminorm ℝ g u).trans (by dsimp [G]; linarith)
  have hh := h0 h t u hu
  have hn : ‖collarComponent434 g f r h t u‖ =
      Real.exp (-u)*‖g u‖*|collarZ434 h t u|^r*‖f (collarZ434 h t u)‖ := by
    simp only [collarComponent434,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (-u))]
  rw [hn]
  calc
    _ = (Real.exp (-u)*‖g u‖)*
      ((1+|h*t|)^j*|collarZ434 h t u|^r*‖f (collarZ434 h t u)‖) := by ring
    _ ≤ (Real.exp B*G)*C0 := by gcongr
    _ = _ := by ring

 theorem source_compact_collar_symbol_uniform434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h t u : ℝ, |u| ≤ B →
      (1+|h*t|)^j * ‖sourceCompactCollarSymbol434 chi kappa h t u‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := collar_component_uniform434 chi kappa B j 0
  refine ⟨C,hC,?_⟩
  intro v t u hu
  simpa [collarComponent434,sourceCompactCollarSymbol434,mul_comm,mul_left_comm,mul_assoc]
    using h v t u hu

 theorem source_compact_collar_first_uniform434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h t u : ℝ, |u| ≤ B →
      (1+|h*t|)^j * ‖sourceCompactCollarFirst434 chi kappa h t u‖ ≤ C := by
  let g0 : 𝓢(ℝ,ℂ) := collarD434 chi - chi
  obtain ⟨C0,hC0,h0⟩ := collar_component_uniform434 g0 kappa B j 0
  obtain ⟨C1,hC1,h1⟩ := collar_component_uniform434 chi (collarD434 kappa) B j 1
  refine ⟨C0+C1,by positivity,?_⟩
  intro h t u hu
  have hid : sourceCompactCollarFirst434 chi kappa h t u =
      collarComponent434 g0 kappa 0 h t u - collarComponent434 chi (collarD434 kappa) 1 h t u := by
    simp [sourceCompactCollarFirst434,collarComponent434,g0]
    ring
  rw [hid]
  have hn := norm_sub_le (collarComponent434 g0 kappa 0 h t u)
    (collarComponent434 chi (collarD434 kappa) 1 h t u)
  have hm := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (1+|h*t|)^j)
  have ha := h0 h t u hu
  have hb := h1 h t u hu
  nlinarith

 theorem source_compact_collar_second_uniform434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h t u : ℝ, |u| ≤ B →
      (1+|h*t|)^j * ‖sourceCompactCollarSecond434 chi kappa h t u‖ ≤ C := by
  let g0 : 𝓢(ℝ,ℂ) := collarD434 (collarD434 chi) - (2:ℂ) • collarD434 chi + chi
  let g1 : 𝓢(ℝ,ℂ) := (3:ℂ) • chi - (2:ℂ) • collarD434 chi
  obtain ⟨C0,hC0,h0⟩ := collar_component_uniform434 g0 kappa B j 0
  obtain ⟨C1,hC1,h1⟩ := collar_component_uniform434 g1 (collarD434 kappa) B j 1
  obtain ⟨C2,hC2,h2⟩ := collar_component_uniform434 chi (collarD434 (collarD434 kappa)) B j 2
  refine ⟨C0+C1+C2,by positivity,?_⟩
  intro h t u hu
  have hid : sourceCompactCollarSecond434 chi kappa h t u =
      collarComponent434 g0 kappa 0 h t u + collarComponent434 g1 (collarD434 kappa) 1 h t u +
        collarComponent434 chi (collarD434 (collarD434 kappa)) 2 h t u := by
    simp [sourceCompactCollarSecond434,collarComponent434,g0,g1]
    ring
  rw [hid]
  have hn := (norm_add_le (collarComponent434 g0 kappa 0 h t u +
      collarComponent434 g1 (collarD434 kappa) 1 h t u)
      (collarComponent434 chi (collarD434 (collarD434 kappa)) 2 h t u)).trans
        (add_le_add (norm_add_le _ _) le_rfl)
  have hm := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (1+|h*t|)^j)
  have ha := h0 h t u hu
  have hb := h1 h t u hu
  have hc := h2 h t u hu
  nlinarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCollarFourierDecay -/

section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1500000

 theorem collar_fourier_norm434 (f : 𝓢(ℝ,ℂ)) (s : ℝ) :
    ‖(𝓕 f) s‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  simpa only [norm_smul, Complex.norm_exp_ofReal_mul_I,one_mul] using
    norm_integral_le_integral_norm (fun u : ℝ =>
      Complex.exp (((-2*Real.pi*⟪u,s⟫ : ℝ) : ℂ)*Complex.I) • f u)

 theorem collar_compact_weighted_integral434
    (f : 𝓢(ℝ,ℂ)) (B W C : ℝ) (hB : 0 ≤ B) (_hW : 0 ≤ W) (_hC : 0 ≤ C)
    (hSupport : Function.support (f : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (hBound : ∀ u ∈ Set.Icc (-B) B, W*‖f u‖ ≤ C) :
    W*(∫ u : ℝ, ‖f u‖) ≤ 2*B*C := by
  let S : Set ℝ := Set.Icc (-B) B
  have hi : Integrable (S.indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (s:=S) (by dsimp [S]; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hp : ∀ u : ℝ, W*‖f u‖ ≤ S.indicator (fun _ => C) u := by
    intro u
    by_cases hu : u ∈ S
    · simpa only [Set.indicator_of_mem hu] using hBound u hu
    · have hf : f u = 0 := by
        by_contra hn
        exact hu (hSupport hn)
      simp [hf,Set.indicator_of_notMem hu]
  calc
    _ = ∫ u : ℝ, W*‖f u‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ u : ℝ, S.indicator (fun _ => C) u := integral_mono (f.integrable.norm.const_mul W) hi hp
    _ = 2*B*C := by
      rw [integral_indicator_const C measurableSet_Icc]
      simp only [Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ B- -B), smul_eq_mul]
      ring

 theorem source_compact_collar_schwartz_second434
    (chi kappa : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (chi : ℝ → ℂ)) (h t : ℝ) :
    (collarD434 (collarD434 (sourceCompactCollarSymbolSchwartz434 chi kappa hc h t)) : ℝ → ℂ) =
      sourceCompactCollarSecond434 chi kappa h t := by
  have he := source_compact_collar_symbol_second_deriv434 chi kappa h t
  calc
    _ = deriv (deriv (sourceCompactCollarSymbol434 chi kappa h t)) := by
      funext u
      rw [collarD434_apply]
      have hd : (collarD434 (sourceCompactCollarSymbolSchwartz434 chi kappa hc h t) : ℝ → ℂ) =
          deriv (sourceCompactCollarSymbol434 chi kappa h t) := by
        funext v
        exact collarD434_apply _ v
      rw [hd]
    _ = _ := he

/-- Uniform compact-source L1 budgets needed for twice integration by parts.
The budgets are derived from the literal symbol, not assumed as energy premises. -/
theorem source_compact_collar_uniform_integrals434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h t : ℝ,
      (1+|h*t|)^j * (∫ u : ℝ, ‖sourceCompactCollarSymbol434 chi kappa h t u‖) ≤ C ∧
      (1+|h*t|)^j * (∫ u : ℝ, ‖sourceCompactCollarSecond434 chi kappa h t u‖) ≤ C := by
  have hc : HasCompactSupport (chi : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (subset_closure.trans hchi)
  obtain ⟨C0,hC0,h0⟩ := source_compact_collar_symbol_uniform434 chi kappa B j
  obtain ⟨C2,hC2,h2⟩ := source_compact_collar_second_uniform434 chi kappa B j
  refine ⟨2*B*(C0+C2),by positivity,?_⟩
  intro h t
  let f := sourceCompactCollarSymbolSchwartz434 chi kappa hc h t
  have hs : Function.support (f : ℝ → ℂ) ⊆ Set.Icc (-B) B := by
    intro u hu
    have hn : chi u ≠ 0 := by
      intro hn
      exact hu (by simp [f,sourceCompactCollarSymbolSchwartz434,sourceCompactCollarSymbol434,hn])
    exact hchi (subset_closure hn)
  have ht : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-B) B := closure_minimal hs isClosed_Icc
  have hs2 : Function.support (collarD434 (collarD434 f) : ℝ → ℂ) ⊆ Set.Icc (-B) B := by
    have hd : (collarD434 f : ℝ → ℂ) = deriv (f : ℝ → ℂ) := funext (collarD434_apply f)
    have hd2 : (collarD434 (collarD434 f) : ℝ → ℂ) = deriv (collarD434 f : ℝ → ℂ) :=
      funext (collarD434_apply (collarD434 f))
    rw [hd2,hd]
    exact support_deriv_subset.trans (tsupport_deriv_subset.trans ht)
  have hi0 := collar_compact_weighted_integral434 f B ((1+|h*t|)^j) C0 hB.le
    (by positivity) hC0.le hs (fun u hu => h0 h t u (by simpa [abs_le] using hu))
  have hd2 := source_compact_collar_schwartz_second434 chi kappa hc h t
  have hi2 := collar_compact_weighted_integral434 (collarD434 (collarD434 f)) B ((1+|h*t|)^j) C2
    hB.le (by positivity) hC2.le hs2 (by
      intro u hu
      change (1+|h*t|)^j * ‖collarD434 (collarD434 (sourceCompactCollarSymbolSchwartz434 chi kappa hc h t)) u‖ ≤ C2
      rw [congrFun hd2 u]
      exact h2 h t u (by simpa [abs_le] using hu))
  constructor
  · exact hi0.trans (by nlinarith)
  · simpa only [f,hd2] using hi2.trans (by nlinarith : 2*B*C2 ≤ 2*B*(C0+C2))

/-- Actual compact logarithmic source amplitude: two IBPs, with a constant
independent of h,t,s. Angular time is retained; s is cycle-normalized Fourier frequency. -/
theorem source_compact_collar_fourier_uniform434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h t s : ℝ,
      (1+|s|)^2 * (1+|h*t|)^j *
        ‖𝓕 (sourceCompactCollarSymbol434 chi kappa h t) s‖ ≤ C := by
  have hc : HasCompactSupport (chi : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (subset_closure.trans hchi)
  obtain ⟨C0,hC0,h0⟩ := source_compact_collar_uniform_integrals434 chi kappa B hB hchi j
  let q : ℝ := (2*Real.pi)^2
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨2*(q+1)*C0/q,by positivity,?_⟩
  intro h t s
  let f := sourceCompactCollarSymbolSchwartz434 chi kappa hc h t
  let W : ℝ := (1+|h*t|)^j
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hf0 : W*‖(𝓕 f) s‖ ≤ C0 :=
    (mul_le_mul_of_nonneg_left (collar_fourier_norm434 f s) hW).trans (h0 h t).1
  have hd2 := source_compact_collar_schwartz_second434 chi kappa hc h t
  have hf2 : W*‖(𝓕 (collarD434 (collarD434 f))) s‖ ≤ C0 := by
    have he := mul_le_mul_of_nonneg_left (collar_fourier_norm434 (collarD434 (collarD434 f)) s) hW
    have hi : W*(∫ u : ℝ, ‖collarD434 (collarD434 f) u‖) ≤ C0 := by
      simpa only [f,hd2] using (h0 h t).2
    exact he.trans hi
  have hn : ‖(𝓕 (collarD434 (collarD434 f))) s‖ = q*s^2*‖(𝓕 f) s‖ := by
    rw [collar_fourier_twice_derivative434]
    simp only [norm_mul,norm_pow,Complex.norm_real,Complex.norm_I,Complex.norm_ofNat,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_one]
    dsimp [q]
    rw [mul_pow, mul_pow,sq_abs]
  rw [hn] at hf2
  have hg : 0 ≤ W*‖(𝓕 f) s‖ := mul_nonneg hW (norm_nonneg _)
  have hcomb : (1+s^2)*(W*‖(𝓕 f) s‖) ≤ (q+1)*C0/q := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  have hab : (1+|s|)^2 ≤ 2*(1+s^2) := by nlinarith [sq_nonneg (|s|-1),sq_abs s]
  have hfin := mul_le_mul_of_nonneg_right hab hg
  change (1+|s|)^2 * W * ‖𝓕 (sourceCompactCollarSymbol434 chi kappa h t) s‖ ≤ _
  have he : (𝓕 f) s = 𝓕 (sourceCompactCollarSymbol434 chi kappa h t) s := by
    exact congrFun (SchwartzMap.fourier_coe f) s
  rw [← he]
  calc
    _ = (1+|s|)^2 * (W*‖(𝓕 f) s‖) := by ring
    _ ≤ 2*((1+s^2)*(W*‖(𝓕 f) s‖)) := by nlinarith only [hfin]
    _ ≤ 2*((q+1)*C0/q) := mul_le_mul_of_nonneg_left hcomb (by norm_num)
    _ = _ := by ring

/-- Literal source Khat specialization, without any physical energy assumption. -/
theorem source_original_collar_amplitude_uniform434
    (chi K : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h t s : ℝ, 0 ≤ h →
      (1+|s|)^2 * (1+h*|t|)^j *
        ‖𝓕 (fun u : ℝ => chi u * (Real.exp (-u) : ℂ) *
          (𝓕 K) (h*Real.exp (-u)*t/(2*Real.pi))) s‖ ≤ C := by
  obtain ⟨C,hC,hc⟩ := source_compact_collar_fourier_uniform434 chi (𝓕 K) B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h t s hh
  change (1+|s|)^2 * (1+h*|t|)^j * ‖𝓕 (sourceCompactCollarSymbol434 chi (𝓕 K) h t) s‖ ≤ C
  simpa only [abs_mul,abs_of_nonneg hh] using hc h t s
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCollarSchurRows -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1000000

/-- The precise cycle-normalized, twice-IBP majorant. -/
noncomputable def collarSchurWeight434 (s : ℝ) : ℝ := ((1 + |s|)^2)⁻¹

theorem collar_schur_weight_nonneg434 (s : ℝ) : 0 ≤ collarSchurWeight434 s := by
  unfold collarSchurWeight434
  positivity

theorem collar_schur_weight_le_one434 (s : ℝ) : collarSchurWeight434 s ≤ 1 := by
  unfold collarSchurWeight434
  have hp : 1 ≤ (1 + |s|)^2 := by nlinarith [abs_nonneg s]
  exact (inv_le_one₀ (by positivity)).mpr hp

theorem collar_schur_weight_integrable434 : Integrable collarSchurWeight434 := by
  apply Integrable.mono' integrable_inv_one_add_sq
  · have hm : Measurable collarSchurWeight434 := by
      unfold collarSchurWeight434
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards with s
    have hp : 1+s^2 ≤ (1+|s|)^2 := by nlinarith [sq_abs s, abs_nonneg s]
    have hi : ((1+|s|)^2)⁻¹ ≤ (1+s^2)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr hp
    change |((1+|s|)^2)⁻¹| ≤ (1+s^2)⁻¹
    rwa [abs_of_nonneg (by positivity)]

/-- Both Schur row integrals are one and the same finite constant. -/
theorem collar_schur_weight_shift434 (a : ℝ) :
    Integrable (fun s : ℝ => collarSchurWeight434 (s+a)) ∧
    (∫ s : ℝ, collarSchurWeight434 (s+a)) =
       ∫ s : ℝ, collarSchurWeight434 s := by
  exact ⟨collar_schur_weight_integrable434.comp_add_right a,
    integral_add_right_eq_self collarSchurWeight434 a⟩

/-- Absolute Gram majorant for every pair of real frequency shifts. -/
theorem collar_schur_gram_integrable434 (a b : ℝ) :
    Integrable (fun s : ℝ =>
      collarSchurWeight434 (s+a) * collarSchurWeight434 (s+b)) := by
  apply Integrable.mono' (collar_schur_weight_shift434 a).1
  · have hm : Measurable (fun s : ℝ =>
        collarSchurWeight434 (s+a) * collarSchurWeight434 (s+b)) := by
      unfold collarSchurWeight434
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards with s
    change |collarSchurWeight434 (s+a)*collarSchurWeight434 (s+b)| ≤
      collarSchurWeight434 (s+a)
    rw [abs_of_nonneg (mul_nonneg
      (collar_schur_weight_nonneg434 (s+a))
      (collar_schur_weight_nonneg434 (s+b)))]
    exact mul_le_of_le_one_right
      (collar_schur_weight_nonneg434 (s+a))
      (collar_schur_weight_le_one434 (s+b))

end Green64Analytic.CorrelationSquare

end

