module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part016
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Inversion / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Inversion.ClippingProfiles -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
namespace SevenEighths.InverseClippingProfiles

def logWindow (v : ℝ → ℂ) (L ρ : ℝ) (y : ℝ) : ℂ := v ((y + ρ) / L)

def rootedWindow (v : ℝ → ℂ) (L ρ a H : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (a * y - H * L) : ℂ) * logWindow v L ρ y

lemma logWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ : ℝ) :
    ContDiff ℝ ∞ (logWindow v L ρ) := by
  exact hv.comp ((contDiff_id.add contDiff_const).div_const L)

lemma rootedWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ a H : ℝ) :
    ContDiff ℝ ∞ (rootedWindow v L ρ a H) := by
  apply ContDiff.mul _ (logWindow_contDiff v hv L ρ)
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma logWindow_iteratedDeriv (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v)
    (L ρ : ℝ) (n : ℕ) :
    iteratedDeriv n (logWindow v L ρ) =
      fun y => (L⁻¹)^n • iteratedDeriv n v ((y + ρ) / L) := by
  have h : (logWindow v L ρ) =
      fun y => (fun z => v (L⁻¹ * z)) (y + ρ) := by
    funext y
    simp only [logWindow, div_eq_mul_inv, mul_comm]
  rw [h, iteratedDeriv_comp_add_const n (fun z => v (L⁻¹ * z)) ρ,
    iteratedDeriv_comp_const_smul (hv.of_le (by simp))]
  simp only [div_eq_mul_inv, mul_comm]

lemma expAffine_iteratedDeriv (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => (Real.exp (a * y + b) : ℂ)) =
      fun y => (a : ℂ)^n * (Real.exp (a * y + b) : ℂ) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h := (((hasDerivAt_id y).const_mul a).add_const b).exp
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y h).const_mul ((a : ℂ)^n)
    simp only [Function.comp_def, id_eq, Complex.ofRealCLM_apply] at hc
    rw [hc.deriv]
    simp only [mul_one, Complex.ofReal_mul, pow_succ]
    ring

lemma logWindow_support (v : ℝ → ℂ) (M B L ρ : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    Function.support (logWindow v L ρ) ⊆ Set.Icc (-(M+B)*L) ((M+B)*L) := by
  intro y hy
  have hy' := hv hy
  change -M ≤ (y+ρ)/L ∧ (y+ρ)/L ≤ M at hy'
  have hl := (le_div_iff₀ hL).mp hy'.1
  have hu := (div_le_iff₀ hL).mp hy'.2
  have hr := abs_le.mp hρ
  constructor <;> nlinarith

lemma rootedWindow_compact (v : ℝ → ℂ) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    HasCompactSupport (rootedWindow v L ρ a H) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro y hy
  apply logWindow_support v M B L ρ hL hρ hv
  exact (mul_ne_zero_iff.mp hy).2

def rootSchwartz (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  (rootedWindow_compact v M B L ρ a H hL hρ hv).toSchwartzMap
    (rootedWindow_contDiff v (v.smooth ⊤) L ρ a H)

@[simp] lemma rootSchwartz_apply (v : 𝓢(ℝ, ℂ)) (M B L ρ a H y : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    rootSchwartz v M B L ρ a H hL hρ hv y = rootedWindow v L ρ a H y := rfl

lemma derivative_support (v : 𝓢(ℝ, ℂ)) (M : ℝ)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (n : ℕ) :
    Function.support (iteratedDeriv n v) ⊆ Set.Icc (-M) M :=
  (subset_tsupport _).trans
    ((CompactProfileFamily.tsupport_iteratedDeriv_subset v n).trans
      (closure_minimal hv isClosed_Icc))

lemma root_exp_le_one (a H M B L ρ y : ℝ)
    (hL : 0 ≤ L) (hρ : |ρ| ≤ B*L) (hy : |(y+ρ)/L| ≤ M)
    (hL0 : L ≠ 0) (hH : |a| *(M+B) ≤ H) :
    Real.exp (a*y-H*L) ≤ 1 := by
  have hs : |y| ≤ (M+B)*L := by
    have h := (abs_le.mp hy)
    have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have h1 := (le_div_iff₀ hLp).mp h.1
    have h2 := (div_le_iff₀ hLp).mp h.2
    have hr := abs_le.mp hρ
    apply abs_le.mpr
    constructor <;> nlinarith
  have ha := le_abs_self (a*y)
  rw [abs_mul] at ha
  have hh := mul_le_mul_of_nonneg_left hs (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_right hH hL
  apply Real.exp_le_one_iff.mpr
  nlinarith

lemma expAffine_iteratedFDeriv_norm (a b y : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ => (Real.exp (a*x+b) : ℂ)) y‖ =
      |a|^n * Real.exp (a*y+b) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, expAffine_iteratedDeriv]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem rootSchwartz_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
        (rootSchwartz v M B L ρ a H (by linarith) hρ hv) ≤
      ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n * derivativeSeminormSum v 0 n := by
  have hLp : 0 < L := by linarith
  have hC : 0 ≤ ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n *
      derivativeSeminormSum v 0 n := by
    apply mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hC
  intro y
  have hbase (j : ℕ) (hj : j ≤ n) :
      ‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ j (logWindow v L ρ) y‖ ≤
        ((M+B)*L)^k * derivativeSeminormSum v 0 n := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logWindow_iteratedDeriv v (v.smooth ⊤)]
    by_cases hz : iteratedDeriv j v ((y+ρ)/L) = 0
    · simp only [hz, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
    have harg := derivative_support v M hv j hz
    have hy : |(y+ρ)/L| ≤ M := abs_le.mpr harg
    have he := root_exp_le_one a H M B L ρ y hLp.le hρ hy (ne_of_gt hLp) hH
    have hx : ‖y‖ ≤ (M+B)*L := by
      have ht := logWindow_support (iteratedDeriv j v) M B L ρ hLp hρ
        (derivative_support v M hv j) hz
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2]
    have hd : ‖iteratedDeriv j v ((y+ρ)/L)‖ ≤ derivativeSeminormSum v 0 n := by
      have hh := (SchwartzMap.le_seminorm ℝ 0 j v ((y+ρ)/L)).trans
        (seminorm_le_derivativeSeminormSum v 0 n j hj)
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hh
    have hi : ‖L⁻¹‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
      exact inv_le_one_of_one_le₀ hL
    have hs : ‖(L⁻¹)^j • iteratedDeriv j v ((y+ρ)/L)‖ ≤
        derivativeSeminormSum v 0 n := by
      rw [norm_smul, norm_pow]
      calc
        _ ≤ 1 * ‖iteratedDeriv j v ((y+ρ)/L)‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hi
        _ ≤ _ := by simpa using hd
    calc
      _ ≤ ((M+B)*L)^k * 1 * derivativeSeminormSum v 0 n := by gcongr
      _ = _ := by ring
  have he : ContDiff ℝ ∞ (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  have hh := norm_iteratedFDeriv_mul_le he (logWindow_contDiff v (v.smooth ⊤) L ρ)
    y (n := n) (by exact_mod_cast le_top)
  change ‖y‖^k * ‖iteratedFDeriv ℝ n (rootedWindow v L ρ a H) y‖ ≤ _
  unfold rootedWindow
  calc
    _ ≤ ‖y‖^k * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) y‖ *
        ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * |a|^i *
        (‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) =
        (fun x : ℝ => (Real.exp (a*x+(-H*L)) : ℂ)) by ext x; congr 2; ring]
      rw [expAffine_iteratedFDeriv_norm]
      rw [show a*y+(-H*L) = a*y-H*L by ring]
      ring
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (1+|a|)^n *
        (((M+B)*L)^k * derivativeSeminormSum v 0 n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : |a|^i ≤ (1+|a|)^n := by
        calc
          _ ≤ (1+|a|)^i := by gcongr; linarith [abs_nonneg a]
          _ ≤ _ := pow_le_pow_right₀ (by linarith [abs_nonneg a])
            (Finset.mem_range_succ_iff.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity))
        (hbase (n-i) (Nat.sub_le _ _)) (by positivity) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

def rootDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (2:ℝ)^i * (1+|a|)^i * derivativeSeminormSum v 0 i

def twistedDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  (2:ℝ)^n * (1+2*Real.pi)^n * rootDerivativeBound v a n

lemma rootDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ rootDerivativeBound v a n := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)

lemma twistedDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ twistedDerivativeBound v a n :=
  mul_nonneg (by positivity) (rootDerivativeBound_nonneg _ _ _)

lemma rootSchwartz_derivativeSum (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n ≤
      ((M+B)*L)^k * rootDerivativeBound v a n := by
  unfold derivativeSeminormSum rootDerivativeBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  convert rootSchwartz_seminorm v M B L ρ a H hM hB hL hρ hv hH k i using 1
  ring

theorem rooted_twist_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
      (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      (M+B)^k * twistedDerivativeBound v a n * L^k * (1+‖θ‖)^n := by
  have hb := frequencyTwist_seminorm_polynomial
    (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ k n
  have hd := rootSchwartz_derivativeSum v M B L ρ a H hM hB hL hρ hv hH k n
  calc
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n) *
        (1+‖θ‖)^n := hb
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        (((M+B)*L)^k * rootDerivativeBound v a n)) * (1+‖θ‖)^n := by gcongr
    _ = _ := by unfold twistedDerivativeBound; rw [mul_pow]; ring

def momentOrder (J : ℕ) : ℕ := J + (volume : Measure ℝ).integrablePower

def windowSourceBound (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (1+(M+B)^(volume : Measure ℝ).integrablePower) *
    ∑ i ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a i

lemma windowSourceBound_nonneg (v : 𝓢(ℝ, ℂ)) (M B a : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (J : ℕ) : 0 ≤ windowSourceBound v M B a J := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)

theorem rooted_twist_moment_sources (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (J i : ℕ) (hi : i ≤ momentOrder J) :
    (SchwartzMap.seminorm ℝ 0 i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  let p := (volume : Measure ℝ).integrablePower
  have h0 := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH 0 i
  have hp := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH p i
  simp only [pow_zero, one_mul, mul_one] at h0
  have hs : twistedDerivativeBound v a i ≤
      ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j := by
    apply Finset.single_le_sum (fun j _ => twistedDerivativeBound_nonneg v a j)
    exact Finset.mem_range_succ_iff.mpr hi
  have hl : 1 ≤ L^p := one_le_pow₀ hL
  have ht : (1+‖θ‖)^i ≤ (1+‖θ‖)^(momentOrder J) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg θ]) hi
  have hc := twistedDerivativeBound_nonneg v a i
  have hsum : 0 ≤ ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j :=
    Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)
  calc
    _ ≤ twistedDerivativeBound v a i * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := add_le_add h0 hp
    _ ≤ twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by gcongr; nlinarith
    _ = (1+(M+B)^p) * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by ring
    _ ≤ _ := by unfold windowSourceBound; gcongr

lemma coefficientMomentBound_mul (J : ℕ) (C D : ℝ) :
    coefficientMomentBound J (C*D) = coefficientMomentBound J C * D := by
  unfold coefficientMomentBound
  ring

theorem rooted_twist_fourier_moment (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H) (J : ℕ) :
    (∫ t : ℝ, (1+‖t‖)^J *
      ‖(𝓕 (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ)) t‖) ≤
      ((2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
        coefficientMomentBound J (windowSourceBound v M B a J))) *
      L^(volume : Measure ℝ).integrablePower * (1+‖θ‖)^(momentOrder J) := by
  have hc := windowSourceBound_nonneg v M B a hM hB J
  have h := uniform_fourier_one_plus_moment
    (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) J 1
    (windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
      (1+‖θ‖)^(momentOrder J)) (by norm_num) (by positivity)
    (by
      intro i hi
      simpa using (rooted_twist_moment_sources v M B L ρ a H θ
        hM hB hL hρ hv hH J i hi))
  simp only [one_mul, coefficientMomentBound_mul] at h
  convert h using 1
  ring

theorem child_log_window_parameters (η Z δ : ℝ) (_hη : 0 ≤ η)
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    0 ≤ δ*Real.log Z ∧ |δ*Real.log Z| ≤ 6*(η*Real.log Z) := by
  have hz : 0 ≤ Real.log Z := Real.log_nonneg hZ
  constructor
  · positivity
  · rw [abs_of_nonneg (by positivity : 0 ≤ δ*Real.log Z)]
    nlinarith [mul_le_mul_of_nonneg_right hδu hz]

theorem clipping_ratio_of_column_witness (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q / Z^N) ≠ 0) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  have hz : 0 < Z := by linarith
  have hn : 0 ≤ max 0 N-N := sub_nonneg.mpr (le_max_right _ _)
  refine ⟨Real.one_le_rpow hZ.le hn, ?_⟩
  by_cases hN : 0 ≤ N
  · simpa [max_eq_right hN] using hb
  · have hN' : N ≤ 0 := le_of_lt (lt_of_not_ge hN)
    rw [max_eq_left hN', zero_sub, Real.rpow_neg hz.le]
    have hsupport := (hw hwitness).2
    calc
      _ = 1 / Z^N := (one_div _).symm
      _ ≤ q / Z^N := div_le_div_of_nonneg_right hq (Real.rpow_nonneg hz.le _)
      _ ≤ b := hsupport

theorem clipped_positive_support (w : ℝ → ℂ) (a b c : ℝ)
    (ha : 0 < a) (hc : 1 ≤ c) (hcb : c ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) :
    Function.support (fun y => w (c*y)) ⊆ Set.Icc (a/b) b := by
  intro y hy
  have hs := hw hy
  have hcp : 0 < c := by linarith
  have hbp : 0 < b := lt_of_lt_of_le hcp hcb
  have hyp : 0 < y := by nlinarith [hs.1]
  constructor
  · apply (div_le_iff₀ hbp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcb hyp.le, hs.1]
  · nlinarith [hs.2]

theorem clipped_log_source (w : ℝ → ℂ) (c y : ℝ) (hc : 0 < c) :
    w (c*Real.exp y) = (fun s => w (Real.exp s)) (y+Real.log c) := by
  change w (c*Real.exp y) = w (Real.exp (y+Real.log c))
  rw [Real.exp_add, Real.exp_log hc]
  congr 1
  ring

open InverseMoment

def firstRootExponent (y : Fin 9 → ℝ) : ℝ :=
  -y 3-y 4/2-y 5-(y 7+y 8)/2

def secondRootExponent (y : Fin 6 → ℝ) : ℝ :=
  -y 1-y 2-(y 4+y 5)/2

theorem first_root_coupled_identity (y : Fin 9 → ℝ) :
    firstRootExponent y = -y 3-y 4/2+(y 0+y 1)/2+y 2 -
      ((∑ i, firstLeftSlope i*y i)+(∑ i, firstRightSlope i*y i))/2 := by
  simp [firstRootExponent, firstLeftSlope, firstRightSlope, Fin.sum_univ_succ]
  ring

theorem second_root_coupled_identity (y : Fin 6 → ℝ) :
    secondRootExponent y = -y 1+y 0 -
      ((∑ i, secondLeftSlope i*y i)+(∑ i, secondRightSlope i*y i))/2 := by
  simp [secondRootExponent, secondLeftSlope, secondRightSlope, Fin.sum_univ_succ]
  ring

theorem first_root_budget (y : Fin 9 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L) (h2 : |y 2| ≤ L)
    (h3 : |y 3| ≤ L) (h4 : |y 4| ≤ L)
    (hl : |∑ i, firstLeftSlope i*y i| ≤ L)
    (hr : |∑ i, firstRightSlope i*y i| ≤ L) :
    firstRootExponent y ≤ (9/2:ℝ)*L := by
  rw [first_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨_, h1⟩
  rcases abs_le.mp h2 with ⟨_, h2⟩
  rcases abs_le.mp h3 with ⟨h3, _⟩
  rcases abs_le.mp h4 with ⟨h4, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

theorem second_root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L)
    (hl : |∑ i, secondLeftSlope i*y i| ≤ 4*L)
    (hr : |∑ i, secondRightSlope i*y i| ≤ 4*L) :
    secondRootExponent y ≤ 6*L := by
  rw [second_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨h1, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

def firstRootSlope : Fin 9 → ℝ := ![0,0,0,-1,-(1/2),-1,0,-(1/2),-(1/2)]
def secondRootSlope : Fin 6 → ℝ := ![0,-1,-1,0,-(1/2),-(1/2)]

lemma inverseNormWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseNormWindow V y = (Real.exp (-y) : ℂ)*V y := by
  simp only [inverseNormWindow, Real.exp_neg, Complex.ofReal_inv, div_eq_mul_inv]
  ring

lemma inverseRootWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseRootWindow V y = (Real.exp (-(y/2)) : ℂ)*V y := by
  rw [inverseRootWindow, ← Real.exp_half, Real.exp_neg, Complex.ofReal_inv]
  ring

theorem firstRootWindows_exp (V : Fin 9 → ℝ → ℂ) (i : Fin 9) (y : ℝ) :
    firstRootWindows V i y = (Real.exp (firstRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [firstRootWindows, firstRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem secondRootWindows_exp (V : Fin 6 → ℝ → ℂ) (i : Fin 6) (y : ℝ) :
    secondRootWindows V i y = (Real.exp (secondRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [secondRootWindows, secondRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem firstRootWindows_prod (V : Fin 9 → ℝ → ℂ) (y : Fin 9 → ℝ) :
    (∏ i, firstRootWindows V i (y i)) =
      (Real.exp (firstRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [firstRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [firstRootSlope, firstRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem secondRootWindows_prod (V : Fin 6 → ℝ → ℂ) (y : Fin 6 → ℝ) :
    (∏ i, secondRootWindows V i (y i)) =
      (Real.exp (secondRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [secondRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [secondRootSlope, secondRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem first_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R L : ℝ) (y : Fin 9 → ℝ) :
    (Real.exp (-(9/2:ℝ)*L) : ℂ)*firstPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (firstRootExponent y-(9/2:ℝ)*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, firstLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, firstRightSlope i*y i)) *
      EisensteinSchwartzPoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, firstKernelSlope i*y i)) := by
  rw [firstPoissonProfile, firstRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem second_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    (Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (secondRootExponent y-6*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, secondLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, secondRightSlope i*y i)) *
      EisensteinSchwartzPoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, secondKernelSlope i*y i)) := by
  rw [secondPoissonProfile, secondRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem fourier_phase_shift (f : ℝ → ℂ) (θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f y)) t = (𝓕 f) (t-θ) := by
  simp only [Real.fourier_eq', logPhase, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translate (f : ℝ → ℂ) (ρ t : ℝ) :
    (𝓕 (fun y => f (y+ρ))) t = logPhase t ρ * (𝓕 f) t := by
  have h := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) f ρ) t
  change _ = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t at h
  have h' : (𝓕 (fun y => f (y+ρ))) t = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t := by
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, Function.comp_def, innerₗ_apply_apply] using h
  rw [h']
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, logPhase]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f (y+ρ))) t =
      logPhase (t-θ) ρ * (𝓕 f) (t-θ) := by
  rw [fourier_phase_shift, fourier_translate]

theorem norm_fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    ‖(𝓕 (fun y => logPhase θ y * f (y+ρ))) t‖ = ‖(𝓕 f) (t-θ)‖ := by
  rw [fourier_translated_twist, norm_mul, logPhase_norm, one_mul]

theorem rooted_family_fourier_joint_measurable (v : 𝓢(ℝ, ℂ)) (a H : ℝ) :
    StronglyMeasurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
      (𝓕 (fun y => logPhase p.1.2.2 y * rootedWindow v p.1.1 p.1.2.1 a H y)) p.2) := by
  apply InverseKernelSourceUniform.fourier_joint_stronglyMeasurable
    (fun q : ℝ × ℝ × ℝ => fun y => logPhase q.2.2 y * rootedWindow v q.1 q.2.1 a H y)
  apply Measurable.stronglyMeasurable
  change Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
    logPhase p.1.2.2 p.2 * ((Real.exp (a*p.2-H*p.1.1) : ℂ) *
      v ((p.2+p.1.2.1)/p.1.1)))
  have hp : Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ => logPhase p.1.2.2 p.2) := by
    unfold logPhase
    fun_prop
  exact hp.mul ((show Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
    (Real.exp (a*p.2-H*p.1.1) : ℂ)) by fun_prop).mul
      (v.continuous.measurable.comp (by fun_prop)))

def childWindowDensity (v : 𝓢(ℝ, ℂ)) (η Z δ θ t : ℝ) : ℂ :=
  (𝓕 (fun y => logPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)))) t

def windowMomentConstant (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
    coefficientMomentBound J (windowSourceBound v M B a J))

theorem childWindowDensity_moment (v : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (J : ℕ)
    (η Z δ θ : ℝ) (hη : 0 ≤ η) (hZ : 1 ≤ Z)
    (hL : 1 ≤ η*Real.log Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    Integrable (fun t : ℝ => (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ∧
    (∫ t : ℝ, (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ≤
      windowMomentConstant v M 6 0 J * (η*Real.log Z)^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  have hρ := (child_log_window_parameters η Z δ hη hZ hδ hδu).2
  let g := frequencyTwist (rootSchwartz v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0
    (by linarith) hρ hv) θ
  have he (t : ℝ) : childWindowDensity v η Z δ θ t = (𝓕 g) t := by
    rw [congrFun (SchwartzMap.fourier_coe g) t]
    unfold childWindowDensity
    have hg : (g : ℝ → ℂ) = fun y =>
        logPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)) := by
      funext y
      simp [g, frequencyTwist_apply, rootSchwartz_apply, rootedWindow, logWindow]
    rw [hg]
  simp_rw [he]
  refine ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable g J, ?_⟩
  exact rooted_twist_fourier_moment v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0 θ
    hM (by norm_num) hL hρ hv (by simp) J

theorem retained_clipped_column (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧
    Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
    ∀ θ t : ℝ,
      (𝓕 (fun y => logPhase θ y * w (c*Real.exp y))) t =
        logPhase (t-θ) (Real.log c) * (𝓕 (fun y => w (Real.exp y))) (t-θ) := by
  dsimp only
  have hc := clipping_ratio_of_column_witness w Z N q a b hZ hq hb hw hwitness
  refine ⟨hc.1, hc.2, clipped_positive_support w a b _ ha hc.1 hc.2 hw, ?_⟩
  intro θ t
  have he : (fun y => logPhase θ y * w (Z^(max 0 N-N)*Real.exp y)) =
      (fun y => logPhase θ y * (fun s => w (Real.exp s)) (y+Real.log (Z^(max 0 N-N)))) := by
    ext y
    rw [clipped_log_source w _ y (by linarith)]
  rw [he]
  exact fourier_translated_twist (fun s => w (Real.exp s)) (Real.log (Z^(max 0 N-N))) θ t

theorem translated_twist_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J *
        ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ≤
        C*(1+‖θ‖)^(momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseMoment.frequencyTwist_fourier_moment J g
  refine ⟨C, hC, ?_⟩
  intro ρ θ
  have he (t : ℝ) : ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖ =
      ‖(𝓕 (frequencyTwist g θ)) t‖ := by
    rw [norm_fourier_translated_twist, congrFun (SchwartzMap.fourier_coe _) t]
    have hf : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
      funext y
      exact frequencyTwist_apply g θ y
    rw [hf, fourier_phase_shift]
  simp_rw [he]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable _ _, hb θ⟩

theorem eventually_log_scale_pow_le (C η π : ℝ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hπ : 0 < π) (k : ℕ) :
    ∀ᶠ Z : ℝ in Filter.atTop, C*(η*Real.log Z)^k ≤ Z^π := by
  have h := (_root_.isLittleO_log_rpow_rpow_atTop (k:ℝ) hπ).const_mul_left (C*η^k)
  filter_upwards [h.bound (by norm_num : (0:ℝ) < 1),
    Filter.eventually_ge_atTop (1:ℝ)] with Z hZ hZ1
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hz : 0 ≤ Z := by linarith
  rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg hz π), one_mul] at hZ
  convert hZ using 1
  ring

def firstBalancedSlope : Fin 9 → ℝ := ![1/2,1/2,1,-1,-(1/2),0,0,0,0]
def secondBalancedSlope : Fin 6 → ℝ := ![1,-1,0,0,0,0]

theorem first_root_normalization_split (y : Fin 9 → ℝ) (L : ℝ) :
    Real.exp (firstRootExponent y-(9/2:ℝ)*L) =
      (∏ i, Real.exp (firstBalancedSlope i*y i-|firstBalancedSlope i| *L)) *
      Real.exp (-(∑ i, firstLeftSlope i*y i)/2-L/2) *
      Real.exp (-(∑ i, firstRightSlope i*y i)/2-L/2) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [firstRootExponent, firstBalancedSlope, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ]
  ring

theorem second_root_normalization_split (y : Fin 6 → ℝ) (L : ℝ) :
    Real.exp (secondRootExponent y-6*L) =
      (∏ i, Real.exp (secondBalancedSlope i*y i-|secondBalancedSlope i| *L)) *
      Real.exp (-(∑ i, secondLeftSlope i*y i)/2-2*L) *
      Real.exp (-(∑ i, secondRightSlope i*y i)/2-2*L) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [secondRootExponent, secondBalancedSlope, secondLeftSlope, secondRightSlope,
    Fin.sum_univ_succ]
  ring

end SevenEighths.InverseClippingProfiles

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialProfile -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment

namespace SevenEighths.InverseInitialProfile

def clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (SchwartzMap.compSubConstCLM ℂ (-Real.log c) g) θ

@[simp] theorem clippedTwist_apply (g : 𝓢(ℝ, ℂ)) (c θ y : ℝ) :
    clippedTwist g c θ y = logPhase θ y * g (y + Real.log c) := by
  simp [clippedTwist]

def sourceDensity (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) : ℂ :=
  logPhase (t-θ) (Real.log c) * (𝓕 g) (t-θ)

theorem fourier_clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    (𝓕 (clippedTwist g c θ)) t = sourceDensity g c θ t := by
  rw [SchwartzMap.fourier_coe]
  have he : (clippedTwist g c θ : ℝ → ℂ) =
      fun y => logPhase θ y * g (y + Real.log c) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translated_twist]
  rfl

theorem sourceDensity_joint_measurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ℝ => sourceDensity g p.1.1 p.1.2 p.2) := by
  unfold sourceDensity logPhase
  apply Measurable.stronglyMeasurable
  apply Measurable.mul
  · exact Complex.continuous_exp.measurable.comp (by fun_prop)
  · exact (𝓕 g : 𝓢(ℝ, ℂ)).continuous.measurable.comp (by fun_prop)

theorem sourceDensity_norm (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    ‖sourceDensity g c θ t‖ = ‖(𝓕 g) (t-θ)‖ := by
  simp [sourceDensity, logPhase_norm]

theorem sourceDensity_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
        C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseClippingProfiles.translated_twist_moment_uniform g J
  refine ⟨C, hC, ?_⟩
  intro c θ
  simpa only [InverseClippingProfiles.fourier_translated_twist, sourceDensity,
    SchwartzMap.fourier_coe] using hb (Real.log c) θ

def clippedSource (W : ℝ → ℂ) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x) * W (c*x)

theorem clipped_log_source (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c : ℝ} (hc : 0 < c) (θ y : ℝ) :
    clippedTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ y =
      clippedSource W c θ (Real.exp y) := by
  simp only [clippedTwist_apply, CubicReflectionKernel.logSchwartz_apply,
    clippedSource, Real.log_exp, Real.exp_add, Real.exp_log hc]
  rw [mul_comm (Real.exp y) c]

def rootExponent (y : Fin 6 → ℝ) : ℝ := -y 1-y 2-(y 4+y 5)/2

theorem root_coupled_identity (y : Fin 6 → ℝ) :
    rootExponent y = -y 1+y 0-((y 0+y 2+y 4)+(y 0+y 2+y 5))/2 := by
  unfold rootExponent
  ring

theorem root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (hd : |y 1| ≤ L) (hC : |y 0| ≤ L)
    (hc₁ : |y 0+y 2+y 4| ≤ L) (hc₂ : |y 0+y 2+y 5| ≤ L) :
    rootExponent y ≤ 3*L := by
  rw [root_coupled_identity]
  have hd' := (abs_le.mp hd).1
  have hC' := (abs_le.mp hC).2
  have h1 := (abs_le.mp hc₁).1
  have h2 := (abs_le.mp hc₂).1
  linarith

def normalizedProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) * secondPoissonProfile W₁ W₂ Φ V R y

theorem normalizedProfile_exact (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    normalizedProfile W₁ W₂ Φ V R L y =
      (Real.exp (rootExponent y-3*L) : ℂ) * (∏ i, V i (y i)) *
      W₁ (Real.exp (y 0+y 2+y 4)) * W₂ (Real.exp (y 0+y 2+y 5)) *
      paperRadialFourier Φ (R*Real.exp (y 3-y 1-2*y 2-y 4-y 5)) := by
  unfold normalizedProfile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  have hleft : (∑ i, secondLeftSlope i*y i) = y 0+y 2+y 4 := by
    simp [secondLeftSlope, Fin.sum_univ_succ]
    ring
  have hright : (∑ i, secondRightSlope i*y i) = y 0+y 2+y 5 := by
    simp [secondRightSlope, Fin.sum_univ_succ]
    ring
  have hker : (∑ i, secondKernelSlope i*y i) = y 3-y 1-2*y 2-y 4-y 5 := by
    simp [secondKernelSlope, Fin.sum_univ_succ]
    ring
  rw [hleft, hright, hker]
  change (Real.exp (-3*L) : ℂ) * (((Real.exp (rootExponent y) : ℂ)*_)*_*_*_) = _
  rw [show Real.exp (rootExponent y-3*L) = Real.exp (-3*L)*Real.exp (rootExponent y) by
    rw [← Real.exp_add]; congr 1; ring, Complex.ofReal_mul]
  ring

def familyDensity (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) : ℂ :=
  (Real.exp (-3*L) : ℂ) * fullProfileDensity g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem familyDensity_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) :
    familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p =
      (Real.exp (-3*L) : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 *
          (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) * coordinateDensity g p.2 := by
  simp only [familyDensity, fullProfileDensity, tripleCoefficient, fourier_clippedTwist]
  ring

theorem familyDensity_weighted_integrable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) := by
  convert (InverseMoment.fullProfileDensity_weighted_integrable g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ J).const_mul
      (Real.exp (-3*L)) using 1
  funext p
  simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

theorem familyDensity_weighted_integral
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Frequency × (Fin 6 → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) =
    Real.exp (-3*L) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
      ∏ i, ∫ u : ℝ, (1+‖u‖)^J * ‖(𝓕 (g i)) u‖ := by
  have he (p : Frequency × (Fin 6 → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖ =
      Real.exp (-3*L) * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁))
          (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p‖) := by
    simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  simp only [fourier_clippedTwist]
  ring

def logFamilyProfile (g₁ g₂ : 𝓢(ℝ, ℂ)) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) *
    ((∏ i, secondRootWindows V i (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

theorem family_common_measure
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ c₁ c₂ θ₁ θ₂ L : ℝ, 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
          ∫ p : Frequency × (Fin 6 → ℝ),
            familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  have hb : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₃, hC₃, hsep⟩ := paperRadialFourier_log_separation_envelope
    Φ (secondRootWindows V) secondKernelSlope M hM hb A J
  obtain ⟨C₁, hC₁, h₁⟩ := sourceDensity_moment_uniform g₁ J
  obtain ⟨C₂, hC₂, h₂⟩ := sourceDensity_moment_uniform g₂ J
  let D : ℝ := ∏ i, ∫ u : ℝ, (1+‖u‖)^J *
    ‖(𝓕 (secondRootSchwartz V hV hS i)) u‖
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun u => by positivity))
  refine ⟨C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, _, hm, _⟩ := hsep R hR
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ L hL
  refine ⟨?_, familyDensity_weighted_integrable _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope R b₃ he y
    have habs := profile_integral_coordinate_absorption (secondRootSchwartz V hV hS)
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    have hid' : logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
        (Real.exp (-3*L) : ℂ) *
          ∫ p : Frequency × (Fin 6 → ℝ),
            fullProfileDensity (secondRootSchwartz V hV hS)
              (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2 := by
      unfold logFamilyProfile
      rw [hid]
      congr 1
      rw [full_density_mode_fubini]
      simpa only [profileMode, secondRootSchwartz, rootSchwartz_apply] using habs
    rw [hid', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold familyDensity
    ring
  · rw [familyDensity_weighted_integral]
    have h1 := (h₁ c₁ θ₁).2
    have h2 := (h₂ c₂ θ₂).2
    have h12 := mul_le_mul h1 h2 (integral_nonneg (fun _ => by positivity))
      (mul_nonneg hC₁ (by positivity))
    have hm0 : 0 ≤ (1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖ := by positivity
    have h123 := mul_le_mul h12 hm hm0 (by positivity)
    have h123D := mul_le_mul_of_nonneg_right h123 hD
    have hnorm : Real.exp (-3*L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have heq : (1+R)^A * (Real.exp (-3*L) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) =
      Real.exp (-3*L) * (((∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖)) *
        ((1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) := by ring
    change (1+R)^A * (_ * _ * _ * _ * D) ≤ _
    rw [heq]
    exact (mul_le_mul_of_nonneg_left h123D (Real.exp_pos _).le).trans
      ((mul_le_of_le_one_left (by positivity) hnorm).trans_eq (by ring))

theorem sourceDensity_moment_seminorm (g : 𝓢(ℝ, ℂ)) (M b : ℝ)
    (hM : 0 ≤ M) (hb : 1 ≤ b) (hg : Function.support g ⊆ Set.Icc (-M) M)
    (J : ℕ) {c : ℝ} (hc : 1 ≤ c) (hcb : c ≤ b) (θ : ℝ) :
    (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
      InverseClippingProfiles.windowMomentConstant g M (Real.log b) 0 J *
        (1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hlog : |Real.log c| ≤ Real.log b * 1 := by
    rw [mul_one, abs_of_nonneg (Real.log_nonneg hc)]
    exact Real.log_le_log hc0 hcb
  have he : clippedTwist g c θ = frequencyTwist
      (InverseClippingProfiles.rootSchwartz g M (Real.log b) 1 (Real.log c) 0 0
        zero_lt_one hlog hg) θ := by
    ext y
    simp [InverseClippingProfiles.rootSchwartz_apply,
      InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]
  have hm := InverseClippingProfiles.rooted_twist_fourier_moment g M (Real.log b)
    1 (Real.log c) 0 0 θ hM (Real.log_nonneg hb) le_rfl hlog hg (by simp) J
  simp_rw [← fourier_clippedTwist, he]
  simpa only [InverseClippingProfiles.windowMomentConstant, one_pow, mul_one] using hm

theorem clippedSource_conjugate (W : ℝ → ℂ) (c θ x : ℝ) :
    star (clippedSource W c θ x) = clippedSource (fun x => star (W x)) c (-θ) x := by
  simp only [clippedSource, star_mul, SecondPassIntegration.logPhase_conjugate]
  ring

theorem familyDensity_joint_measurable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) (L : ℝ) :
    StronglyMeasurable (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × (Frequency × (Fin 6 → ℝ)) =>
      familyDensity g g₁ g₂ b₃ z.1.1.1 z.1.2.1 z.1.1.2 z.1.2.2 L z.2) := by
  simp_rw [familyDensity_formula]
  apply Measurable.stronglyMeasurable
  unfold sourceDensity coordinateDensity logPhase
  have h1 : Measurable ((𝓕 g₁ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 : Measurable ((𝓕 g₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 : Measurable (b₃ : ℝ → ℂ) := b₃.continuous.measurable
  have hu (i : Fin 6) : Measurable ((𝓕 (g i) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have hexp : Measurable Complex.exp := Complex.continuous_exp.measurable
  fun_prop

theorem fresh_cutoff_one (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (_ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hω : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (hs : W (c*(u*v*x)) ≠ 0) : w x = 1 := by
  have hu0 : 0 < u := hA₀.trans_le hu.1
  have hv0 : 0 < v := hA₂.trans_le hv.1
  have hB₀ : 0 < B₀ := hu0.trans_le hu.2
  have hB₂ : 0 < B₂ := hv0.trans_le hv.2
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hs' := hW hs
  have hlo : A₀*A₂ ≤ c*(u*v) := by
    have hprod := mul_le_mul hu.1 hv.1 hA₂.le hu0.le
    exact hprod.trans (le_mul_of_one_le_left (mul_nonneg hu0.le hv0.le) hc)
  have hhi : c*(u*v) ≤ bclip*B₀*B₂ := by
    have hprod := mul_le_mul hu.2 hv.2 hv0.le hB₀.le
    exact (mul_le_mul hcb hprod (mul_nonneg hu0.le hv0.le)
      (zero_lt_one.trans_le hclip).le).trans_eq (by ring)
  apply hω x
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < bclip*B₀*B₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hhi hx.le
    nlinarith [hs'.1]
  · apply (le_div_iff₀ (mul_pos hA₀ hA₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hlo hx.le
    nlinarith [hs'.2]

def columnCenter (D B v : ℝ) : ℝ := D-B-v
def prefactorCenter (m D B θ : ℝ) : ℝ := m-2*D+B-θ
def radialCenter (m H θ D B : ℝ) : ℝ := m+H-θ-2*(D-B)

theorem original_column_scale {Z : ℝ} (hZ : 0 < Z) (D B v : ℝ) :
    Z^B * Z^v * Z^(columnCenter D B v) = Z^D := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold columnCenter
  ring

theorem initial_prefactor_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ : ℝ) :
    Z^(-D) * Z^m / (Z^θ * Z^v * Z^(columnCenter D B v)) =
      Z^(prefactorCenter m D B θ) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter prefactorCenter
  ring

theorem initial_radial_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ) :
    Z^m * Z^H / (Z^θ * (Z^v)^2 * (Z^(columnCenter D B v))^2) =
      Z^(radialCenter m H θ D B) := by
  simp only [pow_two]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter radialCenter
  ring

theorem initial_normalization_scalar {Z : ℝ} (hZ : 0 < Z) (κ η : ℝ) :
    Z^(κ+3*η) * Real.exp (-3*(η*Real.log Z)) = Z^κ := by
  have he : Real.exp (-3*(η*Real.log Z)) = Z^(-3*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he, ← Real.rpow_add hZ]
  congr 1
  ring

def physicalKernel (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  ((Z^(-D)*Z^m/(q 1*q 2*Real.sqrt (q 4*q 5)) : ℝ) : ℂ) *
    W₁ (q 0*q 2*q 4/Z^D) * W₂ (q 0*q 2*q 5/Z^D) *
      paperRadialFourier Φ (Z^m*q 3/(q 1*(q 2)^2*q 4*q 5))

theorem physicalKernel_eq_secondNorm (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      ((Z^(-D)*Z^m : ℝ) : ℂ) *
        secondNormProfile (fun x => W₁ (x/Z^D)) (fun x => W₂ (x/Z^D))
          Φ (fun _ _ => 1) (Z^m) q := by
  unfold physicalKernel secondNormProfile
  rw [Real.sqrt_mul (hq 4).le]
  simp only [Finset.prod_const_one, one_mul, Complex.ofReal_div, Complex.ofReal_mul]
  ring

theorem physicalKernel_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ) : ℝ) *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1) (Z^(radialCenter m H θ D B))
          (secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))) := by
  have hn := secondNormProfile_nominal W₁ W₂ Φ
    (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v)) (Z^m)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) q hq
  rw [original_column_scale hZ D B v, initial_radial_scale hZ D B v m θ H] at hn
  rw [physicalKernel_eq_secondNorm W₁ W₂ Φ Z D m q hq, hn]
  change ((Z^(-D)*Z^m : ℝ) : ℂ) *
      (((Z^θ*Z^v*Z^(columnCenter D B v) : ℝ) : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← div_eq_mul_inv, initial_prefactor_scale hZ D B v m θ]
  rfl

theorem normalizedProfile_eq_family (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (θ₁ θ₂ R L : ℝ)
    (y : Fin 6 → ℝ) :
    normalizedProfile (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ V R L y =
      logFamilyProfile (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
        (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
        Φ V c₁ c₂ θ₁ θ₂ R L y := by
  unfold normalizedProfile logFamilyProfile secondPoissonProfile
  rw [clipped_log_source W₁ a b ha hs₁ hW₁ hc₁,
    clipped_log_source W₂ a b ha hs₂ hW₂ hc₂]

theorem fresh_profile_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i)
    (hw₁ : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1)
    (hw₂ : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1)
    (hV : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 → ∀ i, V i (Real.log (x i)) = 1) :
    (Real.exp (-3*L) : ℂ) * secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R x =
      (w₁ (x 4)*w₂ (x 5)) * normalizedProfile W₁ W₂ Φ V R L (fun i => Real.log (x i)) := by
  unfold normalizedProfile
  rw [secondPoissonProfile_log W₁ W₂ Φ V R x hx]
  by_cases h1 : W₁ (x 0*x 2*x 4) = 0
  · simp only [secondNormProfile, h1, mul_zero, zero_mul, zero_div]
  by_cases h2 : W₂ (x 0*x 2*x 5) = 0
  · simp only [secondNormProfile, h2, mul_zero, zero_mul, zero_div]
  have hv := hV (by rw [hw₁ h1]; exact one_ne_zero) (by rw [hw₂ h2]; exact one_ne_zero)
  simp only [secondNormProfile, hv, hw₁ h1, hw₂ h2, Finset.prod_const_one, one_mul]

def relativeNorm (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) : Fin 6 → ℝ :=
  secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))

def relativeLog (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) (i : Fin 6) : ℝ :=
  Real.log (relativeNorm q Z D B v θ H i)

theorem relativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    {Z : ℝ} (hZ : 0 < Z) (D B v θ H : ℝ) :
    ∀ i, 0 < relativeNorm q Z D B v θ H i :=
  secondRelativeNorm_pos q hq _ _ _ _ _
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _)

theorem initial_kernel_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hw₁ : W₁ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1)
    (hw₂ : W₂ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1)
    (hV : w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 → ∀ i, V i (relativeLog q Z D B v θ H i) = 1) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        normalizedProfile W₁ W₂ Φ V (Z^(radialCenter m H θ D B))
          (η*Real.log Z) (relativeLog q Z D B v θ H) := by
  rw [physicalKernel_nominal W₁ W₂ Φ hZ D B v m θ H q hq]
  have hs := fresh_profile_restore W₁ W₂ w₁ w₂ Φ V (Z^(radialCenter m H θ D B))
    (η*Real.log Z) (relativeNorm q Z D B v θ H)
    (relativeNorm_pos q hq hZ D B v θ H) hw₁ hw₂ hV
  have hn : ((Z^(prefactorCenter m D B θ) : ℝ) : ℂ) =
      (Z^(prefactorCenter m D B θ+3*η) : ℝ) * (Real.exp (-3*(η*Real.log Z)) : ℂ) := by
    rw [← Complex.ofReal_mul, initial_normalization_scalar hZ]
  rw [show relativeLog q Z D B v θ H =
    (fun i => Real.log (relativeNorm q Z D B v θ H i)) by rfl]
  rw [hn, mul_assoc]
  simpa only [mul_assoc, relativeNorm] using congrArg
    (fun z : ℂ => (Z^(prefactorCenter m D B θ+3*η) : ℝ) * z) hs

def PhysicalIdentityAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  ∀ (w₁ w₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
    (clippedSource W₁ c₁ θ₁
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1) →
    (clippedSource W₂ c₂ θ₂
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1) →
    (w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 →
      ∀ i, V i (relativeLog q Z D B v θ H i) = 1) →
    physicalKernel (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        ∫ p : Frequency × (Fin 6 → ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (relativeLog q Z D B v θ H) p.1 p.2

theorem initial_physical_family_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
    let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z D B v m θ H η : ℝ, 0 < Z → 0 ≤ η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ, ℂ), ∀ c₁ c₂ θ₁ θ₂ : ℝ, 0 < c₁ → 0 < c₂ →
      PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ∧
      (1+Z^(radialCenter m H θ D B))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hsep⟩ := family_common_measure
    (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
    (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
    Φ V M hV hS hM hbox A J
  refine ⟨C, hC, ?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃, hb₃⟩ := hsep (Z^(radialCenter m H θ D B)) (Real.rpow_pos_of_pos hZ _)
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨he, hi, hbound⟩ := hb₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hL
  refine ⟨?_, hi, hbound⟩
  intro w₁ w₂ q hq hw₁ hw₂ hcut
  rw [initial_kernel_restore _ _ w₁ w₂ Φ V hZ D B v m θ H η q hq hw₁ hw₂ hcut,
    normalizedProfile_eq_family W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V hc₁ hc₂, he]

theorem fresh_cutoff_one_clippedSource (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hw : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (θ : ℝ) (hs : clippedSource W c θ (u*v*x) ≠ 0) : w x = 1 := by
  exact fresh_cutoff_one W w a b bclip A₀ B₀ A₂ B₂ ha hA₀ hA₂ hclip hW hw
    hc hcb hu hv hx (mul_ne_zero_iff.mp hs).2

theorem clipped_column_ratio {Z : ℝ} (hZ : 0 < Z) (N q : ℝ) :
    q / Z^N = Z^(max 0 N-N) * (q / Z^(max 0 N)) := by
  rw [Real.rpow_sub hZ]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hZ N),
    ne_of_gt (Real.rpow_pos_of_pos hZ (max 0 N))]

theorem clipped_column_source_identity (w : ℝ → ℂ) {Z q : ℝ}
    (hZ : 0 < Z) (hq : 0 < q) (N θ : ℝ) :
    logPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
      logPhase θ (Real.log (Z^(max 0 N-N))) *
        clippedSource w (Z^(max 0 N-N)) θ (q/Z^(max 0 N)) := by
  rw [clipped_column_ratio hZ N q]
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hZ _))
    (ne_of_gt (div_pos hq (Real.rpow_pos_of_pos hZ _))), logPhase_add]
  unfold clippedSource
  ring

theorem retained_initial_clipping (w : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hs : ContDiff ℝ ∞ w) (J : ℕ) :
    let g := CubicReflectionKernel.logSchwartz w a b ha hw hs
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z N q : ℝ, 1 < Z → 1 ≤ q → w (q/Z^N) ≠ 0 →
      let c := Z^(max 0 N-N)
      1 ≤ c ∧ c ≤ b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
      (∀ θ : ℝ, logPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
        logPhase θ (Real.log c) * clippedSource w c θ (q/Z^(max 0 N))) ∧
      (∀ θ : ℝ, Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
          C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hbound⟩ := sourceDensity_moment_uniform
    (CubicReflectionKernel.logSchwartz w a b ha hw hs) J
  refine ⟨C, hC, ?_⟩
  intro Z N q hZ hq hwitness
  obtain ⟨hc, hcb, hsupport, _⟩ := InverseClippingProfiles.retained_clipped_column
    w Z N q a b hZ hq ha hb hw hwitness
  refine ⟨hc, hcb, hsupport, ?_, fun θ => hbound _ θ⟩
  exact fun θ => clipped_column_source_identity w (zero_lt_one.trans hZ)
    (zero_lt_one.trans_le hq) N θ

end SevenEighths.InverseInitialProfile

end

end OAI

end

