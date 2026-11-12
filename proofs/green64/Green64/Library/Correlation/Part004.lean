module

public import Green64.Library.Weights.Part023
public import Mathlib.Analysis.SpecificLimits.Basic
public import Green64.Library.Correlation.Part002
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic
public import Green64.Library.Weights.Part012
public import Green64.Library.Analysis.Estimates.Part004
public import Green64.Library.Analysis.Estimates.Part002

@[expose] public section

/-!
# Correlation / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePhysicalLogIntegrable -/

section

open MeasureTheory
open scoped SchwartzMap BigOperators FourierTransform
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1200000

/-- Integrability companion of the already proved scaled log Jacobian. -/
theorem source_scaled_log_integrable434 (Y : ℝ) (hY : 0 < Y)
    (Q : ℝ → ℂ) (hQ : Integrable (fun u : ℝ => Real.exp u*‖Q u‖^2)) :
    IntegrableOn (fun v : ℝ => ‖Q (Real.log (v/Y))‖^2) (Set.Ioi 0) := by
  let f : ℝ → ℝ := fun u => Y*Real.exp u
  let g : ℝ → ℝ := fun v => ‖Q (Real.log (v/Y))‖^2
  have hd (u : ℝ) (_ : u ∈ Set.univ) :
      HasDerivWithinAt f (Y*Real.exp u) Set.univ u :=
    ((Real.hasDerivAt_exp u).const_mul Y).hasDerivWithinAt
  have hi : Set.InjOn f Set.univ := by
    intro u _ w _ he
    exact Real.exp_injective (mul_left_cancel₀ hY.ne' he)
  have hlog (u : ℝ) : Real.log ((Y*Real.exp u)/Y) = u := by
    rw [mul_div_cancel_left₀ _ hY.ne',Real.log_exp]
  have hTrans : Integrable (fun u : ℝ => (Y*Real.exp u)*g (Y*Real.exp u)) := by
    simpa only [g,hlog,mul_assoc] using hQ.const_mul Y
  have he := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.univ) (f := f) (f' := fun u => Y*Real.exp u)
    MeasurableSet.univ hd hi g
  rw [Set.image_univ,source_scaled_exp_range434 Y hY] at he
  apply he.mpr
  simpa only [f,IntegrableOn,Measure.restrict_univ,
    abs_of_pos (mul_pos hY (Real.exp_pos _)),smul_eq_mul] using hTrans

/-- The actual finite marked Mellin physical Q has an integrable
square on the complete positive physical axis, not just a finite window. -/
theorem source_literal_physical_log_integrable434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (F : Finset ℕ) (a : ℕ → ℂ) (H Y : ℝ) (hH : 0 < H) (hY : 0 < Y) :
    IntegrableOn (fun v : ℝ => (H/(2*Real.pi*Y))^2 *
      ‖sourceActualPhysicalQ434 chi kappa (H/Y)
        (sourceLiteralTwistedMellin434 Y F a) (Real.log (v/Y))‖^2)
      (Set.Ioi 0) := by
  have hWeighted := source_actual_physical_exp_weight_integrable434
    chi kappa B hB hchi 2 (by norm_num) (H/Y) (div_pos hH hY)
    (sourceLiteralTwistedMellin434 Y F a)
    (source_literal_twisted_continuous434 Y F a)
    (∑ n ∈ F, ‖a n‖) (by positivity)
    (source_literal_twisted_bound434 Y F a)
  exact (source_scaled_log_integrable434 Y hY _ hWeighted).const_mul _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralWeightedShell -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1250000

/-- Monotonicity of the actual collar time weight at every |t|>=R. -/
theorem source_literal_weight_large_time434
    (h : ℝ) (hh : 0 < h) (j : ℕ)
    (R : ℝ) (hR : 0 ≤ R)
    (t : ℝ) (ht : R ≤ |t|) :
    ((1+h*|t|)^j)⁻¹ ≤ ((1+h*R)^j)⁻¹ := by
  have hbase : 1+h*R ≤ 1+h*|t| := by
    nlinarith [mul_le_mul_of_nonneg_left ht hh.le]
  have hpow := pow_le_pow_left₀
    (by positivity : 0 ≤ 1+h*R) hbase j
  have hpos : 0 < (1+h*|t|)^j := by
    have hv : 0 ≤ h*|t| := mul_nonneg hh.le (abs_nonneg _)
    exact pow_pos (by linarith : 0 < 1+h*|t|) _
  have hposR : 0 < (1+h*R)^j := by
    have hv : 0 ≤ h*R := mul_nonneg hh.le hR
    exact pow_pos (by linarith : 0 < 1+h*R) _
  exact (inv_le_inv₀ hpos hposR).mpr hpow
/-- Genuine compact-interval weighted estimate derived from full-line
integrability, and with a pointwise distance-from-zero constraint.
No extra energy hypothesis is assumed. -/
theorem source_literal_weighted_interval434
    (F : Finset ℕ) (a : ℕ → ℂ)
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j)
    (R : ℝ) (hR : 0 ≤ R)
    (l u : ℝ) (hAway : ∀ t ∈ Set.Icc l u, R ≤ |t|) :
    (∫ t in Set.Icc l u,
       ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
      ((1+h*R)^j)⁻¹ *
        (∫ t in Set.Icc l u,
          ‖sourceLiteralFiniteMellin434 F a t‖^2) := by
  let P : ℝ → ℂ := sourceLiteralFiniteMellin434 F a
  have hInt := source_literal_finite_mellin_weighted_integrable434 F a h hh j hj
  have hL : IntegrableOn (fun t : ℝ =>
      ((1+h*|t|)^j)⁻¹ * ‖P t‖^2) (Set.Icc l u) :=
    hInt.mono_measure Measure.restrict_le_self
  have hCont : Continuous (fun t : ℝ => ‖P t‖^2) :=
    (source_literal_finite_mellin_continuous434 F a).norm.pow 2
  have hRInt : IntegrableOn (fun t : ℝ =>
      ((1+h*R)^j)⁻¹ * ‖P t‖^2) (Set.Icc l u) :=
    (hCont.integrableOn_Icc).const_mul _
  have hPoint (t : ℝ) (ht : t ∈ Set.Icc l u) :
      ((1+h*|t|)^j)⁻¹ * ‖P t‖^2 ≤
      ((1+h*R)^j)⁻¹ * ‖P t‖^2 :=
    mul_le_mul_of_nonneg_right
      (source_literal_weight_large_time434 h hh j R hR t (hAway t ht))
      (sq_nonneg _)
  calc
    _ ≤ ∫ t in Set.Icc l u,
        ((1+h*R)^j)⁻¹ * ‖P t‖^2 :=
      setIntegral_mono_on hL hRInt measurableSet_Icc hPoint
    _ = _ := integral_const_mul _ _

/-- The exact SOURCE time weight costs the left edge of EACH positive
and negative dyadic shell, rather than a postulated tail saving. -/
theorem source_literal_weighted_dyadic_two_sides434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (h : ℝ) (hh : 0 < h) (j : ℕ) (hj : 2 ≤ j)
    (R : ℝ) (hR : 0 ≤ R) (hF : F ⊆ Finset.Icc 1 N) :
    (∫ t in Set.Icc R (2*R),
      ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
      ((1+h*R)^j)⁻¹ *
        (R+16*(N:ℝ)*(1+Real.log N)) * ∑ n ∈ F, ‖a n‖^2 ∧
    (∫ t in Set.Icc (-2*R) (-R),
      ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
      ((1+h*R)^j)⁻¹ *
        (R+16*(N:ℝ)*(1+Real.log N)) * ∑ n ∈ F, ‖a n‖^2 := by
  have hp := (source_literal_dyadic_two_sides434 N F a R hR hF).1
  have hn := (source_literal_dyadic_two_sides434 N F a R hR hF).2
  have hweight : 0 ≤ ((1+h*R)^j)⁻¹ := by positivity
  constructor
  · have hAway : ∀ t ∈ Set.Icc R (2*R), R ≤ |t| := by
      intro t ht
      exact (Set.mem_Icc.mp ht).1.trans (le_abs_self t)
    have hs := source_literal_weighted_interval434 F a h hh j hj R hR
      R (2*R) hAway
    exact hs.trans (by
      nlinarith [mul_le_mul_of_nonneg_left hp hweight])
  · have hAway : ∀ t ∈ Set.Icc (-2*R) (-R), R ≤ |t| := by
      intro t ht
      have hneg : t ≤ 0 := by linarith [(Set.mem_Icc.mp ht).2]
      rw [abs_of_nonpos hneg]
      linarith [(Set.mem_Icc.mp ht).2]
    have hs := source_literal_weighted_interval434 F a h hh j hj R hR
      (-2*R) (-R) hAway
    exact hs.trans (by
      nlinarith [mul_le_mul_of_nonneg_left hn hweight])
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralAllShellScales -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1000000

/-- The original Fourier cutoff's positive and negative dyadic radii:
R_r = 2^r L Y/H = 2^r L/h, h=H/Y. -/
noncomputable def sourceLiteralDyadicRadius434 (h L : ℝ) (r : ℕ) : ℝ :=
  (2:ℝ)^r * (L/h)

theorem source_literal_dyadic_radius_nonneg434
    (h L : ℝ) (hh : 0 < h) (hL : 0 ≤ L) (r : ℕ) :
    0 ≤ sourceLiteralDyadicRadius434 h L r := by
  unfold sourceLiteralDyadicRadius434
  positivity

theorem source_literal_dyadic_radius_scale434
    (h L : ℝ) (hh : 0 < h) (r : ℕ) :
    h * sourceLiteralDyadicRadius434 h L r = (2:ℝ)^r * L := by
  unfold sourceLiteralDyadicRadius434
  field_simp

/-- Positive AND negative dyadic shells at original T0=LY/H,
with their exact j-dependent source weight and no tail hypothesis. -/
theorem source_literal_original_dyadic_shell_bound434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (h L : ℝ) (hh : 0 < h) (hL : 0 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) (r : ℕ)
    (hF : F ⊆ Finset.Icc 1 N) :
    (∫ t in Set.Icc (sourceLiteralDyadicRadius434 h L r)
        (2 * sourceLiteralDyadicRadius434 h L r),
      ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2) +
    (∫ t in Set.Icc (-2 * sourceLiteralDyadicRadius434 h L r)
        (-sourceLiteralDyadicRadius434 h L r),
      ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2) ≤
    2 * ((1+(2:ℝ)^r*L)^j)⁻¹ *
      (sourceLiteralDyadicRadius434 h L r +
        16*(N:ℝ)*(1+Real.log N)) * ∑ n ∈ F, ‖a n‖^2 := by
  let R : ℝ := sourceLiteralDyadicRadius434 h L r
  have hR : 0 ≤ R := source_literal_dyadic_radius_nonneg434 h L hh hL r
  obtain ⟨hp,hn⟩ :=
    source_literal_weighted_dyadic_two_sides434 N F a h hh j hj R hR hF
  have he : h*R = (2:ℝ)^r*L :=
    source_literal_dyadic_radius_scale434 h L hh r
  have hs : ((1+h*R)^j)⁻¹ =
      ((1+(2:ℝ)^r*L)^j)⁻¹ := by rw [he]
  rw [hs] at hp hn
  change _ ≤ 2 * ((1+(2:ℝ)^r*L)^j)⁻¹ *
    (R+16*(N:ℝ)*(1+Real.log N)) * ∑ n ∈ F, ‖a n‖^2
  linarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralShellJReserve -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- Original j>=2 collar shell weight keeps an arbitrary L^(-(j-2))
reserve uniformly for ALL positive and negative dyadic indices r.
No shell is dropped and no energy saving is postulated. -/
theorem source_original_dyadic_arbitrary_j_reserve434
    (L : ℝ) (hL : 1 ≤ L) (j : ℕ) (hj : 2 ≤ j) (r : ℕ) :
    ((1+(2:ℝ)^r*L)^j)⁻¹ ≤
      (L^(j-2))⁻¹ * ((1+(2:ℝ)^r*L)^2)⁻¹ := by
  let Z : ℝ := (2:ℝ)^r*L
  have hpow2 : (1:ℝ) ≤ 2^r := one_le_pow₀ (by norm_num)
  have hz : L ≤ Z := by
    dsimp [Z]
    calc
      L = (1:ℝ)*L := by ring
      _ ≤ 2^r*L := mul_le_mul_of_nonneg_right hpow2 (by linarith)
  have hbase : L ≤ 1+Z := by linarith
  have hP : L^(j-2) ≤ (1+Z)^(j-2) :=
    pow_le_pow_left₀ (by linarith : 0 ≤ L) hbase _
  have hLarge : L^(j-2)*(1+Z)^2 ≤ (1+Z)^j := by
    calc
      _ ≤ (1+Z)^(j-2)*(1+Z)^2 :=
        mul_le_mul_of_nonneg_right hP (by positivity)
      _ = (1+Z)^j := by
        rw [←pow_add, Nat.sub_add_cancel hj]
  have hLeft : 0 < (1+Z)^j := by
    have hZ : 0 < 1+Z := by linarith
    positivity
  have hRight : 0 < L^(j-2)*(1+Z)^2 := by
    have hZ : 0 < 1+Z := by linarith
    positivity
  have hi : ((1+Z)^j)⁻¹ ≤ (L^(j-2)*(1+Z)^2)⁻¹ :=
    (inv_le_inv₀ hLeft hRight).mpr hLarge
  calc
    _ ≤ (L^(j-2)*(1+Z)^2)⁻¹ := hi
    _ = (L^(j-2))⁻¹ * ((1+Z)^2)⁻¹ := by rw [mul_inv_rev, mul_comm]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralGeometricTail -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- Uniform geometric domination of the exact original shell weight.
Retains the L^{-(j-2)} reserve and both shell signs, for all r>=0. -/
theorem source_literal_geometric_shell_scalar434
    (h L C : ℝ) (hh : 0 < h) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (j : ℕ) (hj : 2 ≤ j) (r : ℕ) :
    ((1+(2:ℝ)^r*L)^j)⁻¹ *
        ((2:ℝ)^r*L/h + C) ≤
      ((L^(j-2))⁻¹ * (L/h+C)) * ((1/2:ℝ)^r) := by
  let A : ℝ := (2:ℝ)^r
  have hA : 1 ≤ A := by
    dsimp [A]
    exact one_le_pow₀ (by norm_num)
  have hApos : 0 < A := by linarith
  have hBase : A ≤ 1+A*L := by
    have hm := mul_nonneg (le_of_lt hApos) (sub_nonneg.mpr hL)
    nlinarith
  have hBasePos : 0 < 1+A*L := by linarith
  have hInv : ((1+A*L)^2)⁻¹ ≤ (A^2)⁻¹ := by
    exact (inv_le_inv₀ (pow_pos hBasePos _) (pow_pos hApos _)).mpr
      (pow_le_pow_left₀ (le_of_lt hApos) hBase 2)
  have hReserve :
      ((1+A*L)^j)⁻¹ ≤ (L^(j-2))⁻¹*((1+A*L)^2)⁻¹ := by
    simpa only [A] using
      (source_original_dyadic_arbitrary_j_reserve434 L hL j hj r)
  have hW :
      ((1+A*L)^j)⁻¹ ≤ (L^(j-2))⁻¹ * (A^2)⁻¹ :=
    hReserve.trans (mul_le_mul_of_nonneg_left hInv (by positivity))
  have hCoef : 0 ≤ A*L/h+C := by positivity
  have hCmul : C ≤ A*C := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) hC]
  have hCoeff : A*L/h+C ≤ A*(L/h+C) := by
    have heq : A*L/h = A*(L/h) := by ring
    rw [heq]
    nlinarith [hCmul]
  have hNorm : (A^2)⁻¹ * (A*(L/h+C)) =
      A⁻¹*(L/h+C) := by
    field_simp
  have hGeom : A⁻¹ = ((1/2:ℝ)^r) := by
    simp [A, inv_pow]
  calc
    _ ≤ ((L^(j-2))⁻¹*(A^2)⁻¹)*(A*L/h+C) :=
      mul_le_mul_of_nonneg_right hW hCoef
    _ ≤ ((L^(j-2))⁻¹*(A^2)⁻¹)*(A*(L/h+C)) :=
      mul_le_mul_of_nonneg_left hCoeff (by positivity)
    _ = (L^(j-2))⁻¹ *((A^2)⁻¹ * (A*(L/h+C))) := by ring
    _ = (L^(j-2))⁻¹ *(A⁻¹*(L/h+C)) := by rw [hNorm]
    _ = ((L^(j-2))⁻¹*(L/h+C))*((1/2:ℝ)^r) := by
      rw [hGeom]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralShellGeometricBound -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1150000

/-- Physical source's genuine positive and negative dyadic intervals,
each indexed by the full (unbounded) natural scale r. -/
noncomputable def sourceLiteralPairedShellEnergy434
    (h L : ℝ) (j : ℕ) (F : Finset ℕ) (a : ℕ → ℂ) (r : ℕ) : ℝ :=
  (∫ t in Set.Icc (sourceLiteralDyadicRadius434 h L r)
      (2*sourceLiteralDyadicRadius434 h L r),
    ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2) +
  (∫ t in Set.Icc (-2*sourceLiteralDyadicRadius434 h L r)
      (-sourceLiteralDyadicRadius434 h L r),
    ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2)

theorem source_literal_paired_shell_nonneg434
    (h L : ℝ) (hh : 0 ≤ h) (j : ℕ) (F : Finset ℕ) (a : ℕ → ℂ) (r : ℕ) :
    0 ≤ sourceLiteralPairedShellEnergy434 h L j F a r := by
  unfold sourceLiteralPairedShellEnergy434
  apply add_nonneg
  · exact setIntegral_nonneg measurableSet_Icc (fun t ht =>
      mul_nonneg (source_collar_real_weight_le_one434 h t hh j).1 (sq_nonneg _))
  · exact setIntegral_nonneg measurableSet_Icc (fun t ht =>
      mul_nonneg (source_collar_real_weight_le_one434 h t hh j).1 (sq_nonneg _))
/-- Valid for every r, not truncated to finitely many shells;
the summable r-decay retains the full L^{-(j-2)} budget. -/
theorem source_literal_shell_geometric_bound434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (h L : ℝ) (hh : 0 < h) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) (hF : F ⊆ Finset.Icc 1 N)
    (r : ℕ) :
    sourceLiteralPairedShellEnergy434 h L j F a r ≤
      (2 * ((L^(j-2))⁻¹ * (L/h+16*(N:ℝ)*(1+Real.log N))) *
         (∑ n ∈ F, ‖a n‖^2)) * (1/2:ℝ)^r := by
  let C : ℝ := 16*(N:ℝ)*(1+Real.log N)
  let E : ℝ := ∑ n ∈ F, ‖a n‖^2
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_natCast_nonneg N
    positivity
  have hE : 0 ≤ E :=
    Finset.sum_nonneg (fun n hn => sq_nonneg _)
  have hL0 : 0 ≤ L := by linarith
  have hUpper := source_literal_original_dyadic_shell_bound434
    N F a h L hh hL0 j hj r hF
  have hScalar := source_literal_geometric_shell_scalar434
    h L C hh hL hC j hj r
  calc
    _ ≤ 2 * (((1+(2:ℝ)^r*L)^j)⁻¹ *
        (sourceLiteralDyadicRadius434 h L r+C)) * E := by
      simpa only [sourceLiteralPairedShellEnergy434,C,E,mul_assoc]
        using hUpper
    _ ≤ 2 * ((((L^(j-2))⁻¹ * (L/h+C)) * (1/2:ℝ)^r)) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      have hScalar' :
          ((1+(2:ℝ)^r*L)^j)⁻¹ *
            (sourceLiteralDyadicRadius434 h L r+C) ≤
          ((L^(j-2))⁻¹*(L/h+C))*((1/2:ℝ)^r) := by
        convert hScalar using 1 <;> dsimp [sourceLiteralDyadicRadius434] <;> ring
      exact mul_le_mul_of_nonneg_left hScalar' (by norm_num)
    _ = (2 * ((L^(j-2))⁻¹ *
        (L/h+16*(N:ℝ)*(1+Real.log N))) * E) * (1/2:ℝ)^r := by
      dsimp [C]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralWholeRealShellTail -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 850000

/-- WHOLE infinite two-sided real-time shell tail, with no cutoff r≤Rmax.
The original large-j reserve L^{-(j-2)} survives summation over r≥0;
all positive and negative dyadic shells occur in the actual summand. -/
theorem source_literal_all_real_shells_summable434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (h L : ℝ) (hh : 0 < h) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) (hF : F ⊆ Finset.Icc 1 N) :
    Summable (sourceLiteralPairedShellEnergy434 h L j F a) := by
  let C : ℝ := (2 * ((L^(j-2))⁻¹ *
    (L/h+16*(N:ℝ)*(1+Real.log N))) *
       (∑ n ∈ F, ‖a n‖^2))
  have hDom : Summable (fun r : ℕ => C*(1/2:ℝ)^r) :=
    summable_geometric_two.mul_left C
  apply Summable.of_nonneg_of_le
    (fun r => source_literal_paired_shell_nonneg434 h L hh.le j F a r)
    (fun r => source_literal_shell_geometric_bound434 N F a h L
      hh hL j hj hF r)
    hDom

/-- Explicit full real-time shell sum. Its constant is source-uniform:
no unproved dyadic shell, high/low or exceptional-time energy input. -/
theorem source_literal_all_real_shells_bound434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (h L : ℝ) (hh : 0 < h) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) (hF : F ⊆ Finset.Icc 1 N) :
    (∑' r : ℕ, sourceLiteralPairedShellEnergy434 h L j F a r) ≤
      4 * ((L^(j-2))⁻¹ *
        (L/h+16*(N:ℝ)*(1+Real.log N))) *
        (∑ n ∈ F, ‖a n‖^2) := by
  let C : ℝ := (2 * ((L^(j-2))⁻¹ *
    (L/h+16*(N:ℝ)*(1+Real.log N))) *
       (∑ n ∈ F, ‖a n‖^2))
  have hDom : Summable (fun r : ℕ => C*(1/2:ℝ)^r) :=
    summable_geometric_two.mul_left C
  have hShell := source_literal_all_real_shells_summable434
    N F a h L hh hL j hj hF
  have hBound (r : ℕ) :
      sourceLiteralPairedShellEnergy434 h L j F a r ≤
        C*(1/2:ℝ)^r :=
    source_literal_shell_geometric_bound434 N F a h L
      hh hL j hj hF r
  calc
    _ ≤ ∑' r : ℕ, C*(1/2:ℝ)^r :=
      hShell.tsum_le_tsum hBound hDom
    _ = C * (∑' r : ℕ, (1/2:ℝ)^r) := tsum_mul_left
    _ = C*2 := by rw [tsum_geometric_two]
    _ = _ := by dsimp [C]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralPhysicalTailTruncated -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1100000

/-- The genuine original finite Mellin polynomial and the physically
truncated polynomial have the SAME two-sided shell energy, pointwise
for EVERY dyadic shell; the artificial bookkeeping N disappears. -/
theorem source_literal_original_shell_trunc_eq434
    (N M : ℕ) (a : ℕ → ℂ)
    (hZero : ∀ n ∈ Finset.Icc 1 N, M < n → a n = 0)
    (h L : ℝ) (j r : ℕ) :
    sourceLiteralPairedShellEnergy434 h L j (Finset.Icc 1 N) a r =
      sourceLiteralPairedShellEnergy434 h L j
        (Finset.Icc 1 (min N M)) a r := by
  unfold sourceLiteralPairedShellEnergy434
  simp_rw [source_literal_finite_mellin_truncate434 N M a hZero]

/-- Every dyadic row and the ENTIRE infinite full-real-time tail are
bounded with physical integer support M, rather than the much larger
formal index N, under genuine coefficient vanishing beyond M. -/
theorem source_literal_physical_complete_shell_trunc434
    (N M : ℕ) (a : ℕ → ℂ)
    (hZero : ∀ n ∈ Finset.Icc 1 N, M < n → a n = 0)
    (h L : ℝ) (hh : 0 < h) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) :
    Summable (sourceLiteralPairedShellEnergy434 h L j
      (Finset.Icc 1 N) a) ∧
    (∑' r : ℕ, sourceLiteralPairedShellEnergy434 h L j
      (Finset.Icc 1 N) a r) ≤
      4 * ((L^(j-2))⁻¹ *
        (L/h+16*(M:ℝ)*(1+Real.log M))) *
        (∑ n ∈ Finset.Icc 1 (min N M), ‖a n‖^2) := by
  let F : Finset ℕ := Finset.Icc 1 (min N M)
  have hF : F ⊆ Finset.Icc 1 M := by
    intro n hn
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hn).1,
        (Finset.mem_Icc.mp hn).2.trans (min_le_right N M)⟩
  have hEq : sourceLiteralPairedShellEnergy434 h L j
      (Finset.Icc 1 N) a =
      sourceLiteralPairedShellEnergy434 h L j F a := by
    funext r
    exact source_literal_original_shell_trunc_eq434 N M a hZero h L j r
  have hSum := source_literal_all_real_shells_summable434
    M F a h L hh hL j hj hF
  have hBound := source_literal_all_real_shells_bound434
    M F a h L hh hL j hj hF
  constructor
  · rw [hEq]
    exact hSum
  · rw [hEq]
    exact hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceLiteralActualFullRealTail -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- No hidden hTail assumption: the literal finite Mellin P has its
ACTUAL full positive+negative real-time integral equal to the entire
source dyadic paired-shell sum, for every h>0,j>=2 and L>=1.
The prior mean-square bound proves the summability. -/
theorem source_literal_real_tail_eq_entire_shell_sum434
    (N : ℕ) (F : Finset ℕ) (a : ℕ → ℂ)
    (hF : F ⊆ Finset.Icc 1 N)
    (h L : ℝ) (hh : 0 < h) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) :
    (∫ t in {t : ℝ | L/h ≤ |t|},
      ((1+h*|t|)^j)⁻¹ *
        ‖sourceLiteralFiniteMellin434 F a t‖^2) =
      ∑' r : ℕ, sourceLiteralPairedShellEnergy434 h L j F a r := by
  let f : ℝ → ℝ := fun t =>
    ((1+h*|t|)^j)⁻¹ * ‖sourceLiteralFiniteMellin434 F a t‖^2
  let T : ℝ := L/h
  have hT : 0 < T := div_pos (by linarith : 0 < L) hh
  have hInt : Integrable f :=
    source_literal_finite_mellin_weighted_integrable434 F a h hh j hj
  have hS : Summable (sourceLiteralPairedShellEnergy434
      h L j F a) :=
    source_literal_all_real_shells_summable434 N F a
      h L hh hL j hj hF
  have hStart (r : ℕ) :
      (2:ℝ)^r*T = sourceLiteralDyadicRadius434 h L r := rfl
  have hEnd (r : ℕ) :
      (2:ℝ)^(r+1)*T =
        2*sourceLiteralDyadicRadius434 h L r := by
    dsimp [T, sourceLiteralDyadicRadius434]
    rw [pow_succ]
    ring
  have hRow (r : ℕ) :
      (∫ t in Set.Icc ((2:ℝ)^r*T) ((2:ℝ)^(r+1)*T), f t) +
      (∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
        (-((2:ℝ)^r*T)), f t) =
      sourceLiteralPairedShellEnergy434 h L j F a r := by
    rw [hStart, hEnd]
    have hneg : -(2*sourceLiteralDyadicRadius434 h L r) =
        (-2)*sourceLiteralDyadicRadius434 h L r := by ring
    rw [hneg]
    rfl
  have hPair : Summable (fun r : ℕ =>
      (∫ t in Set.Icc ((2:ℝ)^r*T) ((2:ℝ)^(r+1)*T), f t) +
      (∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
        (-((2:ℝ)^r*T)), f t)) := by
    simpa only [hRow] using hS
  have hPos (r : ℕ) : 0 ≤
      (∫ t in Set.Icc ((2:ℝ)^r*T) ((2:ℝ)^(r+1)*T), f t) := by
    apply setIntegral_nonneg measurableSet_Icc
    intro t ht
    dsimp [f]
    positivity
  have hNeg (r : ℕ) : 0 ≤
      (∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
        (-((2:ℝ)^r*T)), f t) := by
    apply setIntegral_nonneg measurableSet_Icc
    intro t ht
    dsimp [f]
    positivity
  have hFull := source_dyadic_full_real_integral_tail434
    T hT f hInt hPair hPos hNeg
  change (∫ t in {t : ℝ | T ≤ |t|}, f t) = _
  calc
    _ = ∑' r : ℕ,
      ((∫ t in Set.Icc ((2:ℝ)^r*T) ((2:ℝ)^(r+1)*T), f t) +
       (∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
         (-((2:ℝ)^r*T)), f t)) := hFull
    _ = _ := by
      apply tsum_congr
      exact hRow
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSchwartzLipschitz -/

section

open scoped SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 600000

/-- A proved global Lipschitz constant for every Schwartz kernel.
This discharges the regularity input of the physical log replacement. -/
theorem source_schwartz_lipschitz434 (K : 𝓢(ℝ,ℂ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y : ℝ, ‖K x-K y‖ ≤ M*|x-y| := by
  let D : 𝓢(ℝ,ℂ) := SchwartzMap.derivCLM ℂ ℂ K
  let M : ℝ := SchwartzMap.seminorm ℂ 0 0 D
  have hM : 0 ≤ M := apply_nonneg _ _
  have hb (x : ℝ) : ‖deriv (K : ℝ → ℂ) x‖ ≤ M :=
    SchwartzMap.norm_le_seminorm ℂ D x
  have hLip : LipschitzWith ⟨M,hM⟩ (K : ℝ → ℂ) :=
    lipschitzWith_of_nnnorm_deriv_le K.differentiable
      (fun x => by exact_mod_cast hb x)
  refine ⟨M,hM,?_⟩
  intro x y
  have hd := hLip.dist_le_mul x y
  change dist (K x) (K y) ≤ M * dist x y at hd
  simpa only [dist_eq_norm, Real.norm_eq_abs] using hd
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSelectedArcKernels -/

section

open scoped SchwartzMap FourierTransform
namespace Green64Analytic.CorrelationSquare

/-- All auxiliary analytic kernels are chosen before H,Y and every
arithmetic parameter. None of their properties is an unproved premise. -/
theorem source_selected_arc_kernels434 (A : ℝ) (hA : 1 ≤ A) :
    ∃ (chi K : 𝓢(ℝ,ℂ)) (B δ M c : ℝ),
      0 < B ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ M ∧ 0 < c ∧
      tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B ∧
      (∀ z, K z ≠ 0 → |z| ≤ δ) ∧
      (∀ z z', ‖K z-K z'‖ ≤ M*|z-z'|) ∧
      (∀ t : ℝ, |t| ≤ 1 → c ≤ ‖(𝓕 (K : ℝ → ℂ)) t‖) ∧
      (∀ Y v : ℝ, 0 < Y → v ∈ Set.Icc (Y/(2*A)) (2*A*Y) →
        chi (Real.log (v/Y)) = 1) := by
  obtain ⟨chi,B,hB,hchi,hOne⟩ := source_log_window_cutoff_exists434 A hA
  obtain ⟨K,δ,c,hδ,hδ1,hc,hSupport,hLower⟩ := source_compact_bump_full_band_exists434
  obtain ⟨M,hM,hLip⟩ := source_schwartz_lipschitz434 K
  exact ⟨chi,K,B,δ,M,c,hB,hδ,hδ1,hM,hc,hchi,hSupport,hLip,hLower,hOne⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceSeparatedGeneric -/

section

/-! The same one-separated harmonic estimate over an arbitrary finite
index type, such as the selected exceptional time indices. -/
namespace Green64Analytic.CorrelationMellin

theorem source_separated_generic_reciprocal
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) (B : ℝ)
    (hB : 1 ≤ B)
    (hInj : Set.InjOn f S)
    (hPos : ∀ x ∈ S, 1 ≤ f x)
    (hBound : ∀ x ∈ S, f x ≤ B)
    (hSep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      1 ≤ |f x - f y|) :
    (∑ x ∈ S, (f x)⁻¹) ≤ 1 + Real.log B := by
  classical
  let T : Finset ℝ := S.image f
  have hTpos (u : ℝ) (hu : u ∈ T) : 1 ≤ u := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    exact hPos x hx
  have hTbound (u : ℝ) (hu : u ∈ T) : u ≤ B := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    exact hBound x hx
  have hTsep (u : ℝ) (hu : u ∈ T) (v : ℝ) (hv : v ∈ T)
      (hne : u ≠ v) : 1 ≤ |u-v| := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hne rfl
    exact hSep x hx y hy hxy
  calc
    (∑ x ∈ S, (f x)⁻¹) = ∑ u ∈ T, u⁻¹ := by
      rw [Finset.sum_image hInj]
    _ ≤ 1 + Real.log B :=
      source_separated_positive_reciprocal T B hB hTpos hTbound hTsep
end Green64Analytic.CorrelationMellin

end

/-! ## SourceIndexedHarmonic -/

section

/-! Reciprocal-gap harmonic row inequality for arbitrary Fintype-indexed
1-separated real exceptional times, with |t_j| ≤ Y. -/
namespace Green64Analytic.CorrelationMellin

theorem source_separated_indexed_reciprocal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (times : ι → ℝ) (Y : ℝ)
    (hY : 1 ≤ Y) (hBound : ∀ j, |times j| ≤ Y)
    (hSep : ∀ j k, j ≠ k → 1 ≤ |times j-times k|)
    (i : ι) :
    (∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
      |times i-times j|⁻¹) ≤
        2 * (1 + Real.log (2*Y)) := by
  classical
  let Sp : Finset ι := Finset.univ.filter (fun j => times i < times j)
  let Sm : Finset ι := Finset.univ.filter (fun j => times j < times i)
  have hB : 1 ≤ 2*Y := by linarith
  have hTInj : Function.Injective times := by
    intro j k hjk
    by_contra hne
    have hsep := hSep j k hne
    rw [hjk, sub_self, abs_zero] at hsep
    linarith
  have htp (j : ι) (hj : j ∈ Sp) : times i < times j :=
    (Finset.mem_filter.mp hj).2
  have htm (j : ι) (hj : j ∈ Sm) : times j < times i :=
    (Finset.mem_filter.mp hj).2
  have hInjP : Set.InjOn (fun j : ι => times j-times i) Sp := by
    intro j hj k hk heq
    apply hTInj
    dsimp at heq
    linarith
  have hInjM : Set.InjOn (fun j : ι => times i-times j) Sm := by
    intro j hj k hk heq
    apply hTInj
    dsimp at heq
    linarith
  have hPosP (j : ι) (hj : j ∈ Sp) : 1 ≤ times j-times i := by
    have hij : i ≠ j := fun h =>
      (ne_of_lt (htp j hj)) (congrArg times h)
    have hsep := hSep i j hij
    rw [abs_sub_comm (times i) (times j),
        abs_of_pos (sub_pos.mpr (htp j hj))] at hsep
    exact hsep
  have hPosM (j : ι) (hj : j ∈ Sm) : 1 ≤ times i-times j := by
    have hij : i ≠ j := fun h =>
      (ne_of_gt (htm j hj)) (congrArg times h)
    have hsep := hSep i j hij
    rw [abs_of_pos (sub_pos.mpr (htm j hj))] at hsep
    exact hsep
  have hBoundP (j : ι) (hj : j ∈ Sp) :
      times j-times i ≤ 2*Y := by
    have hjb := abs_le.mp (hBound j)
    have hib := abs_le.mp (hBound i)
    linarith
  have hBoundM (j : ι) (hj : j ∈ Sm) :
      times i-times j ≤ 2*Y := by
    have hjb := abs_le.mp (hBound j)
    have hib := abs_le.mp (hBound i)
    linarith
  have hSepP (j : ι) (hj : j ∈ Sp)
      (k : ι) (hk : k ∈ Sp) (hjk : j ≠ k) :
      1 ≤ |(times j-times i)-(times k-times i)| := by
    have h := hSep j k hjk
    have heq : (times j-times i)-(times k-times i) =
        times j-times k := by ring
    rwa [heq]
  have hSepM (j : ι) (hj : j ∈ Sm)
      (k : ι) (hk : k ∈ Sm) (hjk : j ≠ k) :
      1 ≤ |(times i-times j)-(times i-times k)| := by
    have h := hSep j k hjk
    have heq : (times i-times j)-(times i-times k) =
        -(times j-times k) := by ring
    rwa [heq, abs_neg]
  have hPlus := source_separated_generic_reciprocal
    Sp (fun j => times j-times i) (2*Y)
    hB hInjP hPosP hBoundP hSepP
  have hMinus := source_separated_generic_reciprocal
    Sm (fun j => times i-times j) (2*Y)
    hB hInjM hPosM hBoundM hSepM
  have hPartition :
      Finset.univ.filter (fun j : ι => j ≠ i) = Sp ∪ Sm := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Sp, Sm]
    constructor
    · intro hji
      have htne : times j ≠ times i := by
        intro heq
        exact hji (hTInj heq)
      rcases lt_or_gt_of_ne htne with hlt | hgt
      · exact Or.inr hlt
      · exact Or.inl hgt
    · rintro (hlt | hgt)
      · intro hji
        subst j
        exact (lt_irrefl _) hlt
      · intro hji
        subst j
        exact (lt_irrefl _) hgt
  have hDisj : Disjoint Sp Sm := by
    apply Finset.disjoint_left.mpr
    intro j hjp hjm
    have hp := htp j hjp
    have hm := htm j hjm
    linarith
  have hPsum : (∑ j ∈ Sp, |times i-times j|⁻¹) =
      (∑ j ∈ Sp, (times j-times i)⁻¹) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_sub_comm (times i) (times j),
      abs_of_pos (sub_pos.mpr (htp j hj))]
  have hMsum : (∑ j ∈ Sm, |times i-times j|⁻¹) =
      (∑ j ∈ Sm, (times i-times j)⁻¹) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_of_pos (sub_pos.mpr (htm j hj))]
  rw [hPartition, Finset.sum_union hDisj, hPsum, hMsum]
  linarith
end Green64Analytic.CorrelationMellin

end

/-! ## SourceGramKernelBound -/

section

/-! Kernel bounds combining the first and second discrete derivative
tests on [U,4U], with frequency |Δ| ≤ 2Y and U ≤ Y. -/
namespace Green64Analytic.CorrelationMellin

theorem sourcePhase_complete_large_frequency
    (delta : ℝ) (U : ℕ) (Y : ℝ)
    (hU : 1 ≤ U) (hY : 1 ≤ Y)
    (hUY : (U:ℝ) ≤ Y)
    (hdelta : (U:ℝ) ≤ |delta|)
    (hdeltaY : |delta| ≤ 2*Y) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n delta‖ ≤
      448 * Real.sqrt Y := by
  have hUpos : (0:ℝ) < U := by exact_mod_cast hU
  have hYnonneg : 0 ≤ Y := by linarith
  have hdelpos : 0 < |delta| := lt_of_lt_of_le hUpos hdelta
  have hsqrtUpos : 0 < Real.sqrt (U:ℝ) := Real.sqrt_pos.mpr hUpos
  have hsqrtDpos : 0 < Real.sqrt |delta| := Real.sqrt_pos.mpr hdelpos
  have hSqrtUleD : Real.sqrt (U:ℝ) ≤ Real.sqrt |delta| :=
    Real.sqrt_le_sqrt hdelta
  have hSqrtUleY : Real.sqrt (U:ℝ) ≤ Real.sqrt Y :=
    Real.sqrt_le_sqrt hUY
  have hDivUpper : (U:ℝ)/Real.sqrt |delta| ≤ Real.sqrt (U:ℝ) := by
    rw [div_le_iff₀ hsqrtDpos]
    calc
      (U:ℝ) = Real.sqrt (U:ℝ)*Real.sqrt (U:ℝ) := by
        rw [← pow_two, Real.sq_sqrt (le_of_lt hUpos)]
      _ ≤ Real.sqrt (U:ℝ)*Real.sqrt |delta| :=
        mul_le_mul_of_nonneg_left hSqrtUleD (Real.sqrt_nonneg _)
  have hSqrt4 : Real.sqrt (4*Y) = 2*Real.sqrt Y := by
    calc
      Real.sqrt (4*Y) = Real.sqrt (4:ℝ)*Real.sqrt Y :=
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4) Y
      _ = 2*Real.sqrt Y := by norm_num
  have hd4 : |delta| ≤ 4*Y := by linarith [hdeltaY]
  have hSqrtDleY : Real.sqrt |delta| ≤ 2*Real.sqrt Y := by
    calc
      _ ≤ Real.sqrt (4*Y) := Real.sqrt_le_sqrt hd4
      _ = _ := hSqrt4
  have hVdC := sourcePhase_complete_second_signed delta U hU hdelpos
  calc
    _ ≤ 128*Real.sqrt |delta| +
        192*(U:ℝ)/Real.sqrt |delta| := hVdC
    _ = 128*Real.sqrt |delta| +
        192*((U:ℝ)/Real.sqrt |delta|) := by ring
    _ ≤ 448*Real.sqrt Y := by linarith [hSqrtDleY, hDivUpper, hSqrtUleY]

theorem sourcePhase_complete_offdiagonal
    (delta : ℝ) (U : ℕ) (Y : ℝ)
    (hU : 1 ≤ U) (hY : 1 ≤ Y) (hUY : (U:ℝ) ≤ Y)
    (hdelta : 1 ≤ |delta|) (hdeltaY : |delta| ≤ 2*Y) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n delta‖ ≤
      40*(U:ℝ)/|delta| + 448*Real.sqrt Y := by
  have hdelpos : 0 < |delta| := by linarith
  by_cases hsmall : |delta| ≤ (U:ℝ)
  · have h := sourcePhase_complete_first_signed delta U hU hdelpos hsmall
    have hYnonneg : 0 ≤ Y := by linarith
    have hsqrt : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg _
    linarith
  · have hbig : (U:ℝ) ≤ |delta| := le_of_lt (lt_of_not_ge hsmall)
    have h := sourcePhase_complete_large_frequency
      delta U Y hU hY hUY hbig hdeltaY
    have hUpos : (0:ℝ) < U := by exact_mod_cast hU
    have hr : 0 ≤ 40*(U:ℝ)/|delta| := by positivity
    linarith
end Green64Analytic.CorrelationMellin

end

/-! ## SourceGramDiagonal -/

section

/-! The zero-frequency diagonal row entry is counted on [U,4U]
with the actual inclusive cardinality 3U+1. -/
namespace Green64Analytic.CorrelationMellin

theorem sourcePhase_complete_diagonal
    (U : ℕ) (hU : 1 ≤ U) :
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n 0‖ ≤
      4*(U:ℝ) := by
  have hcard : (Finset.Icc U (4*U)).card ≤ 4*U := by
    simp only [Nat.card_Icc]
    omega
  calc
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n 0‖ ≤
      ∑ n ∈ Finset.Icc U (4*U), ‖sourcePhase n 0‖ :=
        norm_sum_le _ _
    _ = ((Finset.Icc U (4*U)).card:ℝ) := by
      simp [sourcePhase_norm]
    _ ≤ 4*(U:ℝ) := by exact_mod_cast hcard
end Green64Analytic.CorrelationMellin

end

/-! ## SourceUnconditionalGramRows -/

section

/-! Unconditional row-sum estimate for the *complete* natural integer block
[U,4U] and arbitrary one-separated real times.  The analytic input is
the genuine real-frequency phase n^(iΔ), with proved first and second
finite-difference exponential-sum tests. -/
namespace Green64Analytic.CorrelationMellin

theorem source_complete_gram_row_unconditional
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (times : ι → ℝ) (U : ℕ) (Y : ℝ)
    (hU : 1 ≤ U) (hY : 1 ≤ Y) (hUY : (U:ℝ) ≤ Y)
    (hRange : ∀ j, |times j| ≤ Y)
    (hSep : ∀ i j, i ≠ j → 1 ≤ |times i - times j|) :
    ∀ i : ι,
    (∑ j : ι, ‖∑ n ∈ Finset.Icc U (4*U),
      sourcePhase n (times i - times j)‖) ≤
      448 * ((U:ℝ)*(1+Real.log (2*Y))+
        (Fintype.card ι:ℝ)*Real.sqrt Y) := by
  classical
  intro i
  let F : ι → ℝ := fun j =>
    ‖∑ n ∈ Finset.Icc U (4*U), sourcePhase n (times i-times j)‖
  let s : Finset ι := Finset.univ.erase i
  have hs : s = Finset.univ.filter (fun j : ι => j ≠ i) := by
    ext j
    simp [s]
  have hrecip :
      (∑ j ∈ s, |times i-times j|⁻¹) ≤
        2*(1+Real.log (2*Y)) := by
    rw [hs]
    exact source_separated_indexed_reciprocal
      times Y hY hRange hSep i
  have hOff (j : ι) (hj : j ∈ s) :
      F j ≤ 40*(U:ℝ)*|times i-times j|⁻¹+
        448*Real.sqrt Y := by
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hDelta : 1 ≤ |times i-times j| :=
      hSep i j (Ne.symm hne)
    have hDeltaY : |times i-times j| ≤ 2*Y := by
      have hi := abs_le.mp (hRange i)
      have hj' := abs_le.mp (hRange j)
      have habs := abs_sub (times i) (times j)
      linarith [hRange i, hRange j]
    have hbound := sourcePhase_complete_offdiagonal
      (times i-times j) U Y hU hY hUY hDelta hDeltaY
    simpa only [F, div_eq_mul_inv] using hbound
  have hCard : s.card ≤ Fintype.card ι := by
    calc
      s.card ≤ (Finset.univ : Finset ι).card :=
        Finset.card_le_card (Finset.erase_subset i _)
      _ = Fintype.card ι := Finset.card_univ
  have hU0 : 0 ≤ 40*(U:ℝ) := by positivity
  have hSqrt0 : 0 ≤ 448*Real.sqrt Y := by positivity
  have hOffSum :
      (∑ j ∈ s, F j) ≤
        80*(U:ℝ)*(1+Real.log (2*Y))+
        448*(Fintype.card ι:ℝ)*Real.sqrt Y := by
    calc
      _ ≤ ∑ j ∈ s, (40*(U:ℝ)*|times i-times j|⁻¹+
        448*Real.sqrt Y) := Finset.sum_le_sum hOff
      _ = 40*(U:ℝ)*(∑ j ∈ s, |times i-times j|⁻¹)+
          (s.card:ℝ)*(448*Real.sqrt Y) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          nsmul_eq_mul]
      _ ≤ 40*(U:ℝ)*(2*(1+Real.log (2*Y)))+
          (Fintype.card ι:ℝ)*(448*Real.sqrt Y) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hrecip hU0
        · exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hCard) hSqrt0
      _ = _ := by ring
  have hDiag : F i ≤ 4*(U:ℝ) := by
    simpa only [F, sub_self] using sourcePhase_complete_diagonal U hU
  have hTotal : (∑ j : ι, F j) = (∑ j ∈ s, F j) + F i := by
    simpa only [s] using
      (Finset.sum_erase_add (Finset.univ : Finset ι) F
        (Finset.mem_univ i)).symm
  have hLog0 : 0 ≤ Real.log (2*Y) :=
    Real.log_nonneg (by linarith : 1 ≤ 2*Y)
  have hU0' : 0 ≤ (U:ℝ) := Nat.cast_nonneg U
  have hSqrt0' : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hCard0 : 0 ≤ (Fintype.card ι:ℝ) := Nat.cast_nonneg _
  change (∑ j : ι, F j) ≤
      448*((U:ℝ)*(1+Real.log (2*Y))+
        (Fintype.card ι:ℝ)*Real.sqrt Y)
  rw [hTotal]
  nlinarith [hOffSum, hDiag,
    mul_nonneg hU0' hLog0,
    mul_nonneg hCard0 hSqrt0']
end Green64Analytic.CorrelationMellin

end

/-! ## SourceDyadicCoverGram -/

section

/-! Unconditional sparse real-time bound on an arbitrary finite
coefficient support partitioned into finitely many disjoint dyadic
blocks. The blocks use the original full [U,4U] Gram theorem with
zero padding, so no row hypothesis on restricted prime-power support
is needed. -/

namespace Green64Analytic.CorrelationMellin

theorem source_separated_finite_cover_sparse_unconditional
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (times : ι → ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (assign : ℕ → κ) (base : κ → ℕ) (Y : ℝ)
    (hY : 1 ≤ Y)
    (hU : ∀ k, 1 ≤ base k)
    (hUY : ∀ k, (base k : ℝ) ≤ Y)
    (hSupport : ∀ n ∈ s, n ∈ Finset.Icc (base (assign n)) (4*base (assign n)))
    (hRange : ∀ i, |times i| ≤ Y)
    (hSep : ∀ i j, i ≠ j → 1 ≤ |times i - times j|) :
    (∑ i : ι, ‖∑ n ∈ s, coeff n * sourcePhase n (times i)‖^2) ≤
      ((Fintype.card κ : ℝ) *
        (448*(Y*(1+Real.log (2*Y)) +
          (Fintype.card ι:ℝ)*Real.sqrt Y))) *
      (∑ n ∈ s, ‖coeff n‖^2) := by
  classical
  let B : ℝ := 448*(Y*(1+Real.log (2*Y)) +
    (Fintype.card ι:ℝ)*Real.sqrt Y)
  have hYpos : 0 < Y := by linarith
  have hlog : 0 ≤ 1+Real.log (2*Y) := by
    have h : 1 ≤ 2*Y := by linarith
    have hlog' := Real.log_nonneg h
    linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  let sf : κ → Finset ℕ := fun k => s.filter (fun n => assign n = k)
  have hSub (k : κ) : sf k ⊆ Finset.Icc (base k) (4*base k) := by
    intro n hn
    obtain ⟨hn, hassign⟩ := Finset.mem_filter.mp hn
    simpa only [hassign] using hSupport n hn
  have hFrame (k : κ) :
      (∑ i : ι, ‖∑ n ∈ sf k, coeff n * sourcePhase n (times i)‖^2) ≤
        B * (∑ n ∈ sf k, ‖coeff n‖^2) := by
    let padded : ℕ → ℂ := fun n => if n ∈ sf k then coeff n else 0
    have hRows (i : ι) :
        (∑ j : ι, ‖∑ n ∈ Finset.Icc (base k) (4*base k),
            sourcePhase n (times i - times j)‖) ≤ B := by
      have hrow := source_complete_gram_row_unconditional
        times (base k) Y (hU k) hY (hUY k) hRange hSep i
      have hu : (base k : ℝ)*(1+Real.log (2*Y)) ≤
          Y*(1+Real.log (2*Y)) :=
        mul_le_mul_of_nonneg_right (hUY k) hlog
      dsimp only [B]
      nlinarith [hrow, hu]
    have hBound := source_full_integer_block_sparse_of_gram_rows
      (base k) (4*base k) times padded B hB hRows
    have hPad (φ : ℕ → ℂ) :
        (∑ n ∈ Finset.Icc (base k) (4*base k), padded n * φ n) =
        (∑ n ∈ sf k, coeff n * φ n) := by
      calc
        _ = ∑ n ∈ sf k, padded n * φ n := by
          symm
          apply Finset.sum_subset (hSub k)
          intro n hn hnS
          simp [padded, hnS]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [padded, hn]
    have hPadNorm :
        (∑ n ∈ Finset.Icc (base k) (4*base k), ‖padded n‖^2) =
        (∑ n ∈ sf k, ‖coeff n‖^2) := by
      calc
        _ = ∑ n ∈ sf k, ‖padded n‖^2 := by
          symm
          apply Finset.sum_subset (hSub k)
          intro n hn hnS
          simp [padded, hnS]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [padded, hn]
    calc
      _ = ∑ i : ι,
        ‖∑ n ∈ Finset.Icc (base k) (4*base k),
           padded n * sourcePhase n (times i)‖^2 := by
             apply Finset.sum_congr rfl
             intro i _
             rw [hPad]
      _ ≤ B*(∑ n ∈ Finset.Icc (base k) (4*base k),
             ‖padded n‖^2) := hBound
      _ = _ := by rw [hPadNorm]
  have hDecomp (i : ι) :
      (∑ n ∈ s, coeff n * sourcePhase n (times i)) =
      ∑ k : κ, ∑ n ∈ sf k, coeff n * sourcePhase n (times i) := by
    symm
    calc
      _ = ∑ n ∈ s, ∑ k : κ,
          if assign n = k then coeff n * sourcePhase n (times i) else 0 := by
        simp only [sf, Finset.sum_filter]
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n _
        simp
  have hPoint (i : ι) :
      ‖∑ n ∈ s, coeff n * sourcePhase n (times i)‖^2 ≤
      (Fintype.card κ : ℝ) *
        (∑ k : κ, ‖∑ n ∈ sf k, coeff n * sourcePhase n (times i)‖^2) := by
    rw [hDecomp]
    calc
      _ ≤ (∑ k : κ, ‖∑ n ∈ sf k,
        coeff n * sourcePhase n (times i)‖)^2 := by
          gcongr
          exact norm_sum_le _ _
      _ ≤ _ := by
        simpa only [Finset.card_univ] using
          (sq_sum_le_card_mul_sum_sq :
            (∑ k : κ, ‖∑ n ∈ sf k,
                 coeff n * sourcePhase n (times i)‖)^2 ≤
            ((Finset.univ : Finset κ).card : ℝ) *
              (∑ k : κ, ‖∑ n ∈ sf k,
                 coeff n * sourcePhase n (times i)‖^2))
  have hPartition :
      (∑ k : κ, ∑ n ∈ sf k, ‖coeff n‖^2) =
      ∑ n ∈ s, ‖coeff n‖^2 := by
    simp only [sf, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    simp
  calc
    _ ≤ ∑ i : ι, (Fintype.card κ : ℝ) *
        (∑ k : κ, ‖∑ n ∈ sf k,
          coeff n * sourcePhase n (times i)‖^2) :=
      Finset.sum_le_sum (fun i _ => hPoint i)
    _ = (Fintype.card κ:ℝ) *
        ∑ k : κ, ∑ i : ι,
          ‖∑ n ∈ sf k, coeff n * sourcePhase n (times i)‖^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Fintype.card κ:ℝ) *
        ∑ k : κ, B*(∑ n ∈ sf k, ‖coeff n‖^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun k _ => hFrame k)
    _ = (Fintype.card κ:ℝ)*B*
        (∑ n ∈ s, ‖coeff n‖^2) := by
      rw [← Finset.mul_sum, hPartition]
      ring
    _ = _ := rfl
end Green64Analytic.CorrelationMellin

end

/-! ## SourceDyadicFullGram -/

section

/-! Complete [1,Y] separated-point mean-square inequality from the
unconditional [U,4U] Gram kernel. Dyadic assignment is literal
floor(log₂ n), with disjoint fibres. The resulting upper bound has
a harmless multiplicative (log₂ Y+1) factor and an explicit
(#times)*sqrt(Y) term; the latter must be absorbed when applying
the growing factorial moment to exceptional times. -/

namespace Green64Analytic.CorrelationMellin

theorem source_full_unit_to_Y_sparse_unconditional
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (times : ι → ℝ) (Y : ℕ) (coeff : ℕ → ℂ)
    (hY : 1 ≤ Y)
    (hRange : ∀ i, |times i| ≤ (Y:ℝ))
    (hSep : ∀ i j, i ≠ j → 1 ≤ |times i-times j|) :
    (∑ i : ι, ‖∑ n ∈ Finset.Icc 1 Y,
        coeff n * sourcePhase n (times i)‖^2) ≤
      ((Nat.log2 Y+1 : ℕ) : ℝ) *
        (448*((Y:ℝ)*(1+Real.log (2*(Y:ℝ)))+
            (Fintype.card ι:ℝ)*Real.sqrt (Y:ℝ))) *
      (∑ n ∈ Finset.Icc 1 Y, ‖coeff n‖^2) := by
  classical
  let K : ℕ := Nat.log2 Y+1
  let base : Fin K → ℕ := fun k => 2^k.val
  let assign (n : ℕ) : Fin K :=
    ⟨min (Nat.log2 n) (Nat.log2 Y),
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hYpos : Y ≠ 0 := by omega
  have hU (k : Fin K) : 1 ≤ base k := by
    dsimp [base]
    have hp : 0 < (2:ℕ)^k.val := pow_pos (by norm_num) _
    omega
  have hUY (k : Fin K) : (base k:ℝ) ≤ (Y:ℝ) := by
    have hk : k.val ≤ Nat.log2 Y := by
      have hklt := k.isLt
      dsimp [K] at hklt
      omega
    have hpow : (2:ℕ)^k.val ≤ (2:ℕ)^(Nat.log2 Y) := by
      exact pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) hk
    have hy : (2:ℕ)^(Nat.log2 Y) ≤ Y :=
      (Nat.le_log2 hYpos).mp le_rfl
    exact_mod_cast hpow.trans hy
  have hSupport (n : ℕ) (hn : n ∈ Finset.Icc 1 Y) :
      n ∈ Finset.Icc (base (assign n)) (4*base (assign n)) := by
    obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have hlo : (2:ℕ)^(Nat.log2 n) ≤ n :=
      (Nat.le_log2 hn0).mp le_rfl
    have hlog : Nat.log2 n ≤ Nat.log2 Y :=
      (Nat.le_log2 hYpos).mpr (hlo.trans hnY)
    have hhi : n < (2:ℕ)^(Nat.log2 n+1) := by
      apply Nat.lt_of_not_ge
      intro h
      have he := (Nat.le_log2 hn0).mpr h
      omega
    have hbase : base (assign n) = (2:ℕ)^(Nat.log2 n) := by
      simp only [base, assign, Nat.min_eq_left hlog]
    rw [pow_succ] at hhi
    rw [Finset.mem_Icc, hbase]
    constructor
    · exact hlo
    · omega
  have hYreal : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have h := source_separated_finite_cover_sparse_unconditional
    (κ := Fin K) times (Finset.Icc 1 Y) coeff assign base (Y:ℝ)
    hYreal hU hUY hSupport hRange hSep
  simpa only [Fintype.card_fin, K] using h
end Green64Analytic.CorrelationMellin

end

/-! ## SourceExceptionalUnconditionalGram -/

section

/-! Fully unconditional source exceptional prime-power moment estimate
for exact j₀ = floor(log Y/log(2P)), genuine b(p)/p, prime
factorial collapse and arbitrary one-separated real frequencies.
The right side retains its explicit self term (#J)*sqrt(Y); its
absorption is a separate elementary real-inequality obligation. -/

namespace Green64Analytic.CorrelationMellin

theorem source_exceptional_log_count_unconditional_self_term
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (times : ι → ℝ) (s : Finset ℕ) (P Y : ℕ) (C δ : ℝ)
    (hP : 1 ≤ P) (hY : 1 ≤ Y)
    (hprime : ∀ p ∈ s, Nat.Prime p)
    (hSupport : s ⊆ Finset.Icc P (2*P))
    (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (b : ℕ → ℂ) (hb : ∀ p ∈ s, ‖b p‖ ≤ C)
    (hRange : ∀ i, |times i| ≤ (Y:ℝ))
    (hSep : ∀ i j, i ≠ j → 1 ≤ |times i-times j|)
    (hlarge : ∀ i : ι,
      δ ≤ ‖∑ p : {p : ℕ // p ∈ s},
        (b p.val * ((p.val:ℂ)⁻¹)) * sourcePhase p.val (times i)‖) :
    (Fintype.card ι : ℝ) * δ ^ (2*(sourcePrimeMomentOrder P Y)) ≤
      (((Nat.log2 Y+1 : ℕ):ℝ) *
        (448*((Y:ℝ)*(1+Real.log (2*(Y:ℝ))) +
          (Fintype.card ι:ℝ)*Real.sqrt (Y:ℝ)))) *
      ((Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
        (2*C^2/(P:ℝ))^(sourcePrimeMomentOrder P Y)) := by
  classical
  let j := sourcePrimeMomentOrder P Y
  let w : {p : ℕ // p ∈ s} → ℂ :=
    fun p => b p.val * ((p.val:ℂ)⁻¹)
  let support := sourcePrimePowerSupport s j
  let coeff := sourcePrimePowerCoefficients s j w
  let padded : ℕ → ℂ := fun n => if n ∈ support then coeff n else 0
  let B : ℝ := (((Nat.log2 Y+1 : ℕ):ℝ) *
    (448*((Y:ℝ)*(1+Real.log (2*(Y:ℝ))) +
      (Fintype.card ι:ℝ)*Real.sqrt (Y:ℝ))))
  have hYreal : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hB : 0 ≤ B := by
    dsimp [B]
    have hLog : 0 ≤ Real.log (2*(Y:ℝ)) :=
      Real.log_nonneg (by linarith)
    positivity
  have hPow : (2*P)^j ≤ Y :=
    (source_prime_moment_order_power_bounds P Y hP hY).1
  have hFull : support ⊆ Finset.Icc 1 Y :=
    source_prime_power_support_within_Y s j P Y hP hSupport hPow
  have hPad (φ : ℕ → ℂ) :
      (∑ n ∈ Finset.Icc 1 Y, padded n * φ n) =
        ∑ n ∈ support, coeff n * φ n := by
    calc
      _ = ∑ n ∈ support, padded n * φ n := by
        symm
        apply Finset.sum_subset hFull
        intro n hn hnS
        simp [padded, hnS]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [padded, hn]
  have hPadNorm :
      (∑ n ∈ Finset.Icc 1 Y, ‖padded n‖^2) =
        ∑ n ∈ support, ‖coeff n‖^2 := by
    calc
      _ = ∑ n ∈ support, ‖padded n‖^2 := by
        symm
        apply Finset.sum_subset hFull
        intro n hn hnS
        simp [padded, hnS]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [padded, hn]
  have hFrame := source_full_unit_to_Y_sparse_unconditional
    times Y padded hY hRange hSep
  have hSparse :
      (∑ i : ι, ‖∑ n ∈ support,
         coeff n * sourcePhase n (times i)‖^2) ≤
      B * ∑ n ∈ support, ‖coeff n‖^2 := by
    calc
      _ = ∑ i : ι, ‖∑ n ∈ Finset.Icc 1 Y,
           padded n * sourcePhase n (times i)‖^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hPad]
      _ ≤ B * ∑ n ∈ Finset.Icc 1 Y, ‖padded n‖^2 := by
        simpa only [B] using hFrame
      _ = _ := by rw [hPadNorm]
  have hCount := source_exceptional_count_of_power_evaluation
      (Finset.univ : Finset ι) times s j hprime w δ B hδ hB
      (by intro i _; exact hlarge i) (by simpa only [support, coeff] using hSparse)
  have hSq : (∑ p : {p : ℕ // p ∈ s}, ‖w p‖^2) ≤
      2*C^2/(P:ℝ) := by
    have heq : (∑ p : {p : ℕ // p ∈ s}, ‖w p‖^2) =
        ∑ p ∈ s, ‖b p * ((p:ℂ)⁻¹)‖^2 := by
      simpa only [w] using (Finset.sum_subtype s (fun p => Iff.rfl)
        (fun p => ‖b p * ((p:ℂ)⁻¹)‖^2)).symm
    rw [heq]
    exact source_short_prime_reciprocal_square_budget s P C b
      hP hC hSupport hb
  have hPowSq :
      (∑ p : {p : ℕ // p ∈ s}, ‖w p‖^2)^j ≤
      (2*C^2/(P:ℝ))^j := by
    gcongr
  calc
    _ ≤ B*((j.factorial:ℝ) *
           (∑ p : {p : ℕ // p ∈ s}, ‖w p‖^2)^j) := by
      simpa only [Finset.card_univ, j] using hCount
    _ ≤ B*((j.factorial:ℝ) * (2*C^2/(P:ℝ))^j) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact mul_le_mul_of_nonneg_left hPowSq (Nat.cast_nonneg _)
    _ = _ := rfl
end Green64Analytic.CorrelationMellin

end

