module

public import Green64.Library.Weights.SourceU1LogPowerBudget
public import Mathlib
public import Green64.Library.Weights.Part012
public import Green64.Library.Analysis.Estimates.Part002
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part016
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Analysis / Estimates / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceU1HighFrequencyLogSaving -/

section

open MeasureTheory
namespace Green64Analytic.LongPrime

/-! Full numerical log-power saving for the original shifted long-prime
factor, given the already-certified (4.32) physical residual integral
bound as a *precisely exposed* interface. This does NOT replay that
4.32 theorem within the distinct 4.34.1 Lean environment. -/
theorem source_shifted_U1_high_frequency_log_saving
    (τ η Cχ : ℝ) (a c D : ℕ)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) :
    ∃ B₀ Ku X₀ : ℝ, 0 < B₀ ∧ 0 < Ku ∧ 3 ≤ X₀ ∧
    ∀ x : ℝ, X₀ ≤ x →
    ∀ N : ℝ, x^τ/2 ≤ N → N ≤ x^η →
    ∀ q : ℕ, 1 ≤ q → (q:ℝ) ≤ (Real.log x)^Cχ →
    ∀ χ : DirichletCharacter ℂ q,
    ∀ I : Set ℝ, Set.OrdConnected I →
      I ⊆ Set.Icc N (2*N) →
    ∀ (σ : ℝ) (J : Finset ℤ) (F : ℝ → ℂ),
      Continuous F →
      (∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
         (Real.log x)^B₀ + |σ| ≤ |t|) →
      (∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
         |t+σ| ≤ x^2) →
    ∀ (L Y Acoef Ccoef Kmark : ℝ),

      L = Real.log x →
      3 ≤ L → 1 ≤ Y → Y ≤ Real.exp (2*L) →
      0 ≤ Acoef → Acoef ≤ L^a →
      0 ≤ Ccoef → Ccoef ≤ L^c →
      0 ≤ Kmark →
      10752*256*(Kmark*Ku)^2 ≤ L →
      (∑ j ∈ J,
         ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1), ‖F t‖^2) ≤
         10752*(Acoef*Ccoef*Kmark)^2*
           (1+Real.log (4*Y))^4 →
      (∑ j ∈ J,
        ∫ t in Set.Icc (j:ℝ) ((j:ℝ)+1),
          ‖sourceCorrelationLongPrime q χ N I (t+σ) * F t‖^2) ≤
      1/L^D := by
  have hAccuracy : 0 < ((a+c+D+4 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < a+c+D+4)
  obtain ⟨B₀,Ku,X₀,hB₀,hKu,hX₀,hU1⟩ :=
    source_shifted_U1_high_frequency_interval_energy τ η Cχ
      ((a+c+D+4 : ℕ) : ℝ) hτ hτη hη hCχ hAccuracy
  refine ⟨B₀,Ku,X₀,hB₀,hKu,hX₀,?_⟩
  intro x hx N hNl hNu q hq hqC χ I hI hSub
    σ J F hF hLow hHigh
    L Y Acoef Ccoef Kmark hL hL3 hY hYmax
    hAcoef hAmax hCcoef hCmax hKmark hKthreshold hResidual
  have hLongBound :=
    hU1 x hx N hNl hNu q hq hqC χ I hI hSub
      σ J F hF hLow hHigh
      (10752*(Acoef*Ccoef*Kmark)^2*
        (1+Real.log (4*Y))^4) hResidual

  have hNum :=
    source_U1_arbitrary_log_power_numeric
      L Y Acoef Ccoef Kmark Ku a c D
      hL3 hY hYmax hAcoef hCcoef hAmax hCmax
      hKmark (le_of_lt hKu) hKthreshold
  rw [← hL] at hLongBound
  simp only [Real.rpow_natCast] at hLongBound
  exact hLongBound.trans hNum
end Green64Analytic.LongPrime

end

/-! ## SourceU1GrowingMarkBudget -/

section

namespace Green64Analytic.LongPrime

/-! Unlike SourceU1HighFrequencyLogSaving434, the mark coefficient
may grow with L. The original |S|+|B|=O(log L) budget is absorbed
by choosing a larger fixed U1 exponent, not by assuming Kmark fixed. -/

/-- The numerical U1 saving remains uniform when the complete marked
source coefficient grows by a known fixed power of L. -/
theorem source_U1_growing_mark_numeric
    (L Y A C Kmark Ku : ℝ) (a c g D : ℕ)
    (hL : 3 ≤ L) (hY : 1 ≤ Y)
    (hYupper : Y ≤ Real.exp (2*L))
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hAle : A ≤ L^a) (hCle : C ≤ L^c)
    (hKm : 0 ≤ Kmark) (hKupper : Kmark ≤ L^g)
    (hKu : 0 ≤ Ku)
    (hthreshold : 10752*256*Ku^2 ≤ L) :
    (Ku/L^(a+c+g+D+4))^2 *
      (10752*(A*C*Kmark)^2*(1+Real.log (4*Y))^4)
      ≤ 1/L^D := by
  have hLpos : 0 ≤ L := by linarith
  have hCnew : 0 ≤ C*Kmark := mul_nonneg hC hKm
  have hCbound : C*Kmark ≤ L^(c+g) := by
    calc
      C*Kmark ≤ L^c*L^g := by gcongr
      _ = L^(c+g) := (pow_add L c g).symm
  have hNum :=
    source_U1_arbitrary_log_power_numeric
      L Y A (C*Kmark) 1 Ku a (c+g) D
      hL hY hYupper hA hCnew hAle hCbound
      (by norm_num) hKu (by simpa using hthreshold)
  have hPower : a+(c+g)+D+4 = a+c+g+D+4 := by omega
  simpa only [hPower, mul_one, one_mul, mul_assoc] using hNum

end Green64Analytic.LongPrime

end

/-! ## SourceUniformCutoffBudget -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap BigOperators
set_option maxHeartbeats 4000000
namespace Green64Analytic.CorrelationMellin

/-- Exactly the source logarithmic derivative regularity budget. The constants
K_j are fixed before L and the chosen function. -/
def sourceLogDerivativeBudget (C : ℝ) (K : ℕ → ℝ) (L : ℝ)
    (f : ℝ → ℂ) : Prop :=
  ∀ j u, ‖iteratedDeriv j f u‖ ≤ K j * L^(C*((j:ℝ)+1))

/-- Compact support controls the derivative L1 norms with no tail hypothesis. -/
theorem source_cutoff_derivative_integral_bound
    (f : 𝓢(ℝ,ℂ)) (B M : ℝ) (j : ℕ) (hB : 0 ≤ B)
    (hSupp : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (hDeriv : ∀ u, ‖iteratedDeriv j (f : ℝ → ℂ) u‖ ≤ M) :
    (∫ u : ℝ, ‖iteratedFDeriv ℝ j (f : ℝ → ℂ) u‖) ≤ 2*B*M := by
  have hZero (u : ℝ) (hu : u ∉ Set.Icc (-B) B) :
      ‖iteratedFDeriv ℝ j (f : ℝ → ℂ) u‖ = 0 := by
    have h : iteratedFDeriv ℝ j (f : ℝ → ℂ) u = 0 := by
      by_contra hn
      exact hu (hSupp ((support_iteratedFDeriv_subset j) hn))
    simp only [h,norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hZero]
  have hInt : Integrable (fun u : ℝ => ‖iteratedFDeriv ℝ j (f : ℝ → ℂ) u‖) := by
    simpa using f.integrable_pow_mul_iteratedFDeriv volume 0 j
  calc
    _ ≤ ∫ u in Set.Icc (-B) B, M :=
      setIntegral_mono_on hInt.integrableOn
        (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) measurableSet_Icc
        (fun u hu => by simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hDeriv u)
    _ = 2*B*M := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ B-(-B)),smul_eq_mul]
      ring

/-- Uniform integration-by-parts tail at any positive radius, for the source
family derivative budget. Unlike a fixed-bump asymptotic, f is quantified AFTER L. -/
theorem source_cutoff_family_fourier_tail
    (C B : ℝ) (K : ℕ → ℝ) (L R : ℝ) (N : ℕ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : ∀ j, 0 ≤ K j)
    (hL : 1 ≤ L) (hR : 0 < R) (hN : 2 ≤ N)
    (f : 𝓢(ℝ,ℂ)) (hSupp : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (hBudget : sourceLogDerivativeBudget C K L f) :
    (∫ xi in {xi : ℝ | R ≤ |xi|}, ‖(𝓕 f) xi‖) ≤
      (4*B*2^N*(∑ j ∈ Finset.range (N+1), K j) / ((N:ℝ)-1)) *
        L^(C*((N:ℝ)+1)) * R^(-(N:ℝ)+1) := by
  let S : ℝ := ∑ j ∈ Finset.range (N+1), K j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j hj => hK j)
  have hInt (j : ℕ) (hj : j ∈ Finset.range (N+1)) :
      (∫ u : ℝ, ‖iteratedFDeriv ℝ j (f : ℝ → ℂ) u‖) ≤
        2*B*K j*L^(C*((N:ℝ)+1)) := by
    have hb := source_cutoff_derivative_integral_bound f B
      (K j*L^(C*((j:ℝ)+1))) j hB hSupp (hBudget j)
    have hjN : (j:ℝ) ≤ N := by exact_mod_cast (Finset.mem_range_succ_iff.mp hj)
    have hPow : L^(C*((j:ℝ)+1)) ≤ L^(C*((N:ℝ)+1)) :=
      Real.rpow_le_rpow_of_exponent_le hL (mul_le_mul_of_nonneg_left (by linarith) hC)
    exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hPow (mul_nonneg (by positivity : 0 ≤ 2*B) (hK j))])
  have hDecay (xi : ℝ) :
      |xi|^N * ‖(𝓕 f) xi‖ ≤ 2^N*(2*B*S*L^(C*((N:ℝ)+1))) := by
    calc
      _ ≤ 2^N * ∑ j ∈ Finset.range (N+1),
          ∫ u : ℝ, ‖iteratedFDeriv ℝ j (f : ℝ → ℂ) u‖ :=
        source_uniform_fourier_decay f N xi
      _ ≤ 2^N * ∑ j ∈ Finset.range (N+1), 2*B*K j*L^(C*((N:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hInt) (by positivity)
      _ = _ := by simp only [S,Finset.sum_mul,Finset.mul_sum] <;> ring
  have ht := source_uniform_fourier_tail_from_decay f N R
    (2^N*(2*B*S*L^(C*((N:ℝ)+1)))) hN hR (by positivity) hDecay
  exact ht.trans_eq (by dsimp [S]; ring)

/-- The precise source exponent C(N+1)-F(N-1), with fixed F. -/
theorem source_cutoff_family_fourier_log_tail
    (C B F : ℝ) (K : ℕ → ℝ) (L : ℝ) (N : ℕ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : ∀ j, 0 ≤ K j)
    (hL : 1 ≤ L) (hN : 2 ≤ N)
    (f : 𝓢(ℝ,ℂ)) (hSupp : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (hBudget : sourceLogDerivativeBudget C K L f) :
    (∫ xi in {xi : ℝ | L^F ≤ |xi|}, ‖(𝓕 f) xi‖) ≤
      (4*B*2^N*(∑ j ∈ Finset.range (N+1), K j) / ((N:ℝ)-1)) *
        L^(C*((N:ℝ)+1)-F*((N:ℝ)-1)) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ht := source_cutoff_family_fourier_tail C B K L (L^F) N
    hC hB hK hL (Real.rpow_pos_of_pos hLp F) hN f hSupp hBudget
  have hp : L^(C*((N:ℝ)+1)) * (L^F)^(-(N:ℝ)+1) =
      L^(C*((N:ℝ)+1)-F*((N:ℝ)-1)) := by
    rw [← Real.rpow_mul hLp.le, ← Real.rpow_add hLp]
    congr 1
    ring
  simpa only [mul_assoc, hp] using ht
end Green64Analytic.CorrelationMellin

end

/-! ## SourceHarmonicProfileBudget -/

section

open MeasureTheory Filter
open scoped SchwartzMap ContDiff Topology
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 8000000

/-- Remove the harmless exp(u) factor from the already proved compact
source logarithmic window. The original smooth function is unchanged. -/
theorem source_plain_log_profile_compact434
    (A : ℝ) (psi : ℝ → ℂ) (hA : 1 ≤ A)
    (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A) :
    HasCompactSupport (fun u : ℝ => psi (Real.exp u)) := by
  have hc := source_actual_log_window_hasCompactSupport A psi hA hSupport
  have hm : HasCompactSupport
      ((fun u : ℝ => ((Real.exp u:ℝ):ℂ)⁻¹)*sourceActualLogWindow psi) := hc.mul_left
  have heq : ((fun u : ℝ => ((Real.exp u:ℝ):ℂ)⁻¹)*sourceActualLogWindow psi) =
      (fun u : ℝ => psi (Real.exp u)) := by
    funext u
    have he : ((Real.exp u:ℝ):ℂ) ≠ 0 := by exact_mod_cast (Real.exp_ne_zero u)
    simp only [Pi.mul_apply,sourceActualLogWindow,←mul_assoc,inv_mul_cancel₀ he,one_mul]
  rwa [heq] at hm

noncomputable def sourcePlainLogProfileSchwartz434
    (A : ℝ) (psi : ℝ → ℂ) (hA : 1 ≤ A) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A) : SchwartzMap ℝ ℂ :=
  (source_plain_log_profile_compact434 A psi hA hSupport).toSchwartzMap
    (hSmooth.comp Real.contDiff_exp)

/-- A fixed pair of genuine smooth positive-support cutoffs, including
psi(r)/r, has a common derivative budget chosen BEFORE L and every frequency. -/
theorem source_fixed_harmonic_profile_budget434
    (A : ℝ) (psi : ℝ → ℂ) (hA : 1 ≤ A) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A) :
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧ ∀ L : ℝ,
      sourceLogDerivativeBudget 0 K L (fun u => psi (Real.exp u)) ∧
      sourceLogDerivativeBudget 0 K L (fun u => psi (Real.exp u)/((Real.exp u:ℝ):ℂ)) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let psiR : ℝ → ℂ := fun r => psi r/(r:ℂ)
  have hR : ContDiff ℝ ∞ psiR := source_harmonic_reciprocal_smooth434
    psi (1/A) (one_div_pos.mpr hAp) hSmooth (fun r hr => (hSupport r hr).1)
  have hSuppR : ∀ r, psiR r ≠ 0 → 1/A ≤ r ∧ r ≤ A := by
    intro r hr
    apply hSupport r
    intro hz
    apply hr
    simp only [psiR,hz,zero_div]
  let f := sourcePlainLogProfileSchwartz434 A psi hA hSmooth hSupport
  let g := sourcePlainLogProfileSchwartz434 A psiR hA hR hSuppR
  have hfcoe : (f : ℝ → ℂ) = (fun u => psi (Real.exp u)) := rfl
  have hgcoe : (g : ℝ → ℂ) = (fun u => psi (Real.exp u)/((Real.exp u:ℝ):ℂ)) := rfl
  choose Kf hKf hBf using fun j => f.decay 0 j
  choose Kg hKg hBg using fun j => g.decay 0 j
  refine ⟨(fun j => Kf j+Kg j),fun j => by linarith [hKf j,hKg j],?_⟩
  intro L
  constructor
  · intro j u
    have h := hBf j u
    rw [hfcoe] at h
    have hn : ‖iteratedDeriv j (fun u => psi (Real.exp u)) u‖ ≤ Kf j := by
      have h0 : ‖iteratedFDeriv ℝ j (fun u => psi (Real.exp u)) u‖ ≤ Kf j := by
        simpa only [pow_zero,one_mul] using h
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using h0
    simp only [zero_mul,Real.rpow_zero,mul_one]
    linarith [hKg j]
  · intro j u
    have h := hBg j u
    rw [hgcoe] at h
    have hn : ‖iteratedDeriv j (fun u => psi (Real.exp u)/((Real.exp u:ℝ):ℂ)) u‖ ≤ Kg j := by
      have h0 : ‖iteratedFDeriv ℝ j (fun u => psi (Real.exp u)/((Real.exp u:ℝ):ℂ)) u‖ ≤ Kg j := by
        simpa only [pow_zero,one_mul] using h
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using h0
    simp only [zero_mul,Real.rpow_zero,mul_one]
    linarith [hKf j]

/-- Existence of both required physical profiles with a fixed common
source budget. Neither an artificial Gaussian nor a Fourier lower-bound
assumption is introduced at this stage. -/
theorem source_fixed_harmonic_profiles_exist434 (A : ℝ) (hA : 1 ≤ A) :
    ∃ (psi : ℝ → ℂ) (K : ℕ → ℝ), ContDiff ℝ ∞ psi ∧
      ContDiff ℝ ∞ (fun r => psi r/(r:ℂ)) ∧
      (∀ r, psi r ≠ 0 → 1/(4*A) ≤ r ∧ r ≤ 4*A) ∧
      (∀ r ∈ Set.Icc (1/A) A, psi r = 1) ∧ (∀ j, 0 ≤ K j) ∧
      ∀ L : ℝ, sourceLogDerivativeBudget 0 K L (fun u => psi (Real.exp u)) ∧
        sourceLogDerivativeBudget 0 K L (fun u => psi (Real.exp u)/((Real.exp u:ℝ):ℂ)) := by
  obtain ⟨psi,hSmooth,hCompact,hSupport,hOne,hBound⟩ := source_harmonic_physical_window434 A hA
  have h4A : 1 ≤ 4*A := by linarith
  have hPos : 0 < 1/(4*A) := by positivity
  obtain ⟨K,hK,hBudget⟩ := source_fixed_harmonic_profile_budget434 (4*A) psi h4A hSmooth hSupport
  exact ⟨psi,K,hSmooth,source_harmonic_reciprocal_smooth434 psi (1/(4*A)) hPos hSmooth
    (fun r hr => (hSupport r hr).1),hSupport,hOne,hK,hBudget⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceHarmonicWindowInsertion -/

section

open MeasureTheory Filter
open scoped ContDiff
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 8000000

/-- The genuine hard log cell supplies its physical range without using
an integer support cap in place of the actual cell scale. -/
theorem source_original_logcell_real_range434 (F : Finset ℕ) (U h : ℝ)
    (b : ℕ → ℂ) (hU : 0 < U) (hh : h ≤ 1) (n : ℕ)
    (hne : sourceOriginalLogCellMask434 F U h b n ≠ 0) :
    0 < n ∧ U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 3*U := by
  unfold sourceOriginalLogCellMask434 at hne
  split_ifs at hne with hc
  · have hnp : 0 < (n:ℝ) := by exact_mod_cast hc.2.1
    have hl : U ≤ (n:ℝ) := by
      simpa only [Real.exp_log hU,Real.exp_log hnp] using Real.exp_le_exp.mpr hc.2.2.1
    have hu : (n:ℝ) < U*Real.exp h := by
      simpa only [Real.exp_log hU,Real.exp_log hnp,Real.exp_add] using
        Real.exp_lt_exp.mpr hc.2.2.2
    have he : Real.exp h < 3 := (Real.exp_le_exp.mpr hh).trans_lt Real.exp_one_lt_three
    refine ⟨hc.2.1,hl,?_⟩
    nlinarith
  · exact (hne rfl).elim

/-- Positive source shift geometry. Both physical endpoints lie in the
fixed window [Y/(18A),18AY], including negative signed shifts. -/
theorem source_harmonic_shift_window434
    (A Y R w wp delta : ℝ) (hA : 1 ≤ A) (hY : 0 < Y)
    (hRlo : Y ≤ R) (hRhi : R ≤ 9*Y)
    (hw : 1/A ≤ w/R ∧ w/R ≤ A)
    (hDelta : |delta| ≤ R/(2*A)) (hwp : wp=w+delta) :
    w/Y ∈ Set.Icc (1/(18*A)) (18*A) ∧
      wp/Y ∈ Set.Icc (1/(18*A)) (18*A) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hRp : 0 < R := hY.trans_le hRlo
  have hWlo : R ≤ A*w := by
    have h := (div_le_div_iff₀ hAp hRp).mp hw.1
    nlinarith
  have hWhi : w ≤ A*R := (div_le_iff₀ hRp).mp hw.2
  have hD := abs_le.mp hDelta
  have hDlo : -R ≤ (2*A)*delta := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*A)).mp
      (show -delta ≤ R/(2*A) by linarith [hD.1])
    nlinarith
  have hDhi : (2*A)*delta ≤ R := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 2*A)).mp hD.2
  have hWpLo : R ≤ (2*A)*wp := by nlinarith
  have hWpHi : wp ≤ 2*A*R := by
    have h1 : R ≤ 2*A^2*R := by nlinarith [sq_nonneg (A-1)]
    nlinarith
  have hWP : 0 < w := by nlinarith
  have hWpP : 0 < wp := by nlinarith
  have hLower (v : ℝ) (hv : 0 < v) (h : R ≤ 2*A*v) : 1/(18*A) ≤ v/Y := by
    apply (div_le_div_iff₀ (by positivity : 0 < 18*A) hY).mpr
    nlinarith
  have hUpper (v : ℝ) (h : v ≤ 2*A*R) : v/Y ≤ 18*A := by
    apply (div_le_iff₀ hY).mpr
    nlinarith
  exact ⟨⟨hLower w hWP (by nlinarith),hUpper w (by nlinarith)⟩,
    ⟨hLower wp hWpP hWpLo,hUpper wp hWpHi⟩⟩

/-- Exact cutoff insertion on the ORIGINAL pair of hard log cells. The
scale remains Y=Z*U1*U2; no Ncap or rounded integer replaces it. -/
theorem source_original_logcell_window_insertion434
    (F1 F2 : Finset ℕ) (U1 U2 h1 h2 : ℝ) (b1 b2 : ℕ → ℂ)
    (da db : ℕ) (A Z Y w wp k : ℝ) (psi chi : ℝ → ℂ)
    (hU1 : 0 < U1) (hU2 : 0 < U2) (hh1 : h1 ≤ 1) (hh2 : h2 ≤ 1)
    (ha : sourceOriginalLogCellMask434 F1 U1 h1 b1 da ≠ 0)
    (hb : sourceOriginalLogCellMask434 F2 U2 h2 b2 db ≠ 0)
    (hA : 1 ≤ A) (hZ : 0 < Z) (hY : Y=Z*(U1*U2))
    (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hPsi : psi (w/(Z*(da:ℝ)*(db:ℝ))) ≠ 0)
    (hK : |k| ≤ Z/(2*A)) (hShift : wp=w+k*(da:ℝ)*(db:ℝ))
    (hOne : ∀ r ∈ Set.Icc (1/(18*A)) (18*A), chi r=1) :
    chi (w/Y)=1 ∧ chi (wp/Y)=1 := by
  obtain ⟨hda,hdaLo,hdaHi⟩ := source_original_logcell_real_range434 F1 U1 h1 b1 hU1 hh1 da ha
  obtain ⟨hdb,hdbLo,hdbHi⟩ := source_original_logcell_real_range434 F2 U2 h2 b2 hU2 hh2 db hb
  have hYP : 0 < Y := by rw [hY]; positivity
  have hProdLo : U1*U2 ≤ (da:ℝ)*(db:ℝ) :=
    mul_le_mul hdaLo hdbLo hU2.le (Nat.cast_nonneg da)
  have hProdHi : (da:ℝ)*(db:ℝ) ≤ 9*(U1*U2) := by
    have h := mul_le_mul hdaHi hdbHi (Nat.cast_nonneg db) (by positivity : 0 ≤ 3*U1)
    nlinarith
  have hLo : Y ≤ Z*(da:ℝ)*(db:ℝ) := by
    rw [hY]
    nlinarith [mul_le_mul_of_nonneg_left hProdLo hZ.le]
  have hHi : Z*(da:ℝ)*(db:ℝ) ≤ 9*Y := by
    rw [hY]
    nlinarith [mul_le_mul_of_nonneg_left hProdHi hZ.le]
  have hDelta : |k*(da:ℝ)*(db:ℝ)| ≤ (Z*(da:ℝ)*(db:ℝ))/(2*A) := by
    simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg da : (0:ℝ) ≤ (da:ℝ)),
      abs_of_nonneg (Nat.cast_nonneg db : (0:ℝ) ≤ (db:ℝ))]
    calc
      _ ≤ (Z/(2*A))*(da:ℝ)*(db:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg da)) (Nat.cast_nonneg db)
      _ = _ := by ring
  have hW := source_harmonic_shift_window434 A Y (Z*(da:ℝ)*(db:ℝ)) w wp
    (k*(da:ℝ)*(db:ℝ)) hA hYP hLo hHi (hSupport _ hPsi) hDelta hShift
  exact ⟨hOne _ hW.1,hOne _ hW.2⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalLogDerivative -/

section

open scoped BigOperators ContDiff SchwartzMap
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 6000000

/-- Fixed constants for pulling a source cutoff back by exp. They depend
only on the physical support bound and its given derivative constants,
not on L, the selected cutoff, a frequency, or the desired saving. -/
noncomputable def sourcePhysicalLogConstants434 (A : ℝ) (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition j, A^c.length*K c.length

theorem source_physical_log_constants_nonneg434 (A : ℝ) (K : ℕ → ℝ)
    (hA : 0 ≤ A) (hK : ∀ j, 0 ≤ K j) (j : ℕ) :
    0 ≤ sourcePhysicalLogConstants434 A K j := by
  exact Finset.sum_nonneg (fun c hc => mul_nonneg (pow_nonneg hA _) (hK _))

theorem source_real_exp_iterated_derivative434 (j : ℕ) :
    iteratedDeriv j Real.exp = Real.exp := by
  simpa only [one_mul,one_pow] using (iteratedDeriv_exp_const_mul j (1:ℝ))

/-- Exact Faà di Bruno formula, including derivative order zero. -/
theorem source_physical_log_derivative_exact434 (psi : ℝ → ℂ)
    (hSmooth : ContDiff ℝ ∞ psi) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun u => psi (Real.exp u)) u =
      ∑ c : OrderedFinpartition j, (Real.exp u)^c.length •
        iteratedDeriv c.length psi (Real.exp u) := by
  have h := iteratedDeriv_scomp_eq_sum_orderedFinpartition
    (hSmooth.contDiffAt (x := Real.exp u))
    (Real.contDiff_exp.contDiffAt (x := u)) (i := j) (by simp)
  simpa only [Function.comp_def,source_real_exp_iterated_derivative434,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h

theorem source_plain_log_profile_support434 (A : ℝ) (psi : ℝ → ℂ)
    (hA : 1 ≤ A) (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A) :
    tsupport (fun u => psi (Real.exp u)) ⊆ Set.Icc (-Real.log A) (Real.log A) := by
  apply closure_minimal ?_ isClosed_Icc
  intro u hu
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hs := hSupport (Real.exp u) hu
  constructor
  · have hh := Real.log_le_log (one_div_pos.mpr hAp) hs.1
    simpa only [Real.log_exp,one_div,Real.log_inv] using hh
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hs.2

/-- Uniform real-to-log derivative budget for the ORIGINAL variable
cutoff family. The exponent C is unchanged. -/
theorem source_physical_log_derivative_budget434
    (A C L : ℝ) (K : ℕ → ℝ) (psi : ℝ → ℂ)
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hK : ∀ j, 0 ≤ K j) (hL : 1 ≤ L)
    (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hBudget : sourceLogDerivativeBudget C K L psi) :
    sourceLogDerivativeBudget C (sourcePhysicalLogConstants434 A K) L
      (fun u => psi (Real.exp u)) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  intro j u
  by_cases hu : u ∈ Set.Icc (-Real.log A) (Real.log A)
  · have hExp : Real.exp u ≤ A := by
      calc
        Real.exp u ≤ Real.exp (Real.log A) := Real.exp_le_exp.mpr hu.2
        _ = A := Real.exp_log hAp
    rw [source_physical_log_derivative_exact434 psi hSmooth j u]
    calc
      _ ≤ ∑ c : OrderedFinpartition j,
          ‖(Real.exp u)^c.length • iteratedDeriv c.length psi (Real.exp u)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ c : OrderedFinpartition j,
          (A^c.length*K c.length)*L^(C*((j:ℝ)+1)) := by
        apply Finset.sum_le_sum
        intro c hc
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.exp_pos u).le _)]
        have hPow : L^(C*((c.length:ℝ)+1)) ≤ L^(C*((j:ℝ)+1)) := by
          apply Real.rpow_le_rpow_of_exponent_le hL
          apply mul_le_mul_of_nonneg_left _ hC
          have hlen : (c.length:ℝ) ≤ (j:ℝ) := by exact_mod_cast c.length_le
          linarith
        have hDer := (hBudget c.length (Real.exp u)).trans
          (mul_le_mul_of_nonneg_left hPow (hK c.length))
        have hPowA : (Real.exp u)^c.length ≤ A^c.length :=
          pow_le_pow_left₀ (Real.exp_pos u).le hExp _
        calc
          _ ≤ A^c.length*(K c.length*L^(C*((j:ℝ)+1))) :=
            mul_le_mul hPowA hDer (norm_nonneg _) (pow_nonneg hAp.le _)
          _ = _ := by ring
      _ = _ := by rw [←Finset.sum_mul]; rfl
  · have hZero : iteratedFDeriv ℝ j (fun u => psi (Real.exp u)) u = 0 := by
      by_contra hn
      exact hu (source_plain_log_profile_support434 A psi hA hSupport
        ((support_iteratedFDeriv_subset j) hn))
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv,hZero,norm_zero]
    exact mul_nonneg (source_physical_log_constants_nonneg434 A K hAp.le hK j)
      (Real.rpow_nonneg (by linarith) _)

/-- The actual source logarithmic Schwartz profile now comes with its
uniform budget, instead of assuming such a profile at the application. -/
theorem source_physical_log_schwartz434
    (A C L : ℝ) (K : ℕ → ℝ) (psi : ℝ → ℂ)
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hK : ∀ j, 0 ≤ K j) (hL : 1 ≤ L)
    (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hBudget : sourceLogDerivativeBudget C K L psi) :
    ∃ phi : SchwartzMap ℝ ℂ,
      (∀ u, phi u=psi (Real.exp u)) ∧
      tsupport (phi : ℝ → ℂ) ⊆ Set.Icc (-Real.log A) (Real.log A) ∧
      sourceLogDerivativeBudget C (sourcePhysicalLogConstants434 A K) L phi ∧
      (∀ r : ℝ, 0 < r → phi (Real.log r)=psi r) := by
  refine ⟨sourcePlainLogProfileSchwartz434 A psi hA hSmooth hSupport,fun _ => rfl,
    source_plain_log_profile_support434 A psi hA hSupport,
    source_physical_log_derivative_budget434 A C L K psi hA hC hK hL hSmooth hSupport hBudget,?_⟩
  intro r hr
  change psi (Real.exp (Real.log r))=psi r
  rw [Real.exp_log hr]
end Green64Analytic.CorrelationSquare

end

