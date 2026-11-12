module

public import Green64.Library.Correlation.SourceCollarGramDecay
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Mathlib
public import Green64.Library.Analysis.Estimates.Part003
public import Green64.Library.Correlation.Part001
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Basic.Complex.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Green64.Library.Analysis.Estimates.Part002
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Correlation / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceCollarGramActual -/

section

open MeasureTheory
open scoped FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1300000

/-- The genuine Fourier norm of the derived source collar symbol. -/
noncomputable def collarSourceAmplitudeNorm434
    (chi kappa : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (chi : ℝ → ℂ))
    (h t s : ℝ) : ℝ :=
  ‖(𝓕 (sourceCompactCollarSymbolSchwartz434 chi kappa hc h t)) s‖

/-- Uniform weighted majorization by the exact inverse-square Schur kernel. -/
theorem collar_source_amplitude_schur_bound434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h t s : ℝ),
        (1+|h*t|)^j * collarSourceAmplitudeNorm434 chi kappa
            (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
              (subset_closure.trans hchi)) h t s
          ≤ C * collarSchurWeight434 s := by
  obtain ⟨C,hC,h⟩ :=
    source_compact_collar_fourier_uniform434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h0 t s
  have hh := h h0 t s
  have hden : 0 < (1+|s|)^2 := by positivity
  have heq : collarSourceAmplitudeNorm434 chi kappa
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        (subset_closure.trans hchi)) h0 t s =
      ‖𝓕 (sourceCompactCollarSymbol434 chi kappa h0 t) s‖ := by
    exact congrArg norm (congrFun (SchwartzMap.fourier_coe _) s)
  have hm :
      (1+|s|)^2 *
        ((1+|h0*t|)^j * collarSourceAmplitudeNorm434 chi kappa
            (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
              (subset_closure.trans hchi)) h0 t s) ≤ C := by
    simpa only [heq, mul_assoc] using hh
  have hf : (1+|h0*t|)^j * collarSourceAmplitudeNorm434 chi kappa
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        (subset_closure.trans hchi)) h0 t s ≤ C / (1+|s|)^2 :=
    (le_div_iff₀ hden).mpr (by nlinarith only [hm])
  simpa only [collarSchurWeight434, div_eq_mul_inv] using hf

theorem collar_source_amplitude_norm_continuous434
    (chi kappa : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (chi : ℝ → ℂ))
    (h t : ℝ) : Continuous (collarSourceAmplitudeNorm434 chi kappa hc h t) := by
  exact (SchwartzMap.continuous
    (𝓕 (sourceCompactCollarSymbolSchwartz434 chi kappa hc h t))).norm

noncomputable def collarSourceGram434
    (chi kappa : 𝓢(ℝ,ℂ)) (hc : HasCompactSupport (chi : ℝ → ℂ))
    (j : ℕ) (h t t' a b s : ℝ) : ℝ :=
  ((1+|h*t|)^j*collarSourceAmplitudeNorm434 chi kappa hc h t (s+a)) *
  ((1+|h*t'|)^j*collarSourceAmplitudeNorm434 chi kappa hc h t' (s+b))

/-- Source-actual Gram kernel is absolutely integrable for each parameter,
with a uniform inverse-square bound in the difference of center frequencies. -/
theorem collar_source_gram_integrable_and_decay434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h t t' a b : ℝ),
        Integrable (collarSourceGram434 chi kappa
          (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
            (subset_closure.trans hchi)) j h t t' a b) ∧
        (∫ s : ℝ, collarSourceGram434 chi kappa
          (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
            (subset_closure.trans hchi)) j h t t' a b s) ≤
        4*C^2*collarSchurWeight434 (a-b) *
          (∫ s : ℝ, collarSchurWeight434 s) := by
  let hc : HasCompactSupport (chi : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (subset_closure.trans hchi)
  obtain ⟨C,hC,h⟩ := collar_source_amplitude_schur_bound434 chi kappa B hB hchi j
  refine ⟨C,hC,?_⟩
  intro h0 t t' a b
  have hpt (s : ℝ) : collarSourceGram434 chi kappa hc j h0 t t' a b s ≤
      C^2 * (collarSchurWeight434 (s+a)*collarSchurWeight434 (s+b)) := by
    have ha := h h0 t (s+a)
    have hb := h h0 t' (s+b)
    calc
      _ = ((1+|h0*t|)^j * collarSourceAmplitudeNorm434 chi kappa hc h0 t (s+a)) *
          ((1+|h0*t'|)^j * collarSourceAmplitudeNorm434 chi kappa hc h0 t' (s+b)) := rfl
      _ ≤ (C*collarSchurWeight434 (s+a)) *
            (C*collarSchurWeight434 (s+b)) :=
          mul_le_mul ha hb (by unfold collarSourceAmplitudeNorm434; positivity)
            (mul_nonneg hC.le (collar_schur_weight_nonneg434 (s+a)))
      _ = _ := by ring
  have h1 : Continuous (fun s : ℝ =>
      collarSourceAmplitudeNorm434 chi kappa hc h0 t (s+a)) := by
    exact (collar_source_amplitude_norm_continuous434 chi kappa hc h0 t).comp
      (continuous_id.add continuous_const)
  have h2 : Continuous (fun s : ℝ =>
      collarSourceAmplitudeNorm434 chi kappa hc h0 t' (s+b)) := by
    exact (collar_source_amplitude_norm_continuous434 chi kappa hc h0 t').comp
      (continuous_id.add continuous_const)
  have hmeas : Measurable (collarSourceGram434 chi kappa hc j h0 t t' a b) := by
    change Measurable (fun s : ℝ =>
      ((1+|h0*t|)^j * collarSourceAmplitudeNorm434 chi kappa hc h0 t (s+a)) *
      ((1+|h0*t'|)^j * collarSourceAmplitudeNorm434 chi kappa hc h0 t' (s+b)))
    exact ((h1.const_mul _).mul (h2.const_mul _)).measurable
  have hi : Integrable (collarSourceGram434 chi kappa hc j h0 t t' a b) := by
    apply Integrable.mono'
      ((collar_schur_gram_integrable434 a b).const_mul (C^2))
      hmeas.aestronglyMeasurable
    filter_upwards with s
    change |collarSourceGram434 chi kappa hc j h0 t t' a b s| ≤
      C^2 * (collarSchurWeight434 (s+a)*collarSchurWeight434 (s+b))
    have hnn : 0 ≤ collarSourceGram434 chi kappa hc j h0 t t' a b s := by
      unfold collarSourceGram434 collarSourceAmplitudeNorm434
      positivity
    rw [abs_of_nonneg hnn]
    exact hpt s
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ s : ℝ, C^2 *
          (collarSchurWeight434 (s+a)*collarSchurWeight434 (s+b)) := by
      exact integral_mono hi ((collar_schur_gram_integrable434 a b).const_mul _) hpt
    _ = C^2 * (∫ s : ℝ,
          collarSchurWeight434 (s+a)*collarSchurWeight434 (s+b)) := by
      rw [integral_const_mul]
    _ ≤ C^2 * (4*collarSchurWeight434 (a-b) *
          (∫ s : ℝ, collarSchurWeight434 s)) :=
      mul_le_mul_of_nonneg_left (collar_schur_gram_decay434 a b) (sq_nonneg C)
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceComparisonEnergyBudget -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 2500000

/-- Explicit Cauchy exponent budget: a major saving 2D+E and a minor
saving D+E suffice when the endpoint square masses cost L^E. -/
theorem source_comparison_energy_budget434
    (R M F G delta Kmajor Kglobal Kminor Y L D E : ℝ)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hG : 0 ≤ G) (hdelta : 0 ≤ delta)
    (hKm : 0 ≤ Kmajor) (hKg : 0 ≤ Kglobal) (hKi : 0 ≤ Kminor)
    (hY : 0 ≤ Y) (hL : 0 < L)
    (hMajor : M ≤ Kmajor*Y*L^(-2*D-E))
    (hFirst : F ≤ Kglobal*Y*L^E) (hSecond : G ≤ Kglobal*Y*L^E)
    (hMinor : delta ≤ Kminor*L^(-D-E))
    (hCauchy : R ≤ Real.sqrt M*Real.sqrt G + delta*Real.sqrt F*Real.sqrt G) :
    R ≤ (Real.sqrt (Kmajor*Kglobal)+Kminor*Kglobal)*Y*L^(-D) := by
  have hMass : 0 ≤ Kglobal*Y*L^E := by positivity
  have hProd : Real.sqrt F*Real.sqrt G ≤ Kglobal*Y*L^E := by
    have hFG : F*G ≤ (Kglobal*Y*L^E)^2 := by
      calc
        F*G ≤ (Kglobal*Y*L^E)*(Kglobal*Y*L^E) :=
          mul_le_mul hFirst hSecond hG hMass
        _ = _ := (pow_two _).symm
    have hsq : (Real.sqrt F*Real.sqrt G)^2 = F*G := by
      rw [mul_pow,Real.sq_sqrt hF,Real.sq_sqrt hG]
    nlinarith [mul_nonneg (Real.sqrt_nonneg F) (Real.sqrt_nonneg G)]
  have hMajorProd : Real.sqrt M*Real.sqrt G ≤
      Real.sqrt (Kmajor*Kglobal)*Y*L^(-D) := by
    have hMG := mul_le_mul hMajor hSecond hG (by positivity : 0 ≤ Kmajor*Y*L^(-2*D-E))
    have hPow : (Kmajor*Y*L^(-2*D-E))*(Kglobal*Y*L^E) =
        (Real.sqrt (Kmajor*Kglobal)*Y*L^(-D))^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hKm hKg)]
      rw [show (L^(-D))^2 = L^(-D)*L^(-D) by ring,
        ←Real.rpow_add hL]
      have hp : L^(-2*D-E)*L^E = L^(-D+-D) := by
        rw [←Real.rpow_add hL]; congr 1; ring
      calc
        _ = Kmajor*Kglobal*Y^2*(L^(-2*D-E)*L^E) := by ring
        _ = _ := by rw [hp]
    rw [hPow] at hMG
    have hsq : (Real.sqrt M*Real.sqrt G)^2 = M*G := by
      rw [mul_pow,Real.sq_sqrt hM,Real.sq_sqrt hG]
    have ht : 0 ≤ Real.sqrt (Kmajor*Kglobal)*Y*L^(-D) := by positivity
    nlinarith [mul_nonneg (Real.sqrt_nonneg M) (Real.sqrt_nonneg G)]
  have hMinorProd : delta*Real.sqrt F*Real.sqrt G ≤ Kminor*Kglobal*Y*L^(-D) := by
    calc
      _ = delta*(Real.sqrt F*Real.sqrt G) := by ring
      _ ≤ delta*(Kglobal*Y*L^E) := mul_le_mul_of_nonneg_left hProd hdelta
      _ ≤ (Kminor*L^(-D-E))*(Kglobal*Y*L^E) :=
        mul_le_mul_of_nonneg_right hMinor hMass
      _ = _ := by
        have hp : L^(-D-E)*L^E = L^(-D) := by
          rw [←Real.rpow_add hL]; congr 1; ring
        calc
          _ = Kminor*Kglobal*Y*(L^(-D-E)*L^E) := by ring
          _ = _ := by rw [hp]
  exact hCauchy.trans (by nlinarith [hMajorProd,hMinorProd])
end Green64Analytic.CorrelationSquare

end

/-! ## SourceCompositeMinFacStructure -/

section

open Filter Real Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Exact canonical factorization of a genuine composite n into its least
prime factor p and cofactor q≥p, retaining repeated prime factors. -/
theorem source_composite_minfac_factorization
    {n : ℕ} (hn : 2 ≤ n) (hnp : ¬n.Prime) :
    let p := n.minFac
    let q := n / p
    p.Prime ∧ 2 ≤ p ∧ p ≤ q ∧ p*q=n := by
  dsimp
  have h1 : n ≠ 1 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime h1
  refine ⟨hp,hp.two_le,Nat.minFac_le_div (by omega) hnp,?_⟩
  exact Nat.mul_div_cancel' (Nat.minFac_dvd n)


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceCompositeSemiprime -/

section

open Filter Real Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Genuine shifted semiprime forcing lemma: if the least prime factor
p of a composite n satisfies p^3>n, then the cofactor n/p is itself
prime. Repeated prime factors p^2 are INCLUDED. -/
theorem source_composite_cofactor_prime_of_minfac_cube_gt
    {n : ℕ} (hn : 2 ≤ n) (hnp : ¬n.Prime)
    (hcube : n < n.minFac^3) :
    (n / n.minFac).Prime := by
  let p := n.minFac
  let q := n/p
  obtain ⟨hp, hp2, hpq, hfact⟩ :=
    source_composite_minfac_factorization hn hnp
  change q.Prime
  by_contra hqnp
  have hq2 : 2 ≤ q := hp2.trans hpq
  have hqp : q.minFac.Prime := Nat.minFac_prime (by omega : q ≠ 1)
  have hqfactor : q ∣ n := by
    rw [← hfact]
    exact dvd_mul_left q p
  have hqdvd : q.minFac ∣ n := (Nat.minFac_dvd q).trans hqfactor
  have hmin : p ≤ q.minFac :=
    Nat.minFac_le_of_dvd hqp.two_le hqdvd
  have hsq : (q.minFac)^2 ≤ q :=
    Nat.minFac_sq_le_self (by omega : 0 < q) hqnp
  have hpsq : p^2 ≤ q := by
    have hs : p^2 ≤ (q.minFac)^2 := Nat.pow_le_pow_left hmin 2
    exact hs.trans hsq
  have hcube_le : p^3 ≤ n := by
    calc
      p^3 = p*(p^2) := by ring
      _ ≤ p*q := Nat.mul_le_mul_left p hpsq
      _ = n := hfact
  exact (not_lt_of_ge hcube_le) hcube


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceCorrectedDyadicPartition -/

section

open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
set_option maxHeartbeats 1800000

/-- Fixed smooth dyadic profile. Its telescoping partition is exact;
no L-dependent derivative or normalization constant is hidden here. -/
noncomputable def sourceCorrectedDyadicProfile (t : ℝ) : ℝ :=
  Real.smoothTransition (2*t-1)-Real.smoothTransition (t-1)

theorem source_corrected_dyadic_profile_zero_left (t : ℝ) (ht : t ≤ 1/2) :
    sourceCorrectedDyadicProfile t=0 := by
  unfold sourceCorrectedDyadicProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2*t-1 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : t-1 ≤ 0),sub_self]

theorem source_corrected_dyadic_profile_zero_right (t : ℝ) (ht : 2 ≤ t) :
    sourceCorrectedDyadicProfile t=0 := by
  unfold sourceCorrectedDyadicProfile
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2*t-1),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t-1),sub_self]

theorem source_corrected_dyadic_profile_range (t : ℝ) :
    0 ≤ sourceCorrectedDyadicProfile t ∧ sourceCorrectedDyadicProfile t ≤ 1 := by
  by_cases ht : t ≤ 1/2
  · rw [source_corrected_dyadic_profile_zero_left t ht]; norm_num
  unfold sourceCorrectedDyadicProfile
  constructor
  · exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
  · linarith [Real.smoothTransition.le_one (2*t-1),Real.smoothTransition.nonneg (t-1)]

theorem source_corrected_dyadic_profile_smooth :
    ContDiff ℝ (↑(⊤ : ℕ∞)) sourceCorrectedDyadicProfile := by
  unfold sourceCorrectedDyadicProfile
  fun_prop

theorem source_corrected_dyadic_profile_support :
    tsupport sourceCorrectedDyadicProfile ⊆ Set.Icc (1/2:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  rcases not_and_or.mp hn with h | h
  · exact ht (source_corrected_dyadic_profile_zero_left t (le_of_not_ge h))
  · exact ht (source_corrected_dyadic_profile_zero_right t (le_of_not_ge h))

theorem source_corrected_dyadic_profile_compact : HasCompactSupport sourceCorrectedDyadicProfile :=
  isCompact_Icc.of_isClosed_subset isClosed_closure source_corrected_dyadic_profile_support

noncomputable def sourceCorrectedDyadicSchwartz : SchwartzMap ℝ ℂ :=
  (source_corrected_dyadic_profile_compact.comp_left
    (g := fun t : ℝ => (t:ℂ)) (by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp source_corrected_dyadic_profile_smooth)

/-- Finite telescoping identity, with BOTH endpoint transition terms. -/
theorem source_corrected_dyadic_telescope (N : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range (N+1), sourceCorrectedDyadicProfile (t/(2:ℝ)^j)) =
      Real.smoothTransition (2*t-1)-Real.smoothTransition (t/(2:ℝ)^N-1) := by
  induction N with
  | zero => simp [sourceCorrectedDyadicProfile]
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    unfold sourceCorrectedDyadicProfile
    have he : 2*(t/(2:ℝ)^(N+1))=t/(2:ℝ)^N := by
      rw [pow_succ]; field_simp
    rw [he]; ring

/-- Exact partition of unity on the physical finite z range. -/
theorem source_corrected_dyadic_partition_one
    (N : ℕ) (Z0 z : ℝ) (hZ : 0 < Z0) (hlo : Z0 ≤ z)
    (hhi : z ≤ Z0*(2:ℝ)^N) :
    (∑ j ∈ Finset.range (N+1), sourceCorrectedDyadicProfile (z/(Z0*(2:ℝ)^j)))=1 := by
  simp_rw [div_mul_eq_div_div]
  rw [source_corrected_dyadic_telescope]
  have hlo' : 1 ≤ z/Z0 := (le_div_iff₀ hZ).mpr (by simpa using hlo)
  have hhi' : z/Z0/(2:ℝ)^N ≤ 1 := by
    rw [div_le_iff₀ (by positivity),div_le_iff₀ hZ]
    simpa only [one_mul,mul_comm] using hhi
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2*(z/Z0)-1),
    Real.smoothTransition.zero_of_nonpos (by linarith : z/Z0/(2:ℝ)^N-1 ≤ 0)]
  norm_num

end Green64Analytic.ShiftTwoTerminal

end

/-! ## SourceCorrelationU1Shifted -/

section

/-! A 4.34.1-only application of the certified unconditional source U1.
Keep this separate from the 4.32.0 correlation import graph. -/

namespace Green64Analytic.LongPrime

noncomputable def sourceCorrelationLongPrime
    (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℝ)
    (I : Set ℝ) (t : ℝ) : ℂ :=
  ∑ p ∈ (@Finset.filter ℕ (fun p => (p : ℝ) ∈ I)
      (fun _ => Classical.propDecidable _)
      ((Finset.range (⌊2*N⌋₊ + 1)).filter Nat.Prime)),
      χ (p : ZMod q) * (p : ℂ)^((-1 : ℂ) + (t : ℂ)*Complex.I)

/-- Exact shifted-frequency U1 output for the original long prime slot.
This is an unconditional consequence of the separately certified source U1,
not a hypothesis about the prime polynomial. -/
theorem sourceCorrelationLongPrime_shifted_U1
    (τ η C A : ℝ) (hτ : 0 < τ) (hτη : τ < η)
    (hη : η < 1/4) (hC : 0 < C) (hA : 0 < A) :
    ∃ B₀ K X₀ : ℝ, 0 < B₀ ∧ 0 < K ∧ 3 ≤ X₀ ∧
      ∀ x : ℝ, X₀ ≤ x →
      ∀ N : ℝ, x^τ/2 ≤ N → N ≤ x^η →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log x)^C →
      ∀ χ : DirichletCharacter ℂ q,
      ∀ I : Set ℝ, Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      ∀ t σ : ℝ,
        (Real.log x)^B₀ + |σ| ≤ |t| →
        |t+σ| ≤ x^2 →
        ‖sourceCorrelationLongPrime q χ N I (t+σ)‖ ≤
          K / (Real.log x)^A := by
  have hU := sourceLongPrimeU1_unconditional
  dsimp [SourceLongPrimeU1] at hU
  obtain ⟨B₀,K,X₀,hB₀,hK,hX₀,hbound⟩ :=
    hU τ η C A hτ hτη hη hC hA
  refine ⟨B₀, K, X₀, hB₀, hK, hX₀, ?_⟩
  intro x hx N hNl hNu q hq hqC χ I hI hSub t σ hlow hhigh
  have htriangle : |t| ≤ |t+σ| + |σ| := by
    have h := abs_add_le (t+σ) (-σ)
    simpa [add_assoc] using h
  have hfrequency : (Real.log x)^B₀ ≤ |t+σ| := by
    linarith
  simpa only [sourceCorrelationLongPrime] using
    hbound x hx N hNl hNu q hq hqC χ I hI hSub (t+σ)
      hfrequency hhigh
end Green64Analytic.LongPrime

end

/-! ## SourceActualLongPrimeContinuous -/

section

namespace Green64Analytic.CorrelationMellin
open Green64Analytic.LongPrime

/-! Continuous dependence on the real Mellin frequency for the
actual finite prime polynomial, with its fixed source shift. -/

theorem source_actual_long_prime_continuous
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (N : ℝ) (I : Set ℝ) (sigma : ℝ) :
    Continuous (fun t : ℝ =>
      sourceCorrelationLongPrime q chi N I (t+sigma)) := by
  classical
  unfold sourceCorrelationLongPrime
  apply continuous_finset_sum
  intro p hp
  have hpPrime : Nat.Prime p :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hp0 : (p:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpPrime.pos)
  have hPow : Continuous (fun z : ℂ => (p:ℂ)^z) :=
    continuous_iff_continuousAt.mpr
      (fun z => continuousAt_const_cpow hp0)
  have hExponent : Continuous (fun t : ℝ =>
      (-1:ℂ)+((t+sigma:ℝ):ℂ)*Complex.I) := by
    fun_prop
  exact continuous_const.mul (hPow.comp hExponent)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceCutoffLogPower -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 550000

/-- The EXACT original cutoff M=ceil(A Y) has a sixth-divisor
summatory budget of order Y*L^63 when log Y≤3L/2.
The constant depends on fixed A, but not on the bookkeeping N. -/
theorem source_original_cutoff_divisor_log_power434
    (A Y L : ℝ) (hA : 1 ≤ A) (hY : 1 ≤ Y)
    (hL : 1 ≤ L) (hlogY : Real.log Y ≤ (3/2:ℝ)*L) :
    (Nat.ceil (A*Y):ℝ) *
      (1+Real.log (Nat.ceil (A*Y):ℝ))^63 ≤
      (2*A*(Real.log (2*A)+5/2)^63)*Y*L^63 := by
  have hTwoA : 1 ≤ 2*A := by nlinarith
  have hpTwoA : 0 < 2*A := by linarith
  have hlogTwoA : 0 ≤ Real.log (2*A) :=
    Real.log_nonneg hTwoA
  have hlogProd : Real.log (2*A*Y) =
      Real.log (2*A)+Real.log Y := by
    rw [Real.log_mul hpTwoA.ne' (by linarith : Y ≠ 0)]
  have hC : 0 ≤ Real.log (2*A)+5/2 := by linarith
  have hScale : 1+Real.log (2*A*Y) ≤
      (Real.log (2*A)+5/2)*L := by
    rw [hlogProd]
    have hExtra : 0 ≤ (Real.log (2*A)+1)*(L-1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hBase : 0 ≤ 1+Real.log (2*A*Y) := by
    have hOne : 1 ≤ 2*A*Y := by nlinarith
    exact add_nonneg zero_le_one (Real.log_nonneg hOne)
  have hPow : (1+Real.log (2*A*Y))^63 ≤
      ((Real.log (2*A)+5/2)*L)^63 :=
    pow_le_pow_left₀ hBase hScale 63
  calc
    _ ≤ (2*A*Y)*(1+Real.log (2*A*Y))^63 :=
      source_original_ceil_log_moment_scale434 A Y hA hY
    _ ≤ (2*A*Y)*((Real.log (2*A)+5/2)*L)^63 :=
      mul_le_mul_of_nonneg_left hPow (by positivity)
    _ = (2*A*(Real.log (2*A)+5/2)^63)*Y*L^63 := by
      rw [mul_pow]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalTailScalarScale -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- Exact source tail radius L/h=L*Y/H is no larger than
L*Y when the original free scale H>=1, Y>0. -/
theorem source_tail_inverse_scale434
    (L H Y : ℝ) (hL : 0 ≤ L) (hH : 1 ≤ H) (hY : 0 < Y) :
    L/(H/Y) ≤ L*Y := by
  have hh : 0 < H := by linarith
  have hdiv : L/(H/Y) = L*Y/H := by
    field_simp
  rw [hdiv]
  have hLY : 0 ≤ L*Y := mul_nonneg hL hY.le
  apply (div_le_iff₀ hh).mpr
  nlinarith [mul_nonneg hLY (sub_nonneg.mpr hH)]

/-- All source volume on the TRUE physical window: the shell
mean-square length L/h plus 16M(1+log M), with M=ceil(A*Y).
The right side is O(Y*L), independent of source N. -/
theorem source_true_physical_shell_radius_budget434
    (A Y H L : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hL : 1 ≤ L) (hlogY : Real.log Y ≤ (3/2:ℝ)*L) :
    L/(H/Y)+16*(Nat.ceil (A*Y):ℝ)*
      (1+Real.log (Nat.ceil (A*Y):ℝ)) ≤
      (1+32*A*(Real.log (2*A)+5/2))*Y*L := by
  let M : ℝ := (Nat.ceil (A*Y):ℝ)
  let C : ℝ := Real.log (2*A)+5/2
  have hA2 : 1 ≤ 2*A := by nlinarith
  have hC : 0 ≤ C := by
    dsimp [C]
    have hp : 0 ≤ Real.log (2*A) :=
      Real.log_nonneg hA2
    linarith
  have hMpos : 1 ≤ M := by
    dsimp [M]
    have hp : 1 ≤ A*Y := by nlinarith
    exact hp.trans (Nat.le_ceil _)
  have hM : M ≤ 2*A*Y :=
    source_original_ceil_support_scale434 A Y hA hY
  have hLog : Real.log M ≤ Real.log (2*A)+Real.log Y := by
    have hh : Real.log M ≤ Real.log (2*A*Y) :=
      Real.log_le_log (by linarith) hM
    rw [Real.log_mul (by positivity : 2*A ≠ 0)
      (by linarith : Y ≠ 0)] at hh
    exact hh
  have hC1 : 0 ≤ 1+Real.log M := by
    have hh := Real.log_nonneg hMpos
    linarith
  have hC2 : 1+Real.log M ≤ C*L := by
    have hcc : 0 ≤ (Real.log (2*A)+1)*(L-1) := by
      have hp : 0 ≤ Real.log (2*A) := Real.log_nonneg hA2
      exact mul_nonneg (by linarith) (by linarith)
    dsimp [C]
    nlinarith [hLog,hlogY,hcc]
  have hProd : M*(1+Real.log M) ≤ (2*A*Y)*(C*L) :=
    mul_le_mul hM hC2 hC1 (by positivity)
  have hRad : L/(H/Y) ≤ L*Y :=
    source_tail_inverse_scale434 L H Y (by linarith) hH (by linarith)
  calc
    _ = L/(H/Y)+16*(M*(1+Real.log M)) := by
      dsimp [M]
      ring
    _ ≤ L*Y+16*((2*A*Y)*(C*L)) := by
      exact add_le_add hRad
        (mul_le_mul_of_nonneg_left hProd (by norm_num : (0:ℝ) ≤ 16))
    _ = (1+32*A*C)*Y*L := by ring
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourcePhysicalNormalizedTailScale -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1350000

/-- Bound the normalized all-real angular tail by a source-scale
power of L with original Y and the physical endpoint cutoff. -/
theorem source_physical_normalized_tail_scalar434
    (A Y H L B T : ℝ) (j : ℕ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hL : 1 ≤ L) (hlogY : Real.log Y ≤ (3/2:ℝ)*L)
    (hB : 0 ≤ B) :
    T ≤
      (4 * ((L^(j-2))⁻¹ *
        (L/(H/Y)+16*(Nat.ceil (A*Y):ℝ) *
          (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
      (B^2*(Nat.ceil (A*Y):ℝ)*
        (1+Real.log (Nat.ceil (A*Y):ℝ))^63) →
    (1/Y)*T ≤
      (8*A*(1+32*A*(Real.log (2*A)+5/2))*
        (Real.log (2*A)+5/2)^63) *
      B^2*Y*L^64*(L^(j-2))⁻¹ := by
  intro hTail
  let M : ℝ := (Nat.ceil (A*Y):ℝ)
  let C : ℝ := Real.log (2*A)+5/2
  let D : ℝ := 1+32*A*C
  let E : ℝ := 2*A*C^63
  let W : ℝ := 4*(L^(j-2))⁻¹
  let R : ℝ := L/(H/Y)+16*M*(1+Real.log M)
  let Q : ℝ := M*(1+Real.log M)^63
  have hC : 0 ≤ C := by
    dsimp [C]
    have hp : 1 ≤ 2*A := by nlinarith
    have hl : 0 ≤ Real.log (2*A) := Real.log_nonneg hp
    linarith
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hM : 1 ≤ M := by
    dsimp [M]
    have hAY : 1 ≤ A*Y := by nlinarith
    exact hAY.trans (Nat.le_ceil _)
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    have hl : 0 ≤ Real.log M := Real.log_nonneg hM
    positivity
  have hScaleR : R ≤ D*Y*L := by
    simpa only [R,D,C,M] using
      (source_true_physical_shell_radius_budget434
        A Y H L hA hY hH hL hlogY)
  have hScaleQ : Q ≤ E*Y*L^63 := by
    simpa only [Q,E,C,M] using
      (source_original_cutoff_divisor_log_power434
        A Y L hA hY hL hlogY)
  have hTail' : T ≤ W*R*(B^2*Q) := by
    simpa only [W,R,Q,M,mul_assoc] using hTail
  have hYpos : 0 < Y := by linarith
  have hYNonneg : 0 ≤ 1/Y := (one_div_nonneg.mpr hYpos.le)
  have hZ : 0 ≤ B^2*Q := mul_nonneg (sq_nonneg _) hQ
  have hDYL : 0 ≤ D*Y*L := by positivity
  calc
    (1/Y)*T ≤ (1/Y)*(W*R*(B^2*Q)) :=
      mul_le_mul_of_nonneg_left hTail' hYNonneg
    _ ≤ (1/Y)*(W*(D*Y*L)*(B^2*Q)) := by
      have hp := mul_le_mul_of_nonneg_left hScaleR hW
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp hZ) hYNonneg
    _ ≤ (1/Y)*(W*(D*Y*L)*(B^2*(E*Y*L^63))) := by
      have hp := mul_le_mul_of_nonneg_left hScaleQ (sq_nonneg B)
      have hfac : 0 ≤ W*(D*Y*L) := mul_nonneg hW hDYL
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp hfac) hYNonneg
    _ = (4*D*E)*B^2*Y*L^64*(L^(j-2))⁻¹ := by
      have hYN : Y ≠ 0 := hYpos.ne'
      dsimp [W]
      field_simp
    _ = _ := by
      dsimp [D,E,C]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceArcMomentAmplitude -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- Actual localized divisor moment with a polynomial coefficient cap.
The physical volume is Y; no bookkeeping cutoff occurs on the right. -/
theorem source_arc_moment_amplitude434
    (A Y L B B0 E : ℝ) (d : ℕ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (hlogY : Real.log Y ≤ (3/2:ℝ)*L)
    (hB : 0 ≤ B) (hB0 : 0 ≤ B0) (hCap : B ≤ B0*L^E) (hd : d ≤ 63) :
    B^2*(Nat.ceil (A*Y):ℝ)*(1+Real.log (Nat.ceil (A*Y):ℝ))^d ≤
      (B0^2*(2*A*(Real.log (2*A)+5/2)^63))*Y*L^(2*E+63) := by
  have hLp : 0 < L := by linarith
  have hAY : 1 ≤ A*Y := by nlinarith
  have hN : (1:ℝ) ≤ Nat.ceil (A*Y) := hAY.trans (Nat.le_ceil _)
  have hLog : 0 ≤ Real.log (Nat.ceil (A*Y):ℝ) := Real.log_nonneg hN
  have hP : (1+Real.log (Nat.ceil (A*Y):ℝ))^d ≤
      (1+Real.log (Nat.ceil (A*Y):ℝ))^63 :=
    pow_le_pow_right₀ (by linarith) hd
  have hMoment := source_original_cutoff_divisor_log_power434 A Y L hA hY hL hlogY
  have hPow : L^(2*E+63) = (L^E)^2*L^(63:ℕ) := by
    rw [Real.rpow_add hLp,show 2*E = E*2 by ring,Real.rpow_mul hLp.le]
    norm_num
  calc
    _ ≤ B^2*((Nat.ceil (A*Y):ℝ)*(1+Real.log (Nat.ceil (A*Y):ℝ))^63) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hP
        (mul_nonneg (sq_nonneg B) (Nat.cast_nonneg _))
    _ ≤ B^2*((2*A*(Real.log (2*A)+5/2)^63)*Y*L^63) :=
      mul_le_mul_of_nonneg_left hMoment (sq_nonneg B)
    _ ≤ (B0*L^E)^2*((2*A*(Real.log (2*A)+5/2)^63)*Y*L^63) := by
      have hLogA : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
      gcongr
    _ = _ := by rw [hPow]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceArcTailNormalizedBound -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1500000

/-- Scalar absorption of the ACTUAL explicit full-time tail expression.
Only a coefficient cap is used, not a presumed Fourier/Mellin saving. -/
theorem source_arc_explicit_tail_saving434
    (A Y H L B B0 E : ℝ) (j target : ℕ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hlogY : Real.log Y ≤ (3/2:ℝ)*L)
    (hB : 0 ≤ B) (hB0 : 0 ≤ B0) (hCap : B ≤ B0*L^E)
    (hOrder : 2*E+64+(target:ℝ) ≤ ((j-2:ℕ):ℝ)) :
    (1/Y)*((4*((L^(j-2))⁻¹*(L/(H/Y)+16*(Nat.ceil (A*Y):ℝ)*
      (1+Real.log (Nat.ceil (A*Y):ℝ)))))*
      (B^2*(Nat.ceil (A*Y):ℝ)*(1+Real.log (Nat.ceil (A*Y):ℝ))^63)) ≤
    (8*A*(1+32*A*(Real.log (2*A)+5/2))*(Real.log (2*A)+5/2)^63)*
      B0^2*Y*(L^target)⁻¹ := by
  let Ct : ℝ := 8*A*(1+32*A*(Real.log (2*A)+5/2))*(Real.log (2*A)+5/2)^63
  have hLog : 0 ≤ Real.log (2*A) := Real.log_nonneg (by linarith)
  have hCt : 0 ≤ Ct := by dsimp [Ct]; positivity
  have hLp : 0 < L := by linarith
  have hNative := source_physical_normalized_tail_scalar434 A Y H L B
    ((4*((L^(j-2))⁻¹*(L/(H/Y)+16*(Nat.ceil (A*Y):ℝ)*
      (1+Real.log (Nat.ceil (A*Y):ℝ)))))*
      (B^2*(Nat.ceil (A*Y):ℝ)*(1+Real.log (Nat.ceil (A*Y):ℝ))^63))
    j hA hY hH hL hlogY hB le_rfl
  have hPow : L^(2*E+64) = (L^E)^2*L^(64:ℕ) := by
    rw [Real.rpow_add hLp,show 2*E = E*2 by ring,Real.rpow_mul hLp.le]
    norm_num
  have hSave := source_arc_rpow_nat_decay434 L (2*E+64) (j-2) target hL hOrder
  calc
    _ ≤ Ct*B^2*Y*L^64*(L^(j-2))⁻¹ := hNative
    _ ≤ Ct*(B0*L^E)^2*Y*L^64*(L^(j-2))⁻¹ := by gcongr
    _ = Ct*B0^2*Y*(L^(2*E+64)*(L^(j-2))⁻¹) := by rw [hPow]; ring
    _ ≤ Ct*B0^2*Y*(L^target)⁻¹ :=
      mul_le_mul_of_nonneg_left hSave (by positivity)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceD27DensityContinuity -/

section

open Filter Topology
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- The source literal simplex density is continuous in the cofactor
exponent throughout its natural domain, including all multiplicity
thresholds w=k*b; not a hypothesis or a newly defined approximation. -/
theorem sourceD27_original_density_continuousAt_w
    (b w : ℝ) (hb : 0<b) (hbw : b<w) :
    ContinuousAt (fun t : ℝ => Green64Analytic.SmallB.sourceDensity b t) w := by
  let E : Set (ℝ×ℝ) := {q | 0<q.1 ∧ q.1<q.2}
  have hOpen : IsOpen E := by
    dsimp [E]
    exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_fst continuous_snd)
  have hmem : (b,w)∈E := ⟨hb,hbw⟩
  have hSource : ContinuousOn
      (fun q : ℝ×ℝ => Green64Analytic.SmallB.sourceDensity q.1 q.2) E := by
    simpa only [E,Green64Analytic.SmallB.sourceDensity,
      Green64Analytic.SmallB.sourceSimplexTerm] using
      Green64Analytic.ReciprocalSimplex.density_continuity
  have hAt := hSource.continuousAt (hOpen.mem_nhds hmem)
  have hPair : ContinuousAt (fun t : ℝ => ((b,t):ℝ×ℝ)) w :=
    continuousAt_const.prodMk continuousAt_id
  exact hAt.comp hPair


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD27CompactContinuity -/

section

open Filter Topology
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- One uniform modulus of continuity for the EXACT source rough
density on a fixed compact cofactor exponent range. It crosses all
multiplicity thresholds without a case split. -/
theorem sourceD27_original_density_uniform_continuity
    (b A B : ℝ) (hb : 0<b) (hbA : b<A) :
    UniformContinuousOn (fun w : ℝ =>
      Green64Analytic.SmallB.sourceDensity b w) (Set.Icc A B) := by
  have hcont : ContinuousOn (fun w : ℝ =>
      Green64Analytic.SmallB.sourceDensity b w) (Set.Icc A B) := by
    intro w hw
    exact (sourceD27_original_density_continuousAt_w
      b w hb (hbA.trans_le hw.1)).continuousWithinAt
  exact isCompact_Icc.uniformContinuousOn_of_continuous hcont


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD28DensityBound -/

section

open Filter Topology
open scoped Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 0
set_option autoImplicit false

/-- The ACTUAL source simplex density has one finite upper bound on
every compact cofactor exponent interval, even when a multiplicity
threshold w=k*b crosses its interior. -/
theorem sourceD28_density_compact_bounded
    (b A B : ℝ) (hb : 0<b) (hbA : b<A) :
    ∃ C : ℝ, 0≤C ∧
      ∀ w∈Set.Icc A B, Green64Analytic.SmallB.sourceDensity b w ≤ C := by
  have hCont : ContinuousOn
      (fun w : ℝ => Green64Analytic.SmallB.sourceDensity b w)
      (Set.Icc A B) := by
    intro w hw
    exact (sourceD27_original_density_continuousAt_w b w hb
      (hbA.trans_le hw.1)).continuousWithinAt
  obtain ⟨C,hC⟩ :=
    (isCompact_Icc.bddAbove_image hCont)
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro w hw
  have hh : Green64Analytic.SmallB.sourceDensity b w ≤ C :=
    hC ⟨w,hw,rfl⟩
  exact hh.trans (le_max_left _ _)


end Green64Analytic.SourceBlockSieve

end

/-! ## SourceD61ProjectedFourSign -/

section

open scoped BigOperators Classical
namespace Green64ComparisonPartial
set_option autoImplicit false
set_option maxHeartbeats 4500000

/-- Exact physical parity lift, source P_nu(w), where the freed slot count M
changes the parity channel. This is not a new projector or independent sign. -/
noncomputable def originalD61ParityProjector434 (M : ℕ) (eps : ℂ) : ℂ :=
  (1 - (-1:ℂ)^M * eps)/2

/-- Expand the original two-endpoint projector into all FOUR signed channels.
No squaring or abs has occurred and the pattern-dependent sign is retained. -/
theorem original_D61_two_endpoint_four_sign434
    (M : ℕ) (e₁ e₂ : ℂ) :
    originalD61ParityProjector434 M e₁ *
    originalD61ParityProjector434 M e₂ =
      (1 - (-1:ℂ)^M*e₁ - (-1:ℂ)^M*e₂ + e₁*e₂)/4 := by
  have hs : ((-1:ℂ)^M)^2=1 := by
    calc
      _ = ((-1:ℂ)^2)^M := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = 1 := by norm_num
  unfold originalD61ParityProjector434
  calc
    ((1 - (-1:ℂ)^M*e₁)/2)*((1 - (-1:ℂ)^M*e₂)/2) =
      (1 - (-1:ℂ)^M*e₁ - (-1:ℂ)^M*e₂ +
        ((-1:ℂ)^M)^2*e₁*e₂)/4 := by ring
    _ = (1 - (-1:ℂ)^M*e₁ - (-1:ℂ)^M*e₂ + e₁*e₂)/4 := by
      rw [hs]
      ring
/-- The full original four-sign projector is summed BEFORE a Gram square,
so its complex signs are not replaced by four separate positive energies. -/
theorem original_D61_four_sign_linear_sum434
    {ι : Type} (S : Finset ι) (M : ℕ)
    (e₁ e₂ B : ι → ℂ) :
    (∑ i ∈ S,
      B i * originalD61ParityProjector434 M (e₁ i) *
        originalD61ParityProjector434 M (e₂ i)) =
    (1/4:ℂ)*
      ((∑ i ∈ S, B i) -
       (-1:ℂ)^M*(∑ i ∈ S, B i*e₁ i) -
       (-1:ℂ)^M*(∑ i ∈ S, B i*e₂ i) +
       (∑ i ∈ S, B i*e₁ i*e₂ i)) := by
  classical
  have hpoint (i : ι) :
    B i*originalD61ParityProjector434 M (e₁ i)*
        originalD61ParityProjector434 M (e₂ i) =
      (1/4:ℂ)*(B i-(-1:ℂ)^M*B i*e₁ i-
        (-1:ℂ)^M*B i*e₂ i+B i*e₁ i*e₂ i) := by
    calc
      _ = B i*(originalD61ParityProjector434 M (e₁ i) *
          originalD61ParityProjector434 M (e₂ i)) := by ring
      _ = B i * ((1-(-1:ℂ)^M*e₁ i-(-1:ℂ)^M*e₂ i +
          e₁ i*e₂ i)/4) := by rw [original_D61_two_endpoint_four_sign434]
      _ = _ := by ring
  simp_rw [hpoint, ← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  ring
end Green64ComparisonPartial

end

/-! ## SourceDisjointDyads -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

abbrev SourceQuad434 := (ℕ × ℕ) × (ℕ × ℕ)

/-- Half-open integer dyads. Each positive integer belongs to one block. -/
def sourceDyad434 (j : ℕ) : Finset ℕ := Finset.Ico (2^j) (2^(j+1))

def sourceQuadDyadIndex434 (z : SourceQuad434) : SourceQuad434 :=
  ((z.1.1.log2,z.1.2.log2),(z.2.1.log2,z.2.2.log2))

def sourceQuadDyadBox434 (j : SourceQuad434) : Finset SourceQuad434 :=
  ((sourceDyad434 j.1.1).product (sourceDyad434 j.1.2)).product
    ((sourceDyad434 j.2.1).product (sourceDyad434 j.2.2))

theorem source_positive_in_canonical_dyad434 (n : ℕ) (hn : 0 < n) :
    n ∈ sourceDyad434 n.log2 := by
  exact Finset.mem_Ico.mpr ⟨Nat.log2_self_le (Nat.ne_of_gt hn),Nat.lt_log2_self⟩

theorem source_dyad_in_closed_containing434 (j : ℕ) :
    sourceDyad434 j ⊆ Finset.Icc (2^j) (2*(2^j)) := by
  intro n hn
  obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hn
  rw [pow_succ] at hu
  exact Finset.mem_Icc.mpr ⟨hl,by omega⟩

/-- Group a genuine occurrence set without quotienting occurrences.
Q may already contain every original interval, prime and gcd restriction. -/
theorem source_canonical_dyad_sum434
    (Q : Finset SourceQuad434) (f : SourceQuad434 → ℂ) :
    (∑ z ∈ Q, f z) =
      ∑ j ∈ Q.image sourceQuadDyadIndex434,
        ∑ z ∈ Q.filter (fun z => sourceQuadDyadIndex434 z = j), f z := by
  classical
  calc
    _ = ∑ z ∈ Q, ∑ j ∈ Q.image sourceQuadDyadIndex434,
          if sourceQuadDyadIndex434 z = j then f z else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [Finset.mem_image_of_mem sourceQuadDyadIndex434 hz]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]

theorem source_canonical_fibres_disjoint434
    (Q : Finset SourceQuad434) (i j : SourceQuad434) (hij : i ≠ j) :
    Disjoint (Q.filter (fun z => sourceQuadDyadIndex434 z = i))
      (Q.filter (fun z => sourceQuadDyadIndex434 z = j)) := by
  apply Finset.disjoint_left.mpr
  intro z hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem source_canonical_fibre_in_box434
    (Q : Finset SourceQuad434) (j z : SourceQuad434)
    (hz : z ∈ Q.filter (fun z => sourceQuadDyadIndex434 z = j))
    (hpos : 0 < z.1.1 ∧ 0 < z.1.2 ∧ 0 < z.2.1 ∧ 0 < z.2.2) :
    z ∈ sourceQuadDyadBox434 j := by
  have hj := (Finset.mem_filter.mp hz).2
  rw [← hj]
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr
      ⟨source_positive_in_canonical_dyad434 _ hpos.1,
        source_positive_in_canonical_dyad434 _ hpos.2.1⟩,
      Finset.mem_product.mpr
      ⟨source_positive_in_canonical_dyad434 _ hpos.2.2.1,
        source_positive_in_canonical_dyad434 _ hpos.2.2.2⟩⟩

theorem source_dyad_membership_iff434 (n j : ℕ) (hn : 0 < n) :
    n ∈ sourceDyad434 j ↔ n.log2 = j := by
  constructor
  · intro hmem
    obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hmem
    have hcL := Nat.log2_self_le (Nat.ne_of_gt hn)
    have hcU : n < 2^(n.log2+1) := Nat.lt_log2_self
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hpow : 2^(n.log2+1) ≤ 2^j :=
        Nat.pow_le_pow_right (by omega : 0 < (2:ℕ)) (by omega)
      omega
    · have hpow : 2^(j+1) ≤ 2^n.log2 :=
        Nat.pow_le_pow_right (by omega : 0 < (2:ℕ)) (by omega)
      omega
  · intro hj
    rw [← hj]
    exact source_positive_in_canonical_dyad434 n hn

/-- Exact intersection with the original alpha interval, still an interval. -/
theorem source_alpha_interval_dyad_intersection434 (lo hi j : ℕ) :
    (Finset.Icc lo hi) ∩ sourceDyad434 j =
      Finset.Icc (max lo (2^j)) (min hi (2^(j+1)-1)) := by
  ext n
  have hp : 0 < 2^(j+1) := Nat.pow_pos (by omega)
  simp only [Finset.mem_inter,sourceDyad434,Finset.mem_Icc,Finset.mem_Ico]
  omega

/-- Independent supports keep all original restrictions under canonical cuts. -/
theorem source_cartesian_dyad_fibre434
    (M S P R : Finset ℕ) (j : SourceQuad434)
    (hM : ∀ n ∈ M, 0 < n) (hS : ∀ n ∈ S, 0 < n)
    (hP : ∀ n ∈ P, 0 < n) (hR : ∀ n ∈ R, 0 < n) :
    ((M.product S).product (P.product R)).filter
      (fun z => sourceQuadDyadIndex434 z = j) =
    ((M ∩ sourceDyad434 j.1.1).product (S ∩ sourceDyad434 j.1.2)).product
      ((P ∩ sourceDyad434 j.2.1).product (R ∩ sourceDyad434 j.2.2)) := by
  rcases j with ⟨⟨jm,js⟩,⟨jp,jr⟩⟩
  apply Finset.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzQ,hj⟩ := Finset.mem_filter.mp hz
    obtain ⟨hms,hpr⟩ := Finset.mem_product.mp hzQ
    obtain ⟨hm,hs⟩ := Finset.mem_product.mp hms
    obtain ⟨hp,hr⟩ := Finset.mem_product.mp hpr
    have hi : z.1.1.log2 = jm ∧ z.1.2.log2 = js ∧
        z.2.1.log2 = jp ∧ z.2.2.log2 = jr := by
      simpa only [sourceQuadDyadIndex434,Prod.mk.injEq,and_assoc] using hj
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_inter.mpr ⟨hm,(source_dyad_membership_iff434 _ _ (hM _ hm)).mpr hi.1⟩,
       Finset.mem_inter.mpr ⟨hs,(source_dyad_membership_iff434 _ _ (hS _ hs)).mpr hi.2.1⟩⟩,
      Finset.mem_product.mpr
      ⟨Finset.mem_inter.mpr ⟨hp,(source_dyad_membership_iff434 _ _ (hP _ hp)).mpr hi.2.2.1⟩,
       Finset.mem_inter.mpr ⟨hr,(source_dyad_membership_iff434 _ _ (hR _ hr)).mpr hi.2.2.2⟩⟩⟩
  · intro hz
    obtain ⟨hms,hpr⟩ := Finset.mem_product.mp hz
    obtain ⟨hm,hs⟩ := Finset.mem_product.mp hms
    obtain ⟨hp,hr⟩ := Finset.mem_product.mp hpr
    obtain ⟨hm,hmd⟩ := Finset.mem_inter.mp hm
    obtain ⟨hs,hsd⟩ := Finset.mem_inter.mp hs
    obtain ⟨hp,hpd⟩ := Finset.mem_inter.mp hp
    obtain ⟨hr,hrd⟩ := Finset.mem_inter.mp hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hm,hs⟩,Finset.mem_product.mpr ⟨hp,hr⟩⟩,?_⟩
    simp only [sourceQuadDyadIndex434,Prod.mk.injEq]
    exact ⟨⟨(source_dyad_membership_iff434 _ _ (hM _ hm)).mp hmd,
      (source_dyad_membership_iff434 _ _ (hS _ hs)).mp hsd⟩,
      (source_dyad_membership_iff434 _ _ (hP _ hp)).mp hpd,
      (source_dyad_membership_iff434 _ _ (hR _ hr)).mp hrd⟩
end Green64Analytic.CorrelationMellin

end

/-! ## SourceDyadicHalflineCover -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 550000

/-- The ORIGINAL positive dyadic collars are a genuine disjoint
cover of the entire unbounded time half-line. The half-open partition
avoids double-counting shell boundaries in the countable union. -/
theorem source_dyadic_positive_halfline_cover434
    (T : ℝ) (hT : 0 < T) :
    (⋃ r : ℕ, Set.Ico ((2:ℝ)^r*T)
      ((2:ℝ)^(r+1)*T)) = Set.Ici T := by
  let f : ℕ → ℝ := fun r => (2:ℝ)^r*T
  have hFirst (r : ℕ) : f 0 ≤ f r := by
    dsimp [f]
    simpa only [pow_zero, one_mul] using
      (mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hT.le)
  have hTend : Filter.Tendsto f Filter.atTop Filter.atTop := by
    dsimp [f]
    exact Filter.Tendsto.atTop_mul_const hT
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have hUnbounded : ¬BddAbove (Set.range f) := by
    intro hbd
    rcases hbd with ⟨B,hB⟩
    have hevent : ∀ᶠ r : ℕ in Filter.atTop, B < f r :=
      hTend.eventually (Filter.eventually_gt_atTop B)
    obtain ⟨r, hr⟩ := hevent.exists
    exact (not_lt_of_ge (hB (Set.mem_range_self r))) hr
  have hUnion := iUnion_Ico_map_succ_eq_Ici
    (f:=f) hFirst hUnbounded
  change (⋃ a : ℕ, Set.Ico ((2:ℝ)^a*T)
    ((2:ℝ)^(a+1)*T)) = Set.Ici ((2:ℝ)^0*T) at hUnion
  simpa only [pow_zero, one_mul] using hUnion
end Green64Analytic.CorrelationSquare

end

/-! ## SourceDyadicNegativeCover -/

section

open Set
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 650000

/-- The negative angular-time dyadic half-open collars cover the
ENTIRE negative unbounded tail; endpoints are assigned exactly once. -/
theorem source_dyadic_negative_halfline_cover434
    (T : ℝ) (hT : 0 < T) :
    (⋃ r : ℕ, Set.Ioc (-((2:ℝ)^(r+1)*T))
      (-((2:ℝ)^r*T))) = Set.Iic (-T) := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Iic]
  constructor
  · rintro ⟨r, hleft, hright⟩
    have hone : (1:ℝ) ≤ 2^r :=
      one_le_pow₀ (by norm_num)
    have hmul : T ≤ (2:ℝ)^r*T :=
      by simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hone hT.le)
    linarith
  · intro ht
    have hPos : (-t) ∈ Set.Ici T := by
      change T ≤ -t
      linarith
    rw [← source_dyadic_positive_halfline_cover434 T hT] at hPos
    rcases Set.mem_iUnion.mp hPos with ⟨r, hr⟩
    obtain ⟨hlo,hhi⟩ := Set.mem_Ico.mp hr
    exact ⟨r, by linarith, by linarith⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceDyadicNegativeIntegral -/

section

open MeasureTheory
open scoped Function
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 850000

/-- COUNTABLE ADDITIVITY on the original negative full real-time tail.
Every negative dyadic collar occurs exactly once (up to null endpoints);
no negative-time truncation or moment assumption is introduced. -/
theorem source_dyadic_negative_integral_tail434
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : Integrable f) :
    (∫ t in Set.Iic (-T), f t) =
      ∑' r : ℕ, (∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
        (-((2:ℝ)^r*T)), f t) := by
  let c : ℕ → ℝ := fun r => -((2:ℝ)^r*T)
  have hAnti : Antitone c := by
    intro m n hmn
    dsimp [c]
    have hp : (2:ℝ)^m ≤ (2:ℝ)^n :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hmn
    exact neg_le_neg (mul_le_mul_of_nonneg_right hp hT.le)
  have hs (n : ℕ) : Order.succ n = n+1 := rfl
  have hDis : Pairwise (Disjoint on
      fun n : ℕ => Set.Ioc (c (n+1)) (c n)) := by
    simpa only [hs] using hAnti.pairwise_disjoint_on_Ioc_succ
  have hMeas : ∀ n : ℕ, MeasurableSet
      (Set.Ioc (c (n+1)) (c n)) :=
    fun _ => measurableSet_Ioc
  have hOn : IntegrableOn f
      (⋃ n : ℕ, Set.Ioc (c (n+1)) (c n)) :=
    hf.mono_measure Measure.restrict_le_self
  have hSum := (integral_iUnion hMeas hDis hOn)
  have hCover := source_dyadic_negative_halfline_cover434 T hT
  have hEq : (⋃ n : ℕ, Set.Ioc (c (n+1)) (c n)) =
      Set.Iic (-T) := by
    simpa only [c] using hCover
  rw [hEq] at hSum
  calc
    _ = ∑' n : ℕ, (∫ t in Set.Ioc (c (n+1)) (c n), f t) := hSum
    _ = ∑' n : ℕ, (∫ t in Set.Icc (c (n+1)) (c n), f t) := by
      apply tsum_congr
      intro n
      exact (integral_Icc_eq_integral_Ioc
        (μ := volume) (f := f)).symm
    _ = _ := by
      simp only [c]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceDyadicPositiveIntegral -/

section

open MeasureTheory
open scoped Function
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 760000

/-- COUNTABLE ADDITIVITY for every genuinely integrable full-real
angular-time f: the positive physical tail is the infinite sum over
all dyadic collars. This closes the missing shell-to-tail bridge,
without an ad hoc hTail premise. -/
theorem source_dyadic_positive_integral_tail434
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : Integrable f) :
    (∫ t in Set.Ici T, f t) =
      ∑' r : ℕ, (∫ t in Set.Icc ((2:ℝ)^r*T)
        ((2:ℝ)^(r+1)*T), f t) := by
  let b : ℕ → ℝ := fun r => (2:ℝ)^r*T
  have hMono : Monotone b := by
    intro m n hmn
    dsimp [b]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hmn) hT.le
  have hs (n : ℕ) : Order.succ n = n+1 := rfl
  have hDis : Pairwise (Disjoint on
      fun n : ℕ => Set.Ico (b n) (b (n+1))) := by
    simpa only [hs] using hMono.pairwise_disjoint_on_Ico_succ
  have hMeas : ∀ n : ℕ, MeasurableSet
      (Set.Ico (b n) (b (n+1))) :=
    fun _ => measurableSet_Ico
  have hOn : IntegrableOn f
      (⋃ n : ℕ, Set.Ico (b n) (b (n+1))) :=
    hf.mono_measure Measure.restrict_le_self
  have hSum := (integral_iUnion hMeas hDis hOn)
  have hCover := source_dyadic_positive_halfline_cover434 T hT
  have hEq : (⋃ n : ℕ, Set.Ico (b n) (b (n+1))) =
      Set.Ici T := by
    simpa only [b, pow_succ, Nat.succ_eq_add_one] using hCover
  rw [hEq] at hSum
  calc
    _ = ∑' n : ℕ, (∫ t in Set.Ico (b n) (b (n+1)), f t) := hSum
    _ = ∑' n : ℕ, (∫ t in Set.Icc (b n) (b (n+1)), f t) := by
      apply tsum_congr
      intro n
      exact (integral_Icc_eq_integral_Ico
        (μ := volume) (f := f)).symm
    _ = _ := by
      simp only [b, pow_succ, Nat.succ_eq_add_one]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceDyadicFullRealIntegral -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- Genuine full ± real-time weighted tail is IDENTICAL to the entire
countable sum of positive and negative dyadic collar integrals.
Summability of the paired shells is the native prior SOURCE theorem,
not a postulated high/low or tail-energy saving. -/
theorem source_dyadic_full_real_integral_tail434
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : Integrable f)
    (hPair : Summable (fun r : ℕ =>
        (∫ t in Set.Icc ((2:ℝ)^r*T) ((2:ℝ)^(r+1)*T), f t) +
        (∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
          (-((2:ℝ)^r*T)), f t)))
    (hPosNonneg : ∀ r : ℕ, 0 ≤
       ∫ t in Set.Icc ((2:ℝ)^r*T) ((2:ℝ)^(r+1)*T), f t)
    (hNegNonneg : ∀ r : ℕ, 0 ≤
       ∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
          (-((2:ℝ)^r*T)), f t) :
    (∫ t in {t : ℝ | T ≤ |t|}, f t) =
      ∑' r : ℕ,
        ((∫ t in Set.Icc ((2:ℝ)^r*T)
            ((2:ℝ)^(r+1)*T), f t) +
         (∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
            (-((2:ℝ)^r*T)), f t)) := by
  let p : ℕ → ℝ := fun r =>
    ∫ t in Set.Icc ((2:ℝ)^r*T) ((2:ℝ)^(r+1)*T), f t
  let q : ℕ → ℝ := fun r =>
    ∫ t in Set.Icc (-((2:ℝ)^(r+1)*T))
      (-((2:ℝ)^r*T)), f t
  have hp : Summable p := by
    apply Summable.of_nonneg_of_le
      (fun r => hPosNonneg r) (fun r => by
        exact le_add_of_nonneg_right (hNegNonneg r))
    exact hPair
  have hq : Summable q := by
    apply Summable.of_nonneg_of_le
      (fun r => hNegNonneg r) (fun r => by
        exact le_add_of_nonneg_left (hPosNonneg r))
    simpa only [add_comm] using hPair
  have hSet : {t : ℝ | T ≤ |t|} =
      Set.Ici T ∪ Set.Iic (-T) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_union,
      Set.mem_Ici, Set.mem_Iic]
    by_cases hzero : 0 ≤ t
    · rw [abs_of_nonneg hzero]
      constructor
      · intro ht
        exact Or.inl ht
      · rintro (ht | ht)
        · exact ht
        · linarith
    · have htneg : t ≤ 0 := le_of_lt (lt_of_not_ge hzero)
      rw [abs_of_nonpos htneg]
      constructor
      · intro ht
        exact Or.inr (by linarith)
      · rintro (ht | ht) <;> linarith
  have hDisjoint : Disjoint (Set.Ici T) (Set.Iic (-T)) := by
    apply Set.disjoint_left.mpr
    intro t htpos htneg
    have ha : T ≤ t := htpos
    have hb : t ≤ -T := htneg
    linarith
  have hIntPos : IntegrableOn f (Set.Ici T) :=
    hf.mono_measure Measure.restrict_le_self
  have hIntNeg : IntegrableOn f (Set.Iic (-T)) :=
    hf.mono_measure Measure.restrict_le_self
  have hUnion : (∫ t in {t : ℝ | T ≤ |t|}, f t) =
      (∫ t in Set.Ici T, f t) +
      (∫ t in Set.Iic (-T), f t) := by
    rw [hSet]
    exact setIntegral_union hDisjoint measurableSet_Iic hIntPos hIntNeg
  have hPos := source_dyadic_positive_integral_tail434 T hT f hf
  have hNeg := source_dyadic_negative_integral_tail434 T hT f hf
  calc
    _ = (∫ t in Set.Ici T, f t) +
        (∫ t in Set.Iic (-T), f t) := hUnion
    _ = (∑' r : ℕ, p r) + (∑' r : ℕ, q r) := by
      rw [hPos, hNeg]
    _ = ∑' r : ℕ, (p r + q r) := by
      exact (hp.tsum_add hq).symm
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceDyadicReciprocalL1 -/

section

/-! Absolute dyadic Dirichlet polynomial bounds for the genuine
small, long-prime and marked-residual coefficients.  No cancellation or
prime distribution is invoked for these short factors. -/

namespace Green64Analytic.CorrelationMellin

theorem source_dyadic_card_le_twice
    (s : Finset ℕ) (Q : ℕ) (hQ : 1 ≤ Q)
    (hs : s ⊆ Finset.Icc Q (2*Q)) :
    (s.card : ℝ) ≤ 2*(Q:ℝ) := by
  have hcount : s.card ≤ Q+1 := by
    have hc := Finset.card_le_card hs
    rw [Nat.card_Icc] at hc
    have heq : 2*Q+1-Q = Q+1 := by omega
    rwa [heq] at hc
  have htwo : Q+1 ≤ 2*Q := by omega
  exact_mod_cast hcount.trans htwo

/-- Absolute L1 sum for actual reciprocal dyadic coefficients. -/
theorem source_dyadic_reciprocal_l1
    (s : Finset ℕ) (Q : ℕ) (C : ℝ) (a : ℕ → ℂ)
    (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (hs : s ⊆ Finset.Icc Q (2*Q))
    (ha : ∀ n ∈ s, ‖a n‖ ≤ C) :
    (∑ n ∈ s, ‖a n * ((n:ℂ)⁻¹)‖) ≤ 2*C := by
  classical
  have hQR : (0:ℝ) < Q := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
  have hterm (n : ℕ) (hn : n ∈ s) :
      ‖a n * ((n:ℂ)⁻¹)‖ ≤ C/(Q:ℝ) := by
    have hqn := (Finset.mem_Icc.mp (hs hn)).1
    have hnR : (0:ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le hQ hqn
    have hleR : (Q:ℝ) ≤ (n:ℝ) := by exact_mod_cast hqn
    calc
      ‖a n * ((n:ℂ)⁻¹)‖ = ‖a n‖ / (n:ℝ) := by
        simp [norm_mul, norm_inv, div_eq_mul_inv]
      _ ≤ C / (n:ℝ) := div_le_div_of_nonneg_right (ha n hn) hnR.le
      _ ≤ C / (Q:ℝ) := by
        apply (div_le_div_iff₀ hnR hQR).mpr
        exact mul_le_mul_of_nonneg_left hleR hC
  calc
    _ ≤ ∑ _n ∈ s, C/(Q:ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n hn
    _ = (s.card : ℝ) * (C/(Q:ℝ)) := by simp
    _ ≤ (2*(Q:ℝ)) * (C/(Q:ℝ)) :=
      mul_le_mul_of_nonneg_right
        (source_dyadic_card_le_twice s Q hQ hs)
        (div_nonneg hC hQR.le)
    _ = 2*C := by field_simp <;> ring

/-- Pointwise dyadic reciprocal polynomial bound for any real twist.
The same theorem handles the literal long-prime interval character
and the literal marked residual d_{r'} coefficients. -/
theorem source_dyadic_polynomial_bound
    (s : Finset ℕ) (Q : ℕ) (C : ℝ) (a : ℕ → ℂ) (t : ℝ)
    (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (hs : s ⊆ Finset.Icc Q (2*Q))
    (ha : ∀ n ∈ s, ‖a n‖ ≤ C) :
    ‖∑ n ∈ s, a n * ((n:ℂ)⁻¹) * sourcePhase n t‖ ≤ 2*C := by
  calc
    _ ≤ ∑ n ∈ s, ‖a n * ((n:ℂ)⁻¹) * sourcePhase n t‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ s, ‖a n * ((n:ℂ)⁻¹)‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [norm_mul, sourcePhase_norm, mul_one]
    _ ≤ 2*C := source_dyadic_reciprocal_l1 s Q C a hQ hC hs ha
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLowFrequencyOriginalDiscrepancy -/

section

/-! The actual source `sh:discrepancy` is universal over all small
character moduli, ALL integer intervals inside [1,x²], and all real
frequencies bounded by L^B.  The alpha sequence is kept unchanged.
-/

namespace Green64Analytic.CorrelationMellin

/-- Exact quantitative form of the source `sh:discrepancy` premise
sufficient to instantiate every original dyadic alpha polynomial. -/
def SourceAlphaDiscrepancy (L B x : ℝ) (alpha : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ) (chi : DirichletCharacter ℂ q)
    (a b : ℕ) (freq : ℝ),
    (q:ℝ) ≤ L^B →
    1 ≤ a → (b:ℝ) ≤ x^2 → |freq| ≤ L^B →
    ‖∑ m ∈ Finset.Icc a b,
      alpha m * chi m * ((m:ℂ)⁻¹) * sourcePhase m freq‖ ≤
      L^(-B)

/-- Original low-frequency alpha polynomial with its exact character
and the shift by sigma0; no generic coefficient replacement. -/
theorem source_low_frequency_alpha_discrepancy
    (L B x : ℝ) (alpha : ℕ → ℂ)
    (hdisc : SourceAlphaDiscrepancy L B x alpha)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (a b : ℕ) (t sigma0 : ℝ)
    (hq : (q:ℝ) ≤ L^B) (ha : 1 ≤ a)
    (hb : (b:ℝ) ≤ x^2)
    (hfreq : |t+sigma0| ≤ L^B) :
    ‖∑ m ∈ Finset.Icc a b,
      alpha m * chi m * (m:ℂ)⁻¹ * sourcePhase m (sigma0+t)‖ ≤
       L^(-B) := by
  rw [add_comm sigma0 t]
  exact hdisc q chi a b (t+sigma0) hq ha hb hfreq
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLowFrequencyFourFactor -/

section

/-! The actual four-factor source polynomial on LOW frequencies.
The alpha bound is ONLY the literal sh:discrepancy, with modulus,
original dyadic interval, and shifted frequency all explicit.
-/

namespace Green64Analytic.CorrelationMellin

theorem source_fourfactor_low_frequency_pointwise
    (L B x : ℝ) (hL : 0 < L)
    (alpha : ℕ → ℂ) (hdisc : SourceAlphaDiscrepancy L B x alpha)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (a b : ℕ) (hq : (q:ℝ) ≤ L^B)
    (ha : 1 ≤ a) (hb : (b:ℝ) ≤ x^2)
    (sigma0 sigma1 t : ℝ) (hfreq : |t+sigma0| ≤ L^B)
    (P Pprime R0 : ℕ)
    (small long residual : Finset ℕ)
    (bs bp d : ℕ → ℂ) (Cs Cl D : ℝ)
    (hP : 1 ≤ P) (hPprime : 1 ≤ Pprime) (hR0 : 1 ≤ R0)
    (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl) (hD : 0 ≤ D)
    (hSmall : small ⊆ Finset.Icc P (2*P))
    (hLong : long ⊆ Finset.Icc Pprime (2*Pprime))
    (hResidual : residual ⊆ Finset.Icc R0 (2*R0))
    (hbs : ∀ p ∈ small, ‖bs p‖ ≤ Cs)
    (hbp : ∀ p ∈ long, ‖bp p‖ ≤ Cl)
    (hd : ∀ r ∈ residual, ‖d r‖ ≤ D) :
    ‖(∑ p ∈ small, bs p * (p:ℂ)⁻¹ * sourcePhase p t) *
       (∑ p ∈ long, bp p * (p:ℂ)⁻¹ * sourcePhase p (sigma1+t)) *
       ((∑ m ∈ Finset.Icc a b,
         alpha m * chi m * (m:ℂ)⁻¹ * sourcePhase m (sigma0+t)) *
        (∑ r ∈ residual, d r * (r:ℂ)⁻¹ * sourcePhase r t))‖ ≤
      (2*Cs)*(2*Cl)*(L^(-B)*(2*D)) := by
  classical
  have hsmall := source_dyadic_polynomial_bound
    small P Cs bs t hP hCs hSmall hbs
  have hlong := source_dyadic_polynomial_bound
    long Pprime Cl bp (sigma1+t) hPprime hCl hLong hbp
  have hresidual := source_dyadic_polynomial_bound
    residual R0 D d t hR0 hD hResidual hd
  have halpha := source_low_frequency_alpha_discrepancy
    L B x alpha hdisc q chi a b t sigma0 hq ha hb hfreq
  have hLp : 0 ≤ L^(-B) := le_of_lt (Real.rpow_pos_of_pos hL _)
  calc
    _ = (‖∑ p ∈ small, bs p * (p:ℂ)⁻¹ * sourcePhase p t‖) *
        (‖∑ p ∈ long, bp p * (p:ℂ)⁻¹ * sourcePhase p (sigma1+t)‖) *
        ((‖∑ m ∈ Finset.Icc a b,
          alpha m * chi m * (m:ℂ)⁻¹ * sourcePhase m (sigma0+t)‖) *
         (‖∑ r ∈ residual, d r * (r:ℂ)⁻¹ * sourcePhase r t‖)) := by
           simp only [norm_mul]
    _ ≤ (2*Cs)*(2*Cl)*(L^(-B)*(2*D)) := by
      gcongr
end Green64Analytic.CorrelationMellin

end

/-! ## SourceLowFrequencyIntegral -/

section

open MeasureTheory

namespace Green64Analytic.CorrelationMellin

/-- The literal logarithmic real-time source phase is continuous,
including arbitrary fixed additive source twists. -/
theorem sourcePhase_continuous (n : ℕ) (shift : ℝ) :
    Continuous (fun t : ℝ => sourcePhase n (shift+t)) := by
  unfold sourcePhase
  fun_prop

/-- A bounded continuous analytic energy on a REAL interval integrates
to the exact interval-length times the squared pointwise majorant. -/
theorem source_pointwise_to_interval_square_energy
    (F : ℝ → ℂ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcont : Continuous F)
    (hpoint : ∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ C) :
    (∫ t in Set.Icc (-T) T, ‖F t‖^2) ≤ 2*T*C^2 := by
  have hInt : IntegrableOn (fun t : ℝ => ‖F t‖^2)
      (Set.Icc (-T) T) :=
    (hcont.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hμ : volume (Set.Icc (-T) T) ≠ ⊤ :=
    (measure_Icc_lt_top : volume (Set.Icc (-T) T) < ⊤).ne
  have hCInt : IntegrableOn (fun _ : ℝ => C^2)
      (Set.Icc (-T) T) := integrableOn_const hμ
  have hMono : (∫ t in Set.Icc (-T) T, ‖F t‖^2) ≤
      (∫ _t in Set.Icc (-T) T, C^2) := by
    apply setIntegral_mono_on hInt hCInt measurableSet_Icc
    intro t ht
    exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hpoint t ht)
  calc
    _ ≤ (∫ _t in Set.Icc (-T) T, C^2) := hMono
    _ = 2*T*C^2 := by
      rw [setIntegral_const]
      change (volume (Set.Icc (-T) T)).toReal * C^2 = 2*T*C^2
      rw [Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ T - (-T))]
      ring
end Green64Analytic.CorrelationMellin

end

