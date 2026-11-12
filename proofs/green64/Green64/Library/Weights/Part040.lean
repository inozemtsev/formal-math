module

public import Green64.Library.Weights.Part039
public import Green64.Library.Analysis.Estimates.SourceLowFrequencyFourFactorIntegral
public import Mathlib
public import Green64.Library.Analysis.Estimates.Part004
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part012
public import Green64.Library.Weights.Part011
public import Green64.Library.Correlation.Part002
public import Green64.Library.Weights.Part013
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Analysis.Estimates.Part001
public import Green64.Library.Weights.Part033

@[expose] public section

/-!
# Weights / Part040

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceActualFourFactorCollapse -/

section

namespace Green64Analytic.CorrelationMellin

/-! Exact original P_l R product, including the source character and
both fixed frequency shifts. The product support comes from the actual
Mellin dyads and not an independently supplied coefficient array. -/

noncomputable def sourceActualPrimeResidualTriple
    (alpha bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ) :
    Fin 3 → ℕ → ℂ :=
  sourceThreeProductCoefficients
    (fun m => alpha m * chi m * sourcePhase m sigma0)
    (fun p => bp p * sourcePhase p sigma1)
    d

theorem source_actual_prime_residual_triple_eq
    (M P R : Finset ℕ) (alpha bp d : ℕ → ℂ)
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 t : ℝ)
    (hM : ∀ m ∈ M, 0 < m) (hP : ∀ p ∈ P, 0 < p)
    (hR : ∀ r ∈ R, 0 < r) :
    sourceThreeCollapsedAt (sourceThreeActualTuples M P R)
      (sourceActualPrimeResidualTriple alpha bp d chi sigma0 sigma1) t =
    (∑ m ∈ M, alpha m * chi m * (m:ℂ)⁻¹ *
      sourcePhase m (sigma0+t)) *
    (∑ p ∈ P, bp p * (p:ℂ)⁻¹ *
      sourcePhase p (sigma1+t)) *
    (∑ r ∈ R, d r * (r:ℂ)⁻¹ * sourcePhase r t) := by
  unfold sourceActualPrimeResidualTriple
  rw [source_three_actual_product_identity M P R _ _ _ t hM hP hR]
  simp_rw [sourcePhase_add]
  apply congrArg₂ (fun (a b : ℂ) => a * b)
  · apply congrArg₂ (fun (a b : ℂ) => a * b)
    · apply Finset.sum_congr rfl
      intro m hm
      ring
    · apply Finset.sum_congr rfl
      intro p hp
      ring
  · rfl

theorem source_short_prime_as_literal_sum
    (s : Finset ℕ) (bs : ℕ → ℂ) (t : ℝ) :
    sourceShortPrimeAt s bs t =
      ∑ p ∈ s, bs p * (p:ℂ)⁻¹ * sourcePhase p t := by
  classical
  simpa only [sourceShortPrimeAt] using
    (Finset.sum_coe_sort s
      (fun p => bs p * (p:ℂ)⁻¹ * sourcePhase p t))

theorem source_actual_fourfactor_threefactor_eq
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 t : ℝ)
    (ha : 1 ≤ a) (hP : ∀ p ∈ long, 0 < p)
    (hR : ∀ r ∈ R, 0 < r) :
    sourceFourFactorAt small long R a b alpha bs bp d chi
      sigma0 sigma1 t =
    sourceShortPrimeAt small bs t *
      sourceThreeCollapsedAt
        (sourceThreeActualTuples (Finset.Icc a b) long R)
        (sourceActualPrimeResidualTriple alpha bp d chi sigma0 sigma1) t := by
  rw [source_short_prime_as_literal_sum]
  rw [source_actual_prime_residual_triple_eq
    (Finset.Icc a b) long R alpha bp d chi sigma0 sigma1 t]
  · unfold sourceFourFactorAt
    ring
  · intro m hm
    exact lt_of_lt_of_le (by omega : 0 < a) (Finset.mem_Icc.mp hm).1
  · exact hP
  · exact hR

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualShortPrimeUniform -/

section

namespace Green64Analytic.CorrelationMellin

/-! Uniform bound for the actual P_s(t), using only its reciprocal
prime coefficients and the literal dyadic support. No PNT or new
large-prime hypothesis. -/

theorem source_actual_short_prime_uniform
    (s : Finset ℕ) (bs : ℕ → ℂ) (P : ℕ) (Cs : ℝ)
    (hP : 1 ≤ P) (hCs : 0 ≤ Cs)
    (hs : s ⊆ Finset.Icc P (2*P))
    (hbs : ∀ p ∈ s, ‖bs p‖ ≤ Cs)
    (t : ℝ) :
    ‖sourceShortPrimeAt s bs t‖ ≤ 2*Cs := by
  classical
  have hPpos : (0:ℝ) < P := by exact_mod_cast hP
  have hcard : (s.card : ℝ) ≤ 2*(P:ℝ) := by
    have hsub := Finset.card_le_card hs
    have hIcc : (Finset.Icc P (2*P)).card = P+1 := by
      rw [Nat.card_Icc]
      omega
    rw [hIcc] at hsub
    have hc : P+1 ≤ 2*P := by omega
    exact_mod_cast hsub.trans hc
  have hterm (p : ℕ) (hp : p ∈ s) :
      ‖bs p * ((p:ℂ)⁻¹) * sourcePhase p t‖ ≤ Cs/(P:ℝ) := by
    have hpn : P ≤ p := (Finset.mem_Icc.mp (hs hp)).1
    have hpp : (0:ℝ) < p := by exact_mod_cast lt_of_lt_of_le hP hpn
    have hreal : (P:ℝ) ≤ p := by exact_mod_cast hpn
    calc
      _ = ‖bs p‖ / (p:ℝ) := by
        simp only [norm_mul, norm_inv, Complex.norm_natCast,
          sourcePhase_norm, mul_one]
        ring
      _ ≤ Cs / (p:ℝ) :=
        div_le_div_of_nonneg_right (hbs p hp) hpp.le
      _ ≤ Cs / (P:ℝ) := by
        apply (div_le_div_iff₀ hpp hPpos).mpr
        exact mul_le_mul_of_nonneg_left hreal hCs
  rw [source_short_prime_as_literal_sum]
  calc
    _ ≤ ∑ p ∈ s, ‖bs p * ((p:ℂ)⁻¹) * sourcePhase p t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ s, Cs/(P:ℝ) :=
      Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * (Cs/(P:ℝ)) := by simp
    _ ≤ 2*(P:ℝ)*(Cs/(P:ℝ)) :=
      mul_le_mul_of_nonneg_right hcard
        (div_nonneg hCs hPpos.le)
    _ = 2*Cs := by
      field_simp
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualHighPrimeFactorEnergy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Restore the *actual* P_s(t) factor on the high-frequency occupied
large-value source range. This is pointwise Cauchy domination from the
prime dyadic support, not another exceptional-set hypothesis. -/

theorem source_actual_large_high_short_prime_energy
    (s : Finset ℕ) (bs : ℕ → ℂ) (P : ℕ) (Cs : ℝ)
    (T δ S : ℝ) (F : ℝ → ℂ)
    (hP : 1 ≤ P) (hCs : 0 ≤ Cs)
    (hs : s ⊆ Finset.Icc P (2*P))
    (hbs : ∀ p ∈ s, ‖bs p‖ ≤ Cs)
    (hF : Continuous F) :
    (∫ t in sourceActualLargeHighTimes s bs T δ S,
      ‖sourceShortPrimeAt s bs t * F t‖^2) ≤
      (2*Cs)^2 *
        (∫ t in sourceActualLargeHighTimes s bs T δ S,
          ‖F t‖^2) := by
  let E := sourceActualLargeHighTimes s bs T δ S
  have hE : MeasurableSet E :=
    source_actual_large_high_measurable s bs T δ S
  have hEsub : E ⊆ Set.Icc (-T) T := by
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨j,hj'⟩
    rcases Set.mem_iUnion.mp hj' with ⟨_,htCell⟩
    exact htCell.1.1
  have hPcont : Continuous (fun t => sourceShortPrimeAt s bs t * F t) :=
    (sourceShortPrimeAt_continuous s bs).mul hF
  have hFInt : IntegrableOn (fun t : ℝ => ‖F t‖^2) E :=
    ((hF.norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set hEsub
  have hPFInt : IntegrableOn
      (fun t : ℝ => ‖sourceShortPrimeAt s bs t * F t‖^2) E :=
    ((hPcont.norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set hEsub
  have hBound (t : ℝ) (ht : t ∈ E) :
      ‖sourceShortPrimeAt s bs t * F t‖^2 ≤
        (2*Cs)^2 * ‖F t‖^2 := by
    have hS := source_actual_short_prime_uniform
      s bs P Cs hP hCs hs hbs t
    have hSsq := (sq_le_sq₀ (norm_nonneg _)
      (by positivity : 0 ≤ 2*Cs)).mpr hS
    calc
      _ = ‖sourceShortPrimeAt s bs t‖^2 * ‖F t‖^2 := by
        rw [norm_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hSsq (sq_nonneg _)
  have hRightInt : IntegrableOn
      (fun t : ℝ => (2*Cs)^2 * ‖F t‖^2) E :=
    hFInt.const_mul _
  calc
    _ ≤ ∫ t in E, (2*Cs)^2 * ‖F t‖^2 :=
      setIntegral_mono_on hPFInt hRightInt hE hBound
    _ = _ := by
      rw [integral_const_mul]
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualHighFourFactorPhysicalExact -/

section

namespace Green64Analytic.CorrelationMellin
open Green64Analytic.LongPrime

/-! Exact source high physical fourfactor: the short-prime factor,
U1-certified long-prime factor, and actual fixed-gcd marked residual
are the same sourceFourFactorAt from 03-shifted.tex. -/

theorem source_actual_fourfactor_physical_exact
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (G Parity : Finset ℕ) (c : ℕ → ℂ)
    (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
    (sigmaR : ℝ) (small R : Finset ℕ) (a b : ℕ)
    (alpha bs : ℕ → ℂ)
    (qM qL : ℕ) (chiM : DirichletCharacter ℂ qM)
    (chiL : DirichletCharacter ℂ qL)
    (N : ℝ) (I : Set ℝ) (sigma0 sigma1 t : ℝ) :
    sourceFourFactorAt small (sourceLongPrimeSourceSupport N I)
      R a b alpha bs (fun p => chiL p)
      (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR sigmaR)
      chiM sigma0 sigma1 t =
    sourceShortPrimeAt small bs t *
      (sourceCorrelationLongPrime qL chiL N I (t+sigma1) *
      sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR sigmaR
        (Finset.Icc a b) R alpha (fun m => chiM m)
        sigma0 t) := by
  rw [source_physical_fourfactor_eq_source_residual]
  simp_rw [add_comm sigma1 t]
  rw [← source_long_prime_equals_literal_phase qL chiL N I (t+sigma1)]
  rw [source_short_prime_as_literal_sum]
  ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourFactorContinuous -/

section

namespace Green64Analytic.CorrelationMellin

/-! Continuity of the original rational-character four-factor Mellin
polynomial, reused from the verified literal convolution identity. -/

theorem source_actual_fourfactor_continuous
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (ha : 1 ≤ a)
    (hP : ∀ p ∈ long, 0 < p)
    (hR : ∀ r ∈ R, 0 < r) :
    Continuous (fun t : ℝ =>
      sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 t) := by
  have hEq : (fun t : ℝ =>
      sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 t) =
      (fun t => sourceShortPrimeAt small bs t *
        sourceThreeCollapsedAt
          (sourceThreeActualTuples (Finset.Icc a b) long R)
          (sourceActualPrimeResidualTriple alpha bp d chi sigma0 sigma1) t) := by
    funext t
    exact source_actual_fourfactor_threefactor_eq
      small long R a b alpha bs bp d chi sigma0 sigma1 t
      ha hP hR
  rw [hEq]
  exact (sourceShortPrimeAt_continuous small bs).mul
    (sourceThreeCollapsedAt_continuous _ _)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLargeLowPhysicalEnergy -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

theorem source_actual_large_low_physical_fourfactor_energy
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      ∀ (L B x Tfull δ Sfreq : ℝ), 0 < L → 0 ≤ Sfreq+2 →
      ∀ (alpha : ℕ → ℂ), SourceAlphaDiscrepancy L B x alpha →
      ∀ (qM : ℕ) (chiM : DirichletCharacter ℂ qM),
      ∀ (a b : ℕ), (qM:ℝ) ≤ L^B →
        1 ≤ a → (b:ℝ) ≤ x^2 →
      ∀ (sigma0 sigma1 : ℝ), Sfreq+2+|sigma0| ≤ L^B →
      ∀ (P Pprime R0 : ℕ)
        (small long R : Finset ℕ)
        (bs bp : ℕ → ℂ) (Cs Cl C : ℝ),
      1 ≤ P → 1 ≤ Pprime → 1 ≤ R0 →
      0 ≤ Cs → 0 ≤ Cl → 0 ≤ C →
      small ⊆ Finset.Icc P (2*P) →
      long ⊆ Finset.Icc Pprime (2*Pprime) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ p ∈ small, ‖bs p‖ ≤ Cs) →
      (∀ p ∈ long, ‖bp p‖ ≤ Cl) →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      (∫ t in sourceActualLargeLowTimes small bs Tfull δ Sfreq,
        ‖sourceFourFactorAt small long R a b alpha bs bp
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c den d0 q chiR sigmaR)
          chiM sigma0 sigma1 t‖^2) ≤
        2*(Sfreq+2)*((2*Cs)*(2*Cl)*
          (L^(-B)*(2*(C*K^(Fintype.card ι+Fintype.card β+1)))))^2 := by
  obtain ⟨K,hK,hFull⟩ := source_physical_low_frequency_fourfactor_energy
    q0 vmin tmax hq0 hq1 hv
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _ L B x Tfull δ Sfreq hL hSfreq alpha hDisc
    qM chiM a b hqM ha hb sigma0 sigma1 hfreq
    P Pprime R0 small long R bs bp Cs Cl C
    hP hPprime hR0 hCs hCl hC hSmall hLong hR hBs hBp
    S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR
  have hLongPos : ∀ p ∈ long, 0 < p := by
    intro p hp
    have hh := (Finset.mem_Icc.mp (hLong hp)).1
    omega
  have hRPos : ∀ r ∈ R, 0 < r := by
    intro r hr
    have hh := (Finset.mem_Icc.mp (hR hr)).1
    omega
  let d : ℕ → ℂ :=
    sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c den d0 q chiR sigmaR
  let F : ℝ → ℂ := fun t =>
    sourceFourFactorAt small long R a b alpha bs bp d
      chiM sigma0 sigma1 t
  have hContinuous : Continuous F :=
    source_actual_fourfactor_continuous small long R a b
      alpha bs bp d chiM sigma0 sigma1 ha hLongPos hRPos
  have hPartial := source_actual_large_low_energy_from_full_interval
    small bs Tfull δ Sfreq F hContinuous
  have hBound := hFull L B x (Sfreq+2) hL hSfreq alpha hDisc
    qM chiM a b hqM ha hb sigma0 sigma1 hfreq
    P Pprime R0 small long R bs bp Cs Cl C
    hP hPprime hR0 hCs hCl hC hSmall hLong hR hBs hBp
    S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR
  change (∫ t in sourceActualLargeLowTimes small bs Tfull δ Sfreq,
      ‖F t‖^2) ≤ _ 
  exact hPartial.trans hBound

end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLargeLowPhysicalSaving -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

theorem source_actual_large_low_physical_log_saving
    (q0 vmin C0 : ℝ) (tmax ec es D : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) :
    ∃ K : ℝ, ∃ g : ℕ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      ∀ (L x Tfull δ Sfreq : ℝ),
        max 3 K ≤ L → 0 ≤ Sfreq+2 →
        Sfreq+2 ≤ L^es →
        (Fintype.card ι:ℝ) ≤ C0*Real.log L →
        (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (alpha : ℕ → ℂ), SourceAlphaDiscrepancy L ((D+5*(ec+es+g+2)+10:ℕ):ℝ) x alpha →
      ∀ (qM : ℕ) (chiM : DirichletCharacter ℂ qM),
      ∀ (a b : ℕ), (qM:ℝ) ≤ L^((D+5*(ec+es+g+2)+10:ℕ):ℝ) →
        1 ≤ a → (b:ℝ) ≤ x^2 →
      ∀ (sigma0 sigma1 : ℝ), Sfreq+2+|sigma0| ≤ L^((D+5*(ec+es+g+2)+10:ℕ):ℝ) →
      ∀ (P Pprime R0 : ℕ)
        (small long R : Finset ℕ)
        (bs bp : ℕ → ℂ) (Cs Cl C : ℝ),
      1 ≤ P → 1 ≤ Pprime → 1 ≤ R0 →
      0 ≤ Cs → 0 ≤ Cl → 0 ≤ C →
      Cs ≤ L^es → Cl ≤ L^es → C ≤ L^ec →
      small ⊆ Finset.Icc P (2*P) →
      long ⊆ Finset.Icc Pprime (2*Pprime) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ p ∈ small, ‖bs p‖ ≤ Cs) →
      (∀ p ∈ long, ‖bp p‖ ≤ Cl) →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      (∫ t in sourceActualLargeLowTimes small bs Tfull δ Sfreq,
        ‖sourceFourFactorAt small long R a b alpha bs bp
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c den d0 q chiR sigmaR)
          chiM sigma0 sigma1 t‖^2) ≤ (L^D)⁻¹ := by
  obtain ⟨K,hK,hFull⟩ :=
    source_actual_large_low_physical_fourfactor_energy
      q0 vmin tmax hq0 hq1 hv
  obtain ⟨g,hGroups⟩ :=
    Green64Analytic.CorrelationSquare.source_literal_group_card_uniform_nat_log_budget
      K C0 hK hC0
  refine ⟨K,g,hK,?_⟩
  intro ι β _ _ _ _ L x Tfull δ Sfreq hL hSnonneg hSbudget
    hSmall hBig alpha hDisc qM chiM a b hqM ha hb
    sigma0 sigma1 hfreq P Pprime R0 small long R bs bp
    Cs Cl C hP hPprime hR0 hCs hCl hC
    hCsBudget hClBudget hCBudget hSmallSupport hLongSupport
    hRSupport hBs hBp
    S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb
    hVsmall hVbig hcoef G Parity c hc den d0 q chiR sigmaR
  let E : ℕ := ec+es+g+2
  let B : ℝ := ((D+5*E+10:ℕ):ℝ)
  have hL3 : 3 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hPowEs : L^es ≤ L^E :=
    pow_le_pow_right₀ hLone (by dsimp [E]; omega)
  have hPowEc : L^ec ≤ L^E :=
    pow_le_pow_right₀ hLone (by dsimp [E]; omega)
  have hPowG : L^g ≤ L^E :=
    pow_le_pow_right₀ hLone (by dsimp [E]; omega)
  have hMarked : K^(Fintype.card ι+Fintype.card β+1) ≤ L^E :=
    (hGroups L hL (Fintype.card ι) (Fintype.card β) hSmall hBig).trans hPowG
  have hMarkedNonneg :
      0 ≤ K^(Fintype.card ι+Fintype.card β+1) := by positivity
  have hLow := hFull L B x Tfull δ Sfreq hLpos hSnonneg
    alpha hDisc qM chiM a b hqM ha hb sigma0 sigma1 hfreq
    P Pprime R0 small long R bs bp Cs Cl C
    hP hPprime hR0 hCs hCl hC
    hSmallSupport hLongSupport hRSupport hBs hBp
    S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR
  have hNum := source_actual_low_numeric_log_crush
    L (Sfreq+2) Cs Cl C (K^(Fintype.card ι+Fintype.card β+1))
    E D hL3 hSnonneg hCs hCl hC hMarkedNonneg
    (hSbudget.trans hPowEs)
    (hCsBudget.trans hPowEs)
    (hClBudget.trans hPowEs)
    (hCBudget.trans hPowEc) hMarked
  have hInv : L^(-B) = (L^(D+5*E+10))⁻¹ := by
    dsimp [B]
    rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ L)]
    simp only [Real.rpow_natCast]
  calc
    _ ≤ 2*(Sfreq+2)*((2*Cs)*(2*Cl)*
       (L^(-B)*(2*(C*K^(Fintype.card ι+Fintype.card β+1)))))^2 := hLow
    _ = 2*(Sfreq+2)*((2*Cs)*(2*Cl)*
       ((L^(D+5*E+10))⁻¹*(2*(C*K^(Fintype.card ι+Fintype.card β+1)))))^2 := by rw [hInv]
    _ ≤ (L^D)⁻¹ := hNum
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualAllGcdPhysicalLow -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! All genuine gcd classes, all induced characters and the actual
dyad-cut original alpha. Uses only original universal SourceAlphaDiscrepancy,
the already proved physical marked residual bound, and the source
joint modulus budget. No class-specific discrepancy assumption. -/

theorem source_actual_all_gcd_physical_low_log_saving
    (q0 vmin C0 : ℝ) (tmax ec es D : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) :
    ∃ K : ℝ, ∃ g : ℕ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      ∀ (L x Tfull delta Sfreq : ℝ),
        max 3 K ≤ L → 0 ≤ Sfreq+2 →
        Sfreq+2 ≤ L^es →
        (Fintype.card ι:ℝ) ≤ C0*Real.log L →
        (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (alpha : ℕ → ℂ),
        SourceAlphaDiscrepancy L
          ((D+5*(ec+es+g+2)+10:ℕ):ℝ) x alpha →
      ∀ (qBase den lo hi : ℕ) (chi0 : DirichletCharacter ℂ qBase)
        (Cmod : ℝ),
        (qBase:ℝ) ≤ L^Cmod →
        (den:ℝ) ≤ L^Cmod →
        2*Cmod ≤ ((D+5*(ec+es+g+2)+10:ℕ):ℝ) →
      ∀ d ∈ den.divisors,
      ∀ (xi : DirichletCharacter ℂ (den/d)),
      ∀ (a b : ℕ),
        1 ≤ a → (b:ℝ) ≤ x^2 →
      ∀ (sigma0 sigma1 : ℝ),
        Sfreq+2+|sigma0| ≤
          L^((D+5*(ec+es+g+2)+10:ℕ):ℝ) →
      ∀ (P Pprime R0 : ℕ)
        (small long R : Finset ℕ)
        (bs bp : ℕ → ℂ) (Cs Cl C : ℝ),
      1 ≤ P → 1 ≤ Pprime → 1 ≤ R0 →
      0 ≤ Cs → 0 ≤ Cl → 0 ≤ C →
      Cs ≤ L^es → Cl ≤ L^es → C ≤ L^ec →
      small ⊆ Finset.Icc P (2*P) →
      long ⊆ Finset.Icc Pprime (2*Pprime) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ p ∈ small, ‖bs p‖ ≤ Cs) →
      (∀ p ∈ long, ‖bp p‖ ≤ Cl) →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      (∫ t in sourceActualLargeLowTimes small bs Tfull delta Sfreq,
        ‖sourceFourFactorAt small long R a b
          (sourceAlphaDyadicCut alpha lo hi) bs bp
          (sourcePhysicalMarkedResidual S Ts Tb
            q0 Vs Vsmall Vbig ts tb coef k
            G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 t‖^2) ≤ (L^D)⁻¹ := by
  obtain ⟨K,g,hK,hUniform⟩ :=
    source_actual_large_low_physical_log_saving
      q0 vmin C0 tmax ec es D hq0 hq1 hv hC0
  refine ⟨K,g,hK,?_⟩
  intro ι β _ _ _ _ L x Tfull delta Sfreq hL hSNonneg hSbudget
    hSmallGroups hBigGroups alpha hDisc
    qBase den lo hi chi0 Cmod hBase hDen hModBudget
    d hd xi a b ha hb sigma0 sigma1 hFreq
    P Pprime R0 small long R bs bp Cs Cl C
    hP hPprime hR0 hCs hCl hC hCsBudget hClBudget hCBudget
    hSmall hLong hResidual hbs hbp
    S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc denR d0 q chiR sigmaR
  let B : ℝ := ((D+5*(ec+es+g+2)+10:ℕ):ℝ)
  have hLone : 1 ≤ L := by
    have hL3 : 3 ≤ L := (le_max_left _ _).trans hL
    linarith
  have hJoint : ((qBase*(den/d):ℕ):ℝ) ≤ L^B :=
    source_actual_joint_reduced_modulus_budget qBase den d
      L Cmod B hLone hBase hDen hModBudget
  have hDiscCut : SourceAlphaDiscrepancy L B x
        (sourceAlphaDyadicCut alpha lo hi) :=
    source_alpha_dyadic_cut_preserves_discrepancy
      L B x alpha lo hi hDisc
  exact hUniform L x Tfull delta Sfreq hL hSNonneg hSbudget
    hSmallGroups hBigGroups
    (sourceAlphaDyadicCut alpha lo hi) hDiscCut
    (qBase*(den/d))
    (sourceJointCharacter qBase (den/d) chi0 xi)
    a b hJoint ha hb sigma0 sigma1 hFreq
    P Pprime R0 small long R bs bp Cs Cl C
    hP hPprime hR0 hCs hCl hC
    hCsBudget hClBudget hCBudget
    hSmall hLong hResidual hbs hbp
    S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc denR d0 q chiR sigmaR
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualFourDyadTailEnergy -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationMellin

/-! Continuous source fourfold cutoff and quantitative REAL Mellin
tail energy for its finite Fourier approximation. -/
theorem source_actual_fourdyad_literal_term_continuous
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 : ℝ)
    (z : (ℕ × ℕ) × (ℕ × ℕ)) :
    Continuous (fun t : ℝ =>
      sourceActualFourDyadLiteralTerm alpha bs bp d chi
        sigma0 sigma1 t z) := by
  have hm : Continuous (fun t : ℝ =>
      alpha z.1.1 * chi z.1.1 * (z.1.1:ℂ)⁻¹ *
        sourcePhase z.1.1 (sigma0+t)) :=
    continuous_const.mul (sourcePhase_continuous z.1.1 sigma0)
  have hsPhase : Continuous (fun t : ℝ =>
      sourcePhase z.1.2 t) := by
    simpa only [zero_add] using sourcePhase_continuous z.1.2 0
  have hs : Continuous (fun t : ℝ =>
      bs z.1.2 * (z.1.2:ℂ)⁻¹ *
        sourcePhase z.1.2 t) :=
    continuous_const.mul hsPhase
  have hp : Continuous (fun t : ℝ =>
      bp z.2.1 * (z.2.1:ℂ)⁻¹ *
        sourcePhase z.2.1 (sigma1+t)) :=
    continuous_const.mul (sourcePhase_continuous z.2.1 sigma1)
  have hrPhase : Continuous (fun t : ℝ =>
      sourcePhase z.2.2 t) := by
    simpa only [zero_add] using sourcePhase_continuous z.2.2 0
  have hr : Continuous (fun t : ℝ =>
      d z.2.2 * (z.2.2:ℂ)⁻¹ *
        sourcePhase z.2.2 t) :=
    continuous_const.mul hrPhase
  change Continuous (fun t : ℝ =>
    ((alpha z.1.1 * chi z.1.1 * (z.1.1:ℂ)⁻¹ *
         sourcePhase z.1.1 (sigma0+t)) *
      (bs z.1.2 * (z.1.2:ℂ)⁻¹ * sourcePhase z.1.2 t)) *
     (bp z.2.1 * (z.2.1:ℂ)⁻¹ *
         sourcePhase z.2.1 (sigma1+t)) *
      (d z.2.2 * (z.2.2:ℂ)⁻¹ * sourcePhase z.2.2 t))
  exact ((hm.mul hs).mul hp).mul hr
theorem source_actual_smooth_fourdyad_continuous
    (small long R : Finset ℕ) (a b : ℕ)
    (cutoff alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 : ℝ) :
    Continuous (fun t : ℝ =>
      sourceActualSmoothFourDyadAt small long R a b
        cutoff alpha bs bp d chi sigma0 sigma1 t) := by
  unfold sourceActualSmoothFourDyadAt
  apply continuous_finset_sum
  intro z hz
  exact continuous_const.mul
    (source_actual_fourdyad_literal_term_continuous
      alpha bs bp d chi sigma0 sigma1 z)

theorem source_actual_finite_fourier_shift_continuous
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 : ℝ)
    (freqs : Finset ℝ) (weights : ℝ → ℂ)
    (ha : 1 ≤ a)
    (hp : ∀ p ∈ long, 0 < p)
    (hr : ∀ r ∈ R, 0 < r) :
    Continuous (fun t : ℝ =>
      ∑ nu ∈ freqs, weights nu *
        sourceFourFactorAt small long R a b alpha bs bp d chi
          sigma0 sigma1 (t+nu)) := by
  apply continuous_finset_sum
  intro nu hnu
  exact continuous_const.mul
    ((source_actual_fourfactor_continuous small long R a b
       alpha bs bp d chi sigma0 sigma1 ha hp hr).comp
       (continuous_id.add continuous_const))
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualHighFourFactorIntegral -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin
open Green64Analytic.CorrelationSquare
open Green64Analytic.LongPrime

/-! Apply already verified physical high-frequency U1 directly to the
canonical exceptional units of the literal P_s, with no hJ/hWitness
hypothesis and no assumed exceptional-set energy. -/

theorem eventually_source_actual_high_fourfactor_integral
    (a b As Cs q0 vmin τ η Cχ C0 : ℝ) (tmax ea ec D : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) :
    ∃ K B₀ Ku X₀ : ℝ,
      1 ≤ K ∧ 0 < B₀ ∧ 0 < Ku ∧ 3 ≤ X₀ ∧
      ∀ᶠ L : ℝ in Filter.atTop,
      ∀ x : ℝ, X₀ ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P Y : ℕ), 1 ≤ P → 1 ≤ Y →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      ∀ (bs : ℕ → ℂ), (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
      ∀ (T : ℝ), T+2 ≤ (Y:ℝ) →
      ∀ C : ℝ, 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ) (M R : Finset ℕ) (M0 R0 : ℕ)
        (alpha chiM : ℕ → ℂ) (sigma0 A : ℝ),
      0 < M0 → 0 < R0 → 0 ≤ A →
      ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →
      (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
      M ⊆ Finset.Icc M0 (2*M0) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ m ∈ M, ‖alpha m‖ ≤ A) →
      (∀ m ∈ M, ‖chiM m‖ ≤ 1) →
      A ≤ L^ea →
      ∀ (N : ℝ), x^τ/2 ≤ N → N ≤ x^η →
      ∀ (qL : ℕ), 1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (chiL : DirichletCharacter ℂ qL),
      ∀ (I : Set ℝ), Set.OrdConnected I →
        I ⊆ Set.Icc N (2*N) →
      ∀ sigmaL : ℝ,
      (Y:ℝ)+|sigmaL| ≤ x^2 →
      (∫ t in sourceActualLargeHighTimes s bs T (L^(-As))
          (L^B₀+|sigmaL|),
          ‖sourceShortPrimeAt s bs t *
            (sourceCorrelationLongPrime qL chiL N I (t+sigmaL) *
              sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
                ts tb coef k G Parity c den d0 q chiR sigmaR
                M R alpha chiM sigma0 t)‖^2) ≤
          (2*Cs)^2 * (1/L^D) := by
  obtain ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,hHigh⟩ :=
    eventually_source_physical_U1_growing_group_log_saving
      a b As Cs q0 vmin τ η Cχ C0 tmax ea ec D
      ha hab hb hAs hCs hq0 hq1 hv hτ hτη hη hCχ hC0
  refine ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,?_⟩
  filter_upwards [hHigh] with L hL
  intro x hx hLog hL3 P Y hP hY hPmin hPmax hYmin hYmax
  intro ι β _ _ _ _ hSmall hBig s hp hs bs hbs T hT
  intro C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi hAmax
  intro N hNl hNu qL hqL hqLC chiL I hI hISub sigmaL hShift
  let J := sourceActualHighUnits s bs T (L^(-As)) (L^B₀+|sigmaL|)
  let w := sourceActualExceptionalWitness s bs T (L^(-As))
  have hJ : ∀ j ∈ J, |(j:ℝ)|+1 ≤ (Y:ℝ) := by
    intro j hj
    exact sourceActualExceptionalUnits_in_Y s bs T (L^(-As))
      (Y:ℝ) hT j (sourceActualHighUnits_subset s bs T
        (L^(-As)) (L^B₀+|sigmaL|) hj)
  have hw : ∀ j ∈ J, w j ∈ Set.Icc (j:ℝ) ((j:ℝ)+1) := by
    intro j hj
    exact (sourceActualExceptionalWitness_spec s bs T (L^(-As)) j
      (sourceActualHighUnits_subset s bs T
        (L^(-As)) (L^B₀+|sigmaL|) hj)).1
  have hLg : ∀ j ∈ J, L^(-As) ≤
      ‖∑ p : {p : ℕ // p ∈ s},
        (bs p.val * ((p.val:ℂ)⁻¹)) * sourcePhase p.val (w j)‖ := by
    intro j hj
    have hLarge := (sourceActualExceptionalWitness_spec s bs T
      (L^(-As)) j
      (sourceActualHighUnits_subset s bs T
        (L^(-As)) (L^B₀+|sigmaL|) hj)).2.2
    exact le_of_lt (by simpa only [sourceShortPrimeAt,w] using hLarge)
  have hFreq : ∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
      L^B₀+|sigmaL| ≤ |t| := by
    intro j hj t ht
    exact sourceActualHighUnits_frequency s bs T (L^(-As))
      (L^B₀+|sigmaL|) j hj t ht
  have hUpper : ∀ j ∈ J, ∀ t ∈ Set.Icc (j:ℝ) ((j:ℝ)+1),
      |t+sigmaL| ≤ x^2 := by
    intro j hj t ht
    exact sourceActualHighUnits_upper_shift s bs T (L^(-As))
      (L^B₀+|sigmaL|) (Y:ℝ) x sigmaL hT hShift j hj t ht
  have hResult := hL x hx hLog hL3 P Y hP hY hPmin hPmax
    hYmin hYmax hSmall hBig J w s hJ hw hp hs bs hbs hLg
    C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR M R M0 R0
    alpha chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hChi hAmax N hNl hNu qL hqL hqLC chiL I
    hI hISub sigmaL hFreq hUpper
  let F : ℝ → ℂ := fun t =>
    sourceCorrelationLongPrime qL chiL N I (t+sigmaL) *
      sourcePhysicalResidualAt S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c den d0 q chiR sigmaR
        M R alpha chiM sigma0 t
  have hF : Continuous F :=
    (source_actual_long_prime_continuous qL chiL N I sigmaL).mul
      (sourcePhysicalResidualAt_continuous S Ts Tb q0 Vs
        Vsmall Vbig ts tb coef k G Parity c den d0 q chiR
        sigmaR M R alpha chiM sigma0)
  have hCover := source_actual_large_high_energy_cover
    s bs T (L^(-As)) (L^B₀+|sigmaL|) F hF
  have hDirect : (∫ t in sourceActualLargeHighTimes s bs T
      (L^(-As)) (L^B₀+|sigmaL|), ‖F t‖^2) ≤ 1/L^D := by
    simpa only [J,F] using hCover.trans hResult
  have hPrimeBound := source_actual_large_high_short_prime_energy
    s bs P Cs T (L^(-As)) (L^B₀+|sigmaL|)
    F hP hCs hs hbs hF
  change (∫ t in sourceActualLargeHighTimes s bs T
    (L^(-As)) (L^B₀+|sigmaL|),
    ‖sourceShortPrimeAt s bs t * F t‖^2) ≤
      (2*Cs)^2 * (1/L^D)
  exact hPrimeBound.trans
    (mul_le_mul_of_nonneg_left hDirect (sq_nonneg (2*Cs)))
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualHighLiteralIntegral -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin
open Green64Analytic.LongPrime

/-! Apply already verified physical high-frequency U1 directly to the
canonical exceptional units of the literal P_s, with no hJ/hWitness
hypothesis and no assumed exceptional-set energy. -/

theorem eventually_source_actual_high_literal_fourfactor_integral
    (a b As Cs q0 vmin τ η Cχ C0 : ℝ) (tmax ea ec D : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) :
    ∃ K B₀ Ku X₀ : ℝ,
      1 ≤ K ∧ 0 < B₀ ∧ 0 < Ku ∧ 3 ≤ X₀ ∧
      ∀ᶠ L : ℝ in Filter.atTop,
      ∀ x : ℝ, X₀ ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P Y : ℕ), 1 ≤ P → 1 ≤ Y →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      ∀ (bs : ℕ → ℂ), (∀ p ∈ s, ‖bs p‖ ≤ Cs) →
      ∀ (T : ℝ), T+2 ≤ (Y:ℝ) →
      ∀ C : ℝ, 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ) (R : Finset ℕ) (lo hi M0 R0 : ℕ)
        (alpha : ℕ → ℂ) (qM : ℕ)
        (chiM : DirichletCharacter ℂ qM) (sigma0 A : ℝ),
      0 < M0 → 0 < R0 → 0 ≤ A →
      ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →
      (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
      Finset.Icc lo hi ⊆ Finset.Icc M0 (2*M0) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ A) →
      A ≤ L^ea →
      ∀ (N : ℝ), x^τ/2 ≤ N → N ≤ x^η →
      ∀ (qL : ℕ), 1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (chiL : DirichletCharacter ℂ qL),
      ∀ (I : Set ℝ), Set.OrdConnected I →
        I ⊆ Set.Icc N (2*N) →
      ∀ sigmaL : ℝ,
      (Y:ℝ)+|sigmaL| ≤ x^2 →
      (∫ t in sourceActualLargeHighTimes s bs T (L^(-As))
          (L^B₀+|sigmaL|),
          ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
            R lo hi alpha bs (fun p => chiL p)
            (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
              ts tb coef k G Parity c den d0 q chiR sigmaR)
            chiM sigma0 sigmaL t‖^2) ≤
          (2*Cs)^2 * (1/L^D) := by
  obtain ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,hHigh⟩ :=
    eventually_source_actual_high_fourfactor_integral
      a b As Cs q0 vmin τ η Cχ C0 tmax ea ec D
      ha hab hb hAs hCs hq0 hq1 hv hτ hτη hη hCχ hC0
  refine ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,?_⟩
  filter_upwards [hHigh] with L hL
  intro x hx hLog hL3 P Y hP hY hPmin hPmax hYmin hYmax
  intro ι β _ _ _ _ hSmall hBig s hp hs bs hbs T hT
  intro C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc den d0 q chiR sigmaR R lo hi M0 R0
    alpha qM chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hAmax
  intro N hNl hNu qL hqL hqLC chiL I hI hISub sigmaL hShift
  have hCharacter : ∀ m ∈ Finset.Icc lo hi, ‖chiM m‖ ≤ 1 := by
    intro m hm
    exact DirichletCharacter.norm_le_one chiM (m : ZMod qM)
  have hResult := hL x hx hLog hL3 P Y hP hY hPmin hPmax
    hYmin hYmax hSmall hBig s hp hs bs hbs T hT
    C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR
    (Finset.Icc lo hi) R M0 R0 alpha (fun m => chiM m)
    sigma0 A hM0 hR0 hA hUY hUlower hM hR hAlpha
    hCharacter hAmax
    N hNl hNu qL hqL hqLC chiL I hI hISub sigmaL hShift
  simpa only [source_actual_fourfactor_physical_exact] using hResult
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualHighLiteralLogSaving -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Absorb the literal short-prime coefficient norm (2Cs)^2 into
an explicit source logarithmic budget. This is the same four-factor
high-frequency integral, not a generic high-energy assumption. -/

theorem eventually_source_actual_high_literal_log_saving
    (a b As Cs q0 vmin τ η Cχ C0 : ℝ) (tmax ea ec E D : ℕ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hAs : 0 ≤ As) (hCs : 0 ≤ Cs)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) :
    ∃ K B₀ Ku X₀ : ℝ,
      1 ≤ K ∧ 0 < B₀ ∧ 0 < Ku ∧ 3 ≤ X₀ ∧
      ∀ᶠ L : ℝ in Filter.atTop,
      ∀ x : ℝ, X₀ ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P Y : ℕ), 1 ≤ P → 1 ≤ Y →
      Real.exp (L^a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
          [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (s : Finset ℕ), (∀ p ∈ s, Nat.Prime p) →
      s ⊆ Finset.Icc P (2*P) →
      ∀ (bs : ℕ → ℂ), (∀ p ∈ s, ‖bs p‖ ≤ Cs) → Cs ≤ L^E →
      ∀ (T : ℝ), T+2 ≤ (Y:ℝ) →
      ∀ C : ℝ, 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ g : ι, ts g ≤ tmax) →
      (∀ g : β, tb g ≤ tmax) →
      (∀ g : ι, vmin ≤ Vsmall g) →
      (∀ g : β, vmin ≤ Vbig g) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (den d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ) (R : Finset ℕ) (lo hi M0 R0 : ℕ)
        (alpha : ℕ → ℂ) (qM : ℕ)
        (chiM : DirichletCharacter ℂ qM) (sigma0 A : ℝ),
      0 < M0 → 0 < R0 → 0 ≤ A →
      ((M0*R0:ℕ):ℝ) ≤ (Y:ℝ) →
      (Y:ℝ)^(3/5:ℝ) ≤ ((M0*R0:ℕ):ℝ) →
      Finset.Icc lo hi ⊆ Finset.Icc M0 (2*M0) →
      R ⊆ Finset.Icc R0 (2*R0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ A) →
      A ≤ L^ea →
      ∀ (N : ℝ), x^τ/2 ≤ N → N ≤ x^η →
      ∀ (qL : ℕ), 1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (chiL : DirichletCharacter ℂ qL),
      ∀ (I : Set ℝ), Set.OrdConnected I →
        I ⊆ Set.Icc N (2*N) →
      ∀ sigmaL : ℝ,
      (Y:ℝ)+|sigmaL| ≤ x^2 →
      (∫ t in sourceActualLargeHighTimes s bs T (L^(-As))
          (L^B₀+|sigmaL|),
          ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
            R lo hi alpha bs (fun p => chiL p)
            (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
              ts tb coef k G Parity c den d0 q chiR sigmaR)
            chiM sigma0 sigmaL t‖^2) ≤
          (L^D)⁻¹ := by
  obtain ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,hHigh⟩ :=
    eventually_source_actual_high_literal_fourfactor_integral
      a b As Cs q0 vmin τ η Cχ C0 tmax ea ec (D+2*E+5)
      ha hab hb hAs hCs hq0 hq1 hv hτ hτη hη hCχ hC0
  refine ⟨K,B₀,Ku,X₀,hK,hB₀,hKu,hX₀,?_⟩
  filter_upwards [hHigh] with L hL
  intro x hx hLog hL3 P Y hP hY hPmin hPmax hYmin hYmax
  intro ι β _ _ _ _ hSmall hBig s hp hs bs hbs hCsBudget T hT
  intro C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc den d0 q chiR sigmaR R lo hi M0 R0
    alpha qM chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hAmax
  intro N hNl hNu qL hqL hqLC chiL I hI hISub sigmaL hShift
  have hEnergy := hL x hx hLog hL3 P Y hP hY hPmin hPmax
    hYmin hYmax hSmall hBig s hp hs bs hbs T hT
    C hC hCmax S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc den d0 q chiR sigmaR R lo hi M0 R0
    alpha qM chiM sigma0 A hM0 hR0 hA hUY hUlower hM hR
    hAlpha hAmax
    N hNl hNu qL hqL hqLC chiL I hI hISub sigmaL hShift
  have hNumeric :=
    source_actual_high_numeric_log_crush L Cs E D hL3 hCs hCsBudget
  exact hEnergy.trans (by simpa only [one_div] using hNumeric)
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLiteralThreewayAssembly -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! The ORIGINAL source rational-character fourfactor, not a generic
placeholder function, splits across the full Mellin time window.
The partition is formed directly from the literal short prime P_s;
its high/low unit cells are disjoint and need no J hypotheses. -/

theorem source_actual_literal_fourfactor_full_threeway_exact
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 T delta cutoff : ℝ)
    (ha : 1 ≤ a)
    (hLong : ∀ p ∈ long, 0 < p)
    (hR : ∀ r ∈ R, 0 < r) :
    (∫ t in Set.Icc (-T) T,
      ‖sourceFourFactorAt small long R a b
        alpha bs bp d chi sigma0 sigma1 t‖^2) =
    (∫ t in sourceActualSmallTimes small bs T delta,
      ‖sourceFourFactorAt small long R a b
        alpha bs bp d chi sigma0 sigma1 t‖^2) +
    (∫ t in sourceActualLargeHighTimes small bs T delta cutoff,
      ‖sourceFourFactorAt small long R a b
        alpha bs bp d chi sigma0 sigma1 t‖^2) +
    (∫ t in sourceActualLargeLowTimes small bs T delta cutoff,
      ‖sourceFourFactorAt small long R a b
        alpha bs bp d chi sigma0 sigma1 t‖^2) := by
  exact source_actual_full_mellin_three_way_integral
    small bs T delta cutoff
    (fun t => sourceFourFactorAt small long R a b
      alpha bs bp d chi sigma0 sigma1 t)
    (source_actual_fourfactor_continuous small long R a b
      alpha bs bp d chi sigma0 sigma1 ha hLong hR)
/-- Numeric assembly interface: its three inputs are estimates for
the SAME explicitly defined original four-factor integrand, and
these inputs have independent kernel-checked source predecessors.
No assumed properties of an abstract exceptional set are present. -/
theorem source_actual_literal_fourfactor_threeway_bound
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 T delta cutoff : ℝ)
    (ha : 1 ≤ a)
    (hLong : ∀ p ∈ long, 0 < p)
    (hR : ∀ r ∈ R, 0 < r)
    (Esmall Ehigh Elow : ℝ)
    (hSmall :
      (∫ t in sourceActualSmallTimes small bs T delta,
        ‖sourceFourFactorAt small long R a b
          alpha bs bp d chi sigma0 sigma1 t‖^2) ≤ Esmall)
    (hHigh :
      (∫ t in sourceActualLargeHighTimes small bs T delta cutoff,
        ‖sourceFourFactorAt small long R a b
          alpha bs bp d chi sigma0 sigma1 t‖^2) ≤ Ehigh)
    (hLow :
      (∫ t in sourceActualLargeLowTimes small bs T delta cutoff,
        ‖sourceFourFactorAt small long R a b
          alpha bs bp d chi sigma0 sigma1 t‖^2) ≤ Elow) :
    (∫ t in Set.Icc (-T) T,
      ‖sourceFourFactorAt small long R a b
        alpha bs bp d chi sigma0 sigma1 t‖^2) ≤
      Esmall + Ehigh + Elow := by
  rw [source_actual_literal_fourfactor_full_threeway_exact
    small long R a b alpha bs bp d chi sigma0 sigma1 T delta
    cutoff ha hLong hR]
  linarith
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualTripleDyadicBounds -/

section

namespace Green64Analytic.CorrelationMellin

/-! Source dyadic constraints proven directly on the genuine threefold
Cartesian support, not assumed for a generic divisor convolution. -/

theorem source_three_actual_support_dyadic_bounds
    (M P R : Finset ℕ) (M0 P0 R0 : ℕ)
    (hM0 : 1 ≤ M0) (hP0 : 1 ≤ P0) (hR0 : 1 ≤ R0)
    (hM : M ⊆ Finset.Icc M0 (2*M0))
    (hP : P ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0)) :
    sourceThreeCollapsedSupport (sourceThreeActualTuples M P R) ⊆
      Finset.Icc 1 ((2*M0)*(2*P0)*(2*R0)) ∧
    (∀ n ∈ sourceThreeCollapsedSupport (sourceThreeActualTuples M P R),
      ((M0*P0*R0:ℕ):ℝ) ≤ (n:ℝ)) := by
  classical
  have hBase : 0 < M0*P0*R0 := by
    apply Nat.mul_pos
    · apply Nat.mul_pos <;> omega
    · omega
  have hBounds (n : ℕ)
      (hn : n ∈ sourceThreeCollapsedSupport (sourceThreeActualTuples M P R)) :
      M0*P0*R0 ≤ n ∧ n ≤ (2*M0)*(2*P0)*(2*R0) := by
    rcases Finset.mem_image.mp hn with ⟨v,hv,rfl⟩
    rcases Finset.mem_image.mp hv with ⟨⟨⟨m,p⟩,r⟩,hz,rfl⟩
    obtain ⟨hmp,hr⟩ := Finset.mem_product.mp hz
    obtain ⟨hm,hp⟩ := Finset.mem_product.mp hmp
    have hM' := Finset.mem_Icc.mp (hM hm)
    have hP' := Finset.mem_Icc.mp (hP hp)
    have hR' := Finset.mem_Icc.mp (hR hr)
    rw [sourceThreeTuple_product]
    exact ⟨Nat.mul_le_mul (Nat.mul_le_mul hM'.1 hP'.1) hR'.1,
      Nat.mul_le_mul (Nat.mul_le_mul hM'.2 hP'.2) hR'.2⟩
  constructor
  · intro n hn
    obtain ⟨hl,hu⟩ := hBounds n hn
    apply Finset.mem_Icc.mpr
    constructor
    · have hp : 0 < n := lt_of_lt_of_le hBase hl
      omega
    · exact hu
  · intro n hn
    exact_mod_cast (hBounds n hn).1
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualSourceCoefficientBudget -/

section

namespace Green64Analytic.CorrelationMellin

/-! Coefficient bounds for the literal source character and both
frequency twists. No unrelated bounded convolution is substituted. -/

theorem source_three_actual_coeff_bound
    (M P R : Finset ℕ) (am ap ar : ℕ → ℂ)
    (Am Ap Ar : ℝ)
    (hAm : ∀ m ∈ M, ‖am m‖ ≤ Am)
    (hAp : ∀ p ∈ P, ‖ap p‖ ≤ Ap)
    (hAr : ∀ r ∈ R, ‖ar r‖ ≤ Ar) :
    ∀ v ∈ sourceThreeActualTuples M P R, ∀ i : Fin 3,
      ‖sourceThreeProductCoefficients am ap ar i (v i)‖ ≤
        (if i = 0 then Am else if i = 1 then Ap else Ar) := by
  classical
  intro v hv i
  rcases Finset.mem_image.mp hv with ⟨⟨⟨m,p⟩,r⟩,hz,rfl⟩
  obtain ⟨hmp,hr⟩ := Finset.mem_product.mp hz
  obtain ⟨hm,hp⟩ := Finset.mem_product.mp hmp
  fin_cases i
  · simpa [sourceThreeProductCoefficients,sourceThreeTuple] using hAm m hm
  · simpa [sourceThreeProductCoefficients,sourceThreeTuple] using hAp p hp
  · simpa [sourceThreeProductCoefficients,sourceThreeTuple] using hAr r hr

theorem source_actual_prime_residual_coeff_bound
    (M P R : Finset ℕ) (alpha bp d : ℕ → ℂ)
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 : ℝ) (Am Ap Ar : ℝ)
    (hAm : ∀ m ∈ M, ‖alpha m‖ ≤ Am)
    (hAp : ∀ p ∈ P, ‖bp p‖ ≤ Ap)
    (hAr : ∀ r ∈ R, ‖d r‖ ≤ Ar) :
    ∀ v ∈ sourceThreeActualTuples M P R, ∀ i : Fin 3,
      ‖sourceActualPrimeResidualTriple alpha bp d chi sigma0 sigma1 i (v i)‖ ≤
        (if i = 0 then Am else if i = 1 then Ap else Ar) := by
  have hM' (m : ℕ) (hm : m ∈ M) :
      ‖alpha m * chi m * sourcePhase m sigma0‖ ≤ Am := by
    have hChar : ‖chi m‖ ≤ 1 :=
      DirichletCharacter.norm_le_one chi (m : ZMod q)
    have h1 : ‖alpha m * chi m * sourcePhase m sigma0‖ =
        ‖alpha m‖ * ‖chi m‖ := by
      simp [norm_mul, sourcePhase_norm]
    rw [h1]
    calc
      _ ≤ ‖alpha m‖ * 1 :=
        mul_le_mul_of_nonneg_left hChar (norm_nonneg _)
      _ ≤ Am := by simpa using hAm m hm
  have hP' (p : ℕ) (hp : p ∈ P) :
      ‖bp p * sourcePhase p sigma1‖ ≤ Ap := by
    simpa [norm_mul, sourcePhase_norm] using hAp p hp
  exact source_three_actual_coeff_bound M P R
    (fun m => alpha m * chi m * sourcePhase m sigma0)
    (fun p => bp p * sourcePhase p sigma1) d Am Ap Ar
    hM' hP' hAr
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLiteralNonexceptional -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Nonexceptional full Mellin energy for the ORIGINAL rational-character
four-factor polynomial. The remaining inequalities are only the literal
dyadic support and coefficient budgets, not an assumed mean-square bound. -/

theorem source_actual_literal_nonexceptional_full_mean_square
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 T δ : ℝ)
    (M0 P0 R0 : ℕ) (Am Ap Ar : ℝ)
    (hM0 : 1 ≤ M0) (hP0 : 1 ≤ P0) (hR0 : 1 ≤ R0)
    (ha : 1 ≤ a)
    (hM : Finset.Icc a b ⊆ Finset.Icc M0 (2*M0))
    (hP : long ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (hAm : 0 ≤ Am) (hAp : 0 ≤ Ap) (hAr : 0 ≤ Ar)
    (hAlpha : ∀ m ∈ Finset.Icc a b, ‖alpha m‖ ≤ Am)
    (hBp : ∀ p ∈ long, ‖bp p‖ ≤ Ap)
    (hD : ∀ r ∈ R, ‖d r‖ ≤ Ar)
    (hT : 0 ≤ T) (hδ : 0 ≤ δ) :
    (∫ t in sourceActualSmallTimes small bs T δ,
      ‖sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 t‖^2) ≤
      δ^2 * ((2*T+16*((2*M0)*(2*P0)*(2*R0):ℕ) *
        (1+Real.log ((2*M0)*(2*P0)*(2*R0):ℕ))) *
      ((Am*Ap*Ar)^2/(M0*P0*R0:ℕ) *
        (1+Real.log ((2*M0)*(2*P0)*(2*R0):ℕ))^(2^(2*2)))) := by
  let M : Finset ℕ := Finset.Icc a b
  let N : ℕ := (2*M0)*(2*P0)*(2*R0)
  let U : ℝ := (M0*P0*R0:ℕ)
  let A : Fin 3 → ℝ :=
    fun i => if i = 0 then Am else if i = 1 then Ap else Ar
  have hN : 1 ≤ N := by
    dsimp [N]
    have hm : 0 < M0 := by omega
    have hp : 0 < P0 := by omega
    have hr : 0 < R0 := by omega
    have hp1 : 0 < (2*M0)*(2*P0)*(2*R0) := by positivity
    omega
  have hU : 0 < U := by
    dsimp [U]
    have hm : 0 < M0 := by omega
    have hp : 0 < P0 := by omega
    have hr : 0 < R0 := by omega
    positivity
  obtain ⟨hSupport,hLower⟩ :=
    source_three_actual_support_dyadic_bounds M long R M0 P0 R0
      hM0 hP0 hR0 hM hP hR
  have hAm' : ∀ i, 0 ≤ A i := by
    intro i
    fin_cases i <;> simp [A,hAm,hAp,hAr]
  have hCoeff :
      ∀ v ∈ sourceThreeActualTuples M long R, ∀ i,
        ‖sourceActualPrimeResidualTriple alpha bp d chi sigma0 sigma1 i (v i)‖
          ≤ A i := by
    exact source_actual_prime_residual_coeff_bound M long R
      alpha bp d chi sigma0 sigma1 Am Ap Ar
      hAlpha hBp hD
  have hBound := source_actual_nonexceptional_full_mean_square
    small bs T δ
    (sourceThreeActualTuples M long R)
    (sourceActualPrimeResidualTriple alpha bp d chi sigma0 sigma1)
    A U N
    hT hδ hN hAm' hU hSupport hLower hCoeff
  have hMpos : ∀ m ∈ M, 0 < m := by
    intro m hm
    have hma := (Finset.mem_Icc.mp hm).1
    omega
  have hPpos : ∀ p ∈ long, 0 < p := by
    intro p hp
    have hpp := (Finset.mem_Icc.mp (hP hp)).1
    omega
  have hRpos : ∀ r ∈ R, 0 < r := by
    intro r hr
    have hrr := (Finset.mem_Icc.mp (hR hr)).1
    omega
  have hEq (t : ℝ) :
      sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 t =
      sourceShortPrimeAt small bs t *
        sourceThreeCollapsedAt
          (sourceThreeActualTuples M long R)
          (sourceActualPrimeResidualTriple alpha bp d chi sigma0 sigma1) t :=
    source_actual_fourfactor_threefactor_eq small long R a b
      alpha bs bp d chi sigma0 sigma1 t ha hPpos hRpos
  have hProd : (∏ i : Fin 3, A i) = Am*Ap*Ar := by
    simp [Fin.prod_univ_three,A]
  simp_rw [←hEq] at hBound
  rw [hProd] at hBound
  simpa only [M,N,U] using hBound
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualLiteralNonexceptionalSaving -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Full nonexceptional logarithmic saving for the actual source
rational-character four-factor polynomial. The three explicit scale
hypotheses are consequences to be discharged from the original
comparison boxes: T≤M0*P0*R0, 8*M0*P0*R0≤exp(2L), and the
polylogarithmic coefficient budget. -/

theorem source_actual_literal_nonexceptional_log_saving
    (small long R : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q)
    (sigma0 sigma1 T : ℝ)
    (M0 P0 R0 : ℕ) (Am Ap Ar L : ℝ) (E D : ℕ)
    (hM0 : 1 ≤ M0) (hP0 : 1 ≤ P0) (hR0 : 1 ≤ R0)
    (ha : 1 ≤ a)
    (hM : Finset.Icc a b ⊆ Finset.Icc M0 (2*M0))
    (hP : long ⊆ Finset.Icc P0 (2*P0))
    (hR : R ⊆ Finset.Icc R0 (2*R0))
    (hAm : 0 ≤ Am) (hAp : 0 ≤ Ap) (hAr : 0 ≤ Ar)
    (hAlpha : ∀ m ∈ Finset.Icc a b, ‖alpha m‖ ≤ Am)
    (hBp : ∀ p ∈ long, ‖bp p‖ ≤ Ap)
    (hD : ∀ r ∈ R, ‖d r‖ ≤ Ar)
    (hT : 0 ≤ T) (hL : 3 ≤ L)
    (hTU : T ≤ (M0*P0*R0:ℕ))
    (hNexp : (((2*M0)*(2*P0)*(2*R0):ℕ):ℝ) ≤ Real.exp (2*L))
    (hBudget : Am*Ap*Ar ≤ L^E) :
    (∫ t in sourceActualSmallTimes small bs T
      ((L^(E+D+40))⁻¹),
      ‖sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 t‖^2) ≤ (L^D)⁻¹ := by
  let N : ℕ := (2*M0)*(2*P0)*(2*R0)
  let U : ℝ := (M0*P0*R0:ℕ)
  let W : ℝ := 1+Real.log (N:ℝ)
  let B : ℝ := Am*Ap*Ar
  let δ : ℝ := (L^(E+D+40))⁻¹
  have hN : 1 ≤ N := by
    dsimp [N]
    have hh : 0 < (2*M0)*(2*P0)*(2*R0) := by
      have hm : 0 < M0 := by omega
      have hp : 0 < P0 := by omega
      have hr : 0 < R0 := by omega
      positivity
    omega
  have hUpos : 0 < U := by
    dsimp [U]
    have hm : 0 < M0 := by omega
    have hp : 0 < P0 := by omega
    have hr : 0 < R0 := by omega
    positivity
  have hWone : 1 ≤ W := by
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hlog := Real.log_nonneg hn
    dsimp [W]
    linarith
  have hWmax : W ≤ L^2 :=
    source_actual_dyadic_log_budget L N hL hN hNexp
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hNrel : (N:ℝ) = 8*U := by
    dsimp [N,U]
    push_cast
    ring
  have hRaw := source_actual_literal_nonexceptional_full_mean_square
    small long R a b alpha bs bp d chi sigma0 sigma1
    T δ M0 P0 R0 Am Ap Ar
    hM0 hP0 hR0 ha hM hP hR hAm hAp hAr
    hAlpha hBp hD hT hδ
  have hRaw' :
      (∫ t in sourceActualSmallTimes small bs T δ,
        ‖sourceFourFactorAt small long R a b alpha bs bp d chi
          sigma0 sigma1 t‖^2) ≤
       δ^2*((2*T+16*(N:ℝ)*W)*(B^2/U*W^16)) := by
    simpa only [N,U,W,B, Nat.reduceMul, Nat.reducePow] using hRaw
  have hNumeric := source_nonexceptional_polylog_crush
    L T U W B E D hL hUpos (by simpa only [U] using hTU)
    hWone hWmax hB (by simpa only [B] using hBudget)
  change (∫ t in sourceActualSmallTimes small bs T δ,
      ‖sourceFourFactorAt small long R a b alpha bs bp d chi
        sigma0 sigma1 t‖^2) ≤ (L^D)⁻¹
  calc
    _ ≤ δ^2*((2*T+16*(N:ℝ)*W)*(B^2/U*W^16)) := hRaw'
    _ = δ^2*((2*T+128*U*W)*(B^2/U*W^16)) := by
      rw [hNrel]
      ring
    _ ≤ (L^D)⁻¹ := hNumeric
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualNonexceptionalParameterized -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationMellin

/-! Source-specialized NONEXCEPTIONAL energy.
All coefficient budgets, actual dyad cut, genuine joint character,
long-prime natural support and the scale inequalities are derived
from predecessor theorems. There is no independent residual bound,
no invented alpha coefficient and no hTU/hNexp hypothesis. -/
theorem source_actual_physical_nonexceptional_from_comparison_scales
    (q0 vmin C0 : ℝ) (tmax ea ec D : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin)
    (hC0 : 0 ≤ C0) :
    ∃ K : ℝ, ∃ g : ℕ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      ∀ (L Y Hprime Psmall Ccomp Carc N : ℝ)
        (M0 R0 : ℕ) (I : Set ℝ),
      max 3 K ≤ L → 0 ≤ Y → 1 ≤ Psmall →
      0 < Hprime → 1 ≤ N → I ⊆ Set.Icc N (2*N) →
      Y ≤ Ccomp*Psmall*((M0*⌈N⌉₊*R0:ℕ):ℝ) →
      ((M0*⌈N⌉₊*R0:ℕ):ℝ)*Psmall ≤ Ccomp*Y →
      2*L*Ccomp*Psmall*L^Carc ≤ Hprime →
      Y ≤ Real.exp (3*L/2) →
      8*Ccomp ≤ Real.exp (L/2) →
      1 ≤ M0 → 1 ≤ R0 →
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      ∀ (small R : Finset ℕ) (bs : ℕ → ℂ),
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      ∀ (sigma0 sigma1 : ℝ),
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
        (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      (∫ t in sourceActualSmallTimes small bs
          (2*L*Y/(Hprime/L^Carc))
          ((L^(ea+ec+g+D+40))⁻¹),
        ‖sourceFourFactorAt small (sourceLongPrimeSourceSupport N I)
          R a b (sourceAlphaDyadicCut alpha lo hi) bs
          (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 t‖^2) ≤ (L^D)⁻¹ := by
  obtain ⟨K,g,hK,hResidual⟩ :=
    source_actual_physical_residual_polylog_coeff_budget
      q0 vmin C0 tmax ec hq0 hq1 hv hC0
  refine ⟨K,g,hK,?_⟩
  intro ι β _ _ _ _ L Y Hprime Psmall Ccomp Carc N M0 R0 I
    hL hY hPsmall hHprime hN hI hYcompare hUcompare
    hFreeScale hYscale hCmargin hM0 hR0 hGroupSmall hGroupBig
  intro lo hi a b alpha ha hMSupport hAlpha
    small R bs hR qL chiL qBase den d chi0 xi sigma0 sigma1
    C hC hCBudget S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc denR d0 q chiR sigmaR
  let T : ℝ := 2*L*Y/(Hprime/L^Carc)
  let P0 : ℕ := ⌈N⌉₊
  have hL3 : 3 ≤ L := (le_max_left (3:ℝ) K).trans hL
  have hLpos : 0 < L := by linarith
  have hT : 0 ≤ T := by
    dsimp [T]
    have hH : 0 < Hprime/L^Carc := by
      exact div_pos hHprime (Real.rpow_pos_of_pos hLpos Carc)
    positivity
  have hP0 : 1 ≤ P0 :=
    source_actual_long_prime_nat_dyadic_start N hN
  have hLong :
      sourceLongPrimeSourceSupport N I ⊆ Finset.Icc P0 (2*P0) :=
    source_actual_long_prime_nat_dyadic_support N I hI
  have hScale := source_actual_comparison_scale_to_polynomial_budgets
      L Y Hprime Psmall Ccomp Carc M0 P0 R0
      hL3 hY hPsmall hHprime hYcompare hUcompare
      hFreeScale hYscale hCmargin
  have hAm : 0 ≤ L^ea := pow_nonneg hLpos.le _
  have hAr : 0 ≤ L^(ec+g) := pow_nonneg hLpos.le _
  have hAlphaCut : ∀ m ∈ Finset.Icc a b,
      ‖sourceAlphaDyadicCut alpha lo hi m‖ ≤ L^ea :=
    source_actual_alpha_dyadic_cut_coeff_budget
      alpha lo hi a b (L^ea) hAm hAlpha
  have hBp : ∀ p ∈ sourceLongPrimeSourceSupport N I,
      ‖chiL p‖ ≤ (1:ℝ) := by
    intro p hp
    exact DirichletCharacter.norm_le_one chiL (p:ZMod qL)
  have hD : ∀ r ∈ R,
      ‖sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c denR d0 q chiR sigmaR r‖ ≤
      L^(ec+g) := by
    intro r hr
    exact hResidual L hL hGroupSmall hGroupBig C hC hCBudget
      S Ts Tb Vs Vsmall Vbig ts tb coef k
      hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc denR d0 q chiR sigmaR r
  have hBudget :
      L^ea * (1:ℝ) * L^(ec+g) ≤ L^(ea+ec+g) := by
    convert le_refl (L^(ea+ec+g)) using 1
    simp only [mul_one, pow_add]
    ring
  exact source_actual_literal_nonexceptional_log_saving
    small (sourceLongPrimeSourceSupport N I) R
    a b (sourceAlphaDyadicCut alpha lo hi) bs
    (fun p => chiL p)
    (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c denR d0 q chiR sigmaR)
    (sourceJointCharacter qBase (den/d) chi0 xi)
    sigma0 sigma1 T M0 P0 R0
    (L^ea) 1 (L^(ec+g)) L (ea+ec+g) D
    hM0 hP0 hR0 ha hMSupport hLong hR
    hAm (by norm_num) hAr hAlphaCut hBp hD hT hL3
    hScale.1 hScale.2 hBudget
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualAllThreewayUniformAbove -/

section

open MeasureTheory Filter
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationMellin

/-! A unified ORIGINAL fourfactor full Mellin estimate.
One literal source alpha dyadic cut, long-prime support, all-gcd
joint character, marked physical residual, threshold and cutoff.
Only the original source-box hypotheses and original discrepancy
remain, never arbitrary high/low/exceptional energies. -/
theorem eventually_source_actual_all_threeway_physical_log_saving_above
    (aexp bexp τ η Cχ C0 Ccomp q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1req : ℕ)
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) (hComp : 0 < Ccomp)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ KNon : ℝ, ∃ gNon : ℕ,
    ∃ KHigh B0 Ku X0 : ℝ, ∃ s1 : ℕ,
    ∃ KLow : ℝ, ∃ gLow : ℕ,
      1 ≤ KNon ∧ 1 ≤ KHigh ∧ 0 < B0 ∧
      0 < Ku ∧ 3 ≤ X0 ∧ B0 ≤ (s1:ℝ) ∧ s1req ≤ s1 ∧ 1 ≤ KLow ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P M0 R0 : ℕ) (Y Hprime Carc N : ℝ) (I : Set ℝ),
      1 ≤ P → 1 ≤ M0 → 1 ≤ R0 →
      4 ≤ Y → Real.exp (L/2) ≤ Y →
      Y ≤ Real.exp (3*L/2) →
      0 < Hprime → 1 ≤ N →
      Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      x^τ/2 ≤ N → N ≤ x^η →
      Real.exp (L^aexp) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^bexp) →
      Y ≤ Ccomp*(P:ℝ)*((M0*⌈N⌉₊*R0:ℕ):ℝ) →
      ((M0*⌈N⌉₊*R0:ℕ):ℝ)*(P:ℝ) ≤ Ccomp*Y →
      2*L*Ccomp*(P:ℝ)*L^Carc ≤ Hprime →
      4*L*L^Carc ≤ Hprime →
      Ccomp ≤ (P:ℝ)*(⌈N⌉₊:ℝ) →
      2*Ccomp*(P:ℝ)*(⌈N⌉₊:ℝ) ≤ ((⌈Y⌉₊:ℝ)^(2/5:ℝ)) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a → (b:ℝ) ≤ x^2 →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L
        (((D+2+s0+s1+3+2*cm)+
          5*(ec+(s1+2)+gLow+2)+10:ℕ):ℝ) x alpha →
      ∀ (s R : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, p.Prime) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ 1) →
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      d ∈ den.divisors →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1 →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
          (2*L*Y/(Hprime/L^Carc)),
        ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceAlphaDyadicCut alpha lo hi) bs
          (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 t‖^2) ≤ (L^D)⁻¹ := by
  let Dsmall : ℕ := D+2
  obtain ⟨KNon,gNon,hKNon,hNon⟩ :=
    source_actual_physical_nonexceptional_from_comparison_scales
      q0 vmin C0 tmax ea ec Dsmall hq0 hq1 hv hC0
  let E : ℕ := ea+ec+gNon
  let As : ℝ := ((E+Dsmall+40:ℕ):ℝ)
  obtain ⟨KHigh,B0,Ku,X0,hKHigh,hB0,hKu,hX0,hHighEvent⟩ :=
    eventually_source_actual_high_literal_log_saving
      aexp bexp As 1 q0 vmin τ η Cχ C0
      tmax ea ec 0 Dsmall
      haexp hab hb (by positivity) (by norm_num)
      hq0 hq1 hv hτ hτη hη hCχ hC0
  obtain ⟨s1,hs1max⟩ := exists_nat_gt (max B0 (s1req : ℝ))
  have hs1 : B0 < (s1 : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hs1max
  have hs1reqReal : (s1req : ℝ) < (s1 : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hs1max
  have hs1req : s1req ≤ s1 := by
    exact_mod_cast hs1reqReal.le
  let Dlow : ℕ := Dsmall+s0+s1+3+2*cm
  obtain ⟨KLow,gLow,hKLow,hLowAll⟩ :=
    source_actual_all_gcd_physical_low_log_saving
      q0 vmin C0 tmax ec (s1+2) Dlow hq0 hq1 hv hC0
  refine ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,le_of_lt hs1,hs1req,hKLow,?_⟩
  filter_upwards [hHighEvent,
      eventually_ge_atTop (max 3 KNon),
      eventually_ge_atTop (max 3 KLow),
      eventually_ge_atTop (3:ℝ),
      eventually_source_comparison_exponential_margin Ccomp,
      eventually_source_ceil_Y_shift_below_exp_two_L s1] with
    L hHigh hNonBound hLowBound hL hMargin hYShift
  intro x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmin hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare
    hFree hFreeStrong hProdLower hPrimeScales
  intro ι β _ _ _ _ hGroupSmall hGroupBig
  intro lo hi a b alpha ha hb hM hAlpha hDisc
  intro s R bs hPrime hs hbs hR qL chiL hqL hqLC
  intro qBase den d chi0 xi hBase hDen hd sigma0 sigma1
    hSigma0 hSigma1 C hC hCBudget
  intro S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc denR d0 q chiR sigmaR
  let Pprime : ℕ := ⌈N⌉₊
  let Ynat : ℕ := ⌈Y⌉₊
  let T : ℝ := 2*L*Y/(Hprime/L^Carc)
  let cutoff : ℝ := L^B0+|sigma1|
  let delta : ℝ := ((L^(E+Dsmall+40))⁻¹)
  let dPhys : ℕ → ℂ :=
    sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c denR d0 q chiR sigmaR
  let joint : DirichletCharacter ℂ (qBase*(den/d)) :=
    sourceJointCharacter qBase (den/d) chi0 xi
  let alphaCut : ℕ → ℂ := sourceAlphaDyadicCut alpha lo hi
  have hLpos : 0 < L := by linarith
  have hYn : (Ynat:ℝ) < Y+1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hYnLe : Y ≤ (Ynat:ℝ) := Nat.le_ceil Y
  have hYnDouble : (Ynat:ℝ) ≤ 2*Y := by linarith
  have hYnPos : 0 < (Ynat:ℝ) := by linarith
  have hYnatOne : 1 ≤ Ynat := by
    have hh : (1:ℝ) ≤ Ynat := by linarith
    exact_mod_cast hh
  have hYnatMin : Real.exp (L/2) ≤ (Ynat:ℝ) :=
    hYmin.trans hYnLe
  have hYShiftUpper : (Ynat:ℝ)+|sigma1| ≤ Real.exp (2*L) :=
    hYShift Y sigma1 hY hYmax hSigma1
  have hYnatMax : (Ynat:ℝ) ≤ Real.exp (2*L) := by
    linarith [abs_nonneg sigma1]
  have hXpos : 0 < x := by linarith [hX0]
  have hXexp : x = Real.exp L := by
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hXpos).symm
      _ = Real.exp L := by rw [←hLog]
  have hShift : (Ynat:ℝ)+|sigma1| ≤ x^2 := by
    rw [hXexp]
    have heq : Real.exp (2*L) = (Real.exp L)^2 := by
      rw [show 2*L=L+L by ring, Real.exp_add]
      ring
    simpa [heq] using hYShiftUpper
  have hTplus : T+2 ≤ (Ynat:ℝ) :=
    source_actual_mellin_time_plus_two_below_nat_ceil_Y
      L Y Hprime Carc hLpos hY hHprime hFreeStrong
  have hPprime : 1 ≤ Pprime :=
    source_actual_long_prime_nat_dyadic_start N hN
  have hLong : sourceLongPrimeSourceSupport N I ⊆
      Finset.Icc Pprime (2*Pprime) :=
    source_actual_long_prime_nat_dyadic_support N I hI
  let U : ℝ := ((M0*R0:ℕ):ℝ)
  have hUpos : 0 ≤ U := by dsimp [U]; positivity
  have hProducts :
      ((M0*Pprime*R0:ℕ):ℝ) = (Pprime:ℝ)*U := by
    dsimp [U]; push_cast; ring
  have hYcmp : Y ≤ (Ccomp*(P:ℝ)*(Pprime:ℝ))*U := by
    convert hYcompare using 1
    dsimp [Pprime,U]
    push_cast
    ring
  have hYU1Compare : (Ynat:ℝ) ≤
      ((2*Ccomp)*(P:ℝ)*(Pprime:ℝ))*U := by
    calc
      _ ≤ 2*Y := hYnDouble
      _ ≤ 2*((Ccomp*(P:ℝ)*(Pprime:ℝ))*U) :=
        mul_le_mul_of_nonneg_left hYcmp (by norm_num)
      _ = (2*Ccomp)*(P:ℝ)*(Pprime:ℝ)*U := by ring
  have hUlower : (Ynat:ℝ)^(3/5:ℝ) ≤ U :=
    source_actual_comparison_to_U1_residual_lower
      (Ynat:ℝ) (2*Ccomp) (P:ℝ) (Pprime:ℝ) M0 R0
      hYnPos hYU1Compare (by simpa [Pprime] using hPrimeScales)
  have hUupperCmp : U*((P:ℝ)*(Pprime:ℝ)) ≤ Ccomp*Y := by
    convert hUcompare using 1
    dsimp [U,Pprime]
    push_cast
    ring
  have hUupper : U ≤ (Ynat:ℝ) := by
    have hDiff := mul_nonneg
      (sub_nonneg.mpr (by simpa only [Pprime] using hProdLower)) hUpos
    have hUY : U ≤ Y := by nlinarith [hUupperCmp, hDiff, hComp]
    exact hUY.trans hYnLe
  have hAlphaBound :
      ∀ m ∈ Finset.Icc a b, ‖alphaCut m‖ ≤ L^ea :=
    source_actual_alpha_dyadic_cut_coeff_budget
      alpha lo hi a b (L^ea) (by positivity) hAlpha
  have hCutFacts :=
    source_actual_one_cutoff_shift_budget
      L B0 sigma0 sigma1 s0 s1 hL3 (le_of_lt hs1)
      hSigma0 hSigma1
  have hCut0 : 0 ≤ cutoff+2 := by
    simpa only [cutoff] using hCutFacts.1
  have hCutPower : cutoff+2 ≤ L^(s1+2) := by
    simpa only [cutoff] using hCutFacts.2.1
  let Bdisc : ℕ := Dlow+5*(ec+(s1+2)+gLow+2)+10
  have hDiscPower : cutoff+2+|sigma0| ≤ L^Bdisc := by
    have hExponent : s0+s1+3 ≤ Bdisc := by dsimp [Bdisc,Dlow,Dsmall]; omega
    calc
      _ ≤ L^(s0+s1+3) := by
        simpa only [cutoff] using hCutFacts.2.2
      _ ≤ L^Bdisc := pow_le_pow_right₀ (by linarith) hExponent
  have hCutOffset : cutoff+2 ≤ L^(s1+2) := hCutPower
  have hCsBudget : (1:ℝ) ≤ L^(s1+2) := by
    simpa using (pow_le_pow_right₀ (by linarith : (1:ℝ)≤L)
      (Nat.zero_le (s1+2)) : L^0 ≤ L^(s1+2))
  have hModBudget : 2*(cm:ℝ) ≤ (Bdisc:ℝ) := by
    have hh : 2*cm ≤ Bdisc := by dsimp [Bdisc,Dlow,Dsmall]; omega
    exact_mod_cast hh
  have hAlphaBoundLow :
      ∀ p ∈ sourceLongPrimeSourceSupport N I,
        ‖chiL p‖ ≤ (1:ℝ) := by
    intro p hp
    exact DirichletCharacter.norm_le_one chiL (p:ZMod qL)
  have hNonSmall :=
    hNon L Y Hprime (P:ℝ) Ccomp Carc N M0 R0 I
      hNonBound (by linarith) (by exact_mod_cast hP)
      hHprime hN hI hYcompare hUcompare
      hFree hYmax hMargin hM0 hR0 hGroupSmall hGroupBig
      lo hi a b alpha ha hM hAlpha s R bs hR qL chiL
      qBase den d chi0 xi sigma0 sigma1
      C hC hCBudget S Ts Tb Vs Vsmall Vbig ts tb coef k
      hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc denR d0 q chiR sigmaR
  have hHighEnergy :=
    hHigh x hx hLog hL3 P Ynat hP hYnatOne hPmin hPmax
      hYnatMin hYnatMax
      hGroupSmall hGroupBig s hPrime hs bs hbs
      (by norm_num : (1:ℝ) ≤ L^0)
      T hTplus C hC hCBudget
      S Ts Tb Vs Vsmall Vbig ts tb coef k
      hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc denR d0 q chiR sigmaR
      R a b M0 R0 alphaCut (qBase*(den/d)) joint sigma0
      (L^ea) (by omega) (by omega) (by positivity)
      (by simpa only [U] using hUupper)
      (by simpa only [U] using hUlower)
      hM hR hAlphaBound (le_refl _)
      N hNlow hNhigh qL hqL hqLC chiL I
      hIconn hI sigma1 hShift
  have hLowEnergy :=
    hLowAll L x T delta cutoff
      hLowBound hCut0 hCutOffset hGroupSmall hGroupBig
      alpha (by simpa only [Bdisc,Dlow] using hDisc)
      qBase den lo hi chi0 (cm:ℝ)
      (by simpa only [Real.rpow_natCast] using hBase)
      (by simpa only [Real.rpow_natCast] using hDen)
      (by simpa only [Bdisc] using hModBudget)
      d hd xi a b ha hb sigma0 sigma1
      (by simpa only [Bdisc,Real.rpow_natCast] using hDiscPower)
      P Pprime R0 s (sourceLongPrimeSourceSupport N I) R
      bs (fun p => chiL p) 1 1 C
      hP hPprime hR0 (by norm_num) (by norm_num) hC
      hCsBudget hCsBudget hCBudget hs hLong hR
      hbs hAlphaBoundLow
      S Ts Tb Vs Vsmall Vbig ts tb coef k
      hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc denR d0 q chiR sigmaR
  have hLowPower : Dsmall ≤ Dlow := by dsimp [Dsmall,Dlow]; omega
  have hLowStronger :=
    source_actual_stronger_log_saving L Dsmall Dlow hL3 hLowPower
  have hDelta : L^(-As) = delta := by
    dsimp [As,delta,E,Dsmall]
    rw [Real.rpow_neg (by linarith : (0:ℝ)≤L)]
    simp only [Real.rpow_natCast]
  have hHighEnergy' :
      (∫ t in sourceActualLargeHighTimes s bs T delta cutoff,
       ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
          R a b alphaCut bs (fun p => chiL p) dPhys joint
          sigma0 sigma1 t‖^2) ≤ (L^Dsmall)⁻¹ := by
    simpa only [delta,cutoff,alphaCut,dPhys,joint,hDelta] using hHighEnergy
  have hLowEnergy' :
      (∫ t in sourceActualLargeLowTimes s bs T delta cutoff,
       ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
          R a b alphaCut bs (fun p => chiL p) dPhys joint
          sigma0 sigma1 t‖^2) ≤ (L^Dsmall)⁻¹ := by
    have hLowBound' :
        (∫ t in sourceActualLargeLowTimes s bs T delta cutoff,
         ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
            R a b alphaCut bs (fun p => chiL p) dPhys joint
            sigma0 sigma1 t‖^2) ≤ (L^Dlow)⁻¹ := by
      simpa only [alphaCut,dPhys,joint,delta,cutoff,T] using hLowEnergy
    exact hLowBound'.trans hLowStronger
  have hNonSmall' :
      (∫ t in sourceActualSmallTimes s bs T delta,
       ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
          R a b alphaCut bs (fun p => chiL p) dPhys joint
          sigma0 sigma1 t‖^2) ≤ (L^Dsmall)⁻¹ := by
    simpa only [alphaCut,dPhys,joint,delta,T,E,Dsmall] using hNonSmall
  have hLongPos : ∀ p ∈ sourceLongPrimeSourceSupport N I, 0 < p := by
    intro p hp
    have hp' := (Finset.mem_Icc.mp (hLong hp)).1
    omega
  have hRPos : ∀ r ∈ R, 0 < r := by
    intro r hr
    have hr' := (Finset.mem_Icc.mp (hR hr)).1
    omega
  have hFull := source_actual_literal_fourfactor_threeway_bound
    s (sourceLongPrimeSourceSupport N I) R a b
    alphaCut bs (fun p => chiL p) dPhys joint
    sigma0 sigma1 T delta cutoff ha hLongPos hRPos
    ((L^Dsmall)⁻¹) ((L^Dsmall)⁻¹) ((L^Dsmall)⁻¹)
    hNonSmall' hHighEnergy' hLowEnergy'
  calc
    _ ≤ (L^Dsmall)⁻¹+(L^Dsmall)⁻¹+(L^Dsmall)⁻¹ := by
      simpa only [T,alphaCut,dPhys,joint] using hFull
    _ ≤ (L^D)⁻¹ := by
      simpa only [Dsmall] using
        source_actual_three_contributions_log_crush L D hL3
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualRetainedPhysicalFourierUniform -/

section

open MeasureTheory Filter
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationMellin

/-! Exact source threeway energy, uniform for every retained real shift bounded
by any fixed logarithmic power. The accompanying Bochner square uses the SAME
literal physical residual and original alpha discrepancy, no energy premise.
All source scale obligations remain explicit; they must be derived in the final
source comparison-box specialization. -/
theorem eventually_source_actual_retained_physical_fourier_log_saving
    (aexp bexp τ η Cχ C0 Ccomp q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base f : ℕ)
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) (hComp : 0 < Ccomp)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ KNon : ℝ, ∃ gNon : ℕ,
    ∃ KHigh B0 Ku X0 : ℝ, ∃ s1 : ℕ,
    ∃ KLow : ℝ, ∃ gLow : ℕ,
      1 ≤ KNon ∧ 1 ≤ KHigh ∧ 0 < B0 ∧
      0 < Ku ∧ 3 ≤ X0 ∧ B0 ≤ (s1:ℝ) ∧ max s1base f + 1 ≤ s1 ∧ 1 ≤ KLow ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P M0 R0 : ℕ) (Y Hprime Carc N : ℝ) (I : Set ℝ),
      1 ≤ P → 1 ≤ M0 → 1 ≤ R0 →
      4 ≤ Y → Real.exp (L/2) ≤ Y →
      Y ≤ Real.exp (3*L/2) →
      0 < Hprime → 1 ≤ N →
      Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      x^τ/2 ≤ N → N ≤ x^η →
      Real.exp (L^aexp) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^bexp) →
      Y ≤ Ccomp*(P:ℝ)*((M0*⌈N⌉₊*R0:ℕ):ℝ) →
      ((M0*⌈N⌉₊*R0:ℕ):ℝ)*(P:ℝ) ≤ Ccomp*Y →
      2*L*Ccomp*(P:ℝ)*L^Carc ≤ Hprime →
      4*L*L^Carc ≤ Hprime →
      Ccomp ≤ (P:ℝ)*(⌈N⌉₊:ℝ) →
      2*Ccomp*(P:ℝ)*(⌈N⌉₊:ℝ) ≤ ((⌈Y⌉₊:ℝ)^(2/5:ℝ)) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a → (b:ℝ) ≤ x^2 →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L
        (((D+2+(max s0 f+1)+s1+3+2*cm)+
          5*(ec+(s1+2)+gLow+2)+10:ℕ):ℝ) x alpha →
      ∀ (s R : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, p.Prime) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ 1) →
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      d ∈ den.divisors →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      (∀ (nu : ℝ), |nu| ≤ L^f →
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
          (2*L*Y/(Hprime/L^Carc)),
        ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceAlphaDyadicCut alpha lo hi) bs
          (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 (t+nu)‖^2) ≤ (L^D)⁻¹) ∧
      ∀ (freqSet : Set ℝ) (K : ℝ → ℂ) (freq : ℝ → ℝ) (mass : ℝ),
        0 ≤ mass → Continuous freq → IntegrableOn K freqSet →
        (∫ ξ in freqSet, ‖K ξ‖) ≤ mass →
        (∀ᵐ ξ ∂volume.restrict freqSet, |freq ξ| ≤ L^f) →
        ‖∫ ξ in freqSet, K ξ •
          sourceActualFourDyadL2Lift s (sourceLongPrimeSourceSupport N I)
            R a b (2*L*Y/(Hprime/L^Carc))
            (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
            (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
              ts tb coef k G Parity c denR d0 q chiR sigmaR)
            (sourceJointCharacter qBase (den/d) chi0 xi)
            sigma0 sigma1 freq ξ‖^2 ≤ mass^2 * (L^D)⁻¹ := by
  let s0eff : ℕ := max s0 f+1
  let s1req : ℕ := max s1base f+1
  obtain ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
      hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,hMain⟩ :=
    eventually_source_actual_all_threeway_physical_log_saving_above
      aexp bexp τ η Cχ C0 Ccomp q0 vmin tmax ea ec s0eff cm D s1req
      haexp hab hb hτ hτη hη hCχ hC0 hComp hq0 hq1 hv
  refine ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,?_⟩
  filter_upwards [hMain] with L hMainL
  intro x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmin hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare
    hFree hFreeStrong hProdLower hPrimeScales
  intro ι β _ _ _ _ hGroupSmall hGroupBig
  intro lo hi a b alpha ha hb hM hAlpha hDisc
  intro s R bs hPrime hs hbs hR qL chiL hqL hqLC
  intro qBase den d chi0 xi hBase hDen hd sigma0 sigma1
    hSigma0 hSigma1 C hC hCBudget
  intro S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc denR d0 q chiR sigmaR
  let T : ℝ := 2*L*Y/(Hprime/L^Carc)
  have hTranslated (nu : ℝ) (hNu : |nu| ≤ L^f) :
      (∫ t in Set.Icc (-T) T,
        ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceAlphaDyadicCut alpha lo hi) bs
          (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 (t+nu)‖^2) ≤ (L^D)⁻¹ := by
    rw [source_actual_physical_translated_energy
      S Ts Tb q0 Vs Vsmall Vbig ts tb coef k
      G Parity c denR d0 q chiR sigmaR
      s (sourceLongPrimeSourceSupport N I) R a b
      (sourceAlphaDyadicCut alpha lo hi) bs
      (sourceJointCharacter qBase (den/d) chi0 xi) chiL
      sigma0 sigma1 T nu]
    have hShift := source_actual_two_retained_shift_budgets
      L sigma0 sigma1 nu s0 s1base f (by linarith) hSigma0 hSigma1 hNu
    have hSigma1' : |sigma1+nu| ≤ L^s1 :=
      hShift.2.trans (pow_le_pow_right₀ (by linarith) hs1req)
    exact hMainL x hx hLog hL3 P M0 R0 Y Hprime Carc N I
      hP hM0 hR0 hY hYmin hYmax hHprime hN hIconn hI
      hNlow hNhigh hPmin hPmax hYcompare hUcompare
      hFree hFreeStrong hProdLower hPrimeScales
      hGroupSmall hGroupBig lo hi a b alpha ha hb hM hAlpha
      (by simpa only [s0eff] using hDisc)
      s R (sourceActualRetainedFrequencyTwist bs nu)
      hPrime hs (fun p hp => by
        rw [source_actual_retained_frequency_twist_norm]; exact hbs p hp)
      hR qL chiL hqL hqLC
      qBase den d chi0 xi hBase hDen hd (sigma0+nu) (sigma1+nu)
      hShift.1 hSigma1' C hC hCBudget
      S Ts Tb Vs Vsmall Vbig ts tb coef k
      hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc denR d0 q chiR (sigmaR+nu)
  constructor
  · exact hTranslated
  · intro freqSet K freq mass hmass hFreq hK hKmass hWindow
    have hsPos : ∀ ps ∈ s, 0 < ps := by
      intro ps hps; exact (hPrime ps hps).pos
    have hpPos : ∀ p ∈ sourceLongPrimeSourceSupport N I, 0 < p := by
      intro p hp
      have hLong := source_actual_long_prime_nat_dyadic_support N I hI
      have hPprime := source_actual_long_prime_nat_dyadic_start N hN
      have hh := (Finset.mem_Icc.mp (hLong hp)).1
      omega
    have hrPos : ∀ r ∈ R, 0 < r := by
      intro r hr
      have hh := (Finset.mem_Icc.mp (hR hr)).1
      omega
    exact source_actual_fourdyad_fourier_l1_mean_square
      s (sourceLongPrimeSourceSupport N I) R a b T
      (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
      (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c denR d0 q chiR sigmaR)
      (sourceJointCharacter qBase (den/d) chi0 xi)
      sigma0 sigma1 freqSet K freq (L^D)⁻¹ mass
      (by positivity) hmass hFreq hK
      (by filter_upwards [hWindow] with ξ hξ; exact hTranslated (freq ξ) hξ)
      hKmass ha hsPos hpPos hrPos
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualRetainedScalarFourierUniform -/

section

open MeasureTheory Filter
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationMellin

/-! Native scalar version of the actual retained Fourier estimate, with the
full literal four-dyad physical square. The source scale obligations and the
original alpha discrepancy are exactly those of the threeway chain. -/
theorem eventually_source_actual_retained_scalar_fourier_log_saving
    (aexp bexp τ η Cχ C0 Ccomp q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base f : ℕ)
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) (hComp : 0 < Ccomp)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ KNon : ℝ, ∃ gNon : ℕ,
    ∃ KHigh B0 Ku X0 : ℝ, ∃ s1 : ℕ,
    ∃ KLow : ℝ, ∃ gLow : ℕ,
      1 ≤ KNon ∧ 1 ≤ KHigh ∧ 0 < B0 ∧
      0 < Ku ∧ 3 ≤ X0 ∧ B0 ≤ (s1:ℝ) ∧ max s1base f + 1 ≤ s1 ∧ 1 ≤ KLow ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P M0 R0 : ℕ) (Y Hprime Carc N : ℝ) (I : Set ℝ),
      1 ≤ P → 1 ≤ M0 → 1 ≤ R0 →
      4 ≤ Y → Real.exp (L/2) ≤ Y →
      Y ≤ Real.exp (3*L/2) →
      0 < Hprime → 1 ≤ N →
      Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      x^τ/2 ≤ N → N ≤ x^η →
      Real.exp (L^aexp) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^bexp) →
      Y ≤ Ccomp*(P:ℝ)*((M0*⌈N⌉₊*R0:ℕ):ℝ) →
      ((M0*⌈N⌉₊*R0:ℕ):ℝ)*(P:ℝ) ≤ Ccomp*Y →
      2*L*Ccomp*(P:ℝ)*L^Carc ≤ Hprime →
      4*L*L^Carc ≤ Hprime →
      Ccomp ≤ (P:ℝ)*(⌈N⌉₊:ℝ) →
      2*Ccomp*(P:ℝ)*(⌈N⌉₊:ℝ) ≤ ((⌈Y⌉₊:ℝ)^(2/5:ℝ)) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a → (b:ℝ) ≤ x^2 →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L
        (((D+2+(max s0 f+1)+s1+3+2*cm)+
          5*(ec+(s1+2)+gLow+2)+10:ℕ):ℝ) x alpha →
      ∀ (s R : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, p.Prime) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ 1) →
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      d ∈ den.divisors →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      (∀ (nu : ℝ), |nu| ≤ L^f →
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
          (2*L*Y/(Hprime/L^Carc)),
        ‖sourceFourFactorAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceAlphaDyadicCut alpha lo hi) bs
          (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 (t+nu)‖^2) ≤ (L^D)⁻¹) ∧
      ∀ (freqSet : Set ℝ) (K : ℝ → ℂ) (freq : ℝ → ℝ) (mass : ℝ),
        0 ≤ mass → Continuous freq → IntegrableOn K freqSet →
        (∫ ξ in freqSet, ‖K ξ‖) ≤ mass →
        (∀ᵐ ξ ∂volume.restrict freqSet, |freq ξ| ≤ L^f) →
        (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
            (2*L*Y/(Hprime/L^Carc)),
          ‖sourceActualSmoothFourDyadAt s (sourceLongPrimeSourceSupport N I)
            R a b (fun w => ∫ ξ in freqSet, K ξ * sourcePhase w (freq ξ))
            (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
            (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
              ts tb coef k G Parity c denR d0 q chiR sigmaR)
            (sourceJointCharacter qBase (den/d) chi0 xi)
            sigma0 sigma1 t‖^2) ≤ mass^2 * (L^D)⁻¹ := by
  obtain ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
      hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,hMain⟩ :=
    eventually_source_actual_retained_physical_fourier_log_saving
      aexp bexp τ η Cχ C0 Ccomp q0 vmin tmax ea ec s0 cm D s1base f
      haexp hab hb hτ hτη hη hCχ hC0 hComp hq0 hq1 hv
  refine ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,?_⟩
  filter_upwards [hMain] with L hMainL
  intro x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmin hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare
    hFree hFreeStrong hProdLower hPrimeScales
  intro ι β _ _ _ _ hGroupSmall hGroupBig
  intro lo hi a b alpha ha hb hM hAlpha hDisc
  intro s R bs hPrime hs hbs hR qL chiL hqL hqLC
  intro qBase den d chi0 xi hBase hDen hd sigma0 sigma1
    hSigma0 hSigma1 C hC hCBudget
  intro S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc denR d0 q chiR sigmaR
  have hEstimate := hMainL x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmin hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare
    hFree hFreeStrong hProdLower hPrimeScales
    hGroupSmall hGroupBig lo hi a b alpha ha hb hM hAlpha hDisc
    s R bs hPrime hs hbs hR qL chiL hqL hqLC
    qBase den d chi0 xi hBase hDen hd sigma0 sigma1
    hSigma0 hSigma1 C hC hCBudget
    S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc denR d0 q chiR sigmaR
  refine ⟨hEstimate.1, ?_⟩
  intro freqSet K freq mass hmass hFreq hK hKmass hWindow
  rw [← source_actual_fourdyad_bochner_norm_sq_setIntegral
    s (sourceLongPrimeSourceSupport N I) R a b (2*L*Y/(Hprime/L^Carc))
    (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
    (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c denR d0 q chiR sigmaR)
    (sourceJointCharacter qBase (den/d) chi0 xi)
    sigma0 sigma1 freqSet K freq hK hFreq]
  exact hEstimate.2 freqSet K freq mass hmass hFreq hK hKmass hWindow
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualOriginalRetainedWindowUniform -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationMellin

/-! Actual original inverse-Fourier cutoff, retained at an arbitrary fixed
logarithmic power. Uniform in all smooth compact source windows, with their
TRUE Fourier L1 mass explicit. No approximation, tail or energy hypothesis.
The tail and source-box scale obligations are separate and are not asserted. -/
theorem eventually_source_actual_original_retained_window_log_saving
    (aexp bexp τ η Cχ C0 Ccomp q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut : ℕ)
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) (hComp : 0 < Ccomp)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ KNon : ℝ, ∃ gNon : ℕ,
    ∃ KHigh B0 Ku X0 : ℝ, ∃ s1 : ℕ,
    ∃ KLow : ℝ, ∃ gLow : ℕ,
      1 ≤ KNon ∧ 1 ≤ KHigh ∧ 0 < B0 ∧
      0 < Ku ∧ 3 ≤ X0 ∧ B0 ≤ (s1:ℝ) ∧ max s1base (max vexp fcut+2) + 1 ≤ s1 ∧ 1 ≤ KLow ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P M0 R0 : ℕ) (Y Hprime Carc N : ℝ) (I : Set ℝ),
      1 ≤ P → 1 ≤ M0 → 1 ≤ R0 →
      4 ≤ Y → Real.exp (L/2) ≤ Y →
      Y ≤ Real.exp (3*L/2) →
      0 < Hprime → 1 ≤ N →
      Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      x^τ/2 ≤ N → N ≤ x^η →
      Real.exp (L^aexp) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^bexp) →
      Y ≤ Ccomp*(P:ℝ)*((M0*⌈N⌉₊*R0:ℕ):ℝ) →
      ((M0*⌈N⌉₊*R0:ℕ):ℝ)*(P:ℝ) ≤ Ccomp*Y →
      2*L*Ccomp*(P:ℝ)*L^Carc ≤ Hprime →
      4*L*L^Carc ≤ Hprime →
      Ccomp ≤ (P:ℝ)*(⌈N⌉₊:ℝ) →
      2*Ccomp*(P:ℝ)*(⌈N⌉₊:ℝ) ≤ ((⌈Y⌉₊:ℝ)^(2/5:ℝ)) →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a → (b:ℝ) ≤ x^2 →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L
        (((D+2+(max s0 (max vexp fcut+2)+1)+s1+3+2*cm)+
          5*(ec+(s1+2)+gLow+2)+10:ℕ):ℝ) x alpha →
      ∀ (s R : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, p.Prime) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ 1) →
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      d ∈ den.divisors →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      ∀ (A : ℝ) (psi1 : ℝ → ℂ) (hA : 1 ≤ A)
        (hSmooth : ContDiff ℝ ∞ psi1)
        (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
        (v1 : ℝ), |v1| ≤ L^vexp →
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
          (2*L*Y/(Hprime/L^Carc)),
        ‖sourceActualSmoothFourDyadAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceActualOriginalTruncatedWindowWeight
            A Y psi1 hA hSmooth hSupport v1 (L^fcut))
          (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 t‖^2) ≤
      (∫ ξ : ℝ, ‖(𝓕 (sourceActualLogWindowSchwartz
        A psi1 hA hSmooth hSupport)) ξ‖)^2 * (L^D)⁻¹ := by
  let feff : ℕ := max vexp fcut+2
  obtain ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
      hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,hMain⟩ :=
    eventually_source_actual_retained_scalar_fourier_log_saving
      aexp bexp τ η Cχ C0 Ccomp q0 vmin
      tmax ea ec s0 cm D s1base feff
      haexp hab hb hτ hτη hη hCχ hC0 hComp hq0 hq1 hv
  refine ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,?_⟩
  filter_upwards [hMain] with L hMainL
  intro x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmin hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare
    hFree hFreeStrong hProdLower hPrimeScales
  intro ι β _ _ _ _ hGroupSmall hGroupBig
  intro lo hi a b alpha ha hb hM hAlpha hDisc
  intro s R bs hPrime hs hbs hR qL chiL hqL hqLC
  intro qBase den d chi0 xi hBase hDen hd sigma0 sigma1
    hSigma0 hSigma1 C hC hCBudget
  intro S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc denR d0 q chiR sigmaR
  have hEstimate := hMainL x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmin hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare
    hFree hFreeStrong hProdLower hPrimeScales
    hGroupSmall hGroupBig lo hi a b alpha ha hb hM hAlpha hDisc
    s R bs hPrime hs hbs hR qL chiL hqL hqLC
    qBase den d chi0 xi hBase hDen hd sigma0 sigma1
    hSigma0 hSigma1 C hC hCBudget
    S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc denR d0 q chiR sigmaR
  intro A psi1 hA hSmooth hSupport v1 hv1
  let window : 𝓢(ℝ,ℂ) := sourceActualLogWindowSchwartz
    A psi1 hA hSmooth hSupport
  let freqSet : Set ℝ := {ξ : ℝ | |ξ| < L^fcut}
  let K : ℝ → ℂ := sourceActualLogWindowFourierKernel window Y
  let freq : ℝ → ℝ := fun ξ => v1+2*Real.pi*ξ
  let mass : ℝ := ∫ ξ : ℝ, ‖(𝓕 window) ξ‖
  have hFreq : Continuous freq := by dsimp [freq]; fun_prop
  have hK : IntegrableOn K freqSet :=
    (source_actual_log_window_fourier_kernel_integrable window Y).integrableOn
  have hmass : 0 ≤ mass := integral_nonneg (fun ξ => norm_nonneg _)
  have hKmass : (∫ ξ in freqSet, ‖K ξ‖) ≤ mass :=
    source_actual_log_window_fourier_kernel_mass_le window Y freqSet
  have hWindow : ∀ᵐ ξ ∂volume.restrict freqSet, |freq ξ| ≤ L^feff := by
    have hMeas : MeasurableSet freqSet :=
      (isOpen_lt continuous_abs continuous_const).measurableSet
    filter_upwards [ae_restrict_mem hMeas] with ξ hξ
    exact source_actual_original_fourier_frequency_budget
      L v1 ξ vexp fcut hL3 hv1 hξ.le
  have hSquare := hEstimate.2 freqSet K freq mass hmass hFreq hK hKmass hWindow
  have hsPos : ∀ ps ∈ s, 0 < ps := fun ps hps => (hPrime ps hps).pos
  have hpPos : ∀ p ∈ sourceLongPrimeSourceSupport N I, 0 < p := by
    intro p hp
    have hLong := source_actual_long_prime_nat_dyadic_support N I hI
    have hPprime := source_actual_long_prime_nat_dyadic_start N hN
    have hh := (Finset.mem_Icc.mp (hLong hp)).1
    omega
  have hrPos : ∀ r ∈ R, 0 < r := by
    intro r hr
    have hh := (Finset.mem_Icc.mp (hR hr)).1
    omega
  have hPoint (t : ℝ) :=
    source_actual_fourdyad_truncated_window_kernel_exact
      s (sourceLongPrimeSourceSupport N I) R a b
      (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
      (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k G Parity c denR d0 q chiR sigmaR)
      (sourceJointCharacter qBase (den/d) chi0 xi)
      sigma0 sigma1 t A Y v1 (L^fcut) psi1 hA (by linarith)
      ha hsPos hpPos hrPos hSmooth hSupport
  simp_rw [hPoint]
  exact hSquare
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualOriginalRetainedWindowSourceScales -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
set_option maxHeartbeats 8000000
namespace Green64Analytic.CorrelationMellin

/-! Reuse the authentic source scale derivations with the new controlled
retained-frequency theorem. The separate strong free-scale, product-lower,
2/5 split and weak Y-lower hypotheses are derived, never assumed. -/
theorem eventually_source_actual_original_retained_window_from_source_scales
    (aexp bexp τ η Cχ C0 Ccomp q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut : ℕ)
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) (hComp : 0 < Ccomp)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ KNon : ℝ, ∃ gNon : ℕ,
    ∃ KHigh B0 Ku X0 : ℝ, ∃ s1 : ℕ,
    ∃ KLow : ℝ, ∃ gLow : ℕ,
      1 ≤ KNon ∧ 1 ≤ KHigh ∧ 0 < B0 ∧
      0 < Ku ∧ 3 ≤ X0 ∧ B0 ≤ (s1:ℝ) ∧ max s1base (max vexp fcut+2) + 1 ≤ s1 ∧ 1 ≤ KLow ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P M0 R0 : ℕ) (Y Hprime Carc N : ℝ) (I : Set ℝ),
      1 ≤ P → 1 ≤ M0 → 1 ≤ R0 →
      4 ≤ Y →
      Y ≤ Real.exp (3*L/2) →
      0 < Hprime → 1 ≤ N →
      Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      x^τ/2 ≤ N → N ≤ x^η →
      Real.exp (L^aexp) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^bexp) →
      Y ≤ Ccomp*(P:ℝ)*((M0*⌈N⌉₊*R0:ℕ):ℝ) →
      ((M0*⌈N⌉₊*R0:ℕ):ℝ)*(P:ℝ) ≤ Ccomp*Y →
      2*L*Ccomp*(P:ℝ)*L^Carc ≤ Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a → (b:ℝ) ≤ x^2 →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L
        (((D+2+(max s0 (max vexp fcut+2)+1)+s1+3+2*cm)+
          5*(ec+(s1+2)+gLow+2)+10:ℕ):ℝ) x alpha →
      ∀ (s R : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, p.Prime) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ 1) →
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      d ∈ den.divisors →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      ∀ (A : ℝ) (psi1 : ℝ → ℂ) (hA : 1 ≤ A)
        (hSmooth : ContDiff ℝ ∞ psi1)
        (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
        (v1 : ℝ), |v1| ≤ L^vexp →
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
          (2*L*Y/(Hprime/L^Carc)),
        ‖sourceActualSmoothFourDyadAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceActualOriginalTruncatedWindowWeight
            A Y psi1 hA hSmooth hSupport v1 (L^fcut))
          (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 t‖^2) ≤
      (∫ ξ : ℝ, ‖(𝓕 (sourceActualLogWindowSchwartz
        A psi1 hA hSmooth hSupport)) ξ‖)^2 * (L^D)⁻¹ := by
  obtain ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
      hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,hMain⟩ :=
    eventually_source_actual_original_retained_window_log_saving
      aexp bexp τ η Cχ C0 Ccomp q0 vmin
      tmax ea ec s0 cm D s1base vexp fcut
      haexp hab hb hτ hτη hη hCχ hC0 hComp hq0 hq1 hv
  refine ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,?_⟩
  filter_upwards [hMain,
      eventually_source_prime_scale_below_two_fifths
        bexp η Ccomp hb hη hComp,
      eventually_source_short_prime_comparison_lower
        aexp Ccomp haexp hComp] with L hMainL hPrimeScale hShortScale
  intro x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare hFree hYstrong
  obtain ⟨hProdLower,hCP⟩ := hShortScale P N hN hPmin
  have hFreeStrong : 4*L*L^Carc ≤ Hprime :=
    source_actual_strong_free_scale_of_small_prime
      L Ccomp (P:ℝ) Hprime Carc (by linarith) hCP hFree
  have hYmin : Real.exp (L/2) ≤ Y :=
    (Real.exp_le_exp.mpr (by linarith : L/2 ≤ 3*L/4)).trans hYstrong
  have hxpos : 0 < x := by linarith [hX0]
  have hxExp : x = Real.exp L := by
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hxpos).symm
      _ = Real.exp L := by rw [←hLog]
  have hNexp : N ≤ Real.exp (η*L) := by
    have hPrime := hNhigh
    rw [hxExp] at hPrime
    have hPow : (Real.exp L)^η = Real.exp (η*L) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    simpa only [hPow] using hPrime
  have hPrimeBound := hPrimeScale P N Y hN hYstrong hPmax hNexp
  intro ι β _ _ _ _ hGroupSmall hGroupBig
  exact hMainL x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmin hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare
    hFree hFreeStrong hProdLower hPrimeBound hGroupSmall hGroupBig
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualUniformFullWindow -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000
namespace Green64Analytic.CorrelationMellin

/- Full original L-dependent cutoff under the literal source box scales.
Fourier mass and unrestricted tail are DERIVED from the source derivative
budget. The only analytic discrepancy premise remains SourceAlphaDiscrepancy. -/
theorem eventually_source_actual_uniform_full_window_from_source_scales
    (aexp bexp τ η Cχ C0 Ccomp q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) (hComp : 0 < Ccomp)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ KNon : ℝ, ∃ gNon : ℕ,
    ∃ KHigh B0 Ku X0 : ℝ, ∃ s1 : ℕ,
    ∃ KLow : ℝ, ∃ gLow : ℕ,
      1 ≤ KNon ∧ 1 ≤ KHigh ∧ 0 < B0 ∧
      0 < Ku ∧ 3 ≤ X0 ∧ B0 ≤ (s1:ℝ) ∧ max s1base (max vexp fcut+2) + 1 ≤ s1 ∧ 1 ≤ KLow ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P M0 R0 : ℕ) (Y Hprime Carc N : ℝ) (I : Set ℝ),
      1 ≤ P → 1 ≤ M0 → 1 ≤ R0 →
      4 ≤ Y →
      Y ≤ Real.exp (3*L/2) →
      0 < Hprime → 1 ≤ N →
      Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      x^τ/2 ≤ N → N ≤ x^η →
      Real.exp (L^aexp) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^bexp) →
      Y ≤ Ccomp*(P:ℝ)*((M0*⌈N⌉₊*R0:ℕ):ℝ) →
      ((M0*⌈N⌉₊*R0:ℕ):ℝ)*(P:ℝ) ≤ Ccomp*Y →
      2*L*Ccomp*(P:ℝ)*L^Carc ≤ Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a → (b:ℝ) ≤ x^2 →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L
        (((D+2*(epsi+1)+2+2+(max s0 (max vexp fcut+2)+1)+s1+3+2*cm)+
          5*(ec+(s1+2)+gLow+2)+10:ℕ):ℝ) x alpha →
      ∀ (s R : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, p.Prime) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ 1) →
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      d ∈ den.divisors →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      ∀ (psi1 : ℝ → ℂ)
        (hSmooth : ContDiff ℝ ∞ psi1)
        (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
        (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (sourceActualLogWindow psi1) →
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
          (2*L*Y/(Hprime/L^Carc)),
        ‖sourceActualSmoothFourDyadAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceActualOriginalWindowWeight Y psi1 v1)
          (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 t‖^2) ≤
      (L^D)⁻¹ := by
  obtain ⟨KRes,gRes,hKRes,hRes⟩ := source_actual_physical_residual_polylog_coeff_budget
    q0 vmin C0 tmax ec hq0 hq1 hv hC0
  let E : ℕ := ea+ec+gRes
  let Dret : ℕ := D+2*(epsi+1)+2
  obtain ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
      hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,hRet⟩ :=
    eventually_source_actual_original_retained_window_from_source_scales
      aexp bexp τ η Cχ C0 Ccomp q0 vmin
      tmax ea ec s0 cm Dret s1base vexp fcut
      haexp hab hb hτ hτη hη hCχ hC0 hComp hq0 hq1 hv
  have hCF : Cpsi < (fcut:ℝ) := by linarith
  have hTail := eventually_source_actual_uniform_original_cutoff_tail_mean_square
    A Cpsi (fcut:ℝ) Kpsi hA hCpsi hKpsi hCF (E+(D+2)+100)
  have hMass := eventually_source_cutoff_family_fourier_mass_power
    Cpsi (Real.log A) Kpsi epsi hCpsi (Real.log_nonneg hA) hKpsi hepsi
  have hProduct := eventually_source_actual_tail_product_upper Ccomp hComp
  refine ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,?_⟩
  filter_upwards [hRet,hTail,hMass,hProduct,
    eventually_ge_atTop (max 3 KRes),
    eventually_ge_atTop (258*3^65:ℝ)] with
    L hRetL hTailL hMassL hProductL hResScale hTailConst
  intro x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hYcompare hUcompare hFree hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups
  intro lo hi a b alpha ha hbAlpha hM hAlpha hDisc
  intro small R bs hSmallPrime hSmall hBs hR
  intro qL chiL hqL hqLbudget qBase den d chi0 xi hqBase hden hd
  intro sigma0 sigma1 hSigma0 hSigma1 C hC hCBudget
  intro S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc denR d0 q chiR sigmaR psi1 hSmooth hSupport v1 hv1 hBudget
  let long := sourceLongPrimeSourceSupport N I
  let alphaCut := sourceAlphaDyadicCut alpha lo hi
  let joint := sourceJointCharacter qBase (den/d) chi0 xi
  let dPhys := sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
    ts tb coef k G Parity c denR d0 q chiR sigmaR
  let T : ℝ := 2*L*Y/(Hprime/L^Carc)
  let U : ℝ := ((M0*P*⌈N⌉₊*R0:ℕ):ℝ)
  let NN : ℕ := (2*M0)*(2*P)*(2*⌈N⌉₊)*(2*R0)
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hYp : 0 < Y := by linarith
  have hP0 : 1 ≤ ⌈N⌉₊ := source_actual_long_prime_nat_dyadic_start N hN
  have hLong : long ⊆ Finset.Icc ⌈N⌉₊ (2*⌈N⌉₊) :=
    source_actual_long_prime_nat_dyadic_support N I hI
  have hU : 0 < U := by dsimp [U]; positivity
  have hNN : (NN:ℝ) = 16*U := by dsimp [NN,U]; push_cast; ring
  have hYcomp : Y ≤ Ccomp*U := by
    convert hYcompare using 1
    dsimp [U]; push_cast; ring
  have hUcomp : U ≤ Ccomp*Y := by
    convert hUcompare using 1
    dsimp [U]; push_cast; ring
  have hT : T ≤ U := source_actual_tail_time_le_product
    L U Y Hprime Carc Ccomp P hLp hU hYp hHprime hComp hP hYcomp hFree
  have hNNexp : (NN:ℝ) ≤ Real.exp (2*L) := hProductL U Y NN hNN hUcomp hYmax
  have hTpos : 0 ≤ T := by dsimp [T]; positivity
  have hAlphaCut (m : ℕ) (hm : m ∈ Finset.Icc a b) : ‖alphaCut m‖ ≤ L^ea := by
    dsimp [alphaCut,sourceAlphaDyadicCut]
    split_ifs with hm'
    · exact hAlpha m hm'
    · simpa using (pow_nonneg hLp.le ea)
  have hBp (p : ℕ) (hp : p ∈ long) : ‖chiL p‖ ≤ 1 := chiL.norm_le_one _
  have hdPhys (r : ℕ) (hr : r ∈ R) : ‖dPhys r‖ ≤ L^(ec+gRes) :=
    hRes L hResScale hSmallGroups hBigGroups C hC hCBudget
      S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc denR d0 q chiR sigmaR r
  let f : 𝓢(ℝ,ℂ) := sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport
  have hSupp : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-Real.log A) (Real.log A) :=
    source_actual_log_window_tsupport_interval A psi1 hA hSupport
  have hMf := hMassL f hSupp hBudget
  have hMfp : 0 ≤ ∫ xi : ℝ, ‖(𝓕 f) xi‖ := integral_nonneg (fun xi => norm_nonneg _)
  have hRetained := hRetL x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmax hHprime hN hIconn hI hNlow hNhigh hPmin hPmax
    hYcompare hUcompare hFree hYstrong hSmallGroups hBigGroups
    lo hi a b alpha ha hbAlpha hM hAlpha hDisc
    small R bs hSmallPrime hSmall hBs hR
    qL chiL hqL hqLbudget qBase den d chi0 xi hqBase hden hd
    sigma0 sigma1 hSigma0 hSigma1 C hC hCBudget
    S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
    G Parity c hc denR d0 q chiR sigmaR A psi1 hA hSmooth hSupport v1 hv1
  have hRetained' := hRetained.trans
    (source_uniform_window_mass_reserve L (∫ xi : ℝ, ‖(𝓕 f) xi‖)
      epsi D hL1 hMfp hMf)
  have hTailError := hTailL psi1 hSmooth hSupport hBudget
    small long R a b M0 P ⌈N⌉₊ R0 alphaCut bs (fun p => chiL p) dPhys joint
    sigma0 sigma1 (-T) T Y v1 (L^ea) 1 1 (L^(ec+gRes))
    hYp (by linarith) ha hM0 hP hP0 hR0 (by positivity) (by norm_num)
    (by norm_num) (by positivity) hM hSmall hLong hR hAlphaCut hBs hBp hdPhys
  have hTailError' :
      (∫ t in Set.Icc (-T) T, ‖sourceActualSmoothFourDyadAt
        small long R a b (sourceActualOriginalWindowWeight Y psi1 v1)
        alphaCut bs (fun p => chiL p) dPhys joint sigma0 sigma1 t -
        sourceActualSmoothFourDyadAt small long R a b
        (sourceActualOriginalTruncatedWindowWeight A Y psi1 hA hSmooth hSupport v1 (L^fcut))
        alphaCut bs (fun p => chiL p) dPhys joint sigma0 sigma1 t‖^2) ≤
      (L^(D+2))⁻¹ := by
    have hCutEq : L^(fcut:ℝ) = L^fcut := Real.rpow_natCast L fcut
    rw [hCutEq] at hTailError
    have hAmp : L^ea*1*1*L^(ec+gRes) = L^E := by dsimp [E]; simp only [mul_one,pow_add]; ring
    dsimp only at hTailError
    rw [hAmp,show T- -T = 2*T by ring] at hTailError
    exact hTailError.trans (source_uniform_four_cutoff_tail_log_crush
      L U T NN E (D+2) hL3 hTailConst hU hT hNN hNNexp)
  have hSplit := source_actual_fourdyad_energy_split small long R a b T
    (sourceActualOriginalWindowWeight Y psi1 v1)
    (sourceActualOriginalTruncatedWindowWeight A Y psi1 hA hSmooth hSupport v1 (L^fcut))
    alphaCut bs (fun p => chiL p) dPhys joint sigma0 sigma1
  exact hSplit.trans ((add_le_add
    (mul_le_mul_of_nonneg_left hRetained' (by norm_num))
    (mul_le_mul_of_nonneg_left hTailError' (by norm_num))).trans
      (source_uniform_window_split_reserve L D hL3))
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualUniformFullZeroBox -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000
namespace Green64Analytic.CorrelationMellin
/- The zero-box alternative is applied to the FULL original compact cutoff
BEFORE any truncation. Both product comparisons are then derived rather
than assumed. The phase, characters, gcd filter and parity are unchanged. -/
theorem eventually_source_actual_uniform_full_window_all_boxes
    (aexp bexp τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0) 
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ KNon : ℝ, ∃ gNon : ℕ,
    ∃ KHigh B0 Ku X0 : ℝ, ∃ s1 : ℕ,
    ∃ KLow : ℝ, ∃ gLow : ℕ,
      1 ≤ KNon ∧ 1 ≤ KHigh ∧ 0 < B0 ∧
      0 < Ku ∧ 3 ≤ X0 ∧ B0 ≤ (s1:ℝ) ∧ max s1base (max vexp fcut+2) + 1 ≤ s1 ∧ 1 ≤ KLow ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (P M0 R0 : ℕ) (Y Hprime Carc N : ℝ) (I : Set ℝ),
      1 ≤ P → 1 ≤ M0 → 1 ≤ R0 →
      4 ≤ Y →
      Y ≤ Real.exp (3*L/2) →
      0 < Hprime → 1 ≤ N →
      Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
      x^τ/2 ≤ N → N ≤ x^η →
      Real.exp (L^aexp) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L^bexp) →
      2*L*(16*A)*(P:ℝ)*L^Carc ≤ Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι : ℝ) ≤ C0*Real.log L →
      (Fintype.card β : ℝ) ≤ C0*Real.log L →
      ∀ (lo hi a b : ℕ) (alpha : ℕ → ℂ),
      1 ≤ a → (b:ℝ) ≤ x^2 →
      Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L
        (((D+2*(epsi+1)+2+2+(max s0 (max vexp fcut+2)+1)+s1+3+2*cm)+
          5*(ec+(s1+2)+gLow+2)+10:ℕ):ℝ) x alpha →
      ∀ (s R : Finset ℕ) (bs : ℕ → ℂ),
      (∀ p ∈ s, p.Prime) →
      s ⊆ Finset.Icc P (2*P) →
      (∀ p ∈ s, ‖bs p‖ ≤ 1) →
      R ⊆ Finset.Icc R0 (2*R0) →
      ∀ (qL : ℕ) (chiL : DirichletCharacter ℂ qL),
      1 ≤ qL → (qL:ℝ) ≤ L^Cχ →
      ∀ (qBase den d : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (xi : DirichletCharacter ℂ (den/d)),
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      d ∈ den.divisors →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec →
      ∀ (S : Finset ℕ) (Ts : ι → Finset ℕ)
        (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ j : β, Fin (tb j) → ℕ) → ℂ) (k : ℕ),
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) →
      (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) →
      (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (G Parity : Finset ℕ) (c : ℕ → ℂ),
      (∀ n, ‖c n‖ ≤ C) →
      ∀ (denR d0 q : ℕ) (chiR : DirichletCharacter ℂ q)
        (sigmaR : ℝ),
      ∀ (psi1 : ℝ → ℂ)
        (hSmooth : ContDiff ℝ ∞ psi1)
        (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
        (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (sourceActualLogWindow psi1) →
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc)))
          (2*L*Y/(Hprime/L^Carc)),
        ‖sourceActualSmoothFourDyadAt s (sourceLongPrimeSourceSupport N I)
          R a b (sourceActualOriginalWindowWeight Y psi1 v1)
          (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
          (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
            ts tb coef k G Parity c denR d0 q chiR sigmaR)
          (sourceJointCharacter qBase (den/d) chi0 xi)
          sigma0 sigma1 t‖^2) ≤
      (L^D)⁻¹ := by
  have hComp : 0 < 16*A := by linarith
  obtain ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
      hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,hMain⟩ :=
    eventually_source_actual_uniform_full_window_from_source_scales
      aexp bexp τ η Cχ C0 (16*A) q0 vmin
      tmax ea ec s0 cm D s1base vexp fcut epsi A Cpsi Kpsi
      hA hCpsi hKpsi hepsi hFcut
      haexp hab hb hτ hτη hη hCχ hC0 hComp hq0 hq1 hv
  refine ⟨KNon,gNon,KHigh,B0,Ku,X0,s1,KLow,gLow,
    hKNon,hKHigh,hB0,hKu,hX0,hB0s1,hs1req,hKLow,?_⟩
  filter_upwards [hMain] with L hMainL
  intro x hx hLog hL3 P M0 R0 Y Hprime Carc N I
    hP hM0 hR0 hY hYmax hHprime hN hIconn hI
    hNlow hNhigh hPmin hPmax hFree hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups
  intro lo hi a b alpha ha hbAlpha hM hAlpha hDisc
  intro small R bs hSmallPrime hSmall hBs hR
  intro qL chiL hqL hqLbudget qBase den d chi0 xi hqBase hden hd
  intro sigma0 sigma1 hSigma0 hSigma1 C hC hCBudget
  intro S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
  intro G Parity c hc denR d0 q chiR sigmaR psi1 hSmooth hSupport v1 hv1 hBudget
  have hLong := source_actual_long_prime_nat_dyadic_support N I hI
  rcases source_actual_original_window_zero_or_comparable
    small (sourceLongPrimeSourceSupport N I) R a b M0 P ⌈N⌉₊ R0 Y A psi1 v1
    (sourceAlphaDyadicCut alpha lo hi) bs (fun p => chiL p)
    (sourcePhysicalMarkedResidual S Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k G Parity c denR d0 q chiR sigmaR)
    (sourceJointCharacter qBase (den/d) chi0 xi) sigma0 sigma1
    (by linarith) hA hSupport hM hSmall hLong hR with hZero | hCompare
  · simp_rw [hZero]
    simpa using (by positivity : (0:ℝ) ≤ (L^D)⁻¹)
  · exact hMainL x hx hLog hL3 P M0 R0 Y Hprime Carc N I
      hP hM0 hR0 hY hYmax hHprime hN hIconn hI hNlow hNhigh hPmin hPmax
      hCompare.1 hCompare.2 hFree hYstrong hSmallGroups hBigGroups
      lo hi a b alpha ha hbAlpha hM hAlpha hDisc
      small R bs hSmallPrime hSmall hBs hR
      qL chiL hqL hqLbudget qBase den d chi0 xi hqBase hden hd
      sigma0 sigma1 hSigma0 hSigma1 C hC hCBudget
      S Ts Tb Vs Vsmall Vbig ts tb coef k hk hVs hts htb hVsmall hVbig hcoef
      G Parity c hc denR d0 q chiR sigmaR psi1 hSmooth hSupport v1 hv1 hBudget
end Green64Analytic.CorrelationMellin

end

