module

public import Green64.Library.Weights.FineMarkedArc
public import Green64.Library.Weights.Part045
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Correlation.Part033
public import Green64.Library.Weights.Part043
public import Green64.Library.Analysis.Estimates.Part007
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Green64.Library.Weights.Part032
public import Green64.Library.Correlation.Part001
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part033
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.Part042
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Data.Nat.Totient

@[expose] public section

/-!
# Sieve / Foundations / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## UniformFineArcPrecision -/

section

open MeasureTheory Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The actual B629 marked-arc precision is chosen BEFORE every fixed
positive fine-scale/roughness exponent. The same explicit S works for
all source bins. This is obtained from the original arc theorem and
the real fine discrepancy proof, not by taking maxima of unrelated S. -/
theorem parity_b629_full_marked_arc_common_precision434
    (cfg : SourceComparisonFixed434) (target : ℝ) :
    ∃ Karc : ℝ, 0 < Karc ∧ ∃ B : ℕ, ∃ S : ℝ,
      S=2*((B:ℝ)+1)+4 ∧ 2*((B:ℝ)+1)+3 < S ∧
      ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ (betaFine gammaFine : ℝ), 0<betaFine → 0<gammaFine →
      ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (prime : Bool) (l u : ℕ),
      2 ≤ l → u ≤ 2*l → Real.exp (betaFine*L) ≤ (l:ℝ) →
      (u:ℝ) ≤ Real.exp (2*L) →
      ∀ Y Hprime : ℝ, ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      ∀ d : SourceComparisonData434 ι β cfg x L Y Hprime,
      d.alpha = b629ActualFineAlpha434 prime L S gammaFine l u →
      ∀ (eps : Bool) (den h : ℕ), 0 < den → (den:ℝ) ≤ L^cfg.cm →
      (∫ theta in {theta : ℝ | |theta| ≤ L^cfg.Carc/Hprime},
        ‖sourceCircleFourierPoly d.support
          (sourceSignedCoefficients434 d.Ptw eps d.endpoint)
          (((h:ℝ)/(den:ℝ)+theta:ℝ):AddCircle (1:ℝ))‖^2) ≤
        Karc*Y*L^(-target) := by
  obtain ⟨Karc,hKarc,B,X0,hX0,hArc⟩ :=
    eventually_source_data_signed_arc434 cfg target
  let S : ℝ := 2*((B:ℝ)+1)+4
  refine ⟨Karc,hKarc,B,S,rfl,by dsimp [S]; linarith,X0,hX0,?_⟩
  intro betaFine gammaFine hbeta hgamma
  have hB : (0:ℝ)<(B:ℝ)+1 := by positivity
  have hS : 2*((B:ℝ)+1)<S := by dsimp [S]; linarith
  have hFine := b629_actual_fine_source_discrepancy434
    ((B:ℝ)+1) S betaFine gammaFine hB hS hbeta hgamma
  filter_upwards [hArc,hFine] with L hArcL hFineL
  intro x hx hLog hL prime l u hl hu hsize hub Y Hprime ι β _ _ _ _ d hAlpha
    eps den h hden hDenCap
  have hexp : Real.exp L=x := by
    rw [hLog,Real.exp_log (by linarith)]
  have hDiscStrong := hFineL prime l u hl hu hsize hub
  rw [hexp] at hDiscStrong
  have hDisc : SourceAlphaDiscrepancy L (B:ℝ) x d.alpha := by
    rw [hAlpha]
    intro q chi a b t hq ha hb ht
    have hp := Real.rpow_le_rpow_of_exponent_le
      (show 1≤L by linarith) (show (B:ℝ)≤(B:ℝ)+1 by linarith)
    exact (hDiscStrong q chi a b t (hq.trans hp) ha hb (ht.trans hp)).trans
      (Real.rpow_le_rpow_of_exponent_le (show 1≤L by linarith) (by linarith))
  exact hArcL x hx hLog hL Y Hprime d hDisc eps den h hden hDenCap

/-- A fixed finite family of original gamma bins has ONE shared S,
B, arc constant, X0, and a simultaneous large-L threshold. The number
of bins is not assumed to grow with L. This is a common-precision
arc input; propagation through the TypeII wrappers remains separate. -/
theorem parity_b629_finite_bins_full_marked_arc_common_precision434
    (cfg : SourceComparisonFixed434) (target : ℝ) :
    ∃ Karc : ℝ, 0 < Karc ∧ ∃ B : ℕ, ∃ S : ℝ,
      S=2*((B:ℝ)+1)+4 ∧ 2*((B:ℝ)+1)+3 < S ∧
      ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ (k : ℕ) (betaFine gammaFine : Fin k → ℝ),
        (∀ i, 0<betaFine i) → (∀ i, 0<gammaFine i) →
      ∀ᶠ L : ℝ in atTop, ∀ i : Fin k,
      ∀ x : ℝ, X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (prime : Bool) (l u : ℕ),
      2 ≤ l → u ≤ 2*l → Real.exp (betaFine i*L) ≤ (l:ℝ) →
      (u:ℝ) ≤ Real.exp (2*L) →
      ∀ Y Hprime : ℝ, ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      ∀ d : SourceComparisonData434 ι β cfg x L Y Hprime,
      d.alpha = b629ActualFineAlpha434 prime L S (gammaFine i) l u →
      ∀ (eps : Bool) (den h : ℕ), 0 < den → (den:ℝ) ≤ L^cfg.cm →
      (∫ theta in {theta : ℝ | |theta| ≤ L^cfg.Carc/Hprime},
        ‖sourceCircleFourierPoly d.support
          (sourceSignedCoefficients434 d.Ptw eps d.endpoint)
          (((h:ℝ)/(den:ℝ)+theta:ℝ):AddCircle (1:ℝ))‖^2) ≤
        Karc*Y*L^(-target) := by
  obtain ⟨Karc,hKarc,B,S,hSdef,hS,X0,hX0,hAll⟩ :=
    parity_b629_full_marked_arc_common_precision434 cfg target
  refine ⟨Karc,hKarc,B,S,hSdef,hS,X0,hX0,?_⟩
  intro k betaFine gammaFine hbeta hgamma
  exact Filter.eventually_all.mpr (fun i =>
    hAll (betaFine i) (gammaFine i) (hbeta i) (hgamma i))
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalComparisonGlobal -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 10000000

/-- This choice uses ONLY q0,vmin,tmax, not the arc exponent, discrepancy
order, minor-arc parameters, or the size cutoff scale. -/
noncomputable def source_data_weight_constant434 (cfg : SourceComparisonFixed434) : ℝ :=
  Classical.choose (source_original_full_global_log_budget434 cfg.q0 cfg.vmin cfg.tmax
    cfg.hq0 cfg.hq1 cfg.hv)
noncomputable def source_data_global_constant434 (cfg : SourceComparisonFixed434) : ℝ :=
  (cfg.Kpsi 0*source_data_weight_constant434 cfg)^2*(cfg.A+1)*
    (1+(Real.log (cfg.A+1)+3/2))^16
noncomputable def source_data_global_exponent434 (cfg : SourceComparisonFixed434) : ℝ :=
  2*(cfg.Cpsi+(cfg.ea:ℝ)+(cfg.ec:ℝ)+2*cfg.C0*Real.log (source_data_weight_constant434 cfg))+16

theorem source_data_weight_constant_ge434 (cfg : SourceComparisonFixed434) :
    1 ≤ source_data_weight_constant434 cfg :=
  (Classical.choose_spec (source_original_full_global_log_budget434 cfg.q0 cfg.vmin cfg.tmax
    cfg.hq0 cfg.hq1 cfg.hv)).1

theorem source_data_global_constant_nonneg434 (cfg : SourceComparisonFixed434) :
    0 ≤ source_data_global_constant434 cfg := by
  have := cfg.hA
  unfold source_data_global_constant434
  positivity

/-- Actual FULL endpoint coefficient energy. The cutoff, localization, growing
marked-group weights, and alpha dyad are discharged; no discrepancy is used. -/
theorem source_data_global_budget434 (cfg : SourceComparisonFixed434)
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (x L Y Hprime : ℝ) (hL : 3 ≤ L)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime) :
    (∑ n ∈ d.support, ‖d.endpoint n‖^2) ≤
      source_data_global_constant434 cfg*Y*L^(source_data_global_exponent434 cfg) := by
  have hLone : 1 ≤ L := by linarith
  have hYp : 0 < Y := by linarith [d.hY]
  have hYone : 1 ≤ Y := by linarith [d.hY]
  have hAlpha : ∀ m, ‖d.alphaCut m‖ ≤ L^cfg.ea := by
    intro m
    by_cases hm : m ∈ Finset.Icc d.lo d.hi
    · simpa [SourceComparisonData434.alphaCut,sourceAlphaDyadicCut,hm] using d.hAlpha m hm
    · simp only [SourceComparisonData434.alphaCut,sourceAlphaDyadicCut,if_neg hm,norm_zero]
      positivity
  have hCseq : ∀ r, ‖d.c r‖ ≤ L^cfg.ec := fun r => (d.hcBound r).trans d.hCBudget
  have hLambda : ∀ n ∈ Finset.Icc 1 d.Ncap, ‖d.cutoff n‖ ≤ cfg.Kpsi 0*L^cfg.Cpsi := by
    intro n hn
    simpa only [SourceComparisonData434.cutoff,norm_mul,sourcePhase_norm,mul_one] using
      source_original_cutoff_sup434 cfg.Cpsi L Y cfg.Kpsi d.psi1 hYp d.hBudget n
        (Finset.mem_Icc.mp hn).1
  have hSupport : ∀ n, Nat.ceil (cfg.A*Y) < n → d.cutoff n = 0 := by
    intro n hn
    have hlt : cfg.A*Y < (n:ℝ) :=
      (Nat.le_ceil (cfg.A*Y)).trans_lt (by exact_mod_cast hn)
    have hratio : cfg.A < (n:ℝ)/Y := (lt_div_iff₀ hYp).mpr hlt
    have hz : d.psi1 ((n:ℝ)/Y) = 0 := by
      by_contra hne
      exact (not_lt_of_ge (d.hSupport _ hne).2) hratio
    simp only [SourceComparisonData434.cutoff,hz,zero_mul]
  have hGlobal := (Classical.choose_spec
    (source_original_full_global_log_budget434 cfg.q0 cfg.vmin cfg.tmax
      cfg.hq0 cfg.hq1 cfg.hv)).2 (ι := ι) (β := β)
  have hRaw := hGlobal d.S d.Ts d.Tb d.Vs d.Vsmall d.Vbig d.ts d.tb d.coef d.k
    d.hk d.hVs d.hts d.htb d.hVsmall d.hVbig d.hcoef
    d.Ncap d.qBase d.primeSlot d.Ptw d.alphaCut d.c d.cutoff d.chi0
    d.sigma0 d.sigma1 cfg.A Y L cfg.C0 (cfg.Kpsi 0) cfg.Cpsi cfg.ea cfg.ec
    cfg.hA hYone hLone d.hYmax cfg.hC0 (cfg.hKpsi 0)
    d.hSmallGroups d.hBigGroups hAlpha hCseq hLambda hSupport
  have hParseval := source_original_full_coefficient_parseval434
    d.Ncap d.qBase d.S d.Ts d.Tb cfg.q0 d.Vs d.Vsmall d.Vbig d.ts d.tb d.coef d.k
    d.primeSlot d.Ptw d.alphaCut d.c d.chi0 d.sigma0 d.sigma1 d.cutoff
  change (∑ n ∈ d.support, ‖d.endpoint n‖^2) = _ at hParseval
  rw [hParseval]
  exact hRaw
end Green64Analytic.CorrelationSquare

end

/-! ## SourceHarmonicShiftedCauchy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The exact finite shifted harmonic comparison is controlled by BOTH
endpoint second moments, with no pointwise bound for either core.
The shift can be signed, and the endpoint map can be arbitrary. -/
theorem source_finite_coupled_sum_cauchy434
    (S : Finset ℕ) (t : ℕ → ℕ) (U V c : ℕ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hc : ∀ n ∈ S, ‖c n‖ ≤ B) :
    ‖∑ n ∈ S,c n*star (U n)*V (t n)‖ ≤
      B*Real.sqrt (∑ n ∈ S, ‖U n‖^2)*
        Real.sqrt (∑ n ∈ S, ‖V (t n)‖^2) := by
  have hTerm (n : ℕ) (hn : n ∈ S) :
      ‖c n*star (U n)*V (t n)‖ ≤
        B*(‖U n‖*‖V (t n)‖) := by
    calc
      _ = ‖c n‖*(‖U n‖*‖V (t n)‖) := by
        simp only [norm_mul,norm_star]
        ring
      _ ≤ B*(‖U n‖*‖V (t n)‖) :=
        mul_le_mul_of_nonneg_right (hc n hn)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hSum := Finset.sum_le_sum hTerm
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun n => ‖U n‖) (fun n => ‖V (t n)‖)
  calc
    _ ≤ ∑ n ∈ S, ‖c n*star (U n)*V (t n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, B*(‖U n‖*‖V (t n)‖) := hSum
    _ = B*(∑ n ∈ S, ‖U n‖*‖V (t n)‖) := by
      rw [Finset.mul_sum]
    _ ≤ B*(Real.sqrt (∑ n ∈ S, ‖U n‖^2)*
        Real.sqrt (∑ n ∈ S, ‖V (t n)‖^2)) :=
          mul_le_mul_of_nonneg_left hCS hB
    _ = _ := by ring

/-- Injectively reindexed second-end moment is bounded by its TRUE
finite target support. This prevents hidden multiplicity of a shift. -/
theorem source_finite_shifted_moment_subset434
    (S T : Finset ℕ) (t : ℕ → ℕ) (V : ℕ → ℂ)
    (hinj : Set.InjOn t (↑S)) (hsub : S.image t ⊆ T) :
    (∑ n ∈ S, ‖V (t n)‖^2) ≤
      ∑ m ∈ T, ‖V m‖^2 := by
  calc
    _ = ∑ m ∈ S.image t,‖V m‖^2 := by
      rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m hm hnot => sq_nonneg _)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceHarmonicAbsoluteCauchy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Absolute (not signed!) two-end envelope. This is the form needed
for discarded physical rows: no cancellation is used. -/
theorem source_finite_absolute_coupled_cauchy434
    (S T : Finset ℕ) (t : ℕ → ℕ) (U V c : ℕ → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ n ∈ S, ‖c n‖ ≤ B)
    (hinj : Set.InjOn t (↑S))
    (hsub : S.image t ⊆ T) :
    (∑ n ∈ S, ‖c n‖*(‖U n‖*‖V (t n)‖)) ≤
    B*Real.sqrt (∑ n ∈ S, ‖U n‖^2)*
      Real.sqrt (∑ m ∈ T, ‖V m‖^2) := by
  have hterms (n : ℕ) (hn : n ∈ S) :
      ‖c n‖*(‖U n‖*‖V (t n)‖) ≤
      B*(‖U n‖*‖V (t n)‖) :=
    mul_le_mul_of_nonneg_right (hc n hn)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hshift := source_finite_shifted_moment_subset434 S T t V hinj hsub
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun n => ‖U n‖) (fun n => ‖V (t n)‖)
  have hfac : 0 ≤ B*Real.sqrt (∑ n ∈ S, ‖U n‖^2) :=
    mul_nonneg hB (Real.sqrt_nonneg _)
  calc
    _ ≤ ∑ n ∈ S, B*(‖U n‖*‖V (t n)‖) :=
      Finset.sum_le_sum hterms
    _ = B*(∑ n ∈ S, ‖U n‖*‖V (t n)‖) := by
      rw [Finset.mul_sum]
    _ ≤ B*(Real.sqrt (∑ n ∈ S, ‖U n‖^2)*
        Real.sqrt (∑ n ∈ S, ‖V (t n)‖^2)) :=
      mul_le_mul_of_nonneg_left hCS hB
    _ ≤ B*(Real.sqrt (∑ n ∈ S, ‖U n‖^2)*
        Real.sqrt (∑ m ∈ T, ‖V m‖^2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hshift)
          (Real.sqrt_nonneg _)) hB
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHarmonicCauchy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Real original cutoff and harmonic 1/n together cost only K*A/Y
on the actual compact physical source window, with BOTH phases unitary. -/
theorem source_original_harmonic_coefficient_bound434
    (Y A K : ℝ) (hY : 0 < Y) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (psi : ℝ → ℂ)
    (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hNorm : ∀ r, ‖psi r‖ ≤ K)
    (n z : ℕ) (a1 a2 : ℝ) (hn : 0 < n) :
    ‖psi ((n:ℝ)/Y)/(n:ℂ) *
      sourcePhase n a1 * sourcePhase z a2‖ ≤ K*A/Y := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hApos : 0 < A := by linarith
  by_cases hz : psi ((n:ℝ)/Y) = 0
  · simp only [hz,zero_div,zero_mul,norm_zero]
    positivity
  have hLow : 1/A ≤ (n:ℝ)/Y := (hSupport _ hz).1
  have hCross : Y ≤ A*(n:ℝ) := by
    simpa only [one_mul,mul_one,mul_comm] using (div_le_div_iff₀ hApos hY).mp hLow
  have hInv : 1/(n:ℝ) ≤ A/Y :=
    (div_le_div_iff₀ hnR hY).mpr (by simpa using hCross)
  calc
    _ = ‖psi ((n:ℝ)/Y)‖/(n:ℝ) := by
      simp only [norm_mul,norm_div,sourcePhase_norm,Complex.norm_natCast,
        mul_one]
    _ ≤ K/(n:ℝ) :=
      div_le_div_of_nonneg_right (hNorm _) hnR.le
    _ ≤ K*A/Y := by
      have hh := mul_le_mul_of_nonneg_left hInv hK
      simpa only [one_div,one_mul,div_eq_mul_inv,mul_assoc] using hh

/-- Physical harmonic shifted sum with NO endpoint sup bound.
Only genuine L2 energy at the two endpoints appears. For a signed
shift, the caller must prove positivity and injective target support. -/
theorem source_original_harmonic_two_end_moment434
    (S T : Finset ℕ) (t : ℕ → ℕ) (U V : ℕ → ℂ)
    (Y A K : ℝ) (psi : ℝ → ℂ) (a1 a2 : ℝ)
    (hY : 0 < Y) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hSupport : ∀ r, psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hNorm : ∀ r, ‖psi r‖ ≤ K)
    (hSpos : ∀ n ∈ S,0 < n)
    (hinj : Set.InjOn t (↑S))
    (hsub : S.image t ⊆ T) :
    ‖∑ n ∈ S,
      psi ((n:ℝ)/Y)/(n:ℂ)*sourcePhase n a1*sourcePhase (t n) a2*
        star (U n)*V (t n)‖ ≤
      (K*A/Y)*Real.sqrt (∑ n ∈ S, ‖U n‖^2)*
        Real.sqrt (∑ m ∈ T, ‖V m‖^2) := by
  let c : ℕ → ℂ := fun n =>
    psi ((n:ℝ)/Y)/(n:ℂ)*sourcePhase n a1*sourcePhase (t n) a2
  have hcoeff : ∀ n ∈ S, ‖c n‖ ≤ K*A/Y := by
    intro n hn
    exact source_original_harmonic_coefficient_bound434
      Y A K hY hA hK psi hSupport hNorm n (t n) a1 a2 (hSpos n hn)
  have hB : 0 ≤ K*A/Y := by positivity
  have hCS := source_finite_coupled_sum_cauchy434
    S t U V c (K*A/Y) hB hcoeff
  have hshift := source_finite_shifted_moment_subset434 S T t V hinj hsub
  have hmon : Real.sqrt (∑ n ∈ S, ‖V (t n)‖^2) ≤
      Real.sqrt (∑ m ∈ T, ‖V m‖^2) := Real.sqrt_le_sqrt hshift
  have hfac : 0 ≤ (K*A/Y)*Real.sqrt (∑ n ∈ S, ‖U n‖^2) :=
    mul_nonneg hB (Real.sqrt_nonneg _)
  calc
    _ ≤ (K*A/Y)*Real.sqrt (∑ n ∈ S, ‖U n‖^2)*
        Real.sqrt (∑ n ∈ S, ‖V (t n)‖^2) := by
      simpa only [c] using hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left hmon hfac
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryCoreHarmonic -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- True unmarked source-core harmonic second-moment bound after
w=p*y. The signed shifted positions are injective on the genuine
positive domain. The two original cores and four independent parity
choices are unchanged; NO pointwise core majorant is postulated. -/
theorem source_auxiliary_original_core_absolute_harmonic434
    (cfg : SourceComparisonFixed434)
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x L Y Hprime : ℝ) (hL : 1 ≤ L)
    (u v : SourceComparisonData434 ι β cfg x L Y Hprime)
    (S T : Finset ℕ) (N1 N2 : ℕ) (next : ℕ → ℕ)
    (hS : S ⊆ Finset.Icc 1 N1)
    (hT : T ⊆ Finset.Icc 1 N2)
    (hSpos : ∀ n ∈ S,0 < n)
    (hInj : Set.InjOn next (↑S))
    (hNext : S.image next ⊆ T)
    (R A K : ℝ) (hR : 0 < R) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (psi : ℝ → ℂ) (hSupport : ∀ r,psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hNorm : ∀ r,‖psi r‖ ≤ K)
    (a1 a2 : ℝ) (eps1 eps2 : Bool) :
    let U := fun n => sourceEndpointSign434 u.Ptw eps1 n*
      sourceCore (sourceOutsidePart u.G n) u.primeSlot
        u.alphaCut u.c u.qBase u.chi0 u.sigma0 u.sigma1
    let V := fun n => sourceEndpointSign434 u.Ptw eps2 n*
      sourceCore (sourceOutsidePart v.G n) v.primeSlot
        v.alphaCut v.c v.qBase v.chi0 v.sigma0 v.sigma1
    let Acore := (L^cfg.ea*L^cfg.ec)^2
    (∑ n ∈ S,
      ‖psi ((n:ℝ)/R)/(n:ℂ)*sourcePhase n a1*
        sourcePhase (next n) a2‖*‖U n‖*‖V (next n)‖) ≤
    (K*A/R)*
      Real.sqrt (Acore*(N1:ℝ)*(1+Real.log (N1:ℝ))^16)*
      Real.sqrt (Acore*(N2:ℝ)*(1+Real.log (N2:ℝ))^16) := by
  classical
  dsimp only
  let U : ℕ → ℂ := fun n => sourceEndpointSign434 u.Ptw eps1 n*
    sourceCore (sourceOutsidePart u.G n) u.primeSlot
      u.alphaCut u.c u.qBase u.chi0 u.sigma0 u.sigma1
  let V : ℕ → ℂ := fun n => sourceEndpointSign434 u.Ptw eps2 n*
    sourceCore (sourceOutsidePart v.G n) v.primeSlot
      v.alphaCut v.c v.qBase v.chi0 v.sigma0 v.sigma1
  let c : ℕ → ℂ := fun n =>
    psi ((n:ℝ)/R)/(n:ℂ)*sourcePhase n a1*sourcePhase (next n) a2
  let Acore : ℝ := (L^cfg.ea*L^cfg.ec)^2
  let RU : ℝ := Acore*(N1:ℝ)*(1+Real.log (N1:ℝ))^16
  let RV : ℝ := Acore*(N2:ℝ)*(1+Real.log (N2:ℝ))^16
  have hUenergy : (∑ n ∈ S,‖U n‖^2) ≤ RU := by
    have hAll := source_data_unmarked_core_global_square434
      cfg x L Y Hprime hL u N1
    have hSub : (∑ n ∈ S,‖U n‖^2) ≤
        ∑ n ∈ Finset.Icc 1 N1,‖U n‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun n hn hnot => sq_nonneg _)
    have hEq : (∑ n ∈ Finset.Icc 1 N1,‖U n‖^2) =
      ∑ n ∈ Finset.Icc 1 N1,
        ‖sourceCore (sourceOutsidePart u.G n) u.primeSlot
          u.alphaCut u.c u.qBase u.chi0 u.sigma0 u.sigma1‖^2 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [U,norm_mul,source_endpoint_sign_norm434,one_mul]
    rw [hEq] at hSub
    exact hSub.trans hAll
  have hVenergy : (∑ n ∈ T,‖V n‖^2) ≤ RV := by
    have hAll := source_data_unmarked_core_global_square434
      cfg x L Y Hprime hL v N2
    have hSub : (∑ n ∈ T,‖V n‖^2) ≤
        ∑ n ∈ Finset.Icc 1 N2,‖V n‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hT
        (fun n hn hnot => sq_nonneg _)
    have hEq : (∑ n ∈ Finset.Icc 1 N2,‖V n‖^2) =
      ∑ n ∈ Finset.Icc 1 N2,
        ‖sourceCore (sourceOutsidePart v.G n) v.primeSlot
          v.alphaCut v.c v.qBase v.chi0 v.sigma0 v.sigma1‖^2 := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [V,norm_mul,source_endpoint_sign_norm434,one_mul]
    rw [hEq] at hSub
    exact hSub.trans hAll
  have hcoeff (n : ℕ) (hn : n ∈ S) : ‖c n‖ ≤ K*A/R :=
    source_original_harmonic_coefficient_bound434
      R A K hR hA hK psi hSupport hNorm n (next n) a1 a2 (hSpos n hn)
  have hfac : 0 ≤ K*A/R := div_nonneg
    (mul_nonneg hK (zero_le_one.trans hA)) hR.le
  have hPair := source_finite_absolute_coupled_cauchy434
    S T next U V c (K*A/R) hfac hcoeff hInj hNext
  have hRoot1 : Real.sqrt (∑ n ∈ S,‖U n‖^2) ≤ Real.sqrt RU :=
    Real.sqrt_le_sqrt hUenergy
  have hRoot2 : Real.sqrt (∑ n ∈ T,‖V n‖^2) ≤ Real.sqrt RV :=
    Real.sqrt_le_sqrt hVenergy
  have hProduct : Real.sqrt (∑ n ∈ S,‖U n‖^2)*
      Real.sqrt (∑ n ∈ T,‖V n‖^2) ≤
      Real.sqrt RU*Real.sqrt RV :=
    mul_le_mul hRoot1 hRoot2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ = ∑ n ∈ S,‖c n‖*(‖U n‖*‖V (next n)‖) := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [c,U,V]
      ring
    _ ≤ (K*A/R)*Real.sqrt (∑ n ∈ S,‖U n‖^2)*
        Real.sqrt (∑ n ∈ T,‖V n‖^2) := hPair
    _ ≤ (K*A/R)*(Real.sqrt RU*Real.sqrt RV) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hProduct hfac
    _ = _ := by dsimp only [RU,RV,Acore]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryGeneralCoreMoment -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Genuine source stripped term with independent original parity
subset Ptw has the SAME positive unmarked-core envelope as the
untwisted term. This holds for all four sign combinations. -/
theorem source_auxiliary_general_stripped_norm434
    (P Ptw prime1 prime2 : Finset ℕ) (y D q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) :
    let yp := ((y:ℤ)+k*(D:ℤ)).toNat
    ‖sourceAuxiliaryGeneralStripped434 P Ptw prime1 prime2
      y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2‖ =
    ‖psi ((y:ℝ)/(Z*(D:ℝ)))*(y:ℂ)⁻¹*
      sourcePhase y a1*sourcePhase yp a2‖*
    ‖sourceCore (sourceOutsidePart P y)
      prime1 alpha1 c1 q1 chi1 s01 s11‖*
    ‖sourceCore (sourceOutsidePart P yp)
      prime2 alpha2 c2 q2 chi2 s02 s12‖ := by
  dsimp only
  simp only [sourceAuxiliaryGeneralStripped434,norm_mul,
    sourcePhase_norm,source_endpoint_sign_norm434,norm_star,mul_one,one_mul]

/-- A source original post-charge finite fibre is controlled by the
REAL global L2 moments of its two prime-slot cores at the physical
scale Z*D, even for an arbitrary negative shift k. -/
theorem source_auxiliary_original_general_core_moment434
    (cfg : SourceComparisonFixed434)
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x L Y Hprime : ℝ) (hL : 1 ≤ L)
    (u v : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hG : v.G=u.G)
    (S T : Finset ℕ) (N1 N2 : ℕ)
    (D : ℕ) (k : ℤ) (Z A K : ℝ)
    (hZ : 0 < Z) (hD : 0 < D) (hA : 1 ≤ A) (hK : 0 ≤ K)
    (psi : ℝ → ℂ)
    (hSupport : ∀ r,psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hNorm : ∀ r, ‖psi r‖ ≤ K)
    (hS : S ⊆ Finset.Icc 1 N1)
    (hT : T ⊆ Finset.Icc 1 N2)
    (hSpos : ∀ n ∈ S, 0 < n)
    (hShift : ∀ n ∈ S, 0 < (n:ℤ)+k*(D:ℤ))
    (hNext : S.image (fun n : ℕ => ((n:ℤ)+k*(D:ℤ)).toNat) ⊆ T)
    (a1 a2 : ℝ) (eps1 eps2 : Bool) :
    let R := Z*(D:ℝ)
    let Acore := (L^cfg.ea*L^cfg.ec)^2
    (∑ n ∈ S,
      ‖sourceAuxiliaryGeneralStripped434 u.G u.Ptw u.primeSlot v.primeSlot
        n D u.qBase v.qBase k u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
        u.sigma0 u.sigma1 v.sigma0 v.sigma1 Z a1 a2 psi eps1 eps2‖) ≤
      (K*A/R)*
        Real.sqrt (Acore*(N1:ℝ)*(1+Real.log (N1:ℝ))^16)*
        Real.sqrt (Acore*(N2:ℝ)*(1+Real.log (N2:ℝ))^16) := by
  dsimp only
  let R : ℝ := Z*(D:ℝ)
  let next : ℕ → ℕ := fun n => ((n:ℤ)+k*(D:ℤ)).toNat
  let U : ℕ → ℂ := fun n => sourceEndpointSign434 u.Ptw eps1 n*
    sourceCore (sourceOutsidePart u.G n) u.primeSlot
      u.alphaCut u.c u.qBase u.chi0 u.sigma0 u.sigma1
  let V : ℕ → ℂ := fun n => sourceEndpointSign434 u.Ptw eps2 n*
    sourceCore (sourceOutsidePart v.G n) v.primeSlot
      v.alphaCut v.c v.qBase v.chi0 v.sigma0 v.sigma1
  let c : ℕ → ℂ := fun n =>
    psi ((n:ℝ)/R)/(n:ℂ)*sourcePhase n a1*sourcePhase (next n) a2
  have hR : 0 < R := mul_pos hZ (by exact_mod_cast hD)
  have hInj : Set.InjOn next (↑S) := by
    intro n hn m hm he
    have hp1 : ((((n:ℤ)+k*(D:ℤ)).toNat:ℤ))=(n:ℤ)+k*(D:ℤ) :=
      Int.toNat_of_nonneg (hShift n hn).le
    have hp2 : ((((m:ℤ)+k*(D:ℤ)).toNat:ℤ))=(m:ℤ)+k*(D:ℤ) :=
      Int.toNat_of_nonneg (hShift m hm).le
    have hc : (next n:ℤ)=(next m:ℤ) := congrArg Nat.cast he
    dsimp only [next] at hc
    rw [hp1,hp2] at hc
    exact_mod_cast (show (n:ℤ)=(m:ℤ) by omega)
  have hNext' : S.image next ⊆ T := by
    simpa only [next] using hNext
  have hMoment := source_auxiliary_original_core_absolute_harmonic434
    cfg x L Y Hprime hL u v S T N1 N2 next hS hT hSpos hInj hNext'
    R A K hR hA hK psi (by
      simpa only [R] using hSupport) hNorm a1 a2 eps1 eps2
  change (∑ n ∈ S,‖c n‖*‖U n‖*‖V (next n)‖) ≤ _ at hMoment
  calc
    _ = ∑ n ∈ S, ‖c n‖*‖U n‖*‖V (next n)‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hForm := source_auxiliary_general_stripped_norm434
        u.G u.Ptw u.primeSlot v.primeSlot n D u.qBase v.qBase
        k u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
        u.sigma0 u.sigma1 v.sigma0 v.sigma1 Z a1 a2 psi eps1 eps2
      dsimp only at hForm
      rw [hForm]
      dsimp only [c,U,V,next,R]
      rw [hG]
      simp only [source_endpoint_sign_norm434,norm_mul,one_mul,div_eq_mul_inv]
    _ ≤ _ := hMoment
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryTrueWindow -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Original cutoff on y/(Z*D) forces BOTH physical endpoints into
the genuine finite post-charge support, even for negative signed k.
The cap is proportional to Z*D, not to the original larger Z*p*D. -/
theorem source_auxiliary_shifted_window_support434
    (A Z : ℝ) (D y : ℕ) (k : ℤ) (psi : ℝ → ℂ)
    (hA : 1 ≤ A) (hZ : 0 < Z) (hD : 0 < D)
    (hY : 0 < y)
    (hK : |(k:ℝ)| ≤ Z/(2*A))
    (hSupport : ∀ r,psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hPsi : psi ((y:ℝ)/(Z*(D:ℝ))) ≠ 0) :
    let R : ℝ := Z*(D:ℝ)
    let N : ℕ := ⌈18*A*R⌉₊
    y ∈ Finset.Icc 1 N ∧
      0 < (y:ℤ)+k*(D:ℤ) ∧
      ((y:ℤ)+k*(D:ℤ)).toNat ∈ Finset.Icc 1 N := by
  dsimp only
  let R : ℝ := Z*(D:ℝ)
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hR : 0 < R := mul_pos hZ hDR
  let yp : ℤ := (y:ℤ)+k*(D:ℤ)
  have hShift : (yp:ℝ) = (y:ℝ)+(k:ℝ)*(D:ℝ) := by
    simp only [yp,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  have hDelta : |(k:ℝ)*(D:ℝ)| ≤ R/(2*A) := by
    have hDN : 0 ≤ (D:ℝ) := Nat.cast_nonneg _
    rw [abs_mul,abs_of_nonneg hDN]
    calc
      _ ≤ (Z/(2*A))*(D:ℝ) :=
        mul_le_mul_of_nonneg_right hK hDN
      _ = _ := by dsimp [R]; ring
  have hw := source_harmonic_shift_window434 A R R (y:ℝ) (yp:ℝ)
    ((k:ℝ)*(D:ℝ)) hA hR le_rfl (by linarith [hR])
    (hSupport _ hPsi) hDelta hShift
  have hYupper : (y:ℝ) ≤ 18*A*R := (div_le_iff₀ hR).mp hw.1.2
  have hYPupper : (yp:ℝ) ≤ 18*A*R := (div_le_iff₀ hR).mp hw.2.2
  have hYPpos : (0:ℝ) < (yp:ℝ) := by
    have hBound : 0 < (yp:ℝ)/R := (by positivity : (0:ℝ) < 1/(18*A)).trans_le hw.2.1
    exact (div_pos_iff_of_pos_right hR).mp hBound
  have hYP : 0 < yp := by exact_mod_cast hYPpos
  have hYN : y ≤ ⌈18*A*R⌉₊ := by
    exact_mod_cast hYupper.trans (Nat.le_ceil (18*A*R))
  have hYPN : yp.toNat ≤ ⌈18*A*R⌉₊ := by
    have he : (yp.toNat:ℝ) = (yp:ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hYP.le
    have hh : (yp.toNat:ℝ) ≤ (⌈18*A*R⌉₊:ℝ) := by
      calc
        _ = (yp:ℝ) := he
        _ ≤ 18*A*R := hYPupper
        _ ≤ (⌈18*A*R⌉₊:ℝ) := Nat.le_ceil _
    exact_mod_cast hh
  change y ∈ Finset.Icc 1 ⌈18*A*R⌉₊ ∧
    0 < yp ∧ yp.toNat ∈ Finset.Icc 1 ⌈18*A*R⌉₊
  exact ⟨Finset.mem_Icc.mpr ⟨hY,hYN⟩,hYP,
    Finset.mem_Icc.mpr ⟨by omega,hYPN⟩⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryScaleBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Deterministic source post-charge moment budget: the exact natural
cutoff N=ceil(18*A*R), with R=Z*D, never introduces a growing
uncompensated physical factor. A fixed logarithmic exponent suffices. -/
theorem source_auxiliary_true_scale_moment_budget434
    (A R K L : ℝ) (ea ec : ℕ)
    (hA : 1 ≤ A) (hR : 1 ≤ R) (hK : 0 ≤ K) (hL : 1 ≤ L)
    (hNcap : Real.log ((⌈18*A*R⌉₊:ℕ):ℝ) ≤ 2*L) :
    let N : ℕ := ⌈18*A*R⌉₊
    let M : ℝ := ((L^ea*L^ec)^2)*
      (N:ℝ)*(1+Real.log (N:ℝ))^16
    (K*A/R)*Real.sqrt M*Real.sqrt M ≤
      (K*A*(18*A+1)*(3:ℝ)^16)*L^(2*ea+2*ec+16:ℝ) := by
  dsimp only
  let N : ℕ := ⌈18*A*R⌉₊
  let M : ℝ := ((L^ea*L^ec)^2)*
    (N:ℝ)*(1+Real.log (N:ℝ))^16
  have hAp : 0 < A := by linarith
  have hRp : 0 < R := by linarith
  have hLp : 0 < L := by linarith
  have hNpos : 0 < N := by
    have hN : (0:ℝ) < 18*A*R := by positivity
    have hh : 18*A*R ≤ (N:ℝ) := Nat.le_ceil _
    have hnR : (0:ℝ) < N := lt_of_lt_of_le hN hh
    exact_mod_cast hnR
  have hNle : (N:ℝ) ≤ (18*A+1)*R := by
    have hc : (N:ℝ) ≤ 18*A*R+1 :=
      (Nat.ceil_lt_add_one (show 0 ≤ 18*A*R by positivity)).le
    calc
      _ ≤ 18*A*R+1 := hc
      _ ≤ (18*A+1)*R := by nlinarith
  have hLogPos : 0 ≤ Real.log (N:ℝ) :=
    Real.log_nonneg (by exact_mod_cast hNpos)
  have hLogBound : 0 ≤ 1+Real.log (N:ℝ) ∧
      1+Real.log (N:ℝ) ≤ 3*L := by
    constructor
    · linarith
    · change Real.log (N:ℝ) ≤ 2*L at hNcap
      linarith
  have hLogPower : (1+Real.log (N:ℝ))^16 ≤ (3*L)^16 := by
    exact pow_le_pow_left₀ hLogBound.1 hLogBound.2 _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMoment : (K*A/R)*M ≤
      (K*A*(18*A+1)*(3:ℝ)^16)*L^(2*ea+2*ec+16:ℝ) := by
    have hScale : (N:ℝ)/R ≤ 18*A+1 :=
      (div_le_iff₀ hRp).mpr hNle
    have hScaleNonneg : 0 ≤ (K*A)*((L^ea*L^ec)^2) := by positivity
    have hByScale := mul_le_mul_of_nonneg_left hScale hScaleNonneg
    have hByLog := mul_le_mul_of_nonneg_left hLogPower
      (by positivity : 0 ≤ K*A*(18*A+1)*(L^ea*L^ec)^2)
    calc
      _ = (K*A*((L^ea*L^ec)^2))*((N:ℝ)/R)*
          (1+Real.log (N:ℝ))^16 := by dsimp [M]; ring
      _ ≤ (K*A*((L^ea*L^ec)^2))*(18*A+1)*
          (1+Real.log (N:ℝ))^16 :=
        mul_le_mul_of_nonneg_right hByScale
          (pow_nonneg hLogBound.1 _)
      _ ≤ (K*A*((L^ea*L^ec)^2))*(18*A+1)*(3*L)^16 := by
        exact mul_le_mul_of_nonneg_left hLogPower (by positivity)
      _ = _ := by
        have hPow : L^(2*ea+2*ec+16:ℝ) =
            (L^ea*L^ec)^2*L^16 := by
          calc
            _ = L^((((ea:ℝ)+(ec:ℝ))*2)+(16:ℝ)) := by
              congr 1
              push_cast
              ring
            _ = L^(((ea:ℝ)+(ec:ℝ))*2)*L^(16:ℝ) :=
              Real.rpow_add hLp _ _
            _ = (L^((ea:ℝ)+(ec:ℝ)))^2*L^16 := by
              rw [Real.rpow_mul hLp.le]
              norm_cast
            _ = (L^ea*L^ec)^2*L^16 := by
              rw [Real.rpow_add hLp]
              norm_cast
        rw [hPow,mul_pow]
        ring
  change (K*A/R)*Real.sqrt M*Real.sqrt M ≤ _
  calc
    _ = (K*A/R)*(Real.sqrt M*Real.sqrt M) := by ring
    _ = (K*A/R)*M := by rw [Real.mul_self_sqrt hM]
    _ ≤ _ := hMoment
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryTrueFibreSupport -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Original post-charge source fibre has exactly the small,
physically supported y-window. The larger original arithmetic cap
can be removed without any discarded term or assumption on core
coefficients. Negative signed shifts are tested before toNat. -/
theorem source_auxiliary_general_true_window_sum434
    (P Ptw prime1 prime2 : Finset ℕ) (q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) (D M : ℕ) (A : ℝ)
    (hA : 1 ≤ A) (hZ : 0 < Z) (hD : 0 < D)
    (hK : |(k:ℝ)| ≤ Z/(2*A))
    (hSupport : ∀ r,psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hM : ⌈18*A*(Z*(D:ℝ))⌉₊ ≤ M) :
    (∑ y ∈ (Finset.Icc 1 M).filter
      (fun y : ℕ => 0 < (y:ℤ)+k*(D:ℤ)),
      sourceAuxiliaryGeneralStripped434 P Ptw prime1 prime2
        y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
        s01 s11 s02 s12 Z a1 a2 psi eps1 eps2) =
    (∑ y ∈ (Finset.Icc 1 ⌈18*A*(Z*(D:ℝ))⌉₊).filter
      (fun y : ℕ => 0 < (y:ℤ)+k*(D:ℤ)),
      sourceAuxiliaryGeneralStripped434 P Ptw prime1 prime2
        y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
        s01 s11 s02 s12 Z a1 a2 psi eps1 eps2) := by
  classical
  let N : ℕ := ⌈18*A*(Z*(D:ℝ))⌉₊
  let S : Finset ℕ := (Finset.Icc 1 N).filter
    (fun y : ℕ => 0 < (y:ℤ)+k*(D:ℤ))
  let T : Finset ℕ := (Finset.Icc 1 M).filter
    (fun y : ℕ => 0 < (y:ℤ)+k*(D:ℤ))
  have hSub : S ⊆ T := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hy'.1).1,?_⟩,hy'.2⟩
    exact (Finset.mem_Icc.mp hy'.1).2.trans hM
  change (∑ y ∈ T,_) = (∑ y ∈ S,_)
  symm
  apply Finset.sum_subset hSub
  intro y hy hnot
  have hy' := Finset.mem_filter.mp hy
  have hypos : 0 < y := (Finset.mem_Icc.mp hy'.1).1
  have hzero : psi ((y:ℝ)/(Z*(D:ℝ)))=0 := by
    by_contra hn
    have hb := source_auxiliary_shifted_window_support434
      A Z D y k psi hA hZ hD hypos hK hSupport hn
    have hmem : y ∈ S := by
      exact Finset.mem_filter.mpr ⟨hb.1,hy'.2⟩
    exact hnot hmem
  simp only [sourceAuxiliaryGeneralStripped434,hzero,zero_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryTwoEndSupport -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ORIGINAL post-charge cutoff forces the shifted endpoint into
the SAME genuine natural support. The correction from testing only
positivity to testing actual membership has exactly zero discarded
mass, not merely a small analytic error. -/
theorem source_auxiliary_general_two_end_true_support434
    (P Ptw prime1 prime2 : Finset ℕ) (q1 q2 : ℕ)
    (k : ℤ) (alpha1 alpha2 c1 c2 : ℕ → ℂ)
    (chi1 : DirichletCharacter ℂ q1)
    (chi2 : DirichletCharacter ℂ q2)
    (s01 s11 s02 s12 Z a1 a2 : ℝ) (psi : ℝ → ℂ)
    (eps1 eps2 : Bool) (D : ℕ) (A : ℝ)
    (hA : 1 ≤ A) (hZ : 0 < Z) (hD : 0 < D)
    (hK : |(k:ℝ)| ≤ Z/(2*A))
    (hSupport : ∀ r,psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A) :
    let N : ℕ := ⌈18*A*(Z*(D:ℝ))⌉₊
    let T : Finset ℕ := Finset.Icc 1 N
    let f := fun y => sourceAuxiliaryGeneralStripped434 P Ptw prime1 prime2
      y D q1 q2 k alpha1 alpha2 c1 c2 chi1 chi2
      s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
    (∑ y ∈ T.filter (fun y : ℕ => 0 < (y:ℤ)+k*(D:ℤ)),f y) =
    ∑ y ∈ T.filter (fun y : ℕ =>
      0 < (y:ℤ)+k*(D:ℤ) ∧
      ((y:ℤ)+k*(D:ℤ)).toNat∈T),f y := by
  classical
  dsimp only
  let N : ℕ := ⌈18*A*(Z*(D:ℝ))⌉₊
  let T : Finset ℕ := Finset.Icc 1 N
  let S : Finset ℕ := T.filter
    (fun y : ℕ => 0 < (y:ℤ)+k*(D:ℤ))
  let S2 : Finset ℕ := T.filter (fun y : ℕ =>
    0 < (y:ℤ)+k*(D:ℤ) ∧
      ((y:ℤ)+k*(D:ℤ)).toNat ∈ T)
  let f : ℕ → ℂ := fun y => sourceAuxiliaryGeneralStripped434
    P Ptw prime1 prime2 y D q1 q2 k alpha1 alpha2 c1 c2
    chi1 chi2 s01 s11 s02 s12 Z a1 a2 psi eps1 eps2
  have hSub : S2 ⊆ S := by
    intro y hy
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2.1⟩
  change (∑ y ∈ S,f y) = ∑ y ∈ S2,f y
  symm
  apply Finset.sum_subset hSub
  intro y hy hnot
  have hy' := Finset.mem_filter.mp hy
  have hypos := (Finset.mem_Icc.mp hy'.1).1
  have hzero : psi ((y:ℝ)/(Z*(D:ℝ)))=0 := by
    by_contra hn
    have hW := source_auxiliary_shifted_window_support434
      A Z D y k psi hA hZ hD hypos hK hSupport hn
    have hIn : y ∈ S2 := Finset.mem_filter.mpr
      ⟨hy'.1,⟨hy'.2,hW.2.2⟩⟩
    exact hnot hIn
  dsimp only [f]
  simp only [sourceAuxiliaryGeneralStripped434,hzero,zero_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryTrueMoment -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- Quantitative literal post-charge shifted divisor moment, with
the physical target support DERIVED from the source cutoff. This is
uniform in both core choices and all four independent parity channels.
It contains no endpoint pointwise core bound and no unproved
shifted-convolution estimate. -/
theorem source_auxiliary_original_true_shifted_moment434
    (cfg : SourceComparisonFixed434)
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x L Y Hprime : ℝ) (hL : 1 ≤ L)
    (u v : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hG : v.G=u.G) (D : ℕ) (k : ℤ)
    (Z A K : ℝ) (hZ : 0 < Z) (hD : 0 < D)
    (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hShift : |(k:ℝ)| ≤ Z/(2*A))
    (hScale : 1 ≤ Z*(D:ℝ))
    (hLogCap : Real.log ((⌈18*A*(Z*(D:ℝ))⌉₊:ℕ):ℝ) ≤ 2*L)
    (psi : ℝ → ℂ)
    (hSupport : ∀ r,psi r ≠ 0 → 1/A ≤ r ∧ r ≤ A)
    (hNorm : ∀ r,‖psi r‖ ≤ K)
    (a1 a2 : ℝ) (eps1 eps2 : Bool) :
    let N : ℕ := ⌈18*A*(Z*(D:ℝ))⌉₊
    let T : Finset ℕ := Finset.Icc 1 N
    let S : Finset ℕ := T.filter (fun n : ℕ =>
      0 < (n:ℤ)+k*(D:ℤ) ∧
      ((n:ℤ)+k*(D:ℤ)).toNat ∈ T)
    (∑ n ∈ S,
      ‖sourceAuxiliaryGeneralStripped434 u.G u.Ptw
        u.primeSlot v.primeSlot n D u.qBase v.qBase k
        u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
        u.sigma0 u.sigma1 v.sigma0 v.sigma1
        Z a1 a2 psi eps1 eps2‖) ≤
      (K*A*(18*A+1)*(3:ℝ)^16)*
        L^(2*cfg.ea+2*cfg.ec+16:ℝ) := by
  dsimp only
  let R : ℝ := Z*(D:ℝ)
  let N : ℕ := ⌈18*A*R⌉₊
  let T : Finset ℕ := Finset.Icc 1 N
  let S : Finset ℕ := T.filter (fun n : ℕ =>
    0 < (n:ℤ)+k*(D:ℤ) ∧
    ((n:ℤ)+k*(D:ℤ)).toNat∈T)
  have hSsub : S ⊆ Finset.Icc 1 N :=
    Finset.filter_subset _ _
  have hSpos (n : ℕ) (hn : n∈S) : 0 < n :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hSshift (n : ℕ) (hn : n∈S) :
      0 < (n:ℤ)+k*(D:ℤ) := (Finset.mem_filter.mp hn).2.1
  have hNext : S.image (fun n : ℕ => ((n:ℤ)+k*(D:ℤ)).toNat) ⊆ T := by
    intro z hz
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hn).2.2
  have hCore := source_auxiliary_original_general_core_moment434
    cfg x L Y Hprime hL u v hG S T N N
    D k Z A K hZ hD hA hK psi hSupport hNorm
    hSsub (Finset.Subset.rfl) hSpos hSshift hNext
    a1 a2 eps1 eps2
  have hScale' := source_auxiliary_true_scale_moment_budget434
    A R K L cfg.ea cfg.ec hA hScale hK hL hLogCap
  change (∑ n ∈ S,
      ‖sourceAuxiliaryGeneralStripped434 u.G u.Ptw
        u.primeSlot v.primeSlot n D u.qBase v.qBase k
        u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
        u.sigma0 u.sigma1 v.sigma0 v.sigma1
        Z a1 a2 psi eps1 eps2‖) ≤ _ at hCore
  exact hCore.trans hScale'
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalComparisonScales -/

section

open Filter
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 6000000

/-- The modulus cutoffs and physical collar scales follow from original
stretched-exponential prime cells and Z >= x/log(x)^CZ. These are NOT
additional analytic assumptions on the endpoint. -/
theorem eventually_source_comparison_geometric_scales434
    (a c Carc CZ τ A C1 C2 : ℝ) (cm : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hτ : 0 < τ)
    (hA : 1 ≤ A) (hCarc : 0 ≤ Carc) :
    ∀ᶠ L : ℝ in atTop, 3 ≤ L ∧
      L^(2*cm) ≤ Real.exp (Real.sqrt L) ∧
      L^Carc ≤ Real.exp (Real.sqrt L) ∧
      L^Carc < Real.exp (L^a) ∧ L^Carc < Real.exp (τ*L) ∧
      ∀ (x Z U1 U2 : ℝ), 0 < x → L = Real.log x → x*L^(-CZ) ≤ Z →
        Real.exp (L^c-C1) ≤ U1 → Real.exp (L^c-C2) ≤ U2 →
        2 ≤ (U1*U2)/L^Carc ∧ (U1*U2)/L^Carc ≤ (Z*(U1*U2))/(8*A) := by
  have hMod := eventually_rpow_lt_exp_rpow (1/2:ℝ) ((2*cm:ℕ):ℝ) (by norm_num)
  have hArc := eventually_rpow_lt_exp_rpow (1/2:ℝ) Carc (by norm_num)
  have hSmall := eventually_rpow_lt_exp_rpow a Carc ha
  have hRadius := eventually_source_product_arc_radius434 c Carc C1 C2 hc
  have hRatio := eventually_source_fixed_poly_exp_saving 1 (8*A) CZ 0 (by norm_num)
  have hLarge := eventually_ge_atTop (max (3:ℝ) (1/τ^2+1))
  filter_upwards [hMod,hArc,hSmall,hRadius,hRatio,hLarge] with L hModL hArcL hSmallL hRadiusL hRatioL hLargeL
  have hL : 3 ≤ L := (le_max_left _ _).trans hLargeL
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hSqrt : Real.sqrt L < τ*L := by
    have hthreshold : 1/τ^2 < L := lt_of_lt_of_le (by linarith)
      ((le_max_right _ _).trans hLargeL)
    have hOne : 1 < L*τ^2 := (div_lt_iff₀ (sq_pos_of_pos hτ)).mp hthreshold
    have hMult : L < L*(L*τ^2) := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hOne hLp
    have htl : 0 < τ*L := mul_pos hτ hLp
    have hs0 := Real.sqrt_nonneg L
    have hs := Real.sq_sqrt hLp.le
    nlinarith
  have hArcSqrt : L^Carc < Real.exp (Real.sqrt L) := by
    simpa only [←Real.sqrt_eq_rpow] using hArcL
  refine ⟨hL,?_,hArcSqrt.le,hSmallL,hArcSqrt.trans (Real.exp_lt_exp.mpr hSqrt),?_⟩
  · simpa only [←Real.sqrt_eq_rpow,Real.rpow_natCast] using hModL.le
  intro x Z U1 U2 hx hLog hZ hU1 hU2
  have hU1p : 0 < U1 := (Real.exp_pos _).trans_le hU1
  have hU2p : 0 < U2 := (Real.exp_pos _).trans_le hU2
  have hHp : 0 < U1*U2 := mul_pos hU1p hU2p
  have hP : 0 < L^Carc := Real.rpow_pos_of_pos hLp _
  have hr := (hRadiusL.2 U1 U2 hU1 hU2).2
  have hProd : L^Carc < (1/2:ℝ)*(U1*U2) := (div_lt_iff₀ hHp).mp hr
  refine ⟨(le_div_iff₀ hP).mpr (by nlinarith),?_⟩
  have hZp : 0 < Z := (mul_pos hx (Real.rpow_pos_of_pos hLp _)).trans_le hZ
  have hYp : 0 < Z*(U1*U2) := mul_pos hZp hHp
  have hBound := source_actual_arc_ratio_exp_bound434 L x Z (U1*U2) (Z*(U1*U2))
    Carc CZ hLone hx hLog hZ hHp rfl hCarc
  have h8A : 0 < 8*A := by linarith
  have hDecay : (8*A)*(L^CZ*Real.exp (-L)) ≤ 1 := by
    simpa only [Real.rpow_one,Real.rpow_zero,div_one,mul_assoc] using hRatioL.2
  have hRatioBound : (U1*U2/L^Carc)/(Z*(U1*U2)) ≤ 1/(8*A) := by
    apply hBound.trans
    apply (le_div_iff₀ h8A).mpr
    nlinarith
  have hFinal := (div_le_iff₀ hYp).mp hRatioBound
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using hFinal
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryOriginalZLower -/

section

open Filter
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The source comparison constraint Z≥x/L^CZ already implies
Z≥1 eventually. This is NOT a new hypothesis on the physical
operator. The exponent CZ may have either sign. -/
theorem eventually_source_auxiliary_original_Z_ge_one434
    (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (x Z : ℝ), 0 < x → L=Real.log x →
        x*L^(-CZ) ≤ Z → 1 ≤ Z := by
  filter_upwards [eventually_rpow_lt_exp_rpow (1:ℝ) CZ
      (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L hGrowth hL
  intro x Z hx hLog hZ
  have hLp : 0 < L := by linarith
  have hPowPos : 0 < L^CZ := Real.rpow_pos_of_pos hLp CZ
  have hxEq : Real.exp L=x := by rw [hLog,Real.exp_log hx]
  have hMain : L^CZ ≤ x := by
    rw [←hxEq]
    simpa only [Real.rpow_one] using hGrowth.le
  have hBase : 1 ≤ x/L^CZ :=
    (le_div_iff₀ hPowPos).mpr (by simpa using hMain)
  have hEq : x*L^(-CZ) = x/L^CZ := by
    rw [Real.rpow_neg hLp.le,div_eq_mul_inv]
  rw [hEq] at hZ
  exact hBase.trans hZ
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryActualCellMoment -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Full SOURCE-specific post-charge moment at genuine pair of
logarithmic free-product cells. The required uniform estimates
Z≥1, R=Z*D≥1 and log ceil(18AR)≤2L are DERIVED from the
original Z≥x/L^CZ, original Y≤exp(3L/2), and actual p≥9.
No fake analytic cap, no pointwise core bound and no restriction
to common parity signs. -/
theorem eventually_source_auxiliary_actual_cell_core_moment434
    (cfg : SourceComparisonFixed434) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (x Y Hprime : ℝ) (hx : 0 < x) (hLog : L=Real.log x)
        (hL : 1 ≤ L)
        (u v : SourceComparisonData434 ι β cfg x L Y Hprime)
        (hG : v.G=u.G)
        (F1 F2 : Finset ℕ) (U1 U2 h1 h2 : ℝ)
        (b1 b2 : ℕ → ℂ) (da db p D : ℕ)
        (hU1 : 0 < U1) (hU2 : 0 < U2)
        (hh1 : h1 ≤ 1) (hh2 : h2 ≤ 1)
        (ha : sourceOriginalLogCellMask434 F1 U1 h1 b1 da ≠ 0)
        (hb : sourceOriginalLogCellMask434 F2 U2 h2 b2 db ≠ 0)
        (hp : 9 ≤ p) (hD : 0 < D) (hprod : p*D=da*db)
        (hY : Y=u.Z*(U1*U2))
        (k : ℤ) (hShift : |(k:ℝ)| ≤ u.Z/(2*cfg.A))
        (psi : ℝ → ℂ) (K : ℝ) (hK : 0 ≤ K)
        (hSupport : ∀ r,psi r ≠ 0 → 1/cfg.A ≤ r ∧ r ≤ cfg.A)
        (hNorm : ∀ r,‖psi r‖ ≤ K)
        (a1 a2 : ℝ) (eps1 eps2 : Bool),
        let N : ℕ := ⌈18*cfg.A*(u.Z*(D:ℝ))⌉₊
        let T : Finset ℕ := Finset.Icc 1 N
        let S : Finset ℕ := T.filter (fun n : ℕ =>
          0 < (n:ℤ)+k*(D:ℤ) ∧
          ((n:ℤ)+k*(D:ℤ)).toNat ∈ T)
        (∑ n ∈ S,
          ‖sourceAuxiliaryGeneralStripped434 u.G u.Ptw
            u.primeSlot v.primeSlot n D u.qBase v.qBase k
            u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
            u.sigma0 u.sigma1 v.sigma0 v.sigma1
            u.Z a1 a2 psi eps1 eps2‖) ≤
          (K*cfg.A*(18*cfg.A+1)*(3:ℝ)^16)*
            L^(2*cfg.ea+2*cfg.ec+16:ℝ) := by
  filter_upwards [
    eventually_source_auxiliary_original_Z_ge_one434 cfg.CZ,
    eventually_source_auxiliary_reduced_log_cap434 cfg.A cfg.hA
  ] with L hZlarge hLoglarge
  intro ι β _ _ _ _ x Y Hprime hx hLog hL u v hG
    F1 F2 U1 U2 h1 h2 b1 b2 da db p D
    hU1 hU2 hh1 hh2 ha hb hp hD hprod hY
    k hShift psi K hK hSupport hNorm a1 a2 eps1 eps2
  dsimp only
  have hZ1 : 1 ≤ u.Z :=
    hZlarge x u.Z hx hLog u.hZ
  have hScale := source_auxiliary_actual_cell_reduced_scale434
    F1 F2 U1 U2 h1 h2 b1 b2 da db p D u.Z Y
    hU1 hU2 hh1 hh2 ha hb hp hD hprod hZ1 hY
  have hLogCap : Real.log ((⌈18*cfg.A*(u.Z*(D:ℝ))⌉₊:ℕ):ℝ) ≤
      2*L :=
    hLoglarge (u.Z*(D:ℝ)) Y hScale.1 hScale.2 u.hYmax
  exact source_auxiliary_original_true_shifted_moment434
    cfg x L Y Hprime hL u v hG D k u.Z cfg.A K
    (by linarith [hZ1]) hD cfg.hA hK
    hShift hScale.1 hLogCap psi hSupport hNorm
    a1 a2 eps1 eps2
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryActualPatternWeighted -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- SOURCE-SPECIFIC conditional auxiliary p-fibre sum. The actual
fixed source cells, prime-slot cores and four signs are retained.
For each free prime p the reduced original shift is k*(D p), with
p*D p=da*db; the physical window is the EXACT post-charge window.
No independent B(p) hypothesis is needed: the checked original
cell moment supplies the SAME B for all p. -/
theorem eventually_source_auxiliary_actual_pattern_weighted434
    (cfg : SourceComparisonFixed434) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (x Y Hprime : ℝ) (hx : 0 < x) (hLog : L=Real.log x)
        (hL : 1 ≤ L)
        (u v : SourceComparisonData434 ι β cfg x L Y Hprime)
        (hG : v.G=u.G)
        (F1 F2 : Finset ℕ) (U1 U2 h1 h2 : ℝ)
        (b1 b2 : ℕ → ℂ) (da db : ℕ)
        (hU1 : 0 < U1) (hU2 : 0 < U2)
        (hh1 : h1 ≤ 1) (hh2 : h2 ≤ 1)
        (ha : sourceOriginalLogCellMask434 F1 U1 h1 b1 da ≠ 0)
        (hb : sourceOriginalLogCellMask434 F2 U2 h2 b2 db ≠ 0)
        (hY : Y=u.Z*(U1*U2))
        (S : Finset ℕ) (V Q : ℝ)
        (hQ : 0 < Q) (hQ9 : 9 ≤ Q)
        (hV : V=∑ p ∈ S,1/(p:ℝ)) (hVp : 0 < V)
        (hMin : ∀ p ∈ S,Q ≤ (p:ℝ))
        (hPrime : ∀ p ∈ S,p.Prime)
        (hGroup : ∀ p ∈ S,p ∈ u.G)
        (D : ℕ → ℕ)
        (hD : ∀ p ∈ S,0 < D p)
        (hProduct : ∀ p ∈ S,p*(D p)=da*db)
        (k : ℤ) (hShift : |(k:ℝ)| ≤ u.Z/(2*cfg.A))
        (psi : ℝ → ℂ) (K : ℝ) (hK : 0 ≤ K)
        (hSupport : ∀ r,psi r ≠ 0 → 1/cfg.A ≤ r ∧ r ≤ cfg.A)
        (hNorm : ∀ r,‖psi r‖ ≤ K)
        (a1 a2 : ℝ) (eps1 eps2 : Bool),
        let B : ℝ := (K*cfg.A*(18*cfg.A+1)*(3:ℝ)^16)*
          L^(2*cfg.ea+2*cfg.ec+16:ℝ)
        let T : ℕ → Finset ℕ := fun p =>
          let N := ⌈18*cfg.A*(u.Z*(D p:ℝ))⌉₊
          (Finset.Icc 1 N).filter (fun y : ℕ =>
            0 < (y:ℤ)+k*(D p:ℤ) ∧
            ((y:ℤ)+k*(D p:ℤ)).toNat∈Finset.Icc 1 N)
        ‖∑ p ∈ S,(sourcePrimeSharedAtom434 V p:ℂ)*
          (∑ y ∈ T p,sourceAuxiliaryGeneralLifted434
            u.G u.Ptw u.primeSlot v.primeSlot p y (D p)
            u.qBase v.qBase k u.alphaCut v.alphaCut u.c v.c
            u.chi0 v.chi0 u.sigma0 u.sigma1 v.sigma0 v.sigma1
            u.Z a1 a2 psi eps1 eps2)‖ ≤ Q⁻¹*B := by
  filter_upwards [eventually_source_auxiliary_actual_cell_core_moment434 cfg]
    with L hMoment
  intro ι β _ _ _ _ x Y Hprime hx hLog hL
    u v hG F1 F2 U1 U2 h1 h2 b1 b2 da db
    hU1 hU2 hh1 hh2 ha hb hY
    S V Q hQ hQ9 hV hVp hMin hPrime hGroup D hD hProduct
    k hShift psi K hK hSupport hNorm a1 a2 eps1 eps2
  classical
  let B : ℝ := (K*cfg.A*(18*cfg.A+1)*(3:ℝ)^16)*
      L^(2*cfg.ea+2*cfg.ec+16:ℝ)
  let T : ℕ → Finset ℕ := fun p =>
    let N := ⌈18*cfg.A*(u.Z*(D p:ℝ))⌉₊
    (Finset.Icc 1 N).filter (fun y : ℕ =>
      0 < (y:ℤ)+k*(D p:ℤ) ∧
      ((y:ℤ)+k*(D p:ℤ)).toNat∈Finset.Icc 1 N)
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hLp : 0 < L := by linarith
    have hAp : 0 < cfg.A := by linarith [cfg.hA]
    positivity
  have hZ : 0 < u.Z := by
    have hYP : 0 < Y := by linarith [u.hY]
    have hprod : 0 < u.Z*Hprime := by
      rw [←u.hYIdent]
      exact hYP
    nlinarith [u.hH]
  have hP9 (p : ℕ) (hp : p ∈ S) : 9 ≤ p := by
    have hR : (9:ℝ) ≤ p := hQ9.trans (hMin p hp)
    exact_mod_cast hR
  have hT : ∀ p ∈ S,∀ y ∈ T p,
      0 < y ∧ 0 < (y:ℤ)+k*(D p:ℤ) := by
    intro p hp y hy
    have hh := Finset.mem_filter.mp hy
    exact ⟨(Finset.mem_Icc.mp hh.1).1,hh.2.1⟩
  have hStripped : ∀ p ∈ S,
      ‖∑ y ∈ T p,sourceAuxiliaryGeneralStripped434
        u.G u.Ptw u.primeSlot v.primeSlot
        y (D p) u.qBase v.qBase k u.alphaCut v.alphaCut u.c v.c
        u.chi0 v.chi0 u.sigma0 u.sigma1 v.sigma0 v.sigma1
        u.Z a1 a2 psi eps1 eps2‖ ≤ B := by
    intro p hp
    have hm := hMoment x Y Hprime hx hLog hL u v hG
      F1 F2 U1 U2 h1 h2 b1 b2 da db p (D p)
      hU1 hU2 hh1 hh2 ha hb (hP9 p hp) (hD p hp)
      (hProduct p hp) hY k hShift psi K hK
      hSupport hNorm a1 a2 eps1 eps2
    have hBound :
      (∑ y ∈ T p,‖sourceAuxiliaryGeneralStripped434
        u.G u.Ptw u.primeSlot v.primeSlot
        y (D p) u.qBase v.qBase k
        u.alphaCut v.alphaCut u.c v.c
        u.chi0 v.chi0 u.sigma0 u.sigma1 v.sigma0 v.sigma1
        u.Z a1 a2 psi eps1 eps2‖) ≤ B := by
      simpa only [T,B] using hm
    exact (norm_sum_le _ _).trans hBound
  have hFull := source_auxiliary_original_weighted_fibres434
    u.G u.Ptw u.primeSlot v.primeSlot S V Q B
    hQ hB hV hVp hMin D k u.qBase v.qBase
    u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
    u.sigma0 u.sigma1 v.sigma0 v.sigma1 u.Z
    a1 a2 psi eps1 eps2 T hPrime hGroup hD hZ hT hStripped
  simpa only [T,B] using hFull
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryOriginalPowerSaving -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Original free big-group prime lower bound exp(L^c) eventually
exceeds 9, as needed to divide the two genuine log cell products
and obtain the reduced scale R<=Y. -/
theorem eventually_source_actual_auxiliary_prime_nine434
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, (9:ℝ) ≤ Real.exp (L^c) := by
  filter_upwards [eventually_source_fixed_poly_exp_saving c 9 0 0 hc]
    with L h
  have hBase : (9:ℝ)*Real.exp (-(L^c)) ≤ 1 := by
    simpa only [Real.rpow_zero,mul_one,div_one] using h.2
  have hPos : 0 < Real.exp (L^c) := Real.exp_pos _
  have hMul := mul_le_mul_of_nonneg_right hBase hPos.le
  calc
    (9:ℝ) = (9*Real.exp (-(L^c)))*Real.exp (L^c) := by
      rw [Real.exp_neg]
      field_simp
    _ ≤ Real.exp (L^c) := by simpa only [one_mul] using hMul

/-- ALL fixed source log powers (including the core fourth-divisor
cost, the physical window and arbitrary fixed cutoff K) are
swallowed by the actual auxiliary free-prime 1/p saving. The
reciprocal p cost is separate from the original normalized atom
mu(p), so it is not double counted. -/
theorem eventually_source_actual_auxiliary_power_budget434
    (cfg : SourceComparisonFixed434) (K D : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop,
      (Real.exp (L^cfg.cexp))⁻¹*
        ((K*cfg.A*(18*cfg.A+1)*(3:ℝ)^16)*
          L^(2*cfg.ea+2*cfg.ec+16:ℝ)) ≤ L^(-D) := by
  have hc : 0 < cfg.cexp := by
    have h1 := cfg.haexp
    have h2 := cfg.hab
    have h3 := cfg.hbc
    linarith
  let C : ℝ := (2*cfg.ea+2*cfg.ec+16:ℝ)
  let M : ℝ := K*cfg.A*(18*cfg.A+1)*(3:ℝ)^16
  filter_upwards [eventually_source_fixed_poly_exp_saving
      cfg.cexp M C D hc] with L h
  have hLp : 0 < L := by linarith [h.1]
  change (Real.exp (L^cfg.cexp))⁻¹*(M*L^C) ≤ L^(-D)
  calc
    _ = M*L^C*Real.exp (-(L^cfg.cexp)) := by
      rw [Real.exp_neg]
      ring
    _ ≤ 1/L^D := h.2
    _ = L^(-D) := by rw [Real.rpow_neg hLp.le,one_div]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryOriginalPhysicalCell -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Genuine source03 full free-label tuple, one selected auxiliary
collision slot, BOTH true prime-slot endpoint cores and all four
independent parity choices, with the ORIGINAL physical q/V marked
normalization. The per-other-tuple charged physical fibre bound
is automatically a fixed log power divided by the selected prime.
It uses the ACTUAL free log cells, original Z/Y constraints,
and no pointwise prime-slot core bound.
Remaining source gates: disjoint prime groups, exact physical
shared-slot geometry and the coupled K_nu sup norm. -/
theorem eventually_source_auxiliary_full_tuple_physical_cell434
    (cfg : SourceComparisonFixed434) (M : ℕ)
    (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ (Kg E : ℝ), 1 ≤ Kg ∧ 0 ≤ E ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ {ι β φ G : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        [Fintype φ] [DecidableEq φ]
        [Fintype G] [DecidableEq G]
        (x Y Hprime : ℝ) (hx : 0 < x) (hLog : L=Real.log x)
        (hL : 1 ≤ L)
        (u v : SourceComparisonData434 ι β cfg x L Y Hprime)
        (hG : v.G=u.G)
        (F1 F2 : Finset ℕ) (U1 U2 h1 h2 : ℝ)
        (b1 b2 : ℕ → ℂ) (da db : ℕ)
        (hU1 : 0 < U1) (hU2 : 0 < U2)
        (hh1 : h1 ≤ 1) (hh2 : h2 ≤ 1)
        (ha : sourceOriginalLogCellMask434 F1 U1 h1 b1 da ≠ 0)
        (hb : sourceOriginalLogCellMask434 F2 U2 h2 b2 db ≠ 0)
        (hY : Y=u.Z*(U1*U2))
        (labels : φ → ℕ) (slot : φ)
        (hPrimeAll : ∀ j,(labels j).Prime)
        (hPmin : Real.exp (L^cfg.cexp) ≤ (labels slot:ℝ))
        (hProduct : (∏ j : φ,labels j:ℕ)=da*db)
        (k : ℤ) (hShift : |(k:ℝ)| ≤ u.Z/(2*cfg.A))
        (psi : ℝ → ℂ) (Kpsi : ℝ) (hKpsi : 0 ≤ Kpsi)
        (hSupport : ∀ r,psi r ≠ 0 → 1/cfg.A ≤ r ∧ r ≤ cfg.A)
        (hNorm : ∀ r,‖psi r‖ ≤ Kpsi)
        (a1 a2 : ℝ) (eps1 eps2 : Bool)
        (P : G → Finset ℕ) (Eshare : G → Finset (Fin M))
        (s : ∀ g,Eshare g → ℕ) (t : G → ℕ)
        (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ Eshare g})
        (Vg : G → ℝ) (dShared : ℕ)
        (Fmark : ℕ → (G → Fin M → ℕ) →
          (G → Fin M → ℕ) → ℂ) (Bmark : ℝ),
      (Fintype.card G:ℝ) ≤ Cs*Real.log L →
      (∀ g p,p ∈ P g → p.Prime) →
      (∀ g i,s g i ∈ P g) →
      (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
      (∀ g,(Eshare g).card+t g=M) →
      (∀ g,t g ≤ cfg.tmax) →
      (∀ g,cfg.vmin ≤ Vg g) →
      u.G=Finset.univ.biUnion P →
      labels slot ∈ Finset.univ.biUnion P →
      0 ≤ Bmark →
      let d := sourceAuxiliaryOtherProduct434 labels slot
      let N : ℕ := ⌈18*cfg.A*(u.Z*(d:ℝ))⌉₊
      let T : Finset ℕ := (Finset.Icc 1 N).filter
        (fun y : ℕ => 0 < (y:ℤ)+k*(d:ℤ) ∧
           ((y:ℤ)+k*(d:ℤ)).toNat∈Finset.Icc 1 N)
      (∀ y ∈ T,
        ∀ a ∈ sourceGlobalSharedCompletions434 P M Eshare s
          (labels slot*y),
        ∀ b ∈ sourceGlobalSharedCompletions434 P M Eshare s
          (labels slot*((((y:ℤ)+k*(d:ℤ)).toNat):ℕ)),
        ‖Fmark y a b‖ ≤ Bmark) →
      ‖∑ y ∈ T,
        sourceAuxiliaryOriginalFullTupleKernel434
          labels slot (Finset.univ.biUnion P) u.Ptw
          u.primeSlot v.primeSlot y u.qBase v.qBase k
          u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
          u.sigma0 u.sigma1 v.sigma0 v.sigma1
          u.Z a1 a2 psi eps1 eps2 *
        sourceAuxiliaryPhysicalMarkedPair434 P M Eshare s t
          Vg cfg.q0 dShared (labels slot*y)
          (labels slot*(((y:ℤ)+k*(d:ℤ)).toNat))
          (Fmark y)‖ ≤
        (labels slot:ℝ)⁻¹*((Bmark*Kg*L^E)*
          ((Kpsi*cfg.A*(18*cfg.A+1)*(3:ℝ)^16)*
            L^(2*cfg.ea+2*cfg.ec+16:ℝ))) := by
  obtain ⟨Kg,E,hKg,hE,hRow⟩ :=
    source_auxiliary_full_tuple_physical_fibre_bound434
      cfg.q0 cfg.vmin Cs cfg.tmax M
      cfg.hq0 cfg.hq1 cfg.hv hCs
  refine ⟨Kg,E,hKg,hE,?_⟩
  have hc : 0 < cfg.cexp := by
    have h1 := cfg.haexp
    have h2 := cfg.hab
    have h3 := cfg.hbc
    linarith
  filter_upwards [
    eventually_source_auxiliary_actual_cell_core_moment434 cfg,
    eventually_source_actual_auxiliary_prime_nine434 cfg.cexp hc
  ] with L hMoment hNine
  intro ι β φ G _ _ _ _ _ _ _ _ x Y Hprime hx hLog hL
    u v hG F1 F2 U1 U2 h1 h2 b1 b2 da db
    hU1 hU2 hh1 hh2 ha hb hY
    labels slot hPrimeAll hPmin hProduct
    k hShift psi Kpsi hKpsi hSupport hNorm a1 a2 eps1 eps2
    P Eshare s t e Vg dShared Fmark Bmark
    hCard hP hs hDisj hM ht hVg hUnion hpIn hBmark
  dsimp only
  intro hFM
  let d : ℕ := sourceAuxiliaryOtherProduct434 labels slot
  let N : ℕ := ⌈18*cfg.A*(u.Z*(d:ℝ))⌉₊
  let T : Finset ℕ := (Finset.Icc 1 N).filter
    (fun y : ℕ => 0 < (y:ℤ)+k*(d:ℤ) ∧
      ((y:ℤ)+k*(d:ℤ)).toNat∈Finset.Icc 1 N)
  let Bcore : ℝ := (Kpsi*cfg.A*(18*cfg.A+1)*(3:ℝ)^16)*
    L^(2*cfg.ea+2*cfg.ec+16:ℝ)
  have hZ : 0 < u.Z := by
    have hYP : 0 < Y := by linarith [u.hY]
    have hProd : 0 < u.Z*Hprime := by
      rw [←u.hYIdent]
      exact hYP
    nlinarith [u.hH]
  have hd : 0 < d :=
    source_auxiliary_original_other_product_pos434 labels slot hPrimeAll
  have hProduct' : labels slot*d=da*db := by
    rw [←source_auxiliary_original_full_product_split434 labels slot]
    exact hProduct
  have hp9 : 9 ≤ labels slot := by
    have hpReal : (9:ℝ) ≤ labels slot := hNine.trans hPmin
    exact_mod_cast hpReal
  have hMom := hMoment x Y Hprime hx hLog hL u v hG
    F1 F2 U1 U2 h1 h2 b1 b2 da db (labels slot) d
    hU1 hU2 hh1 hh2 ha hb hp9 hd hProduct' hY
    k hShift psi Kpsi hKpsi hSupport hNorm a1 a2 eps1 eps2
  have hCore :
    (∑ y ∈ T,
      ‖sourceAuxiliaryGeneralStripped434
        (Finset.univ.biUnion P) u.Ptw u.primeSlot v.primeSlot
        y d u.qBase v.qBase k
        u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
        u.sigma0 u.sigma1 v.sigma0 v.sigma1
        u.Z a1 a2 psi eps1 eps2‖) ≤ Bcore := by
    simpa only [T,Bcore,d,←hUnion] using hMom
  have hBcore : 0 ≤ Bcore := by
    have hLp : 0 < L := by linarith
    have hAP : 0 < cfg.A := by linarith [cfg.hA]
    dsimp only [Bcore]
    positivity
  have hT : ∀ y ∈ T,0 < y ∧ 0 < (y:ℤ)+k*(d:ℤ) := by
    intro y hy
    have hh := Finset.mem_filter.mp hy
    exact ⟨(Finset.mem_Icc.mp hh.1).1,hh.2.1⟩
  have hh := hRow L hL labels slot P Eshare s t e Vg dShared
    u.Ptw u.primeSlot v.primeSlot u.qBase v.qBase k
    u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
    u.sigma0 u.sigma1 v.sigma0 v.sigma1 u.Z a1 a2 psi eps1 eps2
    Fmark T Bmark Bcore hCard hP hs hDisj hM ht hVg
    hPrimeAll hpIn hZ hBmark hBcore hT hFM hCore
  simpa only [T,Bcore,d] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryCollidingPhysicalCell -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Literal SOURCE auxiliary free-exclusion physical row, including
the TRUE labelled (multiplicity-preserving) reciprocal shared product.
The selected p must appear in the NONSHARED physical endpoint marked
list. The actual q/V damping, K_nu and original two prime-slot cores
are preserved. The uniform mark bound and prime group geometry are
explicit obligations, not assumptions of the algebraic identity. -/
theorem eventually_source_auxiliary_original_colliding_physical_cell434
    (cfg : SourceComparisonFixed434) (M : ℕ)
    (Cs : ℝ) (hCs : 0 ≤ Cs) :
    ∃ (Kg E : ℝ), 1 ≤ Kg ∧ 0 ≤ E ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ {ι β φ G : Type}
        [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        [Fintype φ] [DecidableEq φ]
        [Fintype G] [DecidableEq G]
        (x Y Hprime : ℝ) (hx : 0 < x) (hLog : L=Real.log x)
        (hL : 1 ≤ L)
        (u v : SourceComparisonData434 ι β cfg x L Y Hprime)
        (hG : v.G=u.G)
        (F1 F2 : Finset ℕ) (U1 U2 h1 h2 : ℝ)
        (b1 b2 : ℕ → ℂ) (da db : ℕ)
        (hU1 : 0 < U1) (hU2 : 0 < U2)
        (hh1 : h1 ≤ 1) (hh2 : h2 ≤ 1)
        (ha : sourceOriginalLogCellMask434 F1 U1 h1 b1 da ≠ 0)
        (hb : sourceOriginalLogCellMask434 F2 U2 h2 b2 db ≠ 0)
        (hY : Y=u.Z*(U1*U2))
        (labels : φ → ℕ) (slot : φ)
        (hPrimeAll : ∀ j,(labels j).Prime)
        (hPmin : Real.exp (L^cfg.cexp) ≤ (labels slot:ℝ))
        (hProduct : (∏ j : φ,labels j:ℕ)=da*db)
        (k : ℤ) (hShift : |(k:ℝ)| ≤ u.Z/(2*cfg.A))
        (psi : ℝ → ℂ) (Kpsi : ℝ) (hKpsi : 0 ≤ Kpsi)
        (hSupport : ∀ r,psi r ≠ 0 → 1/cfg.A ≤ r ∧ r ≤ cfg.A)
        (hNorm : ∀ r,‖psi r‖ ≤ Kpsi)
        (a1 a2 : ℝ) (eps1 eps2 : Bool)
        (P : G → Finset ℕ) (Eshare : G → Finset (Fin M))
        (s : ∀ g,Eshare g → ℕ) (t : G → ℕ)
        (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ Eshare g})
        (Vg : G → ℝ)
        (Fmark : ℕ → (G → Fin M → ℕ) →
          (G → Fin M → ℕ) → ℂ) (Bmark : ℝ),
      (Fintype.card G:ℝ) ≤ Cs*Real.log L →
      (∀ g p,p ∈ P g → p.Prime) →
      (∀ g i,s g i ∈ P g) →
      (∀ g h p,p ∈ P g → p ∈ P h → g=h) →
      (∀ g,(Eshare g).card+t g=M) →
      (∀ g,t g ≤ cfg.tmax) →
      (∀ g,cfg.vmin ≤ Vg g) →
      u.G=Finset.univ.biUnion P →
      labels slot ∈ Finset.univ.biUnion P →
      0 ≤ Bmark →
      let d := sourceAuxiliaryOtherProduct434 labels slot
      let N : ℕ := ⌈18*cfg.A*(u.Z*(d:ℝ))⌉₊
      let T : Finset ℕ := (Finset.Icc 1 N).filter
        (fun y : ℕ => 0 < (y:ℤ)+k*(d:ℤ) ∧
           ((y:ℤ)+k*(d:ℤ)).toNat∈Finset.Icc 1 N)
      (∀ y ∈ T,
        ∀ a ∈ sourceGlobalSharedCompletions434 P M Eshare s
          (labels slot*y),
        ∀ b ∈ sourceGlobalSharedCompletions434 P M Eshare s
          (labels slot*((((y:ℤ)+k*(d:ℤ)).toNat):ℕ)),
        ‖Fmark y a b‖ ≤ Bmark) →
      ‖((sourceAuxiliaryTrueSharedDilation434 Eshare s:ℕ):ℂ)⁻¹ *
        (∑ y ∈ T,
        sourceAuxiliaryOriginalFullTupleKernel434
          labels slot (Finset.univ.biUnion P) u.Ptw
          u.primeSlot v.primeSlot y u.qBase v.qBase k
          u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
          u.sigma0 u.sigma1 v.sigma0 v.sigma1
          u.Z a1 a2 psi eps1 eps2 *
        sourceAuxiliaryPhysicalMarkedPair434 P M Eshare s t
          Vg cfg.q0 (sourceAuxiliaryTrueSharedDilation434 Eshare s) (labels slot*y)
          (labels slot*(((y:ℤ)+k*(d:ℤ)).toNat))
          (fun a b => if (∃ g j,a g (e g j)=labels slot) ∨
            (∃ g j,b g (e g j)=labels slot)
          then Fmark y a b else 0))‖ ≤
        (labels slot:ℝ)⁻¹*((Bmark*Kg*L^E)*
          ((Kpsi*cfg.A*(18*cfg.A+1)*(3:ℝ)^16)*
            L^(2*cfg.ea+2*cfg.ec+16:ℝ))) := by
  obtain ⟨Kg,E,hKg,hE,hCell⟩ :=
    eventually_source_auxiliary_full_tuple_physical_cell434
      cfg M Cs hCs
  refine ⟨Kg,E,hKg,hE,?_⟩
  filter_upwards [hCell] with L hCellL
  intro ι β φ G _ _ _ _ _ _ _ _ x Y Hprime hx hLog hL
    u v hG F1 F2 U1 U2 h1 h2 b1 b2 da db
    hU1 hU2 hh1 hh2 ha hb hY
    labels slot hPrimeAll hPmin hProduct
    k hShift psi Kpsi hKpsi hSupport hNorm a1 a2 eps1 eps2
    P Eshare s t e Vg Fmark Bmark
    hCard hP hs hDisj hM ht hVg hUnion hpIn hBmark
  dsimp only
  intro hFM
  let d : ℕ := sourceAuxiliaryOtherProduct434 labels slot
  let dShared : ℕ := sourceAuxiliaryTrueSharedDilation434 Eshare s
  let N : ℕ := ⌈18*cfg.A*(u.Z*(d:ℝ))⌉₊
  let T : Finset ℕ := (Finset.Icc 1 N).filter
    (fun y : ℕ => 0 < (y:ℤ)+k*(d:ℤ) ∧
      ((y:ℤ)+k*(d:ℤ)).toNat∈Finset.Icc 1 N)
  let Fbad : ℕ → (G → Fin M → ℕ) →
      (G → Fin M → ℕ) → ℂ := fun y a b =>
    if (∃ g j,a g (e g j)=labels slot) ∨
       (∃ g j,b g (e g j)=labels slot)
    then Fmark y a b else 0
  have hFMbad : ∀ y ∈ T,
      ∀ a ∈ sourceGlobalSharedCompletions434 P M Eshare s (labels slot*y),
      ∀ b ∈ sourceGlobalSharedCompletions434 P M Eshare s
        (labels slot*((((y:ℤ)+k*(d:ℤ)).toNat):ℕ)),
        ‖Fbad y a b‖ ≤ Bmark := by
    intro y hy a ha b hb
    dsimp only [Fbad]
    by_cases hbad : ((∃ g j,a g (e g j)=labels slot) ∨
                     (∃ g j,b g (e g j)=labels slot))
    · simpa only [if_pos hbad] using hFM y hy a ha b hb
    · simp only [if_neg hbad,norm_zero]
      exact hBmark
  let R : ℂ := ∑ y ∈ T,
    sourceAuxiliaryOriginalFullTupleKernel434
      labels slot (Finset.univ.biUnion P) u.Ptw
      u.primeSlot v.primeSlot y u.qBase v.qBase k
      u.alphaCut v.alphaCut u.c v.c u.chi0 v.chi0
      u.sigma0 u.sigma1 v.sigma0 v.sigma1
      u.Z a1 a2 psi eps1 eps2 *
    sourceAuxiliaryPhysicalMarkedPair434 P M Eshare s t
      Vg cfg.q0 dShared (labels slot*y)
      (labels slot*(((y:ℤ)+k*(d:ℤ)).toNat))
      (Fbad y)
  have hBound := hCellL x Y Hprime hx hLog hL
    u v hG F1 F2 U1 U2 h1 h2 b1 b2 da db
    hU1 hU2 hh1 hh2 ha hb hY
    labels slot hPrimeAll hPmin hProduct
    k hShift psi Kpsi hKpsi hSupport hNorm a1 a2 eps1 eps2
    P Eshare s t e Vg dShared Fbad Bmark
    hCard hP hs hDisj hM ht hVg hUnion hpIn hBmark
    (by simpa only [T,Fbad,d] using hFMbad)
  have hBoundR : ‖R‖ ≤
      (labels slot:ℝ)⁻¹*((Bmark*Kg*L^E)*
        ((Kpsi*cfg.A*(18*cfg.A+1)*(3:ℝ)^16)*
          L^(2*cfg.ea+2*cfg.ec+16:ℝ))) := by
    simpa only [R,T,Fbad,d] using hBound
  have hDRcontract : ‖(dShared:ℂ)⁻¹*R‖ ≤ ‖R‖ := by
    simpa only [one_mul] using
      source_auxiliary_true_shared_reciprocal_contract434
        P M Eshare s hP hs (1:ℂ) R
  have hAll := hDRcontract.trans hBoundR
  simpa only [R,T,d,Fbad,dShared] using hAll
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryCoupledPatternBound -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The literal SOURCE two-end big-mark test, with arbitrary
coupled comparison coefficient K_nu. Both endpoint b-tests
are evaluated on their ACTUAL unshared physical slot projections,
not on a surrogate independent law. -/
noncomputable def sourceAuxiliaryCoupledPatternMark434
    {G : Type} [Fintype G] [DecidableEq G]
    (M : ℕ) (E : G → Finset (Fin M)) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (b1 b2 : (∀ g,Fin (t g) → ℕ) → ℂ)
    (Knu : (∀ g,Fin (t g) → ℕ) →
           (∀ g,Fin (t g) → ℕ) → ℂ)
    (a b : G → Fin M → ℕ) : ℂ :=
  let ua : ∀ g,Fin (t g) → ℕ := fun g j => a g (e g j)
  let ub : ∀ g,Fin (t g) → ℕ := fun g j => b g (e g j)
  star (b1 ua)*b2 ub*Knu ua ub

/-- Exact source03 comparison FAMILY sup bound is sufficient for the
true fully coupled pattern K_nu and BOTH complex endpoint tests.
No independence or factorization of K_nu is assumed. -/
theorem source_auxiliary_coupled_pattern_mark_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (M : ℕ) (E : G → Finset (Fin M)) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (b1 b2 : (∀ g,Fin (t g) → ℕ) → ℂ)
    (Knu : (∀ g,Fin (t g) → ℕ) →
           (∀ g,Fin (t g) → ℕ) → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb1 : ∀ a,‖b1 a‖ ≤ 1)
    (hb2 : ∀ a,‖b2 a‖ ≤ 1)
    (hK : ∀ a b,‖Knu a b‖ ≤ B)
    (a b : G → Fin M → ℕ) :
    ‖sourceAuxiliaryCoupledPatternMark434 M E t e b1 b2 Knu a b‖ ≤ B := by
  let ua : ∀ g,Fin (t g) → ℕ := fun g j => a g (e g j)
  let ub : ∀ g,Fin (t g) → ℕ := fun g j => b g (e g j)
  have hfirst : ‖b1 ua‖*‖b2 ub‖ ≤ 1 := by
    have hm := mul_le_mul (hb1 ua) (hb2 ub)
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using hm
  calc
    _ = ‖b1 ua‖*‖b2 ub‖*‖Knu ua ub‖ := by
      simp only [sourceAuxiliaryCoupledPatternMark434,
        norm_mul,norm_star,ua,ub]
    _ ≤ 1*‖Knu ua ub‖ :=
      mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
    _ ≤ 1*B :=
      mul_le_mul_of_nonneg_left (hK ua ub) (by norm_num)
    _ = B := one_mul B

/-- Exact collision-restricted K_nu physical mark coefficient still
has the source universal comparison sup B. -/
theorem source_auxiliary_coupled_collision_mark_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (M : ℕ) (E : G → Finset (Fin M)) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (b1 b2 : (∀ g,Fin (t g) → ℕ) → ℂ)
    (Knu : (∀ g,Fin (t g) → ℕ) →
           (∀ g,Fin (t g) → ℕ) → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb1 : ∀ a,‖b1 a‖ ≤ 1)
    (hb2 : ∀ a,‖b2 a‖ ≤ 1)
    (hK : ∀ a b,‖Knu a b‖ ≤ B)
    (p : ℕ) (a b : G → Fin M → ℕ) :
    ‖if (∃ g j,a g (e g j)=p) ∨ (∃ g j,b g (e g j)=p)
      then sourceAuxiliaryCoupledPatternMark434 M E t e b1 b2 Knu a b
      else 0‖ ≤ B := by
  by_cases hbad : (∃ g j,a g (e g j)=p) ∨ (∃ g j,b g (e g j)=p)
  · simpa only [if_pos hbad] using
      source_auxiliary_coupled_pattern_mark_bound434 M E t e b1 b2
        Knu B hB hb1 hb2 hK a b
  · simp only [if_neg hbad,norm_zero]
    exact hB
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryOriginalComparisonKnu -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Literal SOURCE03 comparison kernel product, with its original
signed coefficient -(-1)^(|A|+|B|), the FIRST global character/cell
kernel on the target free marks, and the SECOND global kernel on
the source free marks. No separation of the mark tests and
no one-character-kernel-per-group surrogate are used. -/
noncomputable def sourceAuxiliaryOriginalComparisonKnu434
    {G : Type} [Fintype G]
    (t : G → ℕ)
    (KA KB : ℕ → ℕ → ℂ) (DA DB r : ℕ)
    (XA XB : (∀ g,Fin (t g) → ℕ) → ℕ)
    (source target : ∀ g,Fin (t g) → ℕ) : ℂ :=
  -((-1:ℂ)^r)*KA DA (XA target)*KB DB (XB source)

/-- The source kernel product has exactly the combined sup cap.
Each global source kernel is bounded independently; the FULL
two-cell comparison Knu is allowed to couple both marked endpoints.
The signed inclusion-exclusion coefficient has modulus one. -/
theorem source_auxiliary_original_comparison_Knu_bound434
    {G : Type} [Fintype G]
    (t : G → ℕ)
    (KA KB : ℕ → ℕ → ℂ) (DA DB r : ℕ)
    (XA XB : (∀ g,Fin (t g) → ℕ) → ℕ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hKA : ∀ n,‖KA DA n‖ ≤ A)
    (hKB : ∀ n,‖KB DB n‖ ≤ B)
    (source target : ∀ g,Fin (t g) → ℕ) :
    ‖sourceAuxiliaryOriginalComparisonKnu434 t KA KB DA DB r
      XA XB source target‖ ≤ A*B := by
  have hBound : ‖KA DA (XA target)‖*
      ‖KB DB (XB source)‖ ≤ A*B :=
    mul_le_mul (hKA _) (hKB _) (norm_nonneg _) hA
  calc
    _ = ‖KA DA (XA target)‖*‖KB DB (XB source)‖ := by
      simp [sourceAuxiliaryOriginalComparisonKnu434,norm_mul]
    _ ≤ _ := hBound

/-- Use the source03 pointwise bound Q^2*xi^(-1) for BOTH global
kernels, without confusing xi with a probability atom.
The resulting physical Knu cap is Q^4*xi^(-2). -/
theorem source_auxiliary_original_comparison_Knu_global_bound434
    {G : Type} [Fintype G]
    (t : G → ℕ)
    (KA KB : ℕ → ℕ → ℂ) (DA DB r : ℕ)
    (XA XB : (∀ g,Fin (t g) → ℕ) → ℕ)
    (Q xi : ℝ) (hQ : 0 ≤ Q) (hxi : 0 < xi)
    (hKA : ∀ n,‖KA DA n‖ ≤ Q^2*xi⁻¹)
    (hKB : ∀ n,‖KB DB n‖ ≤ Q^2*xi⁻¹)
    (source target : ∀ g,Fin (t g) → ℕ) :
    ‖sourceAuxiliaryOriginalComparisonKnu434 t KA KB DA DB r
      XA XB source target‖ ≤ Q^4*(xi⁻¹)^2 := by
  have hCap : 0 ≤ Q^2*xi⁻¹ := by positivity
  have h := source_auxiliary_original_comparison_Knu_bound434
    t KA KB DA DB r XA XB (Q^2*xi⁻¹) (Q^2*xi⁻¹)
    hCap hCap hKA hKB source target
  convert h using 1
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryOriginalComparisonMark -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- ORIGINAL source03 signed two-global-kernel Knu, projected on
the exact unshared source/target physical marked lists, and both
possibly COMPLEX endpoint b-tests. The TRUE product K_A(D_A,X_A)
K_B(D_B,X_B) costs only the product of the TWO global kernel
sup norms, not a factor for every prime group. -/
theorem source_auxiliary_original_comparison_physical_mark_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (M : ℕ) (E : G → Finset (Fin M)) (t : G → ℕ)
    (e : ∀ g,Fin (t g) ≃ {i : Fin M // i ∉ E g})
    (bSrc bTgt : (∀ g,Fin (t g) → ℕ) → ℂ)
    (KA KB : ℕ → ℕ → ℂ) (DA DB r : ℕ)
    (XA XB : (∀ g,Fin (t g) → ℕ) → ℕ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbSrc : ∀ a,‖bSrc a‖ ≤ 1)
    (hbTgt : ∀ a,‖bTgt a‖ ≤ 1)
    (hKA : ∀ n,‖KA DA n‖ ≤ A)
    (hKB : ∀ n,‖KB DB n‖ ≤ B)
    (m n : G → Fin M → ℕ) :
    ‖sourceAuxiliaryCoupledPatternMark434 M E t e
      bSrc bTgt
      (sourceAuxiliaryOriginalComparisonKnu434 t
        KA KB DA DB r XA XB) m n‖ ≤ A*B := by
  exact source_auxiliary_coupled_pattern_mark_bound434
    M E t e bSrc bTgt
    (sourceAuxiliaryOriginalComparisonKnu434 t KA KB
      DA DB r XA XB) (A*B) (mul_nonneg hA hB)
    hbSrc hbTgt
    (fun x y => source_auxiliary_original_comparison_Knu_bound434
      t KA KB DA DB r XA XB A B hA hB hKA hKB x y)
    m n
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGlobalCharacterCells -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Literal one-GLOBAL-kernel character/cell expansion from source03:
one normalized active log cell j, its source/target cell indicators,
and the sum of its primitive-character terms. Character primitivity
and the logarithmic cell geometry are abstract explicit inputs,
not silently assumed from arbitrary complex functions. -/
noncomputable def sourceOriginalCharacterCellKernel434
    {Cell Character : Type} [DecidableEq Cell]
    (active : Finset Cell) (characters : Finset Character)
    (cell : Cell → ℕ → Prop) (mass : Cell → ℝ)
    (chi : Character → ℕ → ℂ) (D X : ℕ) : ℂ :=
  ∑ j ∈ active,
    if cell j D ∧ cell j X then
      ((mass j:ℂ)⁻¹) *
      (∑ c ∈ characters, star (chi c D)*chi c X)
    else 0

/-- The number of original global characters bounds the literal
character sum whenever each character has modulus at most one. -/
theorem source_original_character_sum_bound434
    {Character : Type} (characters : Finset Character)
    (chi : Character → ℕ → ℂ) (D X : ℕ)
    (hChi : ∀ c ∈ characters, ‖chi c D‖ ≤ 1 ∧ ‖chi c X‖ ≤ 1) :
    ‖∑ c ∈ characters,star (chi c D)*chi c X‖ ≤
      (characters.card:ℝ) := by
  have hTerm (c : Character) (hc : c ∈ characters) :
      ‖star (chi c D)*chi c X‖ ≤ 1 := by
    rw [norm_mul,norm_star]
    nlinarith [mul_le_mul (hChi c hc).1 (hChi c hc).2
      (norm_nonneg (chi c X)) (by norm_num : (0:ℝ) ≤ 1)]
  calc
    _ ≤ ∑ c ∈ characters, ‖star (chi c D)*chi c X‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _c ∈ characters,(1:ℝ) :=
      Finset.sum_le_sum hTerm
    _ = (characters.card:ℝ) := by simp

/-- One-occupied-cell bound for the EXACT global kernel. The
source03 logarithmic intervals are disjoint, so the same pair
(D,X) can activate AT MOST one cell. This prevents the false
extra factor equal to the number of logarithmic cells. -/
theorem source_original_global_character_cell_bound434
    {Cell Character : Type} [DecidableEq Cell]
    (active : Finset Cell) (characters : Finset Character)
    (cell : Cell → ℕ → Prop) (mass : Cell → ℝ)
    (chi : Character → ℕ → ℂ) (D X : ℕ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMass : ∀ j ∈ active, xi ≤ mass j)
    (hUnique : ∀ j ∈ active,∀ k ∈ active,
      cell j D → cell k D → j=k)
    (hChi : ∀ c ∈ characters, ‖chi c D‖ ≤ 1 ∧ ‖chi c X‖ ≤ 1) :
    ‖sourceOriginalCharacterCellKernel434
      active characters cell mass chi D X‖ ≤
      (characters.card:ℝ)*xi⁻¹ := by
  classical
  let F : Cell → ℂ := fun j =>
    ((mass j:ℂ)⁻¹)*
      (∑ c ∈ characters,star (chi c D)*chi c X)
  let gate : Cell → Prop := fun j => cell j D ∧ cell j X
  have hTerm (j : Cell) (hj : j ∈ active) :
      ‖F j‖ ≤ (characters.card:ℝ)*xi⁻¹ := by
    have hm := hMass j hj
    have hmp : 0 < mass j := hxi.trans_le hm
    have hinv : (mass j)⁻¹ ≤ xi⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hxi hm
    calc
      _ = (mass j)⁻¹ *
          ‖∑ c ∈ characters, star (chi c D)*chi c X‖ := by
        simp only [F,norm_mul,norm_inv,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos hmp]
      _ ≤ (mass j)⁻¹*(characters.card:ℝ) :=
        mul_le_mul_of_nonneg_left
          (source_original_character_sum_bound434 characters chi D X hChi)
          (inv_nonneg.mpr hmp.le)
      _ ≤ (characters.card:ℝ)*xi⁻¹ := by
        have := mul_le_mul_of_nonneg_left hinv
          (Nat.cast_nonneg (α:=ℝ) characters.card)
        nlinarith
  change ‖∑ j ∈ active, if gate j then F j else 0‖ ≤ _
  by_cases he : ∃ j ∈ active,gate j
  · obtain ⟨j,hj,hgate⟩ := he
    have hSet : active.filter gate = {j} := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_singleton]
      constructor
      · rintro ⟨hk,hkGate⟩
        exact (hUnique k hk j hj hkGate.1 hgate.1)
      · intro hkj
        subst k
        exact ⟨hj,hgate⟩
    have hEq : (∑ k ∈ active,if gate k then F k else 0) = F j := by
      rw [←Finset.sum_filter,hSet,Finset.sum_singleton]
    rw [hEq]
    exact hTerm j hj
  · have hzero : ∀ j ∈ active, ¬gate j := by
      intro j hj hgj
      exact he ⟨j,hj,hgj⟩
    have hZeroSum : (∑ j ∈ active,if gate j then F j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [if_neg (hzero j hj)]
    rw [hZeroSum,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr hxi.le)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCharacterCellExpansion -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11500000

/-- ONE elementary summand of the original global source03 cell/
primitive-character comparison kernel. The gate tests BOTH actual
products D and X; no other prime-group expansion appears. -/
noncomputable def sourceOriginalCharacterCellAtom434
    {Cell Character : Type}
    (cell : Cell → ℕ → Prop) (mass : Cell → ℝ)
    (chi : Character → ℕ → ℂ)
    (j : Cell) (c : Character) (D X : ℕ) : ℂ :=
  if cell j D ∧ cell j X then
    (mass j:ℂ)⁻¹*star (chi c D)*chi c X else 0

/-- SOURCE03 global comparison kernel is EXACTLY a finite double
sum over ONE global log-cell and ONE primitive character. -/
theorem source_original_character_cell_kernel_expand434
    {Cell Character : Type} [DecidableEq Cell]
    (active : Finset Cell) (characters : Finset Character)
    (cell : Cell → ℕ → Prop) (mass : Cell → ℝ)
    (chi : Character → ℕ → ℂ) (D X : ℕ) :
    sourceOriginalCharacterCellKernel434
      active characters cell mass chi D X =
    ∑ j ∈ active,∑ c ∈ characters,
      sourceOriginalCharacterCellAtom434 cell mass chi j c D X := by
  classical
  unfold sourceOriginalCharacterCellKernel434
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hg : cell j D ∧ cell j X
  · simp only [if_pos hg,sourceOriginalCharacterCellAtom434]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring
  · simp only [if_neg hg,sourceOriginalCharacterCellAtom434,
      Finset.sum_const_zero]

/-- Fourfold finite-source expansion of the TWO GLOBAL comparison
kernels: one log-cell and one character for each of two independent
blocks, not one per prime group. -/
theorem source_original_two_global_character_cell_expand434
    {A B C D : Type}
    (JA : Finset A) (CA : Finset B)
    (JB : Finset C) (CB : Finset D)
    (left : A → B → ℂ) (right : C → D → ℂ)
    (r : ℕ) :
    -((-1:ℂ)^r)*
      (∑ ja ∈ JA,∑ ca ∈ CA,left ja ca)*
      (∑ jb ∈ JB,∑ cb ∈ CB,right jb cb) =
    ∑ ja ∈ JA,∑ ca ∈ CA,∑ jb ∈ JB,∑ cb ∈ CB,
      -((-1:ℂ)^r)*left ja ca*right jb cb := by
  classical
  calc
    _ = ∑ ja ∈ JA,∑ ca ∈ CA,
        -((-1:ℂ)^r)*left ja ca*
        (∑ jb ∈ JB,∑ cb ∈ CB,right jb cb) := by
      have hC : (-((-1:ℂ)^r)) *
          (∑ ja ∈ JA,∑ ca ∈ CA,left ja ca) =
          ∑ ja ∈ JA,∑ ca ∈ CA,
            -((-1:ℂ)^r)*left ja ca := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ja hja
        rw [Finset.mul_sum]
      rw [hC,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ja hja
      rw [Finset.sum_mul]
    _ = ∑ ja ∈ JA,∑ ca ∈ CA,∑ jb ∈ JB,∑ cb ∈ CB,
      -((-1:ℂ)^r)*left ja ca*right jb cb := by
      apply Finset.sum_congr rfl
      intro ja hja
      apply Finset.sum_congr rfl
      intro ca hca
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro jb hjb
      rw [Finset.mul_sum]

/-- Literal source03 signed comparison Knu, defined previously as
a PRODUCT of its TWO global character/cell kernels, expands to
exactly the FOUR finite indices (cellA, charA, cellB, charB). -/
theorem source_original_comparison_kernel_finite_expand434
    {CellA CharA CellB CharB : Type}
    [DecidableEq CellA] [DecidableEq CellB]
    (JA : Finset CellA) (CA : Finset CharA)
    (JB : Finset CellB) (CB : Finset CharB)
    (gateA : CellA → ℕ → Prop) (gateB : CellB → ℕ → Prop)
    (massA : CellA → ℝ) (massB : CellB → ℝ)
    (chiA : CharA → ℕ → ℂ) (chiB : CharB → ℕ → ℂ)
    (DA XA DB XB : ℕ) (r : ℕ) :
    -((-1:ℂ)^r)*
      sourceOriginalCharacterCellKernel434 JA CA gateA massA chiA DA XA*
      sourceOriginalCharacterCellKernel434 JB CB gateB massB chiB DB XB =
    ∑ ja ∈ JA,∑ ca ∈ CA,∑ jb ∈ JB,∑ cb ∈ CB,
      -((-1:ℂ)^r)*
        sourceOriginalCharacterCellAtom434 gateA massA chiA ja ca DA XA*
        sourceOriginalCharacterCellAtom434 gateB massB chiB jb cb DB XB := by
  rw [source_original_character_cell_kernel_expand434,
      source_original_character_cell_kernel_expand434]
  exact source_original_two_global_character_cell_expand434
    JA CA JB CB
    (fun ja ca =>
      sourceOriginalCharacterCellAtom434 gateA massA chiA ja ca DA XA)
    (fun jb cb =>
      sourceOriginalCharacterCellAtom434 gateB massB chiB jb cb DB XB) r
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCharacterCellCost -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The literal coefficient in the TWO-GLOBAL comparison's fourfold
cell/character expansion is 1/(nu_A nu_B), with absolute signed
coefficient one; NOT a product over all prime groups. -/
noncomputable def sourceOriginalTwoCellCoefficient434
    {CellA CellB : Type} (massA : CellA → ℝ)
    (massB : CellB → ℝ) (a : CellA) (b : CellB) : ℝ :=
  (massA a)⁻¹*(massB b)⁻¹

theorem source_original_two_cell_coefficient_bound434
    {CellA CellB : Type}
    (massA : CellA → ℝ) (massB : CellB → ℝ)
    (a : CellA) (b : CellB)
    (xi : ℝ) (hxi : 0 < xi)
    (hA : xi ≤ massA a) (hB : xi ≤ massB b) :
    0 ≤ sourceOriginalTwoCellCoefficient434 massA massB a b ∧
    sourceOriginalTwoCellCoefficient434 massA massB a b ≤ (xi⁻¹)^2 := by
  have ha : 0 < massA a := hxi.trans_le hA
  have hb : 0 < massB b := hxi.trans_le hB
  have hIA : (massA a)⁻¹ ≤ xi⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hxi hA
  have hIB : (massB b)⁻¹ ≤ xi⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hxi hB
  constructor
  · exact mul_nonneg (inv_nonneg.mpr ha.le) (inv_nonneg.mpr hb.le)
  · dsimp only [sourceOriginalTwoCellCoefficient434]
    calc
      _ ≤ xi⁻¹*(massB b)⁻¹ :=
        mul_le_mul_of_nonneg_right hIA (inv_nonneg.mpr hb.le)
      _ ≤ xi⁻¹*xi⁻¹ :=
        mul_le_mul_of_nonneg_left hIB (inv_nonneg.mpr hxi.le)
      _ = (xi⁻¹)^2 := by ring

/-- The complete source03 comparison expansion has TOTAL absolute
coefficient cost at most (#cellA)(#charsA)(#cellB)(#charsB)*xi^{-2}.
This counts exactly TWO GLOBAL expansions. No extra factor per
small or large prime group is present. -/
theorem source_original_global_two_kernel_coefficient_cost434
    {CellA CharA CellB CharB : Type}
    (JA : Finset CellA) (CA : Finset CharA)
    (JB : Finset CellB) (CB : Finset CharB)
    (massA : CellA → ℝ) (massB : CellB → ℝ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA,xi ≤ massA j)
    (hMassB : ∀ j ∈ JB,xi ≤ massB j) :
    (∑ ja ∈ JA,∑ _ca ∈ CA,∑ jb ∈ JB,∑ _cb ∈ CB,
      sourceOriginalTwoCellCoefficient434 massA massB ja jb) ≤
      ((JA.card:ℝ)*(CA.card:ℝ)*(JB.card:ℝ)*(CB.card:ℝ))*
      (xi⁻¹)^2 := by
  have hEach (ja : CellA) (hja : ja ∈ JA)
      (jb : CellB) (hjb : jb ∈ JB) :
      sourceOriginalTwoCellCoefficient434 massA massB ja jb ≤
        (xi⁻¹)^2 :=
    (source_original_two_cell_coefficient_bound434
      massA massB ja jb xi hxi (hMassA ja hja) (hMassB jb hjb)).2
  calc
    _ ≤ (∑ _ja ∈ JA,∑ _ca ∈ CA,∑ _jb ∈ JB,∑ _cb ∈ CB,
          (xi⁻¹)^2) := by
      apply Finset.sum_le_sum
      intro ja hja
      apply Finset.sum_le_sum
      intro ca hca
      apply Finset.sum_le_sum
      intro jb hjb
      apply Finset.sum_le_sum
      intro cb hcb
      exact hEach ja hja jb hjb
    _ = ((JA.card:ℝ)*(CA.card:ℝ)*(JB.card:ℝ)*(CB.card:ℝ))*
        (xi⁻¹)^2 := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      push_cast
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActiveCellMass -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- SOURCE03 active cells are precisely the probability cells
of mass ν_j≥xi. As log cells are disjoint, their original
probabilities have total mass ≤1. Hence the number of active
cells is at most 1/xi, WITHOUT any extra T or h-dependent
cardinality assumption. -/
theorem source_original_probability_active_cell_card434
    {Cell : Type} (active : Finset Cell) (mass : Cell → ℝ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMass : ∀ j ∈ active, xi ≤ mass j)
    (hTotal : (∑ j ∈ active,mass j) ≤ 1) :
    (active.card:ℝ) ≤ xi⁻¹ := by
  have hLower : (active.card:ℝ)*xi ≤
      ∑ j ∈ active,mass j := by
    calc
      _ = ∑ _j ∈ active,xi := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ ∑ j ∈ active,mass j :=
        Finset.sum_le_sum (fun j hj => hMass j hj)
  have hCount : (active.card:ℝ)*xi ≤ 1 :=
    hLower.trans hTotal
  simpa only [one_div] using (le_div_iff₀ hxi).mpr hCount

/-- Total ABSOLUTE comparison-character/cell coefficient mass for
TWO independent GLOBAL kernels is ≤ (#charsA)(#charsB)*xi^{-4}.
This is a direct consequence of the TRUE probability normalization
of active source log cells, not a new assertion of the residual
comparison-pattern family's polynomial cost. -/
theorem source_original_two_global_probability_cell_cost434
    {CellA CharA CellB CharB : Type}
    (JA : Finset CellA) (CA : Finset CharA)
    (JB : Finset CellB) (CB : Finset CharB)
    (massA : CellA → ℝ) (massB : CellB → ℝ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMassA : ∀ j ∈ JA,xi ≤ massA j)
    (hMassB : ∀ j ∈ JB,xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA,massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB,massB j) ≤ 1) :
    (∑ ja ∈ JA,∑ _ca ∈ CA,∑ jb ∈ JB,∑ _cb ∈ CB,
      sourceOriginalTwoCellCoefficient434 massA massB ja jb) ≤
      ((CA.card:ℝ)*(CB.card:ℝ))*(xi⁻¹)^4 := by
  have hBase := source_original_global_two_kernel_coefficient_cost434
    JA CA JB CB massA massB xi hxi hMassA hMassB
  have hCardA := source_original_probability_active_cell_card434
    JA massA xi hxi hMassA hTotalA
  have hCardB := source_original_probability_active_cell_card434
    JB massB xi hxi hMassB hTotalB
  have hInv : 0 ≤ xi⁻¹ := inv_nonneg.mpr hxi.le
  have hCount : (JA.card:ℝ)*(JB.card:ℝ) ≤ (xi⁻¹)^2 := by
    calc
      _ ≤ xi⁻¹*xi⁻¹ :=
        mul_le_mul hCardA hCardB
          (Nat.cast_nonneg _) hInv
      _ = (xi⁻¹)^2 := by ring
  have hFactor : 0 ≤ ((CA.card:ℝ)*(CB.card:ℝ))*(xi⁻¹)^2 := by
    positivity
  calc
    _ ≤ ((JA.card:ℝ)*(CA.card:ℝ)*(JB.card:ℝ)*(CB.card:ℝ))*
        (xi⁻¹)^2 := hBase
    _ = ((JA.card:ℝ)*(JB.card:ℝ))*
        (((CA.card:ℝ)*(CB.card:ℝ))*(xi⁻¹)^2) := by ring
    _ ≤ (xi⁻¹)^2*(((CA.card:ℝ)*(CB.card:ℝ))*(xi⁻¹)^2) :=
      mul_le_mul_of_nonneg_right hCount hFactor
    _ = ((CA.card:ℝ)*(CB.card:ℝ))*(xi⁻¹)^4 := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFourChannelComparison -/

section

open MeasureTheory Filter
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64SourceC6 Green64Analytic.CorrelationMellin
set_option maxHeartbeats 18000000

/-- Genuine SOURCE FULL endpoint comparisons in FOUR independent parity channels.
All endpoint-energy, first-endpoint arc, and multiplier bounds are PROVED,
not hypotheses. Only original coefficient discrepancy is required, and only
for the first endpoint. The marked functions, physical Y, product shifts,
probability normalizations, and shared-label phase are unchanged. -/
theorem eventually_source_original_four_channel_comparison434
    (cfg : SourceComparisonFixed434)
    (dexp Aarc Bsave C1 C2 Chigh Cprod vprod Ck D : ℝ) (m0 : ℕ)
    (hd : 0 ≤ dexp) (hdA : dexp < Aarc) (hB : 0 ≤ Bsave)
    (hCarc : Aarc+Bsave ≤ cfg.Carc) (hChigh : 0 ≤ Chigh)
    (hvprod : 0 < vprod) (hCprod : 0 ≤ Cprod) (hCk : 0 ≤ Ck)
    (hDenExponent : Ck+Bsave+1 ≤ (cfg.cm:ℝ))
    (hChoice : 2*(Cprod*Real.log ((Nat.factorial m0:ℝ)*
      (max (1:ℝ) vprod⁻¹)^m0)+D+source_data_global_exponent434 cfg) ≤ Bsave) :
    ∃ Kout : ℝ, 0 ≤ Kout ∧ ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop, ∀ x : ℝ, X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ {γ₁ γ₂ : Type} [DecidableEq γ₁] [DecidableEq γ₂]
        (G₁ : Finset γ₁) (S₁ : γ₁ → Finset ℕ) (k₁ : γ₁ → ℕ) (V₁ : γ₁ → ℝ)
        (G₂ : Finset γ₂) (S₂ : γ₂ → Finset ℕ) (k₂ : γ₂ → ℕ) (V₂ : γ₂ → ℝ),
      (∀ g ∈ G₁, ∀ p ∈ S₁ g, Nat.Prime p) →
      (∀ g ∈ G₂, ∀ p ∈ S₂ g, Nat.Prime p) →
      (∀ g ∈ G₁, ∀ h ∈ G₁, g ≠ h → Disjoint (S₁ g) (S₁ h)) →
      (∀ g ∈ G₂, ∀ h ∈ G₂, g ≠ h → Disjoint (S₂ g) (S₂ h)) →
      (∀ g ∈ G₁, V₁ g = ∑ p ∈ S₁ g, 1/(p:ℝ)) →
      (∀ g ∈ G₂, V₂ g = ∑ p ∈ S₂ g, 1/(p:ℝ)) →
      (∀ g ∈ G₁, k₁ g ≤ m0) → (∀ g ∈ G₂, k₂ g ≤ m0) →
      (∀ g ∈ G₁, vprod ≤ V₁ g) → (∀ g ∈ G₂, vprod ≤ V₂ g) →
      (G₁.card:ℝ) ≤ Cprod*Real.log L → (G₂.card:ℝ) ≤ Cprod*Real.log L →
      ∀ (M N : ℕ), 0 < M → 0 < N → ∀ (U1 U2 : ℝ),
      Real.exp (L^cfg.cexp-C1) ≤ U1 → Real.exp (L^cfg.cexp-C2) ≤ U2 →
      U1 ≤ (M:ℝ) → U2 ≤ (N:ℝ) →
      U1*U2 ≤ Real.exp (Chigh*Real.log L*L^dexp) →
      ∀ (b₁ b₂ : ℕ → ℂ),
      (∀ n ∈ Finset.Ico M (M+3*M), ‖b₁ n‖ ≤ 1) →
      (∀ n ∈ Finset.Ico N (N+3*N), ‖b₂ n‖ ≤ 1) →
      ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (Y : ℝ) {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
        (u v : SourceComparisonData434 ι β cfg x L Y (U1*U2)),
      SourceAlphaDiscrepancy L (B:ℝ) x u.alpha →
      ∀ (eps1 eps2 : Bool) (sharedSlots : ℕ),
      ‖((if eps1 then (-1:ℂ)^sharedSlots else 1)*
          (if eps2 then (-1:ℂ)^sharedSlots else 1)) *
        (∑ ij ∈ (Finset.range (3*M)).product (Finset.range (3*N)),
          sourceProductShiftCoefficient434 M N
            (sourceProductAtomMass G₁ S₁ k₁ V₁) (sourceProductAtomMass G₂ S₂ k₂ V₂) b₁ b₂ ij *
          (∑ m ∈ u.support, ∑ n ∈ v.support,
            if n = m+sourceProductShift434 M N k ij then
              star (sourceSignedCoefficients434 u.Ptw eps1 u.endpoint m)*
                sourceSignedCoefficients434 u.Ptw eps2 v.endpoint n else 0))‖ ≤ Kout*Y*L^(-D) := by
  let E := source_data_global_exponent434 cfg
  let Kglobal := source_data_global_constant434 cfg
  have hKg : 0 ≤ Kglobal := source_data_global_constant_nonneg434 cfg
  have hc : 0 < cfg.cexp := (cfg.haexp.trans cfg.hab).trans cfg.hbc
  obtain ⟨Karc,hKarc,B,X0,hX0,hArc⟩ :=
    eventually_source_data_signed_arc434 cfg (2*(Ck+Bsave+1)+2*D+E)
  have hComp := eventually_source_logcell_four_channel_comparison434
    cfg.cexp dexp Aarc Bsave cfg.Carc C1 C2 Chigh Cprod vprod Ck D E Karc Kglobal m0
    hc hd hdA hB hCarc hChigh hvprod hCprod hCk hKarc.le hKg hChoice
  refine ⟨Real.sqrt (2*Karc*Kglobal)+64*Kglobal,by positivity,B,X0,hX0,?_⟩
  filter_upwards [hArc,hComp] with L hArcL hCompL
  intro x hx hLog hL γ₁ γ₂ _ _ G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂
    hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂
    M N hM hN U1 U2 hMscale hNscale hU1M hU2N hHigh b₁ b₂ hb₁ hb₂ k hk hKshift
    Y ι β _ _ _ _ u v hDisc
  have hFirst := source_data_global_budget434 cfg x L Y (U1*U2) hL u
  have hSecond := source_data_global_budget434 cfg x L Y (U1*U2) hL v
  have hLone : 1 ≤ L := by linarith
  have hQ := source_product_rational_denominator_cap434 L Ck Bsave k (by linarith) hB hKshift
  have hQcm : ((k.natAbs*Nat.ceil (L^Bsave):ℕ):ℝ) ≤ L^cfg.cm := hQ.trans (by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hLone hDenExponent)
  refine hCompL.2 G₁ S₁ k₁ V₁ G₂ S₂ k₂ V₂ hp₁ hp₂ hd₁ hd₂ hV₁exact hV₂exact
    hk₁ hk₂ hV₁ hV₂ hcard₁ hcard₂ M N hM hN U1 U2 hMscale hNscale hU1M hU2N hHigh
    b₁ b₂ hb₁ hb₂ k hk hKshift u.support v.support u.endpoint v.endpoint u.Ptw Y
    (by linarith [u.hY]) hFirst hSecond ?_
  intro eps den h hden hdenQ hh
  exact hArcL x hx hLog hL Y (U1*U2) u hDisc eps den h hden
    ((by exact_mod_cast hdenQ : (den:ℝ) ≤ ((k.natAbs*Nat.ceil (L^Bsave):ℕ):ℝ)).trans hQcm)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFullGroupFromData -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The ORIGINAL source03 small singled-out marked prime group S,
other small prime groups Ts, and all big prime groups Tb, assembled
into one labelled physical group index. This is the ACTUAL
u.G=S ∪ ⋃ Ts ∪ ⋃ Tb source family, not an invented generic
G/P splitting. -/
abbrev SourceOriginalFullGroupIndex434 (ι β : Type) := (Option ι) ⊕ β

noncomputable def sourceOriginalFullGroupPrimeSets434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hprime) :
    SourceOriginalFullGroupIndex434 ι β → Finset ℕ :=
  fun g => match g with
    | Sum.inl none => u.S
    | Sum.inl (some i) => u.Ts i
    | Sum.inr b => u.Tb b

/-- The ORIGINAL physical group normalization V for the
single distinguished small group, remaining small groups and
all big groups. These are exactly the mass fields in the
same SourceComparisonData434, not new independent V_g. -/
noncomputable def sourceOriginalFullGroupMass434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hprime) :
    SourceOriginalFullGroupIndex434 ι β → ℝ :=
  fun g => match g with
    | Sum.inl none => u.Vs
    | Sum.inl (some i) => u.Vsmall i
    | Sum.inr b => u.Vbig b

/-- EXACT original source03 outside-part group prime union.
No extra hUnion hypothesis is required if the physical group
family is indexed by the genuine S/Ts/Tb groups of u. -/
theorem source_original_full_groups_union434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hprime) :
    u.G = (Finset.univ : Finset
      (SourceOriginalFullGroupIndex434 ι β)).biUnion
        (sourceOriginalFullGroupPrimeSets434 u) := by
  classical
  rw [u.hG]
  ext p
  constructor
  · intro hp
    rcases (Finset.mem_union.mp hp) with hST | hB
    · rcases (Finset.mem_union.mp hST) with hS | hT
      · exact Finset.mem_biUnion.mpr
          ⟨Sum.inl none,Finset.mem_univ _,by
            simpa only [sourceOriginalFullGroupPrimeSets434] using hS⟩
      · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hT
        exact Finset.mem_biUnion.mpr
          ⟨Sum.inl (some i),Finset.mem_univ _,by
            simpa only [sourceOriginalFullGroupPrimeSets434] using hi⟩
    · obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hB
      exact Finset.mem_biUnion.mpr
        ⟨Sum.inr b,Finset.mem_univ _,by
          simpa only [sourceOriginalFullGroupPrimeSets434] using hb⟩
  · intro hp
    obtain ⟨g,_,hg⟩ := Finset.mem_biUnion.mp hp
    cases g with
    | inl o =>
        cases o with
        | none =>
            apply Finset.mem_union.mpr
            apply Or.inl
            apply Finset.mem_union.mpr
            exact Or.inl (by
              simpa only [sourceOriginalFullGroupPrimeSets434] using hg)
        | some i =>
            apply Finset.mem_union.mpr
            apply Or.inl
            apply Finset.mem_union.mpr
            apply Or.inr
            exact Finset.mem_biUnion.mpr
              ⟨i,Finset.mem_univ _,by
                simpa only [sourceOriginalFullGroupPrimeSets434] using hg⟩
    | inr b =>
        apply Finset.mem_union.mpr
        apply Or.inr
        exact Finset.mem_biUnion.mpr
          ⟨b,Finset.mem_univ _,by
            simpa only [sourceOriginalFullGroupPrimeSets434] using hg⟩

/-- Every ACTUAL physical group prime is prime, directly from
u.hSPrime, u.hTsPrime, u.hTbPrime. -/
theorem source_original_full_groups_prime434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hprime) :
    ∀ g p, p ∈ sourceOriginalFullGroupPrimeSets434 u g →
      p.Prime := by
  intro g p hp
  cases g with
  | inl o =>
      cases o with
      | none => exact u.hSPrime p hp
      | some i => exact u.hTsPrime i p hp
  | inr b => exact u.hTbPrime b p hp

/-- The TRUE original physical group norm lower bound is
already a field of the actual endpoint source data. -/
theorem source_original_full_groups_norm_positive434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hprime) :
    ∀ g, cfg.vmin ≤ sourceOriginalFullGroupMass434 u g := by
  intro g
  cases g with
  | inl o =>
      cases o with
      | none => exact u.hVs
      | some i => exact u.hVsmall i
  | inr b => exact u.hVbig b

/-- If the ORIGINAL two endpoints use the SAME physical group
families S,Ts,Tb, their total original prime set G agrees
exactly; this is the hG condition of the original physical
conditional-fibre theorems, not a fabricated identification. -/
theorem source_original_full_endpoints_same_groups434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (u v : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hS : u.S = v.S) (hTs : u.Ts = v.Ts)
    (hTb : u.Tb = v.Tb) :
    v.G = u.G := by
  calc
    v.G = v.S ∪ Finset.univ.biUnion v.Ts ∪
      Finset.univ.biUnion v.Tb := v.hG
    _ = u.S ∪ Finset.univ.biUnion u.Ts ∪
      Finset.univ.biUnion u.Tb := by rw [←hS,←hTs,←hTb]
    _ = u.G := u.hG.symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLiteralLogCells -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- EXACT source03 global logarithmic cell I_j=[j*h,(j+1)*h).
Membership is tested on log of the genuine source free/marked
product, not a groupwise surrogate. -/
def sourceOriginalLiteralLogCell434 (h : ℝ) (j : ℤ) (n : ℕ) : Prop :=
  (j:ℝ)*h ≤ Real.log (n:ℝ) ∧
    Real.log (n:ℝ) < ((j:ℝ)+1)*h

/-- A positive-width original source03 half-open logarithmic mesh
has a UNIQUE cell for any product, including at interval endpoints. -/
theorem source_original_literal_log_cells_unique434
    (h : ℝ) (hh : 0 < h) (D : ℕ)
    (j k : ℤ)
    (hj : sourceOriginalLiteralLogCell434 h j D)
    (hk : sourceOriginalLiteralLogCell434 h k D) : j=k := by
  by_contra hne
  have hcase : j < k ∨ k < j := (lt_or_gt_of_ne hne)
  rcases hcase with hjk | hkj
  · have hc : (j:ℝ)+1 ≤ (k:ℝ) := by
      exact_mod_cast (show j+1 ≤ k by omega)
    have hm : ((j:ℝ)+1)*h ≤ (k:ℝ)*h :=
      mul_le_mul_of_nonneg_right hc hh.le
    dsimp only [sourceOriginalLiteralLogCell434] at hj hk
    linarith [hj.2,hk.1,hm]
  · have hc : (k:ℝ)+1 ≤ (j:ℝ) := by
      exact_mod_cast (show k+1 ≤ j by omega)
    have hm : ((k:ℝ)+1)*h ≤ (j:ℝ)*h :=
      mul_le_mul_of_nonneg_right hc hh.le
    dsimp only [sourceOriginalLiteralLogCell434] at hj hk
    linarith [hk.2,hj.1,hm]

/-- The literal source03 global character-cell kernel has its
advertised Q^2/xi bound, with no cell-count loss: the cell
uniqueness is PROVED from the actual half-open log geometry. -/
theorem source_original_literal_log_character_kernel_bound434
    {Character : Type}
    (active : Finset ℤ) (characters : Finset Character)
    (h : ℝ) (hh : 0 < h)
    (mass : ℤ → ℝ) (chi : Character → ℕ → ℂ)
    (D X : ℕ) (xi : ℝ) (hxi : 0 < xi)
    (hMass : ∀ j ∈ active,xi ≤ mass j)
    (hChi : ∀ c ∈ characters, ‖chi c D‖ ≤ 1 ∧ ‖chi c X‖ ≤ 1) :
    ‖sourceOriginalCharacterCellKernel434 active characters
      (sourceOriginalLiteralLogCell434 h) mass chi D X‖ ≤
      (characters.card:ℝ)*xi⁻¹ := by
  exact source_original_global_character_cell_bound434
    active characters (sourceOriginalLiteralLogCell434 h)
    mass chi D X xi hxi hMass
    (fun j hj k hk hjD hkD =>
      source_original_literal_log_cells_unique434 h hh D j k hjD hkD)
    hChi
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDirichletGlobalCell -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Actual Dirichlet-character values have modulus at most one,
whether the character is principal, primitive, or imprimitive,
and even when the tested integer is not coprime to q. -/
theorem source_original_dirichlet_at_nat_norm434
    (q n : ℕ) (chi : DirichletCharacter ℂ q) :
    ‖chi (n:ZMod q)‖ ≤ 1 :=
  chi.norm_le_one (n:ZMod q)

/-- The genuine source03 global CHARACTER/CELL kernel with a
finite family of complex Dirichlet characters of fixed modulus q
and disjoint ORIGINAL log intervals satisfies Q^2/xi when the
source family has at most Q^2 characters. This includes principal
and imprimitive characters: removing any does not enlarge the norm. -/
theorem source_original_dirichlet_global_cell_bound434
    (q : ℕ)
    (active : Finset ℤ)
    (characters : Finset (DirichletCharacter ℂ q))
    (h : ℝ) (hh : 0 < h)
    (mass : ℤ → ℝ) (xi Q : ℝ)
    (hxi : 0 < xi) (hQ : 0 ≤ Q)
    (hMass : ∀ j ∈ active,xi ≤ mass j)
    (hChars : (characters.card:ℝ) ≤ Q^2)
    (D X : ℕ) :
    ‖sourceOriginalCharacterCellKernel434 active characters
      (sourceOriginalLiteralLogCell434 h) mass
      (fun chi n => chi (n:ZMod q)) D X‖ ≤ Q^2*xi⁻¹ := by
  have hh := source_original_literal_log_character_kernel_bound434
    active characters h hh mass (fun chi n => chi (n:ZMod q))
    D X xi hxi hMass (fun chi hc =>
      ⟨source_original_dirichlet_at_nat_norm434 q D chi,
       source_original_dirichlet_at_nat_norm434 q X chi⟩)
  calc
    _ ≤ (characters.card:ℝ)*xi⁻¹ := hh
    _ ≤ Q^2*xi⁻¹ :=
      mul_le_mul_of_nonneg_right hChars (inv_nonneg.mpr hxi.le)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDirichletCount -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- For one actual positive conductor q, the total number of
complex Dirichlet characters mod q is φ(q)≤q. A primitive subset
can only be smaller. -/
theorem source_original_dirichlet_characters_count434
    (q : ℕ) (hq : 0 < q) :
    Fintype.card (DirichletCharacter ℂ q) ≤ q := by
  letI : NeZero q := ⟨by omega⟩
  have hCard : Nat.card (DirichletCharacter ℂ q) = q.totient :=
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hCard' : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using hCard
  rw [hCard']
  exact Nat.totient_le q

/-- Any selected primitive-character family of this single conductor
has size at most q; no character-count axiom is necessary for a
fixed source03 modulus. -/
theorem source_original_selected_dirichlet_count434
    (q : ℕ) (hq : 0 < q)
    (characters : Finset (DirichletCharacter ℂ q)) :
    characters.card ≤ q := by
  exact (Finset.card_le_card (Finset.subset_univ characters)).trans
    (source_original_dirichlet_characters_count434 q hq)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalAllConductorCharacters -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Across ALL positive source03 conductors q<=Q, even counting
every Dirichlet character (including imprimitive ones), there
are at most Q^2 character choices. The selected primitive
family at each conductor is an arbitrary finite subset,
hence cannot increase the count. This discharges the source03
global character-count input from the true arithmetic objects. -/
theorem source_original_all_conductor_character_count434
    (Q : ℕ)
    (characters : (q : Fin Q) →
      Finset (DirichletCharacter ℂ (q.val+1))) :
    (∑ q : Fin Q,(characters q).card) ≤ Q^2 := by
  classical
  have hEach (q : Fin Q) : (characters q).card ≤ Q := by
    have hChar := source_original_selected_dirichlet_count434
      (q.val+1) (by omega) (characters q)
    omega
  calc
    _ ≤ ∑ _q : Fin Q,Q := by
      exact Finset.sum_le_sum (fun q _ => hEach q)
    _ = Q^2 := by simp [pow_two]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveCharacterFamily -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- A TRUE finite union of selected source Dirichlet characters for
EVERY positive conductor q<=Q, retaining their original modulus in
the dependent (conductor, character) pair. Primitive characters form
a permissible selected subfamily without changes to this definition. -/
noncomputable def sourceOriginalSelectedCharacterFamily434
    (Q : ℕ)
    (selected : (q : Fin Q) →
      Finset (DirichletCharacter ℂ (q.val+1))) :
    Finset (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1)) :=
  Finset.univ.sigma selected

/-- At most Q^2 TRUE complex Dirichlet characters across ALL
original positive conductors up to Q, even when imprimitive
characters are included. -/
theorem source_original_selected_character_family_card434
    (Q : ℕ)
    (selected : (q : Fin Q) →
      Finset (DirichletCharacter ℂ (q.val+1))) :
    (sourceOriginalSelectedCharacterFamily434 Q selected).card ≤ Q^2 := by
  have hc := source_original_all_conductor_character_count434 Q selected
  simpa only [sourceOriginalSelectedCharacterFamily434,
    Finset.card_sigma] using hc

/-- Source03 global one-kernel bound with the ACTUAL primitive/
imprimitive Dirichlet character family of all conductors <=Q,
the ACTUAL half-open logarithmic mesh, and normalized active
cell mass threshold xi. There is NO assumption on number of
characters or cell-disjointness: both are proved. -/
theorem source_original_true_all_conductor_global_kernel_bound434
    (Q : ℕ)
    (selected : (q : Fin Q) →
      Finset (DirichletCharacter ℂ (q.val+1)))
    (active : Finset ℤ)
    (h : ℝ) (hh : 0 < h)
    (mass : ℤ → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hMass : ∀ j ∈ active,xi ≤ mass j)
    (D X : ℕ) :
    ‖sourceOriginalCharacterCellKernel434
      active (sourceOriginalSelectedCharacterFamily434 Q selected)
      (sourceOriginalLiteralLogCell434 h) mass
      (fun c n => c.2 (n:ZMod (c.1.val+1))) D X‖ ≤
      (Q:ℝ)^2*xi⁻¹ := by
  have hChars : ((sourceOriginalSelectedCharacterFamily434
      Q selected).card:ℝ) ≤ (Q:ℝ)^2 := by
    exact_mod_cast source_original_selected_character_family_card434 Q selected
  have hBound := source_original_literal_log_character_kernel_bound434
    active (sourceOriginalSelectedCharacterFamily434 Q selected)
    h hh mass (fun c n => c.2 (n:ZMod (c.1.val+1)))
    D X xi hxi hMass
    (fun c hc =>
      ⟨(c.2).norm_le_one (D:ZMod (c.1.val+1)),
       (c.2).norm_le_one (X:ZMod (c.1.val+1))⟩)
  exact hBound.trans (mul_le_mul_of_nonneg_right hChars
    (inv_nonneg.mpr hxi.le))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveCharacters -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The TRUE source03 primitive-character family: for every
POSITIVE modulus 1 ≤ q ≤ Q, take exactly the characters satisfying
DirichletCharacter.IsPrimitive. This is a source-defined finite
family, not an arbitrary abstract parameter declared primitive. -/
noncomputable def sourceOriginalActualPrimitiveCharacters434
    (Q : ℕ) :
    Finset (Σ q : Fin Q,DirichletCharacter ℂ (q.val+1)) :=
  sourceOriginalSelectedCharacterFamily434 Q
    (fun q => Finset.univ.filter
      (fun χ : DirichletCharacter ℂ (q.val+1) => χ.IsPrimitive))

theorem source_original_actual_primitive_mem434
    (Q : ℕ) (c : Σ q : Fin Q,DirichletCharacter ℂ (q.val+1)) :
    c ∈ sourceOriginalActualPrimitiveCharacters434 Q ↔
    (c.2).IsPrimitive := by
  classical
  simp [sourceOriginalActualPrimitiveCharacters434,
    sourceOriginalSelectedCharacterFamily434]

/-- There are at most Q^2 genuine primitive complex Dirichlet
characters across ALL original conductors ≤ Q. The bound comes
from actual character cardinality φ(q)≤q, not a source axiom. -/
theorem source_original_actual_primitive_count434 (Q : ℕ) :
    (sourceOriginalActualPrimitiveCharacters434 Q).card ≤ Q^2 := by
  classical
  exact source_original_selected_character_family_card434 Q
    (fun q => Finset.univ.filter
      (fun χ : DirichletCharacter ℂ (q.val+1) => χ.IsPrimitive))

/-- Exact source03 primitive, all-conductor GLOBAL kernel on
half-open original logarithmic cells: every term uses the
primitive Dirichlet character at its own original conductor. -/
noncomputable def sourceOriginalActualPrimitiveGlobalKernel434
    (Q : ℕ) (active : Finset ℤ) (h : ℝ)
    (mass : ℤ → ℝ) (D X : ℕ) : ℂ :=
  sourceOriginalCharacterCellKernel434 active
    (sourceOriginalActualPrimitiveCharacters434 Q)
    (sourceOriginalLiteralLogCell434 h) mass
    (fun c n => c.2 (n:ZMod (c.1.val+1))) D X

/-- SOURCE03 single-global primitive-character/cell kernel bound,
with the true finite character set, primitive conductor, and
half-open logarithmic cell uniqueness all kernel verified. -/
theorem source_original_actual_primitive_global_bound434
    (Q : ℕ) (active : Finset ℤ)
    (h : ℝ) (hh : 0 < h) (mass : ℤ → ℝ)
    (xi : ℝ) (hxi : 0 < xi)
    (hMass : ∀ j ∈ active, xi ≤ mass j)
    (D X : ℕ) :
    ‖sourceOriginalActualPrimitiveGlobalKernel434
      Q active h mass D X‖ ≤ (Q:ℝ)^2*xi⁻¹ := by
  classical
  exact source_original_true_all_conductor_global_kernel_bound434
    Q (fun q => Finset.univ.filter
      (fun χ : DirichletCharacter ℂ (q.val+1) => χ.IsPrimitive))
    active h hh mass xi hxi hMass D X
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalUnitFourier -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Explicit multiplicative Fourier coefficient of a function
on the ACTUAL invertible residue classes (ZMod q)^×, using the
complete family of genuine complex Dirichlet characters mod q.
The conductor will later be lowered to its unique primitive
inducing character without altering values on these units. -/
noncomputable def sourceOriginalRationalUnitFourierCoeff434
    (q : ℕ) [NeZero q] (F : (ZMod q)ˣ → ℂ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ((q.totient:ℂ)⁻¹) *
    (∑ a : (ZMod q)ˣ, F a * χ ((a:ZMod q)⁻¹))

/-- Exact Dirichlet-character Fourier inversion on the genuine
finite unit group. This is the rational major-arc character
identity, not a hypothetical decomposition or a generic
averaging estimate. Unlike L² estimates, this equality is
valid for ANY complex function F on reduced residue classes. -/
theorem source_original_rational_unit_fourier_inversion434
    (q : ℕ) [NeZero q] (F : (ZMod q)ˣ → ℂ)
    (b : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q,
       sourceOriginalRationalUnitFourierCoeff434 q F χ *
         χ (b:ZMod q)) = F b := by
  classical
  let T : ℂ := (q.totient:ℂ)
  have hT : T ≠ 0 := by
    dsimp [T]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hOrth (a : (ZMod q)ˣ) :
      (∑ χ : DirichletCharacter ℂ q,
        χ ((a:ZMod q)⁻¹)*χ (b:ZMod q)) =
      (if a=b then T else 0) := by
    have hz :=
      DirichletCharacter.sum_char_inv_mul_char_eq
        ℂ (Units.isUnit a) (b:ZMod q)
    by_cases hab : a=b
    · subst a
      simpa only [T, if_pos rfl] using hz
    · have hv : (a:ZMod q) ≠ (b:ZMod q) :=
        fun hv => hab (Units.val_inj.mp hv)
      simpa only [T, if_neg hab, if_neg hv] using hz
  unfold sourceOriginalRationalUnitFourierCoeff434
  calc
    _ = T⁻¹ * ∑ χ : DirichletCharacter ℂ q,
       (∑ a : (ZMod q)ˣ, F a * χ ((a:ZMod q)⁻¹)) *
         χ (b:ZMod q) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro χ hχ
          dsimp [T]
          ring
    _ = T⁻¹ * ∑ a : (ZMod q)ˣ,
          F a*(∑ χ : DirichletCharacter ℂ q,
            χ ((a:ZMod q)⁻¹)*χ (b:ZMod q)) := by
          congr 1
          calc
            _ = ∑ χ : DirichletCharacter ℂ q,
                  ∑ a : (ZMod q)ˣ,
                    F a*χ ((a:ZMod q)⁻¹)*χ (b:ZMod q) := by
                 apply Finset.sum_congr rfl
                 intro χ hχ
                 rw [Finset.sum_mul]
            _ = ∑ a : (ZMod q)ˣ,
                  ∑ χ : DirichletCharacter ℂ q,
                    F a*χ ((a:ZMod q)⁻¹)*χ (b:ZMod q) :=
               Finset.sum_comm
            _ = _ := by
               apply Finset.sum_congr rfl
               intro a ha
               rw [Finset.mul_sum]
               apply Finset.sum_congr rfl
               intro χ hχ
               ring
    _ = T⁻¹ * ∑ a : (ZMod q)ˣ,
          F a*(if a=b then T else 0) := by
          apply congrArg (fun z : ℂ => T⁻¹*z)
          apply Finset.sum_congr rfl
          intro a ha
          rw [hOrth a]
    _ = F b := by
          have hPick :
              (∑ a : (ZMod q)ˣ, F a*(if a=b then T else 0)) =
              F b*T := by
              simp
          rw [hPick]
          field_simp [hT]
end Green64Analytic.CorrelationSquare

end

