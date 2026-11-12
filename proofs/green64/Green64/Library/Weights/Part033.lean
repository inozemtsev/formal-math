module

public import Green64.Library.Correlation.Part002
public import Green64.Library.Weights.LiteralEndpointProfiles
public import Green64.Library.Analysis.Estimates.Part007
public import Green64.Library.Correlation.Part001
public import Mathlib.Tactic
public import Green64.Library.Weights.Part012
public import Green64.Library.Correlation.Part021
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Green64.Library.Weights.Part011
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Green64.Library.Correlation.Part003
public import Green64.Library.Weights.Part032
public import Mathlib
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Choose.Sum
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Sieve.Foundations.Part002

@[expose] public section

/-!
# Weights / Part033

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## LiteralDyadicProfiles -/

section

open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Literal ORIGINAL native harmonic profile: psi(r)=r*eta_dyad(r).
It remains separate from the fixed endpoint buffer theta. -/
def sourceB578NativePsi434 (r : ℝ) : ℂ :=
  (r:ℂ)*sourceCorrectedDyadicSchwartz r

/-- Exact structural facts for the actual dyadic profile, including its
nonzero value and its original [1/2,2] support. -/
theorem source_B578_literal_native_psi_fields434 :
    ContDiff ℝ ∞ sourceB578NativePsi434 ∧
    (∀r,sourceB578NativePsi434 r≠0 → (1/2:ℝ) ≤ r ∧ r ≤ 2) ∧
    (∀r,‖sourceB578NativePsi434 r‖ ≤ 2) ∧ sourceB578NativePsi434 1=1 := by
  have hSupport : ∀r,sourceB578NativePsi434 r≠0 → (1/2:ℝ) ≤ r ∧ r ≤ 2 := by
    intro r hr
    have hn : sourceCorrectedDyadicProfile r≠0 := by
      intro hz
      apply hr
      change (r:ℂ)*(sourceCorrectedDyadicProfile r:ℂ)=0
      rw [hz,Complex.ofReal_zero,mul_zero]
    exact source_corrected_dyadic_profile_support (subset_tsupport _ hn)
  refine ⟨Complex.ofRealCLM.contDiff.mul sourceCorrectedDyadicSchwartz.smooth',hSupport,?_,?_⟩
  · intro r
    by_cases hr : sourceB578NativePsi434 r=0
    · simp [hr]
    have hs := hSupport r hr
    have hp := source_corrected_dyadic_profile_range r
    change ‖(r:ℂ)*(sourceCorrectedDyadicProfile r:ℂ)‖ ≤ 2
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ r),abs_of_nonneg hp.1]
    nlinarith
  · have he : sourceCorrectedDyadicProfile 1=1 := by
      unfold sourceCorrectedDyadicProfile
      rw [show (2:ℝ)*1-1=1 by ring,show (1:ℝ)-1=0 by ring,
        Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ) ≤ 1),
        Real.smoothTransition.zero_of_nonpos (by norm_num : (0:ℝ) ≤ 0)]
      norm_num
    change (1:ℂ)*(sourceCorrectedDyadicProfile 1:ℂ)=1
    rw [he]
    norm_num

/-- Literal additional Fourier-separation profile phi(u)=psi(exp u).
The original dyadic psi is retained pointwise, not replaced by a new window. -/
def sourceB578NativeLogPhi434 : SchwartzMap ℝ ℂ :=
  sourcePlainLogProfileSchwartz434 2 sourceB578NativePsi434 (by norm_num)
    source_B578_literal_native_psi_fields434.1 source_B578_literal_native_psi_fields434.2.1

theorem source_B578_literal_native_log_profile434 :
    (∀u,sourceB578NativeLogPhi434 u=sourceB578NativePsi434 (Real.exp u)) ∧
    tsupport (sourceB578NativeLogPhi434 : ℝ → ℂ) ⊆
      Set.Icc (-Real.log 2) (Real.log 2) ∧
    (∀r : ℝ,0< r → sourceB578NativeLogPhi434 (Real.log r)=sourceB578NativePsi434 r) := by
  refine ⟨fun _=>rfl,?_,?_⟩
  · exact source_plain_log_profile_support434 2 sourceB578NativePsi434 (by norm_num)
      source_B578_literal_native_psi_fields434.2.1
  · intro r hr
    change sourceB578NativePsi434 (Real.exp (Real.log r))=sourceB578NativePsi434 r
    rw [Real.exp_log hr]

/-- Every derivative bound of the literal extra Fourier profile is supplied
with a single sequence fixed before L; the cutoff exponent 3 can stay fixed. -/
theorem source_B578_literal_native_separation_budget434 :
    ∃ Ksep : ℕ → ℝ,(∀j,0 ≤ Ksep j) ∧ ∀L : ℝ,
      sourceLogDerivativeBudget 0 Ksep L sourceB578NativeLogPhi434 := by
  obtain ⟨K,hK,hB⟩ := source_fixed_harmonic_profile_budget434 2 sourceB578NativePsi434
    (by norm_num) source_B578_literal_native_psi_fields434.1
    source_B578_literal_native_psi_fields434.2.1
  exact ⟨K,hK,fun L=>(hB L).1⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## RankCellCutoff -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- A genuinely constructed, fixed physical cutoff for the common scale
of two original logarithmic cells. Its support constant and ALL log
regularity constants are chosen before L, before the cells, and before
any auxiliary draw. The interval covers both signed-shift endpoints. -/
theorem parity_fixed_rank_cell_cutoff_exists434 :
    ∃ A : ℝ, 64 ≤ A ∧ ∃ eta : ℝ → ℂ,
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ, eta u ≠ 0 → 1/A ≤ u ∧ u ≤ A) ∧
      (∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u = 1) ∧
      (∀ u : ℝ, ‖eta u‖ ≤ 1) ∧
      ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
        ∀ L : ℝ, sourceLogDerivativeBudget 0 K L (fun u : ℝ => eta (Real.exp u)) := by
  let M : ℝ := 64*Real.exp 2+2
  have hM : 2 < M := by dsimp [M]; have := Real.exp_pos (2 : ℝ); linarith
  let A : ℝ := 512+2*M
  have hA512 : 512 ≤ A := by dsimp [A]; linarith
  have hA : 1 ≤ A := by linarith
  let b : ContDiffBump M := ⟨M-1/256,M-1/512,by linarith,by norm_num⟩
  let eta : ℝ → ℂ := fun u => (b u : ℂ)
  have hSmooth : ContDiff ℝ ∞ eta := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hSupport (u : ℝ) (hu : eta u ≠ 0) : 1/A ≤ u ∧ u ≤ A := by
    have hbu : b u ≠ 0 := by
      intro hb
      exact hu (by simp only [eta,hb,Complex.ofReal_zero])
    have hball : u ∈ Metric.ball M b.rOut := by
      rw [← b.support_eq]
      exact hbu
    have habs : |u-M| < M-1/512 := by
      simpa only [Metric.mem_ball,Real.dist_eq,b] using hball
    have hlu : 1/512 < u := by have := (abs_lt.mp habs).1; linarith
    have huu : u < 2*M := by have := (abs_lt.mp habs).2; linarith
    refine ⟨?_,?_⟩
    · exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 512) hA512).trans hlu.le
    · dsimp only [A]
      linarith
  have hOne (u : ℝ) (hu : u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1)) : eta u = 1 := by
    have hdist : |u-M| ≤ M-1/256 := by
      rw [abs_le]
      dsimp only [M]
      constructor <;> linarith [hu.1,hu.2]
    have hb : b u = 1 := b.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall,Real.dist_eq,b] using hdist)
    simp only [eta,hb,Complex.ofReal_one]
  have hNorm (u : ℝ) : ‖eta u‖ ≤ 1 := by
    have hn : 0 ≤ b u := b.nonneg
    have hh : b u ≤ 1 := b.le_one
    simpa only [eta,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn] using hh
  let f := sourcePlainLogProfileSchwartz434 A eta hA hSmooth hSupport
  let K : ℕ → ℝ := fun j => SchwartzMap.seminorm ℂ 0 j f
  refine ⟨A,by linarith,eta,hSmooth,hSupport,hOne,hNorm,K,fun j => apply_nonneg _ _,?_⟩
  intro L j u
  change ‖iteratedDeriv j (f : ℝ → ℂ) u‖ ≤ K j*L^(0*((j : ℝ)+1))
  simpa only [K,pow_zero,one_mul,zero_mul,Real.rpow_zero,mul_one] using
    (SchwartzMap.le_seminorm' ℂ 0 j f u)

/-- The harmonic inverse may be absorbed into a fixed localized endpoint
without losing smoothness at zero. Its entire log derivative budget is
again fixed before L; the support is exactly inherited from eta. -/
theorem parity_fixed_harmonic_cutoff_regular434
    (A : ℝ) (eta : ℝ → ℂ) (hA : 1 ≤ A) (hSmooth : ContDiff ℝ ∞ eta)
    (hSupport : ∀ u : ℝ, eta u ≠ 0 → 1/A ≤ u ∧ u ≤ A) :
    ContDiff ℝ ∞ (fun u : ℝ => eta u/(u : ℂ)) ∧
    (∀ u : ℝ, eta u/(u : ℂ) ≠ 0 → 1/A ≤ u ∧ u ≤ A) ∧
    ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      ∀ L : ℝ, sourceLogDerivativeBudget 0 K L
        (fun u : ℝ => eta (Real.exp u)/(Real.exp u : ℂ)) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hSupp (u : ℝ) (hu : eta u/(u : ℂ) ≠ 0) : 1/A ≤ u ∧ u ≤ A :=
    hSupport u (fun hz => hu (by rw [hz,zero_div]))
  have hs : ContDiff ℝ ∞ (fun u : ℝ => eta u/(u : ℂ)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      have hNear : (fun u : ℝ => eta u/(u : ℂ)) =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
        filter_upwards [eventually_lt_nhds (one_div_pos.mpr hAp)] with u hu
        have hz : eta u = 0 := by
          by_contra hn
          exact (not_le_of_gt hu) (hSupport u hn).1
        rw [hz,zero_div]
      exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) 0).congr_of_eventuallyEq hNear
    · have hr : ContDiffAt ℝ ∞ (fun u : ℝ => u⁻¹) x := contDiffAt_id.inv hx
      have hc : ContDiffAt ℝ ∞ (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
      simpa only [div_eq_mul_inv,Complex.ofReal_inv] using hSmooth.contDiffAt.mul hc
  let f := sourcePlainLogProfileSchwartz434 A (fun u : ℝ => eta u/(u : ℂ)) hA hs hSupp
  let K : ℕ → ℝ := fun j => SchwartzMap.seminorm ℂ 0 j f
  refine ⟨hs,hSupp,K,fun j => apply_nonneg _ _,?_⟩
  intro L j u
  change ‖iteratedDeriv j (f : ℝ → ℂ) u‖ ≤ K j*L^(0*((j : ℝ)+1))
  simpa only [K,pow_zero,one_mul,zero_mul,Real.rpow_zero,mul_one] using
    (SchwartzMap.le_seminorm' ℂ 0 j f u)
end Green64Analytic.Parity

end

end

/-! ## SourceAuxiliaryActualCellScale -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- True original source log-cell geometry after charging p from
D_C=da*db=p*D. If p≥9, the reduced physical scale
Z*D does not exceed the original Y=Z*U1*U2. No invented
dyadic approximation or new cell is introduced. -/
theorem source_auxiliary_actual_cell_reduced_scale434
    (F1 F2 : Finset ℕ) (U1 U2 h1 h2 : ℝ)
    (b1 b2 : ℕ → ℂ) (da db p D : ℕ) (Z Y : ℝ)
    (hU1 : 0 < U1) (hU2 : 0 < U2)
    (hh1 : h1 ≤ 1) (hh2 : h2 ≤ 1)
    (ha : sourceOriginalLogCellMask434 F1 U1 h1 b1 da ≠ 0)
    (hb : sourceOriginalLogCellMask434 F2 U2 h2 b2 db ≠ 0)
    (hp : 9 ≤ p) (hD : 0 < D) (hprod : p*D=da*db)
    (hZ : 1 ≤ Z) (hY : Y=Z*(U1*U2)) :
    1 ≤ Z*(D:ℝ) ∧ Z*(D:ℝ) ≤ Y := by
  obtain ⟨hda,hdaLo,hdaHi⟩ :=
    source_original_logcell_real_range434 F1 U1 h1 b1 hU1 hh1 da ha
  obtain ⟨hdb,hdbLo,hdbHi⟩ :=
    source_original_logcell_real_range434 F2 U2 h2 b2 hU2 hh2 db hb
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hp9 : (9:ℝ) ≤ p := by exact_mod_cast hp
  have hpR : (0:ℝ) < p := by linarith
  have hUP : 0 ≤ U1*U2 := by positivity
  have hprodR : (p:ℝ)*(D:ℝ)=(da:ℝ)*(db:ℝ) := by
    exact_mod_cast hprod
  have hhi : (da:ℝ)*(db:ℝ) ≤ 9*(U1*U2) := by
    have hh := mul_le_mul hdaHi hdbHi (Nat.cast_nonneg db)
      (by positivity : 0 ≤ 3*U1)
    nlinarith
  have hDmax : (D:ℝ) ≤ U1*U2 := by
    have h9 : 9*(U1*U2) ≤ (p:ℝ)*(U1*U2) :=
      mul_le_mul_of_nonneg_right hp9 hUP
    have hh : (p:ℝ)*(D:ℝ) ≤ (p:ℝ)*(U1*U2) :=
      hprodR.le.trans (hhi.trans h9)
    exact (mul_le_mul_iff_of_pos_left hpR).mp hh
  constructor
  · nlinarith
  · rw [hY]
    exact mul_le_mul_of_nonneg_left hDmax (by linarith)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAuxiliaryActualLogCap -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The actual source Y≤exp(3L/2) cap and reduced auxiliary
scale R≤Y imply log ceil(18AR)≤2L once a FIXED source constant
is absorbed into the unused half-log. No hypothesis on the
coefficient functions or on the prime-slot cores occurs. -/
theorem source_auxiliary_reduced_log_cap434
    (A L R Y : ℝ) (hA : 1 ≤ A)
    (hR : 1 ≤ R) (hRY : R ≤ Y)
    (hYmax : Y ≤ Real.exp (3*L/2))
    (hBudget : 2*Real.log (18*A+1) ≤ L) :
    Real.log ((⌈18*A*R⌉₊:ℕ):ℝ) ≤ 2*L := by
  have hAp : 0 < 18*A+1 := by linarith
  have hRp : 0 < R := by linarith
  have hYP : 0 < Y := lt_of_lt_of_le hRp hRY
  have hNpos : 0 < ⌈18*A*R⌉₊ := by
    have hh : 0 < 18*A*R := by positivity
    have hc : 18*A*R ≤ (⌈18*A*R⌉₊:ℝ) := Nat.le_ceil _
    exact_mod_cast hh.trans_le hc
  have hN : (⌈18*A*R⌉₊:ℝ) ≤ (18*A+1)*Y := by
    have hc : (⌈18*A*R⌉₊:ℝ) ≤ 18*A*R+1 :=
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ 18*A*R)).le
    calc
      _ ≤ 18*A*R+1 := hc
      _ ≤ (18*A+1)*Y := by
        have hprod : 18*A*R ≤ 18*A*Y :=
          mul_le_mul_of_nonneg_left hRY (by linarith)
        nlinarith
  have hexp : 18*A+1 ≤ Real.exp (L/2) := by
    calc
      _ = Real.exp (Real.log (18*A+1)) := (Real.exp_log hAp).symm
      _ ≤ Real.exp (L/2) := Real.exp_le_exp.mpr (by linarith)
  have hNexp : (⌈18*A*R⌉₊:ℝ) ≤ Real.exp (2*L) := by
    calc
      _ ≤ (18*A+1)*Y := hN
      _ ≤ Real.exp (L/2)*Real.exp (3*L/2) :=
        mul_le_mul hexp hYmax hYP.le (Real.exp_pos _).le
      _ = Real.exp (2*L) := by
        rw [←Real.exp_add]
        congr 1
        ring
  have hNp : (0:ℝ) < (⌈18*A*R⌉₊:ℕ) := by exact_mod_cast hNpos
  have hh := Real.log_le_log hNp hNexp
  simpa only [Real.log_exp] using hh

/-- A single sufficiently large logarithmic threshold works for
EVERY original source comparison cell and auxiliary prime choice. -/
theorem eventually_source_auxiliary_reduced_log_cap434
    (A : ℝ) (hA : 1 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ R Y : ℝ,
      1 ≤ R → R ≤ Y → Y ≤ Real.exp (3*L/2) →
      Real.log ((⌈18*A*R⌉₊:ℕ):ℝ) ≤ 2*L := by
  filter_upwards [eventually_ge_atTop (2*Real.log (18*A+1))]
    with L hLarge
  intro R Y hR hRY hYmax
  exact source_auxiliary_reduced_log_cap434 A L R Y
    hA hR hRY hYmax hLarge
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCutoffSup -/

section

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin

/-- The source zeroth logarithmic derivative supplies the endpoint cutoff
bound; no separately chosen sup-norm premise is necessary. -/
theorem source_original_cutoff_sup434
    (Cpsi L Y : ℝ) (Kpsi : ℕ → ℝ) (psi : ℝ → ℂ)
    (hY : 0 < Y)
    (hBudget : sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)))
    (n : ℕ) (hn : 0 < n) :
    ‖psi ((n:ℝ)/Y)‖ ≤ Kpsi 0 * L^Cpsi := by
  have hny : 0 < (n:ℝ)/Y := div_pos (Nat.cast_pos.mpr hn) hY
  have h0 := hBudget 0 (Real.log ((n:ℝ)/Y))
  simpa only [iteratedDeriv_zero,Real.exp_log hny,Nat.cast_zero,
    zero_add,mul_one] using h0
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalAmplitudeBudget -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- The actual endpoint amplitude has a fixed log exponent chosen before
any Fourier decay order. Both growing group counts are retained. -/
theorem source_original_amplitude_budget434
    (L Kg C0 K0 Cpsi Bpsi C Vs vmin : ℝ) (ea ec ns nb : ℕ)
    (hL : 1 ≤ L) (hKg : 1 ≤ Kg) (hC0 : 0 ≤ C0)
    (hK0 : 0 ≤ K0) (hBpsi : 0 ≤ Bpsi) (hC : 0 ≤ C)
    (hv : 0 < vmin) (hVs : vmin ≤ Vs)
    (hB : Bpsi ≤ K0*L^Cpsi) (hCB : C ≤ L^ec)
    (hns : (ns:ℝ) ≤ C0*Real.log L) (hnb : (nb:ℝ) ≤ C0*Real.log L) :
    Bpsi*(L^ea*C*(1/Vs)*Kg^(ns+nb+1)) ≤
      (K0*Kg/vmin)*L^(Cpsi+(ea:ℝ)+(ec:ℝ)+2*C0*Real.log Kg) := by
  have hLp : 0 < L := by linarith
  have hVp : 0 < Vs := hv.trans_le hVs
  have hInv := one_div_le_one_div_of_le hv hVs
  have hGroup := source_literal_group_card_log_budget Kg L C0 hKg hL hC0 ns nb hns hnb
  calc
    _ ≤ (K0*L^Cpsi)*(L^ea*L^ec*(1/vmin)*(Kg*L^(2*C0*Real.log Kg))) := by gcongr
    _ = _ := by simp only [Real.rpow_add hLp,Real.rpow_natCast]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceGlobalMomentPower -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 2500000

/-- The full endpoint divisor moment, after true support localization,
has a fixed logarithmic exponent. The support scale is Y, not Ncap. -/
theorem source_global_moment_power434
    (N : ℕ) (Amp Kamp Eamp Csupport Clog Y L : ℝ)
    (hL : 1 ≤ L) (hY : 0 ≤ Y) (hAmp : 0 ≤ Amp) (hK : 0 ≤ Kamp)
    (hCsupport : 0 ≤ Csupport) (hClog : 0 ≤ Clog)
    (hSupport : (N:ℝ) ≤ Csupport*Y)
    (hLog : Real.log (N:ℝ) ≤ Clog*L)
    (hAmpBound : Amp ≤ Kamp*L^Eamp) :
    Amp^2*(N:ℝ)*(1+Real.log (N:ℝ))^16 ≤
      Kamp^2*Csupport*(1+Clog)^16*Y*L^(2*Eamp+16) := by
  have hLp : 0 < L := by linarith
  have hLog0 : 0 ≤ Real.log (N:ℝ) := by
    by_cases hN : N = 0
    · simp [hN]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)
  have hLogBound : 1+Real.log (N:ℝ) ≤ (1+Clog)*L := by nlinarith
  calc
    _ ≤ (Kamp*L^Eamp)^2*(Csupport*Y)*((1+Clog)*L)^16 := by gcongr
    _ = _ := by
      rw [show 2*Eamp+16 = Eamp+Eamp+(16:ℕ) by push_cast; ring]
      simp only [Real.rpow_add hLp,Real.rpow_natCast]
      ring

/-- A genuine cutoff at ceil(A*Y) costs only A+1 on the physical scale. -/
theorem source_localized_support_scale434 (N : ℕ) (A Y : ℝ)
    (hA : 0 ≤ A) (hY : 1 ≤ Y) :
    ((min N (Nat.ceil (A*Y)):ℕ):ℝ) ≤ (A+1)*Y := by
  have hc : (Nat.ceil (A*Y):ℝ) < A*Y+1 :=
    Nat.ceil_lt_add_one (mul_nonneg hA (by linarith))
  have hm : ((min N (Nat.ceil (A*Y)):ℕ):ℝ) ≤ (Nat.ceil (A*Y):ℝ) := by
    exact_mod_cast min_le_right N (Nat.ceil (A*Y))
  nlinarith
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSquareAmplitude -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1800000

/-- The square-peeling coefficient retains the genuine extra factor L
and vmin, while its group constant remains independent of decay order. -/
theorem source_original_square_amplitude_budget434
    (L Kg C0 K0 Cpsi Bpsi C vmin : ℝ) (ea ec ns nb : ℕ)
    (hL : 1 ≤ L) (hKg : 1 ≤ Kg) (hC0 : 0 ≤ C0)
    (hK0 : 0 ≤ K0) (hBpsi : 0 ≤ Bpsi) (hC : 0 ≤ C) (hv : 0 < vmin)
    (hB : Bpsi ≤ K0*L^Cpsi) (hCB : C ≤ L^ec)
    (hns : (ns:ℝ) ≤ C0*Real.log L) (hnb : (nb:ℝ) ≤ C0*Real.log L) :
    Bpsi*(L^ea*C*(Kg^(ns+nb+1)*L*(1+2/(vmin*Real.log 2)))) ≤
      (K0*Kg*(1+2/(vmin*Real.log 2)))*
        L^(Cpsi+(ea:ℝ)+(ec:ℝ)+2*C0*Real.log Kg+1) := by
  have hLp : 0 < L := by linarith
  have hLog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hFac : 0 ≤ 1+2/(vmin*Real.log 2) := by positivity
  have hAmp := source_original_amplitude_budget434 L Kg C0 K0 Cpsi Bpsi C 1 1
    ea ec ns nb hL hKg hC0 hK0 hBpsi hC (by norm_num) le_rfl hB hCB hns hnb
  simp only [div_one,mul_one] at hAmp
  calc
    _ = (Bpsi*(L^ea*C*Kg^(ns+nb+1)))*L*(1+2/(vmin*Real.log 2)) := by ring
    _ ≤ ((K0*Kg)*L^(Cpsi+(ea:ℝ)+(ec:ℝ)+2*C0*Real.log Kg))*L*
      (1+2/(vmin*Real.log 2)) := by gcongr
    _ = _ := by simp only [Real.rpow_add hLp,Real.rpow_one]; ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceUniformCutoffMass -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap BigOperators
set_option maxHeartbeats 4000000
namespace Green64Analytic.CorrelationMellin

/-- Full Fourier L1 mass of the varying source cutoff family is a fixed log power. -/
theorem source_cutoff_family_fourier_mass
    (C B : ℝ) (K : ℕ → ℝ) (L : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : ∀ j, 0 ≤ K j) (hL : 1 ≤ L)
    (f : 𝓢(ℝ,ℂ)) (hSupp : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (hBudget : sourceLogDerivativeBudget C K L f) :
    (∫ xi : ℝ, ‖(𝓕 f) xi‖) ≤
      (4*B*K 0 + 16*B*(∑ j ∈ Finset.range 3, K j)) * L^(3*C) := by
  have hK0 := hK 0
  have hG : Integrable (fun xi : ℝ => ‖(𝓕 f) xi‖) := (𝓕 f).integrable.norm
  have hInt := source_cutoff_derivative_integral_bound f B
    (K 0*L^(C*((0:ℝ)+1))) 0 hB hSupp (by simpa using hBudget 0)
  have hPoint (xi : ℝ) : ‖(𝓕 f) xi‖ ≤ 2*B*K 0*L^C := by
    have hd := source_uniform_fourier_decay f 0 xi
    simp only [pow_zero,one_mul,Finset.range_one,Finset.sum_singleton] at hd
    exact hd.trans (by simpa [mul_assoc] using hInt)
  have hLow : (∫ xi in Set.Icc (-1:ℝ) 1, ‖(𝓕 f) xi‖) ≤ 4*B*K 0*L^C := by
    calc
      _ ≤ ∫ xi in Set.Icc (-1:ℝ) 1, 2*B*K 0*L^C :=
        setIntegral_mono_on hG.integrableOn
          (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
          measurableSet_Icc (fun xi hxi => hPoint xi)
      _ = _ := by
        rw [setIntegral_const,measureReal_def,Real.volume_Icc]
        norm_num
        ring
  have hTail : (∫ xi in {xi : ℝ | 1 ≤ |xi|}, ‖(𝓕 f) xi‖) ≤
      16*B*(∑ j ∈ Finset.range 3, K j)*L^(3*C) := by
    have hh := source_cutoff_family_fourier_tail C B K L 1 2
      hC hB hK hL (by norm_num) (by norm_num) f hSupp hBudget
    convert hh using 1 <;> norm_num <;> ring
  have hSub : (Set.Icc (-1:ℝ) 1)ᶜ ⊆ {xi : ℝ | 1 ≤ |xi|} := by
    intro xi hxi
    simp only [Set.mem_compl_iff,Set.mem_Icc] at hxi
    simp only [Set.mem_setOf_eq,le_abs]
    rcases not_and_or.mp hxi with h | h
    · right; linarith
    · left; linarith
  have hComp : (∫ xi in (Set.Icc (-1:ℝ) 1)ᶜ, ‖(𝓕 f) xi‖) ≤
      16*B*(∑ j ∈ Finset.range 3, K j)*L^(3*C) :=
    (setIntegral_mono_set hG.integrableOn
      (Filter.Eventually.of_forall (fun xi => norm_nonneg ((𝓕 f) xi)))
      hSub.eventuallySubset).trans hTail
  have hPow : L^C ≤ L^(3*C) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc
    _ = (∫ xi in Set.Icc (-1:ℝ) 1, ‖(𝓕 f) xi‖) +
        (∫ xi in (Set.Icc (-1:ℝ) 1)ᶜ, ‖(𝓕 f) xi‖) :=
      (integral_add_compl measurableSet_Icc hG).symm
    _ ≤ 4*B*K 0*L^C + 16*B*(∑ j ∈ Finset.range 3, K j)*L^(3*C) := add_le_add hLow hComp
    _ ≤ (4*B*K 0 + 16*B*(∑ j ∈ Finset.range 3, K j))*L^(3*C) := by
      nlinarith [mul_le_mul_of_nonneg_left hPow (by positivity : 0 ≤ 4*B*K 0)]

/-- A natural log-power bound, uniform in f AFTER L. The one-power reserve
absorbs the fixed support and derivative constants. -/
theorem eventually_source_cutoff_family_fourier_mass_power
    (C B : ℝ) (K : ℕ → ℝ) (e : ℕ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : ∀ j, 0 ≤ K j) (he : 3*C ≤ (e:ℝ)) :
    ∀ᶠ L : ℝ in atTop, ∀ f : 𝓢(ℝ,ℂ),
      tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-B) B →
      sourceLogDerivativeBudget C K L f →
      (∫ xi : ℝ, ‖(𝓕 f) xi‖) ≤ L^(e+1) := by
  let A := 4*B*K 0+16*B*(∑ j ∈ Finset.range 3, K j)
  have hS : 0 ≤ ∑ j ∈ Finset.range 3, K j := Finset.sum_nonneg (fun j hj => hK j)
  have hK0 := hK 0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_ge_atTop (max 1 A)] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hAL : A ≤ L := (le_max_right _ _).trans hL
  intro f hSupp hBudget
  have hp : L^(3*C) ≤ L^e := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hL1 he
  calc
    _ ≤ A*L^(3*C) := source_cutoff_family_fourier_mass C B K L hC hB hK hL1 f hSupp hBudget
    _ ≤ A*L^e := mul_le_mul_of_nonneg_left hp hA
    _ ≤ L*L^e := mul_le_mul_of_nonneg_right hAL (by positivity)
    _ = L^(e+1) := by rw [pow_succ]; ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceUniformCutoffSaving -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap BigOperators
set_option maxHeartbeats 4000000
namespace Green64Analytic.CorrelationMellin

/-- Uniform original-source Fourier tail saving: F is fixed before D;
the cutoff f is quantified after L and may vary with it. No hTail premise. -/
theorem eventually_source_cutoff_family_fourier_tail_saving
    (C B F : ℝ) (K : ℕ → ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hK : ∀ j, 0 ≤ K j) (hCF : C < F) (D : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ f : 𝓢(ℝ,ℂ),
      tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-B) B →
      sourceLogDerivativeBudget C K L f →
      (∫ xi in {xi : ℝ | L^F ≤ |xi|}, ‖(𝓕 f) xi‖) ≤ (L^D)⁻¹ := by
  have hDelta : 0 < F-C := sub_pos.mpr hCF
  obtain ⟨n,hn⟩ := exists_nat_gt ((C+F+(D:ℝ)+1)/(F-C))
  let N : ℕ := max 2 n
  have hN : 2 ≤ N := Nat.le_max_left _ _
  have hnN : (n:ℝ) ≤ N := by exact_mod_cast Nat.le_max_right 2 n
  have hExp : C*((N:ℝ)+1)-F*((N:ℝ)-1) ≤ -(D:ℝ)-1 := by
    have hm := (div_lt_iff₀ hDelta).mp hn
    have hh := mul_le_mul_of_nonneg_right hnN hDelta.le
    nlinarith
  let A : ℝ := 4*B*2^N*(∑ j ∈ Finset.range (N+1), K j) / ((N:ℝ)-1)
  have hN' : (1:ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hS : 0 ≤ ∑ j ∈ Finset.range (N+1), K j := Finset.sum_nonneg (fun j hj => hK j)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_ge_atTop (max 1 A)] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hAL : A ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  intro f hSupp hBudget
  have ht := source_cutoff_family_fourier_log_tail C B F K L N
    hC hB hK hL1 hN f hSupp hBudget
  have hPow := Real.rpow_le_rpow_of_exponent_le hL1 hExp
  have hEq : L^(-(D:ℝ)-1) = (L^D)⁻¹ / L := by
    rw [Real.rpow_sub hLp,Real.rpow_neg hLp.le,Real.rpow_natCast,Real.rpow_one]
  calc
    _ ≤ A * L^(C*((N:ℝ)+1)-F*((N:ℝ)-1)) := ht
    _ ≤ A * L^(-(D:ℝ)-1) := mul_le_mul_of_nonneg_left hPow hA
    _ = A * ((L^D)⁻¹ / L) := by rw [hEq]
    _ ≤ L * ((L^D)⁻¹ / L) := mul_le_mul_of_nonneg_right hAL (by positivity)
    _ = (L^D)⁻¹ := by field_simp
end Green64Analytic.CorrelationMellin

end

/-! ## PhysicalCutoffFourier -/

section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap BigOperators
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The genuine Mellin phase, with the real logarithm of a positive
physical scale when used below. -/
def b658MellinPhase434 (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((t * Real.log x) : ℂ))

/-- The positive Fourier inversion phase, including the factor 2*pi. -/
def b658FourierPhase434 (xi u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * xi * u) : ℂ))

theorem b658_mellin_phase_norm434 (t x : ℝ) :
    ‖b658MellinPhase434 t x‖ = 1 := by
  simpa only [b658MellinPhase434, Complex.ofReal_mul] using
    Complex.norm_exp_I_mul_ofReal (t * Real.log x)

theorem b658_fourier_phase_norm434 (xi u : ℝ) :
    ‖b658FourierPhase434 xi u‖ = 1 := by
  simpa only [b658FourierPhase434, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    Complex.norm_exp_I_mul_ofReal (2 * Real.pi * xi * u)

theorem b658_fourier_phase_star434 (xi u : ℝ) :
    star (b658FourierPhase434 xi u) = b658FourierPhase434 (-xi) u := by
  simp only [b658FourierPhase434, Complex.star_def, ← Complex.exp_conj,
    map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  push_cast
  ring

/-- Exact frequency placement: conjugating the FIRST endpoint supplies
the positive Fourier phase, while the original D phase gets -2*pi*xi.
The formula does not discard the spectral phase or absorb it into Knu. -/
theorem b658_fourier_mellin_frequency434 (zeta xi u D : ℝ) :
    star (b658FourierPhase434 (-xi) u) *
        b658MellinPhase434 (zeta - 2 * Real.pi * xi) D =
      b658MellinPhase434 zeta D *
        b658FourierPhase434 xi (u - Real.log D) := by
  rw [b658_fourier_phase_star434, neg_neg]
  unfold b658FourierPhase434 b658MellinPhase434
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The physical logarithmic cutoff uses n/(Z*D), with the actual D. -/
theorem b658_physical_log_scale434 (n Z D : ℝ)
    (hn : 0 < n) (hZ : 0 < Z) (hD : 0 < D) :
    Real.log (n / Z) - Real.log D = Real.log (n / (Z * D)) := by
  rw [Real.log_div hn.ne' hZ.ne',
    Real.log_div hn.ne' (mul_pos hZ hD).ne', Real.log_mul hZ.ne' hD.ne']
  ring

theorem b658_fourier_mellin_physical434 (zeta xi n Z D : ℝ)
    (hn : 0 < n) (hZ : 0 < Z) (hD : 0 < D) :
    star (b658FourierPhase434 (-xi) (Real.log (n / Z))) *
        b658MellinPhase434 (zeta - 2 * Real.pi * xi) D =
      b658MellinPhase434 zeta D *
        b658FourierPhase434 xi (Real.log (n / (Z * D))) := by
  rw [b658_fourier_mellin_frequency434,
    b658_physical_log_scale434 n Z D hn hZ hD]

/-- Integrability of the actual Fourier density times its unit phase. -/
theorem b658_fourier_density_integrable434 (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    Integrable (fun xi : ℝ => (𝓕 f) xi * b658FourierPhase434 xi u) := by
  have hF : Integrable (fun xi : ℝ => (𝓕 f) xi) := (𝓕 f).integrable
  apply hF.mul_bdd
  · exact (by unfold b658FourierPhase434; fun_prop : Continuous (fun xi : ℝ => b658FourierPhase434 xi u)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun xi => (b658_fourier_phase_norm434 xi u).le)

/-- Genuine Lebesgue Fourier inversion, not a formal measure surrogate.
The density is the Fourier transform of the supplied Schwartz cutoff. -/
theorem b658_fourier_inversion434 (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    (∫ xi : ℝ, (𝓕 f) xi * b658FourierPhase434 xi u) = f u := by
  calc
    _ = (𝓕⁻ ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) u := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards [] with xi
      rw [smul_eq_mul]
      conv_lhs => rw [mul_comm]
      congr 1
      unfold b658FourierPhase434
      congr 1
      simp only [RCLike.inner_apply, conj_trivial]
      push_cast
      ring
    _ = (𝓕⁻ (𝓕 f) : 𝓢(ℝ, ℂ)) u := by
      exact (congrFun (SchwartzMap.fourierInv_coe (𝓕 f)) u).symm
    _ = f u := congrArg (fun h : 𝓢(ℝ, ℂ) => h u) (FourierTransform.fourierInv_fourier_eq f)

/-- Exact cutoff separation with the two physically determined phases. -/
theorem b658_physical_cutoff_inversion434 (f : 𝓢(ℝ, ℂ))
    (zeta n Z D : ℝ) (hn : 0 < n) (hZ : 0 < Z) (hD : 0 < D) :
    (∫ xi : ℝ, (𝓕 f) xi *
      (star (b658FourierPhase434 (-xi) (Real.log (n / Z))) *
        b658MellinPhase434 (zeta - 2 * Real.pi * xi) D)) =
      b658MellinPhase434 zeta D * f (Real.log (n / (Z * D))) := by
  simp_rw [b658_fourier_mellin_physical434 zeta _ n Z D hn hZ hD]
  calc
    _ = b658MellinPhase434 zeta D *
        (∫ xi : ℝ, (𝓕 f) xi * b658FourierPhase434 xi (Real.log (n / (Z * D)))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with xi
      ring
    _ = _ := by rw [b658_fourier_inversion434]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## NativeFrameFourier -/

section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Positivity of the original complete edge product, with every shared
prime and every auxiliary multiplicity retained. -/
theorem b658_native_frame_divisor_pos434
    (x : MemoryIndependentState SP smallMod BP bigMod J ell)
    (frame : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    0 < b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x frame := by
  unfold b650NativeFrameD434 memoryIndependentD
  apply mul_pos
  · apply Finset.prod_pos
    intro g hg
    apply Finset.prod_pos
    intro j hj
    exact Nat.pos_of_ne_zero (NeZero.ne _)
  · apply Finset.prod_pos
    intro g hg
    apply mul_pos
    · apply Finset.prod_pos
      intro j hj
      exact Nat.pos_of_ne_zero (NeZero.ne _)
    · apply Finset.prod_pos
      intro j hj
      exact Nat.pos_of_ne_zero (NeZero.ne _)

/-- The literal positive original edge scalar at theta=0 is its full Knu
times the genuine Mellin phase. The complex logarithm is not replaced
without proving the equality at the actual natural divisor. -/
theorem b658_original_edge_mellin434 (K : ℂ) (zeta : ℝ) (D : ℕ) (k : ℤ) :
    originalEdgeScalar K zeta 0 D 1 k =
      K * b658MellinPhase434 zeta (D:ℝ) := by
  have hlog : Complex.log (D:ℂ) = (Real.log (D:ℝ):ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (Nat.cast_nonneg D : (0:ℝ) ≤ D)).symm
  unfold originalEdgeScalar originalOrientedKernel originalReturnPhase
  simp only [ite_true, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [hlog]
  unfold b658MellinPhase434
  congr 2
  push_cast
  ring

/-- Exact frequency dependence of ONE full original physical frame.
Every gate, normalization, original Knu and endpoint permutation remains
inside the same frame. -/
theorem b658_integer_frame_mellin434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta : ℝ) (k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (frame : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vs Vb Knu zeta 1 k x y frame =
      b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vs Vb Knu 0 1 k x y frame *
      b658MellinPhase434 zeta
        (b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ) := by
  unfold b650IntegerFrameScalar434
  split_ifs
  · rw [b658_original_edge_mellin434, b658_original_edge_mellin434]
    simp only [b658MellinPhase434, Complex.ofReal_zero, zero_mul, mul_zero,
      Complex.exp_zero, mul_one]
    ring
  · simp only [zero_mul]

/-- At a genuine positive physical position n, the endpoint Fourier
phase and the ORIGINAL full native frame give exactly n/(Z*D).
This is a frame identity before summing patterns, signs or marks. -/
theorem b658_integer_frame_fourier434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta xi Z : ℝ) (k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (hx : 0 < x.val.1.val) (hZ : 0 < Z)
    (frame : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns) :
    star (b658FourierPhase434 (-xi) (Real.log ((x.val.1.val:ℝ)/Z))) *
      b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vs Vb Knu (zeta-2*Real.pi*xi) 1 k x y frame =
      b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vs Vb Knu zeta 1 k x y frame *
      b658FourierPhase434 xi (Real.log ((x.val.1.val:ℝ) /
        (Z*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ)))) := by
  have hn : (0:ℝ) < x.val.1.val := by exact_mod_cast hx
  have hD : (0:ℝ) < b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame := by
    exact_mod_cast b658_native_frame_divisor_pos434 SP smallMod BP bigMod J ell m patterns x.val.2 frame
  rw [b658_integer_frame_mellin434 SP smallMod BP bigMod J ell m patterns positions q Vs Vb Knu
      (zeta-2*Real.pi*xi),
    b658_integer_frame_mellin434 SP smallMod BP bigMod J ell m patterns positions q Vs Vb Knu zeta]
  calc
    _ = b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vs Vb Knu 0 1 k x y frame *
      (star (b658FourierPhase434 (-xi) (Real.log ((x.val.1.val:ℝ)/Z))) *
        b658MellinPhase434 (zeta-2*Real.pi*xi)
          (b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ)) := by ring
    _ = _ := by rw [b658_fourier_mellin_physical434 zeta xi _ Z _ hn hZ hD]; ring

/-- The true Fourier integrand for each complete physical frame is
integrable; no formal integration or unspecified measure is used. -/
theorem b658_integer_frame_fourier_integrable434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta Z : ℝ) (k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (hx : 0 < x.val.1.val) (hZ : 0 < Z)
    (frame : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun xi : ℝ => (𝓕 f) xi *
      (star (b658FourierPhase434 (-xi) (Real.log ((x.val.1.val:ℝ)/Z))) *
        b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
          q Vs Vb Knu (zeta-2*Real.pi*xi) 1 k x y frame)) := by
  have h := (b658_fourier_density_integrable434 f
    (Real.log ((x.val.1.val:ℝ) /
      (Z*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ))))).mul_const
    (b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions q Vs Vb Knu zeta 1 k x y frame)
  convert h using 1
  funext xi
  rw [b658_integer_frame_fourier434 SP smallMod BP bigMod J ell m patterns positions q Vs Vb Knu zeta xi Z k x y hx hZ frame]
  ring

/-- Genuine cutoff insertion into the literal physical full frame. -/
theorem b658_integer_frame_cutoff_inversion434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta Z : ℝ) (k : ℤ)
    (x y : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
    (hx : 0 < x.val.1.val) (hZ : 0 < Z)
    (frame : MemoryPrimitiveEFrame (SG:=SG) BP J ell m patterns)
    (f : 𝓢(ℝ, ℂ)) :
    (∫ xi : ℝ, (𝓕 f) xi *
      (star (b658FourierPhase434 (-xi) (Real.log ((x.val.1.val:ℝ)/Z))) *
        b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
          q Vs Vb Knu (zeta-2*Real.pi*xi) 1 k x y frame)) =
      b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vs Vb Knu zeta 1 k x y frame *
      f (Real.log ((x.val.1.val:ℝ) /
        (Z*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ)))) := by
  simp_rw [b658_integer_frame_fourier434 SP smallMod BP bigMod J ell m patterns positions q Vs Vb Knu zeta _ Z k x y hx hZ frame]
  calc
    _ = b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
        q Vs Vb Knu zeta 1 k x y frame *
      (∫ xi : ℝ, (𝓕 f) xi * b658FourierPhase434 xi (Real.log ((x.val.1.val:ℝ) /
        (Z*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ))))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with xi
      ring
    _ = _ := by rw [b658_fourier_inversion434]
end Green64FullPhysicalE

end

end

/-! ## CutoffIntegralBudget -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap BigOperators
noncomputable section
namespace Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The exact retained-frequency saving reserve. It depends only on the
requested saving and the cutoff derivative exponent, before any source
tuple or later Schur exponent. -/
def b662CutoffSavingExponent434 (E C : ℝ) : ℝ :=
  E + (Nat.ceil (3*C) : ℝ) + 3

/-- Genuine Lebesgue integral on a measurable set. Only a pointwise
amplitude bound is used; the Fourier density is the actual transform. -/
theorem b662_fourier_integral_piece434
    (f : 𝓢(ℝ,ℂ)) (a : ℝ → ℂ) (S : Set ℝ) (hS : MeasurableSet S)
    (B : ℝ)
    (hInt : Integrable (fun v : ℝ => (𝓕 f) v * a v))
    (hAmp : ∀ v ∈ S, ‖a v‖ ≤ B) :
    ‖∫ v in S, (𝓕 f) v * a v‖ ≤ B * ∫ v in S, ‖(𝓕 f) v‖ := by
  have hF : Integrable (fun v : ℝ => ‖(𝓕 f) v‖) := (𝓕 f).integrable.norm
  calc
    _ ≤ ∫ v in S, ‖(𝓕 f) v * a v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in S, B * ‖(𝓕 f) v‖ := by
      apply setIntegral_mono_on hInt.norm.integrableOn
        (hF.const_mul B).integrableOn hS
      intro v hv
      rw [norm_mul, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hAmp v hv) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- Retained frequencies plus the actual complementary Fourier tail.
The global bound is used only on the tail and is not a signed saving. -/
theorem b662_fourier_integral_split434
    (f : 𝓢(ℝ,ℂ)) (a : ℝ → ℂ) (R Blo Bhi : ℝ)
    (hBlo : 0 ≤ Blo) (hBhi : 0 ≤ Bhi)
    (hInt : Integrable (fun v : ℝ => (𝓕 f) v * a v))
    (hLow : ∀ v : ℝ, |v| ≤ R → ‖a v‖ ≤ Blo)
    (hAll : ∀ v : ℝ, ‖a v‖ ≤ Bhi) :
    ‖∫ v : ℝ, (𝓕 f) v * a v‖ ≤
      Blo * (∫ v : ℝ, ‖(𝓕 f) v‖) +
      Bhi * (∫ v in {v : ℝ | R ≤ |v|}, ‖(𝓕 f) v‖) := by
  have hF : Integrable (fun v : ℝ => ‖(𝓕 f) v‖) := (𝓕 f).integrable.norm
  have hLo := b662_fourier_integral_piece434 f a (Set.Icc (-R) R)
    measurableSet_Icc Blo hInt
    (fun v hv => hLow v (abs_le.mpr hv))
  have hHi := b662_fourier_integral_piece434 f a (Set.Icc (-R) R)ᶜ
    measurableSet_Icc.compl Bhi hInt (fun v _ => hAll v)
  have hMass : (∫ v in Set.Icc (-R) R, ‖(𝓕 f) v‖) ≤
      ∫ v : ℝ, ‖(𝓕 f) v‖ :=
    setIntegral_le_integral hF (Eventually.of_forall (fun v => norm_nonneg _))
  have hSub : (Set.Icc (-R) R)ᶜ ⊆ {v : ℝ | R ≤ |v|} := by
    intro v hv
    simp only [Set.mem_compl_iff,Set.mem_Icc] at hv
    simp only [Set.mem_ofPred_eq,le_abs]
    rcases not_and_or.mp hv with h | h
    · right
      linarith
    · left
      linarith
  have hTail : (∫ v in (Set.Icc (-R) R)ᶜ, ‖(𝓕 f) v‖) ≤
      ∫ v in {v : ℝ | R ≤ |v|}, ‖(𝓕 f) v‖ :=
    setIntegral_mono_set hF.integrableOn
      (Eventually.of_forall (fun v => norm_nonneg _)) hSub.eventuallySubset
  calc
    _ = ‖(∫ v in Set.Icc (-R) R, (𝓕 f) v * a v) +
        (∫ v in (Set.Icc (-R) R)ᶜ, (𝓕 f) v * a v)‖ := by
      rw [integral_add_compl measurableSet_Icc hInt]
    _ ≤ ‖∫ v in Set.Icc (-R) R, (𝓕 f) v * a v‖ +
        ‖∫ v in (Set.Icc (-R) R)ᶜ, (𝓕 f) v * a v‖ := norm_add_le _ _
    _ ≤ Blo*(∫ v in Set.Icc (-R) R, ‖(𝓕 f) v‖) +
        Bhi*(∫ v in (Set.Icc (-R) R)ᶜ, ‖(𝓕 f) v‖) := add_le_add hLo hHi
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hMass hBlo)
      (mul_le_mul_of_nonneg_left hTail hBhi)

/-- The Fourier band exponent F and saving reserve are fixed before the
later absolute exponent Cglobal. Arbitrary tail precision is obtained
from the original smooth cutoff budget without enlarging the band.
Both cutoff and amplitude may vary AFTER L. -/
theorem b662_eventually_fourier_cutoff_saving434
    (E C B F : ℝ) (K : ℕ → ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK : ∀ j, 0 ≤ K j) (hCF : C < F)
    (Cglobal : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (f : 𝓢(ℝ,ℂ)) (a : ℝ → ℂ) (X : ℝ),
      0 ≤ X → tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-B) B →
      sourceLogDerivativeBudget C K L f →
      Integrable (fun v : ℝ => (𝓕 f) v * a v) →
      (∀ v : ℝ, |v| ≤ L^F →
        ‖a v‖ ≤ X * L^(-b662CutoffSavingExponent434 E C)) →
      (∀ v : ℝ, ‖a v‖ ≤ X * L^Cglobal) →
      ‖∫ v : ℝ, (𝓕 f) v * a v‖ ≤ X * L^(-E) := by
  let e : ℕ := Nat.ceil (3*C)
  let D : ℕ := Nat.ceil (E+Cglobal+2)
  let A : ℝ := b662CutoffSavingExponent434 E C
  have he : 3*C ≤ (e:ℝ) := Nat.le_ceil _
  have hD : E+Cglobal+2 ≤ (D:ℝ) := Nat.le_ceil _
  filter_upwards [
    eventually_source_cutoff_family_fourier_mass_power C B K e hC hB hK he,
    eventually_source_cutoff_family_fourier_tail_saving C B F K hC hB hK hCF D,
    eventually_ge_atTop (2:ℝ)] with L hMass hTail hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  intro f a X hX hSupp hBudget hInt hLow hAll
  have hSplit := b662_fourier_integral_split434 f a (L^F)
    (X*L^(-A)) (X*L^Cglobal) (by positivity) (by positivity) hInt hLow hAll
  have hLowEq : (X*L^(-A))*L^(e+1) = X*L^(-E-2) := by
    calc
      _ = X*(L^(-A)*L^((e+1:ℕ):ℝ)) := by rw [Real.rpow_natCast]; ring
      _ = X*L^(-A+((e+1:ℕ):ℝ)) := by rw [Real.rpow_add hLp]
      _ = _ := by
        dsimp [A,b662CutoffSavingExponent434,e]
        push_cast
        congr 2
        ring
  have hTailEq : (X*L^Cglobal)*(L^D)⁻¹ = X*L^(Cglobal-(D:ℝ)) := by
    rw [Real.rpow_sub hLp,Real.rpow_natCast]
    ring
  have hTailPow : L^(Cglobal-(D:ℝ)) ≤ L^(-E-2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hTwo : (2:ℝ) ≤ L^(2:ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hReserve : 2*L^(-E-2) ≤ L^(-E) := by
    calc
      _ ≤ L^(2:ℝ)*L^(-E-2) :=
        mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg hLp.le _)
      _ = L^((2:ℝ)+(-E-2)) := by rw [Real.rpow_add hLp]
      _ = _ := by congr 1; ring
  calc
    _ ≤ (X*L^(-A))*(∫ v : ℝ, ‖(𝓕 f) v‖) +
        (X*L^Cglobal)*(∫ v in {v : ℝ | L^F ≤ |v|}, ‖(𝓕 f) v‖) := hSplit
    _ ≤ (X*L^(-A))*L^(e+1) + (X*L^Cglobal)*(L^D)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_left (hMass f hSupp hBudget) (by positivity))
        (mul_le_mul_of_nonneg_left (hTail f hSupp hBudget) (by positivity))
    _ = X*L^(-E-2) + X*L^(Cglobal-(D:ℝ)) := by rw [hLowEq,hTailEq]
    _ ≤ X*L^(-E-2)+X*L^(-E-2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hTailPow hX)
    _ = X*(2*L^(-E-2)) := by ring
    _ ≤ X*L^(-E) := mul_le_mul_of_nonneg_left hReserve hX
end Green64Analytic.CorrelationMellin

end

end

/-! ## SourceActualUniformWindowTruncation -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff RealInnerProductSpace
set_option maxHeartbeats 4000000
namespace Green64Analytic.CorrelationMellin

/-- The true original logarithmic window has exactly the fixed source support. -/
theorem source_actual_log_window_tsupport_interval
    (A : ℝ) (psi1 : ℝ → ℂ) (hA : 1 ≤ A)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) :
    tsupport (sourceActualLogWindow psi1) ⊆ Set.Icc (-Real.log A) (Real.log A) := by
  change closure (Function.support (sourceActualLogWindow psi1)) ⊆ _
  apply isClosed_Icc.closure_subset_iff.mpr
  intro u hu
  have hn : psi1 (Real.exp u) ≠ 0 := by
    intro hz
    exact hu (by simp only [sourceActualLogWindow,hz,mul_zero])
  obtain ⟨hLo,hHi⟩ := hSupport (Real.exp u) hn
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hInv : 0 < 1/A := one_div_pos.mpr hAp
  have hl := Real.log_le_log hInv hLo
  have hh := Real.log_le_log (Real.exp_pos u) hHi
  simpa only [one_div,Real.log_inv,Real.log_exp,Set.mem_Icc] using And.intro hl hh

/-- Original cutoff family uniform truncation. The fixed exponent F may be
chosen before accuracy D or the residual family; psi1 is chosen after L. -/
theorem eventually_source_actual_uniform_original_weight_truncation
    (A C F : ℝ) (K : ℕ → ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hK : ∀ j, 0 ≤ K j) (hCF : C < F) (D : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (psi1 : ℝ → ℂ)
      (hSmooth : ContDiff ℝ ∞ psi1)
      (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A),
      sourceLogDerivativeBudget C K L (sourceActualLogWindow psi1) →
      ∀ (Y v1 : ℝ) (w : ℕ), 0 < Y →
      ‖sourceActualOriginalWindowWeight Y psi1 v1 w -
        sourceActualOriginalTruncatedWindowWeight
          A Y psi1 hA hSmooth hSupport v1 (L^F) w‖ ≤ (L^D)⁻¹ := by
  have hLog : 0 ≤ Real.log A := Real.log_nonneg hA
  have hTail := eventually_source_cutoff_family_fourier_tail_saving C (Real.log A) F K
    hC hLog hK hCF D
  filter_upwards [hTail,eventually_ge_atTop (1:ℝ)] with L hTailL hL
  intro psi1 hSmooth hSupport hBudget Y v1 w hY
  by_cases hw : w = 0
  · subst w
    simpa [sourceActualOriginalWindowWeight,sourceActualOriginalTruncatedWindowWeight]
      using (by positivity : (0:ℝ) ≤ (L^D)⁻¹)
  · have hwPos : 0 < w := Nat.pos_of_ne_zero hw
    let f : 𝓢(ℝ,ℂ) := sourceActualLogWindowSchwartz A psi1 hA hSmooth hSupport
    have hSupp : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-Real.log A) (Real.log A) :=
      source_actual_log_window_tsupport_interval A psi1 hA hSupport
    have hTailf := hTailL f hSupp hBudget
    let u : ℝ := Real.log ((w:ℝ)/Y)
    let M : ℂ := ∫ xi in {xi : ℝ | |xi| < L^F},
      Complex.exp (((2*Real.pi*⟪xi,u⟫:ℝ):ℂ)*Complex.I) • (𝓕 f) xi
    have hIdentity : sourceActualOriginalWindowWeight Y psi1 v1 w =
        (𝓕⁻ (𝓕 f)) u * sourcePhase w v1 :=
      source_actual_original_window_schwartz_fourier_exact
        A Y psi1 v1 w hA hY hwPos hSmooth hSupport
    have hTrunc : ‖(𝓕⁻ (𝓕 f)) u - M‖ ≤
        (∫ xi in {xi : ℝ | L^F ≤ |xi|}, ‖(𝓕 f) xi‖) :=
      source_actual_schwartz_fourier_truncation_error f (L^F) u
    simp only [sourceActualOriginalTruncatedWindowWeight,if_neg hw]
    change ‖sourceActualOriginalWindowWeight Y psi1 v1 w - M*sourcePhase w v1‖ ≤ _
    rw [hIdentity, ← sub_mul,norm_mul,sourcePhase_norm,mul_one]
    exact hTrunc.trans hTailf
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualNormalizedLogBudget -/

section

open scoped BigOperators ContDiff
namespace Green64Analytic.CorrelationMellin
set_option maxHeartbeats 5000000

noncomputable def sourceNormalizedLogDerivativeConstants (A : ℝ) (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  A * ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*K (j-i)

theorem source_exp_complex_iterated_deriv (j : ℕ) :
    iteratedDeriv j (fun u : ℝ => (Real.exp u : ℂ)) = fun u : ℝ => (Real.exp u : ℂ) := by
  have hd : deriv (fun u : ℝ => (Real.exp u : ℂ)) = fun u : ℝ => (Real.exp u : ℂ) := by
    funext u
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (Real.hasDerivAt_exp u)).deriv
  induction j with
  | zero => rfl
  | succ j ih => rw [iteratedDeriv_succ,ih,hd]

/-- Multiplying the source logarithmic cutoff by exp(u) changes only the fixed
derivative constants; the exponent Cpsi and its quantifier order are preserved. -/
theorem source_actual_normalized_log_derivative_budget
    (A C L : ℝ) (K : ℕ → ℝ) (psi1 : ℝ → ℂ)
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hK : ∀ j, 0 ≤ K j) (hL : 1 ≤ L)
    (hSmooth : ContDiff ℝ ∞ psi1)
    (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (hBudget : sourceLogDerivativeBudget C K L (fun u => psi1 (Real.exp u))) :
    sourceLogDerivativeBudget C (sourceNormalizedLogDerivativeConstants A K) L
      (sourceActualLogWindow psi1) := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  intro j u
  by_cases hu : u ∈ Set.Icc (-Real.log A) (Real.log A)
  · have hExp : Real.exp u ≤ A := by
      calc
        _ ≤ Real.exp (Real.log A) := Real.exp_le_exp.mpr hu.2
        _ = A := Real.exp_log hAp
    have he : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp u : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp Real.contDiff_exp
    have hg : ContDiff ℝ ∞ (fun u : ℝ => psi1 (Real.exp u)) :=
      hSmooth.comp Real.contDiff_exp
    have hProd : sourceActualLogWindow psi1 =
        (fun u : ℝ => (Real.exp u : ℂ)) * (fun u : ℝ => psi1 (Real.exp u)) := rfl
    rw [hProd,iteratedDeriv_mul (he.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
    calc
      _ ≤ ∑ i ∈ Finset.range (j+1),
          ‖(j.choose i : ℂ) * iteratedDeriv i (fun u : ℝ => (Real.exp u : ℂ)) u *
            iteratedDeriv (j-i) (fun u => psi1 (Real.exp u)) u‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (j+1),
          A*(j.choose i : ℝ)*K (j-i)*L^(C*((j:ℝ)+1)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [source_exp_complex_iterated_deriv,norm_mul,norm_mul,Complex.norm_natCast,
          Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos u)]
        have hkji := hK (j-i)
        have hPow : L^(C*((j-i:ℕ):ℝ)+C) ≤ L^(C*((j:ℝ)+1)) := by
          apply Real.rpow_le_rpow_of_exponent_le hL
          have hh : ((j-i:ℕ):ℝ) ≤ j := by exact_mod_cast Nat.sub_le j i
          nlinarith
        have hb := hBudget (j-i) u
        have hPow' : L^(C*(((j-i:ℕ):ℝ)+1)) ≤ L^(C*((j:ℝ)+1)) := by
          convert hPow using 1 <;> congr 1 <;> ring
        calc
          _ ≤ (j.choose i : ℝ)*A*(K (j-i)*L^(C*(((j-i:ℕ):ℝ)+1))) := by gcongr
          _ ≤ A*(j.choose i : ℝ)*K (j-i)*L^(C*((j:ℝ)+1)) := by
            have hh := mul_le_mul_of_nonneg_left hPow' (by positivity : 0 ≤ A*(j.choose i : ℝ)*K (j-i))
            nlinarith
      _ = sourceNormalizedLogDerivativeConstants A K j * L^(C*((j:ℝ)+1)) := by
        simp only [sourceNormalizedLogDerivativeConstants,Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  · have hs := source_actual_log_window_tsupport_interval A psi1 hA hSupport
    have hZero : iteratedFDeriv ℝ j (sourceActualLogWindow psi1) u = 0 := by
      by_contra hn
      exact hu (hs ((support_iteratedFDeriv_subset j) hn))
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv,hZero,norm_zero]
    unfold sourceNormalizedLogDerivativeConstants
    exact mul_nonneg (mul_nonneg hAp.le
      (Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _) (hK _))))
      (Real.rpow_nonneg hLp.le _)

 theorem source_normalized_log_derivative_constants_nonneg
    (A : ℝ) (K : ℕ → ℝ) (hA : 0 ≤ A) (hK : ∀ j, 0 ≤ K j) (j : ℕ) :
    0 ≤ sourceNormalizedLogDerivativeConstants A K j := by
  unfold sourceNormalizedLogDerivativeConstants
  exact mul_nonneg hA (Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _) (hK _)))
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualUniformCutoffTailMeanSquare -/

section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff
namespace Green64Analytic.CorrelationMellin
/- Actual unrestricted Fourier tail error: use the original full-minus-truncated
window and fixed-order four-factor coefficient mass. No hApprox or hTail. -/
theorem eventually_source_actual_uniform_original_cutoff_tail_mean_square
    (A C F : ℝ) (K : ℕ → ℝ) (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hK : ∀ j, 0 ≤ K j) (hCF : C < F) (D : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (psi1 : ℝ → ℂ)
      (hSmooth : ContDiff ℝ ∞ psi1)
      (hSupport : ∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A),
    sourceLogDerivativeBudget C K L (sourceActualLogWindow psi1) →
    ∀ (small long R : Finset ℕ) (a b M0 P P0 R0 : ℕ)
      (alpha bs bp d : ℕ → ℂ) {q : ℕ}
      (chi : DirichletCharacter ℂ q) (sigma0 sigma1 t0 t1 : ℝ),
    ∀ (Y v1 Am Cs Ap Ar : ℝ),
    0 < Y → t0 ≤ t1 → 1 ≤ a →
    1 ≤ M0 → 1 ≤ P → 1 ≤ P0 → 1 ≤ R0 →
    0 ≤ Am → 0 ≤ Cs → 0 ≤ Ap → 0 ≤ Ar →
    Finset.Icc a b ⊆ Finset.Icc M0 (2*M0) →
    small ⊆ Finset.Icc P (2*P) →
    long ⊆ Finset.Icc P0 (2*P0) →
    R ⊆ Finset.Icc R0 (2*R0) →
    (∀ m ∈ Finset.Icc a b, ‖alpha m‖ ≤ Am) →
    (∀ ps ∈ small, ‖bs ps‖ ≤ Cs) →
    (∀ p ∈ long, ‖bp p‖ ≤ Ap) →
    (∀ r ∈ R, ‖d r‖ ≤ Ar) →
    let U : ℝ := ((M0*P*P0*R0:ℕ):ℝ)
    let N : ℕ := (2*M0)*(2*P)*(2*P0)*(2*R0)
    (∫ t in Set.Icc t0 t1,
      ‖sourceActualSmoothFourDyadAt small long R a b
        (sourceActualOriginalWindowWeight Y psi1 v1)
        alpha bs bp d chi sigma0 sigma1 t -
      sourceActualSmoothFourDyadAt small long R a b
        (sourceActualOriginalTruncatedWindowWeight
          A Y psi1 hA hSmooth hSupport v1 (L^F))
        alpha bs bp d chi sigma0 sigma1 t‖^2) ≤
      ((t1-t0)+16*(N:ℝ)*(1+Real.log N)) *
        (((L^D)⁻¹)^2*((Am*Cs*Ap*Ar)^2/U*(1+Real.log N)^64)) := by
  have hTrunc := eventually_source_actual_uniform_original_weight_truncation
    A C F K hA hC hK hCF D
  filter_upwards [hTrunc,eventually_ge_atTop (3:ℝ)] with L hTruncL hL3
  intro psi1 hSmooth hSupport hBudget
  have hTruncL := hTruncL psi1 hSmooth hSupport hBudget
  intro small long R a b M0 P P0 R0 alpha bs bp d q chi
    sigma0 sigma1 t0 t1 Y v1 Am Cs Ap Ar
    hY ht ha hM0 hP hP0 hR0 hAm hCs hAp hAr
    hM hSmall hLong hR hAlpha hBs hBp hd
  let cutoff : ℕ → ℂ := fun w =>
    sourceActualOriginalWindowWeight Y psi1 v1 w -
    sourceActualOriginalTruncatedWindowWeight A Y psi1 hA hSmooth hSupport v1 (L^F) w
  have hIdentity (t : ℝ) :
    sourceActualSmoothFourDyadAt small long R a b
      (sourceActualOriginalWindowWeight Y psi1 v1)
      alpha bs bp d chi sigma0 sigma1 t -
    sourceActualSmoothFourDyadAt small long R a b
      (sourceActualOriginalTruncatedWindowWeight A Y psi1 hA hSmooth hSupport v1 (L^F))
      alpha bs bp d chi sigma0 sigma1 t =
    sourceActualSmoothFourDyadAt small long R a b
      cutoff alpha bs bp d chi sigma0 sigma1 t := by
    unfold sourceActualSmoothFourDyadAt
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [cutoff]
    ring
  simp_rw [hIdentity]
  exact source_actual_smooth_fourdyad_mean_square
    small long R a b M0 P P0 R0 cutoff alpha bs bp d chi
    sigma0 sigma1 t0 t1 Am Cs Ap Ar ((L^D)⁻¹)
    ha hM0 hP hP0 hR0 hAm hCs hAp hAr (by positivity)
    hM hSmall hLong hR hAlpha hBs hBp hd
    (fun w => hTruncL Y v1 w hY) ht
end Green64Analytic.CorrelationMellin

end

/-! ## SourceUniformCutoffTailNumerics -/

section

namespace Green64Analytic.CorrelationMellin
set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

/-- Explicit tail normalization: translated mean square costs a fixed
logarithmic power, independent of the exponential Mellin interval length. -/
theorem source_uniform_four_cutoff_tail_log_crush
    (L U T : ℝ) (N : ℕ) (E D : ℕ)
    (hL : 3 ≤ L) (hConst : 258*3^65 ≤ L)
    (hU : 0 < U) (hT : T ≤ U)
    (hN : (N:ℝ) = 16*U)
    (hNexp : (N:ℝ) ≤ Real.exp (2*L)) :
    (2*T+16*(N:ℝ)*(1+Real.log N)) *
      (((L^(E+D+100))⁻¹)^2*((L^E)^2/U*(1+Real.log N)^64))
      ≤ (L^D)⁻¹ := by
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hNp : 0 < (N:ℝ) := by rw [hN]; positivity
  have hLog0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by
    have hn : 1 ≤ N := by
      have hh : 0 < N := by exact_mod_cast hNp
      omega
    exact_mod_cast hn)
  have hLog : Real.log (N:ℝ) ≤ 2*L := by
    calc
      _ ≤ Real.log (Real.exp (2*L)) := Real.log_le_log hNp hNexp
      _ = 2*L := Real.log_exp _
  have hLog' : 1+Real.log (N:ℝ) ≤ 3*L := by linarith
  have hFactor : (2*T+16*(N:ℝ)*(1+Real.log N))/U ≤
      258*(1+Real.log N) := by
    apply (div_le_iff₀ hU).mpr
    rw [hN]
    have hg := hLog0
    rw [hN] at hg
    nlinarith [mul_nonneg hU.le hg]
  have hScale :
      258*(1+Real.log N)^65 ≤ L^66 := by
    calc
      _ ≤ 258*(3*L)^65 := by gcongr
      _ = (258*3^65)*L^65 := by rw [mul_pow]; ring
      _ ≤ L*L^65 := mul_le_mul_of_nonneg_right hConst (by positivity)
      _ = L^66 := by rw [pow_succ]; ring
  have hNum : (L^E)^2*L^66*L^D ≤ (L^(E+D+100))^2 := by
    calc
      _ = L^(2*E+66+D) := by rw [← pow_mul]; simp only [pow_add]; ring
      _ ≤ L^(2*(E+D+100)) := pow_le_pow_right₀ hLone (by omega)
      _ = (L^(E+D+100))^2 := by rw [← pow_mul]; congr 1; omega
  have hFrac :
      ((L^(E+D+100))⁻¹)^2*(L^E)^2*L^66 ≤ (L^D)⁻¹ := by
    have hh : (L^E)^2*L^66/(L^(E+D+100))^2 ≤ 1/L^D :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        (by simpa only [one_mul] using hNum)
    simpa only [div_eq_mul_inv, inv_pow, mul_one, mul_assoc, mul_comm, mul_left_comm] using hh
  calc
    _ = ((2*T+16*(N:ℝ)*(1+Real.log N))/U) *
          (((L^(E+D+100))⁻¹)^2*(L^E)^2) * (1+Real.log N)^64 := by ring
    _ ≤ (258*(1+Real.log N)) *
          (((L^(E+D+100))⁻¹)^2*(L^E)^2) * (1+Real.log N)^64 := by
      gcongr
    _ = (((L^(E+D+100))⁻¹)^2*(L^E)^2) *
          (258*(1+Real.log N)^65) := by ring
    _ ≤ (((L^(E+D+100))⁻¹)^2*(L^E)^2)*L^66 :=
      mul_le_mul_of_nonneg_left hScale (by positivity)
    _ ≤ (L^D)⁻¹ := hFrac
end Green64Analytic.CorrelationMellin

end

/-! ## SourceActualUniformTailScales -/

section

open MeasureTheory Filter
namespace Green64Analytic.CorrelationMellin
set_option maxHeartbeats 4000000

/-- The original free-scale and product comparison imply the centered
Mellin interval is no longer than the full reciprocal product scale. -/
theorem source_actual_tail_time_le_product
    (L U Y Hprime Carc Ccomp : ℝ) (P : ℕ)
    (hL : 0 < L) (hU : 0 < U) (hY : 0 < Y)
    (hH : 0 < Hprime) (hC : 0 < Ccomp) (hP : 1 ≤ P)
    (hComp : Y ≤ Ccomp*U)
    (hFree : 2*L*Ccomp*(P:ℝ)*L^Carc ≤ Hprime) :
    2*L*Y/(Hprime/L^Carc) ≤ U := by
  have hPow : 0 < L^Carc := Real.rpow_pos_of_pos hL _
  have hP' : (1:ℝ) ≤ P := by exact_mod_cast hP
  rw [div_div_eq_mul_div]
  apply (div_le_iff₀ hH).mpr
  calc
    2*L*Y*L^Carc ≤ 2*L*(Ccomp*U)*L^Carc := by gcongr
    _ ≤ U*(2*L*Ccomp*(P:ℝ)*L^Carc) := by
      nlinarith [mul_le_mul_of_nonneg_left hP' (by positivity : 0 ≤ U*(2*L*Ccomp*L^Carc))]
    _ ≤ U*Hprime := mul_le_mul_of_nonneg_left hFree hU.le

/-- Original source product comparability and Y<=exp(3L/2) give the
native mean-square upper support bound, with no new scale premise. -/
theorem eventually_source_actual_tail_product_upper
    (Ccomp : ℝ) (hC : 0 < Ccomp) :
    ∀ᶠ L : ℝ in atTop, ∀ (U Y : ℝ) (N : ℕ),
      (N:ℝ) = 16*U → U ≤ Ccomp*Y → Y ≤ Real.exp (3*L/2) →
      (N:ℝ) ≤ Real.exp (2*L) := by
  filter_upwards [eventually_ge_atTop (2*Real.log (16*Ccomp))] with L hL
  intro U Y N hN hComp hY
  have hConst : 16*Ccomp ≤ Real.exp (L/2) := by
    calc
      _ = Real.exp (Real.log (16*Ccomp)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (L/2) := Real.exp_le_exp.mpr (by linarith)
  calc
    (N:ℝ) = 16*U := hN
    _ ≤ (16*Ccomp)*Y := by nlinarith
    _ ≤ (16*Ccomp)*Real.exp (3*L/2) := mul_le_mul_of_nonneg_left hY (by positivity)
    _ ≤ Real.exp (L/2)*Real.exp (3*L/2) := mul_le_mul_of_nonneg_right hConst (Real.exp_pos _).le
    _ = Real.exp (2*L) := by rw [← Real.exp_add]; congr 1; ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceUniformGrid -/

section

set_option maxHeartbeats 2500000
open MeasureTheory Function
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- A common arithmetic grid for all fixed simplex dimensions. -/
def gridLower (b h : ℝ) (k : ℕ) (j : Fin k) : ℝ :=
  b + (j.val : ℝ) * h
def gridUpper (b h : ℝ) (k : ℕ) (j : Fin k) : ℝ :=
  b + ((j.val+1 : ℕ) : ℝ) * h

theorem gridUpper_eq_lower_add (b h : ℝ) (k : ℕ) (j : Fin k) :
    gridUpper b h k j = gridLower b h k j + h := by
  simp only [gridUpper, gridLower, Nat.cast_add, Nat.cast_one]
  ring

theorem gridLower_le_upper (b h : ℝ) (k : ℕ) (j : Fin k)
    (hh : 0 ≤ h) : gridLower b h k j ≤ gridUpper b h k j := by
  rw [gridUpper_eq_lower_add]
  linarith

theorem grid_separated (b h : ℝ) (k : ℕ) (hh : 0 ≤ h) :
    ∀ i j : Fin k, i < j → gridUpper b h k i ≤ gridLower b h k j := by
  intro i j hij
  have hnat : i.val + 1 ≤ j.val := by omega
  have hcast : ((i.val+1 : ℕ) : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hnat
  have := mul_le_mul_of_nonneg_right hcast hh
  dsimp [gridLower, gridUpper]
  linarith

/-- Every point strictly above b inside [b,b+k*h] is in one of the
half-open arithmetic grid cells. No non-integer or irrational endpoint
is silently excluded. -/
theorem grid_cover_coordinate
    (b h t : ℝ) (k : ℕ) (hh : 0 < h)
    (hbt : b < t) (htk : t ≤ b + (k:ℝ)*h) :
    ∃ j : Fin k,
      gridLower b h k j < t ∧
      t ≤ gridUpper b h k j ∧
      gridUpper b h k j ≤ t + h := by
  let r : ℝ := (t-b)/h
  have hrpos : 0 < r := div_pos (sub_pos.mpr hbt) hh
  have hrk : r ≤ (k : ℝ) := by
    dsimp [r]
    apply (div_le_iff₀ hh).mpr
    linarith
  let q : ℕ := ⌈r⌉₊
  have hqpos : 0 < q := Nat.ceil_pos.mpr hrpos
  have hqk : q ≤ k := Nat.ceil_le.mpr hrk
  let j : Fin k := ⟨q-1, by dsimp [q]; omega⟩
  have hqminus : ((q-1:ℕ):ℝ) < r := by
    exact Nat.lt_ceil.mp (by dsimp [q]; omega)
  have hqge : r ≤ (q:ℝ) := Nat.le_ceil r
  have hqidentity : ((q-1:ℕ):ℝ) + 1 = (q:ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ q))
  have hdiv : r * h = t-b := by
    dsimp [r]
    field_simp
  refine ⟨j, ?_, ?_, ?_⟩
  · dsimp [gridLower, j]
    nlinarith [mul_lt_mul_of_pos_right hqminus hh]
  · dsimp [gridUpper, j]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hqge hh.le]
  · dsimp [gridUpper, j]
    push_cast
    nlinarith [mul_lt_mul_of_pos_right hqminus hh]

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceGridCover -/

section

set_option maxHeartbeats 3000000
open MeasureTheory Function
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

noncomputable def gridStep (b : ℝ) (k : ℕ) : ℝ :=
  (1-b)/(k:ℝ)

theorem gridStep_pos (b : ℝ) (k : ℕ)
    (hb1 : b < 1) (hk : 0 < k) : 0 < gridStep b k := by
  exact div_pos (sub_pos.mpr hb1) (by exact_mod_cast hk)

theorem gridStep_scale (b : ℝ) (k : ℕ) (hk : 0 < k) :
    b + (k:ℝ)*gridStep b k = 1 := by
  unfold gridStep
  have hkn : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp
  ring

theorem gridStep_le (b : ℝ) (k : ℕ) (hb1 : b < 1) (hk : 0 < k)
    (j : Fin k) : gridUpper b (gridStep b k) k j ≤ 1 := by
  have hnat : j.val+1 ≤ k := by omega
  have hcast : ((j.val+1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast hnat
  have hh : 0 ≤ gridStep b k :=
    (gridStep_pos b k hb1 hk).le
  have hm := mul_le_mul_of_nonneg_right hcast hh
  have hscale := gridStep_scale b k hk
  dsimp [gridUpper]
  linarith

noncomputable def admissibleGridCells (d k : ℕ) (b h δ : ℝ) :
    Finset (Fin d → Fin k) := by
  classical
  exact Finset.univ.filter
    (fun c => (∑ i : Fin d, gridUpper b h k (c i)) ≤ 1-b-δ/2)

def lowerBoundary (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) :=
  ⋃ i : Fin d, {t | t i = b}

theorem lowerBoundary_null (d : ℕ) (b : ℝ) :
    (volume : Measure (Fin d → ℝ)) (lowerBoundary d b) = 0 := by
  unfold lowerBoundary
  rw [measure_iUnion_null_iff]
  intro i
  have hh := MeasureTheory.Measure.pi_hyperplane
      (fun _ : Fin d => (volume : Measure ℝ)) i b
  change (volume : Measure (Fin d → ℝ)) {t | t i = b} = 0
  rw [volume_pi]
  exact hh

/-- The true δ-truncated source simplex is contained in admissible
frozen exponent-grid rectangles up to exactly the boundary hyperplanes
where a coordinate equals b. -/
theorem truncated_subset_grid_union_or_boundary
    (d k : ℕ) (b h δ : ℝ)
    (hb : 0 < b) (hδ : 0 ≤ δ) (hh : 0 < h)
    (hscale : b + (k:ℝ)*h = 1)
    (hmesh : (d:ℝ)*h ≤ δ/2) :
    sourceRegion d b (1-δ) ⊆
       sourceGridUnion d k (gridLower b h k) (gridUpper b h k)
         (admissibleGridCells d k b h δ) ∪ lowerBoundary d b := by
  classical
  intro t ht
  by_cases hGood : ∀ i : Fin d, b < t i
  · have hTop (i : Fin d) : t i ≤ b + (k:ℝ)*h := by
      have hBound := (sourceRegion_subset_box d b (1-δ) hb.le ht).2 i
      linarith
    have hchoice (i : Fin d) :=
      grid_cover_coordinate b h (t i) k hh (hGood i) (hTop i)
    let c : Fin d → Fin k := fun i => (hchoice i).choose
    have hcell (i : Fin d) :
        gridLower b h k (c i) < t i ∧
        t i ≤ gridUpper b h k (c i) ∧
        gridUpper b h k (c i) ≤ t i + h :=
      (hchoice i).choose_spec
    have hsum : (∑ i : Fin d, gridUpper b h k (c i)) ≤
        (∑ i : Fin d, t i) + (d:ℝ)*h := by
      calc
        _ ≤ ∑ i : Fin d, (t i + h) :=
          Finset.sum_le_sum (fun i _ => (hcell i).2.2)
        _ = _ := by simp [Finset.sum_add_distrib]
    have hroom : (∑ i : Fin d, gridUpper b h k (c i)) ≤
        1-b-δ/2 := by
      have htroom := ht.2
      linarith
    left
    change t ∈ ⋃ c ∈ admissibleGridCells d k b h δ,
      sourceCellSet d (fun i => gridLower b h k (c i))
        (fun i => gridUpper b h k (c i))
    apply Set.mem_iUnion.mpr
    refine ⟨c, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨?_, ?_⟩
    · simp [admissibleGridCells, hroom]
    · exact fun i => ⟨(hcell i).1, (hcell i).2.1⟩
  · right
    push Not at hGood
    obtain ⟨i, hi⟩ := hGood
    have hlo := ht.1 i
    have heq : t i = b := le_antisymm hi hlo
    exact Set.mem_iUnion.mpr ⟨i, heq⟩

/-- The source δ-truncated simplex is a.e. contained in the finite
fixed-grid union, not merely its topological closure. -/
theorem truncated_ae_subset_grid
    (d k : ℕ) (b h δ : ℝ)
    (hb : 0 < b) (hδ : 0 ≤ δ) (hh : 0 < h)
    (hscale : b + (k:ℝ)*h = 1)
    (hmesh : (d:ℝ)*h ≤ δ/2) :
    sourceRegion d b (1-δ) ≤ᵐ[(volume : Measure (Fin d → ℝ))]
       sourceGridUnion d k (gridLower b h k) (gridUpper b h k)
         (admissibleGridCells d k b h δ) := by
  apply ae_le_set.mpr
  have hsub := truncated_subset_grid_union_or_boundary
    d k b h δ hb hδ hh hscale hmesh
  apply measure_mono_null _ (lowerBoundary_null d b)
  intro t ht
  exact (hsub ht.1).resolve_left ht.2

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceGridMass -/

section

set_option maxHeartbeats 3000000
open MeasureTheory Function
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

noncomputable def reciprocalProduct (d : ℕ) (t : Fin d → ℝ) : ℝ :=
  ∏ i, (t i)⁻¹

theorem reciprocalProduct_integrableOn_source
    (d : ℕ) (b w : ℝ) (hb : 0 < b) :
    IntegrableOn (reciprocalProduct d) (sourceRegion d b w) := by
  let f : (Fin d → ℝ) → ℝ :=
    fun t => ∏ i : Fin d, (max b (t i))⁻¹
  have hc : Continuous f := by
    dsimp [f]
    apply continuous_finsetProd
    intro i _
    apply Continuous.inv₀
    · exact continuous_const.max (continuous_apply i)
    · intro t
      exact ne_of_gt (hb.trans_le (le_max_left _ _))
  have hint : IntegrableOn f (sourceRegion d b w) :=
    hc.continuousOn.integrableOn_compact
      (sourceRegion_compact d b w hb.le)
  apply IntegrableOn.congr_fun hint
  · intro t ht
    unfold f reciprocalProduct
    apply Finset.prod_congr rfl
    intro i _
    rw [max_eq_right (ht.1 i)]
  · exact (sourceRegion_closed d b w).measurableSet

theorem reciprocalProduct_nonneg_source
    (d : ℕ) (b w : ℝ) (hb : 0 < b)
    (t : Fin d → ℝ) (ht : t ∈ sourceRegion d b w) :
    0 ≤ reciprocalProduct d t := by
  unfold reciprocalProduct
  apply Finset.prod_nonneg
  intro i _
  exact inv_nonneg.mpr (hb.trans_le (ht.1 i)).le

/-- Exact real reciprocal measure of an arbitrary finite separated
source prime-exponent grid, bounded by the full positive source
reciprocal integral. -/
theorem sourceGrid_reciprocal_mass_le_source
    (d k : ℕ) (b w : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b) (hbu : ∀ j, b ≤ u j)
    (huv : ∀ j, u j ≤ v j)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i)) :
    (∑ c ∈ S, ∏ i : Fin d,
        Real.log (v (c i) / u (c i))) ≤
      (∫ t in sourceRegion d b w, reciprocalProduct d t) := by
  let cell : (Fin d → Fin k) → Set (Fin d → ℝ) :=
    fun c => sourceCellSet d (fun i => u (c i)) (fun i => v (c i))
  have hSub (c : Fin d → Fin k) (hc : c ∈ S) :
      cell c ⊆ sourceRegion d b w :=
    sourceCellSet_subset_sourceRegion d b w
      (fun i => u (c i)) (fun i => v (c i))
      (fun i => hbu (c i)) (hroom c hc)
  have hMeas (c : Fin d → Fin k) (hc : c ∈ S) :
      MeasurableSet (cell c) :=
    sourceCellSet_measurable d (fun i => u (c i)) (fun i => v (c i))
  have hInt (c : Fin d → Fin k) (hc : c ∈ S) :
      IntegrableOn (reciprocalProduct d) (cell c) :=
    (reciprocalProduct_integrableOn_source d b w hb).mono_set (hSub c hc)
  have hDisj : Set.Pairwise (↑S) (Disjoint on cell) := by
    intro c hc c' hc' hne
    exact sourceGridCells_disjoint d k u v hsep c c' hne
  have hSplit :
      (∫ t in sourceGridUnion d k u v S, reciprocalProduct d t) =
      ∑ c ∈ S, ∫ t in cell c, reciprocalProduct d t := by
    change (∫ t in ⋃ c ∈ S, cell c, reciprocalProduct d t) = _
    exact integral_biUnion_finset S hMeas hDisj hInt
  have hGridSubset :
      sourceGridUnion d k u v S ⊆ sourceRegion d b w := by
    intro t ht
    change t ∈ ⋃ c ∈ S, cell c at ht
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hcin, htcell⟩ := Set.mem_iUnion.mp hc
    exact hSub c hcin htcell
  have hNonneg :
      0 ≤ᵐ[(volume : Measure (Fin d → ℝ)).restrict (sourceRegion d b w)]
        reciprocalProduct d := by
    filter_upwards [ae_restrict_mem (sourceRegion_closed d b w).measurableSet] with t ht
    exact reciprocalProduct_nonneg_source d b w hb t ht
  have hMassBound :
      (∫ t in sourceGridUnion d k u v S, reciprocalProduct d t) ≤
      (∫ t in sourceRegion d b w, reciprocalProduct d t) :=
    setIntegral_mono_set (reciprocalProduct_integrableOn_source d b w hb)
      hNonneg (Filter.Eventually.of_forall hGridSubset)
  calc
    _ = ∑ c ∈ S, ∫ t in cell c, reciprocalProduct d t := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (sourceCellSet_reciprocal_integral d
        (fun i => u (c i)) (fun i => v (c i))
        (fun i => hb.trans_le (hbu (c i))) (fun i => huv (c i))).symm
    _ = (∫ t in sourceGridUnion d k u v S, reciprocalProduct d t) := hSplit.symm
    _ ≤ _ := hMassBound

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceGridUpper -/

section

set_option maxHeartbeats 3000000
open MeasureTheory Function
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- The exact whole finite grid has an O(d*h/b²) Darboux error.
Its constant depends on the integrable original reciprocal density,
not on the number of grid cells. -/
theorem finite_source_grid_kernel_upper
    (d k : ℕ) (b w h : ℝ) (u v : Fin k → ℝ)
    (S : Finset (Fin d → Fin k))
    (hb : 0 < b) (hh : 0 ≤ h)
    (hbu : ∀ j, b ≤ u j)
    (huv : ∀ j, u j ≤ v j)
    (hwidth : ∀ j, v j - u j ≤ h)
    (hsep : ∀ i j : Fin k, i < j → v i ≤ u j)
    (hroom : ∀ c ∈ S, b ≤ w - ∑ i : Fin d, v (c i)) :
    (∫ t in sourceGridUnion d k u v S, sourceKernel d w t) ≤
      (∑ c ∈ S,
        (w - ∑ i : Fin d, u (c i))⁻¹ *
          (∏ i : Fin d, Real.log (v (c i) / u (c i)))) +
        ((d:ℝ)*h/b^2) *
          (∫ t in sourceRegion d b w, reciprocalProduct d t) := by
  let E : ℝ := ((d:ℝ)*h/b^2)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let cell : (Fin d → Fin k) → Set (Fin d → ℝ) :=
    fun c => sourceCellSet d (fun i => u (c i)) (fun i => v (c i))
  have hSub (c : Fin d → Fin k) (hc : c ∈ S) :
      cell c ⊆ sourceRegion d b w :=
    sourceCellSet_subset_sourceRegion d b w
      (fun i => u (c i)) (fun i => v (c i))
      (fun i => hbu (c i)) (hroom c hc)
  have hMeas (c : Fin d → Fin k) (hc : c ∈ S) :
      MeasurableSet (cell c) :=
    sourceCellSet_measurable d (fun i => u (c i)) (fun i => v (c i))
  have hInt (c : Fin d → Fin k) (hc : c ∈ S) :
      IntegrableOn (sourceKernel d w) (cell c) :=
    (sourceKernel_integrableOn d b w hb).mono_set (hSub c hc)
  have hDisj : Set.Pairwise (↑S) (Disjoint on cell) := by
    intro c hc c' hc' hne
    exact sourceGridCells_disjoint d k u v hsep c c' hne
  have hSplit :
      (∫ t in sourceGridUnion d k u v S, sourceKernel d w t) =
      ∑ c ∈ S, ∫ t in cell c, sourceKernel d w t := by
    change (∫ t in ⋃ c ∈ S, cell c, sourceKernel d w t) = _
    exact integral_biUnion_finset S hMeas hDisj hInt
  let Q : (Fin d → Fin k) → ℝ := fun c =>
    ∏ i : Fin d, Real.log (v (c i) / u (c i))
  let W : (Fin d → Fin k) → ℝ := fun c =>
    (w - ∑ i : Fin d, u (c i))⁻¹
  have hCell (c : Fin d → Fin k) (hc : c ∈ S) :
      (∫ t in cell c, sourceKernel d w t) ≤ (W c + E) * Q c := by
    exact (sourceCellSet_true_kernel_darboux_bounds
      d b w h (fun i => u (c i)) (fun i => v (c i))
      hb hh (fun i => hbu (c i)) (fun i => huv (c i))
      (fun i => hwidth (c i)) (hroom c hc)).2
  have hMass : (∑ c ∈ S, Q c) ≤
      (∫ t in sourceRegion d b w, reciprocalProduct d t) :=
    sourceGrid_reciprocal_mass_le_source d k b w u v S
      hb hbu huv hsep hroom
  have hErr : E * (∑ c ∈ S, Q c) ≤
      E * (∫ t in sourceRegion d b w, reciprocalProduct d t) :=
    mul_le_mul_of_nonneg_left hMass hE
  calc
    _ = ∑ c ∈ S, ∫ t in cell c, sourceKernel d w t := hSplit
    _ ≤ ∑ c ∈ S, (W c + E) * Q c := by
      apply Finset.sum_le_sum
      intro c hc
      exact hCell c hc
    _ = (∑ c ∈ S, W c * Q c) + E * (∑ c ∈ S, Q c) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ c ∈ S, W c * Q c) +
          E * (∫ t in sourceRegion d b w, reciprocalProduct d t) :=
      add_le_add_right hErr _
    _ = _ := rfl

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceTruncatedGridBound -/

section

set_option maxHeartbeats 4000000
open MeasureTheory Function
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Global finite grid estimate for the *full literal source integral*
on the δ-truncated simplex, using fixed k and unchanged w=1
dependent-last-prime denominator. The finite lower sum is exactly
the one in the source prime-grid theorem. -/
theorem truncated_source_integral_le_fixed_grid
    (d k : ℕ) (b δ : ℝ)
    (hb : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) (hk : 0 < k)
    (hmesh : (d:ℝ)*gridStep b k ≤ δ/2) :
    (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) ≤
      (∑ c ∈ admissibleGridCells d k b (gridStep b k) δ,
        (1 - ∑ i : Fin d, gridLower b (gridStep b k) k (c i))⁻¹ *
        ∏ i : Fin d, Real.log
          (gridUpper b (gridStep b k) k (c i) /
           gridLower b (gridStep b k) k (c i))) +
      ((d:ℝ)*gridStep b k/b^2) *
        (∫ t in sourceRegion d b 1, reciprocalProduct d t) := by
  let h : ℝ := gridStep b k
  let u : Fin k → ℝ := gridLower b h k
  let v : Fin k → ℝ := gridUpper b h k
  let S : Finset (Fin d → Fin k) := admissibleGridCells d k b h δ
  have hh : 0 < h := gridStep_pos b k hb1 hk
  have hscale : b + (k:ℝ)*h = 1 := gridStep_scale b k hk
  have hbu (j : Fin k) : b ≤ u j := by
    dsimp [u, gridLower]
    have hn : (0:ℝ) ≤ (j.val:ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hn hh.le]
  have huv (j : Fin k) : u j ≤ v j :=
    gridLower_le_upper b h k j hh.le
  have hwidth (j : Fin k) : v j - u j ≤ h := by
    dsimp [u, v]
    rw [gridUpper_eq_lower_add]
    linarith
  have hsep (i j : Fin k) (hij : i < j) : v i ≤ u j :=
    grid_separated b h k hh.le i j hij
  have hroom (c : Fin d → Fin k) (hc : c ∈ S) :
      b ≤ 1 - ∑ i : Fin d, v (c i) := by
    have hhroom : (∑ i : Fin d, v (c i)) ≤ 1-b-δ/2 := by
      simpa only [S, v, admissibleGridCells, Finset.mem_filter,
        Finset.mem_univ, true_and] using hc
    linarith
  have hFullSub : sourceGridUnion d k u v S ⊆
      sourceRegion d b 1 := by
    intro t ht
    change t ∈ ⋃ c ∈ S, sourceCellSet d
      (fun i => u (c i)) (fun i => v (c i)) at ht
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hcin, htcell⟩ := Set.mem_iUnion.mp hc
    exact sourceCellSet_subset_sourceRegion d b 1
      (fun i => u (c i)) (fun i => v (c i))
      (fun i => hbu (c i)) (hroom c hcin) htcell
  have hGridMeas : MeasurableSet (sourceGridUnion d k u v S) := by
    unfold sourceGridUnion
    apply Finset.measurableSet_biUnion
    intro c hc
    exact sourceCellSet_measurable d (fun i => u (c i)) (fun i => v (c i))
  have hIntGrid : IntegrableOn (sourceKernel d 1)
      (sourceGridUnion d k u v S) :=
    (sourceKernel_integrableOn d b 1 hb).mono_set hFullSub
  have hPosGrid :
      0 ≤ᵐ[(volume : Measure (Fin d → ℝ)).restrict (sourceGridUnion d k u v S)]
        sourceKernel d 1 := by
    filter_upwards [ae_restrict_mem hGridMeas] with t ht
    exact (sourceKernel_bound d b 1 hb t (hFullSub ht)).1
  have hCover : sourceRegion d b (1-δ) ≤ᵐ[
      (volume : Measure (Fin d → ℝ))] sourceGridUnion d k u v S := by
    exact truncated_ae_subset_grid d k b h δ hb hδ.le hh hscale
      (by simpa only [h] using hmesh)
  have hLower :
      (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) ≤
        (∫ t in sourceGridUnion d k u v S, sourceKernel d 1 t) :=
    setIntegral_mono_set hIntGrid hPosGrid hCover
  have hUpper := finite_source_grid_kernel_upper d k b 1 h u v S
    hb hh.le hbu huv hwidth hsep hroom
  exact hLower.trans hUpper

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceRectangleExhaustion -/

section

set_option maxHeartbeats 3000000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

theorem gridStep_tendsto_zero (b : ℝ) :
    Tendsto (fun k : ℕ => gridStep b k) atTop (𝓝 0) := by
  have hInv : Tendsto (fun k : ℕ => ((k:ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := hInv.const_mul (1-b)
  simpa only [gridStep, div_eq_mul_inv, mul_zero] using h

/-- Actual quantified inner-rectangle Darboux exhaustion for the
unaltered source simplex integral, with a single finite arithmetic
grid independent of the later prime cutoff L. -/
theorem source_truncated_inner_rectangle_exhaustion
    (d : ℕ) (b δ ε : ℝ)
    (hb : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ (d:ℝ)*gridStep b k ≤ δ/2 ∧
      (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) ≤
        (∑ c ∈ admissibleGridCells d k b (gridStep b k) δ,
          (1 - ∑ i : Fin d, gridLower b (gridStep b k) k (c i))⁻¹ *
          ∏ i : Fin d, Real.log
            (gridUpper b (gridStep b k) k (c i) /
             gridLower b (gridStep b k) k (c i))) + ε := by
  let R : ℝ := ∫ t in sourceRegion d b 1, reciprocalProduct d t
  have hStep := gridStep_tendsto_zero b
  have hD : Tendsto (fun k : ℕ => (d:ℝ)*gridStep b k)
      atTop (𝓝 0) := by
    simpa using hStep.const_mul (d:ℝ)
  have hErr : Tendsto (fun k : ℕ =>
        ((d:ℝ)*gridStep b k/b^2)*R)
      atTop (𝓝 0) := by
    have hh := (hD.div_const (b^2)).mul_const R
    simpa only [zero_div, zero_mul] using hh
  have hMeshEv : ∀ᶠ k : ℕ in atTop,
      (d:ℝ)*gridStep b k < δ/2 := by
    exact hD.eventually (isOpen_Iio.mem_nhds (half_pos hδ))
  have hErrEv : ∀ᶠ k : ℕ in atTop,
      ((d:ℝ)*gridStep b k/b^2)*R < ε := by
    exact hErr.eventually (isOpen_Iio.mem_nhds hε)
  have hKEv : ∀ᶠ k : ℕ in atTop, 0 < k :=
    eventually_gt_atTop 0
  obtain ⟨k, hk, hm, he⟩ :=
    (hKEv.and (hMeshEv.and hErrEv)).exists
  refine ⟨k, hk, hm.le, ?_⟩
  have hfixed := truncated_source_integral_le_fixed_grid
    d k b δ hb hb1 hδ hk hm.le
  dsimp [R] at he
  linarith

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceRectangleEventually -/

section

set_option maxHeartbeats 3000000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Every sufficiently fine common arithmetic grid exhausts the
truncated source simplex, not merely one specially chosen grid. -/
theorem source_truncated_inner_rectangle_eventually
    (d : ℕ) (b δ ε : ℝ)
    (hb : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      0 < k ∧ (d:ℝ)*gridStep b k ≤ δ/2 ∧
      (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) ≤
        (∑ c ∈ admissibleGridCells d k b (gridStep b k) δ,
          (1 - ∑ i : Fin d, gridLower b (gridStep b k) k (c i))⁻¹ *
          ∏ i : Fin d, Real.log
            (gridUpper b (gridStep b k) k (c i) /
             gridLower b (gridStep b k) k (c i))) + ε := by
  let R : ℝ := ∫ t in sourceRegion d b 1, reciprocalProduct d t
  have hStep := gridStep_tendsto_zero b
  have hD : Tendsto (fun k : ℕ => (d:ℝ)*gridStep b k)
      atTop (𝓝 0) := by
    simpa using hStep.const_mul (d:ℝ)
  have hErr : Tendsto (fun k : ℕ =>
        ((d:ℝ)*gridStep b k/b^2)*R)
      atTop (𝓝 0) := by
    have hh := (hD.div_const (b^2)).mul_const R
    simpa only [zero_div, zero_mul] using hh
  have hMeshEv : ∀ᶠ k : ℕ in atTop,
      (d:ℝ)*gridStep b k < δ/2 :=
    hD.eventually (isOpen_Iio.mem_nhds (half_pos hδ))
  have hErrEv : ∀ᶠ k : ℕ in atTop,
      ((d:ℝ)*gridStep b k/b^2)*R < ε :=
    hErr.eventually (isOpen_Iio.mem_nhds hε)
  filter_upwards [eventually_gt_atTop (0:ℕ), hMeshEv, hErrEv]
      with k hk hm he
  refine ⟨hk, hm.le, ?_⟩
  have hfixed := truncated_source_integral_le_fixed_grid
    d k b δ hb hb1 hδ hk hm.le
  dsimp [R] at he
  linarith

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceDensityFinite -/

section

set_option maxHeartbeats 3200000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

noncomputable def truncatedDimTerm (d : ℕ) (b δ : ℝ) : ℝ :=
  (∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t) /
    ((d+1).factorial : ℝ)

/-- The genuine d=0 one-prime integral on the zero-dimensional
coordinate space is one whenever the truncated region is nonempty. -/
theorem truncatedDimTerm_zero (b δ : ℝ) (hbd : b ≤ 1-δ) :
    truncatedDimTerm 0 b δ = 1 := by
  have hreg : sourceRegion 0 b (1-δ) = Set.univ := by
    ext t
    simp [sourceRegion, hbd]
  simp [truncatedDimTerm, hreg, sourceKernel, Finset.univ_eq_empty,
    volume_pi]
  change ((Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ).toReal : ℝ) = 1
  rw [Measure.pi_empty_univ]
  norm_num

theorem truncatedDimTerm_succ (n : ℕ) (b δ : ℝ) :
    truncatedDimTerm (n+1) b δ = truncatedSourceTerm n b δ := by
  rfl

/-- Includes the one-prime d=0 term **and** all d=n+1 terms with
exact (d+1)! normalization, without overcounting rough integers. -/
theorem truncatedSourceDensity_eq_finite_dimensions
    (N : ℕ) (b δ : ℝ)
    (hb : 0 < b) (hδ : 0 ≤ δ)
    (hbd : b ≤ 1-δ)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b) :
    truncatedSourceDensity b δ =
      ∑ d ∈ Finset.range (N+1), truncatedDimTerm d b δ := by
  calc
    _ = 1 + ∑ n ∈ Finset.range N, truncatedSourceTerm n b δ :=
      truncatedSourceDensity_finite_cutoff N b δ hb hδ hcut
    _ = (∑ n ∈ Finset.range N, truncatedDimTerm (n+1) b δ) +
          truncatedDimTerm 0 b δ := by
      rw [truncatedDimTerm_zero b δ hbd]
      simp_rw [truncatedDimTerm_succ]
      ring
    _ = _ := (Finset.sum_range_succ' (fun d => truncatedDimTerm d b δ) N).symm

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceFiniteGridDarboux -/

section

set_option maxHeartbeats 3800000
open Filter Topology MeasureTheory
open scoped BigOperators
namespace Green64Analytic.SourceSimplexGeometry

/-- Literal frozen lower-box source mass with the correct 1/(d+1)!
and a single arithmetic grid shared by all dimensions. -/
noncomputable def sourceGridLowerTerm
    (d k : ℕ) (b δ : ℝ) : ℝ :=
  (∑ c ∈ admissibleGridCells d k b (gridStep b k) δ,
      (1 - ∑ i : Fin d, gridLower b (gridStep b k) k (c i))⁻¹ *
      ∏ i : Fin d, Real.log
        (gridUpper b (gridStep b k) k (c i) /
         gridLower b (gridStep b k) k (c i))) /
          ((d+1).factorial : ℝ)

/-- Dimension-by-dimension ε-approximation, with the true source
integral and the unchanged factorial on both sides. -/
theorem truncatedDimTerm_eventually_le_grid
    (d : ℕ) (b δ ε : ℝ)
    (hb : 0 < b) (hb1 : b < 1)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      0 < k ∧ (d:ℝ)*gridStep b k ≤ δ/2 ∧
        truncatedDimTerm d b δ ≤ sourceGridLowerTerm d k b δ + ε := by
  let f : ℝ := ((d+1).factorial : ℝ)
  have hf0 : 0 < f := by
    dsimp [f]
    exact_mod_cast Nat.factorial_pos (d+1)
  have hf1 : (1:ℝ) ≤ f := by
    dsimp [f]
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos (d+1)))
  have herror : ε/f ≤ ε := by
    apply (div_le_iff₀ hf0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hf1 hε.le]
  filter_upwards [source_truncated_inner_rectangle_eventually
    d b δ ε hb hb1 hδ hε] with k hk
  obtain ⟨hkpos, hmesh, hbound⟩ := hk
  refine ⟨hkpos, hmesh, ?_⟩
  let I : ℝ := ∫ t in sourceRegion d b (1-δ), sourceKernel d 1 t
  let B : ℝ := ∑ c ∈ admissibleGridCells d k b (gridStep b k) δ,
    (1 - ∑ i : Fin d, gridLower b (gridStep b k) k (c i))⁻¹ *
      ∏ i : Fin d, Real.log
        (gridUpper b (gridStep b k) k (c i) /
         gridLower b (gridStep b k) k (c i))
  change I/f ≤ B/f + ε
  change I ≤ B+ε at hbound
  calc
    I/f ≤ (B+ε)/f := div_le_div_of_nonneg_right hbound hf0.le
    _ = B/f + ε/f := add_div _ _ _
    _ ≤ B/f + ε := add_le_add_right herror _

/-- All finite source dimensions, including d=0, are simultaneously
approximated by one common, fixed grid. -/
theorem truncatedSourceDensity_eventually_grid_lower
    (N : ℕ) (b δ ε : ℝ)
    (hb : 0 < b) (hb1 : b < 1)
    (hδ : 0 < δ) (hbd : b ≤ 1-δ) (hε : 0 < ε)
    (hcut : 1 ≤ ((N+2:ℕ):ℝ)*b) :
    ∀ᶠ k : ℕ in atTop,
      0 < k ∧
      (∀ d ∈ Finset.range (N+1), (d:ℝ)*gridStep b k ≤ δ/2) ∧
      truncatedSourceDensity b δ ≤
        (∑ d ∈ Finset.range (N+1),
          sourceGridLowerTerm d k b δ) + ε := by
  let D : Finset ℕ := Finset.range (N+1)
  let den : ℝ := (D.card:ℝ)+1
  let η : ℝ := ε/den
  have hden : 0 < den := by dsimp [den]; positivity
  have hη : 0 < η := div_pos hε hden
  have hper : ∀ d ∈ D,
      ∀ᶠ k : ℕ in atTop,
        0 < k ∧ (d:ℝ)*gridStep b k ≤ δ/2 ∧
        truncatedDimTerm d b δ ≤ sourceGridLowerTerm d k b δ + η := by
    intro d hd
    exact truncatedDimTerm_eventually_le_grid d b δ η hb hb1 hδ hη
  have hAll : ∀ᶠ k : ℕ in atTop,
      ∀ d ∈ D, 0 < k ∧ (d:ℝ)*gridStep b k ≤ δ/2 ∧
        truncatedDimTerm d b δ ≤ sourceGridLowerTerm d k b δ + η :=
    (Filter.eventually_all_finset D).mpr hper
  filter_upwards [hAll, eventually_gt_atTop (0:ℕ)] with k hAllk hk
  have hmesh (d : ℕ) (hd : d ∈ D) :
      (d:ℝ)*gridStep b k ≤ δ/2 := (hAllk d hd).2.1
  have hSum :
      (∑ d ∈ D, truncatedDimTerm d b δ) ≤
        (∑ d ∈ D, sourceGridLowerTerm d k b δ) +
        (D.card:ℝ)*η := by
    calc
      _ ≤ ∑ d ∈ D, (sourceGridLowerTerm d k b δ + η) := by
        apply Finset.sum_le_sum
        intro d hd
        exact (hAllk d hd).2.2
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hErr : (D.card:ℝ)*η ≤ ε := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    have hnonneg : (0:ℝ) ≤ (D.card:ℝ) := Nat.cast_nonneg _
    dsimp [den]
    nlinarith [mul_nonneg hε.le hnonneg]
  have hEq := truncatedSourceDensity_eq_finite_dimensions
    N b δ hb hδ.le hbd hcut
  refine ⟨hk, ?_, ?_⟩
  · simpa only [D] using hmesh
  · rw [hEq]
    simpa only [D] using (hSum.trans (add_le_add_right hErr _))

end Green64Analytic.SourceSimplexGeometry

end

/-! ## SourceUniformWindowEnergyNumerics -/

section

namespace Green64Analytic.CorrelationMellin
set_option maxHeartbeats 4000000

/-- Pay the derived full Fourier mass at a fixed natural exponent. -/
theorem source_uniform_window_mass_reserve (L mass : ℝ) (e D : ℕ)
    (hL : 1 ≤ L) (hm : 0 ≤ mass) (hMass : mass ≤ L^(e+1)) :
    mass^2*(L^(D+2*(e+1)+2))⁻¹ ≤ (L^(D+2))⁻¹ := by
  have hp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs := (sq_le_sq₀ hm (by positivity)).mpr hMass
  have hFactor : (L^(e+1))^2*L^(D+2) = L^(D+2*(e+1)+2) := by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  calc
    _ ≤ (L^(e+1))^2*(L^(D+2*(e+1)+2))⁻¹ := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = (L^(D+2))⁻¹ := by rw [←hFactor]; field_simp

/-- Two errors with two-power reserve meet the original requested saving. -/
theorem source_uniform_window_split_reserve (L : ℝ) (D : ℕ) (hL : 3 ≤ L) :
    2*(L^(D+2))⁻¹+2*(L^(D+2))⁻¹ ≤ (L^D)⁻¹ := by
  have hp : 0 < L := by linarith
  have h4 : (4:ℝ) ≤ L^2 := by nlinarith
  have hNum : 4*L^D ≤ L^(D+2) := by
    rw [pow_add]
    calc
      4*L^D ≤ L^2*L^D := mul_le_mul_of_nonneg_right h4 (pow_nonneg hp.le D)
      _ = L^D*L^2 := mul_comm _ _
  have hh : 4/L^(D+2) ≤ 1/L^D :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hNum)
  convert hh using 1 <;> simp only [div_eq_mul_inv,one_mul] <;> ring
end Green64Analytic.CorrelationMellin

end

/-! ## SourceZetaHockey -/

section

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 700000

/-- Hockey-stick binomial identity in the exact prime-power orientation
needed by 64-fold Dirichlet zeta convolution. -/
theorem source_zeta_choose_hockey434 (k e : ℕ) :
    (∑ i ∈ Finset.range (e+1), Nat.choose (i+k) k) =
      Nat.choose (e+k+1) (k+1) := by
  induction e with
  | zero =>
      simp [Nat.choose_self]
  | succ e ih =>
      rw [show e.succ+1 = (e+1)+1 by omega, Finset.sum_range_succ]
      rw [ih]
      have he : e+1+k = e+k+1 := by omega
      rw [he]
      calc
        Nat.choose (e+k+1) (k+1) + Nat.choose (e+k+1) k =
            Nat.choose (e+k+1) k + Nat.choose (e+k+1) (k+1) := add_comm _ _
        _ = Nat.choose ((e+k+1)+1) (k+1) :=
          (Nat.choose_succ_succ' (e+k+1) k).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceZetaConvolutionPrimePower -/

section

open scoped ArithmeticFunction.zeta

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 950000

/-- The exact k-fold Dirichlet zeta convolution at prime powers counts
ordered k-tuples of factors. This is NOT pointwise powering. -/
theorem source_zeta_dirichlet_power_prime434
    (p : ℕ) (hp : Nat.Prime p) :
    ∀ (k e : ℕ),
      ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1)) (p^e) =
        Nat.choose (e+k) k := by
  intro k
  induction k with
  | zero =>
      intro e
      have hp0 : p^e ≠ 0 := pow_ne_zero _ hp.ne_zero
      simpa [ArithmeticFunction.zeta_apply_ne hp0]
  | succ k ih =>
      intro e
      have hconv :
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1+1)) (p^e) =
            ∑ i ∈ Finset.range (e+1),
              ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1)) (p^i) := by
        rw [pow_succ, ArithmeticFunction.mul_zeta_apply,
          Nat.sum_divisors_prime_pow hp]
      calc
        _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1+1)) (p^e) := by
              congr 2
        _ = ∑ i ∈ Finset.range (e+1),
              ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^(k+1)) (p^i) := hconv
        _ = ∑ i ∈ Finset.range (e+1), Nat.choose (i+k) k := by
              apply Finset.sum_congr rfl
              intro i hi
              exact ih i
        _ = Nat.choose (e+k+1) (k+1) :=
              source_zeta_choose_hockey434 k e
        _ = Nat.choose (e+k.succ) k.succ := by
              congr 1 <;> omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceTau6AllIntegerD64 -/

section

open scoped ArithmeticFunction.zeta

namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1400000

/-- The ACTUAL 64-fold Dirichlet divisor function, as Dirichlet
convolution power of zeta, not a weaker artificial coefficient. -/
def sourceD64 : ArithmeticFunction ℕ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℕ)^64

theorem source_d64_prime_power434
    (p e : ℕ) (hp : Nat.Prime p) :
    sourceD64 (p^e) = Nat.choose (e+63) 63 := by
  change ((ArithmeticFunction.zeta : ArithmeticFunction ℕ)^64) (p^e) =
    Nat.choose (e+63) 63
  exact source_zeta_dirichlet_power_prime434 p hp 63 e

/-- TRUE all-positive-integer moment comparison τ(n)^6 <= d64(n);
no squarefreeness, no finite tested range, no source energy hypothesis. -/
theorem source_tau_six_le_d64_all_integer434
    (n : ℕ) (hn : n ≠ 0) :
    (n.divisors.card)^6 ≤ sourceD64 n := by
  classical
  have hf : (ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_sigma
  have hg : sourceD64.IsMultiplicative := by
    unfold sourceD64
    exact ArithmeticFunction.isMultiplicative_zeta.pow
  have hfactorF := hf.multiplicative_factorization
    (ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ) hn
  have hfactorG := hg.multiplicative_factorization sourceD64 hn
  have hProdPow :
      (n.factorization.prod (fun p k =>
        ArithmeticFunction.sigma 0 (p^k)))^6 =
        n.factorization.prod (fun p k =>
          (ArithmeticFunction.sigma 0 (p^k))^6) := by
    simp only [Finsupp.prod, Finset.prod_pow]
  have hProdLe :
      n.factorization.prod (fun p k =>
        (ArithmeticFunction.sigma 0 (p^k))^6) ≤
      n.factorization.prod (fun p k => sourceD64 (p^k)) := by
    simp only [Finsupp.prod]
    apply Finset.prod_le_prod
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors
      (by simpa only [Nat.support_factorization] using hp)
    exact (source_tau6_actual_divisor_prime_power434 p
      (n.factorization p) hpprime).trans_eq
      (source_d64_prime_power434 p (n.factorization p) hpprime).symm
  calc
    n.divisors.card^6 =
        (ArithmeticFunction.sigma 0 n)^6 := by
          rw [ArithmeticFunction.sigma_zero_apply]
    _ = (n.factorization.prod (fun p k =>
        ArithmeticFunction.sigma 0 (p^k)))^6 := by rw [hfactorF]
    _ = n.factorization.prod (fun p k =>
        (ArithmeticFunction.sigma 0 (p^k))^6) := hProdPow
    _ ≤ n.factorization.prod (fun p k => sourceD64 (p^k)) := hProdLe
    _ = sourceD64 n := hfactorG.symm
end Green64Analytic.CorrelationSquare

end

/-! ## SquarefreeDivisorConvolution -/

section

set_option maxHeartbeats 4000000
open scoped BigOperators ArithmeticFunction.sigma

namespace Green64Analytic.SourceDivisorMoment

/-- The unweighted divisor arithmetic function has two local
values at a prime: 1 and the prime itself. -/
theorem sigma_zero_prime (p : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.sigma 0) p = 2 := by
  have h := ArithmeticFunction.sigma_zero_apply_prime_pow
    (i := 1) hp
  simpa using h

/-- At squarefree n, two independent divisor choices are
canonically the four-color prime assignment, hence equal to
the Dirichlet convolution of the *actual* divisor arithmetic function. -/
theorem squarefree_divisor_square_eq_convolution
    (d : ℕ) (hd : Squarefree d) :
    d.divisors.card ^ 2 =
      ((ArithmeticFunction.sigma 0) *
        (ArithmeticFunction.sigma 0)) d := by
  have hconv :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree
      (f := ArithmeticFunction.sigma 0)
      (g := ArithmeticFunction.sigma 0)
      ArithmeticFunction.isMultiplicative_sigma
      ArithmeticFunction.isMultiplicative_sigma hd
  have hpoint (p : ℕ) (hp : p ∈ d.primeFactors) :
      ((ArithmeticFunction.sigma 0)+(ArithmeticFunction.sigma 0)) p = 4 := by
    rw [ArithmeticFunction.add_apply]
    rw [sigma_zero_prime p (Nat.prime_of_mem_primeFactors hp)]
  have hfour :
      (ArithmeticFunction.prodPrimeFactors
       (fun p => ((ArithmeticFunction.sigma 0) +
         (ArithmeticFunction.sigma 0)) p)) d =
        4 ^ d.primeFactors.card := by
    rw [ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero]
    trans ∏ _p ∈ d.primeFactors, (4:ℕ)
    · apply Finset.prod_congr rfl
      intro p hp
      exact hpoint p hp
    · simp
  calc
    _ = (2 ^ d.primeFactors.card)^2 := by
      rw [Green64Analytic.SourceCRT.squarefree_divisors_card d hd]
    _ = 4 ^ d.primeFactors.card := by
      rw [show (4:ℕ)=2^2 by norm_num, ←pow_mul, ←pow_mul]
      ring
    _ = (ArithmeticFunction.prodPrimeFactors
       (fun p => ((ArithmeticFunction.sigma 0) +
         (ArithmeticFunction.sigma 0)) p)) d := hfour.symm
    _ = _ := hconv

end Green64Analytic.SourceDivisorMoment

end

/-! ## DirichletWeight -/

section

set_option maxHeartbeats 4500000
open scoped BigOperators
namespace Green64Analytic.SourceDivisorMoment

/-- The classical Dirichlet-series normalisation f(n)/n, including
the correct zero at n=0. -/
noncomputable def reciprocalLift (f : ArithmeticFunction ℕ) :
    ArithmeticFunction ℝ :=
  ⟨fun n => (f n : ℝ)/(n:ℝ), by simp⟩

@[simp] theorem reciprocalLift_apply
    (f : ArithmeticFunction ℕ) (n : ℕ) :
    reciprocalLift f n = (f n : ℝ)/(n:ℝ) := rfl

/-- Dividing by n is a homomorphism for the *true* Dirichlet
convolution, proved termwise using ab=n on divisor-antidiagonals. -/
theorem reciprocalLift_mul
    (f g : ArithmeticFunction ℕ) :
    reciprocalLift (f*g) = reciprocalLift f * reciprocalLift g := by
  ext n
  rw [reciprocalLift_apply, ArithmeticFunction.mul_apply,
      ArithmeticFunction.mul_apply]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ab hab
  have hprod : ab.1*ab.2=n := (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [←hprod]
  simp only [Nat.cast_mul, reciprocalLift_apply]
  ring
/-- Every positive weighted convolution sums over exact finite
product pairs m*n≤Z (reusing Mathlib's truthful arithmetic-function
convolution formula). -/
theorem reciprocal_convolution_summatory (f g : ArithmeticFunction ℕ)
    (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z, (((f*g) n) : ℝ)/(n:ℝ)) =
      ∑ ab ∈ (Finset.Ioc 0 Z ×ˢ Finset.Ioc 0 Z).filter
        (fun ab : ℕ × ℕ => ab.1*ab.2≤Z),
        ((f ab.1:ℝ)/(ab.1:ℝ))*((g ab.2:ℝ)/(ab.2:ℝ)) := by
  conv_lhs => arg 2; ext n; rw [←reciprocalLift_apply]
  rw [reciprocalLift_mul]
  exact ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter
    (reciprocalLift f) (reciprocalLift g) Z
/-- A positive Dirichlet coefficient sum is bounded by the
product of the two independent reciprocal coefficient sums.
The truncation mn≤Z is handled by a genuine subset inclusion. -/
theorem reciprocal_convolution_le_product (f g : ArithmeticFunction ℕ)
    (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z, (((f*g) n) : ℝ)/(n:ℝ)) ≤
      (∑ a ∈ Finset.Ioc 0 Z, (f a : ℝ)/(a:ℝ)) *
      (∑ b ∈ Finset.Ioc 0 Z, (g b : ℝ)/(b:ℝ)) := by
  rw [reciprocal_convolution_summatory]
  let T := Finset.Ioc 0 Z
  let f' (ab : ℕ × ℕ) : ℝ :=
    ((f ab.1:ℝ)/(ab.1:ℝ))*((g ab.2:ℝ)/(ab.2:ℝ))
  calc
    _ ≤ ∑ ab ∈ T ×ˢ T, f' ab := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro ab hab _
        positivity
    _ = (∑ a ∈ T, (f a:ℝ)/(a:ℝ)) *
        (∑ b ∈ T, (g b:ℝ)/(b:ℝ)) := by
      rw [Finset.sum_product]
      change (∑ a ∈ T, ∑ b ∈ T,
        ((f a:ℝ)/(a:ℝ))*((g b:ℝ)/(b:ℝ))) = _
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

end Green64Analytic.SourceDivisorMoment

end

/-! ## DirichletHarmonic -/

section

set_option maxHeartbeats 4000000
open scoped BigOperators
namespace Green64Analytic.SourceDivisorMoment

noncomputable def reciprocalHarmonic (Z : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 Z, (1:ℝ)/(n:ℝ)

/-- The reciprocal weighted zeta coefficients are exactly the
finite real harmonic sum; n=0 is excluded explicitly. -/
theorem zeta_reciprocal_eq_harmonic (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z,
      ((ArithmeticFunction.zeta n:ℕ):ℝ)/(n:ℝ)) =
        reciprocalHarmonic Z := by
  unfold reciprocalHarmonic
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by
    have hh := (Finset.mem_Ioc.mp hn).1
    omega
  rw [ArithmeticFunction.zeta_apply_ne hn0]
  norm_num

/-- Exact sum-of-divisor arithmetic function is the Dirichlet
convolution of two distinct honest zeta factors. -/
theorem sigma_zero_eq_zeta_mul_zeta :
    ArithmeticFunction.sigma 0 =
      ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
  rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma,
    ArithmeticFunction.pow_zero_eq_zeta]
/-- Dirichlet hyperbola's primary inequality:
a partial convolution sum with the zeta function is bounded by
the harmonic weighted sum of the other nonnegative coefficients. -/
theorem sum_mul_zeta_le_reciprocal
    (f : ArithmeticFunction ℕ) (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z,
      (((f * ArithmeticFunction.zeta) n : ℕ) : ℝ)) ≤
      (Z:ℝ) * (∑ n ∈ Finset.Ioc 0 Z,
        (f n : ℝ)/(n:ℝ)) := by
  have heq := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum f Z
  have hcast :
      (∑ n ∈ Finset.Ioc 0 Z,
        (((f * ArithmeticFunction.zeta) n : ℕ) : ℝ)) =
      ∑ n ∈ Finset.Ioc 0 Z, (f n:ℝ)*(↑(Z/n):ℝ) := by
    exact_mod_cast heq
  rw [hcast]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 Z, (f n:ℝ)*((Z:ℝ)/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hpos : (0:ℝ)<n := by
        exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have hdiv : ((Z/n:ℕ):ℝ) ≤ (Z:ℝ)/(n:ℝ) := by
        apply (le_div_iff₀ hpos).mpr
        have hh : Z/n*n ≤ Z := Nat.div_mul_le_self Z n
        exact_mod_cast hh
      exact mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
    _ = (Z:ℝ) * ∑ n ∈ Finset.Ioc 0 Z,
        (f n:ℝ)/(n:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring

end Green64Analytic.SourceDivisorMoment

end

/-! ## TripleZetaBound -/

section

set_option maxHeartbeats 4500000
open scoped BigOperators
namespace Green64Analytic.SourceDivisorMoment

theorem reciprocalHarmonic_nonneg (Z : ℕ) :
    0 ≤ reciprocalHarmonic Z := by
  unfold reciprocalHarmonic
  apply Finset.sum_nonneg
  intro n hn
  positivity

theorem reciprocalHarmonic_le_one_add_log (Z : ℕ) :
    reciprocalHarmonic Z ≤ 1 + Real.log (Z:ℝ) := by
  have hset : Finset.Ioc 0 Z = Finset.Icc 1 Z := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have heq : reciprocalHarmonic Z = (harmonic Z:ℝ) := by
    unfold reciprocalHarmonic
    rw [hset, harmonic_eq_sum_Icc]
    push_cast
    simp
  rw [heq]
  exact harmonic_le_one_add_log Z

/-- The first Dirichlet convolution of zeta: its reciprocal
coefficient sum is at most the square of the harmonic sum. -/
theorem sigma_zero_reciprocal_le_harmonic_sq (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z,
      ((ArithmeticFunction.sigma 0 n:ℕ):ℝ)/(n:ℝ)) ≤
      (reciprocalHarmonic Z)^2 := by
  calc
    _ = ∑ n ∈ Finset.Ioc 0 Z,
        (((ArithmeticFunction.zeta * ArithmeticFunction.zeta) n : ℕ):ℝ)/(n:ℝ) := by
      rw [← sigma_zero_eq_zeta_mul_zeta]
    _ ≤ (∑ a ∈ Finset.Ioc 0 Z,
           ((ArithmeticFunction.zeta a:ℕ):ℝ)/(a:ℝ)) *
          (∑ b ∈ Finset.Ioc 0 Z,
           ((ArithmeticFunction.zeta b:ℕ):ℝ)/(b:ℝ)) :=
      reciprocal_convolution_le_product
        ArithmeticFunction.zeta ArithmeticFunction.zeta Z
    _ = (reciprocalHarmonic Z)^2 := by
      rw [zeta_reciprocal_eq_harmonic]
      ring

/-- Three independent zeta factors, with the third-power harmonic
bound including every summation cutoff in the right quantifier order. -/
theorem three_zeta_reciprocal_le_harmonic_cube (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z,
      ((((ArithmeticFunction.sigma 0) * ArithmeticFunction.zeta) n : ℕ):ℝ)/
       (n:ℝ)) ≤
      (reciprocalHarmonic Z)^3 := by
  have h2 := sigma_zero_reciprocal_le_harmonic_sq Z
  have h3 :=
    reciprocal_convolution_le_product
      (ArithmeticFunction.sigma 0) ArithmeticFunction.zeta Z
  have hH := reciprocalHarmonic_nonneg Z
  calc
    _ ≤ (∑ n ∈ Finset.Ioc 0 Z, ((ArithmeticFunction.sigma 0 n:ℕ):ℝ)/(n:ℝ)) *
        (∑ n ∈ Finset.Ioc 0 Z, ((ArithmeticFunction.zeta n:ℕ):ℝ)/(n:ℝ)) := h3
    _ = (∑ n ∈ Finset.Ioc 0 Z, ((ArithmeticFunction.sigma 0 n:ℕ):ℝ)/(n:ℝ)) *
        reciprocalHarmonic Z := by
      rw [zeta_reciprocal_eq_harmonic]
    _ ≤ (reciprocalHarmonic Z)^2 * reciprocalHarmonic Z :=
      mul_le_mul_of_nonneg_right h2 hH
    _ = (reciprocalHarmonic Z)^3 := by ring
theorem square_sigma_eq_four_zeta :
    (ArithmeticFunction.sigma 0) * (ArithmeticFunction.sigma 0) =
      ((ArithmeticFunction.sigma 0) * ArithmeticFunction.zeta) *
        ArithmeticFunction.zeta := by
  rw [sigma_zero_eq_zeta_mul_zeta]
  ac_rfl

/-- Full unweighted four-divisor coefficient count up to Z is
bounded by Z times the harmonic cube; all coefficients are genuine. -/
theorem fourfold_divisor_sum_le_harmonic_cube (Z : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Z,
      ((((ArithmeticFunction.sigma 0)*
       (ArithmeticFunction.sigma 0)) n : ℕ):ℝ)) ≤
      (Z:ℝ)*(reciprocalHarmonic Z)^3 := by
  have heq := square_sigma_eq_four_zeta
  simp_rw [heq]
  exact (sum_mul_zeta_le_reciprocal
     ((ArithmeticFunction.sigma 0) * ArithmeticFunction.zeta) Z).trans
      (mul_le_mul_of_nonneg_left
         (three_zeta_reciprocal_le_harmonic_cube Z)
         (Nat.cast_nonneg _))

end Green64Analytic.SourceDivisorMoment

end

