module

public import Green64.Library.Weights.Part099
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import Mathlib
public import Green64.Library.Weights.Part050
public import Green64.Library.Weights.Part054
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.LiteralEndpointProfiles
public import Green64.Library.Correlation.Part066
public import Green64.Library.Correlation.Part033
public import Green64.Library.Analysis.Estimates.LiteralFourierPhaseGates
public import Green64.Library.Correlation.Part065
public import Green64.Library.Correlation.Part027
public import Green64.Library.Correlation.MemoryNumericGates

@[expose] public section

/-!
# Weights / Part100

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeR6ComparisonAsymptoticFields -/

section

open Filter Real Asymptotics
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Original SOURCE03 power-versus-subexponential growth for
arbitrary fixed arc/character exponent C, true positive source
exponent a, and unaltered positive scale t. All parameters are
selected BEFORE the real asymptotic variable L. -/
theorem eventually_native_source_poly_lt_exp_scaled434
    (C a t : ℝ) (hC : 0 ≤ C) (ha : 0 < a) (ht : 0 < t) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧ L^C < Real.exp (t*L^a) := by
  let A := (C+1)/t
  have hA : 0 < A := div_pos (by linarith) ht
  have hsmall := (isLittleO_log_rpow_atTop ha).bound
    (show (0:ℝ) < 1/A by positivity)
  filter_upwards [
    hsmall,
    eventually_ge_atTop (Real.exp 1)] with L hb hL
  refine ⟨hL, ?_⟩
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hLog : 0 < Real.log L :=
    Real.log_pos (by
      have he : (1:ℝ) < Real.exp 1 :=
        Real.one_lt_exp_iff.mpr (by norm_num)
      exact he.trans_le hL)
  have hPow : 0 ≤ L^a := Real.rpow_nonneg hLp.le _
  have hSmall : Real.log L ≤ (1/A)*L^a := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hLog.le,
      abs_of_nonneg hPow] using hb
  have hScaled : (C+1)*Real.log L ≤ t*L^a := by
    have hm := mul_le_mul_of_nonneg_left hSmall hA.le
    have hinv : A*(1/A)=1 := by field_simp [ne_of_gt hA]
    have hright : A*((1/A)*L^a)=L^a := by
      calc
        _ = (A*(1/A))*L^a := by ring
        _ = L^a := by rw [hinv]; ring
    rw [hright] at hm
    calc
      (C+1)*Real.log L = t*(A*Real.log L) := by
        dsimp [A]
        field_simp [ne_of_gt ht]
      _ ≤ t*(L^a) := mul_le_mul_of_nonneg_left hm ht.le
  have hStrict : C*Real.log L < t*L^a := by
    nlinarith [hScaled,hLog]
  rw [Real.rpow_def_of_pos hLp]
  exact Real.exp_lt_exp.mpr (by nlinarith [hStrict])

/-- ALL remaining true SOURCE03 original purely NUMERIC
arc/rough/long-auxiliary comparison requirements are satisfied
uniformly for the actual r=6 fixed configuration:
  L^Carc <= exp(sqrt L), L^Carc < exp(L^aexp),
  L^Carc < exp(τ L), L^(2cm) <= exp(sqrt L).
The actual designated Q-band exponent τ_jQ>0 is unchanged;
no artificially large arc constant or exponent is introduced.
This theorem is about numeric gate fields only; it does not
supply Knu, a Dirichlet coefficient or signed D61 cancellation. -/
theorem eventually_native_r6_original_comparison_arc_gates434
    (jQ mmax cm s0 vexp : ℕ)
    (Carc Cχ CZ : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc)
    (hCχ : (cm:ℝ) ≤ Cχ)
    (hCχpos : 0 < Cχ)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg := sourceNativeOriginalR6Fixed434
      jQ mmax cm s0 vexp Carc Cχ CZ
      hCarc hCχ hCχpos Kpsi hKpsi
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      (L^(2*cfg.cm:ℝ) ≤ Real.exp (Real.sqrt L)) ∧
      (L^cfg.Carc ≤ Real.exp (Real.sqrt L)) ∧
      (L^cfg.Carc < Real.exp (L^cfg.aexp)) ∧
      (L^cfg.Carc < Real.exp (cfg.τ*L)) := by
  let cfg := sourceNativeOriginalR6Fixed434
      jQ mmax cm s0 vexp Carc Cχ CZ
      hCarc hCχ hCχpos Kpsi hKpsi
  have hC : 0 ≤ Carc := (Nat.cast_nonneg cm).trans hCarc
  have hc : 0 ≤ ((2*cm:ℕ):ℝ) := Nat.cast_nonneg _
  have hτ : 0 < cfg.τ := cfg.hτ
  filter_upwards [
    eventually_native_source_poly_lt_exp_scaled434
      ((2*cm:ℕ):ℝ) (1/2:ℝ) 1 hc (by norm_num) (by norm_num),
    eventually_native_source_poly_lt_exp_scaled434
      Carc (1/2:ℝ) 1 hC (by norm_num) (by norm_num),
    eventually_native_source_poly_lt_exp_scaled434
      Carc (1/10:ℝ) 1 hC (by norm_num) (by norm_num),
    eventually_native_source_poly_lt_exp_scaled434
      Carc 1 cfg.τ hC (by norm_num) hτ]
    with L hcmod hW hS hLong
  refine ⟨hcmod.1, ?_⟩
  have hsqrt : Real.sqrt L = L^(1/2:ℝ) := Real.sqrt_eq_rpow L
  have h1 : L^(2*(cm:ℝ)) ≤ Real.exp (Real.sqrt L) := by
    rw [hsqrt]
    simpa only [one_mul,Nat.cast_mul,Nat.cast_ofNat] using hcmod.2.le
  have h2 : L^Carc ≤ Real.exp (Real.sqrt L) := by
    rw [hsqrt]
    simpa only [one_mul] using hW.2.le
  have h3 : L^Carc < Real.exp (L^(1/10:ℝ)) := by
    simpa only [one_mul] using hS.2
  have h4 : L^Carc <
      Real.exp ((sourceOriginalQActualExponent 6 jQ)*L) := by
    have hTauEq : cfg.τ = sourceOriginalQActualExponent 6 jQ :=
      (source_native_original_r6_fixed_literal_fields434
        jQ mmax cm s0 vexp Carc Cχ CZ
        hCarc hCχ hCχpos Kpsi hKpsi).1
    have hh := hLong.2
    rw [hTauEq,Real.rpow_one] at hh
    exact hh
  dsimp only [cfg,sourceNativeOriginalR6Fixed434]
  exact ⟨h1,h2,h3,h4⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceQSkipOriginalSlotLong -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- For a fixed original Q log-exponent τ>0, its exponential lower bound
eventually exceeds the literal source roughness threshold exp(sqrt L). -/
theorem eventually_fixed_Q_exponent_above_roughness434
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, Real.sqrt L < τ*L := by
  have hτsq : 0 < τ^2 := sq_pos_of_pos hτ
  filter_upwards [eventually_gt_atTop (1/τ^2+1)] with L hL
  have hLpos : 0 < L := by
    have : (0:ℝ) ≤ 1/τ^2 := by positivity
    linarith
  have hτLpos : 0 ≤ τ*L := (mul_pos hτ hLpos).le
  apply (Real.sqrt_lt hLpos.le hτLpos).mpr
  have hdiv : (1:ℝ) / τ^2 < L := by linarith
  have hMul := mul_lt_mul_of_pos_left hdiv hτsq
  have hOne : (1:ℝ)/τ^2 * τ^2 = 1 := by
    field_simp [ne_of_gt hτsq]
  have hWide : 1 < τ^2*L := by nlinarith [hMul]
  have hGain := mul_lt_mul_of_pos_right hWide hLpos
  nlinarith [hGain]
/-- Real original designated Q_j prime slot, for a fixed selected j,
is eventually strictly above exp(sqrt L), uniformly over every larger
moving source depth d and every prime in that genuine designated band. -/
theorem eventually_original_designated_Q_long434 (j : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (d : ℕ) (hj : j < d+1) (p : ℕ),
        p ∈ sourceOriginalQActualBands 6 d L ⟨j,hj⟩ →
        Real.exp (Real.sqrt L) < (p:ℝ) := by
  let τ := sourceOriginalQActualExponent 6 j
  have hτ : 0 < τ :=
    (original_source_r6_designated_Q_exponent_gates434 j).1
  filter_upwards [eventually_fixed_Q_exponent_above_roughness434 τ hτ]
    with L hGap
  intro d hj p hp
  have hRange := (source_actual_designated_Q_prime_interval434
    6 d L ⟨j,hj⟩ p).mp hp
  have hLower : Real.exp (τ*L) ≤ (p:ℝ) := hRange.2.1
  exact (Real.exp_lt_exp.mpr hGap).trans_le hLower
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceQSkipLiteralDepthProperties -/

section

open Filter Topology Asymptotics
open scoped Classical
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 5000000

theorem source_original_fixed_depth_admissible_eventually
    (r₀ j : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, sourceOriginalDepthAdmissible r₀ j L := by
  have hr : (0:ℝ) < r₀ := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) hr₀)
  let a : ℝ := (5/(11*(r₀:ℝ)))/(2:ℝ)^j
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < a/20 := by positivity
  have hsmall := Real.isLittleO_log_id_atTop.bound hc
  filter_upwards [hsmall, eventually_ge_atTop (1:ℝ)] with L hbound hL
  have hL0 : 0 ≤ L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs, abs_of_nonneg hlog] at hbound
  change Real.log L ≤ a/20 * |L| at hbound
  rw [abs_of_nonneg hL0] at hbound
  dsimp [sourceOriginalDepthAdmissible, a] at hbound ⊢
  nlinarith

theorem source_original_admissible_search_bound
    (r₀ j : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 1 < L)
    (hj : sourceOriginalDepthAdmissible r₀ j L) :
    j ≤ sourceOriginalDepthSearchBound r₀ L := by
  have hr : (0:ℝ) < r₀ := by exact_mod_cast (by omega : 0 < r₀)
  have hlog : 0 < 20*Real.log L := by
    have := Real.log_pos hL
    positivity
  have hp : 0 < (2:ℝ)^j := by positivity
  have hnum : 0 ≤ (5/(11*(r₀:ℝ)))*L := by positivity
  have hPow : (2:ℝ)^j ≤ ((5/(11*(r₀:ℝ)))*L)/(20*Real.log L) := by
    apply (le_div_iff₀ hlog).2
    dsimp [sourceOriginalDepthAdmissible] at hj
    rw [div_mul_eq_mul_div] at hj
    have hh := (le_div_iff₀ hp).1 hj
    simpa only [mul_comm] using hh
  have hJPow : (j:ℝ) ≤ (2:ℝ)^j := by
    exact_mod_cast (Nat.le_of_lt j.lt_two_pow_self)
  unfold sourceOriginalDepthSearchBound
  exact (Nat.le_floor_iff (div_nonneg hnum hlog.le)).2 (hJPow.trans hPow)

/-- The source depth is derived, including actual admissibility and
maximality over all natural indices. -/

theorem source_original_literal_depth_properties_eventually
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalDepthAdmissible r₀ (sourceOriginalLiteralDepth r₀ L) L ∧
      ∀ j, sourceOriginalDepthAdmissible r₀ j L →
        j ≤ sourceOriginalLiteralDepth r₀ L := by
  filter_upwards [source_original_fixed_depth_admissible_eventually
    r₀ 0 hr₀, eventually_gt_atTop (1:ℝ)] with L h0 hL
  constructor
  · exact Nat.findGreatest_spec
      (P := fun j => sourceOriginalDepthAdmissible r₀ j L)
      (Nat.zero_le (sourceOriginalDepthSearchBound r₀ L)) h0
  · intro j hj
    exact Nat.le_findGreatest
      (source_original_admissible_search_bound r₀ j L hr₀ hL hj) hj

theorem source_original_literal_depth_grows
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, k ≤ sourceOriginalLiteralDepth r₀ L := by
  filter_upwards [source_original_fixed_depth_admissible_eventually r₀ k hr₀,
    source_original_literal_depth_properties_eventually r₀ hr₀] with L hk hd
  exact hd.2 k hk
end Green64Analytic.SourceBlockSieve

end

/-! ## SourceQSkipOriginalComparisonSlot -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- All literal SourceComparisonData434 designated primeSlot fields for one
source-selected Q index j fixed *before L*. The original moving maximum
admissible depth supplies the slot, rather than assuming it exists. -/
theorem eventually_actual_r6_comparison_Q_slot_fields434 (j : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∃ b : Fin (sourceOriginalLiteralDepth 6 L + 1),
        let τ := sourceOriginalQActualExponent 6 j
        let η := (6/5:ℝ)*τ
        let I := Set.Icc (Real.exp (τ*L)) (Real.exp (η*L))
        let primeSlot := sourceOriginalQActualBands 6
          (sourceOriginalLiteralDepth 6 L) L b
        0 < τ ∧ τ < η ∧ η < 1/4 ∧
        Set.OrdConnected I ∧
        (∀ p : ℕ, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) ∧
        I ⊆ Set.Icc ((Real.exp L)^τ) ((Real.exp L)^η) ∧
        (∀ p ∈ primeSlot, Real.exp (Real.sqrt L) < (p:ℝ)) ∧
        (∀ p ∈ primeSlot, Real.exp (τ*L) ≤ (p:ℝ)) := by
  have hgate := original_source_r6_designated_Q_exponent_gates434 j
  filter_upwards [source_original_literal_depth_grows 6 j (by norm_num),
    eventually_original_designated_Q_long434 j] with L hdepth hlong
  have hj : j < sourceOriginalLiteralDepth 6 L + 1 := by omega
  let b : Fin (sourceOriginalLiteralDepth 6 L + 1) := ⟨j,hj⟩
  refine ⟨b, ?_⟩
  dsimp only
  refine ⟨hgate.1,hgate.2.1,hgate.2.2,
    source_actual_designated_Q_interval_connected434 6
      (sourceOriginalLiteralDepth 6 L) L b, ?_, ?_, ?_, ?_⟩
  · intro p
    simpa [b] using source_actual_designated_Q_prime_interval434
      6 (sourceOriginalLiteralDepth 6 L) L b p
  · simpa only [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp,
        mul_comm] using (Set.Subset.rfl : Set.Icc
        (Real.exp (sourceOriginalQActualExponent 6 j*L))
        (Real.exp ((6/5:ℝ)*sourceOriginalQActualExponent 6 j*L)) ⊆
        Set.Icc (Real.exp (sourceOriginalQActualExponent 6 j*L))
        (Real.exp ((6/5:ℝ)*sourceOriginalQActualExponent 6 j*L)))
  · intro p hp
    exact hlong (sourceOriginalLiteralDepth 6 L) hj p hp
  · intro p hp
    exact ((source_actual_designated_Q_prime_interval434
      6 (sourceOriginalLiteralDepth 6 L) L b p).mp hp).2.1
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6ActualQPacket -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Genuine SOURCE03 r=6 Q-component of the comparison datum:
for a designated ORIGINAL Q index jQ selected BEFORE the scale,
choose the literal same index in the original largest admissible
moving depth. Then ALL Boolean QSkip allocations and ALL Fourier
frequency vectors enjoy the EXACT source fields:

(1) original primeSlot equals primes in the exact closed I_Q;
(2) I_Q ordered connected and contained in the original fixed
    [x^tau, x^eta], x=exp L;
(3) original Q primes exceed exp(sqrt L) and exp(tau L);
(4) exact literal unconditioned c(v)=sourceEndpointFibre with
    full (6!)^(-(d+1)) normalization and Fourier sign -xi,
    including repeated prime assignments, with ||c(v)||≤1 and
    C=1≤L^cfg.ec.

This binds ACTUAL cfg, moving largest depth, original Q labels,
factorial residual and prime interval in one quantified packet.
It does NOT construct the remaining original comparison endpoint
record nor change any physical P/OLD source data. -/
theorem eventually_native_r6_original_ACTUAL_Q_packet434
    (jQ : ℕ) (mmax cm s0 vexp : ℕ)
    (Carc Cχ CZ : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ)
    (hCχpos : 0<Cχ)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg := sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp
      Carc Cχ CZ hCarc hCχ hCχpos Kpsi hKpsi
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∃ b : Fin (sourceOriginalLiteralDepth 6 L+1),
        let d := sourceOriginalLiteralDepth 6 L
        let n := (sourceOrderedLabels 6
          (sourceActualSortedScales 6 d L) b (0:Fin 6)).length
        let Q := sourceOriginalQActualBands 6 d L b
        let qs := sourceActualSortedQ 6 d L b (0:Fin 6)
        let s := sourceActualSortedFrequencyScales 6 d L b (0:Fin 6)
        let I := Set.Icc (Real.exp (cfg.τ*L))
          (Real.exp (cfg.η*L))
        0 < cfg.τ ∧ cfg.τ < cfg.η ∧ cfg.η < 1/4 ∧
        Set.OrdConnected I ∧
        (∀ p : ℕ, p∈Q ↔ p.Prime ∧ (p:ℝ)∈I) ∧
        I ⊆ Set.Icc ((Real.exp L)^cfg.τ)
          ((Real.exp L)^cfg.η) ∧
        (∀ p∈Q, Real.exp (Real.sqrt L)<(p:ℝ)) ∧
        (∀ p∈Q, Real.exp (cfg.τ*L)≤(p:ℝ)) ∧
        ∀ (δ : Fin n → Bool) (ξ : Fin n → ℝ),
        let c : ℕ → ℂ := fun v =>
          sourceEndpointFibre (Finset.univ : Finset (OrderedQSkip n qs δ))
            orderedSkipProduct
            (fun a => sourceActualSortedFactorial 6 d *
              orderedSkipPhase s (-ξ) a) v
        (0:ℝ)≤1 ∧ 1≤L^cfg.ec ∧ ∀ v, ‖c v‖≤1 := by
  classical
  let cfg := sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp
    Carc Cχ CZ hCarc hCχ hCχpos Kpsi hKpsi
  have hcfg := source_native_original_r6_fixed_literal_fields434
    jQ mmax cm s0 vexp Carc Cχ CZ
    hCarc hCχ hCχpos Kpsi hKpsi
  have hTau : cfg.τ = sourceOriginalQActualExponent 6 jQ :=
    hcfg.1
  have hEta : cfg.η =
      (6/5:ℝ)*sourceOriginalQActualExponent 6 jQ := hcfg.2.1
  filter_upwards [eventually_actual_r6_comparison_Q_slot_fields434 jQ,
    eventually_ge_atTop (1:ℝ)] with L hSlot hL
  rcases hSlot with ⟨b, ht,hTE,hE,hI,hPrime,hBand,hLong,hMin⟩
  refine ⟨hL, b, ?_⟩
  dsimp [cfg, sourceNativeOriginalR6Fixed434]
  refine ⟨ht,hTE,hE,hI,hPrime,hBand,hLong,hMin,?_⟩
  intro δ ξ
  exact source_original_QSkip_comparison_c_fields434
    cfg L hL b (0:Fin 6) δ ξ
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6QPrimeNcap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The TRUE original r=6 designated Q prime-slot is BELOW the
original comparison endpoint Ncap, without an assumed Q cutoff
outside the source geometry.

Original slot exponent η_j=(6/5)τ_j<1/4, while an actual
SOURCE03 comparison record has Y≥exp(3L/4), 64Y≤Ncap.
All original closed prime-band endpoints, including prime at
the lower endpoint, remain unchanged. -/
theorem source_native_original_r6_Qslot_below_actual_Ncap434
    (d : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (b : Fin (d+1))
    (Y : ℝ) (Ncap : ℕ)
    (hY : Real.exp (3*L/4) ≤ Y)
    (hCap : 64*Y ≤ (Ncap:ℝ)) :
    ∀ p ∈ sourceOriginalQActualBands 6 d L b,
      p ≤ Ncap := by
  intro p hp
  have hPrime := (source_actual_designated_Q_prime_interval434
    6 d L b p).mp hp
  have hgate := original_source_r6_designated_Q_exponent_gates434 b.val
  have hEta := hgate.2.2
  have hLp : 0 ≤ L := by linarith
  have hPEnd : (p:ℝ) ≤
      Real.exp (((6/5:ℝ)*sourceOriginalQActualExponent 6 b.val)*L) :=
    hPrime.2.2
  have hExp : (p:ℝ) ≤ Real.exp (3*L/4) := by
    apply hPEnd.trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr
      (le_of_lt hEta)) hLp]
  have hYpos : 0 < Y := (Real.exp_pos _).trans_le hY
  have hYcap : Y ≤ 64*Y := by
    have hh := mul_nonneg (show (0:ℝ)≤63 by norm_num) hYpos.le
    nlinarith
  have hfinal : (p:ℝ) ≤ (Ncap:ℝ) :=
    hExp.trans (hY.trans (hYcap.trans hCap))
  exact_mod_cast hfinal
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualMovingGroupGates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The complete original family fits the existing C0=4, at every large
real scale; no equal-cardinality cofinal reindexing is imposed. -/
theorem source_B578_actual_group_counts_Cfour434
    (r : ℕ) (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty) :
    (Fintype.card (sourceNativeOriginalTsType434 r L hS):ℝ) ≤ 4*Real.log L ∧
    (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤ 4*Real.log L := by
  have hLpos : 0 < L := (Real.exp_pos _).trans_le hL
  have hlog : 2 ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h
    exact h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log L/Real.log 2 ≤ 2*Real.log L := by
    apply (div_le_iff₀ hlog2).mpr
    nlinarith [mul_le_mul_of_nonneg_left htwo (by linarith : 0≤Real.log L)]
  have harg : 0 ≤ 2+Real.log L/Real.log 2 := by positivity
  have hceil : (sourceOriginalPAllIndexBound L:ℝ) < 3+Real.log L/Real.log 2 := by
    have h := Nat.ceil_lt_add_one harg
    change (⌈2+Real.log L/Real.log 2⌉₊:ℝ) < _
    linarith
  have hall : ((sourceOriginalPAllGroupIndices r L).card:ℝ) ≤ 4*Real.log L := by
    have hc : (sourceOriginalPAllGroupIndices r L).card ≤ sourceOriginalPAllIndexBound L := by
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hcr : ((sourceOriginalPAllGroupIndices r L).card:ℝ) ≤
        (sourceOriginalPAllIndexBound L:ℝ) := by exact_mod_cast hc
    linarith
  have hs : (sourceNativeOriginalSmallIndices434 r L).card ≤
      (sourceOriginalPAllGroupIndices r L).card := Finset.card_filter_le _ _
  have hb : (sourceNativeOriginalBigIndices434 r L).card ≤
      (sourceOriginalPAllGroupIndices r L).card := Finset.card_filter_le _ _
  constructor
  · have he := Finset.card_erase_le
      (s:=sourceNativeOriginalSmallIndices434 r L)
      (a:=sourceNativeOriginalSIndex434 r L hS)
    have hc : Fintype.card (sourceNativeOriginalTsType434 r L hS) ≤
        (sourceOriginalPAllGroupIndices r L).card := by
      simpa only [sourceNativeOriginalTsType434,Fintype.card_coe] using he.trans hs
    exact (show (Fintype.card (sourceNativeOriginalTsType434 r L hS):ℝ) ≤
      ((sourceOriginalPAllGroupIndices r L).card:ℝ) by exact_mod_cast hc).trans hall
  · have hc : Fintype.card (sourceNativeOriginalBigType434 r L) ≤
        (sourceOriginalPAllGroupIndices r L).card := by
      simpa only [sourceNativeOriginalBigType434,Fintype.card_coe] using hb
    exact (show (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      ((sourceOriginalPAllGroupIndices r L).card:ℝ) by exact_mod_cast hc).trans hall

/-- Actual S, all Ts and all Tb fit the real comparison cap ceil(64Y).
The original full family is unchanged. -/
theorem source_B578_actual_P_below_comparison_cap434
    (r : ℕ) (L Y : ℝ) (hL : 4 ≤ L) (Ncap : ℕ)
    (hY : Real.exp (3*L/4) ≤ Y) (hcap : 64*Y ≤ (Ncap:ℝ)) :
    ∀ p ∈ sourceNativeOriginalG434 r L, p ≤ Ncap := by
  intro p hp
  have hsqrt : Real.sqrt L ≤ 3*L/4 := by
    have hs : (Real.sqrt L)^2=L := Real.sq_sqrt (by linarith)
    have hn := Real.sqrt_nonneg L
    nlinarith
  have hbound := (source_native_original_G_bound434 r L (by linarith) p hp).2
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hreal : (p:ℝ) ≤ (Ncap:ℝ) :=
    hbound.trans ((Real.exp_le_exp.mpr hsqrt).trans
      (hY.trans ((by linarith : Y≤64*Y).trans hcap)))
  exact_mod_cast hreal

/-- Every genuine original designated slot with the same fixed band index
has the actual Q arc fields; the threshold is independent of all later cells,
patterns, source and target cofactor masks, characters and frequencies. -/
theorem eventually_source_B578_actual_fixed_Q_all_slots434 (jQ : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      jQ ≤ sourceOriginalLiteralDepth 6 L ∧
      ∀ (b : Fin (sourceOriginalLiteralDepth 6 L+1)), b.val=jQ →
      let τ := sourceOriginalQActualExponent 6 jQ
      let η := (6/5:ℝ)*τ
      let I := Set.Icc (Real.exp (τ*L)) (Real.exp (η*L))
      let P := sourceOriginalQActualBands 6 (sourceOriginalLiteralDepth 6 L) L b
      Set.OrdConnected I ∧
      (∀ p,p∈P ↔ p.Prime ∧ (p:ℝ)∈I) ∧
      I ⊆ Set.Icc ((Real.exp L)^τ) ((Real.exp L)^η) ∧
      (∀ p∈P,Real.exp (Real.sqrt L)<(p:ℝ)) ∧
      (∀ p∈P,Real.exp (τ*L)≤(p:ℝ)) := by
  filter_upwards [source_original_literal_depth_grows 6 jQ (by norm_num),
    eventually_original_designated_Q_long434 jQ] with L hdepth hlong
  refine ⟨hdepth,?_⟩
  intro b hb
  dsimp only
  refine ⟨Set.ordConnected_Icc,?_,?_,?_,?_⟩
  · intro p
    simpa only [hb] using source_actual_designated_Q_prime_interval434
      6 (sourceOriginalLiteralDepth 6 L) L b p
  · simpa only [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm] using
      (Set.Subset.rfl : Set.Icc
        (Real.exp (sourceOriginalQActualExponent 6 jQ*L))
        (Real.exp ((6/5:ℝ)*sourceOriginalQActualExponent 6 jQ*L)) ⊆
      Set.Icc (Real.exp (sourceOriginalQActualExponent 6 jQ*L))
        (Real.exp ((6/5:ℝ)*sourceOriginalQActualExponent 6 jQ*L)))
  · intro p hp
    have he : b = ⟨jQ,by omega⟩ := Fin.ext hb
    rw [he] at hp
    exact hlong (sourceOriginalLiteralDepth 6 L) (by omega) p hp
  · intro p hp
    have h := ((source_actual_designated_Q_prime_interval434
      6 (sourceOriginalLiteralDepth 6 L) L b p).mp hp).2.1
    simpa only [hb] using h
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualAllCellComparisonData -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 12000

/-- The original fixed r=6 source constants, with the actual inner Fourier
box exponent exposed instead of specializing it to zero.  No prime bands,
weights, source witness or cutoff profile are changed by this record. -/
def sourceB578ActualFixed434
    (jQ mmax cm s0 s1 vexp : ℕ) (K Carc Cχ : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ) (hCχpos : 0<Cχ)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀j,0 ≤ Kpsi j) : SourceComparisonFixed434 :=
  {sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp Carc Cχ (K+91)
    hCarc hCχ hCχpos Kpsi hKpsi with s1base := s1}

/-- Exact all-cell record contract.  All objects below are the original
moving P family, full D20 alpha, designated QSkip residual, signed smooth
k-set and full canonical Knu row.  Profile regularity and frequency-box
membership remain the ordinary source input conditions; no discrepancy,
root, RMS or cancellation estimate appears among them. -/
def SourceB578ActualAllCellRecords434
    (cfg : SourceComparisonFixed434) (L : ℝ) (jQ : ℕ) (K : ℝ) (mmax : ℕ) : Prop :=
  ∀ (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (U V : ℝ), Real.exp L/4 ≤ U*V → U*V ≤ 3*Real.exp L →
  ∀ (N j : ℕ), j ≤ N → (2:ℝ)^N ≤ 384*L^(89:ℝ) →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 6 L) (sourceNativeOriginalBigBlockB434 6 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA ≤ 1 → hB ≤ 1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 6 L)
      (sourceNativeOriginalVbig434 6 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 6 L)
      (sourceNativeOriginalVbig434 6 L) nu hB xi →
  ∀ (b : Fin (sourceOriginalLiteralDepth 6 L+1)), b.val=jQ →
  ∀ (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (k : ℤ), k ∈ sourceCorrectedSmoothKSet (L^K) (L^(89:ℝ)) →
  ∀ (chi : DirichletCharacter ℂ k.natAbs) (sigma0 sigma1 v1 : ℝ),
    |sigma0| ≤ L^cfg.s0 → |sigma1| ≤ L^cfg.s1base → |v1| ≤ L^cfg.vexp →
  ∀ (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
    (∀u,psi u≠0 → 1/cfg.A ≤ u ∧ u ≤ cfg.A) →
    sourceLogDerivativeBudget cfg.Cpsi cfg.Kpsi L (fun u=>psi (Real.exp u)) →
  ∀ (Delta y : ℝ), 0<Delta → Real.exp (Real.sqrt L) ≤ y →
  ∀ (lo hi Qcomp : ℕ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 6 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (target : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g) → ℕ)
    (tw : Bool),
  let Z := sourceCorrectedDyadicScale U V (L^K) j
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let P := sourceNativeOriginalTb434 6 L
  let Vm := sourceNativeOriginalVbig434 6 L
  let row := sourceB578CanonicalRow434 J 1 m hmJ nu Qcomp hA hB xi P Vm aux target
  ∃ data : SourceComparisonData434
      (sourceNativeOriginalTsType434 6 L hS) (sourceNativeOriginalBigType434 6 L)
      cfg (Real.exp L) L (Z*Hp) Hp,
    data.Z=Z ∧ data.Ncap=⌈64*(Z*Hp)⌉₊ ∧
    data.G=sourceNativeOriginalG434 6 L ∧
    data.Ptw=(if tw then sourceNativeOriginalG434 6 L else ∅) ∧
    data.S=sourceNativeOriginalS434 6 L hS ∧
    data.Ts=sourceNativeOriginalTs434 6 L hS ∧ data.Tb=P ∧
    data.Vs=sourceNativeOriginalVs434 6 L hS ∧
    data.Vsmall=sourceNativeOriginalVsmall434 6 L hS ∧ data.Vbig=Vm ∧
    data.ts=(fun _=>1) ∧ data.tb=sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu ∧
    HEq data.coef row ∧ data.k=0 ∧
    data.alpha=sourceNativeOriginalFullD20Alpha434 Delta (Real.exp (Real.sqrt L)) y ∧
    data.lo=lo ∧ data.hi=hi ∧
    data.F1=Finset.range (Fintype.card nu.1) ∧
    data.F2=Finset.range (Fintype.card nu.2) ∧
    data.p1=sourceOriginalProbeIndexedPrime434 (fun z : nu.1=>aux (Sum.inl z)) ∧
    data.p2=sourceOriginalProbeIndexedPrime434 (fun z : nu.2=>aux (Sum.inr z)) ∧
    data.U1=Real.exp ((ja:ℝ)*hA) ∧ data.U2=Real.exp ((jb:ℝ)*hB) ∧
    data.primeSlot=sourceOriginalQActualBands 6 (sourceOriginalLiteralDepth 6 L) L b ∧
    data.c=sourceNativeOriginalLiteralResidual434 L b slot delta freq ∧ data.C=1 ∧
    data.qBase=k.natAbs ∧ HEq data.chi0 chi ∧
    data.sigma0=sigma0 ∧ data.sigma1=sigma1 ∧ data.v1=v1 ∧ data.psi1=psi

/-- Complete original comparison data exist for EVERY actual active cell,
all genuine k/characters in the original signed window, every ordered QSkip
allocation and frequency vector, both endpoint parity fields and arbitrary
actual canonical target row.  All numeric, prime, harmonic mass and mark
bounds are derived from the original moving family.  This eliminates the
old equal-size/cofinal/basis/qBase=2 restriction of the data construction.
The scalar row scale is explicitly retained in B578ActualCanonicalRow; this
construction does not assert a comparison or RMS saving. -/
theorem eventually_source_B578_actual_all_cell_comparison_data434
    (jQ mmax cm s0 s1 vexp : ℕ) (K Carc Cχ : ℝ)
    (hK : 0 ≤ K) (hcm : K+92 ≤ (cm:ℝ))
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ) (hCχpos : 0<Cχ)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀j,0 ≤ Kpsi j) :
    let cfg := sourceB578ActualFixed434 jQ mmax cm s0 s1 vexp K Carc Cχ
      hCarc hCχ hCχpos Kpsi hKpsi
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 6 L).Nonempty ∧
      jQ ≤ sourceOriginalLiteralDepth 6 L ∧
      SourceB578ActualAllCellRecords434 cfg L jQ K mmax := by
  let cfg := sourceB578ActualFixed434 jQ mmax cm s0 s1 vexp K Carc Cχ
    hCarc hCχ hCχpos Kpsi hKpsi
  have hCarc0 : 0 ≤ Carc := (Nat.cast_nonneg cm).trans hCarc
  have hScales := Filter.eventually_all.mpr
    (fun m : Fin (mmax+1) => eventually_source_native_original_comparison_cell_scales434
      6 (by norm_num) K hK m.val Carc hCarc0)
  have hArc := eventually_native_r6_original_comparison_arc_gates434
    jQ mmax cm s0 vexp Carc Cχ (K+91) hCarc hCχ hCχpos Kpsi hKpsi
  filter_upwards [hScales,hArc,eventually_source_native_original_group_masses434 6 (by norm_num),
    eventually_source_B578_actual_fixed_Q_all_slots434 jQ,
    eventually_ge_atTop (max (Real.exp 2) 4)] with L hscale hArcL hmass hQ hL
  have hL4 : 4 ≤ L := (le_max_right _ _).trans hL
  have hLe2 : Real.exp 2 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0<L := by linarith
  refine ⟨hmass.2.1,hQ.1,?_⟩
  unfold SourceB578ActualAllCellRecords434
  intro hS U V hUVlo hUVhi N j hj hN J m hmJ hmm nu hnu
    hA hB xi hhA hhB hxi hA1 hB1 ja jb ha hb b hbq slot delta freq
    k hk chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1
    psi hSmooth hSupport hBudget Delta y hDelta hWy lo hi Qcomp aux hAux hAuxA hAuxB target tw
  dsimp only
  let Z := sourceCorrectedDyadicScale U V (L^K) j
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let Y := Z*Hp
  let Ncap : ℕ := ⌈64*Y⌉₊
  have hsc := (hscale ⟨m,by omega⟩).2.2 U V hUVlo hUVhi N j hj hN nu hnu
    hA hB xi hhA hhB hA1 hB1 ja jb ha hb
  dsimp only at hsc
  rcases hsc with ⟨hlog,hZpos,hHpos,hY4,hYstrong,hYmax,hZ,hcap,hNcap,hHband,hArcCap,hks⟩
  have hkfields := hks k hk
  have hGroups := source_B578_actual_group_counts_Cfour434 6 L hLe2 hS
  have hMass := hmass.2.2 hS
  have hG := source_native_original_G_identity434 6 L hS hmass.1
  have hSG : sourceNativeOriginalS434 6 L hS ⊆ sourceNativeOriginalG434 6 L := by
    rw [hG]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have hDisj := source_native_original_small_group_disjoint434 6 L hS (by norm_num) hmass.1
  have hPcap := source_B578_actual_P_below_comparison_cap434 6 L Y hL4 Ncap hYstrong hcap
  have hQcap := source_native_original_r6_Qslot_below_actual_Ncap434
    (sourceOriginalLiteralDepth 6 L) L hL1 b Y Ncap hYstrong hcap
  have hQfields := hQ.2 b hbq
  dsimp only at hQfields
  rcases hQfields with ⟨hI,hSlot,hIBand,hLong,hSlotMin⟩
  obtain ⟨hAne,_,hBne,_⟩ := (source_original_two_block_probe_pattern_mem434
    (sourceNativeOriginalBigBlockA434 6 L) (sourceNativeOriginalBigBlockB434 6 L)
    m nu.1 nu.2).mp hnu
  let aA : nu.1 → ℕ := fun z=>aux (Sum.inl z)
  let aB : nu.2 → ℕ := fun z=>aux (Sum.inr z)
  have hFA : (Finset.range (Fintype.card nu.1)).Nonempty := by
    have hc : 0<Fintype.card nu.1 := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hAne
    exact ⟨0,Finset.mem_range.mpr hc⟩
  have hFB : (Finset.range (Fintype.card nu.2)).Nonempty := by
    have hc : 0<Fintype.card nu.2 := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hBne
    exact ⟨0,Finset.mem_range.mpr hc⟩
  have hPrA : ∀i : Fin (Fintype.card nu.1),
      sourceOriginalProbeIndexedPrime434 aA i ∈ sourceNativeOriginalTb434 6 L
        ((Fintype.equivFin nu.1).symm i).val.1 ∧
      (sourceOriginalProbeIndexedPrime434 aA i).Prime ∧
      Real.exp (L^(3/10:ℝ)) ≤ (sourceOriginalProbeIndexedPrime434 aA i:ℝ) := by
    intro i
    have hp : aA ((Fintype.equivFin nu.1).symm i) ∈ sourceNativeOriginalTb434 6 L
        ((Fintype.equivFin nu.1).symm i).val.1 :=
      (Fintype.mem_piFinset.mp hAux) (Sum.inl ((Fintype.equivFin nu.1).symm i))
    have hr := source_native_original_Tb_prime_range434 6 L _ _ hp
    simpa only [sourceOriginalProbeIndexedPrime434,dite_eq_left i.isLt] using ⟨hp,hr.1,hr.2.1⟩
  have hPrB : ∀i : Fin (Fintype.card nu.2),
      sourceOriginalProbeIndexedPrime434 aB i ∈ sourceNativeOriginalTb434 6 L
        ((Fintype.equivFin nu.2).symm i).val.1 ∧
      (sourceOriginalProbeIndexedPrime434 aB i).Prime ∧
      Real.exp (L^(3/10:ℝ)) ≤ (sourceOriginalProbeIndexedPrime434 aB i:ℝ) := by
    intro i
    have hp : aB ((Fintype.equivFin nu.2).symm i) ∈ sourceNativeOriginalTb434 6 L
        ((Fintype.equivFin nu.2).symm i).val.1 :=
      (Fintype.mem_piFinset.mp hAux) (Sum.inr ((Fintype.equivFin nu.2).symm i))
    have hr := source_native_original_Tb_prime_range434 6 L _ _ hp
    simpa only [sourceOriginalProbeIndexedPrime434,dite_eq_left i.isLt] using ⟨hp,hr.1,hr.2.1⟩
  have hCellA : Real.log (((∏i ∈ Finset.range (Fintype.card nu.1),
      sourceOriginalProbeIndexedPrime434 aA i):ℕ):ℝ) ≤
      Real.log (Real.exp ((ja:ℝ)*hA))+1 := by
    rw [source_original_probe_indexed_prime_product434,Real.log_exp]
    change Real.log (sourceOriginalProbeDA434 m nu aux:ℝ) ≤ (ja:ℝ)*hA+1
    have hu := hAuxA.2
    linarith
  have hCellB : Real.log (((∏i ∈ Finset.range (Fintype.card nu.2),
      sourceOriginalProbeIndexedPrime434 aB i):ℕ):ℝ) ≤
      Real.log (Real.exp ((jb:ℝ)*hB))+1 := by
    rw [source_original_probe_indexed_prime_product434,Real.log_exp]
    change Real.log (sourceOriginalProbeDB434 m nu aux:ℝ) ≤ (jb:ℝ)*hB+1
    have hu := hAuxB.2
    linarith
  have hAlpha := source_native_original_r6_D20_alpha_comparison_fields434
    cfg rfl L Delta y hL1 hDelta hWy lo hi
  have hQSkip : ∀v,‖sourceNativeOriginalLiteralResidual434 L b slot delta freq v‖ ≤ 1 :=
    fun v => source_native_original_six_QSkip_negative_frequency_c434
      L hLp b slot delta freq v
  have hqCap : (k.natAbs:ℝ) ≤ L^cfg.cm := by
    calc
      _  ≤  L^(K+92) := hkfields.2.2.2.1
      _  ≤  L^(cm:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hcm
      _ = L^cfg.cm := by simp only [Real.rpow_natCast]; rfl
  have hmod : L^(2*cfg.cm) ≤ Real.exp (Real.sqrt L) := by
    have h := hArcL.2.1
    have hcast : (2*(cm:ℝ))=((2*cm:ℕ):ℝ) := by push_cast; ring
    change L^(2*(cm:ℝ)) ≤ _ at h
    rw [hcast,Real.rpow_natCast] at h
    exact h
  let data : SourceComparisonData434
      (sourceNativeOriginalTsType434 6 L hS) (sourceNativeOriginalBigType434 6 L)
      cfg (Real.exp L) L Y Hp := {
    Z := Z
    hY := hY4
    hYmax := hYmax
    hH := hHpos
    hYstrong := hYstrong
    hZ := hZ
    hYIdent := rfl
    hSmallGroups := hGroups.1
    hBigGroups := hGroups.2
    lo := lo
    hi := hi
    Ncap := Ncap
    alpha := sourceNativeOriginalFullD20Alpha434 Delta (Real.exp (Real.sqrt L)) y
    hNcap := hNcap
    hCap := hcap
    hAlpha := hAlpha.1
    G := sourceNativeOriginalG434 6 L
    Ptw := if tw then sourceNativeOriginalG434 6 L else ∅
    S := sourceNativeOriginalS434 6 L hS
    primeSlot := sourceOriginalQActualBands 6 (sourceOriginalLiteralDepth 6 L) L b
    Ts := sourceNativeOriginalTs434 6 L hS
    Tb := sourceNativeOriginalTb434 6 L
    Vs := sourceNativeOriginalVs434 6 L hS
    Vsmall := sourceNativeOriginalVsmall434 6 L hS
    Vbig := sourceNativeOriginalVbig434 6 L
    ts := fun _=>1
    tb := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
    coef := sourceB578CanonicalRow434 J 1 m hmJ nu Qcomp hA hB xi
      (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux target
    k := 0
    qBase := k.natAbs
    c := sourceNativeOriginalLiteralResidual434 L b slot delta freq
    chi0 := chi
    hBase := hkfields.2.2.1
    hBaseCap := hqCap
    hk := by change 0+1 ≤ 1+mmax; omega
    hVs := hMass.1.1
    hts := fun _=>by change 1 ≤ 1+mmax; omega
    htb := fun g=> (source_original_probe_free_mark_cap434 J 1 m hmJ nu g).trans (by change 1+m ≤ 1+mmax; omega)
    hVsmall := fun i=>(hMass.2.1 i).1
    hVbig := fun g=>(hMass.2.2 g).1
    hcoef := fun a=>source_B578_actual_canonical_row_norm434 J 1 m hmJ nu Qcomp hA hB xi
      (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux a target hhA hhB hxi
    C := 1
    hC := by norm_num
    hCBudget := by change (1:ℝ) ≤ L^0; simp
    hcBound := hQSkip
    sigma0 := sigma0
    sigma1 := sigma1
    hSigma0 := hsigma0
    hSigma1 := hsigma1
    hModScale := hmod
    hSG := hSG
    hSPrime := fun p hp=>(source_native_original_S_prime_range434 6 L hS p hp).1
    hSN := fun p hp=>hPcap p (hSG hp)
    hPN := hQcap
    hRough := hAlpha.2
    hGroup := fun p hp=>(source_native_original_G_bound434 6 L hL1 p hp).2
    hLong := hLong
    I := Set.Icc (Real.exp (cfg.τ*L)) (Real.exp (cfg.η*L))
    hI := hI
    hSmall := fun p hp=>(source_native_original_S_prime_range434 6 L hS p hp).2
    hSlot := hSlot
    hIBand := hIBand
    F1 := Finset.range (Fintype.card nu.1)
    F2 := Finset.range (Fintype.card nu.2)
    p1 := sourceOriginalProbeIndexedPrime434 aA
    p2 := sourceOriginalProbeIndexedPrime434 aB
    U1 := Real.exp ((ja:ℝ)*hA)
    U2 := Real.exp ((jb:ℝ)*hB)
    hF1 := hFA
    hF2 := hFB
    hp1 := fun i hi=>(hPrA ⟨i,Finset.mem_range.mp hi⟩).2.1.one_le
    hp2 := fun i hi=>(hPrB ⟨i,Finset.mem_range.mp hi⟩).2.1.one_le
    hmin1 := fun i hi=>(hPrA ⟨i,Finset.mem_range.mp hi⟩).2.2
    hmin2 := fun i hi=>(hPrB ⟨i,Finset.mem_range.mp hi⟩).2.2
    hU1 := Real.exp_pos _
    hU2 := Real.exp_pos _
    hcell1 := hCellA
    hcell2 := hCellB
    hHIdent := rfl
    psi1 := psi
    hSmooth := hSmooth
    hSupport := hSupport
    v1 := v1
    hv1 := hv1
    hBudget := hBudget
    hG := hG
    hParity := by cases tw <;> simp
    hTsPrime := fun i p hp=>(source_native_original_Ts_prime_range434 6 L hS i p hp).1
    hTbPrime := fun g p hp=>(source_native_original_Tb_prime_range434 6 L g p hp).1
    hOrigW := hArcL.2.2.1
    hOrigSmall := hArcL.2.2.2.1
    hOrigLong := hArcL.2.2.2.2
    hSlotMin := hSlotMin
    hHband := hHband
    hArcCap := hArcCap
    hDisjS := fun i p hp hpi=>Finset.disjoint_left.mp (hDisj.1 i) hp hpi
    hDisjB := fun g p hp hpg=>Finset.disjoint_left.mp (hDisj.2.1 g) hp hpg }
  refine ⟨data,?_⟩
  dsimp only [data]
  repeat' constructor
end Green64Analytic.SourceBlockSieve

end

end

/-! ## LiteralProfileAllCellData -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 12000

/-- The actual complete-family contract with both original endpoint profiles
BUILT IN. There is no psi variable or smoothness/support/derivative premise.
All physical canonical rows, original arithmetic and Fourier variables remain. -/
def SourceB578ActualLiteralProfileCellRecords434
    (cfg : SourceComparisonFixed434) (L : ℝ) (jQ : ℕ) (K : ℝ) (mmax : ℕ) : Prop :=
  ∀ (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (U V : ℝ), Real.exp L/4 ≤ U*V → U*V ≤ 3*Real.exp L →
  ∀ (N j : ℕ), j ≤ N → (2:ℝ)^N ≤ 384*L^(89:ℝ) →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 6 L) (sourceNativeOriginalBigBlockB434 6 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA ≤ 1 → hB ≤ 1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 6 L)
      (sourceNativeOriginalVbig434 6 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 6 L)
      (sourceNativeOriginalVbig434 6 L) nu hB xi →
  ∀ (b : Fin (sourceOriginalLiteralDepth 6 L+1)), b.val=jQ →
  ∀ (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (k : ℤ), k ∈ sourceCorrectedSmoothKSet (L^K) (L^(89:ℝ)) →
  ∀ (chi : DirichletCharacter ℂ k.natAbs) (sigma0 sigma1 v1 : ℝ),
    |sigma0| ≤ L^cfg.s0 → |sigma1| ≤ L^cfg.s1base → |v1| ≤ L^cfg.vexp →
  ∀ (reciprocal : Bool),
  ∀ (Delta y : ℝ), 0<Delta → Real.exp (Real.sqrt L) ≤ y →
  ∀ (lo hi Qcomp : ℕ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 6 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (target : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g) → ℕ)
    (tw : Bool),
  let Z := sourceCorrectedDyadicScale U V (L^K) j
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let P := sourceNativeOriginalTb434 6 L
  let Vm := sourceNativeOriginalVbig434 6 L
  let row := sourceB578CanonicalRow434 J 1 m hmJ nu Qcomp hA hB xi P Vm aux target
  ∃ data : SourceComparisonData434
      (sourceNativeOriginalTsType434 6 L hS) (sourceNativeOriginalBigType434 6 L)
      cfg (Real.exp L) L (Z*Hp) Hp,
    data.Z=Z ∧ data.Ncap=⌈64*(Z*Hp)⌉₊ ∧
    data.G=sourceNativeOriginalG434 6 L ∧
    data.Ptw=(if tw then sourceNativeOriginalG434 6 L else ∅) ∧
    data.S=sourceNativeOriginalS434 6 L hS ∧
    data.Ts=sourceNativeOriginalTs434 6 L hS ∧ data.Tb=P ∧
    data.Vs=sourceNativeOriginalVs434 6 L hS ∧
    data.Vsmall=sourceNativeOriginalVsmall434 6 L hS ∧ data.Vbig=Vm ∧
    data.ts=(fun _=>1) ∧ data.tb=sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu ∧
    HEq data.coef row ∧ data.k=0 ∧
    data.alpha=sourceNativeOriginalFullD20Alpha434 Delta (Real.exp (Real.sqrt L)) y ∧
    data.lo=lo ∧ data.hi=hi ∧
    data.F1=Finset.range (Fintype.card nu.1) ∧
    data.F2=Finset.range (Fintype.card nu.2) ∧
    data.p1=sourceOriginalProbeIndexedPrime434 (fun z : nu.1=>aux (Sum.inl z)) ∧
    data.p2=sourceOriginalProbeIndexedPrime434 (fun z : nu.2=>aux (Sum.inr z)) ∧
    data.U1=Real.exp ((ja:ℝ)*hA) ∧ data.U2=Real.exp ((jb:ℝ)*hB) ∧
    data.primeSlot=sourceOriginalQActualBands 6 (sourceOriginalLiteralDepth 6 L) L b ∧
    data.c=sourceNativeOriginalLiteralResidual434 L b slot delta freq ∧ data.C=1 ∧
    data.qBase=k.natAbs ∧ HEq data.chi0 chi ∧
    data.sigma0=sigma0 ∧ data.sigma1=sigma1 ∧ data.v1=v1 ∧ data.psi1=sourceB578EndpointProfile434 reciprocal

/-- The exact original theta and theta/r instantiate the full all-real
comparison records.  Their common derivative sequence and nonzero plateau
are fixed before L and before every actual mark, character and phase.
The kappa restoration factor from the full canonical row is unchanged. -/
theorem eventually_source_B578_literal_profile_all_cell_data434
    (jQ mmax cm s0 s1 vexp : ℕ) (K Carc Cχ : ℝ)
    (hK : 0 ≤ K) (hcm : K+92 ≤ (cm:ℝ))
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ) (hCχpos : 0<Cχ) :
    let cfg := sourceB578ActualFixed434 jQ mmax cm s0 s1 vexp K Carc Cχ
      hCarc hCχ hCχpos sourceB578ThetaBudget434 source_B578_literal_theta_budget_nonneg434
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 6 L).Nonempty ∧
      jQ ≤ sourceOriginalLiteralDepth 6 L ∧
      SourceB578ActualLiteralProfileCellRecords434 cfg L jQ K mmax := by
  let cfg := sourceB578ActualFixed434 jQ mmax cm s0 s1 vexp K Carc Cχ
    hCarc hCχ hCχpos sourceB578ThetaBudget434 source_B578_literal_theta_budget_nonneg434
  filter_upwards [eventually_source_B578_actual_all_cell_comparison_data434
    jQ mmax cm s0 s1 vexp K Carc Cχ hK hcm hCarc hCχ hCχpos
    sourceB578ThetaBudget434 source_B578_literal_theta_budget_nonneg434] with L hL
  refine ⟨hL.1,hL.2.1,?_⟩
  unfold SourceB578ActualLiteralProfileCellRecords434
  intro hS U V hUVlo hUVhi N j hj hN J m hmJ hmm nu hnu
    hA hB xi hhA hhB hxi hA1 hB1 ja jb ha hb b hbq slot delta freq
    k hk chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1 reciprocal
    Delta y hDelta hWy lo hi Qcomp aux hAux hAuxA hAuxB target tw
  have hProfile := source_B578_literal_endpoint_profile_fields434 reciprocal
  exact hL.2.2 hS U V hUVlo hUVhi N j hj hN J m hmJ hmm nu hnu
    hA hB xi hhA hhB hxi hA1 hB1 ja jb ha hb b hbq slot delta freq
    k hk chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1
    (sourceB578EndpointProfile434 reciprocal) hProfile.1 hProfile.2.1 (hProfile.2.2.1 L)
    Delta y hDelta hWy lo hi Qcomp aux hAux hAuxA hAuxB target tw
end Green64Analytic.SourceBlockSieve

end

end

/-! ## LiteralD36Mask -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The already loaded production D36 mask is definitionally the literal
original source definition, including both physical endpoints. -/
theorem source_B578_original_D36_mask_defeq434
    (b eta delta L : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    sourceD36OriginalCofactorMask b eta delta L f n =
      if Real.exp ((1-eta)*L) ≤ (n:ℝ) ∧ (n:ℝ) ≤ Real.exp ((1-b+delta)*L)
      then (f n:ℂ) else 0 := rfl

/-- ORIGINAL D61 cofactor coefficient, with the full unshortened D20 cell,
D36 physical cofactor mask, and original upper cap.  a,eta,delta are the
source bin parameters; the chosen positive D35 witness is not reselected. -/
def sourceB578OriginalD36UpperAlpha434 (a eta delta L : ℝ) (n : ℕ) : ℂ :=
  if n ≤ ⌊2*Real.exp L⌋₊+2 then
    sourceD36OriginalCofactorMask a eta delta L
      (sourceD20FullDelta (1/L) (Real.exp (Real.sqrt L)) (Real.exp (a*L))) n
  else 0

/-- Exact zeroing masks preserve the proved full D20 size and roughness.
No arbitrary scalar-discrepancy or signed cancellation input is introduced. -/
theorem source_B578_literal_D36_upper_alpha_fields434
    (a eta delta L : ℝ) (hWy : Real.exp (Real.sqrt L) ≤ Real.exp (a*L)) :
    (∀n,‖sourceB578OriginalD36UpperAlpha434 a eta delta L n‖ ≤ 1) ∧
    (∀n,sourceB578OriginalD36UpperAlpha434 a eta delta L n≠0 →
      SourceRoughAbove n (Real.exp (Real.sqrt L))) := by
  constructor
  · intro n
    have h := source_native_original_FULL_D20_global_abs_le_one434
      (1/L) (Real.exp (Real.sqrt L)) (Real.exp (a*L)) hWy n
    unfold sourceB578OriginalD36UpperAlpha434 sourceD36OriginalCofactorMask
    split_ifs <;> simp only [norm_zero,Complex.norm_real,Real.norm_eq_abs] <;> linarith
  · intro n hn
    apply source_native_original_FULL_D20_rough_support434
      (1/L) (Real.exp (Real.sqrt L)) (Real.exp (a*L)) hWy n
    intro hz
    apply hn
    unfold sourceB578OriginalD36UpperAlpha434 sourceD36OriginalCofactorMask
    split_ifs <;> simp only [hz,Complex.ofReal_zero]

/-- Uniform in EVERY original bin a>=b0. The same fixed positive b0 can be
the coupled D35 witness cutoff; no substitute witness or bin is chosen. -/
theorem eventually_source_B578_original_bin_roughness_gate434
    (b0 : ℝ) (hb0 : 0<b0) :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧ ∀a : ℝ,b0 ≤ a →
      Real.exp (Real.sqrt L) ≤ Real.exp (a*L) := by
  filter_upwards [eventually_ge_atTop (max (4:ℝ) ((b0⁻¹)^2))] with L hL
  have hL4 : 4 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 ≤ L := by linarith
  have hs := Real.sqrt_le_sqrt ((le_max_right _ _).trans hL)
  have hInv : b0⁻¹ ≤ Real.sqrt L := by
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos (inv_pos.mpr hb0)] using hs
  have hm : 1 ≤ b0*Real.sqrt L := by
    have h := mul_le_mul_of_nonneg_left hInv hb0.le
    simpa only [mul_inv_cancel₀ hb0.ne'] using h
  refine ⟨hL4,?_⟩
  intro a ha
  apply Real.exp_le_exp.mpr
  calc
    Real.sqrt L = 1*Real.sqrt L := by ring
    _ ≤ (b0*Real.sqrt L)*Real.sqrt L := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg L)
    _ = b0*L := by rw [mul_assoc,←pow_two,Real.sq_sqrt hLp]
    _ ≤ a*L := mul_le_mul_of_nonneg_right ha hLp
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FullDecoratedNativeEndpoint -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 14000

/-- Every actual SMALL and BIG P group, without forcing equal cardinalities. -/
def sourceB578ActualAllGroups434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) :
    (Unit ⊕ (sourceNativeOriginalTsType434 6 L hS ⊕ sourceNativeOriginalBigType434 6 L)) → Finset ℕ :=
  Sum.elim (fun _ : Unit=>sourceNativeOriginalS434 6 L hS)
    (Sum.elim (sourceNativeOriginalTs434 6 L hS) (sourceNativeOriginalTb434 6 L))

/-- The literal native QSkip core, D36/upper/dyadic alphaD and marked
canonical row endpoint. sourceSide=true carries the conjugate normalized
Knu row; false carries its actual target selector.  Physical k is used in
qBase=|k|; distinguished S has ONE mark, hence source-data mark order zero. -/
def sourceB578ActualNativeRowEndpoint434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (sourceSide : Bool)
    (target : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g) → ℕ)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta deltaC : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigma0 sigma1 : ℝ) (Lambda : ℕ → ℂ) (n : ℕ) : ℂ :=
  Lambda n * primeSlotCoreValue (sourceB578ActualAllGroups434 L hS)
    (sourceNativePrimeCore 6 (sourceOriginalLiteralDepth 6 L) L b slot delta (-freq)
      (Finset.Icc lo hi) (sourceB578OriginalD36UpperAlpha434 a eta deltaC L)
      k.natAbs chi sigma0 sigma1) n *
    actualBigMarkDecoration (sourceB578ActualAllGroups434 L hS)
      (Sum.elim (fun _ : Unit=>1) (Sum.elim (fun _=>1)
        (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu))) (1/2:ℝ)
      (Sum.elim (fun _ : Unit=>sourceNativeOriginalVs434 6 L hS)
        (Sum.elim (sourceNativeOriginalVsmall434 6 L hS) (sourceNativeOriginalVbig434 6 L)))
      (fun marks=>sourceB578ActualPairCoef434 J 1 m hmJ nu Q hA hB xi
        (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux sourceSide target
        (fun g=>marks (.inr (.inr g)))) n

/-- Concrete decorated extension of B538's ordinary-core adapter.  B524 is
used exactly, then the original all-group marked split; RAW W1 is never
substituted for the canonical free-mark counts or row coefficient. -/
theorem source_B578_actual_full_marked_endpoint_eq_native434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (sourceSide : Bool)
    (target : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g) → ℕ)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta deltaC : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigma0 sigma1 : ℝ) (Lambda : ℕ → ℂ) (n : ℕ) :
    sourceOriginalFullEndpointCoefficients434 k.natAbs
      (sourceNativeOriginalS434 6 L hS) (sourceNativeOriginalTs434 6 L hS) (sourceNativeOriginalTb434 6 L)
      (1/2:ℝ) (sourceNativeOriginalVs434 6 L hS) (sourceNativeOriginalVsmall434 6 L hS)
      (sourceNativeOriginalVbig434 6 L) (fun _=>1)
      (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu)
      (sourceB578ActualPairCoef434 J 1 m hmJ nu Q hA hB xi
        (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux sourceSide target)
      0 (sourceOriginalQActualBands 6 (sourceOriginalLiteralDepth 6 L) L b)
      (sourceAlphaDyadicCut (sourceB578OriginalD36UpperAlpha434 a eta deltaC L) lo hi)
      (sourceNativeOriginalLiteralResidual434 L b slot delta freq)
      chi sigma0 sigma1 Lambda (n:ℤ) =
    sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Q hA hB xi aux sourceSide target
      b slot delta freq lo hi a eta deltaC k chi sigma0 sigma1 Lambda n := by
  have hSplit := source_original_marked_core_endpoint_split434
    (sourceNativeOriginalS434 6 L hS) (sourceNativeOriginalTs434 6 L hS) (sourceNativeOriginalTb434 6 L)
    (1/2:ℝ) (sourceNativeOriginalVs434 6 L hS) (sourceNativeOriginalVsmall434 6 L hS)
    (sourceNativeOriginalVbig434 6 L) 0 (fun _=>1)
    (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu)
    (sourceB578ActualPairCoef434 J 1 m hmJ nu Q hA hB xi
      (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux sourceSide target)
    n k.natAbs (sourceOriginalQActualBands 6 (sourceOriginalLiteralDepth 6 L) L b)
    (sourceAlphaDyadicCut (sourceB578OriginalD36UpperAlpha434 a eta deltaC L) lo hi)
    (sourceNativeOriginalLiteralResidual434 L b slot delta freq) Lambda chi sigma0 sigma1
  have hCore := source_native_B524_original_sorted_QSkip_Fock_core_equals_T434
    (sourceB578ActualAllGroups434 L hS) 6 (sourceOriginalLiteralDepth 6 L) L b slot
    delta (-freq) (Finset.Icc lo hi) (sourceB578OriginalD36UpperAlpha434 a eta deltaC L)
    k.natAbs chi sigma0 sigma1 n
  have hLift := congrArg (fun c : ℂ=>Lambda n*c*
    actualBigMarkDecoration (sourceB578ActualAllGroups434 L hS)
      (Sum.elim (fun _ : Unit=>1) (Sum.elim (fun _=>1)
        (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu))) (1/2:ℝ)
      (Sum.elim (fun _ : Unit=>sourceNativeOriginalVs434 6 L hS)
        (Sum.elim (sourceNativeOriginalVsmall434 6 L hS) (sourceNativeOriginalVbig434 6 L)))
      (fun marks=>sourceB578ActualPairCoef434 J 1 m hmJ nu Q hA hB xi
        (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux sourceSide target
        (fun g=>marks (.inr (.inr g)))) n) hCore
  exact hSplit.symm.trans hLift
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualNativePhysicalRecords -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 14000

/-- Source constants use the actual bounded native Fourier boxes. s1=0 is
the literal second core phase; the two endpoint cutoff phases are separate. -/
def sourceB578NativeEndpointFixed434
    (jQ mmax cm nout nin : ℕ) (K Carc Cχ : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ) (hCχpos : 0<Cχ) :
    SourceComparisonFixed434 :=
  sourceB578ActualFixed434 jQ mmax cm (max nout nin+2) 0 (max (max nout nin) 3+3)
    K Carc Cχ hCarc hCχ hCχpos sourceB578ThetaBudget434 source_B578_literal_theta_budget_nonneg434

/-- Complete original actual records, now with every profile and endpoint
phase gate discharged, the literal D36/upper alphaD installed, and the
correct source conjugate-row / target-selector pair built in. -/
def SourceB578NativePhysicalRecords434
    (cfg : SourceComparisonFixed434) (L : ℝ) (jQ : ℕ) (K b0 : ℝ) (mmax nout nin : ℕ) : Prop :=
  ∀ (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (U V : ℝ), Real.exp L/4 ≤ U*V → U*V ≤ 3*Real.exp L →
  ∀ (N j : ℕ), j ≤ N → (2:ℝ)^N ≤ 384*L^(89:ℝ) →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 6 L) (sourceNativeOriginalBigBlockB434 6 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA ≤ 1 → hB ≤ 1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 6 L)
      (sourceNativeOriginalVbig434 6 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 6 L)
      (sourceNativeOriginalVbig434 6 L) nu hB xi →
  ∀ (b : Fin (sourceOriginalLiteralDepth 6 L+1)), b.val=jQ →
  ∀ (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (k : ℤ), k ∈ sourceCorrectedSmoothKSet (L^K) (L^(89:ℝ)) →
  ∀ (chi : DirichletCharacter ℂ k.natAbs) (rho : ℝ) (zeta : Fin 3 → ℝ) (t : ℝ),
    |rho| ≤ L^nout → (∀i,|zeta i| ≤ L^nin) → |t| ≤ L^3 →
  ∀ (sourceSide : Bool) (a eta deltaC : ℝ), b0 ≤ a →
  ∀ (lo hi Qcomp : ℕ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 6 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (target : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g) → ℕ),
  let Z := sourceCorrectedDyadicScale U V (L^K) j
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let P := sourceNativeOriginalTb434 6 L
  let Vm := sourceNativeOriginalVbig434 6 L
  let row := sourceB578ActualPairCoef434 J 1 m hmJ nu Qcomp hA hB xi P Vm aux sourceSide target
  ∃ data : SourceComparisonData434
      (sourceNativeOriginalTsType434 6 L hS) (sourceNativeOriginalBigType434 6 L)
      cfg (Real.exp L) L (Z*Hp) Hp,
    data.Z=Z ∧ data.Ncap=⌈64*(Z*Hp)⌉₊ ∧
    data.G=sourceNativeOriginalG434 6 L ∧
    data.Ptw=sourceNativeOriginalG434 6 L ∧
    data.S=sourceNativeOriginalS434 6 L hS ∧
    data.Ts=sourceNativeOriginalTs434 6 L hS ∧ data.Tb=P ∧
    data.Vs=sourceNativeOriginalVs434 6 L hS ∧
    data.Vsmall=sourceNativeOriginalVsmall434 6 L hS ∧ data.Vbig=Vm ∧
    data.ts=(fun _=>1) ∧ data.tb=sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu ∧
    HEq data.coef row ∧ data.k=0 ∧
    data.alpha=sourceB578OriginalD36UpperAlpha434 a eta deltaC L ∧
    data.lo=lo ∧ data.hi=hi ∧
    data.F1=Finset.range (Fintype.card nu.1) ∧
    data.F2=Finset.range (Fintype.card nu.2) ∧
    data.p1=sourceOriginalProbeIndexedPrime434 (fun z : nu.1=>aux (Sum.inl z)) ∧
    data.p2=sourceOriginalProbeIndexedPrime434 (fun z : nu.2=>aux (Sum.inr z)) ∧
    data.U1=Real.exp ((ja:ℝ)*hA) ∧ data.U2=Real.exp ((jb:ℝ)*hB) ∧
    data.primeSlot=sourceOriginalQActualBands 6 (sourceOriginalLiteralDepth 6 L) L b ∧
    data.c=sourceNativeOriginalLiteralResidual434 L b slot delta freq ∧ data.C=1 ∧
    data.qBase=k.natAbs ∧ HEq data.chi0 chi ∧
    data.sigma0=(if sourceSide then 2*Real.pi*rho-2*Real.pi*zeta 1
      else 2*Real.pi*zeta 0+2*Real.pi*rho) ∧ data.sigma1=0 ∧
    data.v1=(if sourceSide then -(2*Real.pi*rho+2*Real.pi*zeta 2+2*Real.pi*t)
      else -2*Real.pi*rho) ∧ data.psi1=sourceB578EndpointProfile434 sourceSide ∧
    ∀n : ℕ,data.endpoint (n:ℤ) =
      sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Qcomp hA hB xi aux sourceSide target
        b slot delta freq lo hi a eta deltaC k chi
        (if sourceSide then 2*Real.pi*rho-2*Real.pi*zeta 1 else 2*Real.pi*zeta 0+2*Real.pi*rho) 0
        (fun x=>sourceB578EndpointProfile434 sourceSide ((x:ℝ)/(Z*Hp))*
          sourcePhase x (if sourceSide then -(2*Real.pi*rho+2*Real.pi*zeta 2+2*Real.pi*t)
            else -2*Real.pi*rho)) n

/-- All sufficiently large real L, with one threshold before every native
cell, physical mark, Fourier point, character and source/target choice.
The same b0 may be the original positive D35 witness. data.k=0 denotes the
S mark order (one S mark); signed physical k remains qBase=|k| and shift 2k.
No analytic comparison, RMS or root saving is assumed or asserted. -/
theorem eventually_source_B578_actual_native_physical_records434
    (jQ mmax cm nout nin : ℕ) (K b0 Carc Cχ : ℝ)
    (hK : 0 ≤ K) (hb0 : 0<b0) (hcm : K+92 ≤ (cm:ℝ))
    (hCarc : (cm:ℝ) ≤ Carc) (hCχ : (cm:ℝ) ≤ Cχ) (hCχpos : 0<Cχ) :
    let cfg := sourceB578NativeEndpointFixed434 jQ mmax cm nout nin K Carc Cχ hCarc hCχ hCχpos
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 6 L).Nonempty ∧
      jQ ≤ sourceOriginalLiteralDepth 6 L ∧
      SourceB578NativePhysicalRecords434 cfg L jQ K b0 mmax nout nin := by
  let cfg := sourceB578NativeEndpointFixed434 jQ mmax cm nout nin K Carc Cχ hCarc hCχ hCχpos
  have hCarc0 : 0 ≤ Carc := (Nat.cast_nonneg cm).trans hCarc
  have hScales := Filter.eventually_all.mpr
    (fun m : Fin (mmax+1) => eventually_source_native_original_comparison_cell_scales434
      6 (by norm_num) K hK m.val Carc hCarc0)
  have hArc := eventually_native_r6_original_comparison_arc_gates434
    jQ mmax cm (max nout nin+2) (max (max nout nin) 3+3) Carc Cχ (K+91)
    hCarc hCχ hCχpos sourceB578ThetaBudget434 source_B578_literal_theta_budget_nonneg434
  filter_upwards [hScales,hArc,eventually_source_native_original_group_masses434 6 (by norm_num),
    eventually_source_B578_actual_fixed_Q_all_slots434 jQ,
    eventually_ge_atTop (max (Real.exp 2) 4),
    eventually_source_B578_original_bin_roughness_gate434 b0 hb0] with L hscale hArcL hmass hQ hL hBins
  have hL4 : 4 ≤ L := (le_max_right _ _).trans hL
  have hLe2 : Real.exp 2 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0<L := by linarith
  refine ⟨hmass.2.1,hQ.1,?_⟩
  unfold SourceB578NativePhysicalRecords434
  intro hS U V hUVlo hUVhi N j hj hN J m hmJ hmm nu hnu
    hA hB xi hhA hhB hxi hA1 hB1 ja jb ha hb b hbq slot delta freq
    k hk chi rho zeta t hrho hzeta ht sourceSide a eta deltaC ha0
    lo hi Qcomp aux hAux hAuxA hAuxB target
  let sigma0 := if sourceSide then 2*Real.pi*rho-2*Real.pi*zeta 1 else 2*Real.pi*zeta 0+2*Real.pi*rho
  let v1 := if sourceSide then -(2*Real.pi*rho+2*Real.pi*zeta 2+2*Real.pi*t) else -2*Real.pi*rho
  let psi := sourceB578EndpointProfile434 sourceSide
  have hPh := source_B578_literal_native_phase_boxes434 L nout nin rho zeta t hL4 hrho hzeta ht
  have hsigma0 : |sigma0| ≤ L^cfg.s0 := by
    cases sourceSide
    · exact hPh.2.1
    · exact hPh.1
  have hsigma1 : |(0:ℝ)| ≤ L^cfg.s1base := by change |(0:ℝ)| ≤ L^0; simp
  have hv1 : |v1| ≤ L^cfg.vexp := by
    cases sourceSide
    · exact hPh.2.2.2.1
    · exact hPh.2.2.1
  have hProfile := source_B578_literal_endpoint_profile_fields434 sourceSide
  have hSmooth := hProfile.1
  have hSupport := hProfile.2.1
  have hBudget := hProfile.2.2.1 L
  dsimp only
  let Z := sourceCorrectedDyadicScale U V (L^K) j
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let Y := Z*Hp
  let Ncap : ℕ := ⌈64*Y⌉₊
  have hsc := (hscale ⟨m,by omega⟩).2.2 U V hUVlo hUVhi N j hj hN nu hnu
    hA hB xi hhA hhB hA1 hB1 ja jb ha hb
  dsimp only at hsc
  rcases hsc with ⟨hlog,hZpos,hHpos,hY4,hYstrong,hYmax,hZ,hcap,hNcap,hHband,hArcCap,hks⟩
  have hkfields := hks k hk
  have hGroups := source_B578_actual_group_counts_Cfour434 6 L hLe2 hS
  have hMass := hmass.2.2 hS
  have hG := source_native_original_G_identity434 6 L hS hmass.1
  have hSG : sourceNativeOriginalS434 6 L hS ⊆ sourceNativeOriginalG434 6 L := by
    rw [hG]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have hDisj := source_native_original_small_group_disjoint434 6 L hS (by norm_num) hmass.1
  have hPcap := source_B578_actual_P_below_comparison_cap434 6 L Y hL4 Ncap hYstrong hcap
  have hQcap := source_native_original_r6_Qslot_below_actual_Ncap434
    (sourceOriginalLiteralDepth 6 L) L hL1 b Y Ncap hYstrong hcap
  have hQfields := hQ.2 b hbq
  dsimp only at hQfields
  rcases hQfields with ⟨hI,hSlot,hIBand,hLong,hSlotMin⟩
  obtain ⟨hAne,_,hBne,_⟩ := (source_original_two_block_probe_pattern_mem434
    (sourceNativeOriginalBigBlockA434 6 L) (sourceNativeOriginalBigBlockB434 6 L)
    m nu.1 nu.2).mp hnu
  let aA : nu.1 → ℕ := fun z=>aux (Sum.inl z)
  let aB : nu.2 → ℕ := fun z=>aux (Sum.inr z)
  have hFA : (Finset.range (Fintype.card nu.1)).Nonempty := by
    have hc : 0<Fintype.card nu.1 := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hAne
    exact ⟨0,Finset.mem_range.mpr hc⟩
  have hFB : (Finset.range (Fintype.card nu.2)).Nonempty := by
    have hc : 0<Fintype.card nu.2 := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hBne
    exact ⟨0,Finset.mem_range.mpr hc⟩
  have hPrA : ∀i : Fin (Fintype.card nu.1),
      sourceOriginalProbeIndexedPrime434 aA i ∈ sourceNativeOriginalTb434 6 L
        ((Fintype.equivFin nu.1).symm i).val.1 ∧
      (sourceOriginalProbeIndexedPrime434 aA i).Prime ∧
      Real.exp (L^(3/10:ℝ)) ≤ (sourceOriginalProbeIndexedPrime434 aA i:ℝ) := by
    intro i
    have hp : aA ((Fintype.equivFin nu.1).symm i) ∈ sourceNativeOriginalTb434 6 L
        ((Fintype.equivFin nu.1).symm i).val.1 :=
      (Fintype.mem_piFinset.mp hAux) (Sum.inl ((Fintype.equivFin nu.1).symm i))
    have hr := source_native_original_Tb_prime_range434 6 L _ _ hp
    simpa only [sourceOriginalProbeIndexedPrime434,dite_eq_left i.isLt] using ⟨hp,hr.1,hr.2.1⟩
  have hPrB : ∀i : Fin (Fintype.card nu.2),
      sourceOriginalProbeIndexedPrime434 aB i ∈ sourceNativeOriginalTb434 6 L
        ((Fintype.equivFin nu.2).symm i).val.1 ∧
      (sourceOriginalProbeIndexedPrime434 aB i).Prime ∧
      Real.exp (L^(3/10:ℝ)) ≤ (sourceOriginalProbeIndexedPrime434 aB i:ℝ) := by
    intro i
    have hp : aB ((Fintype.equivFin nu.2).symm i) ∈ sourceNativeOriginalTb434 6 L
        ((Fintype.equivFin nu.2).symm i).val.1 :=
      (Fintype.mem_piFinset.mp hAux) (Sum.inr ((Fintype.equivFin nu.2).symm i))
    have hr := source_native_original_Tb_prime_range434 6 L _ _ hp
    simpa only [sourceOriginalProbeIndexedPrime434,dite_eq_left i.isLt] using ⟨hp,hr.1,hr.2.1⟩
  have hCellA : Real.log (((∏i ∈ Finset.range (Fintype.card nu.1),
      sourceOriginalProbeIndexedPrime434 aA i):ℕ):ℝ) ≤
      Real.log (Real.exp ((ja:ℝ)*hA))+1 := by
    rw [source_original_probe_indexed_prime_product434,Real.log_exp]
    change Real.log (sourceOriginalProbeDA434 m nu aux:ℝ) ≤ (ja:ℝ)*hA+1
    have hu := hAuxA.2
    linarith
  have hCellB : Real.log (((∏i ∈ Finset.range (Fintype.card nu.2),
      sourceOriginalProbeIndexedPrime434 aB i):ℕ):ℝ) ≤
      Real.log (Real.exp ((jb:ℝ)*hB))+1 := by
    rw [source_original_probe_indexed_prime_product434,Real.log_exp]
    change Real.log (sourceOriginalProbeDB434 m nu aux:ℝ) ≤ (jb:ℝ)*hB+1
    have hu := hAuxB.2
    linarith
  have hMask := source_B578_literal_D36_upper_alpha_fields434 a eta deltaC L (hBins.2 a ha0)
  have hAlpha : (∀n ∈ Finset.Icc lo hi,‖sourceB578OriginalD36UpperAlpha434 a eta deltaC L n‖ ≤ L^cfg.ea) ∧
      (∀n,sourceAlphaDyadicCut (sourceB578OriginalD36UpperAlpha434 a eta deltaC L) lo hi n≠0 →
        SourceRoughAbove n (Real.exp (Real.sqrt L))) := by
    constructor
    · intro n hn
      change ‖sourceB578OriginalD36UpperAlpha434 a eta deltaC L n‖ ≤ L^0
      simpa only [pow_zero] using hMask.1 n
    · intro n hn
      apply hMask.2 n
      intro hz
      apply hn
      simp [sourceAlphaDyadicCut,hz]
  have hQSkip : ∀v,‖sourceNativeOriginalLiteralResidual434 L b slot delta freq v‖ ≤ 1 :=
    fun v => source_native_original_six_QSkip_negative_frequency_c434
      L hLp b slot delta freq v
  have hqCap : (k.natAbs:ℝ) ≤ L^cfg.cm := by
    calc
      _  ≤  L^(K+92) := hkfields.2.2.2.1
      _  ≤  L^(cm:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hcm
      _ = L^cfg.cm := by simp only [Real.rpow_natCast]; rfl
  have hmod : L^(2*cfg.cm) ≤ Real.exp (Real.sqrt L) := by
    have h := hArcL.2.1
    have hcast : (2*(cm:ℝ))=((2*cm:ℕ):ℝ) := by push_cast; ring
    change L^(2*(cm:ℝ)) ≤ _ at h
    rw [hcast,Real.rpow_natCast] at h
    exact h
  let data : SourceComparisonData434
      (sourceNativeOriginalTsType434 6 L hS) (sourceNativeOriginalBigType434 6 L)
      cfg (Real.exp L) L Y Hp := {
    Z := Z
    hY := hY4
    hYmax := hYmax
    hH := hHpos
    hYstrong := hYstrong
    hZ := hZ
    hYIdent := rfl
    hSmallGroups := hGroups.1
    hBigGroups := hGroups.2
    lo := lo
    hi := hi
    Ncap := Ncap
    alpha := sourceB578OriginalD36UpperAlpha434 a eta deltaC L
    hNcap := hNcap
    hCap := hcap
    hAlpha := hAlpha.1
    G := sourceNativeOriginalG434 6 L
    Ptw := sourceNativeOriginalG434 6 L
    S := sourceNativeOriginalS434 6 L hS
    primeSlot := sourceOriginalQActualBands 6 (sourceOriginalLiteralDepth 6 L) L b
    Ts := sourceNativeOriginalTs434 6 L hS
    Tb := sourceNativeOriginalTb434 6 L
    Vs := sourceNativeOriginalVs434 6 L hS
    Vsmall := sourceNativeOriginalVsmall434 6 L hS
    Vbig := sourceNativeOriginalVbig434 6 L
    ts := fun _=>1
    tb := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
    coef := sourceB578ActualPairCoef434 J 1 m hmJ nu Qcomp hA hB xi
      (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux sourceSide target
    k := 0
    qBase := k.natAbs
    c := sourceNativeOriginalLiteralResidual434 L b slot delta freq
    chi0 := chi
    hBase := hkfields.2.2.1
    hBaseCap := hqCap
    hk := by change 0+1 ≤ 1+mmax; omega
    hVs := hMass.1.1
    hts := fun _=>by change 1 ≤ 1+mmax; omega
    htb := fun g=> (source_original_probe_free_mark_cap434 J 1 m hmJ nu g).trans (by change 1+m ≤ 1+mmax; omega)
    hVsmall := fun i=>(hMass.2.1 i).1
    hVbig := fun g=>(hMass.2.2 g).1
    hcoef := fun u=>source_B578_actual_pair_coef_norm434 J 1 m hmJ nu Qcomp hA hB xi
      (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux sourceSide target u hhA hhB hxi
    C := 1
    hC := by norm_num
    hCBudget := by change (1:ℝ) ≤ L^0; simp
    hcBound := hQSkip
    sigma0 := sigma0
    sigma1 := 0
    hSigma0 := hsigma0
    hSigma1 := hsigma1
    hModScale := hmod
    hSG := hSG
    hSPrime := fun p hp=>(source_native_original_S_prime_range434 6 L hS p hp).1
    hSN := fun p hp=>hPcap p (hSG hp)
    hPN := hQcap
    hRough := hAlpha.2
    hGroup := fun p hp=>(source_native_original_G_bound434 6 L hL1 p hp).2
    hLong := hLong
    I := Set.Icc (Real.exp (cfg.τ*L)) (Real.exp (cfg.η*L))
    hI := hI
    hSmall := fun p hp=>(source_native_original_S_prime_range434 6 L hS p hp).2
    hSlot := hSlot
    hIBand := hIBand
    F1 := Finset.range (Fintype.card nu.1)
    F2 := Finset.range (Fintype.card nu.2)
    p1 := sourceOriginalProbeIndexedPrime434 aA
    p2 := sourceOriginalProbeIndexedPrime434 aB
    U1 := Real.exp ((ja:ℝ)*hA)
    U2 := Real.exp ((jb:ℝ)*hB)
    hF1 := hFA
    hF2 := hFB
    hp1 := fun i hi=>(hPrA ⟨i,Finset.mem_range.mp hi⟩).2.1.one_le
    hp2 := fun i hi=>(hPrB ⟨i,Finset.mem_range.mp hi⟩).2.1.one_le
    hmin1 := fun i hi=>(hPrA ⟨i,Finset.mem_range.mp hi⟩).2.2
    hmin2 := fun i hi=>(hPrB ⟨i,Finset.mem_range.mp hi⟩).2.2
    hU1 := Real.exp_pos _
    hU2 := Real.exp_pos _
    hcell1 := hCellA
    hcell2 := hCellB
    hHIdent := rfl
    psi1 := psi
    hSmooth := hSmooth
    hSupport := hSupport
    v1 := v1
    hv1 := hv1
    hBudget := hBudget
    hG := hG
    hParity := Finset.Subset.refl _
    hTsPrime := fun i p hp=>(source_native_original_Ts_prime_range434 6 L hS i p hp).1
    hTbPrime := fun g p hp=>(source_native_original_Tb_prime_range434 6 L g p hp).1
    hOrigW := hArcL.2.2.1
    hOrigSmall := hArcL.2.2.2.1
    hOrigLong := hArcL.2.2.2.2
    hSlotMin := hSlotMin
    hHband := hHband
    hArcCap := hArcCap
    hDisjS := fun i p hp hpi=>Finset.disjoint_left.mp (hDisj.1 i) hp hpi
    hDisjB := fun g p hp hpg=>Finset.disjoint_left.mp (hDisj.2.1 g) hp hpg }
  refine ⟨data,?_⟩
  dsimp only [data]
  repeat' constructor
  intro n
  exact source_B578_actual_full_marked_endpoint_eq_native434 L hS J m hmJ nu Qcomp hA hB xi
    aux sourceSide target b slot delta freq lo hi a eta deltaC k chi sigma0 0
    (fun x=>psi ((x:ℝ)/Y)*sourcePhase x v1) n
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualRootGroupGates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 14000

/-- Only tmax depends on mmax in the actual native fixed record. Thus the
root may choose m from cfg0 BEFORE the actual comparison threshold is taken. -/
theorem source_B585_actual_fixed_tmax_override434
    (jQ m cm nout nin : ℕ) (K Carc Cchi : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCchi : (cm:ℝ) ≤ Cchi) (hCchiPos : 0<Cchi) :
    sourceB578NativeEndpointFixed434 jQ m cm nout nin K Carc Cchi hCarc hCchi hCchiPos =
    sourceOriginalGlobalRootTmaxFixed434
      (sourceB578NativeEndpointFixed434 jQ 0 cm nout nin K Carc Cchi hCarc hCchi hCchiPos) (1+m) := by
  rfl

/-- Literal native q0=1/2 and rho=9/10 satisfy the actual quarter-power root gate. -/
theorem source_B585_half_quarter_lt_rho434 : (1/2:ℝ)^(1/4:ℝ) < (9/10:ℝ) := by
  have hp : ((1/2:ℝ)^(1/4:ℝ))^4 = (1/2:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  by_contra hn
  have hge : (9/10:ℝ) ≤ (1/2:ℝ)^(1/4:ℝ) := le_of_not_gt hn
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 9/10) hge 4
  rw [hp] at hh
  norm_num at hh

/-- Exact original moving prime sets and their UNRENORMALIZED reciprocal
masses. These fields are already supplied by every B578 actual record. -/
def SourceB585ActualGroupFields434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    {cfg : SourceComparisonFixed434} {x Y Hp : ℝ}
    (data : SourceComparisonData434 (sourceNativeOriginalTsType434 6 L hS)
      (sourceNativeOriginalBigType434 6 L) cfg x L Y Hp) : Prop :=
  data.S=sourceNativeOriginalS434 6 L hS ∧
  data.Ts=sourceNativeOriginalTs434 6 L hS ∧
  data.Tb=sourceNativeOriginalTb434 6 L ∧
  data.Vs=sourceNativeOriginalVs434 6 L hS ∧
  data.Vsmall=sourceNativeOriginalVsmall434 6 L hS ∧
  data.Vbig=sourceNativeOriginalVbig434 6 L

/-- All geometric gates required by TMAX, with fixed literal native constants. -/
def SourceB585ActualRootGroupGates434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    {cfg : SourceComparisonFixed434} {x Y Hp : ℝ}
    (data : SourceComparisonData434 (sourceNativeOriginalTsType434 6 L hS)
      (sourceNativeOriginalBigType434 6 L) cfg x L Y Hp) : Prop :=
  SourceOriginalSource03GroupSeparation434 data ∧
  (∀g : Option (sourceNativeOriginalTsType434 6 L hS),∀p ∈ sourceOriginalActualSmallPrimeSets434 data g,
    (p:ℝ) ≤ Real.exp (L^(1/5:ℝ))) ∧
  (∀g,data.Vbig g ≤ 4) ∧
  (1/(40*Real.log 2))*Real.log L ≤ (Fintype.card (Option (sourceNativeOriginalTsType434 6 L hS)):ℝ) ∧
  (∀g,data.Tb g=sourceOriginalActualPrimeBand434
    (sourceNativeOriginalBigLo434 6 L g) (sourceNativeOriginalBigHi434 6 L g)) ∧
  (∀g,sourceNativeOriginalBigLo434 6 L g ≤ sourceNativeOriginalBigHi434 6 L g) ∧
  (∀g,(sourceNativeOriginalBigHi434 6 L g:ℝ) ≤ Real.exp (L^(2/5:ℝ))) ∧
  (∀g,Real.exp (L^(3/10:ℝ)) ≤ ((sourceNativeOriginalBigLo434 6 L g+1:ℕ):ℝ)) ∧
  (∀g,∀p ∈ data.Tb g,Real.exp (L^(3/10:ℝ)) ≤ (p:ℝ)) ∧
  (∀g,data.Vbig g=∑p ∈ data.Tb g,1/(p:ℝ)) ∧
  Disjoint (sourceNativeOriginalBigBlockA434 6 L) (sourceNativeOriginalBigBlockB434 6 L) ∧
  (1/(120*Real.log 2))*Real.log L ≤ ((sourceNativeOriginalBigBlockA434 6 L).card:ℝ) ∧
  (1/(120*Real.log 2))*Real.log L ≤ ((sourceNativeOriginalBigBlockB434 6 L).card:ℝ)

/-- Every root geometry premise is PROVED for the full original moving R6
family, uniformly before any comparison precision, m or actual endpoint data.
There is no cofinal scale subsequence or equal-cardinality replacement. -/
theorem eventually_source_B585_actual_root_group_gates434 :
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 6 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
        (cfg : SourceComparisonFixed434) (x Y Hp : ℝ)
        (data : SourceComparisonData434 (sourceNativeOriginalTsType434 6 L hS)
          (sourceNativeOriginalBigType434 6 L) cfg x L Y Hp),
        SourceB585ActualGroupFields434 L hS data → SourceB585ActualRootGroupGates434 L hS data := by
  filter_upwards [eventually_source_native_original_group_masses434 6 (by norm_num),
    eventually_source_native_original_small_counts434 6 (by norm_num),
    eventually_source_native_original_big_partition434 6 (by norm_num)] with L hmass hsmall hblocks
  refine ⟨hmass.2.1,?_⟩
  intro hS cfg x Y Hp data hfields
  rcases hfields with ⟨hSdata,hTs,hTb,hVs,hVsmall,hVbig⟩
  have hd := source_native_original_small_group_disjoint434 6 L hS (by norm_num) hmass.1
  have hb := source_native_original_BIG_root_band_fields434 6 L (le_of_lt hmass.1)
  have hmassB := (hmass.2.2 hS).2.2
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hblocks.2.1,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro i j p hi hj
      by_contra hne
      exact Finset.disjoint_left.mp (hd.2.2.1 hne)
        (by simpa only [hTs] using hi) (by simpa only [hTs] using hj)
    · intro i j p hi hj
      by_contra hne
      exact Finset.disjoint_left.mp (hd.2.2.2.1 hne)
        (by simpa only [hTb] using hi) (by simpa only [hTb] using hj)
    · intro i j p hi hj
      exact Finset.disjoint_left.mp (hd.2.2.2.2 i j)
        (by simpa only [hTs] using hi) (by simpa only [hTb] using hj)
  · intro g p hp
    cases g with
    | none =>
      change p ∈ data.S at hp
      rw [hSdata] at hp
      exact (source_native_original_S_prime_range434 6 L hS p hp).2.2
    | some i =>
      change p ∈ data.Ts i at hp
      rw [hTs] at hp
      exact (source_native_original_Ts_prime_range434 6 L hS i p hp).2.2
  · intro g
    rw [hVbig]
    exact (hmassB g).2.1
  · simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using (hsmall.2.2 hS).1
  · intro g
    rw [hTb]
    exact (hb g).1
  · exact fun g=>(hb g).2.1
  · exact fun g=>(hb g).2.2.1
  · exact fun g=>(hb g).2.2.2
  · intro g p hp
    rw [hTb] at hp
    exact (source_native_original_Tb_prime_range434 6 L g p hp).2.1
  · intro g
    rw [hVbig,hTb]
    simp only [sourceNativeOriginalVbig434,one_div]
  · simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using hblocks.2.2.1
  · simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using hblocks.2.2.2
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ParityRootAuxGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Auxiliary endpoint geometry only. It is used to instantiate an
endpoint-independent C-root; the resulting kernel keeps all ACTUAL r20
prime groups, masses, RAW and comparison patterns. -/
def b636AuxIndex434 (L : ℝ) : ℕ := Nat.ceil (Real.exp (L^(3/10:ℝ)))
def b636AuxH434 (L : ℝ) : ℝ := (b636AuxIndex434 L:ℝ)^2
def b636AuxY434 (L : ℝ) : ℝ := Real.exp L*b636AuxH434 L
def b636AuxNcap434 (L : ℝ) : ℕ := Nat.ceil (64*b636AuxY434 L)

/-- All physical scale premises of the auxiliary source record are
proved from a single explicit threshold. No physical root norm is
inferred from the zero endpoint used later in the auxiliary record. -/
theorem b636_aux_geometry434 (L : ℝ) (hL : 1024 ≤ L) :
    1 ≤ b636AuxIndex434 L ∧
    Real.exp (L^(3/10:ℝ)) ≤ (b636AuxIndex434 L:ℝ) ∧
    0 < b636AuxH434 L ∧ 2 ≤ b636AuxH434 L ∧
    4 ≤ b636AuxY434 L ∧
    b636AuxY434 L ≤ Real.exp (3*L/2) ∧
    Real.exp (3*L/4) ≤ b636AuxY434 L ∧
    64*b636AuxY434 L ≤ (b636AuxNcap434 L:ℝ) ∧
    (b636AuxNcap434 L:ℝ) ≤ (Real.exp L)^2 ∧
    b636AuxH434 L ≤ b636AuxY434 L/(8*64) ∧
    Real.exp L ≤ b636AuxY434 L := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hp0 : 0 ≤ L^(3/10:ℝ) := Real.rpow_nonneg hL0 _
  have hp1 : 1 ≤ L^(3/10:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hs := Real.sqrt_nonneg L
  have hs2 := Real.sq_sqrt hL0
  have hs16 : 16 ≤ Real.sqrt L := by nlinarith
  have hsL : Real.sqrt L ≤ L/16 := by nlinarith
  have hpS : L^(3/10:ℝ) ≤ Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hpL : 2*L^(3/10:ℝ)+2 ≤ L/2 := by linarith
  have hExp1 : 1 ≤ Real.exp (L^(3/10:ℝ)) :=
    Real.one_le_exp_iff.mpr hp0
  have hnLo : Real.exp (L^(3/10:ℝ)) ≤ (b636AuxIndex434 L:ℝ) := Nat.le_ceil _
  have hn2 : (2:ℝ) ≤ b636AuxIndex434 L := by
    exact Real.exp_one_gt_two.le.trans
      ((Real.exp_le_exp.mpr hp1).trans hnLo)
  have hn0 : (0:ℝ) ≤ b636AuxIndex434 L := by positivity
  have hnHi : (b636AuxIndex434 L:ℝ) ≤ Real.exp (L^(3/10:ℝ)+1) := by
    have hceil : (b636AuxIndex434 L:ℝ) ≤ Real.exp (L^(3/10:ℝ))+1 :=
      (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
    rw [Real.exp_add]
    have he2 : (2:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    nlinarith
  have hH4 : 4 ≤ b636AuxH434 L := by dsimp [b636AuxH434]; nlinarith
  have hHpos : 0 < b636AuxH434 L := by linarith
  have hHhi : b636AuxH434 L ≤ Real.exp (2*L^(3/10:ℝ)+2) := by
    have hh := pow_le_pow_left₀ hn0 hnHi 2
    have he : (Real.exp (L^(3/10:ℝ)+1))^2 =
        Real.exp (2*L^(3/10:ℝ)+2) := by
      rw [pow_two, ←Real.exp_add]
      congr 1
      ring
    rw [he] at hh
    exact hh
  have hx1 : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL0
  have hx512 : (512:ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hxy : Real.exp L ≤ b636AuxY434 L := by
    dsimp [b636AuxY434]
    nlinarith [Real.exp_pos L]
  have hY4 : 4 ≤ b636AuxY434 L := by
    dsimp [b636AuxY434]
    nlinarith
  have hYhi : b636AuxY434 L ≤ Real.exp (3*L/2) := by
    calc
      b636AuxY434 L ≤ Real.exp L*Real.exp (2*L^(3/10:ℝ)+2) :=
        mul_le_mul_of_nonneg_left hHhi (Real.exp_pos L).le
      _ = Real.exp (L+(2*L^(3/10:ℝ)+2)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (3*L/2) := Real.exp_le_exp.mpr (by linarith)
  have hNlo : 64*b636AuxY434 L ≤ (b636AuxNcap434 L:ℝ) := Nat.le_ceil _
  have hNhi : (b636AuxNcap434 L:ℝ) ≤ (Real.exp L)^2 := by
    have hN : (b636AuxNcap434 L:ℝ) ≤ 64*b636AuxY434 L+1 :=
      (Nat.ceil_lt_add_one (by linarith : 0 ≤ 64*b636AuxY434 L)).le
    have he1 : 1 ≤ Real.exp (3*L/2) := Real.one_le_exp_iff.mpr (by linarith)
    have he65 : (65:ℝ) ≤ Real.exp (L/2) := by
      linarith [Real.add_one_le_exp (L/2)]
    calc
      (b636AuxNcap434 L:ℝ) ≤ 65*Real.exp (3*L/2) := by linarith
      _ ≤ Real.exp (L/2)*Real.exp (3*L/2) :=
        mul_le_mul_of_nonneg_right he65 (Real.exp_pos _).le
      _ = (Real.exp L)^2 := by
        rw [←Real.exp_add, pow_two, ←Real.exp_add]
        congr 1
        ring
  refine ⟨by exact_mod_cast (show (1:ℝ) ≤ b636AuxIndex434 L by linarith),
    hnLo,hHpos,by linarith,hY4,hYhi,?_,hNlo,hNhi,?_,hxy⟩
  · exact (Real.exp_le_exp.mpr (by linarith : 3*L/4 ≤ L)).trans hxy
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<8*64)).mpr
    dsimp [b636AuxY434]
    nlinarith
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ParityActualRootData -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- An auxiliary configuration for the endpoint-independent kernel. Its
P exponents, mass floor and q0 are exactly Parity's; unused prime-slot/cutoff
fields only make a valid source record, and never enter the C-root. -/
def b636ParityRootFixed434 : SourceComparisonFixed434 :=
  { sourceNativeOriginalR6Fixed434 0 0 0 0 0 0 1 0
      (by norm_num) (by norm_num) (by norm_num) (fun _ => 0) (by simp) with
    C0 := 3+(Real.log 2)⁻¹
    hC0 := by have := Real.log_pos (by norm_num : (1:ℝ)<2); positivity }

/-- Actual r20 prime sets and unrenormalized masses in a valid auxiliary
source record. Alpha/coefficient/cutoff zeroing only supplies unused fields.
No root norm is bounded by this construction. -/
def b636ActualP20AuxData434
    (L : ℝ) (hL : 1024 ≤ L) (hexp : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (hVs : Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVs434 20 L hS)
    (hVsmall : ∀ i, Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVsmall434 20 L hS i)
    (hVbig : ∀ g, Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVbig434 20 L g) :
    SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hS) (sourceNativeOriginalBigType434 20 L)
      b636ParityRootFixed434 (Real.exp L) L (b636AuxY434 L) (b636AuxH434 L) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLg : 1 < L := by linarith
  have hGeom := b636_aux_geometry434 L hL
  have hn1 := hGeom.1
  have hnLo := hGeom.2.1
  have hH := hGeom.2.2.1
  have hHtwo := hGeom.2.2.2.1
  have hY := hGeom.2.2.2.2.1
  have hYmax := hGeom.2.2.2.2.2.1
  have hYstrong := hGeom.2.2.2.2.2.2.1
  have hCap := hGeom.2.2.2.2.2.2.2.1
  have hNcap := hGeom.2.2.2.2.2.2.2.2.1
  have hArcCap := hGeom.2.2.2.2.2.2.2.2.2.1
  have hXY := hGeom.2.2.2.2.2.2.2.2.2.2
  have hnPos : (0:ℝ) < b636AuxIndex434 L := by exact_mod_cast (by omega : 0 < b636AuxIndex434 L)
  have hc := source_native_original_group_upper_counts434 20 L hS (by norm_num) hexp
  have hd := source_native_original_small_group_disjoint434 20 L hS (by norm_num) hLg
  have hG := source_native_original_G_identity434 20 L hS hLg
  have hSN : ∀ p ∈ sourceNativeOriginalS434 20 L hS, p ≤ b636AuxNcap434 L := by
    intro p hp
    have hb := (source_native_original_S_prime_range434 20 L hS p hp).2.2
    have he : L^(1/5:ℝ) ≤ L := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1/5:ℝ) ≤ 1)
    have hpy : (p:ℝ) ≤ b636AuxY434 L :=
      hb.trans ((Real.exp_le_exp.mpr he).trans hXY)
    exact_mod_cast (show (p:ℝ) ≤ (b636AuxNcap434 L:ℝ) by linarith)
  refine {
    Z := Real.exp L
    hY := hY
    hYmax := hYmax
    hH := hH
    hYstrong := hYstrong
    hZ := by simp [b636ParityRootFixed434,sourceNativeOriginalR6Fixed434]
    hYIdent := rfl
    hSmallGroups := hc.1
    hBigGroups := hc.2
    lo := 0
    hi := 0
    Ncap := b636AuxNcap434 L
    alpha := fun _ => 0
    hNcap := hNcap
    hCap := hCap
    hAlpha := by intro n hn; change ‖(0:ℂ)‖ ≤ L^0; simp
    G := sourceNativeOriginalG434 20 L
    Ptw := sourceNativeOriginalG434 20 L
    S := sourceNativeOriginalS434 20 L hS
    primeSlot := ∅
    Ts := sourceNativeOriginalTs434 20 L hS
    Tb := sourceNativeOriginalTb434 20 L
    Vs := sourceNativeOriginalVs434 20 L hS
    Vsmall := sourceNativeOriginalVsmall434 20 L hS
    Vbig := sourceNativeOriginalVbig434 20 L
    ts := fun _ => 0
    tb := fun _ => 0
    coef := fun _ => 0
    k := 0
    qBase := 1
    c := fun _ => 0
    chi0 := 1
    hBase := by norm_num
    hBaseCap := by simp [b636ParityRootFixed434,sourceNativeOriginalR6Fixed434]
    hk := by norm_num [b636ParityRootFixed434,sourceNativeOriginalR6Fixed434]
    hVs := hVs
    hts := by intro i; exact Nat.zero_le _
    htb := by intro g; exact Nat.zero_le _
    hVsmall := hVsmall
    hVbig := hVbig
    hcoef := by simp
    C := 0
    hC := le_refl 0
    hCBudget := by change (0:ℝ) ≤ L^0; simp
    hcBound := by simp
    sigma0 := 0
    sigma1 := 0
    hSigma0 := by change |(0:ℝ)| ≤ L^0; simp
    hSigma1 := by change |(0:ℝ)| ≤ L^0; simp
    hModScale := by
      change L^(2*0) ≤ Real.exp (Real.sqrt L)
      simp
    hSG := by
      intro p hp
      rw [hG]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
    hSPrime := fun p hp => (source_native_original_S_prime_range434 20 L hS p hp).1
    hSN := hSN
    hPN := by simp
    hRough := by simp [sourceAlphaDyadicCut]
    hGroup := fun p hp => (source_native_original_G_bound434 20 L hL1 p hp).2
    hLong := by simp
    I := ∅
    hI := by infer_instance
    hSmall := fun p hp => (source_native_original_S_prime_range434 20 L hS p hp).2
    hSlot := by simp
    hIBand := Set.empty_subset _
    F1 := {0}
    F2 := {0}
    p1 := fun _ => b636AuxIndex434 L
    p2 := fun _ => b636AuxIndex434 L
    U1 := (b636AuxIndex434 L:ℝ)
    U2 := (b636AuxIndex434 L:ℝ)
    hF1 := by simp
    hF2 := by simp
    hp1 := fun _ _ => hn1
    hp2 := fun _ _ => hn1
    hmin1 := fun _ _ => hnLo
    hmin2 := fun _ _ => hnLo
    hU1 := hnPos
    hU2 := hnPos
    hcell1 := by simp only [Finset.prod_singleton]; linarith
    hcell2 := by simp only [Finset.prod_singleton]; linarith
    hHIdent := by dsimp [b636AuxH434]; ring
    psi1 := fun _ => 0
    hSmooth := contDiff_const
    hSupport := by simp
    v1 := 0
    hv1 := by change |(0:ℝ)| ≤ L^0; simp
    hBudget := by simp [sourceLogDerivativeBudget,b636ParityRootFixed434,sourceNativeOriginalR6Fixed434]
    hG := hG
    hParity := Finset.Subset.refl _
    hTsPrime := fun g p hp => (source_native_original_Ts_prime_range434 20 L hS g p hp).1
    hTbPrime := fun g p hp => (source_native_original_Tb_prime_range434 20 L g p hp).1
    hOrigW := by
      change L^(0:ℝ) ≤ Real.exp (Real.sqrt L)
      simp
    hOrigSmall := by
      change L^(0:ℝ) < Real.exp (L^(1/10:ℝ))
      simpa using Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL0 (1/10:ℝ))
    hOrigLong := by
      change L^(0:ℝ) < Real.exp (b636ParityRootFixed434.τ*L)
      simpa using Real.one_lt_exp_iff.mpr (mul_pos b636ParityRootFixed434.hτ hL0)
    hSlotMin := by simp
    hHband := by
      change 2 ≤ b636AuxH434 L/L^(0:ℝ)
      simpa using hHtwo
    hArcCap := by
      change b636AuxH434 L/L^(0:ℝ) ≤ b636AuxY434 L/(8*64)
      simpa using hArcCap
    hDisjS := fun g p hp hpg => (Finset.disjoint_left.mp (hd.1 g)) hp hpg
    hDisjB := fun g p hp hpg => (Finset.disjoint_left.mp (hd.2.1 g)) hp hpg
  }

/-- The auxiliary construction retains every actual r20 prime group and
exact original reciprocal mass. The root operator cannot see the zeroed
endpoint fields. -/
theorem b636_actual_p20_aux_group_fields434
    (L : ℝ) (hL : 1024 ≤ L) (hexp : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (hVs : Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVs434 20 L hS)
    (hVsmall : ∀ i, Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVsmall434 20 L hS i)
    (hVbig : ∀ g, Real.log (6/5:ℝ)/2 ≤ sourceNativeOriginalVbig434 20 L g) :
    let d := b636ActualP20AuxData434 L hL hexp hS hVs hVsmall hVbig
    d.S=sourceNativeOriginalS434 20 L hS ∧
    d.Ts=sourceNativeOriginalTs434 20 L hS ∧ d.Tb=sourceNativeOriginalTb434 20 L ∧
    d.Vs=sourceNativeOriginalVs434 20 L hS ∧
    d.Vsmall=sourceNativeOriginalVsmall434 20 L hS ∧
    d.Vbig=sourceNativeOriginalVbig434 20 L := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ParityActualRootGates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 14000

/-- The actual source P scale at r=20 is EXACTLY the Parity sigma=1/44
scale. All following groups use the existing full prime bands unchanged. -/
theorem b636_parity_literal_P_scale434 (L : ℝ) (j : ℕ) :
    sourceOriginalPGroupScale 20 L j = L/((44:ℝ)*(2:ℝ)^j) := by
  dsimp [sourceOriginalPGroupScale]
  ring

/-- Exact original moving prime sets and their UNRENORMALIZED reciprocal
masses. These fields are already supplied by every B578 actual record. -/
def SourceB636ParityActualGroupFields434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {cfg : SourceComparisonFixed434} {x Y Hp : ℝ}
    (data : SourceComparisonData434 (sourceNativeOriginalTsType434 20 L hS)
      (sourceNativeOriginalBigType434 20 L) cfg x L Y Hp) : Prop :=
  data.S=sourceNativeOriginalS434 20 L hS ∧
  data.Ts=sourceNativeOriginalTs434 20 L hS ∧
  data.Tb=sourceNativeOriginalTb434 20 L ∧
  data.Vs=sourceNativeOriginalVs434 20 L hS ∧
  data.Vsmall=sourceNativeOriginalVsmall434 20 L hS ∧
  data.Vbig=sourceNativeOriginalVbig434 20 L

/-- All geometric gates required by TMAX, with fixed literal native constants. -/
def SourceB636ParityActualRootGroupGates434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    {cfg : SourceComparisonFixed434} {x Y Hp : ℝ}
    (data : SourceComparisonData434 (sourceNativeOriginalTsType434 20 L hS)
      (sourceNativeOriginalBigType434 20 L) cfg x L Y Hp) : Prop :=
  SourceOriginalSource03GroupSeparation434 data ∧
  (∀g : Option (sourceNativeOriginalTsType434 20 L hS),∀p ∈ sourceOriginalActualSmallPrimeSets434 data g,
    (p:ℝ) ≤ Real.exp (L^(1/5:ℝ))) ∧
  (∀g,data.Vbig g ≤ 4) ∧
  (1/(40*Real.log 2))*Real.log L ≤ (Fintype.card (Option (sourceNativeOriginalTsType434 20 L hS)):ℝ) ∧
  (∀g,data.Tb g=sourceOriginalActualPrimeBand434
    (sourceNativeOriginalBigLo434 20 L g) (sourceNativeOriginalBigHi434 20 L g)) ∧
  (∀g,sourceNativeOriginalBigLo434 20 L g ≤ sourceNativeOriginalBigHi434 20 L g) ∧
  (∀g,(sourceNativeOriginalBigHi434 20 L g:ℝ) ≤ Real.exp (L^(2/5:ℝ))) ∧
  (∀g,Real.exp (L^(3/10:ℝ)) ≤ ((sourceNativeOriginalBigLo434 20 L g+1:ℕ):ℝ)) ∧
  (∀g,∀p ∈ data.Tb g,Real.exp (L^(3/10:ℝ)) ≤ (p:ℝ)) ∧
  (∀g,data.Vbig g=∑p ∈ data.Tb g,1/(p:ℝ)) ∧
  Disjoint (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) ∧
  (1/(120*Real.log 2))*Real.log L ≤ ((sourceNativeOriginalBigBlockA434 20 L).card:ℝ) ∧
  (1/(120*Real.log 2))*Real.log L ≤ ((sourceNativeOriginalBigBlockB434 20 L).card:ℝ)

/-- Every root geometry premise is PROVED for the full original moving Parity r20
family, uniformly before any comparison precision, m or actual endpoint data.
There is no cofinal scale subsequence or equal-cardinality replacement. -/
theorem eventually_source_B636_parity_root_group_gates434 :
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (cfg : SourceComparisonFixed434) (x Y Hp : ℝ)
        (data : SourceComparisonData434 (sourceNativeOriginalTsType434 20 L hS)
          (sourceNativeOriginalBigType434 20 L) cfg x L Y Hp),
        SourceB636ParityActualGroupFields434 L hS data → SourceB636ParityActualRootGroupGates434 L hS data := by
  filter_upwards [eventually_source_native_original_group_masses434 20 (by norm_num),
    eventually_source_native_original_small_counts434 20 (by norm_num),
    eventually_source_native_original_big_partition434 20 (by norm_num)] with L hmass hsmall hblocks
  refine ⟨hmass.2.1,?_⟩
  intro hS cfg x Y Hp data hfields
  rcases hfields with ⟨hSdata,hTs,hTb,hVs,hVsmall,hVbig⟩
  have hd := source_native_original_small_group_disjoint434 20 L hS (by norm_num) hmass.1
  have hb := source_native_original_BIG_root_band_fields434 20 L (le_of_lt hmass.1)
  have hmassB := (hmass.2.2 hS).2.2
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hblocks.2.1,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro i j p hi hj
      by_contra hne
      exact Finset.disjoint_left.mp (hd.2.2.1 hne)
        (by simpa only [hTs] using hi) (by simpa only [hTs] using hj)
    · intro i j p hi hj
      by_contra hne
      exact Finset.disjoint_left.mp (hd.2.2.2.1 hne)
        (by simpa only [hTb] using hi) (by simpa only [hTb] using hj)
    · intro i j p hi hj
      exact Finset.disjoint_left.mp (hd.2.2.2.2 i j)
        (by simpa only [hTs] using hi) (by simpa only [hTb] using hj)
  · intro g p hp
    cases g with
    | none =>
      change p ∈ data.S at hp
      rw [hSdata] at hp
      exact (source_native_original_S_prime_range434 20 L hS p hp).2.2
    | some i =>
      change p ∈ data.Ts i at hp
      rw [hTs] at hp
      exact (source_native_original_Ts_prime_range434 20 L hS i p hp).2.2
  · intro g
    rw [hVbig]
    exact (hmassB g).2.1
  · simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using (hsmall.2.2 hS).1
  · intro g
    rw [hTb]
    exact (hb g).1
  · exact fun g=>(hb g).2.1
  · exact fun g=>(hb g).2.2.1
  · exact fun g=>(hb g).2.2.2
  · intro g p hp
    rw [hTb] at hp
    exact (source_native_original_Tb_prime_range434 20 L g p hp).2.1
  · intro g
    rw [hVbig,hTb]
    simp only [sourceNativeOriginalVbig434,one_div]
  · simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using hblocks.2.2.1
  · simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using hblocks.2.2.2
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityMemorySaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 60000000
set_option maxRecDepth 18000

/-- The literal r20 Parity P-kernel OLD and Memory root budget. Only actual
prime fibres, unrenormalized reciprocal masses, all physical RAW and
comparison patterns, full caps and the original canonical Knu occur.
There is no endpoint alpha, prime-slot, or auxiliary zero coefficient. -/
def B636ActualParityMemoryBounds434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi E zeta theta : ℝ) (shift : ℤ) : Prop := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let cap := fun g => Fintype.card (BP g)
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let T := Nat.ceil (L^2)
  exact
    (‖sourceOriginalOLDProjectedMemoryRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m cap pats (1/2:ℝ) (9/10:ℝ)
      (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
      Knu zeta theta shift (Nat.ceil (L^(0.52:ℝ))) T‖ ≤ L^(-E*(N:ℝ))) ∧
    (‖memorySourceRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats cap (1/2:ℝ) (9/10:ℝ)
      (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
      Knu zeta theta shift (Nat.ceil (L^(0.52:ℝ)))‖ ≤ L^(-E*(N:ℝ)))

/-- Unconditional r20 actual P-kernel saving, with physical shift2k and
all real moving groups. The source tuple m,D,HH,Cq,Cxi,J and eventual L
threshold precede k, all Fourier phases and all endpoint coefficients.
This is an application of the already proved general full C-root, not
an estimate of a zero endpoint and not the final physical/CRT pairing. -/
theorem b636_eventually_actual_parity_memory_saving434
    (E Cfreq Ck : ℝ) (hE : 0 < E) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h ≤ 1 ∧ 0<xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (zeta theta : ℝ), |zeta| ≤ L^Cfreq →
      ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
        B636ActualParityMemoryBounds434 L hS J m hmJ Q h xi E zeta theta (2*k) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hRoot⟩ :=
    eventually_source_original_global_root_EXPECTED434 b636ParityRootFixed434
      (3/10) (2/5) E Cfreq (1/(120*Real.log 2)) (9/10) 4
      (1/(40*Real.log 2)) (Ck+1)
      (by norm_num) (by norm_num) hE (by positivity) (by norm_num)
      source_B585_half_quarter_lt_rho434 (by norm_num) (by positivity)
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hRoot,eventually_source_B636_parity_root_group_gates434,
    eventually_source_native_original_group_masses434 20 (by norm_num),
    eventually_ge_atTop (1024:ℝ), eventually_ge_atTop (Real.exp 1)]
    with L hRoot hGroups hMass hL hexp
  dsimp only at hRoot ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hRoot⟩ := hRoot
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hGroups.1,?_⟩
  intro hS zeta theta hzeta k hk hkCap
  let data := b636ActualP20AuxData434 L hL hexp hS
    (hMass.2.2 hS).1.1
    (fun i => ((hMass.2.2 hS).2.1 i).1)
    (fun g => ((hMass.2.2 hS).2.2 g).1)
  have hfields : SourceB636ParityActualGroupFields434 L hS data :=
    b636_actual_p20_aux_group_fields434 L hL hexp hS
      (hMass.2.2 hS).1.1
      (fun i => ((hMass.2.2 hS).2.1 i).1)
      (fun g => ((hMass.2.2 hS).2.2 g).1)
  have hg := hGroups.2 hS _ _ _ _ data hfields
  obtain ⟨hSep,hSmall,hVmax,hSmallCount,hFull,hLoHi,hUpper,hLoLarge,hTbLower,hMassB,
    hBlocks,hCountA,hCountB⟩ := hg
  let (g : sourceNativeOriginalBigType434 20 L)
      (p : {p : ℕ // p ∈ data.Tb g}) : NeZero p.val :=
    ⟨(data.hTbPrime g p.val p.property).ne_zero⟩
  have hL0 : 0 < L := by linarith
  have hShift : ((2*k).natAbs:ℝ) ≤ L^(Ck+1) := by
    calc
      ((2*k).natAbs:ℝ) = 2*(k.natAbs:ℝ) := by simp [Int.natAbs_mul]
      _ ≤ 2*L^Ck := mul_le_mul_of_nonneg_left hkCap (by norm_num)
      _ ≤ L*L^Ck := mul_le_mul_of_nonneg_right (by linarith)
        (Real.rpow_nonneg hL0.le _)
      _ = L^(Ck+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
  have hb := hRoot (Real.exp L) (b636AuxY434 L) (b636AuxH434 L) data hSep
    hSmall hVmax hSmallCount
    (sourceNativeOriginalBigLo434 20 L) (sourceNativeOriginalBigHi434 20 L)
    hFull hLoHi hUpper hLoLarge hTbLower hMassB
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    hBlocks hCountA hCountB zeta theta hzeta (2*k) (mul_ne_zero (by norm_num) hk) hShift
  have hsets : sourceOriginalActualSmallPrimeSets434 data =
      SourceNativeMemorySmallSet434 20 L hS := by
    funext g
    cases g <;> rfl
  have hsm : sourceOriginalActualSmallMass434 data =
      SourceNativeMemorySmallMass434 20 L hS := by
    funext g
    cases g <;> rfl
  let SF := {S : Option (sourceNativeOriginalTsType434 20 L hS) → Finset ℕ //
    ∀ g, ∀ p ∈ S g, p ≠ 0}
  let src : SF := ⟨sourceOriginalActualSmallPrimeSets434 data,
    fun g p hp => ((source_original_ACTUAL_SMALL_source_bounds434 data).1 g p hp).ne_zero⟩
  let dst : SF := ⟨SourceNativeMemorySmallSet434 20 L hS, by
    intro g p hp
    cases g with
    | none => exact (source_native_original_S_prime_range434 20 L hS p hp).1.ne_zero
    | some i => exact (source_native_original_Ts_prime_range434 20 L hS i p hp).1.ne_zero⟩
  let T : SF → (Option (sourceNativeOriginalTsType434 20 L hS) → ℝ) → Prop :=
    fun sf vs => by
      let SP := fun g : Option (sourceNativeOriginalTsType434 20 L hS) =>
        {p : ℕ // p ∈ sf.val g}
      let (g : Option (sourceNativeOriginalTsType434 20 L hS)) (p : SP g) : NeZero p.val :=
        ⟨sf.property g p.val p.property⟩
      let BP := SourceNativeMemoryBP434 20 L
      let cap := fun g => Fintype.card (BP g)
      let pats := sourceOriginalMemoryRawComparisonPattern434
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
      let Knu := sourceOriginalMemoryRawComparisonK434
        (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
        (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
        J 1 m hmJ (Nat.ceil (4*L^(D+1)))
        (fun _ => Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ))
        (fun _ => Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)) (L^(-(Cxi:ℝ)))
      let N := 2*Nat.ceil (L^(0.52:ℝ))
      exact
        (‖sourceOriginalOLDProjectedMemoryRoot434 SP (fun _ p => p.val) BP (fun _ p => p.val)
          J 1 m cap pats (1/2:ℝ) (9/10:ℝ) vs (sourceNativeOriginalVbig434 20 L)
          Knu zeta theta (2*k) (Nat.ceil (L^(0.52:ℝ))) (Nat.ceil (L^2))‖ ≤ L^(-E*(N:ℝ))) ∧
        (‖memorySourceRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
          J 1 m pats cap (1/2:ℝ) (9/10:ℝ) vs (sourceNativeOriginalVbig434 20 L)
          Knu zeta theta (2*k) (Nat.ceil (L^(0.52:ℝ)))‖ ≤ L^(-E*(N:ℝ)))
  have hcarrier : src = dst := Subtype.ext hsets
  change T src (sourceOriginalActualSmallMass434 data) at hb
  change T dst (SourceNativeMemorySmallMass434 20 L hS)
  exact (congrArg₂ T hcarrier hsm).mp hb
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityMemoryIdentity -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 16000

/-- Exact independent-residue versus Memory root equality for the complete
actual r20 RAW and comparison kernel. The parameters and all carriers are
identical to B636, including the full canonical physical marked Knu. -/
def B642ActualParityRootIdentity434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi zeta theta : ℝ) (shift : ℤ) : Prop := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let cap := fun g => Fintype.card (BP g)
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  exact
    memoryIndependentRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats (1/2:ℝ)
      (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
      Knu zeta theta shift (Nat.ceil (L^(0.52:ℝ))) =
    memorySourceRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats cap (1/2:ℝ) (9/10:ℝ)
      (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
      Knu zeta theta shift (Nat.ceil (L^(0.52:ℝ)))

/-- All twenty actual-domain premises are discharged for arbitrary
polynomially bounded nonzero k, with literal shift2k and original R.
The exact independent=Memory identity is already proved in the native
source closure and is applied here without an identity/kernel hypothesis. -/
theorem b642_eventually_actual_parity_memory_identity434 (Ck : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (k : ℤ), k≠0 → (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (J m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi zeta theta : ℝ),
        B642ActualParityRootIdentity434 L hS J m hmJ Q h xi zeta theta (2*k) := by
  let C : ℝ := max 0 Ck
  have hC : 0≤C := le_max_left _ _
  have hrho : Real.sqrt (1/2:ℝ) < (9/10:ℝ)^2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2)
    have hn := Real.sqrt_nonneg (1/2:ℝ)
    nlinarith
  have hfloor := Green64Analytic.ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  filter_upwards [eventually_source_native_original_group_masses434 20 (by norm_num),
    eventually_native_memory_poly_shift434 C hC,
    eventually_native_memory_original_visits434] with L hMass hShift hVisits
  refine ⟨hMass.2.1,?_⟩
  intro hS k hk hkcap J m hmJ Q h xi zeta theta
  have hLp : 0<L := zero_lt_one.trans hMass.1
  have hk' : (2*k:ℤ)≠0 := mul_ne_zero (by norm_num) hk
  have hShift' : ((2*k).natAbs:ℝ) < Real.exp (L^(1/10:ℝ)) := by
    calc
      _ = 2*(k.natAbs:ℝ) := by simp [Int.natAbs_mul]
      _ ≤ 2*L^Ck := mul_le_mul_of_nonneg_left hkcap (by norm_num)
      _ ≤ 2*L^C := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hMass.1.le (le_max_right _ _)) (by norm_num)
      _ ≤ 4*L^C := by nlinarith [Real.rpow_nonneg hLp.le C]
      _ < _ := hShift
  have hm := hMass.2.2 hS
  have hd := source_native_memory_domain_of_numeric_gates434
    20 L (by norm_num) hMass.1 hS (1/2) (9/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrho
    (2*k) hk' hShift' (Nat.ceil (L^(0.52:ℝ))) hVisits.1 hVisits.2
    (hfloor.trans_le hm.1.1)
    (fun i => hfloor.trans_le (hm.2.1 i).1)
    (fun g => hfloor.trans_le (hm.2.2 g).1)
  dsimp only [B642ActualParityRootIdentity434]
  apply memory_original_identity_target_proved
  simpa only [SourceNativeMemoryBP434,Fintype.card_coe] using hd
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualNativeGatedPairing -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 14000

/-- The exact distinguished-S and all other SMALL marked factors. Every
SMALL group still contributes one mark, with its original reciprocal mass. -/
def sourceB578ActualSmallMarkedFactor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty) (n : ℕ) : ℂ :=
  (((1/2:ℝ)^((smallPrimeCount (sourceNativeOriginalS434 6 L hS) n:ℤ)-(1:ℤ))/
      (sourceNativeOriginalVs434 6 L hS)^1:ℝ):ℂ)*
    bigMarkPrefactor (sourceNativeOriginalTs434 6 L hS) (fun _=>1) (1/2:ℝ)
      (sourceNativeOriginalVsmall434 6 L hS) n *
    (((smallPrimeCount (sourceNativeOriginalS434 6 L hS) n).descFactorial 1:ℕ):ℂ)*
    ((∏g,(smallPrimeCount (sourceNativeOriginalTs434 6 L hS g) n).descFactorial 1:ℕ):ℂ)

/-- Original native ordinary core, exact profile/phase and every SMALL mark;
only the BIG canonical free row remains to be attached. -/
def sourceB578ActualNativeCommon434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta deltaC : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigma0 sigma1 : ℝ) (Lambda : ℕ → ℂ) (n : ℕ) : ℂ :=
  Lambda n*primeSlotCoreValue (sourceB578ActualAllGroups434 L hS)
    (sourceNativePrimeCore 6 (sourceOriginalLiteralDepth 6 L) L b slot delta (-freq)
      (Finset.Icc lo hi) (sourceB578OriginalD36UpperAlpha434 a eta deltaC L)
      k.natAbs chi sigma0 sigma1) n * sourceB578ActualSmallMarkedFactor434 L hS n

/-- Exact actual all-group endpoint factorization. In particular no RAW W1
factor is substituted for the original free BIG mark counts. -/
theorem source_B578_actual_native_endpoint_common_factor434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (sourceSide : Bool)
    (target : ∀g,Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g) → ℕ)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta deltaC : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigma0 sigma1 : ℝ) (Lambda : ℕ → ℂ) (n : ℕ) :
    sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Q hA hB xi aux sourceSide target
      b slot delta freq lo hi a eta deltaC k chi sigma0 sigma1 Lambda n =
    sourceB578ActualNativeCommon434 L hS b slot delta freq lo hi a eta deltaC k chi
      sigma0 sigma1 Lambda n *
    actualBigMarkDecoration (sourceNativeOriginalTb434 6 L)
      (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) (1/2:ℝ)
      (sourceNativeOriginalVbig434 6 L)
      (sourceB578ActualPairCoef434 J 1 m hmJ nu Q hA hB xi
        (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux sourceSide target) n := by
  unfold sourceB578ActualNativeRowEndpoint434 sourceB578ActualAllGroups434
  rw [source_original_marked_weight_split434]
  unfold literalSourceWeight
  rw [literal_mark_sum_factor]
  unfold sourceB578ActualNativeCommon434 sourceB578ActualSmallMarkedFactor434
    sourceB578ActualAllGroups434 actualBigMarkDecoration
  ring_nf

/-- The FULL native endpoint pair restores the original marked Knu with
kappa ONCE outside the actual target-list sum. All SMALL weights, BIG
free counts, full alphaD, original residual and original character remain. -/
theorem source_B578_actual_native_full_canonical_pair434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta deltaC : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (sigmaF sigmaG : ℝ) (LambdaF LambdaG : ℕ → ℂ) (w wp : ℕ) :
    star (sourceB578ActualNativeCommon434 L hS b slot delta freq lo hi a eta deltaC k chi
      sigmaF 0 LambdaF w)*
    sourceB578ActualNativeCommon434 L hS b slot delta freq lo hi a eta deltaC k chi
      sigmaG 0 LambdaG wp *
    sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi
      (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux (1/2:ℝ) w wp =
    (sourceB578CanonicalRowScale434 Q xi:ℂ)*
      ∑ target ∈ bigMarkLists (sourceNativeOriginalTb434 6 L)
        (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) wp,
        star (sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Q hA hB xi aux true target
          b slot delta freq lo hi a eta deltaC k chi sigmaF 0 LambdaF w)*
        sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Q hA hB xi aux false target
          b slot delta freq lo hi a eta deltaC k chi sigmaG 0 LambdaG wp := by
  rw [source_B578_actual_canonical_conjugated_pairing434]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro target htarget
  rw [source_B578_actual_native_endpoint_common_factor434,
    source_B578_actual_native_endpoint_common_factor434]
  simp only [star_mul]
  ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualStrippedGatedChart -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 14000

/-- The original pattern-dependent physical projector after stripping.
Its freed-slot sign is separate from the sign ALREADY present in Knu. -/
def sourceB578ActualPatternProjector434
    (L : ℝ) (m : ℕ) (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (n : ℕ) : ℂ :=
  (((1-(-1:ℝ)^(nu.1.card+nu.2.card)*
    (-1:ℝ)^sourceOriginalPParityExponent (sourceNativeOriginalG434 6 L) n)/2:ℝ):ℂ)

/-- One literal separated comparison chart: true physical graph parameter
2k gives STRIPPED wp=w+2k DA DB, while the core modulus remains |k|.
Both P-part gates, the pattern projector before any square, all actual
marks, the full target carrier, one exterior Z_j and one kappa are retained.
This is an exact chart transport, not the RAW B538 z'=z+2k identity, not an
RMS estimate, and not a completed Memory/CRT or full Fourier integration. -/
theorem source_B578_actual_stripped_P_gated_chart434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 6 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 6 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (b : Fin (sourceOriginalLiteralDepth 6 L+1)) (slot : Fin 6)
    (delta : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 6
      (sourceActualSortedScales 6 (sourceOriginalLiteralDepth 6 L) L) b slot).length → ℝ)
    (lo hi : ℕ) (a eta deltaC : ℝ) (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs)
    (U V K : ℝ) (j : ℕ) (ja jb : ℤ)
    (rho : ℝ) (zeta : Fin 3 → ℝ) (t : ℝ) (Spos R : Finset ℕ) :
    let Z := sourceCorrectedDyadicScale U V (L^K) j
    let Y := Z*(Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB))
    let D := sourceOriginalProbeDA434 m nu aux*sourceOriginalProbeDB434 m nu aux
    let wp := fun w : ℕ=>((w:ℤ)+2*k*(D:ℤ)).toNat
    let sigmaF := 2*Real.pi*rho-2*Real.pi*zeta 1
    let sigmaG := 2*Real.pi*zeta 0+2*Real.pi*rho
    let LambdaF := fun n : ℕ=>sourceB578EndpointProfile434 true ((n:ℝ)/Y)*
      sourcePhase n (-(2*Real.pi*rho+2*Real.pi*zeta 2+2*Real.pi*t))
    let LambdaG := fun n : ℕ=>sourceB578EndpointProfile434 false ((n:ℝ)/Y)*
      sourcePhase n (-2*Real.pi*rho)
    let gate := fun w : ℕ=>0<w ∧ 0<(w:ℤ)+2*k*(D:ℤ) ∧
      sourceOriginalPPrimePart (sourceNativeOriginalG434 6 L) w ∈ R ∧
      sourceOriginalPPrimePart (sourceNativeOriginalG434 6 L) (wp w) ∈ R
    (Z:ℂ)/(Y:ℂ)*(∑ w ∈ Spos,
      if gate w then
        star (sourceB578ActualNativeCommon434 L hS b slot delta freq lo hi a eta deltaC k chi
          sigmaF 0 LambdaF w)*
        sourceB578ActualNativeCommon434 L hS b slot delta freq lo hi a eta deltaC k chi
          sigmaG 0 LambdaG (wp w)*
        sourceB574CanonicalStrippedSlice434 J 1 m hmJ nu Q hA hB xi
          (sourceNativeOriginalTb434 6 L) (sourceNativeOriginalVbig434 6 L) aux (1/2:ℝ) w (wp w)*
        sourceB578ActualPatternProjector434 L m nu w*
        sourceB578ActualPatternProjector434 L m nu (wp w)
      else 0) =
    (Z:ℂ)*(sourceB578CanonicalRowScale434 Q xi:ℂ)/(Y:ℂ)*(∑ w ∈ Spos,
      if gate w then
        (∑ target ∈ bigMarkLists (sourceNativeOriginalTb434 6 L)
            (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) (wp w),
          star (sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Q hA hB xi aux true target
            b slot delta freq lo hi a eta deltaC k chi sigmaF 0 LambdaF w)*
          sourceB578ActualNativeRowEndpoint434 L hS J m hmJ nu Q hA hB xi aux false target
            b slot delta freq lo hi a eta deltaC k chi sigmaG 0 LambdaG (wp w))*
        sourceB578ActualPatternProjector434 L m nu w*
        sourceB578ActualPatternProjector434 L m nu (wp w)
      else 0) := by
  dsimp only
  have hLift (Zc Yc C : ℂ) (F G : ℕ → ℂ) (h : ∀w,F w=C*G w) :
      Zc/Yc*(∑w ∈ Spos,F w) = Zc*C/Yc*(∑w ∈ Spos,G w) := by
    simp_rw [h,←Finset.mul_sum]
    ring
  apply hLift
  intro w
  split_ifs with hg
  · rw [source_B578_actual_native_full_canonical_pair434]
    ring
  · simp
end Green64Analytic.SourceBlockSieve

end

end

