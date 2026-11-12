module

public import Green64.Library.Sieve.Foundations.Part041
public import Green64.Library.Sieve.Foundations.Part039
public import Green64.Library.Sieve.Foundations.Part012
public import Green64.Library.Sieve.Foundations.Part040
public import Green64.Library.Sieve.Foundations.Part038
public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part034
public import Green64.Library.Sieve.Foundations.Part037

@[expose] public section

/-!
# Sieve / Foundations / Part042

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## TrueYboxSignedWTauAllSlots -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- TRUE expanded Parity(4.10) cap-free physical Ybox=ceil(6UV)
shifted-divisor τ(u+2) / B590 Fourier source mass, integrated over
ALL its original Q frequency cubes, Boolean allocations and all
20 reserved slots. This is an independent POSITIVE enlarged-carrier
estimate, valid already at fixed real Mellin rho, not a fabricated
pointwise equality of the Y0 and Ybox e/n source sums. The original
factorial and Q selected/skipped prime information stays INSIDE W1;
no extra Q Fourier gate or L^S fine-cell loss. Cbox>=1 fixed first;
precision-independent log exponent CW1+16+CF unchanged. -/
theorem parity_eventually_original_true_Ybox_signed_fullQ_tau_allslots_polylog434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V → Real.exp L≤U*V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)),
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                (sourceOriginalLiteralDepth 20 L) L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤
        20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
          L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_eventually_original_true_Ybox_W1_shifted_tau_polylog434
      Cbox hCbox,
    parity_eventually_original_actual_post_cauchy_Q_gate_L1_polylog434]
    with L hTau hGate
  refine ⟨hTau.1,?_⟩
  intro U V hU hV hUV hUVhi E signed band
  have hL : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hTau.1
  let d := sourceOriginalLiteralDepth 20 L
  let Y := Nat.ceil (6*U*V)
  let Mass := ∑u∈Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((u+2).divisors.card:ℝ)
  let B := Real.exp L*L^parityOriginalW1PolylogExponent434*L^16
  let C := L^parityOriginalB590FixedFourierPolynomialExponent434
  have hMass : 0≤Mass := by
    dsimp [Mass]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hMassB : Mass≤B := hTau.2 U V hU hV hUV hUVhi
  have hB : 0≤B := by dsimp [B]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hSlot (slot : Fin 20) :
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤ B*C := by
    let n := (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length
    have hOne (delta : Fin n → Bool) :
        (∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤
        Mass*(∫xi : Fin n → ℝ,
          ‖parityOriginalActualPostCauchyQGate434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) :=
      parity_original_signed_fullQ_tau_Qcube_integral_le_W1_L1434
        d L E L hL signed band slot delta Y
    have hGateOne := hGate band slot E
    dsimp only at hGateOne
    calc
      _ ≤ ∑delta : Fin n → Bool,
        Mass*(∫xi : Fin n → ℝ,
          ‖parityOriginalActualPostCauchyQGate434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) := by
          apply Finset.sum_le_sum
          intro delta hdelta
          exact hOne delta
      _ = Mass*(∑delta : Fin n → Bool,
          ∫xi : Fin n → ℝ,
            ‖parityOriginalActualPostCauchyQGate434 E
              (sourceActualSortedFrequencyScales 20 d L band slot) xi delta‖) := by
          rw [Finset.mul_sum]
      _ ≤ Mass*C := mul_le_mul_of_nonneg_left hGateOne hMass
      _ ≤ B*C := mul_le_mul_of_nonneg_right hMassB hC
  have hAll :
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            ∑u∈Finset.Ioc 0 Y,
              ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) ≤ 20*(B*C) := by
    calc
      _ ≤ ∑_slot : Fin 20, B*C := by
        apply Finset.sum_le_sum
        intro slot hslot
        exact hSlot slot
      _ = 20*(B*C) := by simp
  calc
    _ ≤ 20*(B*C) := by simpa only [d,Y] using hAll
    _ = 20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
        L^parityOriginalB590FixedFourierPolynomialExponent434 := by
          dsimp [B,C]
          ring
end Green64Analytic.Parity

end

end

/-! ## TrueYboxSignedTauSchwartzMoment -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The complete ACTUAL extended Parity(4.10) Ybox=ceil6UV
20-slot original Q-integrated B590 shifted tau(u+2) mass, times
the genuine source Psi-Schwartz high-s Mellin moment R^-H M_H,
has arbitrary O_A(exp L L^-A) saving uniformly in physical U,V.
The Schwarz order H depends on A and C0, and is fixed before L;
Cbox>=1 is fixed first. This is an arithmetic budget statement,
NOT an equality Y0=Ybox for each fixed Mellin s and NOT by itself
a complex high-tail norm bound. -/
theorem parity_eventually_original_true_Ybox_signed_tau_Schwartz_moment_paid434
    (Cbox A C0 : ℝ) (hCbox : 1≤Cbox) (hC0 : 0<C0)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V → Real.exp L≤U*V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)),
      let M_H := ∫s : ℝ, ‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
      (((L^C0/(2*Real.pi))^H)⁻¹ * M_H) *
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 L,
              ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
                ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
                  (sourceOriginalLiteralDepth 20 L) L E u signed band slot delta xi‖ *
                ((u+2).divisors.card:ℝ)) ≤
      (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-A) := by
  let Cmass : ℝ := parityOriginalW1PolylogExponent434+16+
    parityOriginalB590FixedFourierPolynomialExponent434
  obtain ⟨H,hPrecision⟩ :=
    parity_original_true_mellin_moment_order_exists434 A Cmass C0 hC0
  refine ⟨H,?_⟩
  filter_upwards [parity_eventually_original_true_Ybox_signed_fullQ_tau_allslots_polylog434
      Cbox hCbox] with L hSource
  refine ⟨hSource.1,?_⟩
  intro U V hU hV hUV hUVhi E signed band
  have hL : 1≤L := hSource.1
  let M_H : ℝ := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
  have hM : 0≤M_H := by
    dsimp [M_H]
    apply integral_nonneg
    intro s
    positivity
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL
  have hR : 0<L^C0/(2*Real.pi) :=
    div_pos (Real.rpow_pos_of_pos hLp _) (by positivity)
  have hCoeff : 0≤((L^C0/(2*Real.pi))^H)⁻¹*M_H := by positivity
  have hMass := hSource.2 U V hU hV hUV hUVhi E signed band
  have hPrec : Cmass+A≤C0*(H:ℝ) := by linarith [hPrecision]
  have hPower := parity_original_true_mellin_tail_source_mass_absorption434
    L C0 A Cmass M_H H hL hM hPrec
  have hRPow :
      L^parityOriginalW1PolylogExponent434*L^16*
        L^parityOriginalB590FixedFourierPolynomialExponent434 = L^Cmass := by
    dsimp [Cmass]
    rw [Real.rpow_add hLp,Real.rpow_add hLp]
    rw [←Real.rpow_natCast]
    ring
  dsimp only at hMass ⊢
  calc
    _ ≤ (((L^C0/(2*Real.pi))^H)⁻¹*M_H) *
          (20*Real.exp L*L^Cmass) := by
          apply mul_le_mul_of_nonneg_left _ hCoeff
          calc
            _ ≤ 20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
                  L^parityOriginalB590FixedFourierPolynomialExponent434 := hMass
            _ = 20*Real.exp L*L^Cmass := by
              rw [←hRPow]
              ring
    _ ≤ (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-A) := hPower
end Green64Analytic.Parity

end

end

/-! ## TrueYboxHistoricalHighMellinAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The complex original historical Parity(4.7) high-|s| Ψ-Mellin
integral has arbitrary O_A(exp(L)L^-A) saving even at the ACTUAL
capfree Ybox=ceil(6UV), uniformly for all U,V in the original
dyadic slab exp L<=UV<=Cbox exp L. All 20 reserved Q slots and
Boolean allocations, original h=-2 and epsilon source branches,
real 2πs Mellin and full Q-cube remain literal. True source
W1(P,u) tau(u+2) is paid uniformly up to Ybox; it is NOT asserted
that the Y0 and Ybox fixed-s integrands coincide.
H is selected once before L and the same log exponent pays both
Y0/Ybox expanded historical tails. Full TypeII still OPEN. -/
theorem parity_eventually_original_true_Ybox_historical_high_Psi_Mellin_Q_anylog434
    (Cbox goal C0 : ℝ) (hCbox : 1≤Cbox) (hC0 : 0<C0)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V → Real.exp L≤U*V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1))
        (K J : Finset ℕ) (alpha beta : ℕ → ℂ),
        (∀m∈K,‖alpha m‖≤1) →
        (∀n∈J,‖beta n‖≤1) →
      let d := sourceOriginalLiteralDepth 20 L
      let Ybox := Nat.ceil (6*U*V)
      let R := L^C0/(2*Real.pi)
      let M_H := ∫s : ℝ, ‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
      ‖∫s in {s : ℝ | R≤‖s‖},
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 L,
              parityOriginalHistoricalCauchyAtDelta434
                d L E band slot delta xi (2*Real.pi*s)
                  K J alpha beta signed Ybox)‖ ≤
        (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  obtain ⟨H,hSource⟩ :=
    parity_eventually_original_true_Ybox_signed_tau_Schwartz_moment_paid434
      Cbox goal C0 hCbox hC0 Psi hSmooth hSupport
  refine ⟨H,?_⟩
  filter_upwards [hSource] with L hSourceL
  refine ⟨hSourceL.1,?_⟩
  intro U V hU hV hUV hUVhi E signed band K J alpha beta hAlpha hBeta
  let d := sourceOriginalLiteralDepth 20 L
  let Ybox := Nat.ceil (6*U*V)
  let R := L^C0/(2*Real.pi)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
  let M : ℝ := ∑slot : Fin 20,
    ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 L,
        ∑u∈Finset.Ioc 0 Ybox,
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hSourceL.1
  have hR : 0<R := by
    dsimp [R]
    exact div_pos (Real.rpow_pos_of_pos hLp _) (by positivity)
  have hHigh := parity_original_historical_allslots_high_Psi_Mellin_Q_tau_bound434
    d L E hLp rfl band K J alpha beta signed Ybox L 1 1
    (by norm_num) (by norm_num) hAlpha hBeta
    Psi hSmooth hSupport R hR H
  have hMass := hSourceL.2 U V hU hV hUV hUVhi E signed band
  dsimp only at hMass hHigh ⊢
  calc
    _ ≤ ((1:ℝ)*1*M)*((R^H)⁻¹*M_H) := by
      simpa only [M,R,M_H,d,Ybox,mul_assoc] using hHigh
    _ = ((R^H)⁻¹*M_H)*M := by ring
    _ ≤ (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
      simpa only [M,R,M_H,d,Ybox] using hMass
end Green64Analytic.Parity

end

end

/-! ## TrueYboxCapfreeHighMellinExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- SOURCE-EXACT equality of true Ybox historical and cap-free
Parity(4.7) Bprime Q Fourier sums for every original real rho,
all twenty Q reserved slots and all Boolean allocations.
The selected e positivity and actual physical cofactor bound
K⊂(0,2U], J⊂(0,3V] are explicit use-site prerequisites;
no equality with old Y0 is asserted pointwise in rho. -/
theorem parity_original_true_Ybox_allslots_Q_hist_eq_capfree434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1))
    (hSelected : ∀ (slot : Fin 20)
      (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (alpha beta : ℕ → ℂ) (signed : Bool) (rho T : ℝ) :
    (∑slot : Fin 20,
      ∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi rho K J alpha beta signed
            (Nat.ceil (6*U*V))) =
    (∑slot : Fin 20,
      ∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi rho K J alpha beta signed) := by
  classical
  apply Finset.sum_congr rfl
  intro slot hslot
  apply Finset.sum_congr rfl
  intro delta hdelta
  apply integral_congr_ae
  filter_upwards [] with xi
  exact parity_original_historical_selected_Q_Cauchy_box_eq_no_u_cap434
    d L E U V hL hU hV band slot delta xi rho
    K J alpha beta signed (hSelected slot delta) hK hJ

/-- Same SOURCE-TRUE equality after unrestricted high-|s| inverse
Mellin integration: the true Ybox source and cap-free Bprime are
identical at EACH original (rho=2pi*s,xi) as long as the native
physical source supports are preserved. In contrast, Y0=Ybox
holds only after the COMPLETE Ψ-Mellin integral. -/
theorem parity_original_true_Ybox_allslots_high_Psi_Mellin_hist_eq_capfree434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1))
    (hSelected : ∀ (slot : Fin 20)
      (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (alpha beta : ℕ → ℂ) (signed : Bool)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (R T : ℝ) :
    (∫s in {s : ℝ | R≤‖s‖},
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalCauchyAtDelta434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed (Nat.ceil (6*U*V)))) =
    (∫s in {s : ℝ | R≤‖s‖},
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
      (∑slot : Fin 20,
        ∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed)) := by
  apply integral_congr_ae
  filter_upwards [] with s
  exact congrArg (fun z : ℂ =>
    parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s*z)
    (parity_original_true_Ybox_allslots_Q_hist_eq_capfree434
      d L E U V hL hU hV band hSelected K J hK hJ
      alpha beta signed (2*Real.pi*s) T)
end Green64Analytic.Parity

end

end

/-! ## TrueYboxCapfreeHighMellinAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- TRUE original cap-free Bprime Q-Mellin **complex** high-|s|
Ψ tail, with the actual no-u-cap Parity(4.10) source expression,
retaining all 20 reserved Q slots and Boolean allocations.
Uniform inverse-log O_A(exp L L^-A) follows from independently
proved complete Ybox=ceil6UV shifted-τ mass and exact historical↔
capfree SOURCE equality at Ybox, NOT from false Y0=Ybox pointwise.
Actual selected-e positive source and dyadic K/J bounds are explicit
use-site hypotheses; the paper's original §4/§7 supplies these
before the final assembled TypeII result. -/
theorem parity_eventually_original_true_Ybox_capfree_high_Psi_Mellin_Q_anylog434
    (Cbox goal C0 : ℝ) (hCbox : 1≤Cbox) (hC0 : 0<C0)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V → Real.exp L≤U*V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1))
        (K J : Finset ℕ) (alpha beta : ℕ → ℂ),
        (∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length → Bool),
          ∀e∈parityOriginalHistoricalCauchyActiveESupport434
            (sourceOriginalLiteralDepth 20 L) L E band slot delta,0<e) →
        (∀m∈K,(m:ℝ)≤2*U) →
        (∀n∈J,(n:ℝ)≤3*V) →
        (∀m∈K,‖alpha m‖≤1) →
        (∀n∈J,‖beta n‖≤1) →
      let d := sourceOriginalLiteralDepth 20 L
      let Ybox := Nat.ceil (6*U*V)
      let R := L^C0/(2*Real.pi)
      let M_H := ∫s : ℝ, ‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
      ‖∫s in {s : ℝ | R≤‖s‖},
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑slot : Fin 20,
          ∑delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 L,
              parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta xi (2*Real.pi*s)
                  K J alpha beta signed)‖ ≤
        (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  obtain ⟨H,hOld⟩ :=
    parity_eventually_original_true_Ybox_historical_high_Psi_Mellin_Q_anylog434
      Cbox goal C0 hCbox hC0 Psi hSmooth hSupport
  refine ⟨H,?_⟩
  filter_upwards [hOld] with L hLold
  rcases hLold with ⟨hL1,hRest⟩
  refine ⟨hL1,?_⟩
  intro U V hU hV hUV hUVhi E signed band K J alpha beta
    hSelected hK hJ hAlpha hBeta
  let d := sourceOriginalLiteralDepth 20 L
  let R := L^C0/(2*Real.pi)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL1
  have hEq := parity_original_true_Ybox_allslots_high_Psi_Mellin_hist_eq_capfree434
    d L E U V hLp hU.le hV.le band hSelected K J hK hJ alpha beta signed
    Psi hSmooth hSupport R L
  have hBound := hRest U V hU hV hUV hUVhi E signed band
    K J alpha beta hAlpha hBeta
  dsimp only at hBound ⊢
  rw [hEq] at hBound
  simpa only [d,R,M_H] using hBound
end Green64Analytic.Parity

end

end

/-! ## TrueYboxSingleSlotHighCapfreeExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1100000

/-- EXACT one original reserved-Q slot historical Ybox Cauchy sum
is identical to the cap-free Bprime source at EVERY real rho and
all original Boolean allocations and native N-dimensional Q cubes.
This per-slot identity (unlike the full all-slot complex sum)
can be composed directly with the original Parity(4.7) pre-Cauchy
one-slot comparison. Positive selected e and actual K/J support
are explicit use-site constraints. Y0 is NOT exchanged pointwise. -/
theorem parity_original_true_Ybox_single_slot_Q_hist_eq_capfree434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (hSelected : ∀ (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (alpha beta : ℕ → ℂ) (signed : Bool) (rho T : ℝ) :
    (∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta xi rho K J alpha beta signed
          (Nat.ceil (6*U*V))) =
    (∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta xi rho K J alpha beta signed) := by
  classical
  apply Finset.sum_congr rfl
  intro delta hdelta
  apply integral_congr_ae
  filter_upwards [] with xi
  exact parity_original_historical_selected_Q_Cauchy_box_eq_no_u_cap434
    d L E U V hL hU hV band slot delta xi rho
    K J alpha beta signed (hSelected delta) hK hJ

/-- Same exact single-slot physical identity AFTER the complex
high-|s| Mellin integration, retaining genuine 2πs and Q measure.
This is used to obtain an actual one-slot high-s O_A bound, not
only a bound for the sum of twenty complex reserved Q slots. -/
theorem parity_original_true_Ybox_single_slot_high_hist_eq_capfree434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (hSelected : ∀ (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (alpha beta : ℕ → ℂ) (signed : Bool)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (R T : ℝ) :
    (∫s in {s : ℝ | R≤‖s‖},
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed (Nat.ceil (6*U*V)))) =
    (∫s in {s : ℝ | R≤‖s‖},
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed)) := by
  apply integral_congr_ae
  filter_upwards [] with s
  exact congrArg (fun z : ℂ =>
    parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s*z)
    (parity_original_true_Ybox_single_slot_Q_hist_eq_capfree434
      d L E U V hL hU hV band slot hSelected K J hK hJ
      alpha beta signed (2*Real.pi*s) T)
end Green64Analytic.Parity

end

end

/-! ## CapfreeSingleSlotMellinMeasTau -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- For ONE actual original reserved Q slot, the cap-free Bprime Q
Fourier integral summed over its Boolean allocations is strongly
measurable in real Mellin s and uniformly dominated by its OWN
positive Ybox=ceil(6UV) B590 shifted-divisor arithmetic mass.
The proof uses literal selected-Q e positivity, source rho/Q joint
continuity and original e/n historical↔capfree equality, never a
complex cancellation between distinct reserved slots. -/
theorem parity_original_true_Ybox_capfree_single_slot_Mellin_meas_tau_bound434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (hSelected : ∀ (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (alpha beta : ℕ → ℂ) (signed : Bool)
    (hAlpha : ∀m∈K,‖alpha m‖≤1)
    (hBeta : ∀n∈J,‖beta n‖≤1) (T : ℝ) :
    let B : ℝ → ℂ := fun s =>
      ∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed
    let M : ℝ := ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)
    AEStronglyMeasurable B ∧ 0≤M ∧ ∀s:ℝ,‖B s‖≤M := by
  classical
  let n := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let B : ℝ → ℂ := fun s =>
    ∑delta : Fin n → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed
  let M : ℝ := ∑delta : Fin n → Bool,
    ∫xi in parityOriginalActualFullQFrequencyCube434 T,
      ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)
  have hJoint (delta : Fin n → Bool) :=
    parity_original_actual_capfree_Bprime_joint_rho_Q_continuous434
      d L E U V hL hd hU hV band slot delta (hSelected delta)
      K J alpha beta signed hK hJ
  have hMeasRho : StronglyMeasurable (fun rho : ℝ =>
      ∑delta : Fin n → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi rho K J alpha beta signed) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro delta hdelta
    exact (hJoint delta).stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Fin n → ℝ)).restrict
        (parityOriginalActualFullQFrequencyCube434 T))
  have hMeas : AEStronglyMeasurable B :=
    (hMeasRho.comp_measurable
      (by fun_prop : Measurable (fun s : ℝ => 2*Real.pi*s))).aestronglyMeasurable
  have hM : 0≤M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro delta hdelta
    apply integral_nonneg
    intro xi
    apply Finset.sum_nonneg
    intro u hu
    positivity
  have hBound (s : ℝ) : ‖B s‖≤M := by
    have hHistory (delta : Fin n → Bool) :=
      parity_original_historical_Cauchy_Qcube_rho_tau_bound_lean434
        d L E hL hd band slot delta K J alpha beta signed
        (Nat.ceil (6*U*V)) (2*Real.pi*s) T 1 1
        (by norm_num) (by norm_num) hAlpha hBeta
    have hEq := parity_original_true_Ybox_single_slot_Q_hist_eq_capfree434
      d L E U V hL hU hV band slot hSelected K J hK hJ
      alpha beta signed (2*Real.pi*s) T
    dsimp [B]
    rw [←hEq]
    calc
      _ ≤ ∑delta : Fin n → Bool,
        ‖∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed (Nat.ceil (6*U*V))‖ := norm_sum_le _ _
      _ ≤ ∑delta : Fin n → Bool,
        (∫xi in parityOriginalActualFullQFrequencyCube434 T,
          ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
            ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
              d L E u signed band slot delta xi‖ *
              ((u+2).divisors.card:ℝ)) := by
          apply Finset.sum_le_sum
          intro delta hdelta
          simpa only [one_mul] using hHistory delta
      _ = M := by rfl
  change AEStronglyMeasurable B ∧ 0≤M ∧ ∀s:ℝ,‖B s‖≤M
  exact ⟨hMeas,hM,hBound⟩
end Green64Analytic.Parity

end

end

/-! ## CapfreeSingleSlotFullPsiMellinJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- For ONE chosen original reserved Q slot (the one required by
Parity's pre-Cauchy source theorem), the genuine full REAL Ψ-Mellin
complex norm of the actual capfree Bprime is at most its low-Icc
plus high-|s| bounds. The actual Bochner integrability and strong
measurability come from the native selected-e physical Ybox Cauchy
source, the one-slot Q arithmetic τ majorant, and true joint
Mellin×Q continuity: no assumed hMeas, no cancellation with the
19 other complex reserved slots. Both parts use the same capfree
Bprime at each real rho=2πs. -/
theorem parity_original_actual_capfree_single_slot_full_Psi_Mellin_from_low_high434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (hSelected : ∀ (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (alpha beta : ℕ → ℂ) (signed : Bool)
    (hAlpha : ∀m∈K,‖alpha m‖≤1)
    (hBeta : ∀n∈J,‖beta n‖≤1)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (T R Dlow Dhigh : ℝ) (hR : 0≤R)
    (hLow :
      ‖∫s in Set.Icc (-R) R,
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed)‖≤Dlow)
    (hHigh :
      ‖∫s in {s : ℝ | R≤‖s‖},
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed)‖≤Dhigh) :
    ‖∫s : ℝ,
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed)‖≤Dlow+Dhigh := by
  classical
  let B : ℝ → ℂ := fun s =>
    ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
          d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed
  let M : ℝ := ∑delta : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∫xi in parityOriginalActualFullQFrequencyCube434 T,
      ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
        ((u+2).divisors.card:ℝ)
  have hSource := parity_original_true_Ybox_capfree_single_slot_Mellin_meas_tau_bound434
    d L E U V hL hd hU hV band slot hSelected K J hK hJ
    alpha beta signed hAlpha hBeta T
  rcases hSource with ⟨hMeas,hMnonneg,hBound⟩
  have h := parity_original_true_Psi_Mellin_full_norm_le_parts434
    L Psi hSmooth hSupport R hR B hMeas M hMnonneg hBound
    Dlow Dhigh hLow hHigh
  simpa only [B,M] using h
end Green64Analytic.Parity

end

end

/-! ## SingleSlotCapfreeFullMellinQSwap -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2100000

/-- LITERAL original one reserved-Q-slot cap-free Bprime SOURCE
Parity(4.7) with original Q-OUTER Lebesgue product box and full real
Ψ-Mellin INNER integral is exactly the same COMPLEX number as the
full real Ψ-Mellin OUTER of the single-slot sum of Q-integrated
Bprime. Uses the true historical Ybox=ceil6UV, genuine 2πs,
original selected/skipped Q labels, source P/W1/e and finite
Bochner Fubini integrability dominated by Schwartz×shifted τ.
No fictitious measure normalization, duplicated selected Q gate or
complex cancellation of distinct reserved slots. -/
theorem parity_original_actual_capfree_single_slot_full_Psi_Mellin_Q_swap434
    (d : ℕ) (L E U V : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (hU : 0≤U) (hV : 0≤V)
    (band : Fin (d+1)) (slot : Fin 20)
    (hSelected : ∀ (delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool),
      ∀e∈parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot delta,0<e)
    (K J : Finset ℕ) (hK : ∀m∈K,(m:ℝ)≤2*U)
    (hJ : ∀n∈J,(n:ℝ)≤3*V)
    (alpha beta : ℕ → ℂ) (signed : Bool)
    (hAlpha : ∀m∈K,‖alpha m‖≤1)
    (hBeta : ∀n∈J,‖beta n‖≤1)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (T : ℝ) :
    parityOriginalActualPsiMellinCapfreeBprimeQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed T =
    ∫s : ℝ,
      parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed) := by
  classical
  let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let Ybox := Nat.ceil (6*U*V)
  let Kpsi : ℝ → ℂ := parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport
  have hHistory := parity_original_actual_historical_Psi_Mellin_Ybox_eq_capfree434
    d L E U V hL hU hV band slot hSelected K J hK hJ
    Psi hSmooth hSupport alpha beta signed T
  have hSwap := parity_original_historical_single_slot_full_Psi_Mellin_Q_Fubini434
    d L E hL hd band slot K J alpha beta signed Ybox T 1 1
    (by norm_num) (by norm_num) hAlpha hBeta Psi hSmooth hSupport
  have hInt (s : ℝ) (delta : Fin n → Bool) :
      IntegrableOn (fun xi : Fin n → ℝ =>
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot delta xi (2*Real.pi*s) K J alpha beta signed Ybox)
        (parityOriginalActualFullQFrequencyCube434 T) := by
    have hMap : Continuous (fun xi : Fin n → ℝ => (2*Real.pi*s,xi)) :=
      continuous_const.prodMk continuous_id
    have hCont :=
      (parity_original_historical_Cauchy_joint_mellin_Q_continuous434
        d L E hL hd band slot delta K J alpha beta signed Ybox).comp hMap
    exact hCont.continuousOn.integrableOn_compact
      (parity_original_true_full_Q_frequency_cube_compact434 T)
  have hExchange (s : ℝ) :
      (∫xi in parityOriginalActualFullQFrequencyCube434 T,
        Kpsi s * (∑delta : Fin n → Bool,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed Ybox)) =
      Kpsi s * (∑delta : Fin n → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed Ybox) := by
    rw [integral_const_mul]
    rw [integral_finset_sum]
    intro delta hdelta
    exact hInt s delta
  have hEQ (s : ℝ) :
      (∑delta : Fin n → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalCauchyAtDelta434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed Ybox) =
      (∑delta : Fin n → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
            d L E band slot delta xi (2*Real.pi*s)
            K J alpha beta signed) :=
    parity_original_true_Ybox_single_slot_Q_hist_eq_capfree434
      d L E U V hL hU hV band slot hSelected K J hK hJ
      alpha beta signed (2*Real.pi*s) T
  calc
    parityOriginalActualPsiMellinCapfreeBprimeQBox434
      d L E band slot Psi hSmooth hSupport K J alpha beta signed T =
      parityOriginalActualHistoricalPsiMellinCauchyQBox434
        d L E band slot Psi hSmooth hSupport K J alpha beta signed Ybox T :=
        hHistory.symm
    _ = ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          ∫s : ℝ, Kpsi s *
            (∑delta : Fin n → Bool,
              parityOriginalHistoricalCauchyAtDelta434
                d L E band slot delta xi (2*Real.pi*s)
                K J alpha beta signed Ybox) := by
          unfold parityOriginalActualHistoricalPsiMellinCauchyQBox434
            parityOriginalActualHistoricalPsiMellinCauchyAtXi434
          rw [parity_original_Q_fourier_product_restrict_measure_eq_cube434 T]
    _ = ∫s : ℝ,
          ∫xi in parityOriginalActualFullQFrequencyCube434 T,
            Kpsi s * (∑delta : Fin n → Bool,
              parityOriginalHistoricalCauchyAtDelta434
                d L E band slot delta xi (2*Real.pi*s)
                K J alpha beta signed Ybox) := hSwap
    _ = ∫s : ℝ, Kpsi s *
          (∑delta : Fin n → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 T,
              parityOriginalHistoricalCauchyAtDelta434
                d L E band slot delta xi (2*Real.pi*s)
                K J alpha beta signed Ybox) := by
          apply integral_congr_ae
          filter_upwards [] with s
          exact hExchange s
    _ = ∫s : ℝ, Kpsi s *
          (∑delta : Fin n → Bool,
            ∫xi in parityOriginalActualFullQFrequencyCube434 T,
              parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
                d L E band slot delta xi (2*Real.pi*s)
                K J alpha beta signed) := by
          apply integral_congr_ae
          filter_upwards [] with s
          exact congrArg (fun z:ℂ => Kpsi s*z) (hEQ s)
end Green64Analytic.Parity

end

end

/-! ## TrueYboxSingleSlotTauBudget -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Every ONE actual original reserved-Q slot has a positive
shifted-divisor τ(u+2) B590 Fourier mass bounded by the complete
already proved 20-slot source budget at Ybox=ceil6UV. This is the
valid one-slot subestimate (positive integrals), NOT an inequality
between complex signed subsums. The remaining 19 slots contribute
nonnegative real integrals and thus cannot cancel this one. -/
theorem parity_original_true_Ybox_single_slot_tau_le_allslots434
    (d : ℕ) (L E U V : ℝ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    (∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)) ≤
    (∑slot0 : Fin 20,
      ∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot0).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 T,
          ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
            ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
              d L E u signed band slot0 delta xi‖ *
            ((u+2).divisors.card:ℝ)) := by
  classical
  let F : Fin 20 → ℝ := fun slot =>
    ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 T,
        ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot delta xi‖ *
          ((u+2).divisors.card:ℝ)
  have hNonneg (slot : Fin 20) : 0≤F slot := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro delta hdelta
    apply integral_nonneg
    intro xi
    apply Finset.sum_nonneg
    intro u hu
    positivity
  exact Finset.single_le_sum (fun slot0 (_ : slot0∈(Finset.univ : Finset (Fin 20))) =>
    hNonneg slot0) (Finset.mem_univ slot)

/-- The full physical one-slot Q-frequency arithmetic τ mass at
TRUE Ybox is O(exp L L^(CW1+16+CF)), with harmless constant 20.
Uniform in arbitrary original slot, reserved band, E and signed
ε, and physical U,V in one Cbox dyadic slab. This source bound is
strong enough to pay one-slot high-Ψ-Mellin tails without confusing
the original source (one reserved slot) with a COMPLEX sum of slots. -/
theorem parity_eventually_original_true_Ybox_single_slot_tau_polylog434
    (Cbox : ℝ) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V → Real.exp L≤U*V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1))
        (slot : Fin 20),
      (∑delta : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool,
        ∫xi in parityOriginalActualFullQFrequencyCube434 L,
          ∑u∈Finset.Ioc 0 (Nat.ceil (6*U*V)),
            ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
              (sourceOriginalLiteralDepth 20 L) L E u signed band slot delta xi‖ *
            ((u+2).divisors.card:ℝ)) ≤
      20*Real.exp L*L^parityOriginalW1PolylogExponent434*L^16*
        L^parityOriginalB590FixedFourierPolynomialExponent434 := by
  filter_upwards [parity_eventually_original_true_Ybox_signed_fullQ_tau_allslots_polylog434
    Cbox hCbox] with L hTotal
  refine ⟨hTotal.1,?_⟩
  intro U V hU hV hUV hUVhi E signed band slot
  exact (parity_original_true_Ybox_single_slot_tau_le_allslots434
    (sourceOriginalLiteralDepth 20 L) L E U V signed band slot L).trans
      (hTotal.2 U V hU hV hUV hUVhi E signed band)
end Green64Analytic.Parity

end

end

/-! ## TrueYboxCapfreeSingleSlotHighAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The original Parity(4.7) **ONE reserved Q slot** cap-free Bprime
HIGH-Ψ-Mellin complex integral has arbitrary O_A(exp L L^-A) saving
uniformly in expL<=UV<=Cbox expL. Its own positive weighted τ source
mass is bounded using `single_le_sum` BEFORE multiplication by the
Schwartz moment. This does NOT use the invalid |one complex slot|≤
|sum of complex slots| comparison. It is SOURCE-correct for the
specific reserved slot used by the original pre-Cauchy approximation.
The true Ybox=ceil6UV, original 2πs, full Q allocations and
selected-e positivity/cofactor K,J supports are retained.
H is chosen before L. Not yet general TypeII(4.2). -/
theorem parity_eventually_original_true_Ybox_capfree_single_slot_high_anylog434
    (Cbox goal C0 : ℝ) (hCbox : 1≤Cbox) (hC0 : 0<C0)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    ∃ H : ℕ, ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (U V : ℝ), 0<U → 0<V → Real.exp L≤U*V →
        U*V≤Cbox*Real.exp L →
      ∀ (E : ℝ) (signed : Bool)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1))
        (slot : Fin 20)
        (K J : Finset ℕ) (alpha beta : ℕ → ℂ),
        (∀ (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length → Bool),
          ∀e∈parityOriginalHistoricalCauchyActiveESupport434
            (sourceOriginalLiteralDepth 20 L) L E band slot delta,0<e) →
        (∀m∈K,(m:ℝ)≤2*U) →
        (∀n∈J,(n:ℝ)≤3*V) →
        (∀m∈K,‖alpha m‖≤1) →
        (∀n∈J,‖beta n‖≤1) →
      let d := sourceOriginalLiteralDepth 20 L
      let R := L^C0/(2*Real.pi)
      let M_H := ∫s : ℝ, ‖s‖^H *
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
      ‖∫s in {s : ℝ | R≤‖s‖},
        parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s *
        (∑delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool,
          ∫xi in parityOriginalActualFullQFrequencyCube434 L,
            parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
              d L E band slot delta xi (2*Real.pi*s)
              K J alpha beta signed)‖ ≤
        (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  obtain ⟨H,hSource⟩ :=
    parity_eventually_original_true_Ybox_signed_tau_Schwartz_moment_paid434
      Cbox goal C0 hCbox hC0 Psi hSmooth hSupport
  refine ⟨H,?_⟩
  filter_upwards [hSource] with L hSourceL
  refine ⟨hSourceL.1,?_⟩
  intro U V hU hV hUV hUVhi E signed band slot K J alpha beta
    hSelected hK hJ hAlpha hBeta
  let d := sourceOriginalLiteralDepth 20 L
  let Ybox := Nat.ceil (6*U*V)
  let R := L^C0/(2*Real.pi)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖
  let SlotMass : ℝ := ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∫xi in parityOriginalActualFullQFrequencyCube434 L,
      ∑u∈Finset.Ioc 0 Ybox,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
        ((u+2).divisors.card:ℝ)
  let AllMass : ℝ := ∑slot0 : Fin 20,
    ∑delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot0).length → Bool,
      ∫xi in parityOriginalActualFullQFrequencyCube434 L,
        ∑u∈Finset.Ioc 0 Ybox,
          ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot0 delta xi‖ *
          ((u+2).divisors.card:ℝ)
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hSourceL.1
  have hR : 0<R := by
    dsimp [R]
    exact div_pos (Real.rpow_pos_of_pos hLp _) (by positivity)
  have hM : 0≤M_H := by
    dsimp [M_H]
    apply integral_nonneg
    intro s
    positivity
  have hCoefficient : 0≤(R^H)⁻¹*M_H := by positivity
  have hSingle := parity_original_true_Ybox_single_slot_tau_le_allslots434
    d L E U V signed band slot L
  have hMassLe : SlotMass≤AllMass := by
    simpa only [SlotMass,AllMass,d,Ybox] using hSingle
  have hBudget := hSourceL.2 U V hU hV hUV hUVhi E signed band
  have hHistory := parity_original_historical_single_slot_high_Psi_Mellin_Q_tau_bound434
    d L E hLp rfl band slot K J alpha beta signed Ybox 1 1
    (by norm_num) (by norm_num) hAlpha hBeta Psi hSmooth hSupport
    R hR H L
  have hEq := parity_original_true_Ybox_single_slot_high_hist_eq_capfree434
    d L E U V hLp hU.le hV.le band slot hSelected K J hK hJ
    alpha beta signed Psi hSmooth hSupport R L
  rw [hEq] at hHistory
  dsimp only at hHistory ⊢
  calc
    _ ≤ ((1:ℝ)*1*SlotMass)*((R^H)⁻¹*M_H) := by
      simpa only [SlotMass,R,M_H,d,Ybox,mul_assoc] using hHistory
    _ = ((R^H)⁻¹*M_H)*SlotMass := by ring
    _ ≤ ((R^H)⁻¹*M_H)*AllMass :=
      mul_le_mul_of_nonneg_left hMassLe hCoefficient
    _ ≤ (20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
      simpa only [AllMass,R,M_H,d,Ybox] using hBudget
end Green64Analytic.Parity

end

end

/-! ## UnfilteredSingleKOriginalFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- A single signed nonzero original k, with arbitrary complex
cofactor/phase W, reindexed from e,m,(m',n) Cauchy fibres to
m,(e,m',n) native Sigma-source fibres WITHOUT any extra counting.
This exact identity is what permits a common Schwartz Fourier
integral over the COMPLETE original ungated finite e/n support;
no positive norm majorant or conditional analytic bound appears. -/
theorem parity_original_full_psi_unfiltered_fixed_k_fubini_source_exact434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot delta Y e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k,
          W (parityOriginalHistoricalUngatedSourceToSigma434 m (e,q))
      else 0) =
    ∑m∈K,∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta Y m K k,
      W (parityOriginalHistoricalUngatedSourceToSigma434 m q) := by
  classical
  have hIndex := parity_original_full_psi_unfiltered_global_kZ_sigma_image_exact434
    d L E V band slot delta Y K ({k}:Finset ℤ) ({1}:Finset ℕ)
    (by intro k0 hk0; have heq : k0=k := Finset.mem_singleton.mp hk0; rw [heq]; exact hk)
    (fun _ _ i => W i)
  simp only [Finset.sum_singleton] at hIndex
  calc
    _ = ∑m∈K,∑i∈(parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
        d L E V band slot delta Y m K k).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m),W i := hIndex
    _ = ∑m∈K,∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
        d L E V band slot delta Y m K k,
        W (parityOriginalHistoricalUngatedSourceToSigma434 m q) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (parity_original_ungated_actual_fixed_m_k_sigma_signed_reindex434
        d L E V band slot delta Y m K k hk W).symm
end Green64Analytic.Parity

end

end

/-! ## UngatedPhysicalB633ProjectorCoeff -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Pointwise EXACT original Parity(4.16) physical cofactor coefficient:
when the WHOLE native Parity (2.6) character projector on m,m' has value
one, the original full-odd natural (e,n,m,m') Cauchy coefficient with
three source imaginary powers is EXACTLY the real B633 character-free
atom times both original alpha cofactors. This uses the actual native
Q/P/H0 skipped-prime residual, W1 and signed epsilon; no individual
chi is erased and no positive-correlation norm monotonicity is used.
The arithmetic projector equality is an explicit use-site hypothesis,
to be discharged on actual b629 rough-alpha support. -/
theorem parity_original_ungated_physical_coeff_eq_B633_projected434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (Y e m mp n : ℕ) (he : Odd e) (hNe : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot delta Y e m mp n)
    (k : ℤ) (hk : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (hProjector :
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
        chi (mp:ZMod (2*k.natAbs)) *
        star (chi (m:ZMod (2*k.natAbs))))=1) :
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let zp := ((z:ℤ)+2*k).toNat
    let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
      (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
    let Atom := parityOriginalHistoricalB633CharacterFreeAtom434
      L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi m mp z zp
    imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e n m mp =
      Atom * alpha m * star (alpha mp) := by
  classical
  dsimp only
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  let zp := ((z:ℤ)+2*k).toNat
  let q := 2*k.natAbs
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha q
    (1:DirichletCharacter ℂ q) 0 0
  let Atom := parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi m mp z zp
  let P : ℂ := imaginaryPower m xi1 * imaginaryPower mp xi2 *
    imaginaryPower z xi3 *
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e n m mp
  let Q : ℂ := Atom * alpha m * star (alpha mp)
  let c : DirichletCharacter ℂ q → ℂ :=
    parityShiftTwoMaskCoefficient434 k.natAbs
  let cm : DirichletCharacter ℂ q → ℂ := fun chi =>
    chi (mp:ZMod q) * star (chi (m:ZMod q))
  obtain ⟨u,hu,up,hup,hDiv,hDivp,hVS,hVPS⟩ := hValid
  have hmN : m*n=u+2 := (Finset.mem_filter.mp hu).2.2.2
  have hmpN : mp*n=up+2 := (Finset.mem_filter.mp hup).2.2.2
  have huE : e*(u/e)=u := Nat.mul_div_cancel_left' hDiv
  have hupE : e*(up/e)=up := Nat.mul_div_cancel_left' hDivp
  have hMN : m*n=e*(u/e)+2 := by rw [hmN,huE]
  have hMpN : mp*n=e*(up/e)+2 := by rw [hmpN,hupE]
  obtain ⟨k0,hDet,hVShift,hShift⟩ :=
    parity_original_historical_ungated_two_endpoint_signed_k_exists434
      e n m mp (u/e) (up/e) he hMN hMpN
  have hkCanonical : parityOriginalHistoricalOffdiagK434 e m mp=k0 :=
    parity_original_historical_physical_k_eq_quotient434 e m mp he.pos k0 hDet
  have hk0 : k0=k := hkCanonical.symm.trans hk
  have hZpoint : z=mp*(u/e) := by
    dsimp [z,parityOriginalHistoricalCanonicalZ434,
      parityOriginalHistoricalCanonicalV434]
    have hU : m*n-2=u := by omega
    rw [hU]
  have hShiftInt : (((mp*(u/e):ℕ):ℤ)+2*k)=((m*(up/e):ℕ):ℤ) := by
    simpa only [hk0, Nat.cast_mul] using hShift
  have hZpPoint : zp=m*(up/e) := by
    dsimp [zp]
    rw [hZpoint]
    have hh := congrArg Int.toNat hShiftInt
    simpa only [Int.toNat_natCast] using hh
  have hTerm (chi : DirichletCharacter ℂ q) : cm chi * P = Q * cm chi := by
    have hSrc := parity_original_historical_ungated_two_endpoint_source_eq_B633434
      d L band slot delta freq K alpha q chi Y e n m mp u up
      hu hup hDiv hDivp hVS hVPS rho xi1 xi2 xi3 signed
    have hFac := parity_original_historical_B633_full_character_factor434
      L rho xi1 xi2 xi3 signed alpha
      (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).residual
      q chi
      (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).lo
      (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).hi
      m mp z zp
    dsimp only at hSrc hFac
    rw [←hZpoint,←hZpPoint] at hSrc
    change (chi (mp:ZMod q) * star (chi (m:ZMod q)) *
      imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e n m mp) =
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).residual
        q chi
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).hi
        m mp z zp at hSrc
    have hEqual :
      parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).residual
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).hi
        m mp z zp = Atom := rfl
    rw [hEqual] at hFac
    have hFactored :
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).residual
        q chi
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).hi
        m mp z zp = Q*cm chi := by
      simpa only [Q,cm,mul_assoc] using hFac
    calc
      cm chi * P = parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).residual
        q chi
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot delta freq K alpha q chi 0 0).hi
        m mp z zp := by simpa only [cm,P,mul_assoc] using hSrc
      _ = Q*cm chi := hFactored
  have hProj : (∑chi : DirichletCharacter ℂ q,c chi*cm chi)=1 := by
    simpa only [q,c,cm,mul_assoc] using hProjector
  have hSum : (∑chi : DirichletCharacter ℂ q,c chi*(cm chi*P)) =
      ∑chi : DirichletCharacter ℂ q,c chi*(Q*cm chi) := by
    apply Finset.sum_congr rfl
    intro chi hchi
    rw [hTerm chi]
  have hLeft : (∑chi : DirichletCharacter ℂ q,c chi*(cm chi*P)) = P := by
    calc
      _ = (∑chi : DirichletCharacter ℂ q,c chi*cm chi)*P := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro chi hchi
        ring
      _ = P := by rw [hProj]; ring
  have hRight : (∑chi : DirichletCharacter ℂ q,c chi*(Q*cm chi)) = Q := by
    calc
      _ = Q*(∑chi : DirichletCharacter ℂ q,c chi*cm chi) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro chi hchi
        ring
      _ = Q := by rw [hProj]; ring
  change P=Q
  exact hLeft.symm.trans (hSum.trans hRight)
end Green64Analytic.Parity

end

end

/-! ## ActualFinePhysicalB633Coeff -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The actual original full-odd physical B509 cofactor pair is
EXACTLY the original Parity(4.16) B633 character-free atom with
source b629 fine alpha and genuine reserved H0, including ALL
three original source-frequency powers. For nonzero alpha the
entire chi projector is proved from actual roughness and the
physical signed h=-2 bilinear equations; the zero-alpha cases
vanish algebraically. No isolated-chi cancellation is asserted,
no artificial Pfree-e gate or post-Fourier hard mask is introduced.
This is an exact physical coefficient equality, not yet TypeII(4.2). -/
theorem parity_eventually_original_actual_fine_physical_B509_eq_B633_atom434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l uFine : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (Y e m mp n : ℕ),
      Odd e → m≠mp →
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot delta Y e m mp n →
      parityOriginalHistoricalOffdiagK434 e m mp=k →
      ∀ (rho xi1 xi2 xi3 : ℝ) (signed : Bool),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l uFine)
      let z := parityOriginalHistoricalCanonicalZ434 e m mp n
      let zp := ((z:ℤ)+2*k).toNat
      let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
        (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let Atom := parityOriginalHistoricalB633CharacterFreeAtom434
        L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi m mp z zp
      imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot delta freq rho alpha signed Y e n m mp =
        Atom * alpha m * star (alpha mp) := by
  filter_upwards [parity_eventually_original_actual_fine_physical_full_projector_one434
    S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l uFine hl hlow K k hk hkBound d band slot delta freq
    Y e m mp n he hNe hValid hK rho xi1 xi2 xi3 signed
  classical
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma l uFine)
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  let zp := ((z:ℤ)+2*k).toNat
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let Atom := parityOriginalHistoricalB633CharacterFreeAtom434
    L rho xi1 xi2 xi3 signed F0.residual F0.lo F0.hi m mp z zp
  by_cases hmZero : alpha m=0
  · have hPair : parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e n m mp=0 := by
        simp [parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434,hmZero]
    dsimp only
    change imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e n m mp =
      Atom * alpha m * star (alpha mp)
    rw [hPair,hmZero]
    ring
  by_cases hmpZero : alpha mp=0
  · have hPair : parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e n m mp=0 := by
        simp [parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434,hmpZero]
    dsimp only
    change imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e n m mp =
      Atom * alpha m * star (alpha mp)
    rw [hPair,hmpZero]
    simp
  have hMask := hProj.2 prime l uFine hl hlow K k hk hkBound
    d band slot delta Y e m mp n he hNe hValid hK hmZero hmpZero
  have hEq := parity_original_ungated_physical_coeff_eq_B633_projected434
    d L hProj.1 band slot delta freq K alpha
    Y e m mp n he hNe hValid k hK rho xi1 xi2 xi3 signed hMask
  dsimp only at hEq ⊢
  exact hEq
end Green64Analytic.Parity

end

end

/-! ## ActualFineZeroTwistB633Coeff -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false

/-- The actual Parity(4.10) ungated B509 physical source coefficient is
the literal Parity(4.16) B633 source prime-slot atom, before the 3D
Fourier exponent is inserted, with its THREE additional cofactor
frequencies all exactly zero. This is the use-site matching the
original unseparated post-Cauchy complex offdiagonal; the later
Schwartz Fourier integral supplies the nonzero 2πζ shifts. All actual
b629 alpha values including zeros, original H0/W1/epsilon and
signed k modulus 2|k| remain SOURCE-correct. -/
theorem parity_eventually_original_actual_fine_ungated_physical_coeff_eq_B633_zero_twist434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l uFine : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (Y e m mp n : ℕ),
      Odd e → m≠mp →
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot delta Y e m mp n →
      parityOriginalHistoricalOffdiagK434 e m mp=k →
      ∀ (rho : ℝ) (signed : Bool),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l uFine)
      let z := parityOriginalHistoricalCanonicalZ434 e m mp n
      let zp := ((z:ℤ)+2*k).toNat
      let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
        (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e n m mp =
      parityOriginalHistoricalB633CharacterFreeAtom434
        L rho 0 0 0 signed F0.residual F0.lo F0.hi m mp z zp *
        alpha m * star (alpha mp) := by
  filter_upwards [parity_eventually_original_actual_fine_physical_B509_eq_B633_atom434
    S beta gamma Ck hS hbeta hgamma] with L hRoot
  refine ⟨hRoot.1,?_⟩
  intro prime l uFine hl hlow K k hk hkBound d band slot delta freq
    Y e m mp n he hNe hValid hK rho signed
  have h := hRoot.2 prime l uFine hl hlow K k hk hkBound
    d band slot delta freq Y e m mp n he hNe hValid hK rho 0 0 0 signed
  dsimp only at h ⊢
  have hPow (q : ℕ) : imaginaryPower q (0:ℝ)=1 := by
    unfold imaginaryPower
    simp
  simp only [hPow,one_mul] at h
  exact h
end Green64Analytic.Parity

end

end

/-! ## ActualFinePhysicalOuterSigma -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact entire original full-odd ungated Parity (4.10) physical
complex post-Cauchy source sum at fixed signed k, rewritten as the
native B633 Sigma-source image with the ACTUAL zero-frequency
physical cofactor atom and actual fine b629 alpha, including zeros.
All natural e,m,m',n multiplicities, original Q/P/H0 residual,
W1 and ε, and the complete original odd-e character projector are
kept; no cancellation, hard dyadic mask or new coefficient hypothesis
is used. Arbitrary complex W will later be ψ(z/Z)*the true Fourier
phase under a common Schwartz integral. -/
theorem parity_eventually_original_actual_fine_physical_full_odd_k_outer_eq_B633_sigma434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l uFine : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (Y : ℕ) (E V rho : ℝ) (signed : Bool)
        (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l uFine)
      let Ssource := fun m => parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
        d L E V band slot delta Y m K k
      let phi := parityOriginalHistoricalUngatedSourceToSigma434
      let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
        (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
      let Atom := fun i : (Σ z : ℕ, Σ mp : ℕ, ℕ) =>
        parityOriginalHistoricalB633CharacterFreeAtom434
          L rho 0 0 0 signed F0.residual F0.lo F0.hi
          i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
      (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K
            (parityOriginalHistoricalFullNEnvelope434 V) k,
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            W (phi m (e,q))
        else 0) =
      (∑m∈K,∑q∈Ssource m,
        (Atom (phi m q)*alpha m*star (alpha q.2.1)) * W (phi m q)) := by
  filter_upwards [parity_eventually_original_actual_fine_ungated_physical_coeff_eq_B633_zero_twist434
    S beta gamma Ck hS hbeta hgamma] with L hPoint
  refine ⟨hPoint.1,?_⟩
  intro prime l uFine hl hlow K k hk hkBound d band slot delta freq
    Y E V rho signed W
  classical
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l uFine)
  let Ssource := fun m => parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
    d L E V band slot delta Y m K k
  let phi := parityOriginalHistoricalUngatedSourceToSigma434
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let Atom := fun i : (Σ z : ℕ, Σ mp : ℕ, ℕ) =>
    parityOriginalHistoricalB633CharacterFreeAtom434
      L rho 0 0 0 signed F0.residual F0.lo F0.hi
      i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let WA : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ := fun i =>
    (Atom i*alpha i.2.2*star (alpha i.2.1))*W i
  have hElement (e m : ℕ) (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K) (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k) :
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
        W (phi m (e,q)) = WA (phi m (e,q)) := by
    have heOdd : Odd e := (Finset.mem_filter.mp he).2
    have hP := Finset.mem_filter.mp hq
    have hmp := Finset.mem_filter.mp (Finset.mem_product.mp hP.1).1
    have hNe : m≠q.1 := (Finset.mem_erase.mp hmp.1).1.symm
    have hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot delta Y e m q.1 q.2 := hP.2
    have hkq : parityOriginalHistoricalOffdiagK434 e m q.1=k := hmp.2
    have h := hPoint.2 prime l uFine hl hlow K k hk hkBound
      d band slot delta freq Y e m q.1 q.2 heOdd hNe hValid hkq rho signed
    dsimp only at h
    change parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1 =
        Atom (phi m (e,q))*alpha m*star (alpha q.1) at h
    rw [h]
    rfl
  have hPhysical :
      (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K
            (parityOriginalHistoricalFullNEnvelope434 V) k,
            parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
            W (phi m (e,q)) else 0) =
      (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K
            (parityOriginalHistoricalFullNEnvelope434 V) k,
            WA (phi m (e,q)) else 0) := by
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs
    · apply Finset.sum_congr rfl
      intro q hq
      exact hElement e m he hm q hq
    · rfl
  have hIndex := parity_original_full_psi_unfiltered_fixed_k_fubini_source_exact434
    d L E V band slot delta Y K k hk WA
  dsimp only at hPhysical hIndex ⊢
  calc
    _ = (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot delta Y e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k,
          WA (phi m (e,q)) else 0) := hPhysical
    _ = ∑m∈K,∑q∈Ssource m, WA (phi m q) := by
      simpa only [WA,phi,Ssource] using hIndex
    _ = ∑m∈K,∑q∈Ssource m,
          (Atom (phi m q)*alpha m*star (alpha q.2.1))*W (phi m q) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro q hq
      rfl
end Green64Analytic.Parity

end

end

/-! ## ActualFullPsiPhysicalBallEqBprime -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- LITERAL, UNFILTERED source: the full original Cauchy (4.10)
full-odd natural e,m,m',n physical B509 3D Fourier BALL at a genuine
(k,Z) is IDENTICAL to the already Parity(4.17)-estimated Bprime signal
with actual fine b629 alpha. This is proved by exact integral Fubini
and the native real original B509→B633 cofactor identity, with the
complete projected 2|k| character and all original Q/P/H0/W1/epsilon
inside the literal B633 atom. The original C∞ smooth psi(z/Z) and
eta_e*eta_n Schwartz kernel are unchanged, including zero-eta Fourier
ghosts. No Pfree-e gate, no single-chi cancellation or norm monotonicity.
The remaining global k/Z sum follows by finite sum_congr, not a new
TypeII or proxy/sieve theorem. -/
theorem parity_eventually_original_actual_fine_full_psi_physical_cell_ball_eq_Bprime434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l uFine : ℕ),
        2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (U E V Z T rho A : ℝ) (signed : Bool)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      let Y := Nat.ceil (6*U*V)
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l uFine)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let J := parityOriginalHistoricalFullNEnvelope434 V
      (∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          parityOriginalActualTruePsiPhysicalCellFourierBall434
            d L U E V Z hLw band slot delta freq rho alpha signed Y e m K J k
            buf (-Real.log A) (Real.log A) T hSmooth hSupport else 0) =
      parityOriginalActualBprimeFineLowfreqSignal434
        d L U E V hLw Z k band slot delta freq K alpha
        rho 0 0 0 T signed buf A hSmooth hSupport := by
  filter_upwards [parity_eventually_original_actual_fine_physical_full_odd_k_outer_eq_B633_sigma434
    S beta gamma Ck hS hbeta hgamma, eventually_ge_atTop (8:ℝ)] with L hSource hL
  refine ⟨hL,?_⟩
  intro hLw prime l uFine hl hLow K k hk hkBound d band slot delta freq
    U E V Z T rho A signed buf hSmooth hSupport
  classical
  let Y := Nat.ceil (6*U*V)
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l uFine)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let B : Set (EuclideanSpace ℝ (Fin 3)) := {ζ | ‖ζ‖≤T}
  let I : Type := Σ z : ℕ, Σ mp : ℕ, ℕ
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1 : DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let Atom : I → ℂ := fun i => parityOriginalHistoricalB633CharacterFreeAtom434
    L rho 0 0 0 signed F0.residual F0.lo F0.hi
    i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let sourceTerms : ℕ → Finset (ℕ×(ℕ×ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta Y m K k
  let phi := parityOriginalHistoricalUngatedSourceToSigma434
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let S0 : ℕ → ℕ → Finset (ℕ×ℕ) := fun e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k else ∅
  let W : ℕ → ℕ → (ℕ×ℕ) → ℂ := fun e m q =>
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z)
  let t : ℕ → ℕ → (ℕ×ℕ) → EuclideanSpace ℝ (Fin 3) := fun e m q =>
    parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m
      (fun q : ℕ×ℕ => q.1) (fun q : ℕ×ℕ => q.2) q
  let Wζ : EuclideanSpace ℝ (Fin 3) → I → ℂ := fun ζ i =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
    parityOriginal3DPhysicalLogFourierPhase434 ζ
      (parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1)
  have hFubini := parity_original_full_psi_physical_ball_two_outer_fubini434
    EF K S0 W t f T
  have hSourceWeight (ζ : EuclideanSpace ℝ (Fin 3)) :
    (∑e∈EF,∑m∈K,∑q∈S0 e m,
      W e m q*parityOriginal3DPhysicalLogFourierPhase434 ζ (t e m q)) =
    ∑m∈K,∑q∈sourceTerms m,
      (Atom (phi m q)*alpha m*star (alpha q.2.1))*Wζ ζ (phi m q) := by
    have hExact := hSource.2 prime l uFine hl hLow K k hk hkBound
      d band slot delta freq Y E V rho signed (Wζ ζ)
    dsimp only at hExact
    calc
      _ = ∑e∈EF,∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
            ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
              d L band slot delta Y e m K J k,
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
                Wζ ζ (phi m (e,q)) else 0 := by
                apply Finset.sum_congr rfl
                intro e he
                apply Finset.sum_congr rfl
                intro m hm
                by_cases hK : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
                · simp only [S0,hK,ite_true]
                  apply Finset.sum_congr rfl
                  intro q hq
                  dsimp [W,t,Wζ,phi,
                    parityOriginalHistoricalPhysicalFourierEventTriple434,
                    parityOriginalHistoricalUngatedSourceToSigma434]
                  ring
                · simp [S0,hK]
      _ = ∑m∈K,∑q∈sourceTerms m,
          (Atom (phi m q)*alpha m*star (alpha q.2.1))*Wζ ζ (phi m q) := by
          simpa only [EF,J,alpha,sourceTerms,phi,F0,Atom] using hExact
  have hInput : (∑e∈EF,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        parityOriginalActualTruePsiPhysicalCellFourierBall434
          d L U E V Z hLw band slot delta freq rho alpha signed Y e m K J k
          buf (-Real.log A) (Real.log A) T hSmooth hSupport else 0) =
    (∑e∈EF,∑m∈K,
      ∫ζ in B,parityOriginal3DPhysicalFiniteTwistedSource434
        (S0 e m) (W e m) (t e m) f ζ) := by
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hK : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · simp only [S0,hK,ite_true]
      rfl
    · simp [S0,hK,parityOriginal3DPhysicalFiniteTwistedSource434]
  dsimp only
  calc
    _ = ∑e∈EF,∑m∈K,
       ∫ζ in B,parityOriginal3DPhysicalFiniteTwistedSource434
         (S0 e m) (W e m) (t e m) f ζ := hInput
    _ = ∫ζ in B,(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
       (∑e∈EF,∑m∈K,∑q∈S0 e m,
         W e m q*parityOriginal3DPhysicalLogFourierPhase434 ζ (t e m q)) := hFubini
    _ = ∫ζ in B,(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
       (∑m∈K,∑q∈sourceTerms m,
         (Atom (phi m q)*alpha m*star (alpha q.2.1))*Wζ ζ (phi m q)) := by
       apply integral_congr_ae
       filter_upwards [] with ζ
       rw [hSourceWeight ζ]
    _ = parityOriginalActualBprimeFineLowfreqSignal434
         d L U E V hLw Z k band slot delta freq K alpha
         rho 0 0 0 T signed buf A hSmooth hSupport := by
         unfold parityOriginalActualBprimeFineLowfreqSignal434
         apply integral_congr_ae
         filter_upwards [] with ζ
         congr 1
         apply Finset.sum_congr rfl
         intro m hm
         apply Finset.sum_congr rfl
         intro q hq
         dsimp only [Wζ,Atom,phi,
           parityOriginalHistoricalUngatedSourceToSigma434]
         ring
end Green64Analytic.Parity

end

end

/-! ## ActualFullPsiGlobalBallEqBprime -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Full all-odd original Parity(4.10) physical LOW-FREQUENCY BALL,
with all actual signed k and both genuine smooth-psi dyadic Z,
is EXACTLY the Bprime source-image Fourier-ball OUTER sum already
bounded through unrestricted signed Parity (4.17). Real b629 prime/rough
fine alpha is preserved. The original physical Ybox=ceil6UV is used;
all χ are projected before source-image restriction, the actual
eta_e/eta_n Schwartz kernel remains unchanged and no zero-eta
complex-subsums are dropped. This is an exact equality at ONE
reserved band/slot, ONE fine interval and Q allocation/frequency;
no full TypeII(4.2) assertion or full external family sum. -/
theorem parity_eventually_original_actual_fine_full_psi_global_ball_eq_Bprime434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l uFine : ℕ),
        2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (KS : Finset ℤ),
        (∀k∈KS,k≠0 ∧ (k.natAbs:ℝ)≤L^Ck) →
      ∀ (ZS : Finset ℕ)
        (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (U E V T rho A : ℝ) (signed : Bool)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      let Y := Nat.ceil (6*U*V)
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l uFine)
      parityOriginalActualTruePsiGlobalPhysicalBall434
        d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) T hSmooth hSupport =
      ∑k∈KS,∑Z∈ZS,
        parityOriginalActualBprimeFineLowfreqSignal434
          d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
          rho 0 0 0 T signed buf A hSmooth hSupport := by
  filter_upwards [parity_eventually_original_actual_fine_full_psi_physical_cell_ball_eq_Bprime434
    S beta gamma Ck hS hbeta hgamma] with L hPoint
  refine ⟨hPoint.1,?_⟩
  intro hLw prime l uFine hl hlow K KS hKS ZS d band slot delta freq
    U E V T rho A signed buf hSmooth hSupport
  classical
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l uFine)
  let Y := Nat.ceil (6*U*V)
  dsimp only
  unfold parityOriginalActualTruePsiGlobalPhysicalBall434
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro Z hZ
  have hk0 := hKS k hk
  have hCell := hPoint.2 hLw prime l uFine hl hlow K k hk0.1 hk0.2
    d band slot delta freq U E V (Z:ℝ) T rho A signed buf hSmooth hSupport
  dsimp only at hCell ⊢
  exact hCell
end Green64Analytic.Parity

end

end

/-! ## ActualTrueFullPsiBallSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- ACTUAL original Parity (4.10) FULL, UNFILTERED physical C∞ smooth-psi
3D Fourier ball has arbitrarily deep inverse-log saving after the
correct k/Z outer is summed for the actual b629 fine prime/rough
coefficient. It is the same BALL on the RHS of the true positive
Cauchy precursor with BOTH separately paid zero-eta ghosts.
The source no-u-cap Ybox=ceil(6UV), genuine signed k, both smooth
psi neighboring dyads, entire odd-e source including P-bearing e,
full projected modulus 2|k|, H0/W1/epsilon and actual 3D eta source
are retained. One reserved Q band/slot and one b629 fine interval
remain fixed but arbitrary. This is NOT yet the full original TypeII.
J,B,S are chosen before L with the inherited Parity(4.17) accuracy. -/
theorem parity_eventually_original_actual_true_full_psi_physical_ball_any_log434
    (jQ : ℕ) (Agoal D C0 Cf beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+(K0+89)+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        U*V≤Cbox*Real.exp L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖parityOriginalActualTruePsiGlobalPhysicalBall434
          d L U E V hLw band slot delta freq rho alpha signed Ybox K KS
          (parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS)
          buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_true_physical_kZ_any_log434
      jQ Agoal D C0 Cf beta gamma K0 Cbox A R
      hD hPrecision hCf hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  have hSpos : 0<S := by linarith
  have hEq := parity_eventually_original_actual_fine_full_psi_global_ball_eq_Bprime434
    S beta gamma (K0+89) hSpos hbeta hgamma
  have hSource := parity_eventually_original_actual_full_odd_smooth_source_kZ_inputs434
    K0 Cbox hK0 hCbox
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hMain,hEq,hSource] with L hMainL hEqL hSourceL
  rcases hMainL with ⟨hL32,hL6,hFamily,hReserved,hMainRest⟩
  rcases hSourceL with ⟨hLcap,hLarge,hYpos,hYhi,hYlog,hSourceRest⟩
  refine ⟨hL32,hL6,hFamily,hReserved,?_⟩
  intro hLw hFamily0 band hBand slot delta freq rho U E V T signed
    hU hEpos hV hUV hEscale hT hrho
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hGeo := hSourceRest d band slot delta hLw U V E
    hU hV hUV hUVhi hEscale K hDyadStrict
  dsimp only at hGeo
  rcases hGeo with ⟨hKS,hZS,hZwin,hShift⟩
  have hKS0 : ∀k∈KS,k≠0 ∧ (k.natAbs:ℝ)≤L^(K0+89) := by
    intro k hk
    exact ⟨(hKS k hk).1,(hKS k hk).2.2⟩
  have hFull := hEqL.2 hLw prime lFine uFine hl hFineLow K KS hKS0 ZSmooth
    d band slot delta freq U E V T rho A signed buf hSmooth hSupport
  have hZero : |(0:ℝ)|≤L^C0 := by
    simp only [abs_zero]
    exact (Real.rpow_pos_of_pos (by linarith : 0<L) _).le
  have hOld := hMainRest hLw hFamily0 band hBand slot delta freq
    rho 0 0 0 U E V T signed hU hEpos hV hUV hEscale hT
    hrho hZero hZero hZero
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  dsimp only at hFull hOld ⊢
  rw [hFull]
  exact hOld
end Green64Analytic.Parity

end

end

/-! ## TruePsiActualFineFixedKZBallJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- EXACT ORIGINAL all-odd post-Cauchy physical B509 three-dimensional
Fourier BALL over *all* natural e,m,m',n for a fixed signed k and
smooth dyadic Z equals the original source Bprime 4.17-ready ball.
The source m,m' coefficient is the native b629 fine alpha; its
B509->B633 equality and WHOLE q=2|k| character projector have
already been proved on the genuine ungated physical support.
The original H0/W1/epsilon and smooth psi are literal; the three
extra cofactor Fourier powers are zero, while the true 2*pi*zeta
physical phase is preserved. This is a fixed k,Z source identity,
not a signed-subsum inequality, TypeII (4.2), or an assumption on
arbitrary alpha. -/
theorem parity_eventually_original_actual_fine_true_psi_fixed_kZ_ball_eq_Bprime434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l uFine : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (U E V Z T rho A : ℝ) (signed : Bool)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l uFine)
      let Y := Nat.ceil (6*U*V)
      let EF := parityOriginalHistoricalFullOddEEnvelope434 E
      let Nfull := parityOriginalHistoricalFullNEnvelope434 V
      (∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          parityOriginalActualTruePsiPhysicalCellFourierBall434
            d L U E V Z hLw band slot delta freq rho alpha signed
            Y e m K Nfull k buf (-Real.log A) (Real.log A) T hSmooth hSupport
        else 0) =
        parityOriginalActualBprimeFineLowfreqSignal434
          d L U E V hLw Z k band slot delta freq K alpha
          rho 0 0 0 T signed buf A hSmooth hSupport := by
  filter_upwards [parity_eventually_original_actual_fine_physical_full_odd_k_outer_eq_B633_sigma434
    S beta gamma Ck hS hbeta hgamma, eventually_ge_atTop (8:ℝ)]
    with L hOuter hL
  refine ⟨hL,?_⟩
  intro hLw prime l uFine hl hlow K k hk hkBound d band slot delta freq
    U E V Z T rho A signed buf hSmooth hSupport
  classical
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l uFine)
  let Y := Nat.ceil (6*U*V)
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let Nfull := parityOriginalHistoricalFullNEnvelope434 V
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let Ssrc : ℕ → Finset (ℕ × (ℕ × ℕ)) := fun m =>
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta Y m K k
  let phi := parityOriginalHistoricalUngatedSourceToSigma434
  let F0 := sourceNativePrimeCore 20 d L band slot delta freq K alpha
    (2*k.natAbs) (1:DirichletCharacter ℂ (2*k.natAbs)) 0 0
  let Atom : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ := fun i =>
    parityOriginalHistoricalB633CharacterFreeAtom434
      L rho 0 0 0 signed F0.residual F0.lo F0.hi
      i.2.2 i.2.1 i.1 (((i.1:ℤ)+2*k).toNat)
  let Events : ℕ → ℕ → Finset (ℕ×ℕ) := fun e m =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K Nfull k
  let S0 : ℕ → ℕ → Finset (ℕ×ℕ) := fun e m =>
    if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      Events e m else ∅
  let W0 : ℕ → ℕ → (ℕ×ℕ) → ℂ := fun e m q =>
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z)
  let t0 : ℕ → ℕ → (ℕ×ℕ) → EuclideanSpace ℝ (Fin 3) := fun e m q =>
    parityOriginalHistoricalPhysicalFourierEventTriple434
      U Z e m (fun p : ℕ×ℕ => p.1) (fun p : ℕ×ℕ => p.2) q
  let Wsigma : (EuclideanSpace ℝ (Fin 3)) → (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ :=
    fun ζ i =>
      parityOriginalHistoricalDyadicSmoothPsi434 ((i.1:ℝ)/Z) *
      parityOriginal3DPhysicalLogFourierPhase434 ζ
        (parityOriginalHistoricalRealLogTriple434 U Z i.2.2 i.2.1 i.1)
  have hFubini := parity_original_full_psi_physical_ball_two_outer_fubini434
    EF K S0 W0 t0 f T
  have hLeft : (∑e∈EF,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        parityOriginalActualTruePsiPhysicalCellFourierBall434
          d L U E V Z hLw band slot delta freq rho alpha signed
          Y e m K Nfull k buf (-Real.log A) (Real.log A) T hSmooth hSupport
      else 0) =
      ∑e∈EF,∑m∈K,
        ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (S0 e m) (W0 e m) (t0 e m) f ζ := by
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hGate : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · simp only [S0,hGate,ite_true]
      rfl
    · simp [hGate,S0,parityOriginal3DPhysicalFiniteTwistedSource434]
  have hIndex (ζ : EuclideanSpace ℝ (Fin 3)) :
    (∑e∈EF,∑m∈K,∑q∈S0 e m,
       W0 e m q*parityOriginal3DPhysicalLogFourierPhase434 ζ (t0 e m q)) =
    (∑m∈K,∑q∈Ssrc m,
       (Atom (phi m q)*alpha m*star (alpha q.2.1))*Wsigma ζ (phi m q)) := by
    have hOuterZ := hOuter.2 prime l uFine hl hlow K k hk hkBound
      d band slot delta freq Y E V rho signed (Wsigma ζ)
    dsimp only at hOuterZ
    calc
      _ = (∑e∈EF,∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
            ∑q∈Events e m,
              parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
                d L band slot delta freq rho alpha signed Y e q.2 m q.1 *
              Wsigma ζ (phi m (e,q)) else 0) := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro m hm
        by_cases hGate : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
        · simp only [S0,hGate,ite_true]
          apply Finset.sum_congr rfl
          intro q hq
          dsimp [W0,t0,Wsigma,phi,
            parityOriginalHistoricalPhysicalFourierEventTriple434,
            parityOriginalHistoricalUngatedSourceToSigma434]
          ring
        · simp [S0,hGate]
      _ = (∑m∈K,∑q∈Ssrc m,
          (Atom (phi m q)*alpha m*star (alpha q.2.1))*Wsigma ζ (phi m q)) := by
        simpa only [alpha,Y,EF,Nfull,Events,Atom,phi,Ssrc] using hOuterZ
  dsimp only at ⊢
  calc
    _ = ∑e∈EF,∑m∈K,
        ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (S0 e m) (W0 e m) (t0 e m) f ζ := hLeft
    _ = ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
          (∑e∈EF,∑m∈K,∑q∈S0 e m,
            W0 e m q*parityOriginal3DPhysicalLogFourierPhase434 ζ (t0 e m q)) := hFubini
    _ = parityOriginalActualBprimeFineLowfreqSignal434
          d L U E V hLw Z k band slot delta freq K alpha
          rho 0 0 0 T signed buf A hSmooth hSupport := by
      unfold parityOriginalActualBprimeFineLowfreqSignal434
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with ζ
      rw [hIndex ζ]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro q hq
      dsimp [Wsigma,phi,parityOriginalHistoricalUngatedSourceToSigma434,Atom]
      simp only [div_eq_mul_inv]
      ring
end Green64Analytic.Parity

end

end

/-! ## TruePsiActualFineGlobalBallJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The literal SOURCE full-odd h=-2 Parity(4.10) low-frequency
3D Fourier ball (with ALL original natural e,n,m,m' and genuine
signed k, smooth-psi Z outer) is EXACTLY the sum of actual fine
b629 Bprime (4.17)-ready Fourier-ball signals. The equality is
complex, before taking any norm. All underlying source H0/W1,
epsilon, full 2|k| character projector and Schwartz phases are
retained; it uses the preceding UNGATED pair/atom theorem rather
than the old P-free-e gated equality. No independent correlation
saving or artificial hard Z mask appears. -/
theorem parity_eventually_original_actual_fine_true_psi_global_ball_eq_Bprime434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l uFine : ℕ),
        2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ),
        (∀k∈KS,k≠0 ∧ (k.natAbs:ℝ)≤L^Ck) →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (U E V T rho A : ℝ) (signed : Bool)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l uFine)
      let Y := Nat.ceil (6*U*V)
      parityOriginalActualTruePsiGlobalPhysicalBall434
        d L U E V hLw band slot delta freq rho alpha signed Y K KS ZS
        buf (-Real.log A) (Real.log A) T hSmooth hSupport =
      ∑k∈KS,∑Z∈ZS,
        parityOriginalActualBprimeFineLowfreqSignal434
          d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
          rho 0 0 0 T signed buf A hSmooth hSupport := by
  filter_upwards [parity_eventually_original_actual_fine_true_psi_fixed_kZ_ball_eq_Bprime434
    S beta gamma Ck hS hbeta hgamma] with L hFixed
  refine ⟨hFixed.1,?_⟩
  intro hLw prime l uFine hl hlow K KS ZS hKS d band slot delta freq
    U E V T rho A signed buf hSmooth hSupport
  classical
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l uFine)
  let Y := Nat.ceil (6*U*V)
  let Nfull := parityOriginalHistoricalFullNEnvelope434 V
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  unfold parityOriginalActualTruePsiGlobalPhysicalBall434
  dsimp only
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro Z hZ
  have hCell := hFixed.2 hLw prime l uFine hl hlow K k
    (hKS k hk).1 (hKS k hk).2 d band slot delta freq
    U E V (Z:ℝ) T rho A signed buf hSmooth hSupport
  dsimp only at hCell ⊢
  exact hCell
end Green64Analytic.Parity

end

end

/-! ## TruePsiActualFineGlobalBallAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- ACTUAL Parity (4.10) full-odd Cauchy PHYSICAL smooth-psi k×Z
3D low-frequency Fourier ball has arbitrary source-log saving
for the true b629 fine alpha, one original Q band/slot and Q-allocation
family. The previously proven unrestricted signed Parity(4.17) saving,
two paid B633 ghosts and 3D source Schwartz moments are all imported
through the true original Bprime source ball. The complete actual
post-Cauchy natural e,n,m,m',z sum is identified with THAT ball
before taking a complex norm; no Pfree-e or sharp binary-Z gate.

Here the three extra outer cofactor frequencies are exactly zero,
as required BEFORE genuine Fourier separation; shifted frequencies
xi_j+2*pi*zeta_j remain inside the fixed-k,Z Parity(4.17) result.
J,B,S and the single Fourier T=L^Cf are selected BEFORE L.
This remains one original fine interval and reserved Q band/slot,
NOT Parity's complete TypeII (4.2) or prime/sieve extraction. -/
theorem parity_eventually_original_actual_true_psi_full_physical_ball_any_log434
    (jQ : ℕ) (Agoal D C0 Cf beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+(K0+89)+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
          T=L^Cf → |rho|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        U*V≤Cbox*Real.exp L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖parityOriginalActualTruePsiGlobalPhysicalBall434
          d L U E V hLw band slot delta freq rho alpha signed Ybox K KS
          (parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS)
          buf (-Real.log A) (Real.log A) T hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hSave⟩ :=
    parity_eventually_original_actual_Bprime_true_physical_kZ_any_log434
      jQ Agoal D C0 Cf beta gamma K0 Cbox A R
      hD hPrecision hCf hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  have hSpos : 0<S := by
    have hB : (0:ℝ)≤B := Nat.cast_nonneg _
    linarith
  have hExact := parity_eventually_original_actual_fine_true_psi_global_ball_eq_Bprime434
    S beta gamma (K0+89) hSpos hbeta hgamma
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hSave,hExact] with L hSaveL hExactL
  refine ⟨hSaveL.1,hSaveL.2.1,hSaveL.2.2.1,hSaveL.2.2.2.1,?_⟩
  intro hLw hFamily band hBand slot delta freq rho U E V T signed
    hU hEpos hV hUV hEscale hT hrho
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  have hK : ∀k∈KS,k≠0 ∧ (k.natAbs:ℝ)≤L^(K0+89) := by
    intro k hk
    have hh := parity_original_full_odd_smoothed_k_genuine_polylog434
      d L U E V K0 hLw hU hEscale band slot delta Ybox K hDyadStrict k hk
    exact ⟨hh.1,hh.2.1.le⟩
  have hIdentity := hExactL.2 hLw prime lFine uFine hl hFineLow
    K KS ZSmooth hK d band slot delta freq U E V T rho A signed
    buf hSmooth hSupport
  have hZero : |(0:ℝ)|≤L^C0 := by
    simpa using (Real.rpow_pos_of_pos (by linarith : 0<L) C0).le
  have hBound := hSaveL.2.2.2.2 hLw hFamily band hBand slot delta freq
    rho 0 0 0 U E V T signed hU hEpos hV hUV hEscale hT
    hrho hZero hZero hZero
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  dsimp only at hIdentity hBound ⊢
  rw [hIdentity]
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## ZeroEtaGhostMassMonotone -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The true original positive physical coefficient ℓ1 mass of the
η-active source is at most that of its FULL original source carrier.
Unlike a complex signed Fourier sum, the positive mass IS monotone
under genuine pre-Fourier source filtering. -/
theorem parity_original_actual_3d_coefficient_mass_eta_filter_le434
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : ι → Prop)
    [DecidablePred p] (W : ι → ℂ) :
    parityOriginal3DPhysicalFiniteCoefficientMass434 (S.filter p) W ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W := by
  unfold parityOriginal3DPhysicalFiniteCoefficientMass434
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset p S)
    (fun i hi hnot => norm_nonneg _)

/-- The actual source-defined 3D Schwartz Fourier moment is positive
for EVERY H and real 3D Schwartz input, since it bounds a genuine
Lebesgue integral of a nonnegative weighted Fourier density. -/
theorem parity_original_actual_3d_source_moment_finite_nonneg434
    (H : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) :
    0 ≤ parityOriginal3DSourceMomentFiniteBudget434 H f := by
  have hReal := parity_original_real_3d_fourier_moment_le_original_source_finite434 H f
  have hNonneg : 0≤(∫ ξ : EuclideanSpace ℝ (Fin 3),
      ‖ξ‖^H * ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ‖) := by
    apply integral_nonneg
    intro ξ
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  exact hNonneg.trans hReal

/-- Physically filtered source η-active zero-η Fourier ghosts have
NO larger positive Schwartz moment cost than the FULL source.
The positive denominator T^H remains unchanged for all physical
indices: Fourier cutoff T is chosen BEFORE the sum, not per e/n. -/
theorem parity_original_actual_3d_eta_filtered_moment_tail_le_full434
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (p : ι → Prop)
    [DecidablePred p] (W : ι → ℂ)
    (H : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (T : ℝ) (hT : 0<T) :
    parityOriginal3DPhysicalFiniteCoefficientMass434 (S.filter p) W *
      (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
      (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  have hm : 0≤parityOriginal3DSourceMomentFiniteBudget434 H f :=
    parity_original_actual_3d_source_moment_finite_nonneg434 H f
  have hq : 0≤parityOriginal3DSourceMomentFiniteBudget434 H f/T^H :=
    div_nonneg hm (pow_nonneg hT.le _)
  exact mul_le_mul_of_nonneg_right
    (parity_original_actual_3d_coefficient_mass_eta_filter_le434 S p W) hq
end Green64Analytic.Parity

end

end

