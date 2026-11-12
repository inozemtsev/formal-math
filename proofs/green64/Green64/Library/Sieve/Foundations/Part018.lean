module

public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part009
public import Green64.Library.Sieve.Foundations.Part008
public import Green64.Library.Weights.Part005

@[expose] public section

/-!
# Sieve / Foundations / Part018

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalSignedHistoricalEWindowAudit -/

section

open Green64Analytic.Parity

end

/-! ## OriginalSignedWindowPsiMellinBilinear -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Original signed e-window Parity (4.7) *post-Ψ-Mellin* h=-2 physical
B' at ONE true original f0/f1 Fourier frequency ξ. Selected e is
outermost; Ψ has been removed from the inner e,n,m,v convolution and
replaced by its actual smooth logarithmic Fourier transform at rho=2πs.
No unproved sigma in H0 and no character square estimate. -/
def parityOriginalSignedWindowPsiMellinBilinearAtXi434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) : ℂ :=
  ∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
    L Psi hSmooth hSupport s *
      (∑ e ∈ parityOriginalSignedWindowHEFirstSupport434 d L E band slot,
        ∑ u ∈ Finset.Ioc 0 Y,
          parityOriginalSignedWindowHAtE434 d L E u signed
            band slot K α 1 (1 : DirichletCharacter ℂ 1) 0 0
            (2*Real.pi*s) ξ e *
          (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α z.1*β z.2))

/-- TRUE signed original Parity Ψ(u/x) Mellin Fubini for the COMPLETE
h=-2 α_mβ_n bilinear SOURCE with historical selected-e and physical
H0(vStar), at every original fixed ξ. Full source 20! Q/P labels,
W1 ε sign, actual u=mn-2, and exact 2π convention survive.

The sole analytic requirements are actual smooth compact-supported Ψ;
finite h=-2 factors are not smoothed or replaced, and Schwartz
integrability is explicitly proved uniformly in each finite term. -/
theorem parity_original_signed_window_psi_mellin_hminus2_e_first_exact434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) :
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalSignedWindowSourceMellinHAtU434 d L E u signed
        band slot K α 1 (1 : DirichletCharacter ℂ 1) 0 0 0 ξ *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)) =
    parityOriginalSignedWindowPsiMellinBilinearAtXi434
      d L E band slot ξ Psi hSmooth hSupport K J α β signed Y := by
  let U := Finset.Ioc 0 Y
  let fhat : ℝ → ℂ := fun s =>
    parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s
  let H : ℕ → ℝ → ℂ := fun u rho =>
    parityOriginalSignedWindowSourceMellinHAtU434
      d L E u signed band slot K α 1 (1 : DirichletCharacter ℂ 1) 0 0 rho ξ
  let M := parityOriginalSignedWindowHEFirstSupport434 d L E band slot
  let F : ℕ → ℕ → ℝ → ℂ := fun e u rho =>
    parityOriginalSignedWindowHAtE434 d L E u signed band slot
      K α 1 (1 : DirichletCharacter ℂ 1) 0 0 rho ξ e
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α z.1*β z.2
  have hPos (u : ℕ) (hu : u ∈ U) : 0 < u := (Finset.mem_Ioc.mp hu).1
  have hInt (u : ℕ) (hu : u ∈ U) : Integrable
      (fun s : ℝ => (fhat s * H u (2*Real.pi*s))*B u) :=
    (parity_original_signed_window_Psi_Mellin_H_integrable434
      d L E hL hd u (hPos u hu) signed band slot K α 1
      (1 : DirichletCharacter ℂ 1) 0 0 ξ Psi hSmooth hSupport).mul_const _
  have hEq (u : ℕ) (hu : u ∈ U) :
      ((H u 0 * (Psi ((u:ℝ)/Real.exp L):ℂ))*B u) =
      (∫ s : ℝ, fhat s * H u (2*Real.pi*s)) * B u := by
    have h := parity_original_signed_window_Psi_Mellin_H_exact434
      d L E hL hd u (hPos u hu) signed band slot K α 1
      (1 : DirichletCharacter ℂ 1) 0 0 ξ Psi hSmooth hSupport
    change ((Psi ((u:ℝ)/Real.exp L):ℂ)*H u 0) =
      ∫ s : ℝ, fhat s * H u (2*Real.pi*s) at h
    rw [mul_comm (H u 0),h]
  have hPoint (s : ℝ) :
      (∑ u ∈ U, (fhat s * H u (2*Real.pi*s))*B u) =
        fhat s * (∑ e ∈ M, ∑ u ∈ U, F e u (2*Real.pi*s)*B u) := by
    calc
      _ = fhat s * (∑ u ∈ U, H u (2*Real.pi*s)*B u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        ring
      _ = fhat s * (∑ u ∈ U,
            (∑ e ∈ M, F e u (2*Real.pi*s))*B u) := by
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        exact congrArg (fun c : ℂ => c * B u)
          (parity_original_signed_window_H_integrand_eq_e_first434
            d L E u signed band slot K α 1 (1 : DirichletCharacter ℂ 1)
            0 0 (2*Real.pi*s) ξ)
      _ = fhat s * (∑ u ∈ U, ∑ e ∈ M,
            F e u (2*Real.pi*s)*B u) := by
        congr 1
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.sum_mul]
      _ = _ := by rw [Finset.sum_comm]
  unfold parityOriginalSignedWindowPsiMellinBilinearAtXi434
  change (∑ u ∈ U, (H u 0 * (Psi ((u:ℝ)/Real.exp L):ℂ))*B u) =
      ∫ s : ℝ, fhat s *
        (∑ e ∈ M, ∑ u ∈ U, F e u (2*Real.pi*s)*B u)
  calc
    _ = ∑ u ∈ U, (∫ s : ℝ, fhat s * H u (2*Real.pi*s))*B u := by
      exact Finset.sum_congr rfl hEq
    _ = ∑ u ∈ U, ∫ s : ℝ, (fhat s * H u (2*Real.pi*s))*B u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [integral_mul_const]
    _ = ∫ s : ℝ, ∑ u ∈ U, (fhat s * H u (2*Real.pi*s))*B u :=
      (integral_finsetSum U hInt).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with s
      exact hPoint s
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowPsiPostIntegrated -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Actual original Parity (4.7) post-Ψ-Mellin signed physical B':
REAL outer B590 f0/f1 N-dimensional Lebesgue Fourier BOX, REAL
inner Schwartz Mellin s integral with EXACT 2π normalization;
inside lies selected e-FIRST, complete native labelled Q/P factorial,
ε=1/E parity and physical v-side W1(v)H_0(vStar) h=-2 alpha-beta.
The original Ψ has been fully removed from the B' inner sum. -/
def parityOriginalSignedWindowPsiPostIntegrated434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    parityOriginalSignedWindowPsiMellinBilinearAtXi434
      d L E band slot ξ Psi hSmooth hSupport K J α β signed Y
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- Full SOURCE actual original signed e-first Parity (4.7) Ψ Mellin
reduction through BOTH real Lebesgue integrations, at rho=0 on the
untransformed source: after the genuine logarithmic Mellin inversion,
Ψ(u/x) disappears from the e-first B' inner sum and becomes exactly
its Schwartz Fourier kernel at rho=2πs, with no extra normalization,
no change of full Q/P factorial or source physical H0. -/
theorem parity_original_signed_window_e_first_H_box_eq_post_Psi_Mellin434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearMellinWindowHEFirst434
      d L E band slot Psi K J α β signed 0 Y T =
    parityOriginalSignedWindowPsiPostIntegrated434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T := by
  have hEfirst := parity_original_signed_selected_e_H_box_eq_e_first434
    d L E band slot Psi K J α β signed 0 Y T
  rw [←hEfirst]
  unfold parityOriginalShiftTwoSignedBilinearMellinSelectedEHBox434
    parityOriginalSignedWindowPsiPostIntegrated434
  apply integral_congr_ae
  filter_upwards [] with ξ
  exact parity_original_signed_window_psi_mellin_hminus2_e_first_exact434
    d L E hL hd band slot ξ Psi hSmooth hSupport K J α β signed Y
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedWindowPsiTerminal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Original Ψ supported [1,2] automatically satisfies the real
Schwartz-Mellin cutoff support [1/64,64]; not a new hypothesis. -/
theorem parity_original_Psi_window_to_Schwartz_support434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2) :
    ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64 := by
  intro t ht
  have hne : Psi t ≠ 0 := by
    intro hz
    apply ht
    simp [hz]
  have hm : t ∈ Function.support Psi := by
    simpa only [Function.mem_support] using hne
  have hs := hSupport hm
  exact ⟨by linarith [hs.1],by linarith [hs.2]⟩

/-- ORIGINAL full 20!-labelled Parity SOURCE alpha_m beta_n signed
ε=1 or ε=E h=-2 (mn=u+2) sum is O_A(x L^-A)-close to the EXACT
post-Ψ-Mellin Parity (4.7) e-FIRST B' physical integral, individually.

This includes: historical E L^-88 <= e <= E, every true B590 f0/f1
Fourier history, actual Q/P factorial and native B509 reserved H_0,
true W1(P,v)epsilon(v), full smooth Ψ(u/x), exact Fourier 2π,
two real Lebesgue integrals and all actual source alpha-beta bounds.
Neither the odd-projector difference nor a fixed P cap is used to
infer either signed branch. The original SOURCE reserved sigma is
still zero. This is not the all-character Parity (4.17) bound, full Type II,
proxy/sieve or Green64. -/
theorem parity_eventually_original_signed_hminus2_source_to_post_Psi_Mellin_Bprime_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
        (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ))),
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β signed 0
          ⌊2*Real.exp L⌋₊ -
        parityOriginalSignedWindowPsiPostIntegrated434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
          K J α β signed ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_hminus2_source_to_e_first_physical_H_box_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hSmooth hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  have hSchwartzSupport := parity_original_Psi_window_to_Schwartz_support434
    Psi hSupport
  have hEq := parity_original_signed_window_e_first_H_box_eq_post_Psi_Mellin434
    (sourceOriginalLiteralDepth 20 L) L E (by nlinarith [h.1]) rfl
    band slot Psi hSmooth hSchwartzSupport K J α β signed
    ⌊2*Real.exp L⌋₊ L
  rw [←hEq]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed 0
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedIntrinsicPsiPostIntegrated -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Genuine historical B'(4.7) for both independently signed branches,
at fixed original multi-Fourier frequency ξ, AFTER the true Ψ(u/x)
logarithmic Fourier/Mellin inversion. Its internal a_v is the intrinsic
alpha-independent W1(v) epsilon(v) H_0(vStar), while a_e(e) is outside
the original e-fibre. Every original r20 Q/P source factorial survives. -/
def parityOriginalSignedIntrinsicPsiBprimeAtXi434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) : ℂ :=
  ∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
    L Psi hSmooth hSupport s *
      (∑ u ∈ Finset.Ioc 0 Y,
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) ξ *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2))

/-- Fully postintegrated ORIGINAL Parity B' with a_e(e) physically
independent of v and a_v(v) independent of α_m and β_n. Both
Lebesgue integrals are real, the actual Mellin rho is 2πs, the
original reserved sigma remains the source-derived 0. -/
def parityOriginalSignedIntrinsicPsiPostIntegrated434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    parityOriginalSignedIntrinsicPsiBprimeAtXi434
      d L E band slot ξ Psi hSmooth hSupport K J α β signed Y
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- Exact compatibility of the independently proven historical Ψ
Mellin Fubini with the new intrinsic a_e × a_v source identity.
Importantly this preserves the original 2π Fourier convention and does
not push a nonzero phase onto the reserved prime without a source proof. -/
theorem parity_original_signed_intrinsic_Psi_Bprime_eq_source_postintegrated434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    parityOriginalSignedWindowPsiPostIntegrated434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T =
    parityOriginalSignedIntrinsicPsiPostIntegrated434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T := by
  unfold parityOriginalSignedWindowPsiPostIntegrated434
    parityOriginalSignedIntrinsicPsiPostIntegrated434
  apply integral_congr_ae
  filter_upwards [] with ξ
  unfold parityOriginalSignedWindowPsiMellinBilinearAtXi434
    parityOriginalSignedIntrinsicPsiBprimeAtXi434
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  let M := parityOriginalSignedWindowHEFirstSupport434 d L E band slot
  let U := Finset.Ioc 0 Y
  let F : ℕ → ℕ → ℂ := fun e u =>
    parityOriginalSignedWindowHAtE434 d L E u signed band slot K α 1
      (1 : DirichletCharacter ℂ 1) 0 0 (2*Real.pi*s) ξ e
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      α z.1*β z.2
  have hOne (u : ℕ) (hu : u ∈ U) :
      (∑ e ∈ M, F e u) =
      parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot (2*Real.pi*s) ξ := by
    have huPos : u ≠ 0 := (Finset.mem_Ioc.mp hu).1.ne'
    calc
      _ = parityOriginalSignedWindowSourceMellinHAtU434
            d L E u signed band slot K α 1 (1 : DirichletCharacter ℂ 1)
            0 0 (2*Real.pi*s) ξ :=
        (parity_original_signed_window_H_integrand_eq_e_first434
          d L E u signed band slot K α 1 (1 : DirichletCharacter ℂ 1)
          0 0 (2*Real.pi*s) ξ).symm
      _ = _ := parity_original_signed_window_mellin_H_eq_intrinsic_e_first434
        d L E hL hd u huPos signed band slot K α 1
        (1 : DirichletCharacter ℂ 1) 0 0 (2*Real.pi*s) ξ
  change (∑ e ∈ M, ∑ u ∈ U, F e u * B u) =
      ∑ u ∈ U,
        parityOriginalSignedIntrinsicEFirstFullAtU434
          d L E u signed band slot (2*Real.pi*s) ξ * B u
  calc
    _ = ∑ u ∈ U, ∑ e ∈ M, F e u * B u := Finset.sum_comm
    _ = ∑ u ∈ U, (∑ e ∈ M, F e u) * B u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hOne u hu]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedIntrinsicPsiAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- TRUE source-facing signed ε=1/E Parity(4.7) post-Ψ-Mellin
intrinsic B' all-log estimate: the actual original 20! labelled
h=-2 α_mβ_n sum, with the original full P/W1/E parity, true E-window,
beta/4 physical Rankin and complete B590 Fourier tail, differs by
O_A(exp(L)L^-A) from the full real 2π Mellin and B590 BOX integrals
of e-FIRST a_e(e) times the intrinsic physical a_v(v), independent of
α,β and χ. BOTH signs are quantified before squaring. This proves
no TypeII 4.2 without the separate signed Parity 4.17 correlations. -/
theorem parity_eventually_original_signed_source_to_intrinsic_Psi_Bprime_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
        (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ))),
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β signed 0
          ⌊2*Real.exp L⌋₊ -
        parityOriginalSignedIntrinsicPsiPostIntegrated434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
          K J α β signed ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_hminus2_source_to_post_Psi_Mellin_Bprime_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hSmooth hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  have hBound := h.2.2 band hb E hElo hEhi Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  have hL : 0 < L := by nlinarith [h.1]
  rw [parity_original_signed_intrinsic_Psi_Bprime_eq_source_postintegrated434
    (sourceOriginalLiteralDepth 20 L) L E hL rfl
    band slot Psi hSmooth
    (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
    K J α β signed ⌊2*Real.exp L⌋₊ L] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedIntrinsicPsiEOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Exact multi-index Fubini after source B590 assignment: the
selected e coefficient is moved outside the WHOLE original u-sum,
not merely outside a vStar fibre at a fixed u. This preserves every
source δ-dependent actual e support and full physical coefficient. -/
theorem parity_original_intrinsic_e_outer_finite_reindex434
    {N : ℕ} (U : Finset ℕ) (E : (Fin N → Bool) → Finset ℕ)
    (a : (Fin N → Bool) → ℕ → ℂ)
    (V : (Fin N → Bool) → ℕ → ℕ → ℂ)
    (B : ℕ → ℂ) :
    (∑ u ∈ U,
      (∑ δ : Fin N → Bool,
        ∑ e ∈ E δ, a δ e * V δ e u) * B u) =
    ∑ δ : Fin N → Bool,
      ∑ e ∈ E δ,
        a δ e * (∑ u ∈ U, V δ e u * B u) := by
  classical
  calc
    _ = ∑ u ∈ U, ∑ δ : Fin N → Bool,
          ∑ e ∈ E δ, (a δ e * V δ e u) * B u := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro δ hδ
            rw [Finset.sum_mul]
    _ = ∑ δ : Fin N → Bool, ∑ u ∈ U,
          ∑ e ∈ E δ, (a δ e * V δ e u) * B u := Finset.sum_comm
    _ = ∑ δ : Fin N → Bool, ∑ e ∈ E δ,
          ∑ u ∈ U, (a δ e * V δ e u) * B u := by
            apply Finset.sum_congr rfl
            intro δ hδ
            exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro δ hδ
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Complete intrinsic post-Ψ-Mellin actual Parity B' with e outerMOST
relative to original u, actual α_mβ_n and physical vStar convolution.
For each δ, ξ, s, a_e(e) depends only on e; the inner a_v(v)
contains H_0, original W1 and full signed P parity independent of α,β.
The true original e support is retained for each δ (no Cartesian Q
support invented). -/
def parityOriginalSignedIntrinsicPsiEOuterAtXi434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) : ℂ :=
  ∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
    L Psi hSmooth hSupport s *
    (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∑ e ∈ parityOriginalIntrinsicEFirstValues434 d L band slot δ,
        parityOriginalSelectedEGateMellinCoefficient434
          d L E band slot δ ξ (2*Real.pi*s) e *
        (∑ u ∈ Finset.Ioc 0 Y,
          (∑ z ∈ parityOriginalIntrinsicEFirstFibre434 d L band slot δ e,
            parityOriginalIntrinsicEVStarAtU434 d L E u signed
              band slot δ ξ (2*Real.pi*s) z) *
          (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α w.1*β w.2)))

/-- Actual e-outer B' after integrating genuine original N-dimensional
B590 f0/f1 Fourier and 1D Ψ logarithmic Mellin (ρ=2πs).
This is the literal source-dependent finite e-u interchange. -/
def parityOriginalSignedIntrinsicPsiEOuterPost434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    parityOriginalSignedIntrinsicPsiEOuterAtXi434
      d L E band slot ξ Psi hSmooth hSupport K J α β signed Y
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- New exact source-faithful reindexing: post-Mellin Parity B' has TRUE
selected e OUTERMOST before the original alpha-beta convolution, for
both signs. No remainder, hypothetical independence or convolution
coefficients are assumed. -/
theorem parity_original_signed_intrinsic_Psi_post_eq_e_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    parityOriginalSignedIntrinsicPsiPostIntegrated434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T =
    parityOriginalSignedIntrinsicPsiEOuterPost434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T := by
  unfold parityOriginalSignedIntrinsicPsiPostIntegrated434
    parityOriginalSignedIntrinsicPsiEOuterPost434
  apply integral_congr_ae
  filter_upwards [] with ξ
  unfold parityOriginalSignedIntrinsicPsiBprimeAtXi434
    parityOriginalSignedIntrinsicPsiEOuterAtXi434
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  let N := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let ESource : (Fin N → Bool) → Finset ℕ := fun δ =>
    parityOriginalIntrinsicEFirstValues434 d L band slot δ
  let A : (Fin N → Bool) → ℕ → ℂ := fun δ e =>
    parityOriginalSelectedEGateMellinCoefficient434
      d L E band slot δ ξ (2*Real.pi*s) e
  let V : (Fin N → Bool) → ℕ → ℕ → ℂ := fun δ e u =>
    ∑ z ∈ parityOriginalIntrinsicEFirstFibre434 d L band slot δ e,
      parityOriginalIntrinsicEVStarAtU434 d L E u signed
        band slot δ ξ (2*Real.pi*s) z
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α z.1*β z.2
  change (∑ u ∈ Finset.Ioc 0 Y,
    (∑ δ : Fin N → Bool, ∑ e ∈ ESource δ, A δ e * V δ e u)*B u) =
    ∑ δ : Fin N → Bool,
      ∑ e ∈ ESource δ,
        A δ e * (∑ u ∈ Finset.Ioc 0 Y, V δ e u * B u)
  exact parity_original_intrinsic_e_outer_finite_reindex434
    (Finset.Ioc 0 Y) ESource A V B
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedIntrinsicPsiEOuterAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Real original Parity(4.7) signed SOURCE->post-Psi-Mellin B' with
TRUE e OUTERMOST of all source u/m/n/vStar sums. The exact original
20! Q factorial, original f0/f1 B590 Fourier allocation, retained
historical E L^-88<=e<=E, actual Ppart beta/4 Rankin, physical
W1(v)*epsilon(v)*H_0(vStar), and actual h=-2,m*n=e*v+2 support
all survive. For EACH epsilon=1/E the bound is before squaring.
The integrand has no invented nonzero prime phase sigma.
This alone does NOT establish signed (4.17) with beta Ppart cap,
Cauchy square, Type II(4.2), sieve, or terminal Green64. -/
theorem parity_eventually_original_signed_source_to_intrinsic_Psi_EOuter_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
        (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ))),
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β signed 0
          ⌊2*Real.exp L⌋₊ -
        parityOriginalSignedIntrinsicPsiEOuterPost434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
          K J α β signed ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_source_to_intrinsic_Psi_Bprime_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hSmooth hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  have hBound := h.2.2 band hb E hElo hEhi Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  rw [parity_original_signed_intrinsic_Psi_post_eq_e_outer434
    (sourceOriginalLiteralDepth 20 L) L E band slot Psi hSmooth
    (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
    K J α β signed ⌊2*Real.exp L⌋₊ L] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedCartesianSupport -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The genuine original Parity Q-selected e support at fixed allocation δ.
Every original dependent label is present, no supplementary e values. -/
def parityOriginalReservedCartesianESupport434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) : Finset ℕ :=
  paritySourceQSelectedESupport434
    (Q := sourceActualSortedQ 20 d L band slot) δ

/-- Original reserved prime p times the actual B509 skipped-Q product
r. The two are selected INDEPENDENTLY from their original labelled
finite source carriers, including repeated primes and prime-valuations. -/
def parityOriginalReservedCartesianVStarSupport434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) : Finset ℕ :=
  (Finset.univ : Finset ({p : ℕ // p ∈ sourceOriginalQActualBands 20 d L band} ×
      OrderedQSkip (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length
        (sourceActualSortedQ 20 d L band slot) δ)).image
    (fun a => a.1.val*orderedSkipProduct a.2)

/-- The ACTUAL original Parity source full (e,vStar) support is
EXACTLY the cartesian product of its true selected and skipped Q
supports. This is not a source-free assumption: it follows by the
original dependent Q-slot selected/skipped bijection and the real
reserved-prime source slot. The δ-specific supports remain exact. -/
theorem parity_original_reserved_fullQ_EVStar_support_cartesian434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :
    parityOriginalReservedFullQEVStarSupport434 d L band slot δ =
      (parityOriginalReservedCartesianESupport434 d L band slot δ).product
        (parityOriginalReservedCartesianVStarSupport434 d L band slot δ) := by
  classical
  let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let Q := sourceActualSortedQ 20 d L band slot
  let Φ := paritySourceQAllSelectedSkipEquiv434 Q δ
  apply Finset.ext
  intro z
  constructor
  · intro hz
    unfold parityOriginalReservedFullQEVStarSupport434 at hz
    obtain ⟨⟨p,rest⟩,hr,hzEq⟩ := Finset.mem_image.mp hz
    have hSel : paritySourceOrderedAllocatedE434 δ rest =
        paritySourceQSelectedPrimeProduct434 (Φ rest).1 := by
      rw [parity_original_ordered_allocated_e_eq_selected_Q_product434]
      rfl
    have hSkip : paritySourceOrderedAllocatedV434 δ rest =
        orderedSkipProduct (Φ rest).2 := rfl
    have hMemE : paritySourceOrderedAllocatedE434 δ rest ∈
        parityOriginalReservedCartesianESupport434 d L band slot δ := by
      unfold parityOriginalReservedCartesianESupport434 paritySourceQSelectedESupport434
      exact Finset.mem_image.mpr ⟨(Φ rest).1, Finset.mem_univ _,hSel.symm⟩
    have hMemV : p.val*paritySourceOrderedAllocatedV434 δ rest ∈
        parityOriginalReservedCartesianVStarSupport434 d L band slot δ := by
      unfold parityOriginalReservedCartesianVStarSupport434
      exact Finset.mem_image.mpr ⟨(p,(Φ rest).2),Finset.mem_univ _,by rw [hSkip]⟩
    rw [←hzEq]
    exact Finset.mem_product.mpr ⟨hMemE,hMemV⟩
  · intro hz
    have hPair := Finset.mem_product.mp hz
    unfold parityOriginalReservedCartesianESupport434 paritySourceQSelectedESupport434 at hPair
    unfold parityOriginalReservedCartesianVStarSupport434 at hPair
    obtain ⟨sel,hsel,hEqSel⟩ := Finset.mem_image.mp hPair.1
    obtain ⟨⟨p,skip⟩,hskip,hEqV⟩ := Finset.mem_image.mp hPair.2
    let rest := Φ.symm (sel,skip)
    have hPhi : Φ rest = (sel,skip) := Φ.apply_symm_apply (sel,skip)
    have hSel : paritySourceOrderedAllocatedE434 δ rest =
        paritySourceQSelectedPrimeProduct434 sel := by
      rw [parity_original_ordered_allocated_e_eq_selected_Q_product434]
      change paritySourceQSelectedPrimeProduct434 (Φ rest).1 =
        paritySourceQSelectedPrimeProduct434 sel
      rw [hPhi]
    have hSkip : paritySourceOrderedAllocatedV434 δ rest =
        orderedSkipProduct skip := by
      change orderedSkipProduct (Φ rest).2=orderedSkipProduct skip
      rw [hPhi]
    unfold parityOriginalReservedFullQEVStarSupport434
    apply Finset.mem_image.mpr
    refine ⟨(p,rest),Finset.mem_univ _,?_⟩
    apply Prod.ext
    · calc
        paritySourceOrderedAllocatedE434 δ rest =
          paritySourceQSelectedPrimeProduct434 sel := hSel
        _ = z.1 := hEqSel
    · calc
        p.val*paritySourceOrderedAllocatedV434 δ rest =
          p.val*orderedSkipProduct skip := by rw [hSkip]
        _ = z.2 := hEqV
end Green64Analytic.Parity

end

end

/-! ## OriginalCartesianEFirstSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exact mathematical reindex for a REAL Cartesian (e,vStar) source
support, valid even if either original Q carrier is empty: the e-only
coefficient is independently outside the complete vStar convolution. -/
theorem parity_original_cartesian_e_first_reindex434
    (A B : Finset ℕ) (a : ℕ → ℂ) (b : ℕ×ℕ → ℂ) :
    (∑ e ∈ (A.product B).image Prod.fst,
      a e * (∑ z ∈ (A.product B).filter (fun z => z.1=e), b z)) =
    ∑ e ∈ A, a e * (∑ vStar ∈ B, b (e,vStar)) := by
  calc
    _ = ∑ z ∈ A.product B, a z.1*b z :=
      (parity_original_e_first_finset_product_reindex434 (A.product B) a b).symm
    _ = ∑ e ∈ A, ∑ vStar ∈ B, a e*b (e,vStar) := by
      exact Finset.sum_product A B (fun z : ℕ × ℕ => a z.1 * b z)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]

/-- The REAL source original Parity signed epsilon1/E fixed δ,xi,rho
FULL factorial-labelled Q coefficient at an actual physical u is
exactly selected e-only Fourier/Mellin a_e(e) times a sum over ALL
independent genuine reserved-prime×skipped-Q vStar products. The
source product gate e*vStar=ordinaryPart(P,u), original W1(P,v), E
multiplicity sign and H_0(vStar) remain INSIDE the inner sum.
This eliminates the last artificial e-dependence in the physical
vStar-support carrier before historical Parity(4.10) Cauchy, rather
than merely making the formula for a_v independent of e. -/
theorem parity_original_signed_intrinsic_delta_e_outer_independent_vStar_support434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) :
    parityOriginalSignedIntrinsicEFirstAtU434 d L E u signed band slot δ ξ rho =
      ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
        parityOriginalSelectedEGateMellinCoefficient434
          d L E band slot δ ξ rho e *
        (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
          parityOriginalIntrinsicEVStarAtU434
            d L E u signed band slot δ ξ rho (e,vStar)) := by
  have hCart := parity_original_reserved_fullQ_EVStar_support_cartesian434
    d L band slot δ
  unfold parityOriginalSignedIntrinsicEFirstAtU434
  unfold parityOriginalIntrinsicEFirstValues434 parityOriginalIntrinsicEFirstFibre434
  rw [hCart]
  exact parity_original_cartesian_e_first_reindex434
    (parityOriginalReservedCartesianESupport434 d L band slot δ)
    (parityOriginalReservedCartesianVStarSupport434 d L band slot δ)
    (parityOriginalSelectedEGateMellinCoefficient434 d L E band slot δ ξ rho)
    (parityOriginalIntrinsicEVStarAtU434 d L E u signed band slot δ ξ rho)
end Green64Analytic.Parity

end

end

/-! ## OriginalCartesianBPrime -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Original source Parity B' at a fixed Fourier ξ, after the true one-
dimensional Ψ Mellin inversion. Source selected e and full physical
vStar support are genuinely independent for EACH actual δ assignment,
not merely for a fixed u. The entire h=-2 alpha-beta convolution and
rho=2πs are unchanged. -/
def parityOriginalSignedCartesianPsiBprimeAtXi434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) : ℂ :=
  ∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
    L Psi hSmooth hSupport s *
    (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
        parityOriginalSelectedEGateMellinCoefficient434
          d L E band slot δ ξ (2*Real.pi*s) e *
        (∑ u ∈ Finset.Ioc 0 Y,
          (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
            parityOriginalIntrinsicEVStarAtU434 d L E u signed
              band slot δ ξ (2*Real.pi*s) (e,vStar)) *
          (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α w.1*β w.2)))

/-- Full two real Lebesgue integrations of Parity's actual Ψ Mellin and
B590 Fourier BOX, with genuinely independent original source selected
Q e and skipped/reserved physical vStar supports. -/
def parityOriginalSignedCartesianPsiBprime434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    parityOriginalSignedCartesianPsiBprimeAtXi434
      d L E band slot ξ Psi hSmooth hSupport K J α β signed Y
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- Exact REAL post-Psi Mellin source Parity (4.7): the original e-outer
representation now has an independent source-support vStar, preserving
ALL factorials and physical Ppart(u) gate. This is not a conjectural
Cartesian extension: proved by the actual dependent Q Pi equivalence. -/
theorem parity_original_signed_intrinsic_Psi_post_eq_cartesian434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    parityOriginalSignedIntrinsicPsiPostIntegrated434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T =
    parityOriginalSignedCartesianPsiBprime434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T := by
  unfold parityOriginalSignedIntrinsicPsiPostIntegrated434
    parityOriginalSignedCartesianPsiBprime434
  apply integral_congr_ae
  filter_upwards [] with ξ
  unfold parityOriginalSignedIntrinsicPsiBprimeAtXi434
    parityOriginalSignedCartesianPsiBprimeAtXi434
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  let N := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let ESource : (Fin N → Bool) → Finset ℕ := fun δ =>
    parityOriginalReservedCartesianESupport434 d L band slot δ
  let A : (Fin N → Bool) → ℕ → ℂ := fun δ e =>
    parityOriginalSelectedEGateMellinCoefficient434 d L E band slot
      δ ξ (2*Real.pi*s) e
  let V : (Fin N → Bool) → ℕ → ℕ → ℂ := fun δ e u =>
    ∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
      parityOriginalIntrinsicEVStarAtU434 d L E u signed band slot δ
        ξ (2*Real.pi*s) (e,vStar)
  let R : ℕ → ℂ := fun u =>
    ∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α w.1*β w.2
  have hSource (u : ℕ) :
      parityOriginalSignedIntrinsicEFirstFullAtU434
        d L E u signed band slot (2*Real.pi*s) ξ =
      ∑ δ : Fin N → Bool, ∑ e ∈ ESource δ, A δ e * V δ e u := by
    unfold parityOriginalSignedIntrinsicEFirstFullAtU434
    apply Finset.sum_congr rfl
    intro δ hδ
    exact parity_original_signed_intrinsic_delta_e_outer_independent_vStar_support434
      d L E u signed band slot δ ξ (2*Real.pi*s)
  change (∑ u ∈ Finset.Ioc 0 Y,
    parityOriginalSignedIntrinsicEFirstFullAtU434
      d L E u signed band slot (2*Real.pi*s) ξ * R u) =
    ∑ δ : Fin N → Bool, ∑ e ∈ ESource δ,
      A δ e * (∑ u ∈ Finset.Ioc 0 Y, V δ e u * R u)
  calc
    _ = ∑ u ∈ Finset.Ioc 0 Y,
          (∑ δ : Fin N → Bool, ∑ e ∈ ESource δ,
            A δ e * V δ e u) * R u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hSource u]
    _ = _ := parity_original_intrinsic_e_outer_finite_reindex434
      (Finset.Ioc 0 Y) ESource A V R
end Green64Analytic.Parity

end

end

/-! ## OriginalCartesianOdd -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Every ACTUAL source selected-Q prime tuple at r20 has an odd
selected integer e, since all source Q bands have PRIME slots >=4;
this holds even for repeated prime labels and empty selection. -/
theorem parity_original_cartesian_selected_e_odd_of_prime_slots434
    {n : ℕ} {Q : Fin n → Finset ℕ} (δ : Fin n → Bool)
    (hQ : ∀ i q, q ∈ Q i → q.Prime ∧ 4≤q)
    (e : ℕ) (he : e ∈ paritySourceQSelectedESupport434 (Q:=Q) δ) :
    Odd e := by
  rcases Finset.mem_image.mp he with ⟨a,ha,heq⟩
  have hOdd : Odd (paritySourceQSelectedPrimeProduct434 a) := by
    unfold paritySourceQSelectedPrimeProduct434
    apply Finset.prod_induction (p := Odd)
    · intro x y hx hy
      exact hx.mul hy
    · decide
    · intro i hi
      have hp := hQ i.val (a i).val (a i).property
      exact hp.1.odd_of_ne_two (by omega)
  exact heq ▸ hOdd

/-- Actual original source selected e support from the TRULY
independent Cartesian Q-source split is odd, positive, and a unit
modulo R=2 at every physical moving r20 Q band. This discharges
exact applicability assumptions of the historical Parity h=-2
Cauchy determinant and mask, not merely individual tuple oddness. -/
theorem parity_eventually_original_cartesian_selected_e_odd_unit434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (e : ℕ),
        e ∈ parityOriginalReservedCartesianESupport434
          (sourceOriginalLiteralDepth 20 L) L band slot δ →
        Odd e ∧ 0<e ∧ IsUnit (e : ZMod 2) := by
  filter_upwards [parity_eventually_actual_sorted_Q_slot_prime_floor434]
    with L hQ
  refine ⟨hQ.1,?_⟩
  intro band slot δ e he
  have hOdd : Odd e :=
    parity_original_cartesian_selected_e_odd_of_prime_slots434 δ
      (hQ.2 band slot) e he
  refine ⟨hOdd,hOdd.pos,?_⟩
  exact (ZMod.isUnit_iff_coprime _ 2).mpr
    (Nat.coprime_two_right.mpr hOdd)
end Green64Analytic.Parity

end

end

/-! ## OriginalCartesianAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Genuine original Parity(4.7) r20 full signed h=-2 SOURCE is
O_A(exp(L)L^-A) close to post-Psi Mellin B' with TRUE independent
selected e and reserved/skipped-Q vStar SOURCE supports. Every original
20! factorial, 2π Mellin frequency, original B590 f0/f1 Schwartz
Fourier box, full Ppart W1 parity and original E L^-88≤e≤E gate
survive, separately for each epsilon=1 and epsilon=E. The positive
physical vStar coefficient is independent of selected e and outer alpha.
The original β/4 Rankin and outside-e Fourier errors were already paid
BEFORE Cauchy, with no change to source stage. Full TypeII 4.2 still
needs Cauchy square, diagonal/offdiagonal and summation. -/
theorem parity_eventually_original_signed_source_to_cartesian_Psi_Bprime_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
        (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ))),
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β signed 0
          ⌊2*Real.exp L⌋₊ -
        parityOriginalSignedCartesianPsiBprime434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
          K J α β signed ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_source_to_intrinsic_Psi_Bprime_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hSmooth hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  have hBound := h.2.2 band hb E hElo hEhi Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  rw [parity_original_signed_intrinsic_Psi_post_eq_cartesian434
    (sourceOriginalLiteralDepth 20 L) L E band slot Psi hSmooth
    (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
    K J α β signed ⌊2*Real.exp L⌋₊ L] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalAE -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The exact historical Parity(4.7) a_e(e) at a fixed actual B590
allocation δ, true Fourier frequency ξ, and Mellin rho, now with the
ORIGINAL (4.5) window E L^-88≤e≤E INSIDE a_e itself. This coefficient
contains no v, skipped-Q residual, reserved prime, W1/P sign, alpha or beta. -/
def parityOriginalHistoricalWindowAE434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (e : ℕ) : ℂ :=
  if parityOriginalHistoricalEWindow434 L E e then
    parityOriginalSelectedEGateMellinCoefficient434 d L E band slot δ ξ rho e
  else 0

/-- The complete genuine reserved-prime×B509 skipped-Q physical
coefficient at u, with the actual product equation e*vStar=ordinary(P,u)
but NO e-window in the inner vStar source. The e-window has been
transferred entirely to the newly defined historical a_e(e). -/
def parityOriginalIntrinsicUnwindowedEVStarAtU434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (e vStar : ℕ) : ℂ :=
  if e*vStar=sourceOriginalOrdinaryPart
       (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
    parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vStar
      (vStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
  else 0

/-- The original physical vStar source has no residual occurrence
of the historical e-window once its e-only indicator has been
moved into a_e, for both eps=1/E before squaring. -/
theorem parity_original_historical_e_window_separated_from_physical_AV434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (e vStar : ℕ) :
    parityOriginalIntrinsicEVStarAtU434 d L E u signed band slot δ ξ rho (e,vStar) =
      if parityOriginalHistoricalEWindow434 L E e then
        parityOriginalIntrinsicUnwindowedEVStarAtU434
          d L u signed band slot δ ξ rho e vStar
      else 0 := by
  unfold parityOriginalIntrinsicEVStarAtU434
    parityOriginalIntrinsicUnwindowedEVStarAtU434
  by_cases h : parityOriginalHistoricalEWindow434 L E e <;>
    simp [h] <;> rfl

/-- Actual full source fixed allocation/physical u e-FIRST Parity(4.7)
with independent original selected/skipped Q supports and historic
e-window in a_e, not in the physical a_v. Retains real source Q product
gate, Ppart and W1 parity, complete B509 factorial and reserved prime. -/
theorem parity_original_signed_cartesian_e_window_in_AE_exact434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) :
    (∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
       parityOriginalSelectedEGateMellinCoefficient434
         d L E band slot δ ξ rho e *
       (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
         parityOriginalIntrinsicEVStarAtU434
           d L E u signed band slot δ ξ rho (e,vStar))) =
    ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
       parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e *
       (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
         parityOriginalIntrinsicUnwindowedEVStarAtU434
           d L u signed band slot δ ξ rho e vStar) := by
  apply Finset.sum_congr rfl
  intro e he
  by_cases hWin : parityOriginalHistoricalEWindow434 L E e
  · simp only [parityOriginalHistoricalWindowAE434, if_pos hWin]
    apply congrArg (fun t : ℂ =>
      parityOriginalSelectedEGateMellinCoefficient434 d L E band slot δ ξ rho e * t)
    apply Finset.sum_congr rfl
    intro vStar hvStar
    rw [parity_original_historical_e_window_separated_from_physical_AV434]
    simp [hWin]
  · simp only [parityOriginalHistoricalWindowAE434, if_neg hWin,zero_mul]
    have hAllZero : (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434
        d L band slot δ,
        parityOriginalIntrinsicEVStarAtU434
          d L E u signed band slot δ ξ rho (e,vStar)) = 0 := by
      apply Finset.sum_eq_zero
      intro vStar hvStar
      rw [parity_original_historical_e_window_separated_from_physical_AV434]
      simp [hWin]
    rw [hAllZero,mul_zero]

/-- The literal Parity(4.5) e-window can be recorded as the SOURCE support
of the exact a_e coefficient itself, with no dependence on physical v. -/
theorem parity_original_historical_window_AE_support434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (e : ℕ) :
    parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e ≠ 0 →
      E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E := by
  intro hNonzero
  by_contra hNot
  have hNotWin : ¬parityOriginalHistoricalEWindow434 L E e := hNot
  simp [parityOriginalHistoricalWindowAE434,hNotWin] at hNonzero
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalAEBPrime -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Fully historical e-first Parity (4.7) integrand after genuine Ψ(u/x)
logarithmic Mellin inversion, source coefficient a_e(e) INCLUDES
historical E L^-88≤e≤E, and the genuine v-side H_0(vStar), W1(v),
epsilon(v), and exact ordinary/Q product gate are OUTSIDE the e-window.
Both original signed branches and h=-2 alpha beta K,J remain unchanged. -/
def parityOriginalSignedHistoricalAEPsiBprimeAtXi434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) : ℂ :=
  ∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
    L Psi hSmooth hSupport s *
    (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
      ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
        parityOriginalHistoricalWindowAE434 d L E band slot δ ξ (2*Real.pi*s) e *
        (∑ u ∈ Finset.Ioc 0 Y,
          (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
            parityOriginalIntrinsicUnwindowedEVStarAtU434 d L u signed
              band slot δ ξ (2*Real.pi*s) e vStar) *
          (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α w.1*β w.2)))

/-- The actual completed B' across BOTH source Lebesgue integrations,
with historical E L^-88≤e≤E inside a_e and the physical H(vStar)
independent of all source e/Fourier coefficient parameters. -/
def parityOriginalSignedHistoricalAEPsiBprime434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    parityOriginalSignedHistoricalAEPsiBprimeAtXi434
      d L E band slot ξ Psi hSmooth hSupport K J α β signed Y
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- SOURCE-true finite e FIRST / u NEXT historical Fourier e-window
moves solely into independent a_e(e), for any signed epsilon and true
original source Q cartesian e and vStar supports. It never changes the
external alpha beta h=-2 pair fibre. -/
theorem parity_original_historical_AE_window_e_outer_bilinear_exact434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y : ℕ)
    (K J : Finset ℕ) (α β : ℕ → ℂ) :
    (∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
      parityOriginalSelectedEGateMellinCoefficient434 d L E band slot δ ξ rho e *
      (∑ u ∈ Finset.Ioc 0 Y,
        (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
          parityOriginalIntrinsicEVStarAtU434 d L E u signed
            band slot δ ξ rho (e,vStar)) *
        (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α w.1*β w.2))) =
    ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
      parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e *
      (∑ u ∈ Finset.Ioc 0 Y,
        (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
          parityOriginalIntrinsicUnwindowedEVStarAtU434 d L u signed
            band slot δ ξ rho e vStar) *
        (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α w.1*β w.2)) := by
  apply Finset.sum_congr rfl
  intro e he
  by_cases hWin : parityOriginalHistoricalEWindow434 L E e
  · simp only [parityOriginalHistoricalWindowAE434, if_pos hWin]
    apply congrArg (fun t : ℂ =>
      parityOriginalSelectedEGateMellinCoefficient434 d L E band slot δ ξ rho e * t)
    apply Finset.sum_congr rfl
    intro u hu
    apply congrArg (fun t : ℂ =>
      t * (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α w.1*β w.2))
    apply Finset.sum_congr rfl
    intro vStar hvStar
    rw [parity_original_historical_e_window_separated_from_physical_AV434]
    simp [hWin]
  · simp only [parityOriginalHistoricalWindowAE434, if_neg hWin,zero_mul]
    have hZeroU : (∑ u ∈ Finset.Ioc 0 Y,
      (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
          parityOriginalIntrinsicEVStarAtU434 d L E u signed band slot δ ξ rho
            (e,vStar)) *
        (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α w.1*β w.2)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have hZeroV : (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434
          d L band slot δ,
        parityOriginalIntrinsicEVStarAtU434 d L E u signed band slot δ ξ rho
          (e,vStar)) = 0 := by
        apply Finset.sum_eq_zero
        intro vStar hvStar
        rw [parity_original_historical_e_window_separated_from_physical_AV434]
        simp [hWin]
      rw [hZeroV,zero_mul]
    rw [hZeroU,mul_zero]

/-- Original independently signed B590+Ψ Fourier/Mellin source B'
equals the historical a_e-windowed e-first expression under TWO real
Lebesgue integrations. The actual a_e is now independent of v and
carries the complete original selected Q factorial/Fourier multiplier,
while the true physical a_v contains H_0, W1 and multiplicity E sign. -/
theorem parity_original_signed_cartesian_Bprime_eq_historical_AE434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    parityOriginalSignedCartesianPsiBprime434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T =
    parityOriginalSignedHistoricalAEPsiBprime434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T := by
  unfold parityOriginalSignedCartesianPsiBprime434
    parityOriginalSignedHistoricalAEPsiBprime434
  apply integral_congr_ae
  filter_upwards [] with ξ
  unfold parityOriginalSignedCartesianPsiBprimeAtXi434
    parityOriginalSignedHistoricalAEPsiBprimeAtXi434
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_historical_AE_window_e_outer_bilinear_exact434
    d L E band slot δ ξ (2*Real.pi*s) signed Y K J α β
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalAEAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The original historical a_e(e) coefficient with the actual Parity(4.5)
window INCLUDED, true source B590 f0/f1 Fourier transforms and Mellin
rho e-phase, has a fixed r20 20! Q-factorial logarithmic bound uniform
in e,rho, Fourier accuracy, original K0, and both eps branches. No
surrogate physical v coefficient nor pointwise ξ cutoff is used. -/
theorem parity_eventually_original_historical_window_AE_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (e : ℕ),
      ‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e‖ ≤
        L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖) := by
  filter_upwards [parity_eventually_original_intrinsic_e_mellin_coeff_polylog434,
    eventually_gt_atTop (0:ℝ)] with L h hL
  intro band slot E δ ξ rho e
  by_cases hWin : parityOriginalHistoricalEWindow434 L E e
  · simpa only [parityOriginalHistoricalWindowAE434,if_pos hWin] using
      h band slot E δ ξ rho e
  · have hRHS : 0 ≤ L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖) :=
      mul_nonneg (Real.rpow_nonneg hL.le _)
        (Finset.prod_nonneg (by intro i hi; exact norm_nonneg _))
    simpa only [parityOriginalHistoricalWindowAE434,if_neg hWin,norm_zero]
      using hRHS

/-- Terminal exact historical Parity (4.7) signed epsilon=1 and epsilon=E
SOURCE→post-Ψ-Mellin B' with e-window INSIDE the independent e-only
a_e, actual e and vStar supports independent, physical a_v(v) with
complete QSkip B509 factorial/reserved H_0, moving P W1 and source E
multiplicity sign. Full original α_mβ_n h=-2 convolution, original
B590 Fourier 2π and every f0/f1 gate are preserved. The actual original
beta/4 Rankin and Fourier leakage are already paid uniformly at
O_A(exp L L^-A) for BOTH signs separately BEFORE Cauchy.
This remains a source reduction, not full Cauchy/TypeII(4.2). -/
theorem parity_eventually_original_signed_source_to_historical_AE_Psi_Bprime_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
        (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ))),
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (signed : Bool),
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β signed 0
          ⌊2*Real.exp L⌋₊ -
        parityOriginalSignedHistoricalAEPsiBprime434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
          K J α β signed ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_source_to_cartesian_Psi_Bprime_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hSmooth hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  have hBound := h.2.2 band hb E hElo hEhi Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ signed
  rw [parity_original_signed_cartesian_Bprime_eq_historical_AE434
    (sourceOriginalLiteralDepth 20 L) L E band slot Psi hSmooth
    (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
    K J α β signed ⌊2*Real.exp L⌋₊ L] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCauchyInner -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The REAL original Parity h=-2 e,n,m fibre after changing the order
of finite sums. Unlike an abstract Cauchy kernel, this uses precisely
the physical source u and the actual e*vStar=ordinary(P,u) condition
inside the intrinsic H_0(vStar) source. -/
def parityOriginalHistoricalCauchyPhysicalAtENM434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (signed : Bool) (Y e n m : ℕ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    if (0 < m ∧ 0 < n ∧ m*n = u+2) then
      ∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
        parityOriginalIntrinsicUnwindowedEVStarAtU434
          d L u signed band slot δ ξ rho e vStar
    else 0

/-- The EXACT complete historical signed e,n Cauchy amplitude at one
real original f0/f1 B590 Fourier allocation and Ψ Mellin frequency.
Every source a_e(e), beta_n, alpha_m, original positive h=-2
m*n=u+2 fibre, source physical vStar and H_0, W1 and parity is
retained. The e,n pair is OUTERMOST, with the true original e-support
and actual J-beta support; not a hypothetical smooth majorant. -/
def parityOriginalHistoricalCauchyAtDelta434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J,
      (parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e * β n) *
        (∑ m ∈ K, α m *
          parityOriginalHistoricalCauchyPhysicalAtENM434
            d L band slot δ ξ rho signed Y e n m)

/-- Exact integer h=-2 bilinear finite Fubini: the original genuine
`(m,n)` pairs satisfying `m*n=u+2` regroup with n OUTER, m INSIDE,
without dropping positivity or altering any arbitrary physical u
coefficient and outer complex alpha,beta. This is a precise identity,
not a Cauchy majorant or a hypothetical cofactor replacement. -/
theorem parity_original_shift_two_u_mn_to_n_m_u434
    (U K J : Finset ℕ) (α β : ℕ → ℂ) (V : ℕ → ℂ) :
    (∑ u ∈ U,
      V u * (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α w.1 * β w.2)) =
    ∑ n ∈ J, β n * (∑ m ∈ K, α m *
      (∑ u ∈ U, if (0 < m ∧ 0 < n ∧ m*n = u+2) then V u else 0)) := by
  classical
  have hFibre (u : ℕ) :
      (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α w.1 * β w.2) =
      ∑ m ∈ K, ∑ n ∈ J,
        if (0 < m ∧ 0 < n ∧ m*n = u+2) then α m * β n else 0 := by
    unfold parityOriginalShiftTwoPositivePairFibre434
    rw [Finset.sum_filter]
    exact Finset.sum_product K J (fun z : ℕ × ℕ =>
      if 0 < z.1 ∧ 0 < z.2 ∧ z.1*z.2=u+2 then α z.1 * β z.2 else 0)
  calc
    _ = ∑ u ∈ U, V u * (∑ m ∈ K, ∑ n ∈ J,
          if (0 < m ∧ 0 < n ∧ m*n = u+2) then α m * β n else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hFibre u]
    _ = ∑ u ∈ U, ∑ m ∈ K, ∑ n ∈ J,
          V u * (if (0 < m ∧ 0 < n ∧ m*n = u+2) then α m * β n else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ = ∑ m ∈ K, ∑ u ∈ U, ∑ n ∈ J,
          V u * (if (0 < m ∧ 0 < n ∧ m*n = u+2) then α m * β n else 0) :=
        Finset.sum_comm
    _ = ∑ m ∈ K, ∑ n ∈ J, ∑ u ∈ U,
          V u * (if (0 < m ∧ 0 < n ∧ m*n = u+2) then α m * β n else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_comm
    _ = ∑ n ∈ J, ∑ m ∈ K, ∑ u ∈ U,
          V u * (if (0 < m ∧ 0 < n ∧ m*n = u+2) then α m * β n else 0) :=
        Finset.sum_comm
    _ = ∑ n ∈ J, β n * (∑ m ∈ K, α m *
          (∑ u ∈ U, if (0 < m ∧ 0 < n ∧ m*n = u+2) then V u else 0)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      calc
        (∑ u ∈ U, V u *
          (if (0 < m ∧ 0 < n ∧ m*n = u+2) then α m * β n else 0)) =
        ∑ u ∈ U, β n *
          (α m * (if (0 < m ∧ 0 < n ∧ m*n = u+2) then V u else 0)) := by
            apply Finset.sum_congr rfl
            intro u hu
            by_cases h : 0 < m ∧ 0 < n ∧ m*n = u+2
            · simp [h]
              ring
            · simp [h]
        _ = β n * (∑ u ∈ U, α m *
          (if (0 < m ∧ 0 < n ∧ m*n = u+2) then V u else 0)) := by
            rw [Finset.mul_sum]
        _ = β n * (α m * (∑ u ∈ U,
          if (0 < m ∧ 0 < n ∧ m*n = u+2) then V u else 0)) := by
            have hDist :
                (∑ u ∈ U, α m *
                  (if (0 < m ∧ 0 < n ∧ m*n = u+2) then V u else 0)) =
                α m * (∑ u ∈ U,
                  if (0 < m ∧ 0 < n ∧ m*n = u+2) then V u else 0) := by
              rw [Finset.mul_sum]
            exact congrArg (fun z : ℂ => β n * z) hDist

/-- The actual source historical (4.7) e-first physical B' at fixed
δ,ξ,rho is LITERALLY the original e,n-outer Parity(4.10) Cauchy
bilinear sum, with full α_m, β_n, h=-2, B509 residual and both
separate eps signs. This equality is BEFORE taking any square. -/
theorem parity_original_historical_e_first_eq_actual_e_n_cauchy434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    (∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
      parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e *
        (∑ u ∈ Finset.Ioc 0 Y,
          (∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
            parityOriginalIntrinsicUnwindowedEVStarAtU434
              d L u signed band slot δ ξ rho e vStar) *
          (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α w.1*β w.2))) =
    parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y := by
  unfold parityOriginalHistoricalCauchyAtDelta434
  apply Finset.sum_congr rfl
  intro e he
  let V : ℕ → ℂ := fun u =>
    ∑ vStar ∈ parityOriginalReservedCartesianVStarSupport434 d L band slot δ,
      parityOriginalIntrinsicUnwindowedEVStarAtU434 d L u signed band slot δ ξ rho e vStar
  have hReindex := parity_original_shift_two_u_mn_to_n_m_u434
    (Finset.Ioc 0 Y) K J α β V
  change parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e *
      (∑ u ∈ Finset.Ioc 0 Y,
        V u * (∑ w ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α w.1*β w.2)) =
    ∑ n ∈ J, (parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e * β n) *
      (∑ m ∈ K, α m * (∑ u ∈ Finset.Ioc 0 Y,
        if (0 < m ∧ 0 < n ∧ m*n = u+2) then V u else 0))
  rw [hReindex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCauchySquare -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- True complex finite Cauchy inequality for the square of a finite
source bilinear sum. The proof uses the genuine norm triangle and real
Cauchy (not a hypothetical complex square-saving assertion). -/
theorem parity_original_complex_finset_cauchy434
    {ι : Type} (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ x ∈ S, a x * b x‖^2 ≤
      (∑ x ∈ S, ‖a x‖^2) * (∑ x ∈ S, ‖b x‖^2) := by
  classical
  have hTriangle := norm_sum_le S (fun x => a x * b x)
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun x => ‖a x‖) (fun x => ‖b x‖)
  calc
    _ ≤ (∑ x ∈ S, ‖a x * b x‖)^2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (by
        intro x hx
        exact norm_nonneg _))).mpr hTriangle
    _ = (∑ x ∈ S, ‖a x‖*‖b x‖)^2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [norm_mul]
    _ ≤ (∑ x ∈ S, ‖a x‖^2) * (∑ x ∈ S, ‖b x‖^2) := hCauchy

/-- The ACTUAL source historical Parity (4.10) Cauchy square at fixed
B590 assignment δ and true Fourier-Mellin ξ,rho, with real original
selected-e SOURCE support, actual beta_n support J, and physical
h=-2 m,n,vStar,H_0 source inside the squared m-sum.
No abstract original E theorem, off-diagonal input or smooth majorant
is silently invoked: this is the EXACT unsmoothed Cauchy square of the
historical (4.7) source-derived inner sum for both epsilon branches. -/
theorem parity_original_historical_signed_actual_e_n_cauchy_square434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y‖^2 ≤
      (∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
        ∑ n ∈ J,
          ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e * β n‖^2) *
      (∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
        ∑ n ∈ J,
          ‖∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
            d L band slot δ ξ rho signed Y e n m‖^2) := by
  let Q := parityOriginalReservedCartesianESupport434 d L band slot δ
  let S := Q.product J
  let a : (ℕ × ℕ) → ℂ := fun z =>
    parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho z.1 * β z.2
  let b : (ℕ × ℕ) → ℂ := fun z =>
    ∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y z.1 z.2 m
  have hBound := parity_original_complex_finset_cauchy434 S a b
  change ‖∑ x ∈ Q.product J, a x*b x‖^2 ≤
    (∑ x ∈ Q.product J, ‖a x‖^2) *
    (∑ x ∈ Q.product J, ‖b x‖^2) at hBound
  have hSum : (∑ x ∈ Q.product J, a x*b x) =
      ∑ e ∈ Q, ∑ n ∈ J, a (e,n)*b (e,n) :=
    Finset.sum_product Q J (fun z : ℕ × ℕ => a z*b z)
  have hA : (∑ x ∈ Q.product J, ‖a x‖^2) =
      ∑ e ∈ Q, ∑ n ∈ J, ‖a (e,n)‖^2 :=
    Finset.sum_product Q J (fun z : ℕ × ℕ => ‖a z‖^2)
  have hB : (∑ x ∈ Q.product J, ‖b x‖^2) =
      ∑ e ∈ Q, ∑ n ∈ J, ‖b (e,n)‖^2 :=
    Finset.sum_product Q J (fun z : ℕ × ℕ => ‖b z‖^2)
  rw [hSum,hA,hB] at hBound
  simpa only [Q,a,b,parityOriginalHistoricalCauchyAtDelta434] using hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCauchyGram -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Exact square of a genuine complex finite m-sum as the original
physical post-Cauchy m,m' Gram, before any character orthogonality,
wrong modulus, or cancellation estimate. -/
theorem parity_original_complex_cauchy_gram434
    {ι : Type} (K : Finset ι) (F : ι → ℂ) :
    (((‖∑ m ∈ K, F m‖^2 : ℝ) : ℂ)) =
      ∑ m ∈ K, ∑ mp ∈ K, F m * star (F mp) := by
  classical
  have hnorm : (((‖∑ m ∈ K, F m‖^2 : ℝ) : ℂ)) =
      (∑ m ∈ K, F m) * star (∑ m ∈ K, F m) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rfl
  calc
    _ = (∑ m ∈ K, F m) * star (∑ m ∈ K, F m) := hnorm
    _ = (∑ m ∈ K, F m) * (∑ mp ∈ K, star (F mp)) := by rw [star_sum]
    _ = ∑ m ∈ K, ∑ mp ∈ K, F m * star (F mp) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]

/-- Literal m=m' diagonal and m≠m' offdiagonal partition of the
complex Gram; no diagonal terms can leak into the off-diagonal
character-mask family. The latter is EXACTLY K.erase m, not a proxy. -/
theorem parity_original_complex_cauchy_gram_diagonal_offdiag434
    {ι : Type} (K : Finset ι) (F : ι → ℂ) :
    (∑ m ∈ K, ∑ mp ∈ K, F m * star (F mp)) =
      (∑ m ∈ K, F m * star (F m)) +
      (∑ m ∈ K, ∑ mp ∈ K.erase m, F m * star (F mp)) := by
  classical
  have hOne (m : ι) (hm : m∈K) :
      (∑ mp ∈ K, F m * star (F mp)) =
      F m * star (F m) +
      ∑ mp ∈ K.erase m, F m * star (F mp) := by
    have hh := Finset.sum_erase_add K (fun mp => F m * star (F mp)) hm
    simpa only [add_comm] using hh.symm
  calc
    _ = ∑ m ∈ K, (F m * star (F m) +
          ∑ mp ∈ K.erase m, F m * star (F mp)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hOne m hm
    _ = _ := Finset.sum_add_distrib

/-- The genuine diagonal is the sum of NONNEGATIVE physical complex
norm squares, so its sign is known from the true coefficient and not
from a cancellation assumption. -/
theorem parity_original_complex_cauchy_gram_diagonal_norm434
    {ι : Type} (K : Finset ι) (F : ι → ℂ) :
    (∑ m ∈ K, F m * star (F m)) =
      (((∑ m ∈ K, ‖F m‖^2 : ℝ) : ℂ)) := by
  classical
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]

/-- The EXACT original h=-2 source Cauchy square for every actual
selected (e,n), δ, ξ, rho, signed epsilon, with full α_m and actual
physical source H_0(vStar) inside F_m. Every diagonal term has m=m',
and all offdiagonal terms have literal m ≠ m'. This is BEFORE the
Parity (4.13) determinant reindex and character mask identity. -/
theorem parity_original_historical_actual_e_n_square_diag_offdiag434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e n : ℕ) :
    (((‖∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖^2 : ℝ):ℂ)) =
      ((∑ m ∈ K,
        ‖α m * parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2 : ℝ) : ℂ) +
      (∑ m ∈ K, ∑ mp ∈ K.erase m,
        (α m * parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m) *
        star (α mp * parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n mp)) := by
  let F : ℕ → ℂ := fun m =>
    α m * parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m
  calc
    _ = (∑ m ∈ K, ∑ mp ∈ K, F m * star (F mp)) :=
      parity_original_complex_cauchy_gram434 K F
    _ = (∑ m ∈ K, F m * star (F m)) +
          (∑ m ∈ K, ∑ mp ∈ K.erase m, F m * star (F mp)) := by
      calc
        _ = ∑ m ∈ K, (F m * star (F m) +
              ∑ mp ∈ K.erase m, F m * star (F mp)) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hh := Finset.sum_erase_add K
            (fun mp => F m * star (F mp)) hm
          simpa only [add_comm] using hh.symm
        _ = _ := Finset.sum_add_distrib
    _ = ((∑ m ∈ K, ‖F m‖^2 : ℝ) : ℂ) +
          (∑ m ∈ K, ∑ mp ∈ K.erase m, F m * star (F mp)) := by
      rw [parity_original_complex_cauchy_gram_diagonal_norm434]
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCauchyOffdiagK -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Original source physical h=-2 endpoint: for every ACTUAL positive
u=m*n-2 and actual e*vStar=ordinaryPart(P,u), the genuine physical
v=vStar*Ppart(P,u) satisfies m*n=e*v+2. This is the exact source
premise required for Parity(4.13), with ALL P-prime power valuations. -/
theorem parity_original_historical_actual_pair_eq_e_v_plus_two434
    (L : ℝ) (e m n u vStar : ℕ) (hu : 0<u)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (hmn : m*n=u+2) :
    m*n=e*(vStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)+2 :=
  parity_original_e_first_actual_shift_two434 L u e vStar m n hu.ne' hgate hmn

/-- Complete literal Parity (4.13) off-diagonal signed k is DERIVED from
two actual original source physical Cauchy square endpoints at the SAME
selected e and SAME n, not postulated. The hypotheses are exactly the
original source Q/P part gates, positive u=m*n-2, and m≠m'. Both
physical v,v' are the ORIGINAL reserved Q×skipped-Q vStar times the
full physical Ppart. The final z=m'v and z+2k=m v' identity is exact.
This does not yet pay the global character orthogonality and summation. -/
theorem parity_original_historical_actual_cauchy_offdiag_k434
    (L : ℝ) (e m mp n u up vStar vpStar : ℕ)
    (he : Odd e) (hu : 0<u) (hup : 0<up)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (hgatep : e*vpStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up)
    (hmn : m*n=u+2) (hmpn : mp*n=up+2)
    (hneq : m ≠ mp) :
    let v := vStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    let vp := vpStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up
    ∃ k : ℤ, k≠0 ∧
      ((mp:ℤ)-(m:ℤ))=(e:ℤ)*k ∧
      ((vp:ℤ)-(v:ℤ))=k*(n:ℤ) ∧
      ((m:ℤ)*(vp:ℤ)-(mp:ℤ)*(v:ℤ))=2*k ∧
      (mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ) := by
  dsimp only
  have h1 := parity_original_historical_actual_pair_eq_e_v_plus_two434
    L e m n u vStar hu hgate hmn
  have h2 := parity_original_historical_actual_pair_eq_e_v_plus_two434
    L e mp n up vpStar hup hgatep hmpn
  obtain ⟨k,hk,hmshift,hvshift,hdet⟩ :=
    parity_shift_two_original_forward_bilinear434 e m mp n
      (vStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      (vpStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up)
      he h1 h2 hneq
  refine ⟨k,hk,hmshift,hvshift,hdet,?_⟩
  linarith [hdet]

/-- Crucial original Parity (4.13) arithmetic applicability specialized
to EVERY TRUE original selected-e source support at the moving r20 Q
depth, eliminating the previously explicit odd-e hypothesis. This is
actual SOURCE data, not a conditional parity requirement. -/
theorem parity_eventually_original_historical_cauchy_offdiag_k_from_source434 :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (e m mp n u up vStar vpStar : ℕ),
      e ∈ parityOriginalReservedCartesianESupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ →
      0<u → 0<up →
      e*vStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u →
      e*vpStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up →
      m*n=u+2 → mp*n=up+2 → m≠mp →
      let v := vStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
      let vp := vpStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up
      ∃ k : ℤ, k≠0 ∧
        ((mp:ℤ)-(m:ℤ))=(e:ℤ)*k ∧
        ((vp:ℤ)-(v:ℤ))=k*(n:ℤ) ∧
        ((m:ℤ)*(vp:ℤ)-(mp:ℤ)*(v:ℤ))=2*k ∧
        (mp:ℤ)*(v:ℤ)+2*k=(m:ℤ)*(vp:ℤ) := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434]
    with L hSource
  refine ⟨hSource.1,?_⟩
  intro band slot δ e m mp n u up vStar vpStar he hu hup
    hgate hgatep hmn hmpn hneq
  exact parity_original_historical_actual_cauchy_offdiag_k434
    L e m mp n u up vStar vpStar (hSource.2 band slot δ e he).1
    hu hup hgate hgatep hmn hmpn hneq
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCauchyFineMask -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Original SOURCE actual fine-coefficient offdiagonal Cauchy inputs,
with e selected from the TRUE r20 original Q Cartesian support,
full physical e*vStar=ordinary(P,u), e*vpStar=ordinary(P,u'), and
m*n=u+2/m'*n=u'+2, automatically satisfy the ORIGINAL Parity (2.6)
integer ratio Fourier mask at derived nonzero k.
No odd e, rough m, m'-unit modulo 2|k|, or k parity is ASSUMED;
all of these are proved from genuine Q-source and b629 fine α.
The original rank condition |k|≤L^Ck is retained as an implication,
not silently derived without its size hypotheses. -/
theorem parity_eventually_original_historical_actual_fine_cauchy_fourier_mask434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 4 ≤ L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (e m mp n u up vStar vpStar : ℕ),
      e∈parityOriginalReservedCartesianESupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ →
      0<u → 0<up →
      e*vStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u →
      e*vpStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up →
      m*n=u+2 → mp*n=up+2 → m≠mp →
      ∀ (prime : Bool) (lFine uFine : ℕ), 2≤lFine →
        Real.exp (beta*L)≤(lFine:ℝ) →
      ∀ (K : Finset ℕ),
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) m ≠ 0 →
        restrictSequence K (b629ActualFineAlpha434 prime L S gamma lFine uFine) mp ≠ 0 →
      let v := vStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
      let vp := vpStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up
      ∃ k : ℤ, k≠0 ∧
        ((mp:ℤ)-(m:ℤ))=(e:ℤ)*k ∧
        ((vp:ℤ)-(v:ℤ))=k*(n:ℤ) ∧
        ((m:ℤ)*(vp:ℤ)-(mp:ℤ)*(v:ℤ))=2*k ∧
        ((k.natAbs:ℝ) ≤ L^Ck →
          Even k ∧
          (∑ chi : DirichletCharacter ℂ (2*k.natAbs),
            parityShiftTwoMaskCoefficient434 k.natAbs chi *
            chi (mp : ZMod (2*k.natAbs)) *
            star (chi (m : ZMod (2*k.natAbs))))=1) := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434,
    parity_eventually_actual_fine_bilinear_fourier_mask_one434
      S beta gamma Ck hS hbeta hgamma]
    with L hQ hFine
  refine ⟨hQ.1,?_⟩
  intro band slot δ e m mp n u up vStar vpStar he hu hup hgate hgatep
    hmn hmpn hmneq prime lFine uFine hL2 hFineLow K hAlpha hAlphap
  have heOdd : Odd e := (hQ.2 band slot δ e he).1
  have hPhysical := parity_original_historical_actual_pair_eq_e_v_plus_two434
    L e m n u vStar hu hgate hmn
  have hPhysicalp := parity_original_historical_actual_pair_eq_e_v_plus_two434
    L e mp n up vpStar hup hgatep hmpn
  exact hFine.2 prime lFine uFine hL2 hFineLow K m mp n e
    (vStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (vpStar*sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up)
    hAlpha hAlphap heOdd hPhysical hPhysicalp hmneq
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFullCauchyGram -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- ORIGINAL complete post-Cauchy physical square over BOTH selected
e and n, including the genuine source cardinalities and the h=-2
alpha_m inside the m-sum, not an abstract Gram package. -/
def parityOriginalHistoricalCauchyPhysicalSquare434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℝ :=
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J,
      ‖∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
         d L band slot δ ξ rho signed Y e n m‖^2

/-- The EXACT ORIGINAL diagonal of the true historical signed
Cauchy m,m' square: m=m' while the same e,n and genuine physical
B509 H_0, original W1 and parity coefficient remain unchanged. -/
def parityOriginalHistoricalCauchyDiagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℝ :=
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J, ∑ m ∈ K,
      ‖α m * parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2

/-- Original COMPLETE offdiagonal m≠m' from the actual source
Cauchy square. The second cofactor ranges over K.erase m, so no
m=m' term enters a signed k or a character mask. -/
def parityOriginalHistoricalCauchyOffdiagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ e ∈ parityOriginalReservedCartesianESupport434 d L band slot δ,
    ∑ n ∈ J, ∑ m ∈ K, ∑ mp ∈ K.erase m,
      (α m * parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m) *
      star (α mp * parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp)

/-- The real ORIGINAL Parity(4.10) source sum of squared actual
α_m H_0 physical inner coefficients splits EXACTLY into the true
nonnegative diagonal (4.11 precursor) and entire complex offdiagonal
(4.13 precursor), retaining the original (e,n) carrier and all
normalizations. This is an equality under native Lean kernel, not a
conditional Type-II saving or diagonal moment bound. -/
theorem parity_original_historical_full_cauchy_square_diag_offdiag434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    ((parityOriginalHistoricalCauchyPhysicalSquare434 d L band slot δ ξ rho
      K J α signed Y:ℝ):ℂ) =
    ((parityOriginalHistoricalCauchyDiagonal434 d L band slot δ ξ rho
      K J α signed Y:ℝ):ℂ) +
      parityOriginalHistoricalCauchyOffdiagonal434
        d L band slot δ ξ rho K J α signed Y := by
  let ESource := parityOriginalReservedCartesianESupport434 d L band slot δ
  let F : ℕ → ℕ → ℕ → ℂ := fun e n m =>
    α m * parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m
  have hOne (e n : ℕ) :
      ((‖∑ m ∈ K, F e n m‖^2:ℝ):ℂ) =
      ((∑ m ∈ K, ‖F e n m‖^2:ℝ):ℂ) +
      (∑ m ∈ K, ∑ mp ∈ K.erase m,
        F e n m * star (F e n mp)) := by
    exact parity_original_historical_actual_e_n_square_diag_offdiag434
      d L band slot δ ξ rho K α signed Y e n
  unfold parityOriginalHistoricalCauchyPhysicalSquare434
    parityOriginalHistoricalCauchyDiagonal434
    parityOriginalHistoricalCauchyOffdiagonal434
  change ((∑ e ∈ ESource, ∑ n ∈ J,
      ‖∑ m ∈ K, F e n m‖^2:ℝ):ℂ) =
    ((∑ e ∈ ESource, ∑ n ∈ J, ∑ m ∈ K,
      ‖F e n m‖^2:ℝ):ℂ) +
      (∑ e ∈ ESource, ∑ n ∈ J, ∑ m ∈ K,
        ∑ mp ∈ K.erase m, F e n m * star (F e n mp))
  have hLsum :
      ((∑ e ∈ ESource, ∑ n ∈ J,
        ‖∑ m ∈ K, F e n m‖^2 : ℝ) : ℂ) =
      ∑ e ∈ ESource, ∑ n ∈ J,
        ((‖∑ m ∈ K, F e n m‖^2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  have hDsum :
      ((∑ e ∈ ESource, ∑ n ∈ J, ∑ m ∈ K,
        ‖F e n m‖^2 : ℝ) : ℂ) =
      ∑ e ∈ ESource, ∑ n ∈ J,
        ((∑ m ∈ K, ‖F e n m‖^2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Complex.ofReal_sum]
  rw [hLsum,hDsum]
  calc
    _ = ∑ e ∈ ESource, ∑ n ∈ J,
          (((∑ m ∈ K, ‖F e n m‖^2 : ℝ) : ℂ) +
            (∑ m ∈ K, ∑ mp ∈ K.erase m,
              F e n m * star (F e n mp))) := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      exact hOne e n
    _ = (∑ e ∈ ESource, ∑ n ∈ J,
          ((∑ m ∈ K, ‖F e n m‖^2 : ℝ) : ℂ)) +
          (∑ e ∈ ESource, ∑ n ∈ J, ∑ m ∈ K,
            ∑ mp ∈ K.erase m, F e n m * star (F e n mp)) := by
      simp_rw [Finset.sum_add_distrib]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCauchyDiagonalUnique -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- In the real original h=-2 post-Cauchy diagonal at fixed e,n,m,
TWO source physical terms with genuine gates u=m*n-2 and
u'=m*n-2 must have the SAME u. The original Ppart is not dropped. -/
theorem parity_original_historical_actual_diag_same_u434
    (m n u up : ℕ) (h1 : m*n=u+2) (h2 : m*n=up+2) : u=up := by
  omega

/-- With e>0 and the same real original u, the true selected-Q
product equality e*vStar=ordinaryPart(P,u) determines EXACTLY ONE
reserved prime×B509 skipped-Q physical integer vStar. This is not a
pointwise sup bound; it is strict source-fibre uniqueness. -/
theorem parity_original_historical_actual_diag_vStar_unique434
    (L : ℝ) (e u vStar vpStar : ℕ) (he : 0<e)
    (h1 : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (h2 : e*vpStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    vStar=vpStar := by
  apply Nat.mul_left_cancel he
  rw [h1,h2]

/-- The diagonal m=m' in the EXACT original source Cauchy square
forces u=u', vStar=vStar' and physical v=v'; there is NO second
physical or character correlation on the true diagonal. All source
P valuations and reserved Q factor are retained before equality. -/
theorem parity_original_historical_actual_full_diagonal_unique434
    (L : ℝ) (e m n u up vStar vpStar : ℕ) (he : 0<e)
    (h1 : m*n=u+2) (h2 : m*n=up+2)
    (hg1 : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (hg2 : e*vpStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up) :
    u=up ∧ vStar=vpStar ∧
      vStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u =
      vpStar*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up := by
  have huu := parity_original_historical_actual_diag_same_u434 m n u up h1 h2
  subst up
  have hvv := parity_original_historical_actual_diag_vStar_unique434
    L e u vStar vpStar he hg1 hg2
  subst vpStar
  exact ⟨rfl,rfl,rfl⟩

/-- At every actually source-selected e in original r20 Q support,
the diagonal uniqueness requires NO separately assumed e>0: source
odd-e and positivity are independent Lean theorems. -/
theorem parity_eventually_original_historical_actual_diagonal_unique_from_source434 :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (e m n u up vStar vpStar : ℕ),
      e∈parityOriginalReservedCartesianESupport434
        (sourceOriginalLiteralDepth 20 L) L band slot δ →
      m*n=u+2 → m*n=up+2 →
      e*vStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u →
      e*vpStar=sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up →
      u=up ∧ vStar=vpStar ∧
        vStar*sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u =
        vpStar*sourceOriginalPPrimePart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) up := by
  filter_upwards [parity_eventually_original_cartesian_selected_e_odd_unit434]
    with L hSource
  refine ⟨hSource.1,?_⟩
  intro band slot δ e m n u up vStar vpStar he h1 h2 hg1 hg2
  exact parity_original_historical_actual_full_diagonal_unique434
    L e m n u up vStar vpStar (hSource.2 band slot δ e he).2.1
    h1 h2 hg1 hg2
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCauchyWindow -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Actual finite source selected-Q e support truncated at the
ORIGINAL historical Parity (4.5) window EL^-88<=e<=E.
It retains every genuine selected label, including repeated Q primes. -/
def parityOriginalHistoricalCauchyActiveESupport434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) : Finset ℕ :=
  (parityOriginalReservedCartesianESupport434 d L band slot δ).filter
    (parityOriginalHistoricalEWindow434 L E)

/-- The true historical a_e coefficient vanishes OUTSIDE its exact
window, for any source δ,ξ and Mellin rho, before Cauchy. -/
theorem parity_original_historical_AE_zero_outside_window434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (e : ℕ)
    (hNot : ¬parityOriginalHistoricalEWindow434 L E e) :
    parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e = 0 := by
  unfold parityOriginalHistoricalWindowAE434
  simp only [if_neg hNot]

/-- The selected e's contributing NONZERO source Parity(4.7) coefficient
really lie in the historical finite E-window: exact source e-n Cauchy
sum can be RESTRICTED to the true valid e support without changing its
value. This avoids overpaying for all 20! Q configurations. -/
theorem parity_original_historical_cauchy_e_window_restrict_exact434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y =
    ∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot δ,
      ∑ n ∈ J,
        (parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e * β n) *
          (∑ m ∈ K, α m *
            parityOriginalHistoricalCauchyPhysicalAtENM434
              d L band slot δ ξ rho signed Y e n m) := by
  unfold parityOriginalHistoricalCauchyAtDelta434
    parityOriginalHistoricalCauchyActiveESupport434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hwin : parityOriginalHistoricalEWindow434 L E e
  · simp only [if_pos hwin]
  · have hAE0 := parity_original_historical_AE_zero_outside_window434
      d L E band slot δ ξ rho e hwin
    simp only [if_neg hwin, hAE0,zero_mul, Finset.sum_const_zero]

/-- True historical selected Q source support is contained in the
ACTUAL integer interval e<=floor E for any E>=0, with no assumptions
on the number of Q slots, original multiplicities or Fourier branches. -/
theorem parity_original_historical_cauchy_active_e_card_le_E434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (hE : 0 ≤ E) :
    (parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ).card ≤ ⌊E⌋₊+1 := by
  have hSub : parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ ⊆ Finset.range (⌊E⌋₊+1) := by
    intro e he
    have hRange := (Finset.mem_filter.mp he).2
    have hle := Nat.le_floor hRange.2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hCard := Finset.card_le_card hSub
  simpa only [Finset.card_range] using hCard

/-- Exact finite Cauchy coefficient total-square is the product of
selected original a_e(e) square mass and the true beta_n square mass,
with the HISTORICAL window and NO extra character, Fourier or k loss. -/
theorem parity_original_historical_Cauchy_coefficient_L2_factor434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (J : Finset ℕ) (β : ℕ → ℂ) :
    (∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,
        ∑ n ∈ J,
          ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e * β n‖^2) =
      (∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot δ,
          ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e‖^2) *
      (∑ n ∈ J, ‖β n‖^2) := by
  calc
    _ = ∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
          ∑ n ∈ J,
            ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e‖^2 *
              ‖β n‖^2 := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul,mul_pow]
    _ = ∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
          ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e‖^2 *
          (∑ n ∈ J, ‖β n‖^2) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_mul]

/-- Quantitative (4.10) outer Cauchy coefficient budget at true
selected e window: the exact source a_e side has ≤floor(E)+1 terms,
all bounded by A, whereas beta enters only via its genuine full L2
mass. No coefficient β sup assumption or fictitious e/m independence. -/
theorem parity_original_historical_Cauchy_coefficient_L2_card434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (J : Finset ℕ) (β : ℕ → ℂ)
    (hE : 0 ≤ E) (A : ℝ) (hA : 0 ≤ A)
    (hCoeff : ∀ e ∈ parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,
      ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e‖ ≤ A) :
    (∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,
        ∑ n ∈ J,
          ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e * β n‖^2) ≤
    ((⌊E⌋₊+1:ℕ):ℝ)*A^2*(∑ n ∈ J, ‖β n‖^2) := by
  rw [parity_original_historical_Cauchy_coefficient_L2_factor434]
  have hCoeffSum :
      (∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434
        d L E band slot δ,
          ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e‖^2) ≤
      ((⌊E⌋₊+1:ℕ):ℝ)*A^2 := by
    calc
      _ ≤ ∑ _e ∈ parityOriginalHistoricalCauchyActiveESupport434
            d L E band slot δ, A^2 := by
        apply Finset.sum_le_sum
        intro e he
        exact pow_le_pow_left₀ (norm_nonneg _) (hCoeff e he) 2
      _ = (((parityOriginalHistoricalCauchyActiveESupport434
          d L E band slot δ).card:ℝ))*A^2 := by simp
      _ ≤ ((⌊E⌋₊+1:ℕ):ℝ)*A^2 := by
        have hCard := parity_original_historical_cauchy_active_e_card_le_E434
          d L E band slot δ hE
        have hCardReal :
            (((parityOriginalHistoricalCauchyActiveESupport434
              d L E band slot δ).card:ℝ)) ≤ ((⌊E⌋₊+1:ℕ):ℝ) := by
          exact_mod_cast hCard
        exact mul_le_mul_of_nonneg_right hCardReal (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right hCoeffSum (Finset.sum_nonneg (by
    intro n hn
    exact sq_nonneg _))
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalCauchyBudget -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Quantitative ORIGINAL Parity(4.10) Cauchy with the actual historical
selected-e carrier, e-window EL^-88<=e<=E and explicit original
β_n full L2 mass. The physical inner square is exactly the source
H_0, W1, parity, h=-2 sum; no β sup or arbitrary E4.1 is assumed.
The only local input is a bound A on the TRUE source a_e(e) coefficient,
which is discharged unconditionally below by the verified (4.9) bound. -/
theorem parity_original_historical_signed_active_e_n_cauchy_budget434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (hE : 0 ≤ E)
    (A : ℝ) (hA : 0 ≤ A)
    (hCoeff : ∀ e ∈ parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ,
      ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e‖ ≤ A) :
    ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
      K J α β signed Y‖^2 ≤
      (((⌊E⌋₊+1:ℕ):ℝ)*A^2*(∑ n ∈ J, ‖β n‖^2)) *
      (∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434
         d L E band slot δ,
        ∑ n ∈ J,
          ‖∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
            d L band slot δ ξ rho signed Y e n m‖^2) := by
  let Q := parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ
  let S := Q.product J
  let a : (ℕ×ℕ) → ℂ := fun z =>
    parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho z.1 * β z.2
  let b : (ℕ×ℕ) → ℂ := fun z =>
    ∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y z.1 z.2 m
  have hFilter := parity_original_historical_cauchy_e_window_restrict_exact434
    d L E band slot δ ξ rho K J α β signed Y
  have hC := parity_original_complex_finset_cauchy434 S a b
  have hSum : (∑ z ∈ S, a z*b z) =
      ∑ e ∈ Q, ∑ n ∈ J, a (e,n)*b (e,n) := by
    exact Finset.sum_product Q J (fun z : ℕ×ℕ => a z*b z)
  have hCoef : (∑ z ∈ S, ‖a z‖^2) =
      ∑ e ∈ Q, ∑ n ∈ J, ‖a (e,n)‖^2 := by
    exact Finset.sum_product Q J (fun z : ℕ×ℕ => ‖a z‖^2)
  have hPhys : (∑ z ∈ S, ‖b z‖^2) =
      ∑ e ∈ Q, ∑ n ∈ J, ‖b (e,n)‖^2 := by
    exact Finset.sum_product Q J (fun z : ℕ×ℕ => ‖b z‖^2)
  rw [hSum,hCoef,hPhys] at hC
  have hSource :
      ‖parityOriginalHistoricalCauchyAtDelta434 d L E band slot δ ξ rho
        K J α β signed Y‖^2 ≤
      (∑ e ∈ Q, ∑ n ∈ J,
        ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e * β n‖^2) *
      (∑ e ∈ Q, ∑ n ∈ J,
        ‖∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) := by
    rw [hFilter]
    simpa only [Q,a,b] using hC
  have hCoeffBound := parity_original_historical_Cauchy_coefficient_L2_card434
    d L E band slot δ ξ rho J β hE A hA hCoeff
  have hPhysNonneg : 0 ≤ (∑ e ∈ Q, ∑ n ∈ J,
      ‖∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2) := by
    apply Finset.sum_nonneg
    intro e he
    apply Finset.sum_nonneg
    intro n hn
    exact sq_nonneg _
  exact hSource.trans (mul_le_mul_of_nonneg_right hCoeffBound hPhysNonneg)

/-- NO AXIOM or conditional coefficient hypothesis: in every actual
original r20 B590 Fourier assignment δ, the complete historical (4.10)
e,n Cauchy prefactor has source-proved polynomial L^C and EXACT real
f0/f1 Fourier transform factors; its n side is the actual β_n L2 mass.
Every original ε=1/E sign is quantified separately before squaring. -/
theorem parity_eventually_original_historical_signed_active_e_n_cauchy_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ), 1≤E →
      ∀ (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (signed : Bool) (Y : ℕ),
      ‖parityOriginalHistoricalCauchyAtDelta434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho
          K J α β signed Y‖^2 ≤
        (((⌊E⌋₊+1:ℕ):ℝ) *
          (L^parityOriginalSelectedECoefficientPolylogExponent434 *
            (∏ i : Fin (sourceOrderedLabels 20
              (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
              band slot).length,
                ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖))^2 *
          (∑ n ∈ J, ‖β n‖^2)) *
        (∑ e ∈ parityOriginalHistoricalCauchyActiveESupport434
           (sourceOriginalLiteralDepth 20 L) L E band slot δ,
          ∑ n ∈ J,
            ‖∑ m ∈ K, α m * parityOriginalHistoricalCauchyPhysicalAtENM434
              (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
              signed Y e n m‖^2) := by
  filter_upwards [parity_eventually_original_historical_window_AE_polylog434,
    eventually_gt_atTop (0:ℝ)] with L hCoeff hL
  intro band slot E hE δ ξ rho K J α β signed Y
  let A : ℝ := L^parityOriginalSelectedECoefficientPolylogExponent434 *
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖)
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg hL.le _)
    (Finset.prod_nonneg (by intro i hi; exact norm_nonneg _))
  exact parity_original_historical_signed_active_e_n_cauchy_budget434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho K J α β signed Y
    (by linarith) A hA (by
      intro e he
      exact hCoeff band slot E δ ξ rho e)
end Green64Analytic.Parity

end

end

