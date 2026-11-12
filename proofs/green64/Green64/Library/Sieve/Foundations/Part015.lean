module

public import Green64.Library.Sieve.Foundations.Part014
public import Green64.Library.Sieve.Foundations.Part013
public import Green64.Library.Weights.Part117
public import Green64.Library.Sieve.Foundations.Part010
public import Green64.Library.Sieve.Foundations.Part011
public import Green64.Library.Sieve.Foundations.Part012

@[expose] public section

/-!
# Sieve / Foundations / Part015

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalPhysicalCarrierExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- All unsmoothed physical original u-labelled Q rows outside the
actual complete Q-product gate have exactly ZERO B590/B509
branchVWeight, not an estimated contribution. The 20! orbit,
original P parity, reserved prime and Fourier frequency are retained. -/
theorem parity_original_physical_branch_zero_of_bad_fullQ_gate434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot)
    (hBad : ¬ (∏ j : Fin (d+1), ∏ i : Fin 20, (z.2 j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ z = 0 := by
  unfold parityActualOriginalAFullBranchVWeight434
  simp only [if_neg hBad]

/-- Exact carrier-restriction of the REAL original full B590 physical
h=-2 bilinear source: all zero/u=0/bad-Q rows vanish under Ψ(0)=0.
The remaining terms are exactly the source-labelled u=e*v carrier,
not an independent pseudo e/v product support. -/
theorem parity_original_full_fourier_physical_restrict_to_actual_mellin_carrier434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ) (hPsiZero : Psi 0 = 0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearFullFourierSource434
      d L E band slot ξ Psi K J α β Y =
    ∑ t ∈ parityOriginalActualMellinPhysicalCarrier434 d L band slot Y,
      parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
          α z.1*β z.2) *
        (Psi ((t.1:ℝ)/Real.exp L) : ℂ) := by
  rw [parity_original_shift_two_full_fourier_source_eq_selected_e_v_fibre434
    d L E hL hd band slot ξ Psi hPsiZero K J α β Y]
  unfold parityOriginalShiftTwoBilinearPhysicalEFibre434
  have hFibre (u : ℕ) :
      (∑ e ∈ ((Finset.univ : Finset
        (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
          (parityActualOriginalAFullBranchE434 d L band slot)),
        sourceEndpointFibre
          (Finset.univ : Finset
            (parityActualOriginalAFullBranchCarrier434 d L band slot))
          (parityActualOriginalAFullBranchE434 d L band slot)
          (parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ) e) =
      ∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
        parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ z := by
    let S : Finset (parityActualOriginalAFullBranchCarrier434 d L band slot) := Finset.univ
    let g := parityActualOriginalAFullBranchE434 d L band slot
    let w := parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ
    have h := Finset.sum_image' (s := S) (g := g)
      (f := fun e => sourceEndpointFibre S g w e) w (by intro x hx; rfl)
    simpa only [S,g,w,sourceEndpointFibre] using h
  simp_rw [hFibre]
  simp only [Finset.sum_mul, Finset.sum_mul]
  let B := parityActualOriginalAFullBranchCarrier434 d L band slot
  let gate : ℕ × B → Prop := fun t => 0 < t.1 ∧
    (∏ j : Fin (d+1), ∏ i : Fin 20, (t.2.2 j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) t.1
  let w : ℕ × B → ℂ := fun t =>
    (parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
        α z.1*β z.2)) * (Psi ((t.1:ℝ)/Real.exp L) : ℂ)
  change (∑ u ∈ Finset.range (Y+1),
      ∑ z : B,
        parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ z *
          (Psi ((u:ℝ)/Real.exp L) : ℂ) *
          (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α t.1*β t.2)) =
    ∑ t ∈ ((Finset.range (Y+1)).product (Finset.univ : Finset B)).filter gate, w t
  rw [Finset.sum_filter]
  have hProduct :
      (∑ t ∈ (Finset.range (Y+1)).product (Finset.univ : Finset B),
        if gate t then w t else 0) =
      ∑ u ∈ Finset.range (Y+1), ∑ z : B,
        if gate (u,z) then w (u,z) else 0 :=
    Finset.sum_product _ _ _
  rw [hProduct]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hu0 : u=0
  · subst u
    have hGate : ¬gate (0,z) := by
      intro hh
      exact Nat.lt_irrefl 0 hh.1
    simp only [if_neg hGate]
    simp [hPsiZero]
  · by_cases hg : (∏ j : Fin (d+1), ∏ i : Fin 20, (z.2 j i).val) =
        sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    · have hGate : gate (u,z) := ⟨Nat.pos_of_ne_zero hu0,hg⟩
      simp only [if_pos hGate]
      dsimp only [w]
      ring
    · have hGate : ¬gate (u,z) := by
        intro hh
        exact hg hh.2
      simp only [if_neg hGate]
      rw [parity_original_physical_branch_zero_of_bad_fullQ_gate434
        d L E u band slot ξ z hg]
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalPhysicalMellinSelectedE -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- TRUE original Parity §4.2 physical Mellin inner coefficient at one
selected e, with complete labelled 20! Q-orbit support and original
W1(v), parity, B590 f0/f1, skipped-Q phase, reserved prime H precursor,
and all h=-2 α_mβ_n arithmetic. The only additional frequency on v
is the genuine Mellin phase. No factorisation into a_v(v) has been
claimed: this is a literal finite carrier fibre. -/
def parityOriginalActualPhysicalMellinSelectedEInner434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (s : ℝ) (e : ℕ) : ℂ :=
  let T := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
  let g := fun t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot =>
    parityActualOriginalAFullBranchE434 d L band slot t.2
  sourceEndpointFibre T g (fun t =>
    (parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
        α z.1*β z.2)) *
      sourceOriginalPureMellinPhase434 (2*Real.pi*s)
        (parityOriginalActualMellinPhysicalV434 d L band slot t.1 t.2)) e

/-- Finite ORIGINAL source factorization of the full physical h=-2
Mellin integrand: the actual selected-e prime-product phase is
extracted OUTSIDE the original W1/parity/reserved-Q/αβ v-fibre for every
real Mellin frequency s and every original Q-Fourier vector ξ.
The common Schwartz transform and x-phase are also exposed. No e-v
independence of W1 or guessed a_e/c_r coefficients is assumed. -/
theorem parity_original_actual_physical_mellin_selected_e_outer_factor434
    (d : ℕ) (L E Z : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) (s : ℝ) :
    parityOriginalActualPhysicalBilinearMellinAmplitude434
      d L E Z band slot ξ Psi hSmooth hSupport K J α β Y s =
    ((𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
      Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ):ℂ)*Complex.I)) *
    (∑ e ∈ (parityOriginalActualMellinPhysicalCarrier434 d L band slot Y).image
        (fun t => parityActualOriginalAFullBranchE434 d L band slot t.2),
      sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
      parityOriginalActualPhysicalMellinSelectedEInner434
        d L E band slot ξ K J α β Y s e) := by
  let T := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
  let g := fun t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot =>
    parityActualOriginalAFullBranchE434 d L band slot t.2
  let F : ℂ :=
    ((𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
      Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ):ℂ)*Complex.I))
  let C : (ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot) → ℂ :=
    fun t => (parityActualOriginalAFullBranchVWeight434
      d L E t.1 band slot ξ t.2 *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
        α z.1*β z.2)) *
      sourceOriginalPureMellinPhase434 (2*Real.pi*s)
        (parityOriginalActualMellinPhysicalV434 d L band slot t.1 t.2)
  have hTerm (t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot) :
      (parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
          α z.1*β z.2)) *
        parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport
          (g t) (parityOriginalActualMellinPhysicalV434 d L band slot t.1 t.2) =
      F * (sourceOriginalPureMellinPhase434 (2*Real.pi*s) (g t) * C t) := by
    unfold parityOriginalEVMellinAmplitude434
    dsimp [F,C,g]
    ring
  have hFibre (e : ℕ) :
      sourceEndpointFibre T g (fun t =>
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) (g t) * C t) e =
      sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
        sourceEndpointFibre T g C e := by
    unfold sourceEndpointFibre
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have he : g t=e := (Finset.mem_filter.mp ht).2
    change sourceOriginalPureMellinPhase434 (2*Real.pi*s) (g t) * C t =
      sourceOriginalPureMellinPhase434 (2*Real.pi*s) e * C t
    rw [he]
  have hImage :
      (∑ t ∈ T, sourceOriginalPureMellinPhase434 (2*Real.pi*s) (g t)*C t) =
      ∑ e ∈ T.image g,
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
          sourceEndpointFibre T g C e := by
    have h := Finset.sum_image' (s := T) (g := g)
      (f := fun e => sourceEndpointFibre T g
        (fun t => sourceOriginalPureMellinPhase434 (2*Real.pi*s) (g t)*C t) e)
      (fun t => sourceOriginalPureMellinPhase434 (2*Real.pi*s) (g t)*C t)
      (by intro t ht; rfl)
    rw [←h]
    apply Finset.sum_congr rfl
    intro e he
    exact hFibre e
  unfold parityOriginalActualPhysicalBilinearMellinAmplitude434
  change (∑ t ∈ T,
      (parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
          α z.1*β z.2)) *
        parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport
          (g t) (parityOriginalActualMellinPhysicalV434 d L band slot t.1 t.2)) = _
  calc
    _ = ∑ t ∈ T, F * (sourceOriginalPureMellinPhase434 (2*Real.pi*s) (g t)*C t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hTerm t
    _ = F * (∑ t ∈ T, sourceOriginalPureMellinPhase434 (2*Real.pi*s) (g t)*C t) := by
      rw [Finset.mul_sum]
    _ = F * (∑ e ∈ T.image g,
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) e * sourceEndpointFibre T g C e) := by
      rw [hImage]
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalPhysicalMellinSelectedEIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- The genuine ORIGINAL Parity §4.2 physical h=-2 bilinear Q-labelled
carrier (with complete W1(v), P-parity, reserved Q prime, B590/B509
real Fourier ξ, and arbitrary α_m β_n for `mn=u+2`) is EXACTLY an
integral whose finite outer summation is over ORIGINAL selected integer
e. The selected-e Mellin phase is outside its physical v-fibre, and
the Schwartz Fourier weight and normalization 2π are explicit.
Integrability of the actual separated integrand is a CONCLUSION.
This is still before the integration over original B590 Fourier ξ and
the further factorisation into historical Parity (4.7) a_e,c_r,H(v_*). -/
theorem parity_original_actual_physical_bilinear_mellin_selected_e_integral434
    (d : ℕ) (L E Z : ℝ) (hZ : 0 < Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    let F : ℝ → ℂ := fun s =>
      ((𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
        Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ):ℂ)*Complex.I))
    let S := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
    let G : ℝ → ℂ := fun s => F s *
      (∑ e ∈ S.image (fun t =>
        parityActualOriginalAFullBranchE434 d L band slot t.2),
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
          parityOriginalActualPhysicalMellinSelectedEInner434
            d L E band slot ξ K J α β Y s e)
    Integrable G ∧
      (∑ t ∈ S,
        (parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
          (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
            α z.1*β z.2)) *
          (Psi ((t.1:ℝ)/Z):ℂ)) =
      ∫ s : ℝ, G s := by
  dsimp only
  let F : ℝ → ℂ := fun s =>
      ((𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
        Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ):ℂ)*Complex.I))
  let S := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
  let G : ℝ → ℂ := fun s => F s *
      (∑ e ∈ S.image (fun t =>
        parityActualOriginalAFullBranchE434 d L band slot t.2),
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
          parityOriginalActualPhysicalMellinSelectedEInner434
            d L E band slot ξ K J α β Y s e)
  have hF := parity_original_actual_physical_bilinear_mellin_integral434
    d L E Z hZ band slot ξ Psi hSmooth hSupport K J α β Y
  have hIdentity (s : ℝ) :
      parityOriginalActualPhysicalBilinearMellinAmplitude434
        d L E Z band slot ξ Psi hSmooth hSupport K J α β Y s = G s :=
    parity_original_actual_physical_mellin_selected_e_outer_factor434
      d L E Z band slot ξ Psi hSmooth hSupport K J α β Y s
  have hG : Integrable G := hF.1.congr
    (Filter.Eventually.of_forall (fun s => hIdentity s))
  refine ⟨hG,?_⟩
  calc
    _ = ∫ s : ℝ, parityOriginalActualPhysicalBilinearMellinAmplitude434
      d L E Z band slot ξ Psi hSmooth hSupport K J α β Y s := hF.2
    _ = ∫ s : ℝ, G s :=
      integral_congr_ae (Filter.Eventually.of_forall hIdentity)
end Green64Analytic.Parity

end

end

/-! ## OriginalFullFourierMellinIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- TRUE historical original Parity §4.2 full smoothed B590/B509 h=-2
bilinear SOURCE after insertion of an arbitrary original real Q-Fourier
vector ξ is EXACTLY its genuine Mellin integral, whose finite outer
sum is over the TRUE source selected-e products. Every full 20!-labelled
Q branch, source reserved prime, original W1/P odd parity, and h=-2
α_m β_n pair survives; the Mellin e-frequency phase is independent of
all physical v, and all other v weights remain in the e-fibre.
The integrability proof is a conclusion, NOT an assumption or formal
Fubini shortcut. This does NOT yet insert the multi-dimensional inverse
Fourier transform of the original f0/f1 B590 gates, nor prove Parity(4.7)
post-integration `a_e(e)`/H(v*) coefficient identity. -/
theorem parity_original_full_fourier_bilinear_source_mellin_selected_e_integral434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ) (hPsiZero : Psi 0 = 0)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    let Z := Real.exp L
    let F : ℝ → ℂ := fun s =>
      ((𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
        Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ):ℂ)*Complex.I))
    let S := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
    let G : ℝ → ℂ := fun s => F s *
      (∑ e ∈ S.image (fun t =>
        parityActualOriginalAFullBranchE434 d L band slot t.2),
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
          parityOriginalActualPhysicalMellinSelectedEInner434
            d L E band slot ξ K J α β Y s e)
    Integrable G ∧
      parityOriginalShiftTwoBilinearFullFourierSource434
        d L E band slot ξ Psi K J α β Y = ∫ s : ℝ, G s := by
  dsimp only
  have hInt := parity_original_actual_physical_bilinear_mellin_selected_e_integral434
    d L E (Real.exp L) (Real.exp_pos L) band slot ξ Psi
    hSmooth hSupport K J α β Y
  have hCarrier := parity_original_full_fourier_physical_restrict_to_actual_mellin_carrier434
    d L E hL hd band slot ξ Psi hPsiZero K J α β Y
  refine ⟨hInt.1,?_⟩
  calc
    _ = (∑ t ∈ parityOriginalActualMellinPhysicalCarrier434 d L band slot Y,
      (parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
          α z.1*β z.2)) *
        (Psi ((t.1:ℝ)/Real.exp L):ℂ)) := hCarrier
    _ = _ := hInt.2
end Green64Analytic.Parity

end

end

/-! ## OriginalPhysicalMellinCompleteAudit -/

section

/- Exact original Parity Q/P 20!-labelled u=e*v and 2π normalized Schwartz Ψ Mellin e-first source phase, kernel import-only audit. This does not claim unfiltered original ξ-Fourier B590 sum equals carrier or historical Parity(4.7) a_e. -/
open Green64Analytic.Parity

end

/-! ## OriginalPsiMellinIntegrable -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Genuine Parity(4.7) Mellin *integrability*, for every original positive
selected integer e and physical reserved-Q/P integer v, using actual
Schwartz Fourier transform of log Ψ. The Mellin e/v phases and scale
factor all have modulus one, so there is no hidden source cutoff loss
and no hypothetical L1 assumption. This establishes the analytic
precondition for finite labelled-Q sum/integral interchange. -/
theorem parity_original_real_Psi_e_v_mellin_integrable434
    (Z : ℝ) (e v : ℕ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64) :
    Integrable (fun s : ℝ =>
      (𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
      Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
      (sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) v)) := by
  let f := (𝓕 (parityOriginalLogCutoff434
    (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ))
  have hcont : Continuous (fun s : ℝ =>
      f s * Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
      (sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
       sourceOriginalPureMellinPhase434 (2*Real.pi*s) v)) := by
    unfold sourceOriginalPureMellinPhase434
    fun_prop
  apply f.integrable.mono hcont.aestronglyMeasurable
  filter_upwards [] with s
  simp only [norm_mul,Complex.norm_exp_ofReal_mul_I,
    source_original_pure_mellin_phase_norm_one434,mul_one,le_refl]
end Green64Analytic.Parity

end

end

/-! ## OriginalSourceToFourierBoxSelectedEAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The literal original Parity §4.2 B590 frequency-TRUNCATED source
representation with true selected-e OUTERMOST, including all ORIGINAL
Q/P W1/parity, 20! labelled prime factors, reserved source prime,
full f0/f1 Fourier transforms, bounded complex α_mβ_n and original
h=-2 equation `mn=u+2`. Fourier integration is over the TRUE product
Lebesgue box [-T,T]^N, not at ξ=0. Its selected-e endpoint fibres
remain physical and may depend on v, pending historical Parity(4.7)
`a_e(e)` / `c_r` / `H(v_*)` source factorisation. -/
def parityOriginalShiftTwoBilinearFourierBoxSelectedE434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
     band slot).length → ℝ,
    (∑ e ∈ (parityOriginalActualMellinPhysicalCarrier434 d L band slot Y).image
       (fun t => parityActualOriginalAFullBranchE434 d L band slot t.2),
       parityOriginalB590PhysicalFourierSelectedEInner434
         d L E band slot Psi K J α β Y ξ e)
      ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length =>
          (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- The true full original Q/P factorial h=-2 B590 physical Fourier
box is EXACTLY its selected-e outer Fourier box (source carrier u=e*v).
The integral is a real product-measure integral. No extra errors,
hypotheses on E, beta or strength of P-parity are needed. -/
theorem parity_original_B590_hminus2_fourier_box_eq_selected_e_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsiZero : Psi 0=0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearFourierBox434
      d L E band slot Psi K J α β Y T =
    parityOriginalShiftTwoBilinearFourierBoxSelectedE434
      d L E band slot Psi K J α β Y T := by
  unfold parityOriginalShiftTwoBilinearFourierBoxSelectedE434
  exact (parity_original_B590_hminus2_fourier_box_selected_e_integral434
    d L E band slot Psi hPsiZero K J α β Y T).2

/-- ORIGINAL SOURCE Parity(4.3)--(4.7) h=-2 selected-e OUTER Fourier
representation, with TRUE original product Lebesgue frequency cutoff
`[-L,L]^N`, and an unconditional arbitrary-log absolute source error:

`‖sourceOriginalA-bilinear - e-first physical Fourier box integral‖
 ≤ 2*Acoef*Bcoef*exp(L)*L^(-A)`.

For every fixed beta>0, requested A and sufficiently large L, this
retains all 20! source prime labellings, physical reserved prime and
Q products, original W1 and multiplicity-counted odd projector,
real Ψ supported [1,2], and genuine complex α_mβ_n, mn=u+2.
The proof uses the certified SOURCE Rankin (4.3), full multi-gate
Fourier Fubini, true box truncation (4.6), total W1τ arithmetic moment,
and exact finite e-endpoint regrouping.

This is NOT the complete historical (4.7) a_e, (4.17) correlation,
Type II (4.2), Parity §§5--9 sieve or Green64.green_64. -/
theorem parity_eventually_original_hminus2_source_to_selected_e_fourier_box_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β
          (⌊2*Real.exp L⌋₊) -
        parityOriginalShiftTwoBilinearFourierBoxSelectedE434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β (⌊2*Real.exp L⌋₊) L‖ ≤
      2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_source_to_fourier_box_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  rw [←parity_original_B590_hminus2_fourier_box_eq_selected_e_outer434
    (sourceOriginalLiteralDepth 20 L) L E band slot Psi
    (parity_original_Psi_support_zero434 Psi hSupport)
    K J α β (⌊2*Real.exp L⌋₊) L]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
end Green64Analytic.Parity

end

end

/-! ## OriginalB590EWindowInside -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- True Parity(4.5) retained e-window for one full 20!-labelled original
Q prime tuple and every B590 history-dependent allocation δ.
The condition is a literal non-strict interval, not a pointwise Fourier
support condition: excluded branches need not have zero box integrals. -/
def parityOriginalB590InsideEWindowAssignments434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    Finset (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :=
  (Finset.univ : Finset (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)).filter
      (fun δ =>
        let e := paritySourceOrderedAllocatedE434 δ
          (parityActualSourceRemainingFullQTuple434 d L band slot f)
        E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E)

/-- The ORIGINAL finite B590 assignment family decomposes EXACTLY
into in-window and out-of-window δ supports, including equality at
the two window endpoints, for every full Q tuple and every complex
weight function. No f0/f1 support or nonzero Fourier assumption. -/
theorem parity_original_B590_e_window_sum_partition434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (w : (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) → ℂ) :
    (∑ δ ∈ parityOriginalB590InsideEWindowAssignments434 d L E band slot f,
      w δ) +
    (∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434 d L E band slot f,
      w δ) =
    ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool, w δ := by
  classical
  let p : (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) → Prop :=
    fun δ =>
      let e := paritySourceOrderedAllocatedE434 δ
        (parityActualSourceRemainingFullQTuple434 d L band slot f)
      E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E
  have hOutside : parityOriginalB590OutsideEWindowAssignments434
      d L E band slot f = Finset.univ.filter (fun δ => ¬p δ) := by
    ext δ
    dsimp [parityOriginalB590OutsideEWindowAssignments434,p]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    simp only [not_and_or,not_le]
  change (∑ δ ∈ (Finset.univ.filter p), w δ) +
    (∑ δ ∈ parityOriginalB590OutsideEWindowAssignments434 d L E band slot f,
       w δ) = ∑ δ, w δ
  rw [hOutside]
  exact Finset.sum_filter_add_sum_filter_not Finset.univ p w

/-- Full ORIGINAL χ=0 Fourier box physical A(u), with the complete
20! source Q-factorial/P odd-parity projector and true W1, but with
all B590 assignments restricted to EXACT original Parity(4.5)
`E*L^-88 ≤ e ≤ E`. This is an actual finite physical source object. -/
def parityOriginalB590BoxPhysicalInsideEAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
      (∑ δ ∈ parityOriginalB590InsideEWindowAssignments434
        d L E band slot f,
        parityOriginalB590AllGateFourierBox434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot f i).val) T)

/-- EXACT original Fourier box identity: full physical A(u) = inside-e
plus outside-e. The latter is the already independently bounded true
Fourier leakage, not a zero of the truncated integrand. -/
theorem parity_original_B590_box_A_eq_inside_plus_outside434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
      parityOriginalB590BoxPhysicalInsideEAtU434 d L E u band slot T +
      parityOriginalB590BoxPhysicalOutsideEAtU434 d L E u band slot T := by
  unfold parityOriginalB590BoxPhysicalAAtU434
    parityOriginalB590BoxPhysicalInsideEAtU434
    parityOriginalB590BoxPhysicalOutsideEAtU434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←mul_add]
  congr 1
  exact (parity_original_B590_e_window_sum_partition434
    d L E band slot f
    (fun δ => parityOriginalB590AllGateFourierBox434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) δ
      (fun i => (parityActualSourceRemainingFullQTuple434
        d L band slot f i).val) T)).symm

/-- Literal original full alpha_m beta_n h=-2 B590 Fourier box with
all selected e in the historical source window. Nothing is asserted
about arithmetic coefficient independence of physical v. -/
def parityOriginalShiftTwoBilinearInsideEBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (parityOriginalB590BoxPhysicalInsideEAtU434 d L E u band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- Historical e-window selection is a true FULL arithmetic decomposition
of the original Fourier-box αβ source, BEFORE Cauchy. -/
theorem parity_original_hminus2_box_eq_inside_e_plus_outside434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearFourierBox434
      d L E band slot Psi K J α β Y T =
      parityOriginalShiftTwoBilinearInsideEBox434
        d L E band slot Psi K J α β Y T +
      parityOriginalShiftTwoBilinearOutsideEBox434
        d L E band slot Psi K J α β Y T := by
  unfold parityOriginalShiftTwoBilinearFourierBox434
    parityOriginalShiftTwoBilinearInsideEBox434
    parityOriginalShiftTwoBilinearOutsideEBox434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_B590_box_A_eq_inside_plus_outside434]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalB590EWindowFinalAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Complete ORIGINAL Parity §4.1--§4.2 SOURCE→TRUNCATED Fourier
representation WITH THE HISTORICAL (4.5) SELECTED-e WINDOW:

`E*L^-88 <= e <= E`.

For every fixed beta>0 and requested arbitrary inverse-log precision A,
the actual original h=-2 `sourceOriginalA` alpha_m beta_n bilinear
sum is within `4*Acoef*Bcoef*exp(L)*L^-A` of the TRUE physical
B590 Fourier-BOX `[-L,L]^N` with ALL δ branches restricted to that
e-window. Q-prime source is complete (20! factorial with repeated
labels), original W1/P-parity/reserved prime, actual Psi and mn=u+2
are unchanged. The two estimates composing the error are BOTH direct
complex norm differences: SOURCE→full Fourier box (including Rankin
beta/4 and source Fourier truncation), then full box→e-window box
(retained B590 real gate e-support + Fourier leakage, plus discarded
Ppart weighted shifted divisor Rankin).

No wrong claim of pointwise Fourier support is made. The selected-e
window is now mathematically legitimate AFTER source Fourier cutoff.
Still does NOT identify historical Parity(4.7) a_e(e) or H(v*)/c_r,
Parity(4.17), Type II(4.2), Parity §§5-9 or Green64.green_64. -/
theorem parity_eventually_original_hminus2_source_to_inside_e_fourier_box_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β
          ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoBilinearInsideEBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_source_to_fourier_box_all_log434
      beta A hbeta jQ hBand,
    parity_eventually_original_hminus2_outside_e_fourier_box_all_log434
      beta A hbeta jQ hBand] with L hSource hOutside
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro band hb E hE hEcap Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hA hB hα hβ
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let S : ℂ := parityOriginalShiftTwoBilinearSource434 d L Psi K J α β Y
  let F : ℂ := parityOriginalShiftTwoBilinearFourierBox434
    d L E band slot Psi K J α β Y L
  let I : ℂ := parityOriginalShiftTwoBilinearInsideEBox434
    d L E band slot Psi K J α β Y L
  let O : ℂ := parityOriginalShiftTwoBilinearOutsideEBox434
    d L E band slot Psi K J α β Y L
  have hSourceBound : ‖S-F‖ ≤
      2*Acoef*Bcoef*Real.exp L*L^(-A) :=
    hSource.2.2 band hb E hE hEcap Psi hSupport hPsi0 hPsi1
      slot K J α β Acoef Bcoef hA hB hα hβ
  have hOutsideBound : ‖O‖ ≤
      2*Acoef*Bcoef*Real.exp L*L^(-A) :=
    hOutside.2.2 E hE hEcap Psi hSupport hPsi0 hPsi1
      band hb slot K J α β Acoef Bcoef hA hB hα hβ
  have hSplit : F = I+O :=
    parity_original_hminus2_box_eq_inside_e_plus_outside434
      d L E band slot Psi K J α β Y L
  have hDiff : F-I = O := by rw [hSplit]; ring
  change ‖S-I‖ ≤ 4*Acoef*Bcoef*Real.exp L*L^(-A)
  calc
    _ = ‖(S-F)+(F-I)‖ := by ring
    _ ≤ ‖S-F‖+‖F-I‖ := norm_add_le _ _
    _ = ‖S-F‖+‖O‖ := by rw [hDiff]
    _ ≤ (2*Acoef*Bcoef*Real.exp L*L^(-A)) +
          (2*Acoef*Bcoef*Real.exp L*L^(-A)) :=
        add_le_add hSourceBound hOutsideBound
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalB590InsideEOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- A TRUE original full-Q historical Parity(4.5) selected-e carrier,
retaining all labelled Q primes, every B590 assignment and precisely
`E*L^-88<=e<=E`. The SOURCE selected prime product e does not depend
on the original u/P W1 or shifted alpha/beta m,n weights. -/
def parityOriginalB590InsideEFullBranchCarrier434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20) :
    Finset (parityActualOriginalAFullBranchCarrier434 d L band slot) :=
  (Finset.univ : Finset (parityActualOriginalAFullBranchCarrier434 d L band slot)).filter
    (fun z =>
      let e := parityActualOriginalAFullBranchE434 d L band slot z
      E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E)

/-- Original physical selected-e window e SUPPORT: all real e are
products of source allocated Q primes; support is EXACTLY the image
of the full Q-labelled retained-δ source carrier, without inventing
independent e values. -/
def parityOriginalB590InsideEFullSelectedSupport434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20) : Finset ℕ :=
  (parityOriginalB590InsideEFullBranchCarrier434 d L E band slot).image
    (parityActualOriginalAFullBranchE434 d L band slot)

/-- Literal original inside-window complex Q branch weight for each
true u, including factorial,W1,odd Ω parity and finite B590 Fourier
box integral. It vanishes exactly outside the original product gate. -/
def parityOriginalB590InsideEBranchWeight434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot) : ℂ :=
  ((parityActualOriginalAFullTupleWeight434 d L u z.2 : ℝ):ℂ) *
    parityOriginalB590AllGateFourierBox434 E
      (sourceActualSortedFrequencyScales 20 d L band slot) z.1
      (fun i => (parityActualSourceRemainingFullQTuple434
        d L band slot z.2 i).val) T

/-- ORIGINAL source selected-e Fourier BOX fibre. The e endpoint is
only an index; the complete real physical h=-2 arithmetic factors
remain inside the Q/P branch weights. This is NOT yet historic a_e. -/
def parityOriginalB590InsideEEndpointFibre434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) (e : ℕ) : ℂ :=
  sourceEndpointFibre
    (parityOriginalB590InsideEFullBranchCarrier434 d L E band slot)
    (parityActualOriginalAFullBranchE434 d L band slot)
    (parityOriginalB590InsideEBranchWeight434 d L E u band slot T) e

/-- Exact historical e-window selected-e ENDPOINT regrouping of
original r0=20 full labelled Q/P Fourier BOX coefficient at source u.
No Q orbit/factorial collision loss: `Finset.sum_image'` is used with
real source allocated products and original full complex weights. -/
theorem parity_original_B590_inside_e_A_eq_selected_e_fibres434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    parityOriginalB590BoxPhysicalInsideEAtU434 d L E u band slot T =
      ∑ e ∈ parityOriginalB590InsideEFullSelectedSupport434 d L E band slot,
        parityOriginalB590InsideEEndpointFibre434 d L E u band slot T e := by
  let S := parityOriginalB590InsideEFullBranchCarrier434 d L E band slot
  let g := parityActualOriginalAFullBranchE434 d L band slot
  let w := parityOriginalB590InsideEBranchWeight434 d L E u band slot T
  have hReindex := Finset.sum_image'
    (s := S) (g := g)
    (f := fun e => sourceEndpointFibre S g w e)
    w (by intro z hz; rfl)
  have hS :
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        ∑ δ ∈ parityOriginalB590InsideEWindowAssignments434 d L E band slot f,
          w (δ,f)) =
      ∑ z ∈ S, w z := by
    unfold S parityOriginalB590InsideEFullBranchCarrier434
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [parityOriginalB590InsideEWindowAssignments434,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro δ hδ
    rfl
  calc
    parityOriginalB590BoxPhysicalInsideEAtU434 d L E u band slot T =
      ∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        ∑ δ ∈ parityOriginalB590InsideEWindowAssignments434 d L E band slot f,
          w (δ,f) := by
            unfold parityOriginalB590BoxPhysicalInsideEAtU434
            apply Finset.sum_congr rfl
            intro f hf
            rw [Finset.mul_sum]
            rfl
    _ = ∑ z ∈ S, w z := hS
    _ = _ := hReindex.symm
end Green64Analytic.Parity

end

end

/-! ## OriginalB590InsideEOuterAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- GENUINE original Parity(4.5) h=-2 Fourier-BOX physical source,
with actual selected e OUTERMOST and e-window `[E L^-88,E]`.
Its inner source endpoint fibre retains all labelled original Q primes,
20! factorial normalisation, odd multiplicity parity, W1(u), reserved
source Q prime, Ψ(u/x) and true `mn=u+2` α_mβ_n. No historical
independence of inner v from e or finished `a_e(e)` is asserted. -/
def parityOriginalShiftTwoBilinearInsideEBoxOuter434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ e ∈ parityOriginalB590InsideEFullSelectedSupport434 d L E band slot,
    ∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalB590InsideEEndpointFibre434 d L E u band slot T e *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2)

/-- Exact source Parity(4.5) e-FIRST carrier identity for all alpha/beta
and all original Q/P, before analytic TypeII. No approximate support:
all δ inside the e window are retained with original weights. -/
theorem parity_original_hminus2_inside_e_box_eq_e_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearInsideEBox434
      d L E band slot Psi K J α β Y T =
    parityOriginalShiftTwoBilinearInsideEBoxOuter434
      d L E band slot Psi K J α β Y T := by
  unfold parityOriginalShiftTwoBilinearInsideEBox434
    parityOriginalShiftTwoBilinearInsideEBoxOuter434
  simp_rw [parity_original_B590_inside_e_A_eq_selected_e_fibres434]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Strongest current ORIGINAL source h=-2 Parity(4.5)–(4.7) bridge**:
for any fixed beta>0 and requested real inverse-log precision A, the
actual `sourceOriginalA` bilinear alpha/beta shifted-prime source is
within `4 Acoef Bcoef exp(L) L^-A` of its literal original r0=20
Fourier-BOX selected-e OUTER sum restricted to the true historical
window `E L^-88≤e≤E`, with all full factorial Q labels, W1, odd
multiplicity parity, reserved Q, Ψ and `mn=u+2` preserved.

This *does* close the subtle support transfer AFTER Fourier cutoff,
including nonzero individual out-of-window box integrals, paid using
the actual Fourier tail and beta/4 discarded-Ppart Rankin mass.
It does NOT yet identify the historically independent `a_e(e)`,
`c_r` or `H(v*)`; Parity(4.17), TypeII(4.2), §§5–9 sieve and exact
`Green64.green_64` remain OPEN. -/
theorem parity_eventually_original_hminus2_source_to_inside_e_outer_box_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β
          ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoBilinearInsideEBoxOuter434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_source_to_inside_e_fourier_box_all_log434
    beta A hbeta jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hE hEcap Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hA hB hα hβ
  rw [←parity_original_hminus2_inside_e_box_eq_e_outer434
    (sourceOriginalLiteralDepth 20 L) L E band slot Psi K J α β
    ⌊2*Real.exp L⌋₊ L]
  exact h.2.2 band hb E hE hEcap Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hA hB hα hβ
end Green64Analytic.Parity

end

end

/-! ## OriginalB590InsideEActualSupport -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- EVERY e occurring in the exact original Fourier-BOX selected-e
outer carrier has the source-historical Parity(4.5) real support
`E*L^-88 ≤ e ≤ E`. This is inherited from the actual Boolean/Q-product
filter, not imposed as an additional independent e coefficient. -/
theorem parity_original_B590_inside_e_outer_support_exact434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (e : ℕ)
    (he : e ∈ parityOriginalB590InsideEFullSelectedSupport434 d L E band slot) :
    E*L^((-88:ℝ)) ≤ (e:ℝ) ∧ (e:ℝ) ≤ E := by
  unfold parityOriginalB590InsideEFullSelectedSupport434 at he
  obtain ⟨z,hz,hze⟩ := Finset.mem_image.mp he
  have hz' := (Finset.mem_filter.mp hz).2
  dsimp only at hz'
  rw [hze] at hz'
  exact hz'

/-- Source selected-e outer support is positive whenever the original
real source E>0 and L>0. This is a consequence of the TRUE Parity(4.5)
window, not a hypothesis that the historical e coefficient is supported. -/
theorem parity_original_B590_inside_e_outer_positive434
    (d : ℕ) (L E : ℝ) (hL : 0 < L) (hE : 0 < E)
    (band : Fin (d+1)) (slot : Fin 20)
    (e : ℕ)
    (he : e ∈ parityOriginalB590InsideEFullSelectedSupport434 d L E band slot) :
    0 < e := by
  have h := (parity_original_B590_inside_e_outer_support_exact434 d L E band slot e he).1
  have hLow : 0 < E*L^((-88:ℝ)) :=
    mul_pos hE (Real.rpow_pos_of_pos hL _)
  have hPos : (0:ℝ) < (e:ℝ) := hLow.trans_le h
  exact_mod_cast hPos
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinInsideEBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- TRUE original h=-2 B590 Fourier-box source with full original
20! factorial-labelled Q/P W1 parity source, nonseparable Mellin
rho on u=mn-2, all δ selected-e assignments RETAINED only on the
exact historical Parity(4.5) window `E*L^-88≤e≤E`, and full mn=u+2
alpha-beta sums. Not the historical a_e after nonzero reserved σ. -/
def parityOriginalShiftTwoBilinearMellinInsideEBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (sourceOriginalPureMellinPhase434 rho u *
      parityOriginalB590BoxPhysicalInsideEAtU434 d L E u band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- The ORIGINAL Mellin rho-twisted h=-2 Fourier-box source splits
EXACTLY into real selected-e Parity(4.5) in-window and out-window
contributions. No assumed pointwise zero outside e window, and the
Mellin rho phase is kept on the same source u in both terms. -/
theorem parity_original_hminus2_mellin_box_eq_inside_e_plus_outside434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearMellinFourierBox434
      d L E band slot Psi K J α β rho Y T =
    parityOriginalShiftTwoBilinearMellinInsideEBox434
      d L E band slot Psi K J α β rho Y T +
    parityOriginalShiftTwoBilinearMellinOutsideEBox434
      d L E band slot Psi K J α β rho Y T := by
  unfold parityOriginalShiftTwoBilinearMellinFourierBox434
    parityOriginalShiftTwoBilinearMellinInsideEBox434
    parityOriginalShiftTwoBilinearMellinOutsideEBox434
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_B590_box_A_eq_inside_plus_outside434]
  ring

/-- TRUE original h=-2 Mellin rho full-source `sourceOriginalA`
versus its REAL selected-e historical Parity(4.5) truncated Fourier-box
source, uniform in every rho and reserved Q band/slot, with direct
error `4 Acoef Bcoef expL L^-A`: 2AB for SOURCE→full physical H BOX
including original beta/4 Rankin and source Schwartz Fourier tails,
plus 2AB for deleting nonzero out-of-window Fourier branch leakage.
This is still the original B590 in-window Q-sum, not yet the physical
H(vStar)-factorized in-window integral at nonzero rho. -/
theorem parity_eventually_original_hminus2_mellin_source_to_inside_e_box_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (rho : ℝ),
      ‖parityOriginalShiftTwoBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β rho
          ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoBilinearMellinInsideEBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β rho ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_source_mellin_to_H_box_all_log434
      betaP A hbetaP jQ hBand,
    parity_eventually_original_hminus2_mellin_outside_e_fourier_box_all_log434
      betaP A hbetaP jQ hBand] with L hSource hOutside
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let S : ℂ := parityOriginalShiftTwoBilinearMellinSource434
    d L Psi K J α β rho Y
  let F : ℂ := parityOriginalShiftTwoBilinearMellinFourierBox434
    d L E band slot Psi K J α β rho Y L
  let I : ℂ := parityOriginalShiftTwoBilinearMellinInsideEBox434
    d L E band slot Psi K J α β rho Y L
  let O : ℂ := parityOriginalShiftTwoBilinearMellinOutsideEBox434
    d L E band slot Psi K J α β rho Y L
  have hF : F = parityOriginalShiftTwoBilinearMellinHBox434
      d L E band slot Psi K J α β rho Y L :=
    parity_original_hminus2_bilinear_mellin_fourier_box_eq_source_H434
      d L E (by nlinarith [hSource.1]) rfl band slot Psi K J α β rho Y L
  have hSourceBound : ‖S-F‖ ≤
      2*Acoef*Bcoef*Real.exp L*L^(-A) := by
    rw [hF]
    exact hSource.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
      slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  have hOut : ‖O‖ ≤ 2*Acoef*Bcoef*Real.exp L*L^(-A) :=
    hOutside.2.2 E hElo hEhi Psi hSupport hPsiPos hPsiLe
      band hb slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  have hSplit : F = I+O :=
    parity_original_hminus2_mellin_box_eq_inside_e_plus_outside434
      d L E band slot Psi K J α β rho Y L
  have hDiff : F-I = O := by rw [hSplit]; ring
  change ‖S-I‖ ≤ 4*Acoef*Bcoef*Real.exp L*L^(-A)
  calc
    _ = ‖(S-F)+(F-I)‖ := by ring
    _ ≤ ‖S-F‖+‖F-I‖ := norm_add_le _ _
    _ = ‖S-F‖+‖O‖ := by rw [hDiff]
    _ ≤ 2*Acoef*Bcoef*Real.exp L*L^(-A) +
       2*Acoef*Bcoef*Real.exp L*L^(-A) := add_le_add hSourceBound hOut
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinInsideEOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The TRUE full source-original selected-e historical (4.5) window
Fourier BOX with outer selected e and arbitrary original Mellin rho.
Its inner e-endpoint fibre still retains the ORIGINAL Q/P W1, odd
multiplicity parity and h=-2 alpha beta, and is NOT substituted with
a conjectural independent e coefficient. The Mellin phase is at
original `u=mn-2`; the TRUE source Qproduct gate entails u=e*v. -/
def parityOriginalShiftTwoBilinearMellinInsideEBoxOuter434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ e ∈ parityOriginalB590InsideEFullSelectedSupport434 d L E band slot,
    ∑ u ∈ Finset.Ioc 0 Y,
      (sourceOriginalPureMellinPhase434 rho u *
        parityOriginalB590InsideEEndpointFibre434 d L E u band slot T e *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2)

/-- Exact original Parity §4.2 full selected e-FIRST finite source
regrouping with the historical window and arbitrary Mellin rho:
all 20! original labelled Q tuples, true B590 f0/f1 Fourier BOX
integrals, real W1/P odd projector and h=-2 mn=u+2 remain literal.
This equality is independent of Rankin precision and is not a
pointwise Fourier ξ support assertion. -/
theorem parity_original_hminus2_mellin_inside_e_box_eq_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearMellinInsideEBox434
      d L E band slot Psi K J α β rho Y T =
    parityOriginalShiftTwoBilinearMellinInsideEBoxOuter434
      d L E band slot Psi K J α β rho Y T := by
  unfold parityOriginalShiftTwoBilinearMellinInsideEBox434
    parityOriginalShiftTwoBilinearMellinInsideEBoxOuter434
  simp_rw [parity_original_B590_inside_e_A_eq_selected_e_fibres434]
  let M := parityOriginalB590InsideEFullSelectedSupport434 d L E band slot
  let F : ℕ → ℕ → ℂ := fun e u =>
    parityOriginalB590InsideEEndpointFibre434 d L E u band slot T e
  let P : ℕ → ℂ := fun u => sourceOriginalPureMellinPhase434 rho u
  let S : ℕ → ℂ := fun u => (Psi ((u:ℝ)/Real.exp L):ℂ)
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α z.1*β z.2
  change (∑ u ∈ Finset.Ioc 0 Y,
      (P u * (∑ e ∈ M, F e u) * S u) * B u) =
    ∑ e ∈ M, ∑ u ∈ Finset.Ioc 0 Y,
      (P u * F e u * S u) * B u
  calc
    _ = ∑ u ∈ Finset.Ioc 0 Y,
        ∑ e ∈ M, (P u * F e u * S u) * B u := by
          apply Finset.sum_congr rfl
          intro u hu
          calc
            (P u * (∑ e ∈ M, F e u) * S u) * B u =
                ((∑ e ∈ M, P u * F e u) * S u) * B u := by
                  conv_lhs =>
                    arg 1
                    arg 1
                    rw [Finset.mul_sum]
            _ = (∑ e ∈ M, P u * F e u * S u) * B u := by
                  conv_lhs =>
                    arg 1
                    rw [Finset.sum_mul]
            _ = ∑ e ∈ M, (P u * F e u * S u) * B u := by
                  conv_lhs => rw [Finset.sum_mul]
    _ = _ := Finset.sum_comm

/-- COMPLETE original unsmoothed h=-2 sourceOriginalA, for EVERY
real Mellin rho, approximated by the selected-e-FIRST original
frequency BOX [-L,L]^N with genuine historical (4.5) source support
`E L^-88≤e≤E`, original Q/P factorial, W1 odd Omega parity and
actual finite alpha_m beta_n mn=u+2. Uniform direct source complex
error `<=4 Acoef Bcoef expL L^-A` for arbitrary fixed beta>0 and A.

This establishes selected-e outer support after Fourier cutoff at
nonzero rho, without a false pointwise ξ zero or external coefficient
assumption. The inner endpoint still requires its literal fixed-
frequency Fourier integration identification with native H(vStar)
and historical epsilon convention before Parity(4.7) is complete. -/
theorem parity_eventually_original_hminus2_mellin_source_to_inside_e_outer_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (rho : ℝ),
      ‖parityOriginalShiftTwoBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β rho
          ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoBilinearMellinInsideEBoxOuter434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β rho ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_mellin_source_to_inside_e_box_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  rw [←parity_original_hminus2_mellin_inside_e_box_eq_outer434
    (sourceOriginalLiteralDepth 20 L) L E band slot
    Psi K J α β rho ⌊2*Real.exp L⌋₊ L]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
end Green64Analytic.Parity

end

end

/-! ## OriginalSourceToMellinAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16500000

/-- Literal ORIGINAL unsmoothed h=-2 source bilinear sum with full
20!-labelled Q/P parity/W1 is within arbitrary inverse-log error of
the actual normalized Schwartz Mellin integral with selected-e OUTER
sum and actual original reserved/P/skipped-Q physical v-fibre.
All finite alpha,beta supports satisfy true mn=u+2 and are uniformly
bounded, and β/4 Ppart Rankin is applied BEFORE Cauchy. The original
B590/B509 Q Fourier phase is evaluated at ξ=0. This is a proper
SOURCE→Mellin physical bridge, NOT a Fourier inversion of the original
f0/f1 gates and NOT historical Parity (4.7) a_e(e) identification. -/
theorem parity_eventually_original_hminus2_source_to_selected_e_mellin_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
        (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ))) →
        (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      let d := sourceOriginalLiteralDepth 20 L
      let Y := ⌊2*Real.exp L⌋₊
      let Z := Real.exp L
      let ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
        band slot).length → ℝ := fun _ => 0
      let F : ℝ → ℂ := fun s =>
        ((𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
          Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ):ℂ)*Complex.I))
      let S := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
      let G : ℝ → ℂ := fun s => F s *
        (∑ e ∈ S.image (fun t =>
          parityActualOriginalAFullBranchE434 d L band slot t.2),
          sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
            parityOriginalActualPhysicalMellinSelectedEInner434
              d L E band slot ξ K J α β Y s e)
      Integrable G ∧
      ‖parityOriginalShiftTwoBilinearSource434 d L Psi K J α β Y -
          ∫ s : ℝ, G s‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_shift_two_bilinear_source_to_physical_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hPsiSupport hPsi0 hPsi1
    hSmooth hPsiSupport64 slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ := fun _ => 0
  have hLp : 0 < L := by nlinarith [h.1]
  have hPsiZero := parity_original_Psi_support_zero434 Psi hPsiSupport
  have hM := parity_original_full_fourier_bilinear_source_mellin_selected_e_integral434
    d L E hLp rfl band slot ξ Psi hPsiZero hSmooth hPsiSupport64
    K J α β Y
  have hBound := h.2.2 band hb E hElo hEhi Psi hPsiSupport
    hPsi0 hPsi1 slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  have hPhysical :
      parityOriginalShiftTwoBilinearB590Physical434
        d L E band slot Psi K J α β Y =
      parityOriginalShiftTwoBilinearFullFourierSource434
        d L E band slot ξ Psi K J α β Y := rfl
  rw [hPhysical,hM.2] at hBound
  exact ⟨hM.1,hBound⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalSourceMellinCompleteAudit -/

section

/- Green64 rev64 complete literal original h=-2 sourceOriginalA bilinear B590 ξ0 to true e-first Mellin integral, after original beta/4 Pcap Rankin, 20! Q/P W1/parity and true mn=u+2. Import-only kernel audit; NOT Parity(4.7) a_e or source E4.1. -/
open Green64Analytic.Parity

end

/-! ## OriginalSourceFourierMellinCompleteAudit -/

section

/- Original Parity r0=20 source h=-2 B590/B509 αβ SOURCE→selected-e Mellin at ξ=0 with arbitrary all-log Rankin error; exact single real B590 f0/f1 Fourier inversion and all 2^N Fourier L1 variation. Import-only kernel audit. NOT full Parity(4.7), E4.1, TypeII or Green64. -/
open Green64Analytic.Parity

end

/-! ## OriginalB590FullFourierSourceAudit -/

section

/- Green64 rev64: complete original h=-2 sourceOriginalA αβ → N-dimensional source real B590 Fourier integral with factorial W1/P-parity/Q reserve, Rankin all-log, integral_Fin product-measure and finite Fubini. No historical a_e/E4.1 claim. -/
open Green64Analytic.Parity

end

/-! ## OriginalB590BoxSourceAudit -/

section

/- Lean 4.34.1 import-only kernel audit of complete original h=-2 SOURCE→truncated [-L,L]^N B590 Fourier integral and exact W1/parity/Q/alpha-beta error. NOT historical a_e, (4.17), TypeII or Green64. -/
open Green64Analytic.Parity

end

/-! ## OriginalB590FourierSelectedEAndBoxAudit -/

section

/- Native Lean 4.34.1 import-only kernel audit: full original h=-2 SOURCE→ Fourier box with arbitrary inverse-log saving, and full Q/P W1/parity B590 Fourier integrand and integral EXACT selected-e outer reindex. No Parity(4.7) a_e coefficient asserted. -/
open Green64Analytic.Parity

end

/-! ## OriginalSelectedEFourierBoxFullAudit -/

section

/- Green64 rev64 source AUTHOR independent-kernel audit of genuine original h=-2 SOURCE→selected-e OUTER r0=20 B590 multi-dimensional Fourier BOX [-L,L]^N with literal factorial Q/P parity, W1 and alpha beta mn=u+2. Does not claim historical Parity(4.7) a_e, H/c_r, (4.17), Type II, sieve or Green64. -/
open Green64Analytic.Parity

end

/-! ## OriginalEWindowCompleteAudit -/

section

/- Green64 rev64 ORIGINAL Parity(4.5) true e-window E L^-88<=e<=E after B590 Fourier box truncation: retained beta/4 Ppart all-log Fourier leakage, discarded Ppart actual W1×Fourier-variation×shifted divisor Rankin, exact h=-2 alpha beta complex bound, and genuine selected-e OUTER support. Native kernel audit only, not final a_e/c_r/H(v*) or TypeII proof. -/
open Green64Analytic.Parity

end

/-! ## OriginalEWindowAndCoeffAudit -/

section

/- Green64 rev64 native Lean kernel audit: ORIGINAL Parity(4.5) e-window supported h=-2 SOURCE→true physical selected-e OUTER B590 Fourier BOX all-log error, and source-selected Q Fourier coefficient (4.9) polynomial-in-L bound. All source Q/P parity and alpha/beta arithmetic actual; NOT complete a_e/c_r/H(v*), Parity(4.17), Type II, or Green64. -/
open Green64Analytic.Parity

end

/-! ## OriginalEWindowCoefficientFullAudit -/

section

/- Kernel audit of original source Parity(4.5) e-window selected-e OUTER B590 Fourier-box all-log source h=-2 alpha/beta, actual Parity(4.9) selected-Q Fourier e-only coefficient polylog, exact coefficient×native B509 skipped-Q residual and factorial-cancelled residual pointwise bound. NOT literal reserved-prime H(v*) nor (4.17), TypeII or Green64. -/
open Green64Analytic.Parity

end

/-! ## OriginalReservedHFullSourceAudit -/

section

/- Green64 rev64 full native author Lean kernel audit: exact ORIGINAL Parity(4.7)-(4.9) source reserved Q prime p, all labelled nonreserved Q with factorial, selected e and physical vStar=p*skippedQ, c_r actual B509 residual, H(vStar)=sum_(p*r=vStar) p^(iσ)c_r and |H|<=tau(vStar), physical v=vStar*Ppart(u) and original W1/P odd Omega projector invariance, genuine global e/vStar source and full original Q product gate `e*vStar=ordinaryPart(P,u)` source equality, full B590 f0/f1 Fourier integrand with global E character and W1 parity equality to e-only selected-Q coefficient × physical W1(v)oddProjector(v)H(vStar), and fixed/polylog bounds. Does NOT assert postintegrated historic a_e, epsilon sign convention, signed Parity(4.17), full TypeII or Green64. -/
open Green64Analytic.Parity

end

/-! ## OriginalActualHBoxMellinSourceTerminalAudit -/

section

/- Green64 rev64 native kernel audit. TRUE original unsmoothed sourceOriginalA h=-2 αβ mn=u+2 with original 20!-labelled Q/P, W1, odd Omega projector and REAL Ψ supported [1,2]; real B590 Fourier BOX [-L,L]^N, genuine selected Q e-only, reserved-prime H(v*)=sum_(p*r=v*) p^(iσ)c_r with actual B509 factorial residual and |H|<=τ, e*v=source u; arbitrary nonzero physical Mellin rho: e^iρ a_e^selected × v^iρ W1(v)oddProjector(v) H_0(v*). Exact finite Fourier integral and bilinear Fubini for all rho; original SOURCE-to-physical B590 buffered error and full B590-to-Fourier-BOX cutoff both <=AB exp L L^-A UNIFORMLY in rho, terminal sourceOriginalA→H rho Fourier box <=2AB exp L L^-A. Reserved σ=0; source e-window cut AFTER Fourier on H-side at arbitrary rho, postintegrated Mellin and historical epsilon(v) sign NOT completed. TypeII, Parity(4.17), Green64 remain OPEN. -/
open Green64Analytic.Parity

end

/-! ## OriginalActualHBoxMellinEWindowAudit -/

section

/- Lean 4.34.1 native kernel audit of exact original sourceOriginalA h=-2 alpha beta Q/P 20! factorial source-to-reserved H(vStar) Fourier BOX, nonzero source Mellin rho e^iρ×v^iρ original physical selected Q×W1 oddΩ H_0 source coefficients and UNIFORM-in-rho direct original SOURCE-to-Hbox 2AB exp L L^-A; additionally the original full B590 Fourier BOX out-of-Parity(4.5)-e-window tail is uniformly <=2AB exp L L^-A under arbitrary Mellin rho, its in-window e-FIRST full Q original SOURCE object is exact and <=4AB exp L L^-A from original unsmoothed source. The historical e-window e-first B590 source is not YET identified with e-first H(vStar) integral after the restricted source filter; nonzero reserved prime sigma, full postintegration Parity(4.7), historical epsilon(v) sign, Parity(4.17), TypeII and Green64 remain OPEN. -/
open Green64Analytic.Parity

end

/-! ## OriginalSignedProjection -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The two manuscript Parity(4.7) SIGNED endpoint choices are `ε=1`
and `ε=E`, where E(v) is the actual multiplicity-counted P-group
Liouville sign. These are independent source branches, not the odd
projector: that projector is their difference divided by two. -/
def parityOriginalPSignedEpsilon434 (P : Finset ℕ) (signed : Bool)
    (n : ℕ) : ℝ :=
  if signed then (-1:ℝ)^sourceOriginalPParityExponent P n else 1

/-- The true two signed sources have |ε|=1 at every integer,
including repeated P prime powers. -/
theorem parity_original_P_signed_epsilon_abs_one434
    (P : Finset ℕ) (signed : Bool) (n : ℕ) :
    |parityOriginalPSignedEpsilon434 P signed n| = 1 := by
  unfold parityOriginalPSignedEpsilon434
  cases signed <;> simp [abs_pow]

/-- Original source odd projector is EXACTLY half the difference
between the two manuscript signed endpoint choices, without assuming
signed parity positivity or moving the sign into a Q coefficient. -/
theorem parity_original_odd_projector_eq_signed_difference434
    (P : Finset ℕ) (n : ℕ) :
    ((1-(-1:ℝ)^sourceOriginalPParityExponent P n)/2) =
      (parityOriginalPSignedEpsilon434 P false n -
       parityOriginalPSignedEpsilon434 P true n)/2 := by
  simp [parityOriginalPSignedEpsilon434]

/-- The ACTUAL ORIGINAL full Q-tuple arithmetic coefficient for each
independent Parity signed branch. The whole 20! original labelled Q/P
carrier, original factorial and true W1 are present; only the true
signed `ε=1` or `ε=E` replaces the original odd projector.
Unlike the odd-projected source, these coefficients need not be
nonnegative in the ε=E branch. -/
def parityActualOriginalSignedFullTupleWeight434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) : ℝ :=
  if (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
    sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
    (∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)) *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed u
  else 0

/-- Literal source ORIGINAL A full labelled Q-factorial weight is
exactly half the difference of two signed branches, pointwise for
EVERY u and EVERY complete Q-labelled tuple (including wrong Q gates).
No error bound or Riemann integration; this is the source equality
needed before independent ε=1/E signed correlations. -/
theorem parity_original_actual_fullQ_weight_signed_half_difference434
    (d : ℕ) (L : ℝ) (u : ℕ)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) :
    parityActualOriginalAFullTupleWeight434 d L u f =
      (parityActualOriginalSignedFullTupleWeight434 d L u false f -
       parityActualOriginalSignedFullTupleWeight434 d L u true f)/2 := by
  unfold parityActualOriginalAFullTupleWeight434
    parityActualOriginalSignedFullTupleWeight434
  split_ifs with h
  · rw [parity_original_odd_projector_eq_signed_difference434]
    ring
  · ring

/-- Exactly the true original Q-labelled arithmetic A(u) splits as
two independently signed SOURCE sums (ordinary and original P-sign)
before any squaring. The existing original A source definition is
unchanged; signs are NOT inserted into α or β. -/
theorem parity_original_actual_A_eq_signed_Q_sums434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (u : ℕ) :
    sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u =
      ((∑ f : ((j : Fin (d+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
          parityActualOriginalSignedFullTupleWeight434 d L u false f) -
       (∑ f : ((j : Fin (d+1)) → Fin 20 →
          {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
          parityActualOriginalSignedFullTupleWeight434 d L u true f))/2 := by
  rw [parity_actual_original_A_all_Q_labelled_exact434 d L hL u]
  change (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      parityActualOriginalAFullTupleWeight434 d L u f) = _
  simp_rw [parity_original_actual_fullQ_weight_signed_half_difference434]
  rw [←Finset.sum_div, Finset.sum_sub_distrib]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedBilinearSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The literal ORIGINAL all-20!-labelled source Q-P arithmetic
coefficient for Parity's independent signed branch ε=1 or ε=E.
The complete Q product gate and original P weight are retained,
where E=(-1)^Ω_P is multiplicity counted. -/
def parityOriginalSignedSourceA434
    (d : ℕ) (L : ℝ) (signed : Bool) (u : ℕ) : ℝ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
      parityActualOriginalSignedFullTupleWeight434 d L u signed f

/-- The original unsmoothed source coefficient A(u) is exactly
half the difference between the two true signed SOURCE coefficients,
not a choice of just one signed Parity branch. -/
theorem parity_original_source_A_eq_half_signed434
    (d : ℕ) (L : ℝ) (hL : 0 < L) (u : ℕ) :
    sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u =
    (parityOriginalSignedSourceA434 d L false u -
     parityOriginalSignedSourceA434 d L true u)/2 :=
  parity_original_actual_A_eq_signed_Q_sums434 d L hL u

/-- A genuine original Parity(4.7) signed h=-2 bilinear SOURCE
before ANY Fourier/Mellin approximation. The two independent
objects carry ε=1 or ε=E through the true Q factorial sum,
real Psi(u/exp L), and the original finite alpha_m beta_n pairs
subject to mn=u+2. No division by the odd projector. -/
def parityOriginalShiftTwoSignedBilinearSource434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    (((parityOriginalSignedSourceA434 d L signed u *
       Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)) *
    (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      α z.1*β z.2)

/-- ORIGINAL literal odd-projected source h=-2 bilinear is exactly
half the difference of the independent ε=1 and ε=E signed SOURCE
sums, without dropping u=0 or changing alpha/beta supports. This
is required BEFORE squaring for Parity(4.17), rather than inserting a
projector after the signed correlation. -/
theorem parity_original_hminus2_odd_source_eq_signed_half_difference434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) :
    parityOriginalShiftTwoBilinearSource434 d L Psi K J α β Y =
      (parityOriginalShiftTwoSignedBilinearSource434
        d L Psi K J α β false Y -
       parityOriginalShiftTwoSignedBilinearSource434
        d L Psi K J α β true Y)/2 := by
  unfold parityOriginalShiftTwoBilinearSource434
    parityOriginalShiftTwoSignedBilinearSource434
  rw [←Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_source_A_eq_half_signed434 d L hL u]
  push_cast
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedPhysicalTransfer -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- For every true source original selected-Q allocation e, the
complete original P-group sign E(u)=(-1)^Ω_P(u) transports exactly
to the physical v under u=e*v, with multiplicities preserved.
The same holds for the unsigned ε=1 branch. -/
theorem parity_original_signed_epsilon_actual_Q_product_transfer434
    (L : ℝ) (hL : 0 < L)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1))
    (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool)
    (rest : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20
        (sourceOriginalLiteralDepth 20 L) L band slot i})
    (v : ℕ) (hv : v ≠ 0) (signed : Bool) :
    parityOriginalPSignedEpsilon434
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed
      (paritySourceOrderedAllocatedE434 δ rest * v) =
    parityOriginalPSignedEpsilon434
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed v := by
  cases signed
  · simp [parityOriginalPSignedEpsilon434]
  · unfold parityOriginalPSignedEpsilon434
    have h := parity_actual_Q_allocated_e_P_weight_parity_invariant434
      L hL band slot δ rest v hv
    rw [h.2.1]

/-- Both signed Parity endpoints preserve the actual original source
W1(P,u) and their epsilon factor under the genuine original
source e=selected Q product. The identity holds separately for
ε=1 and ε=E, BEFORE their half difference is formed. -/
theorem parity_original_signed_W1_epsilon_actual_Q_transfer434
    (L : ℝ) (hL : 0 < L)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1))
    (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length → Bool)
    (rest : (i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length) →
      {q : ℕ // q ∈ sourceActualSortedQ 20
        (sourceOriginalLiteralDepth 20 L) L band slot i})
    (v : ℕ) (hv : v ≠ 0) (signed : Bool) :
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
      (paritySourceOrderedAllocatedE434 δ rest*v) *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed
        (paritySourceOrderedAllocatedE434 δ rest*v) =
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed v := by
  rw [(parity_actual_Q_allocated_e_P_weight_parity_invariant434
    L hL band slot δ rest v hv).1,
    parity_original_signed_epsilon_actual_Q_product_transfer434
      L hL band slot δ rest v hv signed]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedReservedGate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- ORIGINAL Parity ε=1/E signed full-Q Fourier source at a fixed
physical integer u, allocation δ and source frequency ξ. The
signed full labelled Q-tuple weight has its original 20! factorial,
W1(P,u), actual Qproduct gate, and source multiplicity sign. -/
def parityOriginalSignedFullQSourceFourierAtU434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ) *
      paritySourceFullSlotFourierPhase434
        (sourceActualSortedFrequencyScales 20 d L band slot) ξ δ
        (parityActualSourceRemainingFullQTuple434 d L band slot f)

/-- The genuine fixed-u SOURCE Parity signed ε=1 or ε=E full Q
factorial Fourier coefficient after moving the reserved prime to its
real source slot. This is the ACTUAL original reserved Q-product gate
and a single explicit W1(P,u)*ε(P,u), not the odd projector. -/
def parityOriginalSignedReservedProductGate434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  (((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      parityOriginalPSignedEpsilon434
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) signed u):ℝ):ℂ) *
    parityOriginalReservedFullQPhysicalProductGate434 d L band slot δ ξ 0 u

/-- TRUE original labelled Q source ε=1/E branch, at EACH u,δ,ξ,
exactly equals its reserved-Q full physical gate, with no assumption
that ε=E branch is positive. The source Q-prime labels are moved by
the verified real micro-Q/sorted remaining equivalence, including
original full factorial (20!)^{-(d+1)} in ℝ and its ℂ cast. -/
theorem parity_original_signed_fullQ_source_eq_reserved_gate434
    (d : ℕ) (L : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalSignedFullQSourceFourierAtU434 d L u signed band slot δ ξ =
    parityOriginalSignedReservedProductGate434 d L u signed band slot δ ξ := by
  let D := parityActualOriginalReservedSortedQEquiv434 d L band slot
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let P := sourceOriginalPAllActualBands 20 L
  let Fact : ℝ := ∏ _j : Fin (d+1), (1:ℝ)/((20:ℕ).factorial:ℝ)
  let F : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}) → ℂ :=
    fun f => ((parityActualOriginalSignedFullTupleWeight434 d L u signed f:ℝ):ℂ) *
      paritySourceFullSlotFourierPhase434 s ξ δ
        (parityActualSourceRemainingFullQTuple434 d L band slot f)
  have hEquiv : (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}), F f) =
      ∑ x : ({q : ℕ // q ∈ sourceOriginalQActualBands 20 d L band} ×
        ((i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length) →
          {q : ℕ // q∈sourceActualSortedQ 20 d L band slot i})),
        F (D.symm x) := by
    have h := parity_original_reserved_sum_generic434 d L band slot
      (fun x => F (D.symm x))
    simpa only [D,parityActualOriginalReservedSortedQEquiv434,
      Equiv.symm_apply_apply] using h
  unfold parityOriginalSignedFullQSourceFourierAtU434
    parityOriginalSignedReservedProductGate434
  change (∑ f, F f) = _
  rw [hEquiv]
  rw [Fintype.sum_prod_type]
  unfold parityOriginalReservedFullQPhysicalProductGate434
  rw [Finset.sum_subtype (sourceOriginalQActualBands 20 d L band)
    (by intro p; rfl)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest hrest
  let f := D.symm (p,rest)
  have hD : D f=(p,rest) := D.apply_symm_apply _
  have hfull := parity_actual_original_reserved_sorted_equiv_product434
    d L band slot f
  rw [hD] at hfull
  have hRest := parity_actual_original_reserved_sorted_equiv_rest434
    d L band slot f
  rw [hD] at hRest
  have hFact : (sourceActualSortedFactorial 20 d:ℂ) = (Fact:ℂ) := by
    unfold sourceActualSortedFactorial Fact
    push_cast
    rfl
  unfold F parityActualOriginalSignedFullTupleWeight434
  rw [←hRest,hfull]
  by_cases hgate : p.val*(∏ i, (rest i).val) =
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u
  · dsimp only [P,s] at hgate ⊢
    simp only [if_pos hgate]
    rw [show sourceOriginalPureMellinPhase434 (0:ℝ) p.val=1 by
      simp [sourceOriginalPureMellinPhase434]]
    rw [hFact]
    dsimp only [Fact]
    push_cast
    ring_nf
  · dsimp only [P,s] at hgate ⊢
    simp only [if_neg hgate]
    norm_num
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedReservedHPhysical -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Genuine original Parity ε=1 or ε=E signed v-side source
physical coefficient, with full native reserved Q convolution
`H(vStar)=Σ_(p*r=vStar) p^(iσ)c_r`, original W1(P,v), multiplicity
sign epsilon(v) and true imaginary phase v^(i rho).
The two signed choices are separate BEFORE Cauchy. -/
def parityOriginalReservedSignedPhysicalAV434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ σ rho : ℝ) (signed : Bool) (vStar v : ℕ) : ℂ :=
  sourceOriginalPureMellinPhase434 rho v *
    (((sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) v *
       parityOriginalPSignedEpsilon434
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
         signed v):ℝ):ℂ) *
    parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar

/-- On the true source paired endpoint (e,vStar) satisfying
`e*vStar=ordinaryPart(P,u)` and u>0, the ORIGINAL two signed
P-weights W1(P,u)*epsilon(u) transport exactly to
W1(P,v)*epsilon(v), with v=vStar*Ppart(P,u).
No signed branch is obtained by dividing the odd projector. -/
theorem parity_original_signed_actual_gate_P_weight_transfer434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (signed : Bool) (z : ℕ×ℕ)
    (hz : z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ)
    (hgate : z.1*z.2=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    let P := sourceOriginalPAllActualBands 20 L
    let v := z.2*sourceOriginalPPrimePart (Finset.univ.biUnion P) u
    sourceOriginalW1 P u * parityOriginalPSignedEpsilon434
      (Finset.univ.biUnion P) signed u =
    sourceOriginalW1 P v * parityOriginalPSignedEpsilon434
      (Finset.univ.biUnion P) signed v := by
  subst d
  dsimp only
  let P := sourceOriginalPAllActualBands 20 L
  let v := z.2*sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  have hsplit := source_original_ordinary_times_P_part
    (Finset.univ.biUnion P) u hu
  have hEv : z.1*v=u := by
    dsimp [v]
    calc
      _ = (z.1*z.2)*sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by ac_rfl
      _ = sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u *
        sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by rw [hgate]
      _ = u := hsplit
  have hv : v ≠ 0 := by
    intro h0; apply hu; rw [←hEv,h0,mul_zero]
  unfold parityOriginalReservedFullQEVStarSupport434 at hz
  obtain ⟨⟨p,rest⟩,hr,hendpoint⟩ := Finset.mem_image.mp hz
  have he : paritySourceOrderedAllocatedE434 δ rest=z.1 :=
    congrArg Prod.fst hendpoint
  have hEval : paritySourceOrderedAllocatedE434 δ rest*v=u := by
    rw [he]; exact hEv
  have hNative := parity_original_signed_W1_epsilon_actual_Q_transfer434
    L hL band slot δ rest v hv signed
  conv_lhs => rw [←hEval]
  exact hNative

/-- Actual full original signed Q-product/u source Fourier
coefficient equals selected e Fourier Q fibre × independently signed
physical a_v(v), with exact H(vStar), W1(P,v) and true e*vStar
gate. This holds for BOTH ε=1 and ε=E, BEFORE the odd-half-difference,
and keeps all Q labels/factorials/native skipped-Q coefficients. -/
theorem parity_original_signed_reserved_gate_eq_e_H_v434
    (d : ℕ) (L : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    parityOriginalSignedReservedProductGate434 d L u signed band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2=sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        paritySourceQSelectedFourierEFibre434
          (Q:=sourceActualSortedQ 20 d L band slot) δ
          (sourceActualSortedFrequencyScales 20 d L band slot) ξ z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 signed z.2
          (z.2*sourceOriginalPPrimePart
           (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  unfold parityOriginalSignedReservedProductGate434
  rw [parity_original_reserved_fullQ_product_gate_eq_selected_H434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 u]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hgate : z.1*z.2=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · simp only [if_pos hgate]
    have hW := parity_original_signed_actual_gate_P_weight_transfer434
      d L hL hd u hu band slot δ signed z hz hgate
    unfold parityOriginalReservedSignedPhysicalAV434
    have hZero : sourceOriginalPureMellinPhase434 (0:ℝ)
      (z.2*sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)=1 := by
      simp [sourceOriginalPureMellinPhase434]
    rw [hZero]
    rw [hW]
    push_cast
    ring
  · simp only [if_neg hgate]
    ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedFullFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Genuine original signed ε=1 or ε=E Fourier integrand with ALL
factorial-labelled original Q tuples, P W1/sign, original f0/f1
history-dependent B590 gate Fourier transforms. No odd projector is
inserted into the signed branch. -/
def parityOriginalSignedFullQAllGateFourierAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
    ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ) *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) δ
        (fun i => (parityActualSourceRemainingFullQTuple434
          d L band slot f i).val) ξ

/-- Exact original signed 20! Q/P B590 f0/f1 Fourier integrand at
fixed u and source allocation δ,ξ equals selected e-only frequency
coefficient times source signed physical `W1(v)ε(v)H_0(vStar)`.
This is proved SEPARATELY for both ε=1 and ε=E; no cancellation
between the two signed sources is used. -/
theorem parity_original_signed_fullQ_all_gate_fourier_eq_e_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) :
    parityOriginalSignedFullQAllGateFourierAtU434
      d L E u signed band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2 = sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateFourierCoefficient434
          d L E band slot δ ξ z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 signed z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  let C : ℂ := (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) *
    ((Real.fourierChar (Real.log E *
      (∑ i, ξ i/sourceActualSortedFrequencyScales 20 d L band slot i)) : Circle):ℂ)
  have hSource := parity_original_signed_fullQ_source_eq_reserved_gate434
    d L u signed band slot δ ξ
  have hFactor := parity_original_signed_reserved_gate_eq_e_H_v434
    d L hL hd u hu signed band slot δ ξ K alpha q χ σ₀ σ₁
  calc
    parityOriginalSignedFullQAllGateFourierAtU434 d L E u signed band slot δ ξ =
        C * parityOriginalSignedFullQSourceFourierAtU434
          d L u signed band slot δ ξ := by
      unfold parityOriginalSignedFullQAllGateFourierAtU434
        parityOriginalSignedFullQSourceFourierAtU434
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      rw [parity_original_B590_all_gate_integrand_exact434]
      dsimp [C]
      ring
    _ = C * parityOriginalSignedReservedProductGate434
          d L u signed band slot δ ξ := by rw [hSource]
    _ = _ := by
      rw [hFactor]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hgate : z.1*z.2=sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
      · simp only [if_pos hgate]
        unfold parityOriginalSelectedEGateFourierCoefficient434
        dsimp [C]
        ring
      · simp only [if_neg hgate]
        ring

/-- The TRUE original odd-projected Q/P B590 Fourier integrand is
exactly half the difference of the TWO independent signed ε=1/E
source Fourier integrands at every u,δ,ξ, with true f0/f1,
original labelled Q families and factorial. No signed correlation
is assumed or claimed. -/
theorem parity_original_fullQ_odd_fourier_eq_signed_half_difference434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalActualFullQAllGateFourierAtU434 d L E u band slot δ ξ =
      (parityOriginalSignedFullQAllGateFourierAtU434
        d L E u false band slot δ ξ -
       parityOriginalSignedFullQAllGateFourierAtU434
        d L E u true band slot δ ξ)/2 := by
  unfold parityOriginalActualFullQAllGateFourierAtU434
    parityOriginalSignedFullQAllGateFourierAtU434
  rw [←Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro f hf
  rw [parity_original_actual_fullQ_weight_signed_half_difference434]
  push_cast
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedHBoxIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The genuine original signed ε=1/E all-Q factorial B590
f0/f1 Fourier integrand summed over all histories δ, at fixed
original integer u. This is an independent signed source, not
the original odd projector multiplied after a norm. -/
def parityOriginalSignedFullSourceFourierAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool,
    parityOriginalSignedFullQAllGateFourierAtU434
      d L E u signed band slot δ ξ

/-- Exact ORIGINAL source signed ε=1/E full Fourier δ-integrand
identified with the real physical selected-e source Fourier
coefficient times signed W1(P,v)ε(v)H_0(vStar), with TRUE original
Q-product gate and all native B509 factorial coefficients. -/
def parityOriginalSignedSourceFourierHAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2=sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateFourierCoefficient434 d L E band slot δ ξ z.1 *
        parityOriginalReservedSignedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 signed z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0

/-- Each real ORIGINAL signed branch has an EXACT independent physical
H(vStar) Fourier integrand at source u>0 and moving genuine Q depth.
There is no signed correlation asserted at this stage. -/
theorem parity_original_signed_full_source_integrand_eq_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    parityOriginalSignedFullSourceFourierAtU434
      d L E u signed band slot ξ =
    parityOriginalSignedSourceFourierHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁ ξ := by
  unfold parityOriginalSignedFullSourceFourierAtU434
    parityOriginalSignedSourceFourierHAtU434
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_signed_fullQ_all_gate_fourier_eq_e_H434
    d L E hL hd u hu signed band slot δ ξ K alpha q χ σ₀ σ₁

/-- An original true ε=1 or E signed h=-2 Fourier box coefficient
at source u, integrated over the literal N-dimensional product
Lebesgue measure restricting every ξ_i to [-T,T]. -/
def parityOriginalSignedPhysicalABoxAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
      parityOriginalSignedFullSourceFourierAtU434 d L E u signed band slot ξ
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- The true signed original source f0/f1 B590 Fourier integrand
is integrable over the genuine finite multi-dimensional frequency
box, with no assumption of nonnegativity of ε=E branch. -/
theorem parity_original_signed_full_source_fourier_integrable_on_box434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    Integrable (parityOriginalSignedFullSourceFourierAtU434
      d L E u signed band slot)
      (Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))) := by
  unfold parityOriginalSignedFullSourceFourierAtU434
    parityOriginalSignedFullQAllGateFourierAtU434
  apply integrable_finsetSum
  intro δ hδ
  apply integrable_finsetSum
  intro f hf
  exact (parity_original_B590_all_gate_integrable_on_fourier_box434 E
    (sourceActualSortedFrequencyScales 20 d L band slot) δ
    (fun i => (parityActualSourceRemainingFullQTuple434
      d L band slot f i).val) T).const_mul _

/-- True signed source original full-Q box equals the integral of
the actual physical signed ε=1/E selected-e×H(vStar) source.
The independent signed ε=E contribution may be negative, but its
integrability and equality are proved directly from the genuine
finite Q/δ Fubini and signed physical transfer. -/
theorem parity_original_signed_A_box_eq_H_integral434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (T : ℝ) :
    let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
      Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    Integrable (parityOriginalSignedSourceFourierHAtU434
      d L E u signed band slot K alpha q χ σ₀ σ₁) μ ∧
    parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T =
      ∫ ξ, parityOriginalSignedSourceFourierHAtU434
        d L E u signed band slot K alpha q χ σ₀ σ₁ ξ ∂μ := by
  dsimp only
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  have hOld := parity_original_signed_full_source_fourier_integrable_on_box434
    d L E u signed band slot T
  have hEq (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
      parityOriginalSignedFullSourceFourierAtU434 d L E u signed band slot ξ =
      parityOriginalSignedSourceFourierHAtU434 d L E u signed band slot
        K alpha q χ σ₀ σ₁ ξ :=
    parity_original_signed_full_source_integrand_eq_H434
      d L E hL hd u hu signed band slot K alpha q χ σ₀ σ₁ ξ
  refine ⟨hOld.congr (Filter.Eventually.of_forall hEq),?_⟩
  unfold parityOriginalSignedPhysicalABoxAtU434
  exact integral_congr_ae (Filter.Eventually.of_forall hEq)
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedBilinearHBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Genuine independent signed original Parity ε=1/E full h=-2
B590 Fourier BOX on actual Q/P 20! factorial and source shifts
`mn=u+2`, before any signed correlation or squaring. -/
def parityOriginalShiftTwoSignedBilinearFourierBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- The actual physical signed Parity(4.7) h=-2 source Fourier integral
with complete selected-e×`W1(v)epsilon(v)H(vStar)` signed factors,
all real f0/f1 allocations and original alpha_m beta_n, mn=u+2.
The ε=1 and ε=E branches are genuinely separate physical objects. -/
def parityOriginalShiftTwoSignedBilinearHBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalSignedSourceFourierHAtU434
          d L E u signed band slot K α 1
          (1 : DirichletCharacter ℂ 1) 0 0 ξ *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2))
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- The two separate genuine original Parity signed h=-2 Fourier-BOX
bilinear sums are EXACTLY their respective physical signed
`a_e(e)×W1(v)epsilon(v)H_0(vStar)` source Fourier-box integrals.
True Q/P factorial, native c_r and reserved prime, original Psi and
alpha_m beta_n, mn=u+2, are retained. This is a direct original
Fourier-BOX Fubini identity, NOT a signed correlation estimate. -/
theorem parity_original_hminus2_signed_fourier_box_eq_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoSignedBilinearFourierBox434
      d L E band slot Psi K J α β signed Y T =
    parityOriginalShiftTwoSignedBilinearHBox434
      d L E band slot Psi K J α β signed Y T := by
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let H := fun (u : ℕ) (ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
    parityOriginalSignedSourceFourierHAtU434 d L E u signed band slot K α 1
      (1 : DirichletCharacter ℂ 1) 0 0 ξ
  let C : ℕ → ℂ := fun u =>
    (Psi ((u:ℝ)/Real.exp L):ℂ) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)
  have hPos (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) : u ≠ 0 :=
    (Finset.mem_Ioc.mp hu).1.ne'
  have hA (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (H u) μ ∧
      parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T =
        ∫ ξ, H u ξ ∂μ :=
    parity_original_signed_A_box_eq_H_integral434
      d L E hL hd u (hPos u hu) signed band slot K α 1
        (1 : DirichletCharacter ℂ 1) 0 0 T
  have hInt (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (fun ξ => H u ξ * C u) μ :=
    (hA u hu).1.mul_const _
  unfold parityOriginalShiftTwoSignedBilinearFourierBox434
    parityOriginalShiftTwoSignedBilinearHBox434
  calc
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalSignedPhysicalABoxAtU434 d L E u signed band slot T *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2)) =
      ∑ u ∈ Finset.Ioc 0 Y, ∫ ξ, H u ξ * C u ∂μ := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [(hA u hu).2, integral_mul_const]
        ring
    _ = ∫ ξ, ∑ u ∈ Finset.Ioc 0 Y, H u ξ * C u ∂μ :=
      (integral_finsetSum (Finset.Ioc 0 Y) hInt).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [H,C]
      ring
end Green64Analytic.Parity

end

end

