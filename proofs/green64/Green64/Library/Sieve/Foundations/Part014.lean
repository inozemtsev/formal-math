module

public import Green64.Library.Sieve.Foundations.Part013
public import Green64.Library.Analysis.Estimates.Part016
public import Green64.Library.Sieve.Foundations.Part010
public import Green64.Library.Sieve.Foundations.Part012
public import Green64.Library.Sieve.Foundations.Part011

@[expose] public section

/-!
# Sieve / Foundations / Part014

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalFiniteEVMellinInterchange -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- A genuine finite e,v physical source carrier, retaining only
positive original e and v. The source-specific complete Q-fibre
membership, odd-parity W1 and αβ arithmetic are encoded in arbitrary
fixed complex weights C and may then be substituted without reproof. -/
def parityOriginalPositiveEVCarrier434 (T : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T.filter (fun z => 0 < z.1 ∧ 0 < z.2)

/-- The original post-Mellin 2π frequency amplitude. Its first factor
is independent of e,v, the second depends only on e, the third only on
v. No factor has been replaced by an abstract proxy coefficient. -/
def parityOriginalEVMellinAmplitude434
    (s Z : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64)
    (e v : ℕ) : ℂ :=
  (𝓕 (parityOriginalLogCutoff434
    (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
    Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
    (sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
      sourceOriginalPureMellinPhase434 (2*Real.pi*s) v)

/-- All TRUE original Fourier-Mellin source frequency amplitudes are
integrable for positive e,v, by the existing Schwartz inverse-Fourier
certificate. Integrability is proved BEFORE any finite Fubini. -/
theorem parity_original_e_v_mellin_amplitude_integrable434
    (Z : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (e v : ℕ) (he : 0 < e) (hv : 0 < v) :
    Integrable (fun s : ℝ =>
      parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport e v) := by
  let psi : ℝ → ℂ := fun t => (Psi t : ℂ)
  let f := (𝓕 (parityOriginalLogCutoff434 psi hSmooth hSupport) : 𝓢(ℝ,ℂ))
  have hInt := parity_actual_cutoff_mellin_integrable434 Z psi (e*v) 1
    hSmooth hSupport
  have hOne (s : ℝ) :
      sourceOriginalPureMellinPhase434 (-2*Real.pi*s) 1 = 1 := by
    simp [sourceOriginalPureMellinPhase434]
  have hForm : (fun s : ℝ =>
      parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport e v) =
      (fun s : ℝ => f s *
        Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ):ℂ)*Complex.I) *
        sourceOriginalPureMellinPhase434 (2*Real.pi*s) (e*v) *
        sourceOriginalPureMellinPhase434 (-2*Real.pi*s) 1) := by
    funext s
    unfold parityOriginalEVMellinAmplitude434
    rw [hOne, mul_one,
      source_original_pure_mellin_product_factor434 _ e v he hv]
  rw [hForm]
  exact hInt

/-- SOURCE-EXACT, genuinely integrable Mellin separation and finite
Fubini for ALL positively supported original e,v integer pairs with
arbitrary fixed complex SOURCE weights C(e,v). The source
Psi(e*v/Z) and exactly normalized 2π Fourier-Mellin amplitude are
preserved. A real physical Q/P source weight may be substituted for C
only after showing the fibre/endpoint carrier identity, so this does
not claim full historical Parity(4.7) coefficient factorisation. -/
theorem parity_original_finite_positive_e_v_mellin_fubini434
    (Z : ℝ) (hZ : 0 < Z)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (T : Finset (ℕ × ℕ)) (C : ℕ → ℕ → ℂ) :
    Integrable (fun s : ℝ =>
      ∑ z ∈ parityOriginalPositiveEVCarrier434 T,
        C z.1 z.2 *
          parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport z.1 z.2) ∧
    (∑ z ∈ parityOriginalPositiveEVCarrier434 T,
       C z.1 z.2 * (Psi (((z.1:ℝ)*(z.2:ℝ))/Z) : ℂ)) =
      ∫ s : ℝ,
        ∑ z ∈ parityOriginalPositiveEVCarrier434 T,
          C z.1 z.2 *
            parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport z.1 z.2 := by
  let S := parityOriginalPositiveEVCarrier434 T
  have hPositive (z : ℕ×ℕ) (hz : z ∈ S) : 0 < z.1 ∧ 0 < z.2 :=
    (Finset.mem_filter.mp hz).2
  have hInt (z : ℕ×ℕ) (hz : z ∈ S) :
      Integrable (fun s : ℝ =>
        C z.1 z.2 * parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport z.1 z.2) :=
    (parity_original_e_v_mellin_amplitude_integrable434 Z Psi hSmooth hSupport
      z.1 z.2 (hPositive z hz).1 (hPositive z hz).2).const_mul _
  have hAll : Integrable (fun s : ℝ =>
      ∑ z ∈ S, C z.1 z.2 *
        parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport z.1 z.2) :=
    integrable_finsetSum S hInt
  refine ⟨hAll,?_⟩
  calc
    _ = ∑ z ∈ S, C z.1 z.2 *
        (∫ s : ℝ, parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport z.1 z.2) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact congrArg (fun t : ℂ => C z.1 z.2 * t)
            (parity_original_real_Psi_e_v_mellin_exact434 Z hZ z.1 z.2
              (hPositive z hz).1 (hPositive z hz).2 Psi hSmooth hSupport)
    _ = ∑ z ∈ S, ∫ s : ℝ,
        C z.1 z.2 * parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport z.1 z.2 := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [integral_const_mul]
    _ = _ := (integral_finsetSum S hInt).symm
end Green64Analytic.Parity

end

end

/-! ## OriginalPhysicalTupleMellinFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 34000

/-- Exact TRUE original Parity §4.2 physical labelled source carrier:
positive u and the original full Q product gate, retaining EVERY 20!
Q-labelled tuple, the reserved Q prime and complete B590 assignments.
There is NO `u=e*v` postulate: it is a theorem on this carrier. -/
def parityOriginalActualMellinPhysicalCarrier434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Y : ℕ) : Finset (ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot) :=
  ((Finset.range (Y+1)).product
    (Finset.univ : Finset (parityActualOriginalAFullBranchCarrier434 d L band slot))).filter
      (fun t => 0 < t.1 ∧
        (∏ j : Fin (d+1), ∏ i : Fin 20, (t.2.2 j i).val) =
          sourceOriginalOrdinaryPart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) t.1)

/-- Physical original v consists of the true reserved Q prime, the
full B509 skipped Q product, and all original P-prime-power factors.
It is not a new proxy for the historical Parity v_*. -/
def parityOriginalActualMellinPhysicalV434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (u : ℕ) (z : parityActualOriginalAFullBranchCarrier434 d L band slot) : ℕ :=
  (z.2 band slot).val *
    paritySourceOrderedAllocatedV434 z.1
      (parityActualSourceRemainingFullQTuple434 d L band slot z.2) *
    sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u

/-- The exact original u=e*v equality on EACH member of the complete
P/Q physical labelled carrier, including the original reserved prime
and multiplicity-counted P-part. This is the real finite source
constraint needed for the Mellin sum/integral interchange. -/
theorem parity_original_actual_mellin_physical_carrier_ev434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Y : ℕ)
    (t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot)
    (ht : t ∈ parityOriginalActualMellinPhysicalCarrier434 d L band slot Y) :
    parityActualOriginalAFullBranchE434 d L band slot t.2 *
      parityOriginalActualMellinPhysicalV434 d L band slot t.1 t.2 = t.1 := by
  have hp := (Finset.mem_filter.mp ht).2
  exact parity_actual_original_A_labelled_allocated_ev_exact434
    d L t.1 (Nat.pos_iff_ne_zero.mp hp.1) t.2.2 hp.2 band slot t.2.1

/-- FULL actual original physical B590/B509 labelled source, with any
fixed coefficients C(u,branch) (including actual W1/P parity, alpha_m,
beta_n and arbitrary real Fourier ξ), admits the exact normalized
Schwartz Mellin interchange on the genuine `u=e*v` carrier.
Integrability is checked PER original labelled tuple; then the finite
sum is interchanged with the real integral. This is the source
analytic prerequisite to post-integrated a_e, not the a_e identity. -/
theorem parity_original_actual_physical_tuple_mellin_fubini434
    (d : ℕ) (L Z : ℝ) (hZ : 0 < Z)
    (band : Fin (d+1)) (slot : Fin 20) (Y : ℕ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (C : ℕ → parityActualOriginalAFullBranchCarrier434 d L band slot → ℂ) :
    let T := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
    let e := fun z : parityActualOriginalAFullBranchCarrier434 d L band slot =>
      parityActualOriginalAFullBranchE434 d L band slot z
    let v := parityOriginalActualMellinPhysicalV434 d L band slot
    Integrable (fun s : ℝ =>
      ∑ t ∈ T, C t.1 t.2 *
        parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport
          (e t.2) (v t.1 t.2)) ∧
    (∑ t ∈ T, C t.1 t.2 * (Psi ((t.1:ℝ)/Z) : ℂ)) =
      ∫ s : ℝ,
        ∑ t ∈ T, C t.1 t.2 *
          parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport
            (e t.2) (v t.1 t.2) := by
  dsimp only
  let T := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
  let e := parityActualOriginalAFullBranchE434 d L band slot
  let v := parityOriginalActualMellinPhysicalV434 d L band slot
  have hEV (t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot)
      (ht : t ∈ T) : e t.2 * v t.1 t.2 = t.1 :=
    parity_original_actual_mellin_physical_carrier_ev434 d L band slot Y t ht
  have hPos (t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot)
      (ht : t ∈ T) : 0 < e t.2 ∧ 0 < v t.1 t.2 := by
    have h0 := (Finset.mem_filter.mp ht).2.1
    have hNonzero : e t.2 * v t.1 t.2 ≠ 0 := by
      rw [hEV t ht]
      omega
    exact ⟨Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hNonzero).1,
      Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hNonzero).2⟩
  have hTerm (t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot)
      (ht : t ∈ T) : Integrable (fun s : ℝ =>
        C t.1 t.2 * parityOriginalEVMellinAmplitude434
          s Z Psi hSmooth hSupport (e t.2) (v t.1 t.2)) :=
    (parity_original_e_v_mellin_amplitude_integrable434
      Z Psi hSmooth hSupport _ _ (hPos t ht).1 (hPos t ht).2).const_mul _
  have hAll : Integrable (fun s : ℝ =>
      ∑ t ∈ T, C t.1 t.2 * parityOriginalEVMellinAmplitude434
        s Z Psi hSmooth hSupport (e t.2) (v t.1 t.2)) :=
    integrable_finsetSum T hTerm
  refine ⟨hAll,?_⟩
  calc
    _ = ∑ t ∈ T, C t.1 t.2 *
      (∫ s : ℝ, parityOriginalEVMellinAmplitude434
        s Z Psi hSmooth hSupport (e t.2) (v t.1 t.2)) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hP := parity_original_real_Psi_e_v_mellin_exact434
            Z hZ (e t.2) (v t.1 t.2) (hPos t ht).1 (hPos t ht).2
            Psi hSmooth hSupport
          have hCast : ((e t.2:ℝ)*(v t.1 t.2:ℝ)) = (t.1:ℝ) := by
            exact_mod_cast hEV t ht
          rw [hCast] at hP
          exact congrArg (fun z : ℂ => C t.1 t.2*z) hP
    _ = ∑ t ∈ T, ∫ s : ℝ,
      C t.1 t.2 * parityOriginalEVMellinAmplitude434
        s Z Psi hSmooth hSupport (e t.2) (v t.1 t.2) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [integral_const_mul]
    _ = _ := (integral_finsetSum T hTerm).symm
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierSelectedE -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- TRUE original B590 ξ-Fourier integrand on one full physically
supported Q/P row t=(u,δ,full-labelled-20! Q tuple). All original
W1, multiplicity-parity, factorial, reserved Q, history-dependent
residual and actual shifted `mn=u+2` alpha/beta factors are retained. -/
def parityOriginalB590PhysicalFourierRow434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot) : ℂ :=
    (parityOriginalB590FullBranchArithmetic434 d L t.1 band slot (fun _ => 0) t.2 *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) t.2.1
        (fun i => (parityActualSourceRemainingFullQTuple434
          d L band slot t.2.2 i).val) ξ) *
      ((Psi ((t.1:ℝ)/Real.exp L):ℂ) *
        ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
          α z.1*β z.2)

/-- Physical original Parity (4.7) e-fibre of a TRUE Fourier integration
vector ξ, containing the complete original Q-product gate, W1(v),
parity Ω, reserved Q and alpha/beta h=-2 arithmetic. This is an
endpoint fibre, not the paper's final a_e: its weights can still
depend on skipped Q primes, hence on physical v. -/
def parityOriginalB590PhysicalFourierSelectedEInner434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) (e : ℕ) : ℂ :=
  let T := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
  let g := fun t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot =>
    parityActualOriginalAFullBranchE434 d L band slot t.2
  sourceEndpointFibre T g
    (parityOriginalB590PhysicalFourierRow434 d L E band slot Psi K J α β ξ) e

/-- EXACT finite Parity (4.7) SOURCE Fourier integrand regrouping with
selected e OUTERMOST. This is on the true original Q/P physical
carrier, with actual u=e*v proven separately; all factorial and
history-dependent f0/f1 source transforms are retained.
No independence of the inner v from e is assumed and no optimistic
`a_e(e)` source factorisation is claimed. -/
theorem parity_original_B590_full_carrier_fourier_integrand_eq_selected_e_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) :
    (∑ t ∈ parityOriginalActualMellinPhysicalCarrier434 d L band slot Y,
      parityOriginalB590PhysicalFourierRow434 d L E band slot Psi K J α β ξ t) =
    ∑ e ∈ (parityOriginalActualMellinPhysicalCarrier434 d L band slot Y).image
       (fun t => parityActualOriginalAFullBranchE434 d L band slot t.2),
       parityOriginalB590PhysicalFourierSelectedEInner434
         d L E band slot Psi K J α β Y ξ e := by
  let T := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
  let g := fun t : ℕ × parityActualOriginalAFullBranchCarrier434 d L band slot =>
    parityActualOriginalAFullBranchE434 d L band slot t.2
  let w := parityOriginalB590PhysicalFourierRow434 d L E band slot Psi K J α β ξ
  have h := Finset.sum_image' (s := T) (g := g)
    (f := fun e => sourceEndpointFibre T g w e) w (by intro t ht; rfl)
  simpa only [T,g,w,parityOriginalB590PhysicalFourierSelectedEInner434,
    sourceEndpointFibre] using h.symm
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierSelectedEFull -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Source original full h=-2 B590 all-Q/all-δ Fourier integrand is
EXACTLY the TRUE physical positive `u=e*v` labelled carrier, before
Fourier integration. The u=0 source term vanishes by Ψ(0)=0, and
all incorrect factorial-labelled Q product gates have ZERO original
source arithmetic coefficient. No unproved e/v independence. -/
theorem parity_original_B590_full_fourier_integrand_restrict_carrier434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsiZero : Psi 0 = 0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) :
    (∑ u ∈ Finset.range (Y+1),
      (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
        parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _ => 0) z *
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) z.1
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot z.2 i).val) ξ) *
        ((Psi ((u:ℝ)/Real.exp L):ℂ) *
          (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α t.1*β t.2))) =
    ∑ t ∈ parityOriginalActualMellinPhysicalCarrier434 d L band slot Y,
      parityOriginalB590PhysicalFourierRow434
        d L E band slot Psi K J α β ξ t := by
  let C := parityActualOriginalAFullBranchCarrier434 d L band slot
  let gate : ℕ × C → Prop := fun t => 0 < t.1 ∧
    (∏ j : Fin (d+1), ∏ i : Fin 20, (t.2.2 j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) t.1
  let w := parityOriginalB590PhysicalFourierRow434 d L E band slot Psi K J α β ξ
  simp_rw [Finset.sum_mul]
  change (∑ u ∈ Finset.range (Y+1),
    ∑ z : C, w (u,z)) =
    ∑ t ∈ ((Finset.range (Y+1)).product (Finset.univ : Finset C)).filter gate,
       w t
  rw [Finset.sum_filter]
  have hProd :
      (∑ t ∈ (Finset.range (Y+1)).product (Finset.univ : Finset C),
        if gate t then w t else 0) =
      ∑ u ∈ Finset.range (Y+1), ∑ z : C,
        if gate (u,z) then w (u,z) else 0 :=
    Finset.sum_product _ _ _
  rw [hProd]
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
    unfold w parityOriginalB590PhysicalFourierRow434
    simp [hPsiZero]
  · by_cases hg : (∏ j : Fin (d+1), ∏ i : Fin 20, (z.2 j i).val) =
        sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    · have hGate : gate (u,z) := ⟨Nat.pos_of_ne_zero hu0,hg⟩
      simp only [if_pos hGate]
    · have hGate : ¬gate (u,z) := by
        intro hh
        exact hg hh.2
      simp only [if_neg hGate]
      have hZero : parityOriginalB590FullBranchArithmetic434 d L u band slot
          (fun _ => 0) z = 0 := by
        unfold parityOriginalB590FullBranchArithmetic434
        simp only [if_neg hg]
      change w (u,z) = 0
      dsimp only [w,parityOriginalB590PhysicalFourierRow434]
      rw [hZero]
      ring

/-- The entire genuine original h=-2/sourceOriginalA B590/B509
multidimensional Fourier integrand, now e-FIRST rather than u/f/Q-
first: exact ALL source-finite arithmetic factors/Schwartz gates and
W1/P parity are held in the e endpoint fibre, and `u=e*v` is the real
Q-product gate. No postintegrated historical `a_e(e)` is assumed. -/
theorem parity_original_B590_full_fourier_integrand_selected_e_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsiZero : Psi 0 = 0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) :
    (∑ u ∈ Finset.range (Y+1),
      (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
        parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _ => 0) z *
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) z.1
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot z.2 i).val) ξ) *
        ((Psi ((u:ℝ)/Real.exp L):ℂ) *
          (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α t.1*β t.2))) =
    ∑ e ∈ (parityOriginalActualMellinPhysicalCarrier434 d L band slot Y).image
       (fun t => parityActualOriginalAFullBranchE434 d L band slot t.2),
       parityOriginalB590PhysicalFourierSelectedEInner434
         d L E band slot Psi K J α β Y ξ e := by
  rw [parity_original_B590_full_fourier_integrand_restrict_carrier434
    d L E band slot Psi hPsiZero K J α β Y ξ]
  exact parity_original_B590_full_carrier_fourier_integrand_eq_selected_e_outer434
    d L E band slot Psi K J α β Y ξ
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierSelectedEIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The COMPLETE ORIGINAL Parity (4.7) B590 Fourier integral with every
source all-Q factorial W1/P-parity gate, true reserved source Q prime,
all δ f0/f1 Fourier transformations and h=-2 bilinear alpha/beta,
is exactly an INTEGRABLE Fourier integral whose finite outer source sum
is over true allocated integer e. Zero u and every wrong Q-product
row are deleted by proved zero contributions, not a support axiom.

This is a genuine global source Fourier-integrated e-first identity,
not the final paper coefficient a_e(e): original Mellin separation,
frequency support bounds and c_r/H(v*) source factorisation still need
literal integration and source-specific proofs. -/
theorem parity_original_B590_hminus2_full_fourier_selected_e_integral434
    (d : ℕ) (L E : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsiZero : Psi 0 = 0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    let N := (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length
    let T := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
    let G : (Fin N → ℝ) → ℂ := fun ξ =>
      ∑ e ∈ T.image (fun t =>
        parityActualOriginalAFullBranchE434 d L band slot t.2),
        parityOriginalB590PhysicalFourierSelectedEInner434
          d L E band slot Psi K J α β Y ξ e
    Integrable G ∧
    parityOriginalShiftTwoBilinearFullFourierSource434
      d L E band slot (fun _ => 0) Psi K J α β Y =
      ∫ ξ : Fin N → ℝ, G ξ := by
  dsimp only
  let N := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let T := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
  let G : (Fin N → ℝ) → ℂ := fun ξ =>
    ∑ e ∈ T.image (fun t =>
      parityActualOriginalAFullBranchE434 d L band slot t.2),
      parityOriginalB590PhysicalFourierSelectedEInner434
        d L E band slot Psi K J α β Y ξ e
  have hF := parity_original_B590_hminus2_bilinear_all_labelled_full_fourier434
    d L E band slot (fun _ => 0) Psi K J α β Y
  have hEq (ξ : Fin N → ℝ) :
      (∑ u ∈ Finset.range (Y+1),
        (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
          parityOriginalB590FullBranchArithmetic434 d L u band slot
            (fun _ => 0) z *
          parityOriginalB590AllGateFourierIntegrand434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) z.1
            (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot z.2 i).val) ξ) *
          ((Psi ((u:ℝ)/Real.exp L):ℂ) *
            (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
              α t.1*β t.2))) = G ξ :=
    parity_original_B590_full_fourier_integrand_selected_e_outer434
      d L E band slot Psi hPsiZero K J α β Y ξ
  have hIntG : Integrable G := hF.1.congr
    (Filter.Eventually.of_forall hEq)
  refine ⟨hIntG,?_⟩
  calc
    _ = ∫ ξ : Fin N → ℝ,
       ∑ u ∈ Finset.range (Y+1),
        (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
          parityOriginalB590FullBranchArithmetic434 d L u band slot
            (fun _ => 0) z *
          parityOriginalB590AllGateFourierIntegrand434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) z.1
            (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot z.2 i).val) ξ) *
          ((Psi ((u:ℝ)/Real.exp L):ℂ) *
            (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
              α t.1*β t.2)) := hF.2
    _ = ∫ ξ : Fin N → ℝ, G ξ :=
      integral_congr_ae (Filter.Eventually.of_forall hEq)
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierBoxIntegrable -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The TRUE original source B590 N-dimensional Fourier transform is
integrable EVEN AFTER restricting every frequency coordinate to a
literal real box [-T,T]. The source Q history-dependent phases remain
untouched. No erroneous assumption that bounded box implies
integrability on a noncompact ambient space is used; the proof is a
Schwartz product-measure restriction. -/
theorem parity_original_B590_all_gate_integrable_on_fourier_box434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ) (T : ℝ) :
    Integrable (parityOriginalB590AllGateFourierIntegrand434 E s δ p)
      (Measure.pi (fun _ : Fin N => (volume : Measure ℝ).restrict
        (Set.Icc (-T) T))) := by
  have hCoord (i : Fin N) :
      Integrable (parityOriginalB590SingleGateFourierIntegrand434 E s δ p i)
        ((volume : Measure ℝ).restrict (Set.Icc (-T) T)) :=
    (parity_original_B590_single_gate_fourier_integrable434 E s δ p i).integrableOn
  have h := Integrable.fin_nat_prod hCoord
  exact h

/-- The entire true original factorial/W1/odd-parity Fourier branch
is integrable over the restricted multi-frequency box; no real branch
weight has been replaced by a proxy constant. -/
theorem parity_original_B590_arithmetic_branch_integrable_on_box434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (z : parityActualOriginalAFullBranchCarrier434 d L band slot)
    (T : ℝ) :
    Integrable (fun ξ =>
      parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) z.1
        (fun i => (parityActualSourceRemainingFullQTuple434
          d L band slot z.2 i).val) ξ)
      (Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))) :=
  (parity_original_B590_all_gate_integrable_on_fourier_box434 E
    (sourceActualSortedFrequencyScales 20 d L band slot) z.1
    (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot z.2 i).val)
    T).const_mul _

/-- For EVERY fixed original source u, the COMPLETE factorial-labelled
20!-Q physical integrand with all B590 allocations and parity is
integrable over the true original Fourier box, and its box integral
can be pushed inside the full finite sum (all labels and histories).
This is the actual finite-sum Fubini prerequisite to Parity's truncated
selected-e coefficient. -/
theorem parity_original_B590_arithmetic_all_branches_integral_box434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) (T : ℝ) :
    let C := parityActualOriginalAFullBranchCarrier434 d L band slot
    let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
      Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    let F := fun (z : C) ξ =>
      parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) z.1
        (fun i => (parityActualSourceRemainingFullQTuple434
          d L band slot z.2 i).val) ξ
    Integrable (fun ξ => ∑ z : C, F z ξ) μ ∧
    (∫ ξ, ∑ z : C, F z ξ ∂μ) =
      ∑ z : C, ∫ ξ, F z ξ ∂μ := by
  dsimp only
  let C := parityActualOriginalAFullBranchCarrier434 d L band slot
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let F := fun (z : C) ξ =>
      parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) z.1
        (fun i => (parityActualSourceRemainingFullQTuple434
          d L band slot z.2 i).val) ξ
  have hEach (z : C) (_hz : z ∈ (Finset.univ : Finset C)) :
      Integrable (F z) μ :=
    parity_original_B590_arithmetic_branch_integrable_on_box434
      d L E u band slot χ z T
  exact ⟨integrable_finsetSum Finset.univ hEach,
    integral_finsetSum Finset.univ hEach⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierBoxAIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal original B590 χ=0 Q/P source coefficient with the true
multi-dimensional Fourier box [-T,T]^N: the finished integral of the
full arithmetic Q/δ integrand is EXACTLY the earlier source physical
A-box coefficient at u, without changing factorials, odd parity or
source W1. Original delta/Q order is handled by genuine finite Fubini. -/
theorem parity_original_B590_actual_A_box_eq_full_arithmetic_integral434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20) (T : ℝ) :
    let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
      Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
      ∫ ξ,
        ∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
          parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _=>0) z *
          parityOriginalB590AllGateFourierIntegrand434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) z.1
            (fun i => (parityActualSourceRemainingFullQTuple434
               d L band slot z.2 i).val) ξ ∂μ := by
  dsimp only
  let C := parityActualOriginalAFullBranchCarrier434 d L band slot
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  have hF := (parity_original_B590_arithmetic_all_branches_integral_box434
    d L E u band slot (fun _ => 0) T).2
  rw [hF]
  unfold parityOriginalB590BoxPhysicalAAtU434
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro δ hδ
  have hArithmetic := parity_original_B590_arithmetic_at_zero_eq_actual_tuple_weight434
    d L u band slot (δ,f)
  change ((parityActualOriginalAFullTupleWeight434 d L u f : ℝ):ℂ) *
      parityOriginalB590AllGateFourierBox434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) δ
        (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) T =
    ∫ ξ, parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _=>0) (δ,f) *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) δ
        (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) ξ ∂μ
  rw [hArithmetic,integral_const_mul]
  rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalActualB590BoxHFactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- GENUINE original source Q-part of historical Parity(4.7) after
factorising the TRUE reserved-prime H(v*) on the physical joint
(e,vStar) source carrier for fixed u and real B590 frequency ξ.
The original selected e-only coefficient includes the genuine
f0/f1 Fourier transforms and log E character, and v-side contains
W1(v), odd Omega_P projector and H_0(vStar). This real Q-structure
has not yet incorporated the separate nonzero Mellin frequencies. -/
def parityOriginalActualSourceFourierHAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2 = sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateFourierCoefficient434
          d L E band slot δ ξ z.1 *
        parityOriginalReservedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 0 z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0

/-- The actual 20!-labelled original complete Q/P B590 source
Fourier integrand at u equals the sum of our REAL SOURCE selected-e ×
reserved H(vStar) W1/P odd parity physical coefficients, at every
real Fourier frequency ξ and true moving original Q depth.
There is no independent δ or Q tuple probability assumption; the
source δ×f carrier is exactly finite. -/
theorem parity_original_actual_B590_full_source_integrand_eq_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _ => 0) z *
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) z.1
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot z.2 i).val) ξ) =
    parityOriginalActualSourceFourierHAtU434
      d L E u band slot K alpha q χ σ₀ σ₁ ξ := by
  rw [Fintype.sum_prod_type]
  unfold parityOriginalActualSourceFourierHAtU434
  apply Finset.sum_congr rfl
  intro δ hδ
  calc
    (∑ f : ((j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _ => 0)
          (δ,f) *
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) δ
          (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot f i).val) ξ) =
      parityOriginalActualFullQAllGateFourierAtU434 d L E u band slot δ ξ := by
        unfold parityOriginalActualFullQAllGateFourierAtU434
        apply Finset.sum_congr rfl
        intro f hf
        rw [parity_original_B590_arithmetic_at_zero_eq_actual_tuple_weight434]
    _ = _ := parity_original_actual_fullQ_all_gate_fourier_eq_e_aV434
      d L E hL hd u hu band slot δ ξ K alpha q χ σ₀ σ₁

/-- The REAL ORIGINAL source B590 complete physical A(u) with ALL
Q-prime labelled factorials, source P odd projector, true f0/f1 and
frequency box [-T,T]^N is EXACTLY the integral of the **factorised**
source selected-e × reserved H(vStar) integrand at fixed u>0.
The original product Lebesgue measure and integrability are proved
through the previously kernel-checked full Fourier Q/δ Fubini, NOT
assumed in this theorem. -/
theorem parity_original_actual_B590_physical_A_box_eq_H_integral434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ)
    (T : ℝ) :
    let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
      Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    Integrable (parityOriginalActualSourceFourierHAtU434
      d L E u band slot K alpha q χ σ₀ σ₁) μ ∧
    parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
      ∫ ξ, parityOriginalActualSourceFourierHAtU434
        d L E u band slot K alpha q χ σ₀ σ₁ ξ ∂μ := by
  dsimp only
  let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let G := fun ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
    ∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _ => 0) z *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) z.1
        (fun i => (parityActualSourceRemainingFullQTuple434 d L band slot z.2 i).val) ξ
  have hOld := parity_original_B590_actual_A_box_eq_full_arithmetic_integral434
    d L E u band slot T
  have hEq (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
      G ξ = parityOriginalActualSourceFourierHAtU434
        d L E u band slot K alpha q χ σ₀ σ₁ ξ :=
    parity_original_actual_B590_full_source_integrand_eq_H434
      d L E hL hd u hu band slot K alpha q χ σ₀ σ₁ ξ
  have hIntG : Integrable G μ :=
    (parity_original_B590_arithmetic_all_branches_integral_box434
      d L E u band slot (fun _ => 0) T).1
  have hInt := hIntG.congr (Filter.Eventually.of_forall hEq)
  refine ⟨hInt,?_⟩
  calc
    _ = ∫ ξ, G ξ ∂μ := hOld
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hEq)
end Green64Analytic.Parity

end

end

/-! ## OriginalActualBilinearHBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal true original Parity(4.7),(4.8) h=-2 source B590 Fourier
BOX, with ALL original `sourceOriginalA` Q/P 20! factorial labels
replaced by the exactly proven selected-e × reserved-prime H(vStar)
physical source coefficient, and complete Psi(u/x) and mn=u+2
alpha_m beta_n factors. No Fourier delta/ξ point is silently omitted.
The physical e/vStar carrier is the *true joint* source support, not
a rectangular independent carrier. Nonzero Mellin σ,ρ and the final
historical signed epsilon(v) convention remain separate. -/
def parityOriginalShiftTwoBilinearHBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalActualSourceFourierHAtU434 d L E u band slot K α 1
          (1 : DirichletCharacter ℂ 1) 0 0 ξ *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2))
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- The ACTUAL original `sourceOriginalA` h=-2 physical B590 Fourier
box with full Q/P W1 odd parity and 20! labelled Q branches is
EXACTLY the selected-e × H(vStar) physical Fourier box after
integrating all N source f0/f1 frequencies and summing arbitrary
finite m,n with mn=u+2, for any Psi. This is a true global finite
bilinear equality and uses the source original Q product gate and
factorial normalization, not only a formal coefficient definition.

The H in this equality has native skipped-Q B509 c_r and original
reserved Q band p, and source phase p^0. The chosen trivial
DirichletCharacter and σ0=σ1=0 are dummy parameters: native c_r does
not depend on them in its original definition. This is NOT yet the
full historical Parity(4.7) after nonzero Mellin integration. -/
theorem parity_original_hminus2_bilinear_fourier_box_eq_source_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearFourierBox434 d L E band slot
      Psi K J α β Y T =
    parityOriginalShiftTwoBilinearHBox434 d L E band slot
      Psi K J α β Y T := by
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let H := fun (u : ℕ) (ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
    parityOriginalActualSourceFourierHAtU434 d L E u band slot K α 1
      (1 : DirichletCharacter ℂ 1) 0 0 ξ
  let C : ℕ → ℂ := fun u =>
    (Psi ((u:ℝ)/Real.exp L):ℂ) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)
  have hPos (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) : u ≠ 0 := by
    have h := (Finset.mem_Ioc.mp hu).1
    omega
  have hA (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (H u) μ ∧
      parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
        ∫ ξ, H u ξ ∂μ :=
    parity_original_actual_B590_physical_A_box_eq_H_integral434
      d L E hL hd u (hPos u hu) band slot K α 1
        (1 : DirichletCharacter ℂ 1) 0 0 T
  have hInt (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (fun ξ => H u ξ * C u) μ :=
    (hA u hu).1.mul_const _
  unfold parityOriginalShiftTwoBilinearFourierBox434
    parityOriginalShiftTwoBilinearHBox434
  calc
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T *
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
      dsimp [C,H]
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalActualBilinearHBoxAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- ACTUAL original unsmoothed `sourceOriginalA` h=-2 bilinear source
reduces to the TRUE finite Fourier BOX integral `[-L,L]^N` whose
integrand is factored as selected e-only source B590 Fourier
coefficient times LITERAL reserved-prime H(vStar) native B509 c_r
convolution and W1(P,v) odd Ω_P parity, with no false label
multiplicity or loss of 20! factorials.

For every fixed beta>0, arbitrary requested real inverse-log A and
actual original reserved Q band jQ satisfying original beta/4 cap,
all sufficiently large L, every physical reserved Q mark, real
Ψ∈[0,1] supported [1,2], and complex finite alpha/beta bounded by
Acoef,Bcoef, the true ORIGINAL source h=-2 sum differs from this
H(vStar)-factorised real frequency BOX by at most
`2 Acoef Bcoef exp(L) L^-A`.

This is a direct norm difference between original SOURCE definitions,
not only a formal Q-coefficient identity. The representation is at
the original reserved-prime σ=0 and physical Mellin v-phase ρ=0; full
historical Parity(4.7) requires the genuine nonzero Fourier/Mellin
compatibility, epsilon(v) sign convention, original e-window
insertion on H-side, and the complete signed all-character correlation
Parity(4.17) before TypeII and Green64.
-/
theorem parity_eventually_original_hminus2_source_to_H_fourier_box_all_log434
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
          ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoBilinearHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β ⌊2*Real.exp L⌋₊ L‖ ≤
        2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_source_to_fourier_box_all_log434
      betaP A hbetaP jQ hBand,
    eventually_gt_atTop (0:ℝ)] with L hSource hLp
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro band hb E hElo hEhi Psi hPsiSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  rw [←parity_original_hminus2_bilinear_fourier_box_eq_source_H434
    (sourceOriginalLiteralDepth 20 L) L E hLp rfl band slot
    Psi K J α β ⌊2*Real.exp L⌋₊ L]
  exact hSource.2.2 band hb E hElo hEhi Psi hPsiSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
end Green64Analytic.Parity

end

end

/-! ## OriginalB590FourierBoxSelectedEIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- EXACT original Parity §4.2 physical B590/B509 **TRUNCATED** Fourier
representation in the historical e-FIRST source order. The source box
[-T,T]^N uses the genuine product Lebesgue measure, with all original
f0/f1 Schwartz Fourier transforms, actual sorted Q-prime histories,
full 20! factorial orbit, true P parity/W1, reserved prime, and
true h=-2 α_mβ_n factors retained.

The e-index comes from the original positive Q-product gate u=e*v,
not from a fabricated independent Dirichlet coefficient. All finite
Fubini interchanges and integrability are explicitly proved. This
is a true source-facing step toward Parity(4.7), but the inner e-fibre
still needs source c_r/H(v*) extraction before it can be the paper a_e.
-/
theorem parity_original_B590_hminus2_fourier_box_selected_e_integral434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0 = 0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) (T : ℝ) :
    let N := (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length
    let μ : Measure (Fin N → ℝ) :=
      Measure.pi (fun _ : Fin N =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    let S := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
    let G : (Fin N → ℝ) → ℂ := fun ξ =>
      ∑ e ∈ S.image (fun t =>
        parityActualOriginalAFullBranchE434 d L band slot t.2),
        parityOriginalB590PhysicalFourierSelectedEInner434
          d L E band slot Psi K J α β Y ξ e
    Integrable G μ ∧
    parityOriginalShiftTwoBilinearFourierBox434
      d L E band slot Psi K J α β Y T = ∫ ξ, G ξ ∂μ := by
  dsimp only
  let N := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length
  let μ : Measure (Fin N → ℝ) := Measure.pi (fun _ : Fin N =>
    (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let C := parityActualOriginalAFullBranchCarrier434 d L band slot
  let F : ℕ → (Fin N → ℝ) → ℂ := fun u ξ =>
    ∑ z : C,
      parityOriginalB590FullBranchArithmetic434 d L u band slot (fun _ => 0) z *
      parityOriginalB590AllGateFourierIntegrand434 E
        (sourceActualSortedFrequencyScales 20 d L band slot) z.1
        (fun i => (parityActualSourceRemainingFullQTuple434
          d L band slot z.2 i).val) ξ
  let B : ℕ → ℂ := fun u =>
    (Psi ((u:ℝ)/Real.exp L):ℂ) *
      (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α t.1*β t.2)
  let S := parityOriginalActualMellinPhysicalCarrier434 d L band slot Y
  let G : (Fin N → ℝ) → ℂ := fun ξ =>
    ∑ e ∈ S.image (fun t =>
      parityActualOriginalAFullBranchE434 d L band slot t.2),
      parityOriginalB590PhysicalFourierSelectedEInner434
        d L E band slot Psi K J α β Y ξ e
  have hFi (u : ℕ) : Integrable (F u) μ :=
    (parity_original_B590_arithmetic_all_branches_integral_box434
      d L E u band slot (fun _ => 0) T).1
  have hBu (u : ℕ) (hu : u ∈ Finset.range (Y+1)) :
      Integrable (fun ξ => F u ξ * B u) μ := (hFi u).mul_const _
  have hU : Integrable (fun ξ : Fin N → ℝ =>
      ∑ u ∈ Finset.range (Y+1), F u ξ * B u) μ :=
    integrable_finsetSum (Finset.range (Y+1)) hBu
  have hPoint (ξ : Fin N → ℝ) :
      (∑ u ∈ Finset.range (Y+1), F u ξ * B u) = G ξ :=
    parity_original_B590_full_fourier_integrand_selected_e_outer434
      d L E band slot Psi hPsi0 K J α β Y ξ
  have hG : Integrable G μ := hU.congr
    (Filter.Eventually.of_forall hPoint)
  have hZero (ξ : Fin N → ℝ) : F 0 ξ * B 0 = 0 := by
    dsimp [B]
    simp [hPsi0]
  have hBoxAtU (u : ℕ) :
      parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
      ∫ ξ, F u ξ ∂μ :=
    parity_original_B590_actual_A_box_eq_full_arithmetic_integral434
      d L E u band slot T
  have hBuIoc (u : ℕ) (_hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (fun ξ => F u ξ * B u) μ := (hFi u).mul_const _
  refine ⟨hG,?_⟩
  calc
    parityOriginalShiftTwoBilinearFourierBox434
        d L E band slot Psi K J α β Y T =
      ∑ u ∈ Finset.Ioc 0 Y, (∫ ξ, F u ξ ∂μ)*B u := by
        unfold parityOriginalShiftTwoBilinearFourierBox434
        apply Finset.sum_congr rfl
        intro u hu
        rw [hBoxAtU]
        ring
    _ = ∑ u ∈ Finset.Ioc 0 Y, ∫ ξ, F u ξ * B u ∂μ := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [integral_mul_const]
    _ = ∫ ξ, ∑ u ∈ Finset.Ioc 0 Y, F u ξ * B u ∂μ :=
      (integral_finsetSum (Finset.Ioc 0 Y) hBuIoc).symm
    _ = ∫ ξ, ∑ u ∈ Finset.range (Y+1), F u ξ * B u ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      exact (parity_original_sum_range_eq_Ioc_of_zero434 Y
        (fun u => F u ξ * B u) (hZero ξ)).symm
    _ = ∫ ξ, G ξ ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hPoint)
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinPhaseMul -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The genuine original SOURCE imaginary Mellin phase n^(i rho)
is multiplicative on positive integer n=e*v. This is derived from
the actual frozen source definition `Complex.exp (I * rho * log n)`.
No illegal assertion `log 0 = log e+log v` or artificial phase. -/
theorem parity_original_source_mellin_phase_mul_pos434
    (rho : ℝ) (e v : ℕ) (he : 0 < e) (hv : 0 < v) :
    sourceOriginalPureMellinPhase434 rho (e*v) =
      sourceOriginalPureMellinPhase434 rho e *
        sourceOriginalPureMellinPhase434 rho v := by
  unfold sourceOriginalPureMellinPhase434
  have heR : (e:ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hvR : (v:ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Nat.cast_mul, Real.log_mul heR hvR]
  push_cast
  rw [←Complex.exp_add]
  congr 1 <;> ring
end Green64Analytic.Parity

end

end

/-! ## OriginalActualMellinHBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The exact ORIGINAL selected-Q e-only coefficient after assigning
a nonzero real Mellin frequency rho: native B590 f0/f1 transforms,
global E character, exact original selected Q Fourier e-fibre and
genuine e^(i rho) source Mellin phase. It has NO physical v, skipped-Q
r, reserved prime or original W1/P parity argument. -/
def parityOriginalSelectedEGateMellinCoefficient434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (e : ℕ) : ℂ :=
  sourceOriginalPureMellinPhase434 rho e *
    parityOriginalSelectedEGateFourierCoefficient434 d L E band slot δ ξ e

/-- The ACTUAL original full sourceOriginalA Q/P 20! factorial B590
Fourier integrand at nonzero physical u, multiplied by the real
original Mellin phase u^(i rho), factors EXACTLY at arbitrary rho into

`Σ_(e,vStar), e*vStar=ordinaryPart(P,u)
  [e^(i rho) a_e^selected(δ,ξ,e)] ×
  [(vStar*Ppart(P,u))^(i rho) W1(P,v) oddOmega_P(v) H_0(vStar)]`.

This uses the TRUE source Q-product gate to prove u=e*v, then real
`log(e*v)=log e+log v` for the positive original physical factors;
there is no `log(0)` error. The reserved source prime p exponent is
0 until its own reserved Mellin/Dirichlet phase is inserted.
This is literal source fixed-u,δ,ξ equality (not yet the complete
postintegrated Parity(4.7) e/v coefficient). -/
theorem parity_original_actual_fullQ_mellin_fourier_eq_e_aV434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ) :
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalActualFullQAllGateFourierAtU434
        d L E u band slot δ ξ =
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2 = sourceOriginalOrdinaryPart
         (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateMellinCoefficient434
          d L E band slot δ ξ rho z.1 *
        parityOriginalReservedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0 := by
  rw [parity_original_actual_fullQ_all_gate_fourier_eq_e_aV434
    d L E hL hd u hu band slot δ ξ K alpha q χ σ₀ σ₁]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  let P := sourceOriginalPAllActualBands 20 L
  let v := z.2*sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  by_cases hgate : z.1*z.2=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion P) u
  · dsimp only [P] at hgate ⊢
    simp only [if_pos hgate]
    have hEv : z.1*v=u := by
      dsimp [v]
      calc
        _ = (z.1*z.2)*sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by ac_rfl
        _ = sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u *
          sourceOriginalPPrimePart (Finset.univ.biUnion P) u := by rw [hgate]
        _ = u := source_original_ordinary_times_P_part _ u hu
    have hprod : 0 < z.1*v := by
      rw [hEv]
      exact Nat.pos_of_ne_zero hu
    have he : 0 < z.1 := Nat.pos_of_mul_pos_right hprod
    have hv : 0 < v := Nat.pos_of_mul_pos_left hprod
    have hPhase : sourceOriginalPureMellinPhase434 rho u =
        sourceOriginalPureMellinPhase434 rho z.1 *
          sourceOriginalPureMellinPhase434 rho v := by
      rw [←hEv]
      exact parity_original_source_mellin_phase_mul_pos434 rho z.1 v he hv
    have hAV : parityOriginalReservedPhysicalAV434 d L band slot δ ξ K alpha q χ
        σ₀ σ₁ 0 rho z.2 v =
        sourceOriginalPureMellinPhase434 rho v *
          parityOriginalReservedPhysicalAV434 d L band slot δ ξ K alpha q χ
            σ₀ σ₁ 0 0 z.2 v := by
      unfold parityOriginalReservedPhysicalAV434
      have hZero : sourceOriginalPureMellinPhase434 (0:ℝ) v=1 := by
        simp [sourceOriginalPureMellinPhase434]
      rw [hZero]
      ring
    rw [hPhase]
    unfold parityOriginalSelectedEGateMellinCoefficient434
    rw [hAV]
    ring
  · dsimp only [P] at hgate ⊢
    simp only [if_neg hgate]
    ring
end Green64Analytic.Parity

end

end

/-! ## OriginalActualMellinHBoxIntegral -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- ACTUAL original SOURCE Parity B590 real Fourier integrand, now with
nonzero Mellin frequency rho distributed to the genuine selected e
and physical v factors: e-only `e^(i rho)*a_e^selected(δ,ξ,e)` and
v-side `v^(i rho)*W1(P,v)*oddOmega_P(v)*H_0(vStar)`, under the true
`e*vStar=ordinaryPart(P,u)` gate and all original δ allocations.
No pointwise ξ support assumption; original Q source remains literal. -/
def parityOriginalActualSourceMellinHAtU434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) : ℂ :=
  ∑ δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ z ∈ parityOriginalReservedFullQEVStarSupport434 d L band slot δ,
      if z.1*z.2 = sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u then
        parityOriginalSelectedEGateMellinCoefficient434
          d L E band slot δ ξ rho z.1 *
        parityOriginalReservedPhysicalAV434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho z.2
          (z.2*sourceOriginalPPrimePart
            (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
      else 0

/-- For TRUE original 20!-labelled physical u>0 SOURCE Q tuples,
`u^(i rho) × (sumδ full B590 f0/f1 Fourier source)` equals the
ENTIRE selected-e × physical-v H-convolution at arbitrary real rho,
with all original factorials, W1/P odd parity and reserved Q retained.
This is a genuine source (not an invented auxiliary Mellin coefficient)
finite identity and derives from independently checked per-δ original
SOURCE full-Q Mellin factorisation. -/
theorem parity_original_actual_source_mellin_H_integrand_exact434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalActualSourceFourierHAtU434
        d L E u band slot K alpha q χ σ₀ σ₁ ξ =
      parityOriginalActualSourceMellinHAtU434
        d L E u band slot K alpha q χ σ₀ σ₁ rho ξ := by
  rw [←parity_original_actual_B590_full_source_integrand_eq_H434
    d L E hL hd u hu band slot K alpha q χ σ₀ σ₁ ξ]
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  unfold parityOriginalActualSourceMellinHAtU434
  apply Finset.sum_congr rfl
  intro δ hδ
  have hWeight :
      (∑ f : ((j : Fin (d+1)) → Fin 20 →
        {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j}),
        parityOriginalB590FullBranchArithmetic434 d L u band slot
          (fun _ => 0) (δ,f) *
          parityOriginalB590AllGateFourierIntegrand434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) δ
            (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot f i).val) ξ) =
      parityOriginalActualFullQAllGateFourierAtU434 d L E u band slot δ ξ := by
    unfold parityOriginalActualFullQAllGateFourierAtU434
    apply Finset.sum_congr rfl
    intro f hf
    rw [parity_original_B590_arithmetic_at_zero_eq_actual_tuple_weight434]
  rw [hWeight]
  exact parity_original_actual_fullQ_mellin_fourier_eq_e_aV434
    d L E hL hd u hu band slot δ ξ K alpha q χ σ₀ σ₁ rho

/-- TRUE original A(u) physical B590 Fourier BOX at source u>0,
weighted by the nonzero Mellin phase u^(i rho), is EXACTLY the
product-Lebesgue Fourier BOX integral of the correctly separated
selected e^(i rho) and physical v^(i rho) × H_0(vStar) source
coefficients. Integrability is proved from the ORIGINAL Q/δ Fourier
sum and phase norm-one; not introduced as a Fubini hypothesis. -/
theorem parity_original_actual_B590_A_box_mellin_H_integral434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ rho : ℝ)
    (T : ℝ) :
    let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
      Measure.pi (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length =>
        (volume : Measure ℝ).restrict (Set.Icc (-T) T))
    Integrable (parityOriginalActualSourceMellinHAtU434
      d L E u band slot K alpha q χ σ₀ σ₁ rho) μ ∧
    sourceOriginalPureMellinPhase434 rho u *
      parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
      ∫ ξ, parityOriginalActualSourceMellinHAtU434
        d L E u band slot K alpha q χ σ₀ σ₁ rho ξ ∂μ := by
  dsimp only
  let μ : Measure (Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  have hBase := parity_original_actual_B590_physical_A_box_eq_H_integral434
    d L E hL hd u hu band slot K alpha q χ σ₀ σ₁ T
  have hEq (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ) :
      sourceOriginalPureMellinPhase434 rho u *
      parityOriginalActualSourceFourierHAtU434 d L E u band slot
        K alpha q χ σ₀ σ₁ ξ =
      parityOriginalActualSourceMellinHAtU434 d L E u band slot
        K alpha q χ σ₀ σ₁ rho ξ :=
    parity_original_actual_source_mellin_H_integrand_exact434
      d L E hL hd u hu band slot K alpha q χ σ₀ σ₁ rho ξ
  have hInt : Integrable
      (parityOriginalActualSourceMellinHAtU434
        d L E u band slot K alpha q χ σ₀ σ₁ rho) μ :=
    (hBase.1.const_mul _).congr (Filter.Eventually.of_forall hEq)
  refine ⟨hInt,?_⟩
  rw [hBase.2]
  rw [←integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall hEq)
end Green64Analytic.Parity

end

end

/-! ## OriginalActualBilinearMellinHBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The TRUE source-original physical h=-2 B590 Fourier-box bilinear
with nonzero Mellin phase u^(i rho), where u=mn-2 on its actual
positive source carrier. This is the source B590 sum, not a fabricated
separable alpha/beta twist. -/
def parityOriginalShiftTwoBilinearMellinFourierBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (sourceOriginalPureMellinPhase434 rho u *
      parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- The exact **physical** e-only × H(vStar) nonzero-Mellin rho
representation after integrating genuine B590 f0/f1 source Fourier
gates over the real N-dimensional box and summing all original
shift-two factorizations mn=u+2. Source W1/P odd parity and
reserved prime are carried in actual native H(vStar). -/
def parityOriginalShiftTwoBilinearMellinHBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
    (∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalActualSourceMellinHAtU434 d L E u band slot K α 1
          (1 : DirichletCharacter ℂ 1) 0 0 rho ξ *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2))
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- True ORIGINAL full-source h=-2 alpha beta B590 Fourier BOX
bilinear equality to selected e^(i rho) × physical v^(i rho) H_0(vStar)
for ANY real Mellin frequency rho. Every original Q/P W1/parity
factor and all alpha_m beta_n remain literal, with 20! factorial
normalization once and real product Lebesgue Fubini. The source
B590 frequency box is not evaluated at ξ=0. The separate Mellin
inversion of Psi, historical epsilon, and nonzero reserved p^(iσ)
are still distinct mathematical obligations. -/
theorem parity_original_hminus2_bilinear_mellin_fourier_box_eq_source_H434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) :
    parityOriginalShiftTwoBilinearMellinFourierBox434 d L E band slot
      Psi K J α β rho Y T =
    parityOriginalShiftTwoBilinearMellinHBox434 d L E band slot
      Psi K J α β rho Y T := by
  let μ : Measure (Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) :=
    Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T))
  let H := fun (u : ℕ) (ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
    parityOriginalActualSourceMellinHAtU434 d L E u band slot K α 1
      (1 : DirichletCharacter ℂ 1) 0 0 rho ξ
  let C : ℕ → ℂ := fun u =>
    (Psi ((u:ℝ)/Real.exp L):ℂ) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)
  have hPos (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) : u ≠ 0 := by
    exact (Finset.mem_Ioc.mp hu).1.ne'
  have hA (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (H u) μ ∧
      sourceOriginalPureMellinPhase434 rho u *
        parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T =
        ∫ ξ, H u ξ ∂μ :=
    parity_original_actual_B590_A_box_mellin_H_integral434
      d L E hL hd u (hPos u hu) band slot K α 1
        (1 : DirichletCharacter ℂ 1) 0 0 rho T
  have hInt (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      Integrable (fun ξ => H u ξ * C u) μ :=
    (hA u hu).1.mul_const _
  unfold parityOriginalShiftTwoBilinearMellinFourierBox434
    parityOriginalShiftTwoBilinearMellinHBox434
  calc
    (∑ u ∈ Finset.Ioc 0 Y,
      (sourceOriginalPureMellinPhase434 rho u *
        parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2)) =
      ∑ u ∈ Finset.Ioc 0 Y, ∫ ξ, H u ξ * C u ∂μ := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [integral_mul_const, ←(hA u hu).2]
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

/-! ## OriginalMellinFourierTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Genuine original physical h=-2 full B590 f0/f1 gates with
arbitrary real Mellin twisting sourceOriginalPureMellinPhase434 rho u
and all positive mn=u+2 factorisations. This is NOT the original
unsmoothed sourceOriginalA, because the original Ppart cap Rankin
removal still precedes its physical B590 assignment. -/
def parityOriginalShiftTwoBilinearFullMellinPhysical434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (sourceOriginalPureMellinPhase434 rho u *
      parityOriginalB590FullPhysicalAAtU434 d L E u band slot *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- TRUE source Mellin rho-twisted full-minus-frequency-BOX complex
h=-2 bilinear difference is bounded by the SAME actual original
W1(u) tau(u+2) arithmetic mass × sumδ,i Fourier tail budget as the
untwisted case, uniformly in rho∈R. The reason is precise:
`|u^(i rho)|=1` at every u (including source n=0 by the frozen
Complex.exp definition); no fake separability into alpha_m beta_n.
This provides the missing uniform-Fourier-tail side of actual
nonzero-Mellin historical Parity(4.7). It is *not* the SOURCE Rankin
Ppart cap comparison, which remains to be proved uniformly in rho. -/
theorem parity_original_hminus2_mellin_full_minus_box_le_arithmetic_tail434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsiPos : ∀ x, 0 ≤ Psi x)
    (hPsiLe : ∀ x, Psi x ≤ 1)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Acoef Bcoef : ℝ) (hA : 0 ≤ Acoef) (hB : 0 ≤ Bcoef)
    (hα : ∀ m ∈ K, ‖α m‖ ≤ Acoef)
    (hβ : ∀ n ∈ J, ‖β n‖ ≤ Bcoef)
    (rho : ℝ) (Y : ℕ) (T : ℝ) :
    ‖parityOriginalShiftTwoBilinearFullMellinPhysical434 d L E band slot
        Psi K J α β rho Y -
      parityOriginalShiftTwoBilinearMellinFourierBox434 d L E band slot
        Psi K J α β rho Y T‖ ≤
    (Acoef*Bcoef) *
      (∑ u ∈ Finset.Ioc 0 Y,
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)) *
      (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∑ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length,
          parityOriginalB590OneCoordinateFourierTail434 δ i T) := by
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let tail : ℝ := ∑ δ : Fin N → Bool, ∑ i : Fin N,
    parityOriginalB590OneCoordinateFourierTail434 δ i T
  let w := fun u => sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u
  let D : ℕ → ℂ := fun u =>
    parityOriginalB590FullPhysicalAAtU434 d L E u band slot -
      parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α z.1*β z.2
  let P : ℕ → ℂ := fun u => sourceOriginalPureMellinPhase434 rho u
  let S : ℕ → ℂ := fun u => (Psi ((u:ℝ)/Real.exp L):ℂ)
  have ht : 0 ≤ tail := by
    apply Finset.sum_nonneg
    intro δ hd
    apply Finset.sum_nonneg
    intro i hi
    unfold parityOriginalB590OneCoordinateFourierTail434
    exact mul_nonneg
      (setIntegral_nonneg measurableSet_Icc.compl (fun ξ _ => norm_nonneg _))
      (Finset.prod_nonneg (by intro j hj; exact integral_nonneg (fun ξ => norm_nonneg _)))
  have hw (u : ℕ) : 0 ≤ w u := source_original_W1_nonneg _ _
  have hD (u : ℕ) : ‖D u‖ ≤ w u*tail :=
    parity_original_B590_full_physical_A_minus_box_le_W1_tail434
      d L E hL u band slot T
  have hB (u : ℕ) : ‖B u‖ ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef :=
    parity_original_shift_two_bilinear_fibre_norm_le_tau434 K J u
      α β Acoef Bcoef hA hB hα hβ
  have hTerm (u : ℕ) :
      ‖(P u*D u*S u)*B u‖ ≤
      (Acoef*Bcoef)*(w u*((u+2).divisors.card:ℝ))*tail := by
    rw [norm_mul,norm_mul,norm_mul]
    have hphase : ‖P u‖ = 1 := source_original_pure_mellin_phase_norm_one434 _ _
    have hΨpos : 0 ≤ Psi ((u:ℝ)/Real.exp L) := hPsiPos _
    have hΨle : Psi ((u:ℝ)/Real.exp L) ≤ 1 := hPsiLe _
    have hΨ : ‖S u‖ = Psi ((u:ℝ)/Real.exp L) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hΨpos]
    rw [hphase,one_mul,hΨ]
    have hWt : 0 ≤ w u*tail := mul_nonneg (hw u) ht
    have hB0 : 0 ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef := by positivity
    calc
      _ ≤ ((w u*tail)*Psi ((u:ℝ)/Real.exp L))*
          (((u+2).divisors.card:ℝ)*Acoef*Bcoef) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_right (hD u) hΨpos)
          (hB u) (norm_nonneg _) (mul_nonneg hWt hΨpos)
      _ ≤ (w u*tail)*(((u+2).divisors.card:ℝ)*Acoef*Bcoef) :=
        mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hWt hΨle) hB0
      _ = _ := by ring
  unfold parityOriginalShiftTwoBilinearFullMellinPhysical434
    parityOriginalShiftTwoBilinearMellinFourierBox434
  rw [←Finset.sum_sub_distrib]
  have hDiff :
      (∑ u ∈ Finset.Ioc 0 Y,
        ((P u*parityOriginalB590FullPhysicalAAtU434 d L E u band slot*S u)*B u -
          (P u*parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T*S u)*B u)) =
      ∑ u ∈ Finset.Ioc 0 Y, (P u*D u*S u)*B u := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [D]
    ring
  rw [hDiff]
  calc
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y, ‖(P u*D u*S u)*B u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        (Acoef*Bcoef)*(w u*((u+2).divisors.card:ℝ))*tail := by
      apply Finset.sum_le_sum
      intro u hu
      exact hTerm u
    _ = (Acoef*Bcoef) *
        (∑ u ∈ Finset.Ioc 0 Y, w u*((u+2).divisors.card:ℝ))*tail := by
      rw [←Finset.sum_mul,←Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinFourierTailAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Complete source original B590 h=-2 alpha beta Fourier-frequency
cutoff error with arbitrary nonzero Mellin parameter rho is
`O_A(exp L L^-A)` uniformly for EVERY rho∈R, original moving
r0=20 Q depth, reserved Q band/slot, true labelled Q/P factorial,
W1(P,u), original Psi supported in [1,2] and any finite bounded
alpha_m beta_n on mn=u+2. The proof chooses the f0/f1 Schwartz
moment precision AFTER the fixed W1 divisor expense and observes
that the genuine source imaginary Mellin phase u^(i rho) has modulus 1.
This is a direct complex difference of the actual full-vs-box SOURCE
B590 physical αβ sums, not merely a Fourier budget.

This theorem does NOT assert the independent original sourceOriginalA
unsmoothed-to-physical Rankin comparison uniformly in rho; that is a
remaining nontrivial source-analysis obligation. -/
theorem parity_eventually_original_hminus2_mellin_full_minus_box_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      0 < L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E rho : ℝ) (Psi : ℝ → ℝ),
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearFullMellinPhysical434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β rho ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoBilinearMellinFourierBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β rho ⌊2*Real.exp L⌋₊ L‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_B590_arithmetic_fourier_tail_all_log434 A,
    eventually_gt_atTop (0:ℝ)] with L hBudget hLp
  refine ⟨hLp,?_⟩
  intro band slot E rho Psi hPsiPos hPsiLe K J α β
    Acoef Bcoef hA hB hα hβ
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let M : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((u+2).divisors.card:ℝ)
  let T : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      parityOriginalB590OneCoordinateFourierTail434 δ i L
  have hNorm := parity_original_hminus2_mellin_full_minus_box_le_arithmetic_tail434
    d L E hLp band slot Psi hPsiPos hPsiLe
    K J α β Acoef Bcoef hA hB hα hβ rho Y L
  have hTail := hBudget band slot
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hA hB
  calc
    _ ≤ (Acoef*Bcoef)*M*T := hNorm
    _ = (Acoef*Bcoef)*(M*T) := by ring
    _ ≤ (Acoef*Bcoef)*(Real.exp L*L^(-A)) :=
      mul_le_mul_of_nonneg_left hTail hAB
    _ = Acoef*Bcoef*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinBufferRankin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Exact SOURCE original B590 f0/f1 allocation defect with an
arbitrary real Mellin rho: the genuine original source u^(i rho)
multiplies the full original factorial/Q/P W1/parity defect before
the h=-2 alpha-beta convolution; no separability assumption on
alpha_m,beta_n since rho lives on u=mn-2. -/
def parityOriginalShiftTwoBilinearMellinBufferError434
    (d : ℕ) (L E : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (α β : ℕ → ℂ) (rho : ℝ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    (sourceOriginalPureMellinPhase434 rho u *
      (((parityOriginalFullQBufferDefectAtU434 d L E band slot u *
        Psi ((u:ℝ)/Real.exp L):ℝ):ℂ))) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- The genuine original h=-2 Mellin rho twisted buffered SOURCE
Rankin error is bounded by the SAME discarded beta/4-Ppart W1τ
mass as the untwisted source, for EVERY real rho, because
`‖sourceOriginalPureMellinPhase434 rho u‖=1` pointwise. This does not
claim the untwisted bilinear bound can be reused by replacing
alpha_m or beta_n (which would be wrong for u=mn-2); the true
termwise absolute comparison is proved. -/
theorem parity_original_shift_two_mellin_buffer_pre_cauchy_tau434
    (betaP : ℝ) (hbetaP : 0 < betaP)
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hElo : 1 ≤ E) (hEhi : E ≤ Real.exp ((1-betaP)*L))
    (Psi : ℝ → ℝ)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsi0 : ∀ t, 0 ≤ Psi t) (hPsi1 : ∀ t, Psi t ≤ 1)
    (band : Fin (d+1))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ betaP/4)
    (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ m ∈ K, ‖α m‖ ≤ A)
    (hβ : ∀ n ∈ J, ‖β n‖ ≤ B)
    (rho : ℝ) :
    ‖parityOriginalShiftTwoBilinearMellinBufferError434
      d L E band slot Psi K J α β rho (⌊2*Real.exp L⌋₊)‖ ≤
      A*B*(∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := by
  let Y := ⌊2*Real.exp L⌋₊
  let D := parityOriginalFullQBufferDefectAtU434 d L E band slot
  let C := fun u => ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
    α z.1 * β z.2
  have hD (u : ℕ) : 0 ≤ D u ∧
      D u ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u :=
    parity_original_actual_A_buffer_defect_le_W1434 d L E hL u band slot
  have hRetained (u : ℕ) (hLarge : Real.exp L ≤ (u:ℝ))
      (hCap : parityOriginalPhysicalPcapBeta434 betaP L u) : D u = 0 :=
    parity_original_beta_retained_XA_at_u_defect_zero434
      betaP hbetaP d L E hL hElo hEhi u hLarge hCap band hBand slot
  have hTerm (u : ℕ) (hu : u ∈ Finset.range (Y+1)) :
      ‖sourceOriginalPureMellinPhase434 rho u *
         (((D u * Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)) * C u‖ ≤
      A*B*(if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := by
    rw [norm_mul, norm_mul, source_original_pure_mellin_phase_norm_one434,one_mul]
    have hC := parity_original_shift_two_bilinear_fibre_norm_le_tau434
      K J u α β A B hA hB hα hβ
    have hD0 := (hD u).1
    have hDhi := (hD u).2
    have hPsiPos := hPsi0 ((u:ℝ)/Real.exp L)
    have hPsiHi := hPsi1 ((u:ℝ)/Real.exp L)
    by_cases hCap : parityOriginalPhysicalPcapBeta434 betaP L u
    · by_cases hPsiZero : Psi ((u:ℝ)/Real.exp L)=0
      · simp [hCap,hPsiZero]
      · have hS : ((u:ℝ)/Real.exp L) ∈ Set.Icc (1:ℝ) 2 :=
          hSupport (by simpa [Function.mem_support] using hPsiZero)
        have huLarge : Real.exp L ≤ (u:ℝ) := by
          have hExp : 0 < Real.exp L := Real.exp_pos _
          have h := (le_div_iff₀ hExp).mp hS.1
          simpa only [one_mul] using h
        have hZero := hRetained u huLarge hCap
        simp [hCap,hZero]
    · simp only [if_neg hCap]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hD0 hPsiPos)]
      have hProd : D u * Psi ((u:ℝ)/Real.exp L) ≤
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u := by
        calc
          _ ≤ D u := mul_le_of_le_one_right hD0 hPsiHi
          _ ≤ _ := hDhi
      calc
        _ ≤ (D u * Psi ((u:ℝ)/Real.exp L)) *
            (((u+2).divisors.card:ℝ)*A*B) :=
              mul_le_mul_of_nonneg_left hC (mul_nonneg hD0 hPsiPos)
        _ ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            (((u+2).divisors.card:ℝ)*A*B) :=
              mul_le_mul_of_nonneg_right hProd (by positivity)
        _ = A*B*(sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            ((u+2).divisors.card:ℝ)) := by ring
  unfold parityOriginalShiftTwoBilinearMellinBufferError434
  let W : ℕ → ℂ := fun u =>
    (sourceOriginalPureMellinPhase434 rho u *
      (((D u*Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)))*C u
  have hTriangle := norm_sum_le (Finset.range (Y+1)) W
  calc
    _ ≤ ∑ u ∈ Finset.range (Y+1), ‖W u‖ := hTriangle
    _ ≤ ∑ u ∈ Finset.range (Y+1),
        A*B*(if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
          else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) := Finset.sum_le_sum hTerm
    _ = _ := by rw [←Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinHBoxAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- TRUE original h=-2 alpha beta full physical B590 f0/f1 source,
with ANY real Mellin rho, is within `Acoef Bcoef exp(L)L^-A` of the
ACTUAL selected-e × physical `v^(i rho) W1(P,v) oddOmega_P(v)
H_0(vStar)` coefficient inside one true real N-dimensional Fourier
BOX [-L,L]^N. All original factorial-labelled Q primes, reserved
source Q, u=e*v, physical h=-2 mn=u+2 and Psi are preserved.

The error is a *direct complex norm of genuine source forms* and
uniform in rho and reserved Q position. This combines independently
verified source-Mellin exact Q/P H Fourier-BOX equality with the true
Schwartz moment and arithmetic `ΣW1(u)τ(u+2)` cutoff saving.
It is a FULL-PHYSICAL→H box result, not yet an UNSMOOTHED sourceOriginalA
Rankin bridge uniformly in rho. Nonzero reserved-prime Mellin σ and
historical ε(v) still require separate exact source comparison. -/
theorem parity_eventually_original_hminus2_full_physical_mellin_to_H_box_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      0 < L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E rho : ℝ) (Psi : ℝ → ℝ),
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearFullMellinPhysical434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β rho ⌊2*Real.exp L⌋₊ -
        parityOriginalShiftTwoBilinearMellinHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β rho ⌊2*Real.exp L⌋₊ L‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_mellin_full_minus_box_all_log434 A]
    with L h
  refine ⟨h.1,?_⟩
  intro band slot E rho Psi hPsi0 hPsi1 K J α β
    Acoef Bcoef hA hB hα hβ
  rw [←parity_original_hminus2_bilinear_mellin_fourier_box_eq_source_H434
    (sourceOriginalLiteralDepth 20 L) L E h.1 rfl band slot
      Psi K J α β rho ⌊2*Real.exp L⌋₊ L]
  exact h.2 band slot E rho Psi hPsi0 hPsi1 K J α β
    Acoef Bcoef hA hB hα hβ
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinSourcePhysical -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The TRUE original h=-2 UNSMOOTHED `sourceOriginalA` source
bilinear sum with arbitrary imaginary Mellin twist u^(i rho) on
actual u=mn-2, preserving all 20! labelled Q/P factorial, source
odd multiplicity parity, original real Psi and complex alpha beta. -/
def parityOriginalShiftTwoBilinearMellinSource434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    (sourceOriginalPureMellinPhase434 rho u *
      ((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalPAllActualBands 20 L) u *
        Psi ((u:ℝ)/Real.exp L):ℝ):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- Complete true B590 f0/f1 actual Q/P allotted source as a
finite h=-2 bilinear u-sum with the SAME nonseparable u^(i rho)
phase, before Fourier truncation and true beta/4 Ppart Rankin.
This includes the source u=0 term exactly; support Psi⊆[1,2]
will eliminate it only in a later theorem. -/
def parityOriginalShiftTwoBilinearMellinB590PhysicalRange434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    (sourceOriginalPureMellinPhase434 rho u *
      ((∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
        parityActualOriginalAFullBranchWeight434 d L E u band slot
          (fun _ => 0) z) *
       (Psi ((u:ℝ)/Real.exp L):ℂ))) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- Exact TRUE original SOURCE minus actual full physical B590
allocation mass under nonseparable Mellin twist u^(i rho): it is
precisely the genuine source full Q factorial buffer defect,
multiplied by the same original Psi and h=-2 alpha/beta pair sum.
No asymptotic or sign assumption, no deleted u=0 term, no restricted
Fourier frequencies. -/
theorem parity_original_shift_two_mellin_source_minus_B590_exact434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (α β : ℕ → ℂ) (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearMellinSource434 d L Psi K J α β rho Y -
      parityOriginalShiftTwoBilinearMellinB590PhysicalRange434
        d L E band slot Psi K J α β rho Y =
      parityOriginalShiftTwoBilinearMellinBufferError434
        d L E band slot Psi K J α β rho Y := by
  unfold parityOriginalShiftTwoBilinearMellinSource434
    parityOriginalShiftTwoBilinearMellinB590PhysicalRange434
    parityOriginalShiftTwoBilinearMellinBufferError434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hA := parity_actual_original_A_full_Q_buffered_allocation_defect434
    d L E hL u band slot
  have hM := parity_actual_original_A_zero_freq_full_branch_mass_exact434
    d L E u band slot
  have hScalar :
    ((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalPAllActualBands 20 L) u : ℝ):ℂ) -
    (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchWeight434 d L E u band slot
        (fun _ => 0) z) =
    ((parityOriginalFullQBufferDefectAtU434 d L E band slot u:ℝ):ℂ) := by
    rw [hM]
    exact_mod_cast hA
  calc
    _ = (sourceOriginalPureMellinPhase434 rho u *
      (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalPAllActualBands 20 L) u:ℝ):ℂ) -
       (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
          parityActualOriginalAFullBranchWeight434 d L E u band slot
            (fun _ => 0) z)) *
       (Psi ((u:ℝ)/Real.exp L):ℂ)) *
       (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2) := by push_cast; ring
    _ = _ := by rw [hScalar]; push_cast; ring

/-- Source support Psi(0)=0 makes the genuine u=0 physical B590
term vanish for arbitrary rho and alpha/beta; the source Mellin phase
at 0 is not assumed zero or undefined. The retained physical source
is exactly over the positive carrier `(0,Y]`. -/
theorem parity_original_shift_two_mellin_B590_range_eq_Ioc434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0=0)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearMellinB590PhysicalRange434
      d L E band slot Psi K J α β rho Y =
    parityOriginalShiftTwoBilinearFullMellinPhysical434
      d L E band slot Psi K J α β rho Y := by
  unfold parityOriginalShiftTwoBilinearMellinB590PhysicalRange434
    parityOriginalShiftTwoBilinearFullMellinPhysical434
  rw [parity_original_sum_range_eq_Ioc_of_zero434]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [parity_original_B590_full_physical_A_is_source_zero_freq434]
    ring
  · simp [hPsi0]
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinSourceRankinAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- TRUE original source f0/f1 allocation buffer error under an
arbitrary real source Mellin rho, including literal unsmoothed
sourceOriginalA 20!-Q/P factorial and original h=-2 alpha beta:
for any requested A and fixed beta>0 it costs at most
`Acoef Bcoef exp L L^-A`, uniformly over rho∈R. This is the
correct source pre-Cauchy Rankin proof: the phase is on u=mn-2 and
is bounded inside the ORIGINAL termwise divisor envelope, not split
between arbitrary alpha_m and beta_n. -/
theorem parity_eventually_original_hminus2_mellin_buffer_all_log434
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
      ‖parityOriginalShiftTwoBilinearMellinBufferError434
        (sourceOriginalLiteralDepth 20 L) L E band slot
        Psi K J α β rho (⌊2*Real.exp L⌋₊)‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_beta_Pcap_discard_W1_shifted_tau_all_log434
      betaP A hbetaP,
    parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ] with
    L hRankin hDepth
  refine ⟨hRankin.1,hDepth,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  have hLp : 0 < L := by nlinarith [hRankin.1]
  have hActual : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤ betaP/4 := by
    rw [hb]; exact hBand
  have hPre := parity_original_shift_two_mellin_buffer_pre_cauchy_tau434
    betaP hbetaP (sourceOriginalLiteralDepth 20 L) L E hLp
    hElo hEhi Psi hSupport hPsi0 hPsi1 band hActual slot
    K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  have hRange := parity_original_beta_shifted_tau_Pcap_range_eq_Ioc434
    betaP L hbetaP (le_of_lt hLp) ⌊2*Real.exp L⌋₊
  have hIte :
      (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) =
      (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        (if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
         else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
          ((u+2).divisors.card:ℝ)) := by
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hc : parityOriginalPhysicalPcapBeta434 betaP L u <;> simp [hc]
  rw [hIte,hRange] at hPre
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hAcoef hBcoef
  calc
    _ ≤ (Acoef*Bcoef)*
      (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        (if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
          else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u)*
          ((u+2).divisors.card:ℝ)) := hPre
    _ ≤ (Acoef*Bcoef)*(Real.exp L*L^(-A)) :=
      mul_le_mul_of_nonneg_left hRankin.2 hAB
    _ = Acoef*Bcoef*Real.exp L*L^(-A) := by ring

/-- SOURCE original unsmoothed h=-2 alpha beta vs full r0=20
true B590 allocation model, with the arbitrary Mellin rho phase
carried on u=mn-2, has a uniform O_A(exp L L^-A) bound. This is a
genuine original SOURCE-to-physical complex difference, NOT a
postulated freedom to multiply the earlier untwisted estimate by
a unit-modulus phase after summation. -/
theorem parity_eventually_original_hminus2_mellin_source_to_physical_all_log434
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
       parityOriginalShiftTwoBilinearFullMellinPhysical434
        (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β rho ⌊2*Real.exp L⌋₊‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_mellin_buffer_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  have hLp : 0 < L := by nlinarith [h.1]
  have hPsiAtZero : Psi 0 = 0 :=
    parity_original_Psi_support_zero434 Psi hSupport
  rw [←parity_original_shift_two_mellin_B590_range_eq_Ioc434
      (sourceOriginalLiteralDepth 20 L) L E band slot Psi hPsiAtZero
      K J α β rho ⌊2*Real.exp L⌋₊]
  rw [parity_original_shift_two_mellin_source_minus_B590_exact434
      (sourceOriginalLiteralDepth 20 L) L E hLp band slot Psi
      K J α β rho ⌊2*Real.exp L⌋₊]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
end Green64Analytic.Parity

end

end

/-! ## OriginalActualMellinHBoxSourceAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- TRUE original Parity §4.1--§4.2 unsmoothed `sourceOriginalA` h=-2
bilinear with arbitrary real Mellin rho is approximated by its
literal ORIGINAL FULL 20!-labelled-Q/P reserved-prime H(vStar)
`[-L,L]^N` Fourier BOX and physically split Mellin coefficients
`e^(i rho) a_e^selected(δ,ξ,e)` and
`v^(i rho) W1(P,v) oddOmega_P(v) H_0(vStar)`:

`‖originalSource_rho - originalHBox_rho‖
 <= 2 Acoef Bcoef exp(L) L^-A`.

Uniform for EVERY rho∈R, fixed beta>0 and arbitrary inverse-log
accuracy A, true retained reserved jQ band, original E range,
original Ψ∈[0,1] supported [1,2], any actual finite α,β supports
K,J and true physical mn=u+2. Source proof consists of two
independent genuine complex errors: the ORIGINAL Q allocation
buffer/β/4 Ppart Rankin with Mellin twist applied at u=mn−2,
and the full original source B590 Schwartz Fourier tail after
W1(u)τ(u+2) expense. The Mellin phase has unit modulus and exact
`u=e*v` splitting on the original Q product gate. No false
factorisation into α_m β_n nor fake Fourier ξ=0 integration.

The reserved p imaginary phase σ is fixed to 0: this SOURCE does not
yet claim the post-integrated historical full Parity(4.7) B', signed
ε(v) convention, Parity(4.17), TypeII(4.2) or Green64.green_64. -/
theorem parity_eventually_original_hminus2_source_mellin_to_H_box_all_log434
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
        parityOriginalShiftTwoBilinearMellinHBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β rho ⌊2*Real.exp L⌋₊ L‖ ≤
        2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_mellin_source_to_physical_all_log434
      betaP A hbetaP jQ hBand,
    parity_eventually_original_hminus2_full_physical_mellin_to_H_box_all_log434 A]
    with L hSource hBox
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let S : ℂ := parityOriginalShiftTwoBilinearMellinSource434
    d L Psi K J α β rho Y
  let P : ℂ := parityOriginalShiftTwoBilinearFullMellinPhysical434
    d L E band slot Psi K J α β rho Y
  let B : ℂ := parityOriginalShiftTwoBilinearMellinHBox434
    d L E band slot Psi K J α β rho Y L
  have hFirst : ‖S-P‖ ≤ Acoef*Bcoef*Real.exp L*L^(-A) :=
    hSource.2.2 band hb E hElo hEhi Psi hSupport hPsiPos hPsiLe
      slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ rho
  have hSecond : ‖P-B‖ ≤ Acoef*Bcoef*Real.exp L*L^(-A) :=
    hBox.2 band slot E rho Psi hPsiPos hPsiLe
      K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  change ‖S-B‖ ≤ 2*Acoef*Bcoef*Real.exp L*L^(-A)
  calc
    _ = ‖(S-P)+(P-B)‖ := by ring
    _ ≤ ‖S-P‖+‖P-B‖ := norm_add_le _ _
    _ ≤ (Acoef*Bcoef*Real.exp L*L^(-A)) +
      (Acoef*Bcoef*Real.exp L*L^(-A)) := add_le_add hFirst hSecond
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinOutsideEPreCauchy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Literal historical Parity(4.5) OUTSIDE selected-e window on the
ORIGINAL h=-2 B590 Fourier box: all 20! Q prime labelled tuples,
W1, odd multiplicity parity, Psi and the true mn=u+2 alpha/beta.
No proxy e-support assumption: outside branches are kept as the actual
truncated Fourier integrals (which need not be zero individually). -/
def parityOriginalShiftTwoBilinearMellinOutsideEBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (rho : ℝ) (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (sourceOriginalPureMellinPhase434 rho u *
    (parityOriginalB590BoxPhysicalOutsideEAtU434 d L E u band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ))) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- TRUE outside-e-box pre-Cauchy bound after summing all h=-2
alpha_m beta_n factorisations. The retained beta/4 source Ppart has
arbitrary small L^-A leakage; the discarded part has only its honest
source Fourier-variation times the exact W1(u)tau(u+2) mass.
This is a bound on a literal COMPLEX source bilinear difference, not
an unconnected variation budget or artificial zero of Fourier gates. -/
theorem parity_eventually_original_hminus2_mellin_outside_e_box_pre_cauchy434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (rho : ℝ),
      ‖parityOriginalShiftTwoBilinearMellinOutsideEBox434
        (sourceOriginalLiteralDepth 20 L) L E band slot Psi K J α β rho
        ⌊2*Real.exp L⌋₊ L‖ ≤
      Acoef*Bcoef *
        ((L^(-A)) *
          (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
            sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            ((u+2).divisors.card:ℝ)) +
        (∑ δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool,
          parityOriginalB590FourierBranchVariation434 δ) *
        (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
          (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
            else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
            ((u+2).divisors.card:ℝ))) := by
  filter_upwards [parity_eventually_original_B590_outside_e_Psi_pointwise_bound434
    beta A hbeta jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro E hE hEcap Psi hSupport hPsi0 hPsi1 band hb slot
    K J α β Acoef Bcoef hA hB hα hβ rho
  let Y := ⌊2*Real.exp L⌋₊
  let w : ℕ → ℝ := fun u => sourceOriginalW1
    (sourceOriginalPAllActualBands 20 L) u
  let t : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length → Bool,
    parityOriginalB590FourierBranchVariation434 δ
  let c : ℕ → ℝ := fun u => if parityOriginalPhysicalPcapBeta434 beta L u then 0 else t
  let Q : ℕ → ℂ := fun u => parityOriginalB590BoxPhysicalOutsideEAtU434
    (sourceOriginalLiteralDepth 20 L) L E u band slot L *
    (Psi ((u:ℝ)/Real.exp L):ℂ)
  let F : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      α z.1*β z.2
  have hU (u : ℕ) : ‖Q u‖ ≤ w u*(L^(-A)+c u) :=
    h.2.2 E hE hEcap Psi hSupport hPsi0 hPsi1 u band hb slot
  have hF (u : ℕ) : ‖F u‖ ≤
      ((u+2).divisors.card:ℝ)*Acoef*Bcoef :=
    parity_original_shift_two_bilinear_fibre_norm_le_tau434 K J u
      α β Acoef Bcoef hA hB hα hβ
  have hw (u : ℕ) : 0 ≤ w u := source_original_W1_nonneg _ _
  have ht : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hPow : 0 ≤ L^(-A) := Real.rpow_nonneg (by linarith [h.1]) _
  have hc (u : ℕ) : 0 ≤ c u := by
    dsimp [c]
    split <;> positivity
  have hterm (u : ℕ) :
      ‖(sourceOriginalPureMellinPhase434 rho u*Q u)*F u‖ ≤ Acoef*Bcoef *
        (w u * ((u+2).divisors.card:ℝ) * (L^(-A)+c u)) := by
    rw [norm_mul,norm_mul,source_original_pure_mellin_phase_norm_one434,one_mul]
    have hn : 0 ≤ (w u*(L^(-A)+c u)) :=
      mul_nonneg (hw u) (add_nonneg hPow (hc u))
    have hn2 : 0 ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef := by positivity
    calc
      _ ≤ (w u*(L^(-A)+c u))*
          (((u+2).divisors.card:ℝ)*Acoef*Bcoef) :=
        mul_le_mul (hU u) (hF u) (norm_nonneg _) hn
      _ = _ := by ring
  unfold parityOriginalShiftTwoBilinearMellinOutsideEBox434
  calc
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        ‖(sourceOriginalPureMellinPhase434 rho u*Q u)*F u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        Acoef*Bcoef*(w u*((u+2).divisors.card:ℝ)*(L^(-A)+c u)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hterm u
    _ = Acoef*Bcoef *
        (∑ u ∈ Finset.Ioc 0 Y, w u*((u+2).divisors.card:ℝ)*(L^(-A)+c u)) := by
      rw [Finset.mul_sum]
    _ = Acoef*Bcoef *
        (L^(-A)*(∑ u ∈ Finset.Ioc 0 Y,
          w u*((u+2).divisors.card:ℝ)) +
         t*(∑ u ∈ Finset.Ioc 0 Y,
          (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
            else w u)*((u+2).divisors.card:ℝ))) := by
      congr 1
      have hSplit (u : ℕ) :
          w u * ((u+2).divisors.card:ℝ) * (L^(-A)+c u) =
          L^(-A)*(w u*((u+2).divisors.card:ℝ)) +
          t*((if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
              else w u)*((u+2).divisors.card:ℝ)) := by
        by_cases hp : parityOriginalPhysicalPcapBeta434 beta L u
        · simp [c,hp]
          ring
        · simp [c,hp]
          ring
      conv_lhs =>
        arg 2
        ext u
        rw [hSplit u]
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinOutsideEAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- FULL unconditional original Parity §4.2 (4.5) source e-window
truncation: the ACTUAL h=-2 complex α_m β_n Fourier-BOX contribution
from selected e OUTSIDE `[E*L^-88,E]` is negligible with arbitrary
inverse-log precision, uniformly in all original reserved Q slots and
all originally allowed `1≤E≤exp((1-beta)L)`.
The retained beta/4 original Ppart uses true real f0/f1 gate support,
and outside window the truncated integral is bounded by Fourier tails,
not assumed zero. The discarded Ppart gets the original weighted
shifted-divisor Rankin estimate times genuine Fourier variation. All
original factorial W1/P parity and source `mn=u+2` factors are kept.
The constant 2 is explicit; accuracy A and beta are arbitrary fixed
parameters. This establishes support truncation for the integrated
source object, NOT pointwise ξ support or finished Parity(4.7) a_e. -/
theorem parity_eventually_original_hminus2_mellin_outside_e_fourier_box_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ∀ (rho : ℝ),
      ‖parityOriginalShiftTwoBilinearMellinOutsideEBox434
        (sourceOriginalLiteralDepth 20 L) L E band slot Psi K J α β rho
        ⌊2*Real.exp L⌋₊ L‖ ≤
        2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  let D := parityOriginalOutsideEBoxRetainedAccuracy434 A
  let R := parityOriginalOutsideEBoxDiscardAccuracy434 A
  filter_upwards [parity_eventually_original_hminus2_mellin_outside_e_box_pre_cauchy434
      beta D hbeta jQ hBand,
    parity_eventually_original_W1_shifted_tau_total_mass_polylog434,
    parity_eventually_original_beta_Pcap_discard_W1_shifted_tau_all_log434
      beta R hbeta,
    parity_eventually_original_B590_actual_full_fourier_variation_polylog434]
    with L hPre hTotal hDiscard hVariation
  refine ⟨hPre.1,hPre.2.1,?_⟩
  intro E hE hEcap Psi hSupport hPsi0 hPsi1 band hb slot
    K J α β Acoef Bcoef hA hB hα hβ rho
  let Y := ⌊2*Real.exp L⌋₊
  let M : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
    ((u+2).divisors.card:ℝ)
  let V : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length → Bool, parityOriginalB590FourierBranchVariation434 δ
  let B : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
     else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
     ((u+2).divisors.card:ℝ)
  have hLp : 0 < L := by linarith [hPre.1]
  have hMass : M ≤ Real.exp L*L^parityOriginalW1PolylogExponent434*L^16 := hTotal
  have hV : V ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 :=
    hVariation band slot
  have hDiscardBound : B ≤ Real.exp L*L^(-R) := hDiscard.2
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hVnonneg : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro u hu
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · simp [hc]
    · simp only [if_neg hc]
      exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hD0 : 0 ≤ L^(-D) := Real.rpow_nonneg hLp.le _
  have hR0 : 0 ≤ L^(-R) := Real.rpow_nonneg hLp.le _
  have hCF0 : 0 ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 :=
    Real.rpow_nonneg hLp.le _
  have hFirst : L^(-D)*M ≤ Real.exp L*L^(-A) := by
    calc
      _ ≤ L^(-D)*(Real.exp L*L^parityOriginalW1PolylogExponent434*L^16) :=
        mul_le_mul_of_nonneg_left hMass hD0
      _ = Real.exp L*(L^parityOriginalW1PolylogExponent434*L^16*L^(-D)) := by ring
      _ = Real.exp L*L^(-A) := by
        have h := parity_original_B590_arithmetic_fourier_power_cancel434 L A hLp
        change L^parityOriginalW1PolylogExponent434*L^16*L^(-D) = L^(-A) at h
        rw [h]
  have hSecond : V*B ≤ Real.exp L*L^(-A) := by
    calc
      _ ≤ V*(Real.exp L*L^(-R)) := mul_le_mul_of_nonneg_left hDiscardBound hVnonneg
      _ ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 *
          (Real.exp L*L^(-R)) :=
        mul_le_mul_of_nonneg_right hV
          (mul_nonneg (Real.exp_nonneg _) hR0)
      _ = Real.exp L*(L^parityOriginalB590FixedFourierPolynomialExponent434*
          L^(-R)) := by ring
      _ = Real.exp L*L^(-A) := by
        rw [parity_original_outside_e_discarded_power_cancel434 L A hLp]
  have hPreBound := hPre.2.2 E hE hEcap Psi hSupport hPsi0 hPsi1
    band hb slot K J α β Acoef Bcoef hA hB hα hβ rho
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hA hB
  calc
    _ ≤ (Acoef*Bcoef)*(L^(-D)*M+V*B) := hPreBound
    _ ≤ (Acoef*Bcoef)*((Real.exp L*L^(-A))+(Real.exp L*L^(-A))) :=
      mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hAB
    _ = 2*Acoef*Bcoef*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalPhysicalBilinearMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Literal original physical u=e*v bilinear Mellin amplitude with the
actual W1(v), multiplicity-counted P parity, original 20! Q-labelled
branch weight and complex α_m β_n on the true mn=u+2 fibre. -/
def parityOriginalActualPhysicalBilinearMellinAmplitude434
    (d : ℕ) (L E Z : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) (s : ℝ) : ℂ :=
  ∑ t ∈ parityOriginalActualMellinPhysicalCarrier434 d L band slot Y,
    (parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
        α z.1 * β z.2)) *
    parityOriginalEVMellinAmplitude434 s Z Psi hSmooth hSupport
      (parityActualOriginalAFullBranchE434 d L band slot t.2)
      (parityOriginalActualMellinPhysicalV434 d L band slot t.1 t.2)

/-- EXACT original physical 20!-labelled bilinear carrier Mellin
inversion, with proof of integrability and finite sum/integral Fubini.
The selected Q product e and true reserved-P v are sourced by the
literal Q full product gate and its already kernel-proved u=e*v,
not independent artificial endpoint variables. -/
theorem parity_original_actual_physical_bilinear_mellin_integral434
    (d : ℕ) (L E Z : ℝ) (hZ : 0 < Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    Integrable (fun s : ℝ =>
      parityOriginalActualPhysicalBilinearMellinAmplitude434
        d L E Z band slot ξ Psi hSmooth hSupport K J α β Y s) ∧
    (∑ t ∈ parityOriginalActualMellinPhysicalCarrier434 d L band slot Y,
      (parityActualOriginalAFullBranchVWeight434 d L E t.1 band slot ξ t.2 *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J t.1,
          α z.1 * β z.2)) *
      (Psi ((t.1:ℝ)/Z):ℂ)) =
    ∫ s : ℝ, parityOriginalActualPhysicalBilinearMellinAmplitude434
        d L E Z band slot ξ Psi hSmooth hSupport K J α β Y s := by
  exact parity_original_actual_physical_tuple_mellin_fubini434
    d L Z hZ band slot Y Psi hSmooth hSupport
    (fun u z => parityActualOriginalAFullBranchVWeight434
        d L E u band slot ξ z *
      (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α t.1*β t.2))
end Green64Analytic.Parity

end

end

