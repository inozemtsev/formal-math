module

public import Green64.Library.Weights.ActualGlobalKernelL2
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part015
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Correlation.Part037
public import Green64.Library.Correlation.Part038
public import Green64.Library.Weights.Part047
public import Green64.Library.Weights.Part046
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Green64.Library.Weights.Part001
public import Green64.Library.Weights.Part012
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part018
public import Green64.Library.Sieve.Foundations.Part004

@[expose] public section

/-!
# Correlation / Part039

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualKnuGlobalTransfer -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The already certified actual GLOBAL kernel acting on the original
labelled prime space. The true cell mass stays in its denominator. -/
noncomputable def sourceOriginalActualGlobalAction434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (h : ℝ) (active : Finset ℤ) (Q : ℕ)
    (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (p : SourceOriginalGramPrimeTuple434 S) : ℂ :=
  ∑ q : SourceOriginalGramPrimeTuple434 S,
    (sourceOriginalGramPrimeMass434 S mu q : ℂ) *
      sourceOriginalActualPrimitiveGlobalKernel434 Q active h
        (sourceOriginalRealGramCellMass434 S mu h)
        (sourceOriginalGramPrimeProduct434 S p)
        (sourceOriginalGramPrimeProduct434 S q) * f q

/-- Literal four-tuple signed Knu pairing: two independent original
output tuples and two original auxiliary tuples. The multiplier H
remains jointly dependent on the auxiliary tuples; it is not factored. -/
noncomputable def sourceOriginalActualKnuPair434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hA hB : ℝ) (JA JB : Finset ℤ) (Q r : ℕ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (H : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ) : ℂ :=
  sourceOriginalFiniteTwoSidedMinorBilinear434
    (fun p => (sourceOriginalGramPrimeMass434 SA muA p : ℂ))
    (fun p => (sourceOriginalGramPrimeMass434 SB muB p : ℂ))
    fA fB (fun p =>
      sourceOriginalFiniteTwoSidedMinorBilinear434
        (fun q => (sourceOriginalGramPrimeMass434 SA muA q : ℂ))
        (fun q => (sourceOriginalGramPrimeMass434 SB muB q : ℂ))
        (fun _ => 1) (fun _ => 1) (fun q =>
          sourceOriginalActualPrimitiveComparisonKernel434
            Q JA JB hA hB
            (sourceOriginalRealGramCellMass434 SA muA hA)
            (sourceOriginalRealGramCellMass434 SB muB hB)
            (sourceOriginalGramPrimeProduct434 SA q.1)
            (sourceOriginalGramPrimeProduct434 SA p.1)
            (sourceOriginalGramPrimeProduct434 SB q.2)
            (sourceOriginalGramPrimeProduct434 SB p.2) r * H q))

/-- Exact transfer of BOTH actual GLOBAL blocks onto their original
endpoint tests. No character expansion or cellwise absolute sum is used.
H can contain the full coupled Fourier phase and both dyadic gates.
This equality does NOT assert a bound for an arbitrary joint multiplier
depending simultaneously on auxiliary AND output tuples. -/
theorem source_original_actual_Knu_pair_global_transfer434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hA hB : ℝ) (JA JB : Finset ℤ) (Q r : ℕ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (H : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ) :
    sourceOriginalActualKnuPair434
      SA muA SB muB hA hB JA JB Q r fA fB H =
    -((-1:ℂ)^r) * sourceOriginalFiniteTwoSidedMinorBilinear434
      (fun p => (sourceOriginalGramPrimeMass434 SA muA p : ℂ))
      (fun p => (sourceOriginalGramPrimeMass434 SB muB p : ℂ))
      (sourceOriginalActualGlobalAction434 SA muA hA JA Q fA)
      (sourceOriginalActualGlobalAction434 SB muB hB JB Q fB) H := by
  classical
  let X := SourceOriginalGramPrimeTuple434 SA
  let Y := SourceOriginalGramPrimeTuple434 SB
  let wA : X → ℂ := fun p => (sourceOriginalGramPrimeMass434 SA muA p : ℂ)
  let wB : Y → ℂ := fun p => (sourceOriginalGramPrimeMass434 SB muB p : ℂ)
  let KA : X → X → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434 Q JA hA
      (sourceOriginalRealGramCellMass434 SA muA hA)
      (sourceOriginalGramPrimeProduct434 SA q)
      (sourceOriginalGramPrimeProduct434 SA p)
  let KB : Y → Y → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434 Q JB hB
      (sourceOriginalRealGramCellMass434 SB muB hB)
      (sourceOriginalGramPrimeProduct434 SB q)
      (sourceOriginalGramPrimeProduct434 SB p)
  have hTensor (q : X × Y) :
      (∑ p : X, wA p * KA q.1 p * fA p) *
        (∑ p : Y, wB p * KB q.2 p * fB p) =
      ∑ p : X × Y,
        wA p.1*wB p.2*fA p.1*fB p.2*KA q.1 p.1*KB q.2 p.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  unfold sourceOriginalActualKnuPair434
    sourceOriginalFiniteTwoSidedMinorBilinear434
    sourceOriginalActualGlobalAction434
    sourceOriginalActualPrimitiveComparisonKernel434
  change (∑ p : X × Y, wA p.1*wB p.2*fA p.1*fB p.2 *
      (∑ q : X × Y,
        wA q.1*wB q.2*1*1 *
          (-((-1:ℂ)^r)*KA q.1 p.1*KB q.2 p.2*H q))) =
    -((-1:ℂ)^r) *
      ∑ q : X × Y, wA q.1*wB q.2 *
        (∑ p : X, wA p*KA q.1 p*fA p) *
        (∑ p : Y, wB p*KB q.2 p*fB p) * H q
  have hGrouped (q : X × Y) :
      wA q.1*wB q.2 *
        (∑ p : X, wA p*KA q.1 p*fA p) *
        (∑ p : Y, wB p*KB q.2 p*fB p) * H q =
      wA q.1*wB q.2 *
        (∑ p : X × Y,
          wA p.1*wB p.2*fA p.1*fB p.2*KA q.1 p.1*KB q.2 p.2) * H q := by
    rw [mul_assoc (wA q.1*wB q.2), hTensor]
  simp_rw [hGrouped, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The exact input dyad gates and the original joint Fourier/Mellin phase. -/
noncomputable def sourceOriginalActualC6WindowPhase434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (SB : ιB → Finset ℕ)
    (AW BW : Finset ℕ) (theta ζ : ℝ) (k : ℤ)
    (q : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB) : ℂ :=
  if sourceOriginalGramPrimeProduct434 SA q.1 ∈ AW ∧
     sourceOriginalGramPrimeProduct434 SB q.2 ∈ BW
  then Green64SourceC6.integerPhase (-(k:ℝ)*theta)
      (((sourceOriginalGramPrimeProduct434 SA q.1 *
          sourceOriginalGramPrimeProduct434 SB q.2):ℕ):ℤ) *
    sourceOriginalPureMellinPhase434 ζ
      (sourceOriginalGramPrimeProduct434 SA q.1 *
       sourceOriginalGramPrimeProduct434 SB q.2)
  else 0

theorem source_original_actual_Knu_C6_window_transfer434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hA hB : ℝ) (JA JB : Finset ℤ) (Q r : ℕ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (AW BW : Finset ℕ) (theta ζ : ℝ) (k : ℤ) :
    sourceOriginalActualKnuPair434
      SA muA SB muB hA hB JA JB Q r fA fB
      (sourceOriginalActualC6WindowPhase434 SA SB AW BW theta ζ k) =
    -((-1:ℂ)^r) *
      (∑ qA : SourceOriginalGramPrimeTuple434 SA,
        if sourceOriginalGramPrimeProduct434 SA qA ∈ AW then
          (sourceOriginalGramPrimeMass434 SA muA qA:ℂ) *
          sourceOriginalActualGlobalAction434 SA muA hA JA Q fA qA *
          (∑ qB : SourceOriginalGramPrimeTuple434 SB,
            if sourceOriginalGramPrimeProduct434 SB qB ∈ BW then
              (sourceOriginalGramPrimeMass434 SB muB qB:ℂ) *
              sourceOriginalActualGlobalAction434 SB muB hB JB Q fB qB *
              Green64SourceC6.integerPhase (-(k:ℝ)*theta)
                (((sourceOriginalGramPrimeProduct434 SA qA *
                  sourceOriginalGramPrimeProduct434 SB qB):ℕ):ℤ) *
              sourceOriginalPureMellinPhase434 ζ
                (sourceOriginalGramPrimeProduct434 SA qA *
                 sourceOriginalGramPrimeProduct434 SB qB)
            else 0)
        else 0) := by
  rw [source_original_actual_Knu_pair_global_transfer434]
  congr 1
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro qA hqA
  by_cases ha : sourceOriginalGramPrimeProduct434 SA qA ∈ AW
  · simp only [if_pos ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro qB hqB
    by_cases hb : sourceOriginalGramPrimeProduct434 SB qB ∈ BW
    · simp only [sourceOriginalActualC6WindowPhase434, ha, hb,
        and_self, if_true]
      ring
    · simp [sourceOriginalActualC6WindowPhase434, ha, hb]
  · simp [sourceOriginalActualC6WindowPhase434, ha]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualKnuGlobalMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Applicable C6 MINOR estimate for the literal two-GLOBAL primitive
Knu pairing, using the certified physical GLOBAL norms instead of a
pointwise character/cell majorant. Both original harmonic output measures,
arbitrary mark-sensitive endpoint tests, both input windows, the exact
Fourier phase -k theta, full Mellin phase and original sign are retained.

The threshold precedes the finite group types and probe pattern.
The source O(log L) group count is handled by the existing factorial
budget C. There is NO fixed total-probe cap and NO factor depending on
Qchar, xi, the mesh width or the number of retained cells.
All arithmetic minor-arc and physical SW-band hypotheses are explicit.
This is one input rectangle, not yet the all-frequency residual. -/
theorem eventually_source_original_actual_Knu_GLOBAL_C6_minor434
    (cfg : SourceComparisonFixed434)
    (Cq : ℕ) (Cxi gamma dscale : ℝ)
    (hCxi : 0 ≤ Cxi) (hgamma : 0 < gamma) (hdscale : 0 ≤ dscale) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ) (JA JB : Finset ℤ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (fA : SourceOriginalGramPrimeTuple434
        (fun z : ν.1 => d.Tb z.val.1) → ℂ)
      (fB : SourceOriginalGramPrimeTuple434
        (fun z : ν.2 => d.Tb z.val.1) → ℂ),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (hMassA : ∀ j ∈ JA, xi ≤ sourceOriginalRealGramCellMass434 SA muA hA j)
      (hMassB : ∀ j ∈ JB, xi ≤ sourceOriginalRealGramCellMass434 SB muB hB j)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (ζ : ℝ)
      (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
      (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
      (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
      (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
      (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
      (hP : P ≤ M) (hQ : Q ≤ N)
      (D Bsave : ℝ)
      (hR : L^D ≤ (r:ℝ))
      (hNlarge : L^D ≤ (N:ℝ))
      (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
      (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤ (M:ℝ)*(N:ℝ))
      (C : ℕ)
      (hExponent : cfg.C0*
        Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
          (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
      (hSaving : Bsave+2*(C:ℝ) ≤ D),
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let EA : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA p * ‖fA p‖^2
    let EB : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB p * ‖fB p‖^2
    ‖sourceOriginalActualKnuPair434 SA muA SB muB
      hA hB JA JB Qchar (ν.1.card+ν.2.card) fA fB
      (sourceOriginalActualC6WindowPhase434 SA SB AW BW theta ζ k)‖^2 ≤
      2000*(EA*EB)*L^(-Bsave) := by
  obtain ⟨Y0,hEvent⟩ :=
    eventually_source_original_actual_GLOBAL_kernel_L2_bound_two434
      Cq Cxi gamma dscale hCxi hgamma hdscale cfg.vmin cfg.hv
  refine ⟨Y0,?_⟩
  filter_upwards [hEvent,eventually_ge_atTop (1:ℝ)] with L hKernel hL
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar JA JB
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG fA fB
  dsimp only
  intro hMassA hMassB iA iB uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
    D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
  classical
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let gA := sourceOriginalActualGlobalAction434 SA muA hA JA Qchar fA
  let gB := sourceOriginalActualGlobalAction434 SB muB hB JB Qchar fB
  let EA : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA p * ‖fA p‖^2
  let EB : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB p * ‖fB p‖^2
  let EGA : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA p * ‖gA p‖^2
  let EGB : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB p * ‖gB p‖^2
  have hNormA (z : ν.1) : ∑ p ∈ SA z, muA z p = 1 := by
    dsimp only [SA,muA]
    rw [← Finset.sum_div, ← hVbig z.val.1]
    exact div_self (cfg.hv.trans_le (d.hVbig z.val.1)).ne'
  have hNormB (z : ν.2) : ∑ p ∈ SB z, muB z p = 1 := by
    dsimp only [SB,muB]
    rw [← Finset.sum_div, ← hVbig z.val.1]
    exact div_self (cfg.hv.trans_le (d.hVbig z.val.1)).ne'
  have hPosA (z : ν.1) (p : ℕ) (_hp : p ∈ SA z) : 0 ≤ muA z p :=
    div_nonneg (by positivity) (cfg.hv.trans_le (d.hVbig z.val.1)).le
  have hPosB (z : ν.2) (p : ℕ) (_hp : p ∈ SB z) : 0 ≤ muB z p :=
    div_nonneg (by positivity) (cfg.hv.trans_le (d.hVbig z.val.1)).le
  have hEnergyA : EGA ≤ 4*EA :=
    hKernel SA muA hNormA hPosA hA hhA JA Qchar iA
      (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hBIG z.val.1 p hp⟩)
      hLdyad hQchar uA vA huA huvA hvA huLargeA huBIGA hYA
      (d.Vbig iA.val.1) (d.hVbig iA.val.1) hBandA
      (fun _ => rfl) xi hxi hXipoly hMassA fA
  have hEnergyB : EGB ≤ 4*EB :=
    hKernel SB muB hNormB hPosB hB hhB JB Qchar iB
      (fun z p hp => ⟨d.hTbPrime z.val.1 p hp,hBIG z.val.1 p hp⟩)
      hLdyad hQchar uB vB huB huvB hvB huLargeB huBIGB hYB
      (d.Vbig iB.val.1) (d.hVbig iB.val.1) hBandB
      (fun _ => rfl) xi hxi hXipoly hMassB fB
  have hEA : 0 ≤ EA := Finset.sum_nonneg (fun p _ => mul_nonneg
    (source_original_gram_full_prime_mass_nonneg434 SA muA hPosA p) (sq_nonneg _))
  have hEGB : 0 ≤ EGB := Finset.sum_nonneg (fun p _ => mul_nonneg
    (source_original_gram_full_prime_mass_nonneg434 SB muB hPosB p) (sq_nonneg _))
  have hProduct : EGA*EGB ≤ (4*EA)*(4*EB) :=
    mul_le_mul hEnergyA hEnergyB hEGB (by positivity)
  have hC6 := source_original_true_signed_raw_mellin_physical_minor434
    cfg x L Y Hprime d sep blockA blockB hDisjoint m hm ν hPattern
    ζ gA gB M N P Q hM hN a r beta0 theta k hApprox
    hr hcop hbeta hP hQ D Bsave hL hR hNlarge hMlarge hMNlarge
    C hExponent hSaving
  rw [source_original_actual_Knu_C6_window_transfer434]
  calc
    _ ≤ 125*(EGA*EGB)*L^(-Bsave) := hC6
    _ ≤ 125*((4*EA)*(4*EB))*L^(-Bsave) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hProduct (by norm_num))
        (Real.rpow_nonneg (by linarith) _)
    _ = 2000*(EA*EB)*L^(-Bsave) := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMajorSlowLogPowerBudget -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- In the genuine SOURCE03 major rational frame error, the
small denominator r <= Q <= L^Cq consumes exactly Cq of the
arbitrarily strong unconditional SW logarithmic saving.
If the physical normalizer constant K/Vmin is small enough at
the chosen large L that delta <= 1, then even the nonlinear
two-global delta² term is bounded by 3(K/Vmin)L^-B.
No assumption on character orthogonality is used here. -/
theorem source_original_major_rational_denominator_loss_absorb434
    (Q Cq r : ℕ) (L B K Vmin : ℝ)
    (hL : 1 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hrQ : r ≤ Q)
    (hK : 0 ≤ K) (hVmin : 0 < Vmin)
    (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1) :
    let delta : ℝ := (K/Vmin)*L^(-(B+(Cq:ℝ)))
    (delta+delta+delta*delta)*(r:ℝ) ≤
      3*(K/Vmin)*L^(-B) := by
  let delta : ℝ := (K/Vmin)*L^(-(B+(Cq:ℝ)))
  have hLpos : 0 < L := by linarith
  have hδ : 0 ≤ delta := by
    dsimp [delta]
    exact mul_nonneg (div_nonneg hK hVmin.le)
      (Real.rpow_nonneg hLpos.le _)
  have hδsmall : delta ≤ 1 := hDeltaLe
  have hDeltaSq : delta*delta ≤ delta := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδsmall)]
  have hdeltaBudget : delta+delta+delta*delta ≤ 3*delta := by
    linarith
  have hrnn : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hrL : (r:ℝ) ≤ L^Cq :=
    (by exact_mod_cast hrQ : (r:ℝ) ≤ Q).trans hQ
  have hPow : L^(-(B+(Cq:ℝ)))*L^Cq = L^(-B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]
    congr 1
    ring
  change (delta+delta+delta*delta)*(r:ℝ) ≤
    3*(K/Vmin)*L^(-B)
  calc
    _ ≤ (3*delta)*(r:ℝ) :=
      mul_le_mul_of_nonneg_right hdeltaBudget hrnn
    _ ≤ (3*delta)*(L^Cq) :=
      mul_le_mul_of_nonneg_left hrL (by positivity)
    _ = 3*(K/Vmin)*L^(-B) := by
      dsimp [delta]
      rw [show 3*((K/Vmin)*L^(-(B+(Cq:ℝ))))*L^Cq =
        3*(K/Vmin)*(L^(-(B+(Cq:ℝ)))*L^Cq) by ring]
      rw [hPow]

/-- Both TRUE original major-arc coefficient losses can be
made O(L^-B) simultaneously, explicitly: rational denominator
cost r<=Q consumes Cq of the SW exponent, while the two
primitive frames cost 4*Cq in the slowly-varying Mellin /
irrational-beta phase. Actual physical Vmin stays visible.
This theorem is a quantitative parameter budget, NOT a
minor-arc or raw-Hoeffding theorem. -/
theorem source_original_major_full_log_power_budget434
    (Q Cq r : ℕ) (L B K Vmin ζ beta R hA hB : ℝ)
    (hL : 1 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hrQ : r ≤ Q)
    (hK : 0 ≤ K) (hVmin : 0 < Vmin)
    (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
    (hR : 0 ≤ R)
    (hWidth : 0 ≤ hA+hB) (hWidthLe : hA+hB ≤ 1)
    (hZeta : |ζ| ≤ L^(-(B+((4*Cq:ℕ):ℝ))))
    (hBeta : 2*Real.pi*|beta| *R ≤ L^(-(B+((4*Cq:ℕ):ℝ)))) :
    let delta : ℝ := (K/Vmin)*L^(-(B+(Cq:ℝ)))
    let slow : ℝ := ((Fintype.card
       (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*
      ((|ζ|+2*Real.pi*|beta| *R)*(hA+hB))
    ((delta+delta+delta*delta)*(r:ℝ)+slow) ≤
      (3*(K/Vmin)+2)*L^(-B) := by
  have hrat := source_original_major_rational_denominator_loss_absorb434
    Q Cq r L B K Vmin hL hQ hrQ hK hVmin hDeltaLe
  have hslow := source_original_major_slow_two_char_fourier_loss_absorb434
    Q Cq L B ζ beta R hA hB hL hQ hR
    hWidth hWidthLe hZeta hBeta
  dsimp only at hrat
  dsimp only
  calc
    _ ≤ 3*(K/Vmin)*L^(-B) + 2*L^(-B) :=
      add_le_add hrat hslow
    _ = (3*(K/Vmin)+2)*L^(-B) := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimitiveReproductionFinite -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Mathematically load-bearing source comparison lemma:
a normalized primitive frame whose true diagonal is 1 and
whose genuine offdiagonal entries are epsilon reproduces any
single primitive character at a fixed physical point, with
pointwise loss at most #characters*epsilon. This is a
POINTWISE character reproduction estimate, not merely a
Gram operator norm and not a theorem about an arbitrary H(p). -/
theorem source_original_primitive_frame_reproduction_finite434
    {C : Type} [Fintype C] [DecidableEq C]
    (G : C → C → ℂ) (chi : C → ℂ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hdiag : ∀ c, G c c = 1)
    (hoff : ∀ c e, c ≠ e → ‖G c e‖ ≤ eps)
    (hchi : ∀ c, ‖chi c‖ ≤ 1)
    (e : C) :
    ‖(∑ c : C, G c e * chi c) - chi e‖ ≤
      (Fintype.card C:ℝ)*eps := by
  classical
  let H : C → ℂ := fun c =>
    (G c e - if c=e then 1 else 0)*chi c
  have hsingle :
      (∑ c : C, (if c=e then (1:ℂ) else 0)*chi c) = chi e := by
    simp
  have hrewrite :
      (∑ c : C, G c e * chi c) - chi e =
      ∑ c : C, H c := by
    calc
      _ = (∑ c : C, G c e * chi c) -
          (∑ c : C, (if c=e then (1:ℂ) else 0)*chi c) := by
             rw [hsingle]
      _ = ∑ c : C, (G c e*chi c -
          (if c=e then (1:ℂ) else 0)*chi c) := by
             rw [Finset.sum_sub_distrib]
      _ = ∑ c : C, H c := by
        apply Finset.sum_congr rfl
        intro c hc
        dsimp [H]
        ring
  have hterm (c : C) : ‖H c‖ ≤ eps := by
    by_cases heq : c=e
    · subst c
      simp [H,hdiag,heps]
    · have hentry : H c = G c e*chi c := by
        simp [H,heq]
      rw [hentry,norm_mul]
      have hz := hoff c e heq
      exact (mul_le_mul hz (hchi c) (norm_nonneg _) heps).trans_eq
        (mul_one eps)
  calc
    _ = ‖∑ c : C, H c‖ := congrArg norm hrewrite
    _ ≤ ∑ c : C, ‖H c‖ := norm_sum_le _ _
    _ ≤ ∑ _c : C, eps :=
      Finset.sum_le_sum (fun c hc => hterm c)
    _ = (Fintype.card C:ℝ)*eps := by simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalCharacterReproduction -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Unconditional pointwise character reproduction at a TRUE
physical source03 BIG prime tuple on a retained original GLOBAL
log-product cell. The character is primitive at its real conductor,
the frame is normalized by the ACTUAL cell mass nu_j >= xi,
and input tuple X may contain repeated numerical primes.
No assumption of an independent or mark-free test H. -/
theorem source_original_actual_primitive_reproduction_unconditional434
    (Cq : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (j : ℤ) (Q : ℕ)
      (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
      (hv : (v:ℝ) ≤ Real.exp (L^d))
      (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
      (huBIG : Q^2 ≤ u)
      (hY : Y ≤ ((u+1:ℕ):ℝ))
      (V : ℝ) (hV : 0 < V)
      (hBand : S i = sourceOriginalActualPrimeBand434 u v)
      (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
      (xi : ℝ) (hxi : 0 < xi)
      (hMass : xi ≤ sourceOriginalRealGramCellMass434 S mu h j)
      (p : SourceOriginalGramPrimeTuple434 S)
      (e : sourceOriginalPrimitiveFamily434 Q),
      let nu := sourceOriginalRealGramCellMass434 S mu h j
      ‖(∑ c : sourceOriginalPrimitiveFamily434 Q,
        (sourceOriginalActualPrimitiveGramEntry434 S mu h j Q
          c.val e.val / (nu:ℂ)) *
            c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
              ZMod (c.val.1.val+1))) -
          e.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
              ZMod (e.val.1.val+1))‖ ≤
        (Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ) *
          (((K/V)*L^(-B))/xi) := by
  obtain ⟨K,Y,hK,hGram⟩ :=
    source_original_actual_big_gram_power_unconditional434
      Cq gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro ι instF instD S mu hmu hmuPos h j Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    V hV hBand hWeight xi hxi hMass p e
  dsimp
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let nu : ℝ := sourceOriginalRealGramCellMass434 S mu h j
  let G : Fam → Fam → ℂ := fun c d =>
    sourceOriginalActualPrimitiveGramEntry434
      S mu h j Q c.val d.val / (nu:ℂ)
  let chi : Fam → ℂ := fun c =>
    c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
      ZMod (c.val.1.val+1))
  let eps : ℝ := ((K/V)*L^(-B))/xi
  have hnu : 0 < nu := hxi.trans_le hMass
  have hNu : (nu:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnu.ne'
  have hLnonneg : 0 ≤ L := by linarith
  have heps0 : 0 ≤ (K/V)*L^(-B) := by
    exact mul_nonneg (div_nonneg hK hV.le)
      (Real.rpow_nonneg hLnonneg _)
  have heps : 0 ≤ eps := div_nonneg heps0 hxi.le
  have hdiag (c : Fam) : G c c = 1 := by
    dsimp [G]
    rw [source_original_actual_primitive_gram_diagonal434
      S mu h j Q c.val hBIG]
    exact div_self hNu
  have hchi (c : Fam) : ‖chi c‖ ≤ 1 := by
    dsimp [chi]
    exact le_of_eq
      (source_original_primitive_actual_product_norm_one434
        S Q c.val hBIG p)
  have hoff (c dchar : Fam) (hne : c ≠ dchar) :
      ‖G c dchar‖ ≤ eps := by
    have hneVal : c.val ≠ dchar.val := by
      intro hEq
      exact hne (Subtype.ext hEq)
    have hRaw := hGram S mu hmu hmuPos h j Q
      c.val dchar.val c.property dchar.property hneVal i hBIG
      L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
      V hV hBand hWeight
    change ‖sourceOriginalActualPrimitiveGramEntry434 S mu h j Q
      c.val dchar.val / (nu:ℂ)‖ ≤ eps
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hnu]
    have hInv : nu⁻¹ ≤ xi⁻¹ :=
      (inv_le_inv₀ hnu hxi).2 hMass
    calc
      ‖sourceOriginalActualPrimitiveGramEntry434 S mu h j Q
        c.val dchar.val‖/nu ≤ ((K/V)*L^(-B))/nu :=
        div_le_div_of_nonneg_right hRaw hnu.le
      _ = ((K/V)*L^(-B))*nu⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ ((K/V)*L^(-B))*xi⁻¹ :=
        mul_le_mul_of_nonneg_left hInv heps0
      _ = eps := by simp only [eps,div_eq_mul_inv]
  change ‖(∑ c : Fam, G c e*chi c) - chi e‖ ≤
    (Fintype.card Fam:ℝ)*eps
  exact source_original_primitive_frame_reproduction_finite434
    G chi eps heps hdiag hoff hchi e
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalCharacterReproductionPower -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- ACTUAL physical source03 primitive-character reproduction
with ANY prescribed L^(-B), after absorbing BOTH true losses:
number of real primitive characters <= Q² and retention
probability xi >= L^(-Cxi). Retains the actual harmonic V >= Vmin,
the original indexed BIG band (u,v], and the global log-product
cell; valid pointwise in the entire labelled source tuple.
No new hypothesis on Siegel-Walfisz. -/
theorem source_original_actual_primitive_reproduction_power434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (j : ℤ) (Q : ℕ)
      (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
      (hv : (v:ℝ) ≤ Real.exp (L^d))
      (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
      (huBIG : Q^2 ≤ u)
      (hY : Y ≤ ((u+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (V : ℝ) (hV : Vmin ≤ V)
      (hBand : S i = sourceOriginalActualPrimeBand434 u v)
      (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
      (xi : ℝ) (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (hMass : xi ≤ sourceOriginalRealGramCellMass434 S mu h j)
      (p : SourceOriginalGramPrimeTuple434 S)
      (e : sourceOriginalPrimitiveFamily434 Q),
      let nu := sourceOriginalRealGramCellMass434 S mu h j
      ‖(∑ c : sourceOriginalPrimitiveFamily434 Q,
        (sourceOriginalActualPrimitiveGramEntry434 S mu h j Q
          c.val e.val / (nu:ℂ)) *
            c.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
              ZMod (c.val.1.val+1))) -
          e.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
              ZMod (e.val.1.val+1))‖ ≤ (K/Vmin)*L^(-B) := by
  let Bplus : ℝ := (B+(Cxi:ℝ))+((2*Cq:ℕ):ℝ)
  have hBplus : 0 < Bplus := by
    dsimp [Bplus]
    have hn1 : (0:ℝ) ≤ (Cxi:ℝ) := Nat.cast_nonneg _
    have hn2 : (0:ℝ) ≤ ((2*Cq:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨K,Y,hK,hRep⟩ :=
    source_original_actual_primitive_reproduction_unconditional434
      Cq gamma d Bplus hgamma hd hBplus
  refine ⟨K,Y,hK,?_⟩
  intro ι instF instD S mu hmu hmuPos h j Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    Vmin hVmin V hV hBand hWeight xi hxi hXi hMass p e
  dsimp
  have hVpos : 0 < V := hVmin.trans_le hV
  have hBound := hRep S mu hmu hmuPos h j Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    V hVpos hBand hWeight xi hxi hMass p e
  have hLoss :=
    source_original_normalized_prime_frame_loss_absorb434
      Q Cq Cxi L B K V Vmin xi hL hQ hK hVmin hV hxi hXi
  exact hBound.trans (by simpa only [Bplus] using hLoss)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalCharacterKernelPower -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The ORIGINAL physical single-GLOBAL source03 primitive kernel
reproduces the actual inducing primitive character at each
RETAINED physical target, with ARBITRARILY prescribed power
L^(-B). The real primitive family size Q^2 and cell-retention
loss xi^-1 are absorbed by larger, ALREADY PROVED, Siegel-Walfisz
precision. Original harmonic V>=Vmin, true moving BIG band
and labelled prime tuple are preserved. -/
theorem source_original_actual_kernel_character_power_unconditional434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
      (hmu : ∀ k, ∑ p ∈ S k, mu k p = 1)
      (hmuPos : ∀ k p, p ∈ S k → 0 ≤ mu k p)
      (h : ℝ) (j : ℤ) (Q : ℕ)
      (i : ι) (hBIG : ∀ k p, p ∈ S k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v)
      (hv : (v:ℝ) ≤ Real.exp (L^d))
      (huLarge : Real.exp (L^gamma) ≤ ((u+1:ℕ):ℝ))
      (huBIG : Q^2 ≤ u)
      (hY : Y ≤ ((u+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (V : ℝ) (hV : Vmin ≤ V)
      (hBand : S i = sourceOriginalActualPrimeBand434 u v)
      (hWeight : ∀ p, mu i p = (1/(p:ℝ))/V)
      (xi : ℝ) (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (hMass : xi ≤ sourceOriginalRealGramCellMass434 S mu h j)
      (p : SourceOriginalGramPrimeTuple434 S)
      (hp : sourceOriginalLiteralLogCell434 h j
              (sourceOriginalGramPrimeProduct434 S p))
      (e : sourceOriginalPrimitiveFamily434 Q),
      ‖(∑ q : SourceOriginalGramPrimeTuple434 S,
        (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
          sourceOriginalActualPrimitiveGlobalKernel434
            Q {j} h (sourceOriginalRealGramCellMass434 S mu h)
            (sourceOriginalGramPrimeProduct434 S q)
            (sourceOriginalGramPrimeProduct434 S p) *
          e.val.2 ((sourceOriginalGramPrimeProduct434 S q:ℕ):
            ZMod (e.val.1.val+1))) -
        e.val.2 ((sourceOriginalGramPrimeProduct434 S p:ℕ):
          ZMod (e.val.1.val+1))‖ ≤ (K/Vmin)*L^(-B) := by
  obtain ⟨K,Y,hK,hRep⟩ :=
    source_original_actual_primitive_reproduction_power434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro ι instF instD S mu hmu hmuPos h j Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    Vmin hVmin V hV hBand hWeight xi hxi hXi hMass p hp e
  rw [source_original_actual_character_kernel_gram_action434
    S mu h j Q p hp e]
  exact hRep S mu hmu hmuPos h j Q i hBIG
    L hL hLdyad hQ u v hu huv hv huLarge huBIG hY
    Vmin hVmin V hV hBand hWeight xi hxi hXi hMass p e
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalTwoGlobalFourierSaving -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- TWO genuine source03 GLOBAL primitive frames reproduce an
any finite rational-Fourier linear combination of 
primitive character products at arbitrary retained physical target tuples.
Both blocks have independent true harmonic prime laws, moving
log-product cells, actual source Q and genuine BIG prime bands.
The quantitative error has any chosen logarithmic saving, with
exact error (2eps+eps²) times the Fourier coefficient l1 mass.
This is the rational-character mode step, not yet an unconditional
comparison for arbitrary raw exponential test H(D_A,D_B). -/
theorem source_original_actual_two_global_fourier_span_unconditional434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
      (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
      (hmuA : ∀ k, ∑ p ∈ SA k, muA k p = 1)
      (hmuPosA : ∀ k p, p ∈ SA k → 0 ≤ muA k p)
      (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
      (hmuB : ∀ k, ∑ p ∈ SB k, muB k p = 1)
      (hmuPosB : ∀ k p, p ∈ SB k → 0 ≤ muB k p)
      (hA hB : ℝ) (jA jB : ℤ) (Q : ℕ)
      (iA : ιA) (hBIGA : ∀ k p, p ∈ SA k → p.Prime ∧ Q^2 < p)
      (iB : ιB) (hBIGB : ∀ k p, p ∈ SB k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (VA VB : ℝ) (hVA : Vmin ≤ VA) (hVB : Vmin ≤ VB)
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hWeightA : ∀ p, muA iA p = (1/(p:ℝ))/VA)
      (hWeightB : ∀ p, muB iB p = (1/(p:ℝ))/VB)
      (xi : ℝ) (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (hMassA : xi ≤ sourceOriginalRealGramCellMass434 SA muA hA jA)
      (hMassB : xi ≤ sourceOriginalRealGramCellMass434 SB muB hB jB)
      (pA : SourceOriginalGramPrimeTuple434 SA)
      (pB : SourceOriginalGramPrimeTuple434 SB)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
         (sourceOriginalGramPrimeProduct434 SA pA))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
         (sourceOriginalGramPrimeProduct434 SB pB))
      (a : sourceOriginalPrimitiveFamily434 Q → ℂ),
      let eps : ℝ := (K/Vmin)*L^(-B)
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
        (sourceOriginalActualPrimitiveGlobalKernel434
           Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
           (sourceOriginalGramPrimeProduct434 SA q.1)
           (sourceOriginalGramPrimeProduct434 SA pA) *
         sourceOriginalActualPrimitiveGlobalKernel434
           Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
           (sourceOriginalGramPrimeProduct434 SB q.2)
           (sourceOriginalGramPrimeProduct434 SB pB)) *
        (∑ e : sourceOriginalPrimitiveFamily434 Q,
          a e *
          (e.val.2 ((sourceOriginalGramPrimeProduct434 SA q.1:ℕ):
              ZMod (e.val.1.val+1)) *
           e.val.2 ((sourceOriginalGramPrimeProduct434 SB q.2:ℕ):
              ZMod (e.val.1.val+1))))) -
       (∑ e : sourceOriginalPrimitiveFamily434 Q,
         a e *
         (e.val.2 ((sourceOriginalGramPrimeProduct434 SA pA:ℕ):
             ZMod (e.val.1.val+1)) *
          e.val.2 ((sourceOriginalGramPrimeProduct434 SB pB:ℕ):
             ZMod (e.val.1.val+1))))‖ ≤
       (eps+eps+eps*eps) *
         (∑ e : sourceOriginalPrimitiveFamily434 Q, ‖a e‖) := by
  obtain ⟨K,Y,hK,hReproduce⟩ :=
    source_original_actual_kernel_character_power_unconditional434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro ιA ιB instFA instDA instFB instDB SA muA hmuA hmuPosA
    SB muB hmuB hmuPosB hA hB jA jB Q iA hBIGA iB hBIGB
    L hL hLdyad hQ uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB hWeightA hWeightB
    xi hxi hXi hMassA hMassB pA pB hCellA hCellB a
  dsimp
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let Fam := sourceOriginalPrimitiveFamily434 Q
  let wA : XA → ℝ := sourceOriginalGramPrimeMass434 SA muA
  let wB : XB → ℝ := sourceOriginalGramPrimeMass434 SB muB
  let KA : XA → XA → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
      (sourceOriginalGramPrimeProduct434 SA q)
      (sourceOriginalGramPrimeProduct434 SA p)
  let KB : XB → XB → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
      (sourceOriginalGramPrimeProduct434 SB q)
      (sourceOriginalGramPrimeProduct434 SB p)
  let chiA : XA → Fam → ℂ := fun q e =>
    e.val.2 ((sourceOriginalGramPrimeProduct434 SA q:ℕ):
      ZMod (e.val.1.val+1))
  let chiB : XB → Fam → ℂ := fun q e =>
    e.val.2 ((sourceOriginalGramPrimeProduct434 SB q:ℕ):
      ZMod (e.val.1.val+1))
  let eps : ℝ := (K/Vmin)*L^(-B)
  have heps : 0 ≤ eps := by
    dsimp [eps]
    exact mul_nonneg (div_nonneg hK hVmin.le)
      (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _)
  have hNormA (e : Fam) : ‖chiA pA e‖ ≤ 1 := by
    change ‖e.val.2 ((sourceOriginalGramPrimeProduct434 SA pA:ℕ):
      ZMod (e.val.1.val+1))‖ ≤ 1
    exact le_of_eq
      (source_original_primitive_actual_product_norm_one434
        SA Q e.val hBIGA pA)
  have hNormB (e : Fam) : ‖chiB pB e‖ ≤ 1 := by
    change ‖e.val.2 ((sourceOriginalGramPrimeProduct434 SB pB:ℕ):
      ZMod (e.val.1.val+1))‖ ≤ 1
    exact le_of_eq
      (source_original_primitive_actual_product_norm_one434
        SB Q e.val hBIGB pB)
  have hRepA (e : Fam) :
    ‖(∑ q : XA, (wA q:ℂ)*KA q pA*chiA q e) -
      chiA pA e‖ ≤ eps := by
    exact hReproduce SA muA hmuA hmuPosA hA jA Q iA hBIGA
      L hL hLdyad hQ uA vA huA huvA hvA huLargeA huBIGA hYA
      Vmin hVmin VA hVA hBandA hWeightA xi hxi hXi hMassA
      pA hCellA e
  have hRepB (e : Fam) :
    ‖(∑ q : XB, (wB q:ℂ)*KB q pB*chiB q e) -
      chiB pB e‖ ≤ eps := by
    exact hReproduce SB muB hmuB hmuPosB hB jB Q iB hBIGB
      L hL hLdyad hQ uB vB huB huvB hvB huLargeB huBIGB hYB
      Vmin hVmin VB hVB hBandB hWeightB xi hxi hXi hMassB
      pB hCellB e
  change
    ‖(∑ q : XA × XB,
      ((wA q.1:ℂ)*(wB q.2:ℂ)) *
        (KA q.1 pA*KB q.2 pB) *
        (∑ e : Fam, a e*(chiA q.1 e*chiB q.2 e))) -
      (∑ e : Fam, a e*(chiA pA e*chiB pB e))‖ ≤
    (eps+eps+eps*eps) * (∑ e : Fam, ‖a e‖)
  exact source_original_finite_two_global_fourier_span434
    wA wB KA KB chiA chiB pA pB eps eps
    heps heps hNormA hNormB hRepA hRepB a
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeActualFrameIdentification -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The ORIGINAL ν-dependent A/B GLOBAL cell probabilities from
the real pattern harness are definitionally the SAME probability
as the original physical primitive Gram diagonal on the marked
A/B auxiliary coordinates, respectively. They are not externally
chosen masses, and numerical repeated primes are preserved. -/
theorem source_original_probe_A_cell_probability_gram434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (h : ℝ) (j : ℤ) :
    sourceOriginalProbeCellA434 m P V ν h j =
    sourceOriginalRealGramCellMass434
      (fun z : ν.1 => P z.val.1)
      (fun z : ν.1 => sourcePrimeSharedAtom434 (V z.val.1)) h j := by
  exact source_original_true_cell_probability_eq_gram_mass434
    (fun z : ν.1 => P z.val.1)
    (fun z : ν.1 => sourcePrimeSharedAtom434 (V z.val.1)) h j

theorem source_original_probe_B_cell_probability_gram434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (h : ℝ) (j : ℤ) :
    sourceOriginalProbeCellB434 m P V ν h j =
    sourceOriginalRealGramCellMass434
      (fun z : ν.2 => P z.val.1)
      (fun z : ν.2 => sourcePrimeSharedAtom434 (V z.val.1)) h j := by
  exact source_original_true_cell_probability_eq_gram_mass434
    (fun z : ν.2 => P z.val.1)
    (fun z : ν.2 => sourcePrimeSharedAtom434 (V z.val.1)) h j
/-- TRUE original ν-indexed source03 signed comparison Knu,
with its exact D_A auxiliary product, target X_A product,
D_B auxiliary product, source X_B product, real canonical
active cell selections and real harmonic probabilities, is
EXACTLY a signed product of the two literal physical
primitive-character conditional frame kernels. The pattern
sign is exactly -(-1)^(|A|+|B|). This establishes the missing
physical-index identification; it is NOT yet the Hoeffding
cancellation of the RAW+comparison residual. -/
theorem source_original_probe_actual_two_global_frame_identity434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (hν : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (ha : ∀ z, a z ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z)
    (target source : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (ht : ∀ g i, target g i ∈ P g)
    (hs : ∀ g i, source g i ∈ P g)
    (Q : ℕ) (hA hB xi : ℝ) :
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalProbeDA434 m ν a)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
      (sourceOriginalProbeDB434 m ν a)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
      (ν.1.card+ν.2.card) =
    -((-1:ℂ)^(ν.1.card+ν.2.card)) *
      sourceOriginalPhysicalPrimitiveFrameKernel434
        (fun z : ν.1 => P z.val.1)
        (fun z : ν.1 => sourcePrimeSharedAtom434 (V z.val.1))
        hA (sourceOriginalProbeActiveCellsA434 m P V ν hA xi) Q
        (sourceOriginalProbeAuxAIntoGram434 m ν P a ha)
        (sourceOriginalProbeTargetAIntoGram434
          J ell m hmJ ν P target ht) *
      sourceOriginalPhysicalPrimitiveFrameKernel434
        (fun z : ν.2 => P z.val.1)
        (fun z : ν.2 => sourcePrimeSharedAtom434 (V z.val.1))
        hB (sourceOriginalProbeActiveCellsB434 m P V ν hB xi) Q
        (sourceOriginalProbeAuxBIntoGram434 m ν P a ha)
        (sourceOriginalProbeSourceBIntoGram434
          J ell m hmJ ν P source hs) := by
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let pA := sourceOriginalProbeAuxAIntoGram434 m ν P a ha
  let pB := sourceOriginalProbeAuxBIntoGram434 m ν P a ha
  let qA := sourceOriginalProbeTargetAIntoGram434
    J ell m hmJ ν P target ht
  let qB := sourceOriginalProbeSourceBIntoGram434
    J ell m hmJ ν P source hs
  have hA1 := source_original_probe_aux_A_gram_product434
    m ν P a ha
  have hB1 := source_original_probe_aux_B_gram_product434
    m ν P a ha
  have hXA := source_original_probe_target_A_gram_product434
    J ell m hmJ ν P target ht
  have hXB := source_original_probe_source_B_gram_product434
    J ell m hmJ ν P source hs
  have hMA : sourceOriginalProbeCellA434 m P V ν hA =
      sourceOriginalRealGramCellMass434 SA muA hA := by
    funext j
    exact source_original_probe_A_cell_probability_gram434
      m ν P V hA j
  have hMB : sourceOriginalProbeCellB434 m P V ν hB =
      sourceOriginalRealGramCellMass434 SB muB hB := by
    funext j
    exact source_original_probe_B_cell_probability_gram434
      m ν P V hB j
  have hK :=
    source_original_physical_two_global_Knu_identity434
      SA muA SB muB hA hB JA JB Q (ν.1.card+ν.2.card)
      pA qA pB qB
  simpa only [SA,SB,muA,muB,JA,JB,pA,qA,pB,qB,
    hA1,hB1,hXA,hXB,hMA,hMB] using hK
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeRationalUnits -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- A genuine source BIG prime p>Q² is invertible modulo EVERY
positive rational major-arc denominator q≤Q (not just a primitive
character's own conductor). This ensures rational Fourier
expansion is valid at the real source03 prime-products. -/
theorem source_original_big_prime_rational_unit434
    (Q q p : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (hp : p.Prime) (hpBIG : Q^2 < p) :
    IsUnit (p:ZMod q) := by
  have hQpos : 1 ≤ Q := by omega
  have hQsq : Q ≤ Q^2 := by
    calc
      Q = Q*1 := by omega
      _ ≤ Q*Q := Nat.mul_le_mul_left Q hQpos
      _ = Q^2 := by ring
  have hnot : ¬ p ∣ q := by
    intro hdiv
    have hpq := Nat.le_of_dvd hq hdiv
    omega
  exact (ZMod.isUnit_iff_coprime p q).mpr
    (hp.coprime_iff_not_dvd.mpr hnot)

/-- A true source BIG PRIME-LABELLED product, including possible
numerically repeated primes in different slots, is a unit
modulo every rational major-arc denominator q≤Q. -/
theorem source_original_physical_big_product_rational_unit434
    {ι : Type} [Fintype ι]
    (S : ι → Finset ℕ) (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (hBIG : ∀ i p, p ∈ S i → p.Prime ∧ Q^2 < p)
    (a : SourceOriginalGramPrimeTuple434 S) :
    IsUnit ((sourceOriginalGramPrimeProduct434 S a:ℕ):ZMod q) := by
  unfold sourceOriginalGramPrimeProduct434
  rw [Nat.cast_prod]
  apply IsUnit.prod_univ_iff.mpr
  intro i
  exact source_original_big_prime_rational_unit434
    Q q (a i).val hq hQ
      (hBIG i (a i).val (a i).property).1
      (hBIG i (a i).val (a i).property).2

/-- The ACTUAL source03 original comparison pattern ν has four
literal rational-unit products: auxiliary D_A,D_B and physical
target X_A/source X_B. These are the SAME products used in the
canonical signed Kν, not independent replacement integers.
The premise only requires BIG support for the selected ν slots. -/
theorem source_original_probe_four_rational_units434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (Q q : ℕ)
    (hq : 0 < q) (hQ : q ≤ Q)
    (hABig : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ Q^2 < p)
    (hBBig : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ Q^2 < p)
    (a : SourceOriginalProbeAuxIndex434 m ν → ℕ)
    (ha : ∀ z, a z ∈ sourceOriginalProbeAuxPrimeSets434 m ν P z)
    (target source : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (ht : ∀ g i, target g i ∈ P g)
    (hs : ∀ g i, source g i ∈ P g) :
    IsUnit ((sourceOriginalProbeDA434 m ν a:ℕ):ZMod q) ∧
    IsUnit ((sourceOriginalProbeDB434 m ν a:ℕ):ZMod q) ∧
    IsUnit ((sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target:ℕ):ZMod q) ∧
    IsUnit ((sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source:ℕ):ZMod q) := by
  have hDA :=
    source_original_physical_big_product_rational_unit434
      (fun z : ν.1 => P z.val.1) Q q hq hQ
      (fun z p hp => hABig z p hp)
      (sourceOriginalProbeAuxAIntoGram434 m ν P a ha)
  have hDB :=
    source_original_physical_big_product_rational_unit434
      (fun z : ν.2 => P z.val.1) Q q hq hQ
      (fun z p hp => hBBig z p hp)
      (sourceOriginalProbeAuxBIntoGram434 m ν P a ha)
  have hXA :=
    source_original_physical_big_product_rational_unit434
      (fun z : ν.1 => P z.val.1) Q q hq hQ
      (fun z p hp => hABig z p hp)
      (sourceOriginalProbeTargetAIntoGram434
        J ell m hmJ ν P target ht)
  have hXB :=
    source_original_physical_big_product_rational_unit434
      (fun z : ν.2 => P z.val.1) Q q hq hQ
      (fun z p hp => hBBig z p hp)
      (sourceOriginalProbeSourceBIntoGram434
        J ell m hmJ ν P source hs)
  rw [source_original_probe_aux_A_gram_product434] at hDA
  rw [source_original_probe_aux_B_gram_product434] at hDB
  rw [source_original_probe_target_A_gram_product434] at hXA
  rw [source_original_probe_source_B_gram_product434] at hXB
  exact ⟨hDA,hDB,hXA,hXB⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalPrimitiveIndex -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Every source Dirichlet character modulo a positive q≤Q,
primitive or not, has a genuine primitive inducing character
in the ORIGINAL all-conductor source03 primitive family. The
embedding uses the actual positive conductor and stores its
original modulus as the precise Fin Q level f=conductor-1. -/
noncomputable def sourceOriginalInducedPrimitiveIndex434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (χ : DirichletCharacter ℂ q) :
    sourceOriginalPrimitiveFamily434 Q := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hCondPos : 0 < χ.conductor :=
    Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hCondLe : χ.conductor ≤ Q :=
    (Nat.le_of_dvd hq χ.conductor_dvd_level).trans hQ
  let f : Fin Q := ⟨χ.conductor-1, by omega⟩
  have hf : f.val+1=χ.conductor := by
    dsimp [f]
    omega
  let χprim : DirichletCharacter ℂ (f.val+1) :=
    hf.symm ▸ χ.primitiveCharacter
  have htransport :
      ∀ {n k : ℕ} (h : n = k)
        (ψ : DirichletCharacter ℂ n),
        ψ.IsPrimitive → (h ▸ ψ).IsPrimitive := by
    intro n k hn ψ hp
    cases hn
    exact hp
  have hprim : χprim.IsPrimitive := by
    exact htransport hf.symm χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive
  let c : Σ t : Fin Q, DirichletCharacter ℂ (t.val+1) :=
    ⟨f,χprim⟩
  exact ⟨c,(source_original_actual_primitive_mem434 Q c).mpr hprim⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalPrimitiveEvaluation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Transport of a genuine finite-level Dirichlet character
does not change its value at any natural number, even when the
underlying ZMod types have definitionally different levels. -/
theorem source_original_dirichlet_level_transport_eval434
    {n k : ℕ} (h : n = k)
    (ψ : DirichletCharacter ℂ n) (a : ℕ) :
    (h ▸ ψ) (a : ZMod k) = ψ (a : ZMod n) := by
  cases h
  rfl

/-- An imprimitive rational Fourier character agrees at every
integer COPRIME to its original level with the actual indexed
source03 primitive inducing character of true conductor≤Q. -/
theorem source_original_induced_primitive_eval_nat434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (χ : DirichletCharacter ℂ q) (a : ℕ)
    (hcop : a.Coprime q) :
    (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ).val.2
       (a : ZMod
         ((sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ).val.1.val+1)) =
    χ (a : ZMod q) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let f : Fin Q := ⟨χ.conductor-1, by
    have hp : 0 < χ.conductor :=
      Nat.pos_of_ne_zero χ.conductor_ne_zero
    have hb : χ.conductor ≤ Q :=
      (Nat.le_of_dvd hq χ.conductor_dvd_level).trans hQ
    omega⟩
  have hf : χ.conductor = f.val+1 := by
    dsimp [f]
    have hp : 0 < χ.conductor :=
      Nat.pos_of_ne_zero χ.conductor_ne_zero
    omega
  have hindex :
      (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ).val.1 = f := by
    rfl
  have hchar :
      (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ).val.2 =
       (hf ▸ χ.primitiveCharacter) := by
    rfl
  have heval := source_original_dirichlet_level_transport_eval434
    hf χ.primitiveCharacter a
  have hcop' : IsCoprime (a:ℤ) q :=
    Nat.isCoprime_iff_coprime.mpr hcop
  have hprim := χ.primitiveCharacter_apply_of_isCoprime hcop'
  change (hf ▸ χ.primitiveCharacter) (a : ZMod (f.val+1)) =
    χ (a : ZMod q)
  exact heval.trans (by simpa only [Int.cast_natCast] using hprim)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalPrimitiveUnitEvaluation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Exact character evaluation on a genuine unit of ZMod q:
the unique original primitive inducing character from the source03
all-conductor family agrees with the FULL original q-level
character on this unit, retaining the canonical natural lift. -/
theorem source_original_induced_primitive_eval_unit434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (χ : DirichletCharacter ℂ q)
    (a : (ZMod q)ˣ) :
    (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ).val.2
      (((a:ZMod q).val:ℕ) : ZMod
        ((sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ).val.1.val+1)) =
    χ (a:ZMod q) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let n : ℕ := (a:ZMod q).val
  have hunit : IsUnit (n : ZMod q) := by
    rw [ZMod.natCast_zmod_val]
    exact Units.isUnit a
  have hcop : n.Coprime q :=
    (ZMod.isUnit_iff_coprime n q).mp hunit
  have hh := source_original_induced_primitive_eval_nat434
    Q q hq hQ χ n hcop
  simpa only [n,ZMod.natCast_zmod_val] using hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalPrimitiveFourier -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Genuine SOURCE03 primitive Fourier coefficient, obtained by
pushing the full q-level Dirichlet coefficients to the ACTUAL
primitive inducing characters with their ORIGINAL conductor.
Induction can be many-to-one: coefficients are SUMMED, not
incorrectly reindexed by a bijection. -/
noncomputable def sourceOriginalRationalPrimitiveFourierCoeff434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (F : (ZMod q)ˣ → ℂ)
    (c : sourceOriginalPrimitiveFamily434 Q) : ℂ := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact sourceOriginalFiniteFourierPushforward434
    (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
    (sourceOriginalRationalUnitFourierCoeff434 q F) c

/-- Unconditional original primitive Fourier coefficient l1
budget: for ANY unit bounded function on reduced residues,
the genuine all-conductor source03 primitive Fourier
coefficients have total absolute mass <= q.
No injectivity of induction and no additional
character-count or coefficient-norm hypothesis. -/
theorem source_original_rational_primitive_fourier_l1_bound434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (F : (ZMod q)ˣ → ℂ)
    (hF : ∀ a, ‖F a‖ ≤ 1) :
    (∑ c : sourceOriginalPrimitiveFamily434 Q,
       ‖sourceOriginalRationalPrimitiveFourierCoeff434
          Q q hq hQ F c‖) ≤ (q:ℝ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  change (∑ c : sourceOriginalPrimitiveFamily434 Q,
    ‖sourceOriginalFiniteFourierPushforward434
      (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
      (sourceOriginalRationalUnitFourierCoeff434 q F) c‖) ≤ (q:ℝ)
  exact (source_original_finite_fourier_pushforward_l1434
    (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
    (sourceOriginalRationalUnitFourierCoeff434 q F)).trans
    (source_original_rational_unit_fourier_l1_le_modulus434 q F hF)

/-- Exact ORIGINAL primitive Dirichlet Fourier inversion
on the reduced residues, using the TRUE source03 family
rather than the complete q-level character family. -/
theorem source_original_rational_primitive_fourier_inversion434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (F : (ZMod q)ˣ → ℂ)
    (a : (ZMod q)ˣ) :
    (∑ c : sourceOriginalPrimitiveFamily434 Q,
      sourceOriginalRationalPrimitiveFourierCoeff434 Q q hq hQ F c *
      c.val.2 (((a:ZMod q).val:ℕ):ZMod (c.val.1.val+1))) = F a := by
  letI : NeZero q := ⟨hq.ne'⟩
  let b : sourceOriginalPrimitiveFamily434 Q → ℂ := fun c =>
    c.val.2 (((a:ZMod q).val:ℕ):ZMod (c.val.1.val+1))
  have hPush := source_original_finite_fourier_pushforward_exact434
    (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
    (sourceOriginalRationalUnitFourierCoeff434 q F) b
  change (∑ c : sourceOriginalPrimitiveFamily434 Q,
    sourceOriginalFiniteFourierPushforward434
      (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
      (sourceOriginalRationalUnitFourierCoeff434 q F) c *
      b c) = F a
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
      sourceOriginalRationalUnitFourierCoeff434 q F χ *
        b (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ) := hPush
    _ = ∑ χ : DirichletCharacter ℂ q,
      sourceOriginalRationalUnitFourierCoeff434 q F χ *
        χ (a:ZMod q) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          exact congrArg
            (fun z : ℂ => sourceOriginalRationalUnitFourierCoeff434 q F χ*z)
            (source_original_induced_primitive_eval_unit434 Q q hq hQ χ a)
    _ = F a := source_original_rational_unit_fourier_inversion434 q F a
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalPrimitiveTwoBlock -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- EXACT rational (or any bounded reduced-residue) phase
decomposition in the ORIGINAL TWO GLOBAL primitive-character
blocks: F(a*b) = sum_{primitive c,cond<=Q} beta_c c(a)c(b).
The full modulo-q Fourier characters have been replaced by
their actual primitive inducing characters in source03, with
the correct NATURAL lifts of both genuine units and without
assuming an injective inducing-character map. The same beta
works for all pairs a,b, independent of their prime tuples. -/
theorem source_original_rational_primitive_two_block_inversion434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (F : (ZMod q)ˣ → ℂ)
    (a b : (ZMod q)ˣ) :
    (∑ c : sourceOriginalPrimitiveFamily434 Q,
      sourceOriginalRationalPrimitiveFourierCoeff434 Q q hq hQ F c *
        (c.val.2 (((a:ZMod q).val:ℕ):ZMod (c.val.1.val+1)) *
         c.val.2 (((b:ZMod q).val:ℕ):ZMod (c.val.1.val+1)))) =
      F (a*b) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let target : sourceOriginalPrimitiveFamily434 Q → ℂ := fun c =>
    c.val.2 (((a:ZMod q).val:ℕ):ZMod (c.val.1.val+1)) *
    c.val.2 (((b:ZMod q).val:ℕ):ZMod (c.val.1.val+1))
  have hPush := source_original_finite_fourier_pushforward_exact434
    (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
    (sourceOriginalRationalUnitFourierCoeff434 q F) target
  change (∑ c : sourceOriginalPrimitiveFamily434 Q,
    sourceOriginalFiniteFourierPushforward434
      (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
      (sourceOriginalRationalUnitFourierCoeff434 q F) c *
        target c) = F (a*b)
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
        sourceOriginalRationalUnitFourierCoeff434 q F χ *
          target (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ) :=
      hPush
    _ = ∑ χ : DirichletCharacter ℂ q,
        sourceOriginalRationalUnitFourierCoeff434 q F χ *
          (χ (a:ZMod q)*χ (b:ZMod q)) := by
            apply Finset.sum_congr rfl
            intro χ hχ
            have ha := source_original_induced_primitive_eval_unit434
              Q q hq hQ χ a
            have hb := source_original_induced_primitive_eval_unit434
              Q q hq hQ χ b
            have hpair :
                target (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ) =
                  χ (a:ZMod q)*χ (b:ZMod q) := by
              dsimp only [target]
              rw [ha,hb]
            exact congrArg
              (fun z : ℂ => sourceOriginalRationalUnitFourierCoeff434 q F χ*z)
              hpair
    _ = ∑ χ : DirichletCharacter ℂ q,
        sourceOriginalRationalUnitFourierCoeff434 q F χ *
          χ ((a*b):ZMod q) := by
            apply Finset.sum_congr rfl
            intro χ hχ
            congr 1
            simpa only [Units.val_mul] using
              (map_mul χ (a:ZMod q) (b:ZMod q)).symm
    _ = F (a*b) :=
       source_original_rational_unit_fourier_inversion434 q F (a*b)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The ACTUAL positive rational phase used in the source03
major-arc comparison: exp(2πi * r*a/q), defined intrinsically
on reduced residues through the standard additive character
of ZMod q. This is a concrete phase, not an arbitrary Fourier
function or a hypothesized character expansion. -/
noncomputable def sourceOriginalRationalUnitPhase434
    (q : ℕ) [NeZero q] (r : ℤ) (a : (ZMod q)ˣ) : ℂ :=
  ZMod.stdAddChar ((r:ZMod q)*(a:ZMod q))

/-- Exactly unit modulus at every reduced residue, uniformly
over numerator, denominator and the original positive rational
phase. -/
theorem source_original_rational_unit_phase_norm_one434
    (q : ℕ) [NeZero q] (r : ℤ) (a : (ZMod q)ˣ) :
    ‖sourceOriginalRationalUnitPhase434 q r a‖ = 1 := by
  rw [sourceOriginalRationalUnitPhase434, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The intrinsic ZMod additive character is literally
the usual 2πi-rational exponential on the representative
of the original unit residue. Thus Fourier inversion
below concerns the ACTUAL source03 rational phase. -/
theorem source_original_rational_unit_phase_exp434
    (q : ℕ) [NeZero q] (r : ℤ) (a : (ZMod q)ˣ) :
    sourceOriginalRationalUnitPhase434 q r a =
      Complex.exp (2 * Real.pi * Complex.I *
        (r * (((a:ZMod q).val:ℕ) : ℤ) : ℂ) / (q:ℂ)) := by
  calc
    _ = ZMod.stdAddChar
        ((r*(((a:ZMod q).val:ℕ):ℤ)):ZMod q) := by
          simp only [sourceOriginalRationalUnitPhase434,
            Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    _ = _ := by
      simpa only [Int.cast_mul, Int.cast_natCast] using
        (ZMod.stdAddChar_coe (N:=q)
          (r*(((a:ZMod q).val:ℕ):ℤ)))
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalPrimitiveNaturalProducts -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The exact primitive rational Fourier decomposition on ORIGINAL
natural products D_A and D_B, each coprime to the small source
denominator q. This is the arithmetic interface used for ACTUAL
products of independently labelled BIG primes, whose residues
are units by Q²<prime. There is no fictitious uniform residue
probability, no injection of imprimitive characters into the
primitive family, and no assumption on arbitrary output H. -/
theorem source_original_rational_primitive_two_natural_products434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (F : (ZMod q)ˣ → ℂ)
    (n m : ℕ) (hn : n.Coprime q) (hm : m.Coprime q) :
    let an : (ZMod q)ˣ :=
      ((ZMod.isUnit_iff_coprime n q).mpr hn).unit
    let am : (ZMod q)ˣ :=
      ((ZMod.isUnit_iff_coprime m q).mpr hm).unit
    (∑ c : sourceOriginalPrimitiveFamily434 Q,
      sourceOriginalRationalPrimitiveFourierCoeff434 Q q hq hQ F c *
        (c.val.2 (n:ZMod (c.val.1.val+1)) *
         c.val.2 (m:ZMod (c.val.1.val+1)))) =
      F (an*am) := by
  classical
  letI : NeZero q := ⟨hq.ne'⟩
  let an : (ZMod q)ˣ :=
    ((ZMod.isUnit_iff_coprime n q).mpr hn).unit
  let am : (ZMod q)ˣ :=
    ((ZMod.isUnit_iff_coprime m q).mpr hm).unit
  let mode : sourceOriginalPrimitiveFamily434 Q → ℂ := fun c =>
    c.val.2 (n:ZMod (c.val.1.val+1)) *
    c.val.2 (m:ZMod (c.val.1.val+1))
  have hPush := source_original_finite_fourier_pushforward_exact434
    (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
    (sourceOriginalRationalUnitFourierCoeff434 q F) mode
  have hnval : (an:ZMod q) = (n:ZMod q) :=
    ((ZMod.isUnit_iff_coprime n q).mpr hn).unit_spec
  have hmval : (am:ZMod q) = (m:ZMod q) :=
    ((ZMod.isUnit_iff_coprime m q).mpr hm).unit_spec
  change (∑ c : sourceOriginalPrimitiveFamily434 Q,
      sourceOriginalFiniteFourierPushforward434
        (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ)
        (sourceOriginalRationalUnitFourierCoeff434 q F) c *
        mode c) = F (an*am)
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
        sourceOriginalRationalUnitFourierCoeff434 q F χ *
          mode (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ) :=
      hPush
    _ = ∑ χ : DirichletCharacter ℂ q,
        sourceOriginalRationalUnitFourierCoeff434 q F χ *
          (χ (n:ZMod q) * χ (m:ZMod q)) := by
            apply Finset.sum_congr rfl
            intro χ hχ
            have hn' := source_original_induced_primitive_eval_nat434
              Q q hq hQ χ n hn
            have hm' := source_original_induced_primitive_eval_nat434
              Q q hq hQ χ m hm
            have hv : mode (sourceOriginalInducedPrimitiveIndex434 Q q hq hQ χ) =
                χ (n:ZMod q)*χ (m:ZMod q) := by
              dsimp only [mode]
              rw [hn',hm']
            exact congrArg
              (fun z : ℂ => sourceOriginalRationalUnitFourierCoeff434 q F χ*z) hv
    _ = ∑ χ : DirichletCharacter ℂ q,
        sourceOriginalRationalUnitFourierCoeff434 q F χ *
          χ ((an*am):ZMod q) := by
            apply Finset.sum_congr rfl
            intro χ hχ
            congr 1
            simpa only [hnval,hmval,Units.val_mul] using
              (map_mul χ (n:ZMod q) (m:ZMod q)).symm
    _ = F (an*am) :=
      source_original_rational_unit_fourier_inversion434 q F (an*am)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalNaturalPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Literal positive-denominator rational additive phase on the
TRUE original natural prime products, with the canonical ZMod
additive character. It is the physical multiplier
exp(2πi * u*n/q), not a proxy depending on an arbitrarily
selected residue representative. -/
noncomputable def sourceOriginalPositiveRationalPhaseAtNat434
    (q : ℕ) (hq : 0 < q) (u : ℤ) (n : ℕ) : ℂ := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact ZMod.stdAddChar ((u:ZMod q)*(n:ZMod q))

theorem source_original_positive_rational_phase_norm_one434
    (q : ℕ) (hq : 0 < q) (u : ℤ) (n : ℕ) :
    ‖sourceOriginalPositiveRationalPhaseAtNat434 q hq u n‖ = 1 := by
  letI : NeZero q := ⟨hq.ne'⟩
  change ‖ZMod.stdAddChar ((u:ZMod q)*(n:ZMod q))‖ = 1
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Actual arithmetic phase equals the standard source03
2πi-complex exponential at the ORIGINAL natural integer n. -/
theorem source_original_positive_rational_phase_exp434
    (q : ℕ) (hq : 0 < q) (u : ℤ) (n : ℕ) :
    sourceOriginalPositiveRationalPhaseAtNat434 q hq u n =
      Complex.exp (2 * Real.pi * Complex.I *
        (u*(n:ℤ):ℂ)/(q:ℂ)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    _ = ZMod.stdAddChar ((u*(n:ℤ):ℤ):ZMod q) := by
      simp only [sourceOriginalPositiveRationalPhaseAtNat434,
        Int.cast_mul, Int.cast_natCast]
    _ = _ := by
      simpa only [Int.cast_mul, Int.cast_natCast] using
        (ZMod.stdAddChar_coe (N:=q) (u*(n:ℤ)))

/-- No formal-unit placeholders remain: the actual source
rational phase e(u*D_A*D_B/q) on positive integer products is
EXACTLY the two-GLOBAL sum over genuine primitive Dirichlet
characters of conductor ≤Q, with Fourier coefficients independent
of D_A,D_B and no loss from noninjective primitive induction. -/
theorem source_original_rational_phase_two_natural_products434
    (Q q : ℕ) (hq : 0 < q) (hQ : q ≤ Q)
    (u : ℤ)
    (n m : ℕ) (hn : n.Coprime q) (hm : m.Coprime q) :
    let F : (ZMod q)ˣ → ℂ := by
      letI : NeZero q := ⟨hq.ne'⟩
      exact sourceOriginalRationalUnitPhase434 q u
    (∑ c : sourceOriginalPrimitiveFamily434 Q,
      sourceOriginalRationalPrimitiveFourierCoeff434 Q q hq hQ F c *
        (c.val.2 (n:ZMod (c.val.1.val+1)) *
         c.val.2 (m:ZMod (c.val.1.val+1)))) =
    sourceOriginalPositiveRationalPhaseAtNat434 q hq u (n*m) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let F : (ZMod q)ˣ → ℂ := sourceOriginalRationalUnitPhase434 q u
  let an : (ZMod q)ˣ := ((ZMod.isUnit_iff_coprime n q).mpr hn).unit
  let am : (ZMod q)ˣ := ((ZMod.isUnit_iff_coprime m q).mpr hm).unit
  have hnval : (an:ZMod q) = (n:ZMod q) :=
    ((ZMod.isUnit_iff_coprime n q).mpr hn).unit_spec
  have hmval : (am:ZMod q) = (m:ZMod q) :=
    ((ZMod.isUnit_iff_coprime m q).mpr hm).unit_spec
  have hInv := source_original_rational_primitive_two_natural_products434
    Q q hq hQ F n m hn hm
  change (∑ c : sourceOriginalPrimitiveFamily434 Q,
      sourceOriginalRationalPrimitiveFourierCoeff434 Q q hq hQ F c *
        (c.val.2 (n:ZMod (c.val.1.val+1)) *
         c.val.2 (m:ZMod (c.val.1.val+1)))) =
        sourceOriginalPositiveRationalPhaseAtNat434 q hq u (n*m)
  calc
    _ = F (an*am) := hInv
    _ = sourceOriginalPositiveRationalPhaseAtNat434 q hq u (n*m) := by
      change ZMod.stdAddChar
          ((u:ZMod q)*((an*am: (ZMod q)ˣ):ZMod q)) =
        ZMod.stdAddChar ((u:ZMod q)*((n*m:ℕ):ZMod q))
      rw [Units.val_mul,hnval,hmval,Nat.cast_mul]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFrequencyRationalPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- SOURCE03 true original integer Fourier phase is invariant under
INTEGER period shifts of its real frequency argument. This is
exactly the AddCircle(1) quotient relation, not an approximation. -/
theorem source_original_C6_integer_phase_integer_period434
    (theta : ℝ) (z n : ℤ) :
    Green64SourceC6.integerPhase (theta-(z:ℝ)) n =
      Green64SourceC6.integerPhase theta n := by
  rw [←source_fourier_integer_phase434 n (theta-(z:ℝ)),
      ←source_fourier_integer_phase434 n theta]
  rw [source_circle_integer_shift434 theta z]

/-- Genuine 2πi integer Fourier phase respects real additive
decomposition into rational center and irrational remainder.
No conjugation or k-sign is dropped. -/
theorem source_original_C6_integer_phase_real_add434
    (theta beta : ℝ) (n : ℤ) :
    Green64SourceC6.integerPhase (theta+beta) n =
      Green64SourceC6.integerPhase theta n *
        Green64SourceC6.integerPhase beta n := by
  unfold Green64SourceC6.integerPhase
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring
/-- On the TRUE natural prime product n, the C6 physical
integer Fourier phase e((u/q+beta)*n) factors into the
EXACT ZMod/q additive rational character e_q(u*n) and
the original real remainder e(beta*n).
This is NOT an artificial rational Fourier placeholder. -/
theorem source_original_C6_integer_phase_rational_remainder434
    (q : ℕ) (hq : 0 < q) (u : ℤ)
    (beta : ℝ) (n : ℕ) :
    Green64SourceC6.integerPhase
      ((u:ℝ)/(q:ℝ)+beta) (n:ℤ) =
    sourceOriginalPositiveRationalPhaseAtNat434 q hq u n *
      Green64SourceC6.integerPhase beta (n:ℤ) := by
  rw [source_original_C6_integer_phase_real_add434]
  rw [source_original_positive_rational_phase_exp434]
  unfold Green64SourceC6.integerPhase
  congr 2 <;> push_cast <;> ring

/-- The EXACT correct ORIGINAL source03 physical frequency
is -k*theta, NOT theta. If a true circle-arc real lift has
-k*theta=u/q+beta-Nshift with integer Nshift, then for
EVERY real physical natural product D the corresponding
signed Fourier phase equals the true standard rational
additive phase times the actual beta remainder.
The dropped integer period has been explicitly proved
harmless, rather than silently ignored. -/
theorem source_original_C6_integer_phase_from_frequency_lift434
    (theta beta : ℝ) (k u Nshift : ℤ)
    (q D : ℕ) (hq : 0 < q)
    (hLift : -(k:ℝ)*theta =
      (u:ℝ)/(q:ℝ)+beta-(Nshift:ℝ)) :
    Green64SourceC6.integerPhase
      (-(k:ℝ)*theta) (D:ℤ) =
    sourceOriginalPositiveRationalPhaseAtNat434
      q hq u D *
    Green64SourceC6.integerPhase beta (D:ℤ) := by
  rw [hLift]
  rw [source_original_C6_integer_phase_integer_period434]
  exact source_original_C6_integer_phase_rational_remainder434
    q hq u beta D
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFrequencyRationalSlowPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Exact source03 ORIGINAL slowly varying Mellin/irrational
additive phase M(n)=exp(i*(ζ log n + 2π β n))
is literally the Mellin factor times the genuine
C6 integer Fourier phase at irrational remainder beta.
This keeps the original positive integer n and never
substitutes a generic product proxy. -/
theorem source_original_true_slow_phase_beta_factor434
    (ζ beta : ℝ) (n : ℕ) :
    sourceOriginalSlowMellinAdditivePhase434 ζ beta n =
      Complex.exp (Complex.I *
        ((ζ*Real.log (n:ℝ)):ℂ)) *
      Green64SourceC6.integerPhase beta (n:ℤ) := by
  unfold sourceOriginalSlowMellinAdditivePhase434
    Green64SourceC6.integerPhase
  rw [←Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

/-- Exact physical SOURCE03 Fourier-to-major comparison phase,
including TRUE -k*theta, integer-circle lift, TRUE rational
ZMod additive phase u/q, and the ORIGINAL Mellin twist.
No e-sign, 2π, k-factor, integer period, or prime product
is dropped. This bridges the literal SOURCE03 signed major
comparison phase to its original Fourier phase. -/
theorem source_original_true_integer_mellin_dirichlet_phase434
    (theta beta ζ : ℝ) (k u Nshift : ℤ)
    (q n : ℕ) (hq : 0 < q)
    (hLift : -(k:ℝ)*theta =
      (u:ℝ)/(q:ℝ)+beta-(Nshift:ℝ)) :
    Green64SourceC6.integerPhase
      (-(k:ℝ)*theta) (n:ℤ) *
      Complex.exp (Complex.I *
        ((ζ*Real.log (n:ℝ)):ℂ)) =
    sourceOriginalPositiveRationalPhaseAtNat434
      q hq u n *
    sourceOriginalSlowMellinAdditivePhase434 ζ beta n := by
  rw [source_original_C6_integer_phase_from_frequency_lift434
    theta beta k u Nshift q n hq hLift]
  rw [source_original_true_slow_phase_beta_factor434]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueReducedFourierPhase -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- In the TRUE original SOURCE03 -k*theta Fourier phase,
the rational numerator obtained from a circle arc can share
a factor with its denominator when k≠1. Reduce that
rational center before invoking C196's coprime Dirichlet
bilinear estimate. The denominator NEVER grows, the
real phase remains EXACT, and integer-circle periodicity
has already been accounted for. -/
theorem source_original_true_reduced_integer_frequency_phase434
    (theta beta : ℝ) (k u Nshift : ℤ)
    (q D : ℕ) (hq : 0 < q)
    (hLift : -(k:ℝ)*theta =
      (u:ℝ)/(q:ℝ) + beta - (Nshift:ℝ)) :
    ∃ q' : ℕ, ∃ hq' : 0 < q', ∃ u' : ℤ,
      q' ≤ q ∧ Nat.Coprime u'.natAbs q' ∧
        (u':ℝ)/(q':ℝ) = (u:ℝ)/(q:ℝ) ∧
        Green64SourceC6.integerPhase
          (-(k:ℝ)*theta) (D:ℤ) =
        sourceOriginalPositiveRationalPhaseAtNat434
          q' hq' u' D *
        Green64SourceC6.integerPhase beta (D:ℤ) := by
  obtain ⟨q',hq',hqBound,u',hCoprime,hSame⟩ :=
    source_original_true_rational_center_reduce434 q hq u
  have hLift' : -(k:ℝ)*theta =
      (u':ℝ)/(q':ℝ)+beta-(Nshift:ℝ) := by
    rw [hSame]
    exact hLift
  exact ⟨q',hq',u',hqBound,hCoprime,hSame,
    source_original_C6_integer_phase_from_frequency_lift434
      theta beta k u' Nshift q' D hq' hLift'⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalRationalComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- The full ACTUAL physical two-GLOBAL primitive-character kernel
reproduces the SOURCE03 RATIONAL PHASE, not merely arbitrary
character modes, with a power-saving quantitative error. The
input products are the real independently labelled BIG prime
products with their true harmonic weights; BOTH target products
are in their genuine retained product-log cells.
The RATIONAL denominator r is positive and ≤Q. Both source
products and target products are proven units; the rational
Fourier coefficient sum ≤ r is obtained UNCONDITIONALLY and
absorbed as an explicit factor. All SW savings were proved
in the SAME Lean 4.34.1 kernel.
This theorem is the MAJOR-RATIONAL slice only; it does NOT
include real beta log perturbations, minor arcs, or Hoeffding
and B transference. -/
theorem source_original_two_global_rational_phase_comparison_unconditional434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
      (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
      (hmuA : ∀ k, ∑ p ∈ SA k, muA k p = 1)
      (hmuPosA : ∀ k p, p ∈ SA k → 0 ≤ muA k p)
      (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
      (hmuB : ∀ k, ∑ p ∈ SB k, muB k p = 1)
      (hmuPosB : ∀ k p, p ∈ SB k → 0 ≤ muB k p)
      (hA hB : ℝ) (jA jB : ℤ) (Q : ℕ)
      (iA : ιA) (hBIGA : ∀ k p, p ∈ SA k → p.Prime ∧ Q^2 < p)
      (iB : ιB) (hBIGB : ∀ k p, p ∈ SB k → p.Prime ∧ Q^2 < p)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (VA VB : ℝ) (hVA : Vmin ≤ VA) (hVB : Vmin ≤ VB)
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hWeightA : ∀ p, muA iA p = (1/(p:ℝ))/VA)
      (hWeightB : ∀ p, muB iB p = (1/(p:ℝ))/VB)
      (xi : ℝ) (hxi : 0 < xi) (hXi : xi⁻¹ ≤ L^Cxi)
      (hMassA : xi ≤ sourceOriginalRealGramCellMass434 SA muA hA jA)
      (hMassB : xi ≤ sourceOriginalRealGramCellMass434 SB muB hB jB)
      (pA : SourceOriginalGramPrimeTuple434 SA)
      (pB : SourceOriginalGramPrimeTuple434 SB)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
         (sourceOriginalGramPrimeProduct434 SA pA))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
         (sourceOriginalGramPrimeProduct434 SB pB))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ),
      let eps : ℝ := (K/Vmin)*L^(-B)
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
        (sourceOriginalActualPrimitiveGlobalKernel434
           Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
           (sourceOriginalGramPrimeProduct434 SA q.1)
           (sourceOriginalGramPrimeProduct434 SA pA) *
         sourceOriginalActualPrimitiveGlobalKernel434
           Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
           (sourceOriginalGramPrimeProduct434 SB q.2)
           (sourceOriginalGramPrimeProduct434 SB pB)) *
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2)) -
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA pA *
            sourceOriginalGramPrimeProduct434 SB pB)‖ ≤
        (eps+eps+eps*eps)*(r:ℝ) := by
  obtain ⟨K,Y,hK,hSpan⟩ :=
    source_original_actual_two_global_fourier_span_unconditional434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro ιA ιB instFA instDA instFB instDB SA muA hmuA hmuPosA
    SB muB hmuB hmuPosB hA hB jA jB Q iA hBIGA iB hBIGB
    L hL hLdyad hQ uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB hWeightA hWeightB
    xi hxi hXi hMassA hMassB pA pB hCellA hCellB r hr hrQ u
  dsimp
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let Fam := sourceOriginalPrimitiveFamily434 Q
  letI : NeZero r := ⟨hr.ne'⟩
  let F : (ZMod r)ˣ → ℂ := sourceOriginalRationalUnitPhase434 r u
  let a : Fam → ℂ := sourceOriginalRationalPrimitiveFourierCoeff434
    Q r hr hrQ F
  let eps : ℝ := (K/Vmin)*L^(-B)
  have heps : 0 ≤ eps := by
    dsimp [eps]
    exact mul_nonneg (div_nonneg hK hVmin.le)
      (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ L) _)
  have hL1 : (∑ e : Fam, ‖a e‖) ≤ (r:ℝ) := by
    exact source_original_rational_primitive_fourier_l1_bound434
      Q r hr hrQ F
      (fun t => le_of_eq (source_original_rational_unit_phase_norm_one434 r u t))
  have hCoprimeA (p : XA) :
      (sourceOriginalGramPrimeProduct434 SA p).Coprime r := by
    exact (ZMod.isUnit_iff_coprime _ r).mp
      (source_original_physical_big_product_rational_unit434
        SA Q r hr hrQ hBIGA p)
  have hCoprimeB (p : XB) :
      (sourceOriginalGramPrimeProduct434 SB p).Coprime r := by
    exact (ZMod.isUnit_iff_coprime _ r).mp
      (source_original_physical_big_product_rational_unit434
        SB Q r hr hrQ hBIGB p)
  have hFourier (qA : XA) (qB : XB) :
      (∑ e : Fam, a e *
        (e.val.2 ((sourceOriginalGramPrimeProduct434 SA qA:ℕ):
          ZMod (e.val.1.val+1)) *
         e.val.2 ((sourceOriginalGramPrimeProduct434 SB qB:ℕ):
          ZMod (e.val.1.val+1)))) =
      sourceOriginalPositiveRationalPhaseAtNat434 r hr u
        (sourceOriginalGramPrimeProduct434 SA qA *
         sourceOriginalGramPrimeProduct434 SB qB) := by
    exact source_original_rational_phase_two_natural_products434
      Q r hr hrQ u
      (sourceOriginalGramPrimeProduct434 SA qA)
      (sourceOriginalGramPrimeProduct434 SB qB)
      (hCoprimeA qA) (hCoprimeB qB)
  have hSpanError := hSpan SA muA hmuA hmuPosA SB muB hmuB hmuPosB
    hA hB jA jB Q iA hBIGA iB hBIGB
    L hL hLdyad hQ uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB hWeightA hWeightB
    xi hxi hXi hMassA hMassB pA pB hCellA hCellB a
  let wA : XA → ℝ := sourceOriginalGramPrimeMass434 SA muA
  let wB : XB → ℝ := sourceOriginalGramPrimeMass434 SB muB
  let KA : XA → XA → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
      (sourceOriginalGramPrimeProduct434 SA q)
      (sourceOriginalGramPrimeProduct434 SA p)
  let KB : XB → XB → ℂ := fun q p =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
      (sourceOriginalGramPrimeProduct434 SB q)
      (sourceOriginalGramPrimeProduct434 SB p)
  let phase : XA × XB → ℂ := fun q =>
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA q.1 *
       sourceOriginalGramPrimeProduct434 SB q.2)
  let spanMode : XA × XB → ℂ := fun q =>
    ∑ e : Fam, a e *
      (e.val.2 ((sourceOriginalGramPrimeProduct434 SA q.1:ℕ):
        ZMod (e.val.1.val+1)) *
       e.val.2 ((sourceOriginalGramPrimeProduct434 SB q.2:ℕ):
        ZMod (e.val.1.val+1)))
  have hEvery (q : XA × XB) : spanMode q = phase q :=
    hFourier q.1 q.2
  have hError :
      ‖(∑ q : XA × XB,
         ((wA q.1:ℂ)*(wB q.2:ℂ)) *
           (KA q.1 pA*KB q.2 pB)*spanMode q) -
         spanMode (pA,pB)‖ ≤
      (eps+eps+eps*eps)*(∑ e : Fam, ‖a e‖) := by
    simpa only [XA,XB,Fam,wA,wB,KA,KB,spanMode,eps]
      using hSpanError
  have hOrig :
      ‖(∑ q : XA × XB,
         ((wA q.1:ℂ)*(wB q.2:ℂ)) *
           (KA q.1 pA*KB q.2 pB)*phase q) -
         phase (pA,pB)‖ ≤
      (eps+eps+eps*eps)*(∑ e : Fam, ‖a e‖) := by
    simpa only [← hEvery] using hError
  have hfac : 0 ≤ (eps+eps+eps*eps) := by
    nlinarith [mul_nonneg heps heps]
  change ‖(∑ q : XA × XB,
    ((wA q.1:ℂ)*(wB q.2:ℂ)) *
      (KA q.1 pA*KB q.2 pB)*phase q) -
     phase (pA,pB)‖ ≤ (eps+eps+eps*eps)*(r:ℝ)
  exact hOrig.trans (mul_le_mul_of_nonneg_left hL1 hfac)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeCanonicalHarmonicLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The TWO ν-dependent BIG probe spaces in the ORIGINAL source03
have actual NORMALIZED nonnegative harmonic product prime laws.
Unlike C118's abstract hmu and hmuPos fields, these facts follow
from the source physical input V_g = Σ_{p in P_g}1/p, the
source uniform Vmin lower bound and source prime support.
Numerical repetitions across labelled slots are permitted. -/
theorem source_original_probe_canonical_two_harmonic_laws434
    {G : Type} [DecidableEq G] (m : ℕ)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hMass : ∀ g, Vmin ≤ V g)
    (Q : ℕ)
    (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ Q^2 < p)
    (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ Q^2 < p) :
    (∀ z : ν.1,
      ∑ p ∈ P z.val.1, sourcePrimeSharedAtom434 (V z.val.1) p = 1) ∧
    (∀ z : ν.2,
      ∑ p ∈ P z.val.1, sourcePrimeSharedAtom434 (V z.val.1) p = 1) ∧
    (∀ z : ν.1, ∀ p ∈ P z.val.1,
      0 ≤ sourcePrimeSharedAtom434 (V z.val.1) p) ∧
    (∀ z : ν.2, ∀ p ∈ P z.val.1,
      0 ≤ sourcePrimeSharedAtom434 (V z.val.1) p) := by
  have hNorm (g : G) :
      ∑ p ∈ P g, sourcePrimeSharedAtom434 (V g) p = 1 := by
    exact source_prime_shared_atom_total434 (P g) (V g)
      (hV g) ((hVmin.trans_le (hMass g)).ne')
  have hPos (g : G) (p : ℕ) (hp : p.Prime) :
      0 ≤ sourcePrimeSharedAtom434 (V g) p := by
    have hVg : 0 < V g := hVmin.trans_le (hMass g)
    have hpg : (0:ℝ) < (p:ℝ) := by
      exact_mod_cast hp.pos
    unfold sourcePrimeSharedAtom434
    positivity
  refine ⟨(fun z => hNorm z.val.1),
    (fun z => hNorm z.val.1), ?_, ?_⟩
  · intro z p hp
    exact hPos z.val.1 p (hBIGA z p hp).1
  · intro z p hp
    exact hPos z.val.1 p (hBIGB z p hp).1
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeCanonicalMajorRational -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- ACTUAL source03 ν-INDEXED major-rational comparison with the
real primitive-character kernel on genuine independently labelled
BIG prime product distributions, for physical target X_A and
source X_B with THEIR ORIGINAL J+ell slot locations.
This is not an arbitrary abstract S_i, mu_i frame: the laws,
active log cells, both physical target products, positive
probabilities and vmin are instantiated by the source03 data.
Explicitly retain the load-bearing prime-INTERVAL geometry
per selected BIG group: the original SourceComparisonData only
guarantees prime support, not interval structure, so this
hypothesis is not silently invented. The signed Kν pattern
will be integrated after this major-phase estimate. -/
theorem source_original_probe_actual_major_rational_unconditional434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (jA jB : ℤ)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434
        m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434
        m P V ν hB xi)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (target source : ∀ g,
        Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
      (ht : ∀ g i, target g i ∈ P g)
      (hs : ∀ g i, source g i ∈ P g)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ),
      let SA : ν.1 → Finset ℕ := fun z => P z.val.1
      let SB : ν.2 → Finset ℕ := fun z => P z.val.1
      let muA : ν.1 → ℕ → ℝ :=
        fun z => sourcePrimeSharedAtom434 (V z.val.1)
      let muB : ν.2 → ℕ → ℝ :=
        fun z => sourcePrimeSharedAtom434 (V z.val.1)
      let pA := sourceOriginalProbeTargetAIntoGram434
        J ell m hmJ ν P target ht
      let pB := sourceOriginalProbeSourceBIntoGram434
        J ell m hmJ ν P source hs
      let eps : ℝ := (K/Vmin)*L^(-B)
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
        (sourceOriginalActualPrimitiveGlobalKernel434
           Q {jA} hA (sourceOriginalProbeCellA434 m P V ν hA)
           (sourceOriginalGramPrimeProduct434 SA q.1)
           (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target) *
         sourceOriginalActualPrimitiveGlobalKernel434
           Q {jB} hB (sourceOriginalProbeCellB434 m P V ν hB)
           (sourceOriginalGramPrimeProduct434 SB q.2)
           (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)) *
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2)) -
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
            sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)‖ ≤
        (eps+eps+eps*eps)*(r:ℝ) := by
  obtain ⟨K,Y,hK,hMajor⟩ :=
    source_original_two_global_rational_phase_comparison_unconditional434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G _ J ell m hmJ ν P V hV Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB L hL hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    target source ht hs hCellA hCellB r hr hrQ u
  dsimp
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let pA := sourceOriginalProbeTargetAIntoGram434
    J ell m hmJ ν P target ht
  let pB := sourceOriginalProbeSourceBIntoGram434
    J ell m hmJ ν P source hs
  let eps : ℝ := (K/Vmin)*L^(-B)
  obtain ⟨hmuA,hmuB,hPosA,hPosB⟩ :=
    source_original_probe_canonical_two_harmonic_laws434
      m ν P V Vmin hVmin hV hMass Q hBIGA hBIGB
  have hBIGAP : ∀ z : ν.1, ∀ p ∈ SA z,
      p.Prime ∧ Q^2 < p := by
    intro z p hp
    exact hBIGA z p hp
  have hBIGBP : ∀ z : ν.2, ∀ p ∈ SB z,
      p.Prime ∧ Q^2 < p := by
    intro z p hp
    exact hBIGB z p hp
  have hCellMassA : xi ≤
      sourceOriginalRealGramCellMass434 SA muA hA jA := by
    rw [← source_original_probe_A_cell_probability_gram434
      m ν P V hA jA]
    exact (source_original_probe_active_cell_A_mem_iff434
      m P V ν hA xi hhA hxi jA).mp hjA
  have hCellMassB : xi ≤
      sourceOriginalRealGramCellMass434 SB muB hB jB := by
    rw [← source_original_probe_B_cell_probability_gram434
      m ν P V hB jB]
    exact (source_original_probe_active_cell_B_mem_iff434
      m P V ν hB xi hhB hxi jB).mp hjB
  have hPositiveVA : 0 < V iA.val.1 :=
    hVmin.trans_le (hMass iA.val.1)
  have hPositiveVB : 0 < V iB.val.1 :=
    hVmin.trans_le (hMass iB.val.1)
  have hWeightA (p : ℕ) :
      muA iA p = (1/(p:ℝ))/(V iA.val.1) := by
    dsimp [muA,sourcePrimeSharedAtom434]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hWeightB (p : ℕ) :
      muB iB p = (1/(p:ℝ))/(V iB.val.1) := by
    dsimp [muB,sourcePrimeSharedAtom434]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hBandAP : SA iA = sourceOriginalActualPrimeBand434 uA vA :=
    hBandA
  have hBandBP : SB iB = sourceOriginalActualPrimeBand434 uB vB :=
    hBandB
  have hPA : sourceOriginalGramPrimeProduct434 SA pA =
      sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target :=
    source_original_probe_target_A_gram_product434
      J ell m hmJ ν P target ht
  have hPB : sourceOriginalGramPrimeProduct434 SB pB =
      sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source :=
    source_original_probe_source_B_gram_product434
      J ell m hmJ ν P source hs
  have hCP_A : sourceOriginalLiteralLogCell434 hA jA
      (sourceOriginalGramPrimeProduct434 SA pA) := by
    rw [hPA]
    exact hCellA
  have hCP_B : sourceOriginalLiteralLogCell434 hB jB
      (sourceOriginalGramPrimeProduct434 SB pB) := by
    rw [hPB]
    exact hCellB
  have hMajorInst := hMajor SA muA hmuA hPosA SB muB hmuB hPosB
    hA hB jA jB Q iA hBIGAP iB hBIGBP
    L hL hLdyad hQ uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin (V iA.val.1) (V iB.val.1)
    (hMass iA.val.1) (hMass iB.val.1)
    hBandAP hBandBP hWeightA hWeightB
    xi hxi hXi hCellMassA hCellMassB pA pB hCP_A hCP_B
    r hr hrQ u
  have hMA :
      sourceOriginalProbeCellA434 m P V ν hA =
      sourceOriginalRealGramCellMass434 SA muA hA := by
    funext j
    exact source_original_probe_A_cell_probability_gram434
      m ν P V hA j
  have hMB :
      sourceOriginalProbeCellB434 m P V ν hB =
      sourceOriginalRealGramCellMass434 SB muB hB := by
    funext j
    exact source_original_probe_B_cell_probability_gram434
      m ν P V hB j
  simpa only [SA,SB,muA,muB,pA,pB,eps,hMA,hMB,hPA,hPB]
    using hMajorInst
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeComparisonLaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- All source03 coordinate probability-law obligations for a true
selected A or B pattern fibre follow from the ORIGINAL group
harmonic normalizers and genuine BIG support. There is NO
independence hypothesis on the source test, no proxy probability
distribution, and no extra normalized-prime law assumption. -/
theorem source_original_probe_actual_coordinate_law434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (V : ι → ℝ)
    (hV : ∀ i, V i = ∑ p ∈ S i, 1/(p:ℝ))
    (hVp : ∀ i, 0 < V i)
    (Q : ℕ)
    (hBIG : ∀ i p, p ∈ S i → p.Prime ∧ Q^2 < p) :
    (∀ i, ∑ p ∈ S i, sourcePrimeSharedAtom434 (V i) p = 1) ∧
    (∀ i p, p ∈ S i → 0 ≤ sourcePrimeSharedAtom434 (V i) p) ∧
    (∀ i p, p ∈ S i → p.Prime ∧ Q^2 < p) ∧
    (∀ i p, sourcePrimeSharedAtom434 (V i) p =
        (1/(p:ℝ))/(V i)) := by
  refine ⟨?_,?_,hBIG,?_⟩
  · intro i
    exact source_prime_shared_atom_total434 (S i) (V i)
      (hV i) (hVp i).ne'
  · intro i p hp
    unfold sourcePrimeSharedAtom434
    have hv := hVp i
    have hpp : 0 < (p:ℝ) := by
      exact_mod_cast (hBIG i p hp).1.pos
    positivity
  · intro i p
    unfold sourcePrimeSharedAtom434
    simp only [one_div, mul_inv_rev, div_eq_mul_inv]
    ring
/-- NO external retained-cell mass hypothesis at the A pattern
GLOBAL level: true original active log-product cell j has
mass >=xi in the precise physical primitive Gram probability. -/
theorem source_original_probe_A_retained_gram_mass434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi)
    (j : ℤ)
    (hj : j ∈ sourceOriginalProbeActiveCellsA434 m P V ν h xi) :
    xi ≤ sourceOriginalRealGramCellMass434
       (fun z : ν.1 => P z.val.1)
       (fun z : ν.1 => sourcePrimeSharedAtom434 (V z.val.1)) h j := by
  rw [← source_original_probe_A_cell_probability_gram434
    m ν P V h j]
  exact (source_original_probe_active_cell_A_mem_iff434
    m P V ν h xi hh hxi j).mp hj

/-- Same EXACT retained original physical GLOBAL-cell probability
for the independently freed B marked prime slots. -/
theorem source_original_probe_B_retained_gram_mass434
    {G : Type} [DecidableEq G]
    (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi)
    (j : ℤ)
    (hj : j ∈ sourceOriginalProbeActiveCellsB434 m P V ν h xi) :
    xi ≤ sourceOriginalRealGramCellMass434
       (fun z : ν.2 => P z.val.1)
       (fun z : ν.2 => sourcePrimeSharedAtom434 (V z.val.1)) h j := by
  rw [← source_original_probe_B_cell_probability_gram434
    m ν P V h j]
  exact (source_original_probe_active_cell_B_mem_iff434
    m P V ν h xi hh hxi j).mp hj
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActiveSingletonKernel -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The ORIGINAL full canonical GLOBAL character kernel, evaluated
at any fixed physical target X in its retained cell j, equals
the SINGLE j-character kernel for EVERY source product D.
This is true for a nonempty or empty source cell, includes ALL
actual primitive conductors, and removes the otherwise dangerous
factor equal to the number of GLOBAL log cells. No analytic
estimate or nonzero denominator is invoked. -/
theorem source_original_actual_active_kernel_collapse434
    (Q : ℕ) (active : Finset ℤ) (h : ℝ)
    (hh : 0 < h) (mass : ℤ → ℝ)
    (j : ℤ) (hj : j ∈ active)
    (D X : ℕ)
    (hX : sourceOriginalLiteralLogCell434 h j X) :
    sourceOriginalActualPrimitiveGlobalKernel434 Q active h mass D X =
    sourceOriginalActualPrimitiveGlobalKernel434 Q {j} h mass D X := by
  classical
  unfold sourceOriginalActualPrimitiveGlobalKernel434
    sourceOriginalCharacterCellKernel434
  rw [Finset.sum_singleton]
  let f : ℤ → ℂ := fun k =>
    if sourceOriginalLiteralLogCell434 h k D ∧
       sourceOriginalLiteralLogCell434 h k X then
         ((mass k:ℂ)⁻¹) *
           ∑ c ∈ sourceOriginalActualPrimitiveCharacters434 Q,
             star (c.2 (D:ZMod (c.1.val+1))) *
               c.2 (X:ZMod (c.1.val+1))
    else 0
  change (∑ k ∈ active, f k) = f j
  rw [Finset.sum_eq_single j]
  · intro k hk hne
    have hknot : ¬sourceOriginalLiteralLogCell434 h k X := by
      intro hx
      exact hne (source_original_literal_log_cells_unique434
        h hh X k j hx hX)
    simp [f,hknot]
  · intro hnot
    exact (hnot hj).elim
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeActiveSignedSingleton -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- EXACT original full-active-GLObAL-cell signed physical
comparison kernel reduces to the unique retained A and B
cells of the true target X_A and source X_B, independently
for EVERY auxiliary product D_A,D_B. No cell-count factor,
no normalized-character approximation and no detached
product or pattern-sign proxy. This supplies the FULL-active
to SINGLE-cell bridge missing from C118/C120. -/
theorem source_original_probe_full_active_signed_singleton434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (jA jB : ℤ)
    (hjA : jA ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
    (hjB : jB ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
    (DA DB : ℕ)
    (target source : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
    (hXA : sourceOriginalLiteralLogCell434 hA jA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target))
    (hXB : sourceOriginalLiteralLogCell434 hB jB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)) :
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      DA (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
      DB (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
      (ν.1.card+ν.2.card) =
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      {jA} {jB} hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      DA (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
      DB (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
      (ν.1.card+ν.2.card) := by
  unfold sourceOriginalActualPrimitiveComparisonKernel434
  rw [
    source_original_actual_active_kernel_collapse434
      Q (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      hA hhA (sourceOriginalProbeCellA434 m P V ν hA)
      jA hjA DA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
      hXA,
    source_original_actual_active_kernel_collapse434
      Q (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hB hhB (sourceOriginalProbeCellB434 m P V ν hB)
      jB hjB DB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
      hXB
  ]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeCanonicalSignedMajorRational -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The TRUE signed canonical ν-pattern comparison, with ALL
active A/B global cells, obeys the unconditional major-rational
phase bound on the true harmonic labelled prime tuples.
Unlike C120, the SOURCE ORIGINAL pattern sign and full active
Knu are literally present under the auxiliary expectation.
The original prime-interval geometry stays explicit, and this
major-rational statement does not silently assert minor arcs. -/
theorem source_original_probe_full_active_signed_major_rational_unconditional434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [DecidableEq G]
      (J ell m : ℕ) (hmJ : m ≤ J)
      (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hMass : ∀ g, Vmin ≤ V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
         p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB)
      (hxi : 0 < xi)
      (jA jB : ℤ)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434
        m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434
        m P V ν hB xi)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (target source : ∀ g,
        Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ)
      (ht : ∀ g i, target g i ∈ P g)
      (hs : ∀ g i, source g i ∈ P g)
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ),
      let SA : ν.1 → Finset ℕ := fun z => P z.val.1
      let SB : ν.2 → Finset ℕ := fun z => P z.val.1
      let muA : ν.1 → ℕ → ℝ :=
        fun z => sourcePrimeSharedAtom434 (V z.val.1)
      let muB : ν.2 → ℕ → ℝ :=
        fun z => sourcePrimeSharedAtom434 (V z.val.1)
      let pA := sourceOriginalProbeTargetAIntoGram434
        J ell m hmJ ν P target ht
      let pB := sourceOriginalProbeSourceBIntoGram434
        J ell m hmJ ν P source hs
      let eps : ℝ := (K/Vmin)*L^(-B)
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
        sourceOriginalActualPrimitiveComparisonKernel434 Q
          (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
          (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
          hA hB
          (sourceOriginalProbeCellA434 m P V ν hA)
          (sourceOriginalProbeCellB434 m P V ν hB)
          (sourceOriginalGramPrimeProduct434 SA q.1)
          (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
          (sourceOriginalGramPrimeProduct434 SB q.2)
          (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
          (ν.1.card+ν.2.card) *
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2)) -
        (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
            sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)‖ ≤
        (eps+eps+eps*eps)*(r:ℝ) := by
  obtain ⟨K,Y,hK,hMajor⟩ :=
    source_original_probe_actual_major_rational_unconditional434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G _ J ell m hmJ ν P V hV Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB L hL hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    target source ht hs hCellA hCellB r hr hrQ u
  dsimp
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let ε : ℝ := (K/Vmin)*L^(-B)
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  have hσ : ‖σ‖ = 1 := by simp [σ]
  have hMajorInst :=
    hMajor J ell m hmJ ν P V hV Vmin hVmin hMass Q hBIGA hBIGB
      hA hB xi hhA hhB hxi jA jB hjA hjB
      L hL hLdyad hQ hXi
      iA iB uA vA uB vB huA huB huvA huvB hvA hvB
      huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
      target source ht hs hCellA hCellB r hr hrQ u
  let weight : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ := fun q =>
    ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
     (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ))
  let kA : SourceOriginalGramPrimeTuple434 SA → ℂ := fun q =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jA} hA (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalGramPrimeProduct434 SA q)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
  let kB : SourceOriginalGramPrimeTuple434 SB → ℂ := fun q =>
    sourceOriginalActualPrimitiveGlobalKernel434
      Q {jB} hB (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalGramPrimeProduct434 SB q)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
  let Ksigned : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ := fun q =>
    sourceOriginalActualPrimitiveComparisonKernel434 Q
      (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      hA hB
      (sourceOriginalProbeCellA434 m P V ν hA)
      (sourceOriginalProbeCellB434 m P V ν hB)
      (sourceOriginalGramPrimeProduct434 SA q.1)
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target)
      (sourceOriginalGramPrimeProduct434 SB q.2)
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
      (ν.1.card+ν.2.card)
  let phase : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ := fun q =>
    sourceOriginalPositiveRationalPhaseAtNat434 r hr u
      (sourceOriginalGramPrimeProduct434 SA q.1 *
       sourceOriginalGramPrimeProduct434 SB q.2)
  let phaseX : ℂ := sourceOriginalPositiveRationalPhaseAtNat434 r hr u
    (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target *
     sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source)
  have hKernelCollapse (q :
      SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB) :
      Ksigned q = σ * kA q.1 * kB q.2 := by
    have hc := source_original_probe_full_active_signed_singleton434
      J ell m hmJ ν P V Q hA hB xi hhA hhB
      jA jB hjA hjB
      (sourceOriginalGramPrimeProduct434 SA q.1)
      (sourceOriginalGramPrimeProduct434 SB q.2)
      target source hCellA hCellB
    dsimp only [Ksigned]
    rw [hc]
    rfl
  have hFactor :
      (∑ q : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        weight q * Ksigned q * phase q) =
      σ * (∑ q : SourceOriginalGramPrimeTuple434 SA ×
                 SourceOriginalGramPrimeTuple434 SB,
        weight q * (kA q.1 * kB q.2) * phase q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hKernelCollapse q]
    ring
  have hErrorSign :
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        weight q * Ksigned q * phase q) - σ * phaseX‖ =
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        weight q * (kA q.1 * kB q.2) * phase q) - phaseX‖ := by
    rw [hFactor, ←mul_sub, norm_mul, hσ, one_mul]
  have hNorm :
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        weight q * (kA q.1 * kB q.2) * phase q) - phaseX‖ ≤
      (ε+ε+ε*ε)*(r:ℝ) := by
    simpa only [SA,SB,muA,muB,weight,kA,kB,phase,phaseX,ε]
      using hMajorInst
  change ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
            SourceOriginalGramPrimeTuple434 SB,
    weight q * Ksigned q * phase q) - σ * phaseX‖ ≤
      (ε+ε+ε*ε)*(r:ℝ)
  rw [hErrorSign]
  exact hNorm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeRationalComparisonInstantiation -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- SOURCE03 pattern ν with its ACTUAL two different finite prime
sets, harmonic weights, and canonically chosen ACTIVE log-product
cells. This theorem discharges all external probability law and
retained cell mass assumptions from C118; these follow from
hV_g=sum_{p in P_g} 1/p, V_g>0 and the actual source03 active cells.
Only TRUE analytic BIG group band geometry and Vmin remain explicit.
No artificial independent prime law or arbitrary cell masses. -/
theorem source_original_probe_rational_comparison_instantiated434
    (Cq Cxi : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hB : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [DecidableEq G]
      (m : ℕ) (ν : SourceOriginalProbePattern434 G m)
      (P : G → Finset ℕ) (V : G → ℝ)
      (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
      (hVp : ∀ g, 0 < V g)
      (Q : ℕ)
      (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
           p.Prime ∧ Q^2 < p)
      (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
           p.Prime ∧ Q^2 < p)
      (hA hB xi : ℝ)
      (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
      (jA jB : ℤ)
      (hjA : jA ∈ sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
      (hjB : jB ∈ sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
      (L : ℝ) (hL : 1 ≤ L)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hQ : (Q:ℝ) ≤ L^Cq)
      (hXi : xi⁻¹ ≤ L^Cxi)
      (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^d))
      (hvB : (vB:ℝ) ≤ Real.exp (L^d))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
      (hYA : Y ≤ ((uA+1:ℕ):ℝ))
      (hYB : Y ≤ ((uB+1:ℕ):ℝ))
      (Vmin : ℝ) (hVmin : 0 < Vmin)
      (hAllVmin : ∀ g, Vmin ≤ V g)
      (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
      (pA : SourceOriginalGramPrimeTuple434
          (fun z : ν.1 => P z.val.1))
      (pB : SourceOriginalGramPrimeTuple434
          (fun z : ν.2 => P z.val.1))
      (hCellA : sourceOriginalLiteralLogCell434 hA jA
          (sourceOriginalGramPrimeProduct434
            (fun z : ν.1 => P z.val.1) pA))
      (hCellB : sourceOriginalLiteralLogCell434 hB jB
          (sourceOriginalGramPrimeProduct434
            (fun z : ν.2 => P z.val.1) pB))
      (r : ℕ) (hr : 0 < r) (hrQ : r ≤ Q) (u : ℤ),
      let SA : ν.1 → Finset ℕ := fun z => P z.val.1
      let SB : ν.2 → Finset ℕ := fun z => P z.val.1
      let muA : ν.1 → ℕ → ℝ := fun z =>
        sourcePrimeSharedAtom434 (V z.val.1)
      let muB : ν.2 → ℕ → ℝ := fun z =>
        sourcePrimeSharedAtom434 (V z.val.1)
      let eps : ℝ := (K/Vmin)*L^(-B)
      ‖(∑ q : SourceOriginalGramPrimeTuple434 SA ×
                     SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA q.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB q.2:ℂ)) *
        (sourceOriginalActualPrimitiveGlobalKernel434
           Q {jA} hA (sourceOriginalRealGramCellMass434 SA muA hA)
           (sourceOriginalGramPrimeProduct434 SA q.1)
           (sourceOriginalGramPrimeProduct434 SA pA) *
         sourceOriginalActualPrimitiveGlobalKernel434
           Q {jB} hB (sourceOriginalRealGramCellMass434 SB muB hB)
           (sourceOriginalGramPrimeProduct434 SB q.2)
           (sourceOriginalGramPrimeProduct434 SB pB)) *
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA q.1 *
            sourceOriginalGramPrimeProduct434 SB q.2)) -
        sourceOriginalPositiveRationalPhaseAtNat434 r hr u
           (sourceOriginalGramPrimeProduct434 SA pA *
            sourceOriginalGramPrimeProduct434 SB pB)‖ ≤
        (eps+eps+eps*eps)*(r:ℝ) := by
  obtain ⟨K,Y,hK,hEstimate⟩ :=
    source_original_two_global_rational_phase_comparison_unconditional434
      Cq Cxi gamma d B hgamma hd hB
  refine ⟨K,Y,hK,?_⟩
  intro G instDec m ν P V hV hVp Q hBIGA hBIGB
    hA hB xi hhA hhB hxi jA jB hjA hjB
    L hL hLdyad hQ hXi iA iB uA vA uB vB
    huA huB huvA huvB hvA hvB huLargeA huLargeB
    huBIGA huBIGB hYA hYB Vmin hVmin hAllVmin
    hBandA hBandB pA pB hCellA hCellB r hr hrQ u
  dsimp
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z =>
    sourcePrimeSharedAtom434 (V z.val.1)
  let VA := V iA.val.1
  let VB := V iB.val.1
  obtain ⟨hmuA,hmuPosA,hprimeA,hWeightA⟩ :=
    source_original_probe_actual_coordinate_law434
      SA (fun z : ν.1 => V z.val.1)
      (fun z => hV z.val.1) (fun z => hVp z.val.1)
      Q hBIGA
  obtain ⟨hmuB,hmuPosB,hprimeB,hWeightB⟩ :=
    source_original_probe_actual_coordinate_law434
      SB (fun z : ν.2 => V z.val.1)
      (fun z => hV z.val.1) (fun z => hVp z.val.1)
      Q hBIGB
  have hmA : xi ≤ sourceOriginalRealGramCellMass434
      SA muA hA jA :=
    source_original_probe_A_retained_gram_mass434
      m ν P V hA xi hhA hxi jA hjA
  have hmB : xi ≤ sourceOriginalRealGramCellMass434
      SB muB hB jB :=
    source_original_probe_B_retained_gram_mass434
      m ν P V hB xi hhB hxi jB hjB
  have hVA : Vmin ≤ VA := hAllVmin iA.val.1
  have hVB : Vmin ≤ VB := hAllVmin iB.val.1
  have hFirst := hEstimate
    SA muA hmuA hmuPosA SB muB hmuB hmuPosB
    hA hB jA jB Q iA hprimeA iB hprimeB
    L hL hLdyad hQ
    uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    Vmin hVmin VA VB hVA hVB hBandA hBandB
    (hWeightA iA) (hWeightB iB)
    xi hxi hXi hmA hmB pA pB hCellA hCellB r hr hrQ u
  simpa only [SA,SB,muA,muB,VA,VB] using hFirst
end Green64Analytic.CorrelationSquare

end

