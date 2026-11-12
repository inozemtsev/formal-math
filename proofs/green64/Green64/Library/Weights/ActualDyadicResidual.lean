module

public import Green64.Library.Weights.Part052
public import Green64.Library.Correlation.Part039
public import Green64.Library.Weights.Part015
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003

@[expose] public section

/-!
# Weights / ActualDyadicResidual

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualDyadicResidual -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

noncomputable def sourceOriginalActualC6Phase434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (SB : ιB → Finset ℕ)
    (theta ζ : ℝ) (k : ℤ)
    (q : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB) : ℂ :=
  Green64SourceC6.integerPhase (-(k:ℝ)*theta)
    (((sourceOriginalGramPrimeProduct434 SA q.1 *
        sourceOriginalGramPrimeProduct434 SB q.2):ℕ):ℤ) *
  sourceOriginalPureMellinPhase434 ζ
    (sourceOriginalGramPrimeProduct434 SA q.1 *
     sourceOriginalGramPrimeProduct434 SB q.2)

theorem source_original_actual_GLOBAL_preserves_dyad_support434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hPositive : ∀ i p, p ∈ S i → 0 < p)
    (active : Finset ℤ) (Q N : ℕ) (hN : 0 < N)
    (b : ℕ) (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (hSupp : ∀ p, sourceOriginalGramPrimeProduct434 S p ∉
      Finset.Ico (2^b) (2^(b+1)) → f p = 0)
    (p : SourceOriginalGramPrimeTuple434 S)
    (hp : sourceOriginalGramPrimeProduct434 S p ∉
      Finset.Ico (2^b) (2^(b+1))) :
    sourceOriginalActualGlobalAction434 S mu (Real.log 2/(N:ℝ))
      active Q f p = 0 := by
  have hf : (fun q => if sourceOriginalGramPrimeProduct434 S q ∈
      Finset.Ico (2^b) (2^(b+1)) then f q else 0) = f := by
    funext q
    by_cases hq : sourceOriginalGramPrimeProduct434 S q ∈
      Finset.Ico (2^b) (2^(b+1))
    · simp [hq]
    · simp [hq,hSupp q hq]
  have hh := source_original_actual_GLOBAL_commutes_dyad434
    S mu hPositive active Q N hN b f p
  rw [hf,if_neg hp] at hh
  exact hh

/-- For supported original endpoint tests, ALL auxiliary tuples in the
literal Knu pairing are localized to the SAME two coarse dyads, exactly.
The fine mesh and every retained fine-cell sum remain inside Knu. -/
theorem source_original_actual_Knu_supported_dyad_localization434
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (hPositiveA : ∀ i p, p ∈ SA i → 0 < p)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hPositiveB : ∀ i p, p ∈ SB i → 0 < p)
    (JA JB : Finset ℤ) (Q r NA NB : ℕ)
    (hNA : 0 < NA) (hNB : 0 < NB)
    (sA sB : ℕ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (hSuppA : ∀ p, sourceOriginalGramPrimeProduct434 SA p ∉
      Finset.Ico (2^sA) (2^(sA+1)) → fA p = 0)
    (hSuppB : ∀ p, sourceOriginalGramPrimeProduct434 SB p ∉
      Finset.Ico (2^sB) (2^(sB+1)) → fB p = 0)
    (H : SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB → ℂ) :
    sourceOriginalActualKnuPair434 SA muA SB muB
      (Real.log 2/(NA:ℝ)) (Real.log 2/(NB:ℝ)) JA JB Q r fA fB H =
    sourceOriginalActualKnuPair434 SA muA SB muB
      (Real.log 2/(NA:ℝ)) (Real.log 2/(NB:ℝ)) JA JB Q r fA fB
      (fun q => if sourceOriginalGramPrimeProduct434 SA q.1 ∈
        Finset.Ico (2^sA) (2^(sA+1)) ∧
        sourceOriginalGramPrimeProduct434 SB q.2 ∈
        Finset.Ico (2^sB) (2^(sB+1)) then H q else 0) := by
  rw [source_original_actual_Knu_pair_global_transfer434,
      source_original_actual_Knu_pair_global_transfer434]
  congr 1
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  apply Finset.sum_congr rfl
  intro q hq
  by_cases ha : sourceOriginalGramPrimeProduct434 SA q.1 ∈
      Finset.Ico (2^sA) (2^(sA+1))
  · by_cases hb : sourceOriginalGramPrimeProduct434 SB q.2 ∈
        Finset.Ico (2^sB) (2^(sB+1))
    · simp [ha,hb]
    · rw [source_original_actual_GLOBAL_preserves_dyad_support434
        SB muB hPositiveB JB Q NB hNB sB fB hSuppB q.2 hb]
      simp
  · rw [source_original_actual_GLOBAL_preserves_dyad_support434
      SA muA hPositiveA JA Q NA hNA sA fA hSuppA q.1 ha]
    simp

private theorem original_supported_raw_window
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (fA : SourceOriginalGramPrimeTuple434 SA → ℂ)
    (fB : SourceOriginalGramPrimeTuple434 SB → ℂ)
    (AW BW : Finset ℕ)
    (hA : ∀ p, sourceOriginalGramPrimeProduct434 SA p ∉ AW → fA p = 0)
    (hB : ∀ p, sourceOriginalGramPrimeProduct434 SB p ∉ BW → fB p = 0)
    (theta ζ : ℝ) (k : ℤ) :
    sourceOriginalFiniteTwoSidedMinorBilinear434
      (fun p => (sourceOriginalGramPrimeMass434 SA muA p:ℂ))
      (fun p => (sourceOriginalGramPrimeMass434 SB muB p:ℂ))
      fA fB (sourceOriginalActualC6Phase434 SA SB theta ζ k) =
    (∑ pA : SourceOriginalGramPrimeTuple434 SA,
      if sourceOriginalGramPrimeProduct434 SA pA ∈ AW then
        (sourceOriginalGramPrimeMass434 SA muA pA:ℂ)*fA pA *
        (∑ pB : SourceOriginalGramPrimeTuple434 SB,
          if sourceOriginalGramPrimeProduct434 SB pB ∈ BW then
            (sourceOriginalGramPrimeMass434 SB muB pB:ℂ)*fB pB *
            Green64SourceC6.integerPhase (-(k:ℝ)*theta)
              (((sourceOriginalGramPrimeProduct434 SA pA *
                sourceOriginalGramPrimeProduct434 SB pB):ℕ):ℤ) *
            sourceOriginalPureMellinPhase434 ζ
              (sourceOriginalGramPrimeProduct434 SA pA *
               sourceOriginalGramPrimeProduct434 SB pB)
          else 0)
      else 0) := by
  unfold sourceOriginalFiniteTwoSidedMinorBilinear434
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro pA hpA
  by_cases ha : sourceOriginalGramPrimeProduct434 SA pA ∈ AW
  · simp only [ha,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro pB hpB
    by_cases hb : sourceOriginalGramPrimeProduct434 SB pB ∈ BW
    · simp only [hb,ite_true,sourceOriginalActualC6Phase434]
      ring
    · simp [hb,hB pB hb]
  · simp [ha,hA pA ha]

/-- The ORIGINAL signed comparison residual on one coarse DYADIC output
pair, with ALL auxiliary tuples included. Aligned physical GLOBAL
kernels preserve those dyads exactly, so the actual raw C6 estimate and
the actual Knu C6 estimate combine with constant 4250 on squared norms.
No assumption of smallness, no fine-cell count, no character loss and
no fixed cap on the total number of probes occur. Major arcs and the
global dyadic sum remain separate obligations. -/
theorem eventually_source_original_actual_aligned_DYADIC_RESIDUAL_minor434
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
      (hSaving : Bsave+2*(C:ℝ) ≤ D)
      (NA NB : ℕ) (hNA : 0 < NA) (hNB : 0 < NB)
      (hAlignA : hA = Real.log 2/(NA:ℝ))
      (hAlignB : hB = Real.log 2/(NB:ℝ))
      (sA sB : ℕ) (hMA : M = 2^sA) (hNBscale : N = 2^sB)
      (hPM : P = M) (hQN : Q = N)
      (hSuppA : ∀ p, sourceOriginalGramPrimeProduct434 SA p ∉
        Finset.Ico (2^sA) (2^(sA+1)) → fA p = 0)
      (hSuppB : ∀ p, sourceOriginalGramPrimeProduct434 SB p ∉
        Finset.Ico (2^sB) (2^(sB+1)) → fB p = 0),
    let AW : Finset ℕ := (Finset.range P).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range Q).image (fun j => N+j)
    let EA : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SA,
      sourceOriginalGramPrimeMass434 SA muA p * ‖fA p‖^2
    let EB : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SB,
      sourceOriginalGramPrimeMass434 SB muB p * ‖fB p‖^2
    ‖sourceOriginalActualKnuPair434 SA muA SB muB
      hA hB JA JB Qchar (ν.1.card+ν.2.card) fA fB
      (sourceOriginalActualC6Phase434 SA SB theta ζ k) -
      (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      sourceOriginalFiniteTwoSidedMinorBilinear434
        (fun p => (sourceOriginalGramPrimeMass434 SA muA p:ℂ))
        (fun p => (sourceOriginalGramPrimeMass434 SB muB p:ℂ))
        fA fB (sourceOriginalActualC6Phase434 SA SB theta ζ k)‖^2 ≤
      4250*(EA*EB)*L^(-Bsave) := by
  obtain ⟨Y0,hEvent⟩ := eventually_source_original_actual_Knu_GLOBAL_C6_minor434
    cfg Cq Cxi gamma dscale hCxi hgamma hdscale
  refine ⟨Y0,?_⟩
  filter_upwards [hEvent,eventually_ge_atTop (1:ℝ)] with L hMinor hL
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar JA JB
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG fA fB
  dsimp only
  intro hMassA hMassB iA iB uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
    D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
    NA NB hNA hNB hAlignA hAlignB sA sB hMA hNBscale hPM hQN hSuppA hSuppB
  classical
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let AW := (Finset.range P).image (fun i => M+i)
  let BW := (Finset.range Q).image (fun j => N+j)
  let EA : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SA,
    sourceOriginalGramPrimeMass434 SA muA p*‖fA p‖^2
  let EB : ℝ := ∑ p : SourceOriginalGramPrimeTuple434 SB,
    sourceOriginalGramPrimeMass434 SB muB p*‖fB p‖^2
  let phase := sourceOriginalActualC6Phase434 SA SB theta ζ k
  let Kval := sourceOriginalActualKnuPair434 SA muA SB muB
    hA hB JA JB Qchar (ν.1.card+ν.2.card) fA fB phase
  let Rval := (-((-1:ℂ)^(ν.1.card+ν.2.card))) *
    sourceOriginalFiniteTwoSidedMinorBilinear434
      (fun p => (sourceOriginalGramPrimeMass434 SA muA p:ℂ))
      (fun p => (sourceOriginalGramPrimeMass434 SB muB p:ℂ))
      fA fB phase
  have hAW : AW = Finset.Ico (2^sA) (2^(sA+1)) := by
    dsimp [AW]
    rw [hPM,hMA]
    ext n
    rw [← source_original_ico_eq_C6_range434]
    simp only [pow_succ, Nat.mul_comm]
  have hBW : BW = Finset.Ico (2^sB) (2^(sB+1)) := by
    dsimp [BW]
    rw [hQN,hNBscale]
    ext n
    rw [← source_original_ico_eq_C6_range434]
    simp only [pow_succ, Nat.mul_comm]
  have hPositiveA (z : ν.1) (p : ℕ) (hp : p ∈ SA z) : 0 < p :=
    (d.hTbPrime z.val.1 p hp).pos
  have hPositiveB (z : ν.2) (p : ℕ) (hp : p ∈ SB z) : 0 < p :=
    (d.hTbPrime z.val.1 p hp).pos
  have hLoc := source_original_actual_Knu_supported_dyad_localization434
    SA muA hPositiveA SB muB hPositiveB JA JB
    Qchar (ν.1.card+ν.2.card) NA NB hNA hNB sA sB fA fB hSuppA hSuppB phase
  rw [← hAlignA,← hAlignB] at hLoc
  have hLocalized : Kval = sourceOriginalActualKnuPair434 SA muA SB muB
      hA hB JA JB Qchar (ν.1.card+ν.2.card) fA fB
      (sourceOriginalActualC6WindowPhase434 SA SB AW BW theta ζ k) := by
    have hPhaseEq : sourceOriginalActualC6WindowPhase434 SA SB AW BW theta ζ k =
        (fun q => if sourceOriginalGramPrimeProduct434 SA q.1 ∈
          Finset.Ico (2^sA) (2^(sA+1)) ∧
          sourceOriginalGramPrimeProduct434 SB q.2 ∈
          Finset.Ico (2^sB) (2^(sB+1)) then phase q else 0) := by
      funext q
      unfold sourceOriginalActualC6WindowPhase434
      simp only [hAW,hBW]
      rfl
    rw [hPhaseEq]
    exact hLoc
  have hK0 := hMinor x Y Hprime d sep hVbig blockA blockB hDisjoint m hm ν
    hPattern Qchar JA JB hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG
    fA fB hMassA hMassB iA iB uA vA uB vB huA huB huvA huvB
    hvA hvB huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    ζ M N P Q hM hN a r beta0 theta k hApprox hr hcop hbeta hP hQ
    D Bsave hR hNlarge hMlarge hMNlarge C hExponent hSaving
  have hK : ‖Kval‖^2 ≤ 2000*(EA*EB)*L^(-Bsave) := by
    rw [hLocalized]
    exact hK0
  have hSupportAW (p : SourceOriginalGramPrimeTuple434 SA)
      (hp : sourceOriginalGramPrimeProduct434 SA p ∉ AW) : fA p = 0 :=
    hSuppA p (by simpa only [hAW] using hp)
  have hSupportBW (p : SourceOriginalGramPrimeTuple434 SB)
      (hp : sourceOriginalGramPrimeProduct434 SB p ∉ BW) : fB p = 0 :=
    hSuppB p (by simpa only [hBW] using hp)
  have hRaw := source_original_true_signed_raw_mellin_physical_minor434
    cfg x L Y Hprime d sep blockA blockB hDisjoint m hm ν hPattern
    ζ fA fB M N P Q hM hN a r beta0 theta k hApprox
    hr hcop hbeta hP hQ D Bsave hL hR hNlarge hMlarge hMNlarge C hExponent hSaving
  have hRval : ‖Rval‖^2 ≤ 125*(EA*EB)*L^(-Bsave) := by
    dsimp only [Rval,phase]
    rw [original_supported_raw_window SA muA SB muB fA fB AW BW
      hSupportAW hSupportBW theta ζ k]
    exact hRaw
  change ‖Kval-Rval‖^2 ≤ 4250*(EA*EB)*L^(-Bsave)
  have hTri := norm_sub_le Kval Rval
  have hTriSq := pow_le_pow_left₀ (norm_nonneg (Kval-Rval)) hTri 2
  nlinarith [sq_nonneg (‖Kval‖-‖Rval‖)]
end Green64Analytic.CorrelationSquare

end

