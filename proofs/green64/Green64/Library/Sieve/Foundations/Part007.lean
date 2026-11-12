module

public import Green64.Library.Weights.Part111
public import Green64.Library.Weights.Part113
public import Green64.Library.Analysis.Estimates.Part016
public import Green64.Library.Weights.Part116
public import Green64.Library.Sieve.Foundations.Part004
public import Green64.Library.Weights.Part114
public import Green64.Library.Weights.Part115
public import Green64.Library.Correlation.Part070
public import Green64.Library.Analysis.Estimates.Part014
public import Green64.Library.Weights.Part102
public import Green64.Library.Weights.Part110
public import Green64.Library.Weights.Part112

@[expose] public section

/-!
# Sieve / Foundations / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## UniformRankMain -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- The original actual source contract, with one precision choice before the fine parameters. -/
theorem parity_eventually_enlarged_actual_rank_marked_arc_common_precision434
    (A : ℝ) (hLargeA : 64 ≤ A)
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi Ck Cpsi targetSaving : ℝ)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hcm : Ck+1 ≤ (cm:ℝ))
    (hCarc : (cm:ℝ) ≤ Carc) (hCchi : (cm:ℝ) ≤ Cchi) (hCchiPos : 0 < Cchi)
    (hCpsi : 0 ≤ Cpsi)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg0 := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
      hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
    let cfg := parityEnlargedComparisonFixed434 cfg0 A (by linarith)
    ∃ Karc : ℝ, 0 < Karc ∧ ∃ B : ℕ, ∃ S : ℝ,
      2*((B:ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
          ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ParityEnlargedActualRankComparisonCellArc434 cfg L jQ mmax CZ Ck S beta gamma
          targetSaving Karc := by
  let cfg0 := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
  let cfg := parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  obtain ⟨Karc,hKarc,B,S,hSEq,hSB,X0,hX0,hArc⟩ :=
    parity_b629_full_marked_arc_common_precision434 cfg targetSaving
  refine ⟨Karc,hKarc,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hArc := hArc beta gamma hbeta hgamma
  have hS : 0 < S := by have := Nat.cast_nonneg (α:=ℝ) B; linarith
  have hData := parity_eventually_actual_comparison_data434
    jQ mmax cm s0 s1 vexp CZ Carc Cchi Ck Cpsi S beta gamma
    hCZ hCk hcm hCarc hCchi hCchiPos hCpsi hS hbeta hgamma Kpsi hKpsi
  have hCarc0 : 0 ≤ Carc := (Nat.cast_nonneg cm).trans hCarc
  have hScales := Filter.eventually_all.mpr
    (fun m : Fin (mmax+1) => parity_eventually_enlarged_comparison_cell_scales434
      A CZ Carc m.val hLargeA hCZ hCarc0)
  filter_upwards [hData,hScales,hArc,eventually_ge_atTop (max 3 (Real.log X0))]
    with L hd hscale hArcL hLarge
  have hL : 3 ≤ L := (le_max_left _ _).trans hLarge
  have hLp : 0 < L := by linarith
  have hx : X0 ≤ Real.exp L := by
    have hlog : Real.log X0 ≤ L := (le_max_right _ _).trans hLarge
    simpa only [Real.exp_log (by linarith : 0 < X0)] using Real.exp_le_exp.mpr hlog
  have hZeroBudget : sourceLogDerivativeBudget cfg0.Cpsi cfg0.Kpsi L
      (fun _ : ℝ => (0 : ℂ)) := by
    intro j u
    simpa using (mul_nonneg (cfg0.hKpsi j)
      (Real.rpow_nonneg hLp.le (cfg0.Cpsi*((j:ℝ)+1))))
  refine ⟨hd.1,hd.2.1,?_⟩
  unfold ParityEnlargedActualRankComparisonCellArc434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hA hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hK chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1
    psi hSmooth hSupport hBudget prime lFine uFine a b hFineLow hl hu hub
    Qcomp aux hAux hAuxA hAuxB ca cb tw sourceSide
  dsimp only
  obtain ⟨data,hfields⟩ := hd.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu
    hA hB xi hhA hhB hxi hA1 hB1 ja jb ha hb band hband slot delta freq k hk hK
    chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1 (fun _ => 0) contDiff_const
    (by intro u hu; exact False.elim (hu rfl)) hZeroBudget
    prime lFine uFine a b hFineLow Qcomp aux hAux hAuxA hAuxB (fun _ _=>0) tw true
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let Y := Z*Hp
  have hgeo := (hscale ⟨m,by omega⟩).2 Z hZlo hZhi nu hnu hA hB xi
    hhA hhB hA1 hB1 ja jb ha hb
  dsimp only at hgeo
  obtain ⟨hz,hcap,hG,hTw,hSdata,hTs,hTb,hVs,hVm,hVb,hts,htb,hcoef,hk0,hAlpha,
    hlo,hhi,hcut,hF1,hF2,hp1,hp2,hU1,hU2,hQ,hc,hC,hq,hchi,hs0,hs1,hv,hpsi⟩ := hfields
  have hOldCap : data.Ncap ≤ ⌈A*Y⌉₊ := by
    rw [hcap]
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_right hLargeA (by have hh := data.hY; linarith)
  let enlarged : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L Y Hp :=
    parityEnlargedComparisonData434 data A (by linarith) ⌈A*Y⌉₊
      hgeo.2.1 hgeo.1 hOldCap hgeo.2.2 psi hSmooth hSupport hBudget
  let rank := if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB jb cb
    else paritySecondRankMark434 J 1 m hmJ nu hA ja ca
  have hRank : ∀ marks, ‖rank marks‖ ≤ 1 := by
    intro marks
    have hh := parity_actual_rank_mark_norm434 J 1 m hmJ nu hA hB ja jb ca cb marks
    cases sourceSide
    · exact hh.2
    · exact hh.1
  let ranked : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L Y Hp :=
    { enlarged with
      tb := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu
      coef := rank
      htb := fun g => (source_original_probe_free_mark_cap434 J 1 m hmJ nu g).trans
        (by change 1+m ≤ 1+mmax; omega)
      hcoef := hRank }
  refine ⟨ranked,?_,?_,?_⟩
  · exact ⟨hz,rfl,hG,hTw,hSdata,hTs,hTb,hVs,hVm,hVb,hts,rfl,HEq.rfl,hk0,hAlpha,
      hlo,hhi,hcut,hF1,hF2,hp1,hp2,hU1,hU2,hQ,hc,hC,hq,hchi,hs0,hs1,hv,rfl⟩
  · dsimp only [ranked,enlarged,parityEnlargedComparisonData434,
      SourceComparisonData434.endpoint,SourceComparisonData434.cutoff]
    simp only [hv]
    congr 1
  · intro eps den h hden hDenCap
    exact hArcL (Real.exp L) hx (Real.log_exp L).symm hL prime lFine uFine
      hl hu hFineLow hub _ _ ranked hAlpha eps den h hden hDenCap

/-- The original actual source contract, with one precision choice before the fine parameters. -/
theorem parity_eventually_constructed_actual_rank_marked_arc_common_precision434
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi Ck targetSaving : ℝ)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hcm : Ck+1 ≤ (cm:ℝ))
    (hCarc : (cm:ℝ) ≤ Carc) (hCchi : (cm:ℝ) ≤ Cchi) (hCchiPos : 0 < Cchi) :
    ∃ (A : ℝ) (hA : 64 ≤ A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ, eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u=1) ∧
      (∀ u : ℝ, ‖eta u‖≤1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j, 0≤K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ => eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ => eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0 := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg := parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        ∃ Karc : ℝ, 0 < Karc ∧ ∃ B : ℕ, ∃ S : ℝ,
          2*((B:ℝ)+1)+3 < S ∧
          ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityConstructedActualRankComparisonCellArc434 cfg eta L jQ mmax CZ Ck S beta gamma
              targetSaving Karc := by
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,hsInv,hSuppInv,K,hK,hBudgets⟩ :=
    parity_fixed_rank_cutoff_pair_budget434
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,?_⟩
  obtain ⟨Karc,hKarc,B,S,hSB,hArc⟩ := parity_eventually_enlarged_actual_rank_marked_arc_common_precision434
    A hA jQ mmax cm s0 s1 vexp CZ Carc Cchi Ck 0 targetSaving
    hCZ hCk hcm hCarc hCchi hCchiPos (by norm_num) K hK
  refine ⟨Karc,hKarc,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hArc := hArc beta gamma hbeta hgamma
  filter_upwards [hArc] with L hArcL
  refine ⟨hArcL.1,hArcL.2.1,?_⟩
  unfold ParityConstructedActualRankComparisonCellArc434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1
    prime lFine uFine a b hFineLow hl hu hub
    Qcomp aux hAux hAuxA hAuxB ca cb tw sourceSide
  let psi : ℝ → ℂ := if sourceSide then (fun u => eta u/(u : ℂ)) else eta
  have hPsiSmooth : ContDiff ℝ ∞ psi := by
    cases sourceSide
    · exact hs
    · exact hsInv
  have hPsiSupport : ∀ u : ℝ, psi u≠0 → 1/A≤u ∧ u≤A := by
    cases sourceSide
    · exact hSupp
    · exact hSuppInv
  have hPsiBudget : sourceLogDerivativeBudget 0 K L (fun u : ℝ => psi (Real.exp u)) := by
    cases sourceSide
    · exact (hBudgets L).1
    · exact (hBudgets L).2
  exact hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu
    hAcell hB xi hhA hhB hxi hA1 hB1 ja jb ha hb band hband slot delta freq k hk hKcap
    chi sigma0 sigma1 v1 hsigma0 hsigma1 hv1 psi hPsiSmooth hPsiSupport hPsiBudget
    prime lFine uFine a b hFineLow hl hu hub Qcomp aux hAux hAuxA hAuxB ca cb tw sourceSide

/-- The original actual source contract, with one precision choice before the fine parameters. -/
theorem parity_eventually_B633_actual_rank_marked_arc_common_precision434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck targetSaving Cfreq Ftail : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    ∃ (A : ℝ) (hA : 64≤A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖≤1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0≤K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualRankCellArc434 cfg eta L jQ mmax CZ Ck S beta gamma
              targetSaving Karc Cfreq Ftail := by
  dsimp only
  let s0:=⌈Cfreq+1⌉₊
  let s1:=⌈Cfreq⌉₊
  let vexp:=⌈max Cfreq Ftail+1⌉₊
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,hArc⟩ :=
    parity_eventually_constructed_actual_rank_marked_arc_common_precision434
      jQ mmax cm s0 s1 vexp CZ Carc Cchi Ck targetSaving
      hCZ hCk hcm hCarc hCchi hCchiPos
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hArc := hArc beta gamma hbeta hgamma
  let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  filter_upwards [hArc,eventually_ge_atTop (2+2*Real.pi)] with L hArcL hLlarge
  refine ⟨hArcL.1,hArcL.2.1,?_⟩
  unfold ParityB633ActualRankCellArc434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
    hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
    Qcomp aux hAux hAuxA hAuxB ca cb tw sourceSide
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let core:=if sourceSide then
    b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
    else b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let v:=if sourceSide then -(rho+xi3)-2*Real.pi*s else -rho
  let psi : ℝ → ℂ:=if sourceSide then (fun u=>eta u/(u : ℂ)) else eta
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  have hf:=parity_B633_mellin_frequency_bounds434 L Cfreq Ftail s0 s1 vexp hLlarge
    (Nat.le_ceil _) (Nat.le_ceil _) (Nat.le_ceil _)
    rho xi1 xi2 xi3 sigma s hrho hxi1 hxi2 hxi3 hsigma hsTail
  have hSigma0 : |if sourceSide then -(xi2-rho) else xi1+rho|≤L^cfg.s0 := by
    cases sourceSide
    · exact hf.2.1
    · exact hf.1
  have hSigma1 : |-sigma|≤L^cfg.s1base := hf.2.2.1
  have hV : |v|≤L^cfg.vexp := by
    cases sourceSide
    · exact hf.2.2.2.2
    · exact hf.2.2.2.1
  obtain ⟨data,hd,he,hArcData⟩ := hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu
    hAcell hB xi hhA hhB hxi hA1 hB1 ja jb ha hb band hband slot delta freq k hk hKcap
    chi (if sourceSide then -(xi2-rho) else xi1+rho) (-sigma) v hSigma0 hSigma1 hV
    prime lFine uFine a b hFineLow hl hu hub Qcomp aux hAux hAuxA hAuxB ca cb tw sourceSide
  have hcap : data.Ncap=⌈cfg.A*Y⌉₊ := hd.2.1
  have hparity : data.Ptw=(if tw then sourceNativeOriginalG434 20 L else ∅) := hd.2.2.2.1
  have hSupport : data.support=
      (Finset.Icc 1 ⌈cfg.A*Y⌉₊).image (fun n : ℕ=>(n : ℤ)) := by
    unfold SourceComparisonData434.support
    rw [hcap]
  have hL : 1<L := by linarith [Real.pi_pos]
  have hcoeff (n : ℕ) (hn : 0<n) :
      sourceSignedCoefficients434 data.Ptw true data.endpoint (n : ℤ)=
        psi ((n : ℝ)/Y)*
          parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 core v tw sourceSide n := by
    rw [hparity,he]
    exact (parity_actual_B633_rank_cutoff_original434 L hL hFamily J m hmJ nu hAcell hB rank cfg.q0
      band slot delta freq k chi prime S gamma lFine uFine a b xi1 xi2 xi3 rho sigma s Y eta
      tw sourceSide n hn).symm
  have hpoly : sourceCircleFourierPoly data.support
      (sourceSignedCoefficients434 data.Ptw true data.endpoint)=
      sourceCircleFourierPoly ((Finset.Icc 1 ⌈cfg.A*Y⌉₊).image (fun n : ℕ=>(n : ℤ)))
        (fun z : ℤ=>psi ((z.toNat : ℝ)/Y)*
          parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 core v tw sourceSide z.toNat) := by
    rw [hSupport]
    unfold sourceCircleFourierPoly
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hz
    rw [hcoeff n (by have hh:=(Finset.mem_Icc.mp hn).1;omega)]
    rfl
  dsimp only
  intro den h hden hdenCap
  have hh:=hArcData true den h hden hdenCap
  rw [hpoly] at hh
  exact hh

/-- The original actual source contract, with one precision choice before the fine parameters. -/
theorem parity_eventually_B633_actual_harmonic_rank_arc_common_precision434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck targetSaving Cfreq Ftail : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    ∃ (A : ℝ) (hA : 64≤A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖≤1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0≤K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualHarmonicRankCellArc434 cfg eta L jQ mmax CZ Ck S beta gamma
              targetSaving Karc Cfreq Ftail := by
  dsimp only
  let s0:=⌈Cfreq+1⌉₊
  let s1:=⌈Cfreq⌉₊
  let vexp:=⌈max Cfreq Ftail+1⌉₊
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,hArc⟩ :=
    parity_eventually_B633_actual_rank_marked_arc_common_precision434 jQ mmax cm CZ Carc Cchi Ck
      targetSaving Cfreq Ftail hCZ hCk hcm hCarc hCchi hCchiPos
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hArc := hArc beta gamma hbeta hgamma
  let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  have hCarc0 : 0≤Carc:=(Nat.cast_nonneg cm).trans hCarc
  have hScales:=Filter.eventually_all.mpr
    (fun m : Fin (mmax+1)=>parity_eventually_enlarged_comparison_cell_scales434
      A CZ Carc m.val hA hCZ hCarc0)
  filter_upwards [hArc,hScales] with L hArcL hscale
  refine ⟨hArcL.1,hArcL.2.1,?_⟩
  unfold ParityB633ActualHarmonicRankCellArc434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
    hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
    Qcomp aux hAux hAuxA hAuxB ca cb tw
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let M:=Finset.Icc 1 ⌈A*Y⌉₊
  let U:=fun n : ℕ=>parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
    E (-(rho+xi3)) tw true n
  let V:=fun n : ℕ=>parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
    G (-rho) tw false n
  let Ub:=fun n : ℕ=>(eta ((n : ℝ)/Y)/(((n : ℝ)/Y : ℝ) : ℂ))*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
      E (-(rho+xi3)-2*Real.pi*s) tw true n
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*V n)
  let firstBase:=sourceNatFourierPoly M Ub
  let secondBase:=sourceNatFourierPoly M (fun n : ℕ=>eta ((n : ℝ)/Y)*V n)
  have hgeo:=(hscale ⟨m,by omega⟩).2 Z hZlo hZhi nu hnu hAcell hB xi
    hhA hhB hA1 hB1 ja jb ha hb
  have hL2 : 2≤L:=(hscale ⟨m,by omega⟩).1
  have hLp : 0<L:=by linarith
  have hZ : 0<Z:=(mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hY : 0<Y:=by dsimp [Y,Hp]; positivity
  have hAs : 1≤A:=by linarith
  have hCap : (⌈A*Y⌉₊ : ℝ)≤Real.exp (2*L):=by
    calc
      _≤(Real.exp L)^2:=hgeo.2.1
      _=Real.exp (2*L):=by rw [pow_two,←Real.exp_add];congr 1;ring
  have hFirstScale : first=(Y : ℂ)⁻¹ • firstBase:=by
    unfold first
    rw [parity_actual_cell_mellin_first_carrier434 J Ck L hLp A Y hAs hY eta hSupp hCap U s]
    have heq : parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*U n)=
        (fun n : ℕ=>(Y : ℂ)⁻¹*Ub n):=by
      funext n
      exact parity_actual_cell_mellin_first_endpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0
        E (-(rho+xi3)) s Y hY tw true eta n
    rw [heq]
    exact parity_nat_fourier_const_mul434 M ((Y : ℂ)⁻¹) Ub
  have hSecondCarrier : second=secondBase:=
    parity_actual_cell_fourier_carrier434 J Ck L hLp A Y hAs hY eta hSupp hCap V
  dsimp only
  intro den h hden hdenCap
  let angle:=fun theta : ℝ=>(((h : ℝ)/(den : ℝ)+theta : ℝ) : AddCircle (1 : ℝ))
  let R:=L^cfg.Carc/Hp
  have hFirstBase : (∫ theta in {theta : ℝ | |theta|≤R},‖firstBase (angle theta)‖^2)≤
      Karc*Y*L^(-targetSaving):=
    hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
      ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
      hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw true den h hden hdenCap
  have hSecondBase : (∫ theta in {theta : ℝ | |theta|≤R},‖secondBase (angle theta)‖^2)≤
      Karc*Y*L^(-targetSaving):=
    hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
      ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
      hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw false den h hden hdenCap
  have hFirstValue (theta : ℝ) : first (angle theta)=(Y : ℂ)⁻¹*firstBase (angle theta):=by
    rw [hFirstScale]
    rfl
  have hFirst : (∫ theta in {theta : ℝ | |theta|≤R},‖first (angle theta)‖^2)≤
      (Karc/Y)*L^(-targetSaving):=by
    calc
      _=(Y⁻¹)^2*(∫ theta in {theta : ℝ | |theta|≤R},‖firstBase (angle theta)‖^2):=by
        simp_rw [hFirstValue]
        exact parity_harmonic_arc_energy_scale434 Y R hY (fun theta=>firstBase (angle theta))
      _≤(Y⁻¹)^2*(Karc*Y*L^(-targetSaving)):=
        mul_le_mul_of_nonneg_left hFirstBase (sq_nonneg _)
      _=(Karc/Y)*L^(-targetSaving):=by field_simp [hY.ne']
  have hSecond : (∫ theta in {theta : ℝ | |theta|≤R},‖second (angle theta)‖^2)≤
      Karc*Y*L^(-targetSaving):=by simpa only [hSecondCarrier] using hSecondBase
  refine ⟨hFirst,hSecond,?_⟩
  have hangle : Continuous angle:=by fun_prop
  have hfirst : Continuous (fun theta=>first (angle theta)):=first.continuous.comp hangle
  have hsecond : Continuous (fun theta=>second (angle theta)):=second.continuous.comp hangle
  apply parity_harmonic_arc_cauchy434 Y (Karc*L^(-targetSaving)) R hY
    (fun theta=>first (angle theta)) (fun theta=>second (angle theta)) hfirst hsecond
  · convert hFirst using 1 <;> ring
  · convert hSecond using 1 <;> ring

/-- The original actual source contract, with one precision choice before the fine parameters. -/
theorem parity_eventually_B633_actual_harmonic_circle_major_common_precision434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck targetSaving Cfreq Ftail : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    ∃ (A : ℝ) (hA : 64≤A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖≤1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0≤K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualHarmonicRankCellCircleMajor434 cfg eta L jQ mmax CZ Ck S beta gamma
              targetSaving Karc Cfreq Ftail := by
  dsimp only
  let s0:=⌈Cfreq+1⌉₊
  let s1:=⌈Cfreq⌉₊
  let vexp:=⌈max Cfreq Ftail+1⌉₊
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,hArc⟩ :=
    parity_eventually_B633_actual_harmonic_rank_arc_common_precision434 jQ mmax cm CZ Carc Cchi Ck
      targetSaving Cfreq Ftail hCZ hCk hcm hCarc hCchi hCchiPos
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hArc := hArc beta gamma hbeta hgamma
  let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  have hCarc0 : 0≤Carc:=(Nat.cast_nonneg cm).trans hCarc
  have hScales:=Filter.eventually_all.mpr
    (fun m : Fin (mmax+1)=>parity_eventually_full_comparison_cell_scales434
      CZ (Carc+1) m.val hCZ (by linarith))
  filter_upwards [hArc,hScales] with L hArcL hscale
  refine ⟨hArcL.1,hArcL.2.1,?_⟩
  unfold ParityB633ActualHarmonicRankCellCircleMajor434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
    hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
    Qcomp aux hAux hAuxA hAuxB ca cb tw
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*
      parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 E (-(rho+xi3)) tw true n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 G (-rho) tw false n)
  have hgeo:=(hscale ⟨m,by omega⟩).2 Z hZlo hZhi nu hnu hAcell hB xi
    hhA hhB hA1 hB1 ja jb ha hb
  have hL2 : 2≤L:=(hscale ⟨m,by omega⟩).1
  have hLp : 0<L:=by linarith
  have hL1 : 1≤L:=by linarith
  have hHp : 0<Hp:=by dsimp [Hp];positivity
  have hY : 0<Y:=mul_pos hgeo.1 hHp
  have hBand : 2≤Hp/L^(Carc+1):=hgeo.2.2.2.2.2.2.2.1
  have hRad:=parity_arc_radius_half_of_power_band434 L Hp Carc hL2 hHp hBand
  dsimp only
  intro Qmajor hQ
  let major:=sourceCircleRationalArcs434 Qmajor (L^cfg.Carc/Hp)
  have hQreal : (Qmajor : ℝ)≤L^(cfg.cm : ℝ):=by
    simpa only [Real.rpow_natCast] using hQ
  have hEach (den h : ℕ) (hd : 0<den) (hdQ : den≤Qmajor) :=
    hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
      ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
      hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw den h hd
      ((show (den : ℝ)≤Qmajor by exact_mod_cast hdQ).trans hQ)
  change (∫ theta in major,‖first theta‖^2 ∂AddCircle.haarAddCircle)≤
      (2*Karc/Y)*L^(2*(cfg.cm : ℝ)-targetSaving) ∧
    (∫ theta in major,‖second theta‖^2 ∂AddCircle.haarAddCircle)≤
      2*Karc*Y*L^(2*(cfg.cm : ℝ)-targetSaving) ∧
    (∫ theta in major,‖star (first theta)*second theta‖ ∂AddCircle.haarAddCircle)≤
      2*Karc*L^(2*(cfg.cm : ℝ)-targetSaving)
  refine ⟨?_,?_,?_⟩
  · have hFirst := source_circle_major_arc_saving434 Qmajor first Hp cfg.Carc
      (cfg.cm : ℝ) targetSaving Karc L Y⁻¹ hL1 (Nat.cast_nonneg _) hKarc.le
      (inv_nonneg.mpr hY.le) hQreal hRad.1 hRad.2 (fun den h hd hdQ hhd => by
        have hi := (hEach den h hd hdQ).1
        change (∫ theta in {theta : ℝ | |theta|≤L^cfg.Carc/Hp},
          ‖first (((h : ℝ)/(den : ℝ)+theta : ℝ) : AddCircle (1 : ℝ))‖^2)≤
          (Karc/Y)*L^(-targetSaving) at hi
        simpa only [div_eq_mul_inv] using hi)
    simpa only [major,div_eq_mul_inv,mul_assoc] using hFirst
  · exact source_circle_major_arc_saving434 Qmajor second Hp cfg.Carc
      (cfg.cm : ℝ) targetSaving Karc L Y hL1 (Nat.cast_nonneg _) hKarc.le hY.le
      hQreal hRad.1 hRad.2 (fun den h hd hdQ hhd => (hEach den h hd hdQ).2.1)
  · exact parity_circle_rational_product_saving434 Qmajor first second Hp cfg.Carc
      (cfg.cm : ℝ) targetSaving Karc L hL1 (Nat.cast_nonneg _) hKarc.le
      hQreal hRad.1 hRad.2 (fun den h hd hdQ hhd => (hEach den h hd hdQ).2.2)

/-- The original actual source contract, with one precision choice before the fine parameters. -/
theorem parity_eventually_B633_actual_coupled_circle_bound_common_precision434
    (jQ mmax cm : ℕ)
    (CZ Carc Cchi Ck majorSaving Cfreq Ftail minorSaving D : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hD : 0≤D)
    (hMinorSaving : 2*minorSaving+2+2*(parityCellKernelMomentExponent434 mmax : ℝ)≤D)
    (hcm : Ck+D+3≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hMinorArc : D+2≤Carc) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    let gcfg:=parityComparisonFixed434 jQ mmax cm 0 0 0 CZ Carc Cchi
      hCarc hCchi hCchiPos 0 (by norm_num) (fun _=>0) (by intro j;norm_num)
    ∃ (A : ℝ) (hA : 64≤A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖≤1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0≤K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        let Kg:=parityGlobalMarkConstant434 mmax
        let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
        0<Kglobal ∧ 0≤parityGlobalMarkExponent434 mmax ∧
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualHarmonicGlobalCellEnergy434 gcfg A L jQ mmax CZ Ck S beta gamma
              Kglobal (parityGlobalMarkExponent434 mmax) ∧
            ParityB633ActualCoupledRankCircleBound434 cfg eta L jQ mmax CZ Ck S beta gamma
              majorSaving Karc Cfreq Ftail minorSaving Kglobal := by
  dsimp only
  have hcm0 : Ck+1≤(cm : ℝ):=by linarith
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,hArc⟩ :=
    parity_eventually_B633_actual_harmonic_circle_major_common_precision434 jQ mmax cm CZ Carc Cchi Ck
      majorSaving Cfreq Ftail hCZ hCk hcm0 hCarc hCchi hCchiPos
  have hGlobalFixed:=parity_eventually_B633_actual_harmonic_global_fixed434
    jQ mmax cm CZ Carc Cchi Ck 1 1 A hCZ hCk hcm0 hCarc hCchi hCchiPos (by norm_num) (by norm_num) hA
  have hMinor:=parity_eventually_actual_cell_coupled_minor_saving434
    mmax minorSaving D Carc hD hMinorSaving hMinorArc
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,hGlobalFixed.1,hGlobalFixed.2.1,
    Karc,hKarc,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hArc := hArc beta gamma hbeta hgamma
  have hGlobal:=parity_eventually_B633_actual_harmonic_global_fixed434
    jQ mmax cm CZ Carc Cchi Ck beta gamma A hCZ hCk hcm0 hCarc hCchi hCchiPos hbeta hgamma hA
  have hSpos : 0<S:=by nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  let cfg0:=parityComparisonFixed434 jQ mmax cm ⌈Cfreq+1⌉₊ ⌈Cfreq⌉₊
    ⌈max Cfreq Ftail+1⌉₊ CZ Carc Cchi hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  let Kg:=parityGlobalMarkConstant434 mmax
  let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
  filter_upwards [hArc,hGlobal.2.2 S hSpos,hMinor,eventually_ge_atTop (2 : ℝ)]
    with L hArcL hGlobalL hMinorL hL
  refine ⟨hArcL.1,hArcL.2.1,hGlobalL.2.2,?_⟩
  unfold ParityB633ActualCoupledRankCircleBound434
  intro hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
    ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
    hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
    Qcomp ca cb hca hcb tw
  obtain ⟨aux,hAux,hAuxA,hAuxB⟩:=parity_active_cells_joint_aux434 m nu
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    hAcell hB xi hhA hhB hxi ja jb ha hb
  let Hp:=Real.exp ((ja : ℝ)*hAcell)*Real.exp ((jb : ℝ)*hB)
  let Y:=Z*Hp
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let rank : ParityPrimitiveRankIndex434 Qcomp:=((ja,ca),(jb,cb))
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let first:=sourceNatFourierPoly N
    (parityMellinFourierFirst434 s (fun n : ℕ=>eta ((n : ℝ)/Y)*
      parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 E (-(rho+xi3)) tw true n))
  let second:=sourceNatFourierPoly N (fun n : ℕ=>eta ((n : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hAcell hB rank cfg.q0 G (-rho) tw false n)
  let coeff:=sourceOriginalTwoCellCoefficient434
    (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hAcell)
    (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB) ja jb
  let Qmajor:=(2*k).natAbs*Nat.ceil (L^(D+1))
  let major:=sourceCircleRationalArcs434 Qmajor (L^cfg.Carc/Hp)
  let M : C(AddCircle (1:ℝ),ℂ):=
    ⟨fun theta=>parityActualCellCoupledKernel434 L J m hmJ nu hAcell hB rank (-xi3) Z k s theta,
      parity_actual_cell_coupled_kernel_continuous434 L J m hmJ nu hAcell hB rank (-xi3) Z k s⟩
  have hRank : rank∈parityCanonicalRankIndices434 m nu Qcomp hAcell hB xi
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L):=
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨ha,hca⟩,
      Finset.mem_product.mpr ⟨hb,hcb⟩⟩
  have hDen : (Qmajor : ℝ)≤L^cfg.cm:=
    parity_actual_minor_denominator_budget434 L Ck D cm hL hD hcm k hKcap
  have hMajorBound:=
    (hArcL.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi hhA hhB hxi hA1 hB1
      ja jb ha hb band hband slot delta freq k hk hKcap chi rho xi1 xi2 xi3 sigma s
      hrho hxi1 hxi2 hxi3 hsigma hsTail prime lFine uFine a b hFineLow hl hu hub
      Qcomp aux hAux hAuxA hAuxB ca cb tw Qmajor hDen).2.2
  have hGlobalBound:=
    (hGlobalL.2.2 eta hSupp hNorm hFamily Z hZlo hZhi J m hmJ hmm nu hnu hAcell hB xi
      hhA hhB hxi hA1 hB1 ja jb ha hb band hband slot delta freq k hk hKcap
      chi rho xi1 xi2 xi3 sigma s (-xi3) prime lFine uFine a b hFineLow hl hu hub
      Qcomp ca cb tw).2.2.1
  have hLp : 0<L:=by linarith
  have hco : 0≤ coeff:=
    (source_original_two_cell_coefficient_bound434
      (sourceOriginalProbeCellA434 m (sourceNativeOriginalTb434 20 L)
        (sourceNativeOriginalVbig434 20 L) nu hAcell)
      (sourceOriginalProbeCellB434 m (sourceNativeOriginalTb434 20 L)
        (sourceNativeOriginalVbig434 20 L) nu hB) ja jb xi hxi
      ((source_original_probe_active_cell_A_mem_iff434 m _ _ nu hAcell xi hhA hxi ja).mp ha)
      ((source_original_probe_active_cell_B_mem_iff434 m _ _ nu hB xi hhB hxi jb).mp hb)).1
  have hMin : ∀ theta,theta∉major → ‖M theta‖≤ coeff*L^(-minorSaving):=by
    intro theta hOutside
    obtain ⟨t,ht⟩:=Quotient.exists_rep theta
    subst theta
    exact hMinorL J m hmJ hmm nu hnu Qcomp hAcell hB xi hhA hA1 hhB hB1 hxi
      rank hRank (-xi3) Z k hk s t hOutside
  have hBound:=parity_circle_product_major_minor434 first second M major
    (source_circle_rational_arcs_measurable434 Qmajor (L^cfg.Carc/Hp))
    (coeff*L^(-minorSaving)) (2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving))
    (Kglobal*L^(parityGlobalMarkExponent434 mmax))
    (mul_nonneg hco (Real.rpow_nonneg hLp.le _))
    (fun theta=>parity_actual_cell_coupled_kernel_norm434
      L J m hmJ nu hnu hAcell hB rank (-xi3) Z k s theta)
    hMin hMajorBound hGlobalBound
  have hPower : L^(-minorSaving)*L^(parityGlobalMarkExponent434 mmax)=
      L^(parityGlobalMarkExponent434 mmax-minorSaving):=by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hFactor : (coeff*L^(-minorSaving))*(Kglobal*L^(parityGlobalMarkExponent434 mmax))=
      coeff*Kglobal*L^(parityGlobalMarkExponent434 mmax-minorSaving):=by
    calc
      _=(coeff*Kglobal)*(L^(-minorSaving)*L^(parityGlobalMarkExponent434 mmax)):=by ring
      _=_:=by rw [hPower]
  exact hBound.trans_eq (congrArg
    (fun t : ℝ=>2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving)+t) hFactor)

/-- The original actual source contract, with one precision choice before the fine parameters. -/
theorem parity_eventually_B633_actual_coupled_family_bound_common_precision434
    (jQ mmax cm : ℕ)
    (CZ Carc Cchi Ck majorSaving Cfreq Ftail minorSaving D CQ Cxi : ℝ)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hD : 0 ≤ D)
    (hMinorSaving : 2*minorSaving+2+2*(parityCellKernelMomentExponent434 mmax : ℝ) ≤ D)
    (hcm : Ck+D+3 ≤ (cm : ℝ))
    (hCarc : (cm : ℝ) ≤ Carc) (hCchi : (cm : ℝ) ≤ Cchi) (hCchiPos : 0<Cchi)
    (hMinorArc : D+2 ≤ Carc) :
    let s0:=⌈Cfreq+1⌉₊
    let s1:=⌈Cfreq⌉₊
    let vexp:=⌈max Cfreq Ftail+1⌉₊
    ∃ (A : ℝ) (hA : 64 ≤ A) (eta : ℝ → ℂ),
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ,eta u≠0 → 1/A ≤ u ∧ u ≤ A) ∧
      (∀ u∈Set.Icc (1/128 : ℝ) (64*Real.exp 2+1),eta u=1) ∧
      (∀ u : ℝ,‖eta u‖ ≤ 1) ∧
      ∃ (K : ℕ → ℝ) (hK : ∀ j,0 ≤ K j),
        (∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ=>eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ=>eta (Real.exp u)/(Real.exp u : ℂ))) ∧
        let cfg0:=parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
          hCarc hCchi hCchiPos 0 (by norm_num) K hK
        let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
        let Kg:=parityGlobalMarkConstant434 mmax
        let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
        0<Kglobal ∧ 0 ≤ parityGlobalMarkExponent434 mmax ∧
        ∃ Karc : ℝ,0<Karc ∧ ∃ B : ℕ,∃ S : ℝ,
          2*((B : ℝ)+1)+3<S ∧
          ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ  ≤  sourceOriginalLiteralDepth 20 L ∧
            ParityB633ActualCoupledCircleFamilyBounds434 cfg eta L jQ mmax CZ Ck S beta gamma
              CQ Cxi majorSaving Karc Cfreq Ftail minorSaving Kglobal := by
  dsimp only
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,hKglobal,hEglobal,
      Karc,hKarc,B,S,hSB,hCircle⟩:=
    parity_eventually_B633_actual_coupled_circle_bound_common_precision434 jQ mmax cm
      CZ Carc Cchi Ck majorSaving Cfreq Ftail minorSaving D
      hCZ hCk hD hMinorSaving hcm hCarc hCchi hCchiPos hMinorArc
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,hKglobal,hEglobal,
    Karc,hKarc,B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hCircle := hCircle beta gamma hbeta hgamma
  let cfg0:=parityComparisonFixed434 jQ mmax cm ⌈Cfreq+1⌉₊ ⌈Cfreq⌉₊
    ⌈max Cfreq Ftail+1⌉₊ CZ Carc Cchi hCarc hCchi hCchiPos 0 (by norm_num) K hK
  let cfg:=parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  let Kg:=parityGlobalMarkConstant434 mmax
  let Kglobal:=(A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
  let EG:=parityGlobalMarkExponent434 mmax
  filter_upwards [hCircle,parity_eventually_actual_rank_family_power434 CQ Cxi,
    eventually_ge_atTop (1 : ℝ)] with L hCircleL hFamilyPower hL
  refine ⟨hCircleL.1,hCircleL.2.1,?_⟩
  unfold ParityB633ActualCoupledCircleFamilyBounds434
  intro hFamily Z hZlo hZhi J m hmJ hmm h xi hh h1 hxi band hband slot delta freq k hk hKcap
    chi rho xi1 xi2 xi3 sigma prime lFine uFine a b hFineLow hl hu hub Q hQ hXi tw
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E:=b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G:=b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let EF:=(m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  let P:=sourceNativeOriginalTb434 20 L
  let V:=sourceNativeOriginalVbig434 20 L
  let Fam:=sourceOriginalTwoBlockProbePatterns434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m
  let R:=fun nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m=>
    parityCanonicalRankIndices434 m nu Q h h xi P V
  let C:=fun (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (r : ParityPrimitiveRankIndex434 Q)=>
    sourceOriginalTwoCellCoefficient434 (sourceOriginalProbeCellA434 m P V nu h)
      (sourceOriginalProbeCellB434 m P V nu h) r.1.1 r.2.1
  let N:=parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let Hp:=fun r : ParityPrimitiveRankIndex434 Q=>
    Real.exp ((r.1.1 : ℝ)*h)*Real.exp ((r.2.1 : ℝ)*h)
  let first:=fun (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (r : ParityPrimitiveRankIndex434 Q) (s : ℝ)=>
    sourceNatFourierPoly N (parityMellinFourierFirst434 s
      (fun n=>eta ((n : ℝ)/(Z*Hp r))*
        parityActualRankEndpoint434 L hFamily J m hmJ nu h h r (1/2) E (-(rho+xi3)) tw true n))
  let second:=fun (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (r : ParityPrimitiveRankIndex434 Q)=>
    sourceNatFourierPoly N (fun n=>eta ((n : ℝ)/(Z*Hp r))*
      parityActualRankEndpoint434 L hFamily J m hmJ nu h h r (1/2) G (-rho) tw false n)
  let I:=fun (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
      (r : ParityPrimitiveRankIndex434 Q) (s : ℝ)=>
    ∫ theta : AddCircle (1 : ℝ),
      parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta*
        star (first nu r s theta)*second nu r theta ∂AddCircle.haarAddCircle
  let amplitude:=parityActualCellCoupledCircleFamily434 L hFamily J m hmJ Q h xi rho xi3 Ck Z k E G tw eta
  have h2 : (2*k)≠0:=mul_ne_zero (by norm_num) hk
  have hAmp (s : ℝ) : amplitude s=∑ nu∈Fam,∑ r∈R nu,I nu r s:=by
    simp only [amplitude,parityActualCellCoupledCircleFamily434,h2,ite_false]
    change (∑ nu : ↥Fam,∑ r∈R nu.val,I nu.val r s)=_
    exact Finset.sum_coe_sort Fam (fun nu=>∑ r∈R nu,I nu r s)
  have hTriangle (s : ℝ) : ‖amplitude s‖ ≤ ∑ nu∈Fam,∑ r∈R nu,‖I nu r s‖:=by
    rw [hAmp]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun nu hnu=>norm_sum_le _ _))
  have hBudgets:=hFamilyPower m Q (fun _=>h) (fun _=>h)
    (fun nu hnu=>hh) (fun nu hnu=>hh) xi hxi hQ hXi
  have hLp : 0<L:=by linarith
  have hCount : (∑ nu∈Fam,((R nu).card : ℝ)) ≤ L^(EF+4*CQ+2*Cxi):=hBudgets.1
  have hCost : (∑ nu∈Fam,∑ r∈R nu,C nu r) ≤ L^(EF+4*CQ+4*Cxi):=hBudgets.2
  have hGlobalEach (nu) (hnu : nu∈Fam) (r) (hr : r∈R nu) (s : ℝ) :
      ‖I nu r s‖ ≤ Kglobal*L^EG:=by
    obtain ⟨hra,hrb⟩:=Finset.mem_product.mp hr
    obtain ⟨ha,hca⟩:=Finset.mem_product.mp hra
    obtain ⟨hb,hcb⟩:=Finset.mem_product.mp hrb
    have hi:=(hCircleL.2.2.1 eta hSupp hNorm hFamily Z hZlo hZhi J m hmJ hmm nu hnu h h xi
      hh hh hxi h1 h1 r.1.1 r.2.1 ha hb band hband slot delta freq k hk hKcap
      chi rho xi1 xi2 xi3 sigma s (-xi3) prime lFine uFine a b hFineLow hl hu hub
      Q r.1.2 r.2.2 tw).2.2.2
    change ‖∫ theta : AddCircle (1 : ℝ),
      star (first nu r s theta)*second nu r theta*
        parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta
          ∂AddCircle.haarAddCircle‖ ≤ Kglobal*L^EG at hi
    calc
      ‖I nu r s‖ = ‖∫ theta : AddCircle (1 : ℝ),
          star (first nu r s theta)*second nu r theta*
            parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta
              ∂AddCircle.haarAddCircle‖ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun theta=>by
          change parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta*
            star (first nu r s theta)*second nu r theta =
            star (first nu r s theta)*second nu r theta*
            parityActualCellCoupledKernel434 L J m hmJ nu h h r (-xi3) Z k s theta
          ring)
      _ ≤ Kglobal*L^EG := hi
  constructor
  · intro s
    calc
      ‖amplitude s‖ ≤ ∑ nu∈Fam,∑ r∈R nu,Kglobal*L^EG:=
        (hTriangle s).trans (Finset.sum_le_sum (fun nu hnu=>
          Finset.sum_le_sum (fun r hr=>hGlobalEach nu hnu r hr s)))
      _=(∑ nu∈Fam,((R nu).card : ℝ))*(Kglobal*L^EG):=by
        simp only [Finset.sum_const,nsmul_eq_mul,←Finset.sum_mul]
      _ ≤ L^(EF+4*CQ+2*Cxi)*(Kglobal*L^EG):=
        mul_le_mul_of_nonneg_right hCount (mul_nonneg hKglobal.le (Real.rpow_nonneg hLp.le _))
      _=Kglobal*L^(EG+EF+4*CQ+2*Cxi):=by
        calc
          _=Kglobal*(L^(EF+4*CQ+2*Cxi)*L^EG):=by ring
          _=_:=by rw [←Real.rpow_add hLp];congr 1;ring
  · intro hrho hxi1 hxi2 hxi3 hsigma s hsTail
    let BM:=2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving)
    let BN:=Kglobal*L^(EG-minorSaving)
    have hBM : 0 ≤ BM:=by dsimp [BM];positivity
    have hBN : 0 ≤ BN:=mul_nonneg hKglobal.le (Real.rpow_nonneg hLp.le _)
    have hLowEach (nu) (hnu : nu∈Fam) (r) (hr : r∈R nu) :
        ‖I nu r s‖ ≤ BM+C nu r*BN:=by
      obtain ⟨hra,hrb⟩:=Finset.mem_product.mp hr
      obtain ⟨ha,hca⟩:=Finset.mem_product.mp hra
      obtain ⟨hb,hcb⟩:=Finset.mem_product.mp hrb
      have hi:=hCircleL.2.2.2 hFamily Z hZlo hZhi J m hmJ hmm nu hnu h h xi
        hh hh hxi h1 h1 r.1.1 r.2.1 ha hb band hband slot delta freq k hk hKcap
        chi rho xi1 xi2 xi3 sigma s hrho hxi1 hxi2 hxi3 hsigma hsTail
        prime lFine uFine a b hFineLow hl hu hub Q r.1.2 r.2.2 hca hcb tw
      change ‖I nu r s‖ ≤ BM+(C nu r*Kglobal)*L^(EG-minorSaving) at hi
      simpa only [BN,mul_assoc] using hi
    calc
      ‖amplitude s‖ ≤ ∑ nu∈Fam,∑ r∈R nu,(BM+C nu r*BN):=
        (hTriangle s).trans (Finset.sum_le_sum (fun nu hnu=>
          Finset.sum_le_sum (fun r hr=>hLowEach nu hnu r hr)))
      _=(∑ nu∈Fam,((R nu).card : ℝ))*BM+(∑ nu∈Fam,∑ r∈R nu,C nu r)*BN:=by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.sum_mul]
      _ ≤ L^(EF+4*CQ+2*Cxi)*BM+L^(EF+4*CQ+4*Cxi)*BN:=
        add_le_add (mul_le_mul_of_nonneg_right hCount hBM) (mul_le_mul_of_nonneg_right hCost hBN)
      _=2*Karc*L^(2*(cfg.cm : ℝ)-majorSaving+EF+4*CQ+2*Cxi)+
          Kglobal*L^(EG-minorSaving+EF+4*CQ+4*Cxi):=by
        dsimp only [BM,BN]
        have hM : L^(EF+4*CQ+2*Cxi)*L^(2*(cfg.cm : ℝ)-majorSaving)=
            L^(2*(cfg.cm : ℝ)-majorSaving+EF+4*CQ+2*Cxi):=by
          rw [←Real.rpow_add hLp];congr 1;ring
        have hN : L^(EF+4*CQ+4*Cxi)*L^(EG-minorSaving)=
            L^(EG-minorSaving+EF+4*CQ+4*Cxi):=by
          rw [←Real.rpow_add hLp];congr 1;ring
        calc
          _=(2*Karc)*(L^(EF+4*CQ+2*Cxi)*L^(2*(cfg.cm : ℝ)-majorSaving))+
              Kglobal*(L^(EF+4*CQ+4*Cxi)*L^(EG-minorSaving)):=by ring
          _=_:=by rw [hM,hN]

/-- The original actual source contract, with one precision choice before the fine parameters. -/
theorem parity_eventually_B633_actual_rank_main_saving_common_precision434
    (jQ mmax : ℕ)
    (targetSaving Cpsi Ftail Cfreq CZ Ck CQ Cxi : ℝ) (Kpsi : ℕ → ℝ)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j,0 ≤ Kpsi j) (hCF : Cpsi < Ftail)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∃ B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ (beta gamma : ℝ), 0 < beta → 0 < gamma →
          ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ParityB633ActualRankMainSaving434 L jQ mmax CZ Ck S beta gamma
          targetSaving Cfreq CQ Cxi Cpsi Kpsi := by
  let lowSaving := b662CutoffSavingExponent434 targetSaving Cpsi
  let EFmax := (mmax : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  let Eglobal := parityGlobalMarkExponent434 mmax
  let minorSaving := max 0 (Eglobal+EFmax+4*CQ+4*Cxi+lowSaving+2)
  let D := 2*minorSaving+2+2*(parityCellKernelMomentExponent434 mmax : ℝ)
  let cm := Nat.ceil (Ck+D+3)
  let Carc := (cm : ℝ)+D+2
  let Cchi := (cm : ℝ)+1
  let majorSaving := 2*(cm : ℝ)+EFmax+4*CQ+2*Cxi+lowSaving+2
  let Cglobal := Eglobal+EFmax+4*CQ+2*Cxi+1
  have hMinor0 : 0 ≤ minorSaving := le_max_left _ _
  have hMoment0 : 0 ≤ (parityCellKernelMomentExponent434 mmax : ℝ) := Nat.cast_nonneg _
  have hD : 0 ≤ D := by dsimp only [D]; linarith
  have hCm0 : 0 ≤ (cm : ℝ) := Nat.cast_nonneg _
  have hcm : Ck+D+3 ≤ (cm : ℝ) := Nat.le_ceil _
  have hCarc : (cm : ℝ) ≤ Carc := by dsimp only [Carc]; linarith
  have hCchi : (cm : ℝ) ≤ Cchi := by dsimp only [Cchi]; linarith
  have hCchiPos : 0 < Cchi := by dsimp only [Cchi]; linarith
  have hMinorArc : D+2 ≤ Carc := by dsimp only [Carc]; linarith
  have hMinorPrec : 2*minorSaving+2+2*(parityCellKernelMomentExponent434 mmax : ℝ) ≤ D := le_rfl
  have hFamily := parity_eventually_B633_actual_coupled_family_bound_common_precision434
    jQ mmax cm CZ Carc Cchi Ck majorSaving Cfreq Ftail minorSaving D CQ Cxi
    hCZ hCk hD hMinorPrec hcm hCarc hCchi hCchiPos hMinorArc
  dsimp only at hFamily
  obtain ⟨A,hA,eta,hEtaSmooth,hEtaSupport,hEtaOne,hEtaNorm,Keta,hKeta,hEtaBudget,
    hKglobal,hEglobal,Karc,hKarc,B,S,hSB,hFull⟩ := hFamily
  let Kg := parityGlobalMarkConstant434 mmax
  let Kglobal := (A*Kg)^2*(A+1)*(1+(Real.log (A+1)+3/2))^16
  have hKglobal' : 0 < Kglobal := hKglobal
  have hMajorAllocation : 2*(cm : ℝ)+EFmax+4*CQ+2*Cxi+lowSaving+2 ≤ majorSaving := le_rfl
  have hMinorAllocation : Eglobal+EFmax+4*CQ+4*Cxi+lowSaving+2 ≤ minorSaving := le_max_right _ _
  have hMellin := parity_eventually_actual_main_mellin_transfer434 targetSaving Cpsi Ftail Cglobal
    CZ Ck Kpsi hCpsi hKpsi hCF hCZ hCk
  refine ⟨B,S,hSB,?_⟩
  intro beta gamma hbeta hgamma
  have hFull := hFull beta gamma hbeta hgamma
  filter_upwards [hFull,hMellin,eventually_ge_atTop (max 2 (2*Karc+Kglobal))]
    with L hFullL hTransfer hLarge
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hLarge
  have hKL : 2*Karc+Kglobal ≤ L := (le_max_right _ _).trans hLarge
  refine ⟨hFullL.1,hFullL.2.1,?_⟩
  unfold ParityB633ActualRankMainSaving434
  intro hS Z hZlo hZhi J m hmJ hmm h xi hh h1 hxi band hband slot delta freq k hk hK
    chi rho xi1 xi2 xi3 sigma prime lFine uFine a b hFine hl hu hub Q hQ hX tw
    hrho hxi1 hxi2 hxi3 hsigma psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let EF := (m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  have hEF : EF ≤ EFmax := parity_rank_family_exponent_mono434 m mmax hmm
  have hAbsorb := parity_coupled_family_power_absorb434 L lowSaving Eglobal EF EFmax CQ Cxi
    (cm : ℝ) majorSaving minorSaving Karc Kglobal hL2 hEF hKarc.le hKglobal'.le hKL
    hMajorAllocation hMinorAllocation
  have hPair := hFullL.2.2 hS Z hZlo hZhi J m hmJ hmm h xi hh h1 hxi band hband
    slot delta freq k hk hK chi rho xi1 xi2 xi3 sigma prime lFine uFine a b
    hFine hl hu hub Q hQ hX tw
  dsimp only at hPair
  have hLow (s : ℝ) (hs : |s| ≤ L^Ftail) :
      ‖parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k Ecore Gcore tw eta s‖ ≤
        L^(-b662CutoffSavingExponent434 targetSaving Cpsi) := by
    exact (hPair.2 hrho hxi1 hxi2 hxi3 hsigma s hs).trans hAbsorb.1
  have hAll (s : ℝ) :
      ‖parityActualCellCoupledCircleFamily434 L hS J m hmJ Q h xi rho xi3 Ck Z k Ecore Gcore tw eta s‖ ≤
        L^Cglobal := by
    exact (hPair.1 s).trans hAbsorb.2
  exact hTransfer hS J m hmJ Q h xi rho xi3 Z k h1 hZlo hK Ecore Gcore tw psi eta
    hSmooth hSupport hReg hEtaOne hLow hAll

end Green64Analytic.Parity

end

end

/-! ## ActualCappedRawSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 32000

/-- The genuinely capped literal physical RAW inherits arbitrary inverse-log
saving from the source-signed physical RAW and its quantitative ORIGINAL
Ppart-cap insertion. The shared/free products and the physical endpoint
gates at D_R*w and D_R*w' are left exactly as constructed. This is not
a claim identifying the physical sum with the historical B521 channel. -/
theorem parity_eventually_B633_actual_capped_literal_raw_saving434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        ‖(Z : ℂ)*parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
          (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
          1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)‖
          ≤ Z*L^(-target) := by
  let KH : ℕ → ℝ := sourceNormalizedLogDerivativeConstants 64 Kpsi
  have hKH : ∀ j, 0 ≤ KH j :=
    source_normalized_log_derivative_constants_nonneg 64 Kpsi (by norm_num) hKpsi
  obtain ⟨J,B,S,hSB,hRaw⟩ :=
    parity_eventually_B633_actual_literal_raw_harmonic_saving434 jQ (target+1)
      Cfreq CZ Ck Cpsi beta gamma Kpsi (by linarith) hCZ hCk
      hCpsi hKpsi hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hCap := parity_eventually_actual_literal_raw_cap_outer_Z_saving434
    J S beta gamma CZ Ck Cpsi (KH 0) (target+1)
    hSpos hbeta hgamma hCZ (hKH 0)
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hRaw,hCap,eventually_ge_atTop (2 : ℝ)] with L hRawL hCapL hL2
  refine ⟨hRawL.1,hRawL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let psiH : ℝ → ℂ := fun t => (t : ℂ)*psi t
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let N := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let R := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    N 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH (fun _ _ => 1)
  let T := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    N 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
    (fun n np => 1 - parityOriginalPhysicalPairPcap434 L n np)
  let C := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    N 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
    (parityOriginalPhysicalPairPcap434 L)
  have hLp : 0 < L := by linarith
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hL1 : 1 < L := by linarith
  have hSupportH : ∀ t : ℝ, psiH t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64 := by
    intro t ht
    apply hSupport t
    intro hz
    exact ht (by simp only [psiH,hz,mul_zero])
  have hRegH : sourceLogDerivativeBudget Cpsi KH L
      (fun u => psiH (Real.exp u)) :=
    source_actual_normalized_log_derivative_budget 64 Cpsi L Kpsi psi
      (by norm_num) hCpsi hKpsi hL1.le hSmooth hSupport hReg
  have hSup : ∀ t : ℝ, ‖psiH t‖ ≤ KH 0 * L^Cpsi :=
    parity_original_log_budget_sup434 L Cpsi KH psiH hLp (hKH 0) hSupportH hRegH
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hkBound
  have hR : ‖(Z : ℂ)*R‖ ≤ Z*L^(-(target+1)) :=
    hRawL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  have hT : ‖(Z : ℂ)*T‖ ≤ Z*L^(-(target+1)) := by
    have hTmp := hCapL.2.2 prime lFine uFine hFineLow
      20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
      (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily 0 (Nat.zero_le J) 1 1 1 xi3
      Z k hZlo hZhi hkReal 1 (parityDyadicLimit434 L) tw psiH
      (fun t ht => (hSupportH t ht)) hSup N
    rw [parity_raw_endpoint_weight_physical_aggregate434 L hL1 hFamily
      J 0 (Nat.zero_le J) 1 1 1 (-xi3) Z k N
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
      (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np)] at hTmp
    exact hTmp
  have hC : C = R-T :=
    parity_raw_physical_pcap_difference434 L hFamily J (-xi3) Z k N
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
  have hPower : L*L^(-(target+1)) = L^(-target) := by
    calc
      _ = L^(1+(-(target+1))) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hLp (1 : ℝ) (-(target+1))).symm
      _ = L^(-target) := by congr 1; ring
  change ‖(Z : ℂ)*C‖ ≤ Z*L^(-target)
  calc
    _ = ‖(Z : ℂ)*R-(Z : ℂ)*T‖ := by rw [hC]; congr 1; ring
    _ ≤ ‖(Z : ℂ)*R‖+‖(Z : ℂ)*T‖ := norm_sub_le _ _
    _ ≤ Z*L^(-(target+1))+Z*L^(-(target+1)) := add_le_add hR hT
    _ = Z*(2*L^(-(target+1))) := by ring
    _ ≤ Z*(L*L^(-(target+1))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hLp.le _)) hZ.le
    _ = Z*L^(-target) := by rw [hPower]
end Green64Analytic.Parity

end

end

/-! ## ActualB521SourceSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 32000

/-- Complete actual r20 capped physical RAW is quantitatively close to the
unchanged native original B521 stripped source channel, even though its
physical Ppart caps are imposed at DR*w,DR*wp, not at quotient endpoints.
The bound combines three *independently proved* physical/quotient errors;
it never asserts pointwise equality of those two distinct caps. The same
source channel has arbitrary inverse-log saving. This is a precise
original finite source-channel result, not historical E4.1, TypeII or Green64. -/
theorem parity_eventually_actual_capped_physical_B521_source_saving434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
        let N := parityPositiveNaturalPositions434 positions
        let physical := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
          positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)
        let original := sourceNativeGatedChannel N (sourceOriginalPAllActualBands 20 L)
          (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
          Ecore Gcore k (rho+xi3) (-rho)
          (fun n => if ((n : ℤ)+2*k).toNat∈N then
            (Z : ℂ)⁻¹*psi ((n : ℝ)/Z) else 0) tw tw
        ‖(Z : ℂ)*(physical-original)‖ ≤ Z*L^(-target) ∧
        ‖(Z : ℂ)*original‖ ≤ Z*L^(-target) := by
  let KH : ℕ → ℝ := sourceNormalizedLogDerivativeConstants 64 Kpsi
  have hKH : ∀ j, 0 ≤ KH j :=
    source_normalized_log_derivative_constants_nonneg 64 Kpsi (by norm_num) hKpsi
  obtain ⟨J,B,S,hSB,hRaw⟩ :=
    parity_eventually_B633_actual_literal_raw_harmonic_saving434 jQ (target+1)
      Cfreq CZ Ck Cpsi beta gamma Kpsi (by linarith) hCZ hCk
      hCpsi hKpsi hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hTail := parity_eventually_actual_literal_raw_cap_outer_Z_saving434
    J S beta gamma CZ Ck Cpsi (KH 0) (target+1)
    hSpos hbeta hgamma hCZ (hKH 0)
  have hRest := parity_eventually_actual_physical_raw_stripping434
    J S beta gamma CZ Ck Cpsi (KH 0) (target+1)
    hSpos hbeta hgamma hCZ (hKH 0)
  have hQuot := parity_eventually_actual_normalized_raw_quotient_cap_loss434
    S beta gamma CZ Ck Cpsi (target+1) Kpsi
    hSpos hbeta hgamma hCZ hCpsi hKpsi
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hRaw,hTail,hRest,hQuot,eventually_ge_atTop (3 : ℝ)]
    with L hRawL hTailL hRestL hQuotL hL3
  refine ⟨hRawL.1,hRawL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let psiH : ℝ → ℂ := fun t => (t : ℂ)*psi t
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let N := parityPositiveNaturalPositions434 positions
  let P := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH (fun _ _ => 1)
  let Pc := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
    (parityOriginalPhysicalPairPcap434 L)
  let T := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
    (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np)
  let U := parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw psiH (fun _ _ => 1)
  let C := parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw psiH
    (parityOriginalPhysicalPairPcap434 L)
  let Src := sourceNativeGatedChannel N (sourceOriginalPAllActualBands 20 L)
    (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    E G k (rho+xi3) (-rho)
    (fun n => if ((n : ℤ)+2*k).toNat∈N then
      (Z : ℂ)⁻¹*psi ((n : ℝ)/Z) else 0) tw tw
  have hLp : 0 < L := by linarith
  have hL1 : 1 < L := by linarith
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hSupportH : ∀ t : ℝ, psiH t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64 := by
    intro t ht
    apply hSupport t
    intro hz
    exact ht (by simp only [psiH,hz,mul_zero])
  have hRegH : sourceLogDerivativeBudget Cpsi KH L
      (fun u => psiH (Real.exp u)) :=
    source_actual_normalized_log_derivative_budget 64 Cpsi L Kpsi psi
      (by norm_num) hCpsi hKpsi hL1.le hSmooth hSupport hReg
  have hSup : ∀ t : ℝ, ‖psiH t‖ ≤ KH 0 * L^Cpsi :=
    parity_original_log_budget_sup434 L Cpsi KH psiH hLp (hKH 0) hSupportH hRegH
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hkBound
  have hNpos : ∀ n ∈ N, 0 < n := by
    intro n hn
    exact ((parity_positive_natural_positions_mem434 _ n).mp hn).1
  have hRawSmall : ‖(Z : ℂ)*P‖ ≤ Z*L^(-(target+1)) :=
    hRawL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  have hTailSmall : ‖(Z : ℂ)*T‖ ≤ Z*L^(-(target+1)) := by
    have hTmp := hTailL.2.2 prime lFine uFine hFineLow
      20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
      (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily 0 (Nat.zero_le J) 1 1 1 xi3
      Z k hZlo hZhi hkReal 1 (parityDyadicLimit434 L) tw psiH
      (fun t ht => (hSupportH t ht)) hSup positions
    rw [parity_raw_endpoint_weight_physical_aggregate434 L hL1 hFamily
      J 0 (Nat.zero_le J) 1 1 1 (-xi3) Z k positions
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
      (fun n np => 1-parityOriginalPhysicalPairPcap434 L n np)] at hTmp
    exact hTmp
  have hRestPair := hRestL.2.2 prime lFine uFine hFineLow
      20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
      (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily xi3 Z k hZlo hZhi hkBound tw psiH
      (fun t ht => Set.mem_Icc.mpr (hSupportH t ht)) hSup
  have hRestSmall : ‖(Z : ℂ)*(P-U)‖ ≤ Z*L^(-(target+1)) := hRestPair.2
  have hQuotPair := hQuotL.2.2 prime lFine uFine hFineLow
      20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
      (Finset.Icc a b) (2*k.natAbs) chi 0 0
      xi1 xi2 rho sigma hFamily xi3 Z k hZlo hZhi hkReal
      tw psi hSmooth hSupport hReg positions
  have hQuotSmall : ‖(Z : ℂ)*(U-C)‖ ≤ Z*L^(-(target+1)) := hQuotPair.2
  have hPhysicalCap : Pc=P-T :=
    parity_raw_physical_pcap_difference434 L hFamily J (-xi3) Z k positions
      1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psiH
  have hTailDiff : ‖(Z : ℂ)*(Pc-P)‖ ≤ Z*L^(-(target+1)) := by
    have heq : Pc-P = -T := by rw [hPhysicalCap]; ring
    rw [heq,mul_neg,norm_neg]
    exact hTailSmall
  have hSource : C=Src :=
    parity_raw_stripped_original_B521_normalized434
      L hL1 hFamily rho xi3 Z hZ k hk N hNpos E G tw psi hSupport
  have hPower : L*L^(-(target+1)) = L^(-target) := by
    calc
      _ = L^(1+(-(target+1))) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hLp (1 : ℝ) (-(target+1))).symm
      _ = L^(-target) := by congr 1; ring
  have hBudget : 3*(Z*L^(-(target+1))) ≤ Z*L^(-target) := by
    calc
      _ = Z*(3*L^(-(target+1))) := by ring
      _ ≤ Z*(L*L^(-(target+1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hL3 (Real.rpow_nonneg hLp.le _)) hZ.le
      _ = Z*L^(-target) := by rw [hPower]
  have hBridge : ‖(Z : ℂ)*(Pc-C)‖ ≤ Z*L^(-target) := by
    have heq : Pc-C = (Pc-P)+(P-U)+(U-C) := by ring
    rw [heq,mul_add,mul_add]
    have hTrip := (norm_add_le ((Z : ℂ)*(Pc-P)+(Z : ℂ)*(P-U)) ((Z : ℂ)*(U-C)))
    have hDuo := (norm_add_le ((Z : ℂ)*(Pc-P)) ((Z : ℂ)*(P-U)))
    have hBound : ‖(Z : ℂ)*(Pc-P)+(Z : ℂ)*(P-U)+(Z : ℂ)*(U-C)‖ ≤
        3*(Z*L^(-(target+1))) := by
      calc
        _ ≤ ‖(Z : ℂ)*(Pc-P)+(Z : ℂ)*(P-U)‖+‖(Z : ℂ)*(U-C)‖ := hTrip
        _ ≤ (‖(Z : ℂ)*(Pc-P)‖+‖(Z : ℂ)*(P-U)‖)+‖(Z : ℂ)*(U-C)‖ :=
          add_le_add_left hDuo _
        _ ≤ 3*(Z*L^(-(target+1))) := by linarith
    exact hBound.trans hBudget
  have hSourceSmall : ‖(Z : ℂ)*C‖ ≤ Z*L^(-target) := by
    have heq : C = P-(P-U)-(U-C) := by ring
    rw [heq,mul_sub,mul_sub]
    have hTrip := norm_sub_le ((Z : ℂ)*P-(Z : ℂ)*(P-U)) ((Z : ℂ)*(U-C))
    have hDuo := norm_sub_le ((Z : ℂ)*P) ((Z : ℂ)*(P-U))
    have hBound : ‖(Z : ℂ)*P-(Z : ℂ)*(P-U)-(Z : ℂ)*(U-C)‖ ≤
        3*(Z*L^(-(target+1))) := by
      calc
        _ ≤ ‖(Z : ℂ)*P-(Z : ℂ)*(P-U)‖+‖(Z : ℂ)*(U-C)‖ := hTrip
        _ ≤ (‖(Z : ℂ)*P‖+‖(Z : ℂ)*(P-U)‖)+‖(Z : ℂ)*(U-C)‖ :=
          add_le_add_left hDuo _
        _ ≤ 3*(Z*L^(-(target+1))) := by linarith
    exact hBound.trans hBudget
  change ‖(Z : ℂ)*(Pc-Src)‖ ≤ Z*L^(-target) ∧
    ‖(Z : ℂ)*Src‖ ≤ Z*L^(-target)
  rw [←hSource]
  exact ⟨hBridge,hSourceSmall⟩
end Green64Analytic.Parity

end

end

/-! ## RawSourceCarrier -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 30000

/-- Finite support transport from the complete positive double carrier
to the independently existing original B521 channel. Every discarded
term has zero ORIGINAL cutoff; the signed target indicator is removed
only after proving the actual shifted endpoint belongs to the carrier. -/
theorem parity_raw_source_channel_support434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (rho xi3 Z : ℝ) (k : ℤ) (hk : k≠0)
    (N S : Finset ℕ) (hN : ∀ n∈N,0<n) (hSN : S⊆N)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (hCut : ∀ n∈N,n∉S → psi ((n : ℝ)/Z)=0)
    (hShift : ∀ n∈N,0<(n : ℤ)+2*k → psi ((n : ℝ)/Z)≠0 →
      ((n : ℤ)+2*k).toNat∈N) :
    parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw psi
        (parityOriginalPhysicalPairPcap434 L) =
      sourceNativeGatedChannel S (sourceOriginalPAllActualBands 20 L)
        (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
        F G k (rho+xi3) (-rho) (fun n=>psi ((n : ℝ)/Z)/(n : ℂ)) tw tw := by
  rw [parity_raw_stripped_original_B521_channel434 L hL hS rho xi3 Z k hk N hN F G tw psi]
  unfold sourceNativeGatedChannel
  calc
    _ = ∑ n∈N,
      sourceNativeGatedGramKernel (sourceOriginalPAllActualBands 20 L)
        (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
        F G k (rho+xi3) (-rho) (fun n=>psi ((n : ℝ)/Z)/(n : ℂ)) n *
        ((groupSign (sourceOriginalPAllActualBands 20 L) tw n*
          groupSign (sourceOriginalPAllActualBands 20 L) tw (((n : ℤ)+2*k).toNat) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases ht : ((n : ℤ)+2*k).toNat∈N
      · simp only [sourceNativeGatedGramKernel,ht,ite_true]
      · by_cases hs : 0<(n : ℤ)+2*k
        · have hz : psi ((n : ℝ)/Z)=0 := by
            by_contra hz
            exact ht (hShift n hn hs hz)
          simp only [sourceNativeGatedGramKernel,ht,hz,ite_false,zero_div,zero_mul,ite_self]
        · simp only [sourceNativeGatedGramKernel,hs,false_and,ite_false,zero_mul]
    _ = _ := by
      symm
      apply Finset.sum_subset hSN
      intro n hn hnot
      simp only [sourceNativeGatedGramKernel,hCut n hn hnot,zero_div,zero_mul,ite_self]

/-- The already proved original harmonic scale budget puts every true
cutoff source and its positive signed2k target into the original B654
window. The source interval is EXACTLY Icc1 floor(64Z), not an enlarged
surrogate. The threshold is independent of J and all endpoint data. -/
theorem parity_eventually_raw_source_support434 (CZ Ck : ℝ) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop,1<L ∧
    ∀ (J : ℕ) (Z : ℝ),Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
    ∀ k : ℤ,(k.natAbs : ℝ)≤L^Ck →
    let N := parityPositiveNaturalPositions434
      (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
    let S := Finset.Icc 1 ⌊64*Z⌋₊
    0<Z ∧ S⊆N ∧
    ∀ psi : ℝ→ℂ,(∀ t,psi t≠0 → (1/64 : ℝ)≤t ∧ t≤64) →
      (∀ n∈N,n∉S → psi ((n : ℝ)/Z)=0) ∧
      (∀ n∈N,0<(n : ℤ)+2*k → psi ((n : ℝ)/Z)≠0 →
        ((n : ℤ)+2*k).toNat∈N) := by
  filter_upwards [parity_eventually_harmonic_scale_budget434 CZ Ck hCZ,
    eventually_gt_atTop (1 : ℝ)] with L hBudget hL
  refine ⟨hL,?_⟩
  intro J Z hZlo hZhi k hk
  dsimp only
  have hLp : 0<L := by linarith
  have hkR : |(k : ℝ)|≤L^Ck := by simpa only [Nat.cast_natAbs,Int.cast_abs] using hk
  have hOne : (1 : ℝ)≤Real.exp (Real.sqrt L) := by
    rw [←Real.exp_zero]
    exact Real.exp_le_exp.mpr (Real.sqrt_nonneg L)
  have hB := hBudget.2 Z hZlo hZhi 1 (by norm_num) (by simpa only [Nat.cast_one] using hOne) k hkR
  simp only [Nat.cast_one,Int.cast_one,mul_one] at hB
  have hZ : 0<Z := by linarith [hB.1]
  have hCapPos : 0<(⌈65*Z⌉₊ : ℝ) :=
    (by positivity : 0<65*Z).trans_le (Nat.le_ceil _)
  have hCap : (⌈65*Z⌉₊ : ℝ)≤Real.exp (2*L) := by
    calc
      _ = Real.exp (Real.log (⌈65*Z⌉₊ : ℝ)) := (Real.exp_log hCapPos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hB.2.2
  have hSubset := parity_actual_comparison_cap_subset434 J Ck L hLp _ hCap
  have hFloor : (⌊64*Z⌋₊ : ℝ)≤64*Z := Nat.floor_le (by positivity)
  have hSN : Finset.Icc 1 ⌊64*Z⌋₊ ⊆ parityPositiveNaturalPositions434
      (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)) := by
    intro n hn
    apply hSubset
    have hnI := Finset.mem_Icc.mp hn
    apply Finset.mem_Icc.mpr
    refine ⟨hnI.1,?_⟩
    have hnR : (n : ℝ)≤(⌈65*Z⌉₊ : ℝ) :=
      ((show (n : ℝ)≤(⌊64*Z⌋₊ : ℝ) by exact_mod_cast hnI.2).trans hFloor).trans
        ((show 64*Z≤65*Z by linarith).trans (Nat.le_ceil _))
    exact_mod_cast hnR
  refine ⟨hZ,hSN,?_⟩
  intro psi hSupp
  constructor
  · intro n hn hnot
    by_contra hpsi
    apply hnot
    have hn0 := ((parity_positive_natural_positions_mem434 _ n).mp hn).1
    have hn64 : (n : ℝ)≤64*Z := (div_le_iff₀ hZ).mp (hSupp _ hpsi).2
    exact Finset.mem_Icc.mpr ⟨by omega,(Nat.le_floor_iff (by positivity)).mpr hn64⟩
  · intro n hn hpos hpsi
    let np := ((n : ℤ)+2*k).toNat
    have hnp : 0<np := by dsimp [np];omega
    have hcast : (np : ℤ)=(n : ℤ)+2*k := by dsimp [np];omega
    have hcastR : (np : ℝ)=(n : ℝ)+(2*k : ℤ) := by exact_mod_cast hcast
    have hn64 : (n : ℝ)≤64*Z := (div_le_iff₀ hZ).mp (hSupp _ hpsi).2
    have hnp65 : (np : ℝ)≤65*Z := by
      have hstep := le_abs_self ((2*k : ℤ) : ℝ)
      linarith [hB.2.1]
    apply hSubset
    apply Finset.mem_Icc.mpr
    exact ⟨by omega,by exact_mod_cast hnp65.trans (Nat.le_ceil (65*Z))⟩

/-- Actual r20 source-channel equality with all carrier and cutoff
conditions discharged from the ORIGINAL Z/k ranges. This identifies
the stripped capped RAW functional with the exact existing B521 channel;
it does not identify the un-restored physical shared sum with that channel. -/
theorem parity_eventually_raw_original_B521_channel434 (CZ Ck : ℝ) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop,1<L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (J : ℕ) (rho xi3 Z : ℝ),Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
    ∀ k : ℤ,k≠0 → (k.natAbs : ℝ)≤L^Ck →
    ∀ (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ),
      (∀ t,psi t≠0 → (1/64 : ℝ)≤t ∧ t≤64) →
      parityRawStrippedHarmonic434 L hS rho xi3 Z k
        (parityPositiveNaturalPositions434
          (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))) F G tw psi
          (parityOriginalPhysicalPairPcap434 L) =
        sourceNativeGatedChannel (Finset.Icc 1 ⌊64*Z⌋₊) (sourceOriginalPAllActualBands 20 L)
          (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
          F G k (rho+xi3) (-rho) (fun n=>psi ((n : ℝ)/Z)/(n : ℂ)) tw tw := by
  filter_upwards [parity_eventually_raw_source_support434 CZ Ck hCZ] with L hL
  refine ⟨hL.1,?_⟩
  intro hS J rho xi3 Z hZlo hZhi k hk hK F G tw psi hSupp
  have hData := hL.2 J Z hZlo hZhi k hK
  dsimp only at hData
  have hCuts := hData.2.2 psi hSupp
  exact parity_raw_source_channel_support434 L hL.1 hS rho xi3 Z k hk _ _
    (fun n hn=>((parity_positive_natural_positions_mem434 _ n).mp hn).1)
    hData.2.1 F G tw psi hCuts.1 hCuts.2
end Green64Analytic.Parity

end

end

/-! ## Eq417FiniteUngated -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- The literal ungated Parity (4.17) source: both genuine W1 marks and same parity twist,
with signed 2*k and the conjugated E-input first core. No Ppart truncation. -/
def parityOriginalEq417Ungated434
    (L rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ → ℂ) : ℂ :=
  ∑ z ∈ N,
    if 0 < (z : ℤ)+2*k then
      let zp := ((z : ℤ)+2*k).toNat
      psi ((z : ℝ)/Z) * imaginaryPower z (rho+xi3) *
        imaginaryPower zp (-rho) *
        star (primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z) *
        primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G zp *
        ((groupSign (sourceOriginalPAllActualBands 20 L) tw z *
          groupSign (sourceOriginalPAllActualBands 20 L) tw zp : ℝ) : ℂ) *
        ((sourceMarkedWeight (1/2 : ℝ) 1 (sourceOriginalPAllActualBands 20 L) z *
          sourceMarkedWeight (1/2 : ℝ) 1 (sourceOriginalPAllActualBands 20 L) zp : ℝ) : ℂ)
    else 0

/-- An exact normalization equality, including zero, with one outside Z. -/
theorem parity_raw_original_Z_cancels434
    (Z : ℝ) (hZ : 0 < Z) (psi : ℝ → ℂ)
    (hSupport : ∀ t,psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64)
    (n : ℕ) :
    (Z : ℂ) * (((((n : ℝ)/Z : ℝ) : ℂ)*psi ((n : ℝ)/Z))/(n : ℂ)) =
      psi ((n : ℝ)/Z) := by
  rw [parity_raw_original_normalized_source_coefficient434 Z hZ psi hSupport n]
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  simp [hZc]

/-- Every actual original W1 factor is kept. The only support hypothesis
is that nonzero source cutoff terms have their signed target in N. -/
theorem parity_raw_stripped_uncapped_exact_eq417434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (rho xi3 Z : ℝ) (hZ : 0 < Z) (k : ℤ) (hk : k ≠ 0)
    (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (hSupport : ∀ t,psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64)
    (hShift : ∀ n∈N, 0 < (n : ℤ)+2*k → psi ((n : ℝ)/Z) ≠ 0 →
      ((n : ℤ)+2*k).toNat ∈ N) :
    (Z : ℂ) * parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw
      (fun t => (t : ℂ)*psi t) (fun _ _ => 1) =
    parityOriginalEq417Ungated434 L rho xi3 Z k N F G tw psi := by
  unfold parityRawStrippedHarmonic434
  simp only [one_mul]
  rw [parity_raw_positive_pair_collapse434 N hN k hk]
  rw [Finset.mul_sum]
  unfold parityOriginalEq417Ungated434
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : 0 < (n : ℤ)+2*k
  · by_cases ht : ((n : ℤ)+2*k).toNat ∈ N
    · simp only [hp,ht,and_self,ite_true]
      rw [parity_raw_stripped_original_arithmetic434 L rho xi3 Z F G tw
        (fun t => (t : ℂ)*psi t) n ((n : ℤ)+2*k).toNat]
      rw [parity_actual_raw_stripped_source_weight434 L hL hS n ((n : ℤ)+2*k).toNat]
      have hcoef := parity_raw_original_Z_cancels434 Z hZ psi hSupport n
      calc
        _ = ((Z : ℂ) *
          (((((n : ℝ)/Z : ℝ) : ℂ)*psi ((n : ℝ)/Z))/(n : ℂ))) *
          (imaginaryPower n (rho+xi3) *
           imaginaryPower (((n : ℤ)+2*k).toNat) (-rho) *
           star (primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F n) *
           primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G (((n : ℤ)+2*k).toNat) *
           ((groupSign (sourceOriginalPAllActualBands 20 L) tw n *
             groupSign (sourceOriginalPAllActualBands 20 L) tw (((n : ℤ)+2*k).toNat) : ℝ) : ℂ) *
           ((sourceMarkedWeight (1/2 : ℝ) 1 (sourceOriginalPAllActualBands 20 L) n *
             sourceMarkedWeight (1/2 : ℝ) 1 (sourceOriginalPAllActualBands 20 L)
               (((n : ℤ)+2*k).toNat) : ℝ) : ℂ)) := by ring
        _ = _ := by rw [hcoef]; ring
    · have hz : psi ((n : ℝ)/Z)=0 := by
        by_contra hne
        exact ht (hShift n hn hp hne)
      simp [hp,ht,hz]
  · simp [hp]

/-- Restrict the uncapped literal (4.17) source to the actual original
cutoff support. The original marked weights and endpoints do not change. -/
theorem parity_original_eq417_ungated_restrict434
    (L rho xi3 Z : ℝ) (k : ℤ) (N S : Finset ℕ)
    (hSN : S ⊆ N) (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (hCut : ∀ n∈N,n∉S → psi ((n : ℝ)/Z)=0) :
    parityOriginalEq417Ungated434 L rho xi3 Z k N F G tw psi =
    parityOriginalEq417Ungated434 L rho xi3 Z k S F G tw psi := by
  unfold parityOriginalEq417Ungated434
  symm
  apply Finset.sum_subset hSN
  intro n hn hnot
  simp [hCut n hn hnot]
end Green64Analytic.Parity

end

end

/-! ## Eq417ActualUngated -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- The actual original cutoff and signed-shift geometry identify the
uncapped stripped normalized RAW exactly with literal Parity (4.17) on
Icc 1 floor(64Z), with NO extra Ppart gate or target-carrier mask. -/
theorem parity_eventually_raw_original_ungated_eq417434
    (CZ Ck : ℝ) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop, 1 < L ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (J : ℕ) (rho xi3 Z : ℝ),
        Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
      ∀ k : ℤ, k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
      ∀ (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ),
        (∀ t,psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
        (Z : ℂ)*parityRawStrippedHarmonic434 L hS rho xi3 Z k
          (parityPositiveNaturalPositions434
            (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)))
          F G tw (fun t => (t : ℂ)*psi t) (fun _ _ => 1) =
        parityOriginalEq417Ungated434 L rho xi3 Z k (Finset.Icc 1 ⌊64*Z⌋₊)
          F G tw psi := by
  filter_upwards [parity_eventually_raw_source_support434 CZ Ck hCZ] with L hSupp
  refine ⟨hSupp.1,?_⟩
  intro hS J rho xi3 Z hZlo hZhi k hk hK F G tw psi hSupport
  have hData := hSupp.2 J Z hZlo hZhi k hK
  dsimp only at hData
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let S := Finset.Icc 1 ⌊64*Z⌋₊
  have hN : ∀ n ∈ N,0<n := by
    intro n hn
    exact ((parity_positive_natural_positions_mem434 _ n).mp hn).1
  have hCuts := hData.2.2 psi hSupport
  have heq := parity_raw_stripped_uncapped_exact_eq417434 L hSupp.1 hS
    rho xi3 Z hData.1 k hk N hN F G tw psi hSupport hCuts.2
  rw [heq]
  exact parity_original_eq417_ungated_restrict434 L rho xi3 Z k N S
    hData.2.1 F G tw psi hCuts.1
end Green64Analytic.Parity

end

end

/-! ## RawSourceNormalization -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Exact single outer-Z normalization in the existing original gated
channel. Positivity of source positions is used only for division by n;
both Ppart gates, the signed shift and both independent parity choices
remain untouched. No cap insertion or saving is asserted here. -/
theorem parity_raw_B521_outer_normalization434
    {I : Type} [Fintype I] (P : I → Finset ℕ) (R : Finset ℕ)
    (N : Finset ℕ) (hN : ∀ n∈N,0<n)
    (F G : PrimeSlotCore) (k : ℤ) (a1 a2 Z : ℝ) (hZ : 0<Z)
    (psi : ℝ→ℂ) (tw1 tw2 : Bool) :
    (Z : ℂ)*sourceNativeGatedChannel N P R F G k a1 a2
        (fun n=>(((n : ℝ)/Z : ℝ) : ℂ)*psi ((n : ℝ)/Z)/(n : ℂ)) tw1 tw2 =
      sourceNativeGatedChannel N P R F G k a1 a2
        (fun n=>psi ((n : ℝ)/Z)) tw1 tw2 := by
  have hZC : (Z : ℂ)≠0 := by exact_mod_cast hZ.ne'
  unfold sourceNativeGatedChannel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnC : (n : ℂ)≠0 := by exact_mod_cast (hN n hn).ne'
  simp only [sourceNativeGatedGramKernel]
  split_ifs
  · push_cast
    field_simp [hZC,hnC]
    <;> ring
  · simp

/-- The true independently defined stripped RAW, with the normalized
original cutoff t*psi(t), equals the existing original B521 channel after
ONE outer Z. Actual support/shift geometry is derived uniformly in J,
not supplied as a channel-equality assumption. The channel has both
literal floor(exp(L/44)) gates at w,w+2k. Physical DR*w caps and removal
of the J shared law are separate obligations. -/
theorem parity_eventually_raw_original_B521_outer_Z434
    (CZ Ck : ℝ) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop,1<L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (J : ℕ) (rho xi3 Z : ℝ),Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
    ∀ k : ℤ,k≠0 → (k.natAbs : ℝ)≤L^Ck →
    ∀ (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ),
      (∀ t,psi t≠0 → (1/64 : ℝ)≤t ∧ t≤64) →
      (Z : ℂ)*parityRawStrippedHarmonic434 L hS rho xi3 Z k
        (parityPositiveNaturalPositions434
          (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)))
        F G tw (fun t=>(t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L) =
      sourceNativeGatedChannel (Finset.Icc 1 ⌊64*Z⌋₊)
        (sourceOriginalPAllActualBands 20 L)
        (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
        F G k (rho+xi3) (-rho) (fun n=>psi ((n : ℝ)/Z)) tw tw := by
  filter_upwards [parity_eventually_raw_original_B521_channel434 CZ Ck hCZ,
    parity_eventually_raw_source_support434 CZ Ck hCZ] with L hChannel hSupport
  refine ⟨hChannel.1,?_⟩
  intro hS J rho xi3 Z hZlo hZhi k hk hK F G tw psi hSupp
  have hSuppH : ∀ t : ℝ,(t : ℂ)*psi t≠0 → (1/64 : ℝ)≤t ∧ t≤64 := by
    intro t ht
    apply hSupp t
    intro hz
    exact ht (by rw [hz,mul_zero])
  rw [hChannel.2 hS J rho xi3 Z hZlo hZhi k hk hK F G tw
    (fun t=>(t : ℂ)*psi t) hSuppH]
  exact parity_raw_B521_outer_normalization434 _ _ _
    (fun n hn=>by have h:= (Finset.mem_Icc.mp hn).1;omega)
    F G k (rho+xi3) (-rho) Z
    (hSupport.2 J Z hZlo hZhi k hK).1 psi tw tw
end Green64Analytic.Parity

end

end

/-! ## ActualB521FullSourceSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 32000

/-- Actual r20 FULL ORIGINAL B521 finite source on Icc 1 floor(64Z),
not merely the intermediate positive B654 carrier with a target guard.
A complete capped physical RAW differs by arbitrary inverse-log saving;
the unscaled original source channel itself is uniformly small with one
exact exterior Z. This uses the independent original support and exact
outer-Z carrier normalization proof. Historical external source E4.1 and
final Green64 require separately verified source correspondence. -/
theorem parity_eventually_actual_capped_physical_B521_full_interval_saving434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
        let physical := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
          positions 1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0
          (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)
        let original := sourceNativeGatedChannel (Finset.Icc 1 ⌊64*Z⌋₊)
          (sourceOriginalPAllActualBands 20 L)
          (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
          Ecore Gcore k (rho+xi3) (-rho)
          (fun n => psi ((n : ℝ)/Z)) tw tw
        ‖(Z : ℂ)*physical-original‖ ≤ Z*L^(-target) ∧
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hBridge⟩ :=
    parity_eventually_actual_capped_physical_B521_source_saving434 jQ target
      Cfreq CZ Ck Cpsi beta gamma Kpsi hTarget hCZ hCk hCpsi hKpsi hbeta hgamma
  have hNorm := parity_eventually_raw_original_B521_outer_Z434 CZ Ck hCZ
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hBridge,hNorm] with L hBridgeL hNormL
  refine ⟨hBridgeL.1,hBridgeL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let N := parityPositiveNaturalPositions434 positions
  let P := parityRawHarmonicPhysicalAggregate434 L hFamily J (-xi3) Z k
    positions 1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0
    (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)
  let SrcN := sourceNativeGatedChannel N (sourceOriginalPAllActualBands 20 L)
    (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    E G k (rho+xi3) (-rho)
    (fun n => if ((n : ℤ)+2*k).toNat∈N then
      (Z : ℂ)⁻¹*psi ((n : ℝ)/Z) else 0) tw tw
  let SrcFull := sourceNativeGatedChannel (Finset.Icc 1 ⌊64*Z⌋₊)
    (sourceOriginalPAllActualBands 20 L)
    (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    E G k (rho+xi3) (-rho) (fun n => psi ((n : ℝ)/Z)) tw tw
  have hL1 : 1 < L := hNormL.1
  have hLp : 0 < L := by linarith
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hNpos : ∀ n ∈ N, 0 < n := by
    intro n hn
    exact ((parity_positive_natural_positions_mem434 _ n).mp hn).1
  have hStripped :
    parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw
      (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L) = SrcN :=
    parity_raw_stripped_original_B521_normalized434
      L hL1 hFamily rho xi3 Z hZ k hk N hNpos E G tw psi hSupport
  have hOldNorm := hNormL.2 hFamily J rho xi3 Z hZlo hZhi k hk hkBound E G tw psi hSupport
  have hSrcEq : (Z : ℂ)*SrcN = SrcFull := by
    rw [←hStripped]
    exact hOldNorm
  have hPair := hBridgeL.2.2 hFamily Z hZlo hZhi band hband slot delta freq
    k hk hkBound chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  change ‖(Z : ℂ)*(P-SrcN)‖ ≤ Z*L^(-target) ∧
    ‖(Z : ℂ)*SrcN‖ ≤ Z*L^(-target) at hPair
  change ‖(Z : ℂ)*P-SrcFull‖ ≤ Z*L^(-target) ∧
    ‖SrcFull‖ ≤ Z*L^(-target)
  constructor
  · calc
      _ = ‖(Z : ℂ)*(P-SrcN)‖ := by rw [←hSrcEq]; congr 1; ring
      _ ≤ Z*L^(-target) := hPair.1
  · rw [←hSrcEq]
    exact hPair.2
end Green64Analytic.Parity

end

end

/-! ## Eq417UngatedSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 30000

/-- The literal UNGATED Parity Type-II separated source (4.17) has
arbitrary inverse-log saving for the genuine actual r20 prime-slot cores.
No artificial Ppart cap, positive-target indicator or extra 1/Z appears.
This is specialized to the actual constructed original cores and is NOT
the universal correlation Theorem E4.1 or the full Type II assertion. -/
theorem parity_eventually_B633_original_ungated_eq417_saving434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
        let original := parityOriginalEq417Ungated434 L rho xi3 Z k
          (Finset.Icc 1 ⌊64*Z⌋₊) Ecore Gcore tw psi
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hCapped⟩ :=
    parity_eventually_actual_capped_physical_B521_full_interval_saving434
      jQ (target+1) Cfreq CZ Ck Cpsi beta gamma Kpsi
      (by linarith) hCZ hCk hCpsi hKpsi hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hQuot := parity_eventually_actual_normalized_raw_quotient_cap_loss434
    S beta gamma CZ Ck Cpsi (target+1) Kpsi
    hSpos hbeta hgamma hCZ hCpsi hKpsi
  have hSource := parity_eventually_raw_original_B521_outer_Z434 CZ Ck hCZ
  have hUngated := parity_eventually_raw_original_ungated_eq417434 CZ Ck hCZ
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hCapped,hQuot,hSource,hUngated,eventually_ge_atTop (2 : ℝ)]
    with L hCappedL hQuotL hSourceL hUngatedL hL2
  refine ⟨hCappedL.1,hCappedL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let psiH : ℝ → ℂ := fun t => (t : ℂ)*psi t
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)
  let N := parityPositiveNaturalPositions434 positions
  let U := parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw psiH (fun _ _ => 1)
  let C := parityRawStrippedHarmonic434 L hFamily rho xi3 Z k N E G tw psiH
    (parityOriginalPhysicalPairPcap434 L)
  let SrcC := sourceNativeGatedChannel (Finset.Icc 1 ⌊64*Z⌋₊)
    (sourceOriginalPAllActualBands 20 L)
    (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
    E G k (rho+xi3) (-rho) (fun n => psi ((n : ℝ)/Z)) tw tw
  let SrcU := parityOriginalEq417Ungated434 L rho xi3 Z k
    (Finset.Icc 1 ⌊64*Z⌋₊) E G tw psi
  have hLp : 0 < L := by linarith
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hkBound
  have hCappedSmall : ‖SrcC‖ ≤ Z*L^(-(target+1)) :=
    (hCappedL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg).2
  have hQuotPair := hQuotL.2.2 prime lFine uFine hFineLow
    20 (sourceOriginalLiteralDepth 20 L) (by norm_num) band slot delta freq
    (Finset.Icc a b) (2*k.natAbs) chi 0 0
    xi1 xi2 rho sigma hFamily xi3 Z k hZlo hZhi hkReal
    tw psi hSmooth hSupport hReg positions
  have hQuotSmall : ‖(Z : ℂ)*(U-C)‖ ≤ Z*L^(-(target+1)) := hQuotPair.2
  have hCappedEq : (Z : ℂ)*C = SrcC :=
    hSourceL.2 hFamily J rho xi3 Z hZlo hZhi k hk hkBound E G tw psi hSupport
  have hUngatedEq : (Z : ℂ)*U = SrcU :=
    hUngatedL.2 hFamily J rho xi3 Z hZlo hZhi k hk hkBound E G tw psi hSupport
  have hCappedZ : ‖(Z : ℂ)*C‖ ≤ Z*L^(-(target+1)) := by
    rw [hCappedEq]
    exact hCappedSmall
  have hPower : L*L^(-(target+1)) = L^(-target) := by
    calc
      _ = L^(1+(-(target+1))) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hLp (1 : ℝ) (-(target+1))).symm
      _ = L^(-target) := by congr 1; ring
  change ‖SrcU‖ ≤ Z*L^(-target)
  rw [←hUngatedEq]
  have hSplit : U = C+(U-C) := by ring
  rw [hSplit,mul_add]
  calc
    _ ≤ ‖(Z : ℂ)*C‖+‖(Z : ℂ)*(U-C)‖ := norm_add_le _ _
    _ ≤ Z*L^(-(target+1))+Z*L^(-(target+1)) := add_le_add hCappedZ hQuotSmall
    _ = Z*(2*L^(-(target+1))) := by ring
    _ ≤ Z*(L*L^(-(target+1))) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hLp.le _)) hZ.le
    _ = Z*L^(-target) := by rw [hPower]
end Green64Analytic.Parity

end

end

/-! ## Eq417FirstCore -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Literal Parity (4.17) with his ORIGINAL nonconjugated F(z), G(z+2k)
from Parity (4.16), the two complete W1 marked factors and the actual parity
signs. There is NO Ppart cap or secondary target-support indicator. -/
def parityOriginalEq417WithFirstCore434
    (L rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ → ℂ) : ℂ :=
  ∑ z ∈ N,
    if 0 < (z : ℤ)+2*k then
      let zp := ((z : ℤ)+2*k).toNat
      psi ((z : ℝ)/Z) * imaginaryPower z (rho+xi3) *
        imaginaryPower zp (-rho) *
        primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z *
        primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G zp *
        ((groupSign (sourceOriginalPAllActualBands 20 L) tw z *
          groupSign (sourceOriginalPAllActualBands 20 L) tw zp : ℝ) : ℂ) *
        ((sourceMarkedWeight (1/2 : ℝ) 1 (sourceOriginalPAllActualBands 20 L) z *
          sourceMarkedWeight (1/2 : ℝ) 1 (sourceOriginalPAllActualBands 20 L) zp : ℝ) : ℂ)
    else 0

/-- Parity first input F_E is literally the conjugate of his F from (4.16).
No synthetic or renamed core appears in (4.17): all alpha, residual,
character and prime-slot coefficients are the unchanged original ones. -/
theorem parity_original_eq417_literal_first_core434
    (L rho xi3 Z xi2 sigma : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ) :
    parityOriginalEq417Ungated434 L rho xi3 Z k N
      (b633ParityEFirstCore434 alpha residual q chi lo hi xi2 rho sigma) G tw psi =
    parityOriginalEq417WithFirstCore434 L rho xi3 Z k N
      (b633ParityFirstCore434 alpha residual q chi lo hi xi2 rho sigma) G tw psi := by
  unfold parityOriginalEq417Ungated434 parityOriginalEq417WithFirstCore434
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : 0 < (z : ℤ)+2*k
  · simp only [h,ite_true]
    rw [b633_parity_E_first_literal_conjugate434]
    simp only [star_star]
  · simp [h]

end Green64Analytic.Parity

end

end

/-! ## Eq417DirectSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000

/-- Literal Parity (4.16)-(4.17), now using his F(z) rather than star(E(z)):
the original complete ungated source has arbitrary inverse-log saving
for the actual r20 native prime-slot family. This theorem is still NOT a
general coefficient/discrepancy theorem, nor full Type II or Green64. -/
theorem parity_eventually_B633_original_Parity417_direct_saving434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let Fparity := b633ParityFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
        let original := parityOriginalEq417WithFirstCore434 L rho xi3 Z k
          (Finset.Icc 1 ⌊64*Z⌋₊) Fparity Gcore tw psi
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hOld⟩ :=
    parity_eventually_B633_original_ungated_eq417_saving434 jQ target
      Cfreq CZ Ck Cpsi beta gamma Kpsi hTarget hCZ hCk hCpsi hKpsi hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hOld] with L hOldL
  refine ⟨hOldL.1,hOldL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let E := b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Fparity := b633ParityFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let SrcE := parityOriginalEq417Ungated434 L rho xi3 Z k
    (Finset.Icc 1 ⌊64*Z⌋₊) E G tw psi
  let SrcF := parityOriginalEq417WithFirstCore434 L rho xi3 Z k
    (Finset.Icc 1 ⌊64*Z⌋₊) Fparity G tw psi
  have hBound : ‖SrcE‖ ≤ Z*L^(-target) :=
    hOldL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  have hIdentity : SrcE = SrcF :=
    parity_original_eq417_literal_first_core434 L rho xi3 Z xi2 sigma k
      (Finset.Icc 1 ⌊64*Z⌋₊) F.alpha F.residual (2*k.natAbs) chi F.lo F.hi
      G tw psi
  change ‖SrcF‖ ≤ Z*L^(-target)
  rw [←hIdentity]
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## Eq417PhysicalCofactors -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000
set_option maxRecDepth 28000

/-- Parity's original separated post-Cauchy physical sum BEFORE the prime
cores (4.16) have been contracted. This is a genuine double rough-cofactor
sum with original α_m, α_m', both prime-slot residuals, W1 and the SAME
parity twist at both physical endpoints. No Ppart cap or assumed saving. -/
def parityOriginalEq417PhysicalCofactors434
    (L rho xi1 xi2 xi3 sigma Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (tw : Bool) (psi : ℝ → ℂ) : ℂ :=
  ∑ z ∈ N,
    if 0 < (z : ℤ)+2*k then
      psi ((z : ℝ)/Z)*
        b633ParityPhysicalPair434 (sourceOriginalPAllActualBands 20 L)
          (1/2) 1 tw alpha residual q chi lo hi xi1 xi2 xi3 rho sigma
          z ((z : ℤ)+2*k).toNat
    else 0

/-- Universal finite original Eq(4.17) arithmetic identification: α and
residual are arbitrary, only rough support and original prime-band geometry
are requested. This is a pure source equality, NOT an E4.1 estimate. -/
theorem parity_original_eq417_physical_cofactors_exact434
    (L rho xi1 xi2 xi3 sigma Z : ℝ) (k : ℤ)
    (N : Finset ℕ) (hN : ∀ z∈N,0<z)
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (tw : Bool) (psi : ℝ → ℂ)
    (W : ℝ)
    (hp : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g → p.Prime)
    (hW : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g → (p:ℝ) ≤ W)
    (hrough : ∀ m, alpha m ≠ 0 → sourceD20Rough W m) :
    parityOriginalEq417PhysicalCofactors434 L rho xi1 xi2 xi3 sigma Z k N
      alpha residual q chi lo hi tw psi =
    parityOriginalEq417WithFirstCore434 L rho xi3 Z k N
      (b633ParityFirstCore434 alpha residual q chi lo hi xi2 rho sigma)
      (b633ParitySecondCore434 alpha residual q chi lo hi xi1 rho sigma) tw psi := by
  unfold parityOriginalEq417PhysicalCofactors434 parityOriginalEq417WithFirstCore434
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : 0 < (z : ℤ)+2*k
  · have hzpos : 0<z := hN z hz
    have htpos : 0 < ((z : ℤ)+2*k).toNat := by omega
    simp only [h,ite_true]
    rw [b633_parity_full_physical_pair434
      (sourceOriginalPAllActualBands 20 L) W (1/2) 1 tw
      alpha residual q chi lo hi xi1 xi2 xi3 rho sigma z
      ((z : ℤ)+2*k).toNat hzpos htpos hp hW hrough]
    ring
  · simp [h]
end Green64Analytic.Parity

end

end

/-! ## Eq417CofactorInputs -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Every actual original full P group prime is below the true
rough cutoff exp(sqrt L), with its literal original primality. -/
theorem parity_original_actual_full_P_prime_rough_cap434
    (L : ℝ) (hL : 1 ≤ L) :
    ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g →
      p.Prime ∧ (p:ℝ) ≤ Real.exp (Real.sqrt L) := by
  intro g p hp
  have hG : p ∈ sourceNativeOriginalG434 20 L := by
    unfold sourceNativeOriginalG434
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hp⟩
  exact source_native_original_G_bound434 20 L hL p hG

/-- The actual K-restricted fine alpha has the required original rough
support; this has no extra discrepancy/smallness hypothesis and preserves
arbitrary original intervals K, both prime/proxy signs and fixed S. -/
theorem parity_actual_fine_K_restricted_rough434
    (S beta gamma : ℝ) (hS : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (prime : Bool) (l u : ℕ), 2 ≤ l →
        Real.exp (beta*L) ≤ (l:ℝ) →
        ∀ (K : Finset ℕ) (n : ℕ),
          restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) n ≠ 0 →
          sourceD20Rough (Real.exp (Real.sqrt L)) n := by
  filter_upwards [b629_actual_fine_coefficient_and_rough_support434
    S beta gamma hS hbeta hgamma] with L hcoeff
  intro prime l u hl hlow K n hne
  have hBase : b629ActualFineAlpha434 prime L S gamma l u n ≠ 0 := by
    intro hz
    exact hne (by simp [restrictSequence, hz])
  have hmem : n ∈ Finset.Icc l u := by
    by_contra hn
    exact hBase (by simp [b629ActualFineAlpha434, hn])
  have hn2 : 2 ≤ n := hl.trans (Finset.mem_Icc.mp hmem).1
  have hr := (hcoeff prime l u hlow n).2 hBase
  exact ⟨hn2, hr n.minFac (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)⟩
end Green64Analytic.Parity

end

end

/-! ## ActualFineCauchyAlphaNorm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Actual original Parity(4.2) coefficient class at every fine b629
interval, prime OR rough proxy branch: restriction to the real
cofactor support K never enlarges the pointwise magnitude. The
native b629 source coefficient theorem supplies `||alpha_m||<=1`
and true roughness, so a new independent Acoef premise is not needed
when the original Cauchy diagonal bound is instantiated with Acoef=1.
No arbitrary artificial coefficient or analytic saving is assumed. -/
theorem parity_eventually_original_actual_b629_K_fine_alpha_norm_one434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (prime : Bool) (l uFine : ℕ),
        Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (m : ℕ),
        ‖restrictSequence K (b629ActualFineAlpha434 prime L S gamma l uFine) m‖ ≤ 1 := by
  filter_upwards [b629_actual_fine_coefficient_and_rough_support434
    S beta gamma hS hbeta hgamma] with L hCoeff
  intro prime l uFine hlow K m
  by_cases hm : m∈K
  · have hBound := (hCoeff prime l uFine hlow m).1
    simpa only [restrictSequence,hm,ite_true] using hBound
  · simp [restrictSequence,hm]
end Green64Analytic.Parity

end

end

/-! ## Eq417ActualCofactorSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000

/-- The fully expanded ORIGINAL post-Cauchy m,m' physical cofactor sum
in Parity (4.17), with the actual source r20 prime-minus-proxy coefficient,
has arbitrary inverse-log saving. Its two ordinary-part cofactor sums,
full residual, rough restrictions, W1 factors and equal parity twists are
all independently defined, not replaced by the desired F/G endpoint value.
This is a single actual separated summand, NOT complete Cauchy/TypeII. -/
theorem parity_eventually_actual_original_Parity417_physical_cofactor_saving434
    (jQ : ℕ) (target Cfreq CZ Ck Cpsi beta gamma : ℝ) (Kpsi : ℕ → ℝ)
    (hTarget : 0 < target) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B : ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val = jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (k : ℤ), k ≠ 0 → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma : ℝ),
          |rho| ≤ L^Cfreq → |xi1| ≤ L^Cfreq → |xi2| ≤ L^Cfreq →
          |xi3| ≤ L^Cfreq → |sigma| ≤ L^Cfreq →
        ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L) ≤ (lFine : ℝ) →
          2 ≤ lFine → uFine ≤ 2*lFine → (uFine : ℝ) ≤ Real.exp (2*L) →
        ∀ (tw : Bool) (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
          (∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
        let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
          (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
          (2*k.natAbs) chi 0 0
        let original := parityOriginalEq417PhysicalCofactors434 L rho xi1 xi2 xi3 sigma Z k
          (Finset.Icc 1 ⌊64*Z⌋₊) F.alpha F.residual (2*k.natAbs) chi F.lo F.hi tw psi
        ‖original‖ ≤ Z*L^(-target) := by
  obtain ⟨J,B,S,hSB,hDirect⟩ :=
    parity_eventually_B633_original_Parity417_direct_saving434 jQ target
      Cfreq CZ Ck Cpsi beta gamma Kpsi hTarget hCZ hCk hCpsi hKpsi hbeta hgamma
  have hSpos : 0 < S := by
    nlinarith [show (0 : ℝ) ≤ (B : ℝ) from Nat.cast_nonneg B]
  have hRough := parity_actual_fine_K_restricted_rough434 S beta gamma
    hSpos hbeta hgamma
  refine ⟨J,B,S,hSB,?_⟩
  filter_upwards [hDirect,hRough,eventually_ge_atTop (1 : ℝ)]
    with L hDirectL hRoughL hL
  refine ⟨hDirectL.1,hDirectL.2.1,?_⟩
  intro hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
    chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
    prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  dsimp only
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  let First := b633ParityFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
  let Second := b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
  let N := Finset.Icc 1 ⌊64*Z⌋₊
  let SumPhysical := parityOriginalEq417PhysicalCofactors434 L rho xi1 xi2 xi3 sigma Z k N
    F.alpha F.residual (2*k.natAbs) chi F.lo F.hi tw psi
  let SumDirect := parityOriginalEq417WithFirstCore434 L rho xi3 Z k N First Second tw psi
  have hFullGroup := parity_original_actual_full_P_prime_rough_cap434 L hL
  have hp : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g → p.Prime :=
    fun g p h => (hFullGroup g p h).1
  have hW : ∀ g p, p ∈ sourceOriginalPAllActualBands 20 L g →
      (p:ℝ) ≤ Real.exp (Real.sqrt L) :=
    fun g p h => (hFullGroup g p h).2
  have hRough' : ∀ m, F.alpha m ≠ 0 →
      sourceD20Rough (Real.exp (Real.sqrt L)) m := by
    intro m hm
    exact hRoughL prime lFine uFine hl hFineLow (Finset.Icc a b) m hm
  have hN : ∀ z∈N,0<z := by
    intro z hz
    exact (Finset.mem_Icc.mp hz).1
  have hEq : SumPhysical = SumDirect :=
    parity_original_eq417_physical_cofactors_exact434 L rho xi1 xi2 xi3 sigma Z k N hN
      F.alpha F.residual (2*k.natAbs) chi F.lo F.hi tw psi
      (Real.exp (Real.sqrt L)) hp hW hRough'
  have hSaving : ‖SumDirect‖ ≤ Z*L^(-target) :=
    hDirectL.2.2 hFamily Z hZlo hZhi band hband slot delta freq k hk hkBound
      chi rho xi1 xi2 xi3 sigma hrho hxi1 hxi2 hxi3 hsigma
      prime lFine uFine a b hFineLow hl hu hub tw psi hSmooth hSupport hReg
  change ‖SumPhysical‖ ≤ Z*L^(-target)
  rw [hEq]
  exact hSaving
end Green64Analytic.Parity

end

end

