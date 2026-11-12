module

public import Green64.Library.Weights.Part110
public import Green64.Library.Weights.Part033
public import Green64.Library.Weights.Part105
public import Green64.Library.Weights.Part020
public import Green64.Library.Correlation.Part032
public import Green64.Library.Correlation.Part070
public import Green64.Library.Weights.Part100
public import Green64.Library.Correlation.Part042
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Weights.Part109

@[expose] public section

/-!
# Weights / Part111

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## EnlargedRankArc -/

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

/-- Literal actual r20 rank-arc contract at a fixed enlarged physical
support A. Every original field is retained; the actual carrier now ends
at ceil(A*Z*Hp). The original modulus is 2*natAbs(k), without an even-k
restriction or any replacement of the full marked endpoint. -/
def ParityEnlargedActualRankComparisonCellArc434
    (cfg : SourceComparisonFixed434) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma targetSaving Karc : ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (sigma0 sigma1 v1 : ℝ),
    |sigma0|≤L^cfg.s0 → |sigma1|≤L^cfg.s1base → |v1|≤L^cfg.vexp →
  ∀ (psi : ℝ → ℂ), ContDiff ℝ ∞ psi →
    (∀ u, psi u≠0 → 1/cfg.A≤u ∧ u≤ cfg.A) →
    sourceLogDerivativeBudget cfg.Cpsi cfg.Kpsi L (fun u=>psi (Real.exp u)) →
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 20 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)) (tw sourceSide : Bool),
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let P := sourceNativeOriginalTb434 20 L
  let Vm := sourceNativeOriginalVbig434 20 L
  let row := if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB jb cb
    else paritySecondRankMark434 J 1 m hmJ nu hA ja ca
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  ∃ data : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L (Z*Hp) Hp,
    (data.Z=Z ∧ data.Ncap=⌈cfg.A*(Z*Hp)⌉₊ ∧
    data.G=sourceNativeOriginalG434 20 L ∧
    data.Ptw=(if tw then sourceNativeOriginalG434 20 L else ∅) ∧
    data.S=sourceNativeOriginalS434 20 L hFamily ∧
    data.Ts=sourceNativeOriginalTs434 20 L hFamily ∧ data.Tb=P ∧
    data.Vs=sourceNativeOriginalVs434 20 L hFamily ∧
    data.Vsmall=sourceNativeOriginalVsmall434 20 L hFamily ∧ data.Vbig=Vm ∧
    data.ts=(fun _=>1) ∧ data.tb=sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu ∧
    HEq data.coef row ∧ data.k=0 ∧
    data.alpha=b629ActualFineAlpha434 prime L S gamma lFine uFine ∧
    data.lo=a ∧ data.hi=b ∧ data.alphaCut=F.alpha ∧
    data.F1=Finset.range (Fintype.card nu.1) ∧ data.F2=Finset.range (Fintype.card nu.2) ∧
    data.p1=sourceOriginalProbeIndexedPrime434 (fun z : nu.1=>aux (Sum.inl z)) ∧
    data.p2=sourceOriginalProbeIndexedPrime434 (fun z : nu.2=>aux (Sum.inr z)) ∧
    data.U1=Real.exp ((ja:ℝ)*hA) ∧ data.U2=Real.exp ((jb:ℝ)*hB) ∧
    data.primeSlot=sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band ∧
    data.c=(fun n=>star (F.residual n)) ∧ data.C=1 ∧ data.qBase=2*k.natAbs ∧
    HEq data.chi0 (chi.ringHomComp (starRingEnd ℂ)) ∧
    data.sigma0=sigma0 ∧ data.sigma1=sigma1 ∧ data.v1=v1 ∧ data.psi1=psi) ∧
    data.endpoint = sourceOriginalFullEndpointCoefficients434 (2*k.natAbs)
      (sourceNativeOriginalS434 20 L hFamily) (sourceNativeOriginalTs434 20 L hFamily) P cfg.q0
      (sourceNativeOriginalVs434 20 L hFamily) (sourceNativeOriginalVsmall434 20 L hFamily) Vm
      (fun _=>1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) row 0
      (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band)
      F.alpha (fun n=>star (F.residual n)) (chi.ringHomComp (starRingEnd ℂ)) sigma0 sigma1
      (fun n=>psi ((n:ℝ)/(Z*Hp))*sourcePhase n v1) ∧
    ∀ (eps : Bool) (den h : ℕ), 0 < den → (den:ℝ) ≤ L^cfg.cm →
      (∫ theta in {theta : ℝ | |theta| ≤ L^cfg.Carc/Hp},
        ‖sourceCircleFourierPoly data.support
          (sourceSignedCoefficients434 data.Ptw eps data.endpoint)
          (((h:ℝ)/(den:ℝ)+theta:ℝ):AddCircle (1:ℝ))‖^2) ≤
        Karc*(Z*Hp)*L^(-targetSaving)


/-- Genuine actual B629 saving for an enlarged fixed cutoff support.
The source data are constructed from the already proved r20 records with
a zero temporary cutoff, then transported to the larger exact carrier and
the supplied original smooth cutoff. The enlarged cap and arc geometry are
proved from the real active cells. Requested saving, A and every fixed
budget precede L and the complete ordered operator tuple. The support and
derivative hypotheses are the ordinary explicit cutoff input contract;
there is no assumed data record, arc estimate or Main-smallness premise. -/
theorem parity_eventually_enlarged_actual_rank_marked_arc434
    (A : ℝ) (hLargeA : 64 ≤ A)
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi Ck Cpsi beta gamma targetSaving : ℝ)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hcm : Ck+1 ≤ (cm:ℝ))
    (hCarc : (cm:ℝ) ≤ Carc) (hCchi : (cm:ℝ) ≤ Cchi) (hCchiPos : 0 < Cchi)
    (hCpsi : 0 ≤ Cpsi) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg0 := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
      hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
    let cfg := parityEnlargedComparisonFixed434 cfg0 A (by linarith)
    ∃ Karc : ℝ, 0 < Karc ∧ ∃ B : ℕ, ∃ S : ℝ,
      2*((B:ℝ)+1)+3 < S ∧
      ∀ᶠ L : ℝ in atTop,
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ParityEnlargedActualRankComparisonCellArc434 cfg L jQ mmax CZ Ck S beta gamma
          targetSaving Karc := by
  let cfg0 := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
  let cfg := parityEnlargedComparisonFixed434 cfg0 A (by linarith)
  obtain ⟨Karc,hKarc,B,S,hSB,X0,hX0,hArc⟩ :=
    b629_actual_fine_full_marked_signed_arc434 cfg targetSaving beta gamma hbeta hgamma
  have hS : 0 < S := by have := Nat.cast_nonneg (α:=ℝ) B; linarith
  have hData := parity_eventually_actual_comparison_data434
    jQ mmax cm s0 s1 vexp CZ Carc Cchi Ck Cpsi S beta gamma
    hCZ hCk hcm hCarc hCchi hCchiPos hCpsi hS hbeta hgamma Kpsi hKpsi
  have hCarc0 : 0 ≤ Carc := (Nat.cast_nonneg cm).trans hCarc
  have hScales := Filter.eventually_all.mpr
    (fun m : Fin (mmax+1) => parity_eventually_enlarged_comparison_cell_scales434
      A CZ Carc m.val hLargeA hCZ hCarc0)
  refine ⟨Karc,hKarc,B,S,hSB,?_⟩
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
end Green64Analytic.Parity

end

end

/-! ## ConstructedRankArc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 26000

/-- A common fixed cutoff and its harmonic counterpart have one genuine
log derivative budget. The complete construction precedes every L and
operator choice; neither support nor regularity is assumed. -/
theorem parity_fixed_rank_cutoff_pair_budget434 :
    ∃ A : ℝ, 64 ≤ A ∧ ∃ eta : ℝ → ℂ,
      ContDiff ℝ ∞ eta ∧
      (∀ u : ℝ, eta u≠0 → 1/A≤u ∧ u≤A) ∧
      (∀ u ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1), eta u=1) ∧
      (∀ u : ℝ, ‖eta u‖≤1) ∧
      ContDiff ℝ ∞ (fun u : ℝ => eta u/(u : ℂ)) ∧
      (∀ u : ℝ, eta u/(u : ℂ)≠0 → 1/A≤u ∧ u≤A) ∧
      ∃ K : ℕ → ℝ, (∀ j, 0≤K j) ∧
        ∀ L : ℝ,
          sourceLogDerivativeBudget 0 K L (fun u : ℝ => eta (Real.exp u)) ∧
          sourceLogDerivativeBudget 0 K L
            (fun u : ℝ => eta (Real.exp u)/(Real.exp u : ℂ)) := by
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K0,hK0,hB0⟩ := parity_fixed_rank_cell_cutoff_exists434
  obtain ⟨hsInv,hSuppInv,K1,hK1,hB1⟩ :=
    parity_fixed_harmonic_cutoff_regular434 A eta (by linarith) hs hSupp
  let K : ℕ → ℝ := fun j => K0 j+K1 j
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,hsInv,hSuppInv,K,
    (fun j => add_nonneg (hK0 j) (hK1 j)),?_⟩
  intro L
  constructor
  · intro j u
    have hh := hB0 L j u
    simp only [zero_mul,Real.rpow_zero,mul_one] at hh ⊢
    exact hh.trans (le_add_of_nonneg_right (hK1 j))
  · intro j u
    have hh := hB1 L j u
    simp only [zero_mul,Real.rpow_zero,mul_one] at hh ⊢
    exact hh.trans (le_add_of_nonneg_left (hK0 j))

/-- Actual source rank-arc conclusion for the constructed endpoint pair.
The first cutoff is eta(u)/u and the second is eta(u). There is no cutoff
argument and no support, derivative, data or arc premise in this interface. -/
def ParityConstructedActualRankComparisonCellArc434
    (cfg : SourceComparisonFixed434) (eta : ℝ → ℂ) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma targetSaving Karc : ℝ) : Prop :=
  ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
  ∀ (J m : ℕ) (hmJ : m ≤ J), m ≤ mmax →
  ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
    nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
  ∀ (hA hB xi : ℝ), 0<hA → 0<hB → 0<xi → hA≤1 → hB≤1 →
  ∀ (ja jb : ℤ),
    ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hA xi →
    jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
      (sourceNativeOriginalVbig434 20 L) nu hB xi →
  ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
  ∀ (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (sigma0 sigma1 v1 : ℝ),
    |sigma0|≤L^cfg.s0 → |sigma1|≤L^cfg.s1base → |v1|≤L^cfg.vexp →
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 20 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)) (tw sourceSide : Bool),
  let psi : ℝ → ℂ := if sourceSide then (fun u => eta u/(u : ℂ)) else eta
  let Hp := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let P := sourceNativeOriginalTb434 20 L
  let Vm := sourceNativeOriginalVbig434 20 L
  let row := if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB jb cb
    else paritySecondRankMark434 J 1 m hmJ nu hA ja ca
  let F := sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  ∃ data : SourceComparisonData434
      (sourceNativeOriginalTsType434 20 L hFamily) (sourceNativeOriginalBigType434 20 L)
      cfg (Real.exp L) L (Z*Hp) Hp,
    (data.Z=Z ∧ data.Ncap=⌈cfg.A*(Z*Hp)⌉₊ ∧
    data.G=sourceNativeOriginalG434 20 L ∧
    data.Ptw=(if tw then sourceNativeOriginalG434 20 L else ∅) ∧
    data.S=sourceNativeOriginalS434 20 L hFamily ∧
    data.Ts=sourceNativeOriginalTs434 20 L hFamily ∧ data.Tb=P ∧
    data.Vs=sourceNativeOriginalVs434 20 L hFamily ∧
    data.Vsmall=sourceNativeOriginalVsmall434 20 L hFamily ∧ data.Vbig=Vm ∧
    data.ts=(fun _=>1) ∧ data.tb=sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu ∧
    HEq data.coef row ∧ data.k=0 ∧
    data.alpha=b629ActualFineAlpha434 prime L S gamma lFine uFine ∧
    data.lo=a ∧ data.hi=b ∧ data.alphaCut=F.alpha ∧
    data.F1=Finset.range (Fintype.card nu.1) ∧ data.F2=Finset.range (Fintype.card nu.2) ∧
    data.p1=sourceOriginalProbeIndexedPrime434 (fun z : nu.1=>aux (Sum.inl z)) ∧
    data.p2=sourceOriginalProbeIndexedPrime434 (fun z : nu.2=>aux (Sum.inr z)) ∧
    data.U1=Real.exp ((ja:ℝ)*hA) ∧ data.U2=Real.exp ((jb:ℝ)*hB) ∧
    data.primeSlot=sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band ∧
    data.c=(fun n=>star (F.residual n)) ∧ data.C=1 ∧ data.qBase=2*k.natAbs ∧
    HEq data.chi0 (chi.ringHomComp (starRingEnd ℂ)) ∧
    data.sigma0=sigma0 ∧ data.sigma1=sigma1 ∧ data.v1=v1 ∧ data.psi1=psi) ∧
    data.endpoint = sourceOriginalFullEndpointCoefficients434 (2*k.natAbs)
      (sourceNativeOriginalS434 20 L hFamily) (sourceNativeOriginalTs434 20 L hFamily) P cfg.q0
      (sourceNativeOriginalVs434 20 L hFamily) (sourceNativeOriginalVsmall434 20 L hFamily) Vm
      (fun _=>1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu) row 0
      (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band)
      F.alpha (fun n=>star (F.residual n)) (chi.ringHomComp (starRingEnd ℂ)) sigma0 sigma1
      (fun n=>psi ((n:ℝ)/(Z*Hp))*sourcePhase n v1) ∧
    ∀ (eps : Bool) (den h : ℕ), 0 < den → (den:ℝ) ≤ L^cfg.cm →
      (∫ theta in {theta : ℝ | |theta| ≤ L^cfg.Carc/Hp},
        ‖sourceCircleFourierPoly data.support
          (sourceSignedCoefficients434 data.Ptw eps data.endpoint)
          (((h:ℝ)/(den:ℝ)+theta:ℝ):AddCircle (1:ℝ))‖^2) ≤
        Karc*(Z*Hp)*L^(-targetSaving)



/-- Construct the common physical cutoff, its full fixed log budget and
both actual r20 B629 rank endpoint estimates. All constants and requested
precision are chosen before L and the ordered operator tuple. This is the
arc ingredient only; localization equality and Main saving remain separate. -/
theorem parity_eventually_constructed_actual_rank_marked_arc434
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi Ck beta gamma targetSaving : ℝ)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) (hcm : Ck+1 ≤ (cm:ℝ))
    (hCarc : (cm:ℝ) ≤ Carc) (hCchi : (cm:ℝ) ≤ Cchi) (hCchiPos : 0 < Cchi)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
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
          ∀ᶠ L : ℝ in atTop,
            (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
            jQ ≤ sourceOriginalLiteralDepth 20 L ∧
            ParityConstructedActualRankComparisonCellArc434 cfg eta L jQ mmax CZ Ck S beta gamma
              targetSaving Karc := by
  obtain ⟨A,hA,eta,hs,hSupp,hOne,hNorm,hsInv,hSuppInv,K,hK,hBudgets⟩ :=
    parity_fixed_rank_cutoff_pair_budget434
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,?_⟩
  obtain ⟨Karc,hKarc,B,S,hSB,hArc⟩ := parity_eventually_enlarged_actual_rank_marked_arc434
    A hA jQ mmax cm s0 s1 vexp CZ Carc Cchi Ck 0 beta gamma targetSaving
    hCZ hCk hcm hCarc hCchi hCchiPos (by norm_num) hbeta hgamma K hK
  refine ⟨Karc,hKarc,B,S,hSB,?_⟩
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
end Green64Analytic.Parity

end

end

/-! ## PPartFiniteTransfer -/

section

/- Actual original full-valuation P-part finite fibre transfer.
The native B635 source bundle already proves the full infinite Rankin law.
No archived source, runner, mathematical hypothesis or P-family is changed. -/


open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option maxHeartbeats 2200000

/-- Original W1 depends ONLY on the complete P-prime-power part, for every
positive integer u, without squarefree assumptions. All multiplicities
are retained in the P-part, while W1 uses DISTINCT group divisors. -/
theorem parity_original_W1_at_canonical_P_part434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (u : ℕ) (hu : u ≠ 0) :
    sourceOriginalW1 P u =
      sourceOriginalW1 P
        (sourceOriginalPPrimePart (Finset.univ.biUnion P) u) := by
  let Pall := Finset.univ.biUnion P
  let pp := sourceOriginalPPrimePart Pall u
  have hAll : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g,_,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPrime g p hpg
  have hpEq : pp = sourceOriginalPPrimePowerProduct Pall
      (sourceOriginalPExponentVector Pall u) :=
    source_original_P_prime_part_eq_vector_product Pall hAll u hu
  have hpNonzero : pp ≠ 0 := by
    rw [hpEq]
    exact source_original_P_power_product_ne_zero Pall hAll
      (sourceOriginalPExponentVector Pall u)
  have hVal (p : ℕ) (hp : p ∈ Pall) :
      pp.factorization p = u.factorization p := by
    rw [hpEq,source_original_P_power_factorization_at
      Pall hAll (sourceOriginalPExponentVector Pall u) p hp]
    rfl
  have hDvd (p : ℕ) (hp : p ∈ Pall) :
      (p ∣ pp) ↔ (p ∣ u) := by
    have hprime := hAll p hp
    rw [hprime.dvd_iff_one_le_factorization hpNonzero,
      hprime.dvd_iff_one_le_factorization hu, hVal p hp]
  have hOmega : ∀ g : G,
      shiftTwoGroupOmega (P g) u =
        shiftTwoGroupOmega (P g) pp := by
    intro g
    unfold shiftTwoGroupOmega
    congr 1
    apply Finset.filter_congr
    intro p hp
    exact (hDvd p (Finset.mem_biUnion.mpr
      ⟨g,Finset.mem_univ _,hp⟩)).symm
  unfold sourceOriginalW1
  apply Finset.prod_congr rfl
  intro g hg
  unfold shiftTwoOriginalGroupFactor
  rw [hOmega g]

end Green64Analytic.ShiftTwoTerminal


open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option maxHeartbeats 1200000

/-- A fixed canonical original P-part v cannot occur for more than
floor(Y/v) positive u<=Y. No source proxy or count of labelled Q tuples:
the bound uses the actual P-prime-power equality u=u_* v. -/
theorem parity_original_P_part_fibre_card_le434
    (Pall : Finset ℕ) (Y v : ℕ) :
    ((Finset.Ioc 0 Y).filter
      (fun u => sourceOriginalPPrimePart Pall u = v)).card ≤ Y/v := by
  have hsubset : (Finset.Ioc 0 Y).filter
      (fun u => sourceOriginalPPrimePart Pall u = v) ⊆
    (Finset.Ioc 0 Y).filter (fun u => v ∣ u) := by
    intro u hu
    obtain ⟨huI,huEq⟩ := Finset.mem_filter.mp hu
    have hu0 : u ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp huI).1
    have hsplit := source_original_ordinary_times_P_part Pall u hu0
    have hv : v ∣ u := by
      refine ⟨sourceOriginalOrdinaryPart Pall u, ?_⟩
      rw [← huEq] 
      simpa only [mul_comm] using hsplit.symm
    exact Finset.mem_filter.mpr ⟨huI,hv⟩
  calc
    _ ≤ ((Finset.Ioc 0 Y).filter (fun u => v ∣ u)).card :=
      Finset.card_le_card hsubset
    _ = Y/v := Nat.Ioc_filter_dvd_card_eq_div Y v

end Green64Analytic.ShiftTwoTerminal


open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option maxHeartbeats 4600000

/-- Exact reindex of the ORIGINAL W1-weighted P-large integers by the
complete P-prime-power part. No squarefree assumption or duplicate loss. -/
theorem parity_original_P_part_weighted_fibre_exact434
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (Y H : ℕ) :
    let Pall := Finset.univ.biUnion P
    let part := sourceOriginalPPrimePart Pall
    let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
    (∑ u ∈ S, sourceOriginalW1 P u) =
      ∑ v ∈ S.image part,
        ((S.filter (fun u => part u = v)).card : ℝ) *
          sourceOriginalW1 P v := by
  dsimp only
  let Pall := Finset.univ.biUnion P
  let part := sourceOriginalPPrimePart Pall
  let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
  have hMaps : ∀ u ∈ S, part u ∈ S.image part :=
    fun u hu => Finset.mem_image_of_mem _ hu
  calc
    (∑ u ∈ S, sourceOriginalW1 P u) =
      ∑ u ∈ S, sourceOriginalW1 P (part u) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact parity_original_W1_at_canonical_P_part434 P hPrime u
          (Nat.ne_of_gt (Finset.mem_Ioc.mp
            (Finset.mem_filter.mp hu).1).1)
    _ = ∑ v ∈ S.image part,
          ∑ u ∈ S with part u = v, sourceOriginalW1 P (part u) :=
        (Finset.sum_fiberwise_of_maps_to hMaps
          (fun u => sourceOriginalW1 P (part u))).symm
    _ = ∑ v ∈ S.image part,
          ((S.filter (fun u => part u = v)).card : ℝ) *
            sourceOriginalW1 P v := by
        apply Finset.sum_congr rfl
        intro v hv
        have heq : (∑ u ∈ S with part u = v,
              sourceOriginalW1 P (part u)) =
            ∑ _u ∈ S.filter (fun u => part u = v),
              sourceOriginalW1 P v := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [(Finset.mem_filter.mp hu).2]
        rw [heq]
        simp only [Finset.sum_const, nsmul_eq_mul]

/-- A weighted finite fibre can lose at most the exact number of
positive multiples of v in (0,Y]; this is a genuine Y/v bound. -/
theorem parity_original_P_part_weighted_fibre_count434
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (Y H : ℕ) :
    let Pall := Finset.univ.biUnion P
    let part := sourceOriginalPPrimePart Pall
    let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
    (∑ u ∈ S, sourceOriginalW1 P u) ≤
      ∑ v ∈ S.image part,
        ((Y/v : ℕ) : ℝ) * sourceOriginalW1 P v := by
  dsimp only
  let Pall := Finset.univ.biUnion P
  let part := sourceOriginalPPrimePart Pall
  let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
  rw [parity_original_P_part_weighted_fibre_exact434 P hPrime Y H]
  apply Finset.sum_le_sum
  intro v hv
  have hsubset : S.filter (fun u => part u = v) ⊆
      (Finset.Ioc 0 Y).filter (fun u => part u = v) := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hu'.1).1,hu'.2⟩
  have hcard := (Finset.card_le_card hsubset).trans
    (parity_original_P_part_fibre_card_le434 Pall Y v)
  have hc : ((S.filter (fun u => part u = v)).card:ℝ) ≤
      ((Y/v:ℕ):ℝ) := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right hc (source_original_W1_nonneg P v)

end Green64Analytic.ShiftTwoTerminal


open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option maxHeartbeats 3900000

/-- The source P-part of ANY positive integer is itself a genuine
positive P-supported integer, with repeated P-prime-power factors. -/
theorem parity_native_canonical_P_part_supported434
    (Pall : Finset ℕ) (hPrime : ∀ p ∈ Pall, p.Prime)
    (u : ℕ) (hu : u ≠ 0) :
    let v := sourceOriginalPPrimePart Pall u
    v ≠ 0 ∧ v.primeFactors ⊆ Pall := by
  dsimp only
  rw [source_original_P_prime_part_eq_vector_product Pall hPrime u hu]
  exact ⟨source_original_P_power_product_ne_zero Pall hPrime
      (sourceOriginalPExponentVector Pall u),
    source_original_P_power_primeFactors_subset Pall hPrime
      (sourceOriginalPExponentVector Pall u)⟩

/-- Every actual source W1 finite P-large sum is bounded by Y times
the finite H-tail of the ORIGINAL P-supported harmonic weights.
No heuristic density, no squarefree assumption and no Fourier change. -/
theorem parity_original_P_part_finite_harmonic_bound434
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (Y H : ℕ) :
    let Pall := Finset.univ.biUnion P
    let part := sourceOriginalPPrimePart Pall
    let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
    (∑ u ∈ S, sourceOriginalW1 P u) ≤
      (Y:ℝ) * ∑ v ∈ S.image part, sourceOriginalW1 P v / (v:ℝ) := by
  dsimp only
  let Pall := Finset.univ.biUnion P
  let part := sourceOriginalPPrimePart Pall
  let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
  have hbase := parity_original_P_part_weighted_fibre_count434 P hPrime Y H
  dsimp only at hbase
  calc
    (∑ u ∈ S, sourceOriginalW1 P u) ≤
      ∑ v ∈ S.image part, ((Y/v:ℕ):ℝ)*sourceOriginalW1 P v :=
        hbase
    _ ≤ ∑ v ∈ S.image part, (Y:ℝ)*
      (sourceOriginalW1 P v/(v:ℝ)) := by
        apply Finset.sum_le_sum
        intro v hv
        have hq : ((Y/v:ℕ):ℝ) ≤ (Y:ℝ)/(v:ℝ) :=
          Nat.cast_div_le
        exact (mul_le_mul_of_nonneg_right hq
          (source_original_W1_nonneg P v)).trans_eq (by ring)
    _ = _ := by rw [Finset.mul_sum]

/-- Image values in the finite harmonic P tail have the CORRECT
original source support and exceed exactly the literal cutoff H. -/
theorem parity_original_P_part_finite_tail_support434
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (Y H v : ℕ)
    (hv : v ∈ ((Finset.Ioc 0 Y).filter
      (fun u => H < sourceOriginalPPrimePart (Finset.univ.biUnion P) u)).image
        (sourceOriginalPPrimePart (Finset.univ.biUnion P))) :
    H < v ∧ v ≠ 0 ∧ v.primeFactors ⊆ Finset.univ.biUnion P := by
  obtain ⟨u,hu,huv⟩ := Finset.mem_image.mp hv
  have hu' := Finset.mem_filter.mp hu
  have hu0 : u ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hu'.1).1
  have hAll : ∀ p ∈ Finset.univ.biUnion P, p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPrime g p hpg
  have hs := parity_native_canonical_P_part_supported434
    (Finset.univ.biUnion P) hAll u hu0
  have hcut : H < v := by
    have hh := hu'.2
    rw [huv] at hh
    exact hh
  have hs' : v ≠ 0 ∧ v.primeFactors ⊆ Finset.univ.biUnion P := by
    rw [huv] at hs
    exact hs
  exact ⟨hcut,hs'.1,hs'.2⟩

end Green64Analytic.ShiftTwoTerminal


open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option maxHeartbeats 6500000

/-- Bridge the positive-integer finite original W1 P-tail to the
GENUINE P-supported infinite harmonic series. Only summability of the
exact restricted source tail is required; no false density assumption. -/
theorem parity_original_P_part_finite_le_restricted_tsum434
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (Y H : ℕ)
    (hSumm : Summable
      (fun z : sourceOriginalPSupported (Finset.univ.biUnion P) =>
        if (H:ℝ) < (z.val:ℝ) then
          sourceOriginalW1 P z.val/(z.val:ℝ) else 0)) :
    let Pall := Finset.univ.biUnion P
    let part := sourceOriginalPPrimePart Pall
    let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
    (∑ u ∈ S, sourceOriginalW1 P u) ≤
      (Y:ℝ)*(∑' z : sourceOriginalPSupported Pall,
        if (H:ℝ)<(z.val:ℝ) then
          sourceOriginalW1 P z.val/(z.val:ℝ) else 0) := by
  dsimp only
  let Pall := Finset.univ.biUnion P
  let part := sourceOriginalPPrimePart Pall
  let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
  let T := S.image part
  have hSup (v : ℕ) (hv : v ∈ T) :
      v ≠ 0 ∧ v.primeFactors ⊆ Pall :=
    (parity_original_P_part_finite_tail_support434 P hPrime Y H v hv).2
  let emb : {v : ℕ // v ∈ T} → sourceOriginalPSupported Pall :=
    fun v => ⟨v.val, hSup v.val v.property⟩
  let t : Finset (sourceOriginalPSupported Pall) := T.attach.image emb
  have hInj : Set.InjOn emb ↑T.attach := by
    intro a ha b hb hab
    have hv : (a:ℕ) = (b:ℕ) :=
      congrArg (fun z : sourceOriginalPSupported Pall => z.val) hab
    exact Subtype.ext hv
  have hE : (∑ v ∈ T, sourceOriginalW1 P v/(v:ℝ)) =
      ∑ z ∈ t, sourceOriginalW1 P z.val/(z.val:ℝ) := by
    dsimp [t]
    rw [Finset.sum_image hInj]
    change (∑ v ∈ T, sourceOriginalW1 P v/(v:ℝ)) =
      ∑ z ∈ T.attach, sourceOriginalW1 P z.val/(z.val:ℝ)
    exact (Finset.sum_attach T (fun v => sourceOriginalW1 P v/(v:ℝ))).symm
  let f : sourceOriginalPSupported Pall → ℝ := fun z =>
    if (H:ℝ) < (z.val:ℝ) then
      sourceOriginalW1 P z.val/(z.val:ℝ) else 0
  have hf (z : sourceOriginalPSupported Pall) (hz : z ∈ t) :
      f z = sourceOriginalW1 P z.val/(z.val:ℝ) := by
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hz
    have hcut := (parity_original_P_part_finite_tail_support434
      P hPrime Y H v.val v.property).1
    have hval : z.val = v.val := (congrArg Subtype.val heq).symm
    have hcutReal : (H:ℝ) < (z.val:ℝ) := by
      rw [hval]
      exact_mod_cast hcut
    simp only [f, if_pos hcutReal]
  have hF : (∑ v ∈ T, sourceOriginalW1 P v/(v:ℝ)) =
      ∑ z ∈ t, f z := by
    rw [hE]
    apply Finset.sum_congr rfl
    intro z hz
    exact (hf z hz).symm
  have hRest (z : sourceOriginalPSupported Pall) : 0 ≤ f z := by
    dsimp only [f]
    split_ifs with hcut
    · exact div_nonneg (source_original_W1_nonneg P z.val)
        (by exact_mod_cast Nat.zero_le z.val)
    · exact le_refl _
  have hTsum : (∑ z ∈ t, f z) ≤ ∑' z, f z :=
    hSumm.sum_le_tsum t (fun z hz => hRest z)
  have hBasic := parity_original_P_part_finite_harmonic_bound434 P hPrime Y H
  dsimp only at hBasic
  calc
    (∑ u ∈ S, sourceOriginalW1 P u) ≤
        (Y:ℝ)*(∑ v ∈ T, sourceOriginalW1 P v/(v:ℝ)) :=
      hBasic
    _ = (Y:ℝ)*(∑ z ∈ t, f z) := by rw [hF]
    _ ≤ (Y:ℝ)*(∑' z, f z) :=
      mul_le_mul_of_nonneg_left hTsum (Nat.cast_nonneg _)
    _ = _ := rfl

end Green64Analytic.ShiftTwoTerminal

end

/-! ## ActualPPartTail -/

section

/- Exact native finite integer Rankin saving, followed by the actual moving
P-family. Original multiplicities, distinct-count W1 and true bands retained. -/


open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option maxHeartbeats 6800000

/-- Original W1 tail summed over ACTUAL positive integers, not just
harmonic source P-parts: fixed-P-part fibres cost at most Y/v, so
the existing original Rankin P-tail controls their weighted total. -/
theorem parity_original_P_part_finite_rankin_bound434
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (L σ : ℝ)
    (hL : 1 < L) (hσ : 0 < σ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h6 : ∀ g p, p ∈ P g → 6 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (hV4 : ∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4)
    (hLog : ∀ g p, p ∈ P g → Real.log (p:ℝ) ≤ L^(2/5:ℝ))
    (Y : ℕ) :
    let H := ⌊(Real.exp L)^σ⌋₊
    let Pall := Finset.univ.biUnion P
    let part := sourceOriginalPPrimePart Pall
    let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
    (∑ u ∈ S, sourceOriginalW1 P u) ≤
      (Y:ℝ)*(6*Real.exp 12)^(Fintype.card G)*
        Real.exp (-σ*L^(3/5:ℝ)) := by
  dsimp only
  let H := ⌊(Real.exp L)^σ⌋₊
  let Pall := Finset.univ.biUnion P
  let part := sourceOriginalPPrimePart Pall
  let S := (Finset.Ioc 0 Y).filter (fun u => H < part u)
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    have hh := h6 g p hp
    omega
  have hFull : Summable
      (fun z : sourceOriginalPSupported Pall =>
        sourceOriginalW1 P z.val/(z.val:ℝ)) :=
    (source_original_global_actual_P_normalized_harmonic_law
      P hPrime h3 hPn hDisj).1
  have hCutSumm : Summable
      (fun z : sourceOriginalPSupported Pall =>
        if (H:ℝ)<(z.val:ℝ) then
          sourceOriginalW1 P z.val/(z.val:ℝ) else 0) :=
    hFull.of_nonneg_of_le
      (fun z => by
        split_ifs
        · exact div_nonneg (source_original_W1_nonneg P z.val)
            (Nat.cast_nonneg _)
        · exact le_refl _)
      (fun z => by
        split_ifs
        · exact le_refl _
        · exact div_nonneg (source_original_W1_nonneg P z.val)
            (Nat.cast_nonneg _))
  have hFinite := parity_original_P_part_finite_le_restricted_tsum434
    P hPrime Y H hCutSumm
  dsimp only at hFinite
  have hTh : 0 ≤ (Real.exp L)^σ :=
    Real.rpow_nonneg (Real.exp_pos L).le _
  have hEq (z : sourceOriginalPSupported Pall) :
      ((H:ℝ) < (z.val:ℝ)) ↔ ((Real.exp L)^σ < (z.val:ℝ)) := by
    constructor
    · intro hz
      have hzNat : H < z.val := by exact_mod_cast hz
      have hSucc : (H+1:ℝ) ≤ (z.val:ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hzNat)
      exact (Nat.lt_floor_add_one ((Real.exp L)^σ)).trans_le hSucc
    · intro hz
      have hh : (H:ℝ) ≤ (Real.exp L)^σ :=
        Nat.floor_le hTh
      exact hh.trans_lt hz
  have hTailEq :
      (fun z : sourceOriginalPSupported Pall =>
        if (H:ℝ)<(z.val:ℝ) then
          sourceOriginalW1 P z.val/(z.val:ℝ) else 0) =
      (fun z : sourceOriginalPSupported Pall =>
        if (Real.exp L)^σ < (z.val:ℝ) then
          sourceOriginalW1 P z.val/(z.val:ℝ) else 0) := by
    funext z
    by_cases hz : (H:ℝ) < (z.val:ℝ)
    · have hz' := (hEq z).mp hz
      simp only [if_pos hz, if_pos hz']
    · have hz' : ¬((Real.exp L)^σ < (z.val:ℝ)) :=
        fun hh => hz ((hEq z).mpr hh)
      simp only [if_neg hz, if_neg hz']
  rw [hTailEq] at hFinite
  have hRankin := source_original_P_global_actual_rankin_tail
    P L σ hL hσ hPrime h6 hPn hDisj hV4 hLog
  calc
    (∑ u ∈ S, sourceOriginalW1 P u) ≤
      (Y:ℝ)*(∑' z : sourceOriginalPSupported Pall,
        if (Real.exp L)^σ < (z.val:ℝ) then
          sourceOriginalW1 P z.val/(z.val:ℝ) else 0) := hFinite
    _ ≤ (Y:ℝ)*((6*Real.exp 12)^(Fintype.card G)*
          Real.exp (-σ*L^(3/5:ℝ))) :=
      mul_le_mul_of_nonneg_left hRankin (Nat.cast_nonneg Y)
    _ = _ := by ring

end Green64Analytic.ShiftTwoTerminal


open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option maxHeartbeats 5600000

/-- The ACTUAL original moving P group family, NOT a substitute product
distribution: W1 mass over all positive u<=Y with a large actual P-part.
For fixed sigma and r, uniform in Y, the cost is a fixed power of L
times the proven stretched-exponential Rankin saving. -/
theorem parity_actual_P_part_finite_rankin_eventually434
    (r : ℕ) (hr : 1 ≤ r) (σ : ℝ) (hσ : 0 < σ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ Y : ℕ,
    let H := ⌊(Real.exp L)^σ⌋₊
    let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands r L)
    let part := sourceOriginalPPrimePart Pall
    (∑ u ∈ (Finset.Ioc 0 Y).filter (fun u => H < part u),
      sourceOriginalW1 (sourceOriginalPAllActualBands r L) u) ≤
      (Y:ℝ)* L^((3+(Real.log 2)⁻¹)*Real.log (6*Real.exp 12)) *
        Real.exp (-σ*L^(3/5:ℝ)) := by
  filter_upwards [source_original_P_all_actual_local_eventually r,
    eventually_ge_atTop (Real.exp 1)] with L hLocal hL
  intro Y
  dsimp only
  let P := sourceOriginalPAllActualBands r L
  let G := sourceOriginalPAllGroupType r L
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hExp : 1 < Real.exp (1:ℝ) := by
    have hh : Real.exp (0:ℝ) < Real.exp 1 :=
      Real.exp_strictMono (by norm_num)
    simpa using hh
  have hLgt : 1 < L := hExp.trans_le hL
  have hL1 : 1 ≤ L := hLgt.le
  have hPrime : ∀ g : G, ∀ p ∈ P g, p.Prime :=
    source_original_P_all_actual_band_prime r L
  have hDisj : ∀ g h : G, ∀ p ∈ P g, p ∈ P h → g=h :=
    source_original_P_actual_all_disjoint r L hr hLp
  have hLog : ∀ g : G, ∀ p ∈ P g,
      Real.log (p:ℝ) ≤ L^(2/5:ℝ) :=
    source_original_P_all_actual_band_log r L hL1
  have hRankin := parity_original_P_part_finite_rankin_bound434
    P L σ hLgt hσ hPrime hLocal.2.1 hLocal.1 hDisj
      hLocal.2.2 hLog Y
  dsimp only at hRankin
  have hPoly := source_original_P_all_group_factor_polylog
    r L hr hL
  have hStep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPoly (Nat.cast_nonneg Y))
    (Real.exp_pos (-σ*L^(3/5:ℝ))).le
  exact hRankin.trans hStep

end Green64Analytic.ShiftTwoTerminal

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option maxHeartbeats 5600000

/-- Every fixed real power is absorbed by the literal stretched-exponential
saving. This is proved from the actual limit, not supplied as a loss premise. -/
theorem parity_polylog_stretched_exp_loss434
    (C A σ δ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop,
      L^C * Real.exp (-σ * L^δ) ≤ L^(-A) := by
  have ht : Tendsto
      (fun L : ℝ => (L^δ)^((C+A)/δ) * Real.exp (-σ * L^δ))
      atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((C+A)/δ) σ hσ).comp (tendsto_rpow_atTop hδ)
  have hsmall := (tendsto_order.1 ht).2 1 (by norm_num)
  filter_upwards [hsmall, eventually_gt_atTop (0:ℝ)] with L hsmall hL
  have hEq : (L^δ)^((C+A)/δ) = L^(C+A) := by
    rw [← Real.rpow_mul hL.le]
    congr 1
    field_simp
  have hpos : 0 < L^A := Real.rpow_pos_of_pos hL _
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    L^A * (L^C * Real.exp (-σ * L^δ)) =
        L^(C+A) * Real.exp (-σ * L^δ) := by
      rw [Real.rpow_add hL]
      ring
    _ ≤ 1 := by rw [← hEq]; exact hsmall.le
    _ = L^A * L^(-A) := by
      rw [← Real.rpow_add hL]
      simp

/-- Parity's actual r0=20, sigma=1/44 original P-part half-threshold tail.
The full prime-power part retains all valuations; the genuine W1 uses
original distinct group divisors. Uniform in every natural endpoint cap Y. -/
theorem parity_actual_P_part_half_sigma_tail434 :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℕ,
    let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    let part := sourceOriginalPPrimePart Pall
    (∑ u ∈ (Finset.Ioc 0 Y).filter
      (fun u => ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < part u),
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) ≤
      (Y:ℝ) * L^((3+(Real.log 2)⁻¹)*Real.log (6*Real.exp 12)) *
        Real.exp (-(1/88:ℝ)*L^(3/5:ℝ)) := by
  filter_upwards [parity_actual_P_part_finite_rankin_eventually434
    20 (by norm_num) (1/88) (by norm_num)] with L h
  intro Y
  have hExp : (Real.exp L)^(1/88:ℝ) = Real.exp ((1/88:ℝ)*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp, mul_comm]
  simpa only [hExp] using h Y

/-- The same original half-threshold P-gate has arbitrary logarithmic
saving, still uniformly over the actual finite integer interval (0,Y]. -/
theorem parity_actual_P_part_half_sigma_all_log_saving434 (A : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℕ,
    let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    let part := sourceOriginalPPrimePart Pall
    (∑ u ∈ (Finset.Ioc 0 Y).filter
      (fun u => ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < part u),
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) ≤
      (Y:ℝ)*L^(-A) := by
  filter_upwards [parity_actual_P_part_half_sigma_tail434,
    parity_polylog_stretched_exp_loss434
      ((3+(Real.log 2)⁻¹)*Real.log (6*Real.exp 12)) A
      (1/88) (3/5) (by norm_num) (by norm_num)] with L hTail hLoss
  intro Y
  exact (hTail Y).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hLoss (Nat.cast_nonneg Y))

end Green64Analytic.ShiftTwoTerminal

end

/-! ## HarmonicPGate -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

/-- The literal ORIGINAL physical P cap at D_R*n, with full valuations.
The weight is the genuine W1 of the stripped endpoint; the half threshold
is not part of this definition. -/
def parityPhysicalPcapBadWeight434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (L : ℝ) (DR n : ℕ) : ℝ :=
  if ⌊Real.exp ((1/44:ℝ)*L)⌋₊ <
      sourceOriginalPPrimePart (Finset.univ.biUnion P) (DR*n)
  then sourceOriginalW1 P n else 0

/-- The explicit two-endpoint harmonic P-gate envelope retains the true
shared reciprocal 1/D_R. It is defined using the original physical gates
at D_R*n and D_R*(n+s), not a desired half-threshold majorant. -/
def parityPhysicalPcapHarmonicEnvelope434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (L : ℝ) (DR : ℕ) (X : ℝ) (s : ℤ) (psi : ℝ → ℂ) (M : ℕ) : ℝ :=
  (DR:ℝ)⁻¹ * ∑ n ∈ Finset.Ioc 0 M, ‖psi ((n:ℝ)/X)‖/(n:ℝ) *
    (parityPhysicalPcapBadWeight434 P L DR n +
      parityPhysicalPcapBadWeight434 P L DR ((n:ℤ)+s).toNat)

theorem parity_physical_Pcap_bad_weight_nonneg434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (L : ℝ) (DR n : ℕ) :
    0 ≤ parityPhysicalPcapBadWeight434 P L DR n := by
  unfold parityPhysicalPcapBadWeight434
  split_ifs
  · exact source_original_W1_nonneg P n
  · exact le_refl _

/-- B575 applies to the literal physical gate only after the support and
subexponential size of the SAME shared D_R are supplied. Repeated prime
factors remain in the original Ppart throughout. -/
theorem parity_physical_Pcap_bad_weight_le_half_tail434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (L : ℝ) (DR n : ℕ)
    (hDR : 0 < DR) (hn : 0 < n)
    (hSupport : DR.primeFactors ⊆ Finset.univ.biUnion P)
    (hSmall : (DR:ℝ) ≤ Real.exp ((1/88:ℝ)*L)) :
    parityPhysicalPcapBadWeight434 P L DR n ≤
      if ⌊Real.exp ((1/88:ℝ)*L)⌋₊ <
        sourceOriginalPPrimePart (Finset.univ.biUnion P) n
      then sourceOriginalW1 P n else 0 := by
  classical
  unfold parityPhysicalPcapBadWeight434
  split_ifs with hfail htail htail
  · exact le_refl _
  · have hhalf : ⌊Real.exp ((1/88:ℝ)*L)⌋₊ <
        sourceOriginalPPrimePart (Finset.univ.biUnion P) n := by
      have hh := b575_failed_physical_Pcap_has_stripped_tail
        (Finset.univ.biUnion P) DR n (1/44) L hDR hn hSupport
        (by norm_num only [show (1/44:ℝ)/2=1/88 by norm_num]; exact hSmall) hfail
      norm_num only [show (1/44:ℝ)/2=1/88 by norm_num] at hh
      exact hh
    exact False.elim (htail hhalf)
  · exact source_original_W1_nonneg P n
  · exact le_refl _

/-- Nonnegative weights are transported through a signed integer shift
with an actual injective positive endpoint map. -/
theorem parity_translated_nonnegative_sum_le434
    (S : Finset ℕ) (Y : ℕ) (s : ℤ) (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n)
    (hS : ∀ n ∈ S, 0 < (n:ℤ)+s ∧ (n:ℤ)+s ≤ (Y:ℤ)) :
    (∑ n ∈ S, F ((n:ℤ)+s).toNat) ≤ ∑ n ∈ Finset.Ioc 0 Y, F n := by
  classical
  let f : ℕ → ℕ := fun n => ((n:ℤ)+s).toNat
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro a ha b hb hab
    have hpa := (hS a ha).1
    have hpb := (hS b hb).1
    change ((a:ℤ)+s).toNat = ((b:ℤ)+s).toNat at hab
    omega
  have hsub : S.image f ⊆ Finset.Ioc 0 Y := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    have hh := hS a ha
    rw [Finset.mem_Ioc]
    dsimp only [f]
    omega
  calc
    _ = ∑ n ∈ S.image f, F n := by
      symm
      exact Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot => hF n)

/-- Actual full-cap failure mass is controlled by the proven half-Ppart
mass. This finite transfer does not declare the original gate invariant. -/
theorem parity_physical_Pcap_bad_weight_sum434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (L : ℝ) (DR Y : ℕ) (F : ℝ)
    (hDR : 0 < DR)
    (hSupport : DR.primeFactors ⊆ Finset.univ.biUnion P)
    (hSmall : (DR:ℝ) ≤ Real.exp ((1/88:ℝ)*L))
    (hTail : (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n =>
      ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart (Finset.univ.biUnion P) n),
      sourceOriginalW1 P n) ≤ (Y:ℝ)*F) :
    (∑ n ∈ Finset.Ioc 0 Y, parityPhysicalPcapBadWeight434 P L DR n) ≤ (Y:ℝ)*F := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 Y,
        if ⌊Real.exp ((1/88:ℝ)*L)⌋₊ <
            sourceOriginalPPrimePart (Finset.univ.biUnion P) n
        then sourceOriginalW1 P n else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      exact parity_physical_Pcap_bad_weight_le_half_tail434 P L DR n hDR
        (Finset.mem_Ioc.mp hn).1 hSupport hSmall
    _ = ∑ n ∈ (Finset.Ioc 0 Y).filter (fun n =>
        ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart (Finset.univ.biUnion P) n),
        sourceOriginalW1 P n := by rw [Finset.sum_filter]
    _ ≤ _ := hTail


/-- The ORIGINAL two-endpoint physical P-gate envelope is bounded by its
actual half-tail mass. The factor 1/D_R is retained exactly on both sides. -/
theorem parity_harmonic_physical_Pcap_bound434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (L X K Cpsi F : ℝ) (hL : 0 < L) (hX : 1 ≤ X) (hK : 0 ≤ K) (hF : 0 ≤ F)
    (DR : ℕ) (hDR : 0 < DR)
    (hSupport : DR.primeFactors ⊆ Finset.univ.biUnion P)
    (hSmall : (DR:ℝ) ≤ Real.exp ((1/88:ℝ)*L))
    (s : ℤ) (hs : |(s:ℝ)| ≤ X/128)
    (hTail : ∀ Y : ℕ, (∑ n ∈ (Finset.Ioc 0 Y).filter (fun n =>
      ⌊Real.exp ((1/88:ℝ)*L)⌋₊ < sourceOriginalPPrimePart (Finset.univ.biUnion P) n),
      sourceOriginalW1 P n) ≤ (Y:ℝ)*F)
    (psi : ℝ → ℂ)
    (hSupp : ∀ t, psi t ≠ 0 → t ∈ Set.Icc (1/64:ℝ) 64)
    (hPsi : ∀ t, ‖psi t‖ ≤ K*L^Cpsi) (M : ℕ) :
    parityPhysicalPcapHarmonicEnvelope434 P L DR X s psi M ≤
      (128*66:ℝ)*(DR:ℝ)⁻¹*K*L^Cpsi*F := by
  classical
  let S : Finset ℕ := (Finset.Ioc 0 M).filter (fun n : ℕ => psi ((n:ℝ)/X) ≠ 0)
  let Y : ℕ := ⌈65*X⌉₊
  let B : ℝ := 64*K*L^Cpsi/X
  let W : ℕ → ℝ := parityPhysicalPcapBadWeight434 P L DR
  have hXp : 0 < X := by linarith
  have hDRp : 0 < (DR:ℝ) := by exact_mod_cast hDR
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hW : ∀ n, 0 ≤ W n := parity_physical_Pcap_bad_weight_nonneg434 P L DR
  have hgeom (n : ℕ) (hn : n ∈ S) :=
    parity_harmonic_cutoff_shift_support434 X hXp s hs psi hSupp n
      (Finset.mem_filter.mp hn).2
  have hS : S ⊆ Finset.Ioc 0 Y := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp
      (Finset.mem_filter.mp hn).1).1,(hgeom n hn).2.2.1⟩
  have hShift : ∀ n ∈ S, 0 < (n:ℤ)+s ∧ (n:ℤ)+s ≤ (Y:ℤ) := by
    intro n hn
    exact ⟨(hgeom n hn).1,(hgeom n hn).2.1⟩
  have hwhole : (∑ n ∈ Finset.Ioc 0 Y, W n) ≤ (Y:ℝ)*F :=
    parity_physical_Pcap_bad_weight_sum434 P L DR Y F hDR hSupport hSmall (hTail Y)
  have hfirst : (∑ n ∈ S, W n) ≤ (Y:ℝ)*F :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun n hn hnot => hW n)).trans hwhole
  have hsecond : (∑ n ∈ S, W ((n:ℤ)+s).toNat) ≤ (Y:ℝ)*F :=
    (parity_translated_nonnegative_sum_le434 S Y s W hW hShift).trans hwhole
  have hpair : (∑ n ∈ S, (W n+W ((n:ℤ)+s).toNat)) ≤ 2*(Y:ℝ)*F := by
    rw [Finset.sum_add_distrib]
    linarith
  have hcoef (n : ℕ) (hn : n ∈ S) : ‖psi ((n:ℝ)/X)‖/(n:ℝ) ≤ B := by
    have hnpos : 0 < (n:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1
    apply (div_le_iff₀ hnpos).mpr
    calc
      _ ≤ K*L^Cpsi := hPsi _
      _ = B*(X/64) := by dsimp [B]; field_simp
      _ ≤ B*(n:ℝ) := mul_le_mul_of_nonneg_left (hgeom n hn).2.2.2 hB
  have hY : (Y:ℝ) ≤ 66*X := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 65*X by positivity)
    dsimp only [Y]
    linarith
  have heq : parityPhysicalPcapHarmonicEnvelope434 P L DR X s psi M =
      (DR:ℝ)⁻¹ * ∑ n ∈ S, ‖psi ((n:ℝ)/X)‖/(n:ℝ) *
        (W n+W ((n:ℤ)+s).toNat) := by
    unfold parityPhysicalPcapHarmonicEnvelope434
    congr 1
    symm
    dsimp only [S,W]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs with hh
    · rfl
    · have hz : psi ((n:ℝ)/X)=0 := not_ne_iff.mp hh
      simp only [hz,norm_zero,zero_div,zero_mul]
  rw [heq]
  calc
    _ ≤ (DR:ℝ)⁻¹ * (B*(∑ n ∈ S, (W n+W ((n:ℤ)+s).toNat))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (hcoef n hn) (add_nonneg (hW n) (hW _))
    _ ≤ (DR:ℝ)⁻¹ * (B*(2*(Y:ℝ)*F)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair hB) (by positivity)
    _ ≤ (DR:ℝ)⁻¹ * (B*(2*(66*X)*F)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hB
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hY (by norm_num)) hF
    _ = (128*66:ℝ)*(DR:ℝ)⁻¹*K*L^Cpsi*F := by
      dsimp only [B]
      field_simp <;> ring

/-- Quantitative removal support for BOTH ORIGINAL physical P gates of
an actual r20 frame. Every W1 tail and every D_R/DC/Z/k gate is derived.
A and Cpsi are fixed BEFORE the threshold; the true 1/D_R remains outside. -/
theorem parity_eventually_actual_physical_Pcap_harmonic_saving434
    (J : ℕ) (CZ Ck Cpsi A : ℝ) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop, 1 < L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (m : ℕ) (Nu : Type) [Fintype Nu]
      (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
      (positions : Finset ℤ) (x : B654ActualParityState434 L hS J positions)
      (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
        (SourceNativeMemoryBP434 20 L) J 1 m patterns)
      (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
    ∀ (k : ℤ), |(k:ℝ)| ≤ L^Ck →
    ∀ (K : ℝ), 0 ≤ K →
    ∀ (psi : ℝ → ℂ),
      (∀ t, psi t ≠ 0 → t ∈ Set.Icc (1/64:ℝ) 64) →
      (∀ t, ‖psi t‖ ≤ K*L^Cpsi) →
    ∀ M : ℕ,
      let DR := parityFrameSharedD434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x.val.2 f
      let DC := parityFrameAuxD434 (SourceNativeMemoryBP434 20 L)
        (fun _ p => p.val) J 1 m patterns f
      parityPhysicalPcapHarmonicEnvelope434 (sourceOriginalPAllActualBands 20 L)
        L DR (Z*(DC:ℝ)) (2*k*(DC:ℤ)) psi M ≤
        (128*66:ℝ)*(DR:ℝ)⁻¹*K*L^(-A) := by
  filter_upwards [parity_eventually_harmonic_scale_budget434 CZ Ck hCZ,
    parity_eventually_actual_frame_shared_half_Pcap434 J,
    b651_eventually_parity_window_sqrt434 J 0 (by norm_num),
    parity_actual_P_part_half_sigma_all_log_saving434 (A+Cpsi),
    eventually_gt_atTop (1:ℝ)] with L hBudget hSmall hW hTail hL
  refine ⟨hL,?_⟩
  intro hS m Nu inst patterns positions x f Z hZlo hZhi k hk K hK psi hSupp hPsi M
  dsimp only
  let P := sourceOriginalPAllActualBands 20 L
  let DR := parityFrameSharedD434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  let DC := parityFrameAuxD434 (SourceNativeMemoryBP434 20 L)
    (fun _ p => p.val) J 1 m patterns f
  have hDR : 0 < DR := parity_frame_shared_D_pos434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x.val.2 f
  have hDC : 0 < DC := parity_frame_aux_D_pos434
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m patterns f
  have hSupport : DR.primeFactors ⊆ Finset.univ.biUnion P := by
    change DR.primeFactors ⊆ sourceNativeOriginalG434 20 L
    exact parity_actual_frame_shared_P_support434 L hL hS J m patterns positions x f
  have hDRsmall : (DR:ℝ) ≤ Real.exp ((1/88:ℝ)*L) :=
    hSmall.2 hS m Nu patterns positions x f
  have hDChi : (DC:ℝ) ≤ Real.exp (Real.sqrt L) :=
    (parity_actual_frame_aux_window434 L hW.1 hS J m patterns x.val.2 f).trans hW.2
  have hb := hBudget.2 Z hZlo hZhi DC hDC hDChi k hk
  have hLp : 0 < L := by linarith
  have hbound := parity_harmonic_physical_Pcap_bound434 P L (Z*(DC:ℝ)) K Cpsi
    (L^(-(A+Cpsi))) hLp hb.1 hK (Real.rpow_nonneg hLp.le _) DR hDR
    hSupport hDRsmall (2*k*(DC:ℤ)) hb.2.1 hTail psi hSupp hPsi M
  have hpow : L^Cpsi*L^(-(A+Cpsi))=L^(-A) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ (128*66:ℝ)*(DR:ℝ)⁻¹*K*L^Cpsi*L^(-(A+Cpsi)) := hbound
    _ = ((128*66:ℝ)*(DR:ℝ)⁻¹*K)*(L^Cpsi*L^(-(A+Cpsi))) := by ring
    _ = _ := by rw [hpow]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ParamActualPPartTail -/

section

open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.ShiftTwoTerminal
open SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- TRUE original moving r=20 P-part Rankin tail at a freely chosen
positive Parity b_* / 8 threshold. This is the full valuation-counted
P-part and original distinct-mark W1, uniform over every Y; it does NOT
assume b_* >= 1/11 or reuse the old fixed 1/88 threshold. -/
theorem parity_actual_P_part_beta_eighth_tail434
    (beta : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℕ,
      let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
      let part := sourceOriginalPPrimePart Pall
      (∑ u ∈ (Finset.Ioc 0 Y).filter
        (fun u => ⌊Real.exp ((beta/8)*L)⌋₊ < part u),
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) ≤
        (Y:ℝ) * L^((3+(Real.log 2)⁻¹)*Real.log (6*Real.exp 12)) *
          Real.exp (-(beta/8)*L^(3/5:ℝ)) := by
  filter_upwards [parity_actual_P_part_finite_rankin_eventually434
    20 (by norm_num) (beta/8) (by linarith)] with L h
  intro Y
  have hExp : (Real.exp L)^(beta/8) = Real.exp ((beta/8)*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp, mul_comm]
  simpa only [hExp] using h Y

/-- With the genuinely beta-dependent half-cap exp(beta*L/8), every
fixed inverse-log precision A is available BEFORE the Type II data are
chosen, uniformly over the literal physical interval (0,Y]. This only
proves the W1 tail, not arbitrary-capped Parity (4.17) cancellation. -/
theorem parity_actual_P_part_beta_eighth_all_log_saving434
    (beta A : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℕ,
      let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
      let part := sourceOriginalPPrimePart Pall
      (∑ u ∈ (Finset.Ioc 0 Y).filter
        (fun u => ⌊Real.exp ((beta/8)*L)⌋₊ < part u),
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) ≤
        (Y:ℝ) * L^(-A) := by
  filter_upwards [parity_actual_P_part_beta_eighth_tail434 beta hbeta,
    parity_polylog_stretched_exp_loss434
      ((3+(Real.log 2)⁻¹)*Real.log (6*Real.exp 12)) A
      (beta/8) (3/5) (by linarith) (by norm_num)] with L hTail hLoss
  intro Y
  exact (hTail Y).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hLoss (Nat.cast_nonneg Y))

/-- Exactly the actual Parity b_*-dependent physical retained cap H,
not a half-cap: if the full P-prime-power part exceeds
floor(exp(beta*L/4)), its ORIGINAL W1 mass has a stretched-exponential
tail for every fixed positive beta and every finite physical endpoint. -/
theorem parity_actual_P_part_beta_quarter_tail434
    (beta : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℕ,
      let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
      let part := sourceOriginalPPrimePart Pall
      (∑ u ∈ (Finset.Ioc 0 Y).filter
        (fun u => ⌊Real.exp ((beta/4)*L)⌋₊ < part u),
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) ≤
        (Y:ℝ) * L^((3+(Real.log 2)⁻¹)*Real.log (6*Real.exp 12)) *
          Real.exp (-(beta/4)*L^(3/5:ℝ)) := by
  filter_upwards [parity_actual_P_part_finite_rankin_eventually434
    20 (by norm_num) (beta/4) (by linarith)] with L h
  intro Y
  have hExp : (Real.exp L)^(beta/4) = Real.exp ((beta/4)*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L), Real.log_exp, mul_comm]
  simpa only [hExp] using h Y

/-- Arbitrary inverse-log saving for discarding the EXACT same original
beta/4 P cap used by the physical Gram kernel; this is a genuine
unsigned W1-mass estimate, not yet the signed two-endpoint Parity(4.17). -/
theorem parity_actual_P_part_beta_quarter_all_log_saving434
    (beta A : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℕ,
      let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
      let part := sourceOriginalPPrimePart Pall
      (∑ u ∈ (Finset.Ioc 0 Y).filter
        (fun u => ⌊Real.exp ((beta/4)*L)⌋₊ < part u),
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) ≤
        (Y:ℝ) * L^(-A) := by
  filter_upwards [parity_actual_P_part_beta_quarter_tail434 beta hbeta,
    parity_polylog_stretched_exp_loss434
      ((3+(Real.log 2)⁻¹)*Real.log (6*Real.exp 12)) A
      (beta/4) (3/5) (by linarith) (by norm_num)] with L hTail hLoss
  intro Y
  exact (hTail Y).trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hLoss (Nat.cast_nonneg Y))
end Green64Analytic.ShiftTwoTerminal

end

/-! ## RestorationGroupBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

/-- Expose the exact all-index bound already used inside B578. This counts
all original indices before any SMALL/BIG split or distinguished-index erase. -/
theorem parity_original_all_group_indices_card_four434
    (r : ℕ) (L : ℝ) (hL : Real.exp 2 ≤ L) :
    ((sourceOriginalPAllGroupIndices r L).card : ℝ) ≤ 4*Real.log L := by
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
  have hc : (sourceOriginalPAllGroupIndices r L).card ≤ sourceOriginalPAllIndexBound L :=
    (Finset.card_filter_le _ _).trans (by simp)
  have hcr : ((sourceOriginalPAllGroupIndices r L).card:ℝ) ≤
      (sourceOriginalPAllIndexBound L:ℝ) := by exact_mod_cast hc
  linarith

/-- Actual full groups are exactly all original indices. Option restores the
original distinguished SMALL S index; it is not dropped from the count. -/
theorem parity_actual_full_group_card_identity434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) :
    Fintype.card (B645ActualGroup434 L hS) = (sourceOriginalPAllGroupIndices 20 L).card := by
  change Fintype.card
    (SourceNativeMemorySG434 20 L hS ⊕ sourceNativeOriginalBigType434 20 L) = _
  rw [Fintype.card_sum]
  symm
  simpa only [SourceNativeMemorySG434,Fintype.card_option] using
    source_native_original_all_card434 20 L hS hL

/-- A stronger complete r20 group budget, including distinguished S. -/
theorem parity_actual_full_group_card_four434
    (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) :
    (Fintype.card (B645ActualGroup434 L hS):ℝ) ≤ 4*Real.log L := by
  have he : (1:ℝ) < Real.exp 2 := by
    simpa only [Real.exp_zero] using
      Real.exp_strictMono (show (0:ℝ)<2 by norm_num)
  rw [parity_actual_full_group_card_identity434 L (he.trans_le hL) hS]
  exact parity_original_all_group_indices_card_four434 20 L hL

/-- The requested conservative full-family coefficient eight follows without
adding a spurious extra distinguished group or changing the original carrier. -/
theorem parity_actual_full_group_card_eight434
    (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) :
    (Fintype.card (B645ActualGroup434 L hS):ℝ) ≤ 8*Real.log L := by
  have hc := parity_actual_full_group_card_four434 L hL hS
  have hn : (0:ℝ) ≤ (Fintype.card (B645ActualGroup434 L hS):ℝ) := Nat.cast_nonneg _
  linarith

/-- The complete native two-endpoint q0=1/2 damping loss has exactly the
requested logarithmic budget, with every actual SMALL and BIG group counted. -/
theorem parity_actual_full_damping_log_budget434
    (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ) :
    (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) ≤
      L^(16*(J+1:ℝ)*Real.log 2) := by
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hc := parity_actual_full_group_card_eight434 L hL hS
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfactor : 0 ≤ 2*(J+1:ℝ)*Real.log 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hc hfactor
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by
    simpa only [one_div] using Real.log_inv (2:ℝ)
  rw [Real.rpow_def_of_pos (show (0:ℝ)<1/2 by norm_num),
    Real.rpow_def_of_pos hLp,hhalf]
  apply Real.exp_le_exp.mpr
  convert hm using 1 <;> push_cast <;> ring

/-- A single actual-scale event exposes both budgets. The threshold does not
depend on J; the displayed damping exponent retains its exact J dependence. -/
theorem parity_eventually_actual_restoration_group_budget434 :
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
    ∀ hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty,
      (Fintype.card (B645ActualGroup434 L hS):ℝ) ≤ 8*Real.log L ∧
      ∀ J : ℕ,
        (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) ≤
          L^(16*(J+1:ℝ)*Real.log 2) := by
  filter_upwards [eventually_ge_atTop (Real.exp (2:ℝ))] with L hL
  exact ⟨hL,fun hS => ⟨parity_actual_full_group_card_eight434 L hL hS,
    fun J => parity_actual_full_damping_log_budget434 L hL hS J⟩⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## StrippedKernelLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 26000
set_option linter.unusedSectionVars false

/-- Coherence of the ORIGINAL chosen free-slot enumeration when the
actual freed set is unchanged. Equal counts alone are not used to identify
different enumerations: the hypothesis is equality of the finite sets. -/
theorem parity_original_free_slot_cast434
    (J ell : ℕ) (C D : Finset (Fin J)) (hCD : C=D)
    (hcount : ell+C.card=ell+D.card) (i : Fin (ell+C.card)) :
    (sourceOriginalFreeSlotEquiv434 J ell C i).val =
      (sourceOriginalFreeSlotEquiv434 J ell D (finCongr hcount i)).val := by
  subst D
  simp only [finCongr_refl,Equiv.refl_apply]

variable {SG BG : Type} [Fintype SG] [DecidableEq SG] [Fintype BG] [DecidableEq BG]

/-- Explicit transport from the lifted BIG free index to its original
index. It changes the dependent type using the proved exact free count. -/
def parityFullProbeBigFreeEquiv434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : BG) :
    Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inr g)) ≃
    Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) :=
  finCongr (parity_full_probe_free_count_big434 (SG:=SG) J ell m hmJ nu g)

/-- Every lifted SMALL group has its original ell unshared endpoint slots.
At Parity ell=1 this is the genuine one-mark type, not a chosen singleton. -/
def parityFullProbeSmallFreeEquiv434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : SG) :
    Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inl g)) ≃ Fin ell :=
  finCongr (parity_full_probe_free_count_small434 J ell m hmJ nu g)

/-- The BIG index transport preserves the actual physical slot selected
by sourceOriginalProbeFreeMarkEquiv434, including its original enumeration. -/
theorem parity_full_probe_big_free_coordinate434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : BG)
    (i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inr g))) :
    (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inr g) i).val =
    (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ nu g
      (parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu g i)).val := by
  exact parity_original_free_slot_cast434 J ell
    (sourceOriginalProbeFreedSlots434 J m hmJ (parityFullProbePattern434 SG m nu) (Sum.inr g))
    (sourceOriginalProbeFreedSlots434 J m hmJ nu g)
    (parity_full_probe_freed_big434 J m hmJ nu g)
    (parity_full_probe_free_count_big434 J ell m hmJ nu g) i

/-- SMALL extraction uses the same original empty-freed-set enumeration.
No assertion that this chosen enumeration is in increasing order is made. -/
theorem parity_full_probe_small_free_coordinate434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) (g : SG)
    (i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inl g))) :
    (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inl g) i).val =
    (sourceOriginalFreeSlotEquiv434 J ell ∅
      (parityFullProbeSmallFreeEquiv434 J ell m hmJ nu g i)).val := by
  exact parity_original_free_slot_cast434 J ell
    (sourceOriginalProbeFreedSlots434 J m hmJ (parityFullProbePattern434 SG m nu) (Sum.inl g))
    ∅ (parity_full_probe_freed_small434 J m hmJ nu g)
    (parity_full_probe_free_count_small434 J ell m hmJ nu g) i

/-- Lift complete dependent free endpoint arrays. The construction uses
only the pattern and actual counts; it never refers to auxiliary draws. -/
def parityFullProbeFreeLift434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (small : SG → Fin ell → ℕ)
    (big : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    ∀ g : SG ⊕ BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) g) → ℕ
  | Sum.inl g => fun i => small g (parityFullProbeSmallFreeEquiv434 J ell m hmJ nu g i)
  | Sum.inr g => fun i => big g (parityFullProbeBigFreeEquiv434 J ell m hmJ nu g i)

@[simp] theorem parity_full_probe_free_lift_small434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (small : SG → Fin ell → ℕ)
    (big : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (g : SG)
    (i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inl g))) :
    parityFullProbeFreeLift434 J ell m hmJ nu small big (Sum.inl g) i =
      small g (parityFullProbeSmallFreeEquiv434 J ell m hmJ nu g i) := rfl

@[simp] theorem parity_full_probe_free_lift_big434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (small : SG → Fin ell → ℕ)
    (big : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (g : BG)
    (i : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.inr g))) :
    parityFullProbeFreeLift434 J ell m hmJ nu small big (Sum.inr g) i =
      big g (parityFullProbeBigFreeEquiv434 J ell m hmJ nu g i) := rfl

/-- Exact bijection of complete free endpoint arrays. Source and target
arrays may be chosen independently or tested by any coupled function. -/
def parityFullProbeFreeArrayEquiv434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m) :
    ((SG → Fin ell → ℕ) ×
      (∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)) ≃
    (∀ g : SG ⊕ BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ
      (parityFullProbePattern434 SG m nu) g) → ℕ) where
  toFun a := parityFullProbeFreeLift434 J ell m hmJ nu a.1 a.2
  invFun a :=
    (fun g i => a (Sum.inl g) ((parityFullProbeSmallFreeEquiv434 J ell m hmJ nu g).symm i),
     fun g i => a (Sum.inr g) ((parityFullProbeBigFreeEquiv434 J ell m hmJ nu g).symm i))
  left_inv a := by
    apply Prod.ext
    · funext g i
      simp only [parity_full_probe_free_lift_small434,Equiv.apply_symm_apply]
    · funext g i
      simp only [parity_full_probe_free_lift_big434,Equiv.apply_symm_apply]
  right_inv a := by
    funext g i
    cases g with
    | inl g => simp only [parity_full_probe_free_lift_small434,Equiv.symm_apply_apply]
    | inr g => simp only [parity_full_probe_free_lift_big434,Equiv.symm_apply_apply]

/-- A selected original first-m probe is transported to its EXACT original
free index, not merely to an equal-size free array. -/
theorem parity_full_probe_free_index434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (g : BG) (j : Fin m) (hj : (g,j) ∈ nu.1 ∨ (g,j) ∈ nu.2) :
    parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu g
      (sourceOriginalProbeFreeIndex434 J ell m hmJ (parityFullProbePattern434 SG m nu)
        (Sum.inr g) j (by
          simpa only [parityFullProbePattern434,parity_probe_map_mem_inr434] using hj)) =
    sourceOriginalProbeFreeIndex434 J ell m hmJ nu g j hj := by
  have hc := parity_full_probe_big_free_coordinate434 (SG:=SG) J ell m hmJ nu g
    (sourceOriginalProbeFreeIndex434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      (Sum.inr g) j (by
        simpa only [parityFullProbePattern434,parity_probe_map_mem_inr434] using hj))
  apply (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ nu g).injective
  apply Subtype.ext
  simpa only [sourceOriginalProbeFreeIndex434,Equiv.apply_symm_apply] using hc.symm

theorem parity_full_probe_free_lift_selected434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (small : SG → Fin ell → ℕ)
    (big : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ)
    (g : BG) (j : Fin m) (hj : (g,j) ∈ nu.1 ∨ (g,j) ∈ nu.2) :
    parityFullProbeFreeLift434 J ell m hmJ nu small big (Sum.inr g)
      (sourceOriginalProbeFreeIndex434 J ell m hmJ (parityFullProbePattern434 SG m nu)
        (Sum.inr g) j (by
          simpa only [parityFullProbePattern434,parity_probe_map_mem_inr434] using hj)) =
    big g (sourceOriginalProbeFreeIndex434 J ell m hmJ nu g j hj) := by
  exact congrArg (big g) (parity_full_probe_free_index434 (SG:=SG) J ell m hmJ nu g j hj)

/-- Every selected TARGET free mark, including repetitions of its numeric
value, remains in the original global product X_A. -/
theorem parity_full_probe_free_target_X434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (small : SG → Fin ell → ℕ)
    (big : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceOriginalProbeFreeTargetX434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      (parityFullProbeFreeLift434 J ell m hmJ nu small big) =
    sourceOriginalProbeFreeTargetX434 J ell m hmJ nu big := by
  unfold sourceOriginalProbeFreeTargetX434
  symm
  apply Fintype.prod_equiv (parityProbeSelectionEquiv434 SG m nu.1)
  intro z
  exact (parity_full_probe_free_lift_selected434 J ell m hmJ nu small big
    z.val.1 z.val.2 (Or.inl z.property)).symm

/-- The same exact transport holds for the original SOURCE free product X_B. -/
theorem parity_full_probe_free_source_X434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (small : SG → Fin ell → ℕ)
    (big : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceOriginalProbeFreeSourceX434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      (parityFullProbeFreeLift434 J ell m hmJ nu small big) =
    sourceOriginalProbeFreeSourceX434 J ell m hmJ nu big := by
  unfold sourceOriginalProbeFreeSourceX434
  symm
  apply Fintype.prod_equiv (parityProbeSelectionEquiv434 SG m nu.2)
  intro z
  exact (parity_full_probe_free_lift_selected434 J ell m hmJ nu small big
    z.val.1 z.val.2 (Or.inr z.property)).symm

/-- The literal B574 free-mark ban is preserved by the actual auxiliary
and free-index bijections. The statement contains only inequality with
endpoint MARKS; no cofactor divisibility or clean event is substituted. -/
theorem parity_full_probe_free_aux_ban434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (ss st : SG → Fin ell → ℕ)
    (bs bt : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceB574FreeAuxBan434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      (parityFullProbeAuxLift434 SG m nu aux)
      (parityFullProbeFreeLift434 J ell m hmJ nu ss bs)
      (parityFullProbeFreeLift434 J ell m hmJ nu st bt) ↔
    sourceB574FreeAuxBan434 J ell m hmJ nu aux bs bt := by
  constructor
  · intro h z i
    rcases z with z | z
    · let e := parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu z.val.1
      have hh := h (parityFullProbeAuxEquiv434 SG m nu (Sum.inl z)) (e.symm i)
      change
        parityFullProbeAuxLift434 SG m nu aux (parityFullProbeAuxEquiv434 SG m nu (Sum.inl z)) ≠
          bs z.val.1 (e (e.symm i)) ∧
        parityFullProbeAuxLift434 SG m nu aux (parityFullProbeAuxEquiv434 SG m nu (Sum.inl z)) ≠
          bt z.val.1 (e (e.symm i)) at hh
      rw [e.apply_symm_apply i,parity_full_probe_aux_lift_apply434] at hh
      exact hh
    · let e := parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu z.val.1
      have hh := h (parityFullProbeAuxEquiv434 SG m nu (Sum.inr z)) (e.symm i)
      change
        parityFullProbeAuxLift434 SG m nu aux (parityFullProbeAuxEquiv434 SG m nu (Sum.inr z)) ≠
          bs z.val.1 (e (e.symm i)) ∧
        parityFullProbeAuxLift434 SG m nu aux (parityFullProbeAuxEquiv434 SG m nu (Sum.inr z)) ≠
          bt z.val.1 (e (e.symm i)) at hh
      rw [e.apply_symm_apply i,parity_full_probe_aux_lift_apply434] at hh
      exact hh
  · intro h z i
    obtain ⟨z,rfl⟩ := (parityFullProbeAuxEquiv434 SG m nu).surjective z
    rcases z with z | z
    · change
        parityFullProbeAuxLift434 SG m nu aux (parityFullProbeAuxEquiv434 SG m nu (Sum.inl z)) ≠
          bs z.val.1 (parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu z.val.1 i) ∧
        parityFullProbeAuxLift434 SG m nu aux (parityFullProbeAuxEquiv434 SG m nu (Sum.inl z)) ≠
          bt z.val.1 (parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu z.val.1 i)
      rw [parity_full_probe_aux_lift_apply434]
      exact h (Sum.inl z) (parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu z.val.1 i)
    · change
        parityFullProbeAuxLift434 SG m nu aux (parityFullProbeAuxEquiv434 SG m nu (Sum.inr z)) ≠
          bs z.val.1 (parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu z.val.1 i) ∧
        parityFullProbeAuxLift434 SG m nu aux (parityFullProbeAuxEquiv434 SG m nu (Sum.inr z)) ≠
          bt z.val.1 (parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu z.val.1 i)
      rw [parity_full_probe_aux_lift_apply434]
      exact h (Sum.inr z) (parityFullProbeBigFreeEquiv434 (SG:=SG) J ell m hmJ nu z.val.1 i)

/-- Exact canonical stripped Knu before its original free-mark guard.
The inherited actual-cell identities retain BOTH reciprocal masses and
all primitive-character terms; source and target arrays remain coupled. -/
theorem parity_full_probe_canonical_free_Knu434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (Q : ℕ) (hA hB xi : ℝ)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (ss st : SG → Fin ell → ℕ)
    (bs bt : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceOriginalProbeCanonicalKnu434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      Q hA hB xi (Sum.elim Ps Pb) (Sum.elim Vs Vb) (parityFullProbeAuxLift434 SG m nu aux)
      (parityFullProbeFreeLift434 J ell m hmJ nu ss bs)
      (parityFullProbeFreeLift434 J ell m hmJ nu st bt) =
    sourceOriginalProbeCanonicalKnu434 J ell m hmJ nu Q hA hB xi Pb Vb aux bs bt := by
  have hmassA :
      sourceOriginalProbeCellA434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
        (parityFullProbePattern434 SG m nu) hA =
      sourceOriginalProbeCellA434 m Pb Vb nu hA := by
    funext j
    exact parity_full_probe_cell_A434 m nu Ps Pb Vs Vb hA j
  have hmassB :
      sourceOriginalProbeCellB434 m (Sum.elim Ps Pb) (Sum.elim Vs Vb)
        (parityFullProbePattern434 SG m nu) hB =
      sourceOriginalProbeCellB434 m Pb Vb nu hB := by
    funext j
    exact parity_full_probe_cell_B434 m nu Ps Pb Vs Vb hB j
  unfold sourceOriginalProbeCanonicalKnu434 sourceOriginalProbeConcreteKnu434
    sourceAuxiliaryOriginalComparisonKnu434
  rw [parity_full_probe_active_A434,parity_full_probe_active_B434,hmassA,hmassB,
    parity_full_probe_DA434,parity_full_probe_DB434,
    parity_full_probe_free_target_X434,parity_full_probe_free_source_X434]
  simp only [parityFullProbePattern434,Finset.card_map]

/-- Literal B574 canonical FREE kernel equality under the full-group lift.
This includes the original free-mark ban and all original complex factors. -/
theorem parity_full_probe_canonical_free_kernel434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (Q : ℕ) (hA hB xi : ℝ)
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (ss st : SG → Fin ell → ℕ)
    (bs bt : ∀ g : BG,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    sourceB574CanonicalFreeKernel434 J ell m hmJ (parityFullProbePattern434 SG m nu)
      Q hA hB xi (Sum.elim Ps Pb) (Sum.elim Vs Vb) (parityFullProbeAuxLift434 SG m nu aux)
      (parityFullProbeFreeLift434 J ell m hmJ nu ss bs)
      (parityFullProbeFreeLift434 J ell m hmJ nu st bt) =
    sourceB574CanonicalFreeKernel434 J ell m hmJ nu Q hA hB xi Pb Vb aux bs bt := by
  unfold sourceB574CanonicalFreeKernel434
  rw [parity_full_probe_free_aux_ban434,parity_full_probe_canonical_free_Knu434]

/-- Actual restriction of a full endpoint to its chosen original free
slots. This definition is independent of all auxiliary variables. -/
def parityProbeFreeExtract434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (a : G → Fin (J+ell) → ℕ) :
    ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ :=
  fun g i => a g (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ nu g i).val

def paritySmallFreeExtract434 {G : Type} (J ell : ℕ) (a : G → Fin (J+ell) → ℕ) :
    G → Fin ell → ℕ :=
  fun g i => a g (sourceOriginalFreeSlotEquiv434 J ell ∅ i).val

/-- Restriction of the ORIGINAL full lifted endpoint equals lift of its
actual SMALL and BIG restrictions, using the same original enumerations. -/
theorem parity_full_probe_free_extract_lift434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (s : SG → Fin (J+ell) → ℕ) (b : BG → Fin (J+ell) → ℕ) :
    parityProbeFreeExtract434 J ell m hmJ (parityFullProbePattern434 SG m nu) (Sum.elim s b) =
    parityFullProbeFreeLift434 J ell m hmJ nu
      (paritySmallFreeExtract434 J ell s) (parityProbeFreeExtract434 J ell m hmJ nu b) := by
  funext g i
  cases g with
  | inl g =>
    exact congrArg (s g) (parity_full_probe_small_free_coordinate434 J ell m hmJ nu g i)
  | inr g =>
    exact congrArg (b g) (parity_full_probe_big_free_coordinate434 J ell m hmJ nu g i)

/-- Extracting the original free slots after actual shared/free assembly
returns the exact input array, without a clean or prime hypothesis. -/
theorem parity_probe_free_extract_assemble434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (shared : ∀ g,sourceOriginalProbeSharedSlots434 J ell m hmJ nu g → ℕ)
    (free : ∀ g,Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → ℕ) :
    parityProbeFreeExtract434 J ell m hmJ nu
      (sourceOriginalProbeAssembledFull434 J ell m hmJ nu shared free)=free := by
  funext g i
  exact congrFun (source_shared_extract_assemble434
    (sourceOriginalProbeSharedSlots434 J ell m hmJ nu g) (shared g)
    (sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ nu g) (free g)) i

/-- Retaining the full endpoint's shared labels and its exact extracted
free array reconstructs that SAME endpoint, with no numerical assumptions. -/
theorem parity_probe_assemble_free_extract434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (a : G → Fin (J+ell) → ℕ) :
    sourceOriginalProbeAssembledFull434 J ell m hmJ nu
      (fun g i => a g i.val) (parityProbeFreeExtract434 J ell m hmJ nu a)=a := by
  funext g i
  unfold sourceOriginalProbeAssembledFull434 sourceSharedAssemble434
  split_ifs with hi
  · rfl
  · change a g ((sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ nu g)
      ((sourceOriginalProbeFreeMarkEquiv434 J ell m hmJ nu g).symm ⟨i,hi⟩)).val = a g i
    rw [Equiv.apply_symm_apply]

/-- The existing B26 original shared/free equivalence extracts exactly the
same free array. This exposes its correspondence to the B574 slot formulas. -/
theorem parity_original_split_free_extract434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (a : G → Fin (J+ell) → ℕ) :
    (sourceOriginalB26ActiveSplitEquiv434 (fun _ : G => ℕ) J ell m hmJ nu a).2 =
      parityProbeFreeExtract434 J ell m hmJ nu a := rfl

/-- Exact original endpoint splitting commutes with the SMALL+BIG lift. -/
theorem parity_original_split_free_lift434
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
    (s : SG → Fin (J+ell) → ℕ) (b : BG → Fin (J+ell) → ℕ) :
    (sourceOriginalB26ActiveSplitEquiv434 (fun _ : SG ⊕ BG => ℕ) J ell m hmJ
      (parityFullProbePattern434 SG m nu) (Sum.elim s b)).2 =
    parityFullProbeFreeLift434 J ell m hmJ nu (paritySmallFreeExtract434 J ell s)
      (sourceOriginalB26ActiveSplitEquiv434 (fun _ : BG => ℕ) J ell m hmJ nu b).2 := by
  rw [parity_original_split_free_extract434,parity_original_split_free_extract434]
  exact parity_full_probe_free_extract_lift434 J ell m hmJ nu s b
end Green64Analytic.CorrelationSquare

namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Actual Parity r20, ell=1 specialization of the ORIGINAL stripped kernel
lift, with genuine SMALL/BIG prime families and their unchanged masses. -/
theorem parity_actual_stripped_kernel_lift434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (ss st : SourceNativeMemorySG434 20 L hS → Fin 1 → ℕ)
    (bs bt : ∀ g : sourceNativeOriginalBigType434 20 L,
      Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu g) → ℕ) :
    sourceB574CanonicalFreeKernel434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
      Q hA hB xi (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu aux)
      (parityFullProbeFreeLift434 J 1 m hmJ nu ss bs)
      (parityFullProbeFreeLift434 J 1 m hmJ nu st bt) =
    sourceB574CanonicalFreeKernel434 J 1 m hmJ nu Q hA hB xi
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L) aux bs bt :=
  parity_full_probe_canonical_free_kernel434 J 1 m hmJ nu Q hA hB xi
    (SourceNativeMemorySmallSet434 20 L hS) (sourceNativeOriginalTb434 20 L)
    (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    aux ss st bs bt

/-- The real r20 physical endpoint restriction uses exactly the lifted
one-free-SMALL/variable-free-BIG arrays appearing in the stripped kernel. -/
theorem parity_actual_full_endpoint_free_extract434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (s : SourceNativeMemorySG434 20 L hS → Fin (J+1) → ℕ)
    (b : sourceNativeOriginalBigType434 20 L → Fin (J+1) → ℕ) :
    parityProbeFreeExtract434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) (Sum.elim s b) =
    parityFullProbeFreeLift434 J 1 m hmJ nu
      (paritySmallFreeExtract434 J 1 s) (parityProbeFreeExtract434 J 1 m hmJ nu b) :=
  parity_full_probe_free_extract_lift434 J 1 m hmJ nu s b
end Green64Analytic.SourceBlockSieve

end

end

/-! ## PhysicalSharedFreeSlices -/

section

open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 24000
set_option linter.unusedSectionVars false

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64SmallHaar Green64FullPhysicalE

/-- Native zero residues on the true prime-label subtype count exactly
 the original distinct divisors. No valuation count is substituted. -/
theorem parity_native_subtype_omega_count434 (P : Finset ℕ) (n : ℕ) :
    omega (fun p : {p : ℕ // p ∈ P} => p.val)
      (fun p => ((n : ℤ) : ZMod p.val)) = smallPrimeCount P n := by
  classical
  unfold omega zeroCoordSet smallPrimeCount smallPrimeSupport
  apply Finset.card_bij (fun p _ => p.val)
  · intro p hp
    refine Finset.mem_filter.mpr ⟨p.property,?_⟩
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) p.val).mp
      (Finset.mem_filter.mp hp).2
  · intro a _ b _ h
    exact Subtype.ext h
  · intro p hp
    obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
    refine ⟨⟨p,hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) p).mpr
    exact_mod_cast hd

/-- At an actual full physical state, the native product of half dampings
 is the original real half-power. Ordered marks supply every count lower
 bound internally, so the native Nat.sub causes no truncation. -/
theorem parity_native_group_physical_half434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (M : ℕ) (q : ℝ) (n : ℕ) (hq : 0<q)
    (x : GroupState (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) M)
    (hx : ∀ g p,residues (fun p : {p : ℕ // p ∈ P g} => p.val) M (x g) p =
      ((n : ℤ) : ZMod p.val)) :
    (∏ g,endpointDamping (fun p : {p : ℕ // p ∈ P g} => p.val) M q (x g)) =
      sourcePhysicalGroupedHalf434 P M q n := by
  classical
  calc
    _ = ∏ g,q ^ (((smallPrimeCount (P g) n : ℝ)-(M : ℝ))/2) := by
      apply Finset.prod_congr rfl
      intro g _
      rw [endpointDamping_eq_source_rpow _ _ q hq.le,
        Nat.cast_sub (omega_ge_M _ _ (x g)),funext (hx g),
        parity_native_subtype_omega_count434]
    _ = q ^ (∑ g,((smallPrimeCount (P g) n : ℝ)-(M : ℝ))/2) := by
      rw [← Real.rpow_sum_of_pos hq]
    _ = _ := by
      unfold sourcePhysicalGroupedHalf434
      congr 1
      rw [← Finset.sum_div,Finset.sum_sub_distrib]
      push_cast
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

theorem parity_original_grouped_half_sum434
    {SG BG : Type} [Fintype SG] [Fintype BG]
    (Ps : SG → Finset ℕ) (Pb : BG → Finset ℕ)
    (M : ℕ) (q : ℝ) (n : ℕ) (hq : 0<q) :
    sourcePhysicalGroupedHalf434 Ps M q n * sourcePhysicalGroupedHalf434 Pb M q n =
      sourcePhysicalGroupedHalf434 (Sum.elim Ps Pb) M q n := by
  unfold sourcePhysicalGroupedHalf434
  rw [← Real.rpow_add hq]
  congr 1
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.card_sum]
  push_cast
  ring

/-- Literal independent full-list sum with fixed shared assignment equals
 the two physical completion fibres. This holds for every shared array,
 including repetitions and endpoint collisions. -/
theorem parity_full_marks_fixed_shared_pair434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (M : ℕ) (E : G → Finset (Fin M))
    (s : (i : G) × E i → ℕ) (n np : ℕ)
    (F : (G → Fin M → ℕ) → (G → Fin M → ℕ) → ℂ) :
    (∑ a ∈ bigMarkLists P (fun _ => M) n,
      ∑ b ∈ bigMarkLists P (fun _ => M) np,
        if parityPhysicalSharedRestriction434 M E a=s ∧
          parityPhysicalSharedRestriction434 M E b=s then F a b else 0) =
    ∑ a ∈ parityPhysicalCompletionsAt434 P M E s n,
      ∑ b ∈ parityPhysicalCompletionsAt434 P M E s np,F a b := by
  simp only [parity_physical_completions_restriction_fibre434]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : parityPhysicalSharedRestriction434 M E a=s
  · simp only [ha,true_and,ite_true,Finset.sum_filter]
  · simp only [ha,false_and,ite_false,Finset.sum_const_zero]


/-- The exact native typed comparison Knu with its original auxiliary ban
 equals B574's full physical kernel on a shared physical pair. The hypothesis
 is only the literal shared guard; no injectivity, avoidance or clean event is
 added. The structural A/B disjointness supplies the original aux-slot bijection. -/
theorem parity_memory_canonical_full_kernel434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (hDisj : Disjoint nu.1 nu.2) (Q : ℕ) (hA hB xi : ℝ)
    (aux : Green64FullPhysicalE.SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (hshared : ∀ g (i : sourceOriginalProbeSharedSlots434 J ell m hmJ nu g),
      (s g i).val=(t g i).val) :
    (if sourceOriginalB26FrozenAuxBan434 _ J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux s t then
      sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux s t else 0) =
    sourceB574CanonicalFullKernel434 J ell m hmJ nu Q hA hB xi P V
      (sourceOriginalProbeMemoryAuxValues434 P J m hmJ nu aux)
      (fun g i => (s g i).val) (fun g i => (t g i).val) := by
  classical
  have haux : (sourceOriginalProbeMemoryFlatEquiv434 P J m hmJ nu hDisj aux).val =
      sourceOriginalProbeMemoryAuxValues434 P J m hmJ nu aux := by
    funext z
    exact source_original_probe_memory_flat_values434 P J m hmJ nu hDisj aux z
  have hban := source_original_probe_memory_flat_ban434 P J ell m hmJ nu hDisj aux s t
  rw [haux] at hban
  unfold sourceB574CanonicalFullKernel434
  rw [← hban]
  split_ifs
  · unfold sourceOriginalProbeMemoryCanonicalK434
    have hs : sourceOriginalProbeAssembledFull434 J ell m hmJ nu
        (fun g i => (s g i).val) (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu s) =
        (fun g i => (s g i).val) :=
      parity_probe_assemble_free_extract434 J ell m hmJ nu (fun g i => (s g i).val)
    have ht : sourceOriginalProbeAssembledFull434 J ell m hmJ nu
        (fun g i => (s g i).val) (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu t) =
        (fun g i => (t g i).val) := by
      have he : (fun g (i : sourceOriginalProbeSharedSlots434 J ell m hmJ nu g) => (s g i).val) =
          (fun g (i : sourceOriginalProbeSharedSlots434 J ell m hmJ nu g) => (t g i).val) := by
        funext g i
        exact hshared g i
      rw [he]
      exact parity_probe_assemble_free_extract434 J ell m hmJ nu (fun g i => (t g i).val)
    have h := source_original_probe_canonical_full_physical_identity434
      J ell m hmJ nu Q hA hB xi P V
      (sourceOriginalProbeMemoryAuxValues434 P J m hmJ nu aux)
      (fun g i => (s g i).val)
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu s)
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ nu t)
    rw [hs,ht] at h
    exact h
  · rfl



end Green64Analytic.CorrelationSquare

namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD

/-- The complete original physical residue fibre at one natural integer. -/
abbrev ParityActualPositionFibre434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J n : ℕ) :=
  {x : MemoryIndependentState
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 //
    b650IntegerResidueAt434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 (n : ℤ) x}

/-- Literal numerical readout of all original endpoint marks. -/
def parityActualPositionMarks434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J n : ℕ)
    (x : ParityActualPositionFibre434 L hS J n) : B645ActualGroup434 L hS → Fin (J+1) → ℕ :=
  Sum.elim
    (fun g i => (Green64SmallHaar.marks (fun p : SourceNativeMemorySP434 20 L hS g => p.val)
      (J+1) (x.val.1 g) i).val)
    (fun g i => (Green64SmallHaar.marks (fun p : SourceNativeMemoryBP434 20 L g => p.val)
      (J+1) (x.val.2 g) i).val)

/-- Native endpoint half damping of the complete actual state. -/
def parityActualPositionHalf434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J n : ℕ) (q : ℝ)
    (x : ParityActualPositionFibre434 L hS J n) : ℝ :=
  (∏ g,Green64SmallHaar.endpointDamping
    (fun p : SourceNativeMemorySP434 20 L hS g => p.val) (J+1) q (x.val.1 g)) *
  (∏ g,Green64SmallHaar.endpointDamping
    (fun p : SourceNativeMemoryBP434 20 L g => p.val) (J+1) q (x.val.2 g))

/-- Both native group families give exactly the original FULL-P grouped
 half-power at the same physical integer. -/
theorem parity_actual_position_half_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n : ℕ) (q : ℝ) (hq : 0<q) (x : ParityActualPositionFibre434 L hS J n) :
    parityActualPositionHalf434 L hS J n q x =
      sourcePhysicalGroupedHalf434 (b645ActualBand434 L hS) (J+1) q n := by
  have hs := parity_native_group_physical_half434
    (SourceNativeMemorySmallSet434 20 L hS) (J+1) q n hq x.val.1 x.property.1
  have hb := parity_native_group_physical_half434
    (sourceNativeOriginalTb434 20 L) (J+1) q n hq x.val.2 x.property.2
  unfold parityActualPositionHalf434
  rw [hs,hb,parity_original_grouped_half_sum434 _ _ _ _ _ hq]
  rfl

/-- Arbitrary coupled tests are transported from the two ACTUAL physical
 residue fibres to the independently defined original full-list supports. -/
theorem parity_actual_position_pair_reindex434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n np : ℕ)
    (F : (B645ActualGroup434 L hS → Fin (J+1) → ℕ) →
      (B645ActualGroup434 L hS → Fin (J+1) → ℕ) → ℂ) :
    (∑ x : ParityActualPositionFibre434 L hS J n,
      ∑ y : ParityActualPositionFibre434 L hS J np,
        F (parityActualPositionMarks434 L hS J n x) (parityActualPositionMarks434 L hS J np y)) =
    ∑ a ∈ bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) n,
      ∑ b ∈ bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) np,F a b := by
  classical
  calc
    _ = ∑ a : (↑(bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) n)),
      ∑ b : (↑(bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) np)),F a.val b.val := by
      apply Fintype.sum_equiv (parityActualFixedPositionMarksEquiv434 L hS J n)
      intro x
      apply Fintype.sum_equiv (parityActualFixedPositionMarksEquiv434 L hS J np)
      intro y
      rfl
    _ = _ := by
      simp only [Finset.sum_coe_sort]
      exact Finset.sum_coe_sort
        (bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) n)
        (fun a => ∑ b ∈ bigMarkLists (b645ActualBand434 L hS) (fun _ => J+1) np,F a b)

/-- Exact actual fixed-shared slice carrier reindex, before any restoration
 or clean-event approximation and with an arbitrary coupled full kernel. -/
theorem parity_actual_position_shared_pair_reindex434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J n np : ℕ) (E : B645ActualGroup434 L hS → Finset (Fin (J+1)))
    (s : (g : B645ActualGroup434 L hS) × E g → ℕ)
    (F : (B645ActualGroup434 L hS → Fin (J+1) → ℕ) →
      (B645ActualGroup434 L hS → Fin (J+1) → ℕ) → ℂ) :
    (∑ x : ParityActualPositionFibre434 L hS J n,
      ∑ y : ParityActualPositionFibre434 L hS J np,
        if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J n x)=s ∧
          parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J np y)=s
        then F (parityActualPositionMarks434 L hS J n x) (parityActualPositionMarks434 L hS J np y) else 0) =
    ∑ a ∈ parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s n,
      ∑ b ∈ parityPhysicalCompletionsAt434 (b645ActualBand434 L hS) (J+1) E s np,F a b := by
  rw [parity_actual_position_pair_reindex434 L hS J n np (fun a b =>
    if parityPhysicalSharedRestriction434 (J+1) E a=s ∧ parityPhysicalSharedRestriction434 (J+1) E b=s
    then F a b else 0)]
  exact parity_full_marks_fixed_shared_pair434 _ _ _ _ _ _ _


abbrev ParityActualProbeAux434 (L : ℝ) (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m) :=
  SourceBigAux (SourceNativeMemoryBP434 20 L) J m
    (sourceOriginalProbeMemoryPattern434 J m hmJ nu)

/-- Literal native comparison component, with the ORIGINAL typed auxiliary
 endpoint mark ban and actual Memory canonical Knu on both complete BIG lists. -/
def parityActualPositionCanonicalKernel434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : ParityActualProbeAux434 L J m hmJ nu)
    {n np : ℕ} (x : ParityActualPositionFibre434 L hS J n) (y : ParityActualPositionFibre434 L hS J np) : ℂ :=
  if memoryIndependentAuxBan
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
      J 1 m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux x.val y.val then
    sourceOriginalProbeMemoryCanonicalK434
      (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
      J 1 m hmJ nu Q hA hB xi aux
      (fun g => Green64SmallHaar.marks (fun p : SourceNativeMemoryBP434 20 L g => p.val) (J+1) (x.val.2 g))
      (fun g => Green64SmallHaar.marks (fun p : SourceNativeMemoryBP434 20 L g => p.val) (J+1) (y.val.2 g))
  else 0

/-- Exact native Knu/full-P B574 kernel bridge on the ORIGINAL shared guard.
 Both inverse active-cell masses, original primitive characters, all aux slots
 and the full endpoint ban are carried by the equality. -/
theorem parity_actual_position_canonical_kernel_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hDisj : Disjoint nu.1 nu.2) (Q : ℕ) (hA hB xi : ℝ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    {n np : ℕ} (x : ParityActualPositionFibre434 L hS J n) (y : ParityActualPositionFibre434 L hS J np)
    (hshared : parityPhysicalSharedRestriction434 (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
        (parityActualPositionMarks434 L hS J n x) =
      parityPhysicalSharedRestriction434 (J+1)
        (sourceOriginalProbeSharedSlots434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
        (parityActualPositionMarks434 L hS J np y)) :
    parityActualPositionCanonicalKernel434 L hS J m hmJ nu Q hA hB xi aux x y =
    sourceB574CanonicalFullKernel434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
      Q hA hB xi (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
      (parityActualPositionMarks434 L hS J n x) (parityActualPositionMarks434 L hS J np y) := by
  have hb : ∀ g (i : sourceOriginalProbeSharedSlots434 J 1 m hmJ nu g),
      (Green64SmallHaar.marks (fun p : SourceNativeMemoryBP434 20 L g => p.val) (J+1) (x.val.2 g) i).val =
      (Green64SmallHaar.marks (fun p : SourceNativeMemoryBP434 20 L g => p.val) (J+1) (y.val.2 g) i).val := by
    intro g i
    let ii : sourceOriginalProbeSharedSlots434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) (Sum.inr g) :=
      ⟨i.val,by rw [parity_full_probe_shared_big434]; exact i.property⟩
    exact congrFun hshared ⟨Sum.inr g,ii⟩
  unfold parityActualPositionMarks434
  rw [parity_actual_full_probe_canonical_physical_kernel434]
  exact parity_memory_canonical_full_kernel434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    J 1 m hmJ nu hDisj Q hA hB xi aux _ _ hb

/-- The original BIG row's unshared count is exactly its actual pattern
 free-mark count, with no old constant r0 or fixed slot count substituted. -/
theorem parity_probe_memory_unshared_count434
    {G : Type} [DecidableEq G] (J ell m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 G m) (g : G) :
    Green64SmallHaar.unsharedSlots (J+ell)
      (sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) g) =
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g := by
  have h := source_original_probe_shared_free_card434 J ell m hmJ nu g
  rw [source_original_probe_memory_shared_slots434]
  change (J+ell)-(sourceOriginalProbeSharedSlots434 J ell m hmJ nu g).card = _
  omega

/-- Both literal native row unshared masses. These are separate from mu0,
 all auxiliary probabilities and the two endpoint damping squares. -/
def parityActualUnsharedMass434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m) : ℝ :=
  (∏ g : SourceNativeMemorySG434 20 L hS,
    1/(SourceNativeMemorySmallMass434 20 L hS g)^Green64SmallHaar.unsharedSlots (J+1)
      (sourceSmallShared J 1 g)) *
  (∏ g : sourceNativeOriginalBigType434 20 L,
    1/(sourceNativeOriginalVbig434 20 L g)^Green64SmallHaar.unsharedSlots (J+1)
      (sourceBigShared J 1 m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) g))

/-- The same single mu0 and native unshared masses give exactly B574's
 two full-P prefactors; there is no physical-fibre normalization factor. -/
theorem parity_actual_slice_mass_prefactors434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m) :
    ((b657ActualStateMass434 L hS J * parityActualUnsharedMass434 L hS J m hmJ nu : ℝ) : ℂ) =
    (∏ g : B645ActualGroup434 L hS,
      (((Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) g : ℝ) : ℂ)^(J+1))⁻¹) *
    (∏ g : B645ActualGroup434 L hS,
      (((Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) g : ℝ) : ℂ)^
        sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g)⁻¹) := by
  unfold b657ActualStateMass434 b650IntegerStateMass434 parityActualUnsharedMass434
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,
    parity_full_probe_free_count_small434,parity_full_probe_free_count_big434,
    parity_probe_memory_unshared_count434]
  simp only [Green64SmallHaar.unsharedSlots,source_original_B26_small_shared_card434,
    Nat.add_sub_cancel_left]
  push_cast
  simp only [one_div,pow_one]



/-- Independently defined ACTUAL full physical slice at a labelled shared
 draw. It sums the complete native residue states at DR*w and DR*wp, their
 original typed auxiliary ban and Memory canonical Knu, both NATIVE damping
 squares, the single mu0, the native unshared masses, the actual auxiliary law
 and exactly one inverse of the true labelled shared product. It does not
 reference B574's completion sums or stripped slice. -/
def parityActualCanonicalPhysicalSlice434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : ParityActualProbeAux434 L J m hmJ nu)
    (q : ℝ) (w wp : ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ) : ℂ :=
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  let d := sourceB574SharedDilation434 (J+1) E s
  let S := fun i : (g : B645ActualGroup434 L hS) × E g => s i.1 i.2
  (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
    (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
  ((b657ActualStateMass434 L hS J * parityActualUnsharedMass434 L hS J m hmJ nu : ℝ) : ℂ) *
  (d : ℂ)⁻¹ *
  (∑ x : ParityActualPositionFibre434 L hS J (d*w),
    ∑ y : ParityActualPositionFibre434 L hS J (d*wp),
      if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*w) x)=S ∧
        parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*wp) y)=S then
        (((parityActualPositionHalf434 L hS J (d*w) q x)^2 : ℝ) : ℂ) *
        (((parityActualPositionHalf434 L hS J (d*wp) q y)^2 : ℝ) : ℂ) *
        parityActualPositionCanonicalKernel434 L hS J m hmJ nu Q hA hB xi aux x y
      else 0)

/-- Exact actual r20 physical-to-B574 slice join. Every labelled shared
 draw is allowed in the statement; repeated shared values and collisions
 vanish or remain according to the original physical carrier. Both native
 half-damping squares, mu0, all free masses, the complete auxiliary law,
 original Knu and ban, and one DR inverse are preserved. -/
theorem parity_actual_canonical_physical_slice_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hDisj : Disjoint nu.1 nu.2) (Q : ℕ) (hA hB xi : ℝ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (q : ℝ) (hq : 0<q) (w wp : ℕ)
    (s : ∀ g,sourceOriginalProbeSharedSlots434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g → ℕ) :
    parityActualCanonicalPhysicalSlice434 L hS J m hmJ nu Q hA hB xi aux q w wp s =
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    sourceB574CanonicalPhysicalSlice434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
      Q hA hB xi (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
      q w wp s := by
  classical
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  let E := sourceOriginalProbeSharedSlots434 J 1 m hmJ fullnu
  let d := sourceB574SharedDilation434 (J+1) E s
  let S := fun i : (g : B645ActualGroup434 L hS) × E g => s i.1 i.2
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let a := parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
    (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)
  let H := fun n : ℕ => (((sourcePhysicalGroupedHalf434 P (J+1) q n)^2 : ℝ) : ℂ)
  let K := sourceB574CanonicalFullKernel434 J 1 m hmJ fullnu Q hA hB xi P V a
  have hc (v : ℕ) : parityPhysicalCompletionsAt434 P (J+1) E S (d*v) =
      sourceB574LabelledCompletions434 P (J+1) E s v := rfl
  have hsum :
      (∑ x : ParityActualPositionFibre434 L hS J (d*w),
        ∑ y : ParityActualPositionFibre434 L hS J (d*wp),
          if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*w) x)=S ∧
            parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*wp) y)=S then
            (((parityActualPositionHalf434 L hS J (d*w) q x)^2 : ℝ) : ℂ) *
            (((parityActualPositionHalf434 L hS J (d*wp) q y)^2 : ℝ) : ℂ) *
            parityActualPositionCanonicalKernel434 L hS J m hmJ nu Q hA hB xi aux x y else 0) =
      H (d*w)*H (d*wp)*
        (∑ u ∈ sourceB574LabelledCompletions434 P (J+1) E s w,
          ∑ v ∈ sourceB574LabelledCompletions434 P (J+1) E s wp,K u v) := by
    calc
      _ = ∑ x : ParityActualPositionFibre434 L hS J (d*w),
        ∑ y : ParityActualPositionFibre434 L hS J (d*wp),
          if parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*w) x)=S ∧
            parityPhysicalSharedRestriction434 (J+1) E (parityActualPositionMarks434 L hS J (d*wp) y)=S then
            H (d*w)*H (d*wp)*K (parityActualPositionMarks434 L hS J (d*w) x)
              (parityActualPositionMarks434 L hS J (d*wp) y) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        split_ifs with h
        · rw [parity_actual_position_half_exact434 L hS J (d*w) q hq x,
            parity_actual_position_half_exact434 L hS J (d*wp) q hq y,
            parity_actual_position_canonical_kernel_exact434 L hS J m hmJ nu hDisj Q hA hB xi aux x y
              (h.1.trans h.2.symm)]
        · rfl
      _ = ∑ u ∈ parityPhysicalCompletionsAt434 P (J+1) E S (d*w),
          ∑ v ∈ parityPhysicalCompletionsAt434 P (J+1) E S (d*wp),H (d*w)*H (d*wp)*K u v :=
        parity_actual_position_shared_pair_reindex434 L hS J (d*w) (d*wp) E S
          (fun u v => H (d*w)*H (d*wp)*K u v)
      _ = _ := by rw [hc w,hc wp]; simp only [Finset.mul_sum]
  unfold parityActualCanonicalPhysicalSlice434
  dsimp only
  change _ * ((b657ActualStateMass434 L hS J * parityActualUnsharedMass434 L hS J m hmJ nu : ℝ) : ℂ) *
    (d : ℂ)⁻¹ * _ = _
  rw [hsum,parity_actual_slice_mass_prefactors434]
  unfold sourceB574CanonicalPhysicalSlice434
  dsimp only [fullnu,E,d,S,P,V,a,H,K]
  ring



end Green64Analytic.SourceBlockSieve

end

end

