module

public import Green64.Library.Weights.Part111
public import Green64.Library.Correlation.Part072
public import Green64.Library.Weights.Part112
public import Green64.Library.Weights.Part019
public import Green64.Library.Correlation.Part045
public import Green64.Library.Weights.Part033
public import Green64.Library.Correlation.Part071
public import Green64.Library.Weights.Part109
public import Green64.Library.Weights.Part038
public import Green64.Library.Weights.MarkedSquareDominatesW1
public import Green64.Library.Analysis.Estimates.Part015
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Green64.Library.Correlation.Part070
public import Green64.Library.Weights.Part023

@[expose] public section

/-!
# Weights / Part113

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## RankArcEndpoint -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 26000

/-- Native complex powers and the original B629 phase agree at every
positive natural position. The value at zero is deliberately excluded. -/
theorem parity_imaginary_power_source_phase434 (n : ℕ) (hn : 0<n) (t : ℝ) :
    imaginaryPower n t=sourcePhase n t := by
  unfold imaginaryPower sourcePhase
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne' : (n : ℂ)≠0),
    ←Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- The native common parity is the literal signed endpoint for the
actual P set or the empty set, with no change to valuation multiplicity. -/
theorem parity_endpoint_sign_choice434 (P : Finset ℕ) (tw : Bool) (n : ℕ) :
    sourceEndpointSign434 P tw n=
      sourceEndpointSign434 (if tw then P else ∅) true n := by
  cases tw <;> simp [sourceEndpointSign434,literalSourceParity]

/-- Multiply the independently defined full actual endpoint by its
physical cutoff and identify the original signed B629 coefficient.
All full SMALL/BIG weights, the native core and the character remain. -/
theorem parity_actual_rank_cutoff_original434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q)
    (q : ℝ) (F : PrimeSlotCore) (t : ℝ) (tw sourceSide : Bool)
    (Y : ℝ) (psi : ℝ → ℂ) (n : ℕ) (hn : 0<n) :
    psi ((n : ℝ)/Y)*
        parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q F t tw sourceSide n=
      sourceSignedCoefficients434 (if tw then sourceNativeOriginalG434 20 L else ∅) true
        (sourceOriginalFullEndpointCoefficients434 F.q
          (sourceNativeOriginalS434 20 L hS) (sourceNativeOriginalTs434 20 L hS)
          (sourceNativeOriginalTb434 20 L) q (sourceNativeOriginalVs434 20 L hS)
          (sourceNativeOriginalVsmall434 20 L hS) (sourceNativeOriginalVbig434 20 L)
          (fun _=>1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu)
          (if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB r.2.1 r.2.2
           else paritySecondRankMark434 J 1 m hmJ nu hA r.1.1 r.1.2) 0
          ((Finset.Icc F.lo F.hi).filter Nat.Prime) F.alpha F.residual F.character
          F.sigma₀ F.sigma₁
          (fun u=>psi ((u : ℝ)/Y)*sourcePhase u t)) (n : ℤ) := by
  rw [parity_actual_rank_endpoint_original434 L hL hS J m hmJ nu hA hB r q F t tw sourceSide n]
  unfold sourceSignedCoefficients434 sourceOriginalFullEndpointCoefficients434
  simp only [Int.toNat_natCast,parity_imaginary_power_source_phase434 n hn,
    parity_endpoint_sign_choice434 (sourceNativeOriginalG434 20 L) tw n]
  ring

/-- The native core's prime and interval gates are exactly the original
Q band. Both closed endpoints, the native ceiling and floor are retained. -/
theorem parity_native_core_prime_slot434
    (r d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin r)
    (delta : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ) :
    let F:=sourceNativePrimeCore r d L band slot delta freq K alpha q chi s0 s1
    ((Finset.Icc F.lo F.hi).filter Nat.Prime)=sourceOriginalQActualBands r d L band := by
  rfl

/-- Exact actual r20 B633 endpoint binding after the original cutoff's
Mellin frequency has been inserted. The first side uses eta(u)/u, the
second eta(u); both use the same conjugated residual and character as
B629. The first phase is -(rho+xi3)-2*pi*s and the second is -rho. -/
theorem parity_actual_B633_rank_cutoff_original434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    {Q : ℕ} (hA hB : ℝ) (r : ParityPrimitiveRankIndex434 Q) (q : ℝ)
    (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
    (k : ℤ) (chi : DirichletCharacter ℂ (2*k.natAbs))
    (prime : Bool) (S gamma : ℝ) (lFine uFine a b : ℕ)
    (xi1 xi2 xi3 rho sigma s Y : ℝ) (eta : ℝ → ℂ)
    (tw sourceSide : Bool) (n : ℕ) (hn : 0<n) :
    let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
      (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      (2*k.natAbs) chi 0 0
    let core:=if sourceSide then
      b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma
      else b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma
    let v:=if sourceSide then -(rho+xi3)-2*Real.pi*s else -rho
    let psi : ℝ → ℂ:=if sourceSide then (fun u=>eta u/(u : ℂ)) else eta
    psi ((n : ℝ)/Y)*
        parityActualRankEndpoint434 L hS J m hmJ nu hA hB r q core v tw sourceSide n=
      sourceSignedCoefficients434 (if tw then sourceNativeOriginalG434 20 L else ∅) true
        (sourceOriginalFullEndpointCoefficients434 (2*k.natAbs)
          (sourceNativeOriginalS434 20 L hS) (sourceNativeOriginalTs434 20 L hS)
          (sourceNativeOriginalTb434 20 L) q (sourceNativeOriginalVs434 20 L hS)
          (sourceNativeOriginalVsmall434 20 L hS) (sourceNativeOriginalVbig434 20 L)
          (fun _=>1) (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ nu)
          (if sourceSide then parityFirstRankMark434 J 1 m hmJ nu hB r.2.1 r.2.2
           else paritySecondRankMark434 J 1 m hmJ nu hA r.1.1 r.1.2) 0
          (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band)
          F.alpha (fun u=>star (F.residual u)) (chi.ringHomComp (starRingEnd ℂ))
          (if sourceSide then -(xi2-rho) else xi1+rho) (-sigma)
          (fun u=>psi ((u : ℝ)/Y)*sourcePhase u v)) (n : ℤ) := by
  dsimp only
  let F:=sourceNativePrimeCore 20 (sourceOriginalLiteralDepth 20 L) L band slot delta freq
    (Finset.Icc a b) (b629ActualFineAlpha434 prime L S gamma lFine uFine)
    (2*k.natAbs) chi 0 0
  have hslot : ((Finset.Icc F.lo F.hi).filter Nat.Prime)=
      sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L band :=
    parity_native_core_prime_slot434 20 _ L band slot delta freq _ _ _ chi 0 0
  cases sourceSide
  · simpa only [Bool.false_eq_true,ite_false,b633ParitySecondCore434,hslot] using
      parity_actual_rank_cutoff_original434 L hL hS J m hmJ nu hA hB r q
        (b633ParitySecondCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi1 rho sigma)
        (-rho) tw false Y eta n hn
  · simpa only [ite_true,b633ParityEFirstCore434,hslot] using
      parity_actual_rank_cutoff_original434 L hL hS J m hmJ nu hA hB r q
        (b633ParityEFirstCore434 F.alpha F.residual (2*k.natAbs) chi F.lo F.hi xi2 rho sigma)
        (-(rho+xi3)-2*Real.pi*s) tw true Y (fun u=>eta u/(u : ℂ)) n hn

/-- Explicit frequency losses for the actual B633 cores and the first
Mellin-shifted endpoint. The fixed exponent choices precede L and the
entire operator tuple. No frequency bound on the transformed data is
assumed; it is derived from the original five bounds and |s|<=L^F. -/
theorem parity_B633_mellin_frequency_bounds434
    (L C F : ℝ) (s0 s1 vexp : ℕ)
    (hL : 2+2*Real.pi≤L)
    (hs0 : C+1≤(s0 : ℝ)) (hs1 : C≤(s1 : ℝ))
    (hvexp : max C F+1≤(vexp : ℝ))
    (rho xi1 xi2 xi3 sigma s : ℝ)
    (hrho : |rho|≤L^C) (hxi1 : |xi1|≤L^C) (hxi2 : |xi2|≤L^C)
    (hxi3 : |xi3|≤L^C) (hsigma : |sigma|≤L^C) (hs : |s|≤L^F) :
    |-(xi2-rho)|≤L^s0 ∧ |xi1+rho|≤L^s0 ∧ |-sigma|≤L^s1 ∧
    |-(rho+xi3)-2*Real.pi*s|≤L^vexp ∧ |-rho|≤L^vexp := by
  have hL2 : 2≤L := by linarith [Real.pi_pos]
  have hL1 : 1≤L := by linarith
  have hLp : 0<L := by linarith
  have hnat (a : ℝ) (e : ℕ) (ha : a≤(e : ℝ)) : L^a≤L^e := by
    calc
      L^a≤L^(e : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 ha
      _=L^e := Real.rpow_natCast L e
  have hsum (x y : ℝ) (hx : |x|≤L^C) (hy : |y|≤L^C) : |x+y|≤L^s0 := by
    calc
      |x+y|≤|x|+|y| := abs_add_le x y
      _≤2*L^C := by linarith
      _≤L*L^C := mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hLp.le C)
      _=L^(C+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring
      _≤L^s0 := hnat (C+1) s0 hs0
  have hxi2neg : |xi2+(-rho)|≤L^s0 := hsum xi2 (-rho) hxi2 (by simpa using hrho)
  have hM0 : 0≤L^(max C F) := Real.rpow_nonneg hLp.le _
  have hCM : L^C≤L^(max C F) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hFM : L^F≤L^(max C F) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  refine ⟨by simpa only [abs_neg,sub_eq_add_neg] using hxi2neg,
    hsum xi1 rho hxi1 hrho,?_,?_,?_⟩
  · simpa only [abs_neg] using hsigma.trans (hnat C s1 hs1)
  · calc
      |-(rho+xi3)-2*Real.pi*s|≤|-(rho+xi3)|+|2*Real.pi*s| := by
        simpa only [sub_eq_add_neg,abs_neg] using
          (abs_add_le (-(rho+xi3)) (-(2*Real.pi*s)))
      _=|rho+xi3|+(2*Real.pi)*|s| := by
        rw [abs_neg,abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
      _≤|rho|+|xi3|+(2*Real.pi)*|s| := by linarith [abs_add_le rho xi3]
      _≤(2+2*Real.pi)*L^(max C F) := by
        have h1:=hrho.trans hCM
        have h2:=hxi3.trans hCM
        have h3:=mul_le_mul_of_nonneg_left (hs.trans hFM) (by positivity : 0≤2*Real.pi)
        nlinarith
      _≤L*L^(max C F) := mul_le_mul_of_nonneg_right hL hM0
      _=L^(max C F+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring
      _≤L^vexp := hnat (max C F+1) vexp hvexp
  · have hcv : C≤(vexp : ℝ) := by linarith [le_max_left C F]
    simpa only [abs_neg] using hrho.trans (hnat C vexp hcv)
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
set_option maxHeartbeats 14000000
set_option maxRecDepth 26000

/-- Actual B633 rank endpoint arc energy, expressed directly through the
independent full endpoint. The finite support is the enlarged source cap;
the original global harmonic carrier is not silently identified with it.
The full typed auxiliary cell membership, original modulus and parity are
retained. The first physical cutoff is eta(u)/u and the second eta(u). -/
def ParityB633ActualRankCellArc434
    (cfg : SourceComparisonFixed434) (eta : ℝ → ℂ) (L : ℝ) (jQ mmax : ℕ)
    (CZ Ck S beta gamma targetSaving Karc Cfreq Ftail : ℝ) : Prop :=
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
  ∀ (chi : DirichletCharacter ℂ (2*k.natAbs)) (rho xi1 xi2 xi3 sigma s : ℝ),
    |rho|≤L^Cfreq → |xi1|≤L^Cfreq → |xi2|≤L^Cfreq → |xi3|≤L^Cfreq →
    |sigma|≤L^Cfreq → |s|≤L^Ftail →
  ∀ (prime : Bool) (lFine uFine a b : ℕ), Real.exp (beta*L)≤(lFine:ℝ) →
    2 ≤ lFine → uFine ≤ 2*lFine → (uFine:ℝ) ≤ Real.exp (2*L) →
  ∀ (Qcomp : ℕ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ),
    aux ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m nu
      (sourceNativeOriginalTb434 20 L)) →
    sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu aux) →
    sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu aux) →
  ∀ (ca cb : Σ q : Fin Qcomp, DirichletCharacter ℂ (q.val+1)) (tw sourceSide : Bool),
  let Hp:=Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
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
  let endpoint : ℤ → ℂ:=fun z=>psi ((z.toNat : ℝ)/Y)*
    parityActualRankEndpoint434 L hFamily J m hmJ nu hA hB rank cfg.q0 core v tw sourceSide z.toNat
  ∀ (den h : ℕ), 0<den → (den : ℝ)≤L^cfg.cm →
    (∫ theta in {theta : ℝ | |theta|≤L^cfg.Carc/Hp},
      ‖sourceCircleFourierPoly ((Finset.Icc 1 ⌈cfg.A*Y⌉₊).image (fun n : ℕ=>(n : ℤ)))
        endpoint (((h : ℝ)/(den : ℝ)+theta : ℝ) : AddCircle (1 : ℝ))‖^2) ≤
      Karc*Y*L^(-targetSaving)

/-- Genuine enlarged B629 saving for the actual B633 first and second
rank endpoints. Source frequency exponents are explicitly chosen from
the original bounds and the fixed Mellin truncation exponent before L.
The cutoff, data admissibility and arc estimate are all constructed;
none is an analytic premise. Final Type II precision is not asserted. -/
theorem parity_eventually_B633_actual_rank_marked_arc434
    (jQ mmax cm : ℕ) (CZ Carc Cchi Ck beta gamma targetSaving Cfreq Ftail : ℝ)
    (hCZ : 0≤CZ) (hCk : 0≤Ck) (hcm : Ck+1≤(cm : ℝ))
    (hCarc : (cm : ℝ)≤Carc) (hCchi : (cm : ℝ)≤Cchi) (hCchiPos : 0<Cchi)
    (hbeta : 0<beta) (hgamma : 0<gamma) :
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
    parity_eventually_constructed_actual_rank_marked_arc434
      jQ mmax cm s0 s1 vexp CZ Carc Cchi Ck beta gamma targetSaving
      hCZ hCk hcm hCarc hCchi hCchiPos hbeta hgamma
  refine ⟨A,hA,eta,hs,hSupp,hOne,hNorm,K,hK,hBudgets,Karc,hKarc,B,S,hSB,?_⟩
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
end Green64Analytic.Parity

end

end

/-! ## MainPrecision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The genuine fixed-m family exponent increases with the endpoint-free
multiplicity cap. This supplies a single pre-L precision for every
m<=mmax without adding an outer sum over m. -/
theorem parity_rank_family_exponent_mono434 (m mmax : ℕ) (hm : m ≤ mmax) :
    (m : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2 ≤
      (mmax : ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2 := by
  have hLog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ (3+(Real.log 2)⁻¹)*Real.log 2 := by positivity
  have hmR : (m : ℝ) ≤ (mmax : ℝ) := by exact_mod_cast hm
  nlinarith [mul_le_mul_of_nonneg_right hmR hC]

/-- Exact absorption of the genuine two circle contributions. The major
term pays the rank-count exponent with two cell-count powers; the minor
term pays the coefficient exponent with all four reciprocal-cell powers.
Two powers are reserved before L. The same fixed threshold absorbs the
unrestricted-frequency global constant with one extra power. -/
theorem parity_coupled_family_power_absorb434
    (L B Eglobal EF EFmax CQ Cxi cm majorSaving minorSaving Karc Kglobal : ℝ)
    (hL : 2 ≤ L) (hEF : EF ≤ EFmax)
    (hKarc : 0 ≤ Karc) (hKglobal : 0 ≤ Kglobal)
    (hK : 2*Karc+Kglobal ≤ L)
    (hMajor : 2*cm+EFmax+4*CQ+2*Cxi+B+2 ≤ majorSaving)
    (hMinor : Eglobal+EFmax+4*CQ+4*Cxi+B+2 ≤ minorSaving) :
    2*Karc*L^(2*cm-majorSaving+EF+4*CQ+2*Cxi)+
        Kglobal*L^(Eglobal-minorSaving+EF+4*CQ+4*Cxi) ≤ L^(-B) ∧
    Kglobal*L^(Eglobal+EF+4*CQ+2*Cxi) ≤
      L^(Eglobal+EFmax+4*CQ+2*Cxi+1) := by
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hpa : L^(2*cm-majorSaving+EF+4*CQ+2*Cxi) ≤ L^(-B-2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hpb : L^(Eglobal-minorSaving+EF+4*CQ+4*Cxi) ≤ L^(-B-2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hKsq : 2*Karc+Kglobal ≤ L^(2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith [sq_nonneg (L-1)]
  have hKg : Kglobal ≤ L := by linarith
  constructor
  · calc
      _ ≤ 2*Karc*L^(-B-2)+Kglobal*L^(-B-2) :=
        add_le_add (mul_le_mul_of_nonneg_left hpa (by positivity))
          (mul_le_mul_of_nonneg_left hpb hKglobal)
      _ = (2*Karc+Kglobal)*L^(-B-2) := by ring
      _ ≤ L^(2 : ℝ)*L^(-B-2) :=
        mul_le_mul_of_nonneg_right hKsq (Real.rpow_nonneg hLp.le _)
      _ = L^(-B) := by rw [← Real.rpow_add hLp]; congr 1; ring
  · calc
      _ ≤ Kglobal*L^(Eglobal+EFmax+4*CQ+2*Cxi) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hKglobal
      _ ≤ L*L^(Eglobal+EFmax+4*CQ+2*Cxi) :=
        mul_le_mul_of_nonneg_right hKg (Real.rpow_nonneg hLp.le _)
      _ = L^(1 : ℝ)*L^(Eglobal+EFmax+4*CQ+2*Cxi) := by rw [Real.rpow_one]
      _ = L^(Eglobal+EFmax+4*CQ+2*Cxi+1) := by
        rw [← Real.rpow_add hLp]
        congr 1
        ring
end Green64Analytic.Parity

end

end

/-! ## NativeSharedRestoration -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- The original native physical shared-fibre sum minus the corresponding
stripped canonical slice with the SAME actual auxiliary probability.
This error is defined directly from the two original constructions. -/
def parityNativeSharedRestorationError434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi : ℝ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (w wp : ℕ) : ℂ :=
  (∑ s ∈ Fintype.piFinset
      (fun i : sourceB574OriginalSharedIndex434 J 1 m hmJ
        (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) =>
        b645ActualBand434 L hS i.1),
      parityActualCanonicalPhysicalSlice434 L hS J m hmJ nu Q hA hB xi aux (1/2) w wp
        (fun g i => s ⟨g,i⟩)) -
  (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
    (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    sourceB574CanonicalStrippedSlice434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
      Q hA hB xi (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
      (1/2) w wp

/-- Proved physical-to-canonical error identity. Every unrestricted shared
assignment and every native residue fibre remains in the left-hand side. -/
theorem parity_native_shared_restoration_error_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hDisj : Disjoint nu.1 nu.2) (Q : ℕ) (hA hB xi : ℝ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (w wp : ℕ) :
    parityNativeSharedRestorationError434 L hS J m hmJ nu Q hA hB xi aux w wp =
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
      parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q hA hB xi
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) w wp := by
  unfold parityNativeSharedRestorationError434
  rw [parity_actual_unrestricted_shared_slice_exact434 L hS J m hmJ nu hDisj Q hA hB xi aux
    (1/2) (by norm_num) w wp]
  unfold parityActualCanonicalSharedRestorationError434
  ring

/-- The explicit original B574 collision envelope at the actual r20 data.
Both marked weights and both cell reciprocal losses are retained. -/
def parityActualSharedRestorationEnvelope434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (w wp : ℕ) : ℝ :=
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let a := parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu aux
  let I := sourceB574OriginalSharedIndex434 J 1 m hmJ fullnu
  let t := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu
  ((1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ))+1)*
    ((Q:ℝ)^4*(xi⁻¹)^2)*
    ‖actualBigMarkDecoration P t (1/2) V (fun _=>1) w‖*
    ‖actualBigMarkDecoration P t (1/2) V (fun _=>1) wp‖*
    (((Fintype.card I:ℝ)*
      ((w.log2:ℝ)+(wp.log2:ℝ)+((Finset.univ.image a).card:ℝ))+
      (Fintype.card I:ℝ)^2)/(Real.exp (L^(1/10:ℝ))*(Real.log (6/5:ℝ)/2)))

/-- Genuine native physical-to-stripped restoration with a proved
quantitative collision error at every actual two-block comparison pattern.
Disjointness, prime support, separation and mass floors are all discharged;
the error bound itself is never made an additional hypothesis. -/
theorem parity_eventually_native_shared_restoration434 :
    ∀ᶠ L : ℝ in atTop, 1<L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (J m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
        nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
        ∀ (Q : ℕ) (hA hB xi : ℝ)
          (aux : ParityActualProbeAux434 L J m hmJ nu) (w wp : ℕ),
          0<hA → 0<hB → 0<xi → 0<w → 0<wp →
          ‖parityNativeSharedRestorationError434 L hS J m hmJ nu Q hA hB xi aux w wp‖ ≤
            sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
              (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux *
            parityActualSharedRestorationEnvelope434 L hS J m hmJ nu Q xi
              (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) w wp := by
  filter_upwards [parity_eventually_actual_canonical_shared_restoration434,
    parity_eventually_actual_full_mass_floor434] with L hBnd hMass
  refine ⟨hBnd.1,hBnd.2.1,?_⟩
  intro hS J m hmJ nu hnu Q hA hB xi aux w wp hhA hhB hxi hw hwp
  have hV : ∀ g,0<sourceNativeOriginalVbig434 20 L g := by
    intro g
    exact lt_of_lt_of_le Green64Analytic.ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
      (hMass.2.2 hS (Sum.inr g)).1
  have hmu := source_original_memory_aux_mass_nonneg434
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
    (sourceNativeOriginalVbig434 20 L) hV (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux
  have he : ‖parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q hA hB xi
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) w wp‖ ≤
      parityActualSharedRestorationEnvelope434 L hS J m hmJ nu Q xi
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) w wp :=
    hBnd.2.2 hS J m hmJ nu Q hA hB xi _ w wp hhA hhB hxi hw hwp
  rw [parity_native_shared_restoration_error_exact434 L hS J m hmJ nu
    (parity_actual_comparison_pattern_disjoint434 L m nu hnu) Q hA hB xi aux w wp,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hmu]
  exact mul_le_mul_of_nonneg_left he hmu

end Green64Analytic.SourceBlockSieve

end

end

/-! ## RankCellGeometry -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 22000

/-- Both genuine half-open log cells locate their complete product at
Hp determined by ja,jb. No chosen auxiliary endpoint replaces Hp. -/
theorem parity_literal_cells_product_scale434
    (hA hB : ℝ) (ja jb : ℤ) (DA DB : ℕ) (hDA : 0 < DA) (hDB : 0 < DB)
    (hA1 : hA ≤ 1) (hB1 : hB ≤ 1)
    (hca : sourceOriginalLiteralLogCell434 hA ja DA)
    (hcb : sourceOriginalLiteralLogCell434 hB jb DB) :
    let Hp := Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
    Hp ≤ ((DA*DB : ℕ) : ℝ) ∧ ((DA*DB : ℕ) : ℝ) ≤ Hp*Real.exp 2 := by
  have hDAP : 0 < (DA : ℝ) := by exact_mod_cast hDA
  have hDBP : 0 < (DB : ℝ) := by exact_mod_cast hDB
  have hlo : (ja : ℝ)*hA+(jb : ℝ)*hB ≤ Real.log (DA : ℝ)+Real.log (DB : ℝ) :=
    add_le_add hca.1 hcb.1
  have hhi : Real.log (DA : ℝ)+Real.log (DB : ℝ) ≤ (ja : ℝ)*hA+(jb : ℝ)*hB+2 := by
    have ha := hca.2
    have hb := hcb.2
    nlinarith
  constructor
  · simpa only [Real.exp_add,Real.exp_log hDAP,Real.exp_log hDBP,Nat.cast_mul] using
      Real.exp_le_exp.mpr hlo
  · simpa only [Real.exp_add,Real.exp_log hDAP,Real.exp_log hDBP,Nat.cast_mul] using
      Real.exp_le_exp.mpr hhi

/-- Actual cutoff support and the exact SIGNED displacement put both
natural endpoints in one fixed cell-scale interval. The displacement
bound is quantitative and is derived eventually below. -/
theorem parity_cell_scale_signed_window434
    (Z Hp : ℝ) (c w wp : ℕ) (k : ℤ) (hZ : 0 < Z) (hHp : 0 < Hp)
    (hclo : Hp ≤ (c : ℝ)) (hchi : (c : ℝ) ≤ Hp*Real.exp 2)
    (hSmall : |2*(k : ℝ)/Z| ≤ (128*Real.exp 2)⁻¹)
    (hShift : (wp : ℤ) = (w : ℤ)+(2*k)*(c : ℤ))
    (psi : ℝ → ℂ)
    (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (hPsi : psi ((w : ℝ)/(Z*(c : ℝ))) ≠ 0) :
    (w : ℝ)/(Z*Hp) ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1) ∧
    (wp : ℝ)/(Z*Hp) ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1) := by
  have hcp : 0 < (c : ℝ) := hHp.trans_le hclo
  have hdlo : 1 ≤ (c : ℝ)/Hp := (le_div_iff₀ hHp).mpr (by simpa only [one_mul] using hclo)
  have hdhi : (c : ℝ)/Hp ≤ Real.exp 2 :=
    (div_le_iff₀ hHp).mpr (hchi.trans_eq (by ring))
  have hdp : 0 < (c : ℝ)/Hp := div_pos hcp hHp
  have hu := hSupport _ hPsi
  have hup : 0 ≤ (w : ℝ)/(Z*(c : ℝ)) := by linarith [hu.1]
  have hRat : (w : ℝ)/(Z*Hp) = ((w : ℝ)/(Z*(c : ℝ)))*((c : ℝ)/Hp) := by
    field_simp [hZ.ne',hHp.ne',hcp.ne']
  have hwlo : (1/64 : ℝ) ≤ (w : ℝ)/(Z*Hp) := by
    rw [hRat]
    exact hu.1.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hdlo hup)
  have hwhi : (w : ℝ)/(Z*Hp) ≤ 64*Real.exp 2 := by
    rw [hRat]
    exact mul_le_mul hu.2 hdhi hdp.le (by norm_num)
  have hDelta : |(2*(k : ℝ)/Z)*((c : ℝ)/Hp)| ≤ (1/128 : ℝ) := by
    rw [abs_mul,abs_of_nonneg hdp.le]
    calc
      _ ≤ (128*Real.exp 2)⁻¹*Real.exp 2 :=
        mul_le_mul hSmall hdhi hdp.le (by positivity)
      _ = _ := by field_simp [Real.exp_ne_zero (2 : ℝ)]
  have hShiftR : (wp : ℝ) = (w : ℝ)+2*(k : ℝ)*(c : ℝ) := by exact_mod_cast hShift
  have hDiff : (wp : ℝ)/(Z*Hp) =
      (w : ℝ)/(Z*Hp)+(2*(k : ℝ)/Z)*((c : ℝ)/Hp) := by
    rw [hShiftR]
    field_simp [hZ.ne',hHp.ne']
    <;> ring
  have hd := abs_le.mp hDelta
  refine ⟨⟨by linarith,by linarith⟩,⟨?_,?_⟩⟩ <;> rw [hDiff] <;> linarith

/-- Quantitative signed-shift smallness uniformly over the ORIGINAL Z
window and all |k|<=L^Ck. CZ,Ck are fixed before L. No auxiliary or
physical nonzero-completion hypothesis is required. -/
theorem parity_eventually_rank_cell_signed_shift434 (CZ Ck : ℝ)
    (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ ∀ (Z : ℝ) (k : ℤ),
      Real.exp L*L^(-CZ) ≤ Z → |(k : ℝ)| ≤ L^Ck →
      0 < Z ∧ |2*(k : ℝ)/Z| ≤ (128*Real.exp 2)⁻¹ := by
  have hPoly := eventually_native_source_poly_lt_exp_scaled434
    (CZ+Ck) 1 (1/2) (add_nonneg hCZ hCk) (by norm_num) (by norm_num)
  filter_upwards [hPoly,eventually_ge_atTop (2*Real.log (256*Real.exp 2))] with L hP hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hP.1
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  refine ⟨hL1,?_⟩
  intro Z k hZlo hk
  have hpCZ : 0 < L^(-CZ) := Real.rpow_pos_of_pos hLp _
  have hZ : 0 < Z := (mul_pos (Real.exp_pos L) hpCZ).trans_le hZlo
  refine ⟨hZ,?_⟩
  have hp : L^(CZ+Ck) ≤ Real.exp (L/2) := by
    simpa only [Real.rpow_one,one_div_mul_eq_div] using hP.2.le
  have hConst : 256*Real.exp 2 ≤ Real.exp (L/2) := by
    have hlog : Real.log (256*Real.exp 2) ≤ L/2 := by linarith
    simpa only [Real.exp_log (by positivity : (0 : ℝ) < 256*Real.exp 2)] using Real.exp_le_exp.mpr hlog
  have hPow : L^Ck = L^(CZ+Ck)*L^(-CZ) := by
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  have hExp : Real.exp L = Real.exp (L/2)*Real.exp (L/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hMain : (256*Real.exp 2)*L^Ck ≤ Z := by
    calc
      _ = (256*Real.exp 2)*L^(CZ+Ck)*L^(-CZ) := by rw [hPow]; ring
      _ ≤ Real.exp (L/2)*Real.exp (L/2)*L^(-CZ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hConst hp (by positivity) (Real.exp_pos _).le) hpCZ.le
      _ = Real.exp L*L^(-CZ) := by rw [← hExp]
      _ ≤ Z := hZlo
  have hkZ : (128*Real.exp 2)*(2*|(k : ℝ)|) ≤ Z := by nlinarith [mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 256*Real.exp 2)]
  rw [abs_div,abs_mul,abs_of_pos hZ]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ hZ).mpr
  apply (le_inv_mul_iff₀ (by positivity : (0 : ℝ) < 128*Real.exp 2)).mpr
  simpa only [mul_comm] using hkZ

/-- Specialization to every actual typed r20 auxiliary draw in its
literal A/B cells. c=DA*DB and positivity are proved, so the scale is
Hp from the two cell indices, never from a chosen endpoint. -/
theorem parity_actual_rank_cell_endpoints434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (hA hB : ℝ) (ja jb : ℤ) (hA1 : hA ≤ 1) (hB1 : hB ≤ 1)
    (hca : sourceOriginalLiteralLogCell434 hA ja (sourceOriginalProbeDA434 m nu
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)))
    (hcb : sourceOriginalLiteralLogCell434 hB jb (sourceOriginalProbeDB434 m nu
      (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)))
    (Z : ℝ) (k : ℤ) (w wp : ℕ) (hZ : 0 < Z)
    (hSmall : |2*(k : ℝ)/Z| ≤ (128*Real.exp 2)⁻¹)
    (hShift : (wp : ℤ) = (w : ℤ)+(2*k)*(parityActualProbeAuxD434 L J m hmJ nu aux : ℤ))
    (psi : ℝ → ℂ)
    (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64)
    (hPsi : psi ((w : ℝ)/(Z*(parityActualProbeAuxD434 L J m hmJ nu aux : ℝ))) ≠ 0) :
    let Hp := Real.exp ((ja : ℝ)*hA)*Real.exp ((jb : ℝ)*hB)
    (w : ℝ)/(Z*Hp) ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1) ∧
    (wp : ℝ)/(Z*Hp) ∈ Set.Icc (1/128 : ℝ) (64*Real.exp 2+1) := by
  let a := sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux
  have hSplit := parity_actual_probe_aux_product_split434 L J m hmJ nu hnu aux
  have hc := parity_actual_probe_aux_positive434 L hS J m hmJ nu aux
  rw [hSplit] at hc
  change 0 < sourceOriginalProbeDA434 m nu a * sourceOriginalProbeDB434 m nu a at hc
  have hPos : 0 < sourceOriginalProbeDA434 m nu a ∧ 0 < sourceOriginalProbeDB434 m nu a := by
    constructor
    · by_contra hn
      have hz : sourceOriginalProbeDA434 m nu a = 0 := by omega
      rw [hz,zero_mul] at hc
      omega
    · by_contra hn
      have hz : sourceOriginalProbeDB434 m nu a = 0 := by omega
      rw [hz,mul_zero] at hc
      omega
  have hScale := parity_literal_cells_product_scale434 hA hB ja jb
    (sourceOriginalProbeDA434 m nu a) (sourceOriginalProbeDB434 m nu a)
    hPos.1 hPos.2 hA1 hB1 hca hcb
  rw [← hSplit] at hScale
  exact parity_cell_scale_signed_window434 Z _ _ w wp k hZ (by positivity)
    hScale.1 hScale.2 hSmall hShift psi hSupport hPsi
end Green64Analytic.Parity

end

end

/-! ## RestorationMarkedBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

/-- Keep the original pattern-dependent count ell+|C_g|. Its upper bound
uses only that the selected designated slots form a subset of Fin m. -/
theorem parity_probe_free_mark_count_le434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m) (g : G) :
    sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g ≤ ell+m := by
  unfold sourceOriginalProbeFreeMarkCount434
  apply Nat.add_le_add_left _ ell
  unfold sourceOriginalProbeFreedSlots434
  calc
    _ ≤ ((Finset.univ : Finset (Fin m)).filter
        (fun j => (g,j)∈nu.1 ∨ (g,j)∈nu.2)).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp

/-- Every actual full SMALL+BIG group has at most m+1 free marks; the
SMALL count remains exactly one in the underlying full-pattern definition. -/
theorem parity_actual_full_free_mark_count_le434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (g : B645ActualGroup434 L hS) :
    sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g ≤ m+1 := by
  have h := parity_probe_free_mark_count_le434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g
  omega

/-- Uniform actual marked envelope for every original pattern with m≤J.
J and its exponent are fixed before L; all later groups, actual masses,
bounded ordered-list tests and physical integers remain uniform. -/
theorem parity_eventually_actual_marked_log_budget434 (J : ℕ) :
    ∃ Em : ℝ, 0≤Em ∧
    ∀ᶠ L : ℝ in atTop, 1<L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (b : (∀ g : B645ActualGroup434 L hS,
          Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
            (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g) → ℕ) → ℂ),
        (∀ lists, ‖b lists‖≤1) → ∀ n : ℕ,
        ‖actualBigMarkDecoration (b645ActualBand434 L hS)
          (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
            (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
          (1/2:ℝ)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          b n‖ ≤ L^Em := by
  have hv : 0 < Real.log (6/5:ℝ)/2 :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨Em,hEm,hUniform⟩ := source_marked_weight_log_power
    (1/2) (Real.log (6/5:ℝ)/2) 8 (J+1)
    (by norm_num) (by norm_num) hv (by norm_num)
  refine ⟨Em,hEm,?_⟩
  filter_upwards [parity_eventually_actual_full_mass_floor434,
    parity_eventually_actual_restoration_group_budget434] with L hMass hBudget
  refine ⟨hMass.1,hMass.2.1,?_⟩
  intro hS m hmJ nu b hb n
  exact hUniform L hMass.1.le
    (b645ActualBand434 L hS)
    (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    b (hBudget.2 hS).1
    (fun g => (parity_actual_full_free_mark_count_le434 L hS J m hmJ nu g).trans
      (Nat.add_le_add_right hmJ 1))
    (fun g => (hMass.2.2 hS g).1) hb n
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualMarkedW1Bridge -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 22000

/-- The literal all-group W1 is unchanged by the actual complete SMALL+BIG
index equivalence, including the distinguished SMALL group. -/
theorem parity_actual_full_W1_reindex434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (n : ℕ) :
    sourceOriginalW1 (b645ActualBand434 L hS) n =
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) n := by
  unfold sourceOriginalW1
  exact Fintype.prod_equiv (sourceNativeOriginalFullEquiv434 20 L hS hL) _ _
    (fun g => by rw [parity_actual_full_band_source434 L hL hS g])

/-- The physical full-group reciprocal masses are exactly the groupHarmonic
masses used by the original B575 higher-mark square domination. -/
theorem parity_actual_full_mass_groupHarmonic434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) :
    Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) =
      fun g => groupHarmonic (b645ActualBand434 L hS g) := by
  funext g
  simpa only [groupHarmonic,one_div] using parity_actual_full_mass_exact434 L hS g

/-- Genuine actual r20 higher-mark domination by the SAME original W1
which occurs in the P-part Rankin tail. The fixed J chooses one exponent
before L; all original patterns, ordered-list tests and endpoints follow.
All actual mass and group-count hypotheses of B575 are proved internally. -/
theorem parity_eventually_actual_marked_square_W1434 (J : ℕ) :
    ∃ E : ℝ,0≤E ∧
    ∀ᶠ L : ℝ in atTop, Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (b : (∀ g : B645ActualGroup434 L hS,
          Fin (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
            (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) g) → ℕ) → ℂ),
        (∀ lists,‖b lists‖≤1) → ∀ n : ℕ,
        ‖actualBigMarkDecoration (b645ActualBand434 L hS)
          (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
            (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
          (1/2:ℝ)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          b n‖^2 ≤ L^E * sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) n := by
  obtain ⟨C,hC,hBound⟩ := b575_actual_marked_square_le_literal_original_W1
    (Real.log (6/5:ℝ)/2) (J+1) source_actual_P_uniform_mass_floor_positive
  refine ⟨4*Real.log C,mul_nonneg (by norm_num) (Real.log_nonneg hC),?_⟩
  filter_upwards [parity_eventually_actual_full_mass_floor434,eventually_ge_atTop (Real.exp 2)]
    with L hMass hL
  refine ⟨hL,hMass.2.1,?_⟩
  intro hS m hmJ nu b hb n
  let P := b645ActualBand434 L hS
  let t := sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
    (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)
  have ht (g : B645ActualGroup434 L hS) : 1≤t g ∧ t g≤J+1 := by
    refine ⟨?_,(parity_actual_full_free_mark_count_le434 L hS J m hmJ nu g).trans
      (Nat.add_le_add_right hmJ 1)⟩
    dsimp [t,sourceOriginalProbeFreeMarkCount434]
    omega
  have hV (g : B645ActualGroup434 L hS) :
      Real.log (6/5:ℝ)/2≤groupHarmonic (P g) ∧ groupHarmonic (P g)≤4 := by
    have hh := hMass.2.2 hS g
    rw [parity_actual_full_mass_groupHarmonic434 L hS] at hh
    exact hh
  have hp := hBound P t b ht hV hb n
  rw [←parity_actual_full_mass_groupHarmonic434 L hS,
    parity_actual_full_W1_reindex434 L hMass.1 hS n] at hp
  have hCp : 0<C := lt_of_lt_of_le (by norm_num) hC
  have hLp : 0<L := (Real.exp_pos _).trans_le hL
  have hcard := parity_actual_full_group_card_four434 L hL hS
  have hpow : C^(Fintype.card (B645ActualGroup434 L hS)) ≤ L^(4*Real.log C) := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos hCp,Real.rpow_def_of_pos hLp]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hcard (Real.log_nonneg hC)
    nlinarith only [hh]
  exact hp.trans (mul_le_mul_of_nonneg_right hpow (source_original_W1_nonneg _ _))
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FreeAuxCollisionGeometry -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Literal lift of the actual typed auxiliary draws to the complete
SMALL+BIG source pattern. Every numerical repeat is retained. -/
def parityActualFreeCollisionAux434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    SourceOriginalProbeAuxIndex434 m
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)→ℕ :=
  parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
    (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)

/-- Every actual free auxiliary label is an original BIG prime at the
true exp(L^.3) floor, supported on the full r20 P family, and divides the
exact typed auxiliary product. No distinctness hypothesis is needed. -/
theorem parity_actual_free_collision_label434
    (L : ℝ) (hL : 1<L) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (z : SourceOriginalProbeAuxIndex434 m
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) :
    let p := parityActualFreeCollisionAux434 L hS J m hmJ nu aux z
    p.Prime ∧ Real.exp (L^(3/10:ℝ))≤(p:ℝ) ∧
      p.primeFactors⊆sourceNativeOriginalG434 20 L ∧ p∣parityActualProbeAuxD434 L J m hmJ nu aux := by
  let z0 := (parityFullProbeAuxEquiv434 (SourceNativeMemorySG434 20 L hS) m nu).symm z
  let i := sourceOriginalProbeMemoryAuxSlot434 J m hmJ nu z0
  let p := (aux i.1 i.2).val
  change p.Prime ∧ Real.exp (L^(3/10:ℝ))≤(p:ℝ) ∧
    p.primeFactors⊆sourceNativeOriginalG434 20 L ∧ p∣parityActualProbeAuxD434 L J m hmJ nu aux
  have hprime := source_native_original_Tb_prime_range434 20 L i.1 p (aux i.1 i.2).property
  have hmem : p∈sourceNativeOriginalG434 20 L := by
    rw [source_native_original_G_identity434 20 L hS hL]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i.1,Finset.mem_univ _,(aux i.1 i.2).property⟩)
  have hP : p.primeFactors⊆sourceNativeOriginalG434 20 L := by
    rw [hprime.1.primeFactors]
    exact Finset.singleton_subset_iff.mpr hmem
  have hin : p∣∏ j : (sourceOriginalProbeMemoryPattern434 J m hmJ nu).free i.1,(aux i.1 j).val :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i.2)
  have hout : (∏ j : (sourceOriginalProbeMemoryPattern434 J m hmJ nu).free i.1,(aux i.1 j).val)∣
      parityActualProbeAuxD434 L J m hmJ nu aux :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i.1)
  exact ⟨hprime.1,hprime.2.1,hP,hin.trans hout⟩

/-- The full auxiliary carrier is exactly the lifted BIG labels, with a
conservative finite cardinal bound before any analytic estimate. -/
theorem parity_full_probe_aux_card_le434
    (SG : Type) {BG : Type} [Fintype BG] [DecidableEq BG]
    (m : ℕ) (nu : SourceOriginalProbePattern434 BG m) :
    Fintype.card (SourceOriginalProbeAuxIndex434 m (parityFullProbePattern434 SG m nu))≤
      2*m*Fintype.card BG := by
  rw [←Fintype.card_congr (parityFullProbeAuxEquiv434 SG m nu)]
  have h1 : nu.1.card≤Fintype.card BG*m := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using Finset.card_le_univ nu.1
  have h2 : nu.2.card≤Fintype.card BG*m := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using Finset.card_le_univ nu.2
  simp only [SourceOriginalProbeAuxIndex434,Fintype.card_sum,Fintype.card_coe]
  nlinarith

/-- All collision charge slots cost only one explicit logarithmic
factor, uniformly in the actual r20 pattern with m<=J. -/
theorem parity_actual_free_collision_slots434
    (L : ℝ) (hL : Real.exp 1≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m) :
    (Fintype.card (SourceOriginalProbeAuxIndex434 m
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)):ℝ)≤
      (2*(J:ℝ)*(3+(Real.log 2)⁻¹))*L := by
  have hLp : 0<L := (Real.exp_pos 1).trans_le hL
  have hlog : Real.log L≤L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hm : (m:ℝ)≤J := by exact_mod_cast hmJ
  have hC : 0≤3+(Real.log 2)⁻¹ := by positivity
  have hG := (source_native_original_group_upper_counts434 20 L hS (by norm_num) hL).2
  have hCard := parity_full_probe_aux_card_le434 (SourceNativeMemorySG434 20 L hS) m nu
  calc
    _ ≤ 2*(m:ℝ)*(Fintype.card (sourceNativeOriginalBigType434 20 L):ℝ) := by exact_mod_cast hCard
    _ ≤ 2*(J:ℝ)*((3+(Real.log 2)⁻¹)*Real.log L) := by gcongr
    _ ≤ 2*(J:ℝ)*((3+(Real.log 2)⁻¹)*L) := by gcongr
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## FreeAuxCollisionHarmonic -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Genuine quantitative charge for EACH actual auxiliary label. The true
product D is split as p*d, both cores are exactly invariant, the cutoff
becomes psi(y/(Z*d)), the signed shift becomes 2*k*d, and the harmonic
reciprocal produces p inverse. Original BIG primes give exp(-L^.3).
No collision-smallness, endpoint bound, product-size or scale premise is
assumed; every such input is derived for the actual r20/B633 data. -/
theorem parity_eventually_actual_free_collision_prime_charge434
    (J : ℕ) (S beta gamma CZ Ck Cpsi : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J)
          (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (Kpsi : ℝ),0≤Kpsi → ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ (aux : ParityActualProbeAux434 L J m hmJ nu)
          (z : SourceOriginalProbeAuxIndex434 m
            (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu)) (M : ℕ),
          let c := parityActualProbeAuxD434 L J m hmJ nu aux
          let p := parityActualFreeCollisionAux434 L hS J m hmJ nu aux z
          (∑ w∈Finset.Ioc 0 M,
            if p∣w ∧ 0<(w:ℤ)+(2*k)*(c:ℤ) then
              ‖parityHarmonicStrippedArithmetic434 L (-xi3) Z E G (-(rho+xi3)) (-rho) tw psi
                c w (((w:ℤ)+(2*k)*(c:ℤ)).toNat)‖ else 0) ≤
            Real.exp (-(L^(3/10:ℝ)))*(64*66*(3:ℝ)^15)*Kpsi*L^(15+Cpsi) := by
  filter_upwards [parity_eventually_actual_B633_stripped_tau434 S beta gamma hSfine hbeta hgamma,
    parity_eventually_actual_typed_aux_sqrt434 J,parity_eventually_harmonic_scale_budget434 CZ Ck hCZ,
    parity_eventually_actual_full_mass_floor434,eventually_ge_atTop (Real.exp (2:ℝ))]
    with L hCore hAux hScale hMass hL2
  refine ⟨hL2,hMass.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ nu xi3 Z k hZlo hZhi hk Kpsi hKpsi tw psi hSupp hPsi aux z M
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let EF := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let GG := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let p := parityActualFreeCollisionAux434 L hS J m hmJ nu aux z
  have hpInfo := parity_actual_free_collision_label434 L hMass.1 hS J m hmJ nu aux z
  change p.Prime ∧ Real.exp (L^(3/10:ℝ))≤(p:ℝ) ∧
    p.primeFactors⊆sourceNativeOriginalG434 20 L ∧ p∣c at hpInfo
  have hc := hAux.2 hS m hmJ nu aux
  change 0<c ∧ (c:ℝ)≤Real.exp (Real.sqrt L) at hc
  obtain ⟨d,hd⟩ := hpInfo.2.2.2
  have hp : 0<p := hpInfo.1.pos
  have hdpos : 0<d := by
    have hh : 0<p*d := hd ▸ hc.1
    exact Nat.pos_of_mul_pos_left hh
  have hdle : d≤ c := by
    calc
      d = 1*d := by ring
      _ ≤ p*d := Nat.mul_le_mul_right d hp
      _ = c := hd.symm
  have hdcap : (d:ℝ)≤Real.exp (Real.sqrt L) :=
    (show (d:ℝ)≤(c:ℝ) by exact_mod_cast hdle).trans hc.2
  have hGeom := hScale.2 Z hZlo hZhi d hdpos hdcap k hk
  have hInv : (p:ℝ)⁻¹≤Real.exp (-(L^(3/10:ℝ))) := by
    simpa only [one_div,Real.exp_neg] using
      one_div_le_one_div_of_le (Real.exp_pos (L^(3/10:ℝ))) hpInfo.2.1
  let Dsum := ∑ y∈Finset.Ioc 0 (M/p),
    if 0<(y:ℤ)+(2*k)*(d:ℤ) then
      ‖parityHarmonicStrippedArithmetic434 L (-xi3) Z EF GG (-(rho+xi3)) (-rho) tw psi
        d y (((y:ℤ)+(2*k)*(d:ℤ)).toNat)‖ else 0
  have hSmall : Dsum≤parityHarmonicDivisorEnvelope434 (Z*(d:ℝ)) ((2*k)*(d:ℤ)) psi (M/p) := by
    dsimp only [Dsum,parityHarmonicDivisorEnvelope434]
    apply Finset.sum_le_sum
    intro y hy
    by_cases hShift : 0<(y:ℤ)+(2*k)*(d:ℤ)
    · rw [if_pos hShift]
      have hh := hCore.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
        xi3 Z tw psi d y (((y:ℤ)+(2*k)*(d:ℤ)).toNat) (Finset.mem_Ioc.mp hy).1 (by omega)
      exact hh.trans_eq (by rw [div_eq_mul_inv];ring)
    · rw [if_neg hShift]
      positivity
  have hEnv := parity_harmonic_cutoff_divisor_envelope434 L (Z*(d:ℝ)) Kpsi Cpsi hCore.1 hGeom.1 hKpsi
    ((2*k)*(d:ℤ)) hGeom.2.1 hGeom.2.2 psi hSupp hPsi (M/p)
  have hB : 0≤(64*66*(3:ℝ)^15)*Kpsi*L^(15+Cpsi) := by
    have hLp : 0<L := (Real.exp_pos 2).trans_le hL2
    positivity
  calc
    _ = (p:ℝ)⁻¹*Dsum := by
      change (∑ w∈Finset.Ioc 0 M,
        if p∣w ∧ 0<(w:ℤ)+(2*k)*(c:ℤ) then
          ‖parityHarmonicStrippedArithmetic434 L (-xi3) Z EF GG (-(rho+xi3)) (-rho) tw psi
            c w (((w:ℤ)+(2*k)*(c:ℤ)).toNat)‖ else 0)=_
      rw [hd]
      exact parity_stripped_divisible_harmonic_exact434 L (-xi3) Z EF GG (-(rho+xi3)) (-rho) tw psi
        p d M (2*k) hp hpInfo.2.2.1
    _ ≤ (p:ℝ)⁻¹*parityHarmonicDivisorEnvelope434 (Z*(d:ℝ)) ((2*k)*(d:ℤ)) psi (M/p) :=
      mul_le_mul_of_nonneg_left hSmall (by positivity)
    _ ≤ (p:ℝ)⁻¹*((64*66*(3:ℝ)^15)*Kpsi*L^(15+Cpsi)) :=
      mul_le_mul_of_nonneg_left hEnv (by positivity)
    _ ≤ Real.exp (-(L^(3/10:ℝ)))*((64*66*(3:ℝ)^15)*Kpsi*L^(15+Cpsi)) :=
      mul_le_mul_of_nonneg_right hInv hB
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## SharedDefectBudget -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace Green64Analytic.CorrelationSquare

/-- Every original shared slot is one of the original J+ell labels in
its own group; the distinguished SMALL group is included in G. -/
theorem parity_shared_index_card_le434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m≤J) (nu : SourceOriginalProbePattern434 G m) :
    Fintype.card (sourceB574OriginalSharedIndex434 J ell m hmJ nu) ≤
      (J+ell)*Fintype.card G := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ g : G,Fintype.card (sourceOriginalProbeSharedSlots434 J ell m hmJ nu g) ≤
        ∑ _g : G,(J+ell) := by
      apply Finset.sum_le_sum
      intro g _
      simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (sourceOriginalProbeSharedSlots434 J ell m hmJ nu g))
    _ = _ := by simp [Nat.mul_comm]

/-- All labelled A and B auxiliary slots are counted before taking the
numeric image. Repetitions never require a distinct-draw assumption. -/
theorem parity_aux_value_image_card_le434
    {G : Type} [Fintype G] [DecidableEq G]
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (a : SourceOriginalProbeAuxIndex434 m nu → ℕ) :
    (Finset.univ.image a).card ≤ 2*m*Fintype.card G := by
  have hA : nu.1.card ≤ Fintype.card G*m := by
    simpa using (Finset.card_le_card (Finset.subset_univ nu.1))
  have hB : nu.2.card ≤ Fintype.card G*m := by
    simpa using (Finset.card_le_card (Finset.subset_univ nu.2))
  have hcard : Fintype.card (SourceOriginalProbeAuxIndex434 m nu) = nu.1.card+nu.2.card := by
    simp [SourceOriginalProbeAuxIndex434]
  calc
    _ ≤ Fintype.card (SourceOriginalProbeAuxIndex434 m nu) := by
      simpa using Finset.card_image_le (s:=Finset.univ) (f:=a)
    _ ≤ 2*m*Fintype.card G := by rw [hcard]; nlinarith

end Green64Analytic.CorrelationSquare
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD

/-- The exact natural log2 collision count is controlled by the same
real logarithmic cap used by the actual harmonic support proof. -/
theorem parity_log2_of_positive_cap434
    (L : ℝ) (n Y : ℕ) (hn : 0<n) (hnY : n≤Y)
    (hLog : Real.log (Y:ℝ) ≤ 2*L) :
    (n.log2:ℝ) ≤ 2*L/Real.log 2 := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hny : (n:ℝ)≤Y := by exact_mod_cast hnY
  have hg : Real.log (n:ℝ) ≤ 2*L := (Real.log_le_log hn0 hny).trans hLog
  have htwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  exact (Real.log2_le_logb n).trans (by
    unfold Real.logb
    exact div_le_div_of_nonneg_right hg htwo.le)

/-- A fixed explicit constant for all m<=J. It records the complete
shared-coordinate and auxiliary collision counts, not a single group. -/
def paritySharedDefectConstant434 (J : ℕ) : ℝ :=
  (8*(J+1:ℝ))*(4/Real.log 2+16*J)+(8*(J+1:ℝ))^2

theorem parity_shared_defect_constant_nonneg434 (J : ℕ) :
    0≤paritySharedDefectConstant434 J := by
  have htwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold paritySharedDefectConstant434
  positivity

/-- The complete actual B574 shared-defect numerator has an explicit
quadratic logarithmic-scale budget, uniform over every auxiliary tuple.
The original log2 and both A/B numeric images are bounded from their actual
finite carriers, without any prime-independence surrogate. -/
theorem parity_actual_shared_defect_numerator434
    (L : ℝ) (hL : Real.exp 2≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (w wp : ℕ)
    (hw : (w.log2:ℝ)≤2*L/Real.log 2)
    (hwp : (wp.log2:ℝ)≤2*L/Real.log 2) :
    let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
    let I := sourceB574OriginalSharedIndex434 J 1 m hmJ fullnu
    let a := parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu aux
    (Fintype.card I:ℝ)*((w.log2:ℝ)+(wp.log2:ℝ)+((Finset.univ.image a).card:ℝ))+
      (Fintype.card I:ℝ)^2 ≤ paritySharedDefectConstant434 J*L^2 := by
  let G := B645ActualGroup434 L hS
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  let I := sourceB574OriginalSharedIndex434 J 1 m hmJ fullnu
  let a := parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu aux
  have hL1 : 1<L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hL
  have hL0 : 0<L := by linarith
  have hlog : Real.log L≤L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hG : (Fintype.card G:ℝ)≤8*L :=
    (parity_actual_full_group_card_eight434 L hL hS).trans (by gcongr)
  have hI : (Fintype.card I:ℝ)≤(J+1:ℝ)*(Fintype.card G:ℝ) := by
    exact_mod_cast parity_shared_index_card_le434 J 1 m hmJ fullnu
  have hIC : (Fintype.card I:ℝ)≤8*(J+1:ℝ)*L := by
    calc
      _ ≤ (J+1:ℝ)*(Fintype.card G:ℝ) := hI
      _ ≤ (J+1:ℝ)*(8*L) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = _ := by ring
  have ha : ((Finset.univ.image a).card:ℝ)≤2*(m:ℝ)*(Fintype.card G:ℝ) := by
    exact_mod_cast parity_aux_value_image_card_le434 m fullnu a
  have hm : (m:ℝ)≤J := by exact_mod_cast hmJ
  have haC : ((Finset.univ.image a).card:ℝ)≤16*(J:ℝ)*L := by
    calc
      _ ≤ 2*(m:ℝ)*(Fintype.card G:ℝ) := ha
      _ ≤ 2*(J:ℝ)*(8*L) := by gcongr
      _ = _ := by ring
  change (Fintype.card I:ℝ)*((w.log2:ℝ)+(wp.log2:ℝ)+((Finset.univ.image a).card:ℝ))+
    (Fintype.card I:ℝ)^2 ≤ _
  calc
    _ ≤ (8*(J+1:ℝ)*L)*(2*L/Real.log 2+2*L/Real.log 2+16*(J:ℝ)*L)+
        (8*(J+1:ℝ)*L)^2 := by gcongr
    _ = paritySharedDefectConstant434 J*L^2 := by unfold paritySharedDefectConstant434; ring

end Green64Analytic.SourceBlockSieve

end

end

/-! ## SharedRestorationPower -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- The actual full group carrier is exactly the original all-index carrier,
so its proved four-log bound gives the sharper eight-log damping exponent. -/
theorem parity_actual_full_damping_tight_budget434
    (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ) :
    (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ)) ≤
      L^(8*(J+1:ℝ)*Real.log 2) := by
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hc := parity_actual_full_group_card_four434 L hL hS
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfactor : 0 ≤ 2*(J+1:ℝ)*Real.log 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hc hfactor
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by
    simpa only [one_div] using Real.log_inv (2:ℝ)
  rw [Real.rpow_def_of_pos (show (0:ℝ)<1/2 by norm_num),
    Real.rpow_def_of_pos hLp,hhalf]
  apply Real.exp_le_exp.mpr
  convert hm using 1 <;> push_cast <;> ring

/-- Collapse the literal full shared-restoration envelope using the actual
complete group count, actual shared/auxiliary counts and endpoint cap. The
constant and every polynomial loss are displayed; no restoration estimate
is introduced as a premise. -/
theorem parity_actual_shared_restoration_envelope_power434
    (L : ℝ) (hL : Real.exp 2≤L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (xi Em : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (Y w wp : ℕ) (hw : 0<w) (hwY : w≤Y) (hwp : 0<wp) (hwpY : wp≤Y)
    (hLog : Real.log (Y:ℝ)≤2*L)
    (hMark : ∀ n : ℕ,
      ‖actualBigMarkDecoration (b645ActualBand434 L hS)
        (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
        (1/2:ℝ) (Sum.elim (SourceNativeMemorySmallMass434 20 L hS)
          (sourceNativeOriginalVbig434 20 L)) (fun _=>1) n‖≤L^Em) :
    parityActualSharedRestorationEnvelope434 L hS J m hmJ nu Q xi aux w wp ≤
      (2*paritySharedDefectConstant434 J/(Real.log (6/5:ℝ)/2))*
        ((Q:ℝ)^4*(xi⁻¹)^2)*
        L^(8*(J+1:ℝ)*Real.log 2+2*Em+2)*Real.exp (-(L^(1/10:ℝ))) := by
  let D : ℝ := 8*(J+1:ℝ)*Real.log 2
  let C := paritySharedDefectConstant434 J
  let v : ℝ := Real.log (6/5:ℝ)/2
  have hv : 0<v := Green64Analytic.ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  have hC : 0≤C := parity_shared_defect_constant_nonneg434 J
  have hL1 : 1<L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hL
  have hL0 : 0<L := by linarith
  have htwo : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0≤D := by dsimp [D]; positivity
  have hOne : 1≤L^D := Real.one_le_rpow hL1.le hD
  have hdamp := parity_actual_full_damping_tight_budget434 L hL hS J
  have hd : (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ))+1≤2*L^D := by
    change (1/2:ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS):ℝ))≤L^D at hdamp
    linarith
  have hnum := parity_actual_shared_defect_numerator434 L hL hS J m hmJ nu aux w wp
    (parity_log2_of_positive_cap434 L w Y hw hwY hLog)
    (parity_log2_of_positive_cap434 L wp Y hwp hwpY hLog)
  have hpowers : L^D*L^Em*L^Em*L^2 = L^(D+2*Em+2) := by
    simp only [two_mul,Real.rpow_add hL0,Real.rpow_two]
    ring
  unfold parityActualSharedRestorationEnvelope434
  dsimp only
  calc
    _ ≤ (2*L^D)*((Q:ℝ)^4*(xi⁻¹)^2)*(L^Em)*(L^Em)*
        (C*L^2/(Real.exp (L^(1/10:ℝ))*v)) := by
      gcongr
      · exact hMark w
      · exact hMark wp
    _ = (2*C/v)*((Q:ℝ)^4*(xi⁻¹)^2)*
        (L^D*L^Em*L^Em*L^2)*(Real.exp (L^(1/10:ℝ)))⁻¹ := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [hpowers,Real.exp_neg]

/-- A genuine uniform Parity r20 shared-restoration error estimate. J fixes
one marked exponent Em before L; all actual m<=J, patterns, complete auxiliary
tuples and positive endpoints follow. Its mass, geometry, damping and marked
envelopes are proved from the actual construction, never assumed. -/
theorem parity_eventually_actual_shared_power_saving434 (J : ℕ) :
    ∃ Em : ℝ,0≤Em ∧
    ∀ᶠ L : ℝ in atTop, Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (Q : ℕ) (hA hB xi : ℝ)
        (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ) (Y w wp : ℕ),
        0<hA → 0<hB → 0<xi → 0<w → w≤Y → 0<wp → wp≤Y →
        Real.log (Y:ℝ)≤2*L →
        ‖parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q hA hB xi aux w wp‖ ≤
          (2*paritySharedDefectConstant434 J/(Real.log (6/5:ℝ)/2))*
            ((Q:ℝ)^4*(xi⁻¹)^2)*
            L^(8*(J+1:ℝ)*Real.log 2+2*Em+2)*Real.exp (-(L^(1/10:ℝ))) := by
  obtain ⟨Em,hEm,hM⟩ := parity_eventually_actual_marked_log_budget434 J
  refine ⟨Em,hEm,?_⟩
  filter_upwards [hM,parity_eventually_actual_canonical_shared_restoration434,
    eventually_ge_atTop (Real.exp 2)] with L hMark hRest hL
  refine ⟨hL,hMark.2.1,?_⟩
  intro hS m hmJ nu Q hA hB xi aux Y w wp hhA hhB hxi hw hwY hwp hwpY hLog
  have he : ‖parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q hA hB xi aux w wp‖ ≤
      parityActualSharedRestorationEnvelope434 L hS J m hmJ nu Q xi aux w wp :=
    hRest.2.2 hS J m hmJ nu Q hA hB xi aux w wp hhA hhB hxi hw hwp
  exact he.trans (parity_actual_shared_restoration_envelope_power434 L hL hS J m hmJ nu Q xi Em aux
    Y w wp hw hwY hwp hwpY hLog
    (hMark.2.2 hS m hmJ nu (fun _=>1) (fun _=>by simp)))

end Green64Analytic.SourceBlockSieve

end

end

/-! ## SharedHarmonicRestoration -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

/-- Literal absolute harmonic envelope of the actual full canonical shared
restoration differences. Both original fourth-moment divisor weights and
all auxiliary values are retained. This is not the original DR-dependent
arithmetic functional: that functional still requires weighted stripping. -/
def parityActualSharedHarmonicErrorEnvelope434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (hA hB xi : ℝ) (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
    (X : ℝ) (s : ℤ) (psi : ℝ → ℂ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 M,
    ‖psi ((n:ℝ)/X)‖/(n:ℝ) * (n.divisors.card:ℝ)^2 *
      (((n:ℤ)+s).toNat.divisors.card:ℝ)^2 *
      ‖parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q hA hB xi aux
        n ((n:ℤ)+s).toNat‖

/-- The sharper proved actual group count pays for the quadratic collision
numerator within the source's stated sixteen-log and +16 harmonic budget. -/
theorem parity_shared_harmonic_exponent_le_source434 (J : ℕ) (Em Cpsi : ℝ) :
    8*(J+1:ℝ)*Real.log 2+2*Em+17+Cpsi ≤
      16*(J+1:ℝ)*Real.log 2+2*Em+16+Cpsi := by
  have hlog : (1/2:ℝ)≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at hh ⊢
    exact hh
  have hJ : (0:ℝ)≤J := Nat.cast_nonneg J
  nlinarith

/-- The actual Parity full shared restoration differences have the literal
harmonic error budget, uniformly in all original auxiliary assignments.
For fixed J the marked exponent is chosen before L. Actual P sets, group
masses, marked estimates and restoration are discharged internally. This
remains a canonical harmonic envelope; it does not erase the physical
P-cap guards or DR-dependent arithmetic from the original H_T. -/
theorem parity_eventually_actual_shared_harmonic_error434 (J : ℕ) :
    ∃ Em : ℝ,0≤Em ∧
    ∀ᶠ L : ℝ in atTop, Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (Q : ℕ) (hA hB xi : ℝ)
        (aux : SourceOriginalProbeAuxIndex434 m nu → ℕ)
        (X K Cpsi : ℝ) (s : ℤ) (psi : ℝ → ℂ) (M : ℕ),
        0<hA → 0<hB → 0<xi → 1≤X → 0≤K →
        |(s:ℝ)|≤X/128 → Real.log (⌈65*X⌉₊:ℝ)≤2*L →
        (∀ t, psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
        (∀ t, ‖psi t‖≤K*L^Cpsi) →
        parityActualSharedHarmonicErrorEnvelope434 L hS J m hmJ nu Q hA hB xi aux X s psi M ≤
          (2*paritySharedDefectConstant434 J/(Real.log (6/5:ℝ)/2))*
            ((Q:ℝ)^4*(xi⁻¹)^2)*(64*66*(3:ℝ)^15)*K*
            L^(16*(J+1:ℝ)*Real.log 2+2*Em+16+Cpsi)*Real.exp (-(L^(1/10:ℝ))) := by
  obtain ⟨Em,hEm,hR⟩ := parity_eventually_actual_shared_power_saving434 J
  refine ⟨Em,hEm,?_⟩
  filter_upwards [hR] with L hRest
  refine ⟨hRest.1,hRest.2.1,?_⟩
  intro hS m hmJ nu Q hA hB xi aux X K Cpsi s psi M hhA hhB hxi hX hK hs hLog hSupp hPsi
  have hL1 : 1<L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hRest.1
  have hLp : 0<L := by linarith
  have hXp : 0<X := by linarith
  let Y := ⌈65*X⌉₊
  let C : ℝ := 2*paritySharedDefectConstant434 J/(Real.log (6/5:ℝ)/2)
  let A : ℝ := (Q:ℝ)^4*(xi⁻¹)^2
  let D : ℝ := 8*(J+1:ℝ)*Real.log 2
  let B : ℝ := C*A*L^(D+2*Em+2)*Real.exp (-(L^(1/10:ℝ)))
  have hC : 0≤C := div_nonneg
    (mul_nonneg (by norm_num) (parity_shared_defect_constant_nonneg434 J))
    source_actual_P_uniform_mass_floor_positive.le
  have hAnonneg : 0≤A := by dsimp [A]; positivity
  have hBnonneg : 0≤B := by dsimp [B]; positivity
  have hpoint (n : ℕ) (hn : n∈Finset.Ioc 0 M) (hp : psi ((n:ℝ)/X)≠0) :
      ‖parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q hA hB xi aux
        n ((n:ℤ)+s).toNat‖≤B := by
    have hg := parity_harmonic_cutoff_shift_support434 X hXp s hs psi hSupp n hp
    have hnp : 0<((n:ℤ)+s).toNat := by omega
    have hnpy : ((n:ℤ)+s).toNat≤Y := by dsimp [Y]; omega
    exact hRest.2.2 hS m hmJ nu Q hA hB xi aux Y n ((n:ℤ)+s).toNat
      hhA hhB hxi (Finset.mem_Ioc.mp hn).1 hg.2.2.1 hnp hnpy hLog
  have henv : parityActualSharedHarmonicErrorEnvelope434 L hS J m hmJ nu Q hA hB xi aux X s psi M ≤
      B*parityHarmonicDivisorEnvelope434 X s psi M := by
    unfold parityActualSharedHarmonicErrorEnvelope434 parityHarmonicDivisorEnvelope434
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hp : psi ((n:ℝ)/X)=0
    · simp [hp]
    · calc
        _ ≤ (‖psi ((n:ℝ)/X)‖/(n:ℝ)*(n.divisors.card:ℝ)^2*
            (((n:ℤ)+s).toNat.divisors.card:ℝ)^2)*B :=
          mul_le_mul_of_nonneg_left (hpoint n hn hp) (by positivity)
        _ = _ := by ring
  have hpow : L^(D+2*Em+2)*L^(15+Cpsi) = L^(D+2*Em+17+Cpsi) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hexp : L^(D+2*Em+17+Cpsi) ≤ L^(16*(J+1:ℝ)*Real.log 2+2*Em+16+Cpsi) :=
    Real.rpow_le_rpow_of_exponent_le hL1.le (parity_shared_harmonic_exponent_le_source434 J Em Cpsi)
  calc
    _ ≤ B*parityHarmonicDivisorEnvelope434 X s psi M := henv
    _ ≤ B*((64*66*(3:ℝ)^15)*K*L^(15+Cpsi)) :=
      mul_le_mul_of_nonneg_left
        (parity_harmonic_cutoff_divisor_envelope434 L X K Cpsi hL1.le hX hK s hs hLog psi hSupp hPsi M) hBnonneg
    _ = C*A*(64*66*(3:ℝ)^15)*K*L^(D+2*Em+17+Cpsi)*Real.exp (-(L^(1/10:ℝ))) := by
      dsimp only [B]
      calc
        _ = C*A*(64*66*(3:ℝ)^15)*K*(L^(D+2*Em+2)*L^(15+Cpsi))*Real.exp (-(L^(1/10:ℝ))) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## HarmonicShiftCollapse -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 22000

/-- An actual signed displacement admits at most one target endpoint.
The complete finite double sum therefore pays no target-cardinality factor.
The independent gate may include the literal nonzero-shift comparison test. -/
theorem parity_finite_signed_shift_norm434
    (N : Finset ℕ) (s : ℤ) (gate : Prop) [Decidable gate]
    (A : ℕ → ℕ → ℂ) (B : ℕ → ℝ)
    (hB : ∀ n,0≤B n)
    (hA : ∀ n∈N,∀ np∈N,(np:ℤ)=(n:ℤ)+s → ‖A n np‖≤B n) :
    ‖∑ n∈N,∑ np∈N,if gate ∧ (np:ℤ)=(n:ℤ)+s then A n np else 0‖ ≤
      ∑ n∈N,B n := by
  have hinner (n : ℕ) (hn : n∈N) :
      ‖∑ np∈N,if gate ∧ (np:ℤ)=(n:ℤ)+s then A n np else 0‖≤B n := by
    let t := ((n:ℤ)+s).toNat
    calc
      _ ≤ ∑ np∈N,‖if gate ∧ (np:ℤ)=(n:ℤ)+s then A n np else 0‖ := norm_sum_le _ _
      _ ≤ ∑ np∈N,if np=t then B n else 0 := by
        apply Finset.sum_le_sum
        intro np hnp
        by_cases h : gate ∧ (np:ℤ)=(n:ℤ)+s
        · have he : np=t := by
            have he := congrArg Int.toNat h.2
            simpa only [Int.toNat_natCast] using he
          simp only [if_pos h,if_pos he]
          exact hA n hn np hnp h.2
        · rw [if_neg h,norm_zero]
          split_ifs
          · exact hB n
          · exact le_refl _
      _ ≤ B n := by
        by_cases ht : t∈N <;> simp [ht,hB n]
  calc
    _ ≤ ∑ n∈N,‖∑ np∈N,if gate ∧ (np:ℤ)=(n:ℤ)+s then A n np else 0‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum hinner

/-- The norm of the literal Restored-Stripped difference is bounded by a
single harmonic error envelope on a positive finite carrier. Both divisor
square factors and the entire complex error are retained. -/
theorem parity_finite_weighted_restoration_envelope434
    (N : Finset ℕ) (M : ℕ) (hN : N⊆Finset.Ioc 0 M)
    (s : ℤ) (gate : Prop) [Decidable gate]
    (a : ℕ → ℕ → ℂ) (e : ℕ → ℕ → ℂ) (b : ℕ → ℝ)
    (hb : ∀ n,0≤b n)
    (ha : ∀ n∈N,∀ np∈N,(np:ℤ)=(n:ℤ)+s → ‖a n np‖≤b n) :
    ‖∑ n∈N,∑ np∈N,if gate ∧ (np:ℤ)=(n:ℤ)+s then a n np*e n np else 0‖ ≤
      ∑ n∈Finset.Ioc 0 M,b n*‖e n ((n:ℤ)+s).toNat‖ := by
  calc
    _ ≤ ∑ n∈N,b n*‖e n ((n:ℤ)+s).toNat‖ := by
      apply parity_finite_signed_shift_norm434 N s gate
        (fun n np=>a n np*e n np) (fun n=>b n*‖e n ((n:ℤ)+s).toNat‖)
        (fun n=>mul_nonneg (hb n) (norm_nonneg _))
      intro n hn np hnp hshift
      have he : np=((n:ℤ)+s).toNat := by
        have hh := congrArg Int.toNat hshift
        simpa only [Int.toNat_natCast] using hh
      rw [norm_mul]
      calc
        _ ≤ b n*‖e n np‖ := mul_le_mul_of_nonneg_right (ha n hn np hnp hshift) (norm_nonneg _)
        _ = _ := by rw [he]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hN
      (fun n hn hnot=>mul_nonneg (hb n) (norm_nonneg _))
end Green64Analytic.Parity

end

end

/-! ## FreeAuxCollisionBound -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The literal actual weighted free-auxiliary collision on the original
finite positive endpoint carrier, before its typed auxiliary mass is
integrated. All free marks, Knu, source phases, c-dependent cutoff and
signed shift are unchanged. -/
def parityActualFreeCollisionPairSum434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) (N : Finset ℕ) : ℂ :=
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  ∑ w∈N,∑ wp∈N,if (2*k)≠0 ∧ (wp:ℤ)=(w:ℤ)+(2*k)*(c:ℤ) then
    parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp *
    parityCanonicalFreeCollisionSlice434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) Q h h xi
      (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (parityActualFreeCollisionAux434 L hS J m hmJ nu aux) (1/2) w wp
    else 0

/-- Genuine fixed-auxiliary collision saving. The complete original marked
weights cost an actual L^(2 Em), every auxiliary label is charged by the
proved p-divisible harmonic reindex, and all label slots are paid. Neither
ban removal nor auxiliary-dependent harmonic smallness is assumed. -/
theorem parity_eventually_actual_free_collision_pair_bound434
    (J : ℕ) (S beta gamma CZ Ck Cpsi : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) :
    ∃ Em : ℝ,0≤Em ∧
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J)
          (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
          (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (Kpsi : ℝ),0≤Kpsi → ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ (aux : ParityActualProbeAux434 L J m hmJ nu) (N : Finset ℕ),
          (∀ n∈N,0<n) →
          ‖parityActualFreeCollisionPairSum434 L hS J m hmJ nu Q h xi rho xi3 Z k E G tw psi aux N‖≤
          (2*(J:ℝ)*(3+(Real.log 2)⁻¹))*((Q:ℝ)^4*(xi⁻¹)^2)*
            (64*66*(3:ℝ)^15)*Kpsi*L^(2*Em+16+Cpsi)*Real.exp (-(L^(3/10:ℝ))) := by
  obtain ⟨Em,hEm,hMarks⟩ := parity_eventually_actual_marked_log_budget434 J
  refine ⟨Em,hEm,?_⟩
  filter_upwards [parity_eventually_actual_free_collision_prime_charge434 J S beta gamma CZ Ck Cpsi
    hSfine hbeta hgamma hCZ,hMarks] with L hCharge hMarksL
  refine ⟨hCharge.1,hCharge.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ nu Q h xi xi3 Z k hh hxi hZlo hZhi hk Kpsi hKpsi
    tw psi hSupp hPsi aux N hN
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let EF := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let GG := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let fullnu := parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu
  let P := b645ActualBand434 L hS
  let V := Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
  let fullaux := parityActualFreeCollisionAux434 L hS J m hmJ nu aux
  let I := SourceOriginalProbeAuxIndex434 m fullnu
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let s : ℤ := (2*k)*(c:ℤ)
  let Ar := parityHarmonicStrippedArithmetic434 L (-xi3) Z EF GG (-(rho+xi3)) (-rho) tw psi c
  let Coll := parityCanonicalFreeCollisionSlice434 J 1 m hmJ fullnu Q h h xi P V fullaux (1/2)
  let cap : ℝ := (Q:ℝ)^4*(xi⁻¹)^2
  let C := cap*L^(2*Em)
  let f := fun (z : I) (w : ℕ)=>
    if fullaux z∣w ∧ 0<(w:ℤ)+s then ‖Ar w (((w:ℤ)+s).toNat)‖ else 0
  let B := fun w=>C*(∑ z : I,f z w)
  let M := N.sup id
  let T := Real.exp (-(L^(3/10:ℝ)))*(64*66*(3:ℝ)^15)*Kpsi*L^(15+Cpsi)
  let Slt := 2*(J:ℝ)*(3+(Real.log 2)⁻¹)
  have hLp : 0<L := (Real.exp_pos 2).trans_le hCharge.1
  have hL1 : 1<L := hMarksL.1
  have hcap : 0≤ cap := by dsimp only [cap];positivity
  have hC : 0≤C := mul_nonneg hcap (Real.rpow_nonneg hLp.le _)
  have hf (z : I) (w : ℕ) : 0≤f z w := by dsimp only [f];split_ifs <;> positivity
  have hB (w : ℕ) : 0≤B w := mul_nonneg hC (Finset.sum_nonneg (fun z _=>hf z w))
  have hW (n : ℕ) : ‖actualBigMarkDecoration P
      (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu) (1/2) V (fun _=>1) n‖≤L^Em :=
    hMarksL.2.2 hS m hmJ nu (fun _=>1) (by intro lists;norm_num) n
  have hK (w wp : ℕ) : ‖Coll w wp‖≤C := by
    have hc := parity_canonical_free_collision_marked_bound434 J 1 m hmJ fullnu Q h h xi P V fullaux (1/2) w wp hh hh hxi
    calc
      _ ≤ cap*‖actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu) (1/2) V (fun _=>1) w‖*
          ‖actualBigMarkDecoration P (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ fullnu) (1/2) V (fun _=>1) wp‖ := hc
      _ ≤ cap*(L^Em)*(L^Em) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hW w) hcap) (hW wp)
          (norm_nonneg _) (mul_nonneg hcap (Real.rpow_nonneg hLp.le _))
      _ = C := by
        dsimp only [C]
        rw [mul_assoc,←Real.rpow_add hLp]
        congr 2
        ring
  have hD (z : I) : fullaux z∣c :=
    (parity_actual_free_collision_label434 L hL1 hS J m hmJ nu aux z).2.2.2
  have hPoint (w) (hw : w∈N) (wp) (hwp : wp∈N) (he : (wp:ℤ)=(w:ℤ)+s) :
      ‖Ar w wp*Coll w wp‖≤B w := by
    by_cases hz : Coll w wp=0
    · rw [hz,mul_zero,norm_zero]
      exact hB w
    obtain ⟨z,hdiv⟩ := parity_canonical_free_collision_shift_support434 J 1 m hmJ fullnu Q h h xi P V fullaux
      (1/2) c w wp (2*k) hD (hN wp hwp) he hz
    have hpShift : 0<(w:ℤ)+s := by rw [←he];exact_mod_cast hN wp hwp
    have hnext : (((w:ℤ)+s).toNat)=wp := by rw [←he,Int.toNat_natCast]
    have hsingle : ‖Ar w wp‖≤∑ z : I,f z w := by
      have hh := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset I))=>hf j w) (Finset.mem_univ z)
      have hgate : fullaux z∣w ∧ 0<(w:ℤ)+s := ⟨hdiv,hpShift⟩
      simpa only [f,if_pos hgate,hnext] using hh
    calc
      _ = ‖Ar w wp‖*‖Coll w wp‖ := norm_mul _ _
      _ ≤ ‖Ar w wp‖*C := mul_le_mul_of_nonneg_left (hK w wp) (norm_nonneg _)
      _ = C*‖Ar w wp‖ := by ring
      _ ≤ B w := mul_le_mul_of_nonneg_left hsingle hC
  have hCollapse := parity_finite_signed_shift_norm434 N s ((2*k)≠0)
    (fun w wp=>Ar w wp*Coll w wp) B hB hPoint
  have hSub : N⊆Finset.Ioc 0 M := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨hN n hn,Finset.le_sup (f:=id) hn⟩
  have hEach (z : I) : (∑ w∈Finset.Ioc 0 M,f z w)≤T :=
    hCharge.2.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
      hS m hmJ nu xi3 Z k hZlo hZhi hk Kpsi hKpsi tw psi hSupp hPsi aux z M
  have hTN : 0≤T := by dsimp only [T];positivity
  have hExp1 : Real.exp 1≤L := (Real.exp_le_exp.mpr (by norm_num : (1:ℝ)≤2)).trans hCharge.1
  have hSlots : (Fintype.card I:ℝ)≤Slt*L := parity_actual_free_collision_slots434 L hExp1 hS J m hmJ nu
  have hPower : L^(2*Em)*L*L^(15+Cpsi)=L^(2*Em+16+Cpsi) := by
    calc
      _ = L^(2*Em)*L^(1:ℝ)*L^(15+Cpsi) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hLp,←Real.rpow_add hLp];congr 1;ring
  calc
    _ ≤ ∑ w∈N,B w := hCollapse
    _ = C*(∑ z : I,∑ w∈N,f z w) := by
      dsimp only [B]
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ C*(∑ z : I,∑ w∈Finset.Ioc 0 M,f z w) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum (fun z _=>Finset.sum_le_sum_of_subset_of_nonneg hSub (fun w _ _=>hf z w))
    _ ≤ C*(∑ _z : I,T) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z _=>hEach z)) hC
    _ = C*((Fintype.card I:ℝ)*T) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ C*((Slt*L)*T) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSlots hTN) hC
    _ = Slt*cap*(64*66*(3:ℝ)^15)*Kpsi*(L^(2*Em)*L*L^(15+Cpsi))*Real.exp (-(L^(3/10:ℝ))) := by
      dsimp only [C,T]
      ring
    _ = _ := by rw [hPower]
end Green64Analytic.Parity

end

end

/-! ## FreeAuxCollisionFamily -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- The complete weighted collision correction for the actual comparison
family. Every typed auxiliary atom multiplies its own genuine product,
shift and cutoff dependent harmonic collision sum. -/
def parityActualFreeCollisionFamily434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi rho xi3 Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ) (N : Finset ℕ) : ℂ :=
  ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
    ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
      (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ)*
      parityActualFreeCollisionPairSum434 L hS J m hmJ nu.val Q h xi rho xi3 Z k F G tw psi aux N

/-- Genuine full auxiliary and probe-family integration AFTER the proved
actual harmonic collision charge. Complete independent mass one is used
only here; it is not substituted for the removal of a dependent ban. -/
theorem parity_eventually_actual_free_collision_family_bound434
    (J : ℕ) (S beta gamma CZ Ck Cpsi : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) :
    ∃ Em : ℝ,0≤Em ∧
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
        ∀ (Kpsi : ℝ),0≤Kpsi → ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ N : Finset ℕ,(∀ n∈N,0<n) →
          ‖parityActualFreeCollisionFamily434 L hS J m hmJ Q h xi rho xi3 Z k E G tw psi N‖≤
          (2*(J:ℝ)*(3+(Real.log 2)⁻¹))*((Q:ℝ)^4*(xi⁻¹)^2)*
            (64*66*(3:ℝ)^15)*Kpsi*L^(2*Em+16+Cpsi)*Real.exp (-(L^(3/10:ℝ)))*
          ((sourceOriginalTwoBlockProbePatterns434 (sourceNativeOriginalBigBlockA434 20 L)
            (sourceNativeOriginalBigBlockB434 20 L) m).card:ℝ) := by
  obtain ⟨Em,hEm,hPairs⟩ := parity_eventually_actual_free_collision_pair_bound434 J S beta gamma CZ Ck Cpsi hSfine hbeta hgamma hCZ
  refine ⟨Em,hEm,?_⟩
  filter_upwards [hPairs,parity_eventually_actual_typed_aux_mass434 J] with L hSave hMass
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk Kpsi hKpsi tw psi hSupp hPsi N hN
  let F := sourceNativePrimeCore r e L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let EF := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let GG := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let Fam := sourceOriginalTwoBlockProbePatterns434 (sourceNativeOriginalBigBlockA434 20 L)
    (sourceNativeOriginalBigBlockB434 20 L) m
  let C := (2*(J:ℝ)*(3+(Real.log 2)⁻¹))*((Q:ℝ)^4*(xi⁻¹)^2)*
    (64*66*(3:ℝ)^15)*Kpsi*L^(2*Em+16+Cpsi)*Real.exp (-(L^(3/10:ℝ)))
  let mu := fun (nu : ↥Fam) (aux : ParityActualProbeAux434 L J m hmJ nu.val)=>
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ)
  let I := fun (nu : ↥Fam) (aux : ParityActualProbeAux434 L J m hmJ nu.val)=>
    mu nu aux*parityActualFreeCollisionPairSum434 L hS J m hmJ nu.val Q h xi rho xi3 Z k EF GG tw psi aux N
  have hPoint (nu : ↥Fam) (aux : ParityActualProbeAux434 L J m hmJ nu.val) : ‖I nu aux‖≤C*‖mu nu aux‖ := by
    have h := hSave.2.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1 xi1 xi2 rho sigma
      hS m hmJ nu.val Q h xi xi3 Z k hh hxi hZlo hZhi hk Kpsi hKpsi tw psi hSupp hPsi aux N hN
    dsimp only [I]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by ring)
  have hAux (nu : ↥Fam) : (∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,‖I nu aux‖)≤C := by
    calc
      _ ≤ ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,C*‖mu nu aux‖ :=
        Finset.sum_le_sum (fun aux _=>hPoint nu aux)
      _ = C*(∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,‖mu nu aux‖) := by rw [Finset.mul_sum]
      _ = C := by rw [(hMass.2.2 hS m hmJ nu.val).2,mul_one]
  change ‖∑ nu : ↥Fam,∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,I nu aux‖≤C*(Fam.card:ℝ)
  calc
    _ ≤ ∑ nu : ↥Fam,‖∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,I nu aux‖ := norm_sum_le _ _
    _ ≤ ∑ nu : ↥Fam,∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,‖I nu aux‖ :=
      Finset.sum_le_sum (fun nu _=>norm_sum_le _ _)
    _ ≤ ∑ nu : ↥Fam,C := Finset.sum_le_sum (fun nu _=>hAux nu)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
end Green64Analytic.Parity

end

end

/-! ## FreeAuxCollisionSaving -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE

/-- Every requested logarithmic saving for the complete actual collision
family. All choices precede L and the B633 operator tuple. Both reciprocal
cell masses, every free marked weight and every auxiliary/probe label are
paid before the actual exp(-L^.3) charge absorbs the polynomial budget. -/
theorem parity_eventually_actual_free_collision_family_saving434
    (J : ℕ) (S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) (hK : 0≤Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
          (Q:ℝ)≤L^CQ → xi⁻¹≤L^Cxi →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ N : Finset ℕ,(∀ n∈N,0<n) →
          ‖parityActualFreeCollisionFamily434 L hS J m hmJ Q h xi rho xi3 Z k E G tw psi N‖≤L^(-A) := by
  obtain ⟨Em,hEm,hFamily⟩ := parity_eventually_actual_free_collision_family_bound434
    J S beta gamma CZ Ck Cpsi hSfine hbeta hgamma hCZ
  let C := 2*(J:ℝ)*(3+(Real.log 2)⁻¹)
  let K0 := C*(64*66*(3:ℝ)^15)*Kpsi
  let ef := (J:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  let e := 2*Em+16+Cpsi+ef
  let ec := 4*CQ+2*Cxi
  filter_upwards [hFamily,
    eventually_source_fixed_poly_exp_saving (3/10:ℝ) K0 (e+ec) A (by norm_num)] with L hFamily hSave
  refine ⟨hFamily.1,hFamily.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi N hN
  have hLp : 0<L := (Real.exp_pos 2).trans_le hFamily.1
  have hL1 : 1≤L := hSave.1
  have hExp1 : Real.exp 1≤L := (Real.exp_le_exp.mpr (by norm_num : (1:ℝ)≤2)).trans hFamily.1
  have hLog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0≤C := by dsimp only [C];positivity
  have hBound := hFamily.2.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk
    Kpsi hK tw psi hSupp hPsi N hN
  have hCard := parity_actual_probe_family_card434 L hExp1 hS m
  have hCoeff : 0≤(3+(Real.log 2)⁻¹)*Real.log 2 := by positivity
  have hExponent : (m:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2≤ef := by
    have hm : (m:ℝ)≤J := by exact_mod_cast hmJ
    have hc := mul_le_mul_of_nonneg_right hm hCoeff
    simpa only [ef,mul_assoc] using hc
  have hFam : ((sourceOriginalTwoBlockProbePatterns434 (sourceNativeOriginalBigBlockA434 20 L)
      (sourceNativeOriginalBigBlockB434 20 L) m).card:ℝ)≤L^ef :=
    hCard.trans (Real.rpow_le_rpow_of_exponent_le hL1 hExponent)
  have hCell : (Q:ℝ)^4*(xi⁻¹)^2≤L^ec := by
    calc
      _ ≤ (L^CQ)^4*(L^Cxi)^2 :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 4)
          (pow_le_pow_left₀ (inv_nonneg.mpr hxi.le) hXi 2)
          (sq_nonneg _) (pow_nonneg (Real.rpow_nonneg hLp.le CQ) 4)
      _ = L^ec := by
        rw [←Real.rpow_natCast (L^CQ) 4,←Real.rpow_natCast (L^Cxi) 2,
          ←Real.rpow_mul hLp.le,←Real.rpow_mul hLp.le,←Real.rpow_add hLp]
        congr 1
        dsimp only [ec]
        ring
  have hPower : L^ec*L^(2*Em+16+Cpsi)*L^ef=L^(e+ec) := by
    rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
    congr 1
    dsimp only [e]
    ring
  calc
    _ ≤ C*((Q:ℝ)^4*(xi⁻¹)^2)*(64*66*(3:ℝ)^15)*Kpsi*L^(2*Em+16+Cpsi)*
        Real.exp (-(L^(3/10:ℝ)))*
        ((sourceOriginalTwoBlockProbePatterns434 (sourceNativeOriginalBigBlockA434 20 L)
          (sourceNativeOriginalBigBlockB434 20 L) m).card:ℝ) := hBound
    _ ≤ C*L^ec*(64*66*(3:ℝ)^15)*Kpsi*L^(2*Em+16+Cpsi)*Real.exp (-(L^(3/10:ℝ)))*L^ef := by gcongr
    _ = K0*(L^ec*L^(2*Em+16+Cpsi)*L^ef)*Real.exp (-(L^(3/10:ℝ))) := by dsimp only [K0];ring
    _ = K0*L^(e+ec)*Real.exp (-(L^(3/10:ℝ))) := by rw [hPower]
    _ ≤ L^(-A) := by
      simpa only [Real.rpow_neg hLp.le,one_div] using hSave.2

/-- The full original collision family has one external Z and the
requested Z*L^(-A) budget. No factor depending on the auxiliary product is
pulled through its probability law. -/
theorem parity_eventually_actual_free_collision_outer_Z_saving434
    (J : ℕ) (S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) (hK : 0≤Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J) (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),0<h → 0<xi →
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k:ℝ)|≤L^Ck →
          (Q:ℝ)≤L^CQ → xi⁻¹≤L^Cxi →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) → (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ N : Finset ℕ,(∀ n∈N,0<n) →
          ‖(Z:ℂ)*parityActualFreeCollisionFamily434 L hS J m hmJ Q h xi rho xi3 Z k E G tw psi N‖≤Z*L^(-A) := by
  filter_upwards [parity_eventually_actual_free_collision_family_saving434 J S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A
    hSfine hbeta hgamma hCZ hK] with L hSave
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r e hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi N hN
  have hLp : 0<L := (Real.exp_pos 2).trans_le hSave.1
  have hZ : 0<Z := (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hBound := hSave.2.2 prime l u hlow r e hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi N hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hZ.le]
  exact mul_le_mul_of_nonneg_left hBound hZ.le
end Green64Analytic.Parity

end

end

/-! ## WeightedPGateMoment -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 22000

/-- The original general divisor majorant gives the precise eighth moment
needed by the two-core marked P-tail; no shifted divisor hypothesis occurs. -/
theorem parity_tau_eight_counting434 (Y : ℕ) :
    (∑ n∈Finset.Ioc 0 Y, (n.divisors.card:ℝ)^8) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^255 := by
  have hmajor : (∑ n∈Finset.Ioc 0 Y, (n.divisors.card:ℝ)^8) ≤
      ∑ n∈Finset.Ioc 0 Y, ((ArithmeticFunction.zeta^256) n:ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    have hh := Green64Analytic.SourceDivisorMoment.b593_divisor_power_le_zeta_power434
      8 n (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)
    norm_num only [show (2:ℕ)^8=256 by norm_num] at hh
    exact_mod_cast hh
  have hconv : (∑ n∈Finset.Ioc 0 Y, ((ArithmeticFunction.zeta^256) n:ℝ)) ≤
      (Y:ℝ)*(Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Y)^255 := by
    simpa using Green64Analytic.SourceDivisorMoment.b593_zeta_power_unweighted434 Y 254
  exact hmajor.trans (hconv.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_nonneg Y)
      (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_le_one_add_log Y) 255)
    (Nat.cast_nonneg Y)))

/-- Exact injective translation of the eighth divisor moment, for either
signed shift and any finite positive-endpoint support. -/
theorem parity_translated_tau_eight_sum434
    (S : Finset ℕ) (Y : ℕ) (s : ℤ)
    (hS : ∀ n∈S,0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ)) :
    (∑ n∈S,(((n:ℤ)+s).toNat.divisors.card:ℝ)^8) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^255 := by
  classical
  let f : ℕ → ℕ := fun n => ((n:ℤ)+s).toNat
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro a ha b hb hab
    have hpa := (hS a ha).1
    have hpb := (hS b hb).1
    change ((a:ℤ)+s).toNat=((b:ℤ)+s).toNat at hab
    omega
  have hsub : S.image f ⊆ Finset.Ioc 0 Y := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    have hh := hS a ha
    rw [Finset.mem_Ioc]
    dsimp only [f]
    omega
  calc
    _ = ∑ n∈S.image f,(n.divisors.card:ℝ)^8 := by
      symm
      exact Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)
    _ ≤ ∑ n∈Finset.Ioc 0 Y,(n.divisors.card:ℝ)^8 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot => by positivity)
    _ ≤ _ := parity_tau_eight_counting434 Y

/-- Both complete ordinary-core fourth powers are retained and bounded
by the genuine eighth moment, including negative physical shifts. -/
theorem parity_translated_tau_four_product_sum434
    (S : Finset ℕ) (Y : ℕ) (s : ℤ)
    (hS : S⊆Finset.Ioc 0 Y)
    (hShift : ∀ n∈S,0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ)) :
    (∑ n∈S,(n.divisors.card:ℝ)^4*(((n:ℤ)+s).toNat.divisors.card:ℝ)^4) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^255 := by
  have hfirst : (∑ n∈S,(n.divisors.card:ℝ)^8) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^255 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun n hn hnot => by positivity)).trans (parity_tau_eight_counting434 Y)
  have hsecond := parity_translated_tau_eight_sum434 S Y s hShift
  have hpoint : (∑ n∈S,(n.divisors.card:ℝ)^4*(((n:ℤ)+s).toNat.divisors.card:ℝ)^4) ≤
      ((∑ n∈S,(n.divisors.card:ℝ)^8)+
        (∑ n∈S,(((n:ℤ)+s).toNat.divisors.card:ℝ)^8))/2 := by
    calc
      _ ≤ ∑ n∈S,((n.divisors.card:ℝ)^8+
          (((n:ℤ)+s).toNat.divisors.card:ℝ)^8)/2 := by
        apply Finset.sum_le_sum
        intro n hn
        nlinarith [sq_nonneg ((n.divisors.card:ℝ)^4-
          (((n:ℤ)+s).toNat.divisors.card:ℝ)^4)]
      _ = _ := by rw [←Finset.sum_div,Finset.sum_add_distrib]
  linarith

/-- Cauchy with the genuine higher-mark square/W1 domination. The bounded
opposite endpoint is retained as a full multiplicative factor. This finite
inequality never derives a subset bound from a cancelled complex core. -/
theorem parity_higher_mark_tail_cauchy434
    {ι : Type} (S : Finset ι) (a b c W : ι → ℝ) (M U C E : ℝ)
    (hU : 0≤U) (hC : 0≤C) (hE : 0≤E)
    (hb : ∀ z∈S,(b z)^2≤C*W z)
    (hc : ∀ z∈S,0≤ c z ∧ c z≤U)
    (hm : (∑ z∈S,(a z)^2)≤M)
    (he : (∑ z∈S,W z)≤E) :
    (∑ z∈S,a z*b z*c z)^2 ≤ M*U^2*C*E := by
  have hM : 0≤M := (Finset.sum_nonneg (fun z hz => sq_nonneg (a z))).trans hm
  have hbSum : (∑ z∈S,(b z)^2)≤C*E := by
    calc
      _ ≤ ∑ z∈S,C*W z := Finset.sum_le_sum hb
      _ = C*(∑ z∈S,W z) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left he hC
  have hacSum : (∑ z∈S,(a z*c z)^2)≤M*U^2 := by
    calc
      _ ≤ ∑ z∈S,(a z)^2*U^2 := by
        apply Finset.sum_le_sum
        intro z hz
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (hc z hz).1 hU).mpr (hc z hz).2) (sq_nonneg _)
      _ = (∑ z∈S,(a z)^2)*U^2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  have hh := Finset.sum_mul_sq_le_sq_mul_sq S (fun z=>a z*c z) b
  have heq : (∑ z∈S,(a z*c z)*b z) = ∑ z∈S,a z*b z*c z := by
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [heq] at hh
  calc
    _ ≤ (∑ z∈S,(a z*c z)^2)*(∑ z∈S,(b z)^2) := hh
    _ ≤ (M*U^2)*(C*E) := mul_le_mul hacSum hbSum
      (Finset.sum_nonneg (fun z hz=>sq_nonneg _)) (mul_nonneg hM (sq_nonneg _))
    _ = _ := by ring
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualMarkedPTail -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

/-- The norm of the literal all-ones original higher-mark decoration on
all actual SMALL and BIG groups, with the true pattern-dependent free counts. -/
def parityActualFullMarkedWeight434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (n : ℕ) : ℝ :=
  ‖actualBigMarkDecoration (b645ActualBand434 L hS)
    (sourceOriginalProbeFreeMarkCount434 J 1 m hmJ
      (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu))
    (1/2:ℝ)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (fun _=>1) n‖

/-- Genuine product-weight half P-tail with both full divisor-square cores.
For fixed J and requested A, all actual higher-mark, mass, eighth-moment and
Rankin inputs are proved. The integer shift may have either sign. The tail
set is an arbitrary subset of the original positive endpoints, so literal
cutoff or cell restrictions may be retained without cancellation arguments. -/
theorem parity_eventually_actual_marked_half_tail434 (J : ℕ) (A : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (Y : ℕ) (S : Finset ℕ) (s : ℤ),
        1≤Y → Real.log (Y:ℝ)≤2*L → S⊆Finset.Ioc 0 Y →
        (∀ n∈S,0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ)) →
        (∀ n∈S,⌊Real.exp ((1/88:ℝ)*L)⌋₊ <
          sourceOriginalPPrimePart (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) n) →
        (∑ n∈S,(n.divisors.card:ℝ)^2*(((n:ℤ)+s).toNat.divisors.card:ℝ)^2*
          parityActualFullMarkedWeight434 L hS J m hmJ nu n*
          parityActualFullMarkedWeight434 L hS J m hmJ nu ((n:ℤ)+s).toNat) ≤
            (Y:ℝ)*(3:ℝ)^128*L^(-A) := by
  obtain ⟨Em,hEm,hMarked⟩ := parity_eventually_actual_marked_log_budget434 J
  obtain ⟨E,hE,hSquare⟩ := parity_eventually_actual_marked_square_W1434 J
  let Prec : ℝ := 2*A+2*Em+E+255
  filter_upwards [hMarked,hSquare,parity_actual_P_part_half_sigma_all_log_saving434 Prec]
    with L hM hSq hTail
  refine ⟨hSq.1,hSq.2.1,?_⟩
  intro hS m hmJ nu Y S s hY hLog hSub hShift hBad
  have hL1 : 1<L := hM.1
  have hLp : 0<L := by linarith
  let w : ℕ → ℝ := parityActualFullMarkedWeight434 L hS J m hmJ nu
  let a : ℕ → ℝ := fun n=>(n.divisors.card:ℝ)^2*
    (((n:ℤ)+s).toNat.divisors.card:ℝ)^2
  have hw0 (n : ℕ) : 0≤w n := norm_nonneg _
  have hwCap (n : ℕ) : w n≤L^Em :=
    hM.2.2 hS m hmJ nu (fun _=>1) (fun _=>by simp) n
  have hwSq (n : ℕ) : (w n)^2≤L^E*sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) n :=
    hSq.2.2 hS m hmJ nu (fun _=>1) (fun _=>by simp) n
  have hsubTail : S⊆(Finset.Ioc 0 Y).filter (fun n=>
      ⌊Real.exp ((1/88:ℝ)*L)⌋₊ <
        sourceOriginalPPrimePart (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) n) := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨hSub hn,hBad n hn⟩
  have hsumTail : (∑ n∈S,sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) n) ≤
      (Y:ℝ)*L^(-Prec) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubTail
      (fun n hn hnot=>source_original_W1_nonneg _ _)).trans (hTail Y)
  have hYR : (1:ℝ)≤Y := by exact_mod_cast hY
  have hbase : 0≤1+Real.log (Y:ℝ) := by have hh:=Real.log_nonneg hYR;linarith
  have hlog3 : 1+Real.log (Y:ℝ)≤3*L := by linarith
  have hmoment : (∑ n∈S,(a n)^2)≤(Y:ℝ)*(3:ℝ)^255*L^(255:ℝ) := by
    have hm := parity_translated_tau_four_product_sum434 S Y s hSub hShift
    have heq : (∑ n∈S,(a n)^2)=
        ∑ n∈S,(n.divisors.card:ℝ)^4*(((n:ℤ)+s).toNat.divisors.card:ℝ)^4 := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [a]
      ring
    rw [heq]
    calc
      _ ≤ (Y:ℝ)*(1+Real.log (Y:ℝ))^255 := hm
      _ ≤ (Y:ℝ)*(3*L)^255 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hbase hlog3 255) (Nat.cast_nonneg Y)
      _ = _ := by
        rw [show L^(255:ℝ)=L^(255:ℕ) from Real.rpow_natCast L 255,mul_pow]
        ring
  have hcs := parity_higher_mark_tail_cauchy434 S a w (fun n=>w ((n:ℤ)+s).toNat)
    (sourceOriginalW1 (sourceOriginalPAllActualBands 20 L))
    ((Y:ℝ)*(3:ℝ)^255*L^(255:ℝ)) (L^Em) (L^E) ((Y:ℝ)*L^(-Prec))
    (by positivity) (by positivity) (by positivity)
    (fun n hn=>hwSq n) (fun n hn=>⟨hw0 _,hwCap _⟩) hmoment hsumTail
  have hpower : L^(255:ℝ)*(L^Em)^2*L^E*L^(-Prec)=(L^(-A))^2 := by
    simp only [pow_two,←Real.rpow_add hLp]
    congr 1
    dsimp [Prec]
    ring
  have hright : ((Y:ℝ)*(3:ℝ)^255*L^(255:ℝ))*(L^Em)^2*(L^E)*((Y:ℝ)*L^(-Prec)) =
      (Y:ℝ)^2*(3:ℝ)^255*(L^(-A))^2 := by
    calc
      _ = (Y:ℝ)^2*(3:ℝ)^255*(L^(255:ℝ)*(L^Em)^2*L^E*L^(-Prec)) := by ring
      _ = _ := by rw [hpower]
  rw [hright] at hcs
  have hconst : (3:ℝ)^255≤((3:ℝ)^128)^2 := by norm_num
  have hsquare : (∑ n∈S,a n*w n*w ((n:ℤ)+s).toNat)^2 ≤
      ((Y:ℝ)*(3:ℝ)^128*L^(-A))^2 := by
    calc
      _ ≤ (Y:ℝ)^2*(3:ℝ)^255*(L^(-A))^2 := hcs
      _ ≤ (Y:ℝ)^2*((3:ℝ)^128)^2*(L^(-A))^2 := by gcongr
      _ = _ := by ring
  have hsum0 : 0≤∑ n∈S,a n*w n*w ((n:ℤ)+s).toNat := by
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (mul_nonneg (by dsimp [a];positivity) (hw0 n)) (hw0 _)
  exact (sq_le_sq₀ hsum0 (by positivity)).mp hsquare
end Green64Analytic.SourceBlockSieve

end

end

/-! ## MarkedTailTranslation -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

/-- Both ordinary divisor-square factors and both true marked weights. -/
def parityMarkedPairWeight434 (W : ℕ→ℝ) (s : ℤ) (n : ℕ) : ℝ :=
  (n.divisors.card:ℝ)^2*(((n:ℤ)+s).toNat.divisors.card:ℝ)^2*
    W n*W ((n:ℤ)+s).toNat

theorem parity_marked_pair_weight_nonneg434 (W : ℕ→ℝ) (hW : ∀ n,0≤W n)
    (s : ℤ) (n : ℕ) : 0≤parityMarkedPairWeight434 W s n := by
  unfold parityMarkedPairWeight434
  exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hW n)) (hW _)

/-- Reversal keeps both endpoints and the exact signed shift. -/
theorem parity_marked_pair_weight_reverse434 (W : ℕ→ℝ) (s : ℤ) (n : ℕ)
    (hn : 0<(n:ℤ)+s) :
    parityMarkedPairWeight434 W (-s) ((n:ℤ)+s).toNat = parityMarkedPairWeight434 W s n := by
  have hback : (((((n:ℤ)+s).toNat:ℤ)+(-s)).toNat)=n := by omega
  unfold parityMarkedPairWeight434
  rw [hback]
  ring

/-- The translated carrier and its reverse both retain the exact common
positive integer cap. No shift-sign restriction is introduced. -/
theorem parity_shifted_positive_image434 (S : Finset ℕ) (Y : ℕ) (s : ℤ)
    (hS : S⊆Finset.Ioc 0 Y)
    (hShift : ∀ n∈S,0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ)) :
    S.image (fun n : ℕ=>((n:ℤ)+s).toNat)⊆Finset.Ioc 0 Y ∧
    ∀ u∈S.image (fun n : ℕ=>((n:ℤ)+s).toNat),0<(u:ℤ)+(-s) ∧ (u:ℤ)+(-s)≤(Y:ℤ) := by
  constructor
  · intro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    have hh:=hShift n hn
    rw [Finset.mem_Ioc]
    omega
  · intro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    have hh:=hShift n hn
    have hpos:=Finset.mem_Ioc.mp (hS hn)
    omega

/-- Exact finite reindexing for the genuine symmetric product weight. -/
theorem parity_marked_pair_reverse_sum434
    (W : ℕ→ℝ) (S : Finset ℕ) (s : ℤ)
    (hShift : ∀ n∈S,0<(n:ℤ)+s) :
    (∑ n∈S,parityMarkedPairWeight434 W s n) =
      ∑ u∈S.image (fun n : ℕ=>((n:ℤ)+s).toNat),parityMarkedPairWeight434 W (-s) u := by
  have hinj : Set.InjOn (fun n : ℕ=>((n:ℤ)+s).toNat) (↑S:Set ℕ) := by
    intro a ha b hb hab
    have hpa:=hShift a ha
    have hpb:=hShift b hb
    change ((a:ℤ)+s).toNat=((b:ℤ)+s).toNat at hab
    omega
  rw [Finset.sum_image (fun a ha b hb hab=>hinj ha hb hab)]
  apply Finset.sum_congr rfl
  intro n hn
  exact (parity_marked_pair_weight_reverse434 W s n (hShift n hn)).symm

/-- Both endpoint half-P-tail errors for the complete actual marked product
are bounded simultaneously, including negative shifts and arbitrary subsets. -/
theorem parity_eventually_actual_marked_both_half_tails434 (J : ℕ) (A : ℝ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (m : ℕ) (hmJ : m≤J)
        (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
        (Y : ℕ) (S : Finset ℕ) (s : ℤ),
        1≤Y → Real.log (Y:ℝ)≤2*L → S⊆Finset.Ioc 0 Y →
        (∀ n∈S,0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ)) →
        let W := parityActualFullMarkedWeight434 L hS J m hmJ nu
        let part := sourceOriginalPPrimePart (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
        let H := ⌊Real.exp ((1/88:ℝ)*L)⌋₊
        (∑ n∈S.filter (fun n : ℕ=>H<part n),parityMarkedPairWeight434 W s n)+
          (∑ n∈S.filter (fun n : ℕ=>H<part ((n:ℤ)+s).toNat),parityMarkedPairWeight434 W s n) ≤
            2*(Y:ℝ)*(3:ℝ)^128*L^(-A) := by
  filter_upwards [parity_eventually_actual_marked_half_tail434 J A] with L hTail
  refine ⟨hTail.1,hTail.2.1,?_⟩
  intro hS m hmJ nu Y S s hY hLog hSub hShift
  dsimp only
  let W := parityActualFullMarkedWeight434 L hS J m hmJ nu
  let part := sourceOriginalPPrimePart (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L))
  let H := ⌊Real.exp ((1/88:ℝ)*L)⌋₊
  let SL := S.filter (fun n : ℕ=>H<part n)
  let SR := S.filter (fun n : ℕ=>H<part ((n:ℤ)+s).toNat)
  have hSL : SL⊆Finset.Ioc 0 Y := fun n hn=>hSub (Finset.mem_filter.mp hn).1
  have hSR : SR⊆Finset.Ioc 0 Y := fun n hn=>hSub (Finset.mem_filter.mp hn).1
  have hShiftL : ∀ n∈SL,0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ) :=
    fun n hn=>hShift n (Finset.mem_filter.mp hn).1
  have hShiftR : ∀ n∈SR,0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ) :=
    fun n hn=>hShift n (Finset.mem_filter.mp hn).1
  have hleft : (∑ n∈SL,parityMarkedPairWeight434 W s n)≤(Y:ℝ)*(3:ℝ)^128*L^(-A) :=
    hTail.2.2 hS m hmJ nu Y SL s hY hLog hSL hShiftL
      (fun n hn=>(Finset.mem_filter.mp hn).2)
  let R := SR.image (fun n : ℕ=>((n:ℤ)+s).toNat)
  have hR := parity_shifted_positive_image434 SR Y s hSR hShiftR
  have hBadR : ∀ u∈R,H<part u := by
    intro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hn).2
  have hright : (∑ n∈SR,parityMarkedPairWeight434 W s n)≤(Y:ℝ)*(3:ℝ)^128*L^(-A) := by
    rw [parity_marked_pair_reverse_sum434 W SR s (fun n hn=>(hShiftR n hn).1)]
    exact hTail.2.2 hS m hmJ nu Y R (-s) hY hLog hR.1 hR.2 hBadR
  calc
    _ ≤ (Y:ℝ)*(3:ℝ)^128*L^(-A)+(Y:ℝ)*(3:ℝ)^128*L^(-A) := add_le_add hleft hright
    _ = _ := by ring
end Green64Analytic.SourceBlockSieve

end

end

