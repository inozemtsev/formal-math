module

public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Weights.Part113
public import Green64.Library.Weights.Part109
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Sieve.Foundations.Part013
public import Green64.Library.Sieve.Foundations.Part023
public import Green64.Library.Sieve.Foundations.Part022
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part008
public import Green64.Library.Sieve.Foundations.Part020

@[expose] public section

/-!
# Sieve / Foundations / Part033

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalEq417BetaLossFinite -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Exact original physical positive shifted pair mask for the actual
Parity (4.17) cofactor sum. The original N is NOT enlarged silently. -/
def parityOriginalEq417PositivePositions434 (k : ℤ) (N : Finset ℕ) : Finset ℕ :=
  N.filter (fun z => 0 < (z:ℤ)+2*k)

/-- Arithmetic original W1(z)W1(z+2k)*tau(z)^2*tau(z+2k)^2,
precisely the source majorant in the beta/4 two-endpoint Rankin theorem. -/
def parityOriginalEq417PositivePairMajorant434 (L : ℝ) (k : ℤ) (z : ℕ) : ℝ :=
  (z.divisors.card:ℝ)^2 *
    ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2) *
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) z *
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
      (((z:ℤ)+2*k).toNat)

/-- Exact finite physical Eq417 beta/4 cofactor cap loss bounded by
the original P-weighted two-divisor-square majorant for the REAL
unmodified source cores. No complex cancellation or abstract gated
correlation saving is used. The assumptions on the two core norms
and psi are later discharged by ACTUAL B656 and source smoothness. -/
theorem parity_original_eq417_beta_capped_loss_le_physical_majorant434
    (beta L rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ)
    (F G : PrimeSlotCore) (signed : Bool) (psi : ℝ → ℂ)
    (Cpsi : ℝ) (hCpsi : 0 ≤ Cpsi)
    (hN : ∀ z∈N, 0<z)
    (hPsi : ∀ z∈N, ‖psi ((z:ℝ)/Z)‖ ≤ Cpsi)
    (hF : ∀ z∈N,
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F z‖ ≤
        (z.divisors.card:ℝ)^2)
    (hG : ∀ z∈N, 0 < (z:ℤ)+2*k →
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G
        (((z:ℤ)+2*k).toNat)‖ ≤
        ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2)) :
    ‖parityOriginalEq417WithFirstCore434 L rho xi3 Z k N F G signed psi -
      parityOriginalEq417BetaCapped434 beta L rho xi3 Z k N F G signed psi‖ ≤
    Cpsi * ∑ z∈parityOriginalEq417PositivePositions434 k N,
      if parityOriginalPhysicalPcapBeta434 beta L z ∧
          parityOriginalPhysicalPcapBeta434 beta L (((z:ℤ)+2*k).toNat)
      then (0:ℝ) else parityOriginalEq417PositivePairMajorant434 L k z := by
  let R := parityOriginalEq417PositivePairMajorant434 L k
  let S := parityOriginalEq417PositivePositions434 k N
  have hR (z : ℕ) : 0 ≤ R z := by
    dsimp [R,parityOriginalEq417PositivePairMajorant434]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (source_original_W1_nonneg _ _))
      (source_original_W1_nonneg _ _)
  have hPoint (z : ℕ) (hz : z∈N) :
      ‖(1-parityOriginalPhysicalPairPcapBeta434 beta L z
          (((z:ℤ)+2*k).toNat))*
        parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z‖ ≤
      if 0 < (z:ℤ)+2*k then
        (if parityOriginalPhysicalPcapBeta434 beta L z ∧
             parityOriginalPhysicalPcapBeta434 beta L (((z:ℤ)+2*k).toNat)
         then (0:ℝ) else Cpsi*R z)
      else 0 := by
    by_cases hp : 0 < (z:ℤ)+2*k
    · have hBound := parity_original_eq417_full_term_tau2_pointwise434
        L rho xi3 Z k F G signed psi z (hN z hz) hp (hF z hz)
        (hG z hz hp)
      have hBoundC : ‖parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z‖ ≤
           Cpsi*R z := by
        calc
          _ ≤ ‖psi ((z:ℝ)/Z)‖ * (z.divisors.card:ℝ)^2 *
                 ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2) *
                 sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) z *
                 sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
                    (((z:ℤ)+2*k).toNat) := hBound
          _ = ‖psi ((z:ℝ)/Z)‖*R z := by
                 dsimp [R,parityOriginalEq417PositivePairMajorant434];ring
          _ ≤ Cpsi*R z := mul_le_mul_of_nonneg_right (hPsi z hz) (hR z)
      by_cases hc : parityOriginalPhysicalPcapBeta434 beta L z ∧
        parityOriginalPhysicalPcapBeta434 beta L (((z:ℤ)+2*k).toNat)
      · simp [hp,hc,parityOriginalPhysicalPairPcapBeta434]
      · simpa only [hp,hc,ite_true,ite_false,
          parityOriginalPhysicalPairPcapBeta434,sub_zero,one_mul] using hBoundC
    · simp [hp,parityOriginalEq417FullTerm434]
  rw [parity_original_eq417_beta_capped_exact_complement434]
  calc
    ‖∑ z∈N, (1-parityOriginalPhysicalPairPcapBeta434 beta L z
        (((z:ℤ)+2*k).toNat))*
        parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z‖ ≤
      ∑ z∈N, ‖(1-parityOriginalPhysicalPairPcapBeta434 beta L z
        (((z:ℤ)+2*k).toNat))*
        parityOriginalEq417FullTerm434 L rho xi3 Z k F G signed psi z‖ := norm_sum_le _ _
    _ ≤ ∑ z∈N, if 0 < (z:ℤ)+2*k then
        (if parityOriginalPhysicalPcapBeta434 beta L z ∧
          parityOriginalPhysicalPcapBeta434 beta L (((z:ℤ)+2*k).toNat)
          then (0:ℝ) else Cpsi*R z) else 0 :=
      Finset.sum_le_sum hPoint
    _ = Cpsi * (∑ z∈S, if parityOriginalPhysicalPcapBeta434 beta L z ∧
           parityOriginalPhysicalPcapBeta434 beta L (((z:ℤ)+2*k).toNat)
         then (0:ℝ) else R z) := by
      rw [Finset.mul_sum]
      unfold S parityOriginalEq417PositivePositions434
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hp : 0 < (z:ℤ)+2*k <;> simp [hp] <;> ring
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## OriginalEq417BetaLossActual -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Fully unconditional ACTUAL fine-b629 original Parity(4.17)
complex signed beta-dependent two-Ppart-cap loss for both independent
ε=1 and ε=E. The only external inputs are original positive physical
endpoint geometry and the original psi sup norm; neither a core norm
hypothesis nor a beta-correlator saving is assumed. B656 bounds both
physical cofactor cores; the source original beta Rankin theorem and
shifted eighth-divisor moment pay the whole two-ended discarded set.
The bound has true Y scale for the original Z-dyadic, not exp(2L).
This is a complex physical correlation error, not the whole TypeII. -/
theorem parity_eventually_original_actual_eq417_beta_pair_complex_cap_loss434
    (S betaFine gamma betaCap A : ℝ)
    (hS : 0<S) (hFine : 0<betaFine) (hgamma : 0<gamma)
    (hCap : 0<betaCap) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
      ∀ (prime : Bool) (lFine uFine : ℕ),
        Real.exp (betaFine*L) ≤ (lFine:ℝ) →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (freq : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q)
        (rho xi1 xi2 xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ)
        (signed : Bool) (psi : ℝ → ℂ) (Cpsi : ℝ) (Y : ℕ),
      0 ≤ Cpsi → 1 ≤ Y → (Y:ℝ) ≤ Real.exp (2*L) →
      Real.log (Y:ℝ) ≤ 2*L →
      (∀ z∈N, z∈Finset.Ioc 0 Y) →
      (∀ z∈N, 0<(z:ℤ)+2*k → (z:ℤ)+2*k≤(Y:ℤ)) →
      (∀ z∈N, ‖psi ((z:ℝ)/Z)‖ ≤ Cpsi) →
      let F := sourceNativePrimeCore 20 d L band slot delta freq K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine) q chi 0 0
      let Fparity := b633ParityFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho 0
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho 0
      ‖parityOriginalEq417WithFirstCore434 L rho xi3 Z k N Fparity Gcore signed psi -
        parityOriginalEq417BetaCapped434 betaCap L rho xi3 Z k N
          Fparity Gcore signed psi‖ ≤
        2*Cpsi*(Y:ℝ)*(3:ℝ)^128*L^(-A) := by
  filter_upwards [parity_eventually_original_eq417_actual_two_core_tau2_bounds434
      S betaFine gamma hS hFine hgamma,
    parity_eventually_original_beta_shifted_pair_W1_tau2_tail434 betaCap A hCap]
    with L hCores hTail
  refine ⟨hTail.1,?_⟩
  intro prime lFine uFine hFineLow d band slot delta freq K q chi
    rho xi1 xi2 xi3 Z k N signed psi Cpsi Y hCpsi hY hYexp hYlog hN hShift hPsi
  let F := sourceNativePrimeCore 20 d L band slot delta freq K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine) q chi 0 0
  let Fparity := b633ParityFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho 0
  let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho 0
  let Pos := parityOriginalEq417PositivePositions434 k N
  have hNpos : ∀ z∈N,0<z := by
    intro z hz
    exact (Finset.mem_Ioc.mp (hN z hz)).1
  have hFbound : ∀ z∈N,
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) Fparity z‖ ≤
        (z.divisors.card:ℝ)^2 := by
    intro z hz
    have hzY : (z:ℝ) ≤ (Y:ℝ) := Nat.cast_le.mpr (Finset.mem_Ioc.mp (hN z hz)).2
    have hBound := hCores prime lFine uFine hFineLow d band slot delta freq
      K q chi xi1 xi2 rho 0 z (hNpos z hz) (hzY.trans hYexp)
    exact hBound.1
  have hGbound : ∀ z∈N,0<(z:ℤ)+2*k →
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) Gcore
        (((z:ℤ)+2*k).toNat)‖ ≤
      ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2) := by
    intro z hz hp
    have hzp : 0<(((z:ℤ)+2*k).toNat) := by omega
    have hShiftY := hShift z hz hp
    have hBoundY : (((z:ℤ)+2*k).toNat:ℝ) ≤ (Y:ℝ) := by
      exact_mod_cast (show ((z:ℤ)+2*k).toNat ≤ Y by omega)
    have hBound := hCores prime lFine uFine hFineLow d band slot delta freq
      K q chi xi1 xi2 rho 0 (((z:ℤ)+2*k).toNat) hzp (hBoundY.trans hYexp)
    exact hBound.2
  have hFinite := parity_original_eq417_beta_capped_loss_le_physical_majorant434
    betaCap L rho xi3 Z k N Fparity Gcore signed psi Cpsi hCpsi
    hNpos hPsi hFbound hGbound
  have hPosSub : Pos ⊆ Finset.Ioc 0 Y := by
    intro z hz
    exact hN z (Finset.mem_filter.mp hz).1
  have hPosShift : ∀ z∈Pos, 0 < (z:ℤ)+2*k ∧
      (z:ℤ)+2*k ≤ (Y:ℤ) := by
    intro z hz
    exact ⟨(Finset.mem_filter.mp hz).2,
      hShift z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2⟩
  have hTailBound := hTail.2 Y Pos (2*k) hY hYlog hPosSub (by
    intro z hz
    convert hPosShift z hz using 1 <;> ring)
  have hTail' :
      (∑ z∈Pos,
        if parityOriginalPhysicalPcapBeta434 betaCap L z ∧
           parityOriginalPhysicalPcapBeta434 betaCap L (((z:ℤ)+2*k).toNat)
        then (0:ℝ) else parityOriginalEq417PositivePairMajorant434 L k z) ≤
      2*(Y:ℝ)*(3:ℝ)^128*L^(-A) := by
    simpa only [parityOriginalEq417PositivePairMajorant434] using hTailBound
  change ‖parityOriginalEq417WithFirstCore434 L rho xi3 Z k N Fparity Gcore signed psi -
      parityOriginalEq417BetaCapped434 betaCap L rho xi3 Z k N Fparity Gcore signed psi‖ ≤ _
  calc
    _ ≤ Cpsi * (∑ z∈Pos,
        if parityOriginalPhysicalPcapBeta434 betaCap L z ∧
           parityOriginalPhysicalPcapBeta434 betaCap L (((z:ℤ)+2*k).toNat)
        then (0:ℝ) else parityOriginalEq417PositivePairMajorant434 L k z) :=
      hFinite
    _ ≤ Cpsi*(2*(Y:ℝ)*(3:ℝ)^128*L^(-A)) :=
      mul_le_mul_of_nonneg_left hTail' hCpsi
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalEq417DyadicPairGeometry -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Concrete original Parity(4.17) physical two-endpoint envelope:
Y=ceil(128Z) covers the ENTIRE original [1,floor64Z] source carrier
and both z,z+2k for every original signed nonzero k. Its size is
<=129Z, and Y<=exp(2L), so the precise eighth-moment shifted Rankin
theorem applies at scale Z, not the incorrect scale exp(2L).
All estimates uniform for original Z~exp(L)L^±CZ and |k|<=L^Ck. -/
theorem parity_eventually_original_eq417_true_Z_pair_envelope434
    (CZ Ck : ℝ) (hCZ : 0 ≤ CZ) (hCk : 0 ≤ Ck) :
    ∀ᶠ L : ℝ in atTop, 32 ≤ L ∧
      ∀ (Z : ℝ) (k : ℤ),
        Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
        (k.natAbs:ℝ) ≤ L^Ck →
        let Y := ⌈128*Z⌉₊
        0 < Z ∧ 1 ≤ Y ∧ (Y:ℝ) ≤ 129*Z ∧
        (Y:ℝ) ≤ Real.exp (2*L) ∧ Real.log (Y:ℝ) ≤ 2*L ∧
        (∀ z∈Finset.Icc 1 ⌊64*Z⌋₊, z ∈ Finset.Ioc 0 Y) ∧
        (∀ z∈Finset.Icc 1 ⌊64*Z⌋₊,
          0<(z:ℤ)+2*k → (z:ℤ)+2*k ≤ (Y:ℤ)) := by
  filter_upwards [parity_eventually_rank_cell_signed_shift434 CZ Ck hCZ hCk,
    parity_eventually_source_Z_dyad_floor434 CZ hCZ,
    eventually_native_source_poly_lt_exp_scaled434 CZ 1 (1/2)
      hCZ (by norm_num) (by norm_num),
    eventually_ge_atTop (2*Real.log (129:ℝ))]
    with L hSmall hZlo hPoly hConst
  have hL : 32 ≤ L := hZlo.2.1
  refine ⟨hL,?_⟩
  intro Z k hZlower hZupper hk
  let Y := ⌈128*Z⌉₊
  have hZ : 0 < Z := (hSmall.2 Z k hZlower (by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hk)).1
  have hZlarge : 128*Real.exp (L/2) ≤ Z := hZlo.2.2 Z hZlower
  have hZ1 : 1 ≤ Z := by
    have hexp1 : (1:ℝ) ≤ Real.exp (L/2) := Real.one_le_exp (by linarith)
    nlinarith [hZlarge,hexp1]
  have h128 : 0 ≤ 128*Z := by positivity
  have hYceil : 128*Z ≤ (Y:ℝ) := Nat.le_ceil _
  have hYhi : (Y:ℝ) ≤ 128*Z+1 := (Nat.ceil_lt_add_one h128).le
  have hYpos : 1 ≤ Y := by
    have hYcast : (1:ℝ) ≤ (Y:ℝ) := by linarith
    exact_mod_cast hYcast
  have hY129 : (Y:ℝ) ≤ 129*Z := by linarith
  have hLp : 0 < L := by linarith
  have hPow : L^CZ ≤ Real.exp (L/2) := by
    simpa only [Real.rpow_one,one_div_mul_eq_div] using hPoly.2.le
  have hExp : (129:ℝ) ≤ Real.exp (L/2) := by
    have hlog : Real.log (129:ℝ) ≤ L/2 := by linarith
    calc
      (129:ℝ) = Real.exp (Real.log 129) := (Real.exp_log (by norm_num : (0:ℝ)<129)).symm
      _ ≤ Real.exp (L/2) := Real.exp_le_exp.mpr hlog
  have hYexp : (Y:ℝ) ≤ Real.exp (2*L) := by
    calc
      _ ≤ 129*Z := hY129
      _ ≤ 129*(Real.exp L*L^CZ) := mul_le_mul_of_nonneg_left hZupper (by norm_num)
      _ ≤ Real.exp L*(Real.exp (L/2)*Real.exp (L/2)) := by
        have hbound : 129*L^CZ ≤ Real.exp (L/2)*Real.exp (L/2) :=
          mul_le_mul hExp hPow (Real.rpow_nonneg hLp.le CZ) (Real.exp_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg L)]
      _ = Real.exp (2*L) := by
        rw [←Real.exp_add, ←Real.exp_add]
        congr 1
        ring
  have hYlog : Real.log (Y:ℝ) ≤ 2*L := by
    have hYp : 0 < (Y:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hYpos)
    have hh := Real.log_le_log hYp hYexp
    simpa only [Real.log_exp] using hh
  have hSmall' := (hSmall.2 Z k hZlower (by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hk)).2
  have hShiftAbs : |(2*(k:ℝ))| ≤ Z := by
    have hRat : |2*(k:ℝ)|/Z ≤ (1:ℝ) := by
      have hinv : (128*Real.exp 2)⁻¹ ≤ (1:ℝ) := by
        apply (inv_le_one₀ (by positivity)).mpr
        nlinarith [Real.exp_pos (2:ℝ),Real.add_one_le_exp (2:ℝ)]
      simpa only [abs_div,abs_of_pos hZ] using hSmall'.trans hinv
    simpa only [one_mul] using (div_le_iff₀ hZ).mp hRat
  have hU : ∀ z∈Finset.Icc 1 ⌊64*Z⌋₊, z∈Finset.Ioc 0 Y := by
    intro z hz
    have hBound : (z:ℝ) ≤ 128*Z := by
      have hzle : z ≤ ⌊64*Z⌋₊ := (Finset.mem_Icc.mp hz).2
      have hFloor : (⌊64*Z⌋₊:ℝ) ≤ 64*Z := Nat.floor_le (by positivity)
      exact (Nat.cast_le.mpr hzle).trans (by linarith)
    have hzY : (z:ℝ) ≤ (Y:ℝ) := hBound.trans hYceil
    have hzpos : 0<z := (Finset.mem_Icc.mp hz).1
    exact Finset.mem_Ioc.mpr ⟨hzpos, by exact_mod_cast hzY⟩
  refine ⟨hZ,hYpos,hY129,hYexp,hYlog,hU,?_⟩
  intro z hz hzshift
  have hzBig : (z:ℝ) ≤ 64*Z := by
    have hzc : z ≤ ⌊64*Z⌋₊ := (Finset.mem_Icc.mp hz).2
    exact (Nat.cast_le.mpr hzc).trans (Nat.floor_le (by positivity))
  have hShiftReal : (((z:ℤ)+2*k):ℝ) ≤ 128*Z := by
    have hcast : (((z:ℤ)+2*k):ℝ) = (z:ℝ)+2*(k:ℝ) := by push_cast;ring
    rw [hcast]
    have h2 : 2*(k:ℝ) ≤ |2*(k:ℝ)| := le_abs_self _
    linarith
  have hnat : (((z:ℤ)+2*k).toNat:ℤ)=(z:ℤ)+2*k := by omega
  have hh' : (((z:ℤ)+2*k).toNat:ℝ) = (((z:ℤ)+2*k):ℝ) := by
    exact_mod_cast hnat
  have hShiftY : (((z:ℤ)+2*k).toNat:ℝ) ≤ (Y:ℝ) := by
    rw [hh']
    exact hShiftReal.trans hYceil
  have hh : ((z:ℤ)+2*k).toNat ≤ Y := by exact_mod_cast hShiftY
  omega
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUnrestrictedPairMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- The ORIGINAL completely unrestricted Parity(4.17) two-endpoint
physical z carrier after the exact smooth dyadic ψ(z/Z) is applied,
retaining both the native positive shifted z+2k test and the
ACTUAL C∞ positive compact cutoff. This is NOT a SOURCE-filtered
subset: no recovered n or original Q Pfree e gate appears. -/
def parityOriginalHistoricalUnrestrictedSmoothedZCarrier434
    (k : ℤ) (Z : ℝ) (psi : ℝ → ℂ) (N : Finset ℕ) : Finset ℕ :=
  N.filter (fun z => 0 < (z:ℤ)+2*k ∧ psi ((z:ℝ)/Z) ≠ 0)

/-- **ACTUAL UNRESTRICTED PARITY(4.15) SHIFTED DIVISOR PAIR MASS**:
For ANY arbitrary finite z-set N, any integer (positive OR negative)
nonzero or zero k with |2k|≤Z/128 and ORIGINAL fixed smooth compact
ψ supported [1/64,64], the full shifted divisor-square product on
ALL unrestricted physically nonzero z,z+2k is bounded by one
NATIVE fourth divisor moment, with NO signed-subset estimate:

 Σ_{z∈N, ψ(z/Z)≠0,z+2k>0} τ(z)^2 τ(z+2k)^2
    ≤ Y (1+log Y)^15,  Y=ceil(65Z).

This is precisely the arithmetic backbone of manuscript (4.15).
The shift and repeated prime factors are literal; the source
underlying `parity_translated_tau_square_product_sum434` is an
independent actual fourth divisor moment, valid for either sign.
No e,n,historical Y0, H0 prime-slot, χ or Fourier assumption. -/
theorem parity_original_historical_unrestricted_417_shifted_tau_pair_mass434
    (k : ℤ) (Z : ℝ) (psi : ℝ → ℂ) (N : Finset ℕ)
    (hZ : 0<Z) (hk : |((2*k:ℤ):ℝ)|≤Z/128)
    (hPsi : ∀t, psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) :
    (∑z∈parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N,
      (z.divisors.card:ℝ)^2 *
        ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2)) ≤
    ((Nat.ceil (65*Z):ℕ):ℝ) *
      (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 := by
  let S := parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N
  let Y := Nat.ceil (65*Z)
  have hPosShift (z : ℕ) (hz : z∈S) :
      0 < (z:ℤ)+2*k ∧ (z:ℤ)+2*k ≤ (Y:ℤ) := by
    have hzMem := (Finset.mem_filter.mp hz).2
    have hpsi : psi ((z:ℝ)/Z)≠0 := hzMem.2
    have hh := parity_harmonic_cutoff_shift_support434 Z hZ (2*k) hk psi hPsi z hpsi
    exact ⟨hh.1,hh.2.1⟩
  have hSubset : S⊆Finset.Ioc 0 Y := by
    intro z hz
    have hh := (Finset.mem_filter.mp hz).2.2
    have hBound := parity_harmonic_cutoff_shift_support434
      Z hZ (2*k) hk psi hPsi z hh
    have hzLo : Z/64 ≤ (z:ℝ) := hBound.2.2.2
    have hzPos : 0<z := by
      have hCast : (0:ℝ)<(z:ℝ) := (div_pos hZ (by norm_num)).trans_le hzLo
      exact_mod_cast hCast
    exact Finset.mem_Ioc.mpr ⟨hzPos,hBound.2.2.1⟩
  exact parity_translated_tau_square_product_sum434 S Y (2*k) hSubset hPosShift
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUnrestrictedWeightedMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 28000000

/-- ORIGINAL full UNRESTRICTED Parity (4.15) physical pair
absolute mass, including BOTH actual P-group W1 weights,
but NO analytic cancellation:

 Σ_{z,ψ(z/Z)≠0,z+2k>0} ‖ψ(z/Z)‖
    τ(z)^2 τ(z+2k)^2 W1(z)W1(z+2k)
 ≤ Cψ L^(2CW1) ceil(65Z)(1+log ceil65Z)^15.

Here k can be signed; all ordinary prime factors and P-group
weights are genuine. The uniform W1 pointwise exponent is
an unconditional earlier native original source theorem, and
the shifted two-divisor-square moment is the NATIVE full
translated fourth-moment estimate. Unlike earlier SOURCE-only
cofactor bound, THIS bound applies to the WHOLE unrestricted
Parity(4.17) z-carrier, including all potential ghost terms after
removing n/u support. It is precisely the quantitative mass
needed for a future uniform Fourier tail estimate on those ghosts.
No Parity (4.17) spectral saving assumed. -/
theorem parity_eventually_original_historical_unrestricted_417_W1_shifted_pair_mass434 :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      ∀ (k : ℤ) (Z : ℝ) (psi : ℝ → ℂ) (N : Finset ℕ)
        (Cpsi : ℝ),
      0≤Cpsi → (∀t,‖psi t‖≤Cpsi) →
      0<Z → |((2*k:ℤ):ℝ)|≤Z/128 →
      (∀t, psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
      (∑z∈parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N,
        ‖psi ((z:ℝ)/Z)‖*
          parityOriginalEq417PositivePairMajorant434 L k z) ≤
      Cpsi * L^(2*parityOriginalW1PolylogExponent434) *
        ((Nat.ceil (65*Z):ℕ):ℝ)*
          (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 := by
  filter_upwards [parity_eventually_original_actual_W1_pointwise_polylog434,
    eventually_gt_atTop (0:ℝ)] with L hW hL
  refine ⟨hL,?_⟩
  intro k Z psi N Cpsi hCpsi hPsi hZ hk hSupport
  let S := parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N
  let LW := L^parityOriginalW1PolylogExponent434
  let Y := Nat.ceil (65*Z)
  let a : ℕ → ℝ := fun z =>
    (z.divisors.card:ℝ)^2 *
      ((((z:ℤ)+2*k).toNat.divisors.card:ℝ)^2)
  have hLW : 0≤LW := Real.rpow_nonneg hL.le _
  have hTerm (z : ℕ) (hz : z∈S) :
      ‖psi ((z:ℝ)/Z)‖*
        parityOriginalEq417PositivePairMajorant434 L k z ≤
      (Cpsi*LW^2)*a z := by
    have hpsi := hPsi ((z:ℝ)/Z)
    have ha : 0≤a z := by dsimp [a]; positivity
    have hWz := hW z
    have hWzp := hW (((z:ℤ)+2*k).toNat)
    have hWz0 := source_original_W1_nonneg (sourceOriginalPAllActualBands 20 L) z
    have hWzp0 := source_original_W1_nonneg
      (sourceOriginalPAllActualBands 20 L) (((z:ℤ)+2*k).toNat)
    have hFirst : ‖psi ((z:ℝ)/Z)‖*a z ≤ Cpsi*a z :=
      mul_le_mul_of_nonneg_right hpsi ha
    have hSecond : (‖psi ((z:ℝ)/Z)‖*a z)*
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) z ≤
      (Cpsi*a z)*LW :=
      mul_le_mul hFirst hWz hWz0 (mul_nonneg hCpsi ha)
    have hThird : ((‖psi ((z:ℝ)/Z)‖*a z)*
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) z)*
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
          (((z:ℤ)+2*k).toNat) ≤
      ((Cpsi*a z)*LW)*LW :=
      mul_le_mul hSecond hWzp hWzp0
        (mul_nonneg (mul_nonneg hCpsi ha) hLW)
    dsimp [parityOriginalEq417PositivePairMajorant434,a] at hThird ⊢
    nlinarith [hThird]
  have hSum :
      (∑z∈S,‖psi ((z:ℝ)/Z)‖*
        parityOriginalEq417PositivePairMajorant434 L k z) ≤
      (Cpsi*LW^2)*(∑z∈S,a z) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hTerm
  have hTau : (∑z∈S,a z) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^15 :=
    parity_original_historical_unrestricted_417_shifted_tau_pair_mass434
      k Z psi N hZ hk hSupport
  have hCoeff : 0≤Cpsi*LW^2 := mul_nonneg hCpsi (sq_nonneg _)
  have hPow : LW^2 = L^(2*parityOriginalW1PolylogExponent434) := by
    dsimp [LW]
    rw [pow_two,←Real.rpow_add hL]
    congr 1
    ring
  calc
    _ ≤ (Cpsi*LW^2)*(∑z∈S,a z) := hSum
    _ ≤ (Cpsi*LW^2)*((Y:ℝ)*(1+Real.log (Y:ℝ))^15) :=
      mul_le_mul_of_nonneg_left hTau hCoeff
    _ = _ := by rw [hPow]; ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqUnrestrictedActualCoreMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 28500000

/-- ACTUAL unrestricted ORIGINAL Parity (4.16)--(4.17) first and
second genuine B633 prime-slot cores, with fine b629 actual alpha,
original skipped-Q H0 residual, literal χ and Fourier frequencies:
The COMPLETE shifted signed correlation term z,z+2k has the
unconditional positive norm majorant W1(z)W1(z+2k)
τ(z)^2 τ(z+2k)^2 × ‖ψ(z/Z)‖. This is proven for ALL positive
z,z+2k≤exp(2L), not just the physical source e,n image.

Consequently at legitimate fixed height Z (Y=ceil65Z≤exp2L),
UNRESTRICTED z-carrier actual full two-core correlation ℓ1 mass
is at most Cψ L^(2CW1) Y(1+log Y)^15. There is no signed spectral
saving, but this is the precise universal Parity (4.15) polynomial
positive mass needed to bound *ghost* truncated Fourier integrals
when passing from a physical SOURCE mask to unrestricted 4.17.
Both signs of k and all repeated group primes stay literal.
No arbitrary alpha bound: the REAL original B656 native first/second
core pointwise estimates are invoked. -/
theorem parity_eventually_original_historical_unrestricted_417_actual_B633_core_mass434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      ∀ (prime : Bool) (lFine uFine : ℕ),
      Real.exp (beta*L)≤(lFine:ℝ) →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (K : Finset ℕ) (k : ℤ)
        (χ : DirichletCharacter ℂ (2*k.natAbs))
        (rho xi1 xi2 xi3 sigma Z : ℝ) (psi : ℝ → ℂ)
        (N : Finset ℕ) (signed : Bool) (Cpsi : ℝ),
      0≤Cpsi → (∀t,‖psi t‖≤Cpsi) →
      0<Z → |((2*k:ℤ):ℝ)|≤Z/128 →
      (∀t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
      ((Nat.ceil (65*Z):ℕ):ℝ)≤Real.exp (2*L) →
      let F := sourceNativePrimeCore 20 d L band slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        (2*k.natAbs) χ 0 0
      let Fc := b633ParityFirstCore434 F.alpha F.residual
        (2*k.natAbs) χ F.lo F.hi xi2 rho sigma
      let Gc := b633ParitySecondCore434 F.alpha F.residual
        (2*k.natAbs) χ F.lo F.hi xi1 rho sigma
      (∑z∈parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N,
        ‖parityOriginalEq417FullTerm434 L rho xi3 Z k Fc Gc signed psi z‖) ≤
      Cpsi*L^(2*parityOriginalW1PolylogExponent434)*
        ((Nat.ceil (65*Z):ℕ):ℝ)*
        (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 := by
  filter_upwards [parity_eventually_original_eq417_actual_two_core_tau2_bounds434
      S beta gamma hS hbeta hgamma,
    parity_eventually_original_historical_unrestricted_417_W1_shifted_pair_mass434]
    with L hCore hMass
  refine ⟨hMass.1,?_⟩
  intro prime lFine uFine hFineLow d band slot δ ξ K k χ
    rho xi1 xi2 xi3 sigma Z psi N signed Cpsi hCpsi hPsi hZ hk hSupport hYexp
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K
      (b629ActualFineAlpha434 prime L S gamma lFine uFine)
      (2*k.natAbs) χ 0 0
  let Fc := b633ParityFirstCore434 F.alpha F.residual
      (2*k.natAbs) χ F.lo F.hi xi2 rho sigma
  let Gc := b633ParitySecondCore434 F.alpha F.residual
      (2*k.natAbs) χ F.lo F.hi xi1 rho sigma
  let Sm := parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z psi N
  let Y := Nat.ceil (65*Z)
  have hYbound (z : ℕ) (hz : z∈Sm) :
      0<z ∧ 0<((z:ℤ)+2*k).toNat ∧
      (z:ℝ)≤Real.exp (2*L) ∧
      (((z:ℤ)+2*k).toNat:ℝ)≤Real.exp (2*L) := by
    have hmem := (Finset.mem_filter.mp hz).2
    have hShift := parity_harmonic_cutoff_shift_support434
      Z hZ (2*k) hk psi hSupport z hmem.2
    have hzp : 0<((z:ℤ)+2*k).toNat := by omega
    have hzR : (z:ℝ)≤Real.exp (2*L) := by
      have hh : z≤Y := hShift.2.2.1
      exact (by exact_mod_cast hh : (z:ℝ)≤(Y:ℝ)) |>.trans hYexp
    have hzpR : (((z:ℤ)+2*k).toNat:ℝ)≤Real.exp (2*L) := by
      have hh : ((z:ℤ)+2*k).toNat≤Y := by omega
      exact (by exact_mod_cast hh : (((z:ℤ)+2*k).toNat:ℝ)≤(Y:ℝ)) |>.trans hYexp
    have hzpos : 0<z := by
      have hLo := hShift.2.2.2
      have hh : (0:ℝ)<(z:ℝ) := (div_pos hZ (by norm_num)).trans_le hLo
      exact_mod_cast hh
    exact ⟨hzpos,hzp,hzR,hzpR⟩
  have hEach (z : ℕ) (hz : z∈Sm) :
      ‖parityOriginalEq417FullTerm434 L rho xi3 Z k Fc Gc signed psi z‖ ≤
        ‖psi ((z:ℝ)/Z)‖*
          parityOriginalEq417PositivePairMajorant434 L k z := by
    obtain ⟨hzpos,hzppos,hzR,hzpR⟩ := hYbound z hz
    have hShift : 0<(z:ℤ)+2*k := (Finset.mem_filter.mp hz).2.1
    have hCoreZ := hCore prime lFine uFine hFineLow d band slot δ ξ
      K (2*k.natAbs) χ xi1 xi2 rho sigma z hzpos hzR
    have hCoreZp := hCore prime lFine uFine hFineLow d band slot δ ξ
      K (2*k.natAbs) χ xi1 xi2 rho sigma ((z:ℤ)+2*k).toNat hzppos hzpR
    have hh := parity_original_eq417_full_term_tau2_pointwise434
      L rho xi3 Z k Fc Gc signed psi z hzpos hShift
      hCoreZ.1 hCoreZp.2
    simpa only [parityOriginalEq417PositivePairMajorant434,mul_assoc] using hh
  have hSum := Finset.sum_le_sum hEach
  have hMass' := hMass.2 k Z psi N Cpsi hCpsi hPsi hZ hk hSupport
  exact hSum.trans hMass'
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSmoothPsiSup -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The ONE SOURCE-CONSTRUCTED fixed original Parity4.17 smooth dyadic
profile ψ(t)=guard(t)*(step(t/2)-step(t)) has a GLOBAL L-independent
supremum ‖ψ(t)‖≤1. This is proved pointwise using actual two native
ContDiffBump functions valued in [0,1], not a hypothetical ψ size
assumption. The source ψ remains C∞, compact on 1<t<4, with a
fixed all-derivative Schwartz log budget already verified. -/
theorem parity_original_historical_explicit_smooth_dyadic_psi_norm_le_one434
    (t : ℝ) : ‖parityOriginalHistoricalDyadicSmoothPsi434 t‖ ≤ 1 := by
  let g : ℝ := parityOriginalHistoricalDyadicPositiveGuard434 t
  let b : ℝ := parityOriginalHistoricalDyadicSmoothStep434 (t/2)
  let c : ℝ := parityOriginalHistoricalDyadicSmoothStep434 t
  have hg0 : 0≤g := parityOriginalHistoricalDyadicPositiveGuard434.nonneg
  have hg1 : g≤1 := parityOriginalHistoricalDyadicPositiveGuard434.le_one
  have hb0 : 0≤b := parityOriginalHistoricalDyadicSmoothStep434.nonneg
  have hb1 : b≤1 := parityOriginalHistoricalDyadicSmoothStep434.le_one
  have hc0 : 0≤ c := parityOriginalHistoricalDyadicSmoothStep434.nonneg
  have hc1 : c≤1 := parityOriginalHistoricalDyadicSmoothStep434.le_one
  have hdiff : |b-c|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hEq : parityOriginalHistoricalDyadicSmoothPsi434 t = ((g*(b-c):ℝ):ℂ) := rfl
  rw [hEq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hg0]
  calc
    g*|b-c| ≤ g*1 := mul_le_mul_of_nonneg_left hdiff hg0
    _ ≤ 1 := by simpa only [mul_one] using hg1
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqFixedPsiActualCoreMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 700000

/-- The true ORIGINAL Parity(4.17) FULL UNRESTRICTED B633 prime-slot
sum with all original b629 fine alpha and B509 residual atoms,
signed ε and physical shift h=-2, has genuine absolute ℓ1 mass
bounded by L^(2CW1) ceil65Z(1+logceil65Z)^15 using our EXACT
source fixed C∞ smooth dyadic ψ. No source n/u support filters,
φ(2|k|) or artificial prime-free-e gate. The only remaining
height hypothesis is literal ceil65Z≤exp(2L), discharged from
Parity417's actual Z≍exp L L^O(1) by a separate elementary bound.
This mass applies to every potential ghost cell after physical
source support is dropped, and is independent of Fourier phases.
It does NOT prove Parity417 signed cancellation on a subset. -/
theorem parity_eventually_original_historical_fixed_psi_unrestricted_B633_core_mass434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta)
    (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      ∀ (prime : Bool) (lFine uFine : ℕ),
      Real.exp (beta*L)≤(lFine:ℝ) →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (K : Finset ℕ) (k : ℤ)
        (χ : DirichletCharacter ℂ (2*k.natAbs))
        (rho xi1 xi2 xi3 sigma Z : ℝ)
        (N : Finset ℕ) (signed : Bool),
      0<Z → |((2*k:ℤ):ℝ)|≤Z/128 →
      ((Nat.ceil (65*Z):ℕ):ℝ)≤Real.exp (2*L) →
      let F := sourceNativePrimeCore 20 d L band slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        (2*k.natAbs) χ 0 0
      let Fc := b633ParityFirstCore434 F.alpha F.residual
        (2*k.natAbs) χ F.lo F.hi xi2 rho sigma
      let Gc := b633ParitySecondCore434 F.alpha F.residual
        (2*k.natAbs) χ F.lo F.hi xi1 rho sigma
      (∑z∈parityOriginalHistoricalUnrestrictedSmoothedZCarrier434 k Z
          parityOriginalHistoricalDyadicSmoothPsi434 N,
        ‖parityOriginalEq417FullTerm434 L rho xi3 Z k Fc Gc signed
          parityOriginalHistoricalDyadicSmoothPsi434 z‖) ≤
      L^(2*parityOriginalW1PolylogExponent434)*
        ((Nat.ceil (65*Z):ℕ):ℝ)*
        (1+Real.log ((Nat.ceil (65*Z):ℕ):ℝ))^15 := by
  filter_upwards [parity_eventually_original_historical_unrestricted_417_actual_B633_core_mass434
    S beta gamma hS hbeta hgamma] with L hFull
  refine ⟨hFull.1,?_⟩
  intro prime lFine uFine hl d band slot δ ξ K k χ
    rho xi1 xi2 xi3 sigma Z N signed hZ hk hYexp
  have hh := hFull.2 prime lFine uFine hl d band slot δ ξ K k χ
    rho xi1 xi2 xi3 sigma Z parityOriginalHistoricalDyadicSmoothPsi434
    N signed 1 (by norm_num)
    parity_original_historical_explicit_smooth_dyadic_psi_norm_le_one434
    hZ hk parity_original_historical_dyadic_psi_Parity417_support434 hYexp
  simpa only [one_mul] using hh
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqGhostFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1300000

/-- On any finite original Parity(4.14) potential full Parity(4.17)
source event set, if the genuine SOURCE smooth eta_e*eta_n
Schwartz kernel is zero at EVERY member's real log triple,
its entire signed complex full 3D Fourier integral is ZERO.
This does not claim that the low-frequency Fourier ball is zero. -/
theorem parity_original_historical_3d_ghost_full_integral_zero434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (hZero : ∀ i∈S, f (t i)=0) :
    (∫ ξ : EuclideanSpace ℝ (Fin 3),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ξ)=0 := by
  have hSignal : parityOriginal3DPhysicalFiniteSignal434 S W t f=0 := by
    unfold parityOriginal3DPhysicalFiniteSignal434
    apply Finset.sum_eq_zero
    intro i hi
    rw [hZero i hi,mul_zero]
  have hInv := parity_original_3d_physical_finite_source_fourier_fubini434 S W t f
  rw [hSignal] at hInv
  exact hInv.symm

/-- SOURCE-EXACT ghost extension estimate: although the
FULL Euclidean Fourier integral of unsupported B633 events
vanishes by eta_e*eta_n=0, their truncated Fourier BALL need not
vanish. Its norm is bounded by ONLY the genuine unrestricted
positive coefficient mass Σ‖W_i‖ times the original fixed 3D
Schwartz H moment /T^H. The ghost index set S may be arbitrary,
signed coefficients and all P-group multiplicities retained;
no illegitimate complex subset monotonicity or Parity417 saving.
The remaining substantive work is proving off-source B633 pairs
have actual f(t)=0 at their recovered log coordinates and linking
the real unrestricted B633 cofactor mass to Σ‖W_i‖. -/
theorem parity_original_historical_3d_ghost_ball_le_source_moment434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (H : ℕ) (L : ℝ) (hL : 8≤L)
    (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (T : ℝ) (hT : 0<T)
    (hZero : ∀i∈S,
      parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hBufSmooth hBufSupport (t i)=0) :
    ‖∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ‖ ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport)/T^H) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  have hSignal : parityOriginal3DPhysicalFiniteSignal434 S W t f=0 := by
    unfold parityOriginal3DPhysicalFiniteSignal434
    apply Finset.sum_eq_zero
    intro i hi
    rw [hZero i hi,mul_zero]
  have hTrunc := parity_original_historical_actual_dyadic_finite_3d_truncation434
    S W t H L hL U E V Z k buf a b hBufSmooth hBufSupport T hT
  change ‖parityOriginal3DPhysicalFiniteSignal434 S W t f-
    (∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ξ)‖ ≤ _ at hTrunc
  rw [hSignal,zero_sub,norm_neg] at hTrunc
  exact hTrunc
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqGhostTransfer -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- THE CORRECT ORIGINAL PARITY(4.17) complex correlation EXTENSION
PRINCIPLE. Let S be the unrestricted full two-prime-slot B633
candidate events (m,m',z). Let P be the exact physical SOURCE
predicate on the same finite set. If the actual original C∞
eta_e*eta_n Fourier profile f vanishes on ALL unsupported
members S\P, then for EVERY T>0 and H the difference between
physical low-frequency Fourier ball and unrestricted full B633
low-frequency ball is controlled by the positive ORIGINAL ghost
coefficient l1 mass times real 3D source Schwartz H moment/T^H:

   ‖BALL_source_physical‖ ≤ ‖BALL_unrestricted‖
      + (Σ_ghost ‖W_i‖) B_H(f)/T^H.

This is a rigorous replacement for the invalid assertion that
a complex sub-sum is dominated by the unrestricted full sum.
It is signed, keeps complex phases and exact 2π Fourier
convention, and imposes no assumed Parity417 cancellation. The
hypothesis f=0 on ghosts is ESSENTIAL and must be verified for
the actual full Parity(4.14) e,n reconstruction; this theorem does
NOT pretend that verification has already been completed. -/
theorem parity_original_historical_3d_source_ball_le_unrestricted_plus_ghost434
    {ι : Type*} (S : Finset ι) (P : ι → Prop)
    (W : ι → ℂ) (t : ι → EuclideanSpace ℝ (Fin 3))
    (H : ℕ) (L : ℝ) (hL : 8≤L)
    (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (T : ℝ) (hT : 0<T)
    (hGhostZero : ∀i∈S, ¬P i →
      parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hBufSmooth hBufSupport (t i)=0) :
    ‖∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434
        (S.filter P) W t
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ‖ ≤
    ‖∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ‖ +
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (S.filter (fun i => ¬P i)) W *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport)/T^H) := by
  classical
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  let B : Set (EuclideanSpace ℝ (Fin 3)) := {ξ | ‖ξ‖≤T}
  let SG := S.filter P
  let SB := S.filter (fun i => ¬P i)
  let I (R : Finset ι) : ℂ :=
    ∫ξ in B, parityOriginal3DPhysicalFiniteTwistedSource434 R W t f ξ
  have hSplit : I S = I SG + I SB := by
    dsimp [I]
    rw [parity_original_3d_physical_source_finite_fourier_ball_fubini434 S W t f T,
        parity_original_3d_physical_source_finite_fourier_ball_fubini434 SG W t f T,
        parity_original_3d_physical_source_finite_fourier_ball_fubini434 SB W t f T]
    exact (Finset.sum_filter_add_sum_filter_not S P (fun i =>
      ∫ξ in B,
        W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ)).symm
  have hZero : ∀i∈SB, f (t i)=0 := by
    intro i hi
    have hh := Finset.mem_filter.mp hi
    exact hGhostZero i hh.1 hh.2
  have hGhost := parity_original_historical_3d_ghost_ball_le_source_moment434
    SB W t H L hL U E V Z k buf a b hBufSmooth hBufSupport T hT hZero
  have hEq : I SG = I S-I SB := by
    rw [hSplit]
    ring
  change ‖I SG‖≤‖I S‖ +
    parityOriginal3DPhysicalFiniteCoefficientMass434 SB W*
      (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
  rw [hEq]
  have hGhostBound : ‖I SB‖ ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434 SB W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := hGhost
  exact (norm_sub_le (I S) (I SB)).trans (by linarith [hGhostBound])
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualSourceEtaGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Exactly the ORIGINAL fixed C∞ Parity(4.14) eta_e(e/E)*eta_n(n/V)
Schwartz kernel, evaluated on an arbitrary real 3D logarithmic
point, is ZERO whenever the reconstructed real e/E-cutoff is zero.
No requirement that reconstructed e actually be a natural integer,
or that k have a particular sign. Hence this is an analytic
support statement, NOT yet the entire source physical-mask theorem. -/
theorem parity_original_historical_actual_3d_source_zero_if_eta_e_zero434
    (L : ℝ) (hL : 8≤L) (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (t : EuclideanSpace ℝ (Fin 3))
    (hZero : parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
      (parityOriginalHistoricalEtaELogArg434 U E k
        (EuclideanSpace.equiv (Fin 3) ℝ t))=0) :
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport t=0 := by
  unfold parityOriginalHistoricalActualDyadicCutoffSchwartz434
  rw [parity_original_historical_pulled_euclidean_3d_apply434]
  unfold parityOriginalHistoricalPulledBuffered3D434
    parityOriginalHistoricalPulledCutoff3D434
  rw [hZero]
  ring

/-- The same ORIGINAL Fourier kernel is ZERO whenever the
reconstructed real n/V cutoff η_n is zero, independently of
whether e,n are integer or source-eligible. This precisely
controls the smooth n/V window, not its arithmetic integrality. -/
theorem parity_original_historical_actual_3d_source_zero_if_eta_n_zero434
    (L : ℝ) (hL : 8≤L) (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (t : EuclideanSpace ℝ (Fin 3))
    (hZero : parityOriginalHistoricalActualEtaN434
      (parityOriginalHistoricalEtaNLogArg434 U V Z k
        (EuclideanSpace.equiv (Fin 3) ℝ t))=0) :
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport t=0 := by
  unfold parityOriginalHistoricalActualDyadicCutoffSchwartz434
  rw [parity_original_historical_pulled_euclidean_3d_apply434]
  unfold parityOriginalHistoricalPulledBuffered3D434
    parityOriginalHistoricalPulledCutoff3D434
  rw [hZero]
  ring

/-- Nonzero native Parity(4.14) 3D Schwartz coefficient itself
forces the TRUE original e/E and n/V support intervals at its
real reconstructed logarithmic arguments:
  (L^-88)/2 < e/E < 2,    1/2 < n/V < 3.
There is NO artificial sharp u≤2expL or Pfree e assumption.
This establishes that any candidate unrestricted B633 pair
outside either smooth real window is a real Fourier GHOST.
It does NOT establish natural integrality, original odd-e
congruence or the prime-slot e/n divisor conditions, which must
be handled by character orthogonality and reverse arithmetic. -/
theorem parity_original_historical_actual_3d_source_nonzero_real_windows434
    (L : ℝ) (hL : 8≤L) (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (t : EuclideanSpace ℝ (Fin 3))
    (hNZ : parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport t≠0) :
    let eArg := parityOriginalHistoricalEtaELogArg434 U E k
      (EuclideanSpace.equiv (Fin 3) ℝ t)
    let nArg := parityOriginalHistoricalEtaNLogArg434 U V Z k
      (EuclideanSpace.equiv (Fin 3) ℝ t)
    L^(-88:ℝ)/2 < eArg ∧ eArg<2 ∧ (1/2:ℝ)<nArg ∧ nArg<3 := by
  dsimp only
  let eArg := parityOriginalHistoricalEtaELogArg434 U E k
      (EuclideanSpace.equiv (Fin 3) ℝ t)
  let nArg := parityOriginalHistoricalEtaNLogArg434 U V Z k
      (EuclideanSpace.equiv (Fin 3) ℝ t)
  have heNZ : parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL eArg≠0 := by
    intro hh
    exact hNZ (parity_original_historical_actual_3d_source_zero_if_eta_e_zero434
      L hL U E V Z k buf a b hSmooth hSupport t hh)
  have hnNZ : parityOriginalHistoricalActualEtaN434 nArg≠0 := by
    intro hh
    exact hNZ (parity_original_historical_actual_3d_source_zero_if_eta_n_zero434
      L hL U E V Z k buf a b hSmooth hSupport t hh)
  have ha := parity_original_historical_real_e_eta_parameter434 L hL
  have heRange := parity_original_historical_dyadic_eta_e_complex_support434
    (L^(-88:ℝ)) ha.1 ha.2 eArg (by
      simpa only [parityOriginalHistoricalDyadicEtaEAtLComplex434,
        parityOriginalHistoricalDyadicEtaEAtLReal434,
        parityOriginalHistoricalDyadicEtaE434] using heNZ)
  have hnRange := parity_original_historical_actual_eta_n_support434 nArg hnNZ
  exact ⟨heRange.1,heRange.2,hnRange.1,hnRange.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualFullChiProjector -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1900000

/-- Corrected ORIGINAL Parity(2.5)--(2.6) COMPLETE physical
cofactor χ PROJECTOR over ANY unrestricted finite (m,m',z)
index set, retaining the literal actual b629 fine α_m and
conjugate α_m' pair factors even where one or BOTH vanish:

 Σ_i A_i α_m star(α_m') 1_{k|(m'-m), odd((m'-m)/k)}
   = Σχ cχ Σ_i A_i α_m star(α_m') χ(m') starχ(m).

Unlike the earlier native projector theorem, the full unrestricted
index set requires NO hypothesis of nonzero fine α at each i.
The proof first removes the zero-alpha terms EXACTLY, applies
the proven original odd+unit cofactor arithmetic, then restores
all zero terms; no additional prime-free-e source restriction,
no invented character bound, and no complex signed-subset
inequality. In particular fractional-even/nonintegral e ghosts
are killed by Fourier orthogonality AFTER the χ sum, not by the
per-character SOURCE eta_e smooth factor alone.
The remaining bridge to Parity(4.17) is still the physical source
n-integrality and n/u smoothing, which are different conditions. -/
theorem parity_eventually_original_full_unrestricted_actual_alpha_odd_e_projector434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ {I : Type} [DecidableEq I] (T : Finset I)
        (m mp : I → ℕ) (A : I → ℂ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      (∑i∈T, (A i*alpha (m i)*star (alpha (mp i))) *
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
         then (1:ℂ) else 0)) =
      ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∑i∈T, (A i*alpha (m i)*star (alpha (mp i))) *
          χ (mp i:ZMod (2*k.natAbs)) *
          star (χ (m i:ZMod (2*k.natAbs)))) := by
  filter_upwards [parity_eventually_actual_fine_integer_pair_mask_fourier434
    S beta gamma Ck hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro prime l u hl hlow K k hk hkBound I decI T m mp A
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let P : I → Prop := fun i => alpha (m i)≠0 ∧ alpha (mp i)≠0
  let TG := T.filter P
  let W : I → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))
  have hZero (i : I) (hi : ¬P i) : W i=0 := by
    by_cases hmi : alpha (m i)=0
    · simp [W,hmi]
    · have hmpi : alpha (mp i)=0 := by
        by_contra hh
        exact hi ⟨hmi,hh⟩
      simp [W,hmpi]
  have hFilter (F : I → ℂ)
      (hF : ∀i, ¬P i → F i=0) :
      (∑i∈T,F i)=(∑i∈TG,F i) := by
    change (∑i∈T,F i)=(∑i∈T.filter P,F i)
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hh
    · rfl
    · exact hF i hh
  have hLhs :
      (∑i∈T, W i*(if k∣(mp i:ℤ)-(m i:ℤ) ∧
        Odd (((mp i:ℤ)-(m i:ℤ))/k) then (1:ℂ) else 0)) =
      (∑i∈TG,W i*(if k∣(mp i:ℤ)-(m i:ℤ) ∧
        Odd (((mp i:ℤ)-(m i:ℤ))/k) then (1:ℂ) else 0)) := by
    apply hFilter
    intro i hi
    rw [hZero i hi,zero_mul]
  have hRhs (χ : DirichletCharacter ℂ (2*k.natAbs)) :
      (∑i∈T,W i*χ (mp i:ZMod (2*k.natAbs))*
        star (χ (m i:ZMod (2*k.natAbs)))) =
      (∑i∈TG,W i*χ (mp i:ZMod (2*k.natAbs))*
        star (χ (m i:ZMod (2*k.natAbs)))) := by
    apply hFilter
    intro i hi
    rw [hZero i hi,zero_mul,zero_mul]
  have hNonzero (i : I) (hi : i∈TG) :
      alpha (m i)≠0 ∧ alpha (mp i)≠0 := (Finset.mem_filter.mp hi).2
  have hOld := hMask.2 prime l u hl hlow K k hk hkBound
    TG m mp hNonzero W
  change (∑i∈TG,W i*(if k∣(mp i:ℤ)-(m i:ℤ) ∧
    Odd (((mp i:ℤ)-(m i:ℤ))/k) then (1:ℂ) else 0)) =
    ∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
      (∑i∈TG,W i*χ (mp i:ZMod (2*k.natAbs))*
        star (χ (m i:ZMod (2*k.natAbs)))) at hOld
  calc
    _ = ∑i∈TG,W i*(if k∣(mp i:ℤ)-(m i:ℤ) ∧
        Odd (((mp i:ℤ)-(m i:ℤ))/k) then (1:ℂ) else 0) := hLhs
    _ = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
      (∑i∈TG,W i*χ (mp i:ZMod (2*k.natAbs))*
        star (χ (m i:ZMod (2*k.natAbs)))) := hOld
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hRhs χ]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqProjectedFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- Original Parity(2.5)--(2.6) **INTEGER/ODD e projector at EVERY
physical real 3D Fourier frequency** for the COMPLETE ACTUAL
b629 fine-cofactor source, including all zero coefficients,
arbitrary complex B633 remainder amplitudes A_i and arbitrary
real log positions t_i:

  Σ_i (A_i α_m starα_m') 1_{k|(m'-m),odd e} e^{2πi<ξ,t_i>}
    = Σχ cχ Σ_i (A_i α_m starα_m') χ(m') starχ(m)
          e^{2πi<ξ,t_i>}.

The true signed integer e=(m'-m)/k gate is applied as a
FULL character projector before filtering real SOURCE eta_e/n
weights and before integrating/truncating any Fourier frequency.
This is the exact mathematical order required to avoid the FALSE
claim that each individual character kernel vanishes whenever
nonintegral e has nonzero eta_e(e/E). The proof is pure finite
original Parity2.6 Fourier orthogonality, not Parity(4.17) saving.
No extra |χ| cardinality factor, fake e-Pfree gate or assumed
cancellation on a complex subset. -/
theorem parity_eventually_original_full_unrestricted_actual_alpha_projected_3d_phase434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ {I : Type} [DecidableEq I] (T : Finset I)
        (m mp : I → ℕ) (A : I → ℂ)
        (t : I → EuclideanSpace ℝ (Fin 3))
        (ζ : EuclideanSpace ℝ (Fin 3)),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let W : I → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))
      (∑i∈T, W i*(if k∣(mp i:ℤ)-(m i:ℤ) ∧
        Odd (((mp i:ℤ)-(m i:ℤ))/k) then (1:ℂ) else 0)*
        parityOriginal3DPhysicalLogFourierPhase434 ζ (t i)) =
      ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∑i∈T, W i*χ (mp i:ZMod (2*k.natAbs))*
          star (χ (m i:ZMod (2*k.natAbs))) *
          parityOriginal3DPhysicalLogFourierPhase434 ζ (t i)) := by
  filter_upwards [parity_eventually_original_full_unrestricted_actual_alpha_odd_e_projector434
    S beta gamma Ck hS hbeta hgamma] with L hMask
  refine ⟨hMask.1,?_⟩
  intro prime l u hl hlow K k hk hkBound I instI T m mp A t ζ
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let W : I → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))
  let ph : I → ℂ := fun i => parityOriginal3DPhysicalLogFourierPhase434 ζ (t i)
  have hOld := hMask.2 prime l u hl hlow K k hk hkBound
    T m mp (fun i => A i*ph i)
  dsimp only at hOld
  calc
    _ = ∑i∈T,((A i*ph i)*alpha (m i)*star (alpha (mp i))) *
      (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
        then (1:ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
      (∑i∈T,((A i*ph i)*alpha (m i)*star (alpha (mp i))) *
        χ (mp i:ZMod (2*k.natAbs))*
        star (χ (m i:ZMod (2*k.natAbs)))) := hOld
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqProjectedBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Exact ordinary finite 3D Euclidean Fourier BALL integration
of arbitrary complex signed physical source W_i, with the fixed
native 2pi log phase, equals the finite sum of per-i ball phases.
This is a genuine integral/Fubini equality, independent of the
Dirichlet mask, not an extra source or analytic assumption. -/
theorem parity_original_historical_finite_fourier_ball_phase_coefficients434
    {I : Type*} (T : Finset I) (W : I → ℂ)
    (t : I → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (R : ℝ) :
    (∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 T W t f ζ) =
    ∑i∈T, W i *
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
        parityOriginal3DPhysicalLogFourierPhase434 ζ (t i) *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ) := by
  rw [parity_original_3d_physical_source_finite_fourier_ball_fubini434]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (fun ζ : EuclideanSpace ℝ (Fin 3) =>
      W i * parityOriginal3DPhysicalLogFourierPhase434 ζ (t i) *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ) =
      (fun ζ => W i * (parityOriginal3DPhysicalLogFourierPhase434 ζ (t i) *
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ)) by
        funext ζ
        ring]
  rw [integral_const_mul]

/-- ACTUAL ORIGINAL Parity(2.5)--(2.6) complete integer+ODD-e
cofactor projection COMMUTES with the GENUINE finite Euclidean
3D low-frequency Fourier BALL, including all zero original b629
fine-alpha coefficients. Original unitary complex norm and 2pi
Fourier phases are literal:

 integral_B Fhat * Σ_i A_i α_m conjα_mp [k|mp-m, e odd] phase_i
   = Σ_χ cχ integral_B Fhat *
       Σ_i A_i α_m conjα_mp χ(mp) conjχ(m) phase_i.

The character projector is NOT applied termwise to each χ;
fractional/incorrect-parity e ghost terms cancel only in the
COMPLETE χ sum before truncation. This is an EXACT equality of
actual integrals, not an assumed Parity4.17 saving, and it remains
valid for ANY Schwartz f, including the original cap-free B509
eta_eeta_n nonlinear source Schwartz. No source n-integrality or
unrestricted physical z support identification is claimed. -/
theorem parity_eventually_original_actual_alpha_odd_e_projected_fourier_ball434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ {I : Type} [DecidableEq I] (T : Finset I)
        (m mp : I → ℕ) (A : I → ℂ)
        (t : I → EuclideanSpace ℝ (Fin 3))
        (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) (R : ℝ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let W : I → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))
      let Wodd : I → ℂ := fun i => W i *
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧
          Odd (((mp i:ℤ)-(m i:ℤ))/k) then (1:ℂ) else 0)
      let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ :=
        fun χ i => W i*χ (mp i:ZMod (2*k.natAbs))*
          star (χ (m i:ZMod (2*k.natAbs)))
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 T Wodd t f ζ) =
      ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434 T (Wchi χ) t f ζ) := by
  filter_upwards [parity_eventually_original_full_unrestricted_actual_alpha_odd_e_projector434
    S beta gamma Ck hS hbeta hgamma] with L hProj
  refine ⟨hProj.1,?_⟩
  intro prime l u hl hlow K k hk hkBound I instI T m mp A t f R
  dsimp only
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let W : I → ℂ := fun i => A i*alpha (m i)*star (alpha (mp i))
  let Wodd : I → ℂ := fun i => W i *
    (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
      then (1:ℂ) else 0)
  let Wchi : DirichletCharacter ℂ (2*k.natAbs) → I → ℂ :=
    fun χ i => W i*χ (mp i:ZMod (2*k.natAbs))*
      star (χ (m i:ZMod (2*k.natAbs)))
  let B : I → ℂ := fun i =>
    ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
      parityOriginal3DPhysicalLogFourierPhase434 ζ (t i)*
        (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ
  have hMask := hProj.2 prime l u hl hlow K k hk hkBound
    T m mp (fun i => A i*B i)
  dsimp only at hMask
  have hLhs : (∑i∈T,Wodd i*B i) =
      ∑i∈T,((A i*B i)*alpha (m i)*star (alpha (mp i)))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
          then (1:ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [Wodd,W]
    ring
  have hRhs (χ : DirichletCharacter ℂ (2*k.natAbs)) :
      (∑i∈T,((A i*B i)*alpha (m i)*star (alpha (mp i)))*
        χ (mp i:ZMod (2*k.natAbs))*star (χ (m i:ZMod (2*k.natAbs)))) =
      ∑i∈T,Wchi χ i*B i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [Wchi,W]
    ring
  have hIntOdd := parity_original_historical_finite_fourier_ball_phase_coefficients434
    T Wodd t f R
  have hIntChi (χ : DirichletCharacter ℂ (2*k.natAbs)) :=
    parity_original_historical_finite_fourier_ball_phase_coefficients434
      T (Wchi χ) t f R
  change (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
    parityOriginal3DPhysicalFiniteTwistedSource434 T Wodd t f ζ) =
    ∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤R}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434 T (Wchi χ) t f ζ)
  calc
    _ = ∑i∈T,Wodd i*B i := hIntOdd
    _ = ∑i∈T,((A i*B i)*alpha (m i)*star (alpha (mp i)))*
        (if k∣(mp i:ℤ)-(m i:ℤ) ∧ Odd (((mp i:ℤ)-(m i:ℤ))/k)
          then (1:ℂ) else 0) := hLhs
    _ = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∑i∈T,((A i*B i)*alpha (m i)*star (alpha (mp i)))*
          χ (mp i:ZMod (2*k.natAbs))*
          star (χ (m i:ZMod (2*k.natAbs)))) := hMask
    _ = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∑i∈T,Wchi χ i*B i) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          rw [hRhs χ]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [hIntChi χ]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqReverseLogPullback -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1300000

/-- ORIGINAL Parity(4.14), RAW reverse arithmetic with NO historical
source finite u/Y or n/J mask. If positive cofactor endpoints
satisfy m*n=e*v+2 and z=m'*v with signed k given by
m'-m=e*k, BOTH genuine nonlinear logarithmic η_e and η_n
arguments at (log m/U, log m'/U, log z/Z) are literally e/E
and n/V, including the original h=-2 correction +2/(UV).
The reconstructed e,n are NATURAL and no extra prime-free-e gate
or invented numerical cutoffs enter. This is the exact bridge
needed before testing the SOURCE Schwartz kernel on B633 pairs. -/
theorem parity_original_historical_raw_reverse_log_cutoffs434
    (U E V Z : ℝ) (e m mp n v z : ℕ) (k : ℤ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z)
    (hk : k≠0)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hMN : m*n=e*v+2) (hZprod : z=mp*v) :
    let t := parityOriginalHistoricalRealLogTriple434 U Z m mp z
    parityOriginalHistoricalEtaELogArg434 U E k
      (EuclideanSpace.equiv (Fin 3) ℝ t)=(e:ℝ)/E ∧
    parityOriginalHistoricalEtaNLogArg434 U V Z k
      (EuclideanSpace.equiv (Fin 3) ℝ t)=(n:ℝ)/V := by
  dsimp only
  have hCoords : (EuclideanSpace.equiv (Fin 3) ℝ)
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z)=
      ![Real.log ((m:ℝ)/U),Real.log ((mp:ℝ)/U),Real.log ((z:ℝ)/Z)] := by
    unfold parityOriginalHistoricalRealLogTriple434
    exact (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply _
  have hEratio := parity_original_historical_log_dyadic_e_pullback434
    U E e m mp k hU hE hm hmp hk hDet
  dsimp only at hEratio
  have hMN0 : m*n=(e*v)+2 := hMN
  have hEz : e*z=mp*(e*v) := by
    rw [hZprod]
    ring
  have hNratio := parity_original_historical_log_dyadic_n_pullback434
    U V Z e m mp n (e*v) z k hU hV hZ hm hmp hz hk
    hMN0 hDet hEz
  dsimp only at hNratio
  constructor
  · rw [hCoords]
    simpa [parityOriginalHistoricalEtaELogArg434] using hEratio.symm
  · rw [hCoords]
    simpa [parityOriginalHistoricalEtaNLogArg434] using hNratio.symm
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqReverseEtaWeight -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- On a RAW recovered h=-2 original Parity(4.17) integer pair,
nonvanishing of the genuine smooth 3D Fourier source at the true
positive logarithmic triple IMPLIES that the ACTUAL original
Parity(4.10) source weight η_e(e/E)η_n(n/V) is nonzero. This does
not require finite SOURCE Y/J membership or selected Q/P e gate;
it follows from exact reconstructed source e,n log ratios and
literal matching of real/complex source η_eη_n definitions.
Crucially no claim is made for fractional or non-odd e: those
are handled by the complete Parity(2.6) χ projector, not by an
invalid termwise χ ghost support argument. -/
theorem parity_original_historical_reverse_real_log_nonzero_implies_actual_eta434
    (L : ℝ) (hL : 8≤L) (U E V Z : ℝ)
    (e m mp n v z : ℕ) (k : ℤ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z)
    (hk : k≠0)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hMN : m*n=e*v+2) (hZprod : z=mp*v)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (hNZ : parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z) ≠ 0) :
    parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0 := by
  let t := parityOriginalHistoricalRealLogTriple434 U Z m mp z
  have hArgs := parity_original_historical_raw_reverse_log_cutoffs434
    U E V Z e m mp n v z k hU hE hV hZ hm hmp hz hk hDet hMN hZprod
  dsimp only at hArgs
  have hEtaE : parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
      ((e:ℝ)/E) ≠ 0 := by
    intro hh
    apply hNZ
    apply parity_original_historical_actual_3d_source_zero_if_eta_e_zero434
      L hL U E V Z k buf a b hSmooth hSupport t
    rw [hArgs.1]
    exact hh
  have hEtaN : parityOriginalHistoricalActualEtaN434 ((n:ℝ)/V) ≠ 0 := by
    intro hh
    apply hNZ
    apply parity_original_historical_actual_3d_source_zero_if_eta_n_zero434
      L hL U E V Z k buf a b hSmooth hSupport t
    rw [hArgs.2]
    exact hh
  have hWeight :
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) =
        parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL ((e:ℝ)/E) *
        parityOriginalHistoricalActualEtaN434 ((n:ℝ)/V) := by
    simp [parityOriginalHistoricalDyadicEtaWeight434,
      parityOriginalHistoricalDyadicEtaEAtLComplex434,
      parityOriginalHistoricalActualEtaN434]
  intro hZero
  have hCast : ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ)=0 := by
    rw [hZero]
    rfl
  rw [hWeight] at hCast
  exact (mul_ne_zero hEtaE hEtaN) hCast
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSchwartzPhysicalIff -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1350000

/-- THE ACTUAL original Parity(4.14)--(4.17) SOURCE ghost-support
implication for an arithmetic pair AFTER the COMPLETE INTEGER/
ODD-e Parity(2.6) Dirichlet-character projector. Let the unrestricted
original signed B633 two-prime-slot term be NONZERO, with positive
shifted z,z+2k, literal odd integer e=(mp-m)/k, source-rough
cofactors m,mp and gcd(m,k)=1, and both ORIGINAL P-ordinary-part
divisor cores. Suppose also that the TRUE nonlinear 3D Schwartz
eta_eeta_n pullback is NONZERO at (log(m/U),log(mp/U),log(z/Z)).
Then reverse (4.13) arithmetic reconstructs a COMMON POSITIVE
integer n, the Schwartz nonzero forces the ACTUAL original
η_e(e/E)η_n(n/V) nonzero, both reserved B509 H0 slots come from
the original B633 coefficient, and the pair belongs to the exact
CORRECTED cap-free natural B509 physical k/Z source carrier with
Ybox=ceil(6UV), n in the true η_n full envelope.

Thus there are NO additional FULL-B633 smooth-weighted physical
pairs with integer odd e, original P-rough divisor conditions and
nonzero B633 coefficient/Schwartz weight. No Pfree-e artifact,
no false signed-subsum bound, no extra analytic Parity4.17 saving.
Fractional/incorrect parity e require the WHOLE χ projector and
cannot be treated as per-character zero Fourier ghosts. -/
theorem parity_original_historical_projected_B633_nonzero_schwartz_is_true_source434
    (d : ℕ) (L E U V rho xi1 xi2 xi3 Z : ℝ)
    (hL : 8≤L) (hE : 0<E) (hU : 0<U) (hV : 0<V) (hZ : 0<Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (k : ℤ) (chi : DirichletCharacter ℂ (2*k.natAbs))
    (signed : Bool) (e m mp z zp : ℕ)
    (he : Odd e) (hk : k≠0)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
    (hmDyad : (m:ℝ)≤2*U) (hmpDyad : (mp:ℝ)≤2*U)
    (hmpMem : mp∈K) (hNe : m≠mp)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hCop : m.Coprime k.natAbs)
    (hDivMp : mp∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
    (hDivM : m∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp)
    (hNonzero :
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).residual
        (2*k.natAbs) chi
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).hi
        m mp z zp ≠ 0)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (hF : parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z)≠0) :
    ∃n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 z) ∧
      parityOriginalHistoricalCanonicalZ434 e m mp n=z := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  obtain ⟨v,vp,n0,hv,hvp,hzEq,hzpEq,hmn,hmnp⟩ :=
    parity_original_historical_reverse_417_divisor_pair_to_source_n434
      P m mp e z zp k hm hmp hz hzp hDet hShift hCop hDivMp hDivM
  have hVquot : z/mp=v := by
    rw [hzEq]
    exact Nat.mul_div_cancel_left v hmp
  have hEta : ∀n : ℕ,
      m*n=e*(z/mp)+2 → mp*n=e*(zp/m)+2 →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n≠0 := by
    intro n hMN hMpN
    have hRaw : m*n=e*v+2 := by simpa [hVquot] using hMN
    exact parity_original_historical_reverse_real_log_nonzero_implies_actual_eta434
      L hL U E V Z e m mp n v z k hU hE hV hZ hm hmp hz hk
      hDet hRaw hzEq buf a b hSmooth hBufSupport hF
  exact parity_original_historical_lowfreq_nonzero_B633_smooth_pair_in_full_box434
    d L E U V rho xi1 xi2 xi3 hL hE hU hV band slot δ ξ K alpha
    k chi signed e m mp z zp he hm hmp hz hzp hmDyad hmpDyad
    hmpMem hNe hDet hShift hCop hDivMp hDivM hNonzero hEta
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqWeightedGhostTransfer -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1450000

/-- STRONGER source-accurate Parity(4.17) ghost criterion: the
FULL Fourier integral of ghost events is zero whenever each
complete COMPLEX signed coefficient W_i times the REAL original
3D Schwartz weight f(t_i) is zero. No incorrect requirement that
f(t_i) itself vanish for a B633 amplitude which is already zero.
This distinction is vital after original complete χ projection:
noninteger e ghosts have W_i=0 in the PROJECTED sum, while
integral e with outside eta windows have f(t_i)=0. -/
theorem parity_original_historical_weighted_3d_ghost_full_integral_zero434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ))
    (hWeightedZero : ∀i∈S,W i*f (t i)=0) :
    (∫ξ : EuclideanSpace ℝ (Fin 3),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ξ)=0 := by
  have hSignal : parityOriginal3DPhysicalFiniteSignal434 S W t f=0 := by
    unfold parityOriginal3DPhysicalFiniteSignal434
    exact Finset.sum_eq_zero (fun i hi => hWeightedZero i hi)
  have hFubini := parity_original_3d_physical_finite_source_fourier_fubini434 S W t f
  rw [hSignal] at hFubini
  exact hFubini.symm

/-- EXACT weighted-source ghost high-frequency bound: even if
f(t_i) is nonzero on off-physical original B633 pairs that are
already killed by a zero prime-slot coefficient or complete odd-e
character projector, their finite FULL Fourier integral is zero
provided W_i*f(t_i)=0. The LOW-frequency BALL ghost integral
is bounded by the TRUE positive mass Σ‖W_i‖ times the ACTUAL
source Schwartz H-moment/T^H. All arithmetic and complex
conjugations are left untouched. No spectral Parity4.17 saving. -/
theorem parity_original_historical_weighted_3d_ghost_ball_le_moment434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ)
    (t : ι → EuclideanSpace ℝ (Fin 3))
    (H : ℕ) (L : ℝ) (hL : 8≤L)
    (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (T : ℝ) (hT : 0<T)
    (hWeightedZero : ∀i∈S,W i *
      parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hBufSmooth hBufSupport (t i)=0) :
    ‖∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ‖ ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport)/T^H) := by
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  have hSignal : parityOriginal3DPhysicalFiniteSignal434 S W t f=0 := by
    unfold parityOriginal3DPhysicalFiniteSignal434
    exact Finset.sum_eq_zero (fun i hi => hWeightedZero i hi)
  have hTrunc := parity_original_historical_actual_dyadic_finite_3d_truncation434
    S W t H L hL U E V Z k buf a b hBufSmooth hBufSupport T hT
  change ‖parityOriginal3DPhysicalFiniteSignal434 S W t f-
    (∫ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ξ)‖ ≤ _ at hTrunc
  rw [hSignal,zero_sub,norm_neg] at hTrunc
  exact hTrunc

/-- Full ORIGINAL Parity(4.17) source-support signed correlation
transfer with the CORRECT weighted ghost-zero condition, not
the stronger and potentially false per-term f=0 assumption:

 ‖BALL_physically_supported‖ ≤ ‖BALL_unrestricted‖
      + (Σ_ghost ‖W_i‖) M_H(source)/T^H.

The P-filter may encode the REAL B509 carrier, original η_n n
integer, odd e=(m'-m)/k and exact z support. Ghost terms with
W_i=0 are harmless; SOURCE η_eη_n zeros are also harmless.
The actual per-index hGhostWeightedZero contract is left explicit
and is only to be discharged by genuine arithmetic and the WHOLE
χ projector, not by fictitious norm monotonicity of complex sums.
This is the precise safe analytic adapter for the next Parity4.17
signed majorization step. -/
theorem parity_original_historical_weighted_3d_source_ball_le_full_plus_ghost434
    {ι : Type*} (S : Finset ι) (P : ι → Prop)
    (W : ι → ℂ) (t : ι → EuclideanSpace ℝ (Fin 3))
    (H : ℕ) (L : ℝ) (hL : 8≤L)
    (U E V Z : ℝ) (k : ℤ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (T : ℝ) (hT : 0<T)
    (hGhostWeightedZero : ∀i∈S, ¬P i → W i *
      parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V Z k buf a b hBufSmooth hBufSupport (t i)=0) :
    ‖∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434
        (S.filter P) W t
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ‖ ≤
    ‖∫ ξ in ({ξ : EuclideanSpace ℝ (Fin 3) | ‖ξ‖≤T}:Set _),
      parityOriginal3DPhysicalFiniteTwistedSource434 S W t
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport) ξ‖ +
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (S.filter (fun i => ¬P i)) W *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V Z k buf a b hBufSmooth hBufSupport)/T^H) := by
  classical
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
  let B : Set (EuclideanSpace ℝ (Fin 3)) := {ξ | ‖ξ‖≤T}
  let SG := S.filter P
  let SB := S.filter (fun i => ¬P i)
  let I (R : Finset ι) : ℂ :=
    ∫ξ in B, parityOriginal3DPhysicalFiniteTwistedSource434 R W t f ξ
  have hSplit : I S = I SG + I SB := by
    dsimp [I]
    rw [parity_original_3d_physical_source_finite_fourier_ball_fubini434 S W t f T,
      parity_original_3d_physical_source_finite_fourier_ball_fubini434 SG W t f T,
      parity_original_3d_physical_source_finite_fourier_ball_fubini434 SB W t f T]
    exact (Finset.sum_filter_add_sum_filter_not S P (fun i =>
      ∫ξ in B,
        W i*parityOriginal3DPhysicalLogFourierPhase434 ξ (t i)*
          (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ξ)).symm
  have hZero : ∀i∈SB,W i*f (t i)=0 := by
    intro i hi
    have hh := Finset.mem_filter.mp hi
    exact hGhostWeightedZero i hh.1 hh.2
  have hGhost := parity_original_historical_weighted_3d_ghost_ball_le_moment434
    SB W t H L hL U E V Z k buf a b hBufSmooth hBufSupport T hT hZero
  have hEq : I SG = I S-I SB := by
    rw [hSplit]
    ring
  change ‖I SG‖≤‖I S‖+
    parityOriginal3DPhysicalFiniteCoefficientMass434 SB W *
      (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H)
  rw [hEq]
  have hGhostBound : ‖I SB‖ ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434 SB W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := hGhost
  exact (norm_sub_le (I S) (I SB)).trans (by linarith [hGhostBound])
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqConcreteGhostZero -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- Strong actual SOURCE arithmetic ghost contract AFTER the WHOLE
original Parity(2.6) integer-odd e projection: if a FULL B633 two-core
term is nonzero and the reconstructed pair fails the genuine
capfree B509 eta_n-supported physical k/Z source, the original
3D Schwartz eta_e*eta_n pullback is EXACTLY zero on that pair.
No per-character assertion for nonintegral or negative e. -/
theorem parity_original_historical_projected_B633_ghost_schwartz_zero434
    (d : ℕ) (L E U V rho xi1 xi2 xi3 Z : ℝ)
    (hL : 8≤L) (hE : 0<E) (hU : 0<U) (hV : 0<V) (hZ : 0<Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (k : ℤ) (chi : DirichletCharacter ℂ (2*k.natAbs))
    (signed : Bool) (e m mp z zp : ℕ)
    (he : Odd e) (hk : k≠0)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
    (hmDyad : (m:ℝ)≤2*U) (hmpDyad : (mp:ℝ)≤2*U)
    (hmpMem : mp∈K) (hNe : m≠mp)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hCop : m.Coprime k.natAbs)
    (hDivMp : mp∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
    (hDivM : m∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp)
    (hNonzero :
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).residual
        (2*k.natAbs) chi
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).hi
        m mp z zp ≠ 0)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)

    (hGhost : ¬(∃n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 z) ∧
      parityOriginalHistoricalCanonicalZ434 e m mp n=z)) :
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z)=0 := by
  by_contra hF
  have hActual := parity_original_historical_projected_B633_nonzero_schwartz_is_true_source434
      d L E U V rho xi1 xi2 xi3 Z hL hE hU hV hZ band slot δ ξ K alpha
      k chi signed e m mp z zp he hk hm hmp hz hzp hmDyad hmpDyad
      hmpMem hNe hDet hShift hCop hDivMp hDivM hNonzero
      buf a b hSmooth hBufSupport hF
  exact hGhost hActual

/-- The mathematically appropriate fully WEIGHTED original Parity4.17
source ghost certificate: for every integer-odd projected pair
satisfying real P-ordinary divisor gates, rough cofactor coprimality,
positive z,z+2k, and the fixed true m,m' dyadic bounds, exclusion
from the actual B509 physical n/u source implies the LITERAL
unrestricted B633 pair amplitude TIMES the SOURCE Schwartz eta
weight is zero. This also handles pairs whose B633 coefficient
itself vanishes. Therefore its full Fourier integral can be
added before truncation with no signed-subsum positivity assumption;
the truncated ghost is controlled by the newly proved weighted
Schwartz moment /T^H theorem. Arithmetic hypotheses must still
be verified for the entire projected Parity4.17 index carrier. -/
theorem parity_original_historical_projected_B633_ghost_weighted_zero434
    (d : ℕ) (L E U V rho xi1 xi2 xi3 Z : ℝ)
    (hL : 8≤L) (hE : 0<E) (hU : 0<U) (hV : 0<V) (hZ : 0<Z)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (k : ℤ) (chi : DirichletCharacter ℂ (2*k.natAbs))
    (signed : Bool) (e m mp z zp : ℕ)
    (he : Odd e) (hk : k≠0)
    (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
    (hmDyad : (m:ℝ)≤2*U) (hmpDyad : (mp:ℝ)≤2*U)
    (hmpMem : mp∈K) (hNe : m≠mp)
    (hDet : (mp:ℤ)-(m:ℤ)=(e:ℤ)*k)
    (hShift : (z:ℤ)+2*k=(zp:ℤ))
    (hCop : m.Coprime k.natAbs)
    (hDivMp : mp∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
    (hDivM : m∣sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)

    (hGhost : ¬(∃n : ℕ,
      n∈parityOriginalHistoricalFullNEnvelope434 V ∧
      (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ (Nat.ceil (6*U*V)) e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k
        (parityOriginalHistoricalActualZDyadicScale434 z) ∧
      parityOriginalHistoricalCanonicalZ434 e m mp n=z)) :
    (parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).residual
        (2*k.natAbs) chi
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).hi
        m mp z zp) *
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z) = 0 := by
  by_cases hB : parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).residual
        (2*k.natAbs) chi
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).lo
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha
          (2*k.natAbs) chi 0 0).hi
        m mp z zp=0
  · rw [hB]
    simp only [zero_mul]
  · have hf := parity_original_historical_projected_B633_ghost_schwartz_zero434
      d L E U V rho xi1 xi2 xi3 Z hL hE hU hV hZ band slot δ ξ K alpha
      k chi signed e m mp z zp he hk hm hmp hz hzp hmDyad hmpDyad
      hmpMem hNe hDet hShift hCop hDivMp hDivM hB
      buf a b hSmooth hBufSupport hGhost
    rw [hf]
    simp only [mul_zero]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqActualAlphaCoprime -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1300000

/-- For ORIGINAL true Parity b629 fine α (including parity, repeated
prime multiplicities and source long-prime roughness), EVERY
nonzero source cofactor m in the actual K support is coprime to
the genuine integer signed k for |k|≤L^Ck. This discharges the
previously explicit extra Euclidean gcd(m,k)=1 gate required to
reverse the ORIGINAL literal Parity(4.17) two-core divisor pair
into a UNIQUE common source integer n. It follows from the
native original fine-rough unit modulo **2|k|**, not an assumed
coprimality or a modified/coarsened fine coefficient. -/
theorem parity_eventually_original_full_417_actual_fine_alpha_coprime_k434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (m : ℕ),
      restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) m≠0 →
      m.Coprime k.natAbs := by
  filter_upwards [parity_eventually_actual_fine_alpha_shift_unit434
    S beta gamma Ck hS hbeta hgamma] with L hUnit
  refine ⟨hUnit.1,?_⟩
  intro prime l u hl hlow K k hk hkBound m hα
  have hU : IsUnit (m : ZMod (2*k.natAbs)) :=
    hUnit.2 prime l u hl hlow K k hk hkBound m hα
  have hCop2 : m.Coprime (2*k.natAbs) :=
    (ZMod.isUnit_iff_coprime m (2*k.natAbs)).mp hU
  have hDiv : k.natAbs ∣ 2*k.natAbs := ⟨2,by omega⟩
  exact Nat.Coprime.of_dvd (dvd_refl m) hDiv hCop2

/-- Both original b629 fine cofactor rows m,m' are coprime to
signed k whenever their actual α values are nonzero. This holds
for all native source original r20 cofactor labels and arbitrary
finset K, not merely for synthetic Boolean roughness flags. -/
theorem parity_eventually_original_full_417_actual_two_fine_alpha_coprime_k434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (m mp : ℕ),
      restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) m≠0 →
      restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u) mp≠0 →
      m.Coprime k.natAbs ∧ mp.Coprime k.natAbs := by
  filter_upwards [parity_eventually_original_full_417_actual_fine_alpha_coprime_k434
    S beta gamma Ck hS hbeta hgamma] with L hAlpha
  refine ⟨hAlpha.1,?_⟩
  intro prime l u hl hlow K k hk hkBound m mp hm hmp
  exact ⟨hAlpha.2 prime l u hl hlow K k hk hkBound m hm,
    hAlpha.2 prime l u hl hlow K k hk hkBound mp hmp⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqSignedEPos -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- ORIGINAL Parity(4.14) first nonlinear e-cutoff log argument
for ANY SIGNED INTEGER e, including e<0, satisfying the
literal Parity(2.6) projected divisor identity mp-m=e*k:

   (U/(k E)) (exp(log(mp/U))-exp(log(m/U))) = e/E.

No condition that e is natural or positive enters this exact
real-arithmetic identity. It is the correct prerequisite for
showing that fractional/negative e ghosts are suppressed only
AFTER the full character projector and positive smooth SOURCE
eta_e, without falsely declaring per-χ terms to be zero. -/
theorem parity_original_historical_signed_integer_e_log_argument434
    (U E Z : ℝ) (m mp z : ℕ) (k e : ℤ)
    (hU : 0<U) (hE : 0<E)
    (hm : 0 < m) (hmp : 0 < mp) (hk : k≠0)
    (hDet : (mp:ℤ)-(m:ℤ)=e*k) :
    parityOriginalHistoricalEtaELogArg434 U E k
      (EuclideanSpace.equiv (Fin 3) ℝ
        (parityOriginalHistoricalRealLogTriple434 U Z m mp z))=(e:ℝ)/E := by
  have hCoords : (EuclideanSpace.equiv (Fin 3) ℝ)
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z)=
      ![Real.log ((m:ℝ)/U),Real.log ((mp:ℝ)/U),Real.log ((z:ℝ)/Z)] := by
    unfold parityOriginalHistoricalRealLogTriple434
    exact (EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply _
  have hmR : (0:ℝ)<(m:ℝ) := Nat.cast_pos.mpr hm
  have hmpR : (0:ℝ)<(mp:ℝ) := Nat.cast_pos.mpr hmp
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk
  have hDetR : (mp:ℝ)-(m:ℝ)=(e:ℝ)*(k:ℝ) := by exact_mod_cast hDet
  rw [hCoords]
  change (U/((k:ℝ)*E)) *
    (Real.exp (Real.log ((mp:ℝ)/U)) -
      Real.exp (Real.log ((m:ℝ)/U))) = (e:ℝ)/E
  rw [Real.exp_log (div_pos hmpR hU), Real.exp_log (div_pos hmR hU)]
  field_simp
  nlinarith [hDetR]

/-- A nonzero actual SOURCE Schwartz η_e eta_n at an unrestricted
B633 candidate whose COMPLETE χ projection has established
mp-m=e*k for a SIGNED integer e FORCES e>0. Thus signed odd
negative e cannot contribute to the projected Fourier SOURCE
integral: the actual moving original eta_e has strictly positive
support. This is a native SOURCE fact, not a per-character
orthogonality claim or an assumed positivity cutoff. -/
theorem parity_original_historical_projected_schwartz_nonzero_forces_signed_e_pos434
    (L : ℝ) (hL : 8≤L) (U E V Z : ℝ)
    (m mp z : ℕ) (k e : ℤ)
    (hU : 0<U) (hE : 0<E)
    (hm : 0 < m) (hmp : 0 < mp) (hk : k≠0)
    (hDet : (mp:ℤ)-(m:ℤ)=e*k)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (hF : parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hBufSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z)≠0) :
    0<e := by
  have hArg := parity_original_historical_signed_integer_e_log_argument434
    U E Z m mp z k e hU hE hm hmp hk hDet
  have hSupport := parity_original_historical_actual_3d_source_nonzero_real_windows434
    L hL U E V Z k buf a b hBufSmooth hBufSupport
    (parityOriginalHistoricalRealLogTriple434 U Z m mp z) hF
  dsimp only at hSupport
  have hERatio : (0:ℝ)<(e:ℝ)/E := by
    rw [←hArg]
    exact lt_trans (by positivity : (0:ℝ)<L^(-88:ℝ)/2) hSupport.1
  have hMul : (0:ℝ)<((e:ℝ)/E)*E := mul_pos hERatio hE
  have hEq : ((e:ℝ)/E)*E=(e:ℝ) := div_mul_cancel₀ _ (ne_of_gt hE)
  have heReal : (0:ℝ)<(e:ℝ) := by rwa [hEq] at hMul
  exact_mod_cast heReal

/-- An unrestricted Parity(4.17) projected odd integer e that survives
true SOURCE η_e eta_n smoothing must equal the cast of a POSITIVE
natural e. This is the exact bridge from the signed Dirichlet
projector's integer quotient to natural e for the native reverse
B509 source theorem, without discarding the e<0 terms via an
unjustified complex signed-subset inequality. -/
theorem parity_original_historical_projected_signed_e_pos_nat434
    (L : ℝ) (hL : 8≤L) (U E V Z : ℝ)
    (m mp z : ℕ) (k e : ℤ)
    (hU : 0<U) (hE : 0<E)
    (hm : 0 < m) (hmp : 0 < mp) (hk : k≠0)
    (hDet : (mp:ℤ)-(m:ℤ)=e*k)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (hF : parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hBufSmooth hBufSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z)≠0) :
    ∃en : ℕ, 0<en ∧ (mp:ℤ)-(m:ℤ)=(en:ℤ)*k := by
  have hePos := parity_original_historical_projected_schwartz_nonzero_forces_signed_e_pos434
    L hL U E V Z m mp z k e hU hE hm hmp hk hDet
    buf a b hBufSmooth hBufSupport hF
  refine ⟨e.toNat,by omega,?_⟩
  have hh : (e.toNat:ℤ)=e := by omega
  rw [hh]
  exact hDet
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqB633AlphaCoprime -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1300000

/-- Exact original unrestricted Parity(4.16) ONE literal B633
cofactor pair is nonzero ONLY if BOTH genuine cofactor alpha_m
and alpha_m' factors are nonzero. They occur as first factors in
the actual full complex coefficient, before χ, Fourier phases,
H0 prime rests, signs and W1 weights. This is not an artificial
sharp support mask and holds even when k is negative. -/
theorem parity_original_historical_literal_B633_nonzero_forces_both_alpha434
    (L rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q)
    (lo hi m mp z zp : ℕ)
    (hNZ : parityOriginalHistoricalB633PhysicalPairTerm434
      L rho xi1 xi2 xi3 signed alpha residual q chi lo hi
      m mp z zp≠0) :
    alpha m≠0 ∧ alpha mp≠0 := by
  constructor
  · intro hm
    apply hNZ
    simp [parityOriginalHistoricalB633PhysicalPairTerm434,hm]
  · intro hmp
    apply hNZ
    simp [parityOriginalHistoricalB633PhysicalPairTerm434,hmp]

/-- The actual original r20 b629 finite fine alpha automatically
makes EVERY NONZERO literal full B633 two-core summand coprime to
its signed small shift k, for |k|≤L^Ck. This discharges the
only extra Euclidean gcd(m,k) hypothesis of the native reverse
(4.17) divisor-pair-to-common-integer-n theorem, with no added
source roughness assumption or hidden restriction of complex
unrestricted terms. All zero B633 summands are harmless already. -/
theorem parity_eventually_original_literal_B633_nonzero_implies_coprime_k434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (chi : DirichletCharacter ℂ (2*k.natAbs))
        (rho xi1 xi2 xi3 : ℝ) (signed : Bool)
        (m mp z zp : ℕ),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) chi 0 0
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha F.residual
        (2*k.natAbs) chi F.lo F.hi m mp z zp≠0 →
      m.Coprime k.natAbs ∧ mp.Coprime k.natAbs ∧ m∈K ∧ mp∈K := by
  filter_upwards [parity_eventually_original_full_417_actual_two_fine_alpha_coprime_k434
    S beta gamma Ck hS hbeta hgamma] with L hFine
  refine ⟨hFine.1,?_⟩
  intro prime l u hl hlow K k hk hkBound d band slot δ ξ chi
    rho xi1 xi2 xi3 signed m mp z zp
  dsimp only
  intro hPair
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) chi 0 0
  have hAlpha := parity_original_historical_literal_B633_nonzero_forces_both_alpha434
    L rho xi1 xi2 xi3 signed alpha F.residual
    (2*k.natAbs) chi F.lo F.hi m mp z zp hPair
  have hCoprime := hFine.2 prime l u hl hlow K k hk hkBound m mp
    hAlpha.1 hAlpha.2
  have hKm : m∈K := by
    by_contra hh
    exact hAlpha.1 (by simp [alpha,restrictSequence,hh])
  have hKmp : mp∈K := by
    by_contra hh
    exact hAlpha.2 (by simp [alpha,restrictSequence,hh])
  exact ⟨hCoprime.1,hCoprime.2,hKm,hKmp⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqProjectedActualGhost -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1700000

/-- TRUE ORIGINAL UNRESTRICTED Parity(4.17) projected pair arithmetic
without EXTERNAL assumptions that e is natural/positive, that
m is coprime to signed small k, or that m' belongs to actual
source K: those facts follow from the COMPLETE odd-integer-e χ
projector, the SOURCE eta_e positive support, and nonzero
original b629 fine alpha inside the LITERAL B633 complex pair.

For fixed original L large, every pair with:
* k != 0 and |k| <= L^Ck;
* eInt odd and mp-m=eInt*k (after χ projection);
* positive z, zp=z+2k and the genuine ordinary-P divisor cores;
* both cofactors in original dyadic [U,2U) WHEN their fine alpha
  is nonzero;
* actual unrestricted original B633 single pair != 0;
* actual original nonlinear C∞ eta_e*eta_n 3D Schwartz source
  != 0 at the true log(m/U),log(mp/U),log(z/Z)
produces a POSITIVE NATURAL odd e and a UNIQUE actual physical
shared integer n in the corrected cap-free B509 carrier with
Ybox=ceil(6UV). No synthetic sharp gate or spectral estimate.
This is the precise per-pair arithmetic contract needed to make
all projected off-source B633 ghost contributions vanish after
coefficient/source multiplication, *before* Fourier truncation. -/
theorem parity_eventually_original_projected_actual_B633_schwartz_pair_in_source434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (chi : DirichletCharacter ℂ (2*k.natAbs))
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool)
        (m mp z zp : ℕ) (eInt : ℤ)
        (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
        (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
        (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U)
        (hNe : m≠mp)
        (hDet : (mp:ℤ)-(m:ℤ)=eInt*k)
        (hOdd : Odd eInt)
        (hShift : (z:ℤ)+2*k=(zp:ℤ))
        (hDivMp : mp∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
        (hDivM : m∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp)
        (buf : ℝ → ℂ) (a b : ℝ)
        (hBufSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) chi 0 0
      parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha F.residual
        (2*k.natAbs) chi F.lo F.hi m mp z zp≠0 →
      parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hBufSmooth hBufSupport
        (parityOriginalHistoricalRealLogTriple434 U Z m mp z)≠0 →
      ∃ en : ℕ, Odd en ∧ 0<en ∧
        ∃ n : ℕ,
          n∈parityOriginalHistoricalFullNEnvelope434 V ∧
          (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
            d L band slot δ (Nat.ceil (6*U*V)) en m K
            (parityOriginalHistoricalFullNEnvelope434 V) k
            (parityOriginalHistoricalActualZDyadicScale434 z) ∧
          parityOriginalHistoricalCanonicalZ434 en m mp n=z := by
  filter_upwards [parity_eventually_original_literal_B633_nonzero_implies_coprime_k434
      S beta gamma Ck hS hbeta hgamma,
    eventually_ge_atTop (8:ℝ)] with L hAlpha hL
  refine ⟨hL,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ chi
    rho xi1 xi2 xi3 U E V Z signed m mp z zp eInt
    hU hE hV hZ hm hmp hz hzp hDyad hNe hDet hOdd hShift
    hDivMp hDivM buf a b hBufSmooth hBufSupport
  dsimp only
  intro hB hF
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma l u)
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) chi 0 0
  obtain ⟨hCop,hCopMp,hKm,hKmp⟩ := hAlpha.2 prime l u hl hlow
    K k hk hkBound d band slot δ ξ chi rho xi1 xi2 xi3 signed
    m mp z zp hB
  obtain ⟨en,henPos,hDetNat⟩ :=
    parity_original_historical_projected_signed_e_pos_nat434
      L hLw U E V Z m mp z k eInt hU hE hm hmp hk hDet
      buf a b hBufSmooth hBufSupport hF
  have hCastProd : (en:ℤ)*k=eInt*k := hDetNat.symm.trans hDet
  have hCast : (en:ℤ)=eInt := by
    have hh : ((en:ℤ)-eInt)*k=0 := by
      linear_combination hCastProd
    have heq : (en:ℤ)-eInt=0 :=
      (mul_eq_zero.mp hh).resolve_right hk
    exact sub_eq_zero.mp heq
  have hEnOdd : Odd en := by
    exact_mod_cast (by simpa only [hCast] using hOdd : Odd (en:ℤ))
  obtain ⟨n,hn,hEvent,hZCan⟩ :=
    parity_original_historical_projected_B633_nonzero_schwartz_is_true_source434
      d L E U V rho xi1 xi2 xi3 Z hLw hE hU hV hZ
      band slot δ ξ K alpha k chi signed en m mp z zp
      hEnOdd hk hm hmp hz hzp (hDyad m hKm).2 (hDyad mp hKmp).2
      hKmp hNe hDetNat hShift hCop hDivMp hDivM hB
      buf a b hBufSmooth hBufSupport hF
  exact ⟨en,hEnOdd,henPos,n,hn,hEvent,hZCan⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqProjectedActualGhostZero -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Original unrestricted Parity(4.17) fully PROJECTED signed ghost
coefficient is pointwise zero AFTER multiplication by the ACTUAL
Parity(4.14) nonlinear 3D Schwartz source weight, whenever no true
capfree B509 physical (e,n,m,mp,z) event exists. The exact original
b629 fine-alpha, complete odd-integer e χ projector, original
P-ordinary cofactor divisors and z+2k shift are retained;
nonintegral and negative e ghosts cancel by the full χ projector
or by positive eta_e support, while full literal B633 terms already
zero cause no false Fourier support hypothesis.

This theorem is a concrete native discharge of the WEIGHTED ghost
zero condition for the arithmetic/projector-correct B633 index
carrier, not an unsupported assertion for each individual χ term.
It still requires a full finite double-cofactor/source index
bijection and legal χ/Fourier sum exchange before original full
Parity(4.17) lowfreq saving closes Type II. -/
theorem parity_eventually_original_projected_actual_B633_weighted_ghost_zero434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (chi : DirichletCharacter ℂ (2*k.natAbs))
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool)
        (m mp z zp : ℕ) (eInt : ℤ)
        (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
        (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z) (hzp : 0 < zp)
        (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U)
        (hNe : m≠mp)
        (hDet : (mp:ℤ)-(m:ℤ)=eInt*k)
        (hOdd : Odd eInt)
        (hShift : (z:ℤ)+2*k=(zp:ℤ))
        (hDivMp : mp∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z)
        (hDivM : m∣sourceOriginalOrdinaryPart
          (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp)
        (buf : ℝ → ℂ) (a b : ℝ)
        (hBufSmooth : ContDiff ℝ ∞ buf)
        (hBufSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b),
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) chi 0 0
      (hGhost : ¬(∃ en : ℕ, Odd en ∧ 0<en ∧
        ∃ n : ℕ,
          n∈parityOriginalHistoricalFullNEnvelope434 V ∧
          (mp,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
            d L band slot δ (Nat.ceil (6*U*V)) en m K
            (parityOriginalHistoricalFullNEnvelope434 V) k
            (parityOriginalHistoricalActualZDyadicScale434 z) ∧
          parityOriginalHistoricalCanonicalZ434 en m mp n=z)) →
      (parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha F.residual
        (2*k.natAbs) chi F.lo F.hi m mp z zp) *
      parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hBufSmooth hBufSupport
        (parityOriginalHistoricalRealLogTriple434 U Z m mp z)=0 := by
  filter_upwards [parity_eventually_original_projected_actual_B633_schwartz_pair_in_source434
    S beta gamma Ck hS hbeta hgamma] with L hReal
  refine ⟨hReal.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ chi
    rho xi1 xi2 xi3 U E V Z signed m mp z zp eInt
    hU hE hV hZ hm hmp hz hzp hDyad hNe hDet hOdd hShift
    hDivMp hDivM buf a b hBufSmooth hBufSupport
  dsimp only
  intro hGhost
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) chi 0 0
  let B : ℂ := parityOriginalHistoricalB633PhysicalPairTerm434
        L rho xi1 xi2 xi3 signed alpha F.residual
        (2*k.natAbs) chi F.lo F.hi m mp z zp
  let f : ℂ := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hBufSmooth hBufSupport
        (parityOriginalHistoricalRealLogTriple434 U Z m mp z)
  change B*f=0
  by_cases hB : B=0
  · rw [hB]
    simp only [zero_mul]
  by_cases hf : f=0
  · rw [hf]
    simp only [mul_zero]
  have hActual := hReal.2 hLw prime l u hl hlow K k hk hkBound
    d band slot δ ξ chi rho xi1 xi2 xi3 U E V Z signed
    m mp z zp eInt hU hE hV hZ hm hmp hz hzp hDyad hNe
    hDet hOdd hShift hDivMp hDivM buf a b hBufSmooth hBufSupport
    hB hf
  exact (hGhost hActual).elim
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalLowfreqProjectedLegalFamilyGhostBall -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- The ACTUAL post-Parity(2.6) projected original B633 divisor/cofactor
index laws. These are arithmetic conditions, never a sharp eta_e,
eta_n or u source gate. Importantly signed e may be negative here;
positivity will follow from the genuine nonlinear source support. -/
def parityOriginalHistoricalProjectedLegalPair434
    (L : ℝ) (K : Finset ℕ) (k : ℤ)
    (m mp z zp : ℕ) (eInt : ℤ) : Prop :=
  (0 < m) ∧ (0 < mp) ∧ (0 < z) ∧ (0 < zp) ∧
  (m ∈ K) ∧ (mp ∈ K) ∧ (m ≠ mp) ∧
  ((mp:ℤ)-(m:ℤ)=eInt*k) ∧ Odd eInt ∧
  ((z:ℤ)+2*k=(zp:ℤ)) ∧
  mp∣sourceOriginalOrdinaryPart
    (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) z ∧
  m∣sourceOriginalOrdinaryPart
    (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) zp

/-- ACTUAL original r0=20, h=-2 low-frequency signed B633
fixed-character BALL transfer on the full finite legal cofactor
family, AFTER the complete odd-integer e character projector.

The atom W is the LITERAL B633 first/second reserved-Q core,
with original fine alpha, χ, H0 residual, W1, epsilon and phases;
t is the exact true 3D logarithmic triple. The physical mask is
an EXISTENCE of the genuine cap-free Ybox=ceil(6UV) B509
source e,n,m,m',z event, rather than an artificial hard gate.

No arbitrary ghost vanishing hypothesis: nonphysical legal terms
have W_i*f(t_i)=0 from the ACTUAL original Schwartz eta_e/eta_n,
reverse determinant, alpha coprimality, and B509 source lemmas.
The truncated ghost is paid by its positive B633 coefficient mass
and the exact SOURCE Schwartz moment/T^H. This is an inequality for
the projected legal finite family, NOT an identification with the
entire original χ-outer or an unconditional full Parity(4.17) saving. -/
theorem parity_eventually_original_projected_legal_B633_ball_le_full_plus_ghost434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 8≤L ∧
      ∀ (hLw : 8≤L) (prime : Bool) (l u : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ)
        (chi : DirichletCharacter ℂ (2*k.natAbs))
        (rho xi1 xi2 xi3 U E V Z : ℝ) (signed : Bool),
      0<U → 0<E → 0<V → 0<Z →
      (∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
      ∀ {ι : Type} [DecidableEq ι] (s : Finset ι)
        (m mp z zp : ι → ℕ) (eInt : ι → ℤ)
        (buf : ℝ → ℂ) (a b : ℝ),
      (hSmooth : ContDiff ℝ ∞ buf) →
      (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b) →
      ∀ (H : ℕ) (T : ℝ), 0<T →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l u)
      let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
        (2*k.natAbs) chi 0 0
      let valid : ι → Prop := fun i =>
        parityOriginalHistoricalProjectedLegalPair434 L K k
          (m i) (mp i) (z i) (zp i) (eInt i)
      let sValid := s.filter valid
      let physical : ι → Prop := fun i =>
        ∃ en : ℕ, Odd en ∧ 0<en ∧
          ∃ n : ℕ,
            n∈parityOriginalHistoricalFullNEnvelope434 V ∧
            (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
              (parityOriginalHistoricalFullNEnvelope434 V) k
              (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
            parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
      let W : ι → ℂ := fun i =>
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho xi1 xi2 xi3 signed alpha F.residual
          (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
      let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
        parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
      let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hLw U E V Z k buf a b hSmooth hSupport
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            (sValid.filter physical) W t f ζ‖ ≤
      ‖∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
          parityOriginal3DPhysicalFiniteTwistedSource434
            sValid W t f ζ‖ +
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (sValid.filter (fun i => ¬physical i)) W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  filter_upwards [parity_eventually_original_projected_actual_B633_weighted_ghost_zero434
    S beta gamma Ck hS hbeta hgamma] with L hGhostL
  refine ⟨hGhostL.1,?_⟩
  intro hLw prime l u hl hlow K k hk hkBound d band slot δ ξ chi
    rho xi1 xi2 xi3 U E V Z signed hU hE hV hZ hDyad
    ι decι s m mp z zp eInt buf a b hSmooth hSupport H T hT
  dsimp only
  classical
  let alpha := restrictSequence K (b629ActualFineAlpha434 prime L S gamma l u)
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha
    (2*k.natAbs) chi 0 0
  let valid : ι → Prop := fun i => parityOriginalHistoricalProjectedLegalPair434
    L K k (m i) (mp i) (z i) (zp i) (eInt i)
  let sValid : Finset ι := s.filter valid
  let physical : ι → Prop := fun i =>
    ∃ en : ℕ, Odd en ∧ 0<en ∧
      ∃ n : ℕ,
        n∈parityOriginalHistoricalFullNEnvelope434 V ∧
        (mp i,n)∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          d L band slot δ (Nat.ceil (6*U*V)) en (m i) K
          (parityOriginalHistoricalFullNEnvelope434 V) k
          (parityOriginalHistoricalActualZDyadicScale434 (z i)) ∧
        parityOriginalHistoricalCanonicalZ434 en (m i) (mp i) n=z i
  let W : ι → ℂ := fun i => parityOriginalHistoricalB633PhysicalPairTerm434
    L rho xi1 xi2 xi3 signed alpha F.residual
    (2*k.natAbs) chi F.lo F.hi (m i) (mp i) (z i) (zp i)
  let t : ι → EuclideanSpace ℝ (Fin 3) := fun i =>
    parityOriginalHistoricalRealLogTriple434 U Z (m i) (mp i) (z i)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V Z k buf a b hSmooth hSupport
  have hZero : ∀i∈sValid, ¬physical i → W i * f (t i)=0 := by
    intro i hi hnot
    have hiLegal : valid i := (Finset.mem_filter.mp hi).2
    rcases hiLegal with ⟨hm,hmp,hz,hzp,hmK,hmpK,hNe,hDet,hOdd,
      hShift,hDivMp,hDivM⟩
    exact hGhostL.2 hLw prime l u hl hlow K k hk hkBound
      d band slot δ ξ chi rho xi1 xi2 xi3 U E V Z signed
      (m i) (mp i) (z i) (zp i) (eInt i)
      hU hE hV hZ hm hmp hz hzp hDyad hNe hDet hOdd
      hShift hDivMp hDivM buf a b hSmooth hSupport hnot
  exact parity_original_historical_weighted_3d_source_ball_le_full_plus_ghost434
    sValid physical W t H L hLw U E V Z k buf a b hSmooth hSupport
    T hT hZero
end Green64Analytic.Parity

end

end

