module

public import Green64.Library.Sieve.Foundations.Part037
public import Green64.Library.Sieve.Foundations.Part036
public import Green64.Library.Sieve.Foundations.Part030
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Sieve.Foundations.Part008
public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Sieve.Foundations.Part035
public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Sieve.Foundations.Part012
public import Green64.Library.Sieve.Foundations.Part014
public import Green64.Library.Correlation.Part065
public import Green64.Library.Sieve.Foundations.Part032
public import Green64.Library.Sieve.Foundations.Part013

@[expose] public section

/-!
# Sieve / Foundations / Part038

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SmoothPsiNeighborKZAggregate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false

/-- Summation over ALL potentially nonzero original smooth ψ dyads,
including the preceding half-scale. No hard binary-mask truncation:
nonzero ψ(z/2^j) implies this envelope by the source-verified theorem.
Total loss <=(2N+1)*2*(floor(log2 Y)+1). -/
theorem parity_original_actual_signed_k_smooth_psi_neighbor_global_norm_bound434
    (L D C : ℝ) (hL : 0<L) (hC : 0≤C)
    (KS : Finset ℤ) (N : ℕ) (hKS : ∀ k∈KS, k.natAbs≤N)
    (ZS : Finset ℕ) (Y : ℕ)
    (hZS : ∀ z∈ZS, z≤Y) (hZpos : ∀ z∈ZS, 0<z)
    (F : ℤ → ℕ → ℂ)
    (hCell : ∀ k∈KS, ∀ Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
      ‖F k Z‖≤C*(Z:ℝ)*L^(-D)) :
    ‖∑k∈KS, ∑Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS, F k Z‖ ≤
      (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*C*(Y:ℝ)*L^(-D) := by
  classical
  let DY : Finset ℕ := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS
  have hkcard : KS.card≤2*N+1 :=
    parity_original_actual_signed_k_set_card_le434 KS N hKS
  have hzcard : DY.card≤2*(Nat.log 2 Y+1) :=
    parity_original_actual_smooth_psi_neighbor_card_le434 ZS Y hZS
  have hzle : ∀Z∈DY,(Z:ℝ)≤(Y:ℝ) := by
    intro Z hZ
    have hZE := (Finset.mem_union.mp hZ)
    rcases hZE with hBase | hHalf
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hBase
      have h := (parity_original_historical_actual_z_in_own_dyad434 z (hZpos z hz)).2.1
      exact_mod_cast h.trans (hZS z hz)
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hHalf
      have h := (parity_original_historical_actual_z_in_own_dyad434 z (hZpos z hz)).2.1
      have hhalf : parityOriginalHistoricalActualZDyadicScale434 z / 2 ≤ z := by
        omega
      exact_mod_cast hhalf.trans (hZS z hz)
  have hPow : 0≤L^(-D) := (Real.rpow_pos_of_pos hL _).le
  let M : ℝ := C*(Y:ℝ)*L^(-D)
  have hM : 0≤M := by dsimp [M]; positivity
  have hBound : ∀ k∈KS, ∀ Z∈DY, ‖F k Z‖≤M := by
    intro k hk Z hz
    calc
      ‖F k Z‖ ≤ C*(Z:ℝ)*L^(-D) := hCell k hk Z hz
      _ ≤ C*(Y:ℝ)*L^(-D) := by
        apply mul_le_mul_of_nonneg_right _ hPow
        exact mul_le_mul_of_nonneg_left (hzle Z hz) hC
  have hTri :
      ‖∑ k∈KS, ∑ Z∈DY, F k Z‖ ≤
        ∑ k∈KS, ∑ Z∈DY, ‖F k Z‖ := by
    calc
      _ ≤ ∑ k∈KS, ‖∑ Z∈DY, F k Z‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ k∈KS, ∑ Z∈DY, ‖F k Z‖ := by
        apply Finset.sum_le_sum
        intro k hk
        exact norm_sum_le _ _
  have hFinite : (∑ k∈KS, ∑ Z∈DY, ‖F k Z‖) ≤
      ((KS.card:ℝ)*(DY.card:ℝ))*M := by
    calc
      _ ≤ ∑ k∈KS, ∑ Z∈DY, M := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro Z hz
        exact hBound k hk Z hz
      _ = ((KS.card:ℝ)*(DY.card:ℝ))*M := by simp [mul_assoc]
  have hkc : (KS.card:ℝ)≤((2*N+1:ℕ):ℝ) := by exact_mod_cast hkcard
  have hzc : (DY.card:ℝ)≤((2*(Nat.log 2 Y+1):ℕ):ℝ) := by exact_mod_cast hzcard
  have hProd : (KS.card:ℝ)*(DY.card:ℝ) ≤
      ((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ) := by
    exact mul_le_mul hkc hzc (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ ((KS.card:ℝ)*(DY.card:ℝ))*M := hTri.trans hFinite
    _ ≤ (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*M :=
      mul_le_mul_of_nonneg_right hProd hM
    _ = (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*C*(Y:ℝ)*L^(-D) := by
      dsimp [M]; ring
end Green64Analytic.Parity

end

end

/-! ## BPrimeActualSmoothPsiGlobal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- This is the actual original B' source Fourier signal summed over
both dyadic scales permitted by its ORIGINAL C-infinity ψ(z/Z)
support 1<z/Z<4. The source coefficient, character projector, and
five-factor Schwartz kernel are unchanged; only the **index set**
is the proved complete smooth ψ neighbor envelope. Price: at most
2(2N+1)(floor(log2 Y)+1) per original fine family. -/
theorem parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_norm434
    (jQ : ℕ) (D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 8≤L ∧ 6*Cbox≤L ∧
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
          (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (KS : Finset ℤ) (N Y : ℕ) (ZS : Finset ℕ),
          (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^Ck) →
          (∀z∈ZS, 0<z ∧ z≤Y) →
          (∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            Real.exp L*L^(-CZ)≤(Z:ℝ) ∧
            (Z:ℝ)≤Real.exp L*L^CZ ∧
            (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) →
          (∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∑k∈KS,∑Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
          parityOriginalActualBprimeFineLowfreqSignal434
            d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
            rho xi1 xi2 xi3 T signed buf A hSmooth hSupport‖ ≤
          (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*
            (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D) := by
  obtain ⟨J,B,S,hBS,hLocal⟩ :=
    parity_eventually_original_actual_Bprime_full_odd_fixed_KZ_any_log_saving434
      jQ D C0 Cf CZ Ck beta gamma K0 Cbox A R
      hD hCf hCZ hCk hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC0 : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤Cmoment1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hC : 0≤Cmoment+132*Cmoment1 := by linarith
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hLocal] with L hL
  refine ⟨hL.1,hL.2.1,hL.2.2.1,hL.2.2.2.1,?_⟩
  intro hLw hFamily band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hkZwindow
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let alpha := restrictSequence K
    (b629ActualFineAlpha434 prime L S gamma lFine uFine)
  let F : ℤ → ℕ → ℂ := fun k Z =>
    parityOriginalActualBprimeFineLowfreqSignal434
      d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
      rho xi1 xi2 xi3 T signed buf A hSmooth hSupport
  have hKBound : ∀k∈KS,k.natAbs≤N := by
    intro k hk
    exact (hKS k hk).2.1
  have hZBound : ∀z∈ZS,z≤Y := by
    intro z hz
    exact (hZS z hz).2
  have hZPositive : ∀z∈ZS,0<z := by
    intro z hz
    exact (hZS z hz).1
  have hPosL : 0<L := by linarith
  have hCell : ∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
      ‖F k Z‖≤(Cmoment+132*Cmoment1)*(Z:ℝ)*L^(-D) := by
    intro k hk Z hz
    have hkk := hKS k hk
    have hzz := hZwindow Z hz
    have hkz := hkZwindow k hk Z hz
    have hOne := hL.2.2.2.2 hLw hFamily (Z:ℝ) hzz.1 hzz.2.1
      band hBand slot delta freq k hkk.1 hkk.2.2
      rho xi1 xi2 xi3 U E V T signed
      hU hEpos hV hUV hEscale hzz.2.2 hT
      hrho hxi1 hxi2 hxi3 hkz
      prime lFine uFine a b hFineLow hl hu huExp hDyad
    dsimp only at hOne ⊢
    change ‖F k Z‖ ≤ (Cmoment+132*Cmoment1)*(Z:ℝ)*L^(-D)
    simpa only [F,parityOriginalActualBprimeFineLowfreqSignal434] using hOne
  have hSum :=
    parity_original_actual_signed_k_smooth_psi_neighbor_global_norm_bound434
      L D (Cmoment+132*Cmoment1) hPosL hC KS N hKBound ZS Y hZBound
      hZPositive F hCell
  simpa only [F,d,K,alpha,Cmoment,Cmoment1] using hSum
end Green64Analytic.Parity

end

end

/-! ## BPrimeActualSmoothPsiAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- For one ORIGINAL Q band/slot, one fine b629 interval and fixed
allocation/frequency family, the entire real signed k × source-dyadic Z
post-Cauchy B' low-frequency complex sum has arbitrary source-log
saving O(exp(L)L^(-Agoal)). The precision D is chosen BEFORE the
spectral J,B,S and L. The only new hypotheses on the finite k/Z
carriers are the concrete original integer cap N<=ceil(L^Ck), the
real source z cap Y<=25 Cbox exp(L)L^(K0+88), and logY<=2L;
all are geometry, not a TypeII/correlation assumption. This does NOT
claim original Cauchy, high Fourier tail, or all fine-cell families. -/
theorem parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_any_log434
    (jQ : ℕ) (Agoal D C0 Cf CZ Ck beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+Ck+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hCZ : 0≤CZ) (hCk : 0≤Ck)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 8≤L ∧ 6*Cbox≤L ∧
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
          (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)≤2*U) →
        ∀ (KS : Finset ℤ) (N Y : ℕ) (ZS : Finset ℕ),
          (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^Ck) →
          (∀z∈ZS, 0<z ∧ z≤Y) →
          (∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            Real.exp L*L^(-CZ)≤(Z:ℝ) ∧
            (Z:ℝ)≤Real.exp L*L^CZ ∧
            (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) →
          (∀k∈KS,∀Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
            |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) →
          N≤Nat.ceil (L^Ck) →
          (Y:ℝ)≤25*Cbox*Real.exp L*L^(K0+88) →
          1≤Y → Real.log (Y:ℝ)≤2*L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∑k∈KS,∑Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
          parityOriginalActualBprimeFineLowfreqSignal434
            d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
            rho xi1 xi2 xi3 T signed buf A hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hGlobal⟩ :=
    parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_norm434
      jQ D C0 Cf CZ Ck beta gamma K0 Cbox A R
      hD hCf hCZ hCk hbeta hgamma hK0 hCbox hA hR
      buf hSmooth hSupport hCube
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  have hC0 : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤Cmoment1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hC : 0≤Cmoment+132*Cmoment1 := by linarith
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hGlobal] with L hL
  refine ⟨hL.1,hL.2.1,hL.2.2.1,hL.2.2.2.1,?_⟩
  intro hLw hFamily band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hkZwindow hN hY hYpos hLogY
  have hBound := hL.2.2.2.2 hLw hFamily band hBand slot delta freq
    rho xi1 xi2 xi3 U E V T signed hU hEpos hV hUV hEscale
    hT hrho hxi1 hxi2 hxi3 prime lFine uFine a b
    hFineLow hl hu huExp hDyad KS N Y ZS hKS hZS hZwindow hkZwindow
  have hNumeric := parity_original_actual_kZ_counted_loss_absorbed434
    L Agoal D (Cmoment+132*Cmoment1) Ck K0 Cbox N Y
    (by linarith : 1≤L) hC hCk hK0 hCbox hN hY hYpos hLogY hPrecision
  let Q : ℝ := (((2*N+1:ℕ):ℝ)*((Nat.log 2 Y+1:ℕ):ℝ))*
     (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D)
  have hTwice :
      (((2*N+1:ℕ):ℝ)*((2*(Nat.log 2 Y+1):ℕ):ℝ))*
        (Cmoment+132*Cmoment1)*(Y:ℝ)*L^(-D) = 2*Q := by
    dsimp [Q]; push_cast; ring
  have hTwiceBound :
      2*Q ≤ (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
        Real.exp L*L^(-Agoal) := by
    calc
      2*Q ≤ 2*((125*Cbox*(1+2/Real.log 2)*
          (Cmoment+132*Cmoment1))*Real.exp L*L^(-Agoal)) :=
        mul_le_mul_of_nonneg_left hNumeric (by norm_num)
      _ = _ := by ring
  dsimp only at hBound ⊢
  exact hBound.trans (hTwice ▸ hTwiceBound)
end Green64Analytic.Parity

end

end

/-! ## SourceGlobalFubiniKernel -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- Genuine finite positive-carrier extension, by zero outside the
actual SOURCE support: this is equality of complex sums, not a false
inequality between norms of complex subsums. -/
theorem parity_original_finite_source_sum_zero_extend434
    {ι : Type} [DecidableEq ι] (s t : Finset ι) (hst : s⊆t)
    (f : ι → ℂ) :
    (∑i∈s, f i) = ∑i∈t, if i∈s then f i else 0 := by
  classical
  symm
  calc
    _ = ∑i∈s, if i∈s then f i else 0 := by
      symm
      apply Finset.sum_subset hst
      intro i hit hin
      simp [hin]
    _ = ∑i∈s, f i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]

/-- Exact all-e,m,k,Z and COMPLETE 2|k|-character SOURCE Fubini.
A complex coefficient can be placed on one total k/Z support only
using zero extension; the entire character family remains inside
any fixed (k,Z) group before taking a norm. The original source
sets may depend arbitrarily on e,m,k and may contain P-bad odd e;
no inferred pointwise character cancellation and no multiplicity
factor appears. This is the algebraic transport interface required
by the genuine full Bprime outer, before spectral estimates. -/
theorem parity_original_finite_source_full_character_kZ_fubini434
    (E M : Finset ℕ) (KG : Finset ℤ) (ZG : Finset ℕ)
    (ks : ℕ → ℕ → Finset ℤ)
    (zs : ℕ → ℕ → ℤ → Finset ℕ)
    (c : (k : ℤ) → DirichletCharacter ℂ (2*k.natAbs) → ℂ)
    (F : (e m : ℕ) → (k : ℤ) → DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℂ)
    (hk : ∀ e∈E, ∀ m∈M, ks e m ⊆ KG)
    (hz : ∀ e∈E, ∀ m∈M, ∀ k∈ks e m, zs e m k ⊆ ZG) :
    (∑e∈E, ∑m∈M, ∑k∈ks e m,
      ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        c k χ * (∑z∈zs e m k, F e m k χ z)) =
    ∑k∈KG, ∑z∈ZG, ∑χ : DirichletCharacter ℂ (2*k.natAbs),
      c k χ * (∑e∈E,∑m∈M,
        if k∈ks e m ∧ z∈zs e m k then F e m k χ z else 0) := by
  classical
  have hCell (e m : ℕ) (he : e∈E) (hm : m∈M) :
      (∑k∈ks e m, ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        c k χ * ∑z∈zs e m k, F e m k χ z) =
      ∑k∈KG, ∑z∈ZG, ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        c k χ * (if k∈ks e m ∧ z∈zs e m k then F e m k χ z else 0) := by
    let g : ℤ → ℂ := fun k =>
      ∑χ : DirichletCharacter ℂ (2*k.natAbs),
        c k χ * ∑z∈zs e m k, F e m k χ z
    have hs : ks e m⊆KG := hk e he m hm
    have hExt := parity_original_finite_source_sum_zero_extend434 (ks e m) KG hs g
    change (∑k∈ks e m, g k) = _
    rw [hExt]
    apply Finset.sum_congr rfl
    intro k hkG
    by_cases hkS : k∈ks e m
    · simp only [hkS, if_true]
      change (∑χ : DirichletCharacter ℂ (2*k.natAbs),
        c k χ * (∑z∈zs e m k, F e m k χ z)) = _
      have hZExt (χ : DirichletCharacter ℂ (2*k.natAbs)) :
          (∑z∈zs e m k, F e m k χ z) =
          ∑z∈ZG, if z∈zs e m k then F e m k χ z else 0 :=
        parity_original_finite_source_sum_zero_extend434
          (zs e m k) ZG (hz e he m hm k hkS) _
      have hChi :
          (∑χ : DirichletCharacter ℂ (2*k.natAbs),
            c k χ * (∑z∈zs e m k, F e m k χ z)) =
          ∑χ : DirichletCharacter ℂ (2*k.natAbs),
            c k χ * (∑z∈ZG, if z∈zs e m k then F e m k χ z else 0) := by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [hZExt χ]
      calc
        _ = ∑χ : DirichletCharacter ℂ (2*k.natAbs),
              ∑z∈ZG, c k χ * (if z∈zs e m k then F e m k χ z else 0) := by
            rw [hChi]
            apply Finset.sum_congr rfl
            intro χ hχ
            rw [Finset.mul_sum]
        _ = ∑z∈ZG, ∑χ : DirichletCharacter ℂ (2*k.natAbs),
              c k χ * (if z∈zs e m k then F e m k χ z else 0) :=
          Finset.sum_comm
        _ = _ := by
            apply Finset.sum_congr rfl
            intro z hzG
            simp only [hkS, true_and]
    · simp only [hkS, false_and, if_false, Finset.sum_const_zero, mul_zero]
  calc
    _ = ∑e∈E, ∑m∈M, ∑k∈KG, ∑z∈ZG,
          ∑χ : DirichletCharacter ℂ (2*k.natAbs),
            c k χ * (if k∈ks e m ∧ z∈zs e m k then F e m k χ z else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro m hm
          exact hCell e m he hm
    _ = ∑k∈KG, ∑z∈ZG, ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          c k χ * (∑e∈E,∑m∈M,
            if k∈ks e m ∧ z∈zs e m k then F e m k χ z else 0) := by
          let H : (e m : ℕ) → (k : ℤ) → ℕ →
              DirichletCharacter ℂ (2*k.natAbs) → ℂ :=
            fun e m k z χ => c k χ *
              (if k∈ks e m ∧ z∈zs e m k then F e m k χ z else 0)
          change (∑e∈E, ∑m∈M, ∑k∈KG, ∑z∈ZG,
              ∑χ : DirichletCharacter ℂ (2*k.natAbs), H e m k z χ) = _
          calc
            _ = ∑e∈E, ∑k∈KG, ∑m∈M, ∑z∈ZG,
                ∑χ : DirichletCharacter ℂ (2*k.natAbs), H e m k z χ := by
                  apply Finset.sum_congr rfl
                  intro e he
                  rw [Finset.sum_comm]
            _ = ∑k∈KG, ∑e∈E, ∑m∈M, ∑z∈ZG,
                ∑χ : DirichletCharacter ℂ (2*k.natAbs), H e m k z χ :=
                  Finset.sum_comm
            _ = ∑k∈KG, ∑e∈E, ∑z∈ZG, ∑m∈M,
                ∑χ : DirichletCharacter ℂ (2*k.natAbs), H e m k z χ := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  apply Finset.sum_congr rfl
                  intro e he
                  rw [Finset.sum_comm]
            _ = ∑k∈KG, ∑z∈ZG, ∑e∈E, ∑m∈M,
                ∑χ : DirichletCharacter ℂ (2*k.natAbs), H e m k z χ := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [Finset.sum_comm]
            _ = ∑k∈KG, ∑z∈ZG, ∑e∈E,
                ∑χ : DirichletCharacter ℂ (2*k.natAbs),
                  ∑m∈M, H e m k z χ := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  apply Finset.sum_congr rfl
                  intro z hz
                  apply Finset.sum_congr rfl
                  intro e he
                  rw [Finset.sum_comm]
            _ = ∑k∈KG, ∑z∈ZG,
                ∑χ : DirichletCharacter ℂ (2*k.natAbs),
                  ∑e∈E, ∑m∈M, H e m k z χ := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  apply Finset.sum_congr rfl
                  intro z hz
                  rw [Finset.sum_comm]
            _ = _ := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  apply Finset.sum_congr rfl
                  intro z hz
                  apply Finset.sum_congr rfl
                  intro χ hχ
                  dsimp only [H]
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro e he
                  rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## SourceGlobalFubiniPhysical -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- TRUE original full-odd e and actual cofactor m finite k support,
formed by taking the UNION rather than by inserting an arbitrary
new cutoff on the signed k values. -/
def parityOriginalHistoricalFullOddOriginalKUnion434
    (E : ℝ) (K : Finset ℕ) : Finset ℤ :=
  (parityOriginalHistoricalFullOddEEnvelope434 E).biUnion fun e =>
    K.biUnion fun m => parityOriginalHistoricalNonzeroKSupport434 e m K

/-- Original, only physically populated, ηeηn NONZERO dyadic z
support, union over actual full odd e/m/k. No missed or repeated
physical source cell and no hard mask on the real smooth weights. -/
def parityOriginalHistoricalFullOddOriginalZUnion434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) : Finset ℕ :=
  (parityOriginalHistoricalFullOddEEnvelope434 E).biUnion fun e =>
    K.biUnion fun m =>
      (parityOriginalHistoricalNonzeroKSupport434 e m K).biUnion fun k =>
        parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
          d L E V hL band slot δ Y e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k

/-- Literal physical cap-free B509/B633 original outer reindexed by
all signed k and all ACTUALLY attained dyadic Z. The χ modulus
remains EXACTLY 2|k|, the entire character projector is summed at
fixed k,Z BEFORE the complex norm, and every original source
coefficient at e,m,k,χ,Z is retained once. Source-union zero
extension is exact, including e with P-group prime divisors.
This proves the global algebraic SOURCE k/Z join, not the global
spectral or Type II bound; the latter still needs identification
of the inner fixed-k,Z sum with the full source Bprime ball. -/
theorem parity_original_full_odd_filtered_B633_source_outer_kZ_fubini434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀ t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) :
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hL band slot δ Y K
    parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
      d L U E V hL band slot δ ξ rho K alpha signed Y
      buf a b hSmooth hSupport T =
    ∑k∈KG,∑Z∈ZG,∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∑e∈EF,∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K ∧
              Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
                d L E V hL band slot δ Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) k then
            parityOriginalHistoricalUngatedActualB633FourierBall434
              d L U E V hL Z k band slot δ ξ rho alpha signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupport T
          else 0) := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let KS : ℕ → ℕ → Finset ℤ := fun e m =>
    parityOriginalHistoricalNonzeroKSupport434 e m K
  let ZS : ℕ → ℕ → ℤ → Finset ℕ := fun e m k =>
    parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) k
  let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hL band slot δ Y K
  have hK : ∀ e∈EF, ∀ m∈K, KS e m⊆KG := by
    intro e he m hm k hk
    change k∈(EF.biUnion fun e => K.biUnion fun m => KS e m)
    exact Finset.mem_biUnion.mpr ⟨e,he,Finset.mem_biUnion.mpr ⟨m,hm,hk⟩⟩
  have hZ : ∀ e∈EF, ∀ m∈K, ∀ k∈KS e m, ZS e m k⊆ZG := by
    intro e he m hm k hk z hz
    change z∈(EF.biUnion fun e => K.biUnion fun m =>
      (KS e m).biUnion fun k => ZS e m k)
    exact Finset.mem_biUnion.mpr ⟨e,he, Finset.mem_biUnion.mpr
      ⟨m,hm, Finset.mem_biUnion.mpr ⟨k,hk,hz⟩⟩⟩
  let c : (k : ℤ) → DirichletCharacter ℂ (2*k.natAbs) → ℂ := fun k χ =>
    parityShiftTwoMaskCoefficient434 k.natAbs χ
  let F : (e m : ℕ) → (k : ℤ) → DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℂ :=
    fun e m k χ Z => parityOriginalHistoricalUngatedActualB633FourierBall434
      d L U E V hL Z k band slot δ ξ rho alpha signed Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) χ
      buf a b hSmooth hSupport T
  have hF := parity_original_finite_source_full_character_kZ_fubini434
    EF K KG ZG KS ZS c F hK hZ
  change parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
    d L U E V hL band slot δ ξ rho K alpha signed Y buf a b hSmooth hSupport T = _
  unfold parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
  exact hF
end Green64Analytic.Parity

end

end

/-! ## OriginalDyadicSourceBoundary -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Exact value of the ACTUAL smooth Parity dyadic psi at the lower
edge of the canonical binary cell. This is not an artificial
hard cutoff: the constructed smooth step is one at both 1/2 and 1,
so its difference is zero. Important for auditing sharp-bin versus
smooth-partition SOURCE transports. -/
theorem parity_original_historical_true_dyadic_psi_at_one_zero434 :
    parityOriginalHistoricalDyadicSmoothPsi434 1 = 0 := by
  have hHalf := parity_original_historical_dyadic_step_one434
    (1/2:ℝ) (by norm_num)
  have hOne := parity_original_historical_dyadic_step_one434
    (1:ℝ) (by norm_num)
  unfold parityOriginalHistoricalDyadicSmoothPsi434
    parityOriginalHistoricalDyadicSmoothPsiReal434
  rw [hHalf,hOne]
  norm_num

/-- At the adjacent smaller dyadic scale, the same exact physical
z=2Z source position receives full smooth weight one: the positive
guard is one at 2, the step at 1 is one and at 2 is zero. -/
theorem parity_original_historical_true_dyadic_psi_at_two_one434 :
    parityOriginalHistoricalDyadicSmoothPsi434 2 = 1 := by
  have hOne := parity_original_historical_dyadic_step_one434
    (1:ℝ) (by norm_num)
  have hTwo := parity_original_historical_dyadic_step_zero434
    (2:ℝ) (by norm_num)
  have hGuard := parity_original_historical_dyadic_guard_one434
    (2:ℝ) (by norm_num)
  unfold parityOriginalHistoricalDyadicSmoothPsi434
    parityOriginalHistoricalDyadicSmoothPsiReal434
  simp only [show (2:ℝ)/2=(1:ℝ) by norm_num]
  rw [hOne,hTwo,hGuard]
  norm_num

/-- The exact concrete source audit obstruction: a sharp canonical
binary Z-cell alone is NOT the complete true smooth ψ_Z partition.
At z=2 and own Z=2 the physical ψ equals zero, whereas the
neighboring Z=1 term equals one. This does not refute the separately
proven kernel theorems about a pre-selected ψ-filtered source; it
shows the extra paper-to-Lean bridge required to identify that
filtered object with the unfiltered original Bprime coefficient. -/
theorem parity_original_canonical_binary_Z_not_single_smooth_partition434 :
    parityOriginalHistoricalDyadicSmoothPsi434 ((2:ℝ)/(2:ℝ)) = 0 ∧
    parityOriginalHistoricalDyadicSmoothPsi434 ((2:ℝ)/(1:ℝ)) = 1 := by
  constructor
  · norm_num
    exact parity_original_historical_true_dyadic_psi_at_one_zero434
  · norm_num
    exact parity_original_historical_true_dyadic_psi_at_two_one434
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalSmoothDyadicPartition -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5200000

/-- The TRUE constructed smooth dyadic psi, not the sharp canonical
Z selection, sums to complex ONE on the complete source range.
This follows from the native real telescoping partition by exact
complex cast, retaining the actual fixed Mathlib bump profile. -/
theorem parity_original_true_complex_smooth_dyadic_partition_one434
    (z : ℝ) (N : ℕ) (hzLo : 2≤z) (hzHi : z≤(2:ℝ)^(N+1)) :
    (∑j∈Finset.range (N+1),
      parityOriginalHistoricalDyadicSmoothPsi434 (z/(2:ℝ)^j)) = (1:ℂ) := by
  have hReal := parity_original_historical_fixed_smooth_dyadic_partition_one434
    z N hzLo hzHi
  change (∑j∈Finset.range (N+1),
    (parityOriginalHistoricalDyadicSmoothPsiReal434 (z/(2:ℝ)^j):ℂ)) = 1
  rw [← Complex.ofReal_sum]
  exact_mod_cast hReal

/-- Actual original all-odd-e h=-2 physical TWO-ENDPOINT B509
m'×n source, for any signed complex coefficient W, is exactly its
COMPLETE true SMOOTH dyadic psi partition over 2^j. The source
carrier includes repeated n,m' with their correct multiplicities;
there is no fake per-χ vanishing or complex-subsum norm inequality.
It is NOT the invalid identification with one sharp binary-Z cell.
The real z-range hypotheses are needed ONLY at genuinely nonzero
source W atoms; zero weights are retained and do not create a fake
new support condition. They must be discharged from original SOURCE
geometry before original Type II can use this interface. -/
theorem parity_original_true_physical_full_smooth_dyadic_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (N : ℕ)
    (W : (ℕ×ℕ) → ℂ)
    (hZrange : ∀q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k, W q ≠ 0 →
      (2:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)≤(2:ℝ)^(N+1)) :
    (∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k, W q) =
    ∑j∈Finset.range (N+1),
      ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
        parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j) * W q := by
  classical
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let zz : (ℕ×ℕ) → ℝ := fun q =>
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)
  calc
    _ = ∑q∈S,
        (∑j∈Finset.range (N+1),
          parityOriginalHistoricalDyadicSmoothPsi434 (zz q/(2:ℝ)^j))*W q := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases hW : W q = 0
          · simp [hW]
          · have hr := hZrange q hq hW
            rw [parity_original_true_complex_smooth_dyadic_partition_one434
              (zz q) N hr.1 hr.2]
            ring
    _ = ∑q∈S,∑j∈Finset.range (N+1),
          parityOriginalHistoricalDyadicSmoothPsi434 (zz q/(2:ℝ)^j)*W q := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_mul]
    _ = _ := Finset.sum_comm
end Green64Analytic.Parity

end

end

/-! ## ActualFinePhysicalProjectorOne -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- ORIGINAL Parity(2.6) complete character mask is exactly ONE on
actual populated post-Cauchy full-odd B509 source when the two
ORIGINAL fine b629 cofactors are nonzero. It is NOT assumed and
it is not asserted for individual χ. The physical h=-2 equations
derive the same signed k used by the true modulus 2|k|, while
roughness and cofactor oddness come from the actual fine α.
No P-free e condition is required after positive Cauchy enlargement. -/
theorem parity_eventually_original_actual_fine_physical_full_projector_one434
    (S beta gamma Ck : ℝ)
    (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l uFine : ℕ),
      2≤l → Real.exp (beta*L)≤(l:ℝ) →
      ∀ (K : Finset ℕ) (k : ℤ), k≠0 → (k.natAbs:ℝ)≤L^Ck →
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (Y e m mp n : ℕ),
      Odd e → m≠mp →
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot delta Y e m mp n →
      parityOriginalHistoricalOffdiagK434 e m mp=k →
      let alpha := restrictSequence K
        (b629ActualFineAlpha434 prime L S gamma l uFine)
      alpha m≠0 → alpha mp≠0 →
      (∑chi : DirichletCharacter ℂ (2*k.natAbs),
        parityShiftTwoMaskCoefficient434 k.natAbs chi *
        chi (mp:ZMod (2*k.natAbs)) *
        star (chi (m:ZMod (2*k.natAbs))))=1 := by
  filter_upwards [parity_eventually_actual_fine_bilinear_fourier_mask_one434
    S beta gamma Ck hS hbeta hgamma] with L hFine
  refine ⟨hFine.1,?_⟩
  intro prime l uFine hl hlow K k hk hkBound d band slot delta
    Y e m mp n he hNe hValid hK alpha hα hαp
  obtain ⟨u,hu,up,hup,hDiv,hDivp,hVS,hVPS⟩ := hValid
  have hm : m*n=u+2 := (Finset.mem_filter.mp hu).2.2.2
  have hmp : mp*n=up+2 := (Finset.mem_filter.mp hup).2.2.2
  have h1 : m*n=e*(u/e)+2 := by
    calc
      _ = u+2 := hm
      _ = e*(u/e)+2 := by rw [Nat.mul_div_cancel_left' hDiv]
  have h2 : mp*n=e*(up/e)+2 := by
    calc
      _ = up+2 := hmp
      _ = e*(up/e)+2 := by rw [Nat.mul_div_cancel_left' hDivp]
  obtain ⟨k0,hk0,hDet,hV,h2Det,hMask⟩ := hFine.2
    prime l uFine hl hlow K m mp n e (u/e) (up/e)
    hα hαp he h1 h2 hNe
  have hkCan : parityOriginalHistoricalOffdiagK434 e m mp = k0 :=
    parity_original_historical_physical_k_eq_quotient434 e m mp he.pos k0 hDet
  have hkeq : k0=k := hkCan.symm.trans hK
  have hMask0 := (hMask (by rw [hkeq]; exact hkBound)).2
  rw [hkeq] at hMask0
  exact hMask0
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothedKOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 3900000

/-- SOURCE-TRUE physically nonzero signed k support, NOT the too-wide
union of all quotient k from full odd e<=2E. Every k in this support
has an actual Q/P-B509 two-endpoint n,m' witness with nonzero original
eta_e(e/E)*eta_n(n/V). Empty and zero-weight cells are removed only
at the full source level, before Fourier truncation. -/
def parityOriginalHistoricalFullOddSmoothedKUnion434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) : Finset ℤ :=
  (parityOriginalHistoricalFullOddEEnvelope434 E).biUnion fun e =>
    K.biUnion fun m =>
      (parityOriginalHistoricalNonzeroKSupport434 e m K).filter fun k =>
        (parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
          d L E V hL band slot δ Y e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k).Nonempty

/-- The true nonzero-weight k index set is a subset of the original
literal quotient union. No signed-complex reduction follows from
this inclusion alone; zero extension is proved separately. -/
theorem parity_original_full_odd_smoothed_k_sub_raw434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) :
    parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hL band slot δ Y K ⊆
      parityOriginalHistoricalFullOddOriginalKUnion434 E K := by
  intro k hk
  have hmem := hk
  unfold parityOriginalHistoricalFullOddSmoothedKUnion434 at hmem
  obtain ⟨e,he,hrest⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨m,hm,hk0⟩ := Finset.mem_biUnion.mp hrest
  have hkRaw := (Finset.mem_filter.mp hk0).1
  exact Finset.mem_biUnion.mpr ⟨e,he,Finset.mem_biUnion.mpr ⟨m,hm,hkRaw⟩⟩

/-- Real original full-odd Cauchy source, with e carrying arbitrary
P-group divisors, forces every NONZERO-WEIGHT signed k to satisfy
k ≠ 0 and |k| ≤ ceil(L^(K0+89)). In particular the unrestricted
full KUnion cannot replace this predicate (e as small as 1 causes
spurious huge zero-weight k). -/
theorem parity_original_full_odd_smoothed_k_genuine_polylog434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L) (hU : 0<U)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (k : ℤ)
    (hk : k∈parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hL band slot δ Y K) :
    k≠0 ∧ (k.natAbs:ℝ)<L^(K0+89) ∧
      k.natAbs≤Nat.ceil (L^(K0+89)) := by
  have hmem := hk
  unfold parityOriginalHistoricalFullOddSmoothedKUnion434 at hmem
  obtain ⟨e,he,hrest⟩ := Finset.mem_biUnion.mp hmem
  obtain ⟨mm,hmm,hk0⟩ := Finset.mem_biUnion.mp hrest
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  have hkNe : k≠0 := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hk0).1).2
  have hSel := (Finset.mem_filter.mp hk0).2
  obtain ⟨Z,hZ⟩ := hSel
  have hShort := parity_original_historical_ungated_full_odd_selected_Z_k_short434
    d L U E V K0 hL band slot δ Y e mm K
    (parityOriginalHistoricalFullNEnvelope434 V) k Z
    heOdd hU hE hmm hDyad hZ
  exact ⟨hkNe,hShort.1,hShort.2⟩
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothedKZOuterJoin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- SOURCE-EXACT replacement of the overbroad original k quotient
union by the physically nonzero eta_e eta_n Parity-B509 k union.
This is equality of FULL complex character-projected original B'
Fourier outer, and drops no genuine k or e,n,m,m',z coefficient.
When an excluded k is encountered, EVERY original nonzero-weight
Z cell at that k is empty; the argument proves literal zero, not
false monotonicity of signed complex subsums. -/
theorem parity_original_full_odd_filtered_B633_source_outer_smoothed_kZ_fubini434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀ t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) :
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hL band slot δ Y K
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hL band slot δ Y K
    parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
      d L U E V hL band slot δ ξ rho K alpha signed Y
      buf a b hSmooth hSupport T =
    ∑k∈KSm,∑Z∈ZG,∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∑e∈EF,∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K ∧
              Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
                d L E V hL band slot δ Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) k then
            parityOriginalHistoricalUngatedActualB633FourierBall434
              d L U E V hL Z k band slot δ ξ rho alpha signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupport T
          else 0) := by
  classical
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let KRaw := parityOriginalHistoricalFullOddOriginalKUnion434 E K
  let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hL band slot δ Y K
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hL band slot δ Y K
  let F : ℤ → ℂ := fun k =>
    ∑Z∈ZG,∑χ : DirichletCharacter ℂ (2*k.natAbs),
      parityShiftTwoMaskCoefficient434 k.natAbs χ *
        (∑e∈EF,∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K ∧
              Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
                d L E V hL band slot δ Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) k then
            parityOriginalHistoricalUngatedActualB633FourierBall434
              d L U E V hL Z k band slot δ ξ rho alpha signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupport T
          else 0)
  have hOld := parity_original_full_odd_filtered_B633_source_outer_kZ_fubini434
    d L U E V hL band slot δ ξ rho K alpha signed Y
    buf a b hSmooth hSupport T
  have hSub : KSm ⊆ KRaw :=
    parity_original_full_odd_smoothed_k_sub_raw434 d L E V hL band slot δ Y K
  have hZero (k : ℤ) (hk : k∈KRaw) (hOut : k∉KSm) : F k=0 := by
    dsimp [F]
    apply Finset.sum_eq_zero
    intro Z hZ
    apply Finset.sum_eq_zero
    intro χ hχ
    have hInner : (∑e∈EF,∑m∈K,
          if k∈parityOriginalHistoricalNonzeroKSupport434 e m K ∧
              Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
                d L E V hL band slot δ Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) k then
            parityOriginalHistoricalUngatedActualB633FourierBall434
              d L U E V hL Z k band slot δ ξ rho alpha signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupport T
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      apply Finset.sum_eq_zero
      intro m hm
      have hNot : ¬ (k∈parityOriginalHistoricalNonzeroKSupport434 e m K ∧
          Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
            d L E V hL band slot δ Y e m K
            (parityOriginalHistoricalFullNEnvelope434 V) k) := by
        rintro ⟨hk0,hz0⟩
        apply hOut
        unfold KSm parityOriginalHistoricalFullOddSmoothedKUnion434
        exact Finset.mem_biUnion.mpr ⟨e,he,
          Finset.mem_biUnion.mpr ⟨m,hm,
            Finset.mem_filter.mpr ⟨hk0,⟨Z,hz0⟩⟩⟩⟩
      simp only [if_neg hNot]
    rw [hInner,mul_zero]
  dsimp only at hOld ⊢
  calc
    _ = ∑k∈KRaw,F k := hOld
    _ = ∑k∈KSm,F k := (Finset.sum_subset hSub hZero).symm
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothedZOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4200000

/-- The FULL original post-Cauchy B' physically nonzero original
smooth-weight Z UNION, not one e,m,k cell, satisfies the corrected
cap-free Parity(4.14) lower/upper dyadic window. All odd e (including
P-group prime factors) and all actual physical Q/P/B509 endpoints
are retained in the finite union; no bound on the number of z or
complex-character subsums is assumed. -/
theorem parity_original_full_odd_actual_nonzero_Z_union_box_window434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ)
    (hU : 0<U) (hV : 0<V) (hCbox : 0<Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hL band slot δ (Nat.ceil (6*U*V)) K) :
    (Real.exp L/16)*L^K0 < (Z:ℝ) ∧
    (Z:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
  have hz0 := hZ
  unfold parityOriginalHistoricalFullOddOriginalZUnion434 at hz0
  obtain ⟨e,he,hrest⟩ := Finset.mem_biUnion.mp hz0
  obtain ⟨m,hm,hrest⟩ := Finset.mem_biUnion.mp hrest
  obtain ⟨k,hk,hcell⟩ := Finset.mem_biUnion.mp hrest
  have hOdd : Odd e := (Finset.mem_filter.mp he).2
  obtain ⟨q,hq,hw⟩ := (Finset.mem_filter.mp hcell).2
  exact parity_original_historical_ungated_full_box_smoothed_actual_Z_window434
    d L U V E K0 Cbox hL band slot δ K
    (parityOriginalHistoricalFullNEnvelope434 V) e m k Z
    hOdd hU hV hCbox hUV hUVhi hE hm hDyad q hq hw
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothPsiUnionIdem -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4900000

/-- Exact source binary map is idempotent: re-running the dyadic scale
extraction on an already extracted power of two does not shift it. -/
theorem parity_original_historical_dyadic_scale_idempotent434 (z : ℕ) :
    parityOriginalHistoricalActualZDyadicScale434
      (parityOriginalHistoricalActualZDyadicScale434 z) =
    parityOriginalHistoricalActualZDyadicScale434 z := by
  unfold parityOriginalHistoricalActualZDyadicScale434
  rw [Nat.log_pow (by norm_num : 1<2)]

/-- The original physically nonzero B509 dyadic-height union
consists ONLY of actual powers of two. This is essential when
feeding the full smooth ψ-neighbor set into the k/Z saving; the
source Z union is not an arbitrary set of raw integers. -/
theorem parity_original_full_odd_actual_Z_union_canonical434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (Z : ℕ)
    (hZ : Z∈parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hL band slot δ Y K) :
    parityOriginalHistoricalActualZDyadicScale434 Z=Z := by
  have hz0 := hZ
  unfold parityOriginalHistoricalFullOddOriginalZUnion434 at hz0
  obtain ⟨e,he,hrest⟩ := Finset.mem_biUnion.mp hz0
  obtain ⟨m,hm,hrest⟩ := Finset.mem_biUnion.mp hrest
  obtain ⟨k,hk,hcell⟩ := Finset.mem_biUnion.mp hrest
  obtain ⟨q,hq,hscale⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hcell).1
  rw [←hscale]
  dsimp [parityOriginalHistoricalPhysicalZScaleOfEvent434]
  exact parity_original_historical_dyadic_scale_idempotent434
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)

/-- Consequently the exact smooth ψ neighbor envelope of the
actual original Z union is just the union of that source set with
its immediately preceding half-dyads, not another copy of every
physical z or invented independent dyadic scale. -/
theorem parity_original_full_odd_actual_Z_union_smooth_neighbor_exact434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) :
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hL band slot δ Y K
    parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG =
      ZG ∪ ZG.image (fun Z => Z/2) := by
  classical
  intro ZG
  have hImage : ZG.image parityOriginalHistoricalActualZDyadicScale434=ZG := by
    ext Z
    constructor
    · intro hh
      obtain ⟨z,hz,hval⟩ := Finset.mem_image.mp hh
      have hid : parityOriginalHistoricalActualZDyadicScale434 z=z :=
        parity_original_full_odd_actual_Z_union_canonical434
          d L E V hL band slot δ Y K z hz
      rw [hid] at hval
      exact hval ▸ hz
    · intro hz
      exact Finset.mem_image.mpr
        ⟨Z,hz,(parity_original_full_odd_actual_Z_union_canonical434
          d L E V hL band slot δ Y K Z hz)⟩
  unfold parityOriginalActualSmoothPsiNeighborZEnvelope434
  rw [hImage]
  have hHalf : ZG.image (fun z => parityOriginalHistoricalActualZDyadicScale434 z / 2) =
      ZG.image (fun z => z / 2) := by
    apply Finset.image_congr
    intro z hz
    change parityOriginalHistoricalActualZDyadicScale434 z / 2 = z / 2
    rw [parity_original_full_odd_actual_Z_union_canonical434
      d L E V hL band slot δ Y K z hz]
  rw [hHalf]

/-- Safe pointwise SOURCE support transfer from true smooth ψ to an
arbitrary containing set of actual canonical binary Z scales. No
false ψ=sharp-bin identification is used: both original and preceding
half-scale remain allowed, exactly as required by support 1<t<4. -/
theorem parity_original_actual_smooth_psi_nonzero_in_source_neighbor434
    (ZS : Finset ℕ) (z j : ℕ)
    (hz : parityOriginalHistoricalActualZDyadicScale434 z ∈ ZS)
    (hpsi : parityOriginalHistoricalDyadicSmoothPsi434
      ((z:ℝ)/(2:ℝ)^j)≠0) :
    (2:ℕ)^j ∈ ZS ∪ ZS.image (fun Z => Z/2) := by
  have hh := parity_original_actual_smooth_psi_dyadic_nonzero_neighbor434
    ({z} : Finset ℕ) z j (by simp) hpsi
  have hCase : (2:ℕ)^j = parityOriginalHistoricalActualZDyadicScale434 z ∨
      (2:ℕ)^j = parityOriginalHistoricalActualZDyadicScale434 z / 2 := by
    simpa [parityOriginalActualSmoothPsiNeighborZEnvelope434] using hh
  rcases hCase with hown | hhalf
  · exact Finset.mem_union.mpr (Or.inl (by rw [hown]; exact hz))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨parityOriginalHistoricalActualZDyadicScale434 z,hz,hhalf.symm⟩))
end Green64Analytic.Parity

end

end

/-! ## CauchyWoutPhysical -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The complete ORIGINAL Parity(4.10) exterior selected-Q/β energy
has an exact source e-window, and at most 2V+1 physical n values.
No assumption on the number of Q assignments or character masks is
smuggled into the Cauchy prefactor. This is a separate source
counting lemma, not a bound on the signed B' itself. -/
theorem parity_original_actual_cauchy_Wout_physical_card434
    (d : ℕ) (L E V A : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (J : Finset ℕ) (β : ℕ → ℂ)
    (hE : 0≤E) (hV : 0≤V) (hA : 0≤A)
    (hJ : ∀n∈J,(n:ℝ)≤2*V)
    (hBeta : ∀n∈J,‖β n‖≤1)
    (hAE : ∀e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e‖≤A) :
    (∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      ∑n∈J,‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e*β n‖^2) ≤
    ((⌊E⌋₊+1:ℕ):ℝ)*A^2*((⌊2*V⌋₊+1:ℕ):ℝ) := by
  have hJsub : J⊆Finset.range (⌊2*V⌋₊+1) := by
    intro n hn
    have hnV := hJ n hn
    have hFloor : n≤⌊2*V⌋₊ := Nat.le_floor hnV
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hFloor)
  have hJcard : J.card≤⌊2*V⌋₊+1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hJsub
  have hBetaSq : (∑n∈J,‖β n‖^2) ≤ ((⌊2*V⌋₊+1:ℕ):ℝ) := by
    calc
      _ ≤ ∑_n∈J,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have h := hBeta n hn
        nlinarith [norm_nonneg (β n)]
      _ = (J.card:ℝ) := by simp
      _ ≤ ((⌊2*V⌋₊+1:ℕ):ℝ) := by exact_mod_cast hJcard
  have hOuter := parity_original_historical_Cauchy_coefficient_L2_card434
    d L E band slot δ ξ rho J β hE A hA hAE
  have hCoeff : 0≤((⌊E⌋₊+1:ℕ):ℝ)*A^2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  calc
    _ ≤ ((⌊E⌋₊+1:ℕ):ℝ)*A^2*(∑n∈J,‖β n‖^2) := hOuter
    _ ≤ ((⌊E⌋₊+1:ℕ):ℝ)*A^2*((⌊2*V⌋₊+1:ℕ):ℝ) :=
      mul_le_mul_of_nonneg_left hBetaSq hCoeff

/-- On the physically relevant regime E,V>=1, the complete original
Cauchy exterior energy is bounded by 6EV A², with the initial E and V
factors kept distinct until the true source E=U L^-K0 substitution.
This does not absorb any Fourier or source Q variation by fiat. -/
theorem parity_original_actual_cauchy_Wout_EV434
    (d : ℕ) (L E V A : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (J : Finset ℕ) (β : ℕ → ℂ)
    (hE : 1≤E) (hV : 1≤V) (hA : 0≤A)
    (hJ : ∀n∈J,(n:ℝ)≤2*V)
    (hBeta : ∀n∈J,‖β n‖≤1)
    (hAE : ∀e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      ‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e‖≤A) :
    (∑e∈parityOriginalHistoricalCauchyActiveESupport434 d L E band slot δ,
      ∑n∈J,‖parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e*β n‖^2) ≤
    6*E*V*A^2 := by
  have hFirst := parity_original_actual_cauchy_Wout_physical_card434
    d L E V A band slot δ ξ rho J β (by linarith) (by linarith) hA hJ hBeta hAE
  have hEn : ((⌊E⌋₊+1:ℕ):ℝ) ≤ 2*E := by
    have hf : (⌊E⌋₊:ℝ)≤E := Nat.floor_le (by linarith)
    push_cast
    linarith
  have hVn : ((⌊2*V⌋₊+1:ℕ):ℝ) ≤ 3*V := by
    have hf : (⌊2*V⌋₊:ℝ)≤2*V := Nat.floor_le (by linarith)
    push_cast
    linarith
  have hSize : (((⌊E⌋₊+1:ℕ):ℝ)*A^2)*((⌊2*V⌋₊+1:ℕ):ℝ) ≤ 6*E*V*A^2 := by
    have hp : 0≤A^2 := sq_nonneg A
    have hmul := mul_le_mul hEn hVn (by positivity : 0≤((⌊2*V⌋₊+1:ℕ):ℝ)) (by positivity : 0≤2*E)
    nlinarith [mul_le_mul_of_nonneg_right hmul hp]
  exact hFirst.trans (by nlinarith [hSize])
end Green64Analytic.Parity

end

end

/-! ## CauchyWoutActualAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Original Parity(4.10) exterior Cauchy energy with no abstract source
a_e coefficient hypothesis: use the exact factorial-normalized B590
selected-Q Fourier coefficient bound and the real physical β≤1 and
J⊂[V,2V]. The entire actual Fourier gate product is retained; the
product's L1 integration is a SEPARATE theorem, not a pointwise
replacement by one. This is the correct SOURCE prefactor needed for
full global Parity TypeII. -/
theorem parity_eventually_original_actual_cauchy_Wout_EV_all_log434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E V : ℝ), 1≤E → 1≤V →
      ∀ (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (J : Finset ℕ) (β : ℕ → ℂ),
        (∀n∈J,(n:ℝ)≤2*V) →
        (∀n∈J,‖β n‖≤1) →
      let A : ℝ := L^parityOriginalSelectedECoefficientPolylogExponent434 *
        (∏ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length,
          ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖)
      (∑e∈parityOriginalHistoricalCauchyActiveESupport434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ,
        ∑n∈J,‖parityOriginalHistoricalWindowAE434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho e*β n‖^2) ≤
        6*E*V*A^2 := by
  filter_upwards [parity_eventually_original_historical_window_AE_polylog434,
    eventually_gt_atTop (0:ℝ)] with L hAE hL
  intro band slot E V hE hV δ ξ rho J β hJ hBeta
  let A : ℝ := L^parityOriginalSelectedECoefficientPolylogExponent434 *
    (∏ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
      band slot).length,
      ‖(𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)‖)
  have hA : 0≤A := mul_nonneg (Real.rpow_nonneg hL.le _)
    (Finset.prod_nonneg (by intro i hi; exact norm_nonneg _))
  exact parity_original_actual_cauchy_Wout_EV434
    (sourceOriginalLiteralDepth 20 L) L E V A band slot δ ξ rho J β
    hE hV hA hJ hBeta (by
      intro e he
      exact hAE band slot E δ ξ rho e)
end Green64Analytic.Parity

end

end

/-! ## FullPsiUnfilteredSigmaFibre -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- EXACT original full all-odd, *unfiltered* physical B' e,m',n
source fibre for a fixed real source (m,k). Both endpoints retain
literal Q/P/B509 physical support, e/n envelopes, no Pfree e gate,
and every natural multiplicity. This is stronger in index scope than
the pre-existing eta-active fibre identity and is an equality of
SIGNED COMPLEX sums for arbitrary W, not a norm comparison. -/
theorem parity_original_full_psi_unfiltered_fixed_mk_source_fibre_exact434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ)
    (W : ℕ → ℕ → ℕ → ℂ) :
    (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k,
      W e q.1 q.2) =
    ∑q∈parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta Y m K k,
      W q.1 q.2.1 q.2.2 := by
  classical
  simp [parityOriginalHistoricalUngatedFullOddKPhysicalEvents434,
    parityOriginalHistoricalKPrimeFibre434,
    parityOriginalHistoricalUngatedActualFixedMKSigmaSource434,
    Finset.sum_filter, Finset.sum_product,
    and_assoc, and_left_comm, and_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro mp hmp
  by_cases hk : parityOriginalHistoricalOffdiagK434 e m mp = k
  · simp [hk]
  · simp [hk]

/-- The REAL physical source also reindexes injectively to Parity's
positive Sigma (z,m',m), with full unfiltered odd e source and
no artificial η-gate, preserving arbitrary original signed atoms.
The inverse uses original shifted determinant uniqueness, not a
fibre-counting bound. -/
theorem parity_original_full_psi_unfiltered_fixed_mk_sigma_image_exact434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (W : (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k,
      W (parityOriginalHistoricalUngatedSourceToSigma434 m (e,q))) =
    ∑i∈(parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
      d L E V band slot delta Y m K k).image
        (parityOriginalHistoricalUngatedSourceToSigma434 m), W i := by
  have hIndex := parity_original_full_psi_unfiltered_fixed_mk_source_fibre_exact434
    d L E V band slot delta Y m K k
    (fun e mp n => W (parityOriginalHistoricalUngatedSourceToSigma434 m (e,(mp,n))))
  exact hIndex.trans (parity_original_ungated_actual_fixed_m_k_sigma_signed_reindex434
    d L E V band slot delta Y m K k hk W)
end Green64Analytic.Parity

end

end

/-! ## FullPsiUnfilteredGlobalSigma -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3600000

/-- On ANY genuine original full-odd e,m',n B509 physical event,
the actual nonzero signed k belongs to the literal quotient k-support.
No eta filter, P-free-e restriction or new support hypothesis is
inserted. -/
theorem parity_original_full_psi_unfiltered_event_in_k_support434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) k) :
    k∈parityOriginalHistoricalNonzeroKSupport434 e m K := by
  have hb := (Finset.mem_filter.mp hq).1
  have hprod := Finset.mem_product.mp hb
  have hmp := Finset.mem_filter.mp hprod.1
  have himage : k∈parityOriginalHistoricalKSupport434 e m K := by
    apply Finset.mem_image.mpr
    exact ⟨q.1,hmp.1,hmp.2⟩
  exact Finset.mem_filter.mpr ⟨himage,hk⟩

/-- Redundant original k gate on full unfiltered physical events.
The statement is a finite complex equality and holds for arbitrary
coefficients W; it is NOT norm monotonicity of complex subsums. -/
theorem parity_original_full_psi_unfiltered_k_gate_redundant434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K : Finset ℕ) (k : ℤ) (hk : k≠0)
    (W : (ℕ×ℕ) → ℂ) :
    (if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
      ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k, W q
     else 0) =
    ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) k, W q := by
  classical
  by_cases hmem : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
  · simp [hmem]
  · have hz : (∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k, W q)=0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact False.elim (hmem (parity_original_full_psi_unfiltered_event_in_k_support434
        d L E V band slot delta Y e m K k hk q hq))
    simp only [hmem,ite_false,hz]

/-- COMPLETE unfiltered physical original B509 global k,Z,e,m,m',n
complex source outer equals the genuine Parity Sigma image sum with no
SOURCE overcounting or ghost assumption. The (k,Z,z,m',m) coefficient
W can be the literal original full χ projector and Schwartz Fourier
phase; algebraic equality is proved BEFORE complex norm or spectral
cutoff. This does not yet establish equality of particular source
H0 coefficients with the B633 atom. -/
theorem parity_original_full_psi_unfiltered_global_kZ_sigma_image_exact434
    (d : ℕ) (L E V : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (KS : Finset ℤ) (ZS : Finset ℕ)
    (hKS : ∀k∈KS,k≠0)
    (W : ℤ → ℕ → (Σ z : ℕ, Σ mp : ℕ, ℕ) → ℂ) :
    (∑k∈KS,∑Z∈ZS,
      ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K
            (parityOriginalHistoricalFullNEnvelope434 V) k,
            W k Z (parityOriginalHistoricalUngatedSourceToSigma434 m (e,q))
        else 0) =
    ∑k∈KS,∑Z∈ZS,∑m∈K,
      ∑i∈(parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
        d L E V band slot delta Y m K k).image
          (parityOriginalHistoricalUngatedSourceToSigma434 m), W k Z i := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro Z hZ
  calc
    (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot delta Y e m K
            (parityOriginalHistoricalFullNEnvelope434 V) k,
            W k Z (parityOriginalHistoricalUngatedSourceToSigma434 m (e,q))
        else 0) =
      ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,∑m∈K,
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot delta Y e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k,
          W k Z (parityOriginalHistoricalUngatedSourceToSigma434 m (e,q)) := by
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro m hm
          exact parity_original_full_psi_unfiltered_k_gate_redundant434
            d L E V band slot delta Y e m K k (hKS k hk)
            (fun q => W k Z (parityOriginalHistoricalUngatedSourceToSigma434 m (e,q)))
    _ = ∑m∈K,∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot delta Y e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k,
          W k Z (parityOriginalHistoricalUngatedSourceToSigma434 m (e,q)) :=
            Finset.sum_comm
    _ = ∑m∈K,
        ∑i∈(parityOriginalHistoricalUngatedActualFixedMKSigmaSource434
          d L E V band slot delta Y m K k).image
          (parityOriginalHistoricalUngatedSourceToSigma434 m), W k Z i := by
          apply Finset.sum_congr rfl
          intro m hm
          exact parity_original_full_psi_unfiltered_fixed_mk_sigma_image_exact434
            d L E V band slot delta Y m K k (hKS k hk) (W k Z)
end Green64Analytic.Parity

end

end

/-! ## HistoricalCauchyMellinPolynomial -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- Exact source un-squaring of the real historical post-selected-e
Parity(4.7) Cauchy amplitude, at each fixed original Q allocation and
real xi,rho: it is a FINITE sum over u=m*n−2 of the genuine
source B590 signed e-first factor and the unaltered alpha_m beta_n.
No arbitrary independence between Q-labelled e/vStar; this uses
its previously proved dependent Pi splitting. -/
theorem parity_original_historical_Cauchy_eq_intrinsic_e_first_u_sum434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalCauchyAtDelta434 d L E band slot delta xi rho
      K J alpha beta signed Y =
    ∑u∈Finset.Ioc 0 Y,
      parityOriginalSignedIntrinsicEFirstAtU434
        d L E u signed band slot delta xi rho *
      (∑w∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha w.1*beta w.2) := by
  classical
  let U := Finset.Ioc 0 Y
  let P := parityOriginalReservedCartesianESupport434 d L band slot delta
  let Q := parityOriginalReservedCartesianVStarSupport434 d L band slot delta
  let A : ℕ → ℂ :=
    parityOriginalSelectedEGateMellinCoefficient434 d L E band slot delta xi rho
  let V : ℕ → ℕ → ℂ := fun e u =>
    ∑vStar∈Q,
      parityOriginalIntrinsicEVStarAtU434 d L E u signed
        band slot delta xi rho (e,vStar)
  let B : ℕ → ℂ := fun u =>
    ∑w∈parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha w.1*beta w.2
  have hHistoric :=
    (parity_original_historical_e_first_eq_actual_e_n_cauchy434
      d L E band slot delta xi rho K J alpha beta signed Y).symm
  have hWindow := parity_original_historical_AE_window_e_outer_bilinear_exact434
    d L E band slot delta xi rho signed Y K J alpha beta
  have hOne (u : ℕ) :
      parityOriginalSignedIntrinsicEFirstAtU434
        d L E u signed band slot delta xi rho =
      ∑e∈P,A e*V e u :=
    parity_original_signed_intrinsic_delta_e_outer_independent_vStar_support434
      d L E u signed band slot delta xi rho
  change parityOriginalHistoricalCauchyAtDelta434 d L E band slot delta xi rho
      K J alpha beta signed Y = ∑u∈U,
      parityOriginalSignedIntrinsicEFirstAtU434
        d L E u signed band slot delta xi rho*B u
  calc
    _ = ∑e∈P,A e*(∑u∈U,V e u*B u) := by
      rw [hHistoric,←hWindow]
    _ = ∑e∈P,∑u∈U,A e*(V e u*B u) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
    _ = ∑u∈U,∑e∈P,A e*(V e u*B u) := Finset.sum_comm
    _ = ∑u∈U,((∑e∈P,A e*V e u)*B u) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hOne u]

/-- The exact original selected-Q historical Cauchy amplitude is a
finite Mellin trigonometric polynomial with coefficient weights
independent of rho: exp(i*rho*log u) times TRUE original B590
selected/full skipped-Q source at rho=0. This identity requires the
original source depth and physical u>0. It is the missing interface
for joint rho/Q measurability and source-tail bounds. -/
theorem parity_original_historical_Cauchy_Mellin_polynomial434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    parityOriginalHistoricalCauchyAtDelta434 d L E band slot delta xi rho
      K J alpha beta signed Y =
    ∑u∈Finset.Ioc 0 Y,
      sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi *
      (∑w∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha w.1*beta w.2) := by
  rw [parity_original_historical_Cauchy_eq_intrinsic_e_first_u_sum434]
  apply Finset.sum_congr rfl
  intro u hu
  have hPos : 0<u := (Finset.mem_Ioc.mp hu).1
  rw [←parity_original_signed_fullQ_window_mellin_e_first_intrinsic434
    d L E hL hd u hPos.ne' signed band slot delta xi rho]
end Green64Analytic.Parity

end

end

/-! ## HistoricalMellinUniformMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- An EXPLICIT native arithmetic source majorant for the full
historical Parity(4.7) signed Bprime Cauchy term at each fixed original
Q Fourier tuple, with NO Mellin rho dependence. Every u=m*n−2
has its original selected Q B590 Fourier coefficient and actual
alpha_m beta_n, so the full 20! source multiplicity is kept.
This is not a claimed inverse-log saving; it is precisely what
must be paid against Schwartz tails. -/
def parityOriginalHistoricalBprimeMellinArithmeticMass434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) : ℝ :=
  ∑u∈Finset.Ioc 0 Y,
    ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
      d L E u signed band slot delta xi‖ *
    ‖∑w∈parityOriginalShiftTwoPositivePairFibre434 K J u,
      alpha w.1*beta w.2‖

/-- True native Bprime at EVERY rho bounded by its fixed original
Mellin arithmetic mass. This is a pointwise norm inequality from
finite-sum triangle, not an invalid signed-subsum comparison.
The only analytic fact is |u^(i rho)|=1, including u positive. -/
theorem parity_original_historical_Cauchy_mellin_uniform_arithmetic_mass434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    ‖parityOriginalHistoricalCauchyAtDelta434
      d L E band slot delta xi rho K J alpha beta signed Y‖ ≤
    parityOriginalHistoricalBprimeMellinArithmeticMass434
      d L E band slot delta xi K J alpha beta signed Y := by
  rw [parity_original_historical_Cauchy_Mellin_polynomial434
    d L E hL hd band slot delta xi rho K J alpha beta signed Y]
  unfold parityOriginalHistoricalBprimeMellinArithmeticMass434
  calc
    _ ≤ ∑u∈Finset.Ioc 0 Y,
        ‖sourceOriginalPureMellinPhase434 rho u *
          parityOriginalSignedFullQWindowAllGateFourierAtU434
            d L E u signed band slot delta xi *
          (∑w∈parityOriginalShiftTwoPositivePairFibre434 K J u,
            alpha w.1*beta w.2)‖ := norm_sum_le _ _
    _ = ∑u∈Finset.Ioc 0 Y,
        ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
          d L E u signed band slot delta xi‖ *
        ‖∑w∈parityOriginalShiftTwoPositivePairFibre434 K J u,
          alpha w.1*beta w.2‖ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [norm_mul,norm_mul,source_original_pure_mellin_phase_norm_one434]
      ring

/-- The source arithmetic mass is nonnegative, with no artificial
absolute value of an entire signed subset. -/
theorem parity_original_historical_Bprime_mellin_arithmetic_mass_nonneg434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    0≤parityOriginalHistoricalBprimeMellinArithmeticMass434
      d L E band slot delta xi K J alpha beta signed Y := by
  unfold parityOriginalHistoricalBprimeMellinArithmeticMass434
  positivity
end Green64Analytic.Parity

end

end

/-! ## HistoricalMellinTauMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Exact SOURCE Parity(4.7) full Q-label B590 arithmetic mass at a
fixed original ξ is controlled by the TRUE shifted divisor τ(u+2),
not an invented independent count of (m,n) fibres. The original
m*n=u+2 positive pair condition and the ORIGINAL K,J coefficients
are retained. This is a real bounded-coefficient arithmetic bridge
for the high Mellin Schwartz tail, not yet the source averaged
τ or Q gate integral needed for arbitrary inverse-log saving. -/
theorem parity_original_historical_Bprime_mellin_arithmetic_mass_le_tau434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) (A B : ℝ)
    (hA : 0≤A) (hB : 0≤B)
    (hAlpha : ∀m∈K, ‖alpha m‖≤A)
    (hBeta : ∀n∈J, ‖beta n‖≤B) :
    parityOriginalHistoricalBprimeMellinArithmeticMass434
      d L E band slot delta xi K J alpha beta signed Y ≤
    (A*B) * (∑u∈Finset.Ioc 0 Y,
      ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi‖ *
      ((u+2).divisors.card:ℝ)) := by
  unfold parityOriginalHistoricalBprimeMellinArithmeticMass434
  have hOne (u : ℕ) :
      ‖∑w∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha w.1*beta w.2‖ ≤ ((u+2).divisors.card:ℝ)*(A*B) := by
    have h := parity_original_shift_two_bilinear_fibre_norm_le_tau434
      K J u alpha beta A B hA hB hAlpha hBeta
    nlinarith [h]
  calc
    _ ≤ ∑u∈Finset.Ioc 0 Y,
      ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi‖ *
      (((u+2).divisors.card:ℝ)*(A*B)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hOne u) (norm_nonneg _)
    _ = (A*B) * (∑u∈Finset.Ioc 0 Y,
      ‖parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi‖ *
      ((u+2).divisors.card:ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring
end Green64Analytic.Parity

end

end

/-! ## OriginalPhysicalPsiFullSupport -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4700000

/-- TRUE SOURCE ψ-support completeness, for EVERY original actual
post-Cauchy B509 physical e,m,m',n,k,Z atom with nonzero original
eta_e(e/E)eta_n(n/V). If the genuine smooth ψ(z/2^j) is nonzero,
then the dyadic height 2^j belongs to the exact original physically
populated canonical Z union OR its immediately preceding half-dyad.
The assertion is source-sharp and avoids the disproved identification
of the entire smooth partition with one sharp binary cell. No
unnatural extra e P-free gate, artificial hard smooth masks, or
pointwise χ cancellation is asserted. -/
theorem parity_original_full_odd_physical_smooth_psi_full_neighbor_support434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ)
    (e m : ℕ) (k : ℤ) (Z j : ℕ) (q : ℕ×ℕ)
    (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K)
    (hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K)
    (hq : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k Z)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0)
    (hpsi : parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j) ≠ 0) :
    (2:ℕ)^j ∈ parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V hL band slot δ Y K) := by
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hL band slot δ Y K
  have hData := Finset.mem_filter.mp hq
  have hEvent : q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) k :=
    Finset.mem_filter.mpr ⟨hData.1,hData.2.1⟩
  have hZscale : parityOriginalHistoricalActualZDyadicScale434
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) = Z := hData.2.2.2
  have hCell : Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) k := by
    unfold parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨q,hEvent,?_⟩,⟨q,hq,hw⟩⟩
    exact hZscale
  have hInZG : Z∈ZG := by
    unfold ZG parityOriginalHistoricalFullOddOriginalZUnion434
    exact Finset.mem_biUnion.mpr ⟨e,he,
      Finset.mem_biUnion.mpr ⟨m,hm,
        Finset.mem_biUnion.mpr ⟨k,hk,hCell⟩⟩⟩
  have hOwn : parityOriginalHistoricalActualZDyadicScale434
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) ∈ ZG := by
    rw [hZscale]
    exact hInZG
  have hNeighbor := parity_original_actual_smooth_psi_nonzero_in_source_neighbor434
    ZG (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) j hOwn hpsi
  have hEq := parity_original_full_odd_actual_Z_union_smooth_neighbor_exact434
    d L E V hL band slot δ Y K
  dsimp only at hEq
  rw [hEq]
  exact hNeighbor
end Green64Analytic.Parity

end

end

/-! ## OriginalSelectedAEQFrequencyContinuous -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The genuine original selected-Q source phase, including all
historical delta-dependent frequencies and every repeated labelled
prime factor, is continuous in the whole N-dimensional Q Fourier
frequency. The selected prime tuple is fixed while varying xi. -/
theorem parity_original_actual_selected_e_phase_Q_continuous434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s : Fin n → ℝ) (δ : Fin n → Bool)
    (a : paritySourceQSelected434 n Q δ) :
    Continuous (fun ξ : Fin n → ℝ =>
      paritySourceQSelectedFourierPhase434 s ξ δ a) := by
  classical
  unfold paritySourceQSelectedFourierPhase434
  apply continuous_finsetProd
  intro i hi
  fun_prop

/-- True original full selected integer e SOURCE endpoint fibre is
continuous. It is an exact finite sum over all labelled selected-Q
prime tuples, never an arbitrary surrogate measure or a selected
hard allocation mask inserted after Q-Fourier truncation. -/
theorem parity_original_actual_selected_e_fibre_Q_continuous434
    {n : ℕ} {Q : Fin n → Finset ℕ}
    (s : Fin n → ℝ) (δ : Fin n → Bool) (e : ℕ) :
    Continuous (fun ξ : Fin n → ℝ =>
      paritySourceQSelectedFourierEFibre434 (Q:=Q) δ s ξ e) := by
  classical
  unfold paritySourceQSelectedFourierEFibre434 sourceEndpointFibre
  apply continuous_finsetSum
  intro a ha
  exact parity_original_actual_selected_e_phase_Q_continuous434 (Q:=Q) s δ a

/-- Exact original selected-e Fourier factor, with native f0/f1
Schwartz transforms and log(E) character, is continuous in all Q
frequencies. This is SOURCE a_e, not the post-Cauchy physical B633
frequency variation and not a second external Q-gate. -/
theorem parity_original_actual_selected_e_gate_Q_continuous434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e : ℕ) :
    Continuous (fun ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalSelectedEGateFourierCoefficient434
        d L E band slot δ ξ e) := by
  classical
  let s := sourceActualSortedFrequencyScales 20 d L band slot
  let Q := sourceActualSortedQ 20 d L band slot
  have hFibre := parity_original_actual_selected_e_fibre_Q_continuous434
    (Q:=Q) s δ e
  unfold parityOriginalSelectedEGateFourierCoefficient434
  have hProduct : Continuous (fun ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      ∏ i : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length,
        (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) := by
    apply continuous_finsetProd
    intro i hi
    exact (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)).continuous.comp
      (continuous_apply i)
  have hChar : Continuous (fun ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      (((Real.fourierChar (Real.log E * (∑ i, ξ i/s i)):Circle):ℂ))) := by
    fun_prop
  exact (hProduct.mul hChar).mul hFibre

/-- The exact historical source a_e(e) with its original E-window
and one Mellin phase, used INSIDE Parity (4.10) Cauchy Wout, is
continuous in each original Q Fourier variable. -/
theorem parity_original_historical_window_AE_Q_continuous434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (rho : ℝ) (e : ℕ) :
    Continuous (fun ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalHistoricalWindowAE434 d L E band slot δ ξ rho e) := by
  unfold parityOriginalHistoricalWindowAE434
  by_cases h : parityOriginalHistoricalEWindow434 L E e
  · simp only [h,ite_true]
    change Continuous (fun ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      sourceOriginalPureMellinPhase434 rho e *
        parityOriginalSelectedEGateFourierCoefficient434 d L E band slot δ ξ e)
    exact continuous_const.mul
      (parity_original_actual_selected_e_gate_Q_continuous434 d L E band slot δ e)
  · simpa only [h,ite_false] using
      (continuous_const : Continuous (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ => (0:ℂ)))
end Green64Analytic.Parity

end

end

/-! ## B590SourceQContinuous -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The literal original B590 complete f0/f1 Schwartz Fourier gate
of a SINGLE fully labelled Q prime tuple is continuous jointly in
ALL its original N frequency coordinates. The Q allocation residual
and every selected/skipped prime factor are the source parameters;
this is NOT a new external gate. -/
theorem parity_original_actual_B590_fullQ_gate_continuous434
    {N : ℕ} (E : ℝ) (s : Fin N → ℝ)
    (δ : Fin N → Bool) (p : Fin N → ℕ) :
    Continuous (fun ξ : Fin N → ℝ =>
      parityOriginalB590AllGateFourierIntegrand434 E s δ p ξ) := by
  classical
  unfold parityOriginalB590AllGateFourierIntegrand434
  apply continuous_finsetProd
  intro i hi
  have hF : Continuous (fun ξ : Fin N → ℝ =>
      (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)) (ξ i)) := by
    exact (𝓕 (sourceBufferedGate 20 (δ i)) : 𝓢(ℝ,ℂ)).continuous.comp
      (continuous_apply i)
  have hPhase : Continuous (fun ξ : Fin N → ℝ =>
      Complex.exp (((2*Real.pi*(ξ i / s i) *
        (parityOriginalQAllocationResidual434 E δ p i -
          Real.log (p i : ℝ)):ℝ):ℂ)*Complex.I)) := by
    fun_prop
  exact hF.mul hPhase

/-- The original SOURCE 20!-labelled B590 e-window Fourier fibre
at FIXED positive physical u is continuous in all original Q
frequency variables, with its full dependence on selected allocation
and skipped prime factors. Proof is a finite sum of literal Schwartz
gates; there is no hypothesis about arbitrary cofactor alpha. -/
theorem parity_original_actual_signed_window_fullQ_fibre_continuous434
    (d : ℕ) (L E : ℝ) (u : ℕ) (signed : Bool)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool) :
    Continuous (fun ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot δ ξ) := by
  classical
  unfold parityOriginalSignedFullQWindowAllGateFourierAtU434
  apply continuous_finsetSum
  intro f hf
  by_cases hE : parityOriginalHistoricalEWindow434 L E
      (paritySourceOrderedAllocatedE434 δ
        (parityActualSourceRemainingFullQTuple434 d L band slot f))
  · simp only [hE,ite_true]
    have hG := parity_original_actual_B590_fullQ_gate_continuous434 E
      (sourceActualSortedFrequencyScales 20 d L band slot)
      δ (fun i => (parityActualSourceRemainingFullQTuple434
        d L band slot f i).val)
    have hC : Continuous (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
          ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ)) :=
      continuous_const
    have hEq :
        ((fun _ : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
              ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ)) *
          (fun ξ => parityOriginalB590AllGateFourierIntegrand434 E
            (sourceActualSortedFrequencyScales 20 d L band slot)
            δ (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot f i).val) ξ)) =
        (fun ξ => ((parityActualOriginalSignedFullTupleWeight434 d L u signed f : ℝ):ℂ) *
          parityOriginalB590AllGateFourierIntegrand434 E
            (sourceActualSortedFrequencyScales 20 d L band slot)
            δ (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot f i).val) ξ) := by
      funext ξ
      rfl
    rw [←hEq]
    exact hC.mul hG
  · simpa only [hE,ite_false] using
      (continuous_const : Continuous (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ => (0:ℂ)))
end Green64Analytic.Parity

end

end

/-! ## HistoricalCauchyQFrequencyContinuous -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- At any fixed REAL original Mellin rho, the original historical
Parity(4.7) a_e/W1 signed Cauchy amplitude is continuous in ALL its
original N-dimensional Q Fourier frequency variables. Unlike a
costly joint-product continuity elaboration, this directly uses
its exact native finite-u Mellin polynomial (each rho phase
constant in Q) and the already proven true full B590 gate
Q-continuity. No source alpha/beta, u or reserved Q multiplicity
is changed, no L-dependent measurability axiom is added. -/
theorem parity_original_historical_Cauchy_Q_frequency_continuous434
    (d : ℕ) (L E : ℝ) (hL : 0<L)
    (hd : d=sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (rho : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) (Y : ℕ) :
    Continuous (fun xi : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot delta xi rho K J alpha beta signed Y) := by
  classical
  let n := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  have hEq :
    (fun xi : Fin n → ℝ =>
      parityOriginalHistoricalCauchyAtDelta434
        d L E band slot delta xi rho K J alpha beta signed Y) =
    (fun xi => ∑u∈Finset.Ioc 0 Y,
      sourceOriginalPureMellinPhase434 rho u *
      parityOriginalSignedFullQWindowAllGateFourierAtU434
        d L E u signed band slot delta xi *
      (∑w∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha w.1*beta w.2)) := by
    funext xi
    exact parity_original_historical_Cauchy_Mellin_polynomial434
      d L E hL hd band slot delta xi rho K J alpha beta signed Y
  rw [hEq]
  apply continuous_finsetSum
  intro u hu
  exact (continuous_const.mul
    (parity_original_actual_signed_window_fullQ_fibre_continuous434
      d L E u signed band slot delta)).mul_const _
end Green64Analytic.Parity

end

end

/-! ## OriginalBprimeQFrequencyContinuous -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Original historical QSkip H0, with literal ordered skipped prime
factorial convolution and reserved Q prime range, is jointly
continuous in the original full-dimensional Q Fourier frequency.
No artificial post-Cauchy Fourier kernel is substituted. -/
theorem parity_original_intrinsic_H0_Q_frequency_continuous434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (sigma : ℝ) (v : ℕ) :
    Continuous (fun ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalIntrinsicH434 d L band slot δ ξ sigma v) := by
  classical
  unfold parityOriginalIntrinsicH434 sourceEndpointFibre
  apply continuous_finsetSum
  intro a ha
  have hResidual := parity_original_actual_native_prime_core_residual_continuous434
    20 d L band slot δ (∅ : Finset ℕ) (fun _ => (0:ℂ)) 1
    (1 : DirichletCharacter ℂ 1) 0 0 a.2
  have hR : Continuous (fun ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalIntrinsicResidual434 d L band slot δ ξ a.2) := by
    have hEq :
        (fun ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
          parityOriginalIntrinsicResidual434 d L band slot δ ξ a.2) =
        (fun ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
          (sourceNativePrimeCore 20 d L band slot δ ξ
            (∅ : Finset ℕ) (fun _ => (0:ℂ)) 1
            (1 : DirichletCharacter ℂ 1) 0 0).residual a.2) := by
      funext ξ
      exact (parity_original_native_B509_residual_is_intrinsic434
        d L band slot δ ξ (∅ : Finset ℕ) (fun _ => (0:ℂ)) 1
        (1 : DirichletCharacter ℂ 1) 0 0 a.2).symm
    rw [hEq]
    exact hResidual
  exact continuous_const.mul hR

/-- The source reserved prime-slot H0 is the only original Q-frequency
dependence of the ungated physical signed a_v(v) after fixing e,v.
Mellin rho, W1, the parity epsilon, and all natural factor labels
are fixed; full QSkip history is unchanged. -/
theorem parity_original_ungated_AV_Q_frequency_continuous434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (rho : ℝ) (signed : Bool) (vStar v : ℕ) :
    Continuous (fun ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalIntrinsicSignedAV434 d L band slot δ ξ 0 rho signed vStar v) := by
  unfold parityOriginalIntrinsicSignedAV434
  exact (continuous_const.mul continuous_const).mul
    (parity_original_intrinsic_H0_Q_frequency_continuous434
      d L band slot δ 0 vStar)

/-- Original un-gated Cauchy endpoint a_v((m*n-2)/e), without the
incorrect hard u<=2x support or a P-free e assumption, is
continuous in the complete Q Fourier frequency vector. Every u,
vStar and ordinary/P-part arithmetic selection stays in its original
finite SOURCE support, and the actual QSkip H0 varies continuously. -/
theorem parity_original_ungated_Cauchy_physical_Q_frequency_continuous434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (rho : ℝ) (signed : Bool) (e n m : ℕ) :
    Continuous (fun ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
        d L band slot δ ξ rho signed e n m) := by
  classical
  unfold parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
    parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
  apply continuous_finsetSum
  intro u hu
  by_cases hMN : 0 < m ∧ 0 < n ∧ m*n = u+2
  · simp only [hMN,ite_true]
    apply continuous_finsetSum
    intro vStar hvStar
    unfold parityOriginalHistoricalUngatedEVStarAtU434
    change Continuous (fun ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      if e ∣ u ∧ vStar = sourceOriginalOrdinaryPart
        ((sourceOriginalPAllGroupIndices 20 L).attach.biUnion
          (sourceOriginalPAllActualBands 20 L)) (u/e)
      then parityOriginalIntrinsicSignedAV434
        d L band slot δ ξ 0 rho signed vStar (u/e)
      else (0:ℂ))
    by_cases hEV : e ∣ u ∧ vStar = sourceOriginalOrdinaryPart
      ((sourceOriginalPAllGroupIndices 20 L).attach.biUnion
        (sourceOriginalPAllActualBands 20 L)) (u/e)
    · simpa [hEV] using
        (parity_original_ungated_AV_Q_frequency_continuous434
          d L band slot δ rho signed vStar (u/e))
    · simpa only [hEV,ite_false] using
        (continuous_const : Continuous (fun _ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → ℝ => (0:ℂ)))
  · simpa only [hMN,ite_false] using
      (continuous_const : Continuous (fun _ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ => (0:ℂ)))

/-- The LITERAL pre-Cauchy Parity (4.7) Bprime a_e(e) beta_n times
original ungated a_v physical source is continuous as a function of
ALL Q-allocation Fourier frequencies xi. Crucially the selected-e
f0/f1 gate already lives in a_e: this theorem does NOT attach a
second gate. It supplies honest strong measurability required for
the actual external high-dimensional Fourier box integral. -/
theorem parity_original_capfree_Bprime_Q_frequency_continuous434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (rho : ℝ) (K J : Finset ℕ) (alpha beta : ℕ → ℂ)
    (signed : Bool) :
    Continuous (fun ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
        d L E band slot δ ξ rho K J alpha beta signed) := by
  classical
  unfold parityOriginalHistoricalUngatedCauchyAtDeltaNoUCap434
  apply continuous_finsetSum
  intro e he
  apply continuous_finsetSum
  intro n hn
  have hAE := parity_original_historical_window_AE_Q_continuous434
    d L E band slot δ rho e
  have hPhysical : Continuous (fun ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ =>
      ∑m∈K,alpha m*parityOriginalHistoricalUngatedCauchyPhysicalNoUCap434
        d L band slot δ ξ rho signed e n m) := by
    apply continuous_finsetSum
    intro m hm
    exact continuous_const.mul
      (parity_original_ungated_Cauchy_physical_Q_frequency_continuous434
        d L band slot δ rho signed e n m)
  exact (hAE.mul_const (beta n)).mul hPhysical
end Green64Analytic.Parity

end

end

/-! ## OriginalTypeIITripleSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The exact *original* Parity (4.2) shifted h=-2 finite triple sum,
not its post-Cauchy Q/Mellin model: u>=1, mn=u+2, full original
r0=20 Q/P candidate weight including Ω multiplicities, and
explicit α_m β_n.  The finite cutoff Y need only exceed the
support of the original Psi; no prime/rough or coefficient
assumption has been inserted into the definition. -/
def parityOriginalShiftTwoOriginalTypeIITripleSource434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ z ∈ K.product J,
    ∑ u ∈ Finset.Ioc 0 Y,
      if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
        (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
          (sourceOriginalPAllActualBands 20 L) u *
          Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
          (alpha z.1*beta z.2))
      else 0

/-- Exact finite Fubini SOURCE identity from the original u-first
shifted bilinear carrier to Parity (4.2)'s m,n,u triple sum. The
apparently extra u=0 source term vanishes because the physical
smooth Ψ is supported in [1,2]. No local/Q/FFT approximation,
positive-mass estimate or norm inequality is used. -/
theorem parity_original_shift_two_actual_source_eq_TypeII_triple434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearSource434 d L Psi K J alpha beta Y =
      parityOriginalShiftTwoOriginalTypeIITripleSource434
        d L Psi K J alpha beta Y := by
  classical
  let A : ℕ → ℂ := fun u =>
    ((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u *
      Psi ((u:ℝ)/Real.exp L) : ℝ) : ℂ)
  let f : (ℕ×ℕ) → ℕ → ℂ := fun z u =>
    if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
      A u*(alpha z.1*beta z.2)
    else 0
  have hPsi0 : Psi 0=0 := by
    by_contra hh
    have hmem : (0:ℝ) ∈ Function.support Psi := hh
    have hRange := Set.mem_Icc.mp (hPsiSet hmem)
    norm_num at hRange
  have hA0 : A 0=0 := by simp [A,hPsi0]
  have hFibre (u : ℕ) :
      A u * (∑ z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha z.1*beta z.2) =
        ∑ z ∈ K.product J, f z u := by
    unfold parityOriginalShiftTwoPositivePairFibre434
    rw [Finset.mul_sum,Finset.sum_filter]
  change (∑u∈Finset.range (Y+1),
      A u*(∑z∈parityOriginalShiftTwoPositivePairFibre434 K J u,
        alpha z.1*beta z.2)) =
    ∑z∈K.product J,∑u∈Finset.Ioc 0 Y,f z u
  calc
    _ = ∑u∈Finset.range (Y+1),∑z∈K.product J,f z u := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hFibre u
    _ = ∑z∈K.product J,∑u∈Finset.range (Y+1),f z u :=
      Finset.sum_comm
    _ = ∑z∈K.product J,∑u∈Finset.Ioc 0 Y,f z u := by
      apply Finset.sum_congr rfl
      intro z hz
      have hZero : f z 0=0 := by simp [f,hA0]
      induction Y with
      | zero => simp [hZero]
      | succ Y ih =>
        rw [Finset.sum_range_succ]
        rw [Finset.sum_Ioc_succ_top (Nat.zero_le Y)]
        rw [ih]
end Green64Analytic.Parity

end

end

/-! ## PsiMellinHistoricalCauchyExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The exact ORIGINAL historical Parity(4.7) source AFTER smoothing
with Psi(u/x) and Mellin inversion, at fixed N-dimensional Q frequency
xi. Its Mellin rho is the real 2*pi*s and the selected-Q Fourier
branch appears EXACTLY ONCE, INSIDE original a_e(e). The original
finite u bound Y is retained verbatim, not silently replaced by the
new capfree Ybox. Both signed epsilon branches are respected. -/
def parityOriginalActualHistoricalPsiMellinCauchyAtXi434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) : ℂ :=
  ∫ s : ℝ, parityOriginalSignedWindowPsiMellinKernel434
    L Psi hSmooth hSupport s *
    (∑δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool,
        parityOriginalHistoricalCauchyAtDelta434
          d L E band slot δ ξ (2*Real.pi*s) K J α β signed Y)

/-- A TRUE complex identity, NOT an inequality: original historical
source e-first (u, e, vStar, m, n) is precisely the e,n-outer
Parity(4.10) physical Cauchy amplitude at EACH Mellin s and Q xi,
using native source finite u/m/n reindex; all QSkip factorials,
selected a_e and independent a_v are unchanged. -/
theorem parity_original_actual_historical_Psi_Bprime_atXi_eq_Cauchy_Mellin434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) :
    parityOriginalSignedHistoricalAEPsiBprimeAtXi434 d L E band slot ξ
      Psi hSmooth hSupport K J α β signed Y =
    parityOriginalActualHistoricalPsiMellinCauchyAtXi434 d L E band slot ξ
      Psi hSmooth hSupport K J α β signed Y := by
  unfold parityOriginalSignedHistoricalAEPsiBprimeAtXi434
    parityOriginalActualHistoricalPsiMellinCauchyAtXi434
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  apply Finset.sum_congr rfl
  intro δ hδ
  exact parity_original_historical_e_first_eq_actual_e_n_cauchy434
    d L E band slot δ ξ (2*Real.pi*s) K J α β signed Y

/-- The exact original full N-dimensional Q Fourier box of the
historical Mellin-Cauchy source, with the REAL original restricted
Lebesgue measure in EVERY coordinate. It is not yet a truncation of
the Mellin s integral and not yet the cap-free Bprime model. -/
def parityOriginalActualHistoricalPsiMellinCauchyQBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) : ℂ :=
  ∫ ξ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → ℝ,
      parityOriginalActualHistoricalPsiMellinCauchyAtXi434
        d L E band slot ξ Psi hSmooth hSupport K J α β signed Y
    ∂(Measure.pi (fun _ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length =>
      (volume : Measure ℝ).restrict (Set.Icc (-T) T)))

/-- Original pre-Cauchy correctly sourced signed full-Q Bprime from
historic a_e(e)/a_v(v) is EXACTLY the full Q-box Mellin-Cauchy model.
Each original F0/F1 assignment is summed BEFORE the frequency box.
No duplicated Q-gate, no post-Cauchy u cap extension, and no sign
or alpha restriction is made. -/
theorem parity_original_actual_historical_Psi_Bprime_QBox_eq_Cauchy_Mellin434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    parityOriginalSignedHistoricalAEPsiBprime434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T =
    parityOriginalActualHistoricalPsiMellinCauchyQBox434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T := by
  unfold parityOriginalSignedHistoricalAEPsiBprime434
    parityOriginalActualHistoricalPsiMellinCauchyQBox434
  apply integral_congr_ae
  filter_upwards [] with ξ
  exact parity_original_actual_historical_Psi_Bprime_atXi_eq_Cauchy_Mellin434
    d L E band slot ξ Psi hSmooth hSupport K J α β signed Y

/-- Exact identity from original fully source-Cartesian B' before
any Cauchy square to the same historical e/n Cauchy Q-box. Uses
proven selected-Q Pi split and original e-window source equality. -/
theorem parity_original_actual_cartesian_Psi_Bprime_QBox_eq_Cauchy_Mellin434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (signed : Bool) (Y : ℕ) (T : ℝ) :
    parityOriginalSignedCartesianPsiBprime434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T =
    parityOriginalActualHistoricalPsiMellinCauchyQBox434 d L E band slot
      Psi hSmooth hSupport K J α β signed Y T := by
  rw [parity_original_signed_cartesian_Bprime_eq_historical_AE434]
  exact parity_original_actual_historical_Psi_Bprime_QBox_eq_Cauchy_Mellin434
    d L E band slot Psi hSmooth hSupport K J α β signed Y T
end Green64Analytic.Parity

end

end

/-! ## PsiMellinHistoricalCauchyAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- REAL ORIGINAL r20 signed h=-2 source pre-Cauchy integration:
full actual original 20! source alpha_m beta_n signed sum with Psi(u/x),
reserved slot and complete original B590 Fourier allocation is
O_A(exp(L)L^-A) close to the exact HISTORICAL e,n-outer Cauchy
integral over actual real 2*pi*s Mellin and full N-dimensional Q
Fourier BOX. All original u<=floor(2expL), source 2pi phases,
original a_e(e), H0, W1, epsilon=1/E and the distinct signed branches
are literal. No source u cap enlargement is claimed: its transport
into the capfree Bprime Ybox=ceil(6UV) is the NEXT open analytic bridge
and must correctly use Psi after Mellin integration. -/
theorem parity_eventually_original_signed_source_to_historical_Psi_Mellin_Cauchy_QBox_all_log434
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
        parityOriginalActualHistoricalPsiMellinCauchyQBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi hSmooth (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
          K J α β signed ⌊2*Real.exp L⌋₊ L‖ ≤
        4*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_signed_source_to_cartesian_Psi_Bprime_all_log434
    betaP A hbetaP jQ hBand] with L hOld
  refine ⟨hOld.1,hOld.2.1,?_⟩
  intro band hReserved E hElo hEhi Psi hSupport hSmooth
    hPsiPos hPsiLe slot K J alpha betaSeq Acoef Bcoef
    hAcoef hBcoef hAlpha hBeta signed
  have hBound := hOld.2.2 band hReserved E hElo hEhi Psi hSupport
    hSmooth hPsiPos hPsiLe slot K J alpha betaSeq Acoef Bcoef
    hAcoef hBcoef hAlpha hBeta signed
  have hEq := parity_original_actual_cartesian_Psi_Bprime_QBox_eq_Cauchy_Mellin434
    (sourceOriginalLiteralDepth 20 L) L E band slot Psi hSmooth
    (parity_original_Psi_window_to_Schwartz_support434 Psi hSupport)
    K J alpha betaSeq signed ⌊2*Real.exp L⌋₊ L
  rw [hEq] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## PsiMellinKernelL1Exact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The true original Parity Ψ Mellin kernel, with original 2πs phase
exp(-2π i s log(exp L)), has EXACTLY the L1 density of the Fourier
transform of the original log-cutoff Schwartz function. In particular
its real Mellin L1 cost is independent of L and does not grow with
the number of reserved Q labels. No finite-s restriction is imposed. -/
theorem parity_original_true_Psi_Mellin_kernel_norm_exact434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (s : ℝ) :
    ‖parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s‖ =
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖ := by
  unfold parityOriginalSignedWindowPsiMellinKernel434
  rw [norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]

/-- The ORIGINAL Ψ-Mellin Fourier kernel itself is Lebesgue integrable
for every original L, without imposing `rho` cutoffs or inventing
absolute summability of the physical Bprime coefficient. -/
theorem parity_original_true_Psi_Mellin_kernel_integrable434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    Integrable (parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport) := by
  let f := (𝓕 (parityOriginalLogCutoff434
    (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ))
  have hMeas : AEStronglyMeasurable
      (parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport) := by
    unfold parityOriginalSignedWindowPsiMellinKernel434
    exact (f.continuous.mul (by fun_prop)).aestronglyMeasurable
  apply f.integrable.mono hMeas
  filter_upwards [] with s
  exact (parity_original_true_Psi_Mellin_kernel_norm_exact434
    L Psi hSmooth hSupport s).le

/-- Exact total positive Ψ Mellin variation is the fixed Schwartz
Fourier L1 mass, rather than an L-dependent f0/f1 gate mass. The Q
allocation variation remains a separate factor and must not be paid
twice when applying actual per-Q-frequency Parity (4.17) savings. -/
theorem parity_original_true_Psi_Mellin_kernel_L1_mass_exact434
    (L : ℝ) (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64) :
    (∫s : ℝ,‖parityOriginalSignedWindowPsiMellinKernel434 L Psi hSmooth hSupport s‖) =
    ∫s : ℝ,‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s‖ := by
  apply integral_congr_ae
  filter_upwards [] with s
  exact parity_original_true_Psi_Mellin_kernel_norm_exact434
    L Psi hSmooth hSupport s
end Green64Analytic.Parity

end

end

