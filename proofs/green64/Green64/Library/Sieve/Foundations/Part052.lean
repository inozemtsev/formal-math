module

public import Green64.Library.Sieve.Foundations.Part044
public import Green64.Library.Sieve.Foundations.Part051
public import Green64.Library.Sieve.Foundations.Part049
public import Green64.Library.Sieve.Foundations.Part050
public import Green64.Library.Sieve.Foundations.Part045
public import Green64.Library.Sieve.Foundations.Part004
public import Green64.Library.Sieve.Foundations.Part007
public import Green64.Library.Sieve.Foundations.Part008

@[expose] public section

/-!
# Sieve / Foundations / Part052

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## BothParityFullCellProxyAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Actual Parity (1.2) parity weights, BOTH signs, with the complete original
Q/P source and whole-cell sharp-sharp to proxy-proxy replacement. The two
signed estimates are instantiated, not assumed. One analytic reserved
band and one slot suffice; they are not extra source families. The SAME
H,J,B,S works for both signs, both replacement steps, and both Boolean test
types at this fixed gamma. The true nonsmooth second-step factor-two
cost is retained. The actual external sieve/bin families and positive
source mass are not asserted here. -/
theorem parity_eventually_original_both_parity_two_fullcell_proxy_anylog434
    (jQ : ℕ) (goal target C0 beta betaP bstar gamma K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hce : e≤2*c) (hExpE : (e:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (prime secondPrime : Bool) (rho : ℝ), rho=1 ∨ rho=(-1) →
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalParityBilinearSource434 d L rho Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellSharpTest434 prime L gamma a b)
             (parityOriginalActualFullCellSharpTest434 secondPrime L gamma c e)
             Y -
            parityOriginalParityBilinearSource434 d L rho Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
             (parityOriginalActualFullCellProxyBeta434 secondPrime L S gamma c e)
             Y‖ ≤
            3*(1+2/Real.log 2)^2*Bound := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_signed_two_fullcell_proxy_shared_parameters_anylog434
      jQ goal target C0 beta betaP bstar gamma K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hgamma hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  filter_upwards [hSource] with L hSourceL
  rcases hSourceL with ⟨hBig,h128,h24,hFamily,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFamily,hReserved,?_⟩
  intro a b c e Y ha hc hab hExpB hce hExpE hY prime secondPrime rho hSigns
  let band : Fin (sourceOriginalLiteralDepth 20 L+1) :=
    ⟨jQ,Nat.lt_succ_of_le hReserved⟩
  have hFalse := hRest h128 hFamily a b c e Y ha hc hab hExpB hce hExpE hY
    band rfl (0:Fin 20) prime secondPrime false
  have hTrue := hRest h128 hFamily a b c e Y ha hc hab hExpB hce hExpE hY
    band rfl (0:Fin 20) prime secondPrime true
  have hLpos : 0<L := by linarith
  have hRho : |rho|≤1 := by
    rcases hSigns with rfl | rfl <;> norm_num
  exact parity_original_parity_replacement_norm_le434
    (sourceOriginalLiteralDepth 20 L) L rho hLpos hRho
    Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullCellSharpTest434 prime L gamma a b)
    (parityOriginalActualFullCellSharpTest434 secondPrime L gamma c e)
    (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
    (parityOriginalActualFullCellProxyBeta434 secondPrime L S gamma c e)
    Y _ hFalse hTrue
end Green64Analytic.Parity

end

end

/-! ## SourceD230VsPrimeMass221 -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Pinned Parity §7.3 error precision D*=230, all physically
attained quarter factor dyads O(L²), and the fixed 160 actual
Boolean/slot/signed cases together leave SIX powers of L over the
original positive mass threshold Xrho>=c0 exp(L)L^-221.
This is a numeric ledger, NOT a claim that the external sieve
family equals the 160 signed source nor that its per-source bound
is established for every external test. -/
theorem parity_eventually_original_source_D230_160_quarter_vs_Xrho221434
    (C c0 : ℝ) (hC : 0≤C) (hc0 : 0<c0) :
    ∀ᶠ L : ℝ in atTop,
      160*C *
      (((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1)*
         (Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1):ℕ):ℝ) *
      Real.exp L * L^(-(230:ℝ)) ≤
      c0*Real.exp L*L^(-(222:ℝ)) := by
  let D : ℝ := (1+2/Real.log 2)^2
  have hD : 0≤D := sq_nonneg _
  filter_upwards [eventually_ge_atTop (max 8 (160*C*D/c0))] with L hLarge
  have h8 : 8≤L := (le_max_left _ _).trans hLarge
  have hLp : 0<L := by linarith
  have hOne : 1≤L := by linarith
  have hCoef : 160*C*D≤ c0*L := by
    have hh := (le_max_right (8:ℝ) (160*C*D/c0)).trans hLarge
    have hp := (div_le_iff₀ hc0).mp hh
    nlinarith [hp]
  have hPowSix : L≤L^(6:ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hOne
      (by norm_num : (1:ℝ)≤6)
    simpa using hh
  have hCoefSix : 160*C*D≤ c0*L^(6:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hPowSix hc0.le,hCoef]
  have hLog := parity_original_actual_Y0_quarter_log_sq_le_L_sq434 L h8
  have hMinus : L^(2:ℕ)*L^(-(230:ℝ)) = L^(-(228:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hLp]
    congr 1
    ring
  have hSix : L^(6:ℝ)*L^(-(228:ℝ))=L^(-(222:ℝ)) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  have hNonneg : 0≤160*C*Real.exp L*L^(-(230:ℝ)) := by positivity
  have hBound :
      160*C*D*L^(-(228:ℝ)) ≤ c0*L^(-(222:ℝ)) := by
    calc
      _ ≤ (c0*L^(6:ℝ))*L^(-(228:ℝ)) :=
        mul_le_mul_of_nonneg_right hCoefSix (by positivity)
      _ = c0*L^(-(222:ℝ)) := by rw [mul_assoc,hSix]
  calc
    _ ≤ 160*C*(D*L^2)*Real.exp L*L^(-(230:ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left hLog
        (by positivity : 0≤160*C*Real.exp L*L^(-(230:ℝ)))
      nlinarith [hh]
    _ = (160*C*D)*(L^2*L^(-(230:ℝ)))*Real.exp L := by ring
    _ = (160*C*D*L^(-(228:ℝ)))*Real.exp L := by rw [hMinus]
    _ ≤ (c0*L^(-(222:ℝ)))*Real.exp L :=
      mul_le_mul_of_nonneg_right hBound (Real.exp_pos L).le
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## UnbalancedActualDyadExponentWindow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4400000

/-- Source Parity §7.3 unbalanced physical Psi-active dyads have
BOTH factor scales in the true TypeII window with bstar=b1/3.
The original literal upper 4 exp((1-b1)L) on m, rather than an
unproved x^(1-b1) bound, is paid by exponent slack 2b1/3 before L.
The binary scale downrounding is paid by exp((b1/3)L)>=2.
This is uniform for all actually attained pairs and contains no
hypothetical independent dyad labels or family counts. -/
theorem parity_eventually_original_unbalanced_active_dyads_exponent_window434
    (b1 kappa : ℝ) (hb1 : 0<b1)
    (hkappa : 0≤kappa) (hBand : b1≤(1/2:ℝ)-kappa)
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (K J : Finset ℕ) (Y : ℕ) (scale : ℕ×ℕ),
        scale ∈ parityOriginalActualTypeIIDyadicPairScales434
          (parityOriginalUnbalancedActivePhysicalPairs434
            L b1 kappa Psi K J Y) →
        Real.exp ((b1/3)*L) ≤ (scale.1:ℝ) ∧
        Real.exp ((b1/3)*L) ≤ (scale.2:ℝ) ∧
        (scale.1:ℝ) ≤ Real.exp ((1-b1/3)*L) ∧
        (scale.2:ℝ) ≤ Real.exp ((1-b1/3)*L) := by
  have hbthird : (0:ℝ)<b1/3 := by positivity
  have hGap : (0:ℝ)<2*b1/3 := by positivity
  let threshold := max (Real.log 2/(b1/3)) (Real.log 4/(2*b1/3))
  filter_upwards [eventually_ge_atTop (max threshold 0)] with L hLarge
  have hL : 0≤L := (le_max_right _ _).trans hLarge
  have h2 : (2:ℝ) ≤ Real.exp ((b1/3)*L) := by
    have hBound : Real.log 2/(b1/3) ≤ L :=
      (le_max_left _ _).trans ((le_max_left _ _).trans hLarge)
    have hh : Real.log 2 ≤ (b1/3)*L := by
      have h := (div_le_iff₀ hbthird).mp hBound
      nlinarith [h]
    have h := Real.exp_le_exp.mpr hh
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using h
  have h4 : (4:ℝ) ≤ Real.exp ((2*b1/3)*L) := by
    have hBound : Real.log 4/(2*b1/3) ≤ L :=
      (le_max_right _ _).trans ((le_max_left _ _).trans hLarge)
    have hh : Real.log 4 ≤ (2*b1/3)*L := by
      have h := (div_le_iff₀ hGap).mp hBound
      nlinarith [h]
    have h := Real.exp_le_exp.mpr hh
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<4)] using h
  intro K J Y scale hs
  obtain ⟨z,hz,hScale⟩ := Finset.mem_image.mp hs
  have hAct : z ∈ parityOriginalUnbalancedActivePhysicalPairs434
      L b1 kappa Psi K J Y := hz
  have hLargeFactor :=
    parity_original_unbalanced_active_pairs_true_large_factor_range434
      L b1 kappa Psi hL hPsi K J Y z hAct
  classical
  unfold parityOriginalUnbalancedActivePhysicalPairs434 at hAct
  simp only [Finset.mem_filter] at hAct
  have hPhysical := hAct.1
  unfold parityOriginalTypeIIPhysicalPairs434 at hPhysical
  simp only [Finset.mem_filter] at hPhysical
  have hNmem := (Finset.mem_product.mp hPhysical.1).2
  have hN := (Finset.mem_filter.mp hNmem).2
  have hExpLowM : Real.exp ((2*(b1/3))*L) ≤
      Real.exp (((1/2:ℝ)+kappa)*L) := by
    apply Real.exp_le_exp.mpr
    have hh : 2*(b1/3) ≤ (1/2:ℝ)+kappa := by linarith
    exact mul_le_mul_of_nonneg_right hh hL
  have hExpLowN : Real.exp ((2*(b1/3))*L) ≤ Real.exp (b1*L) := by
    apply Real.exp_le_exp.mpr
    have hh : 2*(b1/3) ≤ b1 := by linarith
    exact mul_le_mul_of_nonneg_right hh hL
  have hFirst := congrArg Prod.fst hScale
  have hSecond := congrArg Prod.snd hScale
  obtain ⟨hUlow,hVlow⟩ :=
    parity_original_actual_quarter_dyad_lower_scales_from_factors434
      (b1/3) L hbthird h2 z.1 z.2 scale.1 scale.2 hFirst hSecond
      (hExpLowM.trans hLargeFactor.1) (hExpLowN.trans hN.1)
  have hMpos : 0<z.1 := by
    have hh : (0:ℝ)<(z.1:ℝ) :=
      (Real.exp_pos _).trans_le hLargeFactor.1
    exact_mod_cast hh
  have hNpos : 0<z.2 := by
    have hh : (0:ℝ)<(z.2:ℝ) := (Real.exp_pos _).trans_le hN.1
    exact_mod_cast hh
  have hMdyad := parity_original_historical_actual_z_in_own_dyad434 z.1 hMpos
  have hNdyad := parity_original_historical_actual_z_in_own_dyad434 z.2 hNpos
  have hUleM : (scale.1:ℝ)≤(z.1:ℝ) := by
    have hNat : scale.1≤z.1 := by
      calc
        scale.1 = parityOriginalHistoricalActualZDyadicScale434 z.1 := hFirst.symm
        _ ≤ z.1 := hMdyad.2.1
    exact_mod_cast hNat
  have hVleN : (scale.2:ℝ)≤(z.2:ℝ) := by
    have hNat : scale.2≤z.2 := by
      calc
        scale.2 = parityOriginalHistoricalActualZDyadicScale434 z.2 := hSecond.symm
        _ ≤ z.2 := hNdyad.2.1
    exact_mod_cast hNat
  have hUpperM : 4*Real.exp ((1-b1)*L) ≤
      Real.exp ((1-b1/3)*L) := by
    have hExp : Real.exp ((1-b1)*L)*Real.exp ((2*b1/3)*L) =
        Real.exp ((1-b1/3)*L) := by
      rw [←Real.exp_add]
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_left h4
      (Real.exp_pos ((1-b1)*L)).le
    calc
      _ ≤ Real.exp ((1-b1)*L)*Real.exp ((2*b1/3)*L) := by nlinarith [hh]
      _ = _ := hExp
  have hUpperN : Real.exp (((1/2:ℝ)-kappa)*L) ≤
      Real.exp ((1-b1/3)*L) := by
    apply Real.exp_le_exp.mpr
    have hh : (1/2:ℝ)-kappa ≤ 1-b1/3 := by linarith
    exact mul_le_mul_of_nonneg_right hh hL
  exact ⟨hUlow,hVlow,
    hUleM.trans (hLargeFactor.2.trans hUpperM),
    hVleN.trans (hN.2.trans hUpperN)⟩
end Green64Analytic.Parity

end

end

/-! ## UnbalancedActiveDyadicSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Every actual source Psi-active positive shifted unbalanced pair
has genuine physical U,V binary dyad scales in the true quarter
product window. This is not a free geometry assumption: it follows
from the same nonzero original Psi and m*n=u+2 equation. -/
theorem parity_original_unbalanced_active_pair_quarter_dyad434
    (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (z : ℕ×ℕ)
    (hz : z ∈ parityOriginalUnbalancedActivePhysicalPairs434
      L b1 kappa Psi K J Y) :
    parityOriginalTypeIIQuarterProductGate434 L
      (parityOriginalHistoricalActualZDyadicScale434 z.1,
       parityOriginalHistoricalActualZDyadicScale434 z.2) := by
  classical
  unfold parityOriginalUnbalancedActivePhysicalPairs434 at hz
  simp only [Finset.mem_filter] at hz
  obtain ⟨hPair,⟨u,hu,hShift,hNonzero⟩⟩ := hz
  unfold parityOriginalTypeIIPhysicalPairs434 at hPair
  simp only [Finset.mem_filter] at hPair
  obtain ⟨_,u',hu',hPosM,hPosN,hShift'⟩ := hPair
  have hBounds := parity_original_actual_pair_scale_real_bounds434
    z (parityOriginalHistoricalActualZDyadicScale434 z.1,
      parityOriginalHistoricalActualZDyadicScale434 z.2) rfl hPosM hPosN
  exact parity_original_TypeII_psi_physical_dyad_UV_true_bounds434
    L (parityOriginalHistoricalActualZDyadicScale434 z.1:ℝ)
      (parityOriginalHistoricalActualZDyadicScale434 z.2:ℝ)
    Psi hL hPsi z.1 z.2 u hPosM hPosN hShift hNonzero
      hBounds.1 hBounds.2.1 hBounds.2.2.1 hBounds.2.2.2

/-- SOURCE-EXACT original Parity(4.2) unbalanced small-factor triple
is the sum over DISTINCT ACTUALLY Psi-ACTIVE dyadic pair fibres;
all attained scales automatically meet true quarter-UV geometry.
This is a finite Fubini identity and source support proof, not an
assertion that all exterior test/sieve families are counted. -/
theorem parity_original_unbalanced_source_eq_active_dyadic_fibres434
    (d : ℕ) (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ) :
    let S := parityOriginalUnbalancedActivePhysicalPairs434 L b1 kappa Psi K J Y
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      K (J.filter (parityOriginalUnbalancedSmallFactor434 L b1 kappa))
      alpha beta Y =
    ∑ scale ∈ parityOriginalActualTypeIIDyadicPairScales434 S,
      ∑ z ∈ S.filter
        (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2)=scale),
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
            (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
              (sourceOriginalPAllActualBands 20 L) u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (alpha z.1*beta z.2))
          else 0 := by
  classical
  dsimp only
  rw [parity_original_unbalanced_triple_eq_active_physical_pairs434]
  let S := parityOriginalUnbalancedActivePhysicalPairs434 L b1 kappa Psi K J Y
  let f : ℕ×ℕ → ℕ×ℕ := fun z =>
    (parityOriginalHistoricalActualZDyadicScale434 z.1,
      parityOriginalHistoricalActualZDyadicScale434 z.2)
  have hMaps : ∀z∈S, f z∈S.image f :=
    fun z hz => Finset.mem_image_of_mem f hz
  exact (Finset.sum_fiberwise_of_maps_to hMaps
    (fun z => ∑u∈Finset.Ioc 0 Y,
      if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
        (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
          (sourceOriginalPAllActualBands 20 L) u *
          Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
          (alpha z.1*beta z.2))
      else 0)).symm

/-- The distinct source dyadic image of the actual Psi-active
unbalanced carrier needs NO additional quarter-product filter.
All its points already satisfy the original true physical gate. -/
theorem parity_original_unbalanced_all_active_scales_quarter434
    (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) :
    ∀ scale ∈ parityOriginalActualTypeIIDyadicPairScales434
      (parityOriginalUnbalancedActivePhysicalPairs434 L b1 kappa Psi K J Y),
      parityOriginalTypeIIQuarterProductGate434 L scale := by
  classical
  intro scale hs
  obtain ⟨z,hz,hScale⟩ := Finset.mem_image.mp hs
  rw [←hScale]
  exact parity_original_unbalanced_active_pair_quarter_dyad434
    L b1 kappa Psi hL hPsi K J Y z hz
end Green64Analytic.Parity

end

end

/-! ## StrictUnbalancedSourceCarrier -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 3500000

/-- Literal Parity section 7.3 interval: its lower endpoint is OPEN.
The older weak-lower interval remains available as a containing set. -/
def parityOriginalUnbalancedStrictSmallFactor434
    (L b1 kappa : ℝ) (n : ℕ) : Prop :=
  Real.exp (b1*L) < (n:ℝ) ∧
  (n:ℝ) ≤ Real.exp (((1/2:ℝ)-kappa)*L)

/-- The strict source interval is exactly the older containing interval
restricted by its genuine open lower endpoint. -/
theorem parity_original_unbalanced_strict_interval_eq_open_filtered434
    (L b1 kappa : ℝ) (J : Finset ℕ) :
    J.filter (parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa) =
    (J.filter (fun (n : ℕ) => Real.exp (b1*L) < (n:ℝ))).filter
      (parityOriginalUnbalancedSmallFactor434 L b1 kappa) := by
  classical
  ext n
  simp only [Finset.mem_filter, parityOriginalUnbalancedStrictSmallFactor434,
    parityOriginalUnbalancedSmallFactor434]
  constructor
  · rintro ⟨hn,hlo,hhi⟩
    exact ⟨⟨hn,hlo⟩,hlo.le,hhi⟩
  · rintro ⟨⟨hn,hlo⟩,_,hhi⟩
    exact ⟨hn,hlo,hhi⟩

/-- No endpoint equality is silently included in the source interval.
This statement applies whenever a real endpoint happens to be integral. -/
theorem parity_original_unbalanced_strict_excludes_lower_endpoint434
    (L b1 kappa : ℝ) (n : ℕ)
    (hEq : (n:ℝ)=Real.exp (b1*L))
    (hUpper : (n:ℝ)≤Real.exp (((1/2:ℝ)-kappa)*L)) :
    parityOriginalUnbalancedSmallFactor434 L b1 kappa n ∧
    ¬ parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa n := by
  constructor
  · exact ⟨hEq.ge,hUpper⟩
  · intro h
    have hh := h.1
    rw [hEq] at hh
    exact (lt_irrefl _) hh

/-- Independently defined actual shifted source carrier, with the strict
Parity interval and a nonzero value of the same compact Psi. -/
def parityOriginalUnbalancedStrictActivePairs434
    (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (Y : ℕ) : Finset (ℕ×ℕ) :=
  (parityOriginalTypeIIPhysicalPairs434 K
    (J.filter (parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa)) Y).filter
      (fun z => ∃ u ∈ Finset.Ioc 0 Y,
        z.1*z.2=u+2 ∧ Psi ((u:ℝ)/Real.exp L)≠0)

theorem parity_original_unbalanced_strict_active_eq_open_filtered434
    (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (Y : ℕ) :
    parityOriginalUnbalancedStrictActivePairs434 L b1 kappa Psi K J Y =
    parityOriginalUnbalancedActivePhysicalPairs434 L b1 kappa Psi K
      (J.filter (fun (n : ℕ) => Real.exp (b1*L) < (n:ℝ))) Y := by
  unfold parityOriginalUnbalancedStrictActivePairs434
    parityOriginalUnbalancedActivePhysicalPairs434
  rw [parity_original_unbalanced_strict_interval_eq_open_filtered434]

/-- Exact full original Q/P weighted alpha-beta source on the strict
interval equals its genuinely Psi-active shifted physical carrier.
There is no assumption of a geometric carrier equality. -/
theorem parity_original_unbalanced_strict_source_eq_active_pairs434
    (d : ℕ) (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ) :
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      K (J.filter (parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa))
      alpha beta Y =
    ∑ z ∈ parityOriginalUnbalancedStrictActivePairs434 L b1 kappa Psi K J Y,
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
            (sourceOriginalPAllActualBands 20 L) u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0 := by
  rw [parity_original_unbalanced_strict_interval_eq_open_filtered434,
    parity_original_unbalanced_strict_active_eq_open_filtered434]
  exact parity_original_unbalanced_triple_eq_active_physical_pairs434
    d L b1 kappa Psi K
      (J.filter (fun (n : ℕ) => Real.exp (b1*L)<(n:ℝ))) Y alpha beta

/-- Exact fibrewise equality for the strict original unbalanced source,
with every coefficient retained. The dyadic family is its actual image. -/
theorem parity_original_unbalanced_strict_source_eq_active_dyads434
    (d : ℕ) (L b1 kappa : ℝ) (Psi : ℝ → ℝ)
    (hL : 0≤L) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (Y : ℕ) (alpha beta : ℕ → ℂ) :
    let S := parityOriginalUnbalancedStrictActivePairs434 L b1 kappa Psi K J Y
    parityOriginalShiftTwoOriginalTypeIITripleSource434 d L Psi
      K (J.filter (parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa))
      alpha beta Y =
    ∑ scale ∈ parityOriginalActualTypeIIDyadicPairScales434 S,
      ∑ z ∈ S.filter
        (fun z => (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2)=scale),
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
            (((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
              (sourceOriginalPAllActualBands 20 L) u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (alpha z.1*beta z.2))
          else 0 := by
  dsimp only
  rw [parity_original_unbalanced_strict_interval_eq_open_filtered434,
    parity_original_unbalanced_strict_active_eq_open_filtered434]
  exact parity_original_unbalanced_source_eq_active_dyadic_fibres434
    d L b1 kappa Psi hL hPsi K
      (J.filter (fun (n : ℕ) => Real.exp (b1*L)<(n:ℝ))) Y alpha beta

/-- The previously proved physical quarter window and exponent margins
apply uniformly to the exact strict source, without an endpoint error. -/
theorem parity_eventually_original_unbalanced_strict_dyads_legal434
    (b1 kappa : ℝ) (hb1 : 0<b1)
    (hkappa : 0≤kappa) (hBand : b1≤(1/2:ℝ)-kappa)
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (K J : Finset ℕ) (Y : ℕ) (scale : ℕ×ℕ),
        scale ∈ parityOriginalActualTypeIIDyadicPairScales434
          (parityOriginalUnbalancedStrictActivePairs434 L b1 kappa Psi K J Y) →
        (Real.exp ((b1/3)*L) ≤ (scale.1:ℝ) ∧
         Real.exp ((b1/3)*L) ≤ (scale.2:ℝ) ∧
         (scale.1:ℝ) ≤ Real.exp ((1-b1/3)*L) ∧
         (scale.2:ℝ) ≤ Real.exp ((1-b1/3)*L)) ∧
        parityOriginalTypeIIQuarterProductGate434 L scale := by
  filter_upwards [
    parity_eventually_original_unbalanced_active_dyads_exponent_window434
      b1 kappa hb1 hkappa hBand Psi hPsi,
    eventually_ge_atTop (0:ℝ)] with L hWindow hL
  intro K J Y scale hs
  rw [parity_original_unbalanced_strict_active_eq_open_filtered434] at hs
  exact ⟨hWindow K _ Y scale hs,
    parity_original_unbalanced_all_active_scales_quarter434
      L b1 kappa Psi hL hPsi K _ Y scale hs⟩
end Green64Analytic.Parity

end

end

/-! ## StrictBothParitySourceDyads -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Both original Parity parity projections, with independent arithmetic
weight A0(1+rho E)/2, have the exact physical pair representation.
This follows by linearity from the two complete signed source identities. -/
theorem parity_original_parity_source_eq_physical_pairs434
    (d : ℕ) (L rho : ℝ) (hL : 0<L) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalParityBilinearSource434 d L rho Psi K J alpha beta Y =
    ∑ z ∈ parityOriginalTypeIIPhysicalPairs434 K J Y,
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (((parityWeight d L rho u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0 := by
  rw [parity_original_parity_bilinear_eq_signed_mellin_projection434 d L rho hL,
    parity_original_signed_source_eq_physical_pair_triple434
      d L Psi hPsi K J alpha beta false 0 Y,
    parity_original_signed_source_eq_physical_pair_triple434
      d L Psi hPsi K J alpha beta true 0 Y]
  rw [Finset.mul_sum, ←Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum, ←Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2
  · simp only [if_pos h]
    rw [parity_original_parity_A_eq_full_signed_projection434 d L rho hL u]
    simp [sourceOriginalPureMellinPhase434]
    push_cast
    ring
  · simp [h]

/-- Exact original section 7.3 strict unbalanced source for BOTH
projections. The weight, Psi, alpha and beta remain literal. Inactive
pairs vanish term by term, independently of the sign or coefficients. -/
theorem parity_original_both_parity_strict_unbalanced_source_eq_active_pairs434
    (d : ℕ) (L rho b1 kappa : ℝ) (hL : 0<L)
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalParityBilinearSource434 d L rho Psi
      K (J.filter (parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa))
      alpha beta Y =
    ∑ z ∈ parityOriginalUnbalancedStrictActivePairs434 L b1 kappa Psi K J Y,
      ∑ u ∈ Finset.Ioc 0 Y,
        if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
          (((parityWeight d L rho u *
            Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
            (alpha z.1*beta z.2))
        else 0 := by
  classical
  rw [parity_original_parity_source_eq_physical_pairs434 d L rho hL Psi hPsi]
  unfold parityOriginalUnbalancedStrictActivePairs434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hActive : ∃ u ∈ Finset.Ioc 0 Y,
      z.1*z.2=u+2 ∧ Psi ((u:ℝ)/Real.exp L)≠0
  · simp only [if_pos hActive]
  · simp only [if_neg hActive]
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hEq : 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2
    · have hZero : Psi ((u:ℝ)/Real.exp L)=0 := by
        by_contra hn
        exact hActive ⟨u,hu,hEq.2.2,hn⟩
      simp [hEq,hZero]
    · simp [hEq]

/-- The two genuine parity sources on the strict interval are the
literal sum over their attained dyadic fibres, for arbitrary alpha,beta.
Sharp tests and full-cell nonsmooth proxies are therefore substituted
without changing or renormalizing the underlying source weight. -/
theorem parity_original_both_parity_strict_unbalanced_source_eq_active_dyads434
    (d : ℕ) (L rho b1 kappa : ℝ) (hL : 0<L)
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    let S := parityOriginalUnbalancedStrictActivePairs434 L b1 kappa Psi K J Y
    parityOriginalParityBilinearSource434 d L rho Psi
      K (J.filter (parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa))
      alpha beta Y =
    ∑ scale ∈ parityOriginalActualTypeIIDyadicPairScales434 S,
      ∑ z ∈ S.filter (fun z =>
        (parityOriginalHistoricalActualZDyadicScale434 z.1,
          parityOriginalHistoricalActualZDyadicScale434 z.2)=scale),
        ∑ u ∈ Finset.Ioc 0 Y,
          if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
            (((parityWeight d L rho u *
              Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
              (alpha z.1*beta z.2))
          else 0 := by
  classical
  dsimp only
  rw [parity_original_both_parity_strict_unbalanced_source_eq_active_pairs434
    d L rho b1 kappa hL Psi hPsi]
  let S := parityOriginalUnbalancedStrictActivePairs434 L b1 kappa Psi K J Y
  let f : ℕ×ℕ → ℕ×ℕ := fun z =>
    (parityOriginalHistoricalActualZDyadicScale434 z.1,
      parityOriginalHistoricalActualZDyadicScale434 z.2)
  have hMaps : ∀ z∈S, f z∈S.image f :=
    fun z hz => Finset.mem_image_of_mem f hz
  exact (Finset.sum_fiberwise_of_maps_to hMaps
    (fun z => ∑ u∈Finset.Ioc 0 Y,
      if 0<z.1 ∧ 0<z.2 ∧ z.1*z.2=u+2 then
        (((parityWeight d L rho u *
          Psi ((u:ℝ)/Real.exp L):ℝ):ℂ) *
          (alpha z.1*beta z.2))
      else 0)).symm
end Green64Analytic.Parity

end

end

/-! ## ExactExponentBinSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 2500000

/-- Literal fixed exponent bin used in Parity section 8.3, with the
open lower and closed upper endpoints of the manuscript. -/
def parityOriginalExponentBin434 (L gamma gamma' : ℝ) (n : ℕ) : Prop :=
  Real.exp (gamma*L)<(n:ℝ) ∧ (n:ℝ)≤Real.exp (gamma'*L)

/-- Exact integer endpoints, including the case where an exponential
endpoint is an integer. No boundary point or small error is dropped. -/
theorem parity_original_exponent_bin_iff_nat_interval434
    (L gamma gamma' : ℝ) (n : ℕ) :
    parityOriginalExponentBin434 L gamma gamma' n ↔
      ⌊Real.exp (gamma*L)⌋₊+1≤n ∧ n≤⌊Real.exp (gamma'*L)⌋₊ := by
  unfold parityOriginalExponentBin434
  rw [←Nat.floor_lt (Real.exp_pos (gamma*L)).le,
    ←Nat.le_floor_iff (Real.exp_pos (gamma'*L)).le]
  omega

/-- Intersecting a real source bin with the true restricted factor
interval gives this precise Icc. The original coefficient functions
are NOT recalculated using the new endpoints. -/
theorem parity_original_exponent_bin_filter_Icc_exact434
    (L gamma gamma' : ℝ) (c e : ℕ) :
    (Finset.Icc c e).filter (parityOriginalExponentBin434 L gamma gamma') =
      Finset.Icc (max c (⌊Real.exp (gamma*L)⌋₊+1))
        (min e ⌊Real.exp (gamma'*L)⌋₊) := by
  classical
  ext n
  simp only [Finset.mem_filter,Finset.mem_Icc,
    parity_original_exponent_bin_iff_nat_interval434,max_le_iff,le_min_iff]
  tauto

/-- Every admissible original fixed bin is a subset of the exact
strict unbalanced interval, uniformly in its integer point. -/
theorem parity_original_admissible_bin_mem_strict_unbalanced434
    (L b1 kappa gamma gamma' : ℝ) (hL : 0≤L)
    (hLower : b1≤gamma) (hUpper : gamma'≤(1/2:ℝ)-kappa)
    (n : ℕ) (hn : parityOriginalExponentBin434 L gamma gamma' n) :
    parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa n := by
  exact ⟨(Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hLower hL)).trans_lt hn.1,
    hn.2.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hUpper hL))⟩

/-- Source-exact bin restriction for BOTH original projections, with
the same alpha and beta before and after interval conversion. This
therefore applies to the sharp prime test and the nonsmooth full-cell
proxy without refitting a normalizer at a bin or dyadic endpoint. -/
theorem parity_original_both_parity_bin_source_Icc_exact434
    (d : ℕ) (L rho gamma gamma' : ℝ) (Psi : ℝ → ℝ)
    (K : Finset ℕ) (c e Y : ℕ) (alpha beta : ℕ → ℂ) :
    parityOriginalParityBilinearSource434 d L rho Psi K
      ((Finset.Icc c e).filter (parityOriginalExponentBin434 L gamma gamma'))
      alpha beta Y =
    parityOriginalParityBilinearSource434 d L rho Psi K
      (Finset.Icc (max c (⌊Real.exp (gamma*L)⌋₊+1))
        (min e ⌊Real.exp (gamma'*L)⌋₊))
      alpha beta Y := by
  rw [parity_original_exponent_bin_filter_Icc_exact434]
end Green64Analytic.Parity

end

end

/-! ## StrictUnbalancedFullCellEndpoints -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A positive physical factor at least exp(bL) has binary dyad scale
at least exp(2bL/3), once the genuine exponent slack pays the factor 2.
No doubling of b in the factor hypothesis is required. -/
theorem parity_original_actual_dyad_lower_two_thirds434
    (b L : ℝ) (hTwo : (2:ℝ)≤Real.exp ((b/3)*L))
    (m : ℕ) (hm : Real.exp (b*L)≤(m:ℝ)) :
    Real.exp ((2*b/3)*L)≤
      (parityOriginalHistoricalActualZDyadicScale434 m:ℝ) := by
  have hmpos : 0 < m := by
    exact_mod_cast (Real.exp_pos (b*L)).trans_le hm
  have hDyad := parity_original_historical_actual_z_in_own_dyad434 m hmpos
  have hUpper : (m:ℝ)<
      2*(parityOriginalHistoricalActualZDyadicScale434 m:ℝ) := by
    exact_mod_cast hDyad.2.2
  have hExp : Real.exp ((2*b/3)*L)*Real.exp ((b/3)*L) =
      Real.exp (b*L) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hPaid := mul_le_mul_of_nonneg_left hTwo
    (Real.exp_pos ((2*b/3)*L)).le
  rw [hExp] at hPaid
  nlinarith

/-- Strong lower endpoints needed by the actual full-cell proxy
theorem, derived on the strict original unbalanced source. These are
exp(2*bstar*L), bstar=b1/3, not merely exp(bstar*L). Upper windows and
the true quarter-product gate remain unchanged. -/
theorem parity_eventually_original_strict_unbalanced_fullcell_endpoints_legal434
    (b1 kappa : ℝ) (hb1 : 0<b1)
    (hkappa : 0≤kappa) (hBand : b1≤(1/2:ℝ)-kappa)
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (K J : Finset ℕ) (Y : ℕ) (scale : ℕ×ℕ),
        scale ∈ parityOriginalActualTypeIIDyadicPairScales434
          (parityOriginalUnbalancedStrictActivePairs434 L b1 kappa Psi K J Y) →
        Real.exp ((2*b1/3)*L)≤(scale.1:ℝ) ∧
        Real.exp ((2*b1/3)*L)≤(scale.2:ℝ) ∧
        (scale.1:ℝ)≤Real.exp ((1-b1/3)*L) ∧
        (scale.2:ℝ)≤Real.exp ((1-b1/3)*L) ∧
        parityOriginalTypeIIQuarterProductGate434 L scale := by
  have hbthird : (0:ℝ)<b1/3 := by positivity
  filter_upwards [
    parity_eventually_original_unbalanced_strict_dyads_legal434
      b1 kappa hb1 hkappa hBand Psi hPsi,
    eventually_ge_atTop (max (0:ℝ) (Real.log 2/(b1/3)))] with L hOld hLarge
  have hL : 0≤L := (le_max_left _ _).trans hLarge
  have hTwo : (2:ℝ)≤Real.exp ((b1/3)*L) := by
    have hThreshold : Real.log 2/(b1/3)≤L :=
      (le_max_right _ _).trans hLarge
    have hLog : Real.log 2≤(b1/3)*L := by
      have h := (div_le_iff₀ hbthird).mp hThreshold
      nlinarith
    have h := Real.exp_le_exp.mpr hLog
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using h
  intro K J Y scale hs
  have hPrior := hOld K J Y scale hs
  obtain ⟨z,hz,hScale⟩ := Finset.mem_image.mp hs
  have hOldPair := hz
  rw [parity_original_unbalanced_strict_active_eq_open_filtered434] at hOldPair
  have hLargeFactor :=
    parity_original_unbalanced_active_pairs_true_large_factor_range434
      L b1 kappa Psi hL hPsi K _ Y z hOldPair
  classical
  unfold parityOriginalUnbalancedStrictActivePairs434 at hz
  simp only [Finset.mem_filter] at hz
  have hPhysical := hz.1
  unfold parityOriginalTypeIIPhysicalPairs434 at hPhysical
  simp only [Finset.mem_filter] at hPhysical
  have hNmem := (Finset.mem_product.mp hPhysical.1).2
  have hN := (Finset.mem_filter.mp hNmem).2
  have hM : Real.exp (b1*L)≤(z.1:ℝ) := by
    have hGap : b1≤(1/2:ℝ)+kappa := by linarith
    exact (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hGap hL)).trans hLargeFactor.1
  have hScaleM := congrArg Prod.fst hScale
  have hScaleN := congrArg Prod.snd hScale
  have hMlow := parity_original_actual_dyad_lower_two_thirds434 b1 L hTwo z.1 hM
  have hNlow := parity_original_actual_dyad_lower_two_thirds434 b1 L hTwo z.2 hN.1.le
  change parityOriginalHistoricalActualZDyadicScale434 z.1=scale.1 at hScaleM
  change parityOriginalHistoricalActualZDyadicScale434 z.2=scale.2 at hScaleN
  rw [hScaleM] at hMlow
  rw [hScaleN] at hNlow
  exact ⟨hMlow,hNlow,hPrior.1.2.2.1,hPrior.1.2.2.2,hPrior.2⟩

/-- Actual nested interval lower endpoints retain the strong physical
dyad lower bound. The max is the real interval-intersection operation. -/
theorem parity_original_nested_cut_endpoints_retain_fullcell_margin434
    (b1 L : ℝ) (scale : ℕ×ℕ)
    (hM : Real.exp ((2*b1/3)*L)≤(scale.1:ℝ))
    (hN : Real.exp ((2*b1/3)*L)≤(scale.2:ℝ))
    (a c : ℕ) :
    Real.exp ((2*(b1/3))*L)≤((max a scale.1:ℕ):ℝ) ∧
    Real.exp ((2*(b1/3))*L)≤((max c scale.2:ℕ):ℝ) := by
  have hm : (scale.1:ℝ)≤((max a scale.1:ℕ):ℝ) := by
    exact_mod_cast le_max_right a scale.1
  have hn : (scale.2:ℝ)≤((max c scale.2:ℕ):ℝ) := by
    exact_mod_cast le_max_right c scale.2
  have he : 2*(b1/3)=2*b1/3 := by ring
  simpa only [he] using And.intro (hM.trans hm) (hN.trans hn)
end Green64Analytic.Parity

end

end

/-! ## StrictParityDeltaIntegratedAudit -/

section

-- Exact public root axioms for this delta; no target-closure claim.

end

/-! ## UniformSignedFullCell -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 32000

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_signed_b629_every_quarter_cut_anylog_common_precision434
    (jQ : ℕ) (goal target C0 beta betaP bstar K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (gamma : ℝ), 0 < gamma →
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (scale : ℕ×ℕ),
          scale ∈ (parityOriginalActualTypeIIDyadicPairScales434
              (parityOriginalTypeIIPhysicalPairs434
                (Finset.Icc a b) (Finset.Icc c e) Y)).filter
              (parityOriginalTypeIIQuarterProductGate434 L) →
          ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (prime : Bool)
            (betaCoeff : ℕ → ℂ) (signed : Bool),
            (∀n∈Finset.Icc (max c scale.2) (min e (2*scale.2-1)),
              ‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let K := Finset.Icc (max a scale.1) (min b (2*scale.1-1))
          let Jcut := Finset.Icc (max c scale.2) (min e (2*scale.2-1))
          let alpha := restrictSequence K
            (b629ActualFineAlpha434 prime L S gamma (max a scale.1) (min b (2*scale.1-1)))
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434
              d L Psi K Jcut alpha betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤
            (4+Csource*(∫s : ℝ,
                ‖(𝓕 (parityOriginalLogCutoff434
                  (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
             20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal) := by
  have hSigned := parity_eventually_original_signed_quarter_b629_fine_one_slot_Psi_Mellin_source_anylog_common_precision434
    jQ goal target C0 betaP K0 4 A R
    hbetaP hBand hC0 hTarget hK0Target hPrecision hK0
    (by norm_num) hA hR buf hSmooth hSupport hOne4 hCube
    Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  have hGates := parity_eventually_original_actual_quarter_cut_all_numeric_gates434
    beta betaP bstar K0 hbetaP hbstar hBeta hK0
  obtain ⟨H,J,B,S,hBS,hSignedL⟩ := hSigned
  refine ⟨H,J,B,S,hBS,?_⟩
  intro gamma hgamma
  have hSignedL := hSignedL beta gamma hbeta hgamma
  filter_upwards [hSignedL,hGates] with L hSignedNow hGateNow
  rcases hSignedNow with ⟨hBig,h128,h24,hFam,hReserved,hRest⟩
  refine ⟨hBig,h128,(by norm_num at h24 ⊢; exact h24),hFam,hReserved,?_⟩
  intro hL hFamily a b c e Y ha hc hab hExpB scale hs
    band hBandSlot slot prime betaCoeff signed hBetaCoeff
  have hG := hGateNow a b c e Y ha hc hab hExpB scale hs
  rcases hG with ⟨hUpos,hVpos,hUVlower,hUVupper,hEone,hEupper,hVone,
    hFineLower,hFine2,hFineWidth,hFineExp,hKcut,hJcut⟩
  have hBound := hRest hL hFamily (scale.1:ℝ) (scale.2:ℝ)
    ((scale.1:ℝ)*L^(-K0)) hUpos hVpos hUVlower hUVupper
    rfl hEone hEupper hVone band hBandSlot slot
    (max a scale.1) (min b (2*scale.1-1))
    (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
    prime betaCoeff signed hFineLower hFine2 hFineWidth hFineExp
    hKcut hJcut hBetaCoeff
  dsimp only at hBound ⊢
  convert hBound using 1 <;> ring

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_signed_quarter_actual_cut_sum_paid_common_precision434
    (jQ : ℕ) (goal target C0 beta betaP bstar K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (gamma : ℝ), 0 < gamma →
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (prime : Bool)
            (betaCoeff : ℕ → ℂ) (signed : Bool),
            (∀n∈Finset.Icc c e,‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let T := (parityOriginalActualTypeIIDyadicPairScales434
              (parityOriginalTypeIIPhysicalPairs434
                (Finset.Icc a b) (Finset.Icc c e) Y)).filter
              (parityOriginalTypeIIQuarterProductGate434 L)
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖∑ scale ∈ T,
             parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
               (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
               (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
               (restrictSequence
                 (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
                 (b629ActualFineAlpha434 prime L S gamma
                   (max a scale.1) (min b (2*scale.1-1))))
               betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤
            (T.card:ℝ)*Bound := by
  obtain ⟨H,J,B,S,hBS,hEvery⟩ :=
    parity_eventually_original_signed_b629_every_quarter_cut_anylog_common_precision434
      jQ goal target C0 beta betaP bstar K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  intro gamma hgamma
  have hEvery := hEvery gamma hgamma
  filter_upwards [hEvery] with L hEveryNow
  rcases hEveryNow with ⟨hBig,h128,h24,hFam,hRes,hRest⟩
  refine ⟨hBig,h128,h24,hFam,hRes,?_⟩
  intro hL hFam0 a b c e Y ha hc hab hExpB band hBandNow
    slot prime betaCoeff signed hBetaWhole
  classical
  let T := (parityOriginalActualTypeIIDyadicPairScales434
      (parityOriginalTypeIIPhysicalPairs434
        (Finset.Icc a b) (Finset.Icc c e) Y)).filter
      (parityOriginalTypeIIQuarterProductGate434 L)
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Bound := (4+Csource*(∫s : ℝ,
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
       20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
  have hEach (scale : ℕ×ℕ) (hs : scale∈T) :
      ‖parityOriginalShiftTwoSignedBilinearMellinSource434
        (sourceOriginalLiteralDepth 20 L) L Psi
        (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
        (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
        (restrictSequence
          (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
          (b629ActualFineAlpha434 prime L S gamma
            (max a scale.1) (min b (2*scale.1-1))))
        betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤ Bound := by
    have hBetaCut : ∀n∈Finset.Icc (max c scale.2) (min e (2*scale.2-1)),
        ‖betaCoeff n‖≤1 := by
      intro n hn
      obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
      have hJn : n∈Finset.Icc c e := Finset.mem_Icc.mpr
        ⟨(le_max_left _ _).trans hlo,hhi.trans (min_le_left _ _)⟩
      exact hBetaWhole n hJn
    have h := hRest hL hFam0 a b c e Y ha hc hab hExpB scale
      hs band hBandNow slot prime betaCoeff signed hBetaCut
    simpa only [Bound,C1,Cmoment,Cphys,Csource,M_H,T] using h
  dsimp only
  calc
    _ ≤ ∑ scale ∈ T,
        ‖parityOriginalShiftTwoSignedBilinearMellinSource434
          (sourceOriginalLiteralDepth 20 L) L Psi
          (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
          (Finset.Icc (max c scale.2) (min e (2*scale.2-1)))
          (restrictSequence
            (Finset.Icc (max a scale.1) (min b (2*scale.1-1)))
            (b629ActualFineAlpha434 prime L S gamma
              (max a scale.1) (min b (2*scale.1-1))))
          betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ := norm_sum_le _ _
    _ ≤ ∑ scale ∈ T, Bound := by
      apply Finset.sum_le_sum
      intro scale hs
      exact hEach scale hs
    _ = (T.card:ℝ)*Bound := by simp

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_signed_fullcell_quarter_b629_anylog_common_precision434
    (jQ : ℕ) (goal target C0 beta betaP bstar K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : goal+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (gamma : ℝ), 0 < gamma →
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (prime : Bool)
            (betaCoeff : ℕ → ℂ) (signed : Bool),
            (∀n∈Finset.Icc c e,‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let T := (parityOriginalActualTypeIIDyadicPairScales434
              (parityOriginalTypeIIPhysicalPairs434
                (Finset.Icc a b) (Finset.Icc c e) Y)).filter
              (parityOriginalTypeIIQuarterProductGate434 L)
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
             betaCoeff signed 0 Y‖ ≤
            (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*Bound := by
  have hPaid := parity_eventually_original_signed_quarter_actual_cut_sum_paid_common_precision434
    jQ goal target C0 beta betaP bstar K0 A R
    hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
    hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
    Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  obtain ⟨H,J,B,S,hBS,hPaidL⟩ := hPaid
  refine ⟨H,J,B,S,hBS,?_⟩
  intro gamma hgamma
  have hPaidL := hPaidL gamma hgamma
  filter_upwards [hPaidL] with L hLnow
  rcases hLnow with ⟨hBig,h128,h24,hFam,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFam,hReserved,?_⟩
  intro hL hFamily a b c e Y ha hc hab hExpB hY band hBandNow
    slot prime betaCoeff signed hBetaWhole
  subst Y
  let Y : ℕ := ⌊2*Real.exp L⌋₊
  classical
  let T := (parityOriginalActualTypeIIDyadicPairScales434
      (parityOriginalTypeIIPhysicalPairs434
        (Finset.Icc a b) (Finset.Icc c e) Y)).filter
      (parityOriginalTypeIIQuarterProductGate434 L)
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Bound := (4+Csource*(∫s : ℝ,
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
       20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
  have hSum := hRest hL hFamily a b c e Y ha hc hab hExpB
    band hBandNow slot prime betaCoeff signed hBetaWhole
  have haPos : 0<a := by
    have hr : (0:ℝ)<(a:ℝ) := (Real.exp_pos _).trans_le ha
    exact_mod_cast hr
  have hcPos : 0<c := by
    have hr : (0:ℝ)<(c:ℝ) := (Real.exp_pos _).trans_le hc
    exact_mod_cast hr
  have hExact := parity_original_signed_fullcell_eq_quarter_b629_cut_sources434
    (sourceOriginalLiteralDepth 20 L) L Psi (by linarith : 0≤L)
    hPsiSet a b c e Y haPos hcPos prime S gamma betaCoeff signed 0
  have hCard := parity_original_actual_quarter_Icc_dyadic_card_le_log_sq434
    a b c e Y L
  have hCmoment : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hLog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCsource : 0≤Csource := by dsimp [Csource,Cphys]; positivity
  have hM0 : 0≤(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) :=
    integral_nonneg (fun s => norm_nonneg _)
  have hMH : 0≤M_H := by
    dsimp [M_H]
    apply integral_nonneg
    intro s
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hBoundNonneg : 0≤Bound := by
    dsimp [Bound]
    have hp : 0≤(2*Real.pi)^H := pow_nonneg (by positivity) _
    positivity
  have hCardReal : (T.card:ℝ) ≤
      (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ) := by
    exact_mod_cast hCard
  change ‖parityOriginalShiftTwoSignedBilinearMellinSource434
    (sourceOriginalLiteralDepth 20 L) L Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
    betaCoeff signed 0 Y‖ ≤ _
  rw [hExact]
  calc
    _ ≤ (T.card:ℝ)*Bound := by
      simpa only [T,Bound,C1,Cmoment,Cphys,Csource,M_H] using hSum
    _ ≤ (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*Bound :=
      mul_le_mul_of_nonneg_right hCardReal hBoundNonneg

/-- Common precision for the original source expression; all local source hypotheses are retained. -/
theorem parity_eventually_original_signed_fullcell_quarter_b629_no_log_loss_common_precision434
    (jQ : ℕ) (goal target C0 beta betaP bstar K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (gamma : ℝ), 0 < gamma →
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hL : 128≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
          ∀ (slot : Fin 20) (prime : Bool)
            (betaCoeff : ℕ → ℂ) (signed : Bool),
            (∀n∈Finset.Icc c e,‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let T := (parityOriginalActualTypeIIDyadicPairScales434
              (parityOriginalTypeIIPhysicalPairs434
                (Finset.Icc a b) (Finset.Icc c e) Y)).filter
              (parityOriginalTypeIIQuarterProductGate434 L)
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalShiftTwoSignedBilinearMellinSource434 d L Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
             betaCoeff signed 0 Y‖ ≤
            (1+2/Real.log 2)^2*Bound := by
  have hPrev := parity_eventually_original_signed_fullcell_quarter_b629_anylog_common_precision434
    jQ (goal+2) target C0 beta betaP bstar K0 A R
    hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
    hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
    Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  obtain ⟨H,J,B,S,hBS,hPrevL⟩ := hPrev
  refine ⟨H,J,B,S,hBS,?_⟩
  intro gamma hgamma
  have hPrevL := hPrevL gamma hgamma
  filter_upwards [hPrevL] with L hLnow
  rcases hLnow with ⟨hBig,h128,h24,hFam,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFam,hReserved,?_⟩
  intro hL hFamily a b c e Y ha hc hab hExpB hY band hBandNow
    slot prime betaCoeff signed hBetaWhole
  classical
  have hBound := hRest hL hFamily a b c e Y ha hc hab hExpB hY
    band hBandNow slot prime betaCoeff signed hBetaWhole
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Coef := 4+Csource*(∫s : ℝ,
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
       20*(2*Real.pi)^H*M_H
  have hCmoment : 0≤Cmoment :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 0 hR
  have hC1 : 0≤C1 :=
    parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
      A R buf hSmooth hSupport 1 hR
  have hLog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCsource : 0≤Csource := by dsimp [Csource,Cphys]; positivity
  have hM0 : 0≤(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) :=
    integral_nonneg (fun s => norm_nonneg _)
  have hMH : 0≤M_H := by
    dsimp [M_H]
    apply integral_nonneg
    intro s
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hCoef : 0≤Coef*Real.exp L := by
    dsimp [Coef]
    positivity
  have hPower := parity_original_actual_quarter_log_sq_power_absorption434
    L goal (by linarith : 8≤L)
  rw [hY] at hBound ⊢
  change ‖parityOriginalShiftTwoSignedBilinearMellinSource434
    (sourceOriginalLiteralDepth 20 L) L Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b)
    betaCoeff signed 0 ⌊2*Real.exp L⌋₊‖ ≤ _
  calc
    _ ≤ (((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1)*
        (Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1):ℕ):ℝ)*
        (Coef*Real.exp L*L^(-(goal+2))) := by
      simpa only [Coef,C1,Cmoment,Cphys,Csource,M_H,mul_assoc] using hBound
    _ = (Coef*Real.exp L)*
      ((((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1)*
        (Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1):ℕ):ℝ)*
        L^(-(goal+2))) := by ring
    _ ≤ (Coef*Real.exp L)*((1+2/Real.log 2)^2*L^(-goal)) :=
      mul_le_mul_of_nonneg_left hPower hCoef
    _ = (1+2/Real.log 2)^2*(Coef*Real.exp L*L^(-goal)) := by ring

end Green64Analytic.Parity

end

end

/-! ## UniformMixedParityProxy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32000

/-- One precision choice works for every fixed positive fine exponent in the actual parity source. -/
theorem parity_eventually_original_both_parity_first_fullcell_proxy_common_precision434
    (jQ : ℕ) (goal target C0 beta betaP bstar K0 A R : ℝ)
    (hbetaP : 0<betaP)
    (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (prime : Bool) (betaCoeff : ℕ → ℂ) (rho : ℝ),
            rho=1 ∨ rho=(-1) →
            (∀n∈Finset.Icc c e,‖betaCoeff n‖≤1) →
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          ‖parityOriginalParityBilinearSource434 d L rho Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellSharpTest434 prime L gamma a b) betaCoeff Y -
            parityOriginalParityBilinearSource434 d L rho Psi
             (Finset.Icc a b) (Finset.Icc c e)
             (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b) betaCoeff Y‖ ≤
            (1+2/Real.log 2)^2*Bound := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_signed_fullcell_quarter_b629_no_log_loss_common_precision434
      jQ goal target C0 beta betaP bstar K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  intro gamma hgamma
  have hSource := hSource gamma hgamma
  filter_upwards [hSource] with L hSourceL
  rcases hSourceL with ⟨hBig,h128,h24,hFamily,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFamily,hReserved,?_⟩
  intro a b c e Y ha hc hab hExpB hY prime betaCoeff rho hSigns hBetaWhole
  let band : Fin (sourceOriginalLiteralDepth 20 L+1) :=
    ⟨jQ,Nat.lt_succ_of_le hReserved⟩
  have hFalse := hRest h128 hFamily a b c e Y ha hc hab hExpB hY
    band rfl (0:Fin 20) prime betaCoeff false hBetaWhole
  have hTrue := hRest h128 hFamily a b c e Y ha hc hab hExpB hY
    band rfl (0:Fin 20) prime betaCoeff true hBetaWhole
  have hDelta :
      (fun m => parityOriginalActualFullCellSharpTest434 prime L gamma a b m -
        parityOriginalActualFullCellProxyBeta434 prime L S gamma a b m) =
      parityOriginalActualFullDyadProxyDifference434 prime L S gamma a b := by
    funext m
    have h := parity_original_actual_fullcell_proxy_plus_delta_eq_test434
      prime L S gamma a b m
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
  dsimp only at hFalse hTrue
  rw [←hDelta] at hFalse hTrue
  rw [←parity_original_signed_first_proxy_difference434
    (sourceOriginalLiteralDepth 20 L) L Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullCellSharpTest434 prime L gamma a b)
    (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
    betaCoeff false 0 Y] at hFalse
  rw [←parity_original_signed_first_proxy_difference434
    (sourceOriginalLiteralDepth 20 L) L Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullCellSharpTest434 prime L gamma a b)
    (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b)
    betaCoeff true 0 Y] at hTrue
  have hLpos : 0<L := by linarith
  have hRho : |rho|≤1 := by
    rcases hSigns with rfl | rfl <;> norm_num
  exact parity_original_parity_replacement_norm_le434
    (sourceOriginalLiteralDepth 20 L) L rho hLpos hRho
    Psi (Finset.Icc a b) (Finset.Icc c e)
    (parityOriginalActualFullCellSharpTest434 prime L gamma a b) betaCoeff
    (parityOriginalActualFullCellProxyBeta434 prime L S gamma a b) betaCoeff
    Y _ hFalse hTrue

/-- The two actual parity-source replacements use different fine exponents and the same H,J,B,S. -/
theorem parity_eventually_original_both_parity_mixed_joint_proxy_steps_common_precision434
    (jQ : ℕ) (goal target C0 beta betaP bstar K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (gammaM gammaN : ℝ), 0 < gammaM → 0 < gammaN →
      ∀ᶠ L : ℝ in atTop, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hce : e≤2*c) (hExpE : (e:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (prime secondPrime : Bool) (rho : ℝ), rho=1 ∨ rho=(-1) →
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          let sharpSharp := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellSharpTest434 prime L gammaM a b)
            (parityOriginalActualFullCellSharpTest434 secondPrime L gammaN c e) Y
          let proxySharp := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellProxyBeta434 prime L S gammaM a b)
            (parityOriginalActualFullCellSharpTest434 secondPrime L gammaN c e) Y
          let proxyProxy := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellProxyBeta434 prime L S gammaM a b)
            (parityOriginalActualFullCellProxyBeta434 secondPrime L S gammaN c e) Y
          let C := (1+2/Real.log 2)^2*Bound
          ‖sharpSharp-proxySharp‖ ≤ C ∧
          ‖proxySharp-proxyProxy‖ ≤ 2*C ∧
          ‖sharpSharp-proxySharp‖+‖proxySharp-proxyProxy‖ ≤ 3*C ∧
          ‖sharpSharp-proxyProxy‖ ≤ 3*C := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_both_parity_first_fullcell_proxy_common_precision434
      jQ goal target C0 beta betaP bstar K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  intro gammaM gammaN hgammaM hgammaN
  have hSourceM := hSource gammaM hgammaM
  have hSourceN := hSource gammaN hgammaN
  have hS : 0 < S := by
    have hB : (0:ℝ) ≤ (B:ℝ) := Nat.cast_nonneg _
    linarith
  have hbpos : 0 < bstar := by linarith
  have hProxy := parity_eventually_original_actual_fullcell_second_proxy_beta_uniform434
    S bstar gammaM hS hbpos hgammaM
  filter_upwards [hSourceM,hSourceN,hProxy] with L hSourceML hSourceNL hProxyL
  rcases hSourceML with ⟨hBig,h128,h24,hFamily,hReserved,hRestM⟩
  rcases hSourceNL with ⟨_,_,_,_,_,hRestN⟩
  refine ⟨hBig,h128,h24,hFamily,hReserved,?_⟩
  intro a b c e Y ha hc hab hExpB hce hExpE hY prime secondPrime rho hSigns
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let N := Finset.Icc c e
  let sharpM := parityOriginalActualFullCellSharpTest434 prime L gammaM a b
  let sharpN := parityOriginalActualFullCellSharpTest434 secondPrime L gammaN c e
  let proxyM := parityOriginalActualFullCellProxyBeta434 prime L S gammaM a b
  let proxyN := parityOriginalActualFullCellProxyBeta434 secondPrime L S gammaN c e
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Bound := (4+Csource*(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
        20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
  let C := (1+2/Real.log 2)^2*Bound
  let s0 := parityOriginalParityBilinearSource434 d L rho Psi K N sharpM sharpN Y
  let s1 := parityOriginalParityBilinearSource434 d L rho Psi K N proxyM sharpN Y
  let s2 := parityOriginalParityBilinearSource434 d L rho Psi K N proxyM proxyN Y
  change ‖s0-s1‖ ≤ C ∧ ‖s1-s2‖ ≤ 2*C ∧
    ‖s0-s1‖+‖s1-s2‖ ≤ 3*C ∧ ‖s0-s2‖ ≤ 3*C
  have hSharpN : ∀n∈N,‖sharpN n‖≤1 := by
    intro n hn
    exact parity_original_actual_fullcell_sharp_test_norm_le_one434
      secondPrime L gammaN c e n
  have hFirst : ‖s0-s1‖ ≤ C := by
    simpa only [s0,s1,d,K,N,sharpM,sharpN,proxyM,C,Bound,C1,Cmoment,Cphys,Csource,M_H]
      using hRestM a b c e Y ha hc hab hExpB hY prime sharpN rho hSigns hSharpN
  have hMlow : Real.exp (bstar*L) ≤ (a:ℝ) := by
    calc
      _ ≤ Real.exp (2*bstar*L) := by
        apply Real.exp_le_exp.mpr
        nlinarith [h128,hbpos]
      _ ≤ (a:ℝ) := ha
  have hProxyNorm : ∀m∈K,‖proxyM m/(2:ℂ)‖≤1 := by
    intro m hm
    exact (hProxyL prime a b hMlow m).2
  have hSwapped :
      ‖parityOriginalParityBilinearSource434 d L rho Psi N K
          sharpN (fun m => proxyM m/(2:ℂ)) Y -
        parityOriginalParityBilinearSource434 d L rho Psi N K
          proxyN (fun m => proxyM m/(2:ℂ)) Y‖ ≤ C := by
    simpa only [d,K,N,sharpN,proxyN,proxyM,C,Bound,C1,Cmoment,Cphys,Csource,M_H]
      using hRestN c e a b Y hc ha hce hExpE hY secondPrime
        (fun m => proxyM m/(2:ℂ)) rho hSigns hProxyNorm
  have hLpos : 0 < L := by linarith
  have hSecond : ‖s1-s2‖ ≤ 2*C :=
    parity_original_parity_second_difference_half_norm_paid434
      d L rho hLpos Psi K N proxyM sharpN proxyN Y C hSwapped
  have hSum : ‖s0-s1‖+‖s1-s2‖ ≤ 3*C := by linarith
  refine ⟨hFirst,hSecond,hSum,?_⟩
  calc
    ‖s0-s2‖ = ‖(s0-s1)+(s1-s2)‖ := by congr 1 <;> ring
    _ ≤ ‖s0-s1‖+‖s1-s2‖ := norm_add_le _ _
    _ ≤ 3*C := hSum

/-- A fixed finite collection of bin pairs has a common eventual threshold and the same source parameters. -/
theorem parity_eventually_original_both_parity_finite_bins_joint_proxy_steps_common_precision434
    {ι : Type*} [Fintype ι]
    (jQ : ℕ) (goal target C0 beta betaP bstar K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (gammaM gammaN : ι → ℝ), (∀ i, 0 < gammaM i) → (∀ i, 0 < gammaN i) →
      ∀ᶠ L : ℝ in atTop, ∀ i : ι, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hab : b≤2*a) (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hce : e≤2*c) (hExpE : (e:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (prime secondPrime : Bool) (rho : ℝ), rho=1 ∨ rho=(-1) →
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          let sharpSharp := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellSharpTest434 prime L (gammaM i) a b)
            (parityOriginalActualFullCellSharpTest434 secondPrime L (gammaN i) c e) Y
          let proxySharp := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellProxyBeta434 prime L S (gammaM i) a b)
            (parityOriginalActualFullCellSharpTest434 secondPrime L (gammaN i) c e) Y
          let proxyProxy := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellProxyBeta434 prime L S (gammaM i) a b)
            (parityOriginalActualFullCellProxyBeta434 secondPrime L S (gammaN i) c e) Y
          let C := (1+2/Real.log 2)^2*Bound
          ‖sharpSharp-proxySharp‖ ≤ C ∧
          ‖proxySharp-proxyProxy‖ ≤ 2*C ∧
          ‖sharpSharp-proxySharp‖+‖proxySharp-proxyProxy‖ ≤ 3*C ∧
          ‖sharpSharp-proxyProxy‖ ≤ 3*C := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_both_parity_mixed_joint_proxy_steps_common_precision434
      jQ goal target C0 beta betaP bstar K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  intro gammaM gammaN hgammaM hgammaN
  exact Filter.eventually_all.mpr (fun i =>
    hSource (gammaM i) (gammaN i) (hgammaM i) (hgammaN i))

end Green64Analytic.Parity

end

end

/-! ## UniformTypeIIIntegratedAudit -/

section

-- Public roots for this exact delta. The prior accepted integration root is retained.

end

/-! ## OriginalBinPartition -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Inserting an actual fixed exponent cut splits the original open/closed bin exactly. -/
theorem parity_original_exponent_bin_split434
    (L a b c : ℝ) (hL : 0 ≤ L) (hab : a ≤ b) (hbc : b ≤ c)
    (n : ℕ) :
    parityOriginalExponentBin434 L a c n ↔
      parityOriginalExponentBin434 L a b n ∨
      parityOriginalExponentBin434 L b c n := by
  have hab' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hL)
  have hbc' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hbc hL)
  unfold parityOriginalExponentBin434
  constructor
  · rintro ⟨ha,hc⟩
    by_cases hb : (n:ℝ) ≤ Real.exp (b*L)
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨lt_of_not_ge hb,hc⟩
  · rintro (⟨ha,hb⟩ | ⟨hb,hc⟩)
    · exact ⟨ha,hb.trans hbc'⟩
    · exact ⟨hab'.trans_lt hb,hc⟩

/-- The bin endpoints assign every integer once, including integer exponential endpoints.
No partition-coverage premise is supplied. -/
theorem parity_original_monotone_bins_weight_partition434
    (L : ℝ) (hL : 0 ≤ L) (t : ℕ → ℝ) (ht : Monotone t)
    (N n : ℕ) (z : ℂ) :
    (∑ i ∈ Finset.range N,
      if parityOriginalExponentBin434 L (t i) (t (i+1)) n then z else 0) =
      if parityOriginalExponentBin434 L (t 0) (t N) n then z else 0 := by
  induction N with
  | zero =>
      have h : ¬ parityOriginalExponentBin434 L (t 0) (t 0) n := by
        rintro ⟨ha,hb⟩
        exact (not_lt_of_ge hb) ha
      simp [h]
  | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      have hs := parity_original_exponent_bin_split434 L (t 0) (t N) (t (N+1))
        hL (ht (Nat.zero_le N)) (ht (Nat.le_succ N)) n
      have hd : ¬ (parityOriginalExponentBin434 L (t 0) (t N) n ∧
          parityOriginalExponentBin434 L (t N) (t (N+1)) n) := by
        rintro ⟨ha,hb⟩
        exact (not_lt_of_ge ha.2) hb.1
      by_cases ha : parityOriginalExponentBin434 L (t 0) (t N) n
      · have hb : ¬ parityOriginalExponentBin434 L (t N) (t (N+1)) n :=
          fun hb => hd ⟨ha,hb⟩
        simp [ha,hb,hs]
      · by_cases hb : parityOriginalExponentBin434 L (t N) (t (N+1)) n
        · simp [ha,hb,hs]
        · simp [ha,hb,hs]

/-- Actual shifted positive-pair fibres commute with restriction of the small factor. -/
theorem parity_original_positive_pair_filter_right434
    (K J : Finset ℕ) (P : ℕ → Prop) (u : ℕ) :
    parityOriginalShiftTwoPositivePairFibre434 K (J.filter P) u =
      (parityOriginalShiftTwoPositivePairFibre434 K J u).filter (fun z => P z.2) := by
  classical
  ext ⟨m,n⟩
  simp only [parityOriginalShiftTwoPositivePairFibre434,Finset.mem_filter]
  constructor
  · rintro ⟨hProd,hRest⟩
    obtain ⟨hm,hn⟩ := Finset.mem_product.mp hProd
    obtain ⟨hn,hp⟩ := Finset.mem_filter.mp hn
    exact ⟨⟨Finset.mem_product.mpr ⟨hm,hn⟩,hRest⟩,hp⟩
  · rintro ⟨⟨hProd,hRest⟩,hp⟩
    obtain ⟨hm,hn⟩ := Finset.mem_product.mp hProd
    exact ⟨Finset.mem_product.mpr ⟨hm,Finset.mem_filter.mpr ⟨hn,hp⟩⟩,hRest⟩

/-- Filtering the original factor carrier is exactly multiplication by its indicator,
with A_rho, Psi and the full original coefficient functions untouched. -/
theorem parity_original_parity_source_filter_right434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (alpha beta : ℕ → ℂ) (Y : ℕ) (P : ℕ → Prop) :
    parityOriginalParityBilinearSource434 d L rho Psi K (J.filter P) alpha beta Y =
      parityOriginalParityBilinearSource434 d L rho Psi K J alpha
        (fun n => if P n then beta n else 0) Y := by
  classical
  unfold parityOriginalParityBilinearSource434
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_positive_pair_filter_right434,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hp : P z.2 <;> simp [hp]

/-- Finite linearity in the second coefficient of the actual u-first Parity source. -/
theorem parity_original_parity_source_sum_right434
    {ι : Type*} (s : Finset ι) (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha : ℕ → ℂ) (beta : ι → ℕ → ℂ) (Y : ℕ) :
    (∑ i ∈ s, parityOriginalParityBilinearSource434 d L rho Psi K J alpha (beta i) Y) =
      parityOriginalParityBilinearSource434 d L rho Psi K J alpha
        (fun n => ∑ i ∈ s, beta i n) Y := by
  classical
  unfold parityOriginalParityBilinearSource434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum]

/-- The original full strict small-factor source is the sum over the real fixed bin
partition. This is an equality of the independently defined A_rho source, not a
declaration that a new aggregate represents it. Coefficients may be nonsmooth. -/
theorem parity_original_both_parity_fixed_bin_source_partition434
    (d : ℕ) (L rho : ℝ) (hL : 0 ≤ L) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y N : ℕ)
    (t : ℕ → ℝ) (ht : Monotone t) :
    parityOriginalParityBilinearSource434 d L rho Psi K
      (J.filter (parityOriginalExponentBin434 L (t 0) (t N))) alpha beta Y =
      ∑ i ∈ Finset.range N,
        parityOriginalParityBilinearSource434 d L rho Psi K
          (J.filter (parityOriginalExponentBin434 L (t i) (t (i+1)))) alpha beta Y := by
  classical
  simp_rw [parity_original_parity_source_filter_right434]
  rw [parity_original_parity_source_sum_right434]
  congr 1
  funext n
  exact (parity_original_monotone_bins_weight_partition434 L hL t ht N n (beta n)).symm

/-- Exact strict unbalanced specialization of the partition identity. -/
theorem parity_original_strict_unbalanced_source_fixed_partition434
    (d : ℕ) (L rho b1 kappa : ℝ) (hL : 0 ≤ L) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y N : ℕ)
    (t : ℕ → ℝ) (ht : Monotone t)
    (hFirst : t 0=b1) (hLast : t N=(1/2:ℝ)-kappa) :
    parityOriginalParityBilinearSource434 d L rho Psi K
      (J.filter (parityOriginalUnbalancedStrictSmallFactor434 L b1 kappa)) alpha beta Y =
      ∑ i ∈ Finset.range N,
        parityOriginalParityBilinearSource434 d L rho Psi K
          (J.filter (parityOriginalExponentBin434 L (t i) (t (i+1)))) alpha beta Y := by
  have h := parity_original_both_parity_fixed_bin_source_partition434
    d L rho hL Psi K J alpha beta Y N t ht
  rw [hFirst,hLast] at h
  exact h
end Green64Analytic.Parity

end

end

/-! ## OriginalCompositeCoverage -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The CLOSED balanced interval in Parity (6.10). This is wider than the
least-prime cutoff used to select the remaining composites. -/
def balancedFactor (L kappa : ℝ) (n : ℕ) : Prop :=
  Real.exp (((1/2:ℝ)-2*kappa)*L) ≤ (n:ℝ) ∧
    (n:ℝ) ≤ Real.exp (((1/2:ℝ)+2*kappa)*L)

/-- Both endpoints of B_kappa are retained, including an integral lower endpoint. -/
theorem parity_original_balanced_factor_iff_nat_interval434
    (L kappa : ℝ) (n : ℕ) :
    balancedFactor L kappa n ↔
      ⌈Real.exp (((1/2:ℝ)-2*kappa)*L)⌉₊ ≤ n ∧
      n ≤ ⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊ := by
  unfold balancedFactor
  rw [Nat.ceil_le, Nat.le_floor_iff (Real.exp_pos _).le]

/-- The real balanced restriction is exactly its closed integer interval. -/
theorem parity_original_balanced_filter_Icc_exact434
    (L kappa : ℝ) (a b : ℕ) :
    (Finset.Icc a b).filter (balancedFactor L kappa) =
      Finset.Icc (max a ⌈Real.exp (((1/2:ℝ)-2*kappa)*L)⌉₊)
        (min b ⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊) := by
  classical
  ext n
  simp only [Finset.mem_filter,Finset.mem_Icc,
    parity_original_balanced_factor_iff_nat_interval434,max_le_iff,le_min_iff]
  tauto

/-- A composite has an actual least-prime/cofactor representation.
There is deliberately no coprimality or distinctness condition. -/
theorem parity_original_composite_least_prime_factorization434
    (N : ℕ) (hN : 2 ≤ N) (hComp : ¬ N.Prime) :
    let p := N.minFac
    let m := N / p
    p.Prime ∧ 2 ≤ m ∧ m*p=N ∧ p ≤ m.minFac ∧ m ≤ N ∧ p ≤ N := by
  dsimp only
  have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hpm : N.minFac ≤ N/N.minFac := Nat.minFac_le_div (by omega) hComp
  have hm : 2 ≤ N/N.minFac := hp.two_le.trans hpm
  have hprod : N/N.minFac*N.minFac=N := Nat.div_mul_cancel (Nat.minFac_dvd N)
  have hDvd : N/N.minFac ∣ N := ⟨N.minFac,hprod.symm⟩
  have hmin : N.minFac ≤ (N/N.minFac).minFac :=
    Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : N/N.minFac≠1)).two_le
      ((Nat.minFac_dvd (N/N.minFac)).trans hDvd)
  exact ⟨hp,hm,hprod,hmin,Nat.div_le_self _ _,Nat.minFac_le (by omega)⟩

/-- If a composite lies below the cube of its least prime, the actual complementary
factor is prime. Squares are included; this counts factors with multiplicity. -/
theorem parity_original_composite_below_minfac_cube_two_primes434
    (N : ℕ) (hN : 2 ≤ N) (hComp : ¬N.Prime)
    (hCube : N < N.minFac^3) :
    (N/N.minFac).Prime ∧ N.minFac.Prime ∧ (N/N.minFac)*N.minFac=N := by
  obtain ⟨hp,hm,hprod,hmin,_,_⟩ :=
    parity_original_composite_least_prime_factorization434 N hN hComp
  have hmPrime : (N/N.minFac).Prime := by
    by_contra hn
    have hsq := Nat.minFac_sq_le_self (by omega : 0<N/N.minFac) hn
    have hsq' : N.minFac^2 ≤ N/N.minFac := by
      have hh := Nat.mul_le_mul hmin hmin
      nlinarith [hsq]
    have hh := Nat.mul_le_mul_right N.minFac hsq'
    nlinarith [hprod]
  exact ⟨hmPrime,hp,hprod⟩

/-- The least-prime choice lies in the genuine gamma-rough cofactor test, including
when the least prime occurs again in the cofactor. -/
theorem parity_original_unbalanced_minfac_rough_test_one434
    (N : ℕ) (hN : 2 ≤ N) (hComp : ¬N.Prime)
    (L gamma : ℝ) (hBin : Real.exp (gamma*L)<(N.minFac:ℝ)) :
    sourceD19RoughTest ((Real.exp L)^gamma) (N/N.minFac)=1 := by
  obtain ⟨_,hm,_,hmin,_,_⟩ :=
    parity_original_composite_least_prime_factorization434 N hN hComp
  have hExp : (Real.exp L)^gamma=Real.exp (gamma*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm]
  have hMin : (N.minFac:ℝ)≤((N/N.minFac).minFac:ℝ) := by exact_mod_cast hmin
  simp [sourceD19RoughTest,hExp,hm,hBin.trans_le hMin]

/-- The original nonnegative parity projections retain the genuine multiplicity
exponent and actual A0 weights. -/
theorem parity_original_parity_A_nonneg434
    (d : ℕ) (L rho : ℝ) (hRho : |rho|≤1) (u : ℕ) :
    0≤parityWeight d L rho u := by
  let e := (-1:ℝ)^sourceOriginalPParityExponent
    (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  have he : |rho*e|≤1 := by simpa [e,abs_mul,abs_pow] using hRho
  have hp : 0≤(1+rho*e)/2 := by
    have hh := (abs_le.mp he).1
    linarith
  exact mul_nonneg (source_original_A0_nonneg 20 _ _ u) hp

/-- The genuine compact Psi support implies the original containing bound for u+2. -/
theorem parity_original_Psi_active_shifted_le_five434
    (L : ℝ) (hL : 0≤L) (Psi : ℝ → ℝ)
    (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (u : ℕ) (hNonzero : Psi ((u:ℝ)/Real.exp L)≠0) :
    ((u+2:ℕ):ℝ)≤5*Real.exp L := by
  have hs := hPsi hNonzero
  have hu : (u:ℝ)≤2*Real.exp L :=
    (div_le_iff₀ (Real.exp_pos L)).mp hs.2
  have hx : 1≤Real.exp L := Real.one_le_exp_iff.mpr hL
  push_cast
  nlinarith

/-- Fixed positive kappa supplies the actual cube separation and containing-constant
slack before any source value is chosen. -/
theorem parity_eventually_original_balanced_cube_and_slack434
    (kappa : ℝ) (hkappa : 0<kappa) (hkappaSmall : kappa<(1/50:ℝ)) :
    ∀ᶠ L : ℝ in atTop, 0≤L ∧
      (5:ℝ)≤Real.exp (kappa*L) ∧
      5*Real.exp L < (Real.exp (((1/2:ℝ)-kappa)*L))^3 := by
  have hGap : 0<(1/2:ℝ)-3*kappa := by linarith
  filter_upwards [eventually_ge_atTop
    (max 0 (max (Real.log 5/kappa) (Real.log 6/((1/2:ℝ)-3*kappa))))] with L hL
  have hL0 : 0≤L := (le_max_left _ _).trans hL
  have h5 : (5:ℝ)≤Real.exp (kappa*L) := by
    have hh : Real.log 5/kappa≤L :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hL)
    have hh' := (div_le_iff₀ hkappa).mp hh
    have hh'' := Real.exp_le_exp.mpr hh'
    simpa [Real.exp_log (by norm_num : (0:ℝ)<5),mul_comm] using hh''
  have h6 : (6:ℝ)≤Real.exp (((1/2:ℝ)-3*kappa)*L) := by
    have hh : Real.log 6/((1/2:ℝ)-3*kappa)≤L :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hL)
    have hh' := (div_le_iff₀ hGap).mp hh
    have hh'' := Real.exp_le_exp.mpr hh'
    simpa [Real.exp_log (by norm_num : (0:ℝ)<6),mul_comm] using hh''
  refine ⟨hL0,h5,?_⟩
  have hid : (Real.exp (((1/2:ℝ)-kappa)*L))^3 =
      Real.exp L * Real.exp (((1/2:ℝ)-3*kappa)*L) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  rw [hid]
  nlinarith [Real.exp_pos L]

/-- Positive factor geometry at the original balanced cutoff, with the source's
containing constant explicitly paid. -/
theorem parity_original_two_factors_mem_balanced434
    (L kappa : ℝ) (hL : 0≤L) (hkappa : 0≤kappa)
    (hFive : (5:ℝ)≤Real.exp (kappa*L))
    (m n : ℕ) (hM : Real.exp (((1/2:ℝ)-kappa)*L)<(m:ℝ))
    (hN : Real.exp (((1/2:ℝ)-kappa)*L)<(n:ℝ))
    (hProduct : (m:ℝ)*(n:ℝ)≤5*Real.exp L) :
    balancedFactor L kappa m ∧
      balancedFactor L kappa n := by
  have hLower : Real.exp (((1/2:ℝ)-2*kappa)*L)≤
      Real.exp (((1/2:ℝ)-kappa)*L) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) hL
  have hpos := Real.exp_pos (((1/2:ℝ)-kappa)*L)
  have hMid : Real.exp (((1/2:ℝ)+kappa)*L)*
      Real.exp (((1/2:ℝ)-kappa)*L)=Real.exp L := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hUp : 5*Real.exp (((1/2:ℝ)+kappa)*L)≤
      Real.exp (((1/2:ℝ)+2*kappa)*L) := by
    have hh := mul_le_mul_of_nonneg_left hFive
      (Real.exp_pos (((1/2:ℝ)+kappa)*L)).le
    have hid : Real.exp (((1/2:ℝ)+kappa)*L)*Real.exp (kappa*L)=
        Real.exp (((1/2:ℝ)+2*kappa)*L) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [hid] at hh
    nlinarith
  have hm0 : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hn0 : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hmUp : (m:ℝ)≤5*Real.exp (((1/2:ℝ)+kappa)*L) := by
    nlinarith [mul_le_mul_of_nonneg_left hN.le hm0]
  have hnUp : (n:ℝ)≤5*Real.exp (((1/2:ℝ)+kappa)*L) := by
    nlinarith [mul_le_mul_of_nonneg_right hM.le hn0]
  exact ⟨⟨hLower.trans hM.le,hmUp.trans hUp⟩,
    ⟨hLower.trans hN.le,hnUp.trans hUp⟩⟩

/-- Original Psi-active balanced composites are covered by ordered prime pairs.
The chosen pair can be diagonal; no squarefree reduction is made. -/
theorem parity_eventually_original_balanced_composite_prime_pair434
    (kappa : ℝ) (hkappa : 0<kappa) (hkappaSmall : kappa<(1/50:ℝ))
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2) :
    ∀ᶠ L : ℝ in atTop, ∀ u : ℕ,
      Psi ((u:ℝ)/Real.exp L)≠0 → ¬(u+2).Prime →
      Real.exp (((1/2:ℝ)-kappa)*L)<((u+2).minFac:ℝ) →
      ∃ m n : ℕ, m.Prime ∧ n.Prime ∧ m*n=u+2 ∧
        balancedFactor L kappa m ∧
        balancedFactor L kappa n := by
  filter_upwards [parity_eventually_original_balanced_cube_and_slack434
    kappa hkappa hkappaSmall] with L hL
  intro u hNonzero hComp hLeast
  have hUpper := parity_original_Psi_active_shifted_le_five434 L hL.1 Psi hPsi u hNonzero
  have hCube : u+2 < (u+2).minFac^3 := by
    have hh : (Real.exp (((1/2:ℝ)-kappa)*L))^3 < ((u+2).minFac:ℝ)^3 := by
      gcongr
    have hReal := hUpper.trans_lt (hL.2.2.trans hh)
    exact_mod_cast hReal
  obtain ⟨hm,hp,hprod⟩ := parity_original_composite_below_minfac_cube_two_primes434
    (u+2) (by omega) hComp hCube
  have hpm := Nat.minFac_le_div (by omega : 0<u+2) hComp
  have hLeastM : Real.exp (((1/2:ℝ)-kappa)*L)<
      ((u+2)/(u+2).minFac:ℕ) := hLeast.trans_le (by exact_mod_cast hpm)
  have hProd : (((u+2)/(u+2).minFac:ℕ):ℝ)*((u+2).minFac:ℝ)≤5*Real.exp L := by
    exact_mod_cast hprod.symm ▸ hUpper
  have hBalanced := parity_original_two_factors_mem_balanced434
    L kappa hL.1 hkappa.le hL.2.1 _ _ hLeastM hLeast hProd
  exact ⟨_,_,hm,hp,hprod,hBalanced.1,hBalanced.2⟩

/-- The original post-replacement W-roughness condition is equivalent on m and m*p
when p>W. A repeated p is permitted; no coprimality is assumed. -/
theorem parity_original_rough_mul_prime_iff434
    (W : ℝ) (m p : ℕ) (hm : 2 ≤ m) (hp : p.Prime) (hW : W < (p : ℝ)) :
    sourceD20Rough W (m*p) ↔ sourceD20Rough W m := by
  have hmp : 2 ≤ m*p := by nlinarith [hp.two_le]
  have hq : (m*p).minFac.Prime := Nat.minFac_prime (by omega)
  have hmPrime : m.minFac.Prime := Nat.minFac_prime (by omega)
  unfold sourceD20Rough
  constructor
  · rintro ⟨_,hMin⟩
    have hh : (m*p).minFac ≤ m.minFac :=
      Nat.minFac_le_of_dvd hmPrime.two_le
        ((Nat.minFac_dvd m).trans (dvd_mul_right m p))
    exact ⟨hm,hMin.trans_le (by exact_mod_cast hh)⟩
  · rintro ⟨_,hMin⟩
    refine ⟨hmp,?_⟩
    rcases hq.dvd_mul.mp (Nat.minFac_dvd (m*p)) with hqm | hqp
    · have hh : m.minFac ≤ (m*p).minFac := Nat.minFac_le_of_dvd hq.two_le hqm
      exact hMin.trans_le (by exact_mod_cast hh)
    · have hh : (m*p).minFac=p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      simpa only [hh] using hW

end Green64Analytic.Parity

end

end

/-! ## OriginalRectangleProxyBounds -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32000

/-- Actual arbitrary full source rectangles: every physical quarter-dyadic cut is
reconstructed with unchanged full-cell proxies, and its count is explicitly paid.
One parameter choice precedes every fixed finite exponent family. No saving premise
or aggregate-source equality is assumed. -/
theorem parity_eventually_original_both_parity_full_rectangles_proxy_steps434
    {ι : Type*} [Fintype ι]
    (jQ : ℕ) (goal target C0 beta betaP bstar K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤bstar)
    (hBeta : beta≤2*bstar)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (gammaM gammaN : ι → ℝ), (∀ i, 0 < gammaM i) → (∀ i, 0 < gammaN i) →
      ∀ᶠ L : ℝ in atTop, ∀ i : ι, (3:ℝ)^16≤L ∧ 128≤L ∧ 24≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (a b c e Y : ℕ)
          (ha : Real.exp (2*bstar*L)≤(a:ℝ))
          (hc : Real.exp (2*bstar*L)≤(c:ℝ))
          (hExpB : (b:ℝ)≤Real.exp (2*L))
          (hExpE : (e:ℝ)≤Real.exp (2*L))
          (hY : Y=⌊2*Real.exp L⌋₊)
          (prime secondPrime : Bool) (rho : ℝ), rho=1 ∨ rho=(-1) →
          let d := sourceOriginalLiteralDepth 20 L
          let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 1
          let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
            A R buf hSmooth hSupport 0
          let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
          let Csource := 1+24*(2+Cphys+24*C1)
          let M_H := ∫s : ℝ, ‖s‖^H *
            ‖(𝓕 (parityOriginalLogCutoff434
              (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
          let Bound := (4+Csource*(∫s : ℝ,
              ‖(𝓕 (parityOriginalLogCutoff434
                (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
                20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
          let sharpSharp := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellSharpTest434 prime L (gammaM i) a b)
            (parityOriginalActualFullCellSharpTest434 secondPrime L (gammaN i) c e) Y
          let proxySharp := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellProxyBeta434 prime L S (gammaM i) a b)
            (parityOriginalActualFullCellSharpTest434 secondPrime L (gammaN i) c e) Y
          let proxyProxy := parityOriginalParityBilinearSource434 d L rho Psi
            (Finset.Icc a b) (Finset.Icc c e)
            (parityOriginalActualFullCellProxyBeta434 prime L S (gammaM i) a b)
            (parityOriginalActualFullCellProxyBeta434 secondPrime L S (gammaN i) c e) Y
          let C := (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*
            ((1+2/Real.log 2)^2*Bound)
          ‖sharpSharp-proxySharp‖ ≤ C ∧
          ‖proxySharp-proxyProxy‖ ≤ 2*C ∧
          ‖sharpSharp-proxySharp‖+‖proxySharp-proxyProxy‖ ≤ 3*C ∧
          ‖sharpSharp-proxyProxy‖ ≤ 3*C := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_both_parity_finite_bins_joint_proxy_steps_common_precision434
      (ι := ι) jQ goal target C0 beta betaP bstar K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  intro gammaM gammaN hgammaM hgammaN
  filter_upwards [hSource gammaM gammaN hgammaM hgammaN] with L hAll
  intro i
  rcases hAll i with ⟨hBig,h128,h24,hFamily,hReserved,hRest⟩
  refine ⟨hBig,h128,h24,hFamily,hReserved,?_⟩
  intro a b c e Y ha hc hExpB hExpE hY prime secondPrime rho hSigns
  let d := sourceOriginalLiteralDepth 20 L
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Bound := (4+Csource*(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
        20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)
  let C := (1+2/Real.log 2)^2*Bound
  let D : ℝ := (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)
  let src := fun pm pn a' b' c' e' =>
    parityOriginalFullCellPairStage434 pm pn prime secondPrime
      d L rho Psi S (gammaM i) (gammaN i) a' b' c' e' Y
  change ‖src false false a b c e-src true false a b c e‖ ≤ D*C ∧
    ‖src true false a b c e-src true true a b c e‖ ≤ 2*(D*C) ∧
    ‖src false false a b c e-src true false a b c e‖+
      ‖src true false a b c e-src true true a b c e‖ ≤ 3*(D*C) ∧
    ‖src false false a b c e-src true true a b c e‖ ≤ 3*(D*C)
  have hL : 0<L := by linarith
  have ha0 : 0<a := by exact_mod_cast (Real.exp_pos _).trans_le ha
  have hc0 : 0<c := by exact_mod_cast (Real.exp_pos _).trans_le hc
  have hLocal : ∀ scale : ℕ×ℕ,
      ‖src false false (max a scale.1) (min b (2*scale.1-1))
          (max c scale.2) (min e (2*scale.2-1)) -
        src true false (max a scale.1) (min b (2*scale.1-1))
          (max c scale.2) (min e (2*scale.2-1))‖ ≤ C ∧
      ‖src true false (max a scale.1) (min b (2*scale.1-1))
          (max c scale.2) (min e (2*scale.2-1)) -
        src true true (max a scale.1) (min b (2*scale.1-1))
          (max c scale.2) (min e (2*scale.2-1))‖ ≤ 2*C := by
    intro scale
    have hma : Real.exp (2*bstar*L)≤((max a scale.1:ℕ):ℝ) :=
      ha.trans (by exact_mod_cast le_max_left a scale.1)
    have hmc : Real.exp (2*bstar*L)≤((max c scale.2:ℕ):ℝ) :=
      hc.trans (by exact_mod_cast le_max_left c scale.2)
    have hba : min b (2*scale.1-1)≤2*max a scale.1 := by
      have h1 := min_le_right b (2*scale.1-1)
      have h2 := le_max_right a scale.1
      omega
    have hec : min e (2*scale.2-1)≤2*max c scale.2 := by
      have h1 := min_le_right e (2*scale.2-1)
      have h2 := le_max_right c scale.2
      omega
    have hbE : ((min b (2*scale.1-1):ℕ):ℝ)≤Real.exp (2*L) :=
      (by exact_mod_cast min_le_left b (2*scale.1-1) : ((min b (2*scale.1-1):ℕ):ℝ)≤(b:ℝ)).trans hExpB
    have heE : ((min e (2*scale.2-1):ℕ):ℝ)≤Real.exp (2*L) :=
      (by exact_mod_cast min_le_left e (2*scale.2-1) : ((min e (2*scale.2-1):ℕ):ℝ)≤(e:ℝ)).trans hExpE
    have h := hRest (max a scale.1) (min b (2*scale.1-1))
      (max c scale.2) (min e (2*scale.2-1)) Y hma hmc hba hbE hec heE hY
      prime secondPrime rho hSigns
    simpa only [src,parityOriginalFullCellPairStage434,parityOriginalFullCellCoefficient434,
      Bool.false_eq_true,ite_false,ite_true,d,C,Bound,C1,Cmoment,Cphys,Csource,M_H]
      using And.intro h.1 h.2.1
  have hC : 0≤C := (norm_nonneg _).trans (hLocal (0,0)).1
  have hCard : ((parityOriginalSourceRectangleDyads434 L a b c e Y).card:ℝ)≤D := by
    dsimp only [D]
    exact_mod_cast parity_original_source_rectangle_dyads_card434 L a b c e Y
  have hFirstCard := parity_original_fullcell_pair_difference_sum_bound434
    false false true false prime secondPrime d L rho hL Psi hPsiSet
    S (gammaM i) (gammaN i) a b c e Y ha0 hc0 C (fun scale _ => (hLocal scale).1)
  have hSecondCard := parity_original_fullcell_pair_difference_sum_bound434
    true false true true prime secondPrime d L rho hL Psi hPsiSet
    S (gammaM i) (gammaN i) a b c e Y ha0 hc0 (2*C) (fun scale _ => (hLocal scale).2)
  have hFirst : ‖src false false a b c e-src true false a b c e‖≤D*C :=
    hFirstCard.trans (mul_le_mul_of_nonneg_right hCard hC)
  have hSecond : ‖src true false a b c e-src true true a b c e‖≤2*(D*C) := by
    have hh := hSecondCard.trans (mul_le_mul_of_nonneg_right hCard (by positivity : 0≤2*C))
    nlinarith [hh]
  have hSum : ‖src false false a b c e-src true false a b c e‖+
      ‖src true false a b c e-src true true a b c e‖ ≤ 3*(D*C) := by linarith
  refine ⟨hFirst,hSecond,hSum,?_⟩
  calc
    _ = ‖(src false false a b c e-src true false a b c e)+
        (src true false a b c e-src true true a b c e)‖ := by congr 1 <;> ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := hSum
end Green64Analytic.Parity

end

end

