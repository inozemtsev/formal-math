module

public import Green64.Library.Sieve.Foundations.Part023
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part020
public import Green64.Library.Sieve.Foundations.Part019
public import Green64.Library.Sieve.Foundations.Part018
public import Green64.Library.Sieve.Foundations.Part017
public import Green64.Library.Weights.Part113

@[expose] public section

/-!
# Sieve / Foundations / Part024

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalActualKZ417Window -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Every NONEMPTY genuine source physical original Parity (4.13)
canonical k/Z fibre has k≠0, with BOTH h=-2 Q/P positive endpoint
carriers. Even if the arbitrary input K,J includes nonsupported
cofactor pairs, a nonempty physical event cannot have k=0. -/
theorem parity_original_historical_nonempty_actual_k_z_nonzero434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e)
    (hNonempty : (parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z).Nonempty) : k≠0 := by
  obtain ⟨q,hq⟩ := hNonempty
  have hMem := Finset.mem_filter.mp hq
  have hMP := (Finset.mem_product.mp hMem.1).1
  have hMNe : m≠q.1 := (Finset.mem_erase.mp (Finset.mem_filter.mp hMP).1).1.symm
  have hK := (Finset.mem_filter.mp hMP).2
  have hValid := hMem.2.1
  have hPos := parity_original_historical_supported_canonical_z_positive_shift434
    d L band slot δ Y e m q.1 q.2 he hMNe hValid
  rw [hK] at hPos
  exact hPos.1

/-- The dyadic Z in every NONEMPTY actual original h=-2 source
physical k/Z fibre lies in the precise manuscript Parity (4.17)
range exp L*L^(-(K0+90))<=Z<=exp L*L^(K0+90).
This range is DERIVED from actual source e-window, m,m' and n dyads,
real original Q/P physical positive u supports and the exact
canonical z=m'v; it is NOT an independent assumption on guessed Z.
This closes the Z-envelope legality gate for applying the already
native-proved per-character Parity (4.17) correlation estimate later. -/
theorem parity_original_historical_nonempty_actual_k_z_parity417_window434
    (d : ℕ) (L U V E K0 : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (J K : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (hL : 8≤L) (hK0 : 0≤K0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0))
    (hWin : parityOriginalHistoricalEWindow434 L E e)
    (he : Odd e) (hmLo : U≤(m:ℝ))
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (hnLo : ∀n∈J,V≤(n:ℝ))
    (hNonempty : (parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m K J k Z).Nonempty) :
    Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
    (Z:ℝ)≤Real.exp L*L^(K0+90) := by
  obtain ⟨q,hq⟩ := hNonempty
  let z := parityOriginalHistoricalCanonicalZ434 e m q.1 q.2
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMp := (Finset.mem_filter.mp hProd.1).1
  have hneq : m≠q.1 := (Finset.mem_erase.mp hMp).1.symm
  have hMpK := (Finset.mem_erase.mp hMp).2
  have hMpDyad := hDyad q.1 hMpK
  have hValid := hMem.2.1
  have hScale := hMem.2.2.2
  have hzJ : z∈parityOriginalHistoricalCanonicalZSupport434 e m q.1 J :=
    Finset.mem_image.mpr ⟨q.2,hProd.2,rfl⟩
  have hnF : q.2∈parityOriginalHistoricalCanonicalZNFibre434 e m q.1 J z :=
    Finset.mem_filter.mpr ⟨hProd.2,rfl⟩
  have hzPhysical : z∈parityOriginalHistoricalPhysicalValidZSupport434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m q.1 J := by
    exact Finset.mem_filter.mpr
      ⟨hzJ,⟨q.2,Finset.mem_filter.mpr ⟨hnF,hValid⟩⟩⟩
  have hWinZ := parity_original_historical_supported_z_actual_parity417_Z_envelope434
    d L U V E K0 band slot δ J e m q.1 z hL hK0 hU hV hUV hE hWin
    he hneq hmLo hMpDyad.1 hMpDyad.2 hnLo hzPhysical
  change parityOriginalHistoricalActualZDyadicScale434 z=Z at hScale
  rw [hScale] at hWinZ
  exact hWinZ


/-- The ORIGINAL source physical nonzero k at any populated
canonical k/Z cofactor fibre obeys the exact logarithmic bound
|k| < L^(K0+88) from the original e-window E L^-88<=e,
E=U L^-K0, and original m,m' dyads. Unlike the character mask,
this bound requires NO nonzero fine alpha or analytic hypothesis:
we derive the TRUE determinant m'-m=e*k from the original two
populated Q/P endpoint witnesses. -/
theorem parity_original_historical_nonempty_actual_k_polylog434
    (d : ℕ) (L U E K0 : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (hL : 8≤L) (hU : 0<U)
    (hE : E=U*L^(-K0))
    (hWin : parityOriginalHistoricalEWindow434 L E e)
    (he : Odd e)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)<2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (hNonempty : (parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z).Nonempty) :
    (k.natAbs:ℝ)<L^(K0+88) := by
  obtain ⟨q,hq⟩ := hNonempty
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMP := Finset.mem_filter.mp hProd.1
  have hneq : m≠q.1 := (Finset.mem_erase.mp hMP.1).1.symm
  have hMPK := (Finset.mem_erase.mp hMP.1).2
  have hMPDyad := hDyad q.1 hMPK
  have hK : parityOriginalHistoricalOffdiagK434 e m q.1=k := hMP.2
  obtain ⟨u,hu,up,hup,⟨vStar,hvs⟩,⟨vpStar,hvps⟩⟩ := hMem.2.1
  have huPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0<up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hgate := (Finset.mem_filter.mp hvs).2
  have hgatep := (Finset.mem_filter.mp hvps).2
  have hmn := (Finset.mem_filter.mp hu).2.2.2
  have hmpn := (Finset.mem_filter.mp hup).2.2.2
  have hPhys := parity_original_historical_actual_k_quotient_source434
    L e m q.1 q.2 u up vStar vpStar he huPos hupPos
    hgate hgatep hmn hmpn hneq
  have hShift : ((q.1:ℤ)-(m:ℤ))=(e:ℤ)*k := by
    simpa only [hK] using hPhys.2.1
  have hLp : 0<L := by linarith
  exact parity_original_historical_k_polylog_from_real_e_window434
    L U E K0 e m q.1 k hLp hU hE hWin
    hmLo hmHi hMPDyad.1 hMPDyad.2 hShift

/-- FULL SOURCE LEGALITY CONTRACT for the existing per-character
Parity (4.17) estimate on any nonempty ORIGINAL physical k/Z fibre:
nonzero k, actual |k|<L^(K0+88), and true dyadic
Z∈[exp L*L^(-(K0+90)),exp L*L^(K0+90)]. Both limits are PROVED
from physical source data, not inserted as arbitrary range input.
Original beta/4 Ppart and smooth ψ_Z endpoint normalization,
full Fourier moment bounds and Type II summation remain OPEN. -/
theorem parity_original_historical_nonempty_actual_k_z_parity417_legality434
    (d : ℕ) (L U V E K0 : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (J K : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (hL : 8≤L) (hK0 : 0≤K0)
    (hU : 0<U) (hV : 0<V) (hUV : Real.exp L≤U*V)
    (hE : E=U*L^(-K0))
    (hWin : parityOriginalHistoricalEWindow434 L E e)
    (he : Odd e) (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)<2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (hnLo : ∀n∈J,V≤(n:ℝ))
    (hNonempty : (parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m K J k Z).Nonempty) :
    k≠0 ∧ (k.natAbs:ℝ)<L^(K0+88) ∧
      Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
      (Z:ℝ)≤Real.exp L*L^(K0+90) := by
  have hk := parity_original_historical_nonempty_actual_k_z_nonzero434
    d L band slot δ ⌊2*Real.exp L⌋₊ e m K J k Z he hNonempty
  have hsize := parity_original_historical_nonempty_actual_k_polylog434
    d L U E K0 band slot δ ⌊2*Real.exp L⌋₊ e m K J k Z
    hL hU hE hWin he hmLo hmHi hDyad hNonempty
  have hZ := parity_original_historical_nonempty_actual_k_z_parity417_window434
    d L U V E K0 band slot δ J K e m k Z
    hL hK0 hU hV hUV hE hWin he hmLo hDyad hnLo hNonempty
  exact ⟨hk,hsize,hZ.1,hZ.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZFourierTwists -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Original physical Parity (4.15)-(4.16) m-cofactor Fourier phase,
including the TRUE 2π factor and dyadic normalization U. Only m and
frequency ξ0 appear: it is constant over the ENTIRE physical
m',z,n source fibre and can be pulled outside the finite correlation. -/
def parityOriginalHistoricalActualMOuterFourierPhase434
    (U : ℝ) (m : ℕ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (((2*Real.pi*(ξ 0)*Real.log ((m:ℝ)/U):ℝ):ℂ)*Complex.I)

/-- Original physical Parity (4.16) genuine m',z cofactor character
Fourier phases, each with the actual original normalized log(m'/U),
log(z/Z) and the source-matched 2π. This is NOT an abstract Fourier
character or a replaced prime-slot kernel. -/
def parityOriginalHistoricalActualMpZFourierPhase434
    (U Z : ℝ) (mp z : ℕ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (((2*Real.pi*(ξ 1)*Real.log ((mp:ℝ)/U):ℝ):ℂ)*Complex.I) *
  Complex.exp (((2*Real.pi*(ξ 2)*Real.log ((z:ℝ)/Z):ℝ):ℂ)*Complex.I)

/-- Exact original 3D Euclidean Fourier phase factors into one
m-only outer logarithmic twist and one (m',z)-only inner twist at
EVERY point, including signed negative Fourier frequencies.
This identity has ZERO analytic assumptions and no #characters loss. -/
theorem parity_original_historical_real_3d_m_mp_z_phase_factor434
    (U Z : ℝ) (m mp z : ℕ)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    parityOriginal3DPhysicalLogFourierPhase434 ξ
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z) =
    parityOriginalHistoricalActualMOuterFourierPhase434 U m ξ *
      parityOriginalHistoricalActualMpZFourierPhase434 U Z mp z ξ := by
  unfold parityOriginal3DPhysicalLogFourierPhase434
    parityOriginalHistoricalActualMOuterFourierPhase434
    parityOriginalHistoricalActualMpZFourierPhase434
  simpa only [mul_assoc] using
    (parity_original_historical_log_triple_fourier_phase434 U Z m mp z ξ)

/-- TRUE source-normalized physical (m',z) twisted cofactor sum on
one canonical original k/Z dyad, with the original signed H0/Q/P
complex weight and the original χ(m') and b629 alpha carried in W.
No synthetic ζ Fourier multiplier, no source gating dropped. -/
def parityOriginalHistoricalActualKZMpZTwistedCorrelation434
    (d : ℕ) (L U : ℝ) (Z : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (ζ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∑q∈parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z,
    parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
      d L band slot δ ξ rho α signed Y e m k χ q *
    parityOriginalHistoricalActualMpZFourierPhase434
      U (Z:ℝ) q.1 (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) ζ

/-- The source-signature Parity (4.15)-(4.16) frequency integrand,
written with the SAME true original eta_e,eta_n Fourier Schwartz
kernel as the Cauchy square; the m-only phase is now OUTSIDE the
physical (m',z,n) signed χ-correlation sum. -/
def parityOriginalHistoricalActualKZTwistedFourierIntegrand434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (Z : ℕ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ, buf t ≠ 0 → a≤t ∧ t≤b)
    (ζ : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (𝓕 (parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport) :
    𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
  parityOriginalHistoricalActualMOuterFourierPhase434 U m ζ *
  parityOriginalHistoricalActualKZMpZTwistedCorrelation434
    d L U Z band slot δ ξ rho α signed Y e m K J k χ ζ

/-- **TRUE PHYSICAL SOURCE Parity (4.16) TWIST FACTORIZATION**:
The complete original signed, character, beta/P/Q-gated physical
k/Z cofactor source Fourier integrand is IDENTICALLY the Fourier
Schwartz multiplier times the outer m-only log twist times the
inner physical m',z log-twisted character correlation.

This is the actual algebraic extraction needed BEFORE applying
Parity(4.17), not a conditional desired saving. It neither suppresses
k or z source fibres nor moves a factor depending on n outside the
physical sum; 2πξ frequencies remain exact. -/
theorem parity_original_historical_actual_k_z_twisted_physical_factor434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (Z : ℕ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ, buf t ≠ 0 → a≤t ∧ t≤b)
    (ζ : EuclideanSpace ℝ (Fin 3)) :
    parityOriginal3DPhysicalFiniteTwistedSource434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
      (parityOriginalHistoricalPhysicalFourierEventTriple434
        U (Z:ℝ) e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2))
      (parityOriginalHistoricalActualDyadicCutoffSchwartz434
        L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport) ζ =
    parityOriginalHistoricalActualKZTwistedFourierIntegrand434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hBufSmooth hBufSupport ζ := by
  unfold parityOriginal3DPhysicalFiniteTwistedSource434
    parityOriginalHistoricalActualKZTwistedFourierIntegrand434
    parityOriginalHistoricalActualKZMpZTwistedCorrelation434
  rw [mul_assoc]
  congr 1
  let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho α signed Y e m k χ
  change ∑q∈S,W q*parityOriginal3DPhysicalLogFourierPhase434 ζ
      (parityOriginalHistoricalRealLogTriple434 U (Z:ℝ) m q.1
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)) =
    parityOriginalHistoricalActualMOuterFourierPhase434 U m ζ *
      ∑q∈S,W q*parityOriginalHistoricalActualMpZFourierPhase434
        U (Z:ℝ) q.1 (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) ζ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [parity_original_historical_real_3d_m_mp_z_phase_factor434]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZ416Trunc -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- HISTORICAL ORIGINAL Parity (4.10)-(4.16) complete SOURCE twisted
Fourier step for one real, physically populated k/Z dyadic cell:

  original selected Q/P h=-2 signed character Cauchy offdiagonal
    = ∫_{||ζ||≤T} \\hat{F}_{L,k,Z}(ζ) ×
       exp(2πi ζ₁ log(m/U)) × original χ(m')
       × (m'/U)^(2πiζ₂) × (z/Z)^(2πiζ₃) [m',z,n physical source]
       + Err,

  |Err| ≤ [actual original cofactor l1 mass] × B_H(source F)/T^H.

The original m',z,n support is the exact source k/Z fibre, not
an artificial full dyadic interval. Both Q/P endpoints and sigma=0,
complex H0, true b629 alpha, epsilon branch, χ, and 2π are retained.
No unproved uniform B_H, character saving, ψ_Z support conversion,
or full Parity(4.17)/(4.2) is used. -/
theorem parity_original_historical_actual_k_z_416_fourier_trunc434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (U E V : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2),buf x=1)
    (hZ : 0<Z) (H : ℕ) (T : ℝ) (hT : 0<T) :
    ‖(∑mp∈parityOriginalHistoricalActualPhysicalDyadicMFibre434
        d L band slot δ Y e m K J k Z,
        χ (mp : ZMod (2*k.natAbs)) *
        (∑z∈parityOriginalHistoricalActualPhysicalZDyadicFibre434
          d L band slot δ Y e m mp J Z,
          ∑n∈(parityOriginalHistoricalCanonicalZNFibre434 e m mp J z).filter
            (parityOriginalHistoricalPhysicalValidN434 d L band slot δ Y e m mp),
            ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) *
              parityOriginalHistoricalOffdiagPhysicalAtENMMp434
                d L band slot δ ξ rho α signed Y e n m mp)) -
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginalHistoricalActualKZTwistedFourierIntegrand434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hBufSmooth hBufSupport ζ)‖ ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport)/T^H) := by
  have hOld := parity_original_historical_actual_nested_character_dyadic_3d_trunc434
    d L hL band slot δ ξ rho α signed Y e m K J k Z χ he
    U E V hU hE hV hmLo hmHi hDyad
    buf a b hBufSmooth hBufSupport hBufOne hZ H T hT
  have hNew :
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434
          (parityOriginalHistoricalActualKZPhysicalEventCarrier434
            d L band slot δ Y e m K J k Z)
          (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
            d L band slot δ ξ rho α signed Y e m k χ)
          (parityOriginalHistoricalPhysicalFourierEventTriple434
            (U:ℝ) (Z:ℝ) e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2))
          (parityOriginalHistoricalActualDyadicCutoffSchwartz434
            L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport) ζ) =
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginalHistoricalActualKZTwistedFourierIntegrand434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hBufSmooth hBufSupport ζ) := by
    apply integral_congr_ae
    filter_upwards [] with ζ
    exact parity_original_historical_actual_k_z_twisted_physical_factor434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hBufSmooth hBufSupport ζ
  rw [hNew] at hOld
  exact hOld
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZUniqueCofactor -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- GENUINE physical original h=-2 determinant m'-m=e*k on a
populated TWO-ENDPOINT Q/P original reserved-prime (4.13) source
cofactor, with the actual B509 and prime-power gates kept intact.
No guessed divisibility or quotient property on arbitrary m' is
assumed; the equality follows from actual source u,u',vStar,vStar'. -/
theorem parity_original_historical_physical_k_exact_cofactor_shift434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n) :
    (mp:ℤ)-(m:ℤ)=(e:ℤ)*parityOriginalHistoricalOffdiagK434 e m mp := by
  obtain ⟨u,hu,up,hup,⟨vStar,hvs⟩,⟨vpStar,hvps⟩⟩ := hValid
  have huPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hupPos : 0<up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hgate := (Finset.mem_filter.mp hvs).2
  have hgatep := (Finset.mem_filter.mp hvps).2
  have hmn := (Finset.mem_filter.mp hu).2.2.2
  have hmpn := (Finset.mem_filter.mp hup).2.2.2
  have hPhys := parity_original_historical_actual_k_quotient_source434
    L e m mp n u up vStar vpStar he huPos hupPos
    hgate hgatep hmn hmpn hneq
  exact hPhys.2.1

/-- At fixed ORIGINAL selected e,m and canonical integer k,
there is at most ONE real physical m' on ANY genuinely populated
h=-2 source data, even if source n and canonical z vary.
This is purely arithmetic m'=m+e*k; it does not assert a singleton
for every formal quotient fibre outside physical Q/P support. -/
theorem parity_original_historical_physical_same_k_cofactor_unique434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp mp' n n' : ℕ) (k : ℤ) (he : Odd e)
    (hneq : m≠mp) (hneq' : m≠mp')
    (hn : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hn' : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp' n')
    (hk : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (hk' : parityOriginalHistoricalOffdiagK434 e m mp'=k) : mp=mp' := by
  have h := parity_original_historical_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m mp n he hneq hn
  have h' := parity_original_historical_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m mp' n' he hneq' hn'
  rw [hk] at h
  rw [hk'] at h'
  have hh : (mp:ℤ)=(mp':ℤ) := by omega
  exact_mod_cast hh

/-- On one actual original signed Parity(4.16) physical k/Z event
carrier the projection to the physical cofactor m' has cardinality
AT MOST ONE. The remaining n/z correlation may still have MANY
terms; this lemma prevents a fictitious #m' factor when moving the
outer m-phase and character χ across the common Fourier kernel.
The true h=-2 source physical endpoint gates are essential. -/
theorem parity_original_historical_actual_k_z_physical_cofactor_card_le_one434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) :
    ((parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z).image Prod.fst).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro mp hmp mp' hmp'
  obtain ⟨⟨x,n⟩,hx,hxEq⟩ := Finset.mem_image.mp hmp
  obtain ⟨⟨x',n'⟩,hx',hxEq'⟩ := Finset.mem_image.mp hmp'
  dsimp only at hxEq hxEq'
  have hData := Finset.mem_filter.mp hx
  have hData' := Finset.mem_filter.mp hx'
  have hXM := (Finset.mem_filter.mp (Finset.mem_product.mp hData.1).1)
  have hXM' := (Finset.mem_filter.mp (Finset.mem_product.mp hData'.1).1)
  have hneq : m≠x := (Finset.mem_erase.mp hXM.1).1.symm
  have hneq' : m≠x' := (Finset.mem_erase.mp hXM'.1).1.symm
  have hUnique := parity_original_historical_physical_same_k_cofactor_unique434
    d L band slot δ Y e m x x' n n' k he hneq hneq'
    hData.2.1 hData'.2.1 hXM.2 hXM'.2
  calc
    mp = x := hxEq.symm
    _ = x' := hUnique
    _ = mp' := hxEq'
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalPairMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact original h=-2 SOURCE physical cofactor pair mass is the
PRODUCT of two actual Cauchy endpoint amplitudes, including the
original signed epsilon, H0, real selected Q/P gates, b629 alpha and
complex conjugate. The proof is algebraic; it does not replace the
physical source by a new prime-slot kernel. -/
theorem parity_original_historical_real_physical_pair_norm_product434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) :
    ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp‖ =
    ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖ *
    ‖α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n mp‖ := by
  rw [←parity_original_historical_actual_ENM_pair_eq_gated_source434
    d L band slot δ ξ rho α signed Y e n m mp]
  rw [norm_mul,norm_star]

/-- Original complete physical signed m≠m' Cauchy cofactor pair is
bounded pointwise by the ARITHMETIC mean of the TWO positive actual
SOURCE diagonal summands. Unlike bounding the signed offdiagonal
by its unweighted value, this uses only a correct absolute-value
inequality 2ab<=a²+b², and no assumed Parity (4.17) cancellation. -/
theorem parity_original_historical_real_physical_pair_norm_le_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) :
    ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp‖ ≤
    (‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖^2 +
     ‖α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n mp‖^2)/2 := by
  rw [parity_original_historical_real_physical_pair_norm_product434]
  let A : ℝ := ‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖
  let B : ℝ := ‖α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n mp‖
  change A*B≤(A^2+B^2)/2
  nlinarith [sq_nonneg (A-B)]

/-- ORIGINAL historical real character source physical pair mass is
never larger than its genuine positive diagonal mean, since native
Dirichlet characters modulo 2|k| have norm at most one. This is
per-term and does NOT introduce a #characters bound. -/
theorem parity_original_historical_character_pair_norm_le_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    ‖χ (mp : ZMod (2*k.natAbs)) *
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho α signed Y e n m mp‖ ≤
    (‖α m*parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖^2 +
     ‖α mp*parityOriginalHistoricalCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n mp‖^2)/2 := by
  rw [norm_mul]
  have hχ : ‖χ (mp : ZMod (2*k.natAbs))‖≤1 :=
    DirichletCharacter.norm_le_one χ _
  have hNorm : 0≤‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho α signed Y e n m mp‖ := norm_nonneg _
  calc
    _ ≤ 1*‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho α signed Y e n m mp‖ :=
      mul_le_mul_of_nonneg_right hχ hNorm
    _ = ‖parityOriginalHistoricalOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho α signed Y e n m mp‖ := one_mul _
    _ ≤ _ := parity_original_historical_real_physical_pair_norm_le_diagonal434
      d L band slot δ ξ rho α signed Y e n m mp
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalKZMassDiagonal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- TRUE source physical pair at any e,n,m,m'∈K, twisted by ANY
Dirichlet character, is bounded by the full ORIGINAL e,n positive
diagonal sum over all actual m0∈K. No assumption on the number of
possible m' or analytic correlation saving. -/
theorem parity_original_historical_physical_character_pair_norm_le_en_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) (K : Finset ℕ) (hm : m∈K) (hmp : mp∈K)
    (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    ‖χ (mp : ZMod (2*k.natAbs)) *
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp‖ ≤
    ∑r∈K, ‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2 := by
  let F : ℕ → ℝ := fun r =>
    ‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2
  have hNonneg : ∀r∈K,0≤F r := by
    intro r hr
    exact sq_nonneg _
  have ha : F m ≤ ∑r∈K,F r := Finset.single_le_sum hNonneg hm
  have hb : F mp ≤ ∑r∈K,F r := Finset.single_le_sum hNonneg hmp
  have hPair := parity_original_historical_character_pair_norm_le_diagonal434
    d L band slot δ ξ rho α signed Y e n m mp k χ
  change ‖χ (mp : ZMod (2*k.natAbs))*
      parityOriginalHistoricalOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp‖ ≤ ∑r∈K,F r
  nlinarith [hPair,ha,hb]

/-- At fixed source selected e and actual canonical k/Z, the
complete TRUE original signed character Fourier cofactor l1 mass
has no extra #m' loss: physical m' is UNIQUE and the sum over
actual n is bounded by the genuine e-fixed original Cauchy
positive diagonal ∑_{n∈J,r∈K}|α_r A(e,n,r)|².

This is an exact structural bound, independent of the original
fine α, signed epsilon, k,Z size, or χ. It is NOT an estimate on
the Fourier-transformed 4.17 core; it bounds the genuine SOURCE
truncation coefficient cost before the main cancellation theorem. -/
theorem parity_original_historical_actual_k_z_physical_l1_mass_le_e_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hm : m∈K)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) ≤
    ∑n∈J,∑r∈K,‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2 := by
  let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho α signed Y e m k χ
  let D : ℕ → ℝ := fun n =>
    ∑r∈K,‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2
  have hD : ∀n,0≤D n := by
    intro n
    apply Finset.sum_nonneg
    intro r hr
    exact sq_nonneg _
  change (∑q∈S,‖W q‖) ≤ ∑n∈J,D n
  by_cases hEmpty : S.Nonempty
  · obtain ⟨q0,hq0⟩ := hEmpty
    have h0Prod := Finset.mem_product.mp (Finset.mem_filter.mp hq0).1
    have h0Mp := (Finset.mem_filter.mp h0Prod.1)
    have h0K : q0.1∈K := (Finset.mem_erase.mp h0Mp.1).2
    have h0Ne : m≠q0.1 := (Finset.mem_erase.mp h0Mp.1).1.symm
    have h0Valid := (Finset.mem_filter.mp hq0).2.1
    let mp0 := q0.1
    let S0 : Finset (ℕ×ℕ) := ({mp0}:Finset ℕ).product J
    have hUnique (q : ℕ×ℕ) (hq : q∈S) : q.1=mp0 := by
      have hqProd := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      have hqMp := Finset.mem_filter.mp hqProd.1
      have hqNe : m≠q.1 := (Finset.mem_erase.mp hqMp.1).1.symm
      exact parity_original_historical_physical_same_k_cofactor_unique434
        d L band slot δ Y e m q.1 mp0 q.2 q0.2 k he hqNe h0Ne
        (Finset.mem_filter.mp hq).2.1 h0Valid hqMp.2 h0Mp.2
    have hSub : S ⊆ S0 := by
      intro q hq
      have hqJ := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr (hUnique q hq),hqJ⟩
    have hSbound : (∑q∈S,‖W q‖) ≤ ∑q∈S0,‖W q‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub
        (fun q hq hnot => norm_nonneg _)
    have hS0 : (∑q∈S0,‖W q‖) = ∑n∈J,‖W (mp0,n)‖ := by
      dsimp [S0]
      rw [Finset.sum_product]
      simp
    have hPoint (n : ℕ) : ‖W (mp0,n)‖ ≤ D n := by
      exact parity_original_historical_physical_character_pair_norm_le_en_diagonal434
        d L band slot δ ξ rho α signed Y e n m mp0 K hm h0K k χ
    calc
      _ ≤ ∑q∈S0,‖W q‖ := hSbound
      _ = ∑n∈J,‖W (mp0,n)‖ := hS0
      _ ≤ ∑n∈J,D n := Finset.sum_le_sum (fun n hn => hPoint n)
  · have hSEmpty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    rw [hSEmpty]
    simp only [Finset.sum_empty]
    exact Finset.sum_nonneg (fun n hn=> hD n)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalKZMassPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The true ORIGINAL source e-fixed positive squared H0 Cauchy
mass is a SINGLE summand of the complete historical selected-e
ACTIVE diagonal. This uses actual e∈Q source support and
nonnegative squares; unlike the signed original offdiagonal,
there is no invalid monotonicity of complex cancellation. -/
theorem parity_original_historical_actual_e_fixed_diagonal_le_active434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e : ℕ) (K J : Finset ℕ)
    (he : e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ) :
    (∑n∈J,∑r∈K,‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2) ≤
    parityOriginalHistoricalActiveCauchyDiagonal434
      d L E band slot δ ξ rho K J α signed Y := by
  let F : ℕ → ℝ := fun e0 =>
    ∑n∈J,∑r∈K,‖α r*parityOriginalHistoricalCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e0 n r‖^2
  have hF : ∀e0∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ, 0≤F e0 := by
    intro e0 he0
    apply Finset.sum_nonneg
    intro n hn
    apply Finset.sum_nonneg
    intro r hr
    exact sq_nonneg _
  change F e≤∑e0∈parityOriginalHistoricalCauchyActiveESupport434
    d L E band slot δ,F e0
  exact Finset.single_le_sum hF he

/-- The genuine original physical h=-2 canonical k/Z Fourier
cofactor signed/χ absolute coefficient mass is bounded by the
complete ACTUAL selected-e Cauchy diagonal for any original e in
that support. No factor #k, #Z, #m' or #chars is introduced:
this is PER physical selected e,m,k,Z,χ. -/
theorem parity_original_historical_actual_k_z_l1_mass_le_active_diagonal434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e)
    (heMem : e∈parityOriginalHistoricalCauchyActiveESupport434
      d L E band slot δ)
    (hm : m∈K) (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) ≤
    parityOriginalHistoricalActiveCauchyDiagonal434
      d L E band slot δ ξ rho K J α signed Y := by
  exact (parity_original_historical_actual_k_z_physical_l1_mass_le_e_diagonal434
    d L band slot δ ξ rho α signed Y e m K J k Z he hm χ).trans
    (parity_original_historical_actual_e_fixed_diagonal_le_active434
      d L E band slot δ ξ rho α signed Y e K J heMem)

/-- SOURCE UNCONDITIONAL fixed exponent bound for an individual
historical signed Parity (4.15) k/Z physical Fourier coefficient l1
mass. The original selected-e positive Cauchy diagonal has a fixed
shifted-divisor moment exponent 2*C_W1+256; this proof transfers it
to ALL genuine supported per-e,m,k,Z,χ signed coefficient masses,
without assuming the desired terminal 4.17 correlation saving.
The result is bounded by X=e^L times a fixed power of L; later
source Z~X polylog permits rewriting in the original (4.15) scale. -/
theorem parity_eventually_original_historical_actual_k_z_l1_mass_polylog434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho E : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ), 0≤Acoef →
        (∀m∈K, ‖α m‖≤Acoef) →
        ∀ (e m : ℕ) (k : ℤ) (Z : ℕ)
          (he : Odd e),
        e∈parityOriginalHistoricalCauchyActiveESupport434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ →
        m∈K →
        ∀ χ : DirichletCharacter ℂ (2*k.natAbs),
        parityOriginal3DPhysicalFiniteCoefficientMass434
          (parityOriginalHistoricalActualKZPhysicalEventCarrier434
            (sourceOriginalLiteralDepth 20 L) L band slot δ
            ⌊2*Real.exp L⌋₊ e m K J k Z)
          (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
            (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α signed
            ⌊2*Real.exp L⌋₊ e m k χ) ≤
        Acoef^2*Real.exp L*
          L^(2*parityOriginalW1PolylogExponent434+256) := by
  filter_upwards [parity_eventually_original_historical_active_diagonal_polylog434]
    with L hDiag
  refine ⟨hDiag.1,?_⟩
  intro band slot δ ξ rho E K J α signed Acoef hA hα e m k Z he heMem hm χ
  exact (parity_original_historical_actual_k_z_l1_mass_le_active_diagonal434
    (sourceOriginalLiteralDepth 20 L) L E band slot δ ξ rho α signed
    ⌊2*Real.exp L⌋₊ e m K J k Z he heMem hm χ).trans
    (hDiag.2 band slot δ ξ E rho K J α signed Acoef hA hα)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalKZMassZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Exact quantitative original Parity (4.15) conversion from the
REAL source lower Z bound to the manuscript Z scale. For positive
L and any fixed exponents C and K0, physical
Z≥exp L * L^(-(K0+90)) implies
exp L * L^C ≤ Z * L^(C+K0+90). The original source x=e^L is
NEVER confused with the log variable L itself. -/
theorem parity_original_historical_source_X_to_Z_polylog434
    (L Z C K0 : ℝ) (hL : 0<L)
    (hZ : Real.exp L*L^(-(K0+90))≤Z) :
    Real.exp L*L^C ≤ Z*L^(C+K0+90) := by
  have hP : 0<L^(K0+90) := Real.rpow_pos_of_pos hL _
  have hC : 0≤L^C := (Real.rpow_pos_of_pos hL _).le
  have hInv : L^(-(K0+90))*L^(K0+90)=1 := by
    rw [←Real.rpow_add hL]
    have hh : -(K0+90)+(K0+90)=0 := by ring
    rw [hh,Real.rpow_zero]
  have hh : Real.exp L ≤ Z*L^(K0+90) := by
    have hmul := mul_le_mul_of_nonneg_right hZ hP.le
    calc
      _ = (Real.exp L*L^(-(K0+90)))*L^(K0+90) := by rw [mul_assoc,hInv,mul_one]
      _ ≤ Z*L^(K0+90) := hmul
  have hc := mul_le_mul_of_nonneg_right hh hC
  calc
    _ ≤ (Z*L^(K0+90))*L^C := hc
    _ = Z*L^(C+K0+90) := by
      have hExp : (K0+90)+C=C+K0+90 := by ring
      rw [mul_assoc,←Real.rpow_add hL,hExp]

/-- The actual original signed character k/Z physical Fourier
coefficient mass is bounded on a NONEMPTY historical source fibre
by the true dyadic Z times a fixed power of L. No additional
Fourier moment or shifted-divisor hypothesis. The exponent is
2*C_W1+256+K0+90, paying precisely the SOURCE e-window width.
The unweighted global diagonal pays the original shifted-divisor
moment, the finite χ k/Z carrier has one physical m' and no
extra cofactor count. -/
theorem parity_eventually_original_historical_actual_k_z_l1_mass_Z434
    (K0 : ℝ) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K J : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
        0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
        0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
        (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
        (∀n∈J,V≤(n:ℝ)) →
        ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
        e∈parityOriginalHistoricalCauchyActiveESupport434
          (sourceOriginalLiteralDepth 20 L) L E band slot δ →
        m∈K →
        (parityOriginalHistoricalActualKZPhysicalEventCarrier434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m K J k Z).Nonempty →
        ∀ χ : DirichletCharacter ℂ (2*k.natAbs),
        parityOriginal3DPhysicalFiniteCoefficientMass434
          (parityOriginalHistoricalActualKZPhysicalEventCarrier434
            (sourceOriginalLiteralDepth 20 L) L band slot δ
            ⌊2*Real.exp L⌋₊ e m K J k Z)
          (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
            (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α signed
            ⌊2*Real.exp L⌋₊ e m k χ) ≤
        Acoef^2*(Z:ℝ)*
          L^(2*parityOriginalW1PolylogExponent434+256+K0+90) := by
  filter_upwards [parity_eventually_original_historical_actual_k_z_l1_mass_polylog434,
    eventually_ge_atTop (8:ℝ)] with L hMass hL8
  refine ⟨hMass.1,hL8,?_⟩
  intro band slot δ ξ rho U V E K J α signed Acoef hA hα hU hV hUV hScale
    hDyad hNLo e m k Z he heMem hm hNonempty χ
  have hLpos : 0<L := by linarith
  have hmLo := (hDyad m hm).1
  have hmHi := (hDyad m hm).2
  have hWin : parityOriginalHistoricalEWindow434 L E e :=
    (Finset.mem_filter.mp heMem).2
  have hZ := parity_original_historical_nonempty_actual_k_z_parity417_window434
    (sourceOriginalLiteralDepth 20 L) L U V E K0 band slot δ J K e m k Z
    hL8 hK0 hU hV hUV hScale hWin he hmLo hDyad hNLo hNonempty
  have hMassBound := hMass.2 band slot δ ξ rho E K J α signed Acoef
    hA hα e m k Z he heMem hm χ
  have hConvert := parity_original_historical_source_X_to_Z_polylog434
    L (Z:ℝ) (2*parityOriginalW1PolylogExponent434+256) K0 hLpos hZ.1
  have hCoefSq : 0≤Acoef^2 := sq_nonneg _
  have hMult := mul_le_mul_of_nonneg_left hConvert hCoefSq
  calc
    _ ≤ Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256) := hMassBound
    _ = Acoef^2*(Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256)) := by ring
    _ ≤ Acoef^2*((Z:ℝ)*L^((2*parityOriginalW1PolylogExponent434+256)+K0+90)) := hMult
    _ = Acoef^2*(Z:ℝ)*L^(2*parityOriginalW1PolylogExponent434+256+K0+90) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalKZ416TailBudget -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- The exact genuine Euclidean R^3 pre-Fourier SOURCE finite
Schwartz derivative budget B_H is NONNEGATIVE, uniformly over
all original source cutoff parameters. This follows from the
previous native Fourier-moment positivity and bound; it is not
a claimed polynomial-in-L growth bound. -/
theorem parity_original_3d_actual_source_finite_B_nonneg434
    (H : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) :
    0≤parityOriginal3DSourceMomentFiniteBudget434 H f := by
  have hm := parity_original_real_3d_fourier_moment_le_original_source_finite434 H f
  have hpos : (0:ℝ) ≤
      (∫ζ : EuclideanSpace ℝ (Fin 3),
        ‖ζ‖^H * ‖(𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ‖) := by
    apply integral_nonneg
    intro ζ
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  exact hpos.trans hm

/-- The ORIGINAL signed physical Parity (4.16) low-frequency
3D Fourier truncation error on one actual k/Z cell with the
REAL constructed eta_e,L/eta_n cutoff and original complex
H0, alpha, Dirichlet chi weights, with all n/z source gates. -/
def parityOriginalHistoricalActualKZ416FourierError434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (Z : ℕ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ, buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℝ :=
  ‖parityOriginalHistoricalActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ -
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginalHistoricalActualKZTwistedFourierIntegrand434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hBufSmooth hBufSupport ζ)‖

/-- The exact ORIGINAL physically weighted/source-dyadic χ k/Z
cofactor error is bounded by its explicit native cofactor ℓ1 mass
times the finite original R^3 source derivative moment B_H/T^H.
This is the fully instantiated historical source version of Parity
(4.15)-(4.16) and no analytical 4.17 saving is assumed. -/
theorem parity_original_historical_actual_k_z_416_error_le_mass434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (U E V : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀x : ℝ, buf x≠0 → a≤x ∧ x≤b)
    (hBufOne : ∀x∈Set.Icc (0:ℝ) (Real.log 2),buf x=1)
    (hZ : 0<Z) (H : ℕ) (T : ℝ) (hT : 0<T) :
    parityOriginalHistoricalActualKZ416FourierError434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hBufSmooth hBufSupport T ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport)/T^H) := by
  unfold parityOriginalHistoricalActualKZ416FourierError434
  rw [parity_original_historical_actual_k_z_weighted_character_eq_original_fibre434
    d L hL band slot δ ξ rho α signed Y e m K J k Z χ he E V]
  exact parity_original_historical_actual_k_z_416_fourier_trunc434
    d L hL band slot δ ξ rho α signed Y e m K J k Z χ he
    U E V hU hE hV hmLo hmHi hDyad
    buf a b hBufSmooth hBufSupport hBufOne hZ H T hT
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedPostMellinAudit -/

section

open Green64Analytic.Parity

end

/-! ## OriginalSignedEq417HResidue -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The REAL source Q-skip residual is zero off the image of the
actual B509 labelled skipped-Q products, including repetitions.
No external support premise: it follows from the exact native
endpoint-fibre definition in sourceNativePrimeCore. -/
theorem parity_original_B509_actual_residual_zero_outside434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (r : ℕ)
    (hr : r ∉ paritySourceB509SkipEndpointSupport434
       (Q := sourceActualSortedQ 20 d L band slot) δ) :
    (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual r = 0 := by
  let Q := sourceActualSortedQ 20 d L band slot
  let S : Finset (OrderedQSkip (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length Q δ) := Finset.univ
  let w := fun a : OrderedQSkip (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length Q δ =>
      sourceActualSortedFactorial 20 d *
        orderedSkipPhase (sourceActualSortedFrequencyScales 20 d L band slot) ξ a
  change sourceEndpointFibre S orderedSkipProduct w r = 0
  unfold sourceEndpointFibre
  apply Finset.sum_eq_zero
  intro a ha
  have ha' := (Finset.mem_filter.mp ha).2
  have hmem : r ∈ paritySourceB509SkipEndpointSupport434 (Q:=Q) δ := by
    unfold paritySourceB509SkipEndpointSupport434
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha'⟩
  exact False.elim (hr hmem)

/-- Exact finite reserved-prime product fibre reindex by NATURAL
DIVISOR p of t, with no duplication or loss of multiplicities.
The residual is exactly zero outside S, so extending the sum to
all p-divisors is valid only after proving that support. -/
theorem parity_original_reserved_pair_product_to_divisor434
    (S : Finset ℕ) (w : ℕ → ℂ)
    (hw : ∀ r, r ∉ S → w r=0)
    (p t : ℕ) (hp : 0<p) (c : ℂ) :
    (∑ r ∈ S, if p*r=t then c*w r else 0) =
    if (p ∣ t) then c * w (t/p) else 0 := by
  by_cases hd : p∣t
  · have heq (r : ℕ) : p*r=t ↔ r=t/p := by
      constructor
      · intro h
        exact Nat.mul_left_cancel hp (by rw [h,Nat.mul_div_cancel' hd])
      · intro h
        rw [h]
        exact Nat.mul_div_cancel' hd
    calc
      _ = ∑ r ∈ S, if r=t/p then c*w r else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          simp only [heq r]
      _ = if t/p ∈ S then c * w (t/p) else 0 :=
        Finset.sum_ite_eq' S (t/p) (fun r => c*w r)
      _ = c * w (t/p) := by
        by_cases hm : t/p ∈ S
        · simp [hm]
        · simp [hm,hw _ hm]
      _ = _ := by simp [hd]
  · have hn (r : ℕ) : p*r≠t := by
      intro h
      exact hd ⟨r,h.symm⟩
    simp [hd,hn]
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEq417HExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- The actual ORIGINAL historical Parity(4.8) H_sigma(vStar), with
complete original reserved Q prime p, full B509 skipped-Q residual,
all 20! factorial labels and even repeated primes, is EXACTLY the
b633PrimeRest source coefficient consumed by specialized Parity(4.17).
The source prime-slot interval is literally the original reserved
Q-band and the B509 residual is zero outside the original skip
product support, proved rather than imposed. σ is arbitrary here
because both H_sigma and b633PrimeRest contain the SAME explicit
prime phase; the original SOURCE yields σ=0 unless separately derived. -/
theorem parity_original_reserved_H_eq_actual_eq417_prime_rest434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ₀ σ₁ σ : ℝ)
    (t : ℕ) (ht : 0 < t) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
    parityOriginalReservedH434 d L band slot δ ξ K alpha q χ σ₀ σ₁ σ t =
      b633PrimeRest434 F.lo F.hi σ F.residual t := by
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  let P := sourceOriginalQActualBands 20 d L band
  let S := paritySourceB509SkipEndpointSupport434
    (Q:=sourceActualSortedQ 20 d L band slot) δ
  have hslot : (Finset.Icc F.lo F.hi).filter Nat.Prime = P := by
    exact parity_native_core_prime_slot434 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
  have hPrime (p : ℕ) (hp : p∈P) : p.Prime := by
    have hmem : p∈(Finset.Icc F.lo F.hi).filter Nat.Prime := by
      rw [hslot]
      exact hp
    exact (Finset.mem_filter.mp hmem).2
  have hw (r : ℕ) (hr : r∉S) : F.residual r=0 := by
    exact parity_original_B509_actual_residual_zero_outside434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ r hr
  have hTerm (p : ℕ) (hp : p∈P) :
    (∑ r ∈ S, if p*r=t then
      sourceOriginalPureMellinPhase434 σ p * F.residual r else 0) =
    if (p∣t) then imaginaryPower p σ * F.residual (t/p) else 0 := by
    have hPair := parity_original_reserved_pair_product_to_divisor434
      S F.residual hw p t (hPrime p hp).pos
      (sourceOriginalPureMellinPhase434 σ p)
    rw [hPair]
    rw [parity_native_imaginary_pure_mellin434 p (hPrime p hp).pos σ]
  have hSet : P.filter (fun p => p∣t) =
      t.divisors.filter (fun p => p.Prime ∧ p∈Finset.Icc F.lo F.hi) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_divisors]
    have hP : p∈P ↔ p.Prime ∧ p∈Finset.Icc F.lo F.hi := by
      rw [←hslot]
      simp only [Finset.mem_filter]
      tauto
    constructor
    · intro hh
      exact ⟨⟨hh.2,ht.ne'⟩,hP.mp hh.1⟩
    · intro hh
      exact ⟨hP.mpr hh.2,hh.1.1⟩
  rw [parity_original_reserved_H_literal_prime_convolution434]
  unfold b633PrimeRest434
  change (∑ p ∈ P, ∑ r ∈ S, if p*r=t then
    sourceOriginalPureMellinPhase434 σ p * F.residual r else 0) =
    ∑ p ∈ t.divisors, if p.Prime ∧ p∈Finset.Icc F.lo F.hi then
      imaginaryPower p σ * F.residual (t/p) else 0
  calc
    _ = ∑ p ∈ P, if (p∣t) then imaginaryPower p σ * F.residual (t/p) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hTerm p hp
    _ = ∑ p ∈ P.filter (fun p => p∣t),
          imaginaryPower p σ * F.residual (t/p) := by
          rw [Finset.sum_filter]
    _ = ∑ p ∈ t.divisors.filter (fun p => p.Prime ∧ p∈Finset.Icc F.lo F.hi),
          imaginaryPower p σ * F.residual (t/p) := by rw [hSet]
    _ = _ := by rw [Finset.sum_filter]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalH0TwoCores -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- The TRUE original signed h=-2 reserved prime-slot coefficient
H_0(vStar) from original B509 skipped Q is exactly the original
B633/Parity (4.16) prime-slot convolution b633PrimeRest, for EVERY
positive literal physical vStar. Neither the source α nor χ nor
external Fourier phase contaminates the source residual. The
original source truly has sigma=0. -/
theorem parity_original_historical_intrinsic_H0_eq_actual_prime_rest434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ) (vStar : ℕ) (hv : 0 < vStar) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
    parityOriginalIntrinsicH434 d L band slot δ ξ 0 vStar =
      b633PrimeRest434 F.lo F.hi 0 F.residual vStar := by
  dsimp only
  calc
    _ = parityOriginalReservedH434 d L band slot δ ξ
          K alpha q χ σ₀ σ₁ 0 vStar :=
        (parity_original_reserved_H_is_intrinsic434
          d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 vStar).symm
    _ = _ := parity_original_reserved_H_eq_actual_eq417_prime_rest434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 vStar hv

/-- Original REAL h=-2 physical Q/P-gated vStar is positive:
it multiplies the positive selected e to produce the true
nonzero ordinary(P,u), for u>0. Positivity is derived, not
postulated as a prime-slot assumption. -/
theorem parity_original_historical_physical_vStar_pos434
    (L : ℝ) (e u vStar : ℕ) (hu : 0<u)
    (hgate : e*vStar=sourceOriginalOrdinaryPart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u) :
    0<vStar := by
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hO : sourceOriginalOrdinaryPart P u≠0 :=
    parity_original_ordinary_part_nonzero434 P u hu.ne'
  have hNZ : vStar≠0 := by
    intro hz
    rw [hz,mul_zero] at hgate
    exact hO hgate.symm
  exact Nat.pos_of_ne_zero hNZ

/-- The ACTUAL original Parity §4.6 two-core reserved-prime sources,
with full signed h=-2 Q/P gates and W-rough m,mp, are LITERALLY
b633PrimeRest on the two canonical shifted target ordinary-part
quotients zStar/mp and z'Star/m. BOTH residuals are the same
intrinsic skipped-Q original B509 c_r (with complex conjugation
applied only later by the original Gram pair); no hypothetical
prime-slot core or P-free vStar is inserted. -/
theorem parity_original_historical_real_two_endpoint_H0_prime_slot434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hm : sourceD20Rough (Real.exp (Real.sqrt L)) m)
    (hmp : sourceD20Rough (Real.exp (Real.sqrt L)) mp)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ : ℝ) :
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let zp := ((z:ℤ)+2*k).toNat
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
    ∃ u ∈ parityOriginalHistoricalFixedMNUSupport434 Y m n,
      ∃ up ∈ parityOriginalHistoricalFixedMNUSupport434 Y mp n,
      ∃ vs ∈ parityOriginalHistoricalOffdiagPhysicalVStarGate434
        d L band slot δ e u,
      ∃ vps ∈ parityOriginalHistoricalOffdiagPhysicalVStarGate434
        d L band slot δ e up,
      0<vs ∧ 0<vps ∧
      parityOriginalIntrinsicH434 d L band slot δ ξ 0 vs =
        b633PrimeRest434 F.lo F.hi 0 F.residual
          (sourceOriginalOrdinaryPart P z / mp) ∧
      parityOriginalIntrinsicH434 d L band slot δ ξ 0 vps =
        b633PrimeRest434 F.lo F.hi 0 F.residual
          (sourceOriginalOrdinaryPart P zp / m) := by
  dsimp only
  obtain ⟨u,hu,up,hup,vs,hvs,vps,hvps,hStarZ,hStarZp,hQuotZ,hQuotZp⟩ :=
    parity_original_historical_physical_source_star_two_cores434
      d L hL band slot δ Y e m mp n he hneq hValid hm hmp
  let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  have hUPos : 0<u := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
  have hUpPos : 0<up := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
  have hGate : e*vs=sourceOriginalOrdinaryPart P u :=
    (Finset.mem_filter.mp hvs).2
  have hGatep : e*vps=sourceOriginalOrdinaryPart P up :=
    (Finset.mem_filter.mp hvps).2
  have hv : 0<vs := parity_original_historical_physical_vStar_pos434
    L e u vs hUPos hGate
  have hvp : 0<vps := parity_original_historical_physical_vStar_pos434
    L e up vps hUpPos hGatep
  have hH : parityOriginalIntrinsicH434 d L band slot δ ξ 0 vs =
      b633PrimeRest434
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).lo
        (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).hi
        0 (sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁).residual vs :=
    parity_original_historical_intrinsic_H0_eq_actual_prime_rest434
      d L band slot δ ξ K alpha q χ σ₀ σ₁ vs hv
  have hHp := parity_original_historical_intrinsic_H0_eq_actual_prime_rest434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ vps hvp
  refine ⟨u,hu,up,hup,vs,hvs,vps,hvps,hv,hvp,?_,?_⟩
  · rw [hQuotZ]
    exact hH
  · rw [hQuotZp]
    exact hHp
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalMellinPhase -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Genuine Parity physical n^(it) for positive n equals the LITERAL
original signed e-first Mellin exponential with no missing logarithm
or different branch. Exact n>0 is source-derived; no assumption on
nonpositive imaginaryPower behaviour. -/
theorem parity_original_physical_imaginary_power_exp434
    (n : ℕ) (hn : 0<n) (t : ℝ) :
    imaginaryPower n t = Complex.exp (Complex.I *((t*Real.log (n:ℝ):ℝ):ℂ)) := by
  rw [parity_native_imaginary_pure_mellin434 n hn t]
  unfold sourceOriginalPureMellinPhase434
  rw [←Complex.ofReal_mul]

/-- True multiplicative SOURCE Mellin phase for positive physical
integers: (ab)^(it)=a^(it)b^(it). Uses actual real log(a*b)
without assuming multiplicativity of complex powers at zero. -/
theorem parity_original_physical_imaginary_power_mul434
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (t : ℝ) :
    imaginaryPower (a*b) t=imaginaryPower a t*imaginaryPower b t := by
  rw [parity_original_physical_imaginary_power_exp434 (a*b) (Nat.mul_pos ha hb) t,
    parity_original_physical_imaginary_power_exp434 a ha t,
    parity_original_physical_imaginary_power_exp434 b hb t]
  have hl : Real.log ((a*b:ℕ):ℝ) =
      Real.log (a:ℝ)+Real.log (b:ℝ) := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')]
  rw [hl]
  have hExp : Complex.I*((t*(Real.log (a:ℝ)+Real.log (b:ℝ)):ℝ):ℂ) =
      Complex.I*((t*Real.log (a:ℝ):ℝ):ℂ)+
      Complex.I*((t*Real.log (b:ℝ):ℝ):ℂ) := by
    push_cast
    ring
  rw [hExp,Complex.exp_add]

/-- Physical n^(i(s+t)) = n^(is)n^(it) with exact original
Mellin/Parity convention at all positive source integers. -/
theorem parity_original_physical_imaginary_power_add434
    (n : ℕ) (hn : 0<n) (s t : ℝ) :
    imaginaryPower n (s+t)=imaginaryPower n s*imaginaryPower n t := by
  simp only [parity_original_physical_imaginary_power_exp434 n hn]
  have hh : Complex.I*((((s+t)*Real.log (n:ℝ)):ℝ):ℂ)=
      Complex.I*((s*Real.log (n:ℝ):ℝ):ℂ)+
      Complex.I*((t*Real.log (n:ℝ):ℝ):ℂ) := by
    push_cast
    ring
  rw [hh,Complex.exp_add]

/-- Original physical Mellin negative-power is the exact STAR
conjugate of positive power at all source n>0. This preserves
sigma=0 prime phases and both signed epsilon branches. -/
theorem parity_original_physical_imaginary_power_star434
    (n : ℕ) (hn : 0<n) (t : ℝ) :
    star (imaginaryPower n t) = imaginaryPower n (-t) := by
  rw [parity_original_physical_imaginary_power_exp434 n hn t,
    parity_original_physical_imaginary_power_exp434 n hn (-t)]
  change (starRingEnd ℂ) (Complex.exp (Complex.I * ((t*Real.log (n:ℝ):ℝ):ℂ))) = _
  rw [←Complex.exp_conj]
  have hh : (starRingEnd ℂ) (Complex.I * ((t*Real.log (n:ℝ):ℝ):ℂ)) =
      Complex.I * (((-t)*Real.log (n:ℝ):ℝ):ℂ) := by
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  rw [hh]

/-- Inverse complex Mellin phases on TRUE positive physical
cofactor integers cancel exactly. This is essential when commuting
Parity's original source v^it with the prime-slot m^it factors. -/
theorem parity_original_physical_imaginary_power_mul_neg_one434
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    imaginaryPower n t * imaginaryPower n (-t) = 1 := by
  have h := parity_original_physical_imaginary_power_add434 n hn t (-t)
  have hz : imaginaryPower n 0 = 1 := by
    rw [parity_original_physical_imaginary_power_exp434 n hn 0]
    simp
  simpa only [add_neg_cancel,hz] using h.symm

/-- Original Parity signed source physical Mellin variables (v,v')
and the two separated log frequencies (m,m',z) factor EXACTLY
into the two prime-slot phase frequencies xi1+rho and xi2-rho,
plus outer shifted-target z^(i(rho+xi3)) and zp^(-i rho).
This is precisely the manuscript (4.16)-(4.17) phase relation.

Hypotheses are the GENUINE source h=-2 positive products z=m'v,
zp=m v' with 0< m,m',v,v'; it is not a hypothetical unconditional
complex power identity on zero or negative integer endpoints. -/
theorem parity_original_physical_mellin_phase_two_core434
    (m mp v vp z zp : ℕ) (hm : 0 < m) (hmp : 0 < mp)
    (hv : 0 < v) (hvp : 0 < vp)
    (hz : z=mp*v) (hzp : zp=m*vp)
    (xi1 xi2 xi3 rho : ℝ) :
    imaginaryPower m xi1 * imaginaryPower mp xi2 *
      imaginaryPower z xi3 * imaginaryPower v rho *
      imaginaryPower vp (-rho) =
    imaginaryPower z (rho+xi3) * imaginaryPower zp (-rho) *
      imaginaryPower m (xi1+rho) * imaginaryPower mp (xi2-rho) := by
  have hzPos : 0 < z := by rw [hz]; exact Nat.mul_pos hmp hv
  have hzpPos : 0 < zp := by rw [hzp];exact Nat.mul_pos hm hvp
  rw [parity_original_physical_imaginary_power_add434 z hzPos rho xi3,
    parity_original_physical_imaginary_power_add434 m hm xi1 rho,
    show xi2-rho=xi2+(-rho) by ring,
    parity_original_physical_imaginary_power_add434 mp hmp xi2 (-rho)]
  have hzphase := parity_original_physical_imaginary_power_mul434 mp v hmp hv rho
  have hzpPhase := parity_original_physical_imaginary_power_mul434 m vp hm hvp (-rho)
  rw [←hz] at hzphase
  rw [←hzp] at hzpPhase
  rw [hzphase,hzpPhase]
  have hmpC := parity_original_physical_imaginary_power_mul_neg_one434 mp hmp rho
  have hmC := parity_original_physical_imaginary_power_mul_neg_one434 m hm (-rho)
  simp only [neg_neg] at hmC
  calc
    _ = (imaginaryPower m xi1 * imaginaryPower mp xi2 *
        imaginaryPower z xi3 * imaginaryPower v rho *
        imaginaryPower vp (-rho)) *
        (imaginaryPower mp rho * imaginaryPower mp (-rho)) *
        (imaginaryPower m (-rho) * imaginaryPower m rho) := by
          rw [hmpC,hmC]
          ring
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalMellinTwist -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- TRUE original Parity (4.16)-(4.17) physical Mellin/Fourier
shift-transfer with NO artificial positivity or product hypotheses.
From an actually populated h=-2 two-endpoint Q/P/B509 source,
with e odd, m≠m', the exact source determines
z=m'v>0, zp=(z+2k).toNat=m*v'>0 and positive m,m',v,v'.

The signed original Mellin pair in the physical Cauchy Gram,
multiplied by the raw m,m',z Fourier powers, is IDENTICALLY the
two prime-slot convolution phases with xi1+rho,xi2-rho and outer
z^(i(xi3+rho)),zp^(-i rho). None of the original Q/P cofactor
support or signed epsilon is changed by this identity. -/
theorem parity_original_historical_source_physical_mellin_two_core434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (xi1 xi2 xi3 rho : ℝ) :
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let zp := ((z:ℤ)+2*k).toNat
    let v := parityOriginalHistoricalCanonicalV434 e m n
    let vp := parityOriginalHistoricalCanonicalV434 e mp n
    imaginaryPower m xi1 * imaginaryPower mp xi2 *
      imaginaryPower z xi3 * imaginaryPower v rho *
      imaginaryPower vp (-rho) =
    imaginaryPower z (rho+xi3) * imaginaryPower zp (-rho) *
      imaginaryPower m (xi1+rho) * imaginaryPower mp (xi2-rho) := by
  dsimp only
  let k := parityOriginalHistoricalOffdiagK434 e m mp
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  let zp := ((z:ℤ)+2*k).toNat
  let v := parityOriginalHistoricalCanonicalV434 e m n
  let vp := parityOriginalHistoricalCanonicalV434 e mp n
  have hFactor := parity_original_historical_true_two_endpoint_z_v_factors434
    d L band slot δ Y e m mp n he hneq hValid
  dsimp only at hFactor
  obtain ⟨hv,hvp,hz,ht,hZ,hZp⟩ := hFactor
  change z=mp*v at hZ
  change zp=m*vp at hZp
  have hmpPos : 0 < mp := by
    have hMul : 0 < mp*v := by rw [←hZ]; exact hz
    exact Nat.pos_of_mul_pos_right hMul
  have hmPos : 0 < m := by
    obtain ⟨u,hu,up,hup,hOther⟩ := hValid
    exact (Finset.mem_filter.mp hu).2.1
  exact parity_original_physical_mellin_phase_two_core434
    m mp v vp z zp hmPos hmpPos hv hvp hZ hZp xi1 xi2 xi3 rho
end Green64Analytic.Parity

end

end

/-! ## OriginalSignedEq417AVExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- TRUE original separately signed historical Parity (4.7) physical
coefficient a_v(v)=v^(i rho)epsilon(v)W1(v)H_sigma(vStar)
IS LITERALLY the one-endpoint source amplitude used in the
specialized original Parity (4.17): original `imaginaryPower`, full
q=1/2 one-marked source weight, true multiplicity parity and
b633PrimeRest with original Q prime-band and B509 residual.
This equality holds for either ε=1 or ε=E, every positive physical
vStar and v, and any physical sigma parameter ON BOTH sides;
the genuine original SOURCE Ψ Mellin representation still has σ=0.
No signed correlation bound or Cauchy square follows from equality
alone. -/
theorem parity_original_signed_aV_eq_actual_eq417_core434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ σ rho : ℝ) (signed : Bool) (vStar v : ℕ)
    (hvStar : 0 < vStar) (hv : 0 < v) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
    parityOriginalReservedSignedPhysicalAV434 d L band slot δ ξ
      K alpha q χ σ₀ σ₁ σ rho signed vStar v =
    imaginaryPower v rho *
      (((sourceMarkedWeight (1/2:ℝ) 1
          (sourceOriginalPAllActualBands 20 L) v *
        groupSign (sourceOriginalPAllActualBands 20 L) signed v):ℝ):ℂ) *
      b633PrimeRest434 F.lo F.hi σ F.residual vStar := by
  dsimp only
  rw [parity_original_signed_aV_eq_eq417_imaginary_marked434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ σ rho signed vStar v hv]
  rw [parity_original_reserved_H_eq_actual_eq417_prime_rest434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ σ vStar hvStar]

/-- For true source sigma=0, the EXACT Parity(4.7) physical a_v for
both signs uses precisely Eq(4.17)'s b633PrimeRest at zero reserved
prime phase. No nonzero sigma has been introduced into the source. -/
theorem parity_original_signed_aV_source_zero_sigma_eq417434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ₀ σ₁ rho : ℝ) (signed : Bool) (vStar v : ℕ)
    (hvStar : 0 < vStar) (hv : 0 < v) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ σ₀ σ₁
    parityOriginalReservedSignedPhysicalAV434 d L band slot δ ξ
      K alpha q χ σ₀ σ₁ 0 rho signed vStar v =
    imaginaryPower v rho *
      (((sourceMarkedWeight (1/2:ℝ) 1
          (sourceOriginalPAllActualBands 20 L) v *
        groupSign (sourceOriginalPAllActualBands 20 L) signed v):ℝ):ℂ) *
      b633PrimeRest434 F.lo F.hi 0 F.residual vStar := by
  exact parity_original_signed_aV_eq_actual_eq417_core434
    d L band slot δ ξ K alpha q χ σ₀ σ₁ 0 rho signed vStar v hvStar hv
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalSignedPairB633 -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The EXACT original Parity(4.7) h=-2 signed Cauchy Gram pair,
INCLUDING both original H_0 reserved prime slots and full skipped-Q
B509 intrinsic c_r, equals the TWO physical Parity(4.16) convolution
factors with their original complex conjugations, real full-W1 and
same epsilon at both endpoints. The original vStar and vpStar remain
literal source parameters, and 0<sigma is NOT invented: sigma=0.

The identity holds for every positive real physical endpoint, any
source alpha and any original choice of signed ε=1,E. No external
saved correlation bound and no imported desired (4.17) saving. -/
theorem parity_original_historical_intrinsic_signed_pair_eq_B633434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (m mp vs vps v vp : ℕ)
    (hvs : 0<vs) (hvps : 0<vps) (hv : 0<v) (hvp : 0<vp)
    (rho : ℝ) (signed : Bool) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ 0 0
    (alpha m * parityOriginalIntrinsicSignedAV434
       d L band slot δ ξ 0 rho signed vs v) *
      star (alpha mp * parityOriginalIntrinsicSignedAV434
        d L band slot δ ξ 0 rho signed vps vp) =
    alpha m * star (alpha mp) *
      imaginaryPower v rho * imaginaryPower vp (-rho) *
      b633PrimeRest434 F.lo F.hi 0 F.residual vs *
      star (b633PrimeRest434 F.lo F.hi 0 F.residual vps) *
      (((sourceMarkedWeight (1/2:ℝ) 1 (sourceOriginalPAllActualBands 20 L) v *
          sourceMarkedWeight (1/2:ℝ) 1 (sourceOriginalPAllActualBands 20 L) vp : ℝ):ℂ)) *
      (((groupSign (sourceOriginalPAllActualBands 20 L) signed v *
          groupSign (sourceOriginalPAllActualBands 20 L) signed vp : ℝ):ℂ)) := by
  dsimp only
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q χ 0 0
  have hAV := parity_original_signed_aV_source_zero_sigma_eq417434
    d L band slot δ ξ K alpha q χ 0 0 rho signed vs v hvs hv
  have hAVp := parity_original_signed_aV_source_zero_sigma_eq417434
    d L band slot δ ξ K alpha q χ 0 0 rho signed vps vp hvps hvp
  rw [parity_original_signed_physical_AV_is_intrinsic434] at hAV
  rw [parity_original_signed_physical_AV_is_intrinsic434] at hAVp
  dsimp only at hAV hAVp
  rw [hAV,hAVp]
  simp only [star_mul]
  rw [parity_original_physical_imaginary_power_star434 vp hvp rho]
  simp only [Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalFourierScaleUnwind -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- EXACT fixed-scale phase from Parity's original logarithmic Fourier
coordinates. This coefficient is independent of the summation
integer n and can be pulled OUTSIDE the physical arithmetic core. -/
def parityOriginalHistoricalFourierScalePhase434 (U nu : ℝ) : ℂ :=
  Complex.exp (Complex.I*((- (2*Real.pi*nu*Real.log U):ℝ):ℂ))

/-- ORIGINAL Parity (4.14)-(4.16): the Euclidean Fourier phase
exp(2πiν log(m/U)), for genuine m>0,U>0, is EXACTLY the
physical complex imaginaryPower m^(2πiν) times a SINGLE fixed
U-dependent phase. Do not replace normalized logarithms by
m^(iν) without this 2π and scaling correction! -/
theorem parity_original_historical_log_phase_to_physical_power434
    (m : ℕ) (hm : 0 < m) (U nu : ℝ) (hU : 0<U) :
    Complex.exp (((2*Real.pi*nu*Real.log ((m:ℝ)/U):ℝ):ℂ)*Complex.I) =
      parityOriginalHistoricalFourierScalePhase434 U nu *
      imaginaryPower m (2*Real.pi*nu) := by
  have hmReal : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hUReal : U≠0 := hU.ne'
  rw [Real.log_div hmReal hUReal]
  rw [parity_original_physical_imaginary_power_exp434 m hm (2*Real.pi*nu)]
  unfold parityOriginalHistoricalFourierScalePhase434
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The EXACT original Parity three-dimensional source 2π Fourier
phase at t=(log(m/U),log(m'/U),log(z/Z)) becomes ONE common
arithmetic-independent scale multiplier times THREE unnormalized
physical imaginary powers with frequencies 2πζ₀,2πζ₁,2πζ₂.
This is the missing bridge before using the source E4.1 bounds
for original Parity (4.16)-(4.17), not a guessed identification. -/
theorem parity_original_historical_three_log_phases_to_parity_416434
    (U Z : ℝ) (hU : 0<U) (hZ : 0<Z)
    (m mp z : ℕ) (hm : 0 < m) (hmp : 0 < mp) (hz : 0 < z)
    (ζ : EuclideanSpace ℝ (Fin 3)) :
    parityOriginal3DPhysicalLogFourierPhase434 ζ
      (parityOriginalHistoricalRealLogTriple434 U Z m mp z) =
    (parityOriginalHistoricalFourierScalePhase434 U (ζ 0) *
     parityOriginalHistoricalFourierScalePhase434 U (ζ 1) *
     parityOriginalHistoricalFourierScalePhase434 Z (ζ 2)) *
    (imaginaryPower m (2*Real.pi*(ζ 0)) *
     imaginaryPower mp (2*Real.pi*(ζ 1)) *
     imaginaryPower z (2*Real.pi*(ζ 2))) := by
  rw [parity_original_historical_real_3d_m_mp_z_phase_factor434]
  unfold parityOriginalHistoricalActualMOuterFourierPhase434
    parityOriginalHistoricalActualMpZFourierPhase434
  rw [parity_original_historical_log_phase_to_physical_power434 m hm U (ζ 0) hU,
      parity_original_historical_log_phase_to_physical_power434 mp hmp U (ζ 1) hU,
      parity_original_historical_log_phase_to_physical_power434 z hz Z (ζ 2) hZ]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalB633PhysicalPairTerm -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Literal ONE (m',m) summand from the source-native Parity(4.16)
`b633ParityPhysicalPair434` original two-core expansion at (z,z+2k),
with all original α,χ, two signed W1/epsilon factors and B509
prime-slot residuals on the P-free parts of z/m', (z+2k)/m.
The complete physical pair is a sum of THESE summands over true
P-ordinary-part divisors. The source sigma remains exactly 0. -/
def parityOriginalHistoricalB633PhysicalPairTerm434
    (L rho xi1 xi2 xi3 : ℝ) (signed : Bool)
    (alpha residual : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi m mp z zp : ℕ) : ℂ :=
  let P := sourceOriginalPAllActualBands 20 L
  let Pall := Finset.univ.biUnion P
  alpha m * star (alpha mp) *
    chi (mp : ZMod q) * star (chi (m : ZMod q)) *
    imaginaryPower m xi1 * imaginaryPower mp xi2 *
    imaginaryPower z xi3 *
    imaginaryPower (z/mp) rho * imaginaryPower (zp/m) (-rho) *
    b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall (z/mp)) *
    star (b633PrimeRest434 lo hi 0 residual (sourceOriginalOrdinaryPart Pall (zp/m))) *
    (((sourceMarkedWeight (1/2:ℝ) 1 P (z/mp) *
        sourceMarkedWeight (1/2:ℝ) 1 P (zp/m) : ℝ):ℂ)) *
    (((groupSign P signed (z/mp) * groupSign P signed (zp/m) : ℝ):ℂ))

/-- Exact original signed h=-2 physical source pair at its true
positive Q/P/B509 endpoints equals the LITERAL single (m',m)
prime-slot convolution summand of the real Parity(4.16) physical pair.

The proof preserves the TRUE selected e, shared n and both original
u=m*n-2/u'=m'*n-2 carrier gates; its source vStar and vpStar are
not replaced by arbitrary factors. The arithmetic identities
z=m'v, z+2k=mv', and ordinary_P(v)=vStar are proved previously,
not inserted as hypothetical independent assumptions. The residual
is exactly the original skipped-Q source, sigma=0 and all complex
conjugations and character placements are unchanged.

This equality does NOT imply that the sum of such SOURCE terms is
already the full unrestricted (4.17) double-core correlation; the
complete support/outer-sum bijection remains a separate open step. -/
theorem parity_original_historical_true_pair_eq_B633_summand434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (Y e m mp n u up vs vps : ℕ)
    (he : Odd e) (hneq : m≠mp)
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434 Y m n)
    (hup : up∈parityOriginalHistoricalFixedMNUSupport434 Y mp n)
    (hvs : vs∈parityOriginalHistoricalOffdiagPhysicalVStarGate434
      d L band slot δ e u)
    (hvps : vps∈parityOriginalHistoricalOffdiagPhysicalVStarGate434
      d L band slot δ e up)
    (rho xi1 xi2 xi3 : ℝ) :
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let zp := ((z:ℤ)+2*k).toNat
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    let v := vs*sourceOriginalPPrimePart P u
    let vp := vps*sourceOriginalPPrimePart P up
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    ∀ signed : Bool,
    chi (mp:ZMod q) * star (chi (m:ZMod q)) *
       imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
       ((alpha m * parityOriginalIntrinsicSignedAV434
            d L band slot δ ξ 0 rho signed vs v) *
          star (alpha mp * parityOriginalIntrinsicSignedAV434
            d L band slot δ ξ 0 rho signed vps vp)) =
    parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
      alpha F.residual q chi F.lo F.hi m mp z zp := by
  dsimp only
  let P := sourceOriginalPAllActualBands 20 L
  let Pall := Finset.univ.biUnion P
  let v := vs*sourceOriginalPPrimePart Pall u
  let vp := vps*sourceOriginalPPrimePart Pall up
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  let zp := ((z:ℤ)+2*parityOriginalHistoricalOffdiagK434 e m mp).toNat
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
  have hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n :=
    ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩
  have hF := parity_original_historical_true_two_endpoint_z_v_factors434
    d L band slot δ Y e m mp n he hneq hValid
  dsimp only at hF
  obtain ⟨hvp0,hvpp0,hzpos,hzppos,hzeq,hzpeq⟩ := hF
  have hVe : parityOriginalHistoricalCanonicalV434 e m n=v :=
    parity_original_historical_canonical_v_eq_source_physical434
      L e m n u vs he.pos
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
      (Finset.mem_filter.mp hu).2.2.2 (Finset.mem_filter.mp hvs).2
  have hVpe : parityOriginalHistoricalCanonicalV434 e mp n=vp :=
    parity_original_historical_canonical_v_eq_source_physical434
      L e mp n up vps he.pos
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
      (Finset.mem_filter.mp hup).2.2.2 (Finset.mem_filter.mp hvps).2
  have hv : 0<v := by rw [←hVe]; exact hvp0
  have hvp : 0<vp := by rw [←hVpe];exact hvpp0
  have hz : z=mp*v := by
    change z=mp*parityOriginalHistoricalCanonicalV434 e m n at hzeq
    rw [hVe] at hzeq
    exact hzeq
  have hzp : zp=m*vp := by
    change zp=m*parityOriginalHistoricalCanonicalV434 e mp n at hzpeq
    rw [hVpe] at hzpeq
    exact hzpeq
  have hm : 0 < m := (Finset.mem_filter.mp hu).2.1
  have hmp : 0 < mp := (Finset.mem_filter.mp hup).2.1
  have hDivZ : z/mp=v := by
    rw [hz]
    exact Nat.mul_div_cancel_left v hmp
  have hDivZp : zp/m=vp := by
    rw [hzp]
    exact Nat.mul_div_cancel_left vp hm
  have hPprime : ∀p∈Pall,p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact (parity_original_actual_full_P_prime_rough_cap434 L hL g p hpg).1
  have hOV : sourceOriginalOrdinaryPart Pall v=vs := by
    exact parity_original_source_vStar_eq_ordinary_physical_v434
      Pall u e vs (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1.ne'
      hPprime (Finset.mem_filter.mp hvs).2
  have hOVp : sourceOriginalOrdinaryPart Pall vp=vps := by
    exact parity_original_source_vStar_eq_ordinary_physical_v434
      Pall up e vps (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1.ne'
      hPprime (Finset.mem_filter.mp hvps).2
  have hvsPos : 0<vs := parity_original_historical_physical_vStar_pos434
    L e u vs (Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1).1
    (Finset.mem_filter.mp hvs).2
  have hvpsPos : 0<vps := parity_original_historical_physical_vStar_pos434
    L e up vps (Finset.mem_Ioc.mp (Finset.mem_filter.mp hup).1).1
    (Finset.mem_filter.mp hvps).2
  intro signed
  have hPair := parity_original_historical_intrinsic_signed_pair_eq_B633434
    d L band slot δ ξ K alpha q chi m mp vs vps v vp
    hvsPos hvpsPos hv hvp rho signed
  dsimp only at hPair
  unfold parityOriginalHistoricalB633PhysicalPairTerm434
  dsimp only [Pall]
  rw [hDivZ,hDivZp,hOV,hOVp]
  rw [hPair]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalSingleSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Literal original h=-2 physical u-support at fixed (Y,m,n) is
EITHER empty OR a singleton: if it contains u, its only possible
value is u=m*n-2. No falsely independent u summation or #u factor
remains after Parity's original Q/P source gates. -/
theorem parity_original_historical_true_fixed_MN_u_singleton434
    (Y m n u : ℕ)
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434 Y m n) :
    parityOriginalHistoricalFixedMNUSupport434 Y m n = {u} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hu,?_⟩
  intro u' hu'
  have h1 := (Finset.mem_filter.mp hu').2.2.2
  have h2 := (Finset.mem_filter.mp hu).2.2.2
  exact parity_original_historical_actual_diag_same_u434 m n u' u h1 h2

/-- Literal original Q/B509 skipped-prime vStar source support at
fixed positive selected e and physical u is EITHER empty OR a
singleton, since e*vStar=ordinary_P(u) determines exactly one
positive integer vStar. This uniqueness is source arithmetic,
not a coefficient-wise norm estimate. -/
theorem parity_original_historical_true_fixed_e_u_vStar_singleton434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (e u vs : ℕ) (he : 0<e)
    (hvs : vs∈parityOriginalHistoricalOffdiagPhysicalVStarGate434
      d L band slot δ e u) :
    parityOriginalHistoricalOffdiagPhysicalVStarGate434
      d L band slot δ e u = {vs} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hvs,?_⟩
  intro vs' hvs'
  have hgate := (Finset.mem_filter.mp hvs').2
  have hgate0 := (Finset.mem_filter.mp hvs).2
  exact parity_original_historical_actual_diag_vStar_unique434
    L e u vs' vs he hgate hgate0

/-- The TRUE ORIGINAL Parity(4.13) h=-2 physical source on ONE
populated (e,n,m,m') fibre is exactly ONE complex signed Cauchy
pair and NOT a multiple-sum with independent u,u',vStar,vStar'
counts. All four finite original Q/P carrier sets have exactly one
inhabited element under the genuine positivity and e-gate.

This eliminates all multiplicity loss from the physical source
expansion BEFORE invoking (4.16)/(4.17), and applies identically
for original epsilon=1 or epsilon=E. -/
theorem parity_original_historical_true_offdiag_source_single_pair434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m mp n u up vs vps : ℕ) (he : 0<e)
    (hu : u∈parityOriginalHistoricalFixedMNUSupport434 Y m n)
    (hup : up∈parityOriginalHistoricalFixedMNUSupport434 Y mp n)
    (hvs : vs∈parityOriginalHistoricalOffdiagPhysicalVStarGate434
      d L band slot δ e u)
    (hvps : vps∈parityOriginalHistoricalOffdiagPhysicalVStarGate434
      d L band slot δ e up) :
    let P := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    parityOriginalHistoricalOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e n m mp =
    (alpha m * parityOriginalIntrinsicSignedAV434
      d L band slot δ ξ 0 rho signed vs (vs*sourceOriginalPPrimePart P u)) *
    star (alpha mp * parityOriginalIntrinsicSignedAV434
      d L band slot δ ξ 0 rho signed vps (vps*sourceOriginalPPrimePart P up)) := by
  dsimp only
  have hU := parity_original_historical_true_fixed_MN_u_singleton434 Y m n u hu
  have hUp := parity_original_historical_true_fixed_MN_u_singleton434 Y mp n up hup
  have hVs := parity_original_historical_true_fixed_e_u_vStar_singleton434
    d L band slot δ e u vs he hvs
  have hVps := parity_original_historical_true_fixed_e_u_vStar_singleton434
    d L band slot δ e up vps he hvps
  unfold parityOriginalHistoricalOffdiagPhysicalAtENMMp434
  rw [hU,hUp]
  simp only [Finset.sum_singleton]
  rw [hVs,hVps]
  simp only [Finset.sum_singleton]

/-- The ACTUAL complete signed, character and original Fourier
twisted historical source coefficient for a populated physical
(e,n,m,m') equals the LITERAL (m',m) B633 Parity(4.16) physical
pair summand, not just one chosen auxiliary witness term.

All original u=m*n-2, u'=m'*n-2, skipped-Q/B509 vStar and vStar'
source sums are eliminated by PROVED singleton arithmetic, and the
remaining prime-slot residual, original alpha, χ conjugation and
real W1/parity have EXACTLY their original source values. There is
no assumed correlation cancellation and no unjustified E4.1 bound.
The full outer e,m,χ,k,Z source-to-(4.17) carrier equality is
SEPARATELY OPEN. -/
theorem parity_original_historical_actual_source_coeff_eq_B633_term434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool) :
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let zp := ((z:ℤ)+2*k).toNat
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha q chi 0 0
    chi (mp:ZMod q) * star (chi (m:ZMod q)) *
       imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
       parityOriginalHistoricalOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho alpha signed Y e n m mp =
    parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
      alpha F.residual q chi F.lo F.hi m mp z zp := by
  dsimp only
  obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hValid
  have hOne := parity_original_historical_true_offdiag_source_single_pair434
    d L band slot δ ξ rho alpha signed Y e m mp n u up vs vps
    he.pos hu hup hvs hvps
  dsimp only at hOne
  rw [hOne]
  exact parity_original_historical_true_pair_eq_B633_summand434
    d L hL band slot δ ξ K alpha q chi Y e m mp n u up vs vps
    he hneq hu hup hvs hvps rho xi1 xi2 xi3 signed
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZB633Finite -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The *COMPLETE FINITE genuine physical* source signed
h=-2 k/Z cofactor χ-sum after Parity (2.6), with literal source
m'→n Q/P support and original H0, IS an exact finite sum
of Parity (4.16) `b633ParityPhysicalPair` (m',m) **summands**.

This is stronger than identifying one arbitrary source witness:
all original u,u',vStar,vStar' summations inside the real Cauchy
coefficient have been proved singleton and are included here.
The same original b629 α, character χ(m') conjχ(m), all source
B509 skipped-Q, W1 and signed epsilon are retained; the
three real Fourier variables xi1,xi2,xi3 are not assumed zero.

The equality is on the TRUE original physical k/Z subcarrier,
not yet an unrestricted sum over all m,m',z in Eq (4.17), and
DOES NOT imply the E4.1 correlation saving without a separate
full support and outer-index reindex. -/
theorem parity_original_historical_actual_k_z_full_finite_eq_B633434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K J : Finset ℕ) (alpha : ℕ → ℂ)
    (Y e m : ℕ) (he : Odd e) (k : ℤ) (Z : ℕ)
    (chi : DirichletCharacter ℂ (2*k.natAbs))
    (rho xi1 xi2 xi3 : ℝ) (signed : Bool) :
    let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha (2*k.natAbs) chi 0 0
    (∑q∈S,
      star (chi (m : ZMod (2*k.natAbs))) *
      imaginaryPower m xi1 * imaginaryPower q.1 xi2 *
      imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) xi3 *
      parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho alpha signed Y e m k chi q) =
    ∑q∈S,
      parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
        alpha F.residual (2*k.natAbs) chi F.lo F.hi m q.1
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
        (((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℤ)+2*k).toNat) := by
  dsimp only
  let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha (2*k.natAbs) chi 0 0
  apply Finset.sum_congr rfl
  intro q hq
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMP := Finset.mem_filter.mp hProd.1
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMP.1).1.symm
  have hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m q.1 q.2 := hMem.2.1
  have hPoint := parity_original_historical_actual_source_coeff_eq_B633_term434
    d L hL band slot δ ξ K alpha (2*k.natAbs) chi Y e m q.1 q.2
    he hNe hValid rho xi1 xi2 xi3 signed
  dsimp only at hPoint
  have hk : parityOriginalHistoricalOffdiagK434 e m q.1=k := hMP.2
  rw [hk] at hPoint
  unfold parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
  calc
    _ = chi (q.1 : ZMod (2*k.natAbs)) *
          star (chi (m : ZMod (2*k.natAbs))) *
          imaginaryPower m xi1 * imaginaryPower q.1 xi2 *
          imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) xi3 *
          parityOriginalHistoricalOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho alpha signed Y e q.2 m q.1 := by ring
    _ = parityOriginalHistoricalB633PhysicalPairTerm434 L rho xi1 xi2 xi3 signed
        alpha F.residual (2*k.natAbs) chi F.lo F.hi m q.1
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
        (((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℤ)+2*k).toNat) :=
      hPoint
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalActualKZFourierB633Join -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- The original source true Euclidean 3D physical k/Z cut-off
Fourier integrand, multiplied by exactly the OUTER
conjugate-character factor of original Parity (2.6), equals ONE
common Fourier Schwartz coefficient times the exact U,U,Z
normalization phase and a finite sum of the LITERAL original
B633/Parity (4.16) two-core physical pair summands.

The coefficient χ(m') remains inside the original fine-alpha
physical source; the character conjugate χ(m) is OUTSIDE it.
The source external real Fourier frequencies are 2πζ₁,₂,₃
and all U,Z normalization phases are explicit and common to
all m',n in this actual physical k/Z fibre.

There are no assumed 4.17 cancellation bounds, no unsupported
z or n fibres, no extra number-of-characters factors, no missing
B509 residuals or fabricated nonzero sigma. This is still ONE
fixed source e,m,k,Z,χ slice; proving that the *sum* of all
such slices reindexes into the full UNRESTRICTED Parity 4.17
correlation, with actual ψ_Z and endpoint Ppart gates, remains
separate and OPEN. -/
theorem parity_original_historical_actual_k_z_3d_fourier_eq_B633434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (K J : Finset ℕ) (alpha : ℕ → ℂ)
    (Y e m : ℕ) (he : Odd e) (k : ℤ) (Z : ℕ)
    (chi : DirichletCharacter ℂ (2*k.natAbs))
    (rho : ℝ) (signed : Bool)
    (hU : 0<U) (hZ : 0<Z)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ, buf t≠0 → a≤t ∧ t≤b)
    (ζ : EuclideanSpace ℝ (Fin 3)) :
    let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha (2*k.natAbs) chi 0 0
    let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport
    let scale := parityOriginalHistoricalFourierScalePhase434 U (ζ 0) *
      parityOriginalHistoricalFourierScalePhase434 U (ζ 1) *
      parityOriginalHistoricalFourierScalePhase434 (Z:ℝ) (ζ 2)
    star (chi (m : ZMod (2*k.natAbs))) *
      parityOriginalHistoricalActualKZTwistedFourierIntegrand434
        d L U E V hL Z k band slot δ ξ rho alpha signed Y e m K J chi
        buf a b hBufSmooth hBufSupport ζ =
    (𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ * scale *
      (∑q∈S,
        parityOriginalHistoricalB633PhysicalPairTerm434
          L rho (2*Real.pi*(ζ 0)) (2*Real.pi*(ζ 1)) (2*Real.pi*(ζ 2))
          signed alpha F.residual (2*k.natAbs) chi F.lo F.hi m q.1
          (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
          (((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℤ)+2*k).toNat)) := by
  dsimp only
  let S := parityOriginalHistoricalActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho alpha signed Y e m k chi
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V (Z:ℝ) k buf a b hBufSmooth hBufSupport
  let scale := parityOriginalHistoricalFourierScalePhase434 U (ζ 0) *
      parityOriginalHistoricalFourierScalePhase434 U (ζ 1) *
      parityOriginalHistoricalFourierScalePhase434 (Z:ℝ) (ζ 2)
  let F := sourceNativePrimeCore 20 d L band slot δ ξ K alpha (2*k.natAbs) chi 0 0
  have hZreal : 0<(Z:ℝ) := by exact_mod_cast hZ
  have hFourier := parity_original_historical_actual_k_z_twisted_physical_factor434
    d L U E V hL Z k band slot δ ξ rho alpha signed Y e m K J chi
    buf a b hBufSmooth hBufSupport ζ
  have hPhase (q : ℕ×ℕ) (hq : q∈S) :
      parityOriginal3DPhysicalLogFourierPhase434 ζ
        (parityOriginalHistoricalPhysicalFourierEventTriple434
          U (Z:ℝ) e m (fun p : ℕ×ℕ =>p.1) (fun p : ℕ×ℕ=>p.2) q) =
      scale *
        (imaginaryPower m (2*Real.pi*(ζ 0)) *
         imaginaryPower q.1 (2*Real.pi*(ζ 1)) *
         imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
           (2*Real.pi*(ζ 2))) := by
    have hMem := Finset.mem_filter.mp hq
    have hPhys : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m q.1 q.2 := hMem.2.1
    obtain ⟨u,hu,up,hup,⟨vs,hvs⟩,⟨vps,hvps⟩⟩ := hPhys
    have hm : 0 < m := (Finset.mem_filter.mp hu).2.1
    have hmp : 0 < q.1 := (Finset.mem_filter.mp hup).2.1
    have hz : 0 < parityOriginalHistoricalCanonicalZ434 e m q.1 q.2 := hMem.2.2.1
    change parityOriginal3DPhysicalLogFourierPhase434 ζ
      (parityOriginalHistoricalRealLogTriple434 U (Z:ℝ) m q.1
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)) = _
    exact parity_original_historical_three_log_phases_to_parity_416434
      U (Z:ℝ) hU hZreal m q.1
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
      hm hmp hz ζ
  have hScaleSum :
      (∑q∈S, W q *
        parityOriginal3DPhysicalLogFourierPhase434 ζ
          (parityOriginalHistoricalPhysicalFourierEventTriple434
            U (Z:ℝ) e m (fun p : ℕ×ℕ =>p.1) (fun p : ℕ×ℕ=>p.2) q)) =
      scale * (∑q∈S,
        imaginaryPower m (2*Real.pi*(ζ 0)) *
        imaginaryPower q.1 (2*Real.pi*(ζ 1)) *
        imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
           (2*Real.pi*(ζ 2)) * W q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hPhase q hq]
    ring
  have hB633 := parity_original_historical_actual_k_z_full_finite_eq_B633434
    d L (by linarith : (1:ℝ)≤L) band slot δ ξ K J alpha Y e m he k Z chi
    rho (2*Real.pi*(ζ 0)) (2*Real.pi*(ζ 1)) (2*Real.pi*(ζ 2)) signed
  dsimp only at hB633
  change (∑q∈S,
    star (chi (m:ZMod (2*k.natAbs))) *
    imaginaryPower m (2*Real.pi*(ζ 0)) *
    imaginaryPower q.1 (2*Real.pi*(ζ 1)) *
    imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
       (2*Real.pi*(ζ 2)) * W q) = _ at hB633
  rw [←hFourier]
  unfold parityOriginal3DPhysicalFiniteTwistedSource434
  change star (chi (m : ZMod (2*k.natAbs))) *
    ((𝓕 f : 𝓢(EuclideanSpace ℝ (Fin 3),ℂ)) ζ *
      (∑q∈S, W q *
        parityOriginal3DPhysicalLogFourierPhase434 ζ
          (parityOriginalHistoricalPhysicalFourierEventTriple434
            U (Z:ℝ) e m (fun p : ℕ×ℕ =>p.1) (fun p : ℕ×ℕ=>p.2) q))) = _
  rw [hScaleSum]
  have hNormalSum :
      (∑q∈S,
        star (chi (m:ZMod (2*k.natAbs))) *
        imaginaryPower m (2*Real.pi*(ζ 0)) *
        imaginaryPower q.1 (2*Real.pi*(ζ 1)) *
        imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
           (2*Real.pi*(ζ 2)) * W q) =
      star (chi (m:ZMod (2*k.natAbs))) *
      (∑q∈S,
        imaginaryPower m (2*Real.pi*(ζ 0)) *
        imaginaryPower q.1 (2*Real.pi*(ζ 1)) *
        imaginaryPower (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
           (2*Real.pi*(ζ 2)) * W q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hNormalSum] at hB633
  rw [←hB633]
  ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalB633SourceDivisors -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Every GENUINE original Parity(4.13) physical h=-2 supported source
(e,m,m',n), with original P/Q gates and W-rough outer alpha
cofactors, is a VALID pair of terms in the precise *divisor sets*
used by the original B633 two-core correlation at z and z+2k:

 m' ∈ divisors(ordinary_P(z)),
 m  ∈ divisors(ordinary_P(z+2k)).

Both original shifted arguments and ordinary parts are positive.
The quotient primes are the ACTUAL vStar,vpStar from the SOURCE.
This proves a rigorous ONE-WAY source→4.17 support embedding.
Converse/full support equality and smooth ψ_Z weights remain OPEN:
a bound for a full COMPLEX signed sum does not automatically bound
one selected subset of its terms. -/
theorem parity_original_historical_actual_source_in_B633_divisor_carrier434
    (d : ℕ) (L : ℝ) (hL : 1≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hm : sourceD20Rough (Real.exp (Real.sqrt L)) m)
    (hmp : sourceD20Rough (Real.exp (Real.sqrt L)) mp) :
    let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
    let k := parityOriginalHistoricalOffdiagK434 e m mp
    let z := parityOriginalHistoricalCanonicalZ434 e m mp n
    let zp := ((z:ℤ)+2*k).toNat
    0<z ∧ 0<zp ∧
      mp∈(sourceOriginalOrdinaryPart Pall z).divisors ∧
      m∈(sourceOriginalOrdinaryPart Pall zp).divisors := by
  dsimp only
  let Pall := Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)
  let z := parityOriginalHistoricalCanonicalZ434 e m mp n
  let zp := ((z:ℤ)+2*parityOriginalHistoricalOffdiagK434 e m mp).toNat
  have hFactor := parity_original_historical_true_two_endpoint_z_v_factors434
    d L band slot δ Y e m mp n he hneq hValid
  dsimp only at hFactor
  obtain ⟨hv,hvp,hz,hshift,hZ,hZp⟩ := hFactor
  have hZpPos : 0<zp := by
    change 0<((parityOriginalHistoricalCanonicalZ434 e m mp n:ℤ)+
      2*parityOriginalHistoricalOffdiagK434 e m mp).toNat
    omega
  obtain ⟨u,hu,up,hup,vs,hvs,vps,hvps,hStarZ,hStarZp,hQz,hQzp⟩ :=
    parity_original_historical_physical_source_star_two_cores434
      d L hL band slot δ Y e m mp n he hneq hValid hm hmp
  have hNonzeroZ : sourceOriginalOrdinaryPart Pall z≠0 :=
    parity_original_ordinary_part_nonzero434 Pall z hz.ne'
  have hNonzeroZp : sourceOriginalOrdinaryPart Pall zp≠0 :=
    parity_original_ordinary_part_nonzero434 Pall zp hZpPos.ne'
  have hStarZ' : sourceOriginalOrdinaryPart Pall z = mp*vs := hStarZ
  have hStarZp' : sourceOriginalOrdinaryPart Pall zp = m*vps := hStarZp
  have hDivZ : mp ∣ sourceOriginalOrdinaryPart Pall z := by
    rw [hStarZ']
    exact dvd_mul_right mp vs
  have hDivZp : m ∣ sourceOriginalOrdinaryPart Pall zp := by
    rw [hStarZp']
    exact dvd_mul_right m vps
  exact ⟨hz,hZpPos,
    Nat.mem_divisors.mpr ⟨hDivZ,hNonzeroZ⟩,
    Nat.mem_divisors.mpr ⟨hDivZp,hNonzeroZp⟩⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalPhysicalENInjective -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The actual original Parity (4.13) determinant relation
  (m'-m)=e*k
makes the SOURCE selected e UNIQUE at fixed (m,m',k), provided
k is the SAME nonzero original integer shift and both genuine
Q/P h=-2 physical endpoint witnesses exist. No count of possible
selected Q label allocations or divisor majorant is used. -/
theorem parity_original_historical_true_source_selected_e_unique434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m mp n n' e e' : ℕ) (k : ℤ)
    (he : Odd e) (he' : Odd e') (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hValid' : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e' m mp n')
    (hk : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (hk' : parityOriginalHistoricalOffdiagK434 e' m mp=k)
    (hkn : k≠0) : e=e' := by
  have hE := parity_original_historical_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m mp n he hneq hValid
  have hE' := parity_original_historical_physical_k_exact_cofactor_shift434
    d L band slot δ Y e' m mp n' he' hneq hValid'
  rw [hk] at hE
  rw [hk'] at hE'
  have hMul : (e:ℤ)*k=(e':ℤ)*k := hE.symm.trans hE'
  have hInt : (e:ℤ)=(e':ℤ) := mul_right_cancel₀ hkn hMul
  exact_mod_cast hInt

/-- The true original h=-2 Parity source map
  (selected e, shared n) ↦ z=m'*(m*n-2)/e
is injective on Q/P POPULATED physical pairs at fixed (m,m',k):
if two allowed source pairs yield the same actual canonical z and
the same nonzero determinant quotient k, then their e AND n are
identical. This proves source→4.17 two-core carrier injection in
these dimensions, not surjectivity onto the unrestricted divisor
sum; cancellation cannot be transferred from that sum without the
separately open converse/support proof. -/
theorem parity_original_historical_true_source_e_n_to_z_injective434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y m mp n n' e e' : ℕ) (k : ℤ) (z : ℕ)
    (he : Odd e) (he' : Odd e') (hneq : m≠mp)
    (hValid : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e m mp n)
    (hValid' : parityOriginalHistoricalPhysicalValidN434
      d L band slot δ Y e' m mp n')
    (hk : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (hk' : parityOriginalHistoricalOffdiagK434 e' m mp=k)
    (hkn : k≠0)
    (hZ : parityOriginalHistoricalCanonicalZ434 e m mp n=z)
    (hZ' : parityOriginalHistoricalCanonicalZ434 e' m mp n'=z) :
    e=e' ∧ n=n' := by
  have heEq := parity_original_historical_true_source_selected_e_unique434
    d L band slot δ Y m mp n n' e e' k he he' hneq hValid hValid' hk hk' hkn
  subst e'
  have hmp : 0 < mp := by
    obtain ⟨u,hu,up,hup,huv⟩ := hValid
    exact (Finset.mem_filter.mp hup).2.1
  have hnEq := parity_original_historical_supported_canonical_z_injective434
    d L band slot δ Y e m mp n n' he.pos hmp hValid hValid'
    (hZ.trans hZ'.symm)
  exact ⟨rfl,hnEq⟩
end Green64Analytic.Parity

end

end

